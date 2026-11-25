import Leader.L4.BStarNativeOffsetSweep

namespace L4.BStarNativeOffsetPhysical
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarH6Ordinal
open BStarAcquireAnchors BStarLongFiberOwner BStarFenceReceiverChart

private theorem word_at_back {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (k : Nat) (i : Fin n) (K : ordinal h hh i=k) :
    word h (back i k)=word h i := by
  induction k generalizing i with
  | zero => rw [back_zero]
  | succ k ih =>
    let prev := RearTrace.predecessor i
    have E : rightNeighbor prev=i := RearTrace.right_predecessor i
    have H : h i=false := Bool.eq_false_iff.mpr (fun U => by
      have Z := (ordinal_zero h hh i).mpr U; omega)
    have P := ordinal_body h hh prev (E.symm ▸ H)
    rw [E,K] at P
    have Q := ih prev (by omega)
    rw [←E,back_right_succ,E]
    have R := right_word h prev
    rw [E,H] at R
    obtain ⟨lo,hi⟩ := word_range h prev hh
    simp only [Bool.toNat_false,Int.natCast_zero,Int.add_zero,Int.emod_eq_of_lt lo hi] at R
    exact Q.trans R.symm

private theorem digit_back {n : Nat} (i : Fin n) (k : Nat) :
    digitFrom (back i k) k=i := by
  induction k generalizing i with
  | zero => simp [digitFrom,back_zero]
  | succ k ih =>
    let prev := RearTrace.predecessor i
    have E : rightNeighbor prev=i := RearTrace.right_predecessor i
    have P : back i (k+1)=back prev k := by rw [←E,back_right_succ]
    rw [P]
    change rightNeighbor (digitFrom (back prev k) k)=i
    rw [ih,E]

theorem same_ordinal_same_word {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i j : Fin n) (O : ordinal h hh i=ordinal h hh j) (W : word h i=word h j) : i=j := by
  let k := ordinal h hh i
  have Hi : h (back i k)=true := (ordinal_spec h hh i).2.1
  have Hj : h (back j k)=true := by rw [show k=ordinal h hh j from O]; exact (ordinal_spec h hh j).2.1
  have T := header_word_injective h (a₁:=⟨back i k,Hi⟩) (a₂:=⟨back j k,Hj⟩)
    ((word_at_back h hh k i rfl).trans (W.trans (word_at_back h hh k j O.symm).symm))
  have T' := congrArg Subtype.val T
  exact (digit_back i k).symm.trans ((congrArg (fun a => digitFrom a k) T').trans (digit_back j k))

open BStarNumericChartCoverage BStarNumericConsecutive BStarNumericChronology
open BStarLongClaims BStarLongLiteral BStarLongEvents BStarLongTransport BStarResetChartTouch
open BStarAcquireVisitOrder BStarAcquireLiteralChain

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

private theorem marks_sublist {base x : X} {addr : Nat→Pos n} {len op k l : Nat}
    {w : List (Fin n)} {ds : List D} (A : Aligned hp base addr len op x k w l ds) :
    (ds.map Departure.mark).Sublist w := by
  induction A with
  | nil _ => exact .slnil
  | stay _ _ _ ih => exact .cons _ ih
  | hop _ _ _ _ ih => exact .cons_cons _ ih

theorem significant_address {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {op k l width : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j=>S.getD j fall) len op x k w l ds)
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (d : D) (M : d∈ds.filter (significant hp base (fun j=>S.getD j fall)))
    (bound : oldOrdinal B base hh d.mark<width) :
    d.mark=digitFrom (S.getD len fall).1 (oldOrdinal B base hh d.mark) := by
  let h := oldH6 B base
  let root := (S.getD len fall).1
  have E := endpoint_spec h hh o 10
  rw [←chart.terminal] at E
  let j := oldOrdinal B base hh d.mark
  have data := digit_from hp E.1 width notShort j bound
  apply same_ordinal_same_word h hh
  · exact data.1.symm
  obtain ⟨dm,sm⟩ := List.mem_filter.mp M
  obtain ⟨V,_,lenBound⟩ := Aligned.record_facts hp A d dm
  have one := (Aligned.record_significant hp A d dm sm).1
  have actual : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
    rw [←actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
    exact List.mem_map.mpr ⟨_,V.1,rfl⟩
  have left : d.claim.source=L 1 := by
    rw [center_of _ _ actual one]
    rfl
  have addrEq : S.getD d.index fall=(d.mark,1) := by
    change (fun j=>S.getD j fall) d.index=(d.mark,1)
    rw [V.2.2.1,left]
    rfl
  have mem : (d.mark,(1 : Fin 11))∈S := by
    rw [←addrEq,←List.getElem_eq_getD (h:=by have := chart.length; omega)]
    exact List.getElem_mem _
  have own := (chart.entries _ mem).2
  have same : word h d.mark=word h root := by
    change owner (total h) (word h d.mark) 1=o.val at own
    have rootOwn := E.2.1
    change owner (total h) (word h root) 1=o.val at rootOwn
    have R := congrArg (fun z => addressWord (total h) z 1) (own.trans rootOwn.symm)
    rw [address_inverse,address_inverse,Int.emod_eq_of_lt (word_range h d.mark hh).1
      (word_range h d.mark hh).2,Int.emod_eq_of_lt (word_range h root hh).1 (word_range h root hh).2] at R
    exact R
  exact same.trans data.2.symm

theorem actual_sweep_sublist {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {op width : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j=>S.getD j fall) len op x 0 w len ds)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1) :
    ((List.range width).map (digitFrom (S.getD len fall).1)).Sublist w := by
  let visits := ds.filter (significant hp base (fun j=>S.getD j fall))
  have ordered : visits.map (fun d => oldOrdinal B base hh d.mark)=List.range width := by
    have L := aligned_ordinals hp chart A flags notShort
    rw [←aligned_sites hp A,List.map_map] at L
    exact L
  have addressed : visits.map Departure.mark=
      (visits.map (fun d => oldOrdinal B base hh d.mark)).map (digitFrom (S.getD len fall).1) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro d dm
    have bound : oldOrdinal B base hh d.mark<width :=
      List.mem_range.mp (ordered ▸ List.mem_map.mpr ⟨d,dm,rfl⟩)
    exact significant_address hp chart A notShort d dm bound
  rw [←ordered,←addressed]
  exact (List.filter_sublist.map Departure.mark).trans (marks_sublist hp A)

/-- A genuinely completed K1 sweep repairs all significant offsets in
its own word, with arbitrary old bits at entry, and preserves them
through every later actual fixed-layout mark. No bound on width
other than physical no-short geometry is needed. -/
theorem after_sweep {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {op width : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j=>S.getD j fall) len op x 0 w len ds)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (suffix : List (Fin n))
    (same : ∀ u v,w++suffix=u++v → oldH6 B (run x u)=oldH6 B base) :
    BStarNativeOffsetSweep.PrefixOK (oldH6 B base) (S.getD len fall).1 (width-1) (run x (w++suffix)) := by
  let h := oldH6 B base
  let root := (S.getD len fall).1
  have E := endpoint_spec h hh o 10
  rw [←chart.terminal] at E
  have visit := actual_sweep_sublist hp chart A flags notShort
  have select : ((List.range (width-1)).map (digitFrom root)).Sublist (w++suffix) :=
    (((List.range_sublist.mpr (Nat.sub_le width 1)).map (digitFrom root)).trans visit).trans
      (List.sublist_append_left _ _)
  apply BStarNativeOffsetSweep.replay hp h root (width-1) x E.1 _ sep (w++suffix) same select
  intro j pos J
  have ord := (digit_from hp E.1 width notShort j (by omega)).1
  apply Bool.eq_false_iff.mpr
  intro Hj
  have zero := (ordinal_zero h hh _).mpr Hj
  change oldOrdinal B base hh (digitFrom root j)=0 at zero
  exact (Nat.ne_of_gt pos) (ord.symm.trans zero)

theorem later_offset {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op op' width : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j=>S.getD j fall) len op x 0 w len ds)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (gap later : List (Fin n)) {ds' : List D}
    (T : Aligned hp base (fun j=>S.getD j fall) len op' (run x (w++gap)) 0 later len ds')
    (same : ∀ u v,(w++gap)++later=u++v → oldH6 B (run x u)=oldH6 B base)
    (d : D) (M : d∈ds'.filter (significant hp base (fun j=>S.getD j fall))) :
    BStarPhysicalDigitSem.off (geom hp d)=min 5 (oldOrdinal B base hh d.mark) := by
  have ords := aligned_ordinals hp chart T flags notShort
  rw [←aligned_sites hp T,List.map_map] at ords
  have jLt : oldOrdinal B base hh d.mark<width :=
    List.mem_range.mp (ords ▸ List.mem_map.mpr ⟨d,M,rfl⟩)
  have coord := significant_address hp chart T notShort d M jLt
  obtain ⟨dm,sm⟩ := List.mem_filter.mp M
  obtain ⟨pre,post,W,_,old⟩ := Aligned.prefix_to hp T d dm
  have E : (w++gap)++later=(w++(gap++pre))++d.mark::post := by
    rw [W]; simp only [List.append_assoc]
  have scope (u v : List (Fin n)) (H : w++(gap++pre)=u++v) :
      oldH6 B (run x u)=oldH6 B base := same u (v++d.mark::post) (by rw [E,H,List.append_assoc])
  have ready := after_sweep hp chart A flags notShort sep (gap++pre) scope
    (oldOrdinal B base hh d.mark) (by omega)
  rw [←coord,←List.append_assoc,BStarResetSchedule.run_append,old] at ready
  obtain ⟨V,L,_⟩ := Aligned.record_facts hp T d dm
  have one := (Aligned.record_significant hp T d dm sm).1
  have main : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
    rw [←actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
    exact List.mem_map.mpr ⟨_,V.1,rfl⟩
  have axis : d.claim.source.side=.left := by rw [center_of _ _ main one]; rfl
  have fixed : oldH6 B d.old=oldH6 B base :=
    funext fun i => (congrArg Prod.fst (L i)).symm
  unfold geom
  rw [axis]
  exact (BStarNativeOffsetTrace.eff_eq hp d.old fixed d.mark).trans ready

#print axioms after_sweep
#print axioms later_offset
#print axioms actual_sweep_sublist
#print axioms same_ordinal_same_word
end L4.BStarNativeOffsetPhysical

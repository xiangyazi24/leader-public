import Leader.L4.BStarNumericContinuity

namespace L4.BStarNumericConsecutive
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongCommand BStarLongArithmetic
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetSchedule
open BStarNumericChronology BStarNumericCarry BStarNumericContinuity
open L4.Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
  (r:=r) (c:=c) (p:=p) (c₁:=c₁)

def byte (d : D) : BitVec LW :=
  BStarLongWork.atOld ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long) d.claim.source

def geom (d : D) : LongGeometry :=
  geometry (oldPair B d.old d.mark) d.claim.source.side

/-- A literal subword from the first hop's post-state to the next
significant visit's old state. Indices between them are padding. -/
def Gap (base : X) (addr : Nat → Pos n) (len op : Nat) (before after : D) : Prop :=
  ∃ w, BusyOnly hp base addr len op (step before.old before.mark) (.out (before.index+1))
      w (.out after.index) ∧
    BStarResetSchedule.run step (step before.old before.mark) w=after.old ∧
    ∀ j, before.index+1≤j → j<after.index →
      (addr j).2.val≠1 ∨ (longGeometry B (base (addr j).1)).inside=false

/-- With the exact physical subword between visits, the next selected
numerical offer equals the preceding physical digit's full output, not
merely its opcode or live tag. -/
theorem consecutive_offers {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (op i : Nat) (code : Code) (K : get i=some code) (before after : D)
    (G : Gap hp base (fun j => S.getD j fall) len op before after)
    (U : Departure.Valid hp (fun j => S.getD j fall) before)
    (V : Departure.Valid hp (fun j => S.getD j fall) after)
    (hl : after.index≤len)
    (N : Numeric before.offer) (nextNum : Numeric after.offer)
    (node : nodeOf before.offer.opcode.toNat=some i)
    (one : before.claim.source.occurrence.val=1) (inside : (geom hp before).inside=true)
    (F : (physicalDigit (geom hp before) (byte before) i code before.offer).2.fault=0)
    (canon : ∀ g j, BStarLongCommand.bind g j
      (.forward (physicalDigit (geom hp before) (byte before) i code before.offer).2)=
      .forward (physicalDigit (geom hp before) (byte before) i code before.offer).2) :
    (physicalDigit (geom hp before) (byte before) i code before.offer).2=after.offer := by
  let addr := fun j => S.getD j fall
  let g := oldPair B after.old after.mark
  let raw : Pair (BitVec LW) := ((after.old after.mark).long,(after.old (rightNeighbor after.mark)).long)
  let pay := (physicalDigit (geom hp before) (byte before) i code before.offer).2
  obtain ⟨w,P,run,pad⟩ := G
  obtain ⟨sel,_,src,_⟩ := V
  have oldBound := offer_exact g raw after.claim after.offer sel nextNum
  obtain ⟨q,Q,H,opc⟩ := BStarForwardProvenance.offer_origin g raw after.claim after.offer sel nextNum.1
  have nq : Numeric q := by
    refine ⟨H,?_,?_⟩ <;> rw [opc]
    · exact nextNum.2.1
    · exact nextNum.2.2
  change addr after.index=address after.mark after.claim.source at src
  have ar : project addr after.old after.index=.forward q := by
    change atCursor after.old (addr after.index)=_
    rw [src,←old_read after.old after.mark after.claim.source]
    exact Q
  have landed := (digit_record hp addr before U N i code node K (sep _) one inside F).2
  have carried := busy_padding hp chart sep P (before.index+1) after.index pay q rfl rfl hl pad
    landed (digit_numeric _ _ _ _ _ N F).1 canon (by rw [run]; exact ar) nq
  unfold bound at oldBound
  rw [Q,←carried,canon _ _] at oldBound
  exact Token.forward.inj oldBound

/-- Lockstep tape retaining both the old selected offer and the exact
busy event that authenticated that record on the same raw mark. -/
inductive Aligned (base : X) (addr : Nat → Pos n) (len op : Nat) :
    X → Nat → List (Fin n) → Nat → List D → Prop
  | nil {x k} (I : Current hp base addr len x (.busy op (.out k))) :
      Aligned base addr len op x k [] k []
  | stay {x k e w l ds} (I : Current hp base addr len x (.busy op (.out k)))
      (E : Event hp addr len x e (.busy op (.out k)) (.busy op (.out k)))
      (T : Aligned base addr len op (step x e) k w l ds) :
      Aligned base addr len op x k (e::w) l ds
  | hop {x k e w l ds C a p} (I : Current hp base addr len x (.busy op (.out k)))
      (E : Event hp addr len x e (.busy op (.out k)) (.busy op (.out (k+1))))
      (V : Departure.Valid hp addr ⟨k,x,e,C,a,p⟩)
      (T : Aligned base addr len op (step x e) (k+1) w l ds) :
      Aligned base addr len op x k (e::w) l (⟨k,x,e,C,a,p⟩::ds)

theorem Aligned.to_tape {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (A : Aligned hp base addr len op x k w l ds) :
    OutTape hp base addr x k w l ds := by
  induction A with
  | nil _ => exact .nil _ _
  | stay _ _ _ ih => exact .stay ih
  | hop I _ V _ ih => exact .hop I.1.1 V ih

theorem Aligned.busy {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (A : Aligned hp base addr len op x k w l ds) :
    BusyOnly hp base addr len op x (.out k) w (.out l) := by
  induction A with
  | nil I => exact .nil I
  | stay I E _ ih => exact .cons I E ih
  | hop I E _ _ ih => exact .cons I E ih

/-- Extract a chronological tape jointly with its genuine old busy
events, so that later carry arguments can cut at recorded marks. -/
theorem aligned_tape {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j => S.getD j fall) len op x z w d) :
    ∀ k l pay, z=.out k → d=.out l → l≤len →
      project (fun j => S.getD j fall) (BStarResetSchedule.run step x w) l=.forward pay →
      pay.fault=0 → ∃ ds, Aligned hp base (fun j => S.getD j fall) len op x k w l ds := by
  induction P with
  | nil I =>
    intro k l _ Z endEq _ _ _
    have eq := Cursor.out.inj (Z.symm.trans endEq)
    subst l
    cases Z
    exact ⟨[],.nil I⟩
  | @cons x z d final e w I E tail ih =>
    intro k l pay Z endEq hie F H
    subst z
    obtain ⟨k',Z'⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp tail ⟨l,endEq⟩
    subst d
    have A : Advance len (.out k) (.out k') := by
      cases E with
      | transit _ _ _ _ seen =>
        cases seen with
        | cons _ _ A _ rest => cases rest; exact A
    obtain ⟨ds,T⟩ := ih k' l pay rfl endEq hie F H
    cases A with
    | stay => exact ⟨ds,.stay I E T⟩
    | forward =>
      have current := busy_start hp tail
      obtain ⟨j,hj,q,Q,hq,_⟩ := BStarOwnerLaunchOrigin.busy_origin hp chart sep tail l hie pay F H
      have U := (BStarOwnerControlHistory.pointed_unique_forward _ len _ current.2.1 current.2.2 j hj).mp ⟨q,Q⟩
      subst j
      obtain ⟨K,a,offer,sel,hd,src,dst⟩ := ring_departure hp chart e (sep e) op k
        (by have := current.2.1.1; omega) I.1 I.2.1 I.2.2 q Q hq
      exact ⟨_,.hop I E ⟨sel,hd,src,dst⟩ T⟩

/-- Locate the pre-mark state of any record on the exact tape, with
its actual prefix word and the corresponding busy-event segment. -/
theorem Aligned.prefix_to {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (A : Aligned hp base addr len op x k w l ds)
    (d : D) (M : d∈ds) :
    ∃ pre post, w=pre++d.mark::post ∧
      BusyOnly hp base addr len op x (.out k) pre (.out d.index) ∧
      BStarResetSchedule.run step x pre=d.old := by
  induction A with
  | nil _ => contradiction
  | stay I E _ ih =>
    obtain ⟨pre,post,split,P,Q⟩ := ih M
    exact ⟨_::pre,post,congrArg (List.cons _) split,.cons I E P,Q⟩
  | @hop x k e w l ds C a p I E V tail ih =>
    rcases List.mem_cons.mp M with EQ|M
    · subst d
      exact ⟨[],w,rfl,.nil I,rfl⟩
    · obtain ⟨pre,post,split,P,Q⟩ := ih M
      exact ⟨e::pre,post,congrArg (List.cons e) split,.cons I E P,Q⟩

/-- An earlier/later pair of selected records determines a genuine
busy subword between their marks, not one chosen by comparing payloads. -/
theorem Aligned.subword_between {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (A : Aligned hp base addr len op x k w l ds)
    (before after : D) (preDs middle suffix : List D)
    (split : ds=preDs++(before::(middle++(after::suffix)))) :
    ∃ gap, BusyOnly hp base addr len op (step before.old before.mark) (.out (before.index+1))
        gap (.out after.index) ∧
      BStarResetSchedule.run step (step before.old before.mark) gap=after.old := by
  induction A generalizing preDs with
  | nil _ => cases preDs <;> contradiction
  | stay _ _ _ ih => exact ih preDs split
  | @hop x k e w l ds C a p I E V tail ih =>
    cases preDs with
    | nil =>
      have eq : (⟨k,x,e,C,a,p⟩ : D)=before ∧ ds=middle++(after::suffix) := List.cons.inj split
      obtain ⟨B0,R⟩ := eq
      subst before
      have M : after∈ds := by rw [R]; simp
      obtain ⟨gap,_,_,P,Q⟩ := Aligned.prefix_to hp tail after M
      exact ⟨gap,P,Q⟩
    | cons b preDs =>
      have H : ds=preDs++(before::(middle++(after::suffix))) := (List.cons.inj split).2
      exact ih preDs H

/-- Consecutive significant records have a genuine padding gap once
the intervening chart indices are certified nonsignificant. -/
theorem Aligned.gap_between {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (A : Aligned hp base addr len op x k w l ds)
    (before after : D) (preDs middle suffix : List D)
    (split : ds=preDs++(before::(middle++(after::suffix))))
    (pad : ∀ j, before.index+1≤j → j<after.index →
      (addr j).2.val≠1 ∨ (longGeometry B (base (addr j).1)).inside=false) :
    Gap hp base addr len op before after := by
  obtain ⟨gap,P,R⟩ := Aligned.subword_between hp A before after preDs middle suffix split
  exact ⟨gap,P,R,pad⟩

private theorem middle_indices {before after : D} {start count : Nat}
    (preDs middle suffix : List D)
    (E : (preDs++(before::(middle++(after::suffix)))).map Departure.index=List.range' start count) :
    middle.map Departure.index=List.range' (before.index+1) (after.index-(before.index+1)) := by
  simp only [List.map_append,List.map_cons] at E
  obtain ⟨k,kl,_,rest⟩ := (List.range'_eq_append_iff (xs:=preDs.map Departure.index)
    (ys:=before.index::(middle.map Departure.index++(after.index::suffix.map Departure.index)))).mp E.symm
  have sub : 0<count-k := by
    have H := congrArg List.length rest
    simp at H
    omega
  have first : before.index=start+k*1 := by
    have H := congrArg List.head? rest
    rw [show count-k=(count-k-1)+1 by omega,List.range'_succ] at H
    simpa using H
  have R : middle.map Departure.index ++ after.index::suffix.map Departure.index =
      List.range' (before.index+1) (count-k-1) := by
    rw [show count-k=(count-k-1)+1 by omega,List.range'_succ,←first] at rest
    exact (List.cons.inj rest).2
  obtain ⟨m,ml,M,last⟩ := (List.range'_eq_append_iff (xs:=middle.map Departure.index) (ys:=after.index::suffix.map Departure.index)).mp R.symm
  have sub' : 0<count-k-1-m := by
    have H := congrArg List.length last
    simp at H
    omega
  have afterEq : after.index=before.index+1+m*1 := by
    have H := congrArg List.head? last
    rw [show count-k-1-m=(count-k-1-m-1)+1 by omega,List.range'_succ] at H
    simpa using H
  rw [M]
  congr
  omega

/-- It suffices to certify the nonsignificant actual records between
two visits. All intervening indexed cursor positions occurred in
those very records, so this is not a separate chart-gap assumption. -/
theorem Aligned.gap_of_records {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (A : Aligned hp base addr len op x k w l ds)
    (before after : D) (preDs middle suffix : List D)
    (split : ds=preDs++(before::(middle++(after::suffix))))
    (pad : ∀ d∈middle,
      (addr d.index).2.val≠1 ∨ (longGeometry B (base (addr d.index).1)).inside=false) :
    Gap hp base addr len op before after := by
  apply Aligned.gap_between hp A before after preDs middle suffix split
  intro j lo hi
  have I := (OutTape.indices hp (Aligned.to_tape hp A)).2
  rw [split] at I
  have E := middle_indices preDs middle suffix I
  have J : j∈List.range' (before.index+1) (after.index-(before.index+1)) :=
    List.mem_range'_1.mpr ⟨lo,by omega⟩
  rw [←E] at J
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp J
  exact pad d hd

def significant (base : X) (addr : Nat → Pos n) (d : D) : Bool :=
  ((addr d.index).2.val==1) && (longGeometry B (base (addr d.index).1)).inside

theorem Aligned.filter_gap {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (A : Aligned hp base addr len op x k w l ds)
    (before after : D) (preDs suffix : List D)
    (split : ds.filter (significant hp base addr)=preDs++before::after::suffix) :
    Gap hp base addr len op before after := by
  obtain ⟨pre,rest,E,_,R⟩ := (List.filter_eq_append_iff
    (L₁:=preDs) (L₂:=before::after::suffix)).mp split
  obtain ⟨skipped,tail,T,_,_,Z⟩ := List.filter_eq_cons_iff.mp R
  obtain ⟨mid,post,M,no,_,_⟩ := List.filter_eq_cons_iff.mp Z
  apply Aligned.gap_of_records hp A before after (pre++skipped) mid post
  · rw [E,T,M,List.append_assoc]
  · intro d hd
    have K := no d hd
    unfold significant at K
    cases I : (longGeometry B (base (addr d.index).1)).inside
    · exact .inr rfl
    · simp [I] at K
      exact .inl K

theorem Aligned.record_facts {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (A : Aligned hp base addr len op x k w l ds) (d : D) (M : d∈ds) :
    Departure.Valid hp addr d ∧
    (∀ j, BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B d.old j) ∧ d.index<len := by
  induction A with
  | nil _ => contradiction
  | stay _ _ _ ih => exact ih M
  | @hop x k e w l ds C a p I E V tail ih =>
    rcases List.mem_cons.mp M with eq|rest
    · subst d
      have T := (busy_start hp (Aligned.busy hp tail)).2.1.1
      exact ⟨V,I.1.1,by dsimp only; omega⟩
    · exact ih rest

theorem Aligned.record_significant {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (A : Aligned hp base addr len op x k w l ds) (d : D)
    (M : d∈ds) (I : significant hp base addr d=true) :
    d.claim.source.occurrence.val=1 ∧ (geom hp d).inside=true := by
  obtain ⟨V,L,_⟩ := Aligned.record_facts hp A d M
  obtain ⟨_,_,src,_⟩ := V
  obtain ⟨J,K⟩ := Bool.and_eq_true_iff.mp I
  change ((addr d.index).2.val==1)=true at J
  change (longGeometry B (base (addr d.index).1)).inside=true at K
  rw [src] at J K
  have E : (geom hp d).inside=(longGeometry B (d.old (site d.mark d.claim.source.side))).inside := by
    unfold geom
    generalize d.claim.source.side=s
    cases s <;> rfl
  rw [E]
  refine ⟨beq_iff_eq.mp J,?_⟩
  exact (congrArg (fun z : Bool × Bool × Bool => z.2.1) (L _)).symm.trans K

/-- Carry equality for adjacent retained visits of the actual filtered
tape. Neither the exact intermediate raw word nor its carry equality
is supplied by the caller. -/
theorem next_significant_offer {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op k l : Nat} {w : List (Fin n)} {ds : List D}
    (T : Aligned hp base (fun j => S.getD j fall) len op x k w l ds)
    (preDs suffix : List D) (before after : D)
    (adj : ds.filter (significant hp base (fun j => S.getD j fall))=preDs++before::after::suffix)
    (i : Nat) (code : Code) (K : get i=some code)
    (N : Numeric before.offer) (N' : Numeric after.offer)
    (node : nodeOf before.offer.opcode.toNat=some i)
    (F : (physicalDigit (geom hp before) (byte before) i code before.offer).2.fault=0)
    (canon : ∀ g j, BStarLongCommand.bind g j
      (.forward (physicalDigit (geom hp before) (byte before) i code before.offer).2)=
      .forward (physicalDigit (geom hp before) (byte before) i code before.offer).2) :
    (physicalDigit (geom hp before) (byte before) i code before.offer).2=after.offer := by
  have bm : before∈ds.filter (significant hp base (fun j => S.getD j fall)) := by rw [adj]; simp
  have am : after∈ds.filter (significant hp base (fun j => S.getD j fall)) := by rw [adj]; simp
  obtain ⟨bM,bS⟩ := List.mem_filter.mp bm
  obtain ⟨aM,_⟩ := List.mem_filter.mp am
  obtain ⟨U,_,_⟩ := Aligned.record_facts hp T before bM
  obtain ⟨V,_,bound⟩ := Aligned.record_facts hp T after aM
  obtain ⟨one,inside⟩ := Aligned.record_significant hp T before bM bS
  exact consecutive_offers hp chart sep op i code K before after
    (Aligned.filter_gap hp T before after preDs suffix adj)
    U V (Nat.le_of_lt bound) N N' node one inside F canon

/-- The accepted DigitSweep on the exact filtered actual tape.
Only per-packet numerical health, the fixed decoded instruction and
canonical width of the digit result are required; adjacency and
carry equality follow from the authenticated raw tape. The final
token is the actual last significant departure's local result (before
any subsequent terminal padding). -/
theorem filtered_sweep {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op k l : Nat} {w : List (Fin n)} {ds : List D}
    (T : Aligned hp base (fun j => S.getD j fall) len op x k w l ds)
    (i : Nat) (code : Code) (K : get i=some code) :
    let visits := ds.filter (significant hp base (fun j => S.getD j fall))
    let digit := fun d : D => physicalDigit (geom hp d) (byte d) i code d.offer
    (∀ d∈visits, Numeric d.offer ∧ nodeOf d.offer.opcode.toNat=some i ∧ (digit d).2.fault=0) →
    (∀ d∈visits, ∀ g j, BStarLongCommand.bind g j (.forward (digit d).2)=.forward (digit d).2) →
    ∃ tokens : Nat → Payload,
      (∀ j : Fin visits.length, tokens j.val=visits[j.val].offer) ∧
      BStarPhysicalWordSem.DigitSweep
        (fun j : Fin visits.length => geom hp visits[j.val])
        (fun j : Fin visits.length => byte visits[j.val])
        (fun j : Fin visits.length => (digit visits[j.val]).1.apply (byte visits[j.val]))
        i code tokens := by
  dsimp only
  intro numeric canonical
  let visits := ds.filter (significant hp base (fun j => S.getD j fall))
  let digit := fun d : D => physicalDigit (geom hp d) (byte d) i code d.offer
  let terminal : Payload :=
    if H : 0<visits.length then (digit (visits[visits.length - 1]'(by omega))).2 else ⟨1,0,0,0,0⟩
  let tokens := fun j => if H : j<visits.length then visits[j].offer else terminal
  have val (j : Nat) (J : j<visits.length) : tokens j=visits[j].offer := by
    unfold tokens
    rw [dif_pos J]
  refine ⟨tokens,fun j => val j.val j.isLt,?_⟩
  constructor
  intro j
  dsimp only
  have q := val j.val j.isLt
  rw [q]
  refine Prod.ext ?_ ?_
  · rfl
  change (digit visits[j.val]).2=tokens (j.val+1)
  by_cases J : j.val+1<visits.length
  · rw [val _ J]
    have cut : visits=visits.take j.val++visits[j.val]::visits[j.val+1]::visits.drop (j.val+2) := by
      have E := List.take_append_drop j.val visits
      rw [List.drop_eq_getElem_cons j.isLt,List.drop_eq_getElem_cons J] at E
      exact E.symm
    have bm : visits[j.val]∈visits := List.getElem_mem _
    have am : visits[j.val+1]∈visits := List.getElem_mem _
    exact next_significant_offer hp chart sep T (visits.take j.val) (visits.drop (j.val+2))
      visits[j.val] visits[j.val+1] cut i code K
      (numeric _ bm).1 (numeric _ am).1 (numeric _ bm).2.1
      (numeric _ bm).2.2 (canonical _ bm)
  · unfold tokens
    rw [dif_neg J]
    unfold terminal
    have J0 : j.val<visits.length := j.isLt
    rw [dif_pos (by omega)]
    have atLast : visits.length-1=j.val := by omega
    have V : visits[j.val] = visits[visits.length - 1]'(by omega) := by
      exact getElem_congr_idx atLast.symm
    exact congrArg (fun v => (digit v).2) V

end L4.BStarNumericConsecutive

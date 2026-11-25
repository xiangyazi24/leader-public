import Leader.L4.BStarNumericFrame
import Leader.L4.BStarNumericConsecutive

namespace L4.BStarNumericWordFrame
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongRouting
open BStarAcquireVisitOrder BStarAcquireForwardTrace BStarH6WordChart BStarLongRegisters
open BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail BStarSeparatorControl
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetSchedule
open BStarNumericFrame BStarLongArithmetic

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

private theorem centre_old {x : X} {e : Fin n} (C : CommandClaim) (u : Payload)
    (sel : (C,.advance u)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (K : C.source.occurrence.val=1) :
    ∃ q, atCursor x (e,1)=.forward q := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have M : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have H : C.source=L 1 := by rw [center_of g C M K]; rfl
  obtain ⟨q,Q⟩ := BStarClearanceCommandFrame.advance_origin g raw C u sel
  unfold bound at Q
  rw [H] at Q
  change BStarLongCommand.bind g.1 1 (atSite (x e).long 1)=_ at Q
  cases E : atSite (x e).long 1 with
  | forward p => exact ⟨p,E⟩
  | empty => rw [E] at Q; contradiction
  | trail => rw [E] at Q; contradiction
  | reply p =>
    rw [E] at Q
    unfold BStarLongCommand.bind at Q
    dsimp only at Q
    split at Q
    · contradiction
    · split at Q <;> contradiction

/-- If the physical K1 is not an old forward, the entire numeric
file at that site survives this literal ring mark, even if there
are unrelated actual advances. -/
theorem step_no_forward (x : X) (e i : Fin n) (j : Nat)
    (sep : e≠rightNeighbor e) (idle : ¬anyTag.F (atCursor x (i,1))) :
    (numeric j).read (step x e i).long=(numeric j).read (x i).long := by
  apply step_other hp x e i j sep
  intro E C u sel K
  subst i
  exact (idle (centre_old hp C u sel K)).elim

def Past (k : Nat) : Cursor → Prop
  | .out j => k<j
  | .back _ => True

private theorem past_event {x : X} {addr : Nat → Pos n} {len op k : Nat}
    {e : Fin n} {z d : Cursor} (P : Past k z)
    (E : Event hp addr len x e (.busy op z) (.busy op d)) :
    Past k d := by
  cases E with
  | arrived_hold _ => exact True.intro
  | transit _ _ _ _ seen =>
    cases seen with
    | cons _ _ A _ rest =>
      cases rest
      cases A
      · exact P
      · unfold Past at *; omega
      · exact True.intro
      · exact True.intro

private theorem past_empty {base x : X} {addr : Nat → Pos n} {len op k : Nat} {z : Cursor}
    (I : Current hp base addr len x (.busy op z)) (P : Past k z) (hk : k≤len) :
    ¬anyTag.F (project addr x k) := by
  intro F
  cases z with
  | back j => exact (BStarOwnerControlHistory.pointed_backward_no_forward _ len j I.2.1 k hk F).elim
  | out j =>
    have E := (BStarOwnerControlHistory.pointed_unique_forward _ len j I.2.1 I.2.2 k hk).mp F
    exact (Nat.ne_of_lt P E).elim

/-- Once the busy cursor has left a physical K1, all numeric fields
there are preserved across every further mark of the same busy tour.
This rules out foreign writes from their actual source read, without
assuming the other scheduled interactions are silent. -/
theorem busy_past {base x : X} {addr : Nat → Pos n} {len op k : Nat}
    {z d : Cursor} {w : List (Fin n)} (P : BusyOnly hp base addr len op x z w d)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (hk : k≤len) (i : Fin n) (A : addr k=(i,1))
    (passed : Past k z) (j : Nat) :
    (numeric j).read ((BStarResetSchedule.run step x w) i).long=(numeric j).read (x i).long := by
  induction P with
  | nil _ => rfl
  | @cons x z d fin e w I E tail ih =>
    have NF := past_empty hp I passed hk
    have q : ¬anyTag.F (atCursor x (i,1)) := by
      change ¬anyTag.F (atCursor x (addr k)) at NF
      rwa [A] at NF
    exact (ih (past_event hp passed E)).trans (step_no_forward hp x e i j (sep e) q)

private theorem centre_trail {x : X} {e : Fin n}
    (he : e≠rightNeighbor e) (C : CommandClaim) (u : Payload)
    (sel : (C,.advance u)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (K : C.source.occurrence.val=1) :
    atCursor (step x e) (e,1)=.trail := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have hm : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have CK := center_of g C hm K
  have src : C.source=L 1 := by rw [CK]; rfl
  let d : AtK := R (if g.2.axes.h6 then 2 else 1)
  have dst : C.destination=some d := by rw [CK]; rfl
  have ne := (BStarAcquireReturn.link_shape g C d hm dst).1
  have row := (BStarClearanceForward.move_lands g raw C u d dst sel (Ne.symm ne)).1
  let pair := (x e,x (rightNeighbor e))
  have J := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp pair C.source
      (fun hr _ => (by rw [src] at hr; contradiction))
  rw [show (e,(1 : Fin 11))=address e C.source by rw [src]; rfl,
    ←new_read B x e he C.source,J]
  change decode (readRaw (patchPair (longWork g raw) raw) C.source)=_
  rw [row,decode_encode]

private theorem aligned_start {base : X} {addr : Nat → Pos n} {len op : Nat}
    {x : X} {k w l ds} (T : BStarNumericConsecutive.Aligned hp base addr len op x k w l ds) :
    Current hp base addr len x (.busy op (.out k)) :=
  busy_start hp (BStarNumericConsecutive.Aligned.busy hp T)

/-- Before the chosen K1 visit, an actual outward tape ending no
later than that slot preserves all its old numeric fields. Even a
possible last stay at that exact index cannot conceal a departure. -/
theorem aligned_before {base x : X} {addr : Nat → Pos n} {len op ku : Nat}
    {k w l ds} (T : BStarNumericConsecutive.Aligned hp base addr len op x k w l ds)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (hu : ku≤len) (limit : l≤ku) (i : Fin n) (A : addr ku=(i,1)) (reg : Nat) :
    (numeric reg).read ((BStarResetSchedule.run step x w) i).long=
      (numeric reg).read (x i).long := by
  induction T with
  | nil _ => rfl
  | @stay x k e w l ds I E tail ih =>
    have R := step_other hp x e i reg (sep e)
    have eq : (numeric reg).read (step x e i).long=(numeric reg).read (x i).long := by
      apply R
      rintro r C u sel K
      subst i
      have F := centre_old hp C u sel K
      have Q : anyTag.F (project addr x ku) := by change anyTag.F (atCursor x (addr ku)); rwa [A]
      have idx := (BStarOwnerControlHistory.pointed_unique_forward _ len k I.2.1 I.2.2 ku hu).mp Q
      have F' := (aligned_start hp tail).2.1.2.1
      change anyTag.F (atCursor (step x e) (addr k)) at F'
      rw [←idx,A,centre_trail hp (sep e) C u sel K] at F'
      exact (BStarSeparatorParked.forward_not_trail F').elim
    exact (ih limit).trans eq
  | @hop x k e w l ds C a p I E V tail ih =>
    have mono := (BStarNumericChronology.OutTape.indices hp
      (BStarNumericConsecutive.Aligned.to_tape hp tail)).1
    have Q : ¬anyTag.F (atCursor x (i,1)) := by
      intro F
      have M : anyTag.F (project addr x ku) := by change anyTag.F (atCursor x (addr ku)); rwa [A]
      have E := (BStarOwnerControlHistory.pointed_unique_forward _ len k I.2.1 I.2.2 ku hu).mp M
      omega
    exact (ih limit).trans (step_no_forward hp x e i reg (sep e) Q)

open BStarNumericChronology BStarNumericConsecutive BStarNumericCarry
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
  (r:=r) (c:=c) (p:=p) (c₁:=c₁)

/-- Split the actual raw tape at the selected record, retaining aligned
prefix and suffix with their precise states and forward cursor indices. -/
theorem split_record {base x : X} {addr : Nat → Pos n} {len op k l : Nat}
    {w : List (Fin n)} {ds : List D}
    (T : Aligned hp base addr len op x k w l ds) (d : D) (M : d∈ds) :
    ∃ pre post before after, w=pre++d.mark::post ∧
      Aligned hp base addr len op x k pre d.index before ∧
      BStarResetSchedule.run step x pre=d.old ∧
      Aligned hp base addr len op (step d.old d.mark) (d.index+1) post l after := by
  induction T with
  | nil _ => contradiction
  | stay I E _ ih =>
    obtain ⟨pre,post,bef,aft,W,P,R,Q⟩ := ih M
    exact ⟨_::pre,post,bef,aft,congrArg (List.cons _) W,.stay I E P,R,Q⟩
  | @hop x k e w l ds C a p I E V tail ih =>
    rcases List.mem_cons.mp M with eq|rest
    · subst d
      exact ⟨[],w,[],ds,rfl,.nil I,rfl,tail⟩
    · obtain ⟨pre,post,bef,aft,W,P,R,Q⟩ := ih rest
      exact ⟨e::pre,post,_::bef,aft,congrArg (List.cons e) W,.hop I E V P,R,Q⟩

/-- Full live ring field bridge for a significant actual visit:
its old numeric input projection is the tour's initial projection;
its exact selected arithmetic write is the tour's final projection.
Foreign, stay and padding marks in both intervals are real old-pair
updates and require no external protection premise. -/
theorem record_to_word {base x : X} {addr : Nat → Pos n} {len op k l : Nat}
    {w : List (Fin n)} {ds : List D}
    (T : Aligned hp base addr len op x k w l ds) (d : D) (M : d∈ds)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (sig : significant hp base addr d=true)
    (i : Nat) (code : L4.Compiler.Native.Code) (K : BStarLongArithmetic.get i=some code)
    (N : Numeric d.offer) (node : nodeOf d.offer.opcode.toNat=some i)
    (healthy : (physicalDigit (geom hp d) (byte d) i code d.offer).2.fault=0)
    (j : Nat) :
    (numeric j).read (byte d)=(numeric j).read (x d.mark).long ∧
    (numeric j).read ((BStarResetSchedule.run step x w) d.mark).long=
      (numeric j).read ((physicalDigit (geom hp d) (byte d) i code d.offer).1.apply (byte d)) := by
  obtain ⟨pre,post,_,_,W,P,R,Q⟩ := split_record hp T d M
  obtain ⟨V,_,bound⟩ := Aligned.record_facts hp T d M
  obtain ⟨one,inside⟩ := Aligned.record_significant hp T d M sig
  let g := oldPair B d.old d.mark
  let raw : Pair (BitVec LW) := ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)
  obtain ⟨sel,_,src,_⟩ := V
  have hm : d.claim∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have C : d.claim.source=L 1 := by rw [center_of g d.claim hm one]; rfl
  have slot : addr d.index=(d.mark,1) := src.trans (by rw [C]; rfl)
  have G : geom hp d=g.1 := by unfold geom; rw [C]; rfl
  have B0 : byte d=raw.1 := by unfold byte; rw [C]; rfl
  have Hl : d.index≤len := Nat.le_of_lt bound
  have old := aligned_before hp P sep Hl (Nat.le_refl _) d.mark slot j
  rw [R] at old
  constructor
  · rw [B0]
    exact old
  · have frame := busy_past hp (Aligned.busy hp Q) sep Hl d.mark slot
      (show Past d.index (.out (d.index+1)) from Nat.lt_succ_self _) j
    have A := step_digit hp d.old d.mark d.claim d.offer i code j sel one N node K
      (G ▸ inside) (by rwa [←G,←B0])
    rw [W,BStarResetSchedule.run_append]
    change (numeric j).read ((BStarResetSchedule.run step (step (BStarResetSchedule.run step x pre)
       d.mark) post) d.mark).long=_
    rw [R]
    exact frame.trans (A.trans (by rw [G,B0]))

open BStarAcquireLiteralChain BStarResetChartTouch

/-- Accepted digit sweep plus a projection to the actual live
initial and final ring words, simultaneously for every numeric
register. Other raw labels within this owner tour are framed by
the actual write once at each selected significant slot. -/
theorem live_sweep {base x : X} {hh : ∃ z,oldH6 B base z=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    {op k l : Nat} {w : List (Fin n)} {ds : List D}
    (chart : Chart hp base hh o S len fall)
    (T : Aligned hp base (fun j => S.getD j fall) len op x k w l ds)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (i : Nat) (code : L4.Compiler.Native.Code)
    (K : BStarLongArithmetic.get i=some code) :
    let visits := ds.filter (significant hp base (fun j => S.getD j fall))
    let digit := fun d : D => physicalDigit (geom hp d) (byte d) i code d.offer
    let updated := fun d : D => (digit d).1.apply (byte d)
    (∀ d∈visits, Numeric d.offer ∧ nodeOf d.offer.opcode.toNat=some i ∧ (digit d).2.fault=0) →
    (∀ d∈visits, ∀ g j, BStarLongCommand.bind g j (.forward (digit d).2)=.forward (digit d).2) →
    ∃ tokens : Nat → Payload,
      (∀ j : Fin visits.length, tokens j.val=visits[j.val].offer) ∧
      BStarPhysicalWordSem.DigitSweep
        (fun j : Fin visits.length => geom hp visits[j.val])
        (fun j : Fin visits.length => byte visits[j.val])
        (fun j : Fin visits.length => updated visits[j.val]) i code tokens ∧
      ∀ j : Fin visits.length, ∀ reg,
        (numeric reg).read (byte visits[j.val])=(numeric reg).read (x visits[j.val].mark).long ∧
        (numeric reg).read (updated visits[j.val]) =
          (numeric reg).read ((BStarResetSchedule.run step x w) visits[j.val].mark).long := by
  dsimp only
  intro numeric canonical
  obtain ⟨tokens,E,H⟩ := filtered_sweep hp chart sep T i code K numeric canonical
  refine ⟨tokens,E,H,?_⟩
  intro j reg
  have M := List.getElem_mem (l:=ds.filter (significant hp base (fun j => S.getD j fall))) j.isLt
  obtain ⟨Md,Ms⟩ := List.mem_filter.mp M
  obtain ⟨N,N0,N1⟩ := numeric _ M
  have P := record_to_word hp T _ Md sep Ms i code K N N0 N1 reg
  exact ⟨P.1,P.2.symm⟩

end L4.BStarNumericWordFrame

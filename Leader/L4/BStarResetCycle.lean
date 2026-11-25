import Leader.L4.BStarResetChartService
import Leader.L4.BStarResetChartNomination
import Leader.L4.BStarResetConsumedClean

/-! Clean reset service in a literal ring after an actual issue, under
a fixed lower layout. This is not arbitrary-entry reachability. -/
namespace L4.BStarResetCycle
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireAnchors BStarAcquireLiteralChain BStarAcquireForwardTrace
open BStarLongFixedRouting BStarResetChartTouch BStarResetChartService
open BStarResetMarkAdapter BStarResetRailRing BStarResetSchedule
open BStarSeparatingRail BStarSeparatingProgress BStarAcquireWaitControl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem issue_control (op arg : Nat) (w : BitVec LW) :
    control ((issued op arg).apply w)=(2,ctrlOp.read w) := by
  unfold issued
  have E (w : BitVec LW) : control
      ((setToken 0 (forward op arg)).apply ((ctrlPhase.assign 2).apply w))=(2,ctrlOp.read w) := by
    unfold BStarAcquireWaitControl.control setToken
    rw [Field.read_other_assign _ _ _ _ (.inr (by decide)),Field.read_assign,
        Field.read_other_assign _ _ _ _ (.inr (by decide)),
        Field.read_other_assign _ _ _ _ (.inl (by decide))]
  split
  · rw [Patch.compose_apply,Patch.compose_apply,E]
    unfold clearFile
    rw [Field.read_other_assign _ _ _ _ (.inr (by decide))]
  · rw [Patch.compose_apply,E]

theorem genuine_wait (x : XX) (e : Fin n) (he : e≠rightNeighbor e)
    (op : Nat) (ho : op<3)
    (head : oldH6 B x (rightNeighbor e)=true)
    (oldP : (ctrlPhase.read (x (rightNeighbor e)).long).toNat=1)
    (oldO : (ctrlOp.read (x (rightNeighbor e)).long).toNat=op) :
    let y := AllSizeS1Geometry.step B x e
    atCursor y (rightNeighbor e,0)=.forward (BStarResetTaggedRows.resetPayload op) ∧
    LongDoorGuard.valid manifest (y (rightNeighbor e)).long=true ∧
    (ctrlPhase.read (y (rightNeighbor e)).long).toNat=2 ∧
    (ctrlOp.read (y (rightNeighbor e)).long).toNat=op := by
  dsimp only
  let raw : BitVec LW := (x (rightNeighbor e)).long
  have V := BStarResetDoor.valid_of raw oldP oldO (.inl rfl) ho
  have Q := BStarResetDoor.joined_reset_issue k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) op ho head oldP oldO
  have D := BStarResetDoor.phase_control_write k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) (issued op 0) (fun t => (2,t.2)) head V
    (BStarResetTaggedRows.reset_issue_decision raw _ op V oldP oldO
      (show op=0 ∨ op=1 ∨ op=2 from by omega)) (issue_control op 0)
  let w : BitVec LW := (AllSizeS1Geometry.step B x e (rightNeighbor e)).long
  have E : w=(largePair B (x e,x (rightNeighbor e))).2.long := by
    simp [w,AllSizeS1Geometry.step,Ne.symm he]
    rfl
  have ph : (ctrlPhase.read w).toNat=2 :=
    (congrArg (fun t => (ctrlPhase.read t).toNat) E).trans
      (congrArg (fun t : BitVec 2 × BitVec 9 => t.1.toNat) D)
  have code : (ctrlOp.read w).toNat=op :=
    (congrArg (fun t => (ctrlOp.read t).toNat) E).trans
      ((congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat) D).trans oldO)
  have hpv := BStarResetDoor.valid_of w ph code (.inr rfl) ho
  exact ⟨(congrArg (fun t => atSite t 0) E).trans (congrArg Prod.fst Q),hpv,ph,code⟩

theorem fixed_nominations {base : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true) :
    ∃ eOf : Label → Fin n,
      (∀ x : XX, (∀ i, Layout B base i=Layout B x i) → ∀ j<len,
        onLink hp x (eOf (.link j)) (fun j => S.getD j fallback) j) ∧
      (∀ x : XX, (∀ i, Layout B base i=Layout B x i) →
        onTerminal hp x (eOf .terminal) (fun j => S.getD j fallback) len) := by
  classical
  have nominate := BStarResetChartNomination.nominate hp C head cont
  let eOf : Label → Fin n
    | .terminal => Classical.choose (nominate len (Nat.le_refl _))
    | .link j => if J : j<len then Classical.choose (nominate j (Nat.le_of_lt J))
        else (S.getD 0 fallback).1
  refine ⟨eOf,?_,?_⟩
  · intro x same j J
    let edge := Classical.choose (nominate j (Nat.le_of_lt J))
    have T : (if j<len then Label.link j else Label.terminal)∈labels hp x edge (fun j => S.getD j fallback) len :=
      Classical.choose_spec (nominate j (Nat.le_of_lt J)) x same
    have U : Label.link j∈labels hp x edge (fun j => S.getD j fallback) len := by
      rw [if_pos J] at T
      exact T
    have K : eOf (.link j)=edge := by simp [eOf,edge,J]
    rw [K]
    exact ((mem_link hp x edge _ len j).mp U).2
  · intro x same
    let edge := Classical.choose (nominate len (Nat.le_refl _))
    have T : (if len<len then Label.link len else Label.terminal)∈labels hp x edge (fun j => S.getD j fallback) len :=
      Classical.choose_spec (nominate len (Nat.le_refl _)) x same
    rw [if_neg (Nat.lt_irrefl _)] at T
    exact (mem_terminal hp x edge _ len).mp T

theorem chart_adapter {base : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (geo : ∀ x : XX, (∀ i, Layout B base i=Layout B x i) →
       ∀ e i, Layout B base i=Layout B (AllSizeS1Geometry.step B x e) i)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (op : Nat) (ho : op<3) :
    ∃ eOf, Adapter (AllSizeS1Geometry.step B) (project (fun j => S.getD j fallback))
      (resetTag op) len (Waiting hp base (S.getD 0 fallback).1 op) eOf := by
  obtain ⟨e,L,T⟩ := fixed_nominations hp C head cont
  exact ⟨e,adapter hp C geo distinct op ho e L T⟩

/-- From a genuine literal issue, sweeps of all directed marks
force this exact reset (or canonical fault) back to its source before
the attached door service mark. The raw suffix at issue is unrestricted. -/
theorem genuine_reset_return {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (geo : ∀ x : XX, (∀ i, Layout B base i=Layout B x i) →
       ∀ e i, Layout B base i=Layout B (AllSizeS1Geometry.step B x e) i)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (same : ∀ i, Layout B base i=Layout B x i)
    (op : Nat) (ho : op<3)
    (oldP : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=1)
    (oldO : (ctrlOp.read (x (S.getD 0 fallback).1).long).toNat=op) :
    let root := (S.getD 0 fallback).1
    let door := RearTrace.predecessor root
    let step := AllSizeS1Geometry.step (n:=n) B
    let y := step x door
    let track : XX → BStarSeparatingRail.Rail := project (fun j => S.getD j fallback)
    ∃ pre post,
      sweeps n (2*len+1)=pre++post ∧ (pre++[door]).length≤n*(2*len+1)+1 ∧
      Seen step track (resetTag op) len y (.out 0) pre (.back 0) ∧
      Clean track (resetTag op) len (BStarResetSchedule.run step y pre) ∧
      let old := BStarResetSchedule.run step y pre
      let out := BStarResetSchedule.run step y (pre++[door])
      track out 0=.empty ∧ (ctrlPhase.read (out root).long)=1 ∧
      (track old 0=finish (BStarResetTaggedRows.resetPayload op) →
        (ctrlOp.read (out root).long)=BitVec.ofNat 9 (op+1)) := by
  dsimp only
  let root := (S.getD 0 fallback).1
  let door := RearTrace.predecessor root
  let step := AllSizeS1Geometry.step (n:=n) B
  let track : XX → BStarSeparatingRail.Rail := project (fun j => S.getD j fallback)
  have R : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C same
  have hdr : oldH6 B x (rightNeighbor door)=true := by rw [R]; exact H
  have E := genuine_wait hp x door (distinct door) op ho hdr
    (show (ctrlPhase.read (x (rightNeighbor door)).long).toNat=1 by rw [R]; exact oldP)
    (show (ctrlOp.read (x (rightNeighbor door)).long).toNat=op by rw [R]; exact oldO)
  rw [R] at E
  let y := step x door
  have inv : Waiting hp base root op y := ⟨geo x same door,E.2.1,E.2.2⟩
  have T {z : XX} : track z 0=atCursor z (root,0) :=
    congrArg (atCursor z) (Prod.ext rfl K)
  have F : (resetTag op).F (track y 0) :=
    ⟨BStarResetTaggedRows.resetPayload op,.inl rfl,T.trans E.1⟩
  obtain ⟨eOf,A⟩ := chart_adapter hp C geo distinct head cont op ho
  let Handled (a b : XX) := track b 0=.empty ∧ (ctrlPhase.read (b root).long)=1 ∧
    (track a 0=finish (BStarResetTaggedRows.resetPayload op) →
      (ctrlOp.read (b root).long)=BitVec.ofNat 9 (op+1))
  have handle (a : XX) (W : Waiting hp base root op a)
      (L : Clean track (resetTag op) len a) : Handled a (step a door) := by
    have rightH : oldH6 B a (rightNeighbor door)=true := by
      rw [R]
      exact (root_header hp C W.1).1
    have q := source_service hp a door (distinct door) op ho rightH
      (by rw [R]; exact W.2.1)
      (by rw [R]; exact W.2.2.1)
      (by rw [R]; exact W.2.2.2)
      (by rw [R,←T]; exact L.1)
    dsimp only at q
    rw [R] at q
    unfold Handled
    exact ⟨T.trans q.1,q.2.1,fun h => q.2.2 (T.symm.trans h)⟩
  exact reset_prefix_then_door A y inv F door Handled handle

/-- Version over a closed lower predicate, not all states with the
same observable layout. The consuming mark also preserves every
already clean suffix slot. -/
theorem genuine_reset_return_on {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (Q : XX → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (AllSizeS1Geometry.step B x e))
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (init : Q x)
    (op : Nat) (ho : op<3)
    (oldP : (ctrlPhase.read (x (S.getD 0 fallback).1).long).toNat=1)
    (oldO : (ctrlOp.read (x (S.getD 0 fallback).1).long).toNat=op) :
    let root := (S.getD 0 fallback).1
    let door := RearTrace.predecessor root
    let step := AllSizeS1Geometry.step (n:=n) B
    let y := step x door
    let track : XX → BStarSeparatingRail.Rail := project (fun j => S.getD j fallback)
    ∃ pre post,
      sweeps n (2*len+1)=pre++post ∧ (pre++[door]).length≤n*(2*len+1)+1 ∧
      Seen step track (resetTag op) len y (.out 0) pre (.back 0) ∧
      Clean track (resetTag op) len (BStarResetSchedule.run step y pre) ∧
      let old := BStarResetSchedule.run step y pre
      let out := BStarResetSchedule.run step y (pre++[door])
      (∀ j≤len, track out j=.empty) ∧ Q out ∧ (ctrlPhase.read (out root).long)=1 ∧
      (track old 0=finish (BStarResetTaggedRows.resetPayload op) →
        (ctrlOp.read (out root).long)=BitVec.ofNat 9 (op+1)) := by
  dsimp only
  let root := (S.getD 0 fallback).1
  let door := RearTrace.predecessor root
  let step := AllSizeS1Geometry.step (n:=n) B
  let track : XX → BStarSeparatingRail.Rail := project (fun j => S.getD j fallback)
  have R : rightNeighbor door=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C (fiber x init)
  have hdr : oldH6 B x (rightNeighbor door)=true := by rw [R]; exact H
  have E := genuine_wait hp x door (distinct door) op ho hdr
    (show (ctrlPhase.read (x (rightNeighbor door)).long).toNat=1 by rw [R]; exact oldP)
    (show (ctrlOp.read (x (rightNeighbor door)).long).toNat=op by rw [R]; exact oldO)
  rw [R] at E
  let y := step x door
  have yQ : Q y := closed x init door
  have inv : Q y ∧ Waiting hp base root op y := ⟨yQ,fiber y yQ,E.2.1,E.2.2⟩
  have T {z : XX} : track z 0=atCursor z (root,0) :=
    congrArg (atCursor z) (Prod.ext rfl K)
  have F : (resetTag op).F (track y 0) :=
    ⟨BStarResetTaggedRows.resetPayload op,.inl rfl,T.trans E.1⟩
  obtain ⟨eOf,L,Tm⟩ := fixed_nominations hp C head cont
  have A := adapter_on hp C Q fiber closed distinct op ho eOf L Tm
  let Handled (a b : XX) := (∀ j≤len, track b j=.empty) ∧ Q b ∧
    (ctrlPhase.read (b root).long)=1 ∧
    (track a 0=finish (BStarResetTaggedRows.resetPayload op) →
      (ctrlOp.read (b root).long)=BitVec.ofNat 9 (op+1))
  have handle (a : XX) (W : Q a ∧ Waiting hp base root op a)
      (L : Clean track (resetTag op) len a) : Handled a (step a door) := by
    obtain ⟨empty,ph,opn⟩ := BStarResetConsumedClean.consumed_clean hp C op ho W.2 L distinct
    exact ⟨empty,closed a W.1 door,ph,opn⟩
  exact reset_prefix_then_door A y inv F door Handled handle

#print axioms genuine_reset_return_on
#print axioms genuine_reset_return
#print axioms genuine_wait
#print axioms chart_adapter
end L4.BStarResetCycle

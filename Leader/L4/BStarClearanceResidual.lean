import Leader.L4.BStarClearanceAttempt
import Leader.L4.BStarClearanceBadIssue
import Leader.L4.BStarControllerLoop

namespace L4.BStarClearanceResidual
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetChartService BStarResetSchedule BStarSeparatingRail
open BStarSeparatorControl BStarClearanceSource BStarClearancePhysical BStarClearanceOffset
open BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

theorem legal_issue (w : BitVec LW) (P : (ctrlPhase.read w).toNat=1)
    (O : (ctrlOp.read w).toNat<413) : Issue w := by
  refine ⟨?_,P⟩
  change ((((ctrlPhase.read w).toNat==1)||((ctrlPhase.read w).toNat==2)) &&
    decide ((ctrlOp.read w).toNat<413))=true
  simp [P,O]

theorem issue_range {w : BitVec LW} (I : Issue w) : (ctrlOp.read w).toNat<413 := by
  have V := I.1
  change ((((ctrlPhase.read w).toNat==1)||((ctrlPhase.read w).toNat==2)) &&
    decide ((ctrlOp.read w).toNat<413))=true at V
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp V).2

structure Boundary (Q : X → Prop) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (addr : Nat → Pos n) (len : Nat) (x : X) : Prop where
  lower : Q x
  offset : correct h hh 5 x
  issue : Issue (x (addr 0).1).long
  clean : ∀ j≤len, project addr x j=.empty

/-- A clean actual ISSUE boundary, not numeric zero in inherited WAIT,
is the invariant of the residual-program loop. The finite bound counts
controller attempts only, not physical marks. -/
theorem to_issue_zero {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (same : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) :
    let addr := fun j => S.getD j fall
    let pc := fun x : X => (ctrlOp.read (x (addr 0).1).long).toNat
    let Inv := Boundary Q (oldH6 B base) hh addr len
    Inv x → ∃ k w, k≤412 ∧
      BStarControllerLoop.FiniteAttempts step Inv pc x (BStarResetSchedule.run step x w) k w ∧
      Inv (BStarResetSchedule.run step x w) ∧ pc (BStarResetSchedule.run step x w)=0 := by
  dsimp only
  intro init
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let e := RearTrace.predecessor root
  let pc := fun x : X => (ctrlOp.read (x root).long).toNat
  let Inv := Boundary Q (oldH6 B base) hh addr len
  have attempt (z : X) (J : Inv z) (_ : pc z≠0) :
      ∃ w : List (Fin n), let y := BStarResetSchedule.run step z w
        Inv y ∧ (pc y=0 ∨ pc z<pc y) := by
    rcases BStarClearanceAttempt.from_issue hp chart sep head cont Q closed same heads conts
      cb J.lower J.offset J.issue with A|⟨a,w,good⟩
    · obtain ⟨bad,_,I,C⟩ := A
      obtain ⟨E,V,P⟩ := BStarClearanceBadIssue.restart hp chart (same z J.lower) sep J.clean J.issue bad
      exact ⟨[e],⟨I,C,V,E⟩,.inl P⟩
    · obtain ⟨_,_,_,_,_,I,C,E,V,next,A,P⟩ := good
      have bound : next<413 := A.elim (fun h => h.symm ▸ (by decide : (0 : Nat)<413)) And.right
      let r := BStarResetSchedule.run step (step z e) w
      let y := step r e
      have J' : Inv y := ⟨I,C,legal_issue (y root).long V (P.symm ▸ bound),E⟩
      refine ⟨e::(w++[e]),?_⟩
      have eq : BStarResetSchedule.run step z (e::(w++[e]))=y := by
        change BStarResetSchedule.run step (step z e) (w++[e])=y
        rw [BStarResetSchedule.run_append]
        rfl
      dsimp only
      rw [eq]
      have PC : pc y=next := P
      refine ⟨J',?_⟩
      change pc y=0 ∨ pc z<pc y
      rw [PC]
      exact A.imp id And.left
  obtain ⟨k,w,_,K,T,I,Z⟩ :=
    @BStarControllerLoop.finite_to_reset X n (AllSizeS1Geometry.step B) Inv pc
      (fun _ h => issue_range h.issue) attempt x init
  exact ⟨k,w,K,T,I,Z⟩

#print axioms to_issue_zero
end L4.BStarClearanceResidual

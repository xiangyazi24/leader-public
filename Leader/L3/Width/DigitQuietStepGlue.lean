import Leader.L3.Width.DigitQuietStepSplit
import Leader.L3.Width.DigitQuietSafe

/-!
# The quiet class: the views after one letter

The interface between the machine (`phiD ring S e`) and the lane views used by the closure proofs:

* `resolved_betas`: under `QWord` the resolved betas of the letter are the old ones;
* `glue_left`, `glue_right`: the lane fields of the views of the two endpoints after the letter are
  `laneRow` of the old views, and their marker (`beta`) is unchanged;
* `glue_other`: a site off the letter keeps its record, hence its view.

The view of site `i` in lane `lane` is `digitEndpointView lane S i`, and `view ring root S lane k` is
this at `digitSite ring root k`.

Consumer: every closure lemma of `QuietStepLaw` (`WidthDigitQuietStep*`).
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- Under `QWord` the resolved betas of the letter are the old betas.  Consumer: `glue_left`,
`glue_right`. -/
theorem resolved_betas (ring : DirectedRing n) (S : Fin n → ProjD c)
    (hW : QWord ring (wordProjection S)) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta ∧
    (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta := by
  have h1 := qword_visible_fixed ring (wordProjection S) hW e e
  have h2 := qword_visible_fixed ring (wordProjection S) hW e (ring.rightNeighbor e)
  have e1 : (phiW ring (wordProjection S) e) e =
      (pairW (S e).word (S (ring.rightNeighbor e)).word).1 := by
    simp [phiW, projectedEdge, wordProjection]
  have e2 : (phiW ring (wordProjection S) e) (ring.rightNeighbor e) =
      (pairW (S e).word (S (ring.rightNeighbor e)).word).2 := by
    simp [phiW, projectedEdge, wordProjection, hne]
  unfold wordVisible at h1 h2
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨congrArg (fun z : Bool × Bool => z.2) h1, congrArg (fun z : Bool × Bool => z.2) h2⟩

/-- **The left endpoint after a letter**: its lane fields are `laneRow` of the old views and its
marker is unchanged.  Consumer: the closure proofs. -/
theorem glue_left (ring : DirectedRing n) (S : Fin n → ProjD c)
    (hW : QWord ring (wordProjection S)) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (lane : DigitLane) :
    LaneFieldsEq (digitEndpointView lane (phiD ring S e) e)
      (laneRow lane (digitEndpointView lane S e)
        (digitEndpointView lane S (ring.rightNeighbor e))).1 ∧
    (digitEndpointView lane (phiD ring S e) e).marker = (digitEndpointView lane S e).marker := by
  obtain ⟨hbX, hbY⟩ := resolved_betas ring S hW e hne
  have hc := (laneRow_correct lane (S e) (S (ring.rightNeighbor e)) hbX hbY).1
  have hl := phiD_at_left ring S e
  refine ⟨?_, ?_⟩
  · simp only [digitEndpointView, hl]
    cases lane <;> exact hc
  · simp only [digitEndpointView, hl]
    cases lane <;> exact hbX

/-- **The right endpoint after a letter.**  Consumer: the closure proofs. -/
theorem glue_right (ring : DirectedRing n) (S : Fin n → ProjD c)
    (hW : QWord ring (wordProjection S)) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (lane : DigitLane) :
    LaneFieldsEq (digitEndpointView lane (phiD ring S e) (ring.rightNeighbor e))
      (laneRow lane (digitEndpointView lane S e)
        (digitEndpointView lane S (ring.rightNeighbor e))).2 ∧
    (digitEndpointView lane (phiD ring S e) (ring.rightNeighbor e)).marker =
      (digitEndpointView lane S (ring.rightNeighbor e)).marker := by
  obtain ⟨hbX, hbY⟩ := resolved_betas ring S hW e hne
  have hc := (laneRow_correct lane (S e) (S (ring.rightNeighbor e)) hbX hbY).2
  have hr := phiD_at_right ring S e hne
  refine ⟨?_, ?_⟩
  · simp only [digitEndpointView, hr]
    cases lane <;> exact hc
  · simp only [digitEndpointView, hr]
    cases lane <;> exact hbY

/-- A site off the letter keeps its view.  Consumer: the closure proofs. -/
theorem glue_other (ring : DirectedRing n) (S : Fin n → ProjD c) (e i : Fin n) (hie : i ≠ e)
    (hij : i ≠ ring.rightNeighbor e) (lane : DigitLane) :
    digitEndpointView lane (phiD ring S e) i = digitEndpointView lane S i := by
  unfold digitEndpointView
  rw [phiD_at_other ring S e i hie hij]

end L3.DigitQuiet

#print axioms L3.DigitQuiet.glue_left
#print axioms L3.DigitQuiet.glue_right

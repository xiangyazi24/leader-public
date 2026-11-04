import Leader.Wu.Elimination.SinkUnifiedCell
import Leader.Wu.RaceEntrance.ArrivalRaceMass

/-!
# Physical race probability on the counted finite local carrier

The three-port mass theorem is consumed here by the actual bounded K2 row,
then by the existing unified controller product.  Erasure preserves every
scheduler choice and the exact success predicate.  No run-time, probability,
simulation, phase, or controller-cleanliness field is assumed by the result.
The remaining protocol question is which complete dispatcher selects this row.
-/

namespace LDSinkFiniteRaceMass

open FiniteUniformStoppingTree LDSinkBoundedKernel LDSinkBoundedStopping
open LDSinkUnifiedFinite StateBoundUnifiedCell LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapEntrance LDSinkTwoGapReachInvariant

set_option autoImplicit false

noncomputable section

theorem bounded_race_mass {n ψ κ : Nat} (hψ : 0 < ψ)
    (F : TwoGapFrame n) (C : BConfig n ψ κ)
    (hg : GapPair hψ F ⟨eraseConfig C, .transit⟩)
    (hr : RaceReady F (eraseConfig C)) :
    n ^ (4 * n) ≤
      16 * successCount (boundedBlockStep hψ F) (.active C) (4 * n) := by
  rw [LDSinkBoundedStopping.successCount_eq hψ F (.active C)
    (.active ⟨eraseConfig C, .transit⟩) rfl]
  exact LDSinkTwoGapArrivalRaceMass.physical_race_mass hψ F _ hg hr

/-- Stop the actual UCell elimination process exactly at tagged deletion. -/
def unifiedBlockStep {n ψ κ : Nat} (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (e : Fin n) : StopNode (Fin n → UCell ψ κ) := by
  classical
  let C' := step hψ F.attack C e
  exact if NoResetSuccess F (eraseConfig (legacyConfig C')) then .success else .active C'

def projectNode {n ψ κ : Nat} :
    StopNode (Fin n → UCell ψ κ) → StopNode (BConfig n ψ κ)
  | .active C => .active (legacyConfig C)
  | .success => .success
  | .failure => .failure

theorem project_stepNode {n ψ κ : Nat} (hψ : 0 < ψ) (F : TwoGapFrame n)
    (z : StopNode (Fin n → UCell ψ κ)) (e : Fin n) :
    projectNode (stepNode (unifiedBlockStep hψ F) z e) =
      stepNode (boundedBlockStep hψ F) (projectNode z) e := by
  classical
  cases z with
  | success => rfl
  | failure => rfl
  | active C =>
      by_cases h : NoResetSuccess F (eraseConfig (boundedStep hψ F.attack (legacyConfig C) e))
      · simp [stepNode, unifiedBlockStep, boundedBlockStep, projectNode, legacy_step, h]
      · simp [stepNode, unifiedBlockStep, boundedBlockStep, projectNode, legacy_step, h]

theorem unified_successCount_eq {n ψ κ : Nat} (hψ : 0 < ψ) (F : TwoGapFrame n)
    (z : StopNode (Fin n → UCell ψ κ)) (T : Nat) :
    successCount (unifiedBlockStep hψ F) z T =
      successCount (boundedBlockStep hψ F) (projectNode z) T := by
  induction T generalizing z with
  | zero => cases z <;> rfl
  | succ T ih =>
      simp only [successCount, treeWeight]
      apply ofFn_sum_eq
      intro e
      change successCount (unifiedBlockStep hψ F)
          (stepNode (unifiedBlockStep hψ F) z e) T = _
      rw [ih, project_stepNode]
      rfl

/-- The success mass is unchanged for arbitrary contents of every existing
controller field: the finite row retains those fields exactly. -/
theorem unified_race_mass {n ψ κ : Nat} (hψ : 0 < ψ)
    (F : TwoGapFrame n) (C : Fin n → UCell ψ κ)
    (hg : GapPair hψ F ⟨eraseConfig (legacyConfig C), .transit⟩)
    (hr : RaceReady F (eraseConfig (legacyConfig C))) :
    n ^ (4 * n) ≤
      16 * successCount (unifiedBlockStep hψ F) (.active C) (4 * n) := by
  rw [unified_successCount_eq]
  exact bounded_race_mass hψ F (legacyConfig C) hg hr

end
end LDSinkFiniteRaceMass

#print axioms LDSinkFiniteRaceMass.bounded_race_mass
#print axioms LDSinkFiniteRaceMass.project_stepNode
#print axioms LDSinkFiniteRaceMass.unified_successCount_eq
#print axioms LDSinkFiniteRaceMass.unified_race_mass

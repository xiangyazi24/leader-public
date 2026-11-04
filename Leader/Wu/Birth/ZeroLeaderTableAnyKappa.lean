import Leader.Wu.Birth.ZeroLeaderTablePsiOne

/-!
# Positive-κ stability of the ψ = 1 four-state raw table

Only saturated WAIT reads `κ` in the complete repaired row.  On the four raw
states used by `ZZZeroLeaderFinite`, every count is zero, carry consumption
never reaches the saturating increment branch, and a positive `κ` makes the
terminal `count = κ` guard false.  The lemmas below expose that fact at WAIT,
the before-CHECK boundary, and the complete local transition.
-/

namespace ZZZeroLeaderKappaPrefix

open PPLL PPLLRepair
open ZZZeroLeaderFinite

set_option autoImplicit false

theorem pPsi_cell (l r : Code4) :
    pPsi hψ (cell l) (cell r) = (cell l, cell r) := by
  cases l <;> cases r <;> rfl

/-- The only κ-sensitive prefix has the same value as at κ=1 on every one of
the sixteen ordered pairs, provided κ is positive. -/
theorem waitSaturated_cell_eq_one (κ : Nat) (hκ : 0 < κ)
    (l r : Code4) :
    waitSaturated hψ κ (cell l) (cell r) =
      waitSaturated hψ 1 (cell l) (cell r) := by
  have hk0 : (0 : Nat) ≠ κ := Nat.ne_of_lt hκ
  cases l <;> cases r <;>
    simp [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
      waitSaturatedReset, waitSaturatedFinish, cell, neutral, hk0]

/-- Consequently the whole κ-dependent prefix through signal movement agrees
with the already certified κ=1 prefix. -/
theorem beforeCheck_cell_eq_one (κ : Nat) (hκ : 0 < κ)
    (l r : Code4) :
    ppllSaturatedBeforeCheck hψ κ (cell l) (cell r) =
      ppllSaturatedBeforeCheck hψ 1 (cell l) (cell r) := by
  unfold ppllSaturatedBeforeCheck
  rw [pPsi_cell]
  unfold genSigSaturated
  simp only
  rw [waitSaturated_cell_eq_one κ hκ]

/-- All later stages are κ-free, so equality of the before-CHECK prefix lifts
to equality of the complete repaired row. -/
theorem full_cell_eq_one (κ : Nat) (hκ : 0 < κ)
    (l r : Code4) :
    ppllSaturatedNoCollision hψ κ (cell l) (cell r) =
      ppllSaturatedNoCollision hψ 1 (cell l) (cell r) := by
  unfold ppllSaturatedNoCollision ppllSaturatedBeforeWrite
    ppllSaturatedBeforeEliminate
  rw [beforeCheck_cell_eq_one κ hκ]

/-- Reusable positive-κ version of the four-state transition table. -/
theorem pair_transition_of_pos (κ : Nat) (hκ : 0 < κ)
    (l r : Code4) :
    ppllSaturatedNoCollision hψ κ (cell l) (cell r) =
      (cell (leftNext l), cell (rightNext l)) := by
  calc
    ppllSaturatedNoCollision hψ κ (cell l) (cell r) =
        ppllSaturatedNoCollision hψ 1 (cell l) (cell r) :=
      full_cell_eq_one κ hκ l r
    _ = (cell (leftNext l), cell (rightNext l)) := pair_transition l r

#print axioms pPsi_cell
#print axioms waitSaturated_cell_eq_one
#print axioms beforeCheck_cell_eq_one
#print axioms full_cell_eq_one
#print axioms pair_transition_of_pos

end ZZZeroLeaderKappaPrefix

import Leader.Wu.Elimination.SinkBoundedStopping
import Leader.Wu.Protocol.StateBoundUnifiedCell

/-!
# Elimination on the already counted unified cell

This is a concrete K2 row on the existing `UCell ψ κ`, not a new carrier.
Every controller field is retained.  The row, its output and its enumeration
are independent of the population size at fixed local parameters.  The
remaining assembly obligation is to show when the full protocol selects this
row and to charge interactions of its other row families.
-/

namespace LDSinkUnifiedFinite

open LDSinkBoundedKernel LDSinkGapCleanup StateBoundUnifiedCell

set_option autoImplicit false

/-- Execute finite K2 on the legacy fields and frame the complete unified
controller.  No traffic flag is implicitly cleared by this row. -/
def eliminationRow {ψ κ : Nat} (hψ : 0 < ψ)
    (l r : UCell ψ κ) : UCell ψ κ × UCell ψ κ :=
  let q := boundedKernel hψ l.legacy r.legacy
  (⟨q.1, l.control⟩, ⟨q.2, r.control⟩)

/-- Projection to the bounded audit fields is the concrete counted kernel. -/
theorem legacy_row {ψ κ : Nat} (hψ : 0 < ψ) (l r : UCell ψ κ) :
    ((eliminationRow hψ l r).1.legacy, (eliminationRow hψ l r).2.legacy) =
      boundedKernel hψ l.legacy r.legacy := rfl

/-- All controller fields, including transient traffic, are framed exactly. -/
theorem control_row {ψ κ : Nat} (hψ : 0 < ψ) (l r : UCell ψ κ) :
    (eliminationRow hψ l r).1.control = l.control ∧
      (eliminationRow hψ l r).2.control = r.control := ⟨rfl, rfl⟩

/-- The complete audit K2 row is realized on the previously counted carrier,
for every input and every bound κ, including saturated counts. -/
theorem erase_row {ψ κ : Nat} (hψ : 0 < ψ) (l r : UCell ψ κ) :
    ((eliminationRow hψ l r).1.legacy.erase,
      (eliminationRow hψ l r).2.legacy.erase) =
      LDSinkKernelC.sinkKernelC hψ l.legacy.erase r.legacy.erase :=
  erase_boundedKernel hψ l.legacy r.legacy

/-- The intended output is the legacy leader bit, independent of control
mode or transient protocol traffic. -/
def output {ψ κ : Nat} (q : UCell ψ κ) : Bool := q.legacy.leader

theorem output_erase {ψ κ : Nat} (q : UCell ψ κ) :
    output q = q.legacy.erase.leader := rfl

/-- Forget only the unified controller, pointwise. -/
def legacyConfig {ψ κ n : Nat} (C : Fin n → UCell ψ κ) :
    Fin n → BoundedAgentState ψ κ := fun i => (C i).legacy

/-- One physical interaction of the unified elimination row. -/
def step {ψ κ n : Nat} (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → UCell ψ κ) (e : Fin n) : Fin n → UCell ψ κ :=
  let q := eliminationRow hψ (C e) (C (F.ring.rightNeighbor e))
  fun i => if i = e then q.1
    else if i = F.ring.rightNeighbor e then q.2 else C i

/-- The controller extension adds neither interactions nor stuttering. -/
theorem legacy_step {ψ κ n : Nat} (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → UCell ψ κ) (e : Fin n) :
    legacyConfig (step hψ F C e) = boundedStep hψ F (legacyConfig C) e := by
  funext i
  simp only [legacyConfig, step, boundedStep, eliminationRow]
  split <;> first | rfl | (split <;> rfl)

/-- Entire scheduler words retain their exact finite-carrier executions. -/
theorem legacy_run {ψ κ n : Nat} (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) :
    legacyConfig (run (step hψ F) C es) =
      run (boundedStep hψ F) (legacyConfig C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih => simp only [run, ih, legacy_step]

/-- The unified elimination row uses exactly the already enumerated UCell
type; its established polynomial bound therefore needs no additional factor. -/
theorem state_bound (ψ κ : Nat) (hψ : 1 ≤ ψ) (hκ : ψ ≤ κ + 1) :
    (allUCell ψ κ).length ≤
      4862332800 * 61931520000000 * (κ + 1) ^ 8 :=
  unifiedCell_state_bound ψ κ hψ hκ

end LDSinkUnifiedFinite

#print axioms LDSinkUnifiedFinite.erase_row
#print axioms LDSinkUnifiedFinite.legacy_run
#print axioms LDSinkUnifiedFinite.state_bound

import Leader.Wu.Protocol.Repairs

/-!
# Literal saturated WAIT count rows

These are equations for the existing Prepare/Carry/Reset/Finish transition.
In particular a simultaneous reset does not suppress the earlier carry hit.
No stochastic interpretation or future passive-prefix closure is assumed.
-/

namespace BirthWaitClockAudit

open PPLL PPLLRepair

set_option autoImplicit false
set_option Elab.async false

/-- Finish changes only wait flags and therefore retains both actual counts. -/
theorem finish_count_frame {psi : Nat} (hpsi : 0 < psi)
    (kappa : Nat) (l r : AgentState psi) :
    (waitSaturatedFinish hpsi kappa l r).1.count = l.count ∧
      (waitSaturatedFinish hpsi kappa l r).2.count = r.count := by
  unfold waitSaturatedFinish
  split <;> dsimp only <;> split <;> exact ⟨rfl, rfl⟩

/-- Reset follows Carry and leaves its count assignment intact. -/
theorem reset_count_frame {psi : Nat} (hpsi : 0 < psi) (l r : AgentState psi) :
    (waitSaturatedReset hpsi l r).1.count = l.count ∧
      (waitSaturatedReset hpsi l r).2.count = r.count := by
  unfold waitSaturatedReset
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- The fully general responder equation tests the prepared fields, so it
also covers the label-zero initiator when psi=2. -/
theorem prepared_count_row {psi : Nat} (hpsi : 0 < psi)
    (kappa : Nat) (l r : AgentState psi) :
    let p := waitSaturatedPrepare hpsi l r
    (waitSaturated hpsi kappa l r).2.count =
      if p.1.carry = true ∧ p.2.h_field = true ∧
          p.2.label = ⟨psi - 1, by omega⟩
      then min (p.2.count + 1) kappa else p.2.count := by
  dsimp only
  unfold waitSaturated
  rw [(finish_count_frame hpsi kappa _ _).2, (reset_count_frame hpsi _ _).2]
  generalize waitSaturatedPrepare hpsi l r = p
  rcases p with ⟨a, b⟩
  dsimp only
  unfold waitSaturatedCarry
  split
  · split
    · split <;> simp_all [satCountSucc]
    · simp_all
  · simp_all

/-- On a non-root terminal edge, the old carry and old terminal bit determine
the exact saturated increment. A pending reset is deliberately unrestricted. -/
theorem terminal_count_row {psi : Nat} (hpsi : 0 < psi)
    (kappa : Nat) (l r : AgentState psi)
    (hl0 : l.label ≠ ⟨0, hpsi⟩) (hr0 : r.label ≠ ⟨0, hpsi⟩)
    (hrt : r.label = ⟨psi - 1, by omega⟩) :
    (waitSaturated hpsi kappa l r).2.count =
      if l.carry = true ∧ r.h_field = true
      then min (r.count + 1) kappa else r.count := by
  have hp : waitSaturatedPrepare hpsi l r = (l, r) := by
    simp only [waitSaturatedPrepare, if_neg hl0, if_neg hr0]
  rw [prepared_count_row, hp]
  simp only [hrt, and_true]

end BirthWaitClockAudit

#print axioms BirthWaitClockAudit.terminal_count_row
#print axioms BirthWaitClockAudit.prepared_count_row

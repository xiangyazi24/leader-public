import Leader.Wu.Birth.WaitClockRows

/-!
# Physical weighted WAIT row accounting

The weight is evaluated on the actual h/carry/count registers. Its extra
root and terminal carry terms vanish on the stated passive boundary inputs.
These are literal WAIT-row laws; no general full-host projection or random
clock law is an input or a conclusion.
-/

namespace BirthWaitClockAudit

open PPLL PPLLRepair

set_option autoImplicit false
set_option Elab.async false

/-- Nonnegative linear weights for the three registers touched by Carry. -/
def energy {psi : Nat} (a b c : Nat) (u : AgentState psi) : Nat :=
  (if u.h_field then a else 0) + (if u.carry then b else 0) + c * u.count

/-- WAIT Finish changes none of the energy registers. -/
theorem finish_energy {psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (l r : AgentState psi) (a b c d e f : Nat) :
    energy a b c (waitSaturatedFinish hpsi kappa l r).1 = energy a b c l ∧
      energy d e f (waitSaturatedFinish hpsi kappa l r).2 = energy d e f r := by
  unfold waitSaturatedFinish
  split <;> dsimp only <;> split <;> exact ⟨rfl, rfl⟩

/-- The reset stage can only remove h-weight; pending carries and the
already updated counts retain their exact old values. -/
theorem reset_energy_le {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) (a b c d e f : Nat) :
    energy a b c (waitSaturatedReset hpsi l r).1 +
        energy d e f (waitSaturatedReset hpsi l r).2 ≤
      energy a b c l + energy d e f r := by
  unfold waitSaturatedReset
  split
  · split <;> simp [energy] <;> omega
  · exact Nat.le_refl _

/-- A nonterminal carry transfers equal binary weight. Setting an already
pending Boolean carry can lose weight, but cannot create extra weight. -/
theorem carry_internal_energy {psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (l r : AgentState psi) (hr : r.label ≠ ⟨psi - 1, by omega⟩) (a w : Nat) :
    energy a w 0 (waitSaturatedCarry hpsi kappa l r).1 +
        energy w (2 * w) 0 (waitSaturatedCarry hpsi kappa l r).2 ≤
      energy a w 0 l + energy w (2 * w) 0 r := by
  cases hc : l.carry <;> cases hh : r.h_field <;> cases hc2 : r.carry <;>
    simp [waitSaturatedCarry, hr, hc, hh, hc2, energy] <;> omega

/-- At the terminal, two equal binary weights fund the capped count hit.
No reset or wait hypothesis is needed for this carry-stage inequality. -/
theorem carry_terminal_energy {psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (l r : AgentState psi) (hr : r.label = ⟨psi - 1, by omega⟩) (a w : Nat) :
    energy a w 0 (waitSaturatedCarry hpsi kappa l r).1 +
        energy w (2 * w) (2 * w) (waitSaturatedCarry hpsi kappa l r).2 ≤
      energy a w 0 l + energy w (2 * w) (2 * w) r := by
  have hcap := Nat.mul_le_mul_left (2 * w) (Nat.min_le_left (r.count + 1) kappa)
  rw [Nat.mul_add, Nat.mul_one] at hcap
  cases hc : l.carry <;> cases hh : r.h_field <;> cases hc2 : r.carry <;>
    simp [waitSaturatedCarry, hr, hc, hh, hc2, energy, satCountSucc] <;> omega

/-- The root toggle increases its physical binary energy by at most one.
The responder is a non-root, so Prepare does not change its energy. -/
theorem prepare_root_energy {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) (hl : l.label = ⟨0, hpsi⟩)
    (hr : r.label ≠ ⟨0, hpsi⟩) (a b c : Nat) :
    energy 1 2 0 (waitSaturatedPrepare hpsi l r).1 +
        energy a b c (waitSaturatedPrepare hpsi l r).2 ≤
      energy 1 2 0 l + energy a b c r + 1 := by
  cases hh : l.h_field <;> cases hc : l.carry <;>
    simp [waitSaturatedPrepare, hl, hr, hh, hc, energy] <;> omega

/-- The binary site weight, with terminal count measured in full turns.
Boundary carry weights are retained so each stage has a literal row law. -/
def clockEnergy {psi : Nat} (j : Nat) (u : AgentState psi) : Nat :=
  energy (2 ^ j) (2 ^ (j + 1)) (if j + 1 = psi then 2 ^ psi else 0) u

/-- Prepare preserves both labels and every responder count. -/
theorem prepare_frame {psi : Nat} (hpsi : 0 < psi) (l r : AgentState psi) :
    (waitSaturatedPrepare hpsi l r).1.label = l.label ∧
      (waitSaturatedPrepare hpsi l r).2.label = r.label ∧
      (waitSaturatedPrepare hpsi l r).2.count = r.count := by
  by_cases hl : l.label = ⟨0, hpsi⟩
  all_goals by_cases hr : r.label = ⟨0, hpsi⟩
  all_goals cases hh : l.h_field
  all_goals simp [waitSaturatedPrepare, hl, hr, hh]

/-- The last two actual WAIT stages never raise any nonnegative register
energy computed immediately after its Carry stage. -/
theorem wait_energy_le_carry {psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (l r : AgentState psi) (a b c d e f : Nat) :
    let p := waitSaturatedPrepare hpsi l r
    let q := waitSaturatedCarry hpsi kappa p.1 p.2
    energy a b c (waitSaturated hpsi kappa l r).1 +
        energy d e f (waitSaturated hpsi kappa l r).2 ≤
      energy a b c q.1 + energy d e f q.2 := by
  dsimp only
  unfold waitSaturated
  rw [(finish_energy hpsi kappa _ _ a b c d e f).1,
    (finish_energy hpsi kappa _ _ a b c d e f).2]
  exact reset_energy_le hpsi _ _ a b c d e f

/-- A correctly labelled internal edge has a literal one-unit charge only
when its initiator is the group root. Resets and carry coalescence are kept. -/
theorem internal_clock_energy {psi : Nat} (hpsi : 0 < psi) (kappa j : Nat)
    (hj : j + 1 < psi) (l r : AgentState psi)
    (hl : l.label.val = j) (hr : r.label.val = j + 1) :
    clockEnergy j (waitSaturated hpsi kappa l r).1 +
        clockEnergy (j + 1) (waitSaturated hpsi kappa l r).2 ≤
      clockEnergy j l + clockEnergy (j + 1) r + (if j = 0 then 1 else 0) := by
  let p := waitSaturatedPrepare hpsi l r
  have hr0 : r.label ≠ ⟨0, hpsi⟩ := by
    intro h
    have hh : r.label.val = 0 := congrArg Fin.val h
    omega
  have hnot : j + 1 ≠ psi := by omega
  have hc : energy (2 ^ j) (2 ^ (j + 1)) 0
          (waitSaturatedCarry hpsi kappa p.1 p.2).1 +
        energy (2 ^ (j + 1)) (2 ^ (j + 1 + 1))
          (if j + 1 + 1 = psi then 2 ^ psi else 0)
          (waitSaturatedCarry hpsi kappa p.1 p.2).2 ≤
      energy (2 ^ j) (2 ^ (j + 1)) 0 p.1 +
        energy (2 ^ (j + 1)) (2 ^ (j + 1 + 1))
          (if j + 1 + 1 = psi then 2 ^ psi else 0) p.2 := by
    by_cases ht : j + 1 + 1 = psi
    · have hp : p.2.label = ⟨psi - 1, by omega⟩ := by
        rw [(prepare_frame hpsi l r).2.1]
        apply Fin.ext
        simp only [hr]
        omega
      have hpow : 2 ^ psi = 2 * 2 ^ (j + 1) := by
        rw [← ht, Nat.pow_succ, Nat.mul_comm]
      simpa only [if_pos ht, hpow, Nat.pow_succ, Nat.mul_comm] using
        carry_terminal_energy hpsi kappa p.1 p.2 hp (2 ^ j) (2 ^ (j + 1))
    · have hp : p.2.label ≠ ⟨psi - 1, by omega⟩ := by
        rw [(prepare_frame hpsi l r).2.1]
        intro h
        have hh : r.label.val = psi - 1 := congrArg Fin.val h
        omega
      simpa only [if_neg ht, Nat.pow_succ, Nat.mul_comm] using
        carry_internal_energy hpsi kappa p.1 p.2 hp (2 ^ j) (2 ^ (j + 1))
  have hs := wait_energy_le_carry hpsi kappa l r
    (2 ^ j) (2 ^ (j + 1)) 0 (2 ^ (j + 1)) (2 ^ (j + 1 + 1))
    (if j + 1 + 1 = psi then 2 ^ psi else 0)
  have hh := Nat.le_trans hs hc
  unfold clockEnergy
  rw [if_neg hnot]
  apply Nat.le_trans hh
  by_cases hj0 : j = 0
  · rcases hj0 with rfl
    have hl0 : l.label = ⟨0, hpsi⟩ := Fin.ext hl
    simpa [p] using
      prepare_root_energy hpsi l r hl0 hr0 (2 ^ 1) (2 ^ (1 + 1))
        (if 1 + 1 = psi then 2 ^ psi else 0)
  · have hl0 : l.label ≠ ⟨0, hpsi⟩ := by
      intro h
      have hh : l.label.val = 0 := congrArg Fin.val h
      omega
    have hp : p = (l, r) := by simp only [p, waitSaturatedPrepare, if_neg hl0, if_neg hr0]
    rw [hp]
    simp only [if_neg hj0, Nat.add_zero, Nat.le_refl]

/-- At a terminal-to-root boundary, no old terminal carry can enter the
next group on the passive prefix. The outgoing group's energy is framed;
the incoming group's root energy can only decrease. -/
theorem terminal_boundary_clock_energy {psi : Nat} (hpsi : 0 < psi)
    (hn : 1 < psi) (kappa : Nat) (l r : AgentState psi)
    (hl : l.label.val = psi - 1) (hr : r.label = ⟨0, hpsi⟩)
    (hc : l.carry = false) :
    clockEnergy (psi - 1) (waitSaturated hpsi kappa l r).1 = clockEnergy (psi - 1) l ∧
      clockEnergy 0 (waitSaturated hpsi kappa l r).2 ≤ clockEnergy 0 r := by
  have hl0 : l.label ≠ ⟨0, hpsi⟩ := by
    intro h
    have hh : l.label.val = 0 := congrArg Fin.val h
    omega
  have hp : waitSaturatedPrepare hpsi l r =
      (l, { r with reset := true, h_field := false }) := by
    simp only [waitSaturatedPrepare, if_pos hr, if_neg hl0]
  have ht : psi - 1 + 1 = psi := by omega
  have hroot : 0 + 1 ≠ psi := by omega
  have hrnt : r.label ≠ ⟨psi - 1, by omega⟩ := by
    intro h
    have hh : r.label.val = psi - 1 := congrArg Fin.val h
    have hz : r.label.val = 0 := congrArg Fin.val hr
    omega
  unfold clockEnergy
  simp only [if_pos ht, if_neg hroot]
  unfold waitSaturated
  rw [hp]
  simp only [waitSaturatedCarry, hc, Bool.false_eq_true, if_false]
  rw [(finish_energy hpsi kappa _ _ (2 ^ (psi - 1)) (2 ^ (psi - 1 + 1))
      (2 ^ psi) 1 2 0).1,
    (finish_energy hpsi kappa _ _ (2 ^ (psi - 1)) (2 ^ (psi - 1 + 1))
      (2 ^ psi) 1 2 0).2]
  cases hz : l.reset <;> simp [waitSaturatedReset, hz, hrnt, energy]

/-- On passive root/terminal inputs, the auxiliary boundary carry weight
is exactly zero; this recovers the advertised bit-plus-terminal-count value. -/
theorem clock_energy_without_carry {psi : Nat} (j : Nat) (u : AgentState psi)
    (hc : u.carry = false) :
    clockEnergy j u = (if u.h_field then 2 ^ j else 0) +
      (if j + 1 = psi then 2 ^ psi * u.count else 0) := by
  simp [clockEnergy, energy, hc]
  split <;> simp

end BirthWaitClockAudit

#print axioms BirthWaitClockAudit.carry_internal_energy
#print axioms BirthWaitClockAudit.carry_terminal_energy
#print axioms BirthWaitClockAudit.internal_clock_energy
#print axioms BirthWaitClockAudit.terminal_boundary_clock_energy

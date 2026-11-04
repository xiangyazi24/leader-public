import Leader.Wu.WallSweep.Repair
import Leader.Wu.WriteSeq.Relocation

/-!
# Deterministic reset-command cleanup sweep

This module isolates the deterministic kernel used by the paper's suppressing
phase: in the absence of an echo ahead of the command, consecutive clockwise
edges move one reset token through the ring and delete arbitrary comparison
carriers at every visited agent.
-/

namespace PPLLWallSweepSchedule

open PPLL PPLLWallSweepRepair PPLLWriteSeqPersistenceRegression
  PPLLWriteSeqRelocation

/-- The first `steps` clockwise edges beginning at `start`. -/
def resetSweepSchedule {n : Nat} (ring : DirectedRing n) (start : Fin n) :
    Nat → DetSchedule n
  | 0 => []
  | steps + 1 =>
      resetSweepSchedule ring start steps ++ [groupOffset ring start steps]

/-- After `steps` reset handoffs, the token and every visited position are
comparison-neutral at offset `steps`; positions strictly ahead are unchanged. -/
def ResetSweepState {ψ n : Nat} (ring : DirectedRing n) (start : Fin n)
    (initial current : Fin n → AgentState ψ) (steps : Nat) : Prop :=
  steps < n ∧
    (current (groupOffset ring start steps)).reset_cmd = true ∧
    ComparisonNeutral (current (groupOffset ring start steps)) ∧
    (∀ k, k < steps →
      ComparisonNeutral (current (groupOffset ring start k))) ∧
    (∀ k, steps < k → k < n →
      current (groupOffset ring start k) =
        initial (groupOffset ring start k))

/-- One additional clockwise interaction advances the reset-sweep invariant. -/
theorem ResetSweepState.step {ψ n steps : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (_hn : 1 < n) (start : Fin n)
    (initial current : Fin n → AgentState ψ)
    (hstate : ResetSweepState ring start initial current steps)
    (hnext : steps + 1 < n)
    (hecho : ∀ i, (initial i).echo = false) :
    let D := stepConfig ring (suppressSigResetKill hψ) current
      (groupOffset ring start steps)
    ResetSweepState ring start initial D (steps + 1) := by
  let e := groupOffset ring start steps
  let j := groupOffset ring start (steps + 1)
  have hneighbor : ring.rightNeighbor e = j := by
    exact rightNeighbor_groupOffset ring start steps
  have hene : e ≠ j := by
    apply groupOffset_ne_of_lt ring start
    · exact hstate.1
    · exact hnext
    · omega
  have hjUntouched := hstate.2.2.2.2 (steps + 1) (by omega) hnext
  have hjEcho : (current j).echo = false := by
    rw [hjUntouched]
    exact hecho j
  have hlocal := suppressSigResetKill_handoff hψ (current e) (current j)
    hstate.2.1 hjEcho
  let q := suppressSigResetKill hψ (current e) (current j)
  change ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 ∧
    q.1.reset_cmd = false ∧ q.2.reset_cmd = true at hlocal
  let D := stepConfig ring (suppressSigResetKill hψ) current e
  have hje : j ≠ e := Ne.symm hene
  have hleft : D e = q.1 := by
    simp [D, q, stepConfig, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, stepConfig, hneighbor, hje]
  change ResetSweepState ring start initial D (steps + 1)
  refine ⟨hnext, ?_, ?_, ?_, ?_⟩
  · rw [hright]
    exact hlocal.2.2.2
  · rw [hright]
    exact hlocal.2.1
  · intro k hk
    by_cases hlast : k = steps
    · subst k
      rw [hleft]
      exact hlocal.1
    · have hkOld : k < steps := by omega
      have hke : groupOffset ring start k ≠ e := by
        apply groupOffset_ne_of_lt ring start
        · omega
        · exact hstate.1
        · omega
      have hkj : groupOffset ring start k ≠ j := by
        apply groupOffset_ne_of_lt ring start
        · omega
        · exact hnext
        · omega
      have hsame := stepConfig_eq_of_ne ring
        (suppressSigResetKill hψ) current e (groupOffset ring start k)
        hke (by simpa [hneighbor] using hkj)
      change D (groupOffset ring start k) =
        current (groupOffset ring start k) at hsame
      rw [hsame]
      exact hstate.2.2.2.1 k hkOld
  · intro k hkAhead hkRange
    have hke : groupOffset ring start k ≠ e := by
      apply groupOffset_ne_of_lt ring start
      · exact hkRange
      · exact hstate.1
      · omega
    have hkj : groupOffset ring start k ≠ j := by
      apply groupOffset_ne_of_lt ring start
      · exact hkRange
      · exact hnext
      · omega
    have hsame := stepConfig_eq_of_ne ring
      (suppressSigResetKill hψ) current e (groupOffset ring start k)
      hke (by simpa [hneighbor] using hkj)
    change D (groupOffset ring start k) =
      current (groupOffset ring start k) at hsame
    rw [hsame, hstate.2.2.2.2 k (by omega) hkRange]

/-- The first reset interaction establishes the sweep invariant at offset one. -/
theorem resetSweepState_one {ψ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (hn : 1 < n) (start : Fin n)
    (C : Fin n → AgentState ψ)
    (hreset : (C start).reset_cmd = true)
    (hecho : ∀ i, (C i).echo = false) :
    let D := applySchedule ring (suppressSigResetKill hψ) C
      (resetSweepSchedule ring start 1)
    ResetSweepState ring start C D 1 := by
  let e := groupOffset ring start 0
  let j := groupOffset ring start 1
  have he : e = start := by
    apply Fin.ext
    simp [e, groupOffset, Nat.mod_eq_of_lt start.isLt]
  have hneighbor : ring.rightNeighbor e = j :=
    rightNeighbor_groupOffset ring start 0
  have hene : e ≠ j := by
    apply groupOffset_ne_of_lt ring start <;> omega
  have hlocal := suppressSigResetKill_handoff hψ (C e) (C j)
    (by simpa [he] using hreset) (hecho j)
  let q := suppressSigResetKill hψ (C e) (C j)
  change ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 ∧
    q.1.reset_cmd = false ∧ q.2.reset_cmd = true at hlocal
  let D := stepConfig ring (suppressSigResetKill hψ) C e
  have hje : j ≠ e := Ne.symm hene
  have hleft : D e = q.1 := by
    simp [D, q, stepConfig, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, stepConfig, hneighbor, hje]
  change ResetSweepState ring start C D 1
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [show groupOffset ring start 1 = j by rfl, hright]
    exact hlocal.2.2.2
  · rw [show groupOffset ring start 1 = j by rfl, hright]
    exact hlocal.2.1
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rw [show groupOffset ring start 0 = e by rfl, hleft]
    exact hlocal.1
  · intro k hk hkn
    have hke : groupOffset ring start k ≠ e := by
      apply groupOffset_ne_of_lt ring start <;> omega
    have hkj : groupOffset ring start k ≠ j := by
      apply groupOffset_ne_of_lt ring start <;> omega
    have hsame := stepConfig_eq_of_ne ring
      (suppressSigResetKill hψ) C e (groupOffset ring start k)
      hke (by simpa [hneighbor] using hkj)
    change D (groupOffset ring start k) = C (groupOffset ring start k) at hsame
    exact hsame

/-- Every positive prefix of the explicit sweep schedule satisfies the reset
invariant. -/
theorem resetSweepSchedule_reaches {ψ n steps : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (hn : 1 < n) (start : Fin n)
    (C : Fin n → AgentState ψ) (hsteps : 0 < steps) (hbound : steps < n)
    (hreset : (C start).reset_cmd = true)
    (hecho : ∀ i, (C i).echo = false) :
    let D := applySchedule ring (suppressSigResetKill hψ) C
      (resetSweepSchedule ring start steps)
    ResetSweepState ring start C D steps := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      by_cases hzero : steps = 0
      · subst steps
        exact resetSweepState_one hψ ring hn start C hreset hecho
      · have hprevBound : steps < n := by omega
        have hprev := ih (by omega) hprevBound
        let C₁ := applySchedule ring (suppressSigResetKill hψ) C
          (resetSweepSchedule ring start steps)
        change ResetSweepState ring start C C₁ steps at hprev
        have hnext := ResetSweepState.step hψ ring hn start C C₁ hprev
          (by omega) hecho
        rw [resetSweepSchedule, applySchedule_append]
        simpa [applySchedule, C₁] using hnext

/-- A reset token clears every ring offset after the first `n-1` clockwise
edges. -/
theorem resetSweepSchedule_clears_all {ψ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (hn : 1 < n) (start : Fin n)
    (C : Fin n → AgentState ψ)
    (hreset : (C start).reset_cmd = true)
    (hecho : ∀ i, (C i).echo = false) :
    let D := applySchedule ring (suppressSigResetKill hψ) C
      (resetSweepSchedule ring start (n - 1))
    ∀ k, k < n → ComparisonNeutral (D (groupOffset ring start k)) := by
  have hreach := resetSweepSchedule_reaches hψ ring hn start C
    (steps := n - 1) (by omega) (by omega) hreset hecho
  let D := applySchedule ring (suppressSigResetKill hψ) C
    (resetSweepSchedule ring start (n - 1))
  change ResetSweepState ring start C D (n - 1) at hreach
  change ∀ k, k < n → ComparisonNeutral (D (groupOffset ring start k))
  intro k hk
  by_cases hlast : k = n - 1
  · subst k
    exact hreach.2.2.1
  · exact hreach.2.2.2.1 k (by omega)

end PPLLWallSweepSchedule

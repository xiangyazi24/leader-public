import Leader.Wu.Birth.IncreaseOrCapPrefireMatcherMass

namespace BirthPhaseB3PrefireBellman

/-- Core Lean has no `Nat.le.trans`; this enables `h.trans` on Nat inequalities. -/
theorem _root_.Nat.le.trans {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Nat.le_trans h1 h2

open FiniteUniformStoppingTree PredictableTwoTargetFiniteTree
open BirthShortDoneTerminalPassiveLocal3
open BirthWaitClockMass.Matcher
open BirthPhaseB3PrefireMatcherMass

set_option autoImplicit false
set_option Elab.async false

variable {n : Nat}

private theorem leftCross_ne_p2 (hn : 4 <= n) :
    leftCross hn ≠ p2 hn := by
  exact (Fin.ne_of_val_ne (by simp [leftCross, p2]; omega) :
    leftCross hn ≠ p2 hn)

private theorem advance_potential_le {kill : Fin n} (p : Pending kill) :
    potential (advance p) <= potential (.active p) := by
  unfold potential
  have h := advance_remaining p
  exact Nat.mul_le_mul_left n (by
    simp only [remaining] at h ⊢
    omega)

private theorem child_potential_le
    (hn : 4 <= n) (p : Pending (p2 hn)) (e : Fin n) :
    potential (controlledMatcher hn p e) <=
      potential (BirthWaitClockMass.Matcher.controlled p e) := by
  unfold controlledMatcher
  by_cases hl : e = leftCross hn
  · rw [if_pos hl]
    subst e
    by_cases hh : leftCross hn = p.head
    · simp [BirthWaitClockMass.Matcher.controlled, hh]
    · have hk := leftCross_ne_p2 hn
      rw [show BirthWaitClockMass.Matcher.controlled p (leftCross hn) =
          .active p by
        simp [BirthWaitClockMass.Matcher.controlled, hh, hk]]
      exact advance_potential_le p
  · rw [if_neg hl]
    exact Nat.le_refl _

private theorem controlledMatcher_bellman (hn : 4 <= n) :
    NatBellmanSuperSolution (controlledMatcher hn) 2 potential := by
  have old :=
    (BirthWaitClockMass.Matcher.bellman (n := n) (kill := p2 hn))
  refine ⟨old.1, old.2.1, ?_⟩
  intro p
  have hs := ofFn_sum_le
    (fun e : Fin n => potential (controlledMatcher hn p e))
    (fun e : Fin n =>
      potential (BirthWaitClockMass.Matcher.controlled p e))
    (child_potential_le hn p)
  exact (Nat.add_le_add_left hs (2 * n)).trans (old.2.2 p)

private theorem controlledMatcher_ne_failure
    (hn : 4 <= n) (p : Pending (p2 hn)) (e : Fin n) :
    controlledMatcher hn p e ≠ .failure := by
  unfold controlledMatcher
  by_cases hl : e = leftCross hn
  · rw [if_pos hl]
    exact advance_ne_failure p
  · rw [if_neg hl]
    unfold BirthWaitClockMass.Matcher.controlled
    split
    · exact advance_ne_failure p
    · intro h
      cases h

/-- The two-kill controlled comparison succeeds on at least half of all
length-`6*n` scheduler words when six requested hits remain. -/
theorem six_stage_controlled_half
    (hn : 4 <= n) (p : Pending (p2 hn))
    (hlen : p.length = 6) :
    n ^ (6 * n) <=
      2 * successCount (controlledMatcher hn) (.active p) (6 * n) := by
  have hn0 : 0 < n := by omega
  have hL : 0 < 6 * n := Nat.mul_pos (by decide) hn0
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (controlledMatcher hn) 2 potential (controlledMatcher_bellman hn)
    (.active p) (6 * n)
  have hactive := two_mul_activeCount_le_pow_of_scaled_cost
    (controlledMatcher hn) (.active p) hL (by decide : 0 < 2)
    (num := n * p.length)
    (by simpa [potential, remaining, Nat.mul_comm] using hcost)
    (by rw [hlen]; omega)
  have hfailure :=
    BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
      (controlledMatcher hn) (controlledMatcher_ne_failure hn) p (6 * n)
  have hpart := node_count_partition
    (controlledMatcher hn) (.active p) (6 * n)
  omega

/-- Combining half mass with the exact `3^6` fiber gives the advertised
pre-fire denominator 1458 at the same horizon. -/
theorem six_stage_raw_1458
    (hn : 4 <= n) (p : Pending (p2 hn))
    (hleft : leftCross hn ∉ p.word) (hlen : p.length = 6) :
    n ^ (6 * n) <=
      1458 * successCount (rawMatcher hn) (.active p) (6 * n) := by
  have h := six_stage_controlled_half hn p hlen
  rw [six_stage_fiber hn p hleft hlen (6 * n)] at h
  calc
    n ^ (6 * n) <=
        2 * (3 ^ 6 * successCount (rawMatcher hn) (.active p) (6 * n)) := h
    _ = 1458 * successCount (rawMatcher hn) (.active p) (6 * n) := by
      have hq : 2 * 3 ^ 6 = 1458 := by decide
      rw [← Nat.mul_assoc, hq]

end BirthPhaseB3PrefireBellman

#print axioms BirthPhaseB3PrefireBellman.six_stage_controlled_half
#print axioms BirthPhaseB3PrefireBellman.six_stage_raw_1458

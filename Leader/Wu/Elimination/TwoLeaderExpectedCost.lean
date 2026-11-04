import Leader.Wu.Elimination.ShortPairMass
import Leader.Wu.Scheduler.LeaderCountExpectedCost
import Leader.Wu.Elimination.HarmonicEpisodeCharge

/-!
# Physical expected cost to at most two leaders

Only the proof observable is shifted: `max(count - 1, 1)` equals one
exactly at physical count at most two. All words, interactions, and
continuing endpoints use the original finite-cell transition. The generic
finite-prefix cost consumer is instantiated with the proved short-pair
mass at every physical count at least three, including its final level.

The result bounds the exact sum of the actual charged word prefixes at
every finite horizon by a harmonic tariff. No final two-to-one service,
positive physical count, termination promise, or output-safety claim is
assumed or concluded.
-/

namespace K2GlobalExpectedCost

open StateBoundUnifiedCell LDSinkBoundedKernel LDTwoGapFrame
  LabelFreeElimination K2FiniteProgress K2GlobalShortPairMass
  LeaderCountDyadicTail LeaderCountExpectedCost
  LDSinkTwoGapRaceEntranceUniformAll

set_option autoImplicit false

variable {n ψ κ : Nat}

/-- A positive proof observable. It is never stored in a protocol cell. -/
def shiftedCount (C : Fin n → UCell ψ κ) : Nat := max (count C - 1) 1

theorem shiftedCount_positive (C : Fin n → UCell ψ κ) : 1 ≤ shiftedCount C :=
  Nat.le_max_right _ _

/-- The observable stops at precisely the physical target, including zero. -/
theorem shiftedCount_one_iff (C : Fin n → UCell ψ κ) :
    shiftedCount C = 1 ↔ count C ≤ 2 := by
  unfold shiftedCount
  omega

theorem shiftedCount_active_iff (C : Fin n → UCell ψ κ) :
    2 ≤ shiftedCount C ↔ 3 ≤ count C := by
  unfold shiftedCount
  omega

theorem shiftedCount_add_one (C : Fin n → UCell ψ κ) (hk : 3 ≤ count C) :
    shiftedCount C + 1 = count C := by
  unfold shiftedCount
  omega

/-- Every strict physical drop above the target is precisely an observable
drop. This includes jumps below two and makes no positivity assumption. -/
theorem shiftedCount_drop_iff (C D : Fin n → UCell ψ κ) (hk : 3 ≤ count C) :
    shiftedCount D < shiftedCount C ↔ count D < count C := by
  unfold shiftedCount
  omega

theorem shiftedCount_step_nonincrease (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) :
    shiftedCount (step hψ ring C e) ≤ shiftedCount C := by
  have h := step_count_nonincrease hψ ring C e
  unfold shiftedCount
  omega

/-- Observable level `k` uses the proved physical block at count `k+1`. -/
def shiftedBlock (n k : Nat) : Nat := countBlock n (k + 1)

/-- The exact number of interactions charged on one actual finite word:
stop before the next interaction once the physical count is at most two. -/
def rawCostToTwo (hψ : 0 < ψ) (ring : DirectedRing n) :
    (Fin n → UCell ψ κ) → List (Fin n) → Nat
  | _, [] => 0
  | C, e :: es =>
      if count C ≤ 2 then 0 else 1 + rawCostToTwo hψ ring (step hψ ring C e) es

/-- Sum over all literal raw scheduler words, with denominator `n^T`. -/
def physicalChargedPrefix (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (rawCostToTwo hψ ring C)

/-- The generic charged payload and the actual first-hit word cost agree
word by word. The payload retains the true successor at a successful edge. -/
theorem rawWordCost_eq_physical (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) :
    FixedSpanRenewalPayload.rawWordCost
      (physicalPayload (step hψ ring) shiftedCount) (haltAt shiftedCount C) es =
      rawCostToTwo hψ ring C es := by
  induction es generalizing C with
  | nil =>
      simp only [FixedSpanRenewalPayload.rawWordCost, rawCostToTwo]
  | cons e es ih =>
      by_cases hk : count C ≤ 2
      · have hs := (shiftedCount_one_iff C).mpr hk
        simp only [haltAt, if_pos hs, FixedSpanRenewalPayload.rawWordCost,
          rawCostToTwo, if_pos hk]
      · have hs : shiftedCount C ≠ 1 := fun h => hk ((shiftedCount_one_iff C).mp h)
        simp only [haltAt, if_neg hs, FixedSpanRenewalPayload.rawWordCost,
          rawCostToTwo, if_neg hk]
        exact congrArg (fun z => 1 + z) (ih (step hψ ring C e))

/-- Exact connection to the generic denominator-aware charged-prefix
numerator. This is an equality of actual finite word sums, not a bound. -/
theorem chargedPrefix_eq_physical (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    chargedPrefixNumerator (step hψ ring) shiftedCount C T =
      physicalChargedPrefix hψ ring C T := by
  rw [chargedPrefix_eq_rawWordCost]
  unfold physicalChargedPrefix
  apply congrArg (FixedSpanRenewalPayload.wordSum n T)
  funext es
  exact rawWordCost_eq_physical hψ ring C es

theorem physicalChargedPrefix_terminal (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hk : count C ≤ 2) (T : Nat) :
    physicalChargedPrefix hψ ring C T = 0 := by
  rw [← chargedPrefix_eq_physical]
  exact chargedPrefix_terminal (step hψ ring) shiftedCount C
    ((shiftedCount_one_iff C).mpr hk) T

noncomputable section

/-- Every active shifted level receives the actual original-scheduler mass,
with exactly the corresponding physical-count block. -/
theorem shifted_count_drop_mass (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (hk : 2 ≤ shiftedCount C) :
    n ^ shiftedBlock n (shiftedCount C) ≤ deletionDenominator *
      wordSum (step hψ ring) (fun D => if shiftedCount D < shiftedCount C then 1 else 0)
        C (shiftedBlock n (shiftedCount C)) := by
  have hp := (shiftedCount_active_iff C).mp hk
  have he := shiftedCount_add_one C hp
  have hw : (fun D : Fin n → UCell ψ κ => if count D < count C then 1 else 0) =
      (fun D => if shiftedCount D < shiftedCount C then 1 else 0) := by
    funext D
    simp only [shiftedCount_drop_iff C D hp]
  have hm := K2GlobalShortPairMass.signalGlobal_count_drop_mass hψ ring C hC hp
  rw [hw] at hm
  simpa only [shiftedBlock, he] using hm

/-- Shifting the target merely reindexes the exact finite tariff: original
levels `3,...,k` become shifted levels `2,...,k-1`. -/
theorem shifted_reserve_eq (H : Nat → Nat) (Q k : Nat) :
    levelReserve (fun j => H (j + 1)) Q Q (H 3) (max (k - 1) 1) =
      Q * levelSum H k := by
  induction k with
  | zero => simp [levelSum]
  | succ k ih =>
      by_cases hk : 3 ≤ k
      · have hm : max (k - 1) 1 = k - 1 := by omega
        have hm' : max (k + 1 - 1) 1 = k := by omega
        have he : k - 1 + 1 = k := by omega
        have hs := levelReserve_succ (fun j => H (j + 1)) Q Q (H 3) (k - 1) (by omega)
        rw [he] at hs
        rw [hm] at ih
        rw [hm', hs, ih]
        simp only [levelSum, if_pos (by omega : 3 ≤ k + 1), Nat.mul_add]
        exact Nat.add_comm _ _
      · have he : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases he with rfl | rfl | rfl <;> simp [levelSum]

/-- A fully produced tariff for all finite horizons on the closed physical
signal domain. The transformed final level is the real three-to-two block,
whose mass has already been proved; there is no final-service premise. -/
theorem signalGlobal_chargedPrefix_le_tariff (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (T : Nat) :
    physicalChargedPrefix hψ ring C T ≤
      n ^ T * (deletionDenominator * levelSum (countBlock n) (count C)) := by
  have hm : ∀ D : Fin n → UCell ψ κ, SignalGlobal ring D → 3 ≤ shiftedCount D →
      n ^ shiftedBlock n (shiftedCount D) ≤ deletionDenominator *
        wordSum (step hψ ring) (fun E => if shiftedCount E < shiftedCount D then 1 else 0)
          D (shiftedBlock n (shiftedCount D)) := by
    intro D hD hk
    exact shifted_count_drop_mass hψ ring D hD (by omega)
  have ht : ∀ D : Fin n → UCell ψ κ, SignalGlobal ring D → shiftedCount D = 2 →
      n ^ countBlock n 3 ≤ deletionDenominator *
        wordSum (step hψ ring) (fun E => if shiftedCount E < shiftedCount D then 1 else 0)
          D (countBlock n 3) := by
    intro D hD hk
    have h := shifted_count_drop_mass hψ ring D hD (by omega)
    simpa only [shiftedBlock, hk] using h
  have h := chargedPrefix_le_reserve_on_closed_domain (step hψ ring) (SignalGlobal ring)
    (fun D e hD => signalGlobal_step hψ ring D hD e) shiftedCount
    (fun D _ => shiftedCount_positive D)
    (fun D e _ => shiftedCount_step_nonincrease hψ ring D e)
    (shiftedBlock n) deletionDenominator deletionDenominator (countBlock n 3)
    deletion_denominator_pos deletion_denominator_pos hm ht T C hC
  rw [chargedPrefix_eq_physical] at h
  have he : levelReserve (shiftedBlock n) deletionDenominator deletionDenominator
      (countBlock n 3) (shiftedCount C) =
      deletionDenominator * levelSum (countBlock n) (count C) :=
    shifted_reserve_eq (countBlock n) deletionDenominator (count C)
  rw [he] at h
  exact h

/-- The real level tariff is bounded by the ordinary floor-division sum.
This uses only the arithmetic part of `HarmonicEpisodeCharge`. -/
theorem levelSum_le_divisionBudget (n k : Nat) :
    levelSum (countBlock n) k ≤ HarmonicEpisodeCharge.divisionBudget (60 * n * n) k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      rw [levelSum, HarmonicEpisodeCharge.divisionBudget_succ]
      by_cases hk : 3 ≤ k + 1
      · simp only [if_pos hk, countBlock]
        exact Nat.add_le_add_right ih _
      · simp only [if_neg hk, Nat.add_zero]
        exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- The existing recursive binary length has at most `log2(n)+1` layers. -/
theorem numBits_le_log2_succ (n : Nat) :
    HarmonicEpisodeCharge.numBits n ≤ Nat.log2 n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hn : 2 ≤ n
      · have hp : 0 < n := by omega
        have hh := ih (n / 2) (Nat.div_lt_self hp (by decide))
        rw [HarmonicEpisodeCharge.numBits_rec n hp, Nat.log2_def n, if_pos hn]
        omega
      · have he : n = 0 ∨ n = 1 := by omega
        rcases he with rfl | rfl <;> simp [HarmonicEpisodeCharge.numBits]

/-- Finite harmonic bound in the original physical count, including every
integer-rounded block. No episode trace or successful-termination field is
used to justify the sum. -/
theorem level_tariff_log_bound (n k : Nat) (hk : k ≤ n) :
    deletionDenominator * levelSum (countBlock n) k ≤
      deletionDenominator * ((60 * n * n) * (Nat.log2 n + 1)) := by
  apply Nat.mul_le_mul_left
  exact Nat.le_trans (levelSum_le_divisionBudget n k)
    (Nat.le_trans (HarmonicEpisodeCharge.divisionBudget_mono (60 * n * n) hk)
      (Nat.le_trans (HarmonicEpisodeCharge.divisionBudget_le_numBits (60 * n * n) n)
        (Nat.mul_le_mul_left (60 * n * n) (numBits_le_log2_succ n))))

/-- Exact expected-prefix numerator at every finite horizon, bounded by
`60*Q*n^2*(log2 n+1)`. Both the word cost and all progress inputs refer to
the actual original finite-cell process. -/
def expectedTariff (n : Nat) : Nat :=
  deletionDenominator * ((60 * n * n) * (Nat.log2 n + 1))

theorem signalGlobal_expected_to_two (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (T : Nat) :
    physicalChargedPrefix hψ ring C T ≤ n ^ T * expectedTariff n :=
  Nat.le_trans (signalGlobal_chargedPrefix_le_tariff hψ ring C hC T)
    (Nat.mul_le_mul_left _ (level_tariff_log_bound n (count C) (count_le_ring_size C)))

/-- At ring size at least two this is the usual `O(Q*n^2*log n)` form,
without an additive logarithmic convention at zero or one. -/
theorem signalGlobal_expected_to_two_log (hψ : 0 < ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n) (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (T : Nat) :
    physicalChargedPrefix hψ ring C T ≤
      n ^ T * (deletionDenominator * ((60 * n * n) * (2 * Nat.log2 n))) := by
  have hlog := (log_parameters n hn).1
  exact Nat.le_trans (signalGlobal_expected_to_two hψ ring C hC T)
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left deletionDenominator
      (Nat.mul_le_mul_left (60 * n * n) (by omega))))

/-- The actual three-leader finite configuration supplies a nonempty active
domain for the all-horizon physical cost theorem. -/
theorem threeLeaderSeed_expected :
    count threeLeaderSeed = 3 ∧ ∀ T,
      physicalChargedPrefix (by decide) NondivisibleExample.frame7.attack.ring
        threeLeaderSeed T ≤
      7 ^ T * expectedTariff 7 := by
  refine ⟨by decide, fun T => ?_⟩
  exact signalGlobal_expected_to_two (by decide) NondivisibleExample.frame7.attack.ring
    threeLeaderSeed threeLeaderSeed_global T

end

end K2GlobalExpectedCost

#print axioms K2GlobalExpectedCost.shiftedCount_one_iff
#print axioms K2GlobalExpectedCost.shiftedCount_drop_iff
#print axioms K2GlobalExpectedCost.rawWordCost_eq_physical
#print axioms K2GlobalExpectedCost.chargedPrefix_eq_physical
#print axioms K2GlobalExpectedCost.physicalChargedPrefix_terminal
#print axioms K2GlobalExpectedCost.shifted_count_drop_mass
#print axioms K2GlobalExpectedCost.shifted_reserve_eq
#print axioms K2GlobalExpectedCost.signalGlobal_chargedPrefix_le_tariff
#print axioms K2GlobalExpectedCost.level_tariff_log_bound
#print axioms K2GlobalExpectedCost.signalGlobal_expected_to_two
#print axioms K2GlobalExpectedCost.signalGlobal_expected_to_two_log
#print axioms K2GlobalExpectedCost.threeLeaderSeed_expected

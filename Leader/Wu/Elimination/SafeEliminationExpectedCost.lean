import Leader.Wu.Elimination.SafeEliminationTail
import Leader.Wu.Elimination.SafeEliminationArithmetic
import Leader.Wu.Elimination.SafeEliminationWordCost

/-!
Exact physical cost through the first semantic safe state. Every finite raw
word is charged at each unfinished prefix; the successful interaction is
included and its later padding is free. Both higher-level and final mass
inputs are the actual proved original-scheduler producers.
-/

set_option autoImplicit false

open StateBoundUnifiedCell LDSinkBoundedKernel LDSinkGapCleanup
open FiniteUniformStoppingTree LabelFreeElimination K2FiniteProgress
open LeaderCountDyadicTail LeaderCountExpectedCost K2GlobalShortPairMass
open K2FiniteSafeEliminationCore K2FiniteSafeEliminationTail

namespace K2FiniteSafeEliminationExpected

noncomputable section

variable {n ψ κ : Nat}

/-- Literal cost of one physical word, including all unfinished prefixes. -/
def rawCostToOne (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) : Nat :=
  rawCost (step hψ ring) (fun D => count D = 1) C es

/-- The stopping criterion here is literally semantic output safety. -/
noncomputable def rawCostToSafe (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) : Nat := by
  classical
  exact rawCost (step hψ ring)
    (fun D => PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring D id) C es

theorem rawCostToOne_nil (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) : rawCostToOne hψ ring C [] = 0 := rfl

theorem rawCostToOne_cons (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (es : List (Fin n)) :
    rawCostToOne hψ ring C (e :: es) =
      if count C = 1 then 0 else 1 + rawCostToOne hψ ring (step hψ ring C e) es := rfl

theorem rawCostToSafe_nil (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) : rawCostToSafe hψ ring C [] = 0 := rfl

theorem rawCostToSafe_cons (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (es : List (Fin n)) :
    rawCostToSafe hψ ring C (e :: es) =
      (by classical exact if PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id then 0
        else 1 + rawCostToSafe hψ ring (step hψ ring C e) es) := rfl

/-- No observation or phase changes the physical cost of any individual word. -/
theorem rawCost_one_eq_safe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (es : List (Fin n)) :
    rawCostToOne hψ ring C es = rawCostToSafe hψ ring C es := by
  classical
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
      have hi := isSafe_iff_count_one hψ hn ring C hC
      by_cases hc : count C = 1
      · simp only [rawCostToOne_cons, if_pos hc, rawCostToSafe_cons, if_pos (hi.mpr hc)]
      · have hs : ¬ PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id :=
          fun h => hc (hi.mp h)
        simp only [rawCostToOne_cons, if_neg hc, rawCostToSafe_cons, if_neg hs]
        exact congrArg (fun z => 1 + z) (ih _ (domain_step hψ hn ring C e hC))

def physicalChargedPrefix (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (rawCostToOne hψ ring C)

noncomputable def semanticChargedPrefix (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (rawCostToSafe hψ ring C)

/-- Exact payload cost equality: successful payloads contain the actual
successor configuration, while their later word suffix costs zero. -/
theorem rawWordCost_eq_physical (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) :
    FixedSpanRenewalPayload.rawWordCost
      (physicalPayload (step hψ ring) count) (haltAt count C) es =
      rawCostToOne hψ ring C es := by
  induction es generalizing C with
  | nil => simp only [FixedSpanRenewalPayload.rawWordCost, rawCostToOne_nil]
  | cons e es ih =>
      by_cases hc : count C = 1
      · simp only [haltAt, FixedSpanRenewalPayload.rawWordCost, rawCostToOne_cons, if_pos hc]
      · simp only [haltAt, FixedSpanRenewalPayload.rawWordCost, rawCostToOne_cons, if_neg hc]
        exact congrArg (fun z => 1 + z) (ih (step hψ ring C e))

theorem chargedPrefix_eq_physical (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    chargedPrefixNumerator (step hψ ring) count C T = physicalChargedPrefix hψ ring C T := by
  rw [chargedPrefix_eq_rawWordCost]
  apply congrArg (FixedSpanRenewalPayload.wordSum n T)
  funext es
  exact rawWordCost_eq_physical hψ ring C es

theorem physicalChargedPrefix_eq_semantic (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (T : Nat) :
    physicalChargedPrefix hψ ring C T = semanticChargedPrefix hψ ring C T := by
  apply congrArg (FixedSpanRenewalPayload.wordSum n T)
  funext es
  exact rawCost_one_eq_safe hψ hn ring C hC es

/-- An unfinished endpoint certifies that the entire raw word was charged.
In particular, no partial block or unsuccessful last prefix is discarded. -/
theorem unfinished_word_cost (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n))
    (hu : 1 < count (run (step hψ ring) C es)) : rawCostToOne hψ ring C es = es.length := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
      have hm := run_count_nonincrease hψ ring C (e :: es)
      have hc : count C ≠ 1 := by omega
      rw [rawCostToOne_cons, if_neg hc, ih (step hψ ring C e) hu, List.length_cons]
      omega

/-- The exact generic prefix recursion counts the present physical edge
and every real successor. It applies also to horizons shorter than any block. -/
theorem semanticChargedPrefix_succ (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (T : Nat) :
    semanticChargedPrefix hψ ring C (T + 1) =
      n ^ (T + 1) * safeMiss hψ ring C +
        (List.ofFn (fun e : Fin n => semanticChargedPrefix hψ ring (step hψ ring C e) T)).sum := by
  have he (D : Fin n → UCell ψ κ) (hD : Domain ring D) (t : Nat) :
      chargedPrefixNumerator (step hψ ring) count D t = semanticChargedPrefix hψ ring D t :=
    (chargedPrefix_eq_physical hψ ring D t).trans (physicalChargedPrefix_eq_semantic hψ hn ring D hD t)
  have h := chargedPrefix_succ_on (step hψ ring) (Domain ring) (domain_step hψ hn ring)
    count (fun D hD => count_positive ring D hD)
    (fun D e _ => step_count_nonincrease hψ ring D e) C hC T
  rw [he C hC (T + 1), ← safeMiss_eq_countMiss hψ hn ring C hC] at h
  rw [ofFn_sum_eq _ _ (fun e => he _ (domain_step hψ hn ring C e hC) T)] at h
  exact h

/-- The cumulative higher-level tariff and the separate final two-to-one
tariff, both at their actual full physical horizons. -/
def exactTariff (n k : Nat) : Nat :=
  higherDenominator * levelSum (countBlock n) k + finalDenominator * (20 * n * n)

/-- Every premise of the generic expected-cost theorem is derived on the
actual closed physical intersection. No final-tail field is supplied. -/
theorem chargedPrefix_le_exactTariff (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (T : Nat) :
    semanticChargedPrefix hψ ring C T ≤ n ^ T * exactTariff n (count C) := by
  have h := chargedPrefix_le_level_tariff (step hψ ring) (Domain ring) (domain_step hψ hn ring)
    count (fun D hD => count_positive ring D hD)
    (fun D e _ => step_count_nonincrease hψ ring D e) (countBlock n)
    higherDenominator finalDenominator (20 * n * n)
    LDSinkTwoGapRaceEntranceUniformAll.deletion_denominator_pos final_denominator_pos
    (fun D hD hk => signalGlobal_count_drop_mass hψ ring D hD.1 hk)
    (fun D hD hk => two_leader_drop_mass hψ hn ring D hD hk) T C hC
  rw [chargedPrefix_eq_physical, physicalChargedPrefix_eq_semantic hψ hn ring C hC] at h
  exact h

def expectedConstant : Nat := 120 * higherDenominator + 20 * finalDenominator

def expectedBound (n : Nat) : Nat := expectedConstant * n * n * Nat.log2 n

theorem exactTariff_le_log (n k : Nat) (hn : 2 ≤ n) (hk : k ≤ n) :
    exactTariff n k ≤ expectedBound n := by
  have hl := (log_parameters n hn).1
  have hh : higherDenominator * levelSum (countBlock n) k ≤
      120 * higherDenominator * n * n * Nat.log2 n := by
    calc
      higherDenominator * levelSum (countBlock n) k ≤
          higherDenominator * ((60 * n * n) * (Nat.log2 n + 1)) :=
        K2FiniteSafeEliminationArithmetic.level_tariff_log (60 * n * n) n k higherDenominator hk
      _ ≤ higherDenominator * ((60 * n * n) * (2 * Nat.log2 n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = 120 * higherDenominator * n * n * Nat.log2 n := by
        generalize higherDenominator = q
        have he : 120 = 60 * 2 := by decide
        rw [he]
        ac_rfl
  have ht : finalDenominator * (20 * n * n) ≤
      20 * finalDenominator * n * n * Nat.log2 n := by
    calc
      finalDenominator * (20 * n * n) ≤ finalDenominator * (20 * n * n) * Nat.log2 n := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (finalDenominator * (20 * n * n)) hl
      _ = 20 * finalDenominator * n * n * Nat.log2 n := by
        generalize finalDenominator = q
        ac_rfl
  calc
    exactTariff n k ≤ 120 * higherDenominator * n * n * Nat.log2 n +
        20 * finalDenominator * n * n * Nat.log2 n := Nat.add_le_add hh ht
    _ = expectedBound n := by
      simp only [expectedBound, expectedConstant, Nat.add_mul]

/-- Uniform finite expected hitting-cost bound for literal semantic safety.
The denominator is `n^T` and the bound holds for every unfinished raw horizon. -/
theorem expected_safe_prefix (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (T : Nat) :
    semanticChargedPrefix hψ ring C T ≤ n ^ T * expectedBound n :=
  Nat.le_trans (chargedPrefix_le_exactTariff hψ hn ring C hC T)
    (Nat.mul_le_mul_left _ (exactTariff_le_log n (count C) hn (count_le_ring_size C)))

end

end K2FiniteSafeEliminationExpected

#print axioms K2FiniteSafeEliminationExpected.rawCost_one_eq_safe
#print axioms K2FiniteSafeEliminationExpected.rawWordCost_eq_physical
#print axioms K2FiniteSafeEliminationExpected.unfinished_word_cost
#print axioms K2FiniteSafeEliminationExpected.semanticChargedPrefix_succ
#print axioms K2FiniteSafeEliminationExpected.chargedPrefix_le_exactTariff
#print axioms K2FiniteSafeEliminationExpected.expected_safe_prefix

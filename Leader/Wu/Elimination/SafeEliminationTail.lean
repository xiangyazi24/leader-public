import Leader.Wu.Elimination.SafeEliminationDomain

/-!
The final-stage tail is produced by finite iteration on the actual closed
physical domain. The dyadic consumer receives only proved physical mass,
closure, count, and clock facts. All endpoint words use the original row.
-/

set_option autoImplicit false

open StateBoundUnifiedCell LDSinkBoundedKernel LDSinkGapCleanup
open FiniteUniformStoppingTree LabelFreeElimination K2FiniteProgress
open LeaderCountDyadicTail K2GlobalShortPairMass K2FiniteSafeEliminationCore

namespace K2FiniteSafeEliminationTail

variable {n ψ κ : Nat}

/-- The frozen higher-level denominator, independent of all parameters. -/
abbrev higherDenominator : Nat := LDSinkTwoGapRaceEntranceUniformAll.deletionDenominator

/-- Every final-stage block is fully charged, including the block in which
the first physical count-one hit occurred. -/
def finalTime (n : Nat) : Nat :=
  (1 + logSlack n) * (2 * finalDenominator * (20 * n * n))

/-- A uniform final tail derived from the actual two-to-one mass; the subtype
retains the same raw scheduler edge and the same physical successor. -/
theorem final_tail (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (hc : count C ≤ 2) :
    2 ^ logSlack n * wordSum (step hψ ring) (fun D => binMiss 1 (count D))
      C (finalTime n) ≤ n ^ finalTime n := by
  let stepP := restrictedStep (step (κ := κ) hψ ring) (Domain ring) (domain_step hψ hn ring)
  have hm : ∀ D : {E : Fin n → UCell ψ κ // Domain ring E},
      1 < count D.val → count D.val ≤ 2 * 1 →
      n ^ (20 * n * n) ≤ finalDenominator * wordSum stepP
        (fun E => if count E.val < count D.val then 1 else 0) D (20 * n * n) := by
    intro D hl hu
    rw [wordSum_restrict (step hψ ring) (Domain ring) (domain_step hψ hn ring)
      (fun E => if count E < count D.val then 1 else 0) (20 * n * n) D]
    exact two_leader_drop_mass hψ hn ring D.val D.property (by omega)
  have h := bin_tail stepP (fun D => count D.val) 1 (20 * n * n)
    finalDenominator (logSlack n) final_denominator_pos
    (fun D e => step_count_nonincrease hψ ring D.val e) hm ⟨C, hC⟩ hc
  change 2 ^ logSlack n * wordSum stepP (fun D => binMiss 1 (count D.val))
    ⟨C, hC⟩ (finalTime n) ≤ n ^ finalTime n at h
  rw [wordSum_restrict (step hψ ring) (Domain ring) (domain_step hψ hn ring)
    (fun D => binMiss 1 (count D)) (finalTime n) ⟨C, hC⟩] at h
  exact h

/-- The final-stage constant is explicit; no recovery-length parameter occurs. -/
def finalClockConstant : Nat := 240 * finalDenominator

theorem final_clock (n : Nat) (hn : 2 ≤ n) :
    finalTime n ≤ finalClockConstant * n * n * Nat.log2 n := by
  have hl := (log_parameters n hn).1
  have hs : 1 + logSlack n ≤ 6 * Nat.log2 n := by
    unfold logSlack
    omega
  calc
    finalTime n ≤ (6 * Nat.log2 n) * (2 * finalDenominator * (20 * n * n)) :=
      Nat.mul_le_mul_right _ hs
    _ = finalClockConstant * n * n * Nat.log2 n := by
      unfold finalClockConstant
      generalize finalDenominator = q
      have he : 240 = 6 * (2 * 20) := by decide
      rw [he]
      ac_rfl

/-- The actual dyadic schedule followed by the proved final-stage schedule. -/
def dyadicSafeTime (n : Nat) : Nat :=
  dyadicTime (levelBlock n 60 0) higherDenominator (logSlack n) (Nat.log2 n) + finalTime n

/-- Absolute constant in the deterministic safe-elimination horizon. -/
def whpConstant : Nat := 732 * higherDenominator + 240 * finalDenominator

def safeHorizon (n : Nat) : Nat := whpConstant * n * n * Nat.log2 n

/-- The existing closed-domain dyadic theorem, with every premise supplied
by a physical producer. This conclusion still refers to the actual count. -/
theorem count_whp_and_clock (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) :
    n * wordSum (step hψ ring) (fun D => binMiss 1 (count D)) C (dyadicSafeTime n)
        ≤ n ^ dyadicSafeTime n ∧
      dyadicSafeTime n ≤ safeHorizon n := by
  have h := leader_count_whp_on_closed_domain (step hψ ring) (Domain ring)
    (domain_step hψ hn ring) count (countBlock n) 60 0 higherDenominator
    finalClockConstant (finalTime n) hn
    LDSinkTwoGapRaceEntranceUniformAll.deletion_denominator_pos
    (fun D e _ => step_count_nonincrease hψ ring D e)
    (fun D _ _ => by unfold countBlock levelBlock; omega)
    (fun D hD hk => signalGlobal_count_drop_mass hψ ring D hD.1 hk)
    (fun D hD hk => final_tail hψ hn ring D hD hk)
    (final_clock n hn) C hC (count_le_ring_size C)
  have he : 12 * higherDenominator * (60 + 0 + 1) + finalClockConstant = whpConstant := by
    unfold finalClockConstant whpConstant
    generalize higherDenominator = q
    generalize finalDenominator = q2
    have hc : 732 = 12 * 61 := by decide
    rw [hc]
    ac_rfl
  simpa only [dyadicSafeTime, safeHorizon, he] using h

/-- Padding performs real additional interactions. Count monotonicity
bounds the exact failure numerator after an arbitrary longer horizon. -/
theorem count_failure_pad (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (q T U : Nat) (hTU : T ≤ U)
    (hm : q * wordSum (step hψ ring) (fun D => binMiss 1 (count D)) C T ≤ n ^ T) :
    q * wordSum (step hψ ring) (fun D => binMiss 1 (count D)) C U ≤ n ^ U := by
  have he : U = T + (U - T) := (Nat.add_sub_of_le hTU).symm
  rw [he, wordSum_horizon_add]
  have hp : wordSum (step hψ ring)
      (fun D => wordSum (step hψ ring) (fun E => binMiss 1 (count E)) D (U - T)) C T ≤
      n ^ (U - T) * wordSum (step hψ ring) (fun D => binMiss 1 (count D)) C T := by
    rw [← wordSum_mul]
    exact wordSum_mono_on (step hψ ring) (fun _ => True) (fun _ _ _ => trivial)
      _ _ (fun D _ => wordSum_le_initial (step hψ ring) (fun E => binMiss 1 (count E))
        (fun E e => binMiss_mono (step_count_nonincrease hψ ring E e)) D (U - T)) T C trivial
  calc
    q * wordSum (step hψ ring)
        (fun D => wordSum (step hψ ring) (fun E => binMiss 1 (count E)) D (U - T)) C T
        ≤ q * (n ^ (U - T) * wordSum (step hψ ring) (fun D => binMiss 1 (count D)) C T) :=
      Nat.mul_le_mul_left q hp
    _ = n ^ (U - T) * (q * wordSum (step hψ ring) (fun D => binMiss 1 (count D)) C T) := by ac_rfl
    _ ≤ n ^ (U - T) * n ^ T := Nat.mul_le_mul_left _ hm
    _ = n ^ (T + (U - T)) := by rw [Nat.pow_add]; ac_rfl

/-- The semantic and physical failure events have identical word sums
because the actual domain is closed after every scheduler prefix. -/
theorem safe_wordSum_eq_count (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (T : Nat) :
    wordSum (step hψ ring) (safeMiss hψ ring) C T =
      wordSum (step hψ ring) (fun D => binMiss 1 (count D)) C T := by
  induction T generalizing C with
  | zero => exact safeMiss_eq_countMiss hψ hn ring C hC
  | succ T ih =>
      exact ofFn_sum_eq _ _ (fun e => ih _ (domain_step hψ hn ring C e hC))

/-- Literal semantic `IsSafe` failure has mass at most `1/n` at the explicit
constant*n²*floor(log2 n) horizon, under the original finite-cell scheduler. -/
theorem safe_failure_whp (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) :
    n * wordSum (step hψ ring) (safeMiss hψ ring) C (safeHorizon n) ≤ n ^ safeHorizon n := by
  rw [safe_wordSum_eq_count hψ hn ring C hC]
  have h := count_whp_and_clock hψ hn ring C hC
  exact count_failure_pad hψ ring C n _ _ h.2 h.1

end K2FiniteSafeEliminationTail

#print axioms K2FiniteSafeEliminationTail.final_tail
#print axioms K2FiniteSafeEliminationTail.final_clock
#print axioms K2FiniteSafeEliminationTail.count_whp_and_clock
#print axioms K2FiniteSafeEliminationTail.safe_wordSum_eq_count
#print axioms K2FiniteSafeEliminationTail.safe_failure_whp

import Leader.L3.Bank.RepairDigitValueWave

/-!
# T22 task A: the three-stage pre-drain ledger

The structural cut `rho` (`DigitStructuralAt`, every complete pair has a first strict completion
in BOTH lanes from time 0) is an all-pairs clock of its own (Lemma e-max, repair.tex 4195-4239).
The paper charges it through `n^2 P_pair` (repair.tex 5279, 5352-5359), not inside the 200
half-units of the value wave (4829ff). This module gives it its own stage:

* `BankRepairDigitStructuralCut`: the coupled BANK x audit run of the T19 cut, with the two base
  covers at some cut, and a first structural cut `rho`.
* `BankRepairDigitStructuralClock`: FirstZero -> Structural at
  `bankRepairDigitStructuralMicroCharge n = 2 * bankRepairDigitPairUpper s * n` (both lanes, the
  same per-lane bound `bankRepairDigitPairUpper` is built from).
* `BankRepairDigitWaveAfterStructuralClock`: Structural -> ValuesStable at the paper's
  `bankRepairDigitValueWaveMicroCharge n = 200 n^2`.
* `BankRepairDigitComparisonClock` (T20) is kept unchanged.
* `bankRepairDigitPreDrainHalfOfThreeClocks`: the 201-half pre-drain from every W-stage entrance.
  The new total fits the 201 budget (`bankRepairDigitLedgerChargesFit`), because
  `6 nu_s < 2^E < n` (proved in BankRepairDigit.lean) leaves room for a second `P_pair`.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

/-! ### The structural cut and the three clocks -/

/-- Structural (`rho`): the coupled BANK x audit run of the T19 first-zero cut (two base covers
after the retirement, at some cut `zeroCut`), and a first cut at which every complete pair has a
first strict completion in both lanes. -/
def BankRepairDigitStructuralCut {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank)
    (word : List (Fin n))
    (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired zeroCut structural : Nat),
    BankRepairRFoldEstablished ring hbank start ∧
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) ∧
    WFixedRoot ring root (piW z.val.1) ∧
    DigitAt ring audit audit.clock (piD z.val.1) audit.current ∧
    DigitTwoBaseCovers ring root audit 0 retired zeroCut ∧
    DigitFirstCut (DigitStructuralAt ring root audit) structural

/-- Both lanes of the all-pairs first strict completion: the full `bankRepairDigitPairUpper`
envelope (which covers two lanes of Lemma e-max), doubled to half-units. -/
def bankRepairDigitStructuralMicroCharge (n : Nat) : Nat :=
  2 * bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) * n

/-- The structural clock `rho`: from the first-zero cut to the structural cut. -/
def BankRepairDigitStructuralClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  BankRepairDigitChargedStage (bankRepairNext ring hbank)
    (BankRepairDigitFirstZeroCut ring hbank)
    (BankRepairDigitStructuralCut ring hbank)
    (bankRepairDigitStructuralMicroCharge n)

/-- The successor-value wave after `rho`: the paper's 200 half-units of repair.tex 4829ff. -/
def BankRepairDigitWaveAfterStructuralClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  BankRepairDigitChargedStage (bankRepairNext ring hbank)
    (BankRepairDigitStructuralCut ring hbank)
    (BankRepairDigitValuesStableCut ring hbank)
    (bankRepairDigitValueWaveMicroCharge n)

/-! ### The budget -/

/-- `P_pair` is one summand of `nu_s`. -/
theorem bankRepairDigitPairUpperLeNu (s : Nat) :
    bankRepairDigitPairUpper s ≤ bankRepairDigitNu s := by
  unfold bankRepairDigitNu
  omega

/-- In the BANK band, `4 nu_s < n`: room for a second `P_pair` beside `nu_s`. -/
theorem bankRepairDigitLedgerRoom {n : Nat} (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 * (bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) +
      bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n))) < n := by
  have hsix := bankRepairDigitNuSixOfGrowth bankRepairDigitNuGrowthProved
    (ceilLogTwo (ceilLogTwo n)) (bankRepairDigitWidthBank hbank)
  have hpop := bankRepairDigitPopulationLower hn hbank
  have hp := bankRepairDigitPairUpperLeNu (ceilLogTwo (ceilLogTwo n))
  omega

/-- The five charges (boundary, first zero, structural, wave, comparison) fit the 201 budget. -/
theorem bankRepairDigitLedgerChargesFit {n : Nat} (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitStructuralMicroCharge n + bankRepairDigitValueWaveMicroCharge n +
        bankRepairDigitComparisonMicroCharge n ≤
      201 * n ^ 2 := by
  have hroom := bankRepairDigitLedgerRoom hn hbank
  have hnum : 2 * (bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) +
      bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n))) * n ≤ n ^ 2 := by
    have h := Nat.mul_le_mul_right n (Nat.le_of_lt hroom)
    simpa only [Nat.pow_two] using h
  have heq : bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitStructuralMicroCharge n + bankRepairDigitValueWaveMicroCharge n +
        bankRepairDigitComparisonMicroCharge n =
      2 * (bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) +
        bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n))) * n + 200 * n ^ 2 := by
    unfold bankRepairDigitBoundaryMicroCharge bankRepairDigitFirstZeroMicroCharge
      bankRepairDigitStructuralMicroCharge bankRepairDigitValueWaveMicroCharge
      bankRepairDigitComparisonMicroCharge bankRepairDigitNu
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  rw [heq]
  omega

/-! ### The pre-drain from the three clocks -/

/-- The 201-half pre-drain from every W-stage entrance on the concrete cuts, from the structural
clock, the wave after `rho`, and the restarted comparison clock. -/
theorem bankRepairDigitPreDrainHalfOfThreeClocks {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrho : BankRepairDigitStructuralClock ring hbank)
    (hwave : BankRepairDigitWaveAfterStructuralClock ring hbank)
    (hpair : BankRepairDigitComparisonClock ring hbank) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (BankRepairDigitComparisonCut ring hbank) 201 := by
  have h0 := bankRepairDigitFirstZeroReceiptClock ring hn hbank
    (BankRepairDigitValuesStableCut ring hbank)
  have h1 := bankRepairDigitZeroCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    (fun z => BankRepairDigitFirstZeroCut ring hbank z ∧
      BankRepairDigitLeaderReceipt ring hbank z)
    (BankRepairDigitStructuralCut ring hbank) _ _ h0 (fun x hx T => hrho x hx.1 T)
  have h2 := bankRepairDigitZeroCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    (BankRepairDigitStructuralCut ring hbank)
    (BankRepairDigitValuesStableCut ring hbank) _ _ h1 hwave
  have h3 := bankRepairDigitZeroCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    (BankRepairDigitValuesStableCut ring hbank)
    (BankRepairDigitComparisonCut ring hbank) _ _ h2 hpair
  have hfit := bankRepairDigitLedgerChargesFit hn hbank
  intro z hz T
  refine Nat.le_trans (h3 z hz T) (Nat.mul_le_mul_left (n ^ T) ?_)
  omega

/-- The structural clock and the wave after `rho` give T20's wave stage, at the wave charge
plus the structural charge (not at 200 n^2 alone). -/
theorem bankRepairDigitWaveThroughStructural {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrho : BankRepairDigitStructuralClock ring hbank)
    (hwave : BankRepairDigitWaveAfterStructuralClock ring hbank) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitFirstZeroCut ring hbank)
      (BankRepairDigitValuesStableCut ring hbank)
      (bankRepairDigitStructuralMicroCharge n + bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitZeroCompose (bankRepairNext ring hbank) _
    (BankRepairDigitStructuralCut ring hbank) _ _ _ hrho hwave

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitPairUpperLeNu
#print axioms L3.RenewalReferenceClock.bankRepairDigitLedgerRoom
#print axioms L3.RenewalReferenceClock.bankRepairDigitLedgerChargesFit
#print axioms L3.RenewalReferenceClock.bankRepairDigitPreDrainHalfOfThreeClocks
#print axioms L3.RenewalReferenceClock.bankRepairDigitWaveThroughStructural

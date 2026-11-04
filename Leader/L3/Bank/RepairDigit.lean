import Leader.L3.LiveTopBlocks
import Leader.L3.Bank.FinishRepair
import Leader.L3.WordPhase

/-!
R10 digit-stage arithmetic and causal-clock obligations.
The Nat expressions are NUMERATORS of paper upper envelopes, not
definitions of real logarithms. The physical clocks remain Props.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

def bankRepairDigitRadius (s : Nat) : Nat := 2 ^ s - 1

def bankRepairDigitExponent (s : Nat) : Nat := 2 ^ (s - 1)

/-- C_r in repair.tex. -/
def bankRepairDigitPairClock (r : Nat) : Nat :=
  2 * r ^ 4 + 8 * r ^ 3 + 3 * r ^ 2 + 11 * r + 4

/-- The enlarged h from renewal.tex (F.16). -/
def bankRepairDigitPairEnvelope (r : Nat) : Nat :=
  12 * r ^ 4 + 40 * r ^ 3 + 18 * r ^ 2 + 36 * r + 10

def bankRepairDigitBaseCount (r : Nat) : Nat :=
  3 * r ^ 2 + 4 * r + 2

def bankRepairDigitForwardCount (r : Nat) : Nat :=
  (2 * r ^ 2 + 1) * bankRepairDigitBaseCount r + 8 * r ^ 3

def bankRepairDigitReturnCount (r : Nat) : Nat :=
  4 * r ^ 2 + 4 * r

def bankRepairDigitSettledCount (r : Nat) : Nat :=
  r ^ 2 * (2 * r ^ 2 + 8 * r + 1) + 5 * r

def bankRepairDigitLeadingLength (s : Nat) : Nat :=
  2 * bankRepairDigitRadius s + s - 2

def bankRepairDigitLeadingRecords (s : Nat) : Nat :=
  bankRepairDigitRadius s + s - 2

def bankRepairDigitLeadingSquare (s : Nat) : Nat :=
  bankRepairDigitLeadingRecords s *
    (bankRepairDigitLeadingRecords s + 1)

def bankRepairDigitLeadingTotal (s : Nat) : Nat :=
  bankRepairDigitLeadingSquare s + bankRepairDigitRadius s

/-- The boundary J_s in repair.tex. -/
def bankRepairDigitBoundaryServices (s : Nat) : Nat :=
  bankRepairDigitLeadingSquare s *
      (bankRepairDigitLeadingRecords s + 1) +
    bankRepairDigitLeadingTotal s * (bankRepairDigitRadius s + 2) +
    2 * (bankRepairDigitLeadingTotal s + bankRepairDigitRadius s) *
      (bankRepairDigitRadius s + 2) +
    2 * bankRepairDigitRadius s +
    (bankRepairDigitLeadingRecords s) ^ 2 + 1

/-- Upper numerator for e(n,s), after log and population bounds. -/
def bankRepairDigitBoundaryUpper (s : Nat) : Nat :=
  2 * (bankRepairDigitExponent s +
      bankRepairDigitLeadingLength s + 3) +
    2 * bankRepairDigitBoundaryServices s +
    bankRepairDigitForwardCount (bankRepairDigitRadius s) +
    bankRepairDigitReturnCount (bankRepairDigitRadius s) +
    bankRepairDigitSettledCount (bankRepairDigitRadius s) +
    bankRepairDigitRadius s + 20 * (bankRepairDigitRadius s) ^ 2

/-- Upper numerator for g(n,r)-100, with common denominator 2^E. -/
def bankRepairDigitValueUpper (s : Nat) : Nat :=
  3 * bankRepairDigitRadius s *
    (bankRepairDigitExponent s + s + 6)

/-- Upper numerator for P_pair(n,r), covering BOTH lanes. -/
def bankRepairDigitPairUpper (s : Nat) : Nat :=
  4 * bankRepairDigitPairEnvelope (bankRepairDigitRadius s) *
    (bankRepairDigitExponent s + 3)

/-- Exactly nu_s as specified in renewal.tex (F.16). -/
def bankRepairDigitNu (s : Nat) : Nat :=
  bankRepairDigitBoundaryUpper s +
    bankRepairDigitValueUpper s + bankRepairDigitPairUpper s

/-- Cross-multiplied surrogate of e+(g-100)+P_pair<1/2.
The logarithm-to-numerator comparison is a SEPARATE bridge. -/
def BankRepairDigitIntegerHalf (n s : Nat) : Prop :=
  2 * bankRepairDigitNu s < n

/-- The exact six-stage ledger preserves its half-unit. -/
theorem bankRepairDigitHalfLedgerExact (s : Nat) :
    2 * (440 * s + 275) + 2 * s + 203 + 1 + 2 =
      2 * (441 * s + 378) := by
  omega

theorem bankRepairDigitNuBase :
    bankRepairDigitNu 7 = 860812189133 := by
  rfl

/-- Stronger than the required factor-two check. -/
theorem bankRepairDigitNuBaseSix :
    6 * bankRepairDigitNu 7 <
      2 ^ bankRepairDigitExponent 7 := by
  have hclosed : 6 * 860812189133 + 1 ≤ (2 : Nat) ^ 64 :=
    Nat.le_of_ble_eq_true rfl
  rw [bankRepairDigitNuBase]
  change 6 * 860812189133 < (2 : Nat) ^ 64
  omega

/-- At q=80, the first BANK n is 2^79+1. -/
theorem bankRepairDigitFirstBankPopulation :
    2 * bankRepairDigitNu 7 < 2 ^ 79 + 1 := by
  have hbase := bankRepairDigitNuBaseSix
  have hpower : (2 : Nat) ^ 64 ≤ 2 ^ 79 :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
      (by omega : 64 ≤ 79)
  change 6 * bankRepairDigitNu 7 < 2 ^ 64 at hbase
  omega

/-- Still open: explicit, purely integer inter-width growth. -/
def BankRepairDigitNuGrowth : Prop :=
  ∀ s : Nat, 7 ≤ s →
    bankRepairDigitNu (s + 1) ≤
      bankRepairDigitNu s * 2 ^ bankRepairDigitExponent s

private theorem bankRepairDigitExponentSucc (s : Nat)
    (hs : 1 ≤ s) :
    bankRepairDigitExponent (s + 1) =
      bankRepairDigitExponent s + bankRepairDigitExponent s := by
  unfold bankRepairDigitExponent
  have hsub : s + 1 - 1 = s := by omega
  rw [hsub]
  have hstep : s = (s - 1) + 1 := by omega
  calc
    2 ^ s = 2 ^ ((s - 1) + 1) :=
      congrArg (fun k : Nat => 2 ^ k) hstep
    _ = 2 ^ (s - 1) * 2 := Nat.pow_succ 2 (s - 1)
    _ = 2 ^ (s - 1) + 2 ^ (s - 1) := by omega

private theorem bankRepairDigitPowerSucc (s : Nat)
    (hs : 1 ≤ s) :
    2 ^ bankRepairDigitExponent (s + 1) =
      2 ^ bankRepairDigitExponent s *
        2 ^ bankRepairDigitExponent s := by
  have hstep := bankRepairDigitExponentSucc s hs
  rw [hstep, Nat.pow_add]

/-- All widths reduce to the closed base and one growth Prop. -/
theorem bankRepairDigitNuSixOfGrowth
    (hg : BankRepairDigitNuGrowth)
    (s : Nat) (hs : 7 ≤ s) :
    6 * bankRepairDigitNu s <
      2 ^ bankRepairDigitExponent s := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, s = 7 + k :=
    ⟨s - 7, by omega⟩
  subst s
  induction k with
  | zero =>
      simpa only [Nat.add_zero] using bankRepairDigitNuBaseSix
  | succ k ih =>
      have hgrowth := hg (7 + k) (by omega)
      have hpos :
          0 < 2 ^ bankRepairDigitExponent (7 + k) :=
        Nat.pow_pos (by omega)
      have hle :
          6 * bankRepairDigitNu (7 + k + 1) ≤
            (6 * bankRepairDigitNu (7 + k)) *
              2 ^ bankRepairDigitExponent (7 + k) := by
        calc
          6 * bankRepairDigitNu (7 + k + 1) ≤
              6 * (bankRepairDigitNu (7 + k) *
                2 ^ bankRepairDigitExponent (7 + k)) :=
                Nat.mul_le_mul_left 6 hgrowth
          _ = (6 * bankRepairDigitNu (7 + k)) *
                2 ^ bankRepairDigitExponent (7 + k) := by
                ac_rfl
      have hlt :
          (6 * bankRepairDigitNu (7 + k)) *
              2 ^ bankRepairDigitExponent (7 + k) <
            2 ^ bankRepairDigitExponent (7 + k) *
              2 ^ bankRepairDigitExponent (7 + k) :=
        Nat.mul_lt_mul_of_pos_right (ih (by omega)) hpos
      have hnext :
          6 * bankRepairDigitNu (7 + k + 1) <
            2 ^ bankRepairDigitExponent (7 + k + 1) := by
        calc
          6 * bankRepairDigitNu (7 + k + 1) ≤
              (6 * bankRepairDigitNu (7 + k)) *
                2 ^ bankRepairDigitExponent (7 + k) := hle
          _ < 2 ^ bankRepairDigitExponent (7 + k) *
                2 ^ bankRepairDigitExponent (7 + k) := hlt
          _ = 2 ^ bankRepairDigitExponent (7 + k + 1) :=
            (bankRepairDigitPowerSucc (7 + k) (by omega)).symm
      simpa only [Nat.add_succ] using hnext

/-- The BANK selector forces s=ceilLogTwo q>=7. -/
theorem bankRepairDigitWidthBank {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    7 ≤ ceilLogTwo (ceilLogTwo n) := by
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have hspec : ceilLogTwo n ≤
      2 ^ ceilLogTwo (ceilLogTwo n) :=
    (ceilLogTwo_spec (ceilLogTwo n) (by omega)).2
  by_cases hsmall : ceilLogTwo (ceilLogTwo n) ≤ 6
  · have hp :
        (2 : Nat) ^ ceilLogTwo (ceilLogTwo n) ≤ 2 ^ 6 :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hsmall
    have h64 : (2 : Nat) ^ 6 = 64 := by rfl
    rw [h64] at hp
    omega
  · omega

/-- The two ceilLogTwo bounds prove n>2^(2^(s-1)). -/
theorem bankRepairDigitPopulationLower {n : Nat}
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 ^ bankRepairDigitExponent
        (ceilLogTwo (ceilLogTwo n)) < n := by
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have hinner :
      2 ^ (ceilLogTwo (ceilLogTwo n) - 1) < ceilLogTwo n :=
    (ceilLogTwo_spec (ceilLogTwo n) (by omega)).1
  have houter :
      2 ^ (ceilLogTwo n - 1) < n :=
    (ceilLogTwo_spec n (by omega)).1
  have hle :
      bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) ≤
        ceilLogTwo n - 1 := by
    change 2 ^ (ceilLogTwo (ceilLogTwo n) - 1) ≤
      ceilLogTwo n - 1
    omega
  have hpow :
      2 ^ bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) ≤
        2 ^ (ceilLogTwo n - 1) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hle
  exact Nat.lt_of_le_of_lt hpow houter

/-- All-BANK cross-multiplied numeric certificate, conditional only
on the explicit integer polynomial growth. Real ln still needs its
own comparison with the paper's rational upper envelopes. -/
theorem bankRepairDigitIntegerHalfOfGrowth {n : Nat}
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hg : BankRepairDigitNuGrowth) :
    BankRepairDigitIntegerHalf n (ceilLogTwo (ceilLogTwo n)) := by
  have ht := bankRepairDigitWidthBank hbank
  have hnum := bankRepairDigitNuSixOfGrowth hg
    (ceilLogTwo (ceilLogTwo n)) ht
  have hden := bankRepairDigitPopulationLower hn hbank
  change 2 * bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) < n
  omega

/-! Remaining proof obligations concern the actual masked BANK
reference. A valid pre-drain class must encode past-visible boundary
retirements, strict packet cohorts, current values/comparisons, and
all-edge no-new-report invariance; it is NOT empty scratch. -/

/-- A 201-half pre-drain stage and 2-half dirty drain on the SAME
bankRepairNext scheduler. Neither is asserted as a theorem. -/
def BankRepairDigitCausalClocks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop) : Prop :=
  BankRepairHalfStage (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank) preDrain 201 ∧
  BankRepairHalfStage (bankRepairNext ring hbank)
    preDrain (BankRepairDigit ring hbank) 2

/-- Required masked-owner projection to phiD, not the unmasked
physical-target statement supplied by Closure.targetSetDigitStep. -/
def BankRepairDigitMaskedProjectionBridge {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (z : BankReferenceState ring hbank) (e : Fin n),
    piD (bankRepairNext ring hbank z e).val.1 =
      phiD ring (piD z.val.1) e

/-- The E.G35 all-edge causal no-new-report invariant. -/
def BankRepairDigitPreDrainClosed {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop) : Prop :=
  ∀ z, preDrain z → ∀ e : Fin n,
    preDrain (bankRepairNext ring hbank z e)

/-- E.G36: the physical post-dirty cut must imply the actual
generated barred digit membership, not a separate ghost assertion. -/
def BankRepairDigitAcceptedCut {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (afterDrain : BankReferenceState ring hbank → Prop) : Prop :=
  ∀ z, afterDrain z → BankRepairDigit ring hbank z

private theorem bankRepairDigitHalfReserve {S : Type} {n : Nat}
    (next : S → Fin n → S) (A P : S → Prop) (allowance : Nat)
    (hsecond : ∀ y, A y → ∀ T,
      2 * costNumerator next P y T ≤ n ^ T * allowance) :
    ∀ y T,
      2 * costNumerator next P y T ≤
        2 * costNumerator next (fun z => A z ∨ P z) y T +
          n ^ T * allowance := by
  classical
  intro y T
  induction T generalizing y with
  | zero =>
      simp only [costNumerator_zero, Nat.mul_zero, Nat.zero_add]
      exact Nat.zero_le _
  | succ T ih =>
      by_cases hp : P y
      · have hu : A y ∨ P y := Or.inr hp
        rw [costNumerator_terminal next P y hp (T + 1),
          costNumerator_terminal next (fun z => A z ∨ P z)
            y hu (T + 1)]
        simp only [Nat.mul_zero, Nat.zero_add]
        exact Nat.zero_le _
      · by_cases ha : A y
        · have hu : A y ∨ P y := Or.inl ha
          rw [costNumerator_terminal next (fun z => A z ∨ P z)
            y hu (T + 1)]
          simpa only [Nat.mul_zero, Nat.zero_add] using
            hsecond y ha (T + 1)
        · have hu : ¬ (A y ∨ P y) := by
            intro h
            rcases h with hA | hP
            · exact ha hA
            · exact hp hP
          have hs :
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum ≤
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next (fun z => A z ∨ P z)
                  (next y e) T)).sum +
                n ^ (T + 1) * allowance := by
            calc
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum =
                  (List.ofFn (fun e : Fin n =>
                    2 * costNumerator next P (next y e) T)).sum := by
                    rw [ofFn_sum_mul_left]
              _ ≤ (List.ofFn (fun e : Fin n =>
                    2 * costNumerator next
                      (fun z => A z ∨ P z) (next y e) T +
                        n ^ T * allowance)).sum :=
                    ofFn_sum_le _ _ (fun e => ih (next y e))
              _ = 2 * (List.ofFn (fun e : Fin n =>
                    costNumerator next (fun z => A z ∨ P z)
                      (next y e) T)).sum +
                      n ^ (T + 1) * allowance := by
                    rw [ofFn_sum_add, ofFn_sum_const,
                      ofFn_sum_mul_left, Nat.pow_succ]
                    ac_rfl
          rw [costNumerator_succ next P y hp T,
            costNumerator_succ next (fun z => A z ∨ P z) y hu T]
          omega

private theorem bankRepairDigitHalfCompose {S : Type} {n : Nat}
    (next : S → Fin n → S) (A B Target : S → Prop)
    (a b : Nat)
    (hfirst : BankRepairHalfStage next A B a)
    (hsecond : BankRepairHalfStage next B Target b) :
    BankRepairHalfStage next A Target (a + b) := by
  intro x hx T
  have hfirstUnion :
      2 * costNumerator next (fun z => B z ∨ Target z) x T ≤
        n ^ T * (a * n ^ 2) := by
    have hmono := Prob.costNumerator_target_mono next B
      (fun z => B z ∨ Target z)
      (fun z hz => Or.inl hz) x T
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono)
      (hfirst x hx T)
  have hreserve := bankRepairDigitHalfReserve next B Target
    (b * n ^ 2) (fun y hy T => hsecond y hy T) x T
  calc
    2 * costNumerator next Target x T ≤
        2 * costNumerator next (fun z => B z ∨ Target z) x T +
          n ^ T * (b * n ^ 2) := hreserve
    _ ≤ n ^ T * (a * n ^ 2) + n ^ T * (b * n ^ 2) :=
      Nat.add_le_add_right hfirstUnion _
    _ = n ^ T * ((a + b) * n ^ 2) := by
      rw [Nat.add_mul, Nat.mul_add]

/-- 203 half units imply the separately rounded 102 whole units. -/
theorem bankRepairDigitStageOfHalf {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hhalf : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDigit ring hbank) 203) :
    BankRepairDigitStage ring hbank := by
  constructor
  · intro z hz
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (bankRepairNext ring hbank)
      (BankRepairDigit ring hbank)
      (by omega : 0 < n) z (102 * n ^ 2)).2
    intro T
    have hcost := hhalf z hz T
    have hscale :
        n ^ T * (203 * n ^ 2) =
          203 * (n ^ T * n ^ 2) := by
      ac_rfl
    rw [hscale] at hcost
    have hrounded :
        costNumerator (bankRepairNext ring hbank)
          (BankRepairDigit ring hbank) z T ≤
            102 * (n ^ T * n ^ 2) := by
      omega
    calc
      costNumerator (bankRepairNext ring hbank)
          (BankRepairDigit ring hbank) z T ≤
            102 * (n ^ T * n ^ 2) := hrounded
      _ = n ^ T * (102 * n ^ 2) := by ac_rfl
  · exact hhalf

/-- Exact conditional R10 DigitStage producer, same scheduler. -/
theorem bankRepairDigitStageOfCausalClocks {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hclocks : BankRepairDigitCausalClocks ring hbank preDrain) :
    BankRepairDigitStage ring hbank := by
  have hcombined : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDigit ring hbank) (201 + 2) :=
    bankRepairDigitHalfCompose (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      preDrain (BankRepairDigit ring hbank)
      201 2 hclocks.1 hclocks.2
  exact bankRepairDigitStageOfHalf ring hn hbank hcombined

/-- Retain the earlier R-fold receipt while obtaining barred D. -/
theorem bankRepairDigitDBarredHalfOfCausalClocks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hpres : BankRepairReceiptPreservation ring hbank)
    (hclocks : BankRepairDigitCausalClocks ring hbank preDrain) :
    BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDBarred ring hbank) 203 := by
  have hcombined : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDigit ring hbank) (201 + 2) :=
    bankRepairDigitHalfCompose (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      preDrain (BankRepairDigit ring hbank)
      201 2 hclocks.1 hclocks.2
  intro z hz T
  have hstrength :=
    costNumeratorTargetOnClosed (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDigit ring hbank)
      hpres.2.2.1
      (fun y hy hd => ⟨hy, hd⟩) T z hz
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hstrength)
    (hcombined z hz T)

end L3.RenewalReferenceClock

/-!
Polynomial growth and nominated dirty-edge bridge.
Source-only continuation.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

private theorem bankRepairDigitIndexLePower (s : Nat) :
    s ≤ 2 ^ s := by
  induction s with
  | zero =>
      simp only [Nat.pow_zero]
      omega
  | succ s ih =>
      have hp : 0 < (2 : Nat) ^ s := Nat.pow_pos (by omega)
      rw [Nat.pow_succ]
      omega

private theorem bankRepairDigitPowerMonotone
    (a b k : Nat) (hab : a ≤ b) :
    a ^ k ≤ b ^ k := by
  induction k with
  | zero =>
      simp only [Nat.pow_zero]
      exact Nat.le_refl 1
  | succ k ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih hab

private theorem bankRepairDigitScalePow
    (a b x i j : Nat) :
    (a * x ^ i) * (b * x ^ j) =
      (a * b) * x ^ (i + j) := by
  rw [Nat.pow_add]
  ac_rfl

/-- A deliberately loose degree-five envelope; all factors are Nat.
The coefficient 4096 leaves twelve exponent bits and avoids division
or real logarithms. -/
private theorem bankRepairDigitNuUpper (s : Nat) :
    bankRepairDigitNu s ≤
      4096 * ((2 : Nat) ^ s) ^ 5 := by
  have hx : 0 < (2 : Nat) ^ s := Nat.pow_pos (by omega)
  have hs : s ≤ (2 : Nat) ^ s :=
    bankRepairDigitIndexLePower s
  have hr :
      bankRepairDigitRadius s ≤ (2 : Nat) ^ s := by
    unfold bankRepairDigitRadius
    omega
  have he :
      bankRepairDigitExponent s ≤ (2 : Nat) ^ s := by
    unfold bankRepairDigitExponent
    exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
      (by omega : s - 1 ≤ s)
  have hXLeTwo : (2 : Nat) ^ s ≤ ((2 : Nat) ^ s) ^ 2 := by
    simpa only [Nat.pow_one] using
      (Nat.pow_le_pow_right hx (by omega : (1 : Nat) ≤ 2))
  have hXLeThree : (2 : Nat) ^ s ≤ ((2 : Nat) ^ s) ^ 3 := by
    simpa only [Nat.pow_one] using
      (Nat.pow_le_pow_right hx (by omega : (1 : Nat) ≤ 3))
  have hXLeFour : (2 : Nat) ^ s ≤ ((2 : Nat) ^ s) ^ 4 := by
    simpa only [Nat.pow_one] using
      (Nat.pow_le_pow_right hx (by omega : (1 : Nat) ≤ 4))
  have hXLeFive : (2 : Nat) ^ s ≤ ((2 : Nat) ^ s) ^ 5 := by
    simpa only [Nat.pow_one] using
      (Nat.pow_le_pow_right hx (by omega : (1 : Nat) ≤ 5))
  have hXTwoLeThree :
      ((2 : Nat) ^ s) ^ 2 ≤ ((2 : Nat) ^ s) ^ 3 :=
    Nat.pow_le_pow_right hx (by omega : (2 : Nat) ≤ 3)
  have hXTwoLeFour :
      ((2 : Nat) ^ s) ^ 2 ≤ ((2 : Nat) ^ s) ^ 4 :=
    Nat.pow_le_pow_right hx (by omega : (2 : Nat) ≤ 4)
  have hXTwoLeFive :
      ((2 : Nat) ^ s) ^ 2 ≤ ((2 : Nat) ^ s) ^ 5 :=
    Nat.pow_le_pow_right hx (by omega : (2 : Nat) ≤ 5)
  have hXThreeLeFour :
      ((2 : Nat) ^ s) ^ 3 ≤ ((2 : Nat) ^ s) ^ 4 :=
    Nat.pow_le_pow_right hx (by omega : (3 : Nat) ≤ 4)
  have hXThreeLeFive :
      ((2 : Nat) ^ s) ^ 3 ≤ ((2 : Nat) ^ s) ^ 5 :=
    Nat.pow_le_pow_right hx (by omega : (3 : Nat) ≤ 5)
  have hXFourLeFive :
      ((2 : Nat) ^ s) ^ 4 ≤ ((2 : Nat) ^ s) ^ 5 :=
    Nat.pow_le_pow_right hx (by omega : (4 : Nat) ≤ 5)
  have hXTwoPos : 0 < ((2 : Nat) ^ s) ^ 2 :=
    Nat.pow_pos hx
  have hXThreePos : 0 < ((2 : Nat) ^ s) ^ 3 :=
    Nat.pow_pos hx
  have hXFourPos : 0 < ((2 : Nat) ^ s) ^ 4 :=
    Nat.pow_pos hx
  have hrTwo :
      (bankRepairDigitRadius s) ^ 2 ≤ ((2 : Nat) ^ s) ^ 2 :=
    bankRepairDigitPowerMonotone _ _ 2 hr
  have hrThree :
      (bankRepairDigitRadius s) ^ 3 ≤ ((2 : Nat) ^ s) ^ 3 :=
    bankRepairDigitPowerMonotone _ _ 3 hr
  have hrFour :
      (bankRepairDigitRadius s) ^ 4 ≤ ((2 : Nat) ^ s) ^ 4 :=
    bankRepairDigitPowerMonotone _ _ 4 hr

  have hm :
      bankRepairDigitLeadingRecords s ≤ 2 * (2 : Nat) ^ s := by
    unfold bankRepairDigitLeadingRecords
    omega
  have hmp :
      bankRepairDigitLeadingRecords s + 1 ≤
        3 * (2 : Nat) ^ s := by
    omega
  have hlength :
      bankRepairDigitLeadingLength s ≤ 3 * (2 : Nat) ^ s := by
    unfold bankRepairDigitLeadingLength
    omega
  have hrplus :
      bankRepairDigitRadius s + 2 ≤
        3 * (2 : Nat) ^ s := by
    omega
  have hSquare :
      bankRepairDigitLeadingSquare s ≤
        6 * ((2 : Nat) ^ s) ^ 2 := by
    change bankRepairDigitLeadingRecords s *
      (bankRepairDigitLeadingRecords s + 1) ≤
        6 * ((2 : Nat) ^ s) ^ 2
    calc
      _ ≤ (2 * (2 : Nat) ^ s) *
          (3 * (2 : Nat) ^ s) :=
        Nat.mul_le_mul hm hmp
      _ = 6 * ((2 : Nat) ^ s) ^ 2 := by
        simpa only [Nat.pow_one, Nat.reduceAdd, Nat.reduceMul] using
          (bankRepairDigitScalePow 2 3 ((2 : Nat) ^ s) 1 1)
  have hTotal :
      bankRepairDigitLeadingTotal s ≤
        7 * ((2 : Nat) ^ s) ^ 2 := by
    unfold bankRepairDigitLeadingTotal
    omega
  have hTotalPlus :
      bankRepairDigitLeadingTotal s + bankRepairDigitRadius s ≤
        8 * ((2 : Nat) ^ s) ^ 2 := by
    omega
  have hFirst :
      bankRepairDigitLeadingSquare s *
        (bankRepairDigitLeadingRecords s + 1) ≤
          18 * ((2 : Nat) ^ s) ^ 3 := by
    calc
      _ ≤ (6 * ((2 : Nat) ^ s) ^ 2) *
          (3 * (2 : Nat) ^ s) :=
        Nat.mul_le_mul hSquare hmp
      _ = 18 * ((2 : Nat) ^ s) ^ 3 := by
        simpa only [Nat.pow_one, Nat.reduceAdd, Nat.reduceMul] using
          (bankRepairDigitScalePow 6 3 ((2 : Nat) ^ s) 2 1)
  have hSecond :
      bankRepairDigitLeadingTotal s *
        (bankRepairDigitRadius s + 2) ≤
          21 * ((2 : Nat) ^ s) ^ 3 := by
    calc
      _ ≤ (7 * ((2 : Nat) ^ s) ^ 2) *
          (3 * (2 : Nat) ^ s) :=
        Nat.mul_le_mul hTotal hrplus
      _ = 21 * ((2 : Nat) ^ s) ^ 3 := by
        simpa only [Nat.pow_one, Nat.reduceAdd, Nat.reduceMul] using
          (bankRepairDigitScalePow 7 3 ((2 : Nat) ^ s) 2 1)
  have hThirdRaw :
      (bankRepairDigitLeadingTotal s + bankRepairDigitRadius s) *
        (bankRepairDigitRadius s + 2) ≤
          24 * ((2 : Nat) ^ s) ^ 3 := by
    calc
      _ ≤ (8 * ((2 : Nat) ^ s) ^ 2) *
          (3 * (2 : Nat) ^ s) :=
        Nat.mul_le_mul hTotalPlus hrplus
      _ = 24 * ((2 : Nat) ^ s) ^ 3 := by
        simpa only [Nat.pow_one, Nat.reduceAdd, Nat.reduceMul] using
          (bankRepairDigitScalePow 8 3 ((2 : Nat) ^ s) 2 1)
  have hThird :
      2 * (bankRepairDigitLeadingTotal s + bankRepairDigitRadius s) *
        (bankRepairDigitRadius s + 2) ≤
          48 * ((2 : Nat) ^ s) ^ 3 := by
    calc
      _ = 2 * ((bankRepairDigitLeadingTotal s +
          bankRepairDigitRadius s) *
          (bankRepairDigitRadius s + 2)) := by ac_rfl
      _ ≤ 2 * (24 * ((2 : Nat) ^ s) ^ 3) :=
        Nat.mul_le_mul_left 2 hThirdRaw
      _ = 48 * ((2 : Nat) ^ s) ^ 3 := by omega
  have hRecordSquare :
      (bankRepairDigitLeadingRecords s) ^ 2 ≤
        4 * ((2 : Nat) ^ s) ^ 3 := by
    calc
      _ = bankRepairDigitLeadingRecords s *
          bankRepairDigitLeadingRecords s := by rw [Nat.pow_two]
      _ ≤ (2 * (2 : Nat) ^ s) *
          (2 * (2 : Nat) ^ s) :=
        Nat.mul_le_mul hm hm
      _ = 4 * ((2 : Nat) ^ s) ^ 2 := by
        simpa only [Nat.pow_one, Nat.reduceAdd, Nat.reduceMul] using
          (bankRepairDigitScalePow 2 2 ((2 : Nat) ^ s) 1 1)
      _ ≤ 4 * ((2 : Nat) ^ s) ^ 3 :=
        Nat.mul_le_mul_left 4 hXTwoLeThree
  have hJ :
      bankRepairDigitBoundaryServices s ≤
        100 * ((2 : Nat) ^ s) ^ 3 := by
    unfold bankRepairDigitBoundaryServices
    omega

  have hBase :
      bankRepairDigitBaseCount (bankRepairDigitRadius s) ≤
        9 * ((2 : Nat) ^ s) ^ 2 := by
    unfold bankRepairDigitBaseCount
    omega
  have hFactor :
      2 * (bankRepairDigitRadius s) ^ 2 + 1 ≤
        3 * ((2 : Nat) ^ s) ^ 2 := by
    omega
  have hForwardProduct :
      (2 * (bankRepairDigitRadius s) ^ 2 + 1) *
        bankRepairDigitBaseCount (bankRepairDigitRadius s) ≤
          27 * ((2 : Nat) ^ s) ^ 4 := by
    calc
      _ ≤ (3 * ((2 : Nat) ^ s) ^ 2) *
          (9 * ((2 : Nat) ^ s) ^ 2) :=
        Nat.mul_le_mul hFactor hBase
      _ = 27 * ((2 : Nat) ^ s) ^ 4 := by
        simpa only [Nat.reduceAdd, Nat.reduceMul] using
          (bankRepairDigitScalePow 3 9 ((2 : Nat) ^ s) 2 2)
  have hForward :
      bankRepairDigitForwardCount (bankRepairDigitRadius s) ≤
        35 * ((2 : Nat) ^ s) ^ 4 := by
    unfold bankRepairDigitForwardCount
    omega
  have hReturn :
      bankRepairDigitReturnCount (bankRepairDigitRadius s) ≤
        8 * ((2 : Nat) ^ s) ^ 2 := by
    unfold bankRepairDigitReturnCount
    omega
  have hInside :
      2 * (bankRepairDigitRadius s) ^ 2 +
        8 * bankRepairDigitRadius s + 1 ≤
          11 * ((2 : Nat) ^ s) ^ 2 := by
    omega
  have hSettledProduct :
      (bankRepairDigitRadius s) ^ 2 *
        (2 * (bankRepairDigitRadius s) ^ 2 +
          8 * bankRepairDigitRadius s + 1) ≤
            11 * ((2 : Nat) ^ s) ^ 4 := by
    calc
      _ ≤ ((2 : Nat) ^ s) ^ 2 *
          (11 * ((2 : Nat) ^ s) ^ 2) :=
        Nat.mul_le_mul hrTwo hInside
      _ = 11 * ((2 : Nat) ^ s) ^ 4 := by
        simpa only [Nat.one_mul, Nat.reduceAdd, Nat.reduceMul] using
          (bankRepairDigitScalePow 1 11 ((2 : Nat) ^ s) 2 2)
  have hSettled :
      bankRepairDigitSettledCount (bankRepairDigitRadius s) ≤
        16 * ((2 : Nat) ^ s) ^ 4 := by
    unfold bankRepairDigitSettledCount
    omega
  have hEnvelope :
      bankRepairDigitPairEnvelope (bankRepairDigitRadius s) ≤
        116 * ((2 : Nat) ^ s) ^ 4 := by
    unfold bankRepairDigitPairEnvelope
    omega
  have hEnvelopeFour :
      4 * bankRepairDigitPairEnvelope (bankRepairDigitRadius s) ≤
        464 * ((2 : Nat) ^ s) ^ 4 := by
    calc
      _ ≤ 4 * (116 * ((2 : Nat) ^ s) ^ 4) :=
        Nat.mul_le_mul_left 4 hEnvelope
      _ = 464 * ((2 : Nat) ^ s) ^ 4 := by omega
  have hExponentPlus :
      bankRepairDigitExponent s + 3 ≤
        4 * (2 : Nat) ^ s := by
    omega
  have hPairUpper :
      bankRepairDigitPairUpper s ≤
        1856 * ((2 : Nat) ^ s) ^ 5 := by
    change 4 * bankRepairDigitPairEnvelope (bankRepairDigitRadius s) *
      (bankRepairDigitExponent s + 3) ≤
        1856 * ((2 : Nat) ^ s) ^ 5
    calc
      _ ≤ (464 * ((2 : Nat) ^ s) ^ 4) *
          (4 * (2 : Nat) ^ s) :=
        Nat.mul_le_mul hEnvelopeFour hExponentPlus
      _ = 1856 * ((2 : Nat) ^ s) ^ 5 := by
        simpa only [Nat.pow_one, Nat.reduceAdd, Nat.reduceMul] using
          (bankRepairDigitScalePow 464 4 ((2 : Nat) ^ s) 4 1)
  have hBoundaryUpper :
      bankRepairDigitBoundaryUpper s ≤
        294 * ((2 : Nat) ^ s) ^ 5 := by
    unfold bankRepairDigitBoundaryUpper
    omega
  have hValueFactor :
      bankRepairDigitExponent s + s + 6 ≤
        8 * (2 : Nat) ^ s := by
    omega
  have hValueUpper :
      bankRepairDigitValueUpper s ≤
        24 * ((2 : Nat) ^ s) ^ 5 := by
    change 3 * bankRepairDigitRadius s *
      (bankRepairDigitExponent s + s + 6) ≤
        24 * ((2 : Nat) ^ s) ^ 5
    calc
      _ ≤ (3 * (2 : Nat) ^ s) *
          (8 * (2 : Nat) ^ s) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 3 hr) hValueFactor
      _ = 24 * ((2 : Nat) ^ s) ^ 2 := by
        simpa only [Nat.pow_one, Nat.reduceAdd, Nat.reduceMul] using
          (bankRepairDigitScalePow 3 8 ((2 : Nat) ^ s) 1 1)
      _ ≤ 24 * ((2 : Nat) ^ s) ^ 5 :=
        Nat.mul_le_mul_left 24 hXTwoLeFive
  unfold bankRepairDigitNu
  omega

/-- For s >= 7, the next degree-five bound fits in the current
double-exponential allowance, with twelve bits of coefficient slack. -/
private theorem bankRepairDigitExponentRoom
    (s : Nat) (hs : 7 ≤ s) :
    5 * (s + 1) + 12 ≤ bankRepairDigitExponent s := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, s = 7 + k :=
    ⟨s - 7, by omega⟩
  subst s
  induction k with
  | zero =>
      change 52 ≤ 64
      omega
  | succ k ih =>
      have hstep :=
        bankRepairDigitExponentSucc (7 + k) (by omega)
      have hpositive : 5 ≤ bankRepairDigitExponent (7 + k) := by
        omega
      rw [show 7 + (k + 1) = 7 + k + 1 by omega, hstep]
      omega

private theorem bankRepairDigitNuNextBelowPower
    (s : Nat) (hs : 7 ≤ s) :
    bankRepairDigitNu (s + 1) ≤
      2 ^ bankRepairDigitExponent s := by
  have hupper := bankRepairDigitNuUpper (s + 1)
  have hshape :
      4096 * ((2 : Nat) ^ (s + 1)) ^ 5 =
        (2 : Nat) ^ (5 * (s + 1) + 12) := by
    have hpow :
        ((2 : Nat) ^ (s + 1)) ^ 5 =
          (2 : Nat) ^ ((s + 1) * 5) := by
      rw [Nat.pow_mul]
    calc
      4096 * ((2 : Nat) ^ (s + 1)) ^ 5 =
          (2 : Nat) ^ 12 * ((2 : Nat) ^ (s + 1)) ^ 5 := by
          rfl
      _ = (2 : Nat) ^ 12 * (2 : Nat) ^ ((s + 1) * 5) := by
          rw [hpow]
      _ = (2 : Nat) ^ (12 + (s + 1) * 5) := by
          rw [Nat.pow_add]
      _ = (2 : Nat) ^ (5 * (s + 1) + 12) := by
          have heq : 12 + (s + 1) * 5 = 5 * (s + 1) + 12 := by
            omega
          rw [heq]
  calc
    bankRepairDigitNu (s + 1) ≤
        4096 * ((2 : Nat) ^ (s + 1)) ^ 5 := hupper
    _ = (2 : Nat) ^ (5 * (s + 1) + 12) := hshape
    _ ≤ 2 ^ bankRepairDigitExponent s :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
        (bankRepairDigitExponentRoom s hs)

/-- Unconditional solution of the named inter-width growth Prop.
The deliberately stronger bound ignores the factor nu_s except for
its positivity. -/
theorem bankRepairDigitNuGrowthProved :
    BankRepairDigitNuGrowth := by
  intro s hs
  have hnext := bankRepairDigitNuNextBelowPower s hs
  have henv :
      0 < bankRepairDigitPairEnvelope (bankRepairDigitRadius s) := by
    unfold bankRepairDigitPairEnvelope
    omega
  have hpair :
      0 < bankRepairDigitPairUpper s := by
    unfold bankRepairDigitPairUpper
    exact Nat.mul_pos
      (Nat.mul_pos (by omega : 0 < (4 : Nat)) henv)
      (by omega : 0 < bankRepairDigitExponent s + 3)
  have hnu : 1 ≤ bankRepairDigitNu s := by
    unfold bankRepairDigitNu
    omega
  have hfactor :
      2 ^ bankRepairDigitExponent s ≤
        bankRepairDigitNu s * 2 ^ bankRepairDigitExponent s := by
    have h := Nat.mul_le_mul_right
      (2 ^ bankRepairDigitExponent s) hnu
    simpa only [Nat.one_mul] using h
  exact Nat.le_trans hnext hfactor

/-- No growth assumption: every BANK population satisfies the
cross-multiplied integer half-certificate. The separate analytic
logarithm comparison remains external. -/
theorem bankRepairDigitIntegerHalf {n : Nat}
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairDigitIntegerHalf n (ceilLogTwo (ceilLogTwo n)) := by
  exact bankRepairDigitIntegerHalfOfGrowth hn hbank
    bankRepairDigitNuGrowthProved

/-! The following is an exact missing *physical* bridge, not a
claim that the BANK protocol satisfies it. A single decreasing edge
and nonincrease on all edges suffice for an n^2 dirty drain, even
without a harmonic-series formalization. -/

/-- Missing local BANK row obligations for the dirty contact phase.
Every legal pre-drain state has at most n dirty sites, a clean state
belongs to the generated digit target, one nominated edge decreases
dirty count whenever the target has not been reached, and no literal
BANK edge increases it. -/
def BankRepairDigitDirtyNominatedBridge {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop) : Prop :=
  ∃ (dirty : BankReferenceState ring hbank → Nat)
    (chosen : BankReferenceState ring hbank → Fin n),
    (∀ z, preDrain z → dirty z ≤ n) ∧
    (∀ z, preDrain z → dirty z = 0 →
      BankRepairDigit ring hbank z) ∧
    (∀ z, preDrain z → ¬ BankRepairDigit ring hbank z →
      dirty (bankRepairNext ring hbank z (chosen z)) + 1 ≤ dirty z) ∧
    (∀ z, preDrain z → ¬ BankRepairDigit ring hbank z →
      ∀ e : Fin n,
        dirty (bankRepairNext ring hbank z e) ≤ dirty z)

/-- On a forward-closed class, adjoining its complement to the
target changes no finite-horizon first-hit cost at entry. -/
private theorem bankRepairDigitCostClosedTarget
    {S : Type} {n : Nat} (next : S → Fin n → S)
    (A P : S → Prop)
    (hclosed : ∀ z, A z → ∀ e : Fin n, A (next z e)) :
    ∀ z, A z → ∀ T,
      costNumerator next P z T =
        costNumerator next (fun y => ¬ A y ∨ P y) z T := by
  classical
  intro z hz T
  induction T generalizing z with
  | zero =>
      simp only [costNumerator_zero]
  | succ T ih =>
      by_cases hp : P z
      · rw [costNumerator_terminal next P z hp (T + 1),
          costNumerator_terminal next (fun y => ¬ A y ∨ P y)
            z (Or.inr hp) (T + 1)]
      · have hu : ¬ (¬ A z ∨ P z) := by
          intro h
          rcases h with hna | hp'
          · exact hna hz
          · exact hp hp'
        rw [costNumerator_succ next P z hp T,
          costNumerator_succ next (fun y => ¬ A y ∨ P y)
            z hu T]
        have hsum := ofFn_sum_eq
          (fun e : Fin n => costNumerator next P (next z e) T)
          (fun e : Fin n =>
            costNumerator next (fun y => ¬ A y ∨ P y)
              (next z e) T)
          (fun e => ih (next z e) (hclosed z hz e))
        rw [hsum]

/-- Conditional *real first-hit* 2-half dirty drain on bankRepairNext.
It uses the existing core nominated-edge Bellman bound, not an
independent edge tape. No physical row discharge is claimed here. -/
theorem bankRepairDigitDirtyHalfOfNominatedBridge {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hclosed : BankRepairDigitPreDrainClosed ring hbank preDrain)
    (hdirty : BankRepairDigitDirtyNominatedBridge
      ring hbank preDrain) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      preDrain (BankRepairDigit ring hbank) 2 := by
  classical
  rcases hdirty with ⟨dirty, chosen, hcap, hclean, hdrop, hnoninc⟩
  have hglobal :
      ∀ z T,
        costNumerator (bankRepairNext ring hbank)
          (fun y => ¬ preDrain y ∨ BankRepairDigit ring hbank y) z T ≤
          n ^ T * (n * (if preDrain z then dirty z else 0)) :=
    Prob.costNumerator_le_of_nominated_edge
      (bankRepairNext ring hbank)
      (fun y => ¬ preDrain y ∨ BankRepairDigit ring hbank y)
      (fun y => if preDrain y then dirty y else 0)
      chosen
      (fun y hnot => by
        have hy : preDrain y := by
          by_cases hp : preDrain y
          · exact hp
          · exact False.elim (hnot (Or.inl hp))
        have hnotDigit : ¬ BankRepairDigit ring hbank y := by
          intro hd
          exact hnot (Or.inr hd)
        have hnext := hclosed y hy (chosen y)
        simpa only [if_pos hy, if_pos hnext] using
          hdrop y hy hnotDigit)
      (fun y hnot e => by
        have hy : preDrain y := by
          by_cases hp : preDrain y
          · exact hp
          · exact False.elim (hnot (Or.inl hp))
        have hnotDigit : ¬ BankRepairDigit ring hbank y := by
          intro hd
          exact hnot (Or.inr hd)
        have hnext := hclosed y hy e
        simpa only [if_pos hy, if_pos hnext] using
          hnoninc y hy hnotDigit e)
  intro z hz T
  have heq := bankRepairDigitCostClosedTarget
    (bankRepairNext ring hbank)
    preDrain (BankRepairDigit ring hbank)
    (fun y hy e => hclosed y hy e) z hz T
  have hle := hglobal z T
  rw [← heq] at hle
  simp only [if_pos hz] at hle
  have hcapz : n * dirty z ≤ n * n :=
    Nat.mul_le_mul_left n (hcap z hz)
  calc
    2 * costNumerator (bankRepairNext ring hbank)
        (BankRepairDigit ring hbank) z T ≤
      2 * (n ^ T * (n * dirty z)) :=
      Nat.mul_le_mul_left 2 hle
    _ ≤ 2 * (n ^ T * (n * n)) :=
      Nat.mul_le_mul_left 2
        (Nat.mul_le_mul_left (n ^ T) hcapz)
    _ = n ^ T * (2 * n ^ 2) := by
      simp only [Nat.pow_two]
      ac_rfl

/-- Connect the exact missing dirty bridge to the already-proved
conditional 201+2 half-clock composition. -/
theorem bankRepairDigitCausalClocksOfDirtyBridge {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hpre : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank) preDrain 201)
    (hclosed : BankRepairDigitPreDrainClosed ring hbank preDrain)
    (hdirty : BankRepairDigitDirtyNominatedBridge
      ring hbank preDrain) :
    BankRepairDigitCausalClocks ring hbank preDrain := by
  exact ⟨hpre,
    bankRepairDigitDirtyHalfOfNominatedBridge
      ring hbank preDrain hclosed hdirty⟩

end L3.RenewalReferenceClock


/-!
Actual masked BANK digit projection and dirty-bit first-hit bridge.
The unrestricted projection property fails on FIRE edges.
The mask alters req/grant only, so every ProjD field is unchanged
by the mask. But phiD uses the E native output and does not
perform a FIRE birth. Concrete old pair:
source pack=0, mode=CWAIT, req=true, grant=false, l=false, b=0;
responder pack=1, tok=CL1, grant=true, l=false, b=0.
With a fresh completed BANK payer the BANK cut can also be true:
the BANK success guard and F2 FIRE are simultaneously enabled.
A root may exist at a different site.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Masking commutes with ProjD on both owners, even on FIRE. -/
private theorem bankRepairDigitMaskedPairProjection
    (c : Compiled) (suppress : Bool) (x y : Agent c) :
    ProjD.ofAgent (renewalMaskedPair c suppress x y).1 =
      ProjD.ofAgent (transition c x y).1 ∧
    ProjD.ofAgent (renewalMaskedPair c suppress x y).2 =
      ProjD.ofAgent (transition c x y).2 := by
  cases suppress <;> constructor <;> rfl

/-- Corrected digit projection for any valid BANK reference whose
selected OLD pair does not FIRE. No condition on the mask bit. -/
theorem bankRepairDigitMaskedProjectionOfNoFire {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hfire : oldFire (z.val.1 e)
      (z.val.1 (ring.rightNeighbor e)) = none) :
    piD (bankRepairNext ring hbank z e).val.1 =
      phiD ring (piD z.val.1) e := by
  have hmask := bankRepairDigitMaskedPairProjection
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring z.val.1 z.val.2 e)
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
  have hreal := transitionD_noFire
    (compileAdvice (ceilLogTwo n))
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) hfire
  have hp :
      (ProjD.ofAgent
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1,
       ProjD.ofAgent
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2) =
        pairD (piD z.val.1 e)
          (piD z.val.1 (ring.rightNeighbor e)) := by
    apply Prod.ext
    · exact hmask.1.trans (congrArg Prod.fst hreal)
    · exact hmask.2.trans (congrArg Prod.snd hreal)
  change piD (renewalMaskedStep ring z.val.1 e
      (renewalBankCut ring z.val.1 z.val.2 e)) =
    phiD ring (piD z.val.1) e
  funext i
  by_cases he : i = e
  · subst i
    simpa [piD, phiD, projectedEdge, renewalMaskedStep]
      using (congrArg Prod.fst hp)
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [piD, phiD, projectedEdge, renewalMaskedStep, he]
        using (congrArg Prod.snd hp)
    · simp [piD, phiD, projectedEdge, renewalMaskedStep, he, hj]

/-- The no-FIRE domain is an explicit physical hypothesis,
not an automatic consequence of the BANK observer stamp. -/
def BankRepairDigitNoFireClass {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop) : Prop :=
  ∀ z, preDrain z → ∀ e : Fin n,
    oldFire (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) = none

theorem bankRepairDigitProjectionOnNoFireClass {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hno : BankRepairDigitNoFireClass ring hbank preDrain) :
    ∀ z, preDrain z → ∀ e : Fin n,
      piD (bankRepairNext ring hbank z e).val.1 =
        phiD ring (piD z.val.1) e := by
  intro z hz e
  exact bankRepairDigitMaskedProjectionOfNoFire
    ring hbank z e (hno z hz e)

/-- Count precisely the Agent.topDirty flags, not a ghost label. -/
def bankRepairDigitDirtyUnit (b : Bool) : Nat := if b then 1 else 0

def bankRepairDigitDirtyCount {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Nat :=
  (List.ofFn (fun i : Fin n =>
    bankRepairDigitDirtyUnit (z.val.1 i).topDirty)).sum

theorem bankRepairDigitDirtyCountCap {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    bankRepairDigitDirtyCount ring hbank z ≤ n := by
  unfold bankRepairDigitDirtyCount
  have hsum := ofFn_sum_le
    (fun i : Fin n => bankRepairDigitDirtyUnit (z.val.1 i).topDirty)
    (fun _ : Fin n => 1)
    (by
      intro i
      cases hb : (z.val.1 i).topDirty <;>
        simp [bankRepairDigitDirtyUnit, hb])
  simpa only [ofFn_sum_const, Nat.mul_one] using hsum

private theorem bankRepairDigitDirtyCountZeroOfClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hclean : ∀ i : Fin n, (z.val.1 i).topDirty = false) :
    bankRepairDigitDirtyCount ring hbank z = 0 := by
  unfold bankRepairDigitDirtyCount
  have hsum := ofFn_sum_eq
    (fun i : Fin n => bankRepairDigitDirtyUnit (z.val.1 i).topDirty)
    (fun _ : Fin n => 0)
    (by intro i; simp [bankRepairDigitDirtyUnit, hclean i])
  rw [hsum, ofFn_sum_const]
  omega

/-- Bounded minimum principle on Fin; no extra library search. -/
private theorem bankRepairDigitLeastTrue {n : Nat}
    (f : Fin n → Bool)
    (hex : ∃ i : Fin n, f i = true) :
    ∃ i : Fin n, f i = true ∧
      ∀ j : Fin n, j.val < i.val → f j = false := by
  have hbounded :
      ∀ k : Nat, (∃ i : Fin n, i.val ≤ k ∧ f i = true) →
        ∃ i : Fin n, i.val ≤ k ∧ f i = true ∧
          ∀ j : Fin n, j.val < i.val → f j = false := by
    intro k
    induction k with
    | zero =>
        intro h
        obtain ⟨i, hi, hf⟩ := h
        refine ⟨i, hi, hf, ?_⟩
        intro j hj
        exact False.elim (by omega : False)
    | succ k ih =>
        intro h
        by_cases hsmall : ∃ i : Fin n, i.val ≤ k ∧ f i = true
        · obtain ⟨i, hi, hf, hmin⟩ := ih hsmall
          exact ⟨i, (by omega), hf, hmin⟩
        · obtain ⟨i, hi, hf⟩ := h
          have hnone : ∀ j : Fin n, j.val ≤ k → f j = false := by
            intro j hj
            cases hb : f j with
            | false => rfl
            | true => exact False.elim (hsmall ⟨j, hj, hb⟩)
          have heq : i.val = k + 1 := by
            by_cases hle : i.val ≤ k
            · exact False.elim (hsmall ⟨i, hle, hf⟩)
            · omega
          refine ⟨i, hi, hf, ?_⟩
          intro j hj
          exact hnone j (by omega)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨j, _, hj, hmin⟩ :=
    hbounded i.val ⟨i, Nat.le_refl _, hi⟩
  exact ⟨j, hj, hmin⟩

noncomputable def bankRepairDigitLeftmostDirtySite {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Fin n :=
  if h : ∃ i : Fin n, (z.val.1 i).topDirty = true then
    Classical.choose (bankRepairDigitLeastTrue
      (fun i : Fin n => (z.val.1 i).topDirty) h)
  else ⟨0, ring.hn⟩

theorem bankRepairDigitLeftmostDirtySpec {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hex : ∃ i : Fin n, (z.val.1 i).topDirty = true) :
    (z.val.1 (bankRepairDigitLeftmostDirtySite ring hbank z)).topDirty = true ∧
      ∀ j : Fin n,
        j.val < (bankRepairDigitLeftmostDirtySite ring hbank z).val →
          (z.val.1 j).topDirty = false := by
  unfold bankRepairDigitLeftmostDirtySite
  simpa only [dif_pos hex] using
    (Classical.choose_spec
      (bankRepairDigitLeastTrue
        (fun i : Fin n => (z.val.1 i).topDirty) hex))

noncomputable def bankRepairDigitIntoLeftmostDirty {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Fin n :=
  ring.leftNeighbor (bankRepairDigitLeftmostDirtySite ring hbank z)

private theorem bankRepairDigitRightOfLeft {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  change (((i.val + n - 1) % n + 1) % n) = i.val
  by_cases hz : i.val = 0
  · rw [hz]
    rw [Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have hs : i.val + n - 1 = (i.val - 1) + n := by omega
    rw [hs, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have ht : i.val - 1 + 1 = i.val := by omega
    rw [ht, Nat.mod_eq_of_lt i.isLt]

/-- Exact per-site TOP field row after identity proposals:
both touched OLD dirty bits clear; every other site frames. -/
def BankRepairDigitDirtyClearRows {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop) : Prop :=
  ∀ z, preDrain z → ∀ e i : Fin n,
    ((bankRepairNext ring hbank z e).val.1 i).topDirty =
      if i = e then false
      else if i = ring.rightNeighbor e then false
      else (z.val.1 i).topDirty

def BankRepairDigitIdentityProposals {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop) : Prop :=
  ∀ z, preDrain z → ∀ e i : Fin n,
    ((bankRepairNext ring hbank z e).val.1 i).d =
      (z.val.1 i).d

/-- The existing source/destination dirty equations in Closure
convert fixed visible digit values into immediate OLD dirty clearing. -/
private theorem bankRepairDigitPhiDirtyClearOfIdentity {n : Nat}
    {c : Compiled} (hn : 2 ≤ n)
    (ring : DirectedRing n) (p : Fin n → ProjD c) (e : Fin n)
    (hid : ∀ i : Fin n,
      ((phiD ring p e) i).top.d = (p i).top.d) :
    ∀ i : Fin n,
      ((phiD ring p e) i).top.topDirty =
        if i = e then false
        else if i = ring.rightNeighbor e then false
        else (p i).top.topDirty := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  intro i
  by_cases he : i = e
  · subst i
    have hdx :
        (pairD (p e) (p (ring.rightNeighbor e))).1.top.d =
          (p e).top.d := by
      simpa [phiD, projectedEdge] using hid e
    have hx :
        (pairD (p e) (p (ring.rightNeighbor e))).1.top.topDirty =
          false := by
      rw [Closure.digitDirtySourceFormula, hdx]
      cases hb : (p e).top.topDirty <;> simp [hb]
    simpa [phiD, projectedEdge] using hx
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hdy :
          (pairD (p e) (p (ring.rightNeighbor e))).2.top.d =
            (p (ring.rightNeighbor e)).top.d := by
        simpa [phiD, projectedEdge, hne] using
          hid (ring.rightNeighbor e)
      have hy :
          (pairD (p e) (p (ring.rightNeighbor e))).2.top.topDirty =
            false := by
        rw [Closure.digitDirtyDestinationFormula, hdy]
        cases hb : (p (ring.rightNeighbor e)).top.topDirty <;>
          simp [hb]
      simpa [phiD, projectedEdge, hne] using hy
    · simp [phiD, projectedEdge, he, hj]

/-- The field-row proof from true identity proposals and a
correct per-edge D projection, with no replacement Markov chain. -/
theorem bankRepairDigitDirtyRowsOfProjectionAndIdentity {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hprojection : ∀ z, preDrain z → ∀ e : Fin n,
      piD (bankRepairNext ring hbank z e).val.1 =
        phiD ring (piD z.val.1) e)
    (hidentity : BankRepairDigitIdentityProposals ring hbank preDrain) :
    BankRepairDigitDirtyClearRows ring hbank preDrain := by
  intro z hz e i
  have hp := hprojection z hz e
  have hid : ∀ j : Fin n,
      ((phiD ring (piD z.val.1) e) j).top.d =
        ((piD z.val.1) j).top.d := by
    intro j
    have h := congrArg
      (fun x : ProjD (compileAdvice (ceilLogTwo n)) => x.top.d)
      (congrFun hp j)
    change ((bankRepairNext ring hbank z e).val.1 j).d =
      ((phiD ring (piD z.val.1) e) j).top.d at h
    exact h.symm.trans (hidentity z hz e j)
  have hrows :=
    bankRepairDigitPhiDirtyClearOfIdentity (by omega : 2 ≤ n)
      ring (piD z.val.1) e hid i
  have hbit := congrArg
    (fun x : ProjD (compileAdvice (ceilLogTwo n)) => x.top.topDirty)
    (congrFun hp i)
  change ((bankRepairNext ring hbank z e).val.1 i).topDirty =
    ((phiD ring (piD z.val.1) e) i).top.topDirty at hbit
  exact hbit.trans hrows

theorem bankRepairDigitDirtyRowsOfNoFireIdentity {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hno : BankRepairDigitNoFireClass ring hbank preDrain)
    (hidentity : BankRepairDigitIdentityProposals ring hbank preDrain) :
    BankRepairDigitDirtyClearRows ring hbank preDrain := by
  exact bankRepairDigitDirtyRowsOfProjectionAndIdentity
    ring hn hbank preDrain
    (bankRepairDigitProjectionOnNoFireClass ring hbank preDrain hno)
    hidentity

private theorem bankRepairDigitDirtyPointwise {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hrows : BankRepairDigitDirtyClearRows ring hbank preDrain)
    (z : BankReferenceState ring hbank) (hz : preDrain z)
    (e i : Fin n) :
    bankRepairDigitDirtyUnit
      ((bankRepairNext ring hbank z e).val.1 i).topDirty ≤
    bankRepairDigitDirtyUnit (z.val.1 i).topDirty := by
  rw [hrows z hz e i]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

theorem bankRepairDigitDirtyCountNonincreasing {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hrows : BankRepairDigitDirtyClearRows ring hbank preDrain)
    (z : BankReferenceState ring hbank) (hz : preDrain z)
    (e : Fin n) :
    bankRepairDigitDirtyCount ring hbank (bankRepairNext ring hbank z e) ≤
      bankRepairDigitDirtyCount ring hbank z := by
  unfold bankRepairDigitDirtyCount
  exact ofFn_sum_le
    (fun i : Fin n => bankRepairDigitDirtyUnit
      ((bankRepairNext ring hbank z e).val.1 i).topDirty)
    (fun i : Fin n => bankRepairDigitDirtyUnit (z.val.1 i).topDirty)
    (fun i => bankRepairDigitDirtyPointwise
      ring hbank preDrain hrows z hz e i)

private theorem bankRepairDigitSumSpike (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

/-- A chosen incoming edge clears the selected OLD true bit;
all other indicators have nonincreasing sum. -/
theorem bankRepairDigitDirtyCountDrop {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hrows : BankRepairDigitDirtyClearRows ring hbank preDrain)
    (z : BankReferenceState ring hbank) (hz : preDrain z)
    (i : Fin n) (hi : (z.val.1 i).topDirty = true) :
    bankRepairDigitDirtyCount ring hbank
        (bankRepairNext ring hbank z (ring.leftNeighbor i)) + 1 ≤
      bankRepairDigitDirtyCount ring hbank z := by
  have hj : ring.rightNeighbor (ring.leftNeighbor i) = i :=
    bankRepairDigitRightOfLeft ring i
  have hclear :
      ((bankRepairNext ring hbank z (ring.leftNeighbor i)).val.1 i).topDirty =
        false := by
    have hr := hrows z hz (ring.leftNeighbor i) i
    rw [hj] at hr
    simpa using hr
  have hpoint : ∀ j : Fin n,
      bankRepairDigitDirtyUnit
        ((bankRepairNext ring hbank z (ring.leftNeighbor i)).val.1 j).topDirty +
        (if j = i then 1 else 0) ≤
          bankRepairDigitDirtyUnit (z.val.1 j).topDirty := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [bankRepairDigitDirtyUnit, hclear, hi]
    · have hmono :=
        bankRepairDigitDirtyPointwise ring hbank preDrain
          hrows z hz (ring.leftNeighbor i) j
      simpa only [if_neg hji, Nat.add_zero] using hmono
  have hs := ofFn_sum_le
    (fun j : Fin n =>
      bankRepairDigitDirtyUnit
        ((bankRepairNext ring hbank z (ring.leftNeighbor i)).val.1 j).topDirty +
          (if j = i then 1 else 0))
    (fun j : Fin n =>
      bankRepairDigitDirtyUnit (z.val.1 j).topDirty) hpoint
  rw [ofFn_sum_add, bankRepairDigitSumSpike n i 1] at hs
  change bankRepairDigitDirtyCount ring hbank
      (bankRepairNext ring hbank z (ring.leftNeighbor i)) + 1 ≤
        bankRepairDigitDirtyCount ring hbank z at hs
  exact hs

/-- Independent E.G36 closure requirement when all OLD dirty bits
have been drained. Bit zero alone is not a generated-history witness. -/
def BankRepairDigitZeroDirtyAccepted {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop) : Prop :=
  ∀ z, preDrain z →
    bankRepairDigitDirtyCount ring hbank z = 0 →
      BankRepairDigit ring hbank z

/-- Instantiate the earlier existential with the literal count and
the incoming leftmost-dirty edge. -/
theorem bankRepairDigitDirtyNominatedOfRows {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hrows : BankRepairDigitDirtyClearRows ring hbank preDrain)
    (haccept : BankRepairDigitZeroDirtyAccepted ring hbank preDrain) :
    BankRepairDigitDirtyNominatedBridge ring hbank preDrain := by
  classical
  refine ⟨bankRepairDigitDirtyCount ring hbank,
    bankRepairDigitIntoLeftmostDirty ring hbank, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact bankRepairDigitDirtyCountCap ring hbank z
  · intro z hz hzero
    exact haccept z hz hzero
  · intro z hz hnot
    have hex : ∃ i : Fin n, (z.val.1 i).topDirty = true := by
      by_cases hdirty : ∃ i : Fin n, (z.val.1 i).topDirty = true
      · exact hdirty
      · have hclean : ∀ i : Fin n, (z.val.1 i).topDirty = false := by
          intro i
          cases hb : (z.val.1 i).topDirty with
          | false => rfl
          | true => exact False.elim (hdirty ⟨i, hb⟩)
        have hzero := bankRepairDigitDirtyCountZeroOfClean
          ring hbank z hclean
        exact False.elim (hnot (haccept z hz hzero))
    have hchosen := (bankRepairDigitLeftmostDirtySpec
      ring hbank z hex).1
    change bankRepairDigitDirtyCount ring hbank
        (bankRepairNext ring hbank z
          (bankRepairDigitIntoLeftmostDirty ring hbank z)) + 1 ≤
        bankRepairDigitDirtyCount ring hbank z
    unfold bankRepairDigitIntoLeftmostDirty
    exact bankRepairDigitDirtyCountDrop ring hbank preDrain
      hrows z hz (bankRepairDigitLeftmostDirtySite ring hbank z) hchosen
  · intro z hz hnot e
    exact bankRepairDigitDirtyCountNonincreasing
      ring hbank preDrain hrows z hz e

theorem bankRepairDigitDirtyNominatedOfNoFireIdentity {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hno : BankRepairDigitNoFireClass ring hbank preDrain)
    (hidentity : BankRepairDigitIdentityProposals ring hbank preDrain)
    (haccept : BankRepairDigitZeroDirtyAccepted ring hbank preDrain) :
    BankRepairDigitDirtyNominatedBridge ring hbank preDrain := by
  exact bankRepairDigitDirtyNominatedOfRows ring hbank preDrain
    (bankRepairDigitDirtyRowsOfNoFireIdentity
      ring hn hbank preDrain hno hidentity) haccept

/-- This is a conditional first-hit inequality on the SAME masked
BANK reference; no separate clock or independent edge tape. -/
theorem bankRepairDigitDirtyHalfOfNoFireIdentity {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hclosed : BankRepairDigitPreDrainClosed ring hbank preDrain)
    (hno : BankRepairDigitNoFireClass ring hbank preDrain)
    (hidentity : BankRepairDigitIdentityProposals ring hbank preDrain)
    (haccept : BankRepairDigitZeroDirtyAccepted ring hbank preDrain) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      preDrain (BankRepairDigit ring hbank) 2 := by
  exact bankRepairDigitDirtyHalfOfNominatedBridge
    ring hbank preDrain hclosed
    (bankRepairDigitDirtyNominatedOfNoFireIdentity
      ring hn hbank preDrain hno hidentity haccept)

end L3.RenewalReferenceClock


/-!
The 201-half pre-drain ledger decomposed on the TRUE
bankRepairNext reference, without prematurely rounding each
small fractional contribution to one independent half-unit.

The three small contributions e, g-100, P_pair have a SHARED
budget strictly below one half-unit. The 100 n^2 value wave
uses 200 half-units. Four separately rounded half clocks
would total 203, not 201.

The predicate fields below are named causal CUT INTERFACES;
they are not asserted to be reachable, closed, or accepted.
A source theorem must instantiate them with witnessed physical
boundary, two-base-cover, stable-value and strict-comparison cuts.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Four positions in the chronological D repair route.
These are predicates on the original BANK reference state.
A later row/history proof must supply their causal receipts.

Boundary: inherited base and both leader fragments retired.
FirstZero: two witnessed root-origin base passes after retirement.
ValuesStable: all successor-value dependencies current and stable.
The last cut, preDrain, is supplied by the caller. -/
structure BankRepairDigitPreDrainCuts {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) where
  boundaryRetired : BankReferenceState ring hbank → Prop
  firstBlockZero : BankReferenceState ring hbank → Prop
  successorValuesStable : BankReferenceState ring hbank → Prop

/-- A charge in interactions, multiplied by the same n^T
truncation numerator, BEFORE it is rounded to half-units. -/
def BankRepairDigitChargedStage {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (start finish : S → Prop)
    (charge : Nat) : Prop :=
  ∀ x, start x → ∀ T : Nat,
    2 * costNumerator next finish x T ≤ n ^ T * charge

/-- Double the e(n,s) integer-numerator envelope, measured
in n rather than n^2 units. Source: repair.tex 4552-4564,
4569-4646. Analytic log comparison is not built into this def. -/
def bankRepairDigitBoundaryMicroCharge (n : Nat) : Nat :=
  2 * bankRepairDigitBoundaryUpper
    (ceilLogTwo (ceilLogTwo n)) * n

/-- Double the (g(n,r)-100) envelope, for inherited base
extinction and two causal zero covers. repair.tex 4656-4689,
4708-4748, 4768-4827. -/
def bankRepairDigitFirstZeroMicroCharge (n : Nat) : Nat :=
  2 * bankRepairDigitValueUpper
    (ceilLogTwo (ceilLogTwo n)) * n

/-- The fixed 100 n^2 successor-value wave equals 200
half-units. repair.tex 4829-4942 and 4994-5020. -/
def bankRepairDigitValueWaveMicroCharge (n : Nat) : Nat :=
  200 * n ^ 2

/-- Double the simultaneous P_pair envelope, including
restarted strict comparison currentness. repair.tex 4195-4239,
4944-4992, 5026-5054 and 5351-5359. -/
def bankRepairDigitComparisonMicroCharge (n : Nat) : Nat :=
  2 * bankRepairDigitPairUpper
    (ceilLogTwo (ceilLogTwo n)) * n

/-- FIRST MISSING PHYSICAL CLOCK, restricted to boundary
and inherited-base retirement, NOT the whole D pre-drain.

Requires the actual masked BANK scheduler to reach a causal
boundary cut with both leading and final packet authority
retired, and inherited base labels extinct, from EVERY
R-fold-established BANK entrance. The charge is the e
numerator before ceil/rounding. No theorem in
Closure/Target/SealedClose/CounterCold/RequestStage supplies
this conditional first-hit bound (repair.tex 4569-4646). -/
def BankRepairDigitBoundaryInheritedMicroClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (boundaryRetired : BankReferenceState ring hbank → Prop) : Prop :=
  BankRepairDigitChargedStage
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    boundaryRetired
    (bankRepairDigitBoundaryMicroCharge n)

/-- The four conditional clocks. All use the ORIGINAL same
Fin n physical scheduler, no separately restarted edge tapes.
Their charges are 2e, 2(g-100), 200, 2P_pair before rounding. -/
def BankRepairDigitFourMicroClocks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop) : Prop :=
  BankRepairDigitBoundaryInheritedMicroClock
      ring hbank cuts.boundaryRetired ∧
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.boundaryRetired cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n) ∧
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n) ∧
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)

/-- The requested separate, COARSE half-stage interfaces.
They cannot be composed to 201 by themselves: 1+1+200+1=203.
The micro clocks above retain the two-half-unit saving. -/
def BankRepairDigitBoundaryHalfClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank) : Prop :=
  BankRepairHalfStage (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank) cuts.boundaryRetired 1

def BankRepairDigitFirstZeroHalfClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank) : Prop :=
  BankRepairHalfStage (bankRepairNext ring hbank)
    cuts.boundaryRetired cuts.firstBlockZero 1

def BankRepairDigitValueWaveHalfClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank) : Prop :=
  BankRepairHalfStage (bankRepairNext ring hbank)
    cuts.firstBlockZero cuts.successorValuesStable 200

def BankRepairDigitComparisonHalfClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop) : Prop :=
  BankRepairHalfStage (bankRepairNext ring hbank)
    cuts.successorValuesStable preDrain 1

/-- Reuse the existing half-unit strong-Markov reserve, but
with exact Nat charges rather than k*n^2. No independence
of stage durations or scheduler samples is used. -/
private theorem bankRepairDigitChargedCompose
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (A B Target : S → Prop) (a b : Nat)
    (hfirst : BankRepairDigitChargedStage next A B a)
    (hsecond : BankRepairDigitChargedStage next B Target b) :
    BankRepairDigitChargedStage next A Target (a + b) := by
  intro x hx T
  have hfirstUnion :
      2 * costNumerator next (fun z => B z ∨ Target z) x T ≤
        n ^ T * a := by
    have hmono := L3.Prob.costNumerator_target_mono next B
      (fun z => B z ∨ Target z)
      (fun z hz => Or.inl hz) x T
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono)
      (hfirst x hx T)
  have hreserve := bankRepairDigitHalfReserve next B Target b
    (fun y hy U => hsecond y hy U) x T
  calc
    2 * costNumerator next Target x T ≤
        2 * costNumerator next (fun z => B z ∨ Target z) x T +
          n ^ T * b := hreserve
    _ ≤ n ^ T * a + n ^ T * b :=
      Nat.add_le_add_right hfirstUnion _
    _ = n ^ T * (a + b) := by rw [Nat.mul_add]

/-- The numeric certificate:
2*nu_s < n. Crucially it is applied ONCE after the four stages,
rather than once to each small stage separately. -/
theorem bankRepairDigitMicroChargesFit {n : Nat}
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    bankRepairDigitBoundaryMicroCharge n +
        bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitValueWaveMicroCharge n +
        bankRepairDigitComparisonMicroCharge n ≤
      201 * n ^ 2 := by
  have hsmall : 2 * bankRepairDigitNu
      (ceilLogTwo (ceilLogTwo n)) < n := by
    have hh := bankRepairDigitIntegerHalf hn hbank
    exact hh
  have hnum :
      (2 * bankRepairDigitNu
        (ceilLogTwo (ceilLogTwo n))) * n ≤ n ^ 2 := by
    have hmul := Nat.mul_le_mul_right n (Nat.le_of_lt hsmall)
    simpa only [Nat.pow_two] using hmul
  have hrearrange :
      bankRepairDigitBoundaryMicroCharge n +
          bankRepairDigitFirstZeroMicroCharge n +
          bankRepairDigitValueWaveMicroCharge n +
          bankRepairDigitComparisonMicroCharge n =
        (2 * bankRepairDigitNu
          (ceilLogTwo (ceilLogTwo n))) * n +
          200 * n ^ 2 := by
    unfold bankRepairDigitBoundaryMicroCharge
      bankRepairDigitFirstZeroMicroCharge
      bankRepairDigitValueWaveMicroCharge
      bankRepairDigitComparisonMicroCharge bankRepairDigitNu
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  calc
    bankRepairDigitBoundaryMicroCharge n +
        bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitValueWaveMicroCharge n +
        bankRepairDigitComparisonMicroCharge n =
      (2 * bankRepairDigitNu
        (ceilLogTwo (ceilLogTwo n))) * n +
        200 * n ^ 2 := hrearrange
    _ ≤ n ^ 2 + 200 * n ^ 2 :=
      Nat.add_le_add_right hnum _
    _ = 201 * n ^ 2 := by omega

/-- All four causal costs composed before a single ceiling.
This is EXACTLY the required 201-half pre-drain first-hit clock,
conditional on the named true-process cut clocks. -/
theorem bankRepairDigitPreDrain201OfMicroClocks {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hclocks : BankRepairDigitFourMicroClocks
      ring hbank cuts preDrain) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank) preDrain 201 := by
  obtain ⟨hboundary, hzero, hwave, hpair⟩ := hclocks
  have hboundaryZero := bankRepairDigitChargedCompose
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    cuts.boundaryRetired cuts.firstBlockZero
    (bankRepairDigitBoundaryMicroCharge n)
    (bankRepairDigitFirstZeroMicroCharge n)
    hboundary hzero
  have hthroughWave := bankRepairDigitChargedCompose
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    cuts.firstBlockZero cuts.successorValuesStable
    (bankRepairDigitBoundaryMicroCharge n +
      bankRepairDigitFirstZeroMicroCharge n)
    (bankRepairDigitValueWaveMicroCharge n)
    hboundaryZero hwave
  have hall := bankRepairDigitChargedCompose
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    cuts.successorValuesStable preDrain
    (bankRepairDigitBoundaryMicroCharge n +
      bankRepairDigitFirstZeroMicroCharge n +
      bankRepairDigitValueWaveMicroCharge n)
    (bankRepairDigitComparisonMicroCharge n)
    hthroughWave hpair
  intro z hz T
  exact Nat.le_trans (hall z hz T)
    (Nat.mul_le_mul_left (n ^ T)
      (bankRepairDigitMicroChargesFit hn hbank))

/-- Generic cost coarsening from a fine charge to one ordinary
BankRepairHalfStage. It deliberately does not feed the 201 proof. -/
private theorem bankRepairDigitChargedToHalf
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (A B : S → Prop)
    (charge halfUnits : Nat)
    (hcharge : charge ≤ halfUnits * n ^ 2)
    (hstage : BankRepairDigitChargedStage next A B charge) :
    BankRepairHalfStage next A B halfUnits := by
  intro x hx T
  exact Nat.le_trans (hstage x hx T)
    (Nat.mul_le_mul_left (n ^ T) hcharge)

/-- Each positive small term separately fits within one half
unit, even though spending all three halves destroys sharpness. -/
theorem bankRepairDigitMicroIndividualCaps {n : Nat}
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    bankRepairDigitBoundaryMicroCharge n ≤ n ^ 2 ∧
    bankRepairDigitFirstZeroMicroCharge n ≤ n ^ 2 ∧
    bankRepairDigitComparisonMicroCharge n ≤ n ^ 2 := by
  have hnu : 2 * bankRepairDigitNu
      (ceilLogTwo (ceilLogTwo n)) < n :=
    bankRepairDigitIntegerHalf hn hbank
  have hb : 2 * bankRepairDigitBoundaryUpper
      (ceilLogTwo (ceilLogTwo n)) ≤ n := by
    have hle :
        bankRepairDigitBoundaryUpper
          (ceilLogTwo (ceilLogTwo n)) ≤
          bankRepairDigitNu
            (ceilLogTwo (ceilLogTwo n)) := by
      unfold bankRepairDigitNu
      omega
    omega
  have hz : 2 * bankRepairDigitValueUpper
      (ceilLogTwo (ceilLogTwo n)) ≤ n := by
    have hle :
        bankRepairDigitValueUpper
          (ceilLogTwo (ceilLogTwo n)) ≤
          bankRepairDigitNu
            (ceilLogTwo (ceilLogTwo n)) := by
      unfold bankRepairDigitNu
      omega
    omega
  have hp : 2 * bankRepairDigitPairUpper
      (ceilLogTwo (ceilLogTwo n)) ≤ n := by
    have hle :
        bankRepairDigitPairUpper
          (ceilLogTwo (ceilLogTwo n)) ≤
          bankRepairDigitNu
            (ceilLogTwo (ceilLogTwo n)) := by
      unfold bankRepairDigitNu
      omega
    omega
  constructor
  · unfold bankRepairDigitBoundaryMicroCharge
    have hh := Nat.mul_le_mul_right n hb
    simpa only [Nat.pow_two] using hh
  constructor
  · unfold bankRepairDigitFirstZeroMicroCharge
    have hh := Nat.mul_le_mul_right n hz
    simpa only [Nat.pow_two] using hh
  · unfold bankRepairDigitComparisonMicroCharge
    have hh := Nat.mul_le_mul_right n hp
    simpa only [Nat.pow_two] using hh

/-- The four explicit BankRepairHalfStage interfaces do follow
from the finer clocks. They are NOT the inputs used for the sharp
201-half composition because their separate ceilings total 203. -/
theorem bankRepairDigitFourHalfClocksOfMicro {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hclocks : BankRepairDigitFourMicroClocks
      ring hbank cuts preDrain) :
    BankRepairDigitBoundaryHalfClock ring hbank cuts ∧
    BankRepairDigitFirstZeroHalfClock ring hbank cuts ∧
    BankRepairDigitValueWaveHalfClock ring hbank cuts ∧
    BankRepairDigitComparisonHalfClock ring hbank cuts preDrain := by
  obtain ⟨hb, hz, hw, hp⟩ := hclocks
  obtain ⟨hboundB, hboundZ, hboundP⟩ :=
    bankRepairDigitMicroIndividualCaps hn hbank
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact bankRepairDigitChargedToHalf
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank) cuts.boundaryRetired
      (bankRepairDigitBoundaryMicroCharge n) 1
      (by simpa only [Nat.one_mul] using hboundB) hb
  · exact bankRepairDigitChargedToHalf
      (bankRepairNext ring hbank)
      cuts.boundaryRetired cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n) 1
      (by simpa only [Nat.one_mul] using hboundZ) hz
  · exact bankRepairDigitChargedToHalf
      (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n) 200
      (Nat.le_refl _) hw
  · exact bankRepairDigitChargedToHalf
      (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n) 1
      (by simpa only [Nat.one_mul] using hboundP) hp

/-- A direct use of the installed four half-stage composition
only gives 203, proving why the fine-budget theorem is needed. -/
theorem bankRepairDigitPreDrain203OfSeparateHalfClocks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hb : BankRepairDigitBoundaryHalfClock ring hbank cuts)
    (hz : BankRepairDigitFirstZeroHalfClock ring hbank cuts)
    (hw : BankRepairDigitValueWaveHalfClock ring hbank cuts)
    (hp : BankRepairDigitComparisonHalfClock ring hbank cuts preDrain) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank) preDrain 203 := by
  have hfirst := bankRepairDigitHalfCompose
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    cuts.boundaryRetired cuts.firstBlockZero
    1 1 hb hz
  have hsecond := bankRepairDigitHalfCompose
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    cuts.firstBlockZero cuts.successorValuesStable
    (1 + 1) 200 hfirst hw
  have hthird := bankRepairDigitHalfCompose
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    cuts.successorValuesStable preDrain
    ((1 + 1) + 200) 1 hsecond hp
  have hcoef : ((1 + 1) + 200) + 1 = 203 := by omega
  rw [hcoef] at hthird
  exact hthird

/-- Source entrance: the accepted R-fold already carries
the original native/candidate factor AND accepted W, all on the
same BANK physical state. It does not retire any D scratch. -/
theorem bankRepairDigitRFoldCarriesEarlierFactors {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairRFoldEstablished ring hbank z) :
    BankRepairCore ring hbank z ∧
    BankRepairWord ring hbank z ∧
    BankRepairReader ring hbank z := by
  exact ⟨hz.1.1, hz.1.2, hz.2⟩

/-- Exact handoff into the 201+2-half
digit-stage framework. The physical pre-drain clock is now
concentrated in the four causal micro-clocks above. -/
theorem bankRepairDigitCausalClocksOfFourMicro {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hclocks : BankRepairDigitFourMicroClocks
      ring hbank cuts preDrain)
    (hclosed : BankRepairDigitPreDrainClosed ring hbank preDrain)
    (hdirty : BankRepairDigitDirtyNominatedBridge
      ring hbank preDrain) :
    BankRepairDigitCausalClocks ring hbank preDrain := by
  exact bankRepairDigitCausalClocksOfDirtyBridge
    ring hbank preDrain
    (bankRepairDigitPreDrain201OfMicroClocks
      ring hn hbank cuts preDrain hclocks)
    hclosed hdirty

end L3.RenewalReferenceClock

/-!
Actual BANK boundary stopping cut and Bellman reduction.

The first coordinate of bankRepairDigitBoundaryAuditNext is literally
bankRepairNext; the second is a proof-only observer of each actual OLD
physical digit projection. The new causal-cover drift producer is an
explicit unproved Prop, not a replacement stochastic chain or an axiom.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- One actual BANK step, with a deterministic proof-only digit audit. -/
def bankRepairDigitBoundaryAuditNext {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) :
    BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n :=
  (bankRepairNext ring hbank z.1 e,
    digitAuditStep ring (piD z.1.val.1) z.2 e)

/-- Every observer word projects to the old masked BANK reference word. -/
theorem bankRepairDigitBoundaryAuditFirst {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (word : List (Fin n)) :
    (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, audit)).1 =
      word.foldl (bankRepairNext ring hbank) start := by
  induction word generalizing start audit with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        (rest.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (bankRepairNext ring hbank start e,
            digitAuditStep ring (piD start.val.1) audit e)).1 =
        rest.foldl (bankRepairNext ring hbank)
          (bankRepairNext ring hbank start e)
      exact ih (bankRepairNext ring hbank start e)
        (digitAuditStep ring (piD start.val.1) audit e)

/-- Actual BANK reachability from ANY accepted R-fold entrance. -/
def BankRepairDigitBoundaryReachable {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank)
    (word : List (Fin n)),
    BankRepairRFoldEstablished ring hbank start ∧
    z = word.foldl (bankRepairNext ring hbank) start

theorem bankRepairDigitBoundaryReachableOrigin {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairRFoldEstablished ring hbank z) :
    BankRepairDigitBoundaryReachable ring hbank z := by
  exact ⟨z, [], hz, rfl⟩

theorem bankRepairDigitBoundaryReachableStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ z : BankReferenceState ring hbank,
      BankRepairDigitBoundaryReachable ring hbank z →
      ∀ e : Fin n,
        BankRepairDigitBoundaryReachable ring hbank
          (bankRepairNext ring hbank z e) := by
  intro z hz e
  obtain ⟨start, word, hstart, hpath⟩ := hz
  refine ⟨start, word ++ [e], hstart, ?_⟩
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  exact congrArg
    (fun x : BankReferenceState ring hbank =>
      bankRepairNext ring hbank x e) hpath

/-- Physical leading and final fragment authority is retired at
DigitBoundaryReceipt; inherited base records are extinct relative
to a concrete same-chain audit started at the R-fold entrance.
New root-origin base records need not disappear. The witnessed root
is the actual protected leader, not a synthetic fresh root. -/
def BankRepairDigitBoundaryRetiredCut {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank)
    (word : List (Fin n))
    (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    BankRepairRFoldEstablished ring hbank start ∧
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) ∧
    WFixedRoot ring root (piW z.val.1) ∧
    DigitAt ring audit audit.clock (piD z.val.1)
      audit.current ∧
    DigitBoundaryReceipt ring root (piD z.val.1) ∧
    DigitBaseExtinct ring root audit 0 audit.clock

/-- The exact boundary predicate implies genuine BANK reachability.
The digit audit does not carry a separate physical scheduler. -/
theorem bankRepairDigitBoundaryCutIsReachable {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hcut : BankRepairDigitBoundaryRetiredCut ring hbank z) :
    BankRepairDigitBoundaryReachable ring hbank z := by
  obtain ⟨start, word, root, audit, hstart, hpair,
    _hroot, _hat, _hshape, _hbase⟩ := hcut
  refine ⟨start, word, hstart, ?_⟩
  have hfirst := congrArg (fun pair => pair.1) hpair
  change
    (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).1 = z
      at hfirst
  exact hfirst.symm.trans
    (bankRepairDigitBoundaryAuditFirst ring hbank start
      (digitAuditInitial (piD start.val.1)) word)

/-- One named, still-unproved source producer. Its three conjuncts
are: the actual BANK-to-phiD row projection on R-fold reachable
states; Bellman drift n + sum_e Phi(next e) <= n*Phi before the
specific causal boundary cut; and the fine 2e micro-charge at
EVERY R-fold entrance. The missing mathematical content is the
paper's labelled base-record extinction and both packet-fragment
causal covers, including transfer/collision and root sinks.
This is a definition of a Prop, not a theorem or axiom. -/
def BankRepairDigitBoundaryCausalCoverDrift {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    Prop :=
  ∃ potential : BankReferenceState ring hbank → Nat,
    (∀ z : BankReferenceState ring hbank,
      BankRepairDigitBoundaryReachable ring hbank z →
      ∀ e : Fin n,
        piD (bankRepairNext ring hbank z e).val.1 =
          phiD ring (piD z.val.1) e) ∧
    (∀ z : BankReferenceState ring hbank,
      BankRepairDigitBoundaryReachable ring hbank z →
      ¬ BankRepairDigitBoundaryRetiredCut ring hbank z →
      n + (List.ofFn (fun e : Fin n =>
        potential (bankRepairNext ring hbank z e))).sum ≤
          n * potential z) ∧
    (∀ z : BankReferenceState ring hbank,
      BankRepairRFoldEstablished ring hbank z →
      2 * potential z ≤ bankRepairDigitBoundaryMicroCharge n)

/-- The exact boundary first-hit inequality follows from the
single named causal-cover producer. This proof uses the ordinary
finite-horizon Bellman inequality, not independence of stages.
The comparison target additionally stops outside the forward-closed
R-fold-reachable class, and its cost agrees with the real boundary
cost for every valid entrance. -/
theorem bankRepairDigitBoundaryInheritedOfCausalDrift {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcausal : BankRepairDigitBoundaryCausalCoverDrift ring hbank) :
    BankRepairDigitBoundaryInheritedMicroClock ring hbank
      (BankRepairDigitBoundaryRetiredCut ring hbank) := by
  classical
  obtain ⟨potential, _hphysical, hdrift, hcap⟩ := hcausal
  intro z hz T
  have hclosed :=
    bankRepairDigitBoundaryReachableStep ring hbank
  have hreach : BankRepairDigitBoundaryReachable ring hbank z :=
    bankRepairDigitBoundaryReachableOrigin ring hbank z hz
  have hbellman :
      ∀ y : BankReferenceState ring hbank,
        ¬ (¬ BankRepairDigitBoundaryReachable ring hbank y ∨
          BankRepairDigitBoundaryRetiredCut ring hbank y) →
        n + (List.ofFn (fun e : Fin n =>
          if BankRepairDigitBoundaryReachable ring hbank
              (bankRepairNext ring hbank y e) then
            potential (bankRepairNext ring hbank y e)
          else 0)).sum ≤
        n * (if BankRepairDigitBoundaryReachable ring hbank y
          then potential y else 0) := by
    intro y hnot
    have hy : BankRepairDigitBoundaryReachable ring hbank y := by
      by_cases hyes :
          BankRepairDigitBoundaryReachable ring hbank y
      · exact hyes
      · exact False.elim (hnot (Or.inl hyes))
    have hnon :
        ¬ BankRepairDigitBoundaryRetiredCut ring hbank y := by
      intro hcut
      exact hnot (Or.inr hcut)
    have hsum :
        (List.ofFn (fun e : Fin n =>
          if BankRepairDigitBoundaryReachable ring hbank
              (bankRepairNext ring hbank y e) then
            potential (bankRepairNext ring hbank y e)
          else 0)).sum =
        (List.ofFn (fun e : Fin n =>
          potential (bankRepairNext ring hbank y e))).sum := by
      exact ofFn_sum_eq _ _ (by
        intro e
        exact if_pos (hclosed y hy e))
    rw [hsum, if_pos hy]
    exact hdrift y hy hnon
  have hcomparison :
      costNumerator (bankRepairNext ring hbank)
        (fun y => ¬ BankRepairDigitBoundaryReachable ring hbank y ∨
          BankRepairDigitBoundaryRetiredCut ring hbank y) z T ≤
      n ^ T * (if BankRepairDigitBoundaryReachable ring hbank z
        then potential z else 0) :=
    Prob.costNumerator_le_of_potential
      (bankRepairNext ring hbank)
      (fun y => ¬ BankRepairDigitBoundaryReachable ring hbank y ∨
        BankRepairDigitBoundaryRetiredCut ring hbank y)
      (fun y => if BankRepairDigitBoundaryReachable ring hbank y
        then potential y else 0)
      hbellman z T
  have hequal :=
    bankRepairDigitCostClosedTarget
      (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryReachable ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank)
      (fun y hy e => hclosed y hy e) z hreach T
  have hactual :
      costNumerator (bankRepairNext ring hbank)
        (BankRepairDigitBoundaryRetiredCut ring hbank) z T ≤
        n ^ T * potential z := by
    rw [hequal]
    simpa only [if_pos hreach] using hcomparison
  calc
    2 * costNumerator (bankRepairNext ring hbank)
        (BankRepairDigitBoundaryRetiredCut ring hbank) z T ≤
      2 * (n ^ T * potential z) :=
        Nat.mul_le_mul_left 2 hactual
    _ = n ^ T * (2 * potential z) := by ac_rfl
    _ ≤ n ^ T * bankRepairDigitBoundaryMicroCharge n :=
      Nat.mul_le_mul_left (n ^ T) (hcap z hz)

/-- First causal cover composed with the next, at the exact
micro-charge, with no intermediate half-unit ceiling. -/
theorem bankRepairDigitBoundaryFirstZeroOfCausalDrift {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (firstZero : BankReferenceState ring hbank → Prop)
    (hcausal : BankRepairDigitBoundaryCausalCoverDrift ring hbank)
    (hzero : BankRepairDigitChargedStage
      (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) firstZero
      (bankRepairDigitFirstZeroMicroCharge n)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank) firstZero
      (bankRepairDigitBoundaryMicroCharge n +
        bankRepairDigitFirstZeroMicroCharge n) := by
  exact bankRepairDigitChargedCompose
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    (BankRepairDigitBoundaryRetiredCut ring hbank)
    firstZero
    (bankRepairDigitBoundaryMicroCharge n)
    (bankRepairDigitFirstZeroMicroCharge n)
    (bankRepairDigitBoundaryInheritedOfCausalDrift
      ring hbank hcausal) hzero

/-- The 201-half composition consumes the
completed boundary fine clock and the other three true-process
micro-clocks. It never rounds each small stage in isolation. -/
theorem bankRepairDigitPreDrainOfBoundaryDrift {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hcut : cuts.boundaryRetired =
      BankRepairDigitBoundaryRetiredCut ring hbank)
    (hcausal : BankRepairDigitBoundaryCausalCoverDrift ring hbank)
    (hzero : BankRepairDigitChargedStage
      (bankRepairNext ring hbank)
      cuts.boundaryRetired cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage
      (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hcomparison : BankRepairDigitChargedStage
      (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank) preDrain 201 := by
  have hboundary :
      BankRepairDigitBoundaryInheritedMicroClock
        ring hbank cuts.boundaryRetired := by
    rw [hcut]
    exact bankRepairDigitBoundaryInheritedOfCausalDrift
      ring hbank hcausal
  exact bankRepairDigitPreDrain201OfMicroClocks
    ring hn hbank cuts preDrain
    ⟨hboundary, hzero, hwave, hcomparison⟩

/-- Concrete OLD pair: a leader with otherwise blank local
fields, serving a blank nonleader. The WB owner creates SEEK at
the destination. This is a local row example, NOT an assertion of
reachability from a production BANK R-fold entrance. -/
theorem bankRepairDigitBoundaryRootLaunchPhysicalExample
    (c : Compiled) :
    (liveTopPair c { Agent.blank c with l := true }
      (Agent.blank c)).y.wBase = .SEEK := by
  rfl

/-- The source-scope E.G ghost assigns this event a new rootLaunch
label, not an inherited label. This is the 0 -> 1 edge of an
explicit five-site OLD pair. A count of ALL active base records
is therefore not a monotone inherited-extinction potential. -/
theorem bankRepairDigitBoundaryRootLaunchAuditExample
    (c : Compiled) :
    (digitBaseReplay 1 (0 : Fin 5) (1 : Fin 5)
      (ProjD.ofAgent { Agent.blank c with l := true })
      (ProjD.ofAgent (Agent.blank c)) false none none).y =
      some (.rootLaunch 1 (0 : Fin 5) (1 : Fin 5)) := by
  rfl

end L3.RenewalReferenceClock


/-!
Inherited-only digit boundary accounting: source row audit.

The distinction essential to the paper is between an inherited
base identity and a new rootLaunch. The physical wBase field cannot
recover that distinction by itself. This block proves the
following causal infrastructure directly from Target.digitBaseReplay:

* all surviving base labels in each selected endpoint are either
  old endpoint labels or a new rootLaunch label;
* no selected E.G base row produces a fresh inherited identity;
* arbitrary R-fold-reachable BANK states admit an exact causal
  audit on the SAME real BANK scheduler;
* an inherited-tag count has the correct n-label cap and its
  J_t-weighted proof-only audit charge fits the e(n,t) boundary
  micro-envelope;
* the first physical projection conjunct of the requested drift
  follows from an explicit reachable no-FIRE hypothesis;
* a finite nominated n-unit drop plus weak all-edge rows supplies
  exactly the required Bellman sum, without an independence claim.

The missing mathematical step remains the history-coherent packet
frontier/leader-authority task rank. A physical BANK state may have
more than one reaching history; arbitrary choice of one digit audit
does not provide a transition-compatible rank. The named certificate
below records precisely the required bounded inherited-only rank,
its per-edge weak rows, and its nominated strict packet task.
It is a Prop, NOT a theorem or additional axiom.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Only source-side labels tagged inherited contribute.
New rootLaunch labels are deliberately charged zero here. -/
def bankRepairDigitInheritedTagUnit {n : Nat}
    (origin : Option (DigitBaseOrigin n)) : Nat :=
  match origin with
  | none => 0
  | some (.inherited _) => 1
  | some (.rootLaunch _ _ _) => 0

def bankRepairDigitInheritedAuditCount {n : Nat} {c : Compiled}
    (ghost : Fin n → DigitGhost c n) : Nat :=
  (List.ofFn (fun i : Fin n =>
    bankRepairDigitInheritedTagUnit (ghost i).base)).sum

/-- Each physical site holds at most one inherited base label,
independent of arbitrary other ghost and packet contents. -/
theorem bankRepairDigitInheritedTagUnitCap {n : Nat}
    (origin : Option (DigitBaseOrigin n)) :
    bankRepairDigitInheritedTagUnit origin ≤ 1 := by
  cases origin with
  | none =>
      exact Nat.zero_le _
  | some origin =>
      cases origin <;>
        simp [bankRepairDigitInheritedTagUnit]

theorem bankRepairDigitInheritedAuditCountCap {n : Nat} {c : Compiled}
    (ghost : Fin n → DigitGhost c n) :
    bankRepairDigitInheritedAuditCount ghost ≤ n := by
  unfold bankRepairDigitInheritedAuditCount
  have hsum := ofFn_sum_le
    (fun i : Fin n =>
      bankRepairDigitInheritedTagUnit (ghost i).base)
    (fun _ : Fin n => 1)
    (by intro i; exact bankRepairDigitInheritedTagUnitCap (ghost i).base)
  simpa only [ofFn_sum_const, Nat.mul_one] using hsum

/-- The original digit audit assigns inherited precisely to
nonempty OLD physical base records, never rootLaunch. -/
theorem bankRepairDigitInheritedInitialTag {n : Nat} {c : Compiled}
    (S : Fin n → ProjD c) (i : Fin n) :
    (digitGhostInitial S i).base =
      if (S i).top.wBase == .NONE then none
      else some (.inherited i) := by
  rfl

theorem bankRepairDigitInheritedInitialCountCap {n : Nat} {c : Compiled}
    (S : Fin n → ProjD c) :
    bankRepairDigitInheritedAuditCount (digitGhostInitial S) ≤ n := by
  exact bankRepairDigitInheritedAuditCountCap (digitGhostInitial S)

/-- A remote edge cannot change the old inherited label,
even when the receiver changes some unrelated W/packet field. -/
theorem bankRepairDigitInheritedAuditAwayFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n)
    (time : Nat) (e i : Fin n)
    (hx : i ≠ e) (hy : i ≠ ring.rightNeighbor e) :
    (digitGhostStep ring S G time e i).base = (G i).base := by
  simp [digitGhostStep, hx, hy]

/-- The exact selected E.G base record never creates an
unrelated source label. At X it either clears the record,
or keeps the OLD source identity unchanged. -/
theorem bankRepairDigitBaseReplayXChoice {n : Nat} {c : Compiled}
    (time : Nat) (xsite ysite : Fin n)
    (x y : ProjD c) (betaY : Bool)
    (gx gy : Option (DigitBaseOrigin n)) :
    (digitBaseReplay time xsite ysite x y betaY gx gy).x = none ∨
      (digitBaseReplay time xsite ysite x y betaY gx gy).x = gx := by
  unfold digitBaseReplay
  dsimp only
  repeat' split
  all_goals simp

/-- Exhaustive choice by the FIVE source-row classes, not by
all native/worker/packet Boolean fields. The new Y label is
OLD X, OLD Y, or one NEW rootLaunch; there is no inherited
producer in the native E.G row. -/
theorem bankRepairDigitBaseReplayYChoice {n : Nat} {c : Compiled}
    (time : Nat) (xsite ysite : Fin n)
    (x y : ProjD c) (betaY : Bool)
    (gx gy : Option (DigitBaseOrigin n)) :
    (digitBaseReplay time xsite ysite x y betaY gx gy).y = gy ∨
    (digitBaseReplay time xsite ysite x y betaY gx gy).y = gx ∨
    (digitBaseReplay time xsite ysite x y betaY gx gy).y =
      some (.rootLaunch time xsite ysite) := by
  unfold digitBaseReplay
  dsimp only
  repeat' split
  all_goals simp

/-- A source with an inherited post-row identity had the SAME
inherited identity before the service; none is born at X. -/
theorem bankRepairDigitReplayXInheritedParent {n : Nat} {c : Compiled}
    (time : Nat) (xsite ysite : Fin n)
    (x y : ProjD c) (betaY : Bool)
    (gx gy : Option (DigitBaseOrigin n))
    (h : ∃ site : Fin n,
      (digitBaseReplay time xsite ysite x y betaY gx gy).x =
        some (.inherited site)) :
    ∃ site : Fin n, gx = some (.inherited site) := by
  obtain ⟨site, hsite⟩ := h
  rcases bankRepairDigitBaseReplayXChoice
      time xsite ysite x y betaY gx gy with hnone | hold
  · have hbad : (none : Option (DigitBaseOrigin n)) =
        some (.inherited site) := hnone.symm.trans hsite
    cases hbad
  · exact ⟨site, hold.symm.trans hsite⟩

/-- Every inherited Y identity came from OLD X or OLD Y.
In particular a rootLaunch cannot be silently reclassified
as inherited when an OLD inherited label collides or retires. -/
theorem bankRepairDigitReplayYInheritedParent {n : Nat} {c : Compiled}
    (time : Nat) (xsite ysite : Fin n)
    (x y : ProjD c) (betaY : Bool)
    (gx gy : Option (DigitBaseOrigin n))
    (h : ∃ site : Fin n,
      (digitBaseReplay time xsite ysite x y betaY gx gy).y =
        some (.inherited site)) :
    (∃ site : Fin n, gx = some (.inherited site)) ∨
      (∃ site : Fin n, gy = some (.inherited site)) := by
  obtain ⟨site, hsite⟩ := h
  rcases bankRepairDigitBaseReplayYChoice
      time xsite ysite x y betaY gx gy with hgy | hgx | hnew
  · exact Or.inr ⟨site, hgy.symm.trans hsite⟩
  · exact Or.inl ⟨site, hgx.symm.trans hsite⟩
  · have hbad : some (DigitBaseOrigin.rootLaunch time xsite ysite) =
        some (DigitBaseOrigin.inherited site) :=
      hnew.symm.trans hsite
    cases hbad

/-- WB is a new root-origin launch even if the OLD source
possesses a separately tagged inherited identity. Its X
identity dies; Y does not inherit it on this row. -/
theorem bankRepairDigitBaseReplayWBLaunch {n : Nat} {c : Compiled}
    (time : Nat) (xsite ysite : Fin n)
    (x y : ProjD c) (betaY : Bool)
    (gx gy : Option (DigitBaseOrigin n))
    (hx : x.word.native.l = true)
    (hy : y.word.native.l = false)
    (hblank : y.top.wBase = .NONE) :
    (digitBaseReplay time xsite ysite x y betaY gx gy).x = none ∧
    (digitBaseReplay time xsite ysite x y betaY gx gy).y =
      some (.rootLaunch time xsite ysite) := by
  simp [digitBaseReplay, hx, hy, hblank]

/-- Concrete five-site WB event: 0 has a physical leader
and an inherited OLD source label, 1 is blank, and the
root first-match creates a rootLaunch at 1. This is the
explicit small row motivating lineage-qualified charging;
it is NOT a counterexample to the inherited-only ranking. -/
theorem bankRepairDigitBoundaryInheritedWBExample :
    (digitBaseReplay 1 (0 : Fin 5) (1 : Fin 5)
      (ProjD.ofAgent
        { Agent.blank (compileAdvice 7) with l := true })
      (ProjD.ofAgent (Agent.blank (compileAdvice 7)))
      false (some (.inherited (0 : Fin 5))) none).x = none ∧
    (digitBaseReplay 1 (0 : Fin 5) (1 : Fin 5)
      (ProjD.ofAgent
        { Agent.blank (compileAdvice 7) with l := true })
      (ProjD.ofAgent (Agent.blank (compileAdvice 7)))
      false (some (.inherited (0 : Fin 5))) none).y =
        some (.rootLaunch 1 (0 : Fin 5) (1 : Fin 5)) := by
  constructor <;> rfl

/-- A completed causal audit exists at every BANK state
reachable from an accepted R-fold entrance. Its first
coordinate is EXACTLY the real BANK scheduling word, not a
surrogate digit process or an arbitrary tag injection. -/
theorem bankRepairDigitBoundaryReachableHasAudit {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitBoundaryReachable ring hbank z) :
    ∃ (start : BankReferenceState ring hbank)
      (word : List (Fin n))
      (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
      BankRepairRFoldEstablished ring hbank start ∧
      word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1)) = (z, audit) := by
  obtain ⟨start, word, hstart, hpath⟩ := hz
  refine ⟨start, word,
    (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).2,
    hstart, ?_⟩
  apply Prod.ext
  · rw [bankRepairDigitBoundaryAuditFirst]
    exact hpath.symm
  · rfl

/-- J_t-weighted initial inherited proof-only base count.
This is an AUDIT rank; no identification with a function of
the physical BANK state has been assumed. Packet/leading/
final task weights still need to be attached to each label. -/
def bankRepairDigitInheritedAuditServiceRank {n : Nat} {c : Compiled}
    (A : DigitAudit c n) : Nat :=
  bankRepairDigitInheritedAuditCount A.current *
    bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n))

/-- The inherited-only audit count with one J_t slot per
remaining inherited identity fits the original boundary
micro-charge. This numerical fact alone is NOT the
Bellman drift: each living label requires a decreasing
remaining-task rank, not a constant J_t until retirement. -/
theorem bankRepairDigitInheritedAuditServiceRankCap {n : Nat} {c : Compiled}
    (A : DigitAudit c n) :
    2 * bankRepairDigitInheritedAuditServiceRank A ≤
      bankRepairDigitBoundaryMicroCharge n := by
  have hcount :=
    bankRepairDigitInheritedAuditCountCap A.current
  have hJ :
      bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n)) ≤
        bankRepairDigitBoundaryUpper (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitBoundaryUpper
    omega
  have hweighted :
      bankRepairDigitInheritedAuditCount A.current *
          bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n)) ≤
        n * bankRepairDigitBoundaryUpper
          (ceilLogTwo (ceilLogTwo n)) := by
    calc
      bankRepairDigitInheritedAuditCount A.current *
          bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n)) ≤
        n * bankRepairDigitBoundaryServices
          (ceilLogTwo (ceilLogTwo n)) :=
            Nat.mul_le_mul_right _ hcount
      _ ≤ n * bankRepairDigitBoundaryUpper
          (ceilLogTwo (ceilLogTwo n)) :=
            Nat.mul_le_mul_left n hJ
  have hscaled := Nat.mul_le_mul_left 2 hweighted
  change
    2 * (bankRepairDigitInheritedAuditCount A.current *
      bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n))) ≤
      2 * bankRepairDigitBoundaryUpper
        (ceilLogTwo (ceilLogTwo n)) * n
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hscaled

/-- The first conjunct of BoundaryCausalCoverDrift follows
from the existing exact masked BANK/phiD projection theorem,
conditional on NO OLD FIRE on the reachable source domain. -/
theorem bankRepairDigitBoundaryProjectionOfReachableNoFire {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hno : BankRepairDigitNoFireClass ring hbank
      (BankRepairDigitBoundaryReachable ring hbank)) :
    ∀ (z : BankReferenceState ring hbank),
      BankRepairDigitBoundaryReachable ring hbank z →
      ∀ e : Fin n,
        piD (bankRepairNext ring hbank z e).val.1 =
          phiD ring (piD z.val.1) e := by
  exact bankRepairDigitProjectionOnNoFireClass ring hbank
    (BankRepairDigitBoundaryReachable ring hbank) hno

/-- Finite Bellman algebra: if every physical edge is weak
and one nominated real edge drops a full n-unit ticket,
the uniform n-edge sum pays one interaction. -/
private theorem bankRepairDigitBoundaryNominatedBellman
    {n : Nat} {State : Type}
    (next : State → Fin n → State)
    (potential : State → Nat) (z : State)
    (hweak : ∀ e : Fin n,
      potential (next z e) ≤ potential z)
    (hstrict : ∃ e : Fin n,
      potential (next z e) + n ≤ potential z) :
    n + (List.ofFn (fun e : Fin n =>
      potential (next z e))).sum ≤ n * potential z := by
  obtain ⟨chosen, hdrop⟩ := hstrict
  have hpoint :
      ∀ e : Fin n,
        potential (next z e) +
          (if e = chosen then n else 0) ≤ potential z := by
    intro e
    by_cases he : e = chosen
    · subst e
      simpa only [if_pos rfl, ↓reduceIte] using hdrop
    · simpa only [if_neg he, Nat.add_zero] using hweak e
  have hsum := ofFn_sum_le
    (fun e : Fin n =>
      potential (next z e) + (if e = chosen then n else 0))
    (fun _ : Fin n => potential z) hpoint
  rw [ofFn_sum_add, bankRepairDigitSumSpike n chosen n,
    ofFn_sum_const] at hsum
  omega

/-- EXACT missing source task certificate.
The rank is required on the physical BANK state, not chosen
independently from a causal audit at each cut. Its intended
constituents are:
  inherited-origin base labels with remaining seek/zero tasks;
  source/target packet, front and carry lineage tasks in
  the leading fragment, bounded by J_t per lane;
  final leader-sink authority tasks bounded by F+R+U+r;
  the residual inherited-label extinction/log reserve.
For WB, a new .rootLaunch contributes no inherited label.

The three fields below are (i) every physical WB/packet/
retirement edge weak, (ii) one actual selected frontier edge
strict by n, (iii) the initial e(n,t) envelope. None is
available as a theorem in the pinned native owner or proof
ghost. This single Prop is the outstanding source
row/history obligation, not a proof of the desired clock. -/
def BankRepairDigitBoundaryInheritedPacketTaskCertificate {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∃ potential : BankReferenceState ring hbank → Nat,
    (∀ z : BankReferenceState ring hbank,
      BankRepairDigitBoundaryReachable ring hbank z →
      ¬ BankRepairDigitBoundaryRetiredCut ring hbank z →
      ∀ e : Fin n,
        potential (bankRepairNext ring hbank z e) ≤ potential z) ∧
    (∀ z : BankReferenceState ring hbank,
      BankRepairDigitBoundaryReachable ring hbank z →
      ¬ BankRepairDigitBoundaryRetiredCut ring hbank z →
      ∃ e : Fin n,
        potential (bankRepairNext ring hbank z e) + n ≤ potential z) ∧
    (∀ z : BankReferenceState ring hbank,
      BankRepairRFoldEstablished ring hbank z →
      2 * potential z ≤ bankRepairDigitBoundaryMicroCharge n)

/-- Precise handoff: supplied with a compatible physical
inherited-only packet-task certificate and the reachable
no-FIRE property, the original three-part boundary drift
follows without new randomness or state-space changes. -/
theorem bankRepairDigitBoundaryCausalCoverDriftOfInheritedTasks
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hno : BankRepairDigitNoFireClass ring hbank
      (BankRepairDigitBoundaryReachable ring hbank))
    (htasks : BankRepairDigitBoundaryInheritedPacketTaskCertificate
      ring hbank) :
    BankRepairDigitBoundaryCausalCoverDrift ring hbank := by
  obtain ⟨potential, hweak, hstrict, hcap⟩ := htasks
  refine ⟨potential, ?_, ?_, hcap⟩
  · exact bankRepairDigitBoundaryProjectionOfReachableNoFire
      ring hbank hno
  · intro z hz hnon
    exact bankRepairDigitBoundaryNominatedBellman
      (bankRepairNext ring hbank) potential z
      (hweak z hz hnon) (hstrict z hz hnon)

/-!
AUDIT / REMAINING FACT.

The named BankRepairDigitBoundaryInheritedPacketTaskCertificate
is UNPROVED, as is the reachable no-FIRE premise (the latter
is explicitly isolated instead of assuming BankRepairNoFireFromW).
The existing no-FIRE projection gives the first desired conjunct,
and the finite nominated-edge sum gives the second from weak and
strict ranks; the numeric e(n,t) cap for an inherited-tag
J_t-weighted audit count has been proved separately.

These results do NOT establish the full
BankRepairDigitBoundaryCausalCoverDrift. Crucially the displayed
audit count is not itself the physical potential: an inherited
record may require many packet services before retirement and
its identity is historical, not determined by current wBase.
It would be unsound to assert a strict drop for every unfinished
frontier, or to select inconsistent audits after each edge.

The concrete WB example above has n=5, selected pair 0->1,
OLD X=(leader, inherited origin), OLD Y=(blank, no origin).
Its new Y SEEK is tagged .rootLaunch, not .inherited.
That edge is the first explicit local row where an
all-physical-record potential acquires an unpaid new token;
the inherited-only source tag correctly avoids it.

Next task: define a history-compatible weighted remaining-task
frontier whose state rank descends on the packet progress,
collision, boundary-root-sink and inherited-retirement rows.
Check the original BANK/phiD coupling using the explicit no-FIRE
premise until a source theorem proves it on all R-fold histories.
-/

end L3.RenewalReferenceClock



/-!
Per-inherited-label retirement (no new global potential).
This block gives the row-level no-resurrection
certificate, a general finite-horizon max<=sum theorem, and the
exact numerical obstruction to the requested SUM strategy.

It does NOT promote a numerical ledger bound to a physical
single-label retirement drift: neither the outgoing SEEK/ZERO
service-rank descent nor the simultaneous leading/final packet
completion is proved by the existing ancestry lemmas.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The label identity is its OLD inherited site, not its current
host. A newly created rootLaunch never counts as this label. -/
def bankRepairDigitInheritedLabelAlive {n : Nat} {c : Compiled}
    (site : Fin n) (G : Fin n → DigitGhost c n) : Prop :=
  ∃ i : Fin n, (G i).base = some (.inherited site)

def bankRepairDigitInheritedLabelRetired {n : Nat} {c : Compiled}
    (site : Fin n) (G : Fin n → DigitGhost c n) : Prop :=
  ¬ bankRepairDigitInheritedLabelAlive site G

/-- A selected base-service child with inherited identity has an
inherited parent at an OLD endpoint; an untouched child has its
parent at its own OLD site. This is the useful WB/parent
transport without an invented task ranking. -/
theorem bankRepairDigitInheritedLabelParentStep
    {n : Nat} {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n)
    (time : Nat) (e site : Fin n)
    (hnew : bankRepairDigitInheritedLabelAlive site
      (digitGhostStep ring S G time e)) :
    bankRepairDigitInheritedLabelAlive site G := by
  obtain ⟨i, hi⟩ := hnew
  by_cases he : i = e
  · subst i
    have hsource :
        (digitBaseReplay time e (ring.rightNeighbor e)
          (S e) (S (ring.rightNeighbor e))
          (workerW (S e).word
            (S (ring.rightNeighbor e)).word).betaY
          (G e).base (G (ring.rightNeighbor e)).base).x =
          some (.inherited site) := by
      simpa [digitGhostStep, digitService] using hi
    rcases bankRepairDigitBaseReplayXChoice time e
        (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
        (workerW (S e).word
          (S (ring.rightNeighbor e)).word).betaY
        (G e).base (G (ring.rightNeighbor e)).base with hnone | hold
    · rw [hnone] at hsource
      cases hsource
    · exact ⟨e, hold.symm.trans hsource⟩
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hne : ring.rightNeighbor e ≠ e :=
        EWord.rightNeighborDifferent ring hn e
      have hdest :
          (digitBaseReplay time e (ring.rightNeighbor e)
            (S e) (S (ring.rightNeighbor e))
            (workerW (S e).word
              (S (ring.rightNeighbor e)).word).betaY
            (G e).base (G (ring.rightNeighbor e)).base).y =
            some (.inherited site) := by
        simpa [digitGhostStep, digitService, hne] using hi
      rcases bankRepairDigitBaseReplayYChoice time e
          (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
          (workerW (S e).word
            (S (ring.rightNeighbor e)).word).betaY
          (G e).base (G (ring.rightNeighbor e)).base with
        hY | hX | hNew
      · exact ⟨ring.rightNeighbor e, hY.symm.trans hdest⟩
      · exact ⟨e, hX.symm.trans hdest⟩
      · have hbad :
            (some (.rootLaunch time e (ring.rightNeighbor e)) :
              Option (DigitBaseOrigin n)) =
              some (.inherited site) := hNew.symm.trans hdest
        cases hbad
    · have hframe :=
        bankRepairDigitInheritedAuditAwayFrame
          ring S G time e i he hj
      exact ⟨i, hframe.symm.trans hi⟩

/-- No inherited label can reappear once its last causal
descendant has gone. Every row is either a parent transfer,
erasure, collision, rootLaunch or an unchanged remote site. -/
theorem bankRepairDigitInheritedLabelRetiredStep
    {n : Nat} {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (S : Fin n → ProjD c)
    (A : DigitAudit c n)
    (site e : Fin n)
    (hret : bankRepairDigitInheritedLabelRetired site A.current) :
    bankRepairDigitInheritedLabelRetired site
      (digitAuditStep ring S A e).current := by
  intro hnew
  exact hret (bankRepairDigitInheritedLabelParentStep
    hn ring S A.current (A.clock + 1) e site hnew)

/-- The corresponding terminal predicate is closed along the
SAME coupled actual bankRepairNext / OLD digit-audit replay. -/
theorem bankRepairDigitInheritedLabelRetiredBankStep
    {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (site : Fin n)
    (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hret : bankRepairDigitInheritedLabelRetired
      site z.2.current) :
    bankRepairDigitInheritedLabelRetired site
      (bankRepairDigitBoundaryAuditNext ring hbank z e).2.current := by
  exact bankRepairDigitInheritedLabelRetiredStep hn ring
    (piD z.1.val.1) z.2 site e hret

/-- No alternate digit chain: the observer's first coordinate is
the BANK successor for every edge. -/
theorem bankRepairDigitSingleLabelPhysicalProjection
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) :
    (bankRepairDigitBoundaryAuditNext ring hbank z e).1 =
      bankRepairNext ring hbank z.1 e := rfl

/-! ## The pathwise max<=sum finite-horizon principle -/

/-- This lemma is the finite-horizon version of max(T_P,T_Q) <=
T_P+T_Q when each first-hit event is absorbing. Its proof is
induction on the SAME costNumerator and SAME Fin n scheduler.
No independence between different label lifetimes is invoked. -/
private theorem bankRepairDigitTwoTerminalCostBound
    {State : Type} {n : Nat}
    (next : State → Fin n → State)
    (P Q : State → Prop)
    (hP : ∀ z e, P z → P (next z e))
    (hQ : ∀ z e, Q z → Q (next z e)) :
    ∀ z T,
      costNumerator next (fun y => P y ∧ Q y) z T ≤
        costNumerator next P z T + costNumerator next Q z T := by
  classical
  intro z T
  induction T generalizing z with
  | zero =>
      simp only [costNumerator_zero]
      omega
  | succ T ih =>
      by_cases hp : P z
      · by_cases hq : Q z
        · rw [costNumerator_terminal next
            (fun y => P y ∧ Q y) z ⟨hp, hq⟩ (T + 1)]
          exact Nat.zero_le _
        · have hpair : ¬ (P z ∧ Q z) := by
            intro h
            exact hq h.2
          rw [costNumerator_succ next
            (fun y => P y ∧ Q y) z hpair T,
            costNumerator_terminal next P z hp (T + 1),
            costNumerator_succ next Q z hq T]
          have hsum :=
            ofFn_sum_le
              (fun e : Fin n =>
                costNumerator next (fun y => P y ∧ Q y)
                  (next z e) T)
              (fun e : Fin n =>
                costNumerator next Q (next z e) T)
              (fun e => by
                have hi := ih (next z e)
                rw [costNumerator_terminal next P
                  (next z e) (hP z e hp) T,
                  Nat.zero_add] at hi
                exact hi)
          omega
      · by_cases hq : Q z
        · have hpair : ¬ (P z ∧ Q z) := by
            intro h
            exact hp h.1
          rw [costNumerator_succ next
            (fun y => P y ∧ Q y) z hpair T,
            costNumerator_succ next P z hp T,
            costNumerator_terminal next Q z hq (T + 1)]
          have hsum :=
            ofFn_sum_le
              (fun e : Fin n =>
                costNumerator next (fun y => P y ∧ Q y)
                  (next z e) T)
              (fun e : Fin n =>
                costNumerator next P (next z e) T)
              (fun e => by
                have hi := ih (next z e)
                rw [costNumerator_terminal next Q
                  (next z e) (hQ z e hq) T,
                  Nat.add_zero] at hi
                exact hi)
          omega
        · have hpair : ¬ (P z ∧ Q z) := by
            intro h
            exact hp h.1
          rw [costNumerator_succ next
            (fun y => P y ∧ Q y) z hpair T,
            costNumerator_succ next P z hp T,
            costNumerator_succ next Q z hq T]
          have hsum :=
            ofFn_sum_le
              (fun e : Fin n =>
                costNumerator next (fun y => P y ∧ Q y)
                  (next z e) T)
              (fun e : Fin n =>
                costNumerator next P (next z e) T +
                  costNumerator next Q (next z e) T)
              (fun e => ih (next z e))
          rw [ofFn_sum_add] at hsum
          omega

/-- The exact conjunction of a list of absorbed label outcomes. -/
def bankRepairDigitAllLabelTerminals
    {State Label : Type}
    (P : Label → State → Prop) : List Label → State → Prop
  | [], _ => True
  | site :: sites, z =>
      P site z ∧ bankRepairDigitAllLabelTerminals P sites z

private theorem bankRepairDigitAllTerminalsClosed
    {State Label : Type} {n : Nat}
    (next : State → Fin n → State)
    (P : Label → State → Prop)
    (hP : ∀ site z e, P site z → P site (next z e)) :
    ∀ sites z e,
      bankRepairDigitAllLabelTerminals P sites z →
        bankRepairDigitAllLabelTerminals P sites (next z e) := by
  intro sites
  induction sites with
  | nil =>
      intro z e h
      trivial
  | cons site rest ih =>
      intro z e h
      exact ⟨hP site z e h.1, ih z e h.2⟩

/-- The first hit of the intersection has no more finite-horizon
cost than the sum of the separate absorbed first-hit costs.
This is the exact stopping-time max<=sum argument, not a
union bound on one-time state occupancies. -/
theorem bankRepairDigitAllTerminalCostLeSum
    {State Label : Type} {n : Nat}
    (next : State → Fin n → State)
    (P : Label → State → Prop)
    (hclosed : ∀ site z e, P site z → P site (next z e)) :
    ∀ sites z T,
      costNumerator next
        (bankRepairDigitAllLabelTerminals P sites) z T ≤
      (sites.map (fun site => costNumerator next
        (P site) z T)).sum := by
  intro sites
  induction sites with
  | nil =>
      intro z T
      have hdone : bankRepairDigitAllLabelTerminals P [] z := trivial
      rw [costNumerator_terminal next
        (bankRepairDigitAllLabelTerminals P []) z hdone T]
      exact Nat.le_refl _
  | cons site rest ih =>
      intro z T
      have hrest :
          ∀ y e,
            bankRepairDigitAllLabelTerminals P rest y →
            bankRepairDigitAllLabelTerminals P rest (next y e) :=
        fun y e hy =>
          bankRepairDigitAllTerminalsClosed next P hclosed
            rest y e hy
      have htwo := bankRepairDigitTwoTerminalCostBound
        next (P site)
        (bankRepairDigitAllLabelTerminals P rest)
        (hclosed site) hrest z T
      have htail := ih z T
      change
        costNumerator next
            (fun y => P site y ∧
              bankRepairDigitAllLabelTerminals P rest y) z T ≤
          costNumerator next (P site) z T +
            (rest.map (fun a =>
              costNumerator next (P a) z T)).sum
      exact Nat.le_trans htwo (Nat.add_le_add_left htail _)

/-- Summing uniform bounds for independent labels does NOT gain
a logarithm: the cost is multiplied by the number of labels. -/
private theorem bankRepairDigitListMapSumBound
    {Label : Type} (sites : List Label)
    (cost : Label → Nat) (cap : Nat) :
    (∀ site, site ∈ sites → cost site ≤ cap) →
      (sites.map cost).sum ≤ sites.length * cap := by
  induction sites with
  | nil =>
      intro hcost
      simp
  | cons site rest ih =>
      intro hcost
      have hsite : cost site ≤ cap := hcost site (by simp)
      have htail : ∀ other, other ∈ rest → cost other ≤ cap := by
        intro other hmem
        exact hcost other (by simp [hmem])
      have hbound := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-! ## One-label FIRST HIT: conditional only on its own task rank -/

/-- The actual same-word audit prefix from ONE specified R-fold
BANK entrance. Keeping a fixed entrance avoids silently choosing
a fresh incompatible inherited-label identity at later cuts. -/
def BankRepairDigitOneLabelReachableFrom
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ word : List (Fin n),
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = z

theorem bankRepairDigitOneLabelReachableStep
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hz : BankRepairDigitOneLabelReachableFrom
      ring hbank start z) :
    BankRepairDigitOneLabelReachableFrom ring hbank start
      (bankRepairDigitBoundaryAuditNext ring hbank z e) := by
  obtain ⟨word, hword⟩ := hz
  refine ⟨word ++ [e], ?_⟩
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact congrArg
    (fun w => bankRepairDigitBoundaryAuditNext ring hbank w e)
    hword

/-- This is ONE inherited base identity only, not a global
potential for all packet authority or the boundary cut.
Its promised task count decreases on a nominated actual edge
and does not increase on other edges. The budget is L_s:
the paper's SEEK followed by ZERO lifetime, NOT J_s, which is
an aggregate packet ledger per leading lane.

The origin/parent/away lemmas do not prove this interface:
they do not quantify a strictly decreasing remaining distance for
all collision and top/beta first-match rows. -/
def BankRepairDigitSingleInheritedLabelTasks
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (site : Fin n) : Prop :=
  ∃ remaining :
      (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) → Nat,
    (∀ z,
      BankRepairDigitOneLabelReachableFrom ring hbank start z →
      ¬ bankRepairDigitInheritedLabelRetired site z.2.current →
      ∀ e : Fin n,
        remaining (bankRepairDigitBoundaryAuditNext
          ring hbank z e) ≤ remaining z) ∧
    (∀ z,
      BankRepairDigitOneLabelReachableFrom ring hbank start z →
      ¬ bankRepairDigitInheritedLabelRetired site z.2.current →
      ∃ e : Fin n,
        remaining (bankRepairDigitBoundaryAuditNext
          ring hbank z e) + 1 ≤ remaining z) ∧
    remaining (start, digitAuditInitial (piD start.val.1)) ≤
      bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))

/-- For ONE inherited identity, one nominated actual edge that
spends one remaining task has mean <=n per task.
This is a finite-horizon n*L_s bound conditional ONLY on the
single-label row/task certificate, not a global boundary drift.
The comparison stop outside the actual-reachable region is exact
at its original entrance because that region is forward closed. -/
theorem bankRepairDigitSingleLabelCostOfTasks
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (site : Fin n)
    (hcert : BankRepairDigitSingleInheritedLabelTasks
      ring hbank start site) :
    ∀ T : Nat,
      costNumerator
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun z => bankRepairDigitInheritedLabelRetired
          site z.2.current)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      n ^ T *
        (n * bankRepairDigitLeadingLength
          (ceilLogTwo (ceilLogTwo n))) := by
  classical
  obtain ⟨remaining, hweak, hstrict, hcap⟩ := hcert
  have hroot :
      BankRepairDigitOneLabelReachableFrom ring hbank start
        (start, digitAuditInitial (piD start.val.1)) :=
    ⟨[], rfl⟩
  have hbellman :
      ∀ z,
        ¬ (¬ BankRepairDigitOneLabelReachableFrom
              ring hbank start z ∨
            bankRepairDigitInheritedLabelRetired site z.2.current) →
        n + (List.ofFn (fun e : Fin n =>
          if BankRepairDigitOneLabelReachableFrom ring hbank start
              (bankRepairDigitBoundaryAuditNext ring hbank z e)
          then n * remaining
              (bankRepairDigitBoundaryAuditNext ring hbank z e)
          else 0)).sum ≤
        n * (if BankRepairDigitOneLabelReachableFrom
              ring hbank start z then n * remaining z else 0) := by
    intro z hnot
    have hreach :
        BankRepairDigitOneLabelReachableFrom
          ring hbank start z := by
      by_cases hr :
          BankRepairDigitOneLabelReachableFrom ring hbank start z
      · exact hr
      · exact False.elim (hnot (Or.inl hr))
    have halive :
        ¬ bankRepairDigitInheritedLabelRetired site z.2.current := by
      intro hr
      exact hnot (Or.inr hr)
    have hweakScaled :
        ∀ e : Fin n,
          n * remaining
            (bankRepairDigitBoundaryAuditNext ring hbank z e) ≤
              n * remaining z := by
      intro e
      exact Nat.mul_le_mul_left n
        (hweak z hreach halive e)
    have hstrictScaled :
        ∃ e : Fin n,
          n * remaining
            (bankRepairDigitBoundaryAuditNext ring hbank z e) + n ≤
              n * remaining z := by
      obtain ⟨e, he⟩ := hstrict z hreach halive
      refine ⟨e, ?_⟩
      have hm := Nat.mul_le_mul_left n he
      simpa only [Nat.mul_add, Nat.mul_one] using hm
    have hdrift :=
      bankRepairDigitBoundaryNominatedBellman
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun y => n * remaining y) z hweakScaled hstrictScaled
    have hsum :
        (List.ofFn (fun e : Fin n =>
          if BankRepairDigitOneLabelReachableFrom ring hbank start
              (bankRepairDigitBoundaryAuditNext ring hbank z e)
          then n * remaining
              (bankRepairDigitBoundaryAuditNext ring hbank z e)
          else 0)).sum =
        (List.ofFn (fun e : Fin n =>
          n * remaining
            (bankRepairDigitBoundaryAuditNext ring hbank z e))).sum := by
      exact ofFn_sum_eq _ _ (by
        intro e
        exact if_pos (bankRepairDigitOneLabelReachableStep
          ring hbank start z e hreach))
    rw [hsum, if_pos hreach]
    exact hdrift
  intro T
  have hcomparison :=
    Prob.costNumerator_le_of_potential
      (bankRepairDigitBoundaryAuditNext ring hbank)
      (fun z =>
        ¬ BankRepairDigitOneLabelReachableFrom ring hbank start z ∨
        bankRepairDigitInheritedLabelRetired site z.2.current)
      (fun z =>
        if BankRepairDigitOneLabelReachableFrom ring hbank start z
        then n * remaining z else 0)
      hbellman
      (start, digitAuditInitial (piD start.val.1)) T
  have hsame :=
    bankRepairDigitCostClosedTarget
      (bankRepairDigitBoundaryAuditNext ring hbank)
      (BankRepairDigitOneLabelReachableFrom ring hbank start)
      (fun z => bankRepairDigitInheritedLabelRetired site z.2.current)
      (fun z hz e =>
        bankRepairDigitOneLabelReachableStep
          ring hbank start z e hz)
      (start, digitAuditInitial (piD start.val.1)) hroot T
  have hbound :
      costNumerator
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun z => bankRepairDigitInheritedLabelRetired
          site z.2.current)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      n ^ T * (n * remaining
        (start, digitAuditInitial (piD start.val.1))) := by
    rw [hsame]
    simpa only [if_pos hroot] using hcomparison
  exact Nat.le_trans hbound
    (Nat.mul_le_mul_left (n ^ T)
      (Nat.mul_le_mul_left n hcap))

/-! ## All inherited base labels: max <= sum on one audit history -/

/-- The first time all n possible inherited identities have
disappeared. The actual initial audit can have fewer than n labels:
an initially absent identity is already retired and costs zero. -/
def bankRepairDigitAllInheritedLabelsRetired
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  bankRepairDigitAllLabelTerminals
    (fun site (w : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) =>
      bankRepairDigitInheritedLabelRetired site w.2.current)
    (List.ofFn (fun site : Fin n => site)) z

/-- The desired max<=sum result, on the complete coupled
BANK/OLD-audit process, with each separate absorbed first-hit
cost measured from the SAME actual R-fold entrance. -/
theorem bankRepairDigitAllInheritedCostLeSum
    {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (T : Nat) :
    costNumerator (bankRepairDigitBoundaryAuditNext ring hbank)
        (bankRepairDigitAllInheritedLabelsRetired ring hbank)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      ((List.ofFn (fun site : Fin n => site)).map
        (fun site =>
          costNumerator (bankRepairDigitBoundaryAuditNext ring hbank)
            (fun z => bankRepairDigitInheritedLabelRetired
              site z.2.current)
            (start, digitAuditInitial (piD start.val.1)) T)).sum := by
  exact bankRepairDigitAllTerminalCostLeSum
    (bankRepairDigitBoundaryAuditNext ring hbank)
    (fun site (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) =>
        bankRepairDigitInheritedLabelRetired site z.2.current)
    (fun site z e hz =>
      bankRepairDigitInheritedLabelRetiredBankStep
        hn ring hbank site z e hz)
    (List.ofFn (fun site : Fin n => site))
    (start, digitAuditInitial (piD start.val.1)) T

/-- Suppose each of at most n labels has a first-hit bound
n*L_s. The max<=sum method then spends n^2*L_s,
not the paper's n*(log n+L_s) bound.
This theorem is a fully precise finite-horizon ceiling for
the proposed sum method, conditional on single-label clocks. -/
theorem bankRepairDigitAllInheritedSumOfSingles
    {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hsingle : ∀ site : Fin n, ∀ T,
      costNumerator (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun z => bankRepairDigitInheritedLabelRetired site z.2.current)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      n ^ T *
        (n * bankRepairDigitLeadingLength
          (ceilLogTwo (ceilLogTwo n)))) :
    ∀ T,
      2 * costNumerator
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (bankRepairDigitAllInheritedLabelsRetired ring hbank)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      n ^ T *
        (2 * (n ^ 2 * bankRepairDigitLeadingLength
          (ceilLogTwo (ceilLogTwo n)))) := by
  intro T
  have hmax := bankRepairDigitAllInheritedCostLeSum
    hn ring hbank start T
  have hsum := bankRepairDigitListMapSumBound
    (List.ofFn (fun site : Fin n => site))
    (fun site =>
      costNumerator (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun z => bankRepairDigitInheritedLabelRetired site z.2.current)
        (start, digitAuditInitial (piD start.val.1)) T)
    (n ^ T * (n * bankRepairDigitLeadingLength
      (ceilLogTwo (ceilLogTwo n))))
    (fun site _ => hsingle site T)
  have hlength :
      (List.ofFn (fun site : Fin n => site)).length = n := by
    simp
  calc
    2 * costNumerator
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (bankRepairDigitAllInheritedLabelsRetired ring hbank)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      2 * ((List.ofFn (fun site : Fin n => site)).map
        (fun site =>
          costNumerator (bankRepairDigitBoundaryAuditNext ring hbank)
            (fun z => bankRepairDigitInheritedLabelRetired
              site z.2.current)
            (start, digitAuditInitial (piD start.val.1)) T)).sum :=
        Nat.mul_le_mul_left 2 hmax
    _ ≤ 2 * ((List.ofFn (fun site : Fin n => site)).length *
      (n ^ T * (n * bankRepairDigitLeadingLength
        (ceilLogTwo (ceilLogTwo n))))) :=
        Nat.mul_le_mul_left 2 hsum
    _ = n ^ T * (2 * (n ^ 2 * bankRepairDigitLeadingLength
        (ceilLogTwo (ceilLogTwo n)))) := by
          rw [hlength]
          simp only [Nat.pow_two]
          ac_rfl

/-- All single-label task certificates are sufficient for the
preceding n^2 L_s sum estimate, but NOT for the requested micro
charge. No packet boundary is inferred from base-label extinction. -/
theorem bankRepairDigitAllInheritedSumOfLabelTasks
    {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hcert : ∀ site : Fin n,
      BankRepairDigitSingleInheritedLabelTasks ring hbank start site) :
    ∀ T,
      2 * costNumerator
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (bankRepairDigitAllInheritedLabelsRetired ring hbank)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      n ^ T *
        (2 * (n ^ 2 * bankRepairDigitLeadingLength
          (ceilLogTwo (ceilLogTwo n)))) := by
  exact bankRepairDigitAllInheritedSumOfSingles hn ring hbank
    start (fun site T =>
      bankRepairDigitSingleLabelCostOfTasks
        ring hbank start site (hcert site) T)

/-! ## Exact integer failure of sum charging on the BANK band -/

/-- Evaluating the actual source definitions at the first BANK
width, including the full J_s and e-envelope terms. -/
theorem bankRepairDigitSingleLabelFirstBankConstants :
    bankRepairDigitLeadingLength 7 = 259 ∧
    bankRepairDigitBoundaryServices 7 = 9228714 ∧
    bankRepairDigitBoundaryUpper 7 = 2149294308 := by
  exact ⟨rfl, rfl, rfl⟩

/-- At n=2^79+1 the outer compiled q is 80 and s is 7.
This is a closed computation using Params.ceilLogTwo=Nat.log2. -/
theorem bankRepairDigitSingleLabelFirstBankWidth :
    ceilLogTwo (ceilLogTwo ((2 : Nat) ^ 79 + 1)) = 7 := by
  rfl

/-- The proposed n-label SUM of n*L_s is larger than the
boundary micro-charge by this exact positive Nat amount.
This is a gap between PROOF BOUNDS, not a counterexample
to the genuine first-hit expectation or to the paper. -/
theorem bankRepairDigitBaseLabelSumExactGap :
    2 * ((((2 : Nat) ^ 79 + 1) ^ 2) *
      bankRepairDigitLeadingLength 7) =
    bankRepairDigitBoundaryMicroCharge ((2 : Nat) ^ 79 + 1) +
      189264462034351925309040429168375972696629814280254 := by
  rw [bankRepairDigitBoundaryMicroCharge,
    bankRepairDigitSingleLabelFirstBankWidth]
  rfl

theorem bankRepairDigitBaseLabelSumExceedsMicroCharge :
    bankRepairDigitBoundaryMicroCharge ((2 : Nat) ^ 79 + 1) <
      2 * ((((2 : Nat) ^ 79 + 1) ^ 2) *
        bankRepairDigitLeadingLength 7) := by
  have h := bankRepairDigitBaseLabelSumExactGap
  omega

/-- If one charges a full J_s to each inherited label instead
of the paper's correct J_s for an entire leading lane, the
overcount is much larger. Its precise positive difference: -/
theorem bankRepairDigitPacketLabelSumExactGap :
    2 * ((((2 : Nat) ^ 79 + 1) ^ 2) *
      bankRepairDigitBoundaryServices 7) =
    bankRepairDigitBoundaryMicroCharge ((2 : Nat) ^ 79 + 1) +
      6743890310729313196931024509916590486497502033944404364 := by
  rw [bankRepairDigitBoundaryMicroCharge,
    bankRepairDigitSingleLabelFirstBankWidth]
  rfl

end L3.RenewalReferenceClock

/-!
Integer exponential-tail method for inherited base labels.

This block *does not* introduce a global boundary potential.
It converts ONE inherited label's nominated remaining-task rank
to a weighted word-count inequality, sums the indicators over the
finite initial set of inherited labels, and develops a separate
Nat-only geometric-tail bound. Neither labels nor edge words are
reset between terms.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open UniformFirstHit

set_option autoImplicit false
set_option Elab.async false

open Classical in
/-- A retired label has weight zero. A live label has the discrete
exponential weight 2^remaining; no Rat, Real or Mathlib is used. -/
noncomputable def bankRepairDigitLivePowWeight {State : Type}
    (alive : State → Prop) (remaining : State → Nat)
    (z : State) : Nat :=
  if alive z then 2 ^ remaining z else 0

/-- For each living label, all outgoing edges weakly decrease its
remaining tasks, and at least one real edge removes a task.
The exact one-step inequality is 2 sum_e weight(next e)
<= (2n-1) weight(old); it also holds after retirement because
the retirement event is absorbing. -/
theorem bankRepairDigitLivePowWeightEdge
    {State : Type} {n : Nat}
    (hn : 1 ≤ n)
    (next : State → Fin n → State)
    (good alive : State → Prop)
    (remaining : State → Nat)
    (hret : ∀ z e, ¬ alive z → ¬ alive (next z e))
    (hweak : ∀ z, good z → alive z →
      ∀ e, remaining (next z e) ≤ remaining z)
    (hstrict : ∀ z, good z → alive z →
      ∃ e : Fin n, remaining (next z e) + 1 ≤ remaining z)
    (z : State) (hz : good z) :
    2 * (List.ofFn (fun e : Fin n =>
      bankRepairDigitLivePowWeight alive remaining (next z e))).sum ≤
      (2 * n - 1) * bankRepairDigitLivePowWeight alive remaining z := by
  classical
  by_cases ha : alive z
  · obtain ⟨chosen, hdrop⟩ := hstrict z hz ha
    have hpositive : 1 ≤ remaining z := by omega
    have hpowstep :
        2 * 2 ^ (remaining z - 1) = 2 ^ remaining z := by
      calc
        2 * 2 ^ (remaining z - 1) =
            2 ^ (remaining z - 1) * 2 := by ac_rfl
        _ = 2 ^ ((remaining z - 1) + 1) :=
          (Nat.pow_succ 2 (remaining z - 1)).symm
        _ = 2 ^ remaining z := by
          congr 1
          omega
    have hchosen :
        2 * bankRepairDigitLivePowWeight alive remaining
          (next z chosen) ≤ 2 ^ remaining z := by
      by_cases hc : alive (next z chosen)
      · have hle : remaining (next z chosen) ≤
            remaining z - 1 := by omega
        have hp :
            2 ^ remaining (next z chosen) ≤
              2 ^ (remaining z - 1) :=
          Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hle
        simp only [bankRepairDigitLivePowWeight, if_pos hc]
        exact Nat.le_trans (Nat.mul_le_mul_left 2 hp)
          (Nat.le_of_eq hpowstep)
      · simp [bankRepairDigitLivePowWeight, hc]
    have hpoint :
        ∀ e : Fin n,
          2 * bankRepairDigitLivePowWeight alive remaining
              (next z e) +
            (if e = chosen then
              bankRepairDigitLivePowWeight alive remaining z
             else 0) ≤
          2 * bankRepairDigitLivePowWeight alive remaining z := by
      intro e
      by_cases he : e = chosen
      · subst e
        rw [if_pos rfl]
        have hwz :
            bankRepairDigitLivePowWeight alive remaining z =
              2 ^ remaining z := by
          simp [bankRepairDigitLivePowWeight, ha]
        rw [hwz]
        omega
      · rw [if_neg he, Nat.add_zero]
        by_cases hnext : alive (next z e)
        · have hp :=
            Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
              (hweak z hz ha e)
          simp only [bankRepairDigitLivePowWeight,
            if_pos hnext, if_pos ha]
          exact Nat.mul_le_mul_left 2 hp
        · simp [bankRepairDigitLivePowWeight, hnext, ha]
    have hsum := ofFn_sum_le
      (fun e : Fin n =>
        2 * bankRepairDigitLivePowWeight alive remaining
            (next z e) +
          (if e = chosen then
            bankRepairDigitLivePowWeight alive remaining z
           else 0))
      (fun _ : Fin n =>
        2 * bankRepairDigitLivePowWeight alive remaining z)
      hpoint
    rw [ofFn_sum_add, ofFn_sum_mul_left,
      bankRepairDigitSumSpike n chosen
        (bankRepairDigitLivePowWeight alive remaining z),
      ofFn_sum_const] at hsum
    have hcoefficient : (2 * n - 1) + 1 = 2 * n := by
      omega
    have hidentity :
        n * (2 * bankRepairDigitLivePowWeight alive remaining z) =
        (2 * n - 1) * bankRepairDigitLivePowWeight alive remaining z +
          bankRepairDigitLivePowWeight alive remaining z := by
      calc
        n * (2 * bankRepairDigitLivePowWeight alive remaining z) =
            (2 * n) * bankRepairDigitLivePowWeight alive remaining z := by
              ac_rfl
        _ = ((2 * n - 1) + 1) *
            bankRepairDigitLivePowWeight alive remaining z := by
              rw [hcoefficient]
        _ = (2 * n - 1) *
            bankRepairDigitLivePowWeight alive remaining z +
              bankRepairDigitLivePowWeight alive remaining z := by
              rw [Nat.add_mul, Nat.one_mul]
    rw [hidentity] at hsum
    omega
  · have hzero :
        bankRepairDigitLivePowWeight alive remaining z = 0 := by
      simp [bankRepairDigitLivePowWeight, ha]
    have hzeroNext :
        (List.ofFn (fun e : Fin n =>
          bankRepairDigitLivePowWeight alive remaining
            (next z e))).sum = 0 := by
      have heq := ofFn_sum_eq
        (fun e : Fin n =>
          bankRepairDigitLivePowWeight alive remaining (next z e))
        (fun _ : Fin n => 0)
        (by
          intro e
          simp [bankRepairDigitLivePowWeight, hret z e ha])
      rw [heq, ofFn_sum_const, Nat.mul_zero]
    rw [hzero, hzeroNext]
    exact Nat.zero_le _

/-- Literal sum of weights of all n^t edge words, represented by
a structurally recursive finite tree. The case t=0 weighs the
single empty word; t+1 branches over all n physical edges. -/
noncomputable def bankRepairDigitWeightedAliveWords
    {State : Type} {n : Nat}
    (next : State → Fin n → State)
    (alive : State → Prop)
    (remaining : State → Nat)
    (z : State) : Nat → Nat
  | 0 => bankRepairDigitLivePowWeight alive remaining z
  | t + 1 =>
      (List.ofFn (fun e : Fin n =>
        bankRepairDigitWeightedAliveWords next alive remaining
          (next z e) t)).sum

/-- The desired per-label exponential-tail integer inequality:
2^t times the weighted alive word count is bounded by
2^remaining(start) * (2n-1)^t. Induction is over t only;
the old-to-new good predicate is forward closed. -/
theorem bankRepairDigitWeightedAliveWordsBound
    {State : Type} {n : Nat}
    (hn : 1 ≤ n)
    (next : State → Fin n → State)
    (good alive : State → Prop)
    (remaining : State → Nat)
    (hgood : ∀ z e, good z → good (next z e))
    (hret : ∀ z e, ¬ alive z → ¬ alive (next z e))
    (hweak : ∀ z, good z → alive z →
      ∀ e, remaining (next z e) ≤ remaining z)
    (hstrict : ∀ z, good z → alive z →
      ∃ e : Fin n, remaining (next z e) + 1 ≤ remaining z) :
    ∀ z, good z → ∀ t,
      2 ^ t * bankRepairDigitWeightedAliveWords next
        alive remaining z t ≤
      (2 * n - 1) ^ t *
        bankRepairDigitLivePowWeight alive remaining z := by
  intro z hz t
  induction t generalizing z with
  | zero =>
      simp [bankRepairDigitWeightedAliveWords]
  | succ t ih =>
      have hpoint :
          ∀ e : Fin n,
            2 ^ t * bankRepairDigitWeightedAliveWords
              next alive remaining (next z e) t ≤
            (2 * n - 1) ^ t *
              bankRepairDigitLivePowWeight alive remaining
                (next z e) := by
        intro e
        exact ih (next z e) (hgood z e hz)
      have hsum := ofFn_sum_le
        (fun e : Fin n =>
          2 ^ t * bankRepairDigitWeightedAliveWords
            next alive remaining (next z e) t)
        (fun e : Fin n =>
          (2 * n - 1) ^ t *
            bankRepairDigitLivePowWeight alive remaining
              (next z e))
        hpoint
      have hedge := bankRepairDigitLivePowWeightEdge
        hn next good alive remaining hret hweak hstrict z hz
      calc
        2 ^ (t + 1) *
            bankRepairDigitWeightedAliveWords next
              alive remaining z (t + 1) =
          2 * (List.ofFn (fun e : Fin n =>
            2 ^ t * bankRepairDigitWeightedAliveWords next
              alive remaining (next z e) t)).sum := by
                rw [Nat.pow_succ]
                simp only [bankRepairDigitWeightedAliveWords,
                  ofFn_sum_mul_left]
                ac_rfl
        _ ≤ 2 * (List.ofFn (fun e : Fin n =>
            (2 * n - 1) ^ t *
              bankRepairDigitLivePowWeight alive remaining
                (next z e))).sum :=
          Nat.mul_le_mul_left 2 hsum
        _ = (2 * n - 1) ^ t *
            (2 * (List.ofFn (fun e : Fin n =>
              bankRepairDigitLivePowWeight alive remaining
                (next z e))).sum) := by
                  rw [ofFn_sum_mul_left]
                  ac_rfl
        _ ≤ (2 * n - 1) ^ t *
            ((2 * n - 1) *
              bankRepairDigitLivePowWeight alive remaining z) :=
          Nat.mul_le_mul_left _ hedge
        _ = (2 * n - 1) ^ (t + 1) *
            bankRepairDigitLivePowWeight alive remaining z := by
              rw [Nat.pow_succ]
              ac_rfl


/-! ## Union bound by finite sums of SAME-word alive indicators -/

open Classical in
/-- Unweighted number of edge words of length t satisfying the
given predicate at the final state. The entire tree is finite. -/
noncomputable def bankRepairDigitAliveWordCount
    {State : Type} {n : Nat}
    (next : State → Fin n → State)
    (alive : State → Prop) (z : State) : Nat → Nat
  | 0 => if alive z then 1 else 0
  | t + 1 =>
      (List.ofFn (fun e : Fin n =>
        bankRepairDigitAliveWordCount next alive (next z e) t)).sum

private theorem bankRepairDigitListMappedTermLeSum
    {Label : Type}
    (sites : List Label) (f : Label → Nat)
    (site : Label) (hmem : site ∈ sites) :
    f site ≤ (sites.map f).sum := by
  induction sites with
  | nil =>
      cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst site
        simp only [List.map_cons, List.sum_cons]
        exact Nat.le_add_right _ _
      · have hle := ih hrest
        simp only [List.map_cons, List.sum_cons]
        omega

/-- Reorder finite sums: sum over edge then over labels equals
sum over labels then over edge. No Finset or Fubini theorem needed. -/
private theorem bankRepairDigitSwapEdgeLabelSums
    {Label : Type} {n : Nat}
    (sites : List Label)
    (f : Label → Fin n → Nat) :
    (List.ofFn (fun e : Fin n =>
      (sites.map (fun site => f site e)).sum)).sum =
      (sites.map (fun site =>
        (List.ofFn (fun e : Fin n => f site e)).sum)).sum := by
  induction sites with
  | nil =>
      simp only [List.map_nil, List.sum_nil, ofFn_sum_const,
        Nat.mul_zero]
  | cons site rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ofFn_sum_add, ih]

/-- For every common edge word, the indicator "some member of
the fixed label list is alive" is at most the sum of
2^remaining for the surviving labels. The induction on t
keeps the SAME physical successor, not independent tapes. -/
theorem bankRepairDigitUnionAliveCountLeWeightedSum
    {State Label : Type} {n : Nat}
    (next : State → Fin n → State)
    (sites : List Label)
    (alive : Label → State → Prop)
    (remaining : Label → State → Nat) :
    ∀ z t,
      bankRepairDigitAliveWordCount next
          (fun y => ∃ site, site ∈ sites ∧ alive site y) z t ≤
        (sites.map (fun site =>
          bankRepairDigitWeightedAliveWords next
            (alive site) (remaining site) z t)).sum := by
  classical
  intro z t
  induction t generalizing z with
  | zero =>
      simp only [bankRepairDigitAliveWordCount,
        bankRepairDigitWeightedAliveWords]
      by_cases hsome : ∃ site, site ∈ sites ∧ alive site z
      · rw [if_pos hsome]
        obtain ⟨site, hmem, halive⟩ := hsome
        have hterm :=
          bankRepairDigitListMappedTermLeSum sites
            (fun site =>
              bankRepairDigitLivePowWeight
                (alive site) (remaining site) z) site hmem
        have hpos :
            1 ≤ bankRepairDigitLivePowWeight
              (alive site) (remaining site) z := by
          simp only [bankRepairDigitLivePowWeight, if_pos halive]
          exact Nat.pow_pos (by omega : 0 < (2 : Nat))
        exact Nat.le_trans hpos hterm
      · rw [if_neg hsome]
        exact Nat.zero_le _
  | succ t ih =>
      change
        (List.ofFn (fun e : Fin n =>
          bankRepairDigitAliveWordCount next
            (fun y => ∃ site, site ∈ sites ∧ alive site y)
            (next z e) t)).sum ≤
        (sites.map (fun site =>
          (List.ofFn (fun e : Fin n =>
            bankRepairDigitWeightedAliveWords next
              (alive site) (remaining site)
              (next z e) t)).sum)).sum
      calc
        (List.ofFn (fun e : Fin n =>
          bankRepairDigitAliveWordCount next
            (fun y => ∃ site, site ∈ sites ∧ alive site y)
            (next z e) t)).sum ≤
          (List.ofFn (fun e : Fin n =>
            (sites.map (fun site =>
              bankRepairDigitWeightedAliveWords next
                (alive site) (remaining site)
                (next z e) t)).sum)).sum :=
            ofFn_sum_le _ _ (fun e => ih (next z e))
        _ = (sites.map (fun site =>
            (List.ofFn (fun e : Fin n =>
              bankRepairDigitWeightedAliveWords next
                (alive site) (remaining site)
                (next z e) t)).sum)).sum :=
          bankRepairDigitSwapEdgeLabelSums sites
            (fun site e =>
              bankRepairDigitWeightedAliveWords next
                (alive site) (remaining site) (next z e) t)

private theorem bankRepairDigitScaleMappedListSum
    {Label : Type}
    (sites : List Label) (f : Label → Nat) (scale : Nat) :
    scale * (sites.map f).sum =
      (sites.map (fun site => scale * f site)).sum := by
  induction sites with
  | nil => rfl
  | cons site rest ih =>
      simp only [List.map_cons, List.sum_cons, Nat.mul_add, ih]

/-- The integer union-tail bound at ANY common start state:
2^t #words(some label alive) <=
 (2n-1)^t * sum_label 2^remaining(start).
All labels use the SAME physical edge history. -/
private theorem bankRepairDigitListMapSumMono
    {Label : Type}
    (sites : List Label) (f g : Label → Nat)
    (h : ∀ site, site ∈ sites → f site ≤ g site) :
    (sites.map f).sum ≤ (sites.map g).sum := by
  induction sites with
  | nil =>
      exact Nat.le_refl _
  | cons site rest ih =>
      have hhead := h site (by simp)
      have htail : ∀ other, other ∈ rest → f other ≤ g other := by
        intro other hmem
        exact h other (by simp [hmem])
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add hhead (ih htail)

/-- Same-word union-tail inequality without independence, for any
finite list of labelled absorbing tasks. Multiply the literal
union indicator by 2^t, then interchange finite edge/label sums. -/
theorem bankRepairDigitUnionTailOfLabelRanks
    {State Label : Type} {n : Nat}
    (hn : 1 ≤ n)
    (next : State → Fin n → State)
    (sites : List Label)
    (good : State → Prop)
    (alive : Label → State → Prop)
    (remaining : Label → State → Nat)
    (hgood : ∀ z e, good z → good (next z e))
    (hret : ∀ site z e,
      ¬ alive site z → ¬ alive site (next z e))
    (hweak : ∀ site z, good z → alive site z →
      ∀ e, remaining site (next z e) ≤ remaining site z)
    (hstrict : ∀ site z, good z → alive site z →
      ∃ e : Fin n,
        remaining site (next z e) + 1 ≤ remaining site z)
    (z : State) (hz : good z) (t : Nat) :
    2 ^ t * bankRepairDigitAliveWordCount next
        (fun y => ∃ site, site ∈ sites ∧ alive site y) z t ≤
      (2 * n - 1) ^ t *
        (sites.map (fun site =>
          bankRepairDigitLivePowWeight
            (alive site) (remaining site) z)).sum := by
  have hu := bankRepairDigitUnionAliveCountLeWeightedSum
    next sites alive remaining z t
  have hmono :=
    bankRepairDigitListMapSumMono sites
      (fun site => 2 ^ t *
        bankRepairDigitWeightedAliveWords next
          (alive site) (remaining site) z t)
      (fun site => (2 * n - 1) ^ t *
        bankRepairDigitLivePowWeight
          (alive site) (remaining site) z)
      (by
        intro site hmem
        exact bankRepairDigitWeightedAliveWordsBound
          hn next good (alive site) (remaining site)
          hgood (hret site) (hweak site) (hstrict site)
          z hz t)
  have hfirst := bankRepairDigitScaleMappedListSum
    sites (fun site =>
      bankRepairDigitWeightedAliveWords
        next (alive site) (remaining site) z t) (2 ^ t)
  have hsecond := bankRepairDigitScaleMappedListSum
    sites (fun site =>
      bankRepairDigitLivePowWeight
        (alive site) (remaining site) z) ((2 * n - 1) ^ t)
  calc
    2 ^ t * bankRepairDigitAliveWordCount next
        (fun y => ∃ site, site ∈ sites ∧ alive site y) z t ≤
      2 ^ t *
        (sites.map (fun site =>
          bankRepairDigitWeightedAliveWords next
            (alive site) (remaining site) z t)).sum :=
      Nat.mul_le_mul_left (2 ^ t) hu
    _ = (sites.map (fun site => 2 ^ t *
          bankRepairDigitWeightedAliveWords next
            (alive site) (remaining site) z t)).sum := hfirst
    _ ≤ (sites.map (fun site => (2 * n - 1) ^ t *
          bankRepairDigitLivePowWeight
            (alive site) (remaining site) z)).sum := hmono
    _ = (2 * n - 1) ^ t *
          (sites.map (fun site =>
            bankRepairDigitLivePowWeight
              (alive site) (remaining site) z)).sum := hsecond.symm


/-! ## Nat Bernoulli and geometric decay, without Rat or Real -/

/-- The first two binomial terms, proved inductively over k.
For b=a+1 this supplies the exact half-life block inequality.
No binomial coefficients, Finset or field arithmetic are used. -/
theorem bankRepairDigitNatBernoulli
    (a : Nat) :
    ∀ k : Nat,
      a ^ (k + 1) + (k + 1) * a ^ k ≤
        (a + 1) ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hmul := Nat.mul_le_mul_right (a + 1) ih
      have hidentity :
          (a ^ (k + 1) + (k + 1) * a ^ k) * (a + 1) =
            a ^ ((k + 1) + 1) +
              ((k + 1) + 1) * a ^ (k + 1) +
              (k + 1) * a ^ k := by
        have hs := Nat.pow_succ a k
        have hss := Nat.pow_succ a (k + 1)
        calc
          (a ^ (k + 1) + (k + 1) * a ^ k) * (a + 1) =
            (a ^ (k + 1) * a + a ^ (k + 1)) +
              ((k + 1) * a ^ k * a + (k + 1) * a ^ k) := by
              rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
              ac_rfl
          _ = a ^ ((k + 1) + 1) +
              ((k + 1) + 1) * a ^ (k + 1) +
              (k + 1) * a ^ k := by
              have hcoef :
                  ((k + 1) + 1) * a ^ (k + 1) =
                    (k + 1) * a ^ (k + 1) + a ^ (k + 1) := by
                rw [Nat.add_mul, Nat.one_mul]
              rw [hss, hcoef, hs]
              ac_rfl
      calc
        a ^ ((k + 1) + 1) +
            ((k + 1) + 1) * a ^ (k + 1) ≤
          a ^ ((k + 1) + 1) +
            ((k + 1) + 1) * a ^ (k + 1) +
              (k + 1) * a ^ k := Nat.le_add_right _ _
        _ = (a ^ (k + 1) + (k + 1) * a ^ k) *
              (a + 1) := hidentity.symm
        _ ≤ (a + 1) ^ (k + 1) * (a + 1) := hmul
        _ = (a + 1) ^ ((k + 1) + 1) :=
          (Nat.pow_succ (a + 1) (k + 1)).symm

/-- Every block of b>=2 fair Bernoulli trials with failure
probability (b-1)/b has at most half its original mass.
Use b=2n to obtain 2(2n-1)^(2n) <= (2n)^(2n). -/
theorem bankRepairDigitGeometricBlockHalf
    (b : Nat) (hb : 2 ≤ b) :
    2 * (b - 1) ^ b ≤ b ^ b := by
  have hunit : (b - 1) + 1 = b := by omega
  have hbern :
      (b - 1) ^ b + b * (b - 1) ^ (b - 1) ≤ b ^ b := by
    simpa only [hunit] using
      bankRepairDigitNatBernoulli (b - 1) (b - 1)
  have hpow :
      (b - 1) ^ b =
        (b - 1) ^ (b - 1) * (b - 1) := by
    rw [← hunit]
    exact Nat.pow_succ (b - 1) (b - 1)
  have hcomponent :
      (b - 1) ^ b ≤ b * (b - 1) ^ (b - 1) := by
    rw [hpow]
    calc
      (b - 1) ^ (b - 1) * (b - 1) ≤
          (b - 1) ^ (b - 1) * b :=
        Nat.mul_le_mul_left _ (by omega)
      _ = b * (b - 1) ^ (b - 1) := by ac_rfl
  have htwo :
      2 * (b - 1) ^ b ≤
        (b - 1) ^ b + b * (b - 1) ^ (b - 1) := by
    omega
  exact Nat.le_trans htwo hbern

theorem bankRepairDigitTwoNBlockHalf
    (n : Nat) (hn : 1 ≤ n) :
    2 * (2 * n - 1) ^ (2 * n) ≤
      (2 * n) ^ (2 * n) :=
  bankRepairDigitGeometricBlockHalf (2 * n) (by omega)

/-- Elementary monotonicity in the POWER BASE by induction.
This avoids assuming an unverified Mathlib power helper. -/
private theorem bankRepairDigitNatPowBaseMono
    (a b : Nat) (hab : a ≤ b) :
    ∀ k : Nat, a ^ k ≤ b ^ k := by
  intro k
  induction k with
  | zero =>
      exact Nat.le_refl _
  | succ k ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      calc
        a ^ k * a ≤ b ^ k * a :=
          Nat.mul_le_mul_right a ih
        _ ≤ b ^ k * b := Nat.mul_le_mul_left _ hab

/-- The source ceiling logarithm satisfies A <= 2^ceilLogTwo A,
including the small exceptions A=0 and A=1. -/
theorem bankRepairDigitCeilLogTwoCovers
    (A : Nat) :
    A ≤ 2 ^ ceilLogTwo A := by
  by_cases hz : A = 0
  · subst A
    exact Nat.zero_le _
  · by_cases ho : A = 1
    · subst A
      exact Nat.le_refl _
    · have htwo : 2 ≤ A := by omega
      exact (ceilLogTwo_spec A htwo).2

/-- After b*ceilLogTwo A interactions, the integer geometric
tail envelope A*(b-1)^t is no larger than b^t.
Each b-block halves the envelope; at most a=ceilLogTwo A
blocks are required. -/
theorem bankRepairDigitGeometricAfterCut
    (b A : Nat) (hb : 2 ≤ b) :
    A * (b - 1) ^ (b * ceilLogTwo A) ≤
      b ^ (b * ceilLogTwo A) := by
  have hceil := bankRepairDigitCeilLogTwoCovers A
  have hhalf := bankRepairDigitGeometricBlockHalf b hb
  have hpow := bankRepairDigitNatPowBaseMono
    (2 * (b - 1) ^ b) (b ^ b) hhalf (ceilLogTwo A)
  have hleft :
      (2 * (b - 1) ^ b) ^ ceilLogTwo A =
        2 ^ ceilLogTwo A *
          (b - 1) ^ (b * ceilLogTwo A) := by
    rw [Nat.mul_pow, Nat.pow_mul]
  have hright :
      (b ^ b) ^ ceilLogTwo A =
        b ^ (b * ceilLogTwo A) := by
    rw [Nat.pow_mul]
  calc
    A * (b - 1) ^ (b * ceilLogTwo A) ≤
      2 ^ ceilLogTwo A * (b - 1) ^ (b * ceilLogTwo A) :=
        Nat.mul_le_mul_right _ hceil
    _ = (2 * (b - 1) ^ b) ^ ceilLogTwo A := hleft.symm
    _ ≤ (b ^ b) ^ ceilLogTwo A := hpow
    _ = b ^ (b * ceilLogTwo A) := hright

/-- Numerator of the simple b/(b-1) geometric tail. The
recurrence pays b*(b-1)^k at each additional time, with a
factor b applied to the previously accumulated cost. -/
def bankRepairDigitGeometricTail (b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      b * bankRepairDigitGeometricTail b k +
        b * (b - 1) ^ k

/-- An exact, subtraction-free telescoping identity. This is
the integer version of summing (1-1/b)^k over a finite horizon. -/
theorem bankRepairDigitGeometricTailIdentity
    (b : Nat) (hb : 1 ≤ b) :
    ∀ k,
      bankRepairDigitGeometricTail b k +
        b * (b - 1) ^ k = b ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
      simp [bankRepairDigitGeometricTail, Nat.pow_succ]
  | succ k ih =>
      have hbase : 1 + (b - 1) = b := by omega
      have hstep :
          bankRepairDigitGeometricTail b (k + 1) +
              b * (b - 1) ^ (k + 1) =
            b * (bankRepairDigitGeometricTail b k +
              b * (b - 1) ^ k) := by
        change b * bankRepairDigitGeometricTail b k +
            b * (b - 1) ^ k +
            b * ((b - 1) ^ k * (b - 1)) =
          b * (bankRepairDigitGeometricTail b k +
            b * (b - 1) ^ k)
        calc
          b * bankRepairDigitGeometricTail b k +
              b * (b - 1) ^ k +
              b * ((b - 1) ^ k * (b - 1)) =
            b * bankRepairDigitGeometricTail b k +
              b * (b - 1) ^ k * (1 + (b - 1)) := by
                rw [Nat.mul_add, Nat.mul_one]
                ac_rfl
          _ = b * bankRepairDigitGeometricTail b k +
                b * (b - 1) ^ k * b := by rw [hbase]
          _ = b * (bankRepairDigitGeometricTail b k +
                b * (b - 1) ^ k) := by
                rw [Nat.mul_add]
                ac_rfl
      calc
        bankRepairDigitGeometricTail b (k + 1) +
            b * (b - 1) ^ (k + 1) =
          b * (bankRepairDigitGeometricTail b k +
            b * (b - 1) ^ k) := hstep
        _ = b * b ^ (k + 1) := by rw [ih]
        _ = b ^ ((k + 1) + 1) := by
          rw [Nat.pow_succ b (k + 1)]
          ac_rfl

/-- A truncated natural analogue of the integral of
min(1, A*((b-1)/b)^t). Its recurrence is exactly the
unrolled finite sum of b^t and A*(b-1)^t at each time. -/
def bankRepairDigitGeometricMinCost
    (b A : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 =>
      b * bankRepairDigitGeometricMinCost b A t +
        b * min (b ^ t) (A * (b - 1) ^ t)

/-- Before the logarithmic cutoff, every truncated tail
term is bounded by the unconditioned probability one.
Thus the total cost through T steps is at most T*b^T. -/
theorem bankRepairDigitGeometricMinCostTrivial
    (b A : Nat) :
    ∀ T,
      bankRepairDigitGeometricMinCost b A T ≤ T * b ^ T := by
  intro T
  induction T with
  | zero =>
      exact Nat.le_refl _
  | succ T ih =>
      have hmin := Nat.min_le_left (b ^ T)
        (A * (b - 1) ^ T)
      calc
        bankRepairDigitGeometricMinCost b A (T + 1) =
          b * bankRepairDigitGeometricMinCost b A T +
            b * min (b ^ T) (A * (b - 1) ^ T) := rfl
        _ ≤ b * (T * b ^ T) + b * b ^ T :=
          Nat.add_le_add
            (Nat.mul_le_mul_left b ih)
            (Nat.mul_le_mul_left b hmin)
        _ = (T + 1) * b ^ (T + 1) := by
          rw [Nat.pow_succ, Nat.succ_mul]
          rw [Nat.mul_comm b (b ^ T)]
          rw [Nat.mul_left_comm b T (b ^ T), Nat.mul_comm b (b ^ T)]


/-- After a cutoff C satisfying A*(b-1)^C <= b^C, the
remaining geometric envelope is bounded by an exact
telescoping tail. This avoids Nat division entirely. -/
theorem bankRepairDigitGeometricMinCostAfterCut
    (b A C U : Nat)
    (hcut : A * (b - 1) ^ C ≤ b ^ C) :
    bankRepairDigitGeometricMinCost b A (C + U) ≤
      C * b ^ (C + U) +
        b ^ C * bankRepairDigitGeometricTail b U := by
  induction U with
  | zero =>
      simpa only [Nat.add_zero, bankRepairDigitGeometricTail, Nat.mul_zero] using
          bankRepairDigitGeometricMinCostTrivial b A C
  | succ U ih =>
      have hpow :
          A * (b - 1) ^ (C + U) ≤
            b ^ C * (b - 1) ^ U := by
        calc
          A * (b - 1) ^ (C + U) =
              (A * (b - 1) ^ C) * (b - 1) ^ U := by
                rw [Nat.pow_add]
                ac_rfl
          _ ≤ b ^ C * (b - 1) ^ U :=
            Nat.mul_le_mul_right ((b - 1) ^ U) hcut
      have hmin :
          min (b ^ (C + U))
                (A * (b - 1) ^ (C + U)) ≤
              b ^ C * (b - 1) ^ U :=
        Nat.le_trans (Nat.min_le_right _ _) hpow
      have hnext :
          C + (U + 1) = (C + U) + 1 := by omega
      calc
        bankRepairDigitGeometricMinCost b A (C + (U + 1)) =
          b * bankRepairDigitGeometricMinCost b A (C + U) +
            b * min (b ^ (C + U))
              (A * (b - 1) ^ (C + U)) := by
                rw [hnext]
                rfl
        _ ≤ b * (C * b ^ (C + U) +
              b ^ C * bankRepairDigitGeometricTail b U) +
            b * (b ^ C * (b - 1) ^ U) :=
          Nat.add_le_add
            (Nat.mul_le_mul_left b ih)
            (Nat.mul_le_mul_left b hmin)
        _ = C * b ^ (C + (U + 1)) +
              b ^ C * bankRepairDigitGeometricTail b (U + 1) := by
              rw [hnext, Nat.pow_succ]
              change
                b * (C * (b ^ (C + U)) +
                    b ^ C * bankRepairDigitGeometricTail b U) +
                  b * (b ^ C * (b - 1) ^ U) =
                C * (b ^ (C + U) * b) +
                  b ^ C * (b * bankRepairDigitGeometricTail b U +
                    b * (b - 1) ^ U)
              rw [Nat.mul_add, Nat.mul_add]
              ac_rfl

/-- Final geometric-tail cost bound with a NAT logarithmic cutoff:
G(T) <= b^T * b*(ceilLogTwo A + 2).
When b=2n this is the desired 2n(log_2 A+2) form. -/
theorem bankRepairDigitGeometricMinCostBound
    (b A : Nat) (hb : 2 ≤ b) :
    ∀ T,
      bankRepairDigitGeometricMinCost b A T ≤
        b ^ T * (b * (ceilLogTwo A + 2)) := by
  intro T
  have hcut := bankRepairDigitGeometricAfterCut b A hb
  by_cases hbefore : T ≤ b * ceilLogTwo A
  · have htrivial := bankRepairDigitGeometricMinCostTrivial b A T
    have hcoefficient :
        T ≤ b * (ceilLogTwo A + 2) := by
      have hmul := Nat.mul_le_mul_left b
        (by omega : ceilLogTwo A ≤ ceilLogTwo A + 2)
      omega
    calc
      bankRepairDigitGeometricMinCost b A T ≤ T * b ^ T :=
        htrivial
      _ ≤ (b * (ceilLogTwo A + 2)) * b ^ T :=
        Nat.mul_le_mul_right _ hcoefficient
      _ = b ^ T * (b * (ceilLogTwo A + 2)) := by ac_rfl
  · have hafter : b * ceilLogTwo A ≤ T := by omega
    obtain ⟨U, hU⟩ : ∃ U, T = b * ceilLogTwo A + U :=
      ⟨T - b * ceilLogTwo A, by omega⟩
    subst T
    have htailIdentity :=
      bankRepairDigitGeometricTailIdentity b (by omega : 1 ≤ b) U
    have htail : bankRepairDigitGeometricTail b U ≤
        b ^ (U + 1) := by omega
    have hstep := bankRepairDigitGeometricMinCostAfterCut
      b A (b * ceilLogTwo A) U hcut
    have hcoefficient :
        b * ceilLogTwo A + b ≤
          b * (ceilLogTwo A + 2) := by
      have hh := Nat.mul_le_mul_left b
        (by omega : ceilLogTwo A + 1 ≤ ceilLogTwo A + 2)
      have heq :
          b * ceilLogTwo A + b =
            b * (ceilLogTwo A + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    calc
      bankRepairDigitGeometricMinCost b A
          (b * ceilLogTwo A + U) ≤
        (b * ceilLogTwo A) *
            b ^ (b * ceilLogTwo A + U) +
          b ^ (b * ceilLogTwo A) *
            bankRepairDigitGeometricTail b U := hstep
      _ ≤ (b * ceilLogTwo A) *
            b ^ (b * ceilLogTwo A + U) +
          b ^ (b * ceilLogTwo A) * b ^ (U + 1) :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_left _ htail) _
      _ = (b * ceilLogTwo A + b) *
            b ^ (b * ceilLogTwo A + U) := by
        rw [Nat.pow_add, Nat.pow_succ, Nat.add_mul]
        ac_rfl
      _ ≤ (b * (ceilLogTwo A + 2)) *
            b ^ (b * ceilLogTwo A + U) :=
        Nat.mul_le_mul_right _ hcoefficient
      _ = b ^ (b * ceilLogTwo A + U) *
            (b * (ceilLogTwo A + 2)) := by ac_rfl

/-- The actual ratio for a uniform n-edge scheduler is
b=2n, r=2n-1. This is the complete Nat-only geometric
summation with a logarithmic, rather than linear, label count. -/
theorem bankRepairDigitGeometricTailCostOfTwoN
    (n A : Nat) (hn : 1 ≤ n) (T : Nat) :
    bankRepairDigitGeometricMinCost (2 * n) A T ≤
      (2 * n) ^ T * (2 * n * (ceilLogTwo A + 2)) := by
  exact bankRepairDigitGeometricMinCostBound
    (2 * n) A (by omega) T


/-- The recursively accumulated geometric min cost is exactly
the requested finite sum over t<T. This justifies using the
recurrence instead of division or rational coefficients. -/
theorem bankRepairDigitGeometricMinCostUnroll
    (b A : Nat) :
    ∀ T,
      bankRepairDigitGeometricMinCost b A T =
      ((List.range T).map (fun t =>
        min (b ^ t) (A * (b - 1) ^ t) * b ^ (T - t))).sum := by
  intro T
  induction T with
  | zero =>
      rfl
  | succ T ih =>
      have hmap :
          ((List.range T).map (fun t =>
            min (b ^ t) (A * (b - 1) ^ t) *
              b ^ (T + 1 - t))).sum =
            b * ((List.range T).map (fun t =>
              min (b ^ t) (A * (b - 1) ^ t) *
                b ^ (T - t))).sum := by
        have heq :
            (List.range T).map (fun t =>
              min (b ^ t) (A * (b - 1) ^ t) *
                b ^ (T + 1 - t)) =
              (List.range T).map (fun t =>
                b * (min (b ^ t) (A * (b - 1) ^ t) *
                  b ^ (T - t))) := by
          apply List.map_congr_left
          intro t ht
          have hlt : t < T := List.mem_range.mp ht
          have hexp : T + 1 - t = (T - t) + 1 := by omega
          rw [hexp, Nat.pow_succ]
          ac_rfl
        rw [heq]
        exact (bankRepairDigitScaleMappedListSum
          (List.range T)
          (fun t => min (b ^ t) (A * (b - 1) ^ t) *
            b ^ (T - t)) b).symm
      have hnew :
          ((List.range (T + 1)).map (fun t =>
            min (b ^ t) (A * (b - 1) ^ t) *
              b ^ ((T + 1) - t))).sum =
          ((List.range T).map (fun t =>
            min (b ^ t) (A * (b - 1) ^ t) *
              b ^ (T + 1 - t))).sum +
            b * min (b ^ T) (A * (b - 1) ^ T) := by
        rw [List.range_succ, List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Nat.add_zero]
        have hlast : T + 1 - T = 1 := by omega
        rw [hlast, Nat.pow_one]
        ac_rfl
      calc
        bankRepairDigitGeometricMinCost b A (T + 1) =
          b * bankRepairDigitGeometricMinCost b A T +
            b * min (b ^ T) (A * (b - 1) ^ T) := rfl
        _ = b * ((List.range T).map (fun t =>
              min (b ^ t) (A * (b - 1) ^ t) *
                b ^ (T - t))).sum +
            b * min (b ^ T) (A * (b - 1) ^ T) := by rw [ih]
        _ = ((List.range T).map (fun t =>
              min (b ^ t) (A * (b - 1) ^ t) *
                b ^ (T + 1 - t))).sum +
            b * min (b ^ T) (A * (b - 1) ^ T) := by
              rw [hmap]
        _ = ((List.range (T + 1)).map (fun t =>
              min (b ^ t) (A * (b - 1) ^ t) *
                b ^ ((T + 1) - t))).sum := hnew.symm

/-- A single Nat statement of the requested item (3):
the sum over 0<=t<T of
min(b^t, A*(b-1)^t) b^(T-t)
has coefficient b*(ceilLogTwo A+2). -/
theorem bankRepairDigitGeometricMinSumBound
    (b A : Nat) (hb : 2 ≤ b) (T : Nat) :
    ((List.range T).map (fun t =>
      min (b ^ t) (A * (b - 1) ^ t) * b ^ (T - t))).sum ≤
        b ^ T * (b * (ceilLogTwo A + 2)) := by
  rw [← bankRepairDigitGeometricMinCostUnroll]
  exact bankRepairDigitGeometricMinCostBound b A hb T

/-- Initial payload is at most n*2^L for n possible
inherited identities, even when some are initially absent. -/
theorem bankRepairDigitInitialLabelWeightCap
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hcert : ∀ site : Fin n,
      BankRepairDigitSingleInheritedLabelTasks ring hbank start site) :
    ((List.ofFn (fun site : Fin n => site)).map (fun site =>
      bankRepairDigitLivePowWeight
        (fun z : BankReferenceState ring hbank ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          bankRepairDigitInheritedLabelAlive site z.2.current)
        (Classical.choose (hcert site))
        (start, digitAuditInitial (piD start.val.1)))).sum ≤
      n * 2 ^ bankRepairDigitLeadingLength
        (ceilLogTwo (ceilLogTwo n)) := by
  classical
  have hcap : ∀ site : Fin n,
      bankRepairDigitLivePowWeight
        (fun z : BankReferenceState ring hbank ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          bankRepairDigitInheritedLabelAlive site z.2.current)
        (Classical.choose (hcert site))
        (start, digitAuditInitial (piD start.val.1)) ≤
        2 ^ bankRepairDigitLeadingLength
          (ceilLogTwo (ceilLogTwo n)) := by
    intro site
    have hs := (Classical.choose_spec (hcert site)).2.2
    by_cases ha : bankRepairDigitInheritedLabelAlive site
        (digitAuditInitial (piD start.val.1)).current
    · simp only [bankRepairDigitLivePowWeight, if_pos ha]
      exact Nat.pow_le_pow_right
        (by omega : 0 < (2 : Nat)) hs
    · simp [bankRepairDigitLivePowWeight, ha]
  have hsum := bankRepairDigitListMapSumBound
    (List.ofFn (fun site : Fin n => site))
    (fun site =>
      bankRepairDigitLivePowWeight
        (fun z : BankReferenceState ring hbank ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          bankRepairDigitInheritedLabelAlive site z.2.current)
        (Classical.choose (hcert site))
        (start, digitAuditInitial (piD start.val.1)))
    (2 ^ bankRepairDigitLeadingLength
      (ceilLogTwo (ceilLogTwo n)))
    (fun site _ => hcap site)
  simpa using hsum

/-- For EACH fixed R-fold entrance, the n possible OLD inherited
label identities share the same physical BANK edge word.
Their all-label ALIVE union has an exponentially decreasing tail
with initial factor n*2^L. This replaces the incorrect max<=sum
mean strategy without asserting the still-unproved local tasks. -/
theorem bankRepairDigitInheritedLabelUnionTailOfTasks
    {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hcert : ∀ site : Fin n,
      BankRepairDigitSingleInheritedLabelTasks ring hbank start site)
    (t : Nat) :
    2 ^ t *
      bankRepairDigitAliveWordCount
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun z : BankReferenceState ring hbank ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ∃ site : Fin n,
            bankRepairDigitInheritedLabelAlive site z.2.current)
        (start, digitAuditInitial (piD start.val.1)) t ≤
      (n * 2 ^ bankRepairDigitLeadingLength
        (ceilLogTwo (ceilLogTwo n))) *
        (2 * n - 1) ^ t := by
  classical
  have hstart :
      BankRepairDigitOneLabelReachableFrom ring hbank start
        (start, digitAuditInitial (piD start.val.1)) :=
    ⟨[], rfl⟩
  have htail := bankRepairDigitUnionTailOfLabelRanks
    (by omega : 1 ≤ n)
    (bankRepairDigitBoundaryAuditNext ring hbank)
    (List.ofFn (fun site : Fin n => site))
    (BankRepairDigitOneLabelReachableFrom ring hbank start)
    (fun site z =>
      bankRepairDigitInheritedLabelAlive site z.2.current)
    (fun site => Classical.choose (hcert site))
    (fun z e hz =>
      bankRepairDigitOneLabelReachableStep
        ring hbank start z e hz)
    (fun site z e hret =>
      bankRepairDigitInheritedLabelRetiredBankStep
        hn ring hbank site z e hret)
    (fun site z hz ha e =>
      (Classical.choose_spec (hcert site)).1 z hz
        (fun hno => hno ha) e)
    (fun site z hz ha =>
      (Classical.choose_spec (hcert site)).2.1 z hz
        (fun hno => hno ha))
    (start, digitAuditInitial (piD start.val.1)) hstart t
  have hcap := bankRepairDigitInitialLabelWeightCap
    ring hbank start hcert
  have hmul := Nat.mul_le_mul_left ((2 * n - 1) ^ t) hcap
  have hlist : ∀ z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n,
      (∃ site : Fin n,
        site ∈ List.ofFn (fun i : Fin n => i) ∧
        bankRepairDigitInheritedLabelAlive site z.2.current) ↔
      (∃ site : Fin n,
        bankRepairDigitInheritedLabelAlive site z.2.current) := by
    intro z
    constructor
    · intro h
      obtain ⟨site, _, ha⟩ := h
      exact ⟨site, ha⟩
    · intro h
      obtain ⟨site, ha⟩ := h
      exact ⟨site, List.mem_ofFn.mpr ⟨site, rfl⟩, ha⟩
  have hword :
      bankRepairDigitAliveWordCount
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun z : BankReferenceState ring hbank ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ∃ site, site ∈ List.ofFn
            (fun i : Fin n => i) ∧
            bankRepairDigitInheritedLabelAlive site z.2.current)
        (start, digitAuditInitial (piD start.val.1)) t =
      bankRepairDigitAliveWordCount
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun z : BankReferenceState ring hbank ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ∃ site : Fin n,
            bankRepairDigitInheritedLabelAlive site z.2.current)
        (start, digitAuditInitial (piD start.val.1)) t := by
    exact congrArg
      (fun P =>
        bankRepairDigitAliveWordCount
          (bankRepairDigitBoundaryAuditNext ring hbank) P
          (start, digitAuditInitial (piD start.val.1)) t)
      (funext (fun z =>
        propext (hlist z)))
  rw [hword] at htail
  exact Nat.le_trans htail (by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hmul)


/-! ## From weighted word tails to finite-horizon costNumerator -/

/-- Uniform finite-edge scheduler survival never exceeds the
number n^t of all words of length t. This is independent
of the protocol row and requires no absorbing-target premise. -/
theorem bankRepairDigitSurvivalCountCap
    {State : Type} {n : Nat}
    (next : State → Fin n → State)
    (target : State → Prop) (z : State) :
    ∀ t,
      survivalNumerator next target z t ≤ n ^ t := by
  classical
  intro t
  induction t with
  | zero =>
      by_cases hz : target z
      · rw [UniformFirstHit.survivalNumerator_of_target
          next target z hz 0]
        exact Nat.zero_le _
      · rw [UniformFirstHit.survivalNumerator_zero_of_not
          next target z hz]
        exact Nat.le_refl _
  | succ t ih =>
      have hs := UniformFirstHit.survivalNumerator_succ_le
        next target z t
      calc
        survivalNumerator next target z (t + 1) ≤
          n * survivalNumerator next target z t := hs
        _ ≤ n * n ^ t := Nat.mul_le_mul_left n ih
        _ = n ^ (t + 1) := by
          rw [Nat.pow_succ]
          ac_rfl

/-- For a forward-closed terminal event, reaching it at an
earlier prefix is the same as being terminal at the end.
Hence survivalNumerator equals the actual number of final
nonterminal words. -/
theorem bankRepairDigitSurvivalEqualsAliveWordCount
    {State : Type} {n : Nat}
    (next : State → Fin n → State)
    (terminal : State → Prop)
    (hclosed : ∀ z e, terminal z → terminal (next z e)) :
    ∀ z t,
      survivalNumerator next terminal z t =
        bankRepairDigitAliveWordCount next
          (fun y => ¬ terminal y) z t := by
  classical
  intro z t
  induction t generalizing z with
  | zero =>
      by_cases hz : terminal z
      · rw [UniformFirstHit.survivalNumerator_of_target
          next terminal z hz 0]
        simp [bankRepairDigitAliveWordCount, hz]
      · rw [UniformFirstHit.survivalNumerator_zero_of_not
          next terminal z hz]
        simp [bankRepairDigitAliveWordCount, hz]
  | succ t ih =>
      by_cases hz : terminal z
      · rw [UniformFirstHit.survivalNumerator_of_target
          next terminal z hz (t + 1)]
        change 0 =
          (List.ofFn (fun e : Fin n =>
            bankRepairDigitAliveWordCount next
              (fun y => ¬ terminal y) (next z e) t)).sum
        have hsum := ofFn_sum_eq
          (fun e : Fin n =>
            bankRepairDigitAliveWordCount next
              (fun y => ¬ terminal y) (next z e) t)
          (fun _ : Fin n => 0)
          (by
            intro e
            rw [← ih (next z e)]
            exact UniformFirstHit.survivalNumerator_of_target
              next terminal (next z e) (hclosed z e hz) t)
        rw [hsum, ofFn_sum_const, Nat.mul_zero]
      · rw [UniformFirstHit.survivalNumerator_succ_of_not
          next terminal z hz t]
        change
          (List.ofFn (fun e : Fin n =>
            survivalNumerator next terminal (next z e) t)).sum =
          (List.ofFn (fun e : Fin n =>
            bankRepairDigitAliveWordCount next
              (fun y => ¬ terminal y) (next z e) t)).sum
        exact ofFn_sum_eq _ _ (fun e => ih (next z e))

/-- Any terminal target whose scaled survival count satisfies
2^t*F(t) <= A*(2n-1)^t inherits the Nat geometric-min cost.
The induction uses exactly the first-hit cost
recurrence; there is no probabilistic independence assumption. -/
theorem bankRepairDigitCostFromGeometricTail
    {State : Type} {n : Nat}
    (hn : 1 ≤ n)
    (next : State → Fin n → State)
    (terminal : State → Prop)
    (z : State) (A : Nat)
    (htail : ∀ t,
      2 ^ t * survivalNumerator next terminal z t ≤
        A * (2 * n - 1) ^ t) :
    ∀ T,
      costNumerator next terminal z T ≤
        n ^ T * (2 * n * (ceilLogTwo A + 2)) := by
  have hscaled : ∀ T,
      2 ^ T * costNumerator next terminal z T ≤
        bankRepairDigitGeometricMinCost (2 * n) A T := by
    intro T
    induction T with
    | zero =>
        rw [costNumerator_zero]
        simp [bankRepairDigitGeometricMinCost]
    | succ T ih =>
        have hcount := bankRepairDigitSurvivalCountCap
          next terminal z T
        have hpow :
            2 ^ T * survivalNumerator next terminal z T ≤
              (2 * n) ^ T := by
          calc
            2 ^ T * survivalNumerator next terminal z T ≤
              2 ^ T * n ^ T :=
              Nat.mul_le_mul_left (2 ^ T) hcount
            _ = (2 * n) ^ T := (Nat.mul_pow 2 n T).symm
        have hmin :
            2 ^ T * survivalNumerator next terminal z T ≤
              min ((2 * n) ^ T)
                (A * (2 * n - 1) ^ T) :=
          Nat.le_min.mpr ⟨hpow, htail T⟩
        calc
          2 ^ (T + 1) *
              costNumerator next terminal z (T + 1) =
            (2 * n) *
              (2 ^ T * costNumerator next terminal z T +
                2 ^ T * survivalNumerator next terminal z T) := by
                  rw [UniformFirstHit.costNumerator_succ_eq,
                    Nat.pow_succ, Nat.mul_add]
                  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
                    Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
                    Nat.add_comm, Nat.add_left_comm]
          _ ≤ (2 * n) *
              (bankRepairDigitGeometricMinCost (2 * n) A T +
                min ((2 * n) ^ T)
                  (A * (2 * n - 1) ^ T)) :=
              Nat.mul_le_mul_left _
                (Nat.add_le_add ih hmin)
          _ = bankRepairDigitGeometricMinCost
              (2 * n) A (T + 1) := by
                change
                  (2 * n) *
                    (bankRepairDigitGeometricMinCost (2 * n) A T +
                      min ((2 * n) ^ T)
                        (A * (2 * n - 1) ^ T)) =
                  (2 * n) * bankRepairDigitGeometricMinCost
                      (2 * n) A T +
                    (2 * n) * min ((2 * n) ^ T)
                      (A * (2 * n - 1) ^ T)
                rw [Nat.mul_add]
  intro T
  have hbound := Nat.le_trans (hscaled T)
    (bankRepairDigitGeometricTailCostOfTwoN n A hn T)
  have heq :
      (2 * n) ^ T * (2 * n * (ceilLogTwo A + 2)) =
        2 ^ T *
          (n ^ T * (2 * n * (ceilLogTwo A + 2))) := by
    rw [Nat.mul_pow]
    ac_rfl
  rw [heq] at hbound
  by_cases hle :
      costNumerator next terminal z T ≤
        n ^ T * (2 * n * (ceilLogTwo A + 2))
  · exact hle
  · have hlt :
        n ^ T * (2 * n * (ceilLogTwo A + 2)) <
          costNumerator next terminal z T := by omega
    have hpositive : 0 < 2 ^ T :=
      Nat.pow_pos (by omega : 0 < (2 : Nat))
    have hcontr := Nat.mul_lt_mul_of_pos_left hlt hpositive
    omega


/-! ## Physical same-BANK first hit for inherited-base extinction -/

/-- A target on the paired process: every inherited ORIGINAL
base identity is gone. Root-launched labels do not count. This
is not silently identified with the stronger boundary cut,
which additionally requires leading/final packet authority inert. -/
def bankRepairDigitAllBaseLabelsGone
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ¬ ∃ site : Fin n,
    bankRepairDigitInheritedLabelAlive site z.2.current

theorem bankRepairDigitAllBaseLabelsGoneClosed
    {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hz : bankRepairDigitAllBaseLabelsGone ring hbank z) :
    bankRepairDigitAllBaseLabelsGone ring hbank
      (bankRepairDigitBoundaryAuditNext ring hbank z e) := by
  intro hnew
  obtain ⟨site, halive⟩ := hnew
  have hret : bankRepairDigitInheritedLabelRetired site z.2.current := by
    intro hold
    exact hz ⟨site, hold⟩
  exact (bankRepairDigitInheritedLabelRetiredBankStep
    hn ring hbank site z e hret) halive

/-- The geometric union bound is the exact survival numerator
of the first hit of all inherited labels retired, because
individual retirement is absorbing on the actual edge tape. -/
theorem bankRepairDigitAllBaseSurvivalTailOfTasks
    {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hcert : ∀ site : Fin n,
      BankRepairDigitSingleInheritedLabelTasks ring hbank start site)
    (t : Nat) :
    2 ^ t * survivalNumerator
      (bankRepairDigitBoundaryAuditNext ring hbank)
      (bankRepairDigitAllBaseLabelsGone ring hbank)
      (start, digitAuditInitial (piD start.val.1)) t ≤
      (n * 2 ^ bankRepairDigitLeadingLength
        (ceilLogTwo (ceilLogTwo n))) *
        (2 * n - 1) ^ t := by
  have hsurv := bankRepairDigitSurvivalEqualsAliveWordCount
    (bankRepairDigitBoundaryAuditNext ring hbank)
    (bankRepairDigitAllBaseLabelsGone ring hbank)
    (fun z e hz =>
      bankRepairDigitAllBaseLabelsGoneClosed hn ring hbank z e hz)
    (start, digitAuditInitial (piD start.val.1)) t
  have heq :
      (fun z : BankReferenceState ring hbank ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ¬ bankRepairDigitAllBaseLabelsGone ring hbank z) =
        (fun z : BankReferenceState ring hbank ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ∃ site : Fin n,
            bankRepairDigitInheritedLabelAlive site z.2.current) := by
    classical
    funext z
    apply propext
    simp [bankRepairDigitAllBaseLabelsGone]
  rw [heq] at hsurv
  rw [hsurv]
  exact bankRepairDigitInheritedLabelUnionTailOfTasks
    hn ring hbank start hcert t

/-- A finite positive power has the expected ceiling logarithm.
The proof uses the existing source ceilLogTwo_unique theorem. -/
theorem bankRepairDigitCeilLogTwoPower
    (k : Nat) (hk : 1 ≤ k) :
    ceilLogTwo (2 ^ k) = k := by
  have hpos : 0 < 2 ^ (k - 1) :=
    Nat.pow_pos (by omega : 0 < (2 : Nat))
  have hstep : 2 ^ k = 2 ^ (k - 1) * 2 := by
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (k - 1) * 2 :=
        Nat.pow_succ 2 (k - 1)
  have hlt : 2 ^ (k - 1) < 2 ^ k := by
    rw [hstep]
    omega
  exact ceilLogTwo_unique k (2 ^ k) hk hlt (Nat.le_refl _)

/-- Inflating A=n*2^L to a PURE power of two prevents any
nonlinear/logarithm conversion: ceilLogTwo A is exactly q+L.
This only makes the geometric-tail upper bound weaker, safely. -/
theorem bankRepairDigitLabelTailPowerEnvelope
    (n L : Nat) :
    n * 2 ^ L ≤ 2 ^ (ceilLogTwo n + L) := by
  have hn := bankRepairDigitCeilLogTwoCovers n
  calc
    n * 2 ^ L ≤ 2 ^ ceilLogTwo n * 2 ^ L :=
      Nat.mul_le_mul_right _ hn
    _ = 2 ^ (ceilLogTwo n + L) := (Nat.pow_add 2 (ceilLogTwo n) L).symm

/-- First-hit bound for the TRUE coupled BANK/audit process,
assuming only the n local inherited-label task certificates.
The bound is logarithmic in n and L_s, NOT n^2*L_s. -/
theorem bankRepairDigitAllBaseCostLogarithmicOfTasks
    {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hcert : ∀ site : Fin n,
      BankRepairDigitSingleInheritedLabelTasks ring hbank start site) :
    ∀ T,
      costNumerator
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (bankRepairDigitAllBaseLabelsGone ring hbank)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      n ^ T * (2 * n * (ceilLogTwo n +
        bankRepairDigitLeadingLength
          (ceilLogTwo (ceilLogTwo n)) + 2)) := by
  have hqpos : 1 ≤ ceilLogTwo n := by
    have hq := ceilLogTwo_eq n hn
    omega
  have hpositive :
      1 ≤ ceilLogTwo n + bankRepairDigitLeadingLength
        (ceilLogTwo (ceilLogTwo n)) := by omega
  have hpow := bankRepairDigitCeilLogTwoPower
    (ceilLogTwo n + bankRepairDigitLeadingLength
      (ceilLogTwo (ceilLogTwo n))) hpositive
  have hA := bankRepairDigitLabelTailPowerEnvelope n
    (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)))
  have htail : ∀ t,
      2 ^ t * survivalNumerator
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (bankRepairDigitAllBaseLabelsGone ring hbank)
        (start, digitAuditInitial (piD start.val.1)) t ≤
      2 ^ (ceilLogTwo n + bankRepairDigitLeadingLength
        (ceilLogTwo (ceilLogTwo n))) *
        (2 * n - 1) ^ t := by
    intro t
    have hs := bankRepairDigitAllBaseSurvivalTailOfTasks
      hn ring hbank start hcert t
    exact Nat.le_trans hs
      (Nat.mul_le_mul_right ((2 * n - 1) ^ t) hA)
  intro T
  have hcost := bankRepairDigitCostFromGeometricTail
    (by omega : 1 ≤ n)
    (bankRepairDigitBoundaryAuditNext ring hbank)
    (bankRepairDigitAllBaseLabelsGone ring hbank)
    (start, digitAuditInitial (piD start.val.1))
    (2 ^ (ceilLogTwo n + bankRepairDigitLeadingLength
      (ceilLogTwo (ceilLogTwo n))))
    htail T
  rw [hpow] at hcost
  exact hcost


/-! ## The new logarithmic coefficient versus the original boundary -/

/-- The physical BANK band implies
q=ceilLogTwo n <= 2^s = 2*bankRepairDigitExponent s.
The J_s term then pays the additional factor needed to
compare 2*(q+L_s+2) with the existing boundary numerator. -/
theorem bankRepairDigitBoundaryUpperPaysBaseLog
    {n : Nat}
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 * (ceilLogTwo n +
      bankRepairDigitLeadingLength
        (ceilLogTwo (ceilLogTwo n)) + 2) ≤
      bankRepairDigitBoundaryUpper
        (ceilLogTwo (ceilLogTwo n)) := by
  have hs : 7 ≤ ceilLogTwo (ceilLogTwo n) :=
    bankRepairDigitWidthBank hbank
  have hq80 : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have hq2 : 2 ≤ ceilLogTwo n := by omega
  have hq :
      ceilLogTwo n ≤
        2 ^ ceilLogTwo (ceilLogTwo n) :=
    (ceilLogTwo_spec (ceilLogTwo n) hq2).2
  have hpower :
      2 ^ ceilLogTwo (ceilLogTwo n) =
        2 * bankRepairDigitExponent
          (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitExponent
    calc
      2 ^ ceilLogTwo (ceilLogTwo n) =
          2 ^ ((ceilLogTwo (ceilLogTwo n) - 1) + 1) := by
            congr 1
            omega
      _ = 2 ^ (ceilLogTwo (ceilLogTwo n) - 1) * 2 :=
        Nat.pow_succ 2 (ceilLogTwo (ceilLogTwo n) - 1)
      _ = 2 * 2 ^ (ceilLogTwo (ceilLogTwo n) - 1) := by
        ac_rfl
  have hepos :
      0 < bankRepairDigitExponent
        (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitExponent
    exact Nat.pow_pos (by omega : 0 < (2 : Nat))
  have hradius :
      bankRepairDigitExponent
          (ceilLogTwo (ceilLogTwo n)) ≤
        bankRepairDigitRadius
          (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitRadius
    rw [hpower]
    omega
  have hservice :
      bankRepairDigitRadius
          (ceilLogTwo (ceilLogTwo n)) ≤
        bankRepairDigitBoundaryServices
          (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitBoundaryServices
    omega
  have hbudget :
      2 * (bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) +
        bankRepairDigitLeadingLength
          (ceilLogTwo (ceilLogTwo n)) + 3) +
        2 * bankRepairDigitBoundaryServices
          (ceilLogTwo (ceilLogTwo n)) ≤
      bankRepairDigitBoundaryUpper
          (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitBoundaryUpper
    omega
  rw [hpower] at hq
  omega

/-- The exponential-tail cost of retiring ALL inherited-base
identities fits the exact boundary micro-charge.
This is the requested numerical comparison, conditional only on
the local one-label task ranks. It does not claim that the stronger
leading/final-fragment boundary cut has been reached. -/
theorem bankRepairDigitAllBaseFitsBoundaryMicroOfTasks
    {n : Nat}
    (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hcert : ∀ site : Fin n,
      BankRepairDigitSingleInheritedLabelTasks ring hbank start site) :
    ∀ T,
      2 * costNumerator
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (bankRepairDigitAllBaseLabelsGone ring hbank)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      n ^ T * bankRepairDigitBoundaryMicroCharge n := by
  have hnumeric := bankRepairDigitBoundaryUpperPaysBaseLog hn hbank
  have hcap :
      2 * n * (ceilLogTwo n +
          bankRepairDigitLeadingLength
            (ceilLogTwo (ceilLogTwo n)) + 2) ≤
        bankRepairDigitBoundaryUpper
          (ceilLogTwo (ceilLogTwo n)) * n := by
    have hh := Nat.mul_le_mul_right n hnumeric
    simpa only [Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hh
  have hcost := bankRepairDigitAllBaseCostLogarithmicOfTasks
    (by omega : 2 ≤ n) ring hbank start hcert
  intro T
  calc
    2 * costNumerator
        (bankRepairDigitBoundaryAuditNext ring hbank)
        (bankRepairDigitAllBaseLabelsGone ring hbank)
        (start, digitAuditInitial (piD start.val.1)) T ≤
      2 * (n ^ T *
        (2 * n * (ceilLogTwo n +
          bankRepairDigitLeadingLength
            (ceilLogTwo (ceilLogTwo n)) + 2))) :=
        Nat.mul_le_mul_left 2 (hcost T)
    _ ≤ 2 * (n ^ T *
        (bankRepairDigitBoundaryUpper
          (ceilLogTwo (ceilLogTwo n)) * n)) :=
        Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left (n ^ T) hcap)
    _ = n ^ T * bankRepairDigitBoundaryMicroCharge n := by
      unfold bankRepairDigitBoundaryMicroCharge
      ac_rfl

/-- Full remaining *structural* scope, rather than another
global task potential: the existing boundaryRetired target
also checks physical leading/final packet authority.
Base-label extinction alone proves none of those packet rows.
The terminal inclusion has to be supplied by those independent
causal-cover proofs before a physical BoundaryInheritedMicroClock
can follow from the strong paired first-hit result above. -/
def BankRepairDigitBaseExtinctionImpliesFullBoundary
    {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (start : BankReferenceState ring hbank)
    (word : List (Fin n)),
    BankRepairRFoldEstablished ring hbank start →
    bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))) →
    BankRepairDigitBoundaryRetiredCut ring hbank
      (word.foldl (bankRepairNext ring hbank) start)

end L3.RenewalReferenceClock

/-!
## Inherited-label retirement under explicit leading geometry

The R-fold entrance `BankRepairRFoldEstablished` alone does not fix
the spacing of delimiters ahead of the inherited base record, nor
freeze the beta bits along the audit prefix.  The proposition
`BankRepairDigitLabelLeadingGeometry` states exactly that extra
leading geometry; under it the single inherited label retires within
`L_t` services of its host.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Walk `k` services to the right. -/
def bankRepairDigitRightWalk {n : Nat} (ring : DirectedRing n) :
    Nat → Fin n → Fin n
  | 0, i => i
  | k + 1, i => bankRepairDigitRightWalk ring k (ring.rightNeighbor i)

/-- SEEK flag of a physical base record. -/
def bankRepairDigitBaseSeek : WBase → Bool
  | .SEEK => true
  | _ => false

/-- Remaining services of one base label (fuel-bounded). -/
def bankRepairDigitLabelCost {n : Nat} (ring : DirectedRing n)
    (root beta : Fin n → Bool) : Nat → Fin n → Bool → Nat
  | 0, _, _ => 0
  | f + 1, i, seek =>
      if root i = true then 1
      else if root (ring.rightNeighbor i) = true then 1
      else if seek = true then
        1 + bankRepairDigitLabelCost ring root beta f
          (ring.rightNeighbor i) (!beta (ring.rightNeighbor i))
      else if beta (ring.rightNeighbor i) = true then 1
      else 1 + bankRepairDigitLabelCost ring root beta f
          (ring.rightNeighbor i) false

theorem bankRepairDigitLabelCostSucc {n : Nat}
    (ring : DirectedRing n) (root beta : Fin n → Bool)
    (g : Nat) (i : Fin n) (s : Bool) :
    bankRepairDigitLabelCost ring root beta (g + 1) i s =
      if root i = true then 1
      else if root (ring.rightNeighbor i) = true then 1
      else if s = true then
        1 + bankRepairDigitLabelCost ring root beta g
          (ring.rightNeighbor i) (!beta (ring.rightNeighbor i))
      else if beta (ring.rightNeighbor i) = true then 1
      else 1 + bankRepairDigitLabelCost ring root beta g
          (ring.rightNeighbor i) false := rfl

theorem bankRepairDigitLabelCostSaturate {n : Nat}
    (ring : DirectedRing n) (root beta : Fin n → Bool) :
    ∀ f i s,
      bankRepairDigitLabelCost ring root beta f i s < f →
      bankRepairDigitLabelCost ring root beta (f + 1) i s =
        bankRepairDigitLabelCost ring root beta f i s := by
  intro f
  induction f with
  | zero => intro i s h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
      intro i s h
      rw [bankRepairDigitLabelCostSucc ring root beta (f + 1) i s,
        bankRepairDigitLabelCostSucc ring root beta f i s]
      rw [bankRepairDigitLabelCostSucc ring root beta f i s] at h
      by_cases h1 : root i = true
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        rw [if_neg h1] at h
        by_cases h2 : root (ring.rightNeighbor i) = true
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h2]
          rw [if_neg h2] at h
          by_cases h3 : s = true
          · rw [if_pos h3, if_pos h3]
            rw [if_pos h3] at h
            rw [ih _ _ (by omega)]
          · rw [if_neg h3, if_neg h3]
            rw [if_neg h3] at h
            by_cases h4 : beta (ring.rightNeighbor i) = true
            · rw [if_pos h4, if_pos h4]
            · rw [if_neg h4, if_neg h4]
              rw [if_neg h4] at h
              rw [ih _ _ (by omega)]

/-- A stop `k` services ahead: a root, or a delimiter after
an earlier delimiter (or any delimiter in ZERO mode). -/
def bankRepairDigitLabelStop {n : Nat} (ring : DirectedRing n)
    (root beta : Fin n → Bool) (i : Fin n) (seek : Bool) (k : Nat) : Prop :=
  root (bankRepairDigitRightWalk ring k i) = true ∨
    (beta (bankRepairDigitRightWalk ring k i) = true ∧
      (seek = false ∨ ∃ k', 1 ≤ k' ∧ k' < k ∧
        beta (bankRepairDigitRightWalk ring k' i) = true))

theorem bankRepairDigitLabelCostOfStop {n : Nat}
    (ring : DirectedRing n) (root beta : Fin n → Bool) :
    ∀ k f i s, 1 ≤ k → k + 1 ≤ f →
      bankRepairDigitLabelStop ring root beta i s k →
      bankRepairDigitLabelCost ring root beta f i s ≤ k := by
  intro k
  induction k with
  | zero => intro f i s h; omega
  | succ k ih =>
      intro f i s _ hf hstop
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [bankRepairDigitLabelCostSucc]
      by_cases h1 : root i = true
      · rw [if_pos h1]; omega
      · rw [if_neg h1]
        by_cases h2 : root (ring.rightNeighbor i) = true
        · rw [if_pos h2]; omega
        · rw [if_neg h2]
          cases k with
          | zero =>
              unfold bankRepairDigitLabelStop at hstop
              simp only [bankRepairDigitRightWalk] at hstop
              rcases hstop with hr | ⟨hb, hs | ⟨k', hk1, hk2, _⟩⟩
              · exact absurd hr h2
              · subst hs
                rw [if_neg (by simp), if_pos hb]
                omega
              · omega
          | succ k =>
              have hj : ∀ m, bankRepairDigitRightWalk ring (m + 1) i =
                  bankRepairDigitRightWalk ring m (ring.rightNeighbor i) :=
                fun m => rfl
              unfold bankRepairDigitLabelStop at hstop
              rw [hj] at hstop
              by_cases h3 : s = true
              · rw [if_pos h3]
                have hnext : bankRepairDigitLabelStop ring root beta
                    (ring.rightNeighbor i) (!beta (ring.rightNeighbor i))
                    (k + 1) := by
                  unfold bankRepairDigitLabelStop
                  rcases hstop with hr | ⟨hb, hs | ⟨k', hk1, hk2, hk'⟩⟩
                  · exact Or.inl hr
                  · exact absurd hs (by simp [h3])
                  · refine Or.inr ⟨hb, ?_⟩
                    by_cases hk : k' = 1
                    · subst hk
                      left
                      simp only [bankRepairDigitRightWalk] at hk'
                      simp [hk']
                    · right
                      obtain ⟨m, rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by omega⟩
                      exact ⟨m, by omega, by omega, by rw [← hj]; exact hk'⟩
                have := ih g (ring.rightNeighbor i) _ (by omega) (by omega) hnext
                omega
              · rw [if_neg h3]
                have hs : s = false := by simpa using h3
                by_cases h4 : beta (ring.rightNeighbor i) = true
                · rw [if_pos h4]; omega
                · rw [if_neg h4]
                  have hnext : bankRepairDigitLabelStop ring root beta
                      (ring.rightNeighbor i) false (k + 1) := by
                    unfold bankRepairDigitLabelStop
                    rcases hstop with hr | ⟨hb, _⟩
                    · exact Or.inl hr
                    · exact Or.inr ⟨hb, Or.inl rfl⟩
                  have := ih g (ring.rightNeighbor i) _ (by omega) (by omega) hnext
                  omega

theorem bankRepairDigitLiveTopWBaseY (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) :
    (liveTopPair c ox oy bx bY).y.wBase =
      (if oy.l then ((.NONE : WBase), oy.wBase, (none : Option (Fin c.topA)))
       else if ox.l && !oy.l then
         (.NONE, (if oy.wBase == .NONE then .SEEK else oy.wBase), none)
       else if !ox.l && ox.wBase == .ZERO then
         (.NONE, (if !oy.l && !bY && oy.wBase == .NONE then .ZERO else oy.wBase),
          some c.zeroDigit)
       else if !ox.l && ox.wBase == .SEEK then
         (.NONE, (if !oy.l && oy.wBase == .NONE then
            (if bY then .ZERO else .SEEK) else oy.wBase), none)
       else (ox.wBase, oy.wBase, none)).2.1 := rfl

theorem bankRepairDigitReplayHostX {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : ProjD c) (betaY : Bool)
    (gx gy : Option (DigitBaseOrigin n))
    (hx : x.top.wBase ≠ .NONE) :
    (digitBaseReplay time source destination x y betaY gx gy).x =
      none := by
  unfold digitBaseReplay
  cases hrx : x.word.native.l <;> cases hry : y.word.native.l <;>
    cases hw : x.top.wBase <;> simp_all

theorem bankRepairDigitReplayStayY {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : ProjD c) (betaY : Bool)
    (gx gy : Option (DigitBaseOrigin n))
    (hy : y.top.wBase ≠ .NONE) :
    (digitBaseReplay time source destination x y betaY gx gy).y =
      gy := by
  unfold digitBaseReplay
  cases hrx : x.word.native.l <;> cases hry : y.word.native.l <;>
    cases hw : x.top.wBase <;> cases hwy : y.top.wBase <;> simp_all

theorem bankRepairDigitLiveTopStayY {c : Compiled} (x y : ProjD c)
    (bx bY : Bool) (hy : y.top.wBase ≠ .NONE) :
    (liveTopPair c x.lift y.lift bx bY).y.wBase = y.top.wBase := by
  rw [bankRepairDigitLiveTopWBaseY]
  have hl : ∀ a : ProjD c, a.lift.l = a.word.native.l := fun _ => rfl
  have hw : ∀ a : ProjD c, a.lift.wBase = a.top.wBase := fun _ => rfl
  simp only [hl, hw]
  cases hrx : x.word.native.l <;> cases hry : y.word.native.l <;>
    cases hwx : x.top.wBase <;> cases hwy : y.top.wBase <;>
    cases bY <;> simp_all

theorem bankRepairDigitReplayMoveY {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : ProjD c) (bx betaY : Bool)
    (gx gy : Option (DigitBaseOrigin n))
    (hne : gy ≠ gx) (hgx : ∃ s, gx = some (.inherited s))
    (hmove : (digitBaseReplay time source destination x y betaY gx gy).y =
      gx) :
    x.word.native.l = false ∧ y.word.native.l = false ∧
      ((x.top.wBase = .SEEK ∧
          (liveTopPair c x.lift y.lift bx betaY).y.wBase =
            (if betaY then .ZERO else .SEEK)) ∨
        (x.top.wBase = .ZERO ∧ betaY = false ∧
          (liveTopPair c x.lift y.lift bx betaY).y.wBase = .ZERO)) := by
  rw [bankRepairDigitLiveTopWBaseY]
  have hl : ∀ a : ProjD c, a.lift.l = a.word.native.l := fun _ => rfl
  have hw : ∀ a : ProjD c, a.lift.wBase = a.top.wBase := fun _ => rfl
  simp only [hl, hw]
  obtain ⟨s, rfl⟩ := hgx
  unfold digitBaseReplay at hmove
  cases hrx : x.word.native.l <;> cases hry : y.word.native.l <;>
    cases hwx : x.top.wBase <;> cases hwy : y.top.wBase <;>
    cases betaY <;> simp_all

theorem bankRepairDigitLabelCostPos {n : Nat}
    (ring : DirectedRing n) (root beta : Fin n → Bool)
    (f : Nat) (i : Fin n) (s : Bool) :
    1 ≤ bankRepairDigitLabelCost ring root beta (f + 1) i s := by
  rw [bankRepairDigitLabelCostSucc]
  repeat' split
  all_goals omega

/-- Where the single inherited label sits after one service:
the host serves forward, every other row leaves it in place. -/
theorem bankRepairDigitLabelServiceHost {c : Compiled} {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (time : Nat) (e site h : Fin n)
    (hwh : (S h).top.wBase ≠ .NONE)
    (huniq : ∀ i, (G i).base = some (.inherited site) → i = h)
    (i : Fin n)
    (hi : (digitGhostStep ring S G time e i).base =
      some (.inherited site)) :
    i = (if e = h then ring.rightNeighbor e else h) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  by_cases hie : i = e
  · subst i
    have hx :
        (digitBaseReplay time e (ring.rightNeighbor e)
          (S e) (S (ring.rightNeighbor e))
          (workerW (S e).word
            (S (ring.rightNeighbor e)).word).betaY
          (G e).base (G (ring.rightNeighbor e)).base).x =
          some (.inherited site) := by
      simpa [digitGhostStep, digitService] using hi
    rcases bankRepairDigitBaseReplayXChoice time e
        (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
        (workerW (S e).word
          (S (ring.rightNeighbor e)).word).betaY
        (G e).base (G (ring.rightNeighbor e)).base with hnone | hold
    · rw [hnone] at hx
      cases hx
    · have hih : e = h := huniq e (hold.symm.trans hx)
      subst h
      rw [bankRepairDigitReplayHostX time e (ring.rightNeighbor e)
        (S e) (S (ring.rightNeighbor e)) _ _ _ hwh] at hx
      cases hx
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      have hy :
          (digitBaseReplay time e (ring.rightNeighbor e)
            (S e) (S (ring.rightNeighbor e))
            (workerW (S e).word
              (S (ring.rightNeighbor e)).word).betaY
            (G e).base (G (ring.rightNeighbor e)).base).y =
            some (.inherited site) := by
        simpa [digitGhostStep, digitService, hne] using hi
      rcases bankRepairDigitBaseReplayYChoice time e
          (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
          (workerW (S e).word
            (S (ring.rightNeighbor e)).word).betaY
          (G e).base (G (ring.rightNeighbor e)).base with
        hY | hX | hNew
      · have hjh := huniq _ (hY.symm.trans hy)
        by_cases heh : e = h
        · rw [if_pos heh]
        · rw [if_neg heh]
          exact hjh
      · have heh := huniq _ (hX.symm.trans hy)
        rw [if_pos heh]
      · have hbad :
            (some (.rootLaunch time e (ring.rightNeighbor e)) :
              Option (DigitBaseOrigin n)) =
              some (.inherited site) := hNew.symm.trans hy
        cases hbad
    · have hframe :=
        bankRepairDigitInheritedAuditAwayFrame
          ring S G time e i hie hij
      have hih : i = h := huniq i (hframe.symm.trans hi)
      have heh : ¬ e = h := fun h' => hie (hih.trans h'.symm)
      rw [if_neg heh]
      exact hih

/-- One service of the single inherited label: its physical
record stays live, and its remaining cost does not grow; it drops
by one exactly when the host edge serves. -/
theorem bankRepairDigitLabelServiceCost {c : Compiled} {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (R B : Fin n → Bool) (L : Nat)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (time : Nat) (e site h : Fin n)
    (hR : ∀ i, (S i).word.native.l = R i)
    (hB : ∀ i, (phiD ring S e i).word.beta = B i)
    (hh : (G h).base = some (.inherited site))
    (hwh : (S h).top.wBase ≠ .NONE)
    (hcost : bankRepairDigitLabelCost ring R B (L + 1) h
      (bankRepairDigitBaseSeek (S h).top.wBase) ≤ L)
    (huniq : ∀ i, (G i).base = some (.inherited site) → i = h)
    (i : Fin n)
    (hi : (digitGhostStep ring S G time e i).base =
      some (.inherited site)) :
    (phiD ring S e i).top.wBase ≠ .NONE ∧
    bankRepairDigitLabelCost ring R B (L + 1) i
        (bankRepairDigitBaseSeek (phiD ring S e i).top.wBase) +
      (if e = h then 1 else 0) ≤
      bankRepairDigitLabelCost ring R B (L + 1) h
        (bankRepairDigitBaseSeek (S h).top.wBase) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hpos := bankRepairDigitLabelServiceHost hn ring S G time e site h
    hwh huniq i hi
  by_cases heh : e = h
  · subst h
    rw [if_pos rfl] at hpos
    subst i
    rw [if_pos rfl]
    have hy :
        (digitBaseReplay time e (ring.rightNeighbor e)
          (S e) (S (ring.rightNeighbor e))
          (workerW (S e).word
            (S (ring.rightNeighbor e)).word).betaY
          (G e).base (G (ring.rightNeighbor e)).base).y =
          some (.inherited site) := by
      simpa [digitGhostStep, digitService, hne] using hi
    rcases bankRepairDigitBaseReplayYChoice time e
        (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
        (workerW (S e).word
          (S (ring.rightNeighbor e)).word).betaY
        (G e).base (G (ring.rightNeighbor e)).base with
      hY | hX | hNew
    · exact absurd (huniq _ (hY.symm.trans hy)) hne
    · have hgne : (G (ring.rightNeighbor e)).base ≠ (G e).base := by
        intro heq
        exact hne (huniq _ (heq.trans hh))
      obtain ⟨hrx, hry, hcase⟩ := bankRepairDigitReplayMoveY time e
        (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
        (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
        (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY
        (G e).base (G (ring.rightNeighbor e)).base hgne ⟨site, hh⟩ hX
      have hphi : phiD ring S e (ring.rightNeighbor e) =
          (pairD (S e) (S (ring.rightNeighbor e))).2 := by
        simp [phiD, projectedEdge, hne]
      have htop : (phiD ring S e (ring.rightNeighbor e)).top.wBase =
          (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
            (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
            (workerW (S e).word
              (S (ring.rightNeighbor e)).word).betaY).y.wBase := by
        rw [hphi]; rfl
      have hbeta : (workerW (S e).word
          (S (ring.rightNeighbor e)).word).betaY =
          B (ring.rightNeighbor e) := by
        rw [← hB (ring.rightNeighbor e), hphi]; rfl
      have hRe : R e = false := (hR e).symm.trans hrx
      have hRj : R (ring.rightNeighbor e) = false := (hR _).symm.trans hry
      rw [htop]
      rw [bankRepairDigitLabelCostSucc ring R B L e
          (bankRepairDigitBaseSeek (S e).top.wBase),
        if_neg (by simp [hRe]), if_neg (by simp [hRj])] at hcost ⊢
      rcases hcase with ⟨hs, hyw⟩ | ⟨hz, hb, hyw⟩
      · have hseek : bankRepairDigitBaseSeek (S e).top.wBase = true := by
          rw [hs]; rfl
        rw [if_pos hseek] at hcost ⊢
        rw [hyw, hbeta]
        have hsk : bankRepairDigitBaseSeek
            (if B (ring.rightNeighbor e) = true then WBase.ZERO
              else WBase.SEEK) = !B (ring.rightNeighbor e) := by
          cases B (ring.rightNeighbor e) <;> rfl
        have hnn : (if B (ring.rightNeighbor e) = true then WBase.ZERO
              else WBase.SEEK) ≠ WBase.NONE := by
          cases B (ring.rightNeighbor e) <;> simp
        rw [hsk, bankRepairDigitLabelCostSaturate ring R B L _ _
          (by omega)]
        exact ⟨hnn, by omega⟩
      · have hseek : bankRepairDigitBaseSeek (S e).top.wBase = false := by
          rw [hz]; rfl
        have hBj : B (ring.rightNeighbor e) = false := hbeta.symm.trans hb
        rw [if_neg (by simp [hseek]), if_neg (by simp [hBj])] at hcost ⊢
        rw [hyw]
        have hsk : bankRepairDigitBaseSeek WBase.ZERO = false := rfl
        rw [hsk, bankRepairDigitLabelCostSaturate ring R B L _ _
          (by omega)]
        exact ⟨by simp, by omega⟩
    · have hbad :
          (some (.rootLaunch time e (ring.rightNeighbor e)) :
            Option (DigitBaseOrigin n)) =
            some (.inherited site) := hNew.symm.trans hy
      cases hbad
  · rw [if_neg heh] at hpos
    subst i
    rw [if_neg heh, Nat.add_zero]
    by_cases hjh : ring.rightNeighbor e = h
    · subst h
      have hphi : phiD ring S e (ring.rightNeighbor e) =
          (pairD (S e) (S (ring.rightNeighbor e))).2 := by
        simp [phiD, projectedEdge, hne]
      have htop : (phiD ring S e (ring.rightNeighbor e)).top.wBase =
          (S (ring.rightNeighbor e)).top.wBase := by
        rw [hphi]
        exact bankRepairDigitLiveTopStayY (S e) (S (ring.rightNeighbor e))
          _ _ hwh
      rw [htop]
      exact ⟨hwh, Nat.le_refl _⟩
    · have hhe : h ≠ e := fun h' => heh h'.symm
      have hhj : h ≠ ring.rightNeighbor e := fun h' => hjh h'.symm
      have hframe : phiD ring S e h = S h := by
        simp [phiD, projectedEdge, hhe, hhj]
      rw [hframe]
      exact ⟨hwh, Nat.le_refl _⟩

/-- The single inherited label, wherever it sits, has a live
physical base record, a remaining cost within the cap, and a
unique host. -/
def bankRepairDigitLabelInvariant {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (R B : Fin n → Bool) (L : Nat)
    (site : Fin n) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n) : Prop :=
  ∀ h, (G h).base = some (.inherited site) →
    (S h).top.wBase ≠ .NONE ∧
    bankRepairDigitLabelCost ring R B (L + 1) h
      (bankRepairDigitBaseSeek (S h).top.wBase) ≤ L ∧
    ∀ i, (G i).base = some (.inherited site) → i = h

open Classical in
/-- Remaining services of the single inherited label (zero once
retired). -/
noncomputable def bankRepairDigitLabelRemaining {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (R B : Fin n → Bool) (L : Nat)
    (site : Fin n) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n) : Nat :=
  if hA : bankRepairDigitInheritedLabelAlive site G then
    bankRepairDigitLabelCost ring R B (L + 1) (Classical.choose hA)
      (bankRepairDigitBaseSeek (S (Classical.choose hA)).top.wBase)
  else 0

theorem bankRepairDigitLabelRemainingHost {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (R B : Fin n → Bool) (L : Nat)
    (site : Fin n) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n) (h : Fin n)
    (hh : (G h).base = some (.inherited site))
    (huniq : ∀ i, (G i).base = some (.inherited site) → i = h) :
    bankRepairDigitLabelRemaining ring R B L site S G =
      bankRepairDigitLabelCost ring R B (L + 1) h
        (bankRepairDigitBaseSeek (S h).top.wBase) := by
  unfold bankRepairDigitLabelRemaining
  split
  · next hA =>
      rw [huniq _ (Classical.choose_spec hA)]
  · next hA => exact absurd ⟨h, hh⟩ hA

theorem bankRepairDigitLabelRemainingDead {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (R B : Fin n → Bool) (L : Nat)
    (site : Fin n) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n)
    (hA : ¬ bankRepairDigitInheritedLabelAlive site G) :
    bankRepairDigitLabelRemaining ring R B L site S G = 0 := by
  unfold bankRepairDigitLabelRemaining
  split
  · next hA' => exact absurd hA' hA
  · rfl

theorem bankRepairDigitLabelStepInv {c : Compiled} {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (R B : Fin n → Bool) (L : Nat)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (time : Nat) (e site : Fin n)
    (hR : ∀ i, (S i).word.native.l = R i)
    (hB : ∀ i, (phiD ring S e i).word.beta = B i)
    (hinv : bankRepairDigitLabelInvariant ring R B L site S G) :
    bankRepairDigitLabelInvariant ring R B L site (phiD ring S e)
      (digitGhostStep ring S G time e) := by
  intro h' hh'
  obtain ⟨h, hh⟩ := bankRepairDigitInheritedLabelParentStep hn ring S G
    time e site ⟨h', hh'⟩
  obtain ⟨hwh, hcost, huniq⟩ := hinv h hh
  obtain ⟨hw', hc'⟩ := bankRepairDigitLabelServiceCost hn ring R B L S G
    time e site h hR hB hh hwh hcost huniq h' hh'
  refine ⟨hw', Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans hc' hcost),
    ?_⟩
  intro i hi
  exact (bankRepairDigitLabelServiceHost hn ring S G time e site h hwh
      huniq i hi).trans
    (bankRepairDigitLabelServiceHost hn ring S G time e site h hwh
      huniq h' hh').symm

theorem bankRepairDigitLabelStepCost {c : Compiled} {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (R B : Fin n → Bool) (L : Nat)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (time : Nat) (e site h : Fin n)
    (hR : ∀ i, (S i).word.native.l = R i)
    (hB : ∀ i, (phiD ring S e i).word.beta = B i)
    (hinv : bankRepairDigitLabelInvariant ring R B L site S G)
    (hh : (G h).base = some (.inherited site)) :
    bankRepairDigitLabelRemaining ring R B L site (phiD ring S e)
        (digitGhostStep ring S G time e) + (if e = h then 1 else 0) ≤
      bankRepairDigitLabelRemaining ring R B L site S G := by
  obtain ⟨hwh, hcost, huniq⟩ := hinv h hh
  rw [bankRepairDigitLabelRemainingHost ring R B L site S G h hh huniq]
  by_cases hA : bankRepairDigitInheritedLabelAlive site
      (digitGhostStep ring S G time e)
  · obtain ⟨h', hh'⟩ := hA
    have hinv' := bankRepairDigitLabelStepInv hn ring R B L S G time e site
      hR hB hinv
    obtain ⟨_, _, huniq'⟩ := hinv' h' hh'
    rw [bankRepairDigitLabelRemainingHost ring R B L site (phiD ring S e)
      _ h' hh' huniq']
    exact (bankRepairDigitLabelServiceCost hn ring R B L S G time e site h
      hR hB hh hwh hcost huniq h' hh').2
  · rw [bankRepairDigitLabelRemainingDead ring R B L site _ _ hA]
    have := bankRepairDigitLabelCostPos ring R B L h
      (bankRepairDigitBaseSeek (S h).top.wBase)
    split <;> omega

theorem bankRepairDigitLabelInitialSite {c : Compiled} {n : Nat}
    (S : Fin n → ProjD c) (site h : Fin n)
    (hh : (digitGhostInitial S h).base = some (.inherited site)) :
    h = site ∧ (S h).top.wBase ≠ .NONE := by
  simp only [digitGhostInitial, DigitGhost.initial] at hh
  cases hw : (S h).top.wBase <;> simp_all

theorem bankRepairDigitLabelInitialInv {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (R B : Fin n → Bool) (L : Nat)
    (site : Fin n) (S : Fin n → ProjD c)
    (hstop : (S site).top.wBase ≠ .NONE →
      ∃ k, 1 ≤ k ∧ k ≤ L ∧
        bankRepairDigitLabelStop ring R B site
          (bankRepairDigitBaseSeek (S site).top.wBase) k) :
    bankRepairDigitLabelInvariant ring R B L site S
      (digitGhostInitial S) := by
  intro h hh
  obtain ⟨hhs, hw⟩ := bankRepairDigitLabelInitialSite S site h hh
  subst hhs
  obtain ⟨k, hk1, hkL, hs⟩ := hstop hw
  refine ⟨hw, ?_, ?_⟩
  · exact Nat.le_trans (bankRepairDigitLabelCostOfStop ring R B k (L + 1)
      h _ hk1 (by omega) hs) hkL
  · intro i hi
    exact (bankRepairDigitLabelInitialSite S h i hi).1

/-- Extra leading geometry for the single inherited label, from
a fixed R-fold entrance: along the actual reachable audit prefix
no selected OLD pair FIRES, the root bits and the delimiter (beta)
bits stay frozen to one pattern `R`, `B`, and the inherited base
record at `site` sees a stop (root, or a delimiter in ZERO mode,
or a second delimiter in SEEK mode) within `L_t` services ahead,
with `t = ceilLogTwo (ceilLogTwo n)`. -/
def BankRepairDigitLabelLeadingGeometry {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (site : Fin n) : Prop :=
  ∃ R B : Fin n → Bool,
    (∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      (∀ e : Fin n,
        oldFire (z.1.val.1 e) (z.1.val.1 (ring.rightNeighbor e)) =
          none) ∧
      (∀ i, (piD z.1.val.1 i).word.native.l = R i) ∧
      (∀ i, (piD z.1.val.1 i).word.beta = B i)) ∧
    ((piD start.val.1 site).top.wBase ≠ .NONE →
      ∃ k, 1 ≤ k ∧
        k ≤ bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)) ∧
        bankRepairDigitLabelStop ring R B site
          (bankRepairDigitBaseSeek (piD start.val.1 site).top.wBase) k)

theorem bankRepairDigitLabelReachStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (R B : Fin n → Bool)
    (hgeo : ∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      (∀ e : Fin n,
        oldFire (z.1.val.1 e) (z.1.val.1 (ring.rightNeighbor e)) =
          none) ∧
      (∀ i, (piD z.1.val.1 i).word.native.l = R i) ∧
      (∀ i, (piD z.1.val.1 i).word.beta = B i))
    (z : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : BankRepairDigitOneLabelReachableFrom ring hbank start z)
    (e : Fin n) :
    piD (bankRepairDigitBoundaryAuditNext ring hbank z e).1.val.1 =
        phiD ring (piD z.1.val.1) e ∧
      (∀ i, (piD z.1.val.1 i).word.native.l = R i) ∧
      (∀ i, (phiD ring (piD z.1.val.1) e i).word.beta = B i) := by
  obtain ⟨hfire, hR, _⟩ := hgeo z hz
  obtain ⟨_, _, hB'⟩ := hgeo _
    (bankRepairDigitOneLabelReachableStep ring hbank start z e hz)
  have hproj : piD (bankRepairDigitBoundaryAuditNext ring hbank z e).1.val.1 =
      phiD ring (piD z.1.val.1) e :=
    bankRepairDigitMaskedProjectionOfNoFire ring hbank z.1 e (hfire e)
  refine ⟨hproj, hR, ?_⟩
  intro i
  rw [← hproj]
  exact hB' i

theorem bankRepairDigitLabelReachableInv {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (site : Fin n)
    (R B : Fin n → Bool) (L : Nat)
    (hgeo : ∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      (∀ e : Fin n,
        oldFire (z.1.val.1 e) (z.1.val.1 (ring.rightNeighbor e)) =
          none) ∧
      (∀ i, (piD z.1.val.1 i).word.native.l = R i) ∧
      (∀ i, (piD z.1.val.1 i).word.beta = B i))
    (hinit : bankRepairDigitLabelInvariant ring R B L site
      (piD start.val.1) (digitGhostInitial (piD start.val.1))) :
    ∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      bankRepairDigitLabelInvariant ring R B L site
        (piD z.1.val.1) z.2.current := by
  have key : ∀ (word : List (Fin n)) z0,
      BankRepairDigitOneLabelReachableFrom ring hbank start z0 →
      bankRepairDigitLabelInvariant ring R B L site
        (piD z0.1.val.1) z0.2.current →
      bankRepairDigitLabelInvariant ring R B L site
        (piD (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          z0).1.val.1)
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          z0).2.current := by
    intro word
    induction word with
    | nil => intro z0 _ h; exact h
    | cons a l ih =>
        intro z0 hz0 hinv
        apply ih _ (bankRepairDigitOneLabelReachableStep ring hbank start
          z0 a hz0)
        obtain ⟨hproj, hR, hB⟩ := bankRepairDigitLabelReachStep ring hbank
          start R B hgeo z0 hz0 a
        rw [hproj]
        exact bankRepairDigitLabelStepInv hn ring R B L (piD z0.1.val.1)
          z0.2.current (z0.2.clock + 1) a site hR hB hinv
  rintro z ⟨word, rfl⟩
  exact key word _ ⟨[], rfl⟩ hinit

/-- Inherited-label retirement from a fixed R-fold entrance under
the explicit leading geometry. -/
theorem bankRepairDigitSingleInheritedLabelTasksOfLeadingGeometry
    {n : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (site : Fin n)
    (_hest : BankRepairRFoldEstablished ring hbank start)
    (hgeo : BankRepairDigitLabelLeadingGeometry ring hbank start site) :
    BankRepairDigitSingleInheritedLabelTasks ring hbank start site := by
  obtain ⟨R, B, hfr, hstop⟩ := hgeo
  have hinit := bankRepairDigitLabelInitialInv ring R B
    (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
    (piD start.val.1) hstop
  have hinv := bankRepairDigitLabelReachableInv hn ring hbank start site
    R B _ hfr hinit
  have hcost : ∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      ∀ h, (z.2.current h).base = some (.inherited site) → ∀ e : Fin n,
      bankRepairDigitLabelRemaining ring R B
          (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
          (piD (bankRepairDigitBoundaryAuditNext ring hbank z e).1.val.1)
          (bankRepairDigitBoundaryAuditNext ring hbank z e).2.current +
        (if e = h then 1 else 0) ≤
      bankRepairDigitLabelRemaining ring R B
          (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
          (piD z.1.val.1) z.2.current := by
    intro z hz h hh e
    obtain ⟨hproj, hR, hB⟩ := bankRepairDigitLabelReachStep ring hbank
      start R B hfr z hz e
    rw [hproj]
    exact bankRepairDigitLabelStepCost hn ring R B _ (piD z.1.val.1)
      z.2.current (z.2.clock + 1) e site h hR hB (hinv z hz) hh
  refine ⟨fun z => bankRepairDigitLabelRemaining ring R B
      (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
      (piD z.1.val.1) z.2.current, ?_, ?_, ?_⟩
  · intro z hz hret e
    obtain ⟨h, hh⟩ : bankRepairDigitInheritedLabelAlive site z.2.current :=
      Classical.byContradiction fun hA => hret hA
    exact Nat.le_trans (Nat.le_add_right _ _) (hcost z hz h hh e)
  · intro z hz hret
    obtain ⟨h, hh⟩ : bankRepairDigitInheritedLabelAlive site z.2.current :=
      Classical.byContradiction fun hA => hret hA
    refine ⟨h, ?_⟩
    have := hcost z hz h hh h
    rw [if_pos rfl] at this
    exact this
  · show bankRepairDigitLabelRemaining ring R B
        (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
        (piD start.val.1) (digitGhostInitial (piD start.val.1)) ≤ _
    by_cases hA : bankRepairDigitInheritedLabelAlive site
        (digitGhostInitial (piD start.val.1))
    · obtain ⟨h, hh⟩ := hA
      obtain ⟨_, hc, hu⟩ := hinit h hh
      rw [bankRepairDigitLabelRemainingHost ring R B _ site _ _ h hh hu]
      exact hc
    · rw [bankRepairDigitLabelRemainingDead ring R B _ site _ _ hA]
      exact Nat.zero_le _

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- The left output of the literal native pair of a non-leader
is a non-leader with zero `b`: it is FIRE-eligible. -/
theorem bankRepairDigitLiteralLeftNonLeader (ax ay : CertNative)
    (h : ax.l = false) :
    (certLiteralEPair ax ay).1.l = false ∧
      (certLiteralEPair ax ay).1.b.val = 0 := by
  obtain ⟨l, b, sh, sg⟩ := ax
  obtain ⟨rl, rb, rsh, rsg⟩ := ay
  simp only at h
  subst h
  rcases b with ⟨_ | _ | _ | b, hb⟩
  all_goals first
    | omega
    | (cases rl <;> cases rsh <;> cases rsg <;> cases sh <;> cases sg <;>
        exact ⟨rfl, rfl⟩)

/-- A requesting, granted non-leader always FIREs in OLD
selection (branch F0 of `fireSelect`). -/
theorem bankRepairDigitOldFireOfRequestGrant {c : Compiled}
    (x y : Agent c) (hl : x.l = false) (hr : x.req = true)
    (hg : x.grant = true) :
    oldFire x y ≠ none := by
  have hlit := bankRepairDigitLiteralLeftNonLeader x.certNative
    y.certNative hl
  simp [oldFire, fireSelect, hlit.1, hlit.2, hr, hg]

/-- Raise the request and grant bits at the site `e`, leaving
every other field and every other site unchanged. -/
def bankRepairDigitFireConfig {c : Compiled} {n : Nat}
    (C : Fin n → Agent c) (e : Fin n) : Fin n → Agent c :=
  fun i => if i = e then { C e with req := true, grant := true } else C i

theorem bankRepairDigitFireConfigProjR {c : Compiled} {n : Nat}
    (C : Fin n → Agent c) (e i : Fin n) :
    ProjR.ofAgent (bankRepairDigitFireConfig C e i) =
      ProjR.ofAgent (C i) := by
  unfold bankRepairDigitFireConfig
  by_cases h : i = e
  · subst h
    rw [if_pos rfl]
    rfl
  · rw [if_neg h]

theorem bankRepairDigitFireConfigCand {c : Compiled} {n : Nat}
    (C : Fin n → Agent c) (e i : Fin n) :
    NativeCand.ofAgent (bankRepairDigitFireConfig C e i) =
      NativeCand.ofAgent (C i) := by
  unfold bankRepairDigitFireConfig
  by_cases h : i = e
  · subst h
    rw [if_pos rfl]
    rfl
  · rw [if_neg h]

/-- The valid BANK reference with request and grant raised at `e`.
Validity only reads the memory stamps, so it is inherited. -/
def bankRepairDigitFireProbe {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (e : Fin n) :
    BankReferenceState ring hbank :=
  ⟨(bankRepairDigitFireConfig start.val.1 e, start.val.2), start.property⟩

/-- The R-fold entrance reads neither `req` nor `grant`, so it is
preserved by raising both at one site. -/
theorem bankRepairDigitFireProbeEstablished {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (e : Fin n)
    (hest : BankRepairRFoldEstablished ring hbank start) :
    BankRepairRFoldEstablished ring hbank
      (bankRepairDigitFireProbe ring hbank start e) := by
  have hR : ∀ i, ProjR.ofAgent (bankRepairDigitFireConfig start.val.1 e i) =
      ProjR.ofAgent (start.val.1 i) :=
    bankRepairDigitFireConfigProjR start.val.1 e
  have hC : ∀ i,
      NativeCand.ofAgent (bankRepairDigitFireConfig start.val.1 e i) =
        NativeCand.ofAgent (start.val.1 i) :=
    bankRepairDigitFireConfigCand start.val.1 e
  have hnat : nativeProjection (bankRepairDigitFireConfig start.val.1 e) =
      nativeProjection start.val.1 :=
    funext fun i => congrArg (fun p => p.word.native) (hR i)
  have hcand : (fun i =>
      NativeCand.ofAgent (bankRepairDigitFireConfig start.val.1 e i)) =
      (fun i => NativeCand.ofAgent (start.val.1 i)) := funext hC
  have hW : piW (bankRepairDigitFireConfig start.val.1 e) =
      piW start.val.1 :=
    funext fun i => congrArg ProjR.word (hR i)
  have hpR : piR (bankRepairDigitFireConfig start.val.1 e) =
      piR start.val.1 := funext hR
  unfold BankRepairRFoldEstablished BankRepairWAccepted BankRepairCore
    BankRepairWord BankRepairReader Closure.NativeFactor
    Closure.CandidateFactor Closure.WordFactor Closure.ReaderFactor
    at hest ⊢
  dsimp only [bankRepairDigitFireProbe]
  rw [hnat, hcand, hW, hpR]
  exact hest

/-- At the probe, the start itself is a reachable audit state on
which the edge out of `e` FIREs; so part 1 (no FIRE) of the
leading geometry fails, for every site. -/
theorem bankRepairDigitFireProbeNotLeadingGeometry {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (e : Fin n)
    (hl : (start.val.1 e).l = false) (site : Fin n) :
    ¬ BankRepairDigitLabelLeadingGeometry ring hbank
      (bankRepairDigitFireProbe ring hbank start e) site := by
  rintro ⟨R, B, hfr, -⟩
  have h := (hfr (bankRepairDigitFireProbe ring hbank start e,
    digitAuditInitial
      (piD (bankRepairDigitFireProbe ring hbank start e).val.1))
    ⟨[], rfl⟩).1 e
  have hx : bankRepairDigitFireConfig start.val.1 e e =
      { start.val.1 e with req := true, grant := true } := if_pos rfl
  change oldFire (bankRepairDigitFireConfig start.val.1 e e)
    (bankRepairDigitFireConfig start.val.1 e (ring.rightNeighbor e)) =
      none at h
  rw [hx] at h
  exact bankRepairDigitOldFireOfRequestGrant
    (x := { start.val.1 e with req := true, grant := true }) _ hl rfl rfl h

/-- T4 step 3: the R-fold entrance does NOT imply the leading
geometry. From any entrance state (n ≥ 2), raising `req` and `grant`
at a non-leader site gives another entrance state at which part 1
(no OLD FIRE along the reachable prefix) fails for every site. -/
theorem bankRepairDigitEntranceNotLeadingGeometry {n : Nat}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hest : BankRepairRFoldEstablished ring hbank start) :
    ∃ start' : BankReferenceState ring hbank,
      BankRepairRFoldEstablished ring hbank start' ∧
      ∀ site, ¬ BankRepairDigitLabelLeadingGeometry ring hbank start' site := by
  obtain ⟨p, _, huniq⟩ := hest.1.1.1.1
  obtain ⟨e, hne⟩ : ∃ e : Fin n, e ≠ p := by
    by_cases hp : p.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by
        have : (1 : Nat) = p.val := congrArg Fin.val h
        omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => by
        have : (0 : Nat) = p.val := congrArg Fin.val h
        omega⟩
  have hl : (start.val.1 e).l = false := by
    cases h : (start.val.1 e).l
    · rfl
    · exact absurd (huniq e h) hne
  exact ⟨bankRepairDigitFireProbe ring hbank start e,
    bankRepairDigitFireProbeEstablished ring hbank start e hest,
    bankRepairDigitFireProbeNotLeadingGeometry ring hbank start e hl⟩

end L3.RenewalReferenceClock

/-!
T5: what the R-fold producer guarantees, and the strengthened entrance.

In the stage chain `bankFinishMaskedRepairBoundOfStages` every R-fold
entrance is reached on `bankRepairNext` from a `BankPreparedAtSomeRoot`
state, which carries `BankPostInheritedSingleton root`; that class is
closed under every step (`bankPostInheritedSingletonClosed`). It gives
zero physical grants (requests stay arbitrary) and a frozen native root.
Grant-freeness alone disables every FIRE branch of `fireSelect`.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- The digit entrance actually produced by the stage chain: the
R-fold receipts together with the post-inherited rooted, grant-free,
authority-extinct class that the earlier stages keep. -/
def BankRepairDigitProducedEntrance {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) : Prop :=
  BankRepairRFoldEstablished ring hbank start ∧
    ∃ root : Fin n, BankPostInheritedSingleton ring hbank root start

theorem bankRepairDigitPostInheritedSingletonRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) :
    ∀ (word : List (Fin n)) (x : BankReferenceState ring hbank),
      BankPostInheritedSingleton ring hbank root x →
      BankPostInheritedSingleton ring hbank root
        (word.foldl (bankRepairNext ring hbank) x) := by
  intro word
  induction word with
  | nil => intro x hx; exact hx
  | cons e rest ih =>
      intro x hx
      exact ih (bankRepairNext ring hbank x e)
        (bankPostInheritedSingletonClosed ring hn hbank root x hx e)

/-- Producer side: any R-fold state reached on the actual chain from
a prepared state is a produced entrance. -/
theorem bankRepairDigitProducedEntranceOfPrepared {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (word : List (Fin n))
    (hR : BankRepairRFoldEstablished ring hbank
      (word.foldl (bankRepairNext ring hbank) x)) :
    BankRepairDigitProducedEntrance ring hbank
      (word.foldl (bankRepairNext ring hbank) x) := by
  obtain ⟨root, hs, -⟩ := hx
  exact ⟨hR, root,
    bankRepairDigitPostInheritedSingletonRun ring hn hbank root word x hs⟩

/-- No OLD pair FIREs when both old grants are zero. -/
theorem bankRepairDigitOldFireNoneOfGrantFree {c : Compiled}
    (x y : Agent c) (hx : x.grant = false) (hy : y.grant = false) :
    oldFire x y = none := by
  simp [oldFire, fireSelect, hx, hy]

/-- The accepted W factor carries Q_W of the physical W projection. -/
theorem bankRepairDigitWordSafeOfFactor {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hW : BankRepairWord ring hbank z) :
    AcceptedReceipts.QWord ring (piW z.val.1) := by
  obtain ⟨root, ρ, γ₀, w, γ, -, -, hacc⟩ := hW
  cases γ with
  | failed => exact hacc.1.elim
  | live shadow h => exact hacc.1.2.2.2.2

/-- The W projection of a no-FIRE step is the projected W step. -/
theorem bankRepairDigitWordProjectionOfNoFire {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hfire : oldFire (z.val.1 e)
      (z.val.1 (ring.rightNeighbor e)) = none) :
    piW (bankRepairNext ring hbank z e).val.1 =
      phiW ring (piW z.val.1) e := by
  have h := bankRepairDigitMaskedProjectionOfNoFire ring hbank z e hfire
  funext i
  have hi := congrArg (fun S => (S i).word) h
  refine hi.trans ?_
  dsimp only [phiD, phiW, projectedEdge]
  by_cases h1 : i = e
  · rw [if_pos h1, if_pos h1]
    rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i = ring.rightNeighbor e
    · rw [if_pos h2, if_pos h2]
      rfl
    · rw [if_neg h2, if_neg h2]
      rfl

/-- The post-inherited root fixes every native leader bit. -/
theorem bankRepairDigitRootedLeader {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (hs : BankPostInheritedSingleton ring hbank root z) (i : Fin n) :
    (z.val.1 i).l = decide (i = root) := by
  have h1 : (z.val.1 root).l = true := hs.2.1
  have h2 : ∀ j : Fin n, (z.val.1 j).l = true → j = root := hs.2.2.1
  by_cases hi : i = root
  · subst hi
    simp [h1]
  · cases h : (z.val.1 i).l
    · simp [hi]
    · exact absurd (h2 i h) hi

/-- The digit-stage invariant from a produced entrance. -/
def BankRepairDigitProducedInv {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (B : Fin n → Bool)
    (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedSingleton ring hbank root z ∧
    AcceptedReceipts.QWord ring (piW z.val.1) ∧
    ∀ i, (z.val.1 i).beta = B i

theorem bankRepairDigitProducedInvStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (B : Fin n → Bool)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitProducedInv ring hbank root B z) (e : Fin n) :
    BankRepairDigitProducedInv ring hbank root B
      (bankRepairNext ring hbank z e) := by
  obtain ⟨hs, hq, hb⟩ := hz
  have hg : ∀ i, (z.val.1 i).grant = false := hs.1.1.2
  have hfire := bankRepairDigitOldFireNoneOfGrantFree _ _
    (hg e) (hg (ring.rightNeighbor e))
  have hproj := bankRepairDigitWordProjectionOfNoFire ring hbank z e hfire
  refine ⟨bankPostInheritedSingletonClosed ring hn hbank root z hs e, ?_, ?_⟩
  · rw [hproj]
    exact (AcceptedReceipts.qword_step ring _ hq e).2
  · intro i
    have hv := congrArg Prod.snd
      (AcceptedReceipts.qword_visible_fixed ring _ hq e i)
    have hi : ((bankRepairNext ring hbank z e).val.1 i).beta =
        (phiW ring (piW z.val.1) e i).beta :=
      congrArg (fun S => (S i).beta) hproj
    rw [hi]
    exact hv.trans (hb i)

theorem bankRepairDigitProducedReachableInv {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (root : Fin n)
    (hs : BankPostInheritedSingleton ring hbank root start)
    (hq : AcceptedReceipts.QWord ring (piW start.val.1)) :
    ∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      BankRepairDigitProducedInv ring hbank root
        (fun i => (start.val.1 i).beta) z.1 := by
  have key : ∀ (word : List (Fin n))
      (z0 : BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n),
      BankRepairDigitProducedInv ring hbank root
        (fun i => (start.val.1 i).beta) z0.1 →
      BankRepairDigitProducedInv ring hbank root
        (fun i => (start.val.1 i).beta)
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z0).1 := by
    intro word
    induction word with
    | nil => intro z0 h; exact h
    | cons e rest ih =>
        intro z0 h
        exact ih (bankRepairDigitBoundaryAuditNext ring hbank z0 e)
          (bankRepairDigitProducedInvStep ring hn hbank root _ z0.1 h e)
  rintro z ⟨word, rfl⟩
  exact key word _ ⟨hs, hq, fun _ => rfl⟩

/-- T5 (a): the produced entrance plus one-label reachability gives
part 1 of the leading geometry, with `R` and `B` the entrance's own
leader and delimiter bits. -/
theorem bankRepairDigitProducedEntranceNoFireFrozen {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hent : BankRepairDigitProducedEntrance ring hbank start) :
    ∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      (∀ e : Fin n,
        oldFire (z.1.val.1 e) (z.1.val.1 (ring.rightNeighbor e)) =
          none) ∧
      (∀ i, (piD z.1.val.1 i).word.native.l =
        (piD start.val.1 i).word.native.l) ∧
      (∀ i, (piD z.1.val.1 i).word.beta =
        (piD start.val.1 i).word.beta) := by
  obtain ⟨hest, root, hs⟩ := hent
  have hq := bankRepairDigitWordSafeOfFactor ring hbank start hest.1.2
  intro z hz
  obtain ⟨hzs, -, hzb⟩ :=
    bankRepairDigitProducedReachableInv hn ring hbank start root hs hq z hz
  have hg : ∀ i, (z.1.val.1 i).grant = false := hzs.1.1.2
  refine ⟨fun e => bankRepairDigitOldFireNoneOfGrantFree _ _
    (hg e) (hg _), ?_, hzb⟩
  intro i
  show (z.1.val.1 i).l = (start.val.1 i).l
  rw [bankRepairDigitRootedLeader ring hbank root z.1 hzs i,
    bankRepairDigitRootedLeader ring hbank root start hs i]

/-- The produced entrance plus the stop clause (part 2) for the
entrance's own bits gives the full leading geometry. -/
theorem bankRepairDigitLeadingGeometryOfProducedEntrance {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (site : Fin n)
    (hent : BankRepairDigitProducedEntrance ring hbank start)
    (hstop : (piD start.val.1 site).top.wBase ≠ .NONE →
      ∃ k, 1 ≤ k ∧
        k ≤ bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)) ∧
        bankRepairDigitLabelStop ring
          (fun i => (piD start.val.1 i).word.native.l)
          (fun i => (piD start.val.1 i).word.beta) site
          (bankRepairDigitBaseSeek (piD start.val.1 site).top.wBase) k) :
    BankRepairDigitLabelLeadingGeometry ring hbank start site :=
  ⟨_, _, bankRepairDigitProducedEntranceNoFireFrozen hn ring hbank start hent,
    hstop⟩

/-- T3 from the produced entrance: only the stop clause remains. -/
theorem bankRepairDigitSingleInheritedLabelTasksOfProducedEntrance
    {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (site : Fin n)
    (hent : BankRepairDigitProducedEntrance ring hbank start)
    (hstop : (piD start.val.1 site).top.wBase ≠ .NONE →
      ∃ k, 1 ≤ k ∧
        k ≤ bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)) ∧
        bankRepairDigitLabelStop ring
          (fun i => (piD start.val.1 i).word.native.l)
          (fun i => (piD start.val.1 i).word.beta) site
          (bankRepairDigitBaseSeek (piD start.val.1 site).top.wBase) k) :
    BankRepairDigitSingleInheritedLabelTasks ring hbank start site :=
  bankRepairDigitSingleInheritedLabelTasksOfLeadingGeometry (by omega)
    ring hbank start site hent.1
    (bankRepairDigitLeadingGeometryOfProducedEntrance hn ring hbank start
      site hent hstop)

/-- The T4 probe is not a produced entrance: it raises a grant. -/
theorem bankRepairDigitFireProbeNotProduced {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (e : Fin n) :
    ¬ BankRepairDigitProducedEntrance ring hbank
      (bankRepairDigitFireProbe ring hbank start e) := by
  rintro ⟨-, root, hs⟩
  have h : (bankRepairDigitFireConfig start.val.1 e e).grant = false :=
    hs.1.1.2 e
  simp [bankRepairDigitFireConfig] at h

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-! ### T6: the stop clause

The stop clause asks that the base label at a non-root `site` meet,
within `L_t = 2 r + t - 2` services to the right, a root or (ZERO) a
delimiter / (SEEK) a second delimiter.  The produced entrance does not
constrain `beta`; the clause follows from the static certificate
relations (recurrence, nonzero, marker) of the entrance word.  The
root site needs no clause: its label cost is `1`. -/

theorem bankRepairDigitFoldConst {α : Type} : ∀ (m : Nat) (x : α),
    Fin.foldl m (fun acc (_ : Fin m) => acc) x = x := by
  intro m
  induction m with
  | zero => intro x; rfl
  | succ m ih => intro x; rw [Fin.foldl_succ]; exact ih x

theorem bankRepairDigitFoldAndTrue (m : Nat) (u : Fin m → Bool)
    (hu : ∀ j, u j = true) :
    Fin.foldl m (fun acc j => acc && u j) true = true := by
  have h : (fun acc j => acc && u j) = fun acc (_ : Fin m) => acc := by
    funext acc j
    rw [hu j, Bool.and_true]
  rw [h]
  exact bankRepairDigitFoldConst m true

/-- With all taps zero, the recurrence shifts in zeros. -/
theorem bankRepairDigitZeroTapsIter (t : Nat) (taps : Nat → Bool)
    (htaps : ∀ j, taps j = false) :
    ∀ (k : Nat) (u : Fin t → Bool) (i : Fin t), t ≤ i.val + k →
      recIter t taps k u i = false := by
  intro k
  induction k with
  | zero => intro u i h; have := i.isLt; omega
  | succ k ih =>
      intro u i h
      rw [recIter_succ]
      unfold recStep
      by_cases hi : i.val + 1 < t
      · rw [dif_pos hi]
        exact ih u _ (by simp only; omega)
      · rw [dif_neg hi]
        have hf : (fun acc (j : Fin t) =>
            Bool.xor acc (Bool.and (taps j.val) (recIter t taps k u j))) =
            fun acc (_ : Fin t) => acc := by
          funext acc j
          rw [htaps j.val]
          simp
        rw [hf]
        exact bankRepairDigitFoldConst t false

theorem bankRepairDigitRecIterAdd (t : Nat) (taps : Nat → Bool) :
    ∀ (a b : Nat) (u : Fin t → Bool),
      recIter t taps (a + b) u = recIter t taps a (recIter t taps b u) := by
  intro a
  induction a with
  | zero => intro b u; rw [Nat.zero_add]; rfl
  | succ a ih =>
      intro b u
      rw [Nat.succ_add, recIter_succ, recIter_succ, ih]

theorem bankRepairDigitPowLower : ∀ t : Nat, t + 1 ≤ 2 ^ t := by
  intro t
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ]; omega

theorem bankRepairDigitWalkSite {n : Nat} (ring : DirectedRing n) :
    ∀ (k : Nat) (i : Fin n),
      bankRepairDigitRightWalk ring k i = certSite i k := by
  intro k
  induction k with
  | zero => intro i; exact (certSite_zero i).symm
  | succ k ih =>
      intro i
      show bankRepairDigitRightWalk ring k (ring.rightNeighbor i) = _
      rw [ih]
      have h1 : ring.rightNeighbor i = certSite i 1 := rfl
      rw [h1, certSite_add, Nat.add_comm 1 k]

/-- The static delimiter relations of a certificate word: recurrence,
nonzero and marker (no block increment). -/
def BankRepairDigitStaticDelimiters {n : Nat} {c : Compiled}
    (W : CertificateWord n c) : Prop :=
  ∀ s : Fin n, RecurrenceRelation W s ∧ NonzeroRelation W s ∧
    MarkerRelation W s

theorem bankRepairDigitWindowIter {n : Nat} {c : Compiled}
    (W : CertificateWord n c) (hW : BankRepairDigitStaticDelimiters W)
    (s : Fin n) (M : Nat)
    (harc : ∀ m, m < M + c.t → certLeader W (certSite s m) = false) :
    ∀ k, k ≤ M → certWindow W (certSite s k) =
      recIter c.t c.taps k (certWindow W s) := by
  intro k
  induction k with
  | zero => intro _; rw [certSite_zero, recIter_zero]
  | succ k ih =>
      intro hk
      have harc' : certFollowerArc W (certSite s k) (c.t + 1) := by
        intro j
        rw [certSite_add]
        exact harc _ (by have := j.isLt; omega)
      rw [show certSite s (k + 1) = certSite (certSite s k) 1 from
        (certSite_add s k 1).symm]
      rw [(hW (certSite s k)).1 harc', ih (by omega), recIter_succ]

/-- Static delimiters give every follower site a stop within
`2 r + t - 2` services, in either mode. -/
theorem bankRepairDigitStaticStop {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (W : CertificateWord n c)
    (hW : BankRepairDigitStaticDelimiters W)
    (ht : 2 ≤ c.t)
    (htaps : IsPrimitive c.t c.taps ∨ ∀ j, c.taps j = false)
    (L : Nat) (hL : 2 * c.rho + c.t - 2 ≤ L)
    (i : Fin n) (hi : certLeader W i = false) (seek : Bool) :
    ∃ k, 1 ≤ k ∧ k ≤ L ∧
      bankRepairDigitLabelStop ring (certLeader W) (certMarker W) i seek k := by
  have hpow := bankRepairDigitPowLower c.t
  have hr : c.rho = 2 ^ c.t - 1 := rfl
  by_cases hroot : ∃ k, 1 ≤ k ∧ k ≤ L ∧ certLeader W (certSite i k) = true
  · obtain ⟨k, hk1, hkL, hk⟩ := hroot
    refine ⟨k, hk1, hkL, Or.inl ?_⟩
    rw [bankRepairDigitWalkSite]
    exact hk
  · have harc : ∀ m, m ≤ L → certLeader W (certSite i m) = false := by
      intro m hm
      by_cases h0 : m = 0
      · subst h0; rw [certSite_zero]; exact hi
      · cases h : certLeader W (certSite i m) with
        | false => rfl
        | true => exact absurd ⟨m, by omega, hm, h⟩ hroot
    have hiter := bankRepairDigitWindowIter W hW i (2 * c.rho - 1)
      (fun m hm => harc m (by omega))
    have hnz : ∃ j : Fin c.t, certWindow W i j = true :=
      (hW i).2.1 (fun j => harc j.val (by have := j.isLt; omega))
    rcases htaps with hp | hz
    · obtain ⟨k0, hk0, hk0v⟩ := isPrimitive_orbit_covers hp
        (certWindow W i) (fun _ => true) hnz ⟨⟨0, by omega⟩, rfl⟩
      have hper : recIter c.t c.taps (2 ^ c.t - 1) (certWindow W i) =
          certWindow W i := (hp _ hnz).1
      have hw1 : certWindow W (certSite i k0) = fun _ => true := by
        rw [hiter k0 (by omega)]
        exact hk0v
      have hw2 : certWindow W (certSite i (k0 + c.rho)) = fun _ => true := by
        rw [hiter (k0 + c.rho) (by omega), bankRepairDigitRecIterAdd, hr,
          hper]
        exact hk0v
      have hm : ∀ s : Fin n, certWindow W s = (fun _ => true) →
          certFollowerArc W s c.t →
          certMarker W (certSite s (c.t - 1)) = true := by
        intro s hs harc'
        rw [(hW s).2.2 harc', hs]
        exact bankRepairDigitFoldAndTrue c.t (fun _ => true) (fun _ => rfl)
      have harc1 : certFollowerArc W (certSite i k0) c.t := fun j => by
        rw [certSite_add]
        exact harc _ (by have := j.isLt; omega)
      have harc2 : certFollowerArc W (certSite i (k0 + c.rho)) c.t :=
        fun j => by
          rw [certSite_add]
          exact harc _ (by have := j.isLt; omega)
      have hb1 := hm _ hw1 harc1
      have hb2 := hm _ hw2 harc2
      rw [certSite_add] at hb1 hb2
      refine ⟨k0 + c.rho + (c.t - 1), by omega, by omega, ?_⟩
      unfold bankRepairDigitLabelStop
      simp only [bankRepairDigitWalkSite]
      exact Or.inr ⟨hb2, Or.inr ⟨k0 + (c.t - 1), by omega, by omega, hb1⟩⟩
    · have hwt := hiter c.t (by omega)
      have harct : certFollowerArc W (certSite i c.t) (c.t + 1) :=
        fun j => by
          rw [certSite_add]
          exact harc _ (by have := j.isLt; omega)
      obtain ⟨j, hj⟩ := (hW (certSite i c.t)).2.1 harct
      rw [hwt, bankRepairDigitZeroTapsIter c.t c.taps hz c.t _ j
        (by omega)] at hj
      exact absurd hj (by decide)

/-- The initial label invariant, with the root site exempt from the
stop clause (its label costs one service). -/
theorem bankRepairDigitLabelInitialInvExempt {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (R B : Fin n → Bool) (L : Nat) (hL : 1 ≤ L)
    (site : Fin n) (S : Fin n → ProjD c)
    (hstop : R site = false → (S site).top.wBase ≠ .NONE →
      ∃ k, 1 ≤ k ∧ k ≤ L ∧
        bankRepairDigitLabelStop ring R B site
          (bankRepairDigitBaseSeek (S site).top.wBase) k) :
    bankRepairDigitLabelInvariant ring R B L site S
      (digitGhostInitial S) := by
  intro h hh
  obtain ⟨hhs, hw⟩ := bankRepairDigitLabelInitialSite S site h hh
  subst hhs
  refine ⟨hw, ?_, ?_⟩
  · by_cases hr : R h = true
    · rw [bankRepairDigitLabelCostSucc, if_pos hr]
      exact hL
    · obtain ⟨k, hk1, hkL, hs⟩ := hstop (by simpa using hr) hw
      exact Nat.le_trans (bankRepairDigitLabelCostOfStop ring R B k (L + 1)
        h _ hk1 (by omega) hs) hkL
  · intro i hi
    exact (bankRepairDigitLabelInitialSite S h i hi).1

/-- T3 from frozen bits and any initial label invariant. -/
theorem bankRepairDigitSingleInheritedLabelTasksOfFrozenInit
    {n : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (site : Fin n) (R B : Fin n → Bool)
    (hfr : ∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      (∀ e : Fin n,
        oldFire (z.1.val.1 e) (z.1.val.1 (ring.rightNeighbor e)) =
          none) ∧
      (∀ i, (piD z.1.val.1 i).word.native.l = R i) ∧
      (∀ i, (piD z.1.val.1 i).word.beta = B i))
    (hinit : bankRepairDigitLabelInvariant ring R B
      (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
      (piD start.val.1) (digitGhostInitial (piD start.val.1))) :
    BankRepairDigitSingleInheritedLabelTasks ring hbank start site := by
  have hinv := bankRepairDigitLabelReachableInv hn ring hbank start site
    R B _ hfr hinit
  have hcost : ∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      ∀ h, (z.2.current h).base = some (.inherited site) → ∀ e : Fin n,
      bankRepairDigitLabelRemaining ring R B
          (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
          (piD (bankRepairDigitBoundaryAuditNext ring hbank z e).1.val.1)
          (bankRepairDigitBoundaryAuditNext ring hbank z e).2.current +
        (if e = h then 1 else 0) ≤
      bankRepairDigitLabelRemaining ring R B
          (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
          (piD z.1.val.1) z.2.current := by
    intro z hz h hh e
    obtain ⟨hproj, hR, hB⟩ := bankRepairDigitLabelReachStep ring hbank
      start R B hfr z hz e
    rw [hproj]
    exact bankRepairDigitLabelStepCost hn ring R B _ (piD z.1.val.1)
      z.2.current (z.2.clock + 1) e site h hR hB (hinv z hz) hh
  refine ⟨fun z => bankRepairDigitLabelRemaining ring R B
      (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
      (piD z.1.val.1) z.2.current, ?_, ?_, ?_⟩
  · intro z hz hret e
    obtain ⟨h, hh⟩ : bankRepairDigitInheritedLabelAlive site z.2.current :=
      Classical.byContradiction fun hA => hret hA
    exact Nat.le_trans (Nat.le_add_right _ _) (hcost z hz h hh e)
  · intro z hz hret
    obtain ⟨h, hh⟩ : bankRepairDigitInheritedLabelAlive site z.2.current :=
      Classical.byContradiction fun hA => hret hA
    refine ⟨h, ?_⟩
    have := hcost z hz h hh h
    rw [if_pos rfl] at this
    exact this
  · show bankRepairDigitLabelRemaining ring R B
        (bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))) site
        (piD start.val.1) (digitGhostInitial (piD start.val.1)) ≤ _
    by_cases hA : bankRepairDigitInheritedLabelAlive site
        (digitGhostInitial (piD start.val.1))
    · obtain ⟨h, hh⟩ := hA
      obtain ⟨_, hc, hu⟩ := hinit h hh
      rw [bankRepairDigitLabelRemainingHost ring R B _ site _ _ h hh hu]
      exact hc
    · rw [bankRepairDigitLabelRemainingDead ring R B _ site _ _ hA]
      exact Nat.zero_le _

/-- The weakest extra fact the label needs: the stop clause at
`site` unless `site` is the root. -/
def BankRepairDigitNonRootStop {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (site : Fin n) : Prop :=
  (piD start.val.1 site).word.native.l = false →
  (piD start.val.1 site).top.wBase ≠ .NONE →
    ∃ k, 1 ≤ k ∧
      k ≤ bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)) ∧
      bankRepairDigitLabelStop ring
        (fun i => (piD start.val.1 i).word.native.l)
        (fun i => (piD start.val.1 i).word.beta) site
        (bankRepairDigitBaseSeek (piD start.val.1 site).top.wBase) k

theorem bankRepairDigitLeadingLengthPos {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    1 ≤ bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)) := by
  have h7 := bankRepairDigitWidthBank hbank
  have hp := bankRepairDigitPowLower (ceilLogTwo (ceilLogTwo n))
  unfold bankRepairDigitLeadingLength bankRepairDigitRadius
  omega

/-- T3 from the produced entrance and the non-root stop clause. -/
theorem bankRepairDigitSingleInheritedLabelTasksOfNonRootStop
    {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (site : Fin n)
    (hent : BankRepairDigitProducedEntrance ring hbank start)
    (hstop : BankRepairDigitNonRootStop ring hbank start site) :
    BankRepairDigitSingleInheritedLabelTasks ring hbank start site :=
  bankRepairDigitSingleInheritedLabelTasksOfFrozenInit (by omega) ring
    hbank start site _ _
    (bankRepairDigitProducedEntranceNoFireFrozen hn ring hbank start hent)
    (bankRepairDigitLabelInitialInvExempt ring _ _ _
      (bankRepairDigitLeadingLengthPos hbank) site _ hstop)

/-- The static delimiter relations of the entrance word give the
non-root stop clause at every site. -/
theorem bankRepairDigitNonRootStopOfStaticDelimiters {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (site : Fin n)
    (hW : BankRepairDigitStaticDelimiters
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n))
        start.val.1)) :
    BankRepairDigitNonRootStop ring hbank start site := by
  intro hl _
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have ht : (compileAdvice (ceilLogTwo n)).t =
      ceilLogTwo (ceilLogTwo n) :=
    compileAdvice_t_large _ (by omega)
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two _ (by omega)
  have htaps : IsPrimitive (compileAdvice (ceilLogTwo n)).t
        (compileAdvice (ceilLogTwo n)).taps ∨
      ∀ j, (compileAdvice (ceilLogTwo n)).taps j = false := by
    left
    exact tapTablePrimitive _ ht2
  have hL : 2 * (compileAdvice (ceilLogTwo n)).rho +
        (compileAdvice (ceilLogTwo n)).t - 2 ≤
      bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitLeadingLength bankRepairDigitRadius Compiled.rho
    rw [ht] <;> omega
  exact bankRepairDigitStaticStop ring _ hW ht2 htaps _ hL site hl _

/-- T6 on the actual chain: a prepared state run to an R-fold state
retires the single inherited label at every site, given the static
delimiter relations of the reached word. -/
theorem bankRepairDigitSingleInheritedLabelTasksOfPreparedDelimiters
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (word : List (Fin n))
    (hR : BankRepairRFoldEstablished ring hbank
      (word.foldl (bankRepairNext ring hbank) x))
    (hW : BankRepairDigitStaticDelimiters
      (certificateWordOfAgents (compileAdvice (ceilLogTwo n))
        (word.foldl (bankRepairNext ring hbank) x).val.1)) :
    ∀ site, BankRepairDigitSingleInheritedLabelTasks ring hbank
      (word.foldl (bankRepairNext ring hbank) x) site := fun site =>
  bankRepairDigitSingleInheritedLabelTasksOfNonRootStop hn ring hbank _ site
    (bankRepairDigitProducedEntranceOfPrepared ring hn hbank x hx word hR)
    (bankRepairDigitNonRootStopOfStaticDelimiters ring hbank _ site hW)

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-! ### T7: where the delimiter spacing comes from

The beta bits are written by the W worker rows (Target.lean:3373,
3399, 3477). The invariant saying that the visible word is the
certificate word of the advice is
`AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues`
(Target.lean:5530), a field of `CleanWorkerInv`. The W acceptance
(`BlockA.acceptsWord`, Target.lean:2978) records only receipt flags
and `QWord`, so the invariant is NOT carried to the R-fold entrance.
Below: the invariant at the native root gives the non-root stop
clause; once established at the W hit it is carried to the entrance;
for `t > 17` (zero taps) it is empty, and the word the literal W rows
write has no delimiter beyond offset `t`. -/

theorem bankRepairDigitFinFoldlRange {β : Type} (g : β → Nat → β) :
    ∀ (t : Nat) (x : β),
      Fin.foldl t (fun acc (j : Fin t) => g acc j.val) x =
        (List.range t).foldl g x := by
  intro t
  induction t with
  | zero => intro x; rfl
  | succ t ih =>
      intro x
      rw [Fin.foldl_succ_last, List.range_succ, List.foldl_append, ← ih]
      rfl

theorem bankRepairDigitOrFoldTrue (s : Nat → Bool) :
    ∀ (l : List Nat) (z : Bool),
      l.foldl (fun z j => z || s j) z = true →
        z = true ∨ ∃ j, j ∈ l ∧ s j = true := by
  intro l
  induction l with
  | nil => intro z h; exact Or.inl h
  | cons x l ih =>
      intro z h
      rcases ih (z || s x) h with h1 | ⟨j, hj, hs⟩
      · cases z with
        | true => exact Or.inl rfl
        | false => exact Or.inr ⟨x, by simp, by simpa using h1⟩
      · exact Or.inr ⟨j, by simp [hj], hs⟩

theorem bankRepairDigitOrFoldFalse (s : Nat → Bool) :
    ∀ (l : List Nat) (z : Bool),
      l.foldl (fun z j => z || s j) z = false →
        z = false ∧ ∀ j, j ∈ l → s j = false := by
  intro l
  induction l with
  | nil => intro z h; exact ⟨h, fun j hj => by simp at hj⟩
  | cons x l ih =>
      intro z h
      obtain ⟨h1, h2⟩ := ih (z || s x) h
      have hz : z = false ∧ s x = false := by simpa using h1
      refine ⟨hz.1, fun j hj => ?_⟩
      rcases List.mem_cons.mp hj with hjx | hj'
      · rw [hjx]; exact hz.2
      · exact h2 j hj'

theorem bankRepairDigitTrailFoldTrue (s : Nat → Bool) :
    ∀ (l : List Nat) (a : Bool), (∀ j, j ∈ l → j ≠ 0 → s j = true) →
      l.foldl (fun a j => if j = 0 then a else a && s j) a = a := by
  intro l
  induction l with
  | nil => intro a _; rfl
  | cons x l ih =>
      intro a h
      have hx : (if x = 0 then a else a && s x) = a := by
        by_cases h0 : x = 0
        · rw [if_pos h0]
        · rw [if_neg h0, h x (by simp) h0, Bool.and_true]
      show l.foldl (fun a j => if j = 0 then a else a && s j)
        (if x = 0 then a else a && s x) = a
      rw [hx]
      exact ih a (fun j hj => h j (by simp [hj]))

theorem bankRepairDigitTrailFoldFalseStart (s : Nat → Bool) :
    ∀ (l : List Nat),
      l.foldl (fun a j => if j = 0 then a else a && s j) false = false := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hx : (if x = 0 then false else false && s x) = false := by
        by_cases h0 : x = 0
        · rw [if_pos h0]
        · rw [if_neg h0, Bool.false_and]
      show l.foldl (fun a j => if j = 0 then a else a && s j)
        (if x = 0 then false else false && s x) = false
      rw [hx]
      exact ih

theorem bankRepairDigitTrailFoldFalse (s : Nat → Bool) :
    ∀ (l : List Nat) (a : Bool) (j : Nat), j ∈ l → j ≠ 0 → s j = false →
      l.foldl (fun a j => if j = 0 then a else a && s j) a = false := by
  intro l
  induction l with
  | nil => intro a j hj; simp at hj
  | cons x l ih =>
      intro a j hj hj0 hs
      show l.foldl (fun a j => if j = 0 then a else a && s j)
        (if x = 0 then a else a && s x) = false
      rcases List.mem_cons.mp hj with hjx | hj'
      · rw [← hjx, if_neg hj0, hs, Bool.and_false]
        exact bankRepairDigitTrailFoldFalseStart s l
      · exact ih _ j hj' hj0 hs

theorem bankRepairDigitXorFoldZeroTaps (taps s : Nat → Bool)
    (hz : ∀ j, taps j = false) :
    ∀ (l : List Nat) (p : Bool),
      l.foldl (fun p j => Bool.xor p (taps j && s j)) p = p := by
  intro l
  induction l with
  | nil => intro p; rfl
  | cons x l ih =>
      intro p
      show l.foldl (fun p j => Bool.xor p (taps j && s j))
        (Bool.xor p (taps x && s x)) = p
      rw [hz x, Bool.false_and, Bool.xor_false]
      exact ih p

/-- The `t` bits starting at root offset `m`. -/
def bankRepairDigitOffsetWindow (t : Nat) (ub : Nat → Bool) (m : Nat) :
    Fin t → Bool := fun j => ub (m + j.val)

theorem bankRepairDigitOffsetWindowStep (n t : Nat) (taps ub : Nat → Bool)
    (hrec : ∀ k, t < k → k < n →
      ub k = (List.range t).foldl
        (fun parity j => Bool.xor parity (taps j && ub (k - t + j))) false)
    (m : Nat) (hm : 1 ≤ m) (hmn : m + t < n) :
    bankRepairDigitOffsetWindow t ub (m + 1) =
      recStep t taps (bankRepairDigitOffsetWindow t ub m) := by
  funext i
  unfold recStep
  by_cases hi : i.val + 1 < t
  · rw [dif_pos hi]
    show ub (m + 1 + i.val) = ub (m + (i.val + 1))
    rw [show m + 1 + i.val = m + (i.val + 1) by omega]
  · rw [dif_neg hi]
    have hit : i.val = t - 1 := by have := i.isLt; omega
    have h := hrec (m + t) (by omega) hmn
    rw [Nat.add_sub_cancel] at h
    show ub (m + 1 + i.val) = _
    rw [show m + 1 + i.val = m + t by omega, h]
    exact (bankRepairDigitFinFoldlRange
      (fun parity j => Bool.xor parity (taps j && ub (m + j))) t false).symm

theorem bankRepairDigitOffsetWindowIter (n t : Nat) (taps ub : Nat → Bool)
    (hrec : ∀ k, t < k → k < n →
      ub k = (List.range t).foldl
        (fun parity j => Bool.xor parity (taps j && ub (k - t + j))) false)
    (a : Nat) (ha : 1 ≤ a) :
    ∀ k, a + k + t ≤ n →
      bankRepairDigitOffsetWindow t ub (a + k) =
        recIter t taps k (bankRepairDigitOffsetWindow t ub a) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      rw [recIter_succ, ← ih (by omega)]
      exact bankRepairDigitOffsetWindowStep n t taps ub hrec (a + k)
        (by omega) (by omega)

/-- The certificate-word equations in root offsets give, from every
follower offset `a` with no root within `L`, two delimiters within
`L = 2 r + t - 2` steps (primitive taps); with zero taps they are
contradictory. -/
theorem bankRepairDigitOffsetStop (n t : Nat) (taps ub bb : Nat → Bool)
    (ht : 2 ≤ t)
    (htaps : IsPrimitive t taps ∨ ∀ j, taps j = false)
    (hrec : ∀ k, t < k → k < n →
      ub k = (List.range t).foldl
        (fun parity j => Bool.xor parity (taps j && ub (k - t + j))) false)
    (hnz : ∀ k, t < k → k < n →
      (List.range t).foldl (fun z j => z || ub (k - t + j)) false = true)
    (hmk : ∀ k, t ≤ k → k < n →
      bb k = ((List.range t).foldl
        (fun a j => if j = 0 then a else a && ub (k - t + j)) true && ub k))
    (L : Nat) (hL : 2 * (2 ^ t - 1) + t - 2 ≤ L)
    (a : Nat) (ha : 1 ≤ a) (haL : a + L < n) :
    ∃ k, 1 ≤ k ∧ k ≤ L ∧ bb (a + k) = true ∧
      ∃ k', 1 ≤ k' ∧ k' < k ∧ bb (a + k') = true := by
  have hpow := bankRepairDigitPowLower t
  have hnzw : ∀ m, 1 ≤ m → m + t < n →
      ∃ j : Fin t, bankRepairDigitOffsetWindow t ub m j = true := by
    intro m hm hmn
    have h := hnz (m + t) (by omega) hmn
    rw [Nat.add_sub_cancel] at h
    rcases bankRepairDigitOrFoldTrue (fun j => ub (m + j)) _ _ h with
      h0 | ⟨j, hj, hs⟩
    · exact absurd h0 (by decide)
    · exact ⟨⟨j, List.mem_range.mp hj⟩, hs⟩
  have hmkw : ∀ m, 1 ≤ m → m + t - 1 < n →
      bankRepairDigitOffsetWindow t ub m = (fun _ => true) →
      bb (m + t - 1) = true := by
    intro m hm hmn hw
    have hall : ∀ j, j < t → ub (m + j) = true :=
      fun j hj => congrFun hw ⟨j, hj⟩
    rw [hmk (m + t - 1) (by omega) hmn]
    rw [show m + t - 1 - t = m - 1 by omega]
    rw [bankRepairDigitTrailFoldTrue (fun j => ub (m - 1 + j))
      (List.range t) true ?_]
    · rw [show m + t - 1 = m + (t - 1) by omega, hall (t - 1) (by omega)]
      rfl
    · intro j hj hj0
      have := List.mem_range.mp hj
      show ub (m - 1 + j) = true
      rw [show m - 1 + j = m + (j - 1) by omega]
      exact hall _ (by omega)
  have hnz0 := hnzw a ha (by omega)
  rcases htaps with hp | hz
  · obtain ⟨k0, hk0, hk0v⟩ := isPrimitive_orbit_covers hp
      (bankRepairDigitOffsetWindow t ub a) (fun _ => true) hnz0
      ⟨⟨0, by omega⟩, rfl⟩
    have hper := (hp (bankRepairDigitOffsetWindow t ub a) hnz0).1
    have hw1 : bankRepairDigitOffsetWindow t ub (a + k0) = fun _ => true := by
      rw [bankRepairDigitOffsetWindowIter n t taps ub hrec a ha k0 (by omega)]
      exact hk0v
    have hw2 : bankRepairDigitOffsetWindow t ub (a + (k0 + (2 ^ t - 1))) =
        fun _ => true := by
      rw [bankRepairDigitOffsetWindowIter n t taps ub hrec a ha
          (k0 + (2 ^ t - 1)) (by omega),
        bankRepairDigitRecIterAdd, hper]
      exact hk0v
    have hb1 := hmkw (a + k0) (by omega) (by omega) hw1
    have hb2 := hmkw (a + (k0 + (2 ^ t - 1))) (by omega) (by omega) hw2
    refine ⟨k0 + (2 ^ t - 1) + (t - 1), by omega, by omega, ?_,
      k0 + (t - 1), by omega, by omega, ?_⟩
    · rw [show a + (k0 + (2 ^ t - 1) + (t - 1)) =
          a + (k0 + (2 ^ t - 1)) + t - 1 by omega]
      exact hb2
    · rw [show a + (k0 + (t - 1)) = a + k0 + t - 1 by omega]
      exact hb1
  · have hwt := bankRepairDigitOffsetWindowIter n t taps ub hrec a ha t
      (by omega)
    obtain ⟨j, hj⟩ := hnzw (a + t) (by omega) (by omega)
    rw [hwt, bankRepairDigitZeroTapsIter t taps hz t _ j (by omega)] at hj
    exact absurd hj (by decide)

/-- With zero taps the certificate-word equations are contradictory
as soon as `2 t + 1 < n`. -/
theorem bankRepairDigitZeroTapsWordEmpty (n t : Nat) (taps ub : Nat → Bool)
    (ht : 1 ≤ t) (hz : ∀ j, taps j = false)
    (hrec : ∀ k, t < k → k < n →
      ub k = (List.range t).foldl
        (fun parity j => Bool.xor parity (taps j && ub (k - t + j))) false)
    (hnz : ∀ k, t < k → k < n →
      (List.range t).foldl (fun z j => z || ub (k - t + j)) false = true)
    (hn : 2 * t + 1 < n) : False := by
  have h0 : ∀ j, j < t → ub (t + 1 + j) = false := by
    intro j hj
    rw [hrec (t + 1 + j) (by omega) (by omega)]
    exact bankRepairDigitXorFoldZeroTaps taps
      (fun i => ub (t + 1 + j - t + i)) hz _ false
  rcases bankRepairDigitOrFoldTrue (fun j => ub (2 * t + 1 - t + j)) _ _
      (hnz (2 * t + 1) (by omega) hn) with h | ⟨j, hj, hs⟩
  · exact absurd h (by decide)
  · have hj' := List.mem_range.mp hj
    have hs' : ub (t + 1 + j) = true := by
      rw [show t + 1 + j = 2 * t + 1 - t + j by omega]
      exact hs
    rw [h0 j hj'] at hs'
    exact absurd hs' (by decide)

theorem bankRepairDigitShiftWalk {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (a k : Nat) :
    bankRepairDigitRightWalk ring k (PPL.shiftRight ring root a) =
      PPL.shiftRight ring root (a + k) := by
  rw [bankRepairDigitWalkSite]
  apply Fin.ext
  show ((root.val + a) % n + k) % n = (root.val + (a + k)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem bankRepairDigitShiftOffset {n : Nat} (ring : DirectedRing n)
    (root i : Fin n) :
    PPL.shiftRight ring root (PPL.cyclicOffset ring root i) = i := by
  apply Fin.ext
  show (root.val + (i.val + n - root.val) % n) % n = i.val
  have hr := root.isLt
  rw [Nat.add_mod_mod,
    show root.val + (i.val + n - root.val) = i.val + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem bankRepairDigitShiftZero {n : Nat} (ring : DirectedRing n)
    (root : Fin n) : PPL.shiftRight ring root 0 = root := by
  apply Fin.ext
  show (root.val + 0) % n = root.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt root.isLt]

theorem bankRepairDigitShiftFull {n : Nat} (ring : DirectedRing n)
    (root : Fin n) : PPL.shiftRight ring root n = root := by
  apply Fin.ext
  show (root.val + n) % n = root.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt root.isLt]

theorem bankRepairDigitShiftNeRoot {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (m : Nat) (h0 : 0 < m) (hm : m < n) :
    PPL.shiftRight ring root m ≠ root := by
  intro h
  have hv := congrArg Fin.val h
  change (root.val + m) % n = root.val at hv
  have hr := root.isLt
  by_cases hlt : root.val + m < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega

/-- The BANK width, taps and `L_t` facts. -/
theorem bankRepairDigitBankTaps {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 ≤ (compileAdvice (ceilLogTwo n)).t ∧
      (IsPrimitive (compileAdvice (ceilLogTwo n)).t
          (compileAdvice (ceilLogTwo n)).taps ∨
        ∀ j, (compileAdvice (ceilLogTwo n)).taps j = false) ∧
      2 * (2 ^ (compileAdvice (ceilLogTwo n)).t - 1) +
          (compileAdvice (ceilLogTwo n)).t - 2 ≤
        bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)) := by
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have ht : (compileAdvice (ceilLogTwo n)).t =
      ceilLogTwo (ceilLogTwo n) :=
    compileAdvice_t_large _ (by omega)
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two _ (by omega)
  refine ⟨ht2, ?_, ?_⟩
  · left
    exact tapTablePrimitive _ ht2
  · unfold bankRepairDigitLeadingLength bankRepairDigitRadius
    rw [ht] <;> exact Nat.le_refl _

/-- T7 (b): the certificate-word equations of the visible word at the
native root give the stop clause at every site. -/
theorem bankRepairDigitNonRootStopOfWordValues {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (root : Fin n)
    (hroot : (start.val.1 root).l = true)
    (hv : AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (piW start.val.1))
    (site : Fin n) :
    BankRepairDigitNonRootStop ring hbank start site := by
  intro hl _
  obtain ⟨ht2, htaps, hL⟩ := bankRepairDigitBankTaps hbank
  obtain ⟨a, ha⟩ : ∃ a, a = PPL.cyclicOffset ring root site := ⟨_, rfl⟩
  have hsite : PPL.shiftRight ring root a = site := by
    rw [ha]
    exact bankRepairDigitShiftOffset ring root site
  have han : a < n := by
    rw [ha]
    exact Nat.mod_lt _ ring.hn
  have ha1 : 1 ≤ a := by
    by_cases h0 : a = 0
    · exfalso
      have hs : site = root := by
        rw [← hsite, h0]
        exact bankRepairDigitShiftZero ring root
      rw [hs] at hl
      have h' : (start.val.1 root).l = false := hl
      rw [hroot] at h'
      exact absurd h' (by decide)
    · omega
  have hwalk : ∀ k, bankRepairDigitRightWalk ring k site =
      PPL.shiftRight ring root (a + k) := by
    intro k
    rw [← hsite]
    exact bankRepairDigitShiftWalk ring root a k
  by_cases hreach :
      n ≤ a + bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n))
  · refine ⟨n - a, by omega, by omega, Or.inl ?_⟩
    rw [hwalk, show a + (n - a) = n by omega, bankRepairDigitShiftFull ring root]
    exact hroot
  · obtain ⟨k, hk1, hkL, hb, k', hk1', hk', hb'⟩ :=
      bankRepairDigitOffsetStop n (compileAdvice (ceilLogTwo n)).t
        (compileAdvice (ceilLogTwo n)).taps
        (fun k => AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root
          (piW start.val.1) k)
        (fun k => AcceptedReceipts.WordEntrance.CleanWorker.cwMarker ring root
          (piW start.val.1) k)
        ht2 htaps
        (fun k h1 h2 => hv.recurrence ⟨k, h2⟩ h1)
        (fun k h1 h2 => hv.laterNonzero ⟨k, h2⟩ h1)
        (fun k h1 h2 => hv.markers ⟨k, h2⟩ h1)
        _ hL a ha1 (by omega)
    refine ⟨k, hk1, hkL, Or.inr ⟨?_, Or.inr ⟨k', hk1', hk', ?_⟩⟩⟩
    · rw [hwalk]
      exact hb
    · rw [hwalk]
      exact hb'

/-- The step-1 invariant, stated for the entrance: at every native
leader the visible word satisfies the certificate-word equations
(`CleanWorkerWordValues`, Target.lean:5530). -/
def BankRepairDigitRootWordValues {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∀ root : Fin n, (z.val.1 root).l = true →
    AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (piW z.val.1)

/-- T7 (b) on produced entrances: the missing invariant gives the
non-root stop clause at every site. -/
theorem bankRepairDigitNonRootStopOfProducedWordValues {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hent : BankRepairDigitProducedEntrance ring hbank start)
    (hw : BankRepairDigitRootWordValues ring hbank start) (site : Fin n) :
    BankRepairDigitNonRootStop ring hbank start site := by
  obtain ⟨-, root, hs⟩ := hent
  have hroot : (start.val.1 root).l = true := hs.2.1
  exact bankRepairDigitNonRootStopOfWordValues ring hbank start root hroot
    (hw root hroot) site

theorem bankRepairDigitSingleInheritedLabelTasksOfProducedWordValues
    {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (site : Fin n)
    (hent : BankRepairDigitProducedEntrance ring hbank start)
    (hw : BankRepairDigitRootWordValues ring hbank start) :
    BankRepairDigitSingleInheritedLabelTasks ring hbank start site :=
  bankRepairDigitSingleInheritedLabelTasksOfNonRootStop hn ring hbank start
    site hent
    (bankRepairDigitNonRootStopOfProducedWordValues ring hbank start hent hw
      site)

/-- The class that carries the invariant from the W hit onward:
rooted singleton, `Q_W`, and the word equations at the root. -/
def BankRepairDigitWordValuesClass {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedSingleton ring hbank root z ∧
    AcceptedReceipts.QWord ring (piW z.val.1) ∧
    AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (piW z.val.1)

theorem bankRepairDigitWordValuesClassStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitWordValuesClass ring hbank root z) (e : Fin n) :
    BankRepairDigitWordValuesClass ring hbank root
      (bankRepairNext ring hbank z e) := by
  obtain ⟨hs, hq, hv⟩ := hz
  have hg : ∀ i, (z.val.1 i).grant = false := hs.1.1.2
  have hfire := bankRepairDigitOldFireNoneOfGrantFree _ _
    (hg e) (hg (ring.rightNeighbor e))
  have hproj := bankRepairDigitWordProjectionOfNoFire ring hbank z e hfire
  refine ⟨bankPostInheritedSingletonClosed ring hn hbank root z hs e, ?_, ?_⟩
  · rw [hproj]
    exact (AcceptedReceipts.qword_step ring _ hq e).2
  · rw [hproj]
    exact AcceptedReceipts.WordEntrance.CleanWorker.cleanWorkerWordValues_congr
      ring root _ _
      (fun i => AcceptedReceipts.qword_visible_fixed ring _ hq e i) hv

theorem bankRepairDigitWordValuesClassRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) :
    ∀ (word : List (Fin n)) (x : BankReferenceState ring hbank),
      BankRepairDigitWordValuesClass ring hbank root x →
      BankRepairDigitWordValuesClass ring hbank root
        (word.foldl (bankRepairNext ring hbank) x) := by
  intro word
  induction word with
  | nil => intro x hx; exact hx
  | cons e rest ih =>
      intro x hx
      exact ih (bankRepairNext ring hbank x e)
        (bankRepairDigitWordValuesClassStep ring hn hbank root x hx e)

/-- T7 on the actual chain: if the W stage leaves the word equations
at its hit (`BankRepairWord` plus `BankRepairDigitRootWordValues`),
then every later R-fold entrance retires the single inherited label
at every site. The W stage (`BankRepairWordStage`) must establish
`BankRepairDigitRootWordValues` at its hit. -/
theorem bankRepairDigitSingleInheritedLabelTasksOfPreparedWordValues
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (wordW : List (Fin n))
    (hW : BankRepairWord ring hbank
      (wordW.foldl (bankRepairNext ring hbank) x))
    (hwv : BankRepairDigitRootWordValues ring hbank
      (wordW.foldl (bankRepairNext ring hbank) x))
    (wordR : List (Fin n))
    (hR : BankRepairRFoldEstablished ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x))) :
    ∀ site, BankRepairDigitSingleInheritedLabelTasks ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x)) site := by
  obtain ⟨root, hs, -⟩ := hx
  have hsy := bankRepairDigitPostInheritedSingletonRun ring hn hbank root
    wordW x hs
  have hqy := bankRepairDigitWordSafeOfFactor ring hbank _ hW
  have hroot : ((wordW.foldl (bankRepairNext ring hbank) x).val.1 root).l =
      true := hsy.2.1
  have hz := bankRepairDigitWordValuesClassRun ring hn hbank root wordR _
    ⟨hsy, hqy, hwv root hroot⟩
  have hent : BankRepairDigitProducedEntrance ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x)) := ⟨hR, root, hz.1⟩
  intro site
  exact bankRepairDigitSingleInheritedLabelTasksOfNonRootStop hn ring hbank
    _ site hent
    (bankRepairDigitNonRootStopOfWordValues ring hbank _ root hz.1.2.1
      hz.2.2 site)

/-- The equations the literal W rows publish (Target.lean:3477):
`u = (if OR window then tap parity else 1)`, `beta = trailing AND && u`. -/
def BankRepairDigitKickWord (n t : Nat) (taps ub bb : Nat → Bool) : Prop :=
  ∀ k, t < k → k < n →
    ub k = (if (List.range t).foldl (fun z j => z || ub (k - t + j)) false
      then (List.range t).foldl
        (fun parity j => Bool.xor parity (taps j && ub (k - t + j))) false
      else true) ∧
    bb k = ((List.range t).foldl
      (fun a j => if j = 0 then a else a && ub (k - t + j)) true && ub k)

/-- With zero taps the literal rows write no delimiter after offset `t`. -/
theorem bankRepairDigitKickWordNoDelimiter (n t : Nat)
    (taps ub bb : Nat → Bool) (ht : 2 ≤ t) (hz : ∀ j, taps j = false)
    (hK : BankRepairDigitKickWord n t taps ub bb) :
    ∀ k, t < k → k < n → bb k = false := by
  intro k h1 h2
  obtain ⟨hu, hb⟩ := hK k h1 h2
  rw [hb]
  cases hor : (List.range t).foldl (fun z j => z || ub (k - t + j)) false with
  | true =>
      rw [hor, if_pos rfl,
        bankRepairDigitXorFoldZeroTaps taps (fun j => ub (k - t + j)) hz]
        at hu
      rw [hu, Bool.and_false]
  | false =>
      have hall := (bankRepairDigitOrFoldFalse (fun j => ub (k - t + j))
        _ _ hor).2
      have hlast : ub (k - t + (t - 1)) = false :=
        hall (t - 1) (List.mem_range.mpr (by omega))
      rw [bankRepairDigitTrailFoldFalse (fun j => ub (k - t + j)) _ true
        (t - 1) (List.mem_range.mpr (by omega)) (by omega) hlast,
        Bool.false_and]

/-- Hence, on the word the literal rows write with zero taps, a SEEK
or ZERO label at any offset `a ≥ t` with `a + L < n` has no stop
within `L` services. -/
theorem bankRepairDigitKickWordNoStop {n : Nat} (ring : DirectedRing n)
    (t : Nat) (taps ub : Nat → Bool) (ht : 2 ≤ t)
    (hz : ∀ j, taps j = false)
    (root : Fin n) (R B : Fin n → Bool)
    (hR : ∀ i, R i = true → i = root)
    (hK : BankRepairDigitKickWord n t taps ub
      (fun m => B (PPL.shiftRight ring root m)))
    (L a : Nat) (ha : t ≤ a) (haL : a + L < n) (seek : Bool) :
    ∀ k, 1 ≤ k → k ≤ L →
      ¬ bankRepairDigitLabelStop ring R B
        (PPL.shiftRight ring root a) seek k := by
  intro k hk1 hkL hstop
  unfold bankRepairDigitLabelStop at hstop
  rw [bankRepairDigitShiftWalk] at hstop
  rcases hstop with hr | ⟨hb, -⟩
  · exact bankRepairDigitShiftNeRoot ring root (a + k) (by omega) (by omega)
      (hR _ hr)
  · have h0 : B (PPL.shiftRight ring root (a + k)) = false :=
      bankRepairDigitKickWordNoDelimiter n t taps ub _ ht hz hK (a + k)
        (by omega) (by omega)
    rw [h0] at hb
    exact absurd hb (by decide)

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-! ### T8: the W-run invariant missing at DONE

`BankRepairWordStage` (BankFinishRepair.lean:160) is a hitting-time
bound into `BankRepairWord` = `AcceptedWord` (Target.lean:3958): an
existential W history from `initializesWord` (Target.lean:3049) whose
last control passes `acceptsWord` (Target.lean:2978). That gives DONE,
the receipt census and `QWord`, but no word value and no tie between the
monitor root and the leader bits at the cut.

The invariant below is the first one missing at DONE: every issued
publication receipt certifies its word equation, and the monitor root
is the fixed leader. It holds at initialization and after every clear
or launch, survives every step that leaves the visible word and the
receipts fixed, and follows from the existing DONE certificate.
Carried along the W runs, it gives `BankRepairDigitRootWordValues` at
the W hit, which is where
`bankRepairDigitSingleInheritedLabelTasksOfPreparedWordValues` starts. -/

/-- Receipts certify values; the monitor root is the fixed leader. -/
structure BankRepairDigitWordPublished {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop where
  rootFixed : WFixedRoot ring h.root p
  prefixZeros : ∀ k : Fin n, 0 < k.val → k.val < c.t →
    h.publications (PPL.shiftRight ring h.root k.val) = .prefixZero →
    cwMarker ring h.root p k.val = false
  firstWindow : ∀ k : Fin n, k.val = c.t →
    h.publications (PPL.shiftRight ring h.root k.val) = .prefixEnd →
    cwPrefixOr ring h.root p c.t = true ∧
      cwMarker ring h.root p k.val =
        (cwSumTrailing ring h.root p k.val c.t &&
          cwBit ring h.root p k.val)
  /-- A `.recurrence` receipt certifies what S1 writes (CertRows.lean,
  row S1: `v := if z == false then true else p`, `betaY := a && v`):
  either the window is nonzero and the bit is the tap parity, or the
  window is all zero and the bit was forced to `true`. -/
  laterWindows : ∀ k : Fin n, c.t < k.val →
    h.publications (PPL.shiftRight ring h.root k.val) = .recurrence →
    ((cwSumOr ring h.root p k.val c.t = true ∧
        cwBit ring h.root p k.val = cwSumParity ring h.root p k.val c.t) ∨
      (cwSumOr ring h.root p k.val c.t = false ∧
        cwBit ring h.root p k.val = true)) ∧
      cwMarker ring h.root p k.val =
        (cwSumTrailing ring h.root p k.val c.t &&
          cwBit ring h.root p k.val)

/-- The all-zero window is fixed by the recurrence. -/
theorem bankRepairDigitRecIterZeroWindow (t : Nat) (taps : Nat → Bool) :
    ∀ k, recIter t taps k (fun _ => false) = fun _ => false := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [recIter_succ, ih]
      funext i
      unfold recStep
      split
      · rfl
      · show Fin.foldl t (fun acc (j : Fin t) =>
            Bool.xor acc (Bool.and (taps j.val) false)) false = false
        have hf : (fun acc (j : Fin t) =>
            Bool.xor acc (Bool.and (taps j.val) false)) =
            fun acc (_ : Fin t) => acc := by
          funext acc j
          simp
        rw [hf]
        exact bankRepairDigitFoldConst t false

/-- Primitive taps: the recurrence maps a nonzero window to a nonzero
window (otherwise the period `2^t - 1` would return to zero). This is
the only use of primitivity in the forced-window repair. -/
theorem bankRepairDigitRecStepNonzero {t : Nat} {taps : Nat → Bool}
    (hp : IsPrimitive t taps) (ht : 1 ≤ t) (w : Fin t → Bool)
    (hw : ∃ i, w i = true) : ∃ i, recStep t taps w i = true := by
  apply Classical.byContradiction
  intro hne
  have hz : recStep t taps w = fun _ => false := by
    funext i
    cases hv : recStep t taps w i with
    | false => rfl
    | true => exact absurd ⟨i, hv⟩ hne
  have hper := (hp w hw).1
  have hpow := bankRepairDigitPowLower t
  rw [show 2 ^ t - 1 = (2 ^ t - 1 - 1) + 1 by omega,
    bankRepairDigitRecIterAdd t taps (2 ^ t - 1 - 1) 1] at hper
  have h1 : recIter t taps 1 w = recStep t taps w := rfl
  rw [h1, hz, bankRepairDigitRecIterZeroWindow] at hper
  obtain ⟨i, hi⟩ := hw
  rw [← hper] at hi
  exact Bool.false_ne_true hi

/-- Forced-window lemma: if the first follower window (offsets
`1..t`) is nonzero and every nonzero window is followed by its tap
parity, then (primitive taps) no window `m..m+t-1` inside the ring is
all zero, so the forced S1 branch never fires. -/
theorem bankRepairDigitKickWindowNonzero (n t : Nat) (taps ub : Nat → Bool)
    (ht : 1 ≤ t) (hp : IsPrimitive t taps)
    (hfirst : ∃ j, j < t ∧ ub (j + 1) = true)
    (hkick : ∀ k, t < k → k < n →
      (List.range t).foldl (fun z j => z || ub (k - t + j)) false = true →
      ub k = (List.range t).foldl
        (fun parity j => Bool.xor parity (taps j && ub (k - t + j))) false) :
    ∀ d, 1 + d + t ≤ n →
      ∃ j : Fin t, bankRepairDigitOffsetWindow t ub (1 + d) j = true := by
  intro d
  induction d with
  | zero =>
      intro _
      obtain ⟨j, hj, hu⟩ := hfirst
      refine ⟨⟨j, hj⟩, ?_⟩
      show ub (1 + 0 + j) = true
      rw [show 1 + 0 + j = j + 1 by omega]
      exact hu
  | succ d ih =>
      intro hd
      obtain ⟨j, hj⟩ := ih (by omega)
      have hor : (List.range t).foldl
          (fun z i => z || ub (1 + d + t - t + i)) false = true := by
        cases hf : (List.range t).foldl
            (fun z i => z || ub (1 + d + t - t + i)) false with
        | true => rfl
        | false =>
            have hall := (bankRepairDigitOrFoldFalse
              (fun i => ub (1 + d + t - t + i)) _ _ hf).2 j.val
              (List.mem_range.mpr j.isLt)
            have h2 : ub (1 + d + t - t + j.val) = false := hall
            have h3 : ub (1 + d + j.val) = true := hj
            rw [show 1 + d + t - t + j.val = 1 + d + j.val by omega, h3] at h2
            exact absurd h2 (by decide)
      have hk := hkick (1 + d + t) (by omega) (by omega) hor
      rw [show 1 + d + t - t = 1 + d by omega] at hk
      have hstep : bankRepairDigitOffsetWindow t ub (1 + d + 1) =
          recStep t taps (bankRepairDigitOffsetWindow t ub (1 + d)) := by
        funext i
        unfold recStep
        by_cases hi : i.val + 1 < t
        · rw [dif_pos hi]
          show ub (1 + d + 1 + i.val) = ub (1 + d + (i.val + 1))
          rw [show 1 + d + 1 + i.val = 1 + d + (i.val + 1) by omega]
        · rw [dif_neg hi]
          have hit : i.val = t - 1 := by have := i.isLt; omega
          show ub (1 + d + 1 + i.val) = _
          rw [show 1 + d + 1 + i.val = 1 + d + t by omega, hk]
          exact (bankRepairDigitFinFoldlRange
            (fun parity j => Bool.xor parity (taps j && ub (1 + d + j)))
            t false).symm
      obtain ⟨i, hi⟩ := bankRepairDigitRecStepNonzero hp ht _ ⟨j, hj⟩
      refine ⟨i, ?_⟩
      rw [show 1 + (d + 1) = 1 + d + 1 by omega, hstep]
      exact hi

/-- At a control whose receipt census is complete (the A0 guard and
the `acceptsWord` census), the invariant is the full word equations. -/
theorem bankRepairDigitWordValuesOfPublished {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hpub : BankRepairDigitWordPublished ring h p)
    (hall : BlockA.wordAllPublished ring h)
    (ht : 0 < c.t) (htn : c.t < n) (hprim : IsPrimitive c.t c.taps) :
    CleanWorkerWordValues ring h.root p := by
  have hlater : ∀ k : Fin n, c.t < k.val →
      ((cwSumOr ring h.root p k.val c.t = true ∧
          cwBit ring h.root p k.val = cwSumParity ring h.root p k.val c.t) ∨
        (cwSumOr ring h.root p k.val c.t = false ∧
          cwBit ring h.root p k.val = true)) ∧
        cwMarker ring h.root p k.val =
          (cwSumTrailing ring h.root p k.val c.t &&
            cwBit ring h.root p k.val) := by
    intro k hk
    have hn1 : ¬ k.val < c.t := by omega
    have hn2 : ¬ k.val = c.t := by omega
    have h1 := hall k (by omega)
    dsimp only at h1
    rw [if_neg hn1, if_neg hn2] at h1
    exact hpub.laterWindows k hk h1.1
  have hfirst : cwPrefixOr ring h.root p c.t = true := by
    obtain ⟨k, hk⟩ : ∃ k : Fin n, k.val = c.t := ⟨⟨c.t, htn⟩, rfl⟩
    have hn1 : ¬ k.val < c.t := by omega
    have h1 := hall k (by omega)
    dsimp only at h1
    rw [if_neg hn1, if_pos hk] at h1
    exact (hpub.firstWindow k hk h1.1).1
  have hf : ∃ j, j < c.t ∧ cwBit ring h.root p (j + 1) = true := by
    rcases bankRepairDigitOrFoldTrue (fun j => cwBit ring h.root p (j + 1))
        (List.range c.t) false hfirst with h0 | ⟨j, hj, hs⟩
    · exact absurd h0 (by decide)
    · exact ⟨j, List.mem_range.mp hj, hs⟩
  have hnz : ∀ k : Fin n, c.t < k.val →
      cwSumOr ring h.root p k.val c.t = true := by
    intro k hk
    obtain ⟨j, hj⟩ := bankRepairDigitKickWindowNonzero n c.t c.taps
      (fun m => cwBit ring h.root p m) ht hprim hf
      (fun k' h1 h2 hor => by
        rcases (hlater ⟨k', h2⟩ h1).1 with ⟨_, hb⟩ | ⟨hb, _⟩
        · exact hb
        · exact absurd (hb.symm.trans hor) (by decide))
      (k.val - c.t - 1) (by omega)
    cases hor : cwSumOr ring h.root p k.val c.t with
    | true => rfl
    | false =>
        have hall' := (bankRepairDigitOrFoldFalse
          (fun j => cwBit ring h.root p (k.val - c.t + j)) (List.range c.t)
          false hor).2 j.val (List.mem_range.mpr j.isLt)
        have h2 : cwBit ring h.root p (k.val - c.t + j.val) = false := hall'
        have h3 : cwBit ring h.root p (1 + (k.val - c.t - 1) + j.val) =
            true := hj
        rw [show 1 + (k.val - c.t - 1) + j.val = k.val - c.t + j.val by omega,
          h2] at h3
        exact absurd h3 (by decide)
  refine ⟨?_, hfirst, hnz, ?_, ?_⟩
  · intro k hk hlt
    have h1 := hall k hk
    dsimp only at h1
    rw [if_pos hlt] at h1
    exact hpub.prefixZeros k hk hlt h1.1
  · intro k hk
    rcases (hlater k hk).1 with ⟨_, hb⟩ | ⟨hb, _⟩
    · exact hb
    · rw [hnz k hk] at hb
      exact absurd hb (by decide)
  · intro k hk
    have hn1 : ¬ k.val < c.t := by omega
    have h1 := hall k (by omega)
    dsimp only at h1
    rw [if_neg hn1] at h1
    by_cases heq : k.val = c.t
    · rw [if_pos heq] at h1
      exact (hpub.firstWindow k heq h1.1).2
    · exact (hlater k (by omega)).2

/-- The full word equations at a fixed root give the invariant. -/
theorem bankRepairDigitWordPublishedOfValues {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (hfix : WFixedRoot ring h.root p)
    (hv : CleanWorkerWordValues ring h.root p) :
    BankRepairDigitWordPublished ring h p :=
  ⟨hfix, fun k hk hlt _ => hv.prefixZeros k hk hlt,
    fun k hk _ => ⟨hv.firstNonzero, hv.markers k (by omega)⟩,
    fun k hk _ => ⟨Or.inl ⟨hv.laterNonzero k hk, hv.recurrence k hk⟩,
      hv.markers k (by omega)⟩⟩

/-- The existing DONE certificate implies the invariant. -/
theorem bankRepairDigitWordPublishedOfPhaseDone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (hdone : h.phase = .done)
    (inv : CleanWorkerPhaseInv ring h p) :
    BankRepairDigitWordPublished ring h p := by
  have hv := (cwPhaseDoneValues ring h p hdone inv).1
  have hfix : WFixedRoot ring h.root p := by
    cases inv with
    | «prefix» hp =>
        rcases hp with ⟨_, _, _, _, hw, _⟩
        cases hw.symm.trans hdone
    | back hb =>
        rcases hb with ⟨_, _, _, hw, _⟩
        cases hw.symm.trans hdone
    | sum hs =>
        rcases hs with ⟨_, _, _, _, _, _, hw, _⟩
        cases hw.symm.trans hdone
    | ready hr =>
        rcases hr with ⟨_, hw, _⟩
        cases hw.symm.trans hdone
    | done _ full => exact full.rootFixed
  exact bankRepairDigitWordPublishedOfValues ring h p hfix hv

/-- With no receipt issued, the invariant is root fixity alone. -/
theorem bankRepairDigitWordPublishedOfAbsent {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (hfix : WFixedRoot ring h.root p)
    (habs : ∀ i, h.publications i = .absent) :
    BankRepairDigitWordPublished ring h p := by
  refine ⟨hfix, ?_, ?_, ?_⟩
  · intro k _ _ hk
    rw [habs] at hk
    cases hk
  · intro k _ hk
    rw [habs] at hk
    cases hk
  · intro k _ hk
    rw [habs] at hk
    cases hk

/-- Base case: every `initializesWord` origin satisfies it. -/
theorem bankRepairDigitWordPublishedOfInit {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (origin : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (hinit : BlockA.initializesWord ring origin γ₀)
    (shadow : Fin n → ProjW c) (h : BlockA.WordControl n c)
    (hγ : γ₀ = .live shadow h) :
    BankRepairDigitWordPublished ring h origin := by
  obtain ⟨root, h', hγ', hroot, hfix, -, -, -, -, hcl, -, -⟩ := hinit
  have hh : h = h' := by
    rw [hγ] at hγ'
    injection hγ' with _ h2
  rw [hh]
  refine bankRepairDigitWordPublishedOfAbsent ring h' origin ?_
    (fun i => (hcl i).2.2.2.2.1)
  rw [hroot]
  exact hfix

/-- Every cancellation (`wordClear`) re-establishes it. -/
theorem bankRepairDigitWordPublishedOfClear {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (request : Bool) (p : Fin n → ProjW c)
    (hfix : WFixedRoot ring h.root p) :
    BankRepairDigitWordPublished ring (BlockA.wordClear h request) p :=
  bankRepairDigitWordPublishedOfAbsent ring _ p hfix (fun _ => rfl)

/-- The hard launch (`wordHardLaunch`) re-establishes it. -/
theorem bankRepairDigitWordPublishedOfHardLaunch {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (e j : Fin n) (p : Fin n → ProjW c)
    (hfix : WFixedRoot ring h.root p) :
    BankRepairDigitWordPublished ring (BlockA.wordHardLaunch h e j) p :=
  bankRepairDigitWordPublishedOfAbsent ring _ p hfix (fun _ => rfl)

/-- The worker launch (`wordWorkerLaunch`, I0) re-establishes it. -/
theorem bankRepairDigitWordPublishedOfWorkerLaunch {n : Nat}
    {c : Compiled} (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (hfix : WFixedRoot ring h.root p) :
    BankRepairDigitWordPublished ring (BlockA.wordWorkerLaunch h) p :=
  bankRepairDigitWordPublishedOfAbsent ring _ p hfix (fun _ => rfl)

/-- Frame: a step that keeps the visible word, the root and every
receipt (or drops it) preserves the invariant. This covers every
non-publishing control update (B0, B1, S0, A1, A0, frame, erase) and
the frozen DONE phase, provided the physical edge keeps u/beta. -/
theorem bankRepairDigitWordPublishedFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c)
    (hpub : BankRepairDigitWordPublished ring h p)
    (hroot : h'.root = h.root)
    (hfix : WFixedRoot ring h'.root p')
    (hv : ∀ i, AcceptedReceipts.wordVisible p' i =
      AcceptedReceipts.wordVisible p i)
    (hrec : ∀ i, h'.publications i = h.publications i ∨
      h'.publications i = .absent) :
    BankRepairDigitWordPublished ring h' p' := by
  have hb : ∀ k, cwBit ring h.root p' k = cwBit ring h.root p k :=
    fun k => congrArg Prod.fst (hv (PPL.shiftRight ring h.root k))
  have hm : ∀ k, cwMarker ring h.root p' k = cwMarker ring h.root p k :=
    fun k => congrArg Prod.snd (hv (PPL.shiftRight ring h.root k))
  have hor : cwPrefixOr ring h.root p' c.t = cwPrefixOr ring h.root p c.t := by
    unfold cwPrefixOr
    simp only [hb]
  have hso : ∀ k, cwSumOr ring h.root p' k c.t =
      cwSumOr ring h.root p k c.t := by
    intro k
    unfold cwSumOr cwSourceBit
    simp only [hb]
  have hsp : ∀ k, cwSumParity ring h.root p' k c.t =
      cwSumParity ring h.root p k c.t := by
    intro k
    unfold cwSumParity cwSourceBit
    simp only [hb]
  have hst : ∀ k, cwSumTrailing ring h.root p' k c.t =
      cwSumTrailing ring h.root p k c.t := by
    intro k
    unfold cwSumTrailing cwSourceBit
    simp only [hb]
  have hpk : ∀ (i : Fin n) (r : BlockA.PublicationReceipt),
      h'.publications i = r → r ≠ .absent → h.publications i = r := by
    intro i r hi hr
    rcases hrec i with he | he
    · rw [← he]
      exact hi
    · exact absurd (he.symm.trans hi) (Ne.symm hr)
  refine ⟨hfix, ?_, ?_, ?_⟩
  · intro k hk hlt hp
    rw [hroot] at hp ⊢
    rw [hm]
    exact hpub.prefixZeros k hk hlt (hpk _ _ hp (by decide))
  · intro k hk hp
    rw [hroot] at hp ⊢
    rw [hor, hm, hst, hb]
    exact hpub.firstWindow k hk (hpk _ _ hp (by decide))
  · intro k hk hp
    rw [hroot] at hp ⊢
    rw [hso, hb, hsp, hm, hst]
    exact hpub.laterWindows k hk (hpk _ _ hp (by decide))

/-- The W-run invariant as a Prop: it holds at every live control of
every projected W run from `initializesWord`. Base case:
`bankRepairDigitWordPublishedOfInit`; clears/launches/frames: above.
Open: the publishing rows P1, P3 and S1 (S1 first without proof) and
visible fixity at the non-publishing steps, incl. after DONE. -/
def BankRepairDigitWordRunPublished {n : Nat}
    (ring : DirectedRing n) (c : Compiled) : Prop :=
  ∀ (origin p : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (w : List (Fin n)) (shadow : Fin n → ProjW c)
    (h : BlockA.WordControl n c),
    BlockA.initializesWord ring origin γ₀ →
    BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
      (.live shadow h) →
    BankRepairDigitWordPublished ring h p

/-- Sufficiency at the W acceptance cut: the accepted word satisfies
the certificate-word equations at a root which is its fixed leader. -/
theorem bankRepairDigitWordValuesOfAccepted {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (hrun : BankRepairDigitWordRunPublished ring c)
    (hprim : IsPrimitive c.t c.taps)
    (p : Fin n → ProjW c)
    (hacc : AcceptedReceipts.AcceptedWord ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) p) :
    ∃ root, WFixedRoot ring root p ∧
      CleanWorkerWordValues ring root p := by
  obtain ⟨_, origin, γ₀, w, γ, hinit, hr, hacc⟩ := hacc
  cases γ with
  | failed => exact False.elim hacc.1
  | live shadow h =>
      have hpub := hrun origin p γ₀ w shadow h hinit hr
      obtain ⟨_, _, _, _, _, ht2, htn, _⟩ := hinit
      have hpow := bankRepairDigitPowLower c.t
      have hall : BlockA.wordAllPublished ring h := hacc.1.2.2.2.1
      exact ⟨h.root, hpub.rootFixed,
        bankRepairDigitWordValuesOfPublished ring h p hpub hall
          (by omega) (by omega) hprim⟩

/-- At the W hit the BANK state satisfies the T7 invariant: every
leader is the accepted W root (WFixedRoot), whose word equations hold. -/
theorem bankRepairDigitRootWordValuesOfWordRun {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrun : BankRepairDigitWordRunPublished ring
      (compileAdvice (ceilLogTwo n)))
    (y : BankReferenceState ring hbank)
    (hW : BankRepairWord ring hbank y) :
    BankRepairDigitRootWordValues ring hbank y := by
  have hprim : IsPrimitive (compileAdvice (ceilLogTwo n)).t
      (compileAdvice (ceilLogTwo n)).taps :=
    tapTablePrimitive _ (bankRepairDigitBankTaps hbank).1
  obtain ⟨r, hfix, hv⟩ :=
    bankRepairDigitWordValuesOfAccepted ring hrun hprim (piW y.val.1) hW
  intro root hroot
  have hr : root = r := hfix.2.1 root hroot
  rw [hr]
  exact hv

/-- T8 on the actual chain, conditional only on the W-run invariant:
every R-fold entrance reached after the W stage retires the single
inherited label at every site. -/
theorem bankRepairDigitSingleInheritedLabelTasksOfWordRunPublished
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrun : BankRepairDigitWordRunPublished ring
      (compileAdvice (ceilLogTwo n)))
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (wordW : List (Fin n))
    (hW : BankRepairWord ring hbank
      (wordW.foldl (bankRepairNext ring hbank) x))
    (wordR : List (Fin n))
    (hR : BankRepairRFoldEstablished ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x))) :
    ∀ site, BankRepairDigitSingleInheritedLabelTasks ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x)) site :=
  bankRepairDigitSingleInheritedLabelTasksOfPreparedWordValues ring hn
    hbank x hx wordW hW
    (bankRepairDigitRootWordValuesOfWordRun ring hbank hrun _ hW)
    wordR hR

/-- Row classification used for `siStep`: a publishing row, or u/beta
are copied. -/
def BankRepairDigitSiQuietOrPublishing {c : Compiled} (ox oy : Agent c)
    (r : SIResult c.t) : Prop :=
  r.row = "P1" ∨ r.row = "P2" ∨ r.row = "P3" ∨ r.row = "S1" ∨
    (r.uX = ox.u ∧ r.uY = oy.u ∧ r.betaX = ox.beta ∧ r.betaY = oy.beta)

theorem bankRepairDigitIteMotive {α : Type} {Q : α → Prop} {p : Prop}
    [Decidable p] {a b : α} (ha : Q a) (hb : Q b) :
    Q (if p then a else b) := by
  by_cases hp : p
  · rw [if_pos hp]
    exact ha
  · rw [if_neg hp]
    exact hb

/-- Only the rows P1, P2, P3 and S1 of `siStep` (CertRows.lean:357)
write u or beta; every other row copies them. -/
theorem bankRepairDigitSiStepVisible (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (h1 : (siStep c ox oy post hard).row ≠ "P1")
    (h2 : (siStep c ox oy post hard).row ≠ "P2")
    (h3 : (siStep c ox oy post hard).row ≠ "P3")
    (h4 : (siStep c ox oy post hard).row ≠ "S1") :
    (siStep c ox oy post hard).uX = ox.u ∧
      (siStep c ox oy post hard).uY = oy.u ∧
      (siStep c ox oy post hard).betaX = ox.beta ∧
      (siStep c ox oy post hard).betaY = oy.beta := by
  have hcase : BankRepairDigitSiQuietOrPublishing ox oy
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitIteMotive ?_ ?_
    all_goals first
      | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)))
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases hcase with h | h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact absurd h h4
  · exact h

/-- A projected edge whose worker row is not P1/P2/P3/S1 keeps the
whole visible word. -/
theorem bankRepairDigitQuietRowVisible {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n)
    (h1 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P1")
    (h2 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P2")
    (h3 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P3")
    (h4 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "S1") :
    ∀ i, AcceptedReceipts.wordVisible (phiW ring p e) i =
      AcceptedReceipts.wordVisible p i := by
  have hs := bankRepairDigitSiStepVisible c (p e).lift
    (p (ring.rightNeighbor e)).lift
    (postW (p e) (p (ring.rightNeighbor e)))
    (serW (p e) (p (ring.rightNeighbor e))).hard h1 h2 h3 h4
  obtain ⟨hux, huy, hbx, hby⟩ := hs
  intro i
  unfold AcceptedReceipts.wordVisible phiW projectedEdge
  by_cases hie : i = e
  · rw [if_pos hie, hie]
    exact Prod.ext hux hbx
  · rw [if_neg hie]
    by_cases hij : i = ring.rightNeighbor e
    · rw [if_pos hij, hij]
      exact Prod.ext huy hby
    · rw [if_neg hij]

/-- Hence every non-publishing row (I0, I1, P0, B0, B1, S0, A1, A0,
frame) preserves the invariant once its control update keeps the root
and the receipts and the leader stays fixed. The open cases are the
publishing rows P1, P3, S1 (P2 always cancels the monitor). -/
theorem bankRepairDigitWordPublishedQuietRow {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hpub : BankRepairDigitWordPublished ring h p)
    (h1 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P1")
    (h2 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P2")
    (h3 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P3")
    (h4 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "S1")
    (hroot : h'.root = h.root)
    (hfix : WFixedRoot ring h'.root (phiW ring p e))
    (hrec : ∀ i, h'.publications i = h.publications i ∨
      h'.publications i = .absent) :
    BankRepairDigitWordPublished ring h' (phiW ring p e) :=
  bankRepairDigitWordPublishedFrame ring h h' p (phiW ring p e) hpub hroot
    hfix (bankRepairDigitQuietRowVisible ring p e h1 h2 h3 h4) hrec

end L3.RenewalReferenceClock

/-!
T9 item 1: the P1 row preserves `BankRepairDigitWordPublished` in the
general case. Helpers: the native layer of phiW is literal E (so the
fixed root survives every W step, n >= 3), and the receipt census of a
single `wordT` step (each receipt is kept, dropped, or newly issued by
P1 at j, P3 at e, or S1 at j). See comms/T9-notes.md.
-/

namespace L3.RenewalReferenceClock

open L3.AcceptedReceipts.WordEntrance.CleanWorker

/-- The native layer of a projected W step is literal E. -/
theorem bankRepairDigitPhiWNative {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n) :
    (fun i => ((phiW ring p e) i).native) =
      nativeE ring (fun i => (p i).native) e := by
  funext i
  simp only [phiW, projectedEdge, nativeE, pairW, postW]
  by_cases hie : i = e
  · simp [hie]
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      have hne : ¬ ring.rightNeighbor e = e := hie
      simp [hne]
    · simp [hie, hij]

/-- Every projected W step keeps the fixed root (n >= 3): literal E
creates no leader and preserves PPlus, so the root stays the unique
leader. -/
theorem bankRepairDigitWFixedRootPhiW {n : Nat} {c : Compiled}
    (hn : 3 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hfix : WFixedRoot ring root p) :
    WFixedRoot ring root (phiW ring p e) := by
  have hnat := bankRepairDigitPhiWNative ring p e
  have hold : ∀ i : Fin n, ((phiW ring p e) i).native.l = true →
      (p i).native.l = true := by
    intro i hi
    have hi' : (nativeE ring (fun i => (p i).native) e i).l = true := by
      rw [← hnat]; exact hi
    simp only [nativeE] at hi'
    by_cases hie : i = e
    · rw [if_pos hie] at hi'
      rw [L3.Closure.literalESourceLeader] at hi'
      rw [hie]; exact hi'
    · rw [if_neg hie] at hi'
      by_cases hij : i = ring.rightNeighbor e
      · rw [if_pos hij] at hi'
        rw [hij]
        exact L3.Closure.literalEDestinationLeaderOnlyOld _ _ hi'
      · rw [if_neg hij] at hi'
        exact hi'
  have hpp : Protected ring (fun i => ((phiW ring p e) i).native) := by
    rw [hnat]
    exact nativeE_preserves_PPlus hn ring _ e hfix.2.2
  have huniq : ∀ i : Fin n, ((phiW ring p e) i).native.l = true → i = root :=
    fun i hi => hfix.2.1 i (hold i hi)
  refine ⟨?_, huniq, hpp⟩
  obtain ⟨q, hq⟩ := hpp.1
  have hqr : q = root := huniq q hq
  rw [← hqr]
  exact hq

/-- What one W control step can do to the receipt at a site. -/
def BankRepairDigitWordReceiptStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) : Prop :=
  h'.root = h.root ∧ ∀ i : Fin n,
    h'.publications i = h.publications i ∨
    h'.publications i = .absent ∨
    (i = ring.rightNeighbor e ∧
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .prefixMove ∧
      (workerW (p e) (p (ring.rightNeighbor e))).betaY = false ∧
      h'.publications i = .prefixZero) ∨
    (i = e ∧
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .prefixPublish ∧
      h'.publications i = .prefixEnd) ∨
    (i = ring.rightNeighbor e ∧
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .sumPublish ∧
      h'.publications i = .recurrence)

theorem bankRepairDigitWordReceiptStepWorker {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool) :
    BankRepairDigitWordReceiptStep ring h
      (BlockA.wordWorkerNext ring h p e request) p e := by
  unfold BlockA.wordWorkerNext
  dsimp only
  split
  all_goals (rename_i hcase)
  all_goals (repeat' split)
  all_goals first
    | exact ⟨rfl, fun _ => Or.inr (Or.inl rfl)⟩
    | exact ⟨rfl, fun _ => Or.inl rfl⟩
    | skip
  all_goals refine ⟨rfl, fun i => ?_⟩
  all_goals simp only [BlockA.wordPut]
  all_goals by_cases hie : i = e <;> by_cases hij : i = ring.rightNeighbor e
  all_goals simp_all

theorem bankRepairDigitWordReceiptStepValidate {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool) :
    BankRepairDigitWordReceiptStep ring h
      (BlockA.wordValidateNext ring h p e request) p e := by
  unfold BlockA.wordValidateNext
  dsimp only
  split
  all_goals (repeat' split)
  all_goals first
    | exact ⟨rfl, fun _ => Or.inr (Or.inl rfl)⟩
    | exact ⟨rfl, fun _ => Or.inl rfl⟩

/-- Receipt census of the complete W control step `wordT`. -/
theorem bankRepairDigitWordReceiptStepT {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (p' : Fin n → ProjW c) :
    BankRepairDigitWordReceiptStep ring h
      (BlockA.wordT ring h p e p') p e := by
  unfold BlockA.wordT
  split
  · exact ⟨rfl, fun _ => Or.inl rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, fun _ => Or.inr (Or.inl rfl)⟩
    · split
      · exact ⟨rfl, fun _ => Or.inr (Or.inl rfl)⟩
      · exact bankRepairDigitWordReceiptStepValidate ring h p e _
      · exact bankRepairDigitWordReceiptStepWorker ring h p e _
      · exact ⟨rfl, fun _ => Or.inl rfl⟩

theorem bankRepairDigitWorkerCaseOfRow {c : Compiled} (x y : ProjW c) :
    ((workerW x y).row = "P1" → BlockA.workerCase x y = .prefixMove) ∧
    ((workerW x y).row = "P3" → BlockA.workerCase x y = .prefixPublish) ∧
    ((workerW x y).row = "S1" → BlockA.workerCase x y = .sumPublish) := by
  refine ⟨fun hr => ?_, fun hr => ?_, fun hr => ?_⟩ <;>
    (unfold BlockA.workerCase; simp [hr])

/-! T11 item 1: the reachability invariant of a W run. Physical PREFIX
records sit at their own clockwise offset j (I0 fires only at the fixed
leader, P1 moves j to j+1, no other row creates PREFIX); window receipts
sit at offsets >= t and target/ready colours at offsets > t (P3 at the
offset-t PREFIX, S1 at a target, A1 never into the root since the root
is a post-E leader). See comms/T11-notes.md. -/

/-- A property wrapper: the `ite` eliminator below sees its argument. -/
def bankRepairDigitHolds {α : Type} (P : α → Prop) (a : α) : Prop := P a

theorem bankRepairDigitHoldsIte {α : Type} {P : α → Prop}
    {q : Prop} [Decidable q] {a b : α}
    (ha : q → bankRepairDigitHolds P a)
    (hb : ¬ q → bankRepairDigitHolds P b) :
    bankRepairDigitHolds P (if q then a else b) := by
  by_cases hq : q
  · rw [if_pos hq]; exact ha hq
  · rw [if_neg hq]; exact hb hq

theorem bankRepairDigitSiJSucc (t j : Nat) (h : j < t) :
    (siJ t (j + 1)).val = j + 1 := by
  unfold siJ
  rw [dif_pos (by omega)]

set_option linter.unusedSimpArgs false in
/-- `siStep` writes a PREFIX record at x only by I0 (hard accept). -/
theorem bankRepairDigitSiStepPrefixX (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hk : (siStep c ox oy post hard).x.kind = .PREFIX) :
    (hard.hardAccept = true ∧
        (siStep c ox oy post hard).x = launchPrefix c.t) ∨
      (siStep c ox oy post hard).x = ox.si := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.x.kind = .PREFIX →
      (hard.hardAccept = true ∧ r.x = launchPrefix c.t) ∨ r.x = ox.si)
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hk
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [offSI, launchPrefix, setCursor, clearCursor,
      launchRootBack, *] at hk ⊢
    all_goals (by_cases hL : hard.hardLeft = true <;>
      simp [hL, offSI] at hk ⊢)
  exact key hk

set_option linter.unusedSimpArgs false in
/-- `siStep` writes a PREFIX record at y only by P1, with index j+1. -/
theorem bankRepairDigitSiStepPrefixY (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hk : (siStep c ox oy post hard).y.kind = .PREFIX) :
    (ox.si.kind = .PREFIX ∧ ox.si.j.val < c.t ∧
        (siStep c ox oy post hard).y.j.val = ox.si.j.val + 1) ∨
      (siStep c ox oy post hard).y = oy.si := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.y.kind = .PREFIX →
      (ox.si.kind = .PREFIX ∧ ox.si.j.val < c.t ∧
        r.y.j.val = ox.si.j.val + 1) ∨ r.y = oy.si)
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hk
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [offSI, launchPrefix, setCursor, clearCursor,
      launchRootBack, bankRepairDigitSiJSucc, *] at hk ⊢
    all_goals (by_cases hR : hard.hardRight = true <;>
      simp [hR, offSI] at hk ⊢)
  exact key hk

set_option linter.unusedSimpArgs false in
theorem bankRepairDigitSiStepRowPone (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row = "P1") :
    ox.si.kind = .PREFIX ∧ ox.si.j.val < c.t := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "P1" →
      ox.si.kind = .PREFIX ∧ ox.si.j.val < c.t) (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

set_option linter.unusedSimpArgs false in
theorem bankRepairDigitSiStepRowAone (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row = "A1") :
    post.eY.l = false := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "A1" →
      post.eY.l = false) (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWorkerCaseAdvance {c : Compiled} (x y : ProjW c)
    (h : BlockA.workerCase x y = .advance) : (workerW x y).row = "A1" := by
  have key : bankRepairDigitHolds
      (fun w : BlockA.WorkerReceiptCase => w = .advance →
        (workerW x y).row = "A1") (BlockA.workerCase x y) := by
    unfold BlockA.workerCase
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hw
    all_goals simp_all
  exact key h

/-- A hard accept needs a (post-E, hence OLD) leader at x. -/
theorem bankRepairDigitHardAcceptLeader {c : Compiled} (x y : ProjW c)
    (h : (serW x y).hard.hardAccept = true) : x.native.l = true := by
  have h2 : (postW x y).eX.l = true := by
    revert h
    unfold serW serializerStep
    dsimp only
    cases (postW x y).eX.l <;> simp
  exact h2

theorem bankRepairDigitShiftInjective {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (a b : Nat) (ha : a < n) (hb : b < n)
    (h : PPL.shiftRight ring root a = PPL.shiftRight ring root b) :
    a = b := by
  have hv := congrArg Fin.val h
  change (root.val + a) % n = (root.val + b) % n at hv
  have hr := root.isLt
  have hA : (root.val + a) % n =
      (if root.val + a < n then root.val + a else root.val + a - n) := by
    by_cases h1 : root.val + a < n
    · rw [if_pos h1, Nat.mod_eq_of_lt h1]
    · rw [if_neg h1, Nat.mod_eq_sub_mod (show n ≤ root.val + a by omega),
        Nat.mod_eq_of_lt (show root.val + a - n < n by omega)]
  have hB : (root.val + b) % n =
      (if root.val + b < n then root.val + b else root.val + b - n) := by
    by_cases h1 : root.val + b < n
    · rw [if_pos h1, Nat.mod_eq_of_lt h1]
    · rw [if_neg h1, Nat.mod_eq_sub_mod (show n ≤ root.val + b by omega),
        Nat.mod_eq_of_lt (show root.val + b - n < n by omega)]
  rw [hA, hB] at hv
  split at hv <;> split at hv <;> omega

theorem bankRepairDigitWordPutCases {n : Nat} {A : Type} (f : Fin n → A)
    (j : Fin n) (a : A) (i : Fin n) :
    BlockA.wordPut f j a i = f i ∨ (i = j ∧ BlockA.wordPut f j a i = a) := by
  unfold BlockA.wordPut
  by_cases hi : i = j
  · exact Or.inr ⟨hi, by rw [if_pos hi]⟩
  · exact Or.inl (by rw [if_neg hi])

/-- Every physical PREFIX record sits at its own clockwise offset. -/
def BankRepairDigitPrefixSites {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c) : Prop :=
  ∀ s : Fin n, (p s).si.kind = .PREFIX →
    s = PPL.shiftRight ring root (p s).si.j.val

/-- T11 item 1: the reachability invariant of a W run. Either the monitor
is scrubbed (no receipt, no worker colour), or physical PREFIX records
sit at their offsets, window receipts (`.prefixEnd`/`.recurrence`) at
offsets >= t, and target/ready colours at offsets > t. -/
def BankRepairDigitWordReach {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  ((∀ i, h.publications i = .absent) ∧ (∀ i, h.workerKind i = .empty)) ∨
  (BankRepairDigitPrefixSites ring h.root p ∧
    (∀ i, (h.publications i = .prefixEnd ∨
        h.publications i = .recurrence) →
      ∃ k, c.t ≤ k ∧ k < n ∧ i = PPL.shiftRight ring h.root k) ∧
    (∀ i s, ((∃ b, h.workerKind i = .target s b) ∨
        h.workerKind i = .ready s) →
      ∃ k, c.t < k ∧ k < n ∧ i = PPL.shiftRight ring h.root k))

/-- Every projected W edge keeps PREFIX records at their offsets. -/
theorem bankRepairDigitPrefixSitesPhiW {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c)
    (e : Fin n)
    (huniq : ∀ i : Fin n, (p i).native.l = true → i = root)
    (hps : BankRepairDigitPrefixSites ring root p) :
    BankRepairDigitPrefixSites ring root (phiW ring p e) := by
  intro s hs
  by_cases hse : s = e
  · rw [hse] at hs ⊢
    have hx : (phiW ring p e) e =
        (pairW (p e) (p (ring.rightNeighbor e))).1 := by
      simp only [phiW, projectedEdge, if_pos rfl]
    rw [hx] at hs ⊢
    change (siStep c (p e).lift (p (ring.rightNeighbor e)).lift
      (postW (p e) (p (ring.rightNeighbor e)))
      (serW (p e) (p (ring.rightNeighbor e))).hard).x.kind = .PREFIX at hs
    change e = PPL.shiftRight ring root
      (siStep c (p e).lift (p (ring.rightNeighbor e)).lift
        (postW (p e) (p (ring.rightNeighbor e)))
        (serW (p e) (p (ring.rightNeighbor e))).hard).x.j.val
    rcases bankRepairDigitSiStepPrefixX c _ _ _ _ hs with ⟨ha, hxe⟩ | hxe
    · rw [hxe, huniq e (bankRepairDigitHardAcceptLeader _ _ ha)]
      exact (WordPhase.wordPhaseShiftZero ring root).symm
    · rw [hxe] at hs ⊢
      exact hps e hs
  · by_cases hsj : s = ring.rightNeighbor e
    · rw [hsj] at hs ⊢
      have hne : ring.rightNeighbor e ≠ e := fun h0 => hse (hsj.trans h0)
      have hy : (phiW ring p e) (ring.rightNeighbor e) =
          (pairW (p e) (p (ring.rightNeighbor e))).2 := by
        simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
      rw [hy] at hs ⊢
      change (siStep c (p e).lift (p (ring.rightNeighbor e)).lift
        (postW (p e) (p (ring.rightNeighbor e)))
        (serW (p e) (p (ring.rightNeighbor e))).hard).y.kind = .PREFIX at hs
      change ring.rightNeighbor e = PPL.shiftRight ring root
        (siStep c (p e).lift (p (ring.rightNeighbor e)).lift
          (postW (p e) (p (ring.rightNeighbor e)))
          (serW (p e) (p (ring.rightNeighbor e))).hard).y.j.val
      rcases bankRepairDigitSiStepPrefixY c _ _ _ _ hs with
        ⟨hk, _, hj⟩ | hye
      · rw [hj, WordPhase.wordPhaseShiftSucc]
        exact congrArg ring.rightNeighbor (hps e hk)
      · rw [hye] at hs ⊢
        exact hps _ hs
    · rw [cwPhiWFrame ring p e s hse hsj] at hs ⊢
      exact hps s hs

theorem bankRepairDigitWordReachScrub {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hp : ∀ i, h.publications i = .absent)
    (hk : ∀ i, h.workerKind i = .empty) :
    BankRepairDigitWordReach ring h p :=
  Or.inl ⟨hp, hk⟩

theorem bankRepairDigitWordReachSame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hreach : BankRepairDigitWordReach ring h p)
    (huniq : ∀ i : Fin n, (p i).native.l = true → i = h.root)
    (hroot : h'.root = h.root) (hpub : h'.publications = h.publications)
    (hwk : h'.workerKind = h.workerKind) :
    BankRepairDigitWordReach ring h' (phiW ring p e) := by
  rcases hreach with ⟨h1, h2⟩ | ⟨hps, hwin, hkd⟩
  · exact Or.inl ⟨by rw [hpub]; exact h1, by rw [hwk]; exact h2⟩
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [hroot]
      exact bankRepairDigitPrefixSitesPhiW ring h.root p e huniq hps
    · rw [hroot, hpub]
      exact hwin
    · rw [hroot, hwk]
      exact hkd

/-- The validated I0 launch: physical SI is clean except the root's
launch PREFIX at offset 0. -/
theorem bankRepairDigitWordReachLaunch {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (he : e = h.root) (hfree : BlockA.wordOtherWorkersFree ring h p e)
    (hx : (workerW (p e) (p (ring.rightNeighbor e))).x = launchPrefix c.t)
    (hy : freeSI (workerW (p e) (p (ring.rightNeighbor e))).y = true) :
    BankRepairDigitWordReach ring (BlockA.wordWorkerLaunch h)
      (phiW ring p e) := by
  refine Or.inr ⟨?_, fun i hi => ?_, fun i s hi => ?_⟩
  · intro s hs
    show s = PPL.shiftRight ring h.root _
    by_cases hse : s = e
    · rw [hse] at hs ⊢
      have hx' : (phiW ring p e) e =
          (pairW (p e) (p (ring.rightNeighbor e))).1 := by
        simp only [phiW, projectedEdge, if_pos rfl]
      rw [hx']
      change e = PPL.shiftRight ring h.root
        (workerW (p e) (p (ring.rightNeighbor e))).x.j.val
      rw [hx, he]
      exact (WordPhase.wordPhaseShiftZero ring h.root).symm
    · by_cases hsj : s = ring.rightNeighbor e
      · rw [hsj] at hs
        have hne : ring.rightNeighbor e ≠ e := fun h0 => hse (hsj.trans h0)
        have hy' : (phiW ring p e) (ring.rightNeighbor e) =
            (pairW (p e) (p (ring.rightNeighbor e))).2 := by
          simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
        rw [hy'] at hs
        change (workerW (p e) (p (ring.rightNeighbor e))).y.kind =
          .PREFIX at hs
        simp [freeSI, hs] at hy
      · rw [cwPhiWFrame ring p e s hse hsj] at hs
        have hf := hfree s hse hsj
        simp [freeSI, hs] at hf
  · simp [BlockA.wordWorkerLaunch, BlockA.wordClear] at hi
  · by_cases hr : i = h.root <;>
      simp [BlockA.wordWorkerLaunch, BlockA.wordClear, hr] at hi

theorem bankRepairDigitWordReachValidate {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (hreach : BankRepairDigitWordReach ring h p)
    (huniq : ∀ i : Fin n, (p i).native.l = true → i = h.root) :
    BankRepairDigitWordReach ring
      (BlockA.wordValidateNext ring h p e request) (phiW ring p e) := by
  unfold BlockA.wordValidateNext
  dsimp only
  split
  all_goals (repeat' split)
  all_goals first
    | exact bankRepairDigitWordReachScrub ring _ _ (fun _ => rfl) (fun _ => rfl)
    | exact bankRepairDigitWordReachSame ring h _ p e hreach huniq rfl rfl rfl
    | skip
  rename_i hg
  obtain ⟨he, -, -, -, -, hfree, -, -, hx, hy⟩ := hg
  exact bankRepairDigitWordReachLaunch ring h p e he hfree hx hy

theorem bankRepairDigitWordReachPone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hreach : BankRepairDigitWordReach ring h p)
    (huniq : ∀ i : Fin n, (p i).native.l = true → i = h.root)
    {idx idx' : Fin (c.t + 1)} {z a z' a' : Bool}
    (hk : h.workerKind e = .prefix idx z a)
    (hroot : h'.root = h.root)
    (hpub : h'.publications = h.publications ∨
      h'.publications =
        BlockA.wordPut h.publications (ring.rightNeighbor e) .prefixZero)
    (hwk : h'.workerKind =
      BlockA.wordPut (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e) (.prefix idx' z' a')) :
    BankRepairDigitWordReach ring h' (phiW ring p e) := by
  rcases hreach with ⟨_, h2⟩ | ⟨hps, hwin, hkd⟩
  · rw [h2 e] at hk
    cases hk
  · refine Or.inr ⟨?_, fun i hi => ?_, fun i s hi => ?_⟩
    · rw [hroot]
      exact bankRepairDigitPrefixSitesPhiW ring h.root p e huniq hps
    · rw [hroot]
      have hold : h'.publications i = h.publications i ∨
          h'.publications i = .prefixZero := by
        rcases hpub with hp | hp
        · exact Or.inl (by rw [hp])
        · rw [hp]
          rcases bankRepairDigitWordPutCases h.publications
              (ring.rightNeighbor e) .prefixZero i with h1 | ⟨_, h1⟩
          · exact Or.inl h1
          · exact Or.inr h1
      rcases hold with h1 | h1
      · rw [h1] at hi
        exact hwin i hi
      · rw [h1] at hi
        rcases hi with hi | hi <;> cases hi
    · rw [hroot]
      rw [hwk] at hi
      rcases bankRepairDigitWordPutCases
          (BlockA.wordPut h.workerKind e .empty) (ring.rightNeighbor e)
          (.prefix idx' z' a') i with h1 | ⟨_, h1⟩
      · rw [h1] at hi
        rcases bankRepairDigitWordPutCases h.workerKind e .empty i with
          h2 | ⟨_, h2⟩
        · rw [h2] at hi
          exact hkd i s hi
        · rw [h2] at hi
          rcases hi with ⟨_, hi⟩ | hi <;> cases hi
      · rw [h1] at hi
        rcases hi with ⟨_, hi⟩ | hi <;> cases hi

theorem bankRepairDigitWordReachPthree {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hreach : BankRepairDigitWordReach ring h p)
    (huniq : ∀ i : Fin n, (p i).native.l = true → i = h.root)
    (ht : c.t + 1 < n)
    {idx : Fin (c.t + 1)} {z a : Bool}
    (hk : h.workerKind e = .prefix idx z a)
    (hidx : idx.val = c.t) (hkind : (p e).si.kind = .PREFIX)
    (hj : (p e).si.j = idx)
    (hroot : h'.root = h.root)
    (hpub : h'.publications = BlockA.wordPut h.publications e .prefixEnd)
    (hwk : h'.workerKind =
      BlockA.wordPut (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e) (.target (ring.rightNeighbor e) true)) :
    BankRepairDigitWordReach ring h' (phiW ring p e) := by
  rcases hreach with ⟨_, h2⟩ | ⟨hps, hwin, hkd⟩
  · rw [h2 e] at hk
    cases hk
  · have he : e = PPL.shiftRight ring h.root c.t := by
      have h0 := hps e hkind
      rw [hj, hidx] at h0
      exact h0
    have hjt : ring.rightNeighbor e =
        PPL.shiftRight ring h.root (c.t + 1) := by
      rw [WordPhase.wordPhaseShiftSucc, ← he]
    refine Or.inr ⟨?_, fun i hi => ?_, fun i s hi => ?_⟩
    · rw [hroot]
      exact bankRepairDigitPrefixSitesPhiW ring h.root p e huniq hps
    · rw [hroot]
      rw [hpub] at hi
      rcases bankRepairDigitWordPutCases h.publications e .prefixEnd i with
        h1 | ⟨hie, _⟩
      · rw [h1] at hi
        exact hwin i hi
      · exact ⟨c.t, Nat.le_refl _, by omega, hie.trans he⟩
    · rw [hroot]
      rw [hwk] at hi
      rcases bankRepairDigitWordPutCases
          (BlockA.wordPut h.workerKind e .empty) (ring.rightNeighbor e)
          (.target (ring.rightNeighbor e) true) i with h1 | ⟨hij, _⟩
      · rw [h1] at hi
        rcases bankRepairDigitWordPutCases h.workerKind e .empty i with
          h2 | ⟨_, h2⟩
        · rw [h2] at hi
          exact hkd i s hi
        · rw [h2] at hi
          rcases hi with ⟨_, hi⟩ | hi <;> cases hi
      · exact ⟨c.t + 1, by omega, ht, hij.trans hjt⟩

theorem bankRepairDigitWordReachSone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hreach : BankRepairDigitWordReach ring h p)
    (huniq : ∀ i : Fin n, (p i).native.l = true → i = h.root)
    (hkj : h.workerKind (ring.rightNeighbor e) =
      .target (ring.rightNeighbor e) true)
    (hroot : h'.root = h.root)
    (hpub : h'.publications =
      BlockA.wordPut h.publications (ring.rightNeighbor e) .recurrence)
    (hwk : h'.workerKind = BlockA.wordPut h.workerKind
      (ring.rightNeighbor e) (.ready (ring.rightNeighbor e))) :
    BankRepairDigitWordReach ring h' (phiW ring p e) := by
  rcases hreach with ⟨_, h2⟩ | ⟨hps, hwin, hkd⟩
  · rw [h2] at hkj
    cases hkj
  · obtain ⟨k, hk1, hk2, hk3⟩ := hkd _ _ (Or.inl ⟨true, hkj⟩)
    refine Or.inr ⟨?_, fun i hi => ?_, fun i s hi => ?_⟩
    · rw [hroot]
      exact bankRepairDigitPrefixSitesPhiW ring h.root p e huniq hps
    · rw [hroot]
      rw [hpub] at hi
      rcases bankRepairDigitWordPutCases h.publications
          (ring.rightNeighbor e) .recurrence i with h1 | ⟨hij, _⟩
      · rw [h1] at hi
        exact hwin i hi
      · exact ⟨k, by omega, hk2, hij.trans hk3⟩
    · rw [hroot]
      rw [hwk] at hi
      rcases bankRepairDigitWordPutCases h.workerKind
          (ring.rightNeighbor e) (.ready (ring.rightNeighbor e)) i with
        h1 | ⟨hij, _⟩
      · rw [h1] at hi
        exact hkd i s hi
      · exact ⟨k, hk1, hk2, hij.trans hk3⟩

/-- A1 never colours the root as a target: there the root is a post-E
leader, so the physical row is A0, not A1. -/
theorem bankRepairDigitWordReachAone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hreach : BankRepairDigitWordReach ring h p)
    (huniq : ∀ i : Fin n, (p i).native.l = true → i = h.root)
    (hfix' : WFixedRoot ring h.root (phiW ring p e))
    (hne : ring.rightNeighbor e ≠ e)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .advance)
    (hke : h.workerKind e = .ready e)
    (hroot : h'.root = h.root)
    (hpub : h'.publications = h.publications)
    (hwk : h'.workerKind =
      BlockA.wordPut (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e) (.target (ring.rightNeighbor e) true)) :
    BankRepairDigitWordReach ring h' (phiW ring p e) := by
  rcases hreach with ⟨_, h2⟩ | ⟨hps, hwin, hkd⟩
  · rw [h2] at hke
    cases hke
  · obtain ⟨k, hk1, hk2, hk3⟩ := hkd e e (Or.inr hke)
    have hjk : ring.rightNeighbor e =
        PPL.shiftRight ring h.root (k + 1) := by
      rw [WordPhase.wordPhaseShiftSucc, ← hk3]
    have hkn : k + 1 < n := by
      by_cases hkn : k + 1 < n
      · exact hkn
      · exfalso
        have hroot' : ring.rightNeighbor e = h.root := by
          rw [hjk, show k + 1 = n by omega]
          exact bankRepairDigitShiftFull ring h.root
        have hrow := bankRepairDigitWorkerCaseAdvance _ _ hcase
        have hl := bankRepairDigitSiStepRowAone c _ _ _ _ hrow
        have hl' := hfix'.1
        rw [← hroot'] at hl'
        have hy : (phiW ring p e) (ring.rightNeighbor e) =
            (pairW (p e) (p (ring.rightNeighbor e))).2 := by
          simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
        rw [hy] at hl'
        change (postW (p e) (p (ring.rightNeighbor e))).eY.l = true at hl'
        rw [hl] at hl'
        cases hl'
    refine Or.inr ⟨?_, fun i hi => ?_, fun i s hi => ?_⟩
    · rw [hroot]
      exact bankRepairDigitPrefixSitesPhiW ring h.root p e huniq hps
    · rw [hroot]
      rw [hpub] at hi
      exact hwin i hi
    · rw [hroot]
      rw [hwk] at hi
      rcases bankRepairDigitWordPutCases
          (BlockA.wordPut h.workerKind e .empty) (ring.rightNeighbor e)
          (.target (ring.rightNeighbor e) true) i with h1 | ⟨hij, _⟩
      · rw [h1] at hi
        rcases bankRepairDigitWordPutCases h.workerKind e .empty i with
          h2 | ⟨_, h2⟩
        · rw [h2] at hi
          exact hkd i s hi
        · rw [h2] at hi
          rcases hi with ⟨_, hi⟩ | hi <;> cases hi
      · exact ⟨k + 1, by omega, hkn, hij.trans hjk⟩

theorem bankRepairDigitWordReachWorker {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix : WFixedRoot ring h.root p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e))
    (ht : c.t + 1 < n) :
    BankRepairDigitWordReach ring
      (BlockA.wordWorkerNext ring h p e request) (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  have huniq := hfix.2.1
  unfold BlockA.wordWorkerNext
  dsimp only
  split
  all_goals (repeat' split)
  all_goals first
    | exact bankRepairDigitWordReachScrub ring _ _ (fun _ => rfl) (fun _ => rfl)
    | exact bankRepairDigitWordReachSame ring h _ p e hreach huniq rfl rfl rfl
    | skip
  all_goals first
    | exact bankRepairDigitWordReachPone ring h _ p e hreach huniq ‹_› rfl
        (Or.inr rfl) rfl
    | exact bankRepairDigitWordReachPone ring h _ p e hreach huniq ‹_› rfl
        (Or.inl rfl) rfl
    | (rename_i hC
       exact bankRepairDigitWordReachPthree ring h _ p e hreach huniq ht ‹_›
         hC.1 hC.2.1 hC.2.2.2.2.1 rfl rfl rfl)
    | (rename_i hC
       exact bankRepairDigitWordReachSone ring h _ p e hreach huniq hC.2.1
         rfl rfl rfl)
    | (rename_i hC
       exact bankRepairDigitWordReachAone ring h _ p e hreach huniq hfix' hne
         ‹_› hC.1 rfl rfl rfl)

/-- One complete W monitor step preserves the reachability invariant. -/
theorem bankRepairDigitWordReachStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix : WFixedRoot ring h.root p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e))
    (ht : c.t + 1 < n) :
    BankRepairDigitWordReach ring
      (BlockA.wordT ring h p e (phiW ring p e)) (phiW ring p e) := by
  unfold BlockA.wordT
  split
  · exact bankRepairDigitWordReachSame ring h h p e hreach hfix.2.1 rfl rfl rfl
  · dsimp only
    split
    · exact bankRepairDigitWordReachScrub ring _ _ (fun _ => rfl) (fun _ => rfl)
    · split
      · exact bankRepairDigitWordReachScrub ring _ _ (fun _ => rfl)
          (fun _ => rfl)
      · exact bankRepairDigitWordReachValidate ring h p e _ hreach hfix.2.1
      · exact bankRepairDigitWordReachWorker ring h p e _ hreach hfix hfix' ht
      · exact bankRepairDigitWordReachSame ring h h p e hreach hfix.2.1
          rfl rfl rfl

theorem bankRepairDigitWordReachRunAux {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (origin : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (root : Fin n) (h₀ : BlockA.WordControl n c)
    (hγ₀ : γ₀ = .live origin h₀) (hroot₀ : h₀.root = root)
    (hfix₀ : WFixedRoot ring root origin)
    (hcl : ∀ i, h₀.publications i = .absent ∧ h₀.workerKind i = .empty)
    (hn : 3 ≤ n) (ht : c.t + 1 < n)
    {w : List (Fin n)} {p : Fin n → ProjW c}
    {γ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c)}
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p γ) :
    ∀ shadow h, γ = .live shadow h →
      shadow = p ∧ WFixedRoot ring h.root p ∧
        BankRepairDigitWordReach ring h p := by
  induction hrun with
  | empty =>
      intro shadow h hγ
      rw [hγ₀] at hγ
      injection hγ with h1 h2
      subst h1 h2
      refine ⟨rfl, ?_, Or.inl ⟨fun i => (hcl i).1, fun i => (hcl i).2⟩⟩
      rw [hroot₀]
      exact hfix₀
  | @next w p γ hr e ih =>
      intro shadow h hγ
      cases γ with
      | failed =>
          rw [BlockA.update_failed] at hγ
          cases hγ
      | live s h₁ =>
          obtain ⟨hs, hfix₁, hreach₁⟩ := ih s h₁ rfl
          rw [hs, AcceptedReceipts.WordEntrance.word_update_live] at hγ
          injection hγ with h1 h2
          subst h1 h2
          have hroot' :
              (BlockA.wordT ring h₁ p e (phiW ring p e)).root = h₁.root :=
            (bankRepairDigitWordReceiptStepT ring h₁ p e _).1
          have hfix' : WFixedRoot ring h₁.root (phiW ring p e) :=
            bankRepairDigitWFixedRootPhiW hn ring h₁.root p e hfix₁
          refine ⟨rfl, ?_,
            bankRepairDigitWordReachStep ring h₁ p e hreach₁ hfix₁ hfix' ht⟩
          rw [hroot']
          exact hfix'

/-- T11 item 1: along every projected W run from `initializesWord` the
root stays the fixed leader and the reachability invariant holds: window
receipts sit at offsets >= t, targets/ready sites at offsets > t, and
every physical PREFIX record sits at its own offset j (so the P1 chain,
which publishes at offset j+1 < t, stays below t). -/
theorem bankRepairDigitWordRunReach {n : Nat} (ring : DirectedRing n)
    (c : Compiled) :
    ∀ (origin p : Fin n → ProjW c)
      (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
      (w : List (Fin n)) (shadow : Fin n → ProjW c)
      (h : BlockA.WordControl n c),
      BlockA.initializesWord ring origin γ₀ →
      BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
        (.live shadow h) →
      WFixedRoot ring h.root p ∧ BankRepairDigitWordReach ring h p := by
  intro origin p γ₀ w shadow h hinit hrun
  obtain ⟨root, h₀, hγ₀, hroot, hfix, ht2, htn, -, -, hcl, -, -⟩ := hinit
  have hpow := bankRepairDigitPowLower c.t
  obtain ⟨-, hf, hr⟩ := bankRepairDigitWordReachRunAux ring origin γ₀ root h₀
    hγ₀ hroot hfix (fun i => ⟨(hcl i).2.2.2.2.1, (hcl i).2.2.1⟩)
    (by omega) (by omega) hrun shadow h rfl
  exact ⟨hf, hr⟩

/-- The P1 responder at offset j+1 < t never carries a window receipt. -/
theorem bankRepairDigitWordReachPoneTarget {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hreach : BankRepairDigitWordReach ring h p)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "P1")
    (hlt : (p e).si.j.val + 1 < c.t) :
    h.publications (ring.rightNeighbor e) = .absent ∨
      h.publications (ring.rightNeighbor e) = .prefixZero := by
  rcases hreach with ⟨h1, _⟩ | ⟨hps, hwin, _⟩
  · exact Or.inl (h1 _)
  · have hk : (p e).si.kind = .PREFIX :=
      (bankRepairDigitSiStepRowPone c _ _ _ _ hrow).1
    have he := hps e hk
    have hj : ring.rightNeighbor e =
        PPL.shiftRight ring h.root ((p e).si.j.val + 1) := by
      rw [WordPhase.wordPhaseShiftSucc, ← he]
    have hbad : ∀ k, c.t ≤ k → k < n →
        ring.rightNeighbor e ≠ PPL.shiftRight ring h.root k := by
      intro k hk1 hk2 hk3
      have := bankRepairDigitShiftInjective ring h.root _ _ (by omega) hk2
        (hj.symm.trans hk3)
      omega
    cases hpub : h.publications (ring.rightNeighbor e) with
    | absent => exact Or.inl rfl
    | prefixZero => exact Or.inr rfl
    | prefixEnd =>
        obtain ⟨k, hk1, hk2, hk3⟩ := hwin _ (Or.inl hpub)
        exact absurd hk3 (hbad k hk1 hk2)
    | recurrence =>
        obtain ⟨k, hk1, hk2, hk3⟩ := hwin _ (Or.inr hpub)
        exact absurd hk3 (hbad k hk1 hk2)

/-- T9 item 1: P1 preserves the invariant in general, in every monitor
phase. The receipt P1 issues is `.prefixZero` at j = rightNeighbor e,
the same follower where P1 writes beta = false (when idx+1 < t), so its
marker clause is exactly the written betaY. The u bits are unchanged, so
all window folds are unchanged. T11: the former hypothesis `hj` (no
window receipt at the follower whose marker P1 zeroes) is now derived
from the reachability invariant `BankRepairDigitWordReach`, which holds
on every W run (`bankRepairDigitWordRunReach`). -/
theorem bankRepairDigitWordPublishedPone {n : Nat} {c : Compiled}
    (hn : 3 ≤ n) (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hpub : BankRepairDigitWordPublished ring h p)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "P1")
    (hreach : BankRepairDigitWordReach ring h p) :
    BankRepairDigitWordPublished ring
      (BlockA.wordT ring h p e (phiW ring p e)) (phiW ring p e) := by
  have hj := bankRepairDigitWordReachPoneTarget ring h p e hreach hrow
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  obtain ⟨hroot, hsite⟩ :=
    bankRepairDigitWordReceiptStepT ring h p e (phiW ring p e)
  obtain ⟨_, _, hu, hbeta, hbj⟩ :=
    WordPhase.wordPhasePonePhysicalFields ring p e hne hrow
  have hcase := (bankRepairDigitWorkerCaseOfRow (p e)
    (p (ring.rightNeighbor e))).1 hrow
  have hbetaY : ((phiW ring p e) (ring.rightNeighbor e)).beta =
      (workerW (p e) (p (ring.rightNeighbor e))).betaY := by
    simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte, pairW]
  have hbit : ∀ r k, cwBit ring r (phiW ring p e) k = cwBit ring r p k :=
    fun r k => by simp only [cwBit, hu]
  have hmarker : ∀ s, h.publications s ≠ .absent →
      h.publications s ≠ .prefixZero →
      ((phiW ring p e) s).beta = (p s).beta := by
    intro s h1 h2
    by_cases hs : s = ring.rightNeighbor e
    · subst hs
      rw [hbj]
      split
      · rename_i hlt
        rcases hj hlt with h3 | h3
        · exact absurd h3 h1
        · exact absurd h3 h2
      · rfl
    · exact hbeta s hs
  have hsite' : ∀ s,
      (BlockA.wordT ring h p e (phiW ring p e)).publications s =
        h.publications s ∨
      (BlockA.wordT ring h p e (phiW ring p e)).publications s = .absent ∨
      (((phiW ring p e) s).beta = false ∧
        (BlockA.wordT ring h p e (phiW ring p e)).publications s =
          .prefixZero) := by
    intro s
    rcases hsite s with h1 | h1 | ⟨hs, _, hb, h2⟩ | ⟨_, hc, _⟩ | ⟨_, hc, _⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · subst hs
      exact Or.inr (Or.inr ⟨hbetaY.trans hb, h2⟩)
    · rw [hcase] at hc; cases hc
    · rw [hcase] at hc; cases hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hroot]
    exact bankRepairDigitWFixedRootPhiW hn ring h.root p e hpub.rootFixed
  · intro k hk hkt hp'
    rw [hroot] at hp' ⊢
    unfold cwMarker
    rcases hsite' (PPL.shiftRight ring h.root k.val) with h1 | h1 | ⟨hb, _⟩
    · rw [h1] at hp'
      have hold := hpub.prefixZeros k hk hkt hp'
      unfold cwMarker at hold
      by_cases hs : PPL.shiftRight ring h.root k.val = ring.rightNeighbor e
      · rw [hs] at hold ⊢
        rw [hbj]
        split
        · rfl
        · exact hold
      · rw [hbeta _ hs]
        exact hold
    · rw [h1] at hp'; cases hp'
    · exact hb
  · intro k hk hp'
    rw [hroot] at hp' ⊢
    rcases hsite' (PPL.shiftRight ring h.root k.val) with h1 | h1 | ⟨_, h2⟩
    · rw [h1] at hp'
      have hold := hpub.firstWindow k hk hp'
      have hm := hmarker (PPL.shiftRight ring h.root k.val)
        (by rw [hp']; decide) (by rw [hp']; decide)
      simp only [cwPrefixOr, cwSumTrailing, cwSourceBit, hbit]
      unfold cwMarker at hold ⊢
      rw [hm]
      exact hold
    · rw [h1] at hp'; cases hp'
    · rw [h2] at hp'; cases hp'
  · intro k hk hp'
    rw [hroot] at hp' ⊢
    rcases hsite' (PPL.shiftRight ring h.root k.val) with h1 | h1 | ⟨_, h2⟩
    · rw [h1] at hp'
      have hold := hpub.laterWindows k hk hp'
      have hm := hmarker (PPL.shiftRight ring h.root k.val)
        (by rw [hp']; decide) (by rw [hp']; decide)
      simp only [cwSumOr, cwSumParity, cwSumTrailing, cwSourceBit, hbit]
      unfold cwMarker at hold ⊢
      rw [hm]
      exact hold
    · rw [h1] at hp'; cases hp'
    · rw [h2] at hp'; cases hp'

/-! T10 item 1: the toy witness that the OR-only `laterWindows` clause
(before the forced-window repair) fails at a reachable W state: t = 2,
zero taps, n = 5, 28-edge prefix, then edge 3 runs S1 on an all-zero
window. -/

/-- Fold a W schedule through `phiW` and `wordT`. -/
def bankRepairDigitWordFold {n : Nat} {c : Compiled} (ring : DirectedRing n)
    (s : (Fin n → ProjW c) × BlockA.WordControl n c) (w : List (Fin n)) :
    (Fin n → ProjW c) × BlockA.WordControl n c :=
  w.foldl (fun s e => (phiW ring s.1 e,
    BlockA.wordT ring s.2 s.1 e (phiW ring s.1 e))) s

theorem bankRepairDigitWordRunOfFold {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (origin : Fin n → ProjW c)
    (h₀ : BlockA.WordControl n c) (w : List (Fin n)) :
    BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin (.live origin h₀) w
      (bankRepairDigitWordFold ring (origin, h₀) w).1
      (.live (bankRepairDigitWordFold ring (origin, h₀) w).1
        (bankRepairDigitWordFold ring (origin, h₀) w).2) := by
  suffices hgen : ∀ (w₁ : List (Fin n)) (p : Fin n → ProjW c)
      (h : BlockA.WordControl n c),
      BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin (.live origin h₀)
        w₁ p (.live p h) →
      BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin (.live origin h₀)
        (w₁ ++ w) (bankRepairDigitWordFold ring (p, h) w).1
        (.live (bankRepairDigitWordFold ring (p, h) w).1
          (bankRepairDigitWordFold ring (p, h) w).2) by
    simpa using hgen [] origin h₀ .empty
  induction w with
  | nil =>
      intro w₁ p h hr
      simpa [bankRepairDigitWordFold] using hr
  | cons e es ih =>
      intro w₁ p h hr
      have hnext := BlockA.Run.next hr e
      rw [AcceptedReceipts.WordEntrance.word_update_live] at hnext
      have := ih (w₁ ++ [e]) _ _ hnext
      simpa [bankRepairDigitWordFold, List.foldl_cons] using this

def bankRepairDigitWordKickOrigin (i : Fin 5) : ProjW cwToyCfg :=
  { native := { l := i == 0, b := 0, sh := false, sg := false }
    ser := { phase := .C, out := .NEW, probe := .NONE, cert := .IDLE, wphase := .OFF }
    siLease := 0, si := offSI cwToyCfg.t, u := i == 1, beta := false }

def bankRepairDigitWordKickControl : BlockA.WordControl 5 cwToyCfg :=
  { root := 0, phase := .awaitRequest, requested := false,
    serializer := fun _ => BlockA.wordColor .empty none,
    workerKind := fun _ => .empty, workerCursor := fun _ => .empty,
    prefixReads := BlockA.wordEmptyLedger,
    sumReads := BlockA.wordEmptyLedger,
    publications := fun _ => .absent, visibleReceipts := fun _ => false,
    prefixMarkers := fun _ => false }

def bankRepairDigitWordKickPrefix : List (Fin 5) :=
  [4,0,1,0,1,2,1,2,3,2,3,4,3,3,2,1,0,0,1,2,2,1,1,2,3,3,2,2]

theorem bankRepairDigitWordKickInit :
    BlockA.initializesWord cwToyRing bankRepairDigitWordKickOrigin
      (.live bankRepairDigitWordKickOrigin bankRepairDigitWordKickControl) := by
  refine ⟨0, bankRepairDigitWordKickControl, rfl, rfl, ⟨rfl, ?_, ?_⟩,
    by decide, by decide, rfl, rfl, ?_, rfl, rfl⟩
  · intro i hi
    revert hi
    revert i
    decide
  · refine ⟨⟨0, rfl⟩, ?_⟩
    intro v hv
    exfalso
    unfold LiveBullet at hv
    revert hv
    revert v
    decide
  · intro i
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Before the step: phase worker, edge 3 -> 4 runs S1, no receipt at 4. -/
theorem bankRepairDigitWordKickRow :
    let s := bankRepairDigitWordFold cwToyRing
      (bankRepairDigitWordKickOrigin, bankRepairDigitWordKickControl)
      bankRepairDigitWordKickPrefix
    s.2.phase = .worker ∧
      (workerW (s.1 3) (s.1 (cwToyRing.rightNeighbor 3))).row = "S1" ∧
      s.2.publications 4 = .absent := by
  decide +kernel

/-- After the S1 step: a `.recurrence` receipt at offset 4 on an
all-zero window, with the forced bit and its marker. -/
theorem bankRepairDigitWordKickAfter :
    let s := bankRepairDigitWordFold cwToyRing
      (bankRepairDigitWordKickOrigin, bankRepairDigitWordKickControl)
      (bankRepairDigitWordKickPrefix ++ [3])
    s.2.publications (PPL.shiftRight cwToyRing s.2.root 4) = .recurrence ∧
      cwSumOr cwToyRing s.2.root s.1 4 cwToyCfg.t = false ∧
      cwBit cwToyRing s.2.root s.1 4 = true ∧
      cwMarker cwToyRing s.2.root s.1 4 =
        (cwSumTrailing cwToyRing s.2.root s.1 4 cwToyCfg.t &&
          cwBit cwToyRing s.2.root s.1 4) := by
  decide +kernel

/-- T10 item 1: at a reachable W state a `.recurrence` receipt sits on
an all-zero window, so the OR-only clause fails; the forced branch of
the repaired `laterWindows` holds there. -/
theorem bankRepairDigitWordKickOrClauseFails :
    ∃ (origin p : Fin 5 → ProjW cwToyCfg)
      (γ₀ : BlockA.Decoration (Fin 5 → ProjW cwToyCfg)
        (BlockA.WordControl 5 cwToyCfg))
      (w : List (Fin 5)) (shadow : Fin 5 → ProjW cwToyCfg)
      (h : BlockA.WordControl 5 cwToyCfg) (k : Fin 5),
      BlockA.initializesWord cwToyRing origin γ₀ ∧
      BlockA.Run cwToyRing (phiW cwToyRing) (BlockA.wordT cwToyRing)
        origin γ₀ w p (.live shadow h) ∧
      cwToyCfg.t < k.val ∧
      h.publications (PPL.shiftRight cwToyRing h.root k.val) =
        .recurrence ∧
      cwSumOr cwToyRing h.root p k.val cwToyCfg.t = false ∧
      cwBit cwToyRing h.root p k.val = true ∧
      cwMarker cwToyRing h.root p k.val =
        (cwSumTrailing cwToyRing h.root p k.val cwToyCfg.t &&
          cwBit cwToyRing h.root p k.val) := by
  have hf := bankRepairDigitWordKickAfter
  exact ⟨_, _, _, _, _, _, ⟨4, by decide⟩, bankRepairDigitWordKickInit,
    bankRepairDigitWordRunOfFold cwToyRing _ _
      (bankRepairDigitWordKickPrefix ++ [3]),
    by decide, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩

end L3.RenewalReferenceClock

/-!
T11 item 2: the accumulator invariant. The running values that P3 and S1
publish are carried by the worker colours: a PREFIX tag's z/a are the
prefix OR/AND (`cwPhasePrefixPhysical` is reused for its SI record), and
a SUM cursor's z/parity/trailing are the actual window OR/parity/trailing
(the `cwSumOr`/`cwSumParity`/`cwSumTrailing` of `CleanWorkerInv.sumAcc`)
over the sources read so far, at the source offset `target - t + idx`.
B0, B1 and S0 preserve it. See comms/T11-notes.md.
-/

namespace L3.RenewalReferenceClock

open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option linter.unusedSimpArgs false

theorem bankRepairDigitWorkerCaseRows {c : Compiled} (x y : ProjW c) :
    (BlockA.workerCase x y = .backwardsMove → (workerW x y).row = "B0") ∧
    (BlockA.workerCase x y = .backwardsInit → (workerW x y).row = "B1") ∧
    (BlockA.workerCase x y = .sumMove → (workerW x y).row = "S0") := by
  have key : bankRepairDigitHolds
      (fun w : BlockA.WorkerReceiptCase =>
        (w = .backwardsMove → (workerW x y).row = "B0") ∧
        (w = .backwardsInit → (workerW x y).row = "B1") ∧
        (w = .sumMove → (workerW x y).row = "S0"))
      (BlockA.workerCase x y) := by
    unfold BlockA.workerCase
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals simp_all
  exact key

theorem bankRepairDigitSiStepRowBzero (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row = "B0") :
    freeSI ox.si = true ∧ oy.si.kind ≠ .PREFIX := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "B0" →
      freeSI ox.si = true ∧ oy.si.kind ≠ .PREFIX)
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitSiStepRowBone (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row = "B1") :
    freeSI ox.si = true ∧ oy.si.kind ≠ .PREFIX ∧
      (siStep c ox oy post hard).x = setCursor ox.si .SUM 0 false false true := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "B1" →
      freeSI ox.si = true ∧ oy.si.kind ≠ .PREFIX ∧
        r.x = setCursor ox.si .SUM 0 false false true)
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitSiStepRowSzero (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row = "S0") :
    ox.si.kind = .OFF ∧ freeSI oy.si = true ∧
      (siStep c ox oy post hard).y.kind = .OFF := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "S0" →
      ox.si.kind = .OFF ∧ freeSI oy.si = true ∧ r.y.kind = .OFF)
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [setCursor, *] at hr ⊢
  exact key hr

theorem bankRepairDigitRightNeighborInjective {n : Nat}
    (ring : DirectedRing n) (a b : Fin n)
    (h : ring.rightNeighbor a = ring.rightNeighbor b) : a = b := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (a.val + 1) % n = (b.val + 1) % n at hv
  have ha := a.isLt
  have hb := b.isLt
  have hA : (a.val + 1) % n = (if a.val + 1 < n then a.val + 1 else 0) := by
    by_cases h1 : a.val + 1 < n
    · rw [if_pos h1, Nat.mod_eq_of_lt h1]
    · rw [if_neg h1, show a.val + 1 = n by omega, Nat.mod_self]
  have hB : (b.val + 1) % n = (if b.val + 1 < n then b.val + 1 else 0) := by
    by_cases h1 : b.val + 1 < n
    · rw [if_pos h1, Nat.mod_eq_of_lt h1]
    · rw [if_neg h1, show b.val + 1 = n by omega, Nat.mod_self]
  rw [hA, hB] at hv
  split at hv <;> split at hv <;> omega

/-- The left neighbour of a clockwise site is the previous offset. -/
theorem bankRepairDigitShiftPred {n : Nat} (ring : DirectedRing n)
    (root e : Fin n) (m : Nat)
    (h : ring.rightNeighbor e = PPL.shiftRight ring root (m + 1)) :
    e = PPL.shiftRight ring root m := by
  apply bankRepairDigitRightNeighborInjective ring
  rw [h, WordPhase.wordPhaseShiftSucc]

theorem bankRepairDigitPhiWSites {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    ((phiW ring p e) e).si = (workerW (p e) (p (ring.rightNeighbor e))).x ∧
    ((phiW ring p e) (ring.rightNeighbor e)).si =
      (workerW (p e) (p (ring.rightNeighbor e))).y := by
  constructor
  · simp only [phiW, projectedEdge, if_pos rfl]
    rfl
  · simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
    rfl

/-- The five window folds read only the u bits. -/
theorem bankRepairDigitWordFoldsCongr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p p' : Fin n → ProjW c)
    (hu : ∀ i, (p' i).u = (p i).u) (T k : Nat) :
    cwPrefixOr ring root p' k = cwPrefixOr ring root p k ∧
    cwPrefixAnd ring root p' k = cwPrefixAnd ring root p k ∧
    cwSumOr ring root p' T k = cwSumOr ring root p T k ∧
    cwSumParity ring root p' T k = cwSumParity ring root p T k ∧
    cwSumTrailing ring root p' T k = cwSumTrailing ring root p T k := by
  have hb : ∀ m, cwBit ring root p' m = cwBit ring root p m :=
    fun m => hu _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold cwPrefixOr
    simp only [hb]
  · unfold cwPrefixAnd
    simp only [hb]
  · unfold cwSumOr cwSourceBit
    simp only [hb]
  · unfold cwSumParity cwSourceBit
    simp only [hb]
  · unfold cwSumTrailing cwSourceBit
    simp only [hb]

/-- One more source bit in the SUM folds. -/
theorem bankRepairDigitSumFoldStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c)
    (T k : Nat) :
    cwSumOr ring root p T (k + 1) =
      (cwSumOr ring root p T k || cwSourceBit ring root p T k) ∧
    cwSumParity ring root p T (k + 1) =
      Bool.xor (cwSumParity ring root p T k)
        (c.taps k && cwSourceBit ring root p T k) ∧
    cwSumTrailing ring root p T (k + 1) =
      (if k = 0 then cwSumTrailing ring root p T k
       else (cwSumTrailing ring root p T k &&
         cwSourceBit ring root p T k)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold cwSumOr
    rw [List.range_succ, List.foldl_append]
    rfl
  · unfold cwSumParity
    rw [List.range_succ, List.foldl_append]
    rfl
  · unfold cwSumTrailing
    rw [List.range_succ, List.foldl_append]
    rfl

theorem bankRepairDigitSumFoldZero {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c) (T : Nat) :
    cwSumOr ring root p T 0 = false ∧ cwSumParity ring root p T 0 = false ∧
      cwSumTrailing ring root p T 0 = true :=
  ⟨rfl, rfl, rfl⟩

/-- T11 item 2: the accumulator invariant at one site. A PREFIX tag's
z/a are the prefix OR/AND (the values P3 publishes); a BACK cursor sits
at window offset `target - t + idx`; a SUM cursor sits at the source
offset `target - t + idx` and its z/parity/trailing are the actual
window OR/parity/trailing over the first `idx` sources (the values S1
publishes). The physical SI record matches the colour. -/
def BankRepairDigitWordAccAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (i : Fin n) : Prop :=
  (∀ (idx : Fin (c.t + 1)) (z a : Bool),
    h.workerKind i = .prefix idx z a →
      cwPhasePrefixPhysical p i idx z a ∧
      i = PPL.shiftRight ring h.root idx.val ∧
      z = cwPrefixOr ring h.root p idx.val ∧
      a = cwPrefixAnd ring h.root p idx.val) ∧
  (∀ (target : Fin n) (idx : Fin (c.t + 1)),
    h.workerCursor i = .back target idx →
      (p i).si.cur = .BACK ∧ (p i).si.j = idx ∧
      i = PPL.shiftRight ring h.root
        (PPL.cyclicOffset ring h.root target - c.t + idx.val)) ∧
  (∀ (target : Fin n) (idx : Fin (c.t + 1)) (z parity trailing : Bool),
    h.workerCursor i = .sum target idx z parity trailing →
      (p i).si.kind = .OFF ∧ (p i).si.cur = .SUM ∧ (p i).si.j = idx ∧
      (p i).si.z = z ∧ (p i).si.p = parity ∧ (p i).si.a = trailing ∧
      i = PPL.shiftRight ring h.root
        (PPL.cyclicOffset ring h.root target - c.t + idx.val) ∧
      z = cwSumOr ring h.root p
        (PPL.cyclicOffset ring h.root target) idx.val ∧
      parity = cwSumParity ring h.root p
        (PPL.cyclicOffset ring h.root target) idx.val ∧
      trailing = cwSumTrailing ring h.root p
        (PPL.cyclicOffset ring h.root target) idx.val)

/-- T11 item 2: the accumulator invariant, at every site. -/
def BankRepairDigitWordAcc {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  ∀ i, BankRepairDigitWordAccAt ring h p i

theorem bankRepairDigitWordAccScrub {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hk : ∀ i, h.workerKind i = .empty)
    (hc : ∀ i, h.workerCursor i = .empty) :
    BankRepairDigitWordAcc ring h p := by
  intro i
  refine ⟨fun _ _ _ h1 => ?_, fun _ _ h1 => ?_, fun _ _ _ _ _ h1 => ?_⟩
  · rw [hk i] at h1
    cases h1
  · rw [hc i] at h1
    cases h1
  · rw [hc i] at h1
    cases h1

/-- A site whose colours and SI record are untouched keeps its clauses
when no u bit changes. -/
theorem bankRepairDigitWordAccAtSi {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c) (i : Fin n)
    (hat : BankRepairDigitWordAccAt ring h p i)
    (hsi : (p' i).si = (p i).si) (hu : ∀ i, (p' i).u = (p i).u)
    (hroot : h'.root = h.root)
    (hk : h'.workerKind i = h.workerKind i)
    (hc : h'.workerCursor i = h.workerCursor i) :
    BankRepairDigitWordAccAt ring h' p' i := by
  obtain ⟨h1, h2, h3⟩ := hat
  have hf := bankRepairDigitWordFoldsCongr ring h.root p p' hu
  refine ⟨fun idx z a hk' => ?_, fun target idx hc' => ?_,
    fun target idx z parity trailing hc' => ?_⟩
  · rw [hk] at hk'
    obtain ⟨hph, hpos, hz, ha⟩ := h1 idx z a hk'
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold cwPhasePrefixPhysical at hph ⊢
      rw [hsi]
      exact hph
    · rw [hroot]
      exact hpos
    · rw [hroot, (hf 0 idx.val).1]
      exact hz
    · rw [hroot, (hf 0 idx.val).2.1]
      exact ha
  · rw [hc] at hc'
    rw [hsi, hroot]
    exact h2 target idx hc'
  · rw [hc] at hc'
    rw [hsi, hroot, (hf _ idx.val).2.2.1, (hf _ idx.val).2.2.2.1,
      (hf _ idx.val).2.2.2.2]
    exact h3 _ _ _ _ _ hc'

theorem bankRepairDigitWordAccAtFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c) (i : Fin n)
    (hat : BankRepairDigitWordAccAt ring h p i)
    (hpi : p' i = p i) (hu : ∀ i, (p' i).u = (p i).u)
    (hroot : h'.root = h.root)
    (hk : h'.workerKind i = h.workerKind i)
    (hc : h'.workerCursor i = h.workerCursor i) :
    BankRepairDigitWordAccAt ring h' p' i :=
  bankRepairDigitWordAccAtSi ring h h' p p' i hat (congrArg ProjW.si hpi) hu
    hroot hk hc

/-- B0 (successful `backwardsMove`) preserves the accumulator invariant. -/
theorem bankRepairDigitWordAccBzeroLeaf {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "B0")
    {target : Fin n} {idx : Fin (c.t + 1)}
    (hcj : h.workerCursor (ring.rightNeighbor e) = .back target idx)
    (hcurx : (workerW (p e) (p (ring.rightNeighbor e))).x.cur = .BACK)
    (hjx : (workerW (p e) (p (ring.rightNeighbor e))).x.j.val + 1 =
      idx.val)
    (hroot : h'.root = h.root) (hwk : h'.workerKind = h.workerKind)
    (hwc : h'.workerCursor =
      BlockA.wordPut (BlockA.wordPut h.workerCursor (ring.rightNeighbor e)
        .empty) e
        (.back target (workerW (p e) (p (ring.rightNeighbor e))).x.j)) :
    BankRepairDigitWordAcc ring h' (phiW ring p e) := by
  obtain ⟨hfree, hkindj⟩ := bankRepairDigitSiStepRowBzero c _ _ _ _ hrow
  have hu : ∀ i, ((phiW ring p e) i).u = (p i).u := fun i =>
    congrArg Prod.fst (bankRepairDigitQuietRowVisible ring p e
      (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide)
      (by rw [hrow]; decide) i)
  obtain ⟨hsx, _⟩ := bankRepairDigitPhiWSites ring p e hne
  have hfreeE : (p e).si.kind = .OFF := by
    simp only [freeSI, Bool.and_eq_true, beq_iff_eq] at hfree
    exact hfree.1
  have hge : e = PPL.shiftRight ring h.root
      (PPL.cyclicOffset ring h.root target - c.t +
        (workerW (p e) (p (ring.rightNeighbor e))).x.j.val) := by
    apply bankRepairDigitShiftPred ring h.root e
    exact ((hacc _).2.1 target idx hcj).2.2.trans
      (congrArg (PPL.shiftRight ring h.root) (by omega))
  intro i
  by_cases hie : i = e
  · rw [hie]
    refine ⟨fun idx' z a hk => ?_, fun target' idx' hc => ?_,
      fun target' idx' z parity trailing hc => ?_⟩
    · rw [hwk] at hk
      have h0 := ((hacc e).1 idx' z a hk).1.1
      rw [hfreeE] at h0
      cases h0
    · rw [hwc] at hc
      simp only [BlockA.wordPut, if_pos rfl] at hc
      injection hc with h1 h2
      subst h1 h2
      rw [hsx, hroot]
      exact ⟨hcurx, rfl, hge⟩
    · rw [hwc] at hc
      simp only [BlockA.wordPut, if_pos rfl] at hc
      cases hc
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij]
      refine ⟨fun idx' z a hk => ?_, fun target' idx' hc => ?_,
        fun target' idx' z parity trailing hc => ?_⟩
      · rw [hwk] at hk
        exact absurd ((hacc _).1 idx' z a hk).1.1 hkindj
      · rw [hwc] at hc
        simp only [BlockA.wordPut, if_neg hne, if_pos rfl] at hc
        cases hc
      · rw [hwc] at hc
        simp only [BlockA.wordPut, if_neg hne, if_pos rfl] at hc
        cases hc
    · exact bankRepairDigitWordAccAtFrame ring h h' p (phiW ring p e) i
        (hacc i) (cwPhiWFrame ring p e i hie hij) hu hroot
        (by rw [hwk])
        (by rw [hwc]; simp only [BlockA.wordPut, if_neg hie, if_neg hij])

/-- B1 (successful `backwardsInit`) preserves the accumulator invariant. -/
theorem bankRepairDigitWordAccBoneLeaf {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "B1")
    {target : Fin n} {idx : Fin (c.t + 1)}
    (hcj : h.workerCursor (ring.rightNeighbor e) = .back target idx)
    (hidx : idx.val = 1)
    (hjx : (workerW (p e) (p (ring.rightNeighbor e))).x.j.val = 0)
    (hroot : h'.root = h.root) (hwk : h'.workerKind = h.workerKind)
    (hwc : h'.workerCursor =
      BlockA.wordPut (BlockA.wordPut h.workerCursor (ring.rightNeighbor e)
        .empty) e
        (.sum target (workerW (p e) (p (ring.rightNeighbor e))).x.j
          false false true)) :
    BankRepairDigitWordAcc ring h' (phiW ring p e) := by
  obtain ⟨hfree, hkindj, hxeq⟩ := bankRepairDigitSiStepRowBone c _ _ _ _ hrow
  have hu : ∀ i, ((phiW ring p e) i).u = (p i).u := fun i =>
    congrArg Prod.fst (bankRepairDigitQuietRowVisible ring p e
      (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide)
      (by rw [hrow]; decide) i)
  obtain ⟨hsx, _⟩ := bankRepairDigitPhiWSites ring p e hne
  have hfreeE : (p e).si.kind = .OFF := by
    simp only [freeSI, Bool.and_eq_true, beq_iff_eq] at hfree
    exact hfree.1
  have hxk : (workerW (p e) (p (ring.rightNeighbor e))).x.kind = .OFF := by
    rw [show (workerW (p e) (p (ring.rightNeighbor e))).x = _ from hxeq]
    exact hfreeE
  have hxs : (workerW (p e) (p (ring.rightNeighbor e))).x.cur = .SUM ∧
      (workerW (p e) (p (ring.rightNeighbor e))).x.z = false ∧
      (workerW (p e) (p (ring.rightNeighbor e))).x.p = false ∧
      (workerW (p e) (p (ring.rightNeighbor e))).x.a = true := by
    rw [show (workerW (p e) (p (ring.rightNeighbor e))).x = _ from hxeq]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hge : e = PPL.shiftRight ring h.root
      (PPL.cyclicOffset ring h.root target - c.t +
        (workerW (p e) (p (ring.rightNeighbor e))).x.j.val) := by
    apply bankRepairDigitShiftPred ring h.root e
    exact ((hacc _).2.1 target idx hcj).2.2.trans
      (congrArg (PPL.shiftRight ring h.root) (by omega))
  have h0 := bankRepairDigitSumFoldZero ring h.root (phiW ring p e)
    (PPL.cyclicOffset ring h.root target)
  intro i
  by_cases hie : i = e
  · rw [hie]
    refine ⟨fun idx' z a hk => ?_, fun target' idx' hc => ?_,
      fun target' idx' z parity trailing hc => ?_⟩
    · rw [hwk] at hk
      have h1 := ((hacc e).1 idx' z a hk).1.1
      rw [hfreeE] at h1
      cases h1
    · rw [hwc] at hc
      simp only [BlockA.wordPut, if_pos rfl] at hc
      cases hc
    · rw [hwc] at hc
      simp only [BlockA.wordPut, if_pos rfl] at hc
      injection hc with h1 h2 h3 h4 h5
      subst h1 h2 h3 h4 h5
      rw [hsx, hroot, hjx, h0.1, h0.2.1, h0.2.2]
      rw [hjx] at hge
      exact ⟨hxk, hxs.1, rfl, hxs.2.1, hxs.2.2.1, hxs.2.2.2, hge, rfl, rfl,
        rfl⟩
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij]
      refine ⟨fun idx' z a hk => ?_, fun target' idx' hc => ?_,
        fun target' idx' z parity trailing hc => ?_⟩
      · rw [hwk] at hk
        exact absurd ((hacc _).1 idx' z a hk).1.1 hkindj
      · rw [hwc] at hc
        simp only [BlockA.wordPut, if_neg hne, if_pos rfl] at hc
        cases hc
      · rw [hwc] at hc
        simp only [BlockA.wordPut, if_neg hne, if_pos rfl] at hc
        cases hc
    · exact bankRepairDigitWordAccAtFrame ring h h' p (phiW ring p e) i
        (hacc i) (cwPhiWFrame ring p e i hie hij) hu hroot
        (by rw [hwk])
        (by rw [hwc]; simp only [BlockA.wordPut, if_neg hie, if_neg hij])

/-- S0 (successful `sumMove`) preserves the accumulator invariant: the
responder's z/parity/trailing are the folds over one more source. -/
theorem bankRepairDigitWordAccSzeroLeaf {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "S0")
    {target : Fin n} {idx : Fin (c.t + 1)} {z parity trailing : Bool}
    (hce : h.workerCursor e = .sum target idx z parity trailing)
    (hyc : (workerW (p e) (p (ring.rightNeighbor e))).y.cur = .SUM)
    (hyj : (workerW (p e) (p (ring.rightNeighbor e))).y.j.val = idx.val + 1)
    (hyz : (workerW (p e) (p (ring.rightNeighbor e))).y.z =
      (BlockA.wordFold idx z parity trailing (p e).u).1)
    (hyp : (workerW (p e) (p (ring.rightNeighbor e))).y.p =
      (BlockA.wordFold idx z parity trailing (p e).u).2.1)
    (hya : (workerW (p e) (p (ring.rightNeighbor e))).y.a =
      (BlockA.wordFold idx z parity trailing (p e).u).2.2)
    (hroot : h'.root = h.root) (hwk : h'.workerKind = h.workerKind)
    (hwc : h'.workerCursor =
      BlockA.wordPut (BlockA.wordPut h.workerCursor e .empty)
        (ring.rightNeighbor e)
        (.sum target (workerW (p e) (p (ring.rightNeighbor e))).y.j
          (workerW (p e) (p (ring.rightNeighbor e))).y.z
          (workerW (p e) (p (ring.rightNeighbor e))).y.p
          (workerW (p e) (p (ring.rightNeighbor e))).y.a)) :
    BankRepairDigitWordAcc ring h' (phiW ring p e) := by
  obtain ⟨hxk, hfreeJ, hyk⟩ := bankRepairDigitSiStepRowSzero c _ _ _ _ hrow
  have hu : ∀ i, ((phiW ring p e) i).u = (p i).u := fun i =>
    congrArg Prod.fst (bankRepairDigitQuietRowVisible ring p e
      (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide)
      (by rw [hrow]; decide) i)
  obtain ⟨_, hsy⟩ := bankRepairDigitPhiWSites ring p e hne
  have hfreeJ' : (p (ring.rightNeighbor e)).si.kind = .OFF := by
    simp only [freeSI, Bool.and_eq_true, beq_iff_eq] at hfreeJ
    exact hfreeJ.1
  obtain ⟨-, -, -, -, -, -, he, hz, hpar, htr⟩ :=
    (hacc e).2.2 target idx z parity trailing hce
  have hsrc : cwSourceBit ring h.root p (PPL.cyclicOffset ring h.root target)
      idx.val = (p e).u := by
    unfold cwSourceBit cwBit
    rw [← he]
  have hf := bankRepairDigitWordFoldsCongr ring h.root p (phiW ring p e) hu
  have hs := bankRepairDigitSumFoldStep ring h.root p
    (PPL.cyclicOffset ring h.root target) idx.val
  have hgj : ring.rightNeighbor e = PPL.shiftRight ring h.root
      (PPL.cyclicOffset ring h.root target - c.t +
        (workerW (p e) (p (ring.rightNeighbor e))).y.j.val) := by
    calc ring.rightNeighbor e
        = ring.rightNeighbor (PPL.shiftRight ring h.root
            (PPL.cyclicOffset ring h.root target - c.t + idx.val)) :=
          congrArg _ he
      _ = PPL.shiftRight ring h.root
            (PPL.cyclicOffset ring h.root target - c.t + idx.val + 1) :=
          (WordPhase.wordPhaseShiftSucc ring h.root _).symm
      _ = _ := congrArg (PPL.shiftRight ring h.root) (by omega)
  intro i
  by_cases hie : i = e
  · rw [hie]
    refine ⟨fun idx' z' a hk => ?_, fun target' idx' hc => ?_,
      fun target' idx' z' parity' trailing' hc => ?_⟩
    · rw [hwk] at hk
      have h1 := ((hacc e).1 idx' z' a hk).1.1
      rw [show (p e).si.kind = .OFF from hxk] at h1
      cases h1
    · rw [hwc] at hc
      simp only [BlockA.wordPut, if_neg hne.symm, if_pos rfl] at hc
      cases hc
    · rw [hwc] at hc
      simp only [BlockA.wordPut, if_neg hne.symm, if_pos rfl] at hc
      cases hc
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij]
      refine ⟨fun idx' z' a hk => ?_, fun target' idx' hc => ?_,
        fun target' idx' z' parity' trailing' hc => ?_⟩
      · rw [hwk] at hk
        have h1 := ((hacc _).1 idx' z' a hk).1.1
        rw [hfreeJ'] at h1
        cases h1
      · rw [hwc] at hc
        simp only [BlockA.wordPut, if_pos rfl] at hc
        cases hc
      · rw [hwc] at hc
        simp only [BlockA.wordPut, if_pos rfl] at hc
        injection hc with h1 h2 h3 h4 h5
        subst h1 h2 h3 h4 h5
        rw [hsy, hroot, (hf _ _).2.2.1, (hf _ _).2.2.2.1, (hf _ _).2.2.2.2,
          hyj, hs.1, hs.2.1, hs.2.2, ← hz, ← hpar, ← htr, hsrc]
        refine ⟨hyk, hyc, rfl, rfl, rfl, rfl, by rw [← hyj]; exact hgj, ?_, ?_,
          ?_⟩
        · rw [hyz]
          rfl
        · rw [hyp]
          rfl
        · rw [hya]
          show (if idx.val = 0 then true else trailing && (p e).u) = _
          by_cases h0 : idx.val = 0
          · rw [if_pos h0, if_pos h0, htr, h0]
            rfl
          · rw [if_neg h0, if_neg h0]
    · exact bankRepairDigitWordAccAtFrame ring h h' p (phiW ring p e) i
        (hacc i) (cwPhiWFrame ring p e i hie hij) hu hroot
        (by rw [hwk])
        (by rw [hwc]; simp only [BlockA.wordPut, if_neg hie, if_neg hij])

/-- T11 item 2, B0: every `backwardsMove` worker step preserves the
accumulator invariant (success moves the cursor left, failure clears). -/
theorem bankRepairDigitWordAccBzero {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool) (hn : 2 ≤ n)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
      .backwardsMove) :
    BankRepairDigitWordAcc ring (BlockA.wordWorkerNext ring h p e request)
      (phiW ring p e) := by
  have hne := EWord.rightNeighborDifferent ring hn e
  have hrow := (bankRepairDigitWorkerCaseRows _ _).1 hcase
  unfold BlockA.wordWorkerNext
  dsimp only
  simp only [hcase]
  split
  · rename_i target idx hcj
    split
    · rename_i hC
      exact bankRepairDigitWordAccBzeroLeaf ring h _ p e hne hacc hrow hcj
        hC.2.2.2.2.1 hC.2.2.2.2.2 rfl rfl rfl
    · exact bankRepairDigitWordAccScrub ring _ _ (fun _ => rfl) (fun _ => rfl)
  all_goals exact bankRepairDigitWordAccScrub ring _ _ (fun _ => rfl) (fun _ => rfl)

/-- T11 item 2, B1: every `backwardsInit` worker step preserves it; the
new SUM cursor starts at the first source with the empty folds. -/
theorem bankRepairDigitWordAccBone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool) (hn : 2 ≤ n)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
      .backwardsInit) :
    BankRepairDigitWordAcc ring (BlockA.wordWorkerNext ring h p e request)
      (phiW ring p e) := by
  have hne := EWord.rightNeighborDifferent ring hn e
  have hrow := (bankRepairDigitWorkerCaseRows _ _).2.1 hcase
  unfold BlockA.wordWorkerNext
  dsimp only
  simp only [hcase]
  split
  · rename_i target idx hcj
    split
    · rename_i hC
      exact bankRepairDigitWordAccBoneLeaf ring h _ p e hne hacc hrow hcj
        hC.2.2.1 hC.2.2.2.2.2.2 rfl rfl rfl
    · exact bankRepairDigitWordAccScrub ring _ _ (fun _ => rfl) (fun _ => rfl)
  all_goals exact bankRepairDigitWordAccScrub ring _ _ (fun _ => rfl) (fun _ => rfl)

/-- T11 item 2, S0: every `sumMove` worker step preserves it. -/
theorem bankRepairDigitWordAccSzero {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool) (hn : 2 ≤ n)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
      .sumMove) :
    BankRepairDigitWordAcc ring (BlockA.wordWorkerNext ring h p e request)
      (phiW ring p e) := by
  have hne := EWord.rightNeighborDifferent ring hn e
  have hrow := (bankRepairDigitWorkerCaseRows _ _).2.2 hcase
  unfold BlockA.wordWorkerNext
  dsimp only
  simp only [hcase]
  split
  · rename_i target idx z parity trailing hce
    split
    · rename_i hC
      obtain ⟨-, -, -, -, -, -, -, -, -, hyc, hyj, hyz, hyp, hya⟩ := hC
      exact bankRepairDigitWordAccSzeroLeaf ring h _ p e hne hacc hrow hce
        hyc hyj hyz hyp hya rfl rfl rfl
    · exact bankRepairDigitWordAccScrub ring _ _ (fun _ => rfl) (fun _ => rfl)
  all_goals exact bankRepairDigitWordAccScrub ring _ _ (fun _ => rfl) (fun _ => rfl)

/-- T11 item 2 at the full monitor step: in the worker phase, B0, B1 and
S0 edges preserve the accumulator invariant (a hard start scrubs). -/
theorem bankRepairDigitWordAccRows {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (hn : 2 ≤ n)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hphase : h.phase = .worker)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
        .backwardsMove ∨
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) =
        .backwardsInit ∨
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .sumMove) :
    BankRepairDigitWordAcc ring (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  by_cases hno : BlockA.wordIsHardStart ring h p e
  · have hstep : BlockA.wordT ring h p e (phiW ring p e) =
        BlockA.wordHardLaunch h e (ring.rightNeighbor e) := by
      simp [BlockA.wordT, hphase, hno]
    rw [hstep]
    exact bankRepairDigitWordAccScrub ring _ _ (fun _ => rfl) (fun _ => rfl)
  · have hstep : BlockA.wordT ring h p e (phiW ring p e) =
        BlockA.wordWorkerNext ring h p e
          (BlockA.wordRequestNext ring h p e) := by
      simp [BlockA.wordT, hphase, hno]
    rw [hstep]
    rcases hcase with hc | hc | hc
    · exact bankRepairDigitWordAccBzero ring h p e _ hn hacc hc
    · exact bankRepairDigitWordAccBone ring h p e _ hn hacc hc
    · exact bankRepairDigitWordAccSzero ring h p e _ hn hacc hc

end L3.RenewalReferenceClock

/-!
T12 item 1: the accumulator invariant along whole W runs. A token
invariant (at most one worker token: a prefix tag, or a target with one
cursor, or a ready tag) and phase clauses (no colour outside the worker
and done phases; no prefix colour and no cursor once A0 has fired) are
carried with `BankRepairDigitWordAcc`. I0, P1, P3, S1, A1, B0, B1, S0,
the frame and erase rows, the validate phase and the done phase all
preserve the bundle. See comms/T12-notes.md.
-/

namespace L3.RenewalReferenceClock

open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option linter.unusedSimpArgs false

theorem bankRepairDigitOffsetShift {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (d : Nat) (hd : d < n) :
    PPL.cyclicOffset ring root (PPL.shiftRight ring root d) = d := by
  have hr := root.isLt
  show ((root.val + d) % n + n - root.val) % n = d
  by_cases h1 : root.val + d < n
  · rw [Nat.mod_eq_of_lt h1, show root.val + d + n - root.val = d + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  · rw [Nat.mod_eq_sub_mod (show n ≤ root.val + d by omega),
      Nat.mod_eq_of_lt (show root.val + d - n < n by omega),
      show root.val + d - n + n - root.val = d by omega, Nat.mod_eq_of_lt hd]

/-- One more follower in the prefix folds. -/
theorem bankRepairDigitPrefixFoldStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c) (k : Nat) :
    cwPrefixOr ring root p (k + 1) =
      (cwPrefixOr ring root p k || cwBit ring root p (k + 1)) ∧
    cwPrefixAnd ring root p (k + 1) =
      (cwPrefixAnd ring root p k && cwBit ring root p (k + 1)) := by
  refine ⟨?_, ?_⟩
  · unfold cwPrefixOr
    rw [List.range_succ, List.foldl_append]
    rfl
  · unfold cwPrefixAnd
    rw [List.range_succ, List.foldl_append]
    rfl

theorem bankRepairDigitWorkerCaseMore {c : Compiled} (x y : ProjW c) :
    (BlockA.workerCase x y = .prefixMove → (workerW x y).row = "P1") ∧
    (BlockA.workerCase x y = .erase → (workerW x y).row = "I1") ∧
    (BlockA.workerCase x y = .frame →
      (workerW x y).row ≠ "I0" ∧ (workerW x y).row ≠ "I1" ∧
      (workerW x y).row ≠ "P0" ∧ (workerW x y).row ≠ "P1" ∧
      (workerW x y).row ≠ "P2" ∧ (workerW x y).row ≠ "P3" ∧
      (workerW x y).row ≠ "B0" ∧ (workerW x y).row ≠ "B1" ∧
      (workerW x y).row ≠ "S0" ∧ (workerW x y).row ≠ "S1" ∧
      (workerW x y).row ≠ "A1" ∧ (workerW x y).row ≠ "A0") := by
  have key : bankRepairDigitHolds
      (fun w : BlockA.WorkerReceiptCase =>
        (w = .prefixMove → (workerW x y).row = "P1") ∧
        (w = .erase → (workerW x y).row = "I1") ∧
        (w = .frame →
          (workerW x y).row ≠ "I0" ∧ (workerW x y).row ≠ "I1" ∧
          (workerW x y).row ≠ "P0" ∧ (workerW x y).row ≠ "P1" ∧
          (workerW x y).row ≠ "P2" ∧ (workerW x y).row ≠ "P3" ∧
          (workerW x y).row ≠ "B0" ∧ (workerW x y).row ≠ "B1" ∧
          (workerW x y).row ≠ "S0" ∧ (workerW x y).row ≠ "S1" ∧
          (workerW x y).row ≠ "A1" ∧ (workerW x y).row ≠ "A0"))
      (BlockA.workerCase x y) := by
    unfold BlockA.workerCase
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals simp_all
  exact key

/-- The frame row `F` of `siStep` copies both SI records and u bits. -/
theorem bankRepairDigitSiStepFrame (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row ≠ "I0" ∧
      (siStep c ox oy post hard).row ≠ "I1" ∧
      (siStep c ox oy post hard).row ≠ "P0" ∧
      (siStep c ox oy post hard).row ≠ "P1" ∧
      (siStep c ox oy post hard).row ≠ "P2" ∧
      (siStep c ox oy post hard).row ≠ "P3" ∧
      (siStep c ox oy post hard).row ≠ "B0" ∧
      (siStep c ox oy post hard).row ≠ "B1" ∧
      (siStep c ox oy post hard).row ≠ "S0" ∧
      (siStep c ox oy post hard).row ≠ "S1" ∧
      (siStep c ox oy post hard).row ≠ "A1" ∧
      (siStep c ox oy post hard).row ≠ "A0") :
    (siStep c ox oy post hard).x = ox.si ∧
      (siStep c ox oy post hard).y = oy.si ∧
      (siStep c ox oy post hard).uX = ox.u ∧
      (siStep c ox oy post hard).uY = oy.u := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t =>
      (r.row ≠ "I0" ∧ r.row ≠ "I1" ∧ r.row ≠ "P0" ∧ r.row ≠ "P1" ∧
        r.row ≠ "P2" ∧ r.row ≠ "P3" ∧ r.row ≠ "B0" ∧ r.row ≠ "B1" ∧
        r.row ≠ "S0" ∧ r.row ≠ "S1" ∧ r.row ≠ "A1" ∧ r.row ≠ "A0") →
      r.x = ox.si ∧ r.y = oy.si ∧ r.uX = ox.u ∧ r.uY = oy.u)
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals simp at hr ⊢
  exact key hr

/-- The erase row I1 clears exactly the hard sites. -/
theorem bankRepairDigitSiStepRowIone (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row = "I1") :
    (siStep c ox oy post hard).x =
        (if hard.hardLeft = true then offSI c.t else ox.si) ∧
      (siStep c ox oy post hard).y =
        (if hard.hardRight = true then offSI c.t else oy.si) := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "I1" →
      r.x = (if hard.hardLeft = true then offSI c.t else ox.si) ∧
      r.y = (if hard.hardRight = true then offSI c.t else oy.si))
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals simp at hr ⊢
  exact key hr

theorem bankRepairDigitSiStepRowPoneFields (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row = "P1") :
    (siStep c ox oy post hard).y.cur = .NONE ∧
      (siStep c ox oy post hard).uX = ox.u ∧
      (siStep c ox oy post hard).uY = oy.u := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "P1" →
      r.y.cur = .NONE ∧ r.uX = ox.u ∧ r.uY = oy.u)
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals simp at hr ⊢
  exact key hr

theorem bankRepairDigitUniqueSite {n : Nat} {A : Type} (f : Fin n → A)
    (a0 : A) (s s' : Fin n) (hs : f s ≠ a0)
    (hf : ∀ i, i ≠ s' → f i = a0) :
    ∀ i, i ≠ s → f i = a0 := by
  have hss : s = s' := Classical.byContradiction fun hne => hs (hf s hne)
  rw [hss]
  exact hf

theorem bankRepairDigitPutSame {n : Nat} {A : Type} (f : Fin n → A)
    (r : Fin n) (v : A) : BlockA.wordPut f r v r = v := by
  simp [BlockA.wordPut]

theorem bankRepairDigitPutOther {n : Nat} {A : Type} (f : Fin n → A)
    (r i : Fin n) (v : A) (hi : i ≠ r) : BlockA.wordPut f r v i = f i := by
  simp [BlockA.wordPut, hi]

theorem bankRepairDigitPutMove {n : Nat} {A : Type} (f : Fin n → A)
    (a0 : A) (q r : Fin n) (v : A) (hf : ∀ i, i ≠ q → f i = a0) :
    ∀ i, i ≠ r → BlockA.wordPut (BlockA.wordPut f q a0) r v i = a0 := by
  intro i hi
  rw [bankRepairDigitPutOther _ _ _ _ hi]
  by_cases hq : i = q
  · rw [hq, bankRepairDigitPutSame]
  · rw [bankRepairDigitPutOther _ _ _ _ hq, hf i hq]

theorem bankRepairDigitPutClear {n : Nat} {A : Type} (f : Fin n → A)
    (a0 : A) (q : Fin n) (hf : ∀ i, i ≠ q → f i = a0) :
    ∀ i, BlockA.wordPut f q a0 i = a0 := by
  intro i
  by_cases hi : i = q
  · rw [hi, bankRepairDigitPutSame]
  · rw [bankRepairDigitPutOther _ _ _ _ hi, hf i hi]

/-- T12 item 1: at most one worker token. Either no colour, or a single
prefix tag and no cursor, or a single target tag with at most one cursor,
or a single ready tag and no cursor. -/
def BankRepairDigitWordTok {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) : Prop :=
  ((∀ i, h.workerKind i = .empty) ∧ (∀ i, h.workerCursor i = .empty)) ∨
  (∃ s idx z a, h.workerKind s = .prefix idx z a ∧
    (∀ i, i ≠ s → h.workerKind i = .empty) ∧
    (∀ i, h.workerCursor i = .empty)) ∨
  (∃ T, h.workerKind T = .target T true ∧
    (∀ i, i ≠ T → h.workerKind i = .empty) ∧
    ∃ q, ∀ i, i ≠ q → h.workerCursor i = .empty) ∨
  (∃ T, h.workerKind T = .ready T ∧
    (∀ i, i ≠ T → h.workerKind i = .empty) ∧
    (∀ i, h.workerCursor i = .empty))

theorem bankRepairDigitWordTokPrefix {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (htok : BankRepairDigitWordTok h)
    (e : Fin n) {idx : Fin (c.t + 1)} {z a : Bool}
    (hk : h.workerKind e = .prefix idx z a) :
    (∀ i, i ≠ e → h.workerKind i = .empty) ∧
      (∀ i, h.workerCursor i = .empty) := by
  have hne : h.workerKind e ≠ .empty := by
    rw [hk]
    intro h0
    cases h0
  rcases htok with ⟨hk0, _⟩ | ⟨s, _, _, _, _, hko, hco⟩ |
      ⟨T, hkT, hko, _⟩ | ⟨T, hkT, hko, _⟩
  · exact absurd (hk0 e) hne
  · exact ⟨bankRepairDigitUniqueSite _ _ e s hne hko, hco⟩
  · exfalso
    by_cases heT : e = T
    · rw [heT, hkT] at hk
      cases hk
    · exact hne (hko e heT)
  · exfalso
    by_cases heT : e = T
    · rw [heT, hkT] at hk
      cases hk
    · exact hne (hko e heT)

theorem bankRepairDigitWordTokReady {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (htok : BankRepairDigitWordTok h)
    (e : Fin n) {s : Fin n} (hk : h.workerKind e = .ready s) :
    (∀ i, i ≠ e → h.workerKind i = .empty) ∧
      (∀ i, h.workerCursor i = .empty) := by
  have hne : h.workerKind e ≠ .empty := by
    rw [hk]
    intro h0
    cases h0
  rcases htok with ⟨hk0, _⟩ | ⟨s', _, _, _, hks, hko, _⟩ |
      ⟨T, hkT, hko, _⟩ | ⟨T, _, hko, hco⟩
  · exact absurd (hk0 e) hne
  · exfalso
    by_cases heT : e = s'
    · rw [heT, hks] at hk
      cases hk
    · exact hne (hko e heT)
  · exfalso
    by_cases heT : e = T
    · rw [heT, hkT] at hk
      cases hk
    · exact hne (hko e heT)
  · exact ⟨bankRepairDigitUniqueSite _ _ e T hne hko, hco⟩

theorem bankRepairDigitWordTokCursor {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (htok : BankRepairDigitWordTok h)
    (a : Fin n) (ha : h.workerCursor a ≠ .empty) :
    ∃ T, h.workerKind T = .target T true ∧
      (∀ i, i ≠ T → h.workerKind i = .empty) ∧
      ∀ i, i ≠ a → h.workerCursor i = .empty := by
  rcases htok with ⟨_, hc0⟩ | ⟨_, _, _, _, _, _, hco⟩ |
      ⟨T, hkT, hko, q, hcq⟩ | ⟨_, _, _, hco⟩
  · exact absurd (hc0 a) ha
  · exact absurd (hco a) ha
  · exact ⟨T, hkT, hko, bankRepairDigitUniqueSite _ _ a q ha hcq⟩
  · exact absurd (hco a) ha

theorem bankRepairDigitWordTokCongr {n : Nat} {c : Compiled}
    (h h' : BlockA.WordControl n c)
    (hk : h'.workerKind = h.workerKind) (hc : h'.workerCursor = h.workerCursor)
    (htok : BankRepairDigitWordTok h) : BankRepairDigitWordTok h' := by
  unfold BankRepairDigitWordTok
  rw [hk, hc]
  exact htok

/-- A cursor move (B0, B1, S0) keeps the single token. -/
theorem bankRepairDigitWordTokCursorMove {n : Nat} {c : Compiled}
    (h h' : BlockA.WordControl n c) (htok : BankRepairDigitWordTok h)
    (a b : Fin n) (v : BlockA.WorkerTag n c.t)
    (ha : h.workerCursor a ≠ .empty)
    (hwk : h'.workerKind = h.workerKind)
    (hwc : h'.workerCursor =
      BlockA.wordPut (BlockA.wordPut h.workerCursor a .empty) b v) :
    BankRepairDigitWordTok h' := by
  obtain ⟨T, hkT, hko, hco⟩ := bankRepairDigitWordTokCursor h htok a ha
  refine Or.inr (Or.inr (Or.inl ⟨T, by rw [hwk]; exact hkT,
    by rw [hwk]; exact hko, b, ?_⟩))
  rw [hwc]
  exact bankRepairDigitPutMove _ _ a b v hco

theorem bankRepairDigitWordAccAtEmpty {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (i : Fin n)
    (hk : h.workerKind i = .empty) (hc : h.workerCursor i = .empty) :
    BankRepairDigitWordAccAt ring h p i := by
  refine ⟨fun _ _ _ h1 => ?_, fun _ _ h1 => ?_, fun _ _ _ _ _ h1 => ?_⟩
  · rw [hk] at h1
    cases h1
  · rw [hc] at h1
    cases h1
  · rw [hc] at h1
    cases h1

/-- With no prefix colour and no cursor the invariant is vacuous. -/
theorem bankRepairDigitWordAccNoColour {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hk : ∀ i idx z a, h.workerKind i ≠ .prefix idx z a)
    (hc : ∀ i, h.workerCursor i = .empty) :
    BankRepairDigitWordAcc ring h p := by
  intro i
  refine ⟨fun idx z a h1 => absurd h1 (hk i idx z a), fun _ _ h1 => ?_,
    fun _ _ _ _ _ h1 => ?_⟩
  · rw [hc] at h1
    cases h1
  · rw [hc] at h1
    cases h1

theorem bankRepairDigitWordAccSingle {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (r : Fin n)
    (hk : ∀ i, i ≠ r → h.workerKind i = .empty)
    (hc : ∀ i, i ≠ r → h.workerCursor i = .empty)
    (hat : BankRepairDigitWordAccAt ring h p r) :
    BankRepairDigitWordAcc ring h p := by
  intro i
  by_cases hi : i = r
  · rw [hi]
    exact hat
  · exact bankRepairDigitWordAccAtEmpty ring h p i (hk i hi) (hc i hi)

/-- A step that keeps every colour keeps the invariant if each SI record
is unchanged or uncoloured and no u bit changes. -/
theorem bankRepairDigitWordAccKeep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hu : ∀ i, (p' i).u = (p i).u) (hroot : h'.root = h.root)
    (hk : h'.workerKind = h.workerKind) (hc : h'.workerCursor = h.workerCursor)
    (hsite : ∀ i, (p' i).si = (p i).si ∨
      (h.workerKind i = .empty ∧ h.workerCursor i = .empty)) :
    BankRepairDigitWordAcc ring h' p' := by
  intro i
  rcases hsite i with hsi | ⟨hki, hci⟩
  · exact bankRepairDigitWordAccAtSi ring h h' p p' i (hacc i) hsi hu hroot
      (by rw [hk]) (by rw [hc])
  · exact bankRepairDigitWordAccAtEmpty ring h' p' i (by rw [hk]; exact hki)
      (by rw [hc]; exact hci)

/-- T12 item 1: the run bundle. The single-token invariant, no colour
outside the worker and done phases, no prefix colour and no cursor in the
done phase, and the accumulator invariant. -/
def BankRepairDigitWordAccRun {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  BankRepairDigitWordTok h ∧
  ((h.phase = .awaitRequest ∨ h.phase = .validate) →
    (∀ i, h.workerKind i = .empty) ∧ (∀ i, h.workerCursor i = .empty)) ∧
  (h.phase = .done →
    (∀ i idx z a, h.workerKind i ≠ .prefix idx z a) ∧
      (∀ i, h.workerCursor i = .empty)) ∧
  BankRepairDigitWordAcc ring h p

theorem bankRepairDigitWordAccRunIdle {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hk : ∀ i, h.workerKind i = .empty) (hc : ∀ i, h.workerCursor i = .empty) :
    BankRepairDigitWordAccRun ring h p :=
  ⟨Or.inl ⟨hk, hc⟩, fun _ => ⟨hk, hc⟩,
    fun _ => ⟨fun i idx z a h0 => (by rw [hk i] at h0; cases h0), hc⟩,
    bankRepairDigitWordAccScrub ring h p hk hc⟩

theorem bankRepairDigitWordAccRunWorkerPhase {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (hph : h.phase = .worker)
    (htok : BankRepairDigitWordTok h) (hacc : BankRepairDigitWordAcc ring h p) :
    BankRepairDigitWordAccRun ring h p := by
  refine ⟨htok, ?_, ?_, hacc⟩
  · intro h0
    rcases h0 with h0 | h0
    · rw [hph] at h0
      cases h0
    · rw [hph] at h0
      cases h0
  · intro h0
    rw [hph] at h0
    cases h0

/-- The done phase freezes the control; with no prefix colour and no
cursor the invariant holds for every physical successor. -/
theorem bankRepairDigitWordAccRunDone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c) (hrun : BankRepairDigitWordAccRun ring h p)
    (hph : h.phase = .done) : BankRepairDigitWordAccRun ring h p' := by
  obtain ⟨htok, hidle, hdone, -⟩ := hrun
  obtain ⟨hk, hc⟩ := hdone hph
  exact ⟨htok, hidle, hdone, bankRepairDigitWordAccNoColour ring h p' hk hc⟩

/-- The validated I0 launch: one prefix tag at the root, z/a empty folds. -/
theorem bankRepairDigitWordAccRunLaunch {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (he : e = h.root)
    (hx : (workerW (p e) (p (ring.rightNeighbor e))).x = launchPrefix c.t) :
    BankRepairDigitWordAccRun ring (BlockA.wordWorkerLaunch h)
      (phiW ring p e) := by
  have hkr : (BlockA.wordWorkerLaunch h).workerKind h.root =
      .prefix 0 false true := by
    simp [BlockA.wordWorkerLaunch]
  have hko : ∀ i, i ≠ h.root →
      (BlockA.wordWorkerLaunch h).workerKind i = .empty := by
    intro i hi
    simp [BlockA.wordWorkerLaunch, hi]
  have hc : ∀ i, (BlockA.wordWorkerLaunch h).workerCursor i = .empty :=
    fun _ => rfl
  have hsi : ((phiW ring p e) h.root).si = launchPrefix c.t := by
    rw [← he]
    simp only [phiW, projectedEdge, if_pos rfl]
    exact hx
  refine bankRepairDigitWordAccRunWorkerPhase ring _ _ rfl
    (Or.inr (Or.inl ⟨h.root, 0, false, true, hkr, hko, hc⟩)) ?_
  refine bankRepairDigitWordAccSingle ring _ _ h.root hko (fun i _ => hc i) ?_
  refine ⟨fun idx z a hk => ?_, fun _ _ h1 => ?_, fun _ _ _ _ _ h1 => ?_⟩
  · rw [hkr] at hk
    injection hk with h1 h2 h3
    subst h2 h3
    rw [← h1]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold cwPhasePrefixPhysical
      rw [hsi]
      exact ⟨rfl, rfl, by first | rfl | exact Fin.ext (by simp [launchPrefix]),
        rfl, rfl⟩
    · first
        | exact (WordPhase.wordPhaseShiftZero ring h.root).symm
        | simp [BlockA.wordWorkerLaunch, BlockA.wordClear,
            WordPhase.wordPhaseShiftZero]
    · first | rfl | simp [cwPrefixOr]
    · first | rfl | simp [cwPrefixAnd]
  · rw [hc] at h1
    cases h1
  · rw [hc] at h1
    cases h1

theorem bankRepairDigitWordAccRunKeep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c)
    (hrun : BankRepairDigitWordAccRun ring h p)
    (hph : h'.phase = .worker)
    (hu : ∀ i, (p' i).u = (p i).u) (hroot : h'.root = h.root)
    (hk : h'.workerKind = h.workerKind) (hc : h'.workerCursor = h.workerCursor)
    (hsite : ∀ i, (p' i).si = (p i).si ∨
      (h.workerKind i = .empty ∧ h.workerCursor i = .empty)) :
    BankRepairDigitWordAccRun ring h' p' :=
  bankRepairDigitWordAccRunWorkerPhase ring h' p' hph
    (bankRepairDigitWordTokCongr h h' hk hc hrun.1)
    (bankRepairDigitWordAccKeep ring h h' p p' hrun.2.2.2 hu hroot hk hc hsite)

/-- The frame row keeps every SI record and u bit. -/
theorem bankRepairDigitWordFrameSites {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .frame) :
    (∀ i, ((phiW ring p e) i).u = (p i).u) ∧
      ∀ i, ((phiW ring p e) i).si = (p i).si := by
  have hf := bankRepairDigitSiStepFrame c _ _ _ _
    ((bankRepairDigitWorkerCaseMore _ _).2.2 hcase)
  have hx : (workerW (p e) (p (ring.rightNeighbor e))).x = (p e).si := hf.1
  have hy : (workerW (p e) (p (ring.rightNeighbor e))).y =
      (p (ring.rightNeighbor e)).si := hf.2.1
  have hux : (workerW (p e) (p (ring.rightNeighbor e))).uX = (p e).u :=
    hf.2.2.1
  have huy : (workerW (p e) (p (ring.rightNeighbor e))).uY =
      (p (ring.rightNeighbor e)).u := hf.2.2.2
  obtain ⟨hsx, hsy⟩ := bankRepairDigitPhiWSites ring p e hne
  refine ⟨fun i => ?_, fun i => ?_⟩
  · by_cases hie : i = e
    · rw [hie]
      simp only [phiW, projectedEdge, if_pos rfl]
      exact hux
    · by_cases hij : i = ring.rightNeighbor e
      · rw [hij]
        simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
        exact huy
      · rw [cwPhiWFrame ring p e i hie hij]
  · by_cases hie : i = e
    · rw [hie, hsx, hx]
    · by_cases hij : i = ring.rightNeighbor e
      · rw [hij, hsy, hy]
      · rw [cwPhiWFrame ring p e i hie hij]

/-- The erase row I1, when the monitor keeps going, clears only
uncoloured hard sites and keeps every u bit. -/
theorem bankRepairDigitWordEraseSites {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .erase)
    (hkeep : ¬(((serW (p e) (p (ring.rightNeighbor e))).hard.hardLeft = true ∧
        (h.workerKind e ≠ .empty ∨ h.workerCursor e ≠ .empty)) ∨
      ((serW (p e) (p (ring.rightNeighbor e))).hard.hardRight = true ∧
        (h.workerKind (ring.rightNeighbor e) ≠ .empty ∨
          h.workerCursor (ring.rightNeighbor e) ≠ .empty)))) :
    (∀ i, ((phiW ring p e) i).u = (p i).u) ∧
      ∀ i, ((phiW ring p e) i).si = (p i).si ∨
        (h.workerKind i = .empty ∧ h.workerCursor i = .empty) := by
  have hrow := (bankRepairDigitWorkerCaseMore _ _).2.1 hcase
  have hvis := bankRepairDigitQuietRowVisible ring p e
    (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide)
    (by rw [hrow]; decide)
  have hI := bankRepairDigitSiStepRowIone c _ _ _ _ hrow
  have hx : (workerW (p e) (p (ring.rightNeighbor e))).x =
      (if (serW (p e) (p (ring.rightNeighbor e))).hard.hardLeft = true
       then offSI c.t else (p e).si) := hI.1
  have hy : (workerW (p e) (p (ring.rightNeighbor e))).y =
      (if (serW (p e) (p (ring.rightNeighbor e))).hard.hardRight = true
       then offSI c.t else (p (ring.rightNeighbor e)).si) := hI.2
  obtain ⟨hsx, hsy⟩ := bankRepairDigitPhiWSites ring p e hne
  refine ⟨fun i => congrArg Prod.fst (hvis i), fun i => ?_⟩
  by_cases hie : i = e
  · rw [hie]
    by_cases hL : (serW (p e) (p (ring.rightNeighbor e))).hard.hardLeft = true
    · exact Or.inr ⟨Classical.byContradiction fun h0 =>
          hkeep (Or.inl ⟨hL, Or.inl h0⟩),
        Classical.byContradiction fun h0 => hkeep (Or.inl ⟨hL, Or.inr h0⟩)⟩
    · left
      rw [hsx, hx, if_neg hL]
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij]
      by_cases hR :
          (serW (p e) (p (ring.rightNeighbor e))).hard.hardRight = true
      · exact Or.inr ⟨Classical.byContradiction fun h0 =>
            hkeep (Or.inr ⟨hR, Or.inl h0⟩),
          Classical.byContradiction fun h0 => hkeep (Or.inr ⟨hR, Or.inr h0⟩)⟩
      · left
        rw [hsy, hy, if_neg hR]
    · exact Or.inl (by rw [cwPhiWFrame ring p e i hie hij])

/-- P1 moves the single prefix tag to offset j+1 and extends its OR/AND
by the responder bit. -/
theorem bankRepairDigitWordAccRunPone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (htok : BankRepairDigitWordTok h)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "P1")
    {idx : Fin (c.t + 1)} {z a : Bool}
    (hk : h.workerKind e = .prefix idx z a)
    (hyk : (workerW (p e) (p (ring.rightNeighbor e))).y.kind = .PREFIX)
    (hyj : (workerW (p e) (p (ring.rightNeighbor e))).y.j.val = idx.val + 1)
    (hyz : (workerW (p e) (p (ring.rightNeighbor e))).y.z =
      (z || (p (ring.rightNeighbor e)).u))
    (hya : (workerW (p e) (p (ring.rightNeighbor e))).y.a =
      (a && (p (ring.rightNeighbor e)).u))
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind =
      BlockA.wordPut (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e)
        (.prefix (workerW (p e) (p (ring.rightNeighbor e))).y.j
          (workerW (p e) (p (ring.rightNeighbor e))).y.z
          (workerW (p e) (p (ring.rightNeighbor e))).y.a))
    (hwc : h'.workerCursor = h.workerCursor) :
    BankRepairDigitWordAccRun ring h' (phiW ring p e) := by
  obtain ⟨hko, hco⟩ := bankRepairDigitWordTokPrefix h htok e hk
  obtain ⟨hycur, hux, huy⟩ := bankRepairDigitSiStepRowPoneFields c _ _ _ _ hrow
  have hu : ∀ i, ((phiW ring p e) i).u = (p i).u := by
    intro i
    by_cases hie : i = e
    · rw [hie]
      simp only [phiW, projectedEdge, if_pos rfl]
      exact hux
    · by_cases hij : i = ring.rightNeighbor e
      · rw [hij]
        simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
        exact huy
      · rw [cwPhiWFrame ring p e i hie hij]
  obtain ⟨-, hsy⟩ := bankRepairDigitPhiWSites ring p e hne
  obtain ⟨-, hpos, hz, ha⟩ := (hacc e).1 idx z a hk
  have hjpos : ring.rightNeighbor e =
      PPL.shiftRight ring h.root (idx.val + 1) := by
    rw [WordPhase.wordPhaseShiftSucc, ← hpos]
  have hf := bankRepairDigitWordFoldsCongr ring h.root p (phiW ring p e) hu
  have hs := bankRepairDigitPrefixFoldStep ring h.root p idx.val
  have hbit : cwBit ring h.root p (idx.val + 1) =
      (p (ring.rightNeighbor e)).u := by
    unfold cwBit
    rw [← hjpos]
  have hkj : h'.workerKind (ring.rightNeighbor e) =
      .prefix (workerW (p e) (p (ring.rightNeighbor e))).y.j
        (workerW (p e) (p (ring.rightNeighbor e))).y.z
        (workerW (p e) (p (ring.rightNeighbor e))).y.a := by
    rw [hwk, bankRepairDigitPutSame]
  have hko' : ∀ i, i ≠ ring.rightNeighbor e → h'.workerKind i = .empty := by
    rw [hwk]
    exact bankRepairDigitPutMove _ _ e _ _ hko
  have hco' : ∀ i, h'.workerCursor i = .empty := by
    rw [hwc]
    exact hco
  refine bankRepairDigitWordAccRunWorkerPhase ring h' _ hph
    (Or.inr (Or.inl ⟨_, _, _, _, hkj, hko', hco'⟩)) ?_
  refine bankRepairDigitWordAccSingle ring h' _ _ hko' (fun i _ => hco' i) ?_
  refine ⟨fun idx' z' a' hk' => ?_, fun _ _ h1 => ?_,
    fun _ _ _ _ _ h1 => ?_⟩
  · rw [hkj] at hk'
    injection hk' with h1 h2 h3
    subst h1 h2 h3
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold cwPhasePrefixPhysical
      rw [hsy]
      exact ⟨hyk, hycur, rfl, rfl, rfl⟩
    · rw [hroot, hyj]
      exact hjpos
    · rw [hroot, (hf 0 _).1, hyj, hs.1, hbit, hyz, hz]
    · rw [hroot, (hf 0 _).2.1, hyj, hs.2, hbit, hya, ha]
  · rw [hco'] at h1
    cases h1
  · rw [hco'] at h1
    cases h1

/-- P3 and A1 both create a target tag and a BACK cursor at j = offset
m >= t, with BACK index t; the cursor sits at offset m - t + t. -/
theorem bankRepairDigitWordAccRunTarget {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hko : ∀ i, i ≠ e → h.workerKind i = .empty)
    (hco : ∀ i, h.workerCursor i = .empty)
    (hyc : (workerW (p e) (p (ring.rightNeighbor e))).y.cur = .BACK)
    (hyj : (workerW (p e) (p (ring.rightNeighbor e))).y.j.val = c.t)
    {m : Nat} (hm1 : c.t ≤ m) (hm2 : m < n)
    (hjm : ring.rightNeighbor e = PPL.shiftRight ring h.root m)
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind =
      BlockA.wordPut (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e) (.target (ring.rightNeighbor e) true))
    (hwc : h'.workerCursor = BlockA.wordPut h.workerCursor
      (ring.rightNeighbor e)
      (.back (ring.rightNeighbor e)
        (workerW (p e) (p (ring.rightNeighbor e))).y.j)) :
    BankRepairDigitWordAccRun ring h' (phiW ring p e) := by
  obtain ⟨-, hsy⟩ := bankRepairDigitPhiWSites ring p e hne
  have hkj : h'.workerKind (ring.rightNeighbor e) =
      .target (ring.rightNeighbor e) true := by
    rw [hwk, bankRepairDigitPutSame]
  have hko' : ∀ i, i ≠ ring.rightNeighbor e → h'.workerKind i = .empty := by
    rw [hwk]
    exact bankRepairDigitPutMove _ _ e _ _ hko
  have hcj : h'.workerCursor (ring.rightNeighbor e) =
      .back (ring.rightNeighbor e)
        (workerW (p e) (p (ring.rightNeighbor e))).y.j := by
    rw [hwc, bankRepairDigitPutSame]
  have hco' : ∀ i, i ≠ ring.rightNeighbor e → h'.workerCursor i = .empty := by
    intro i hi
    rw [hwc, bankRepairDigitPutOther _ _ _ _ hi]
    exact hco i
  have hoff : PPL.cyclicOffset ring h.root (ring.rightNeighbor e) = m := by
    rw [hjm]
    exact bankRepairDigitOffsetShift ring h.root m hm2
  refine bankRepairDigitWordAccRunWorkerPhase ring h' _ hph
    (Or.inr (Or.inr (Or.inl ⟨_, hkj, hko', _, hco'⟩))) ?_
  refine bankRepairDigitWordAccSingle ring h' _ _ hko' hco' ?_
  refine ⟨fun idx z a hk => ?_, fun target idx hc => ?_,
    fun _ _ _ _ _ hc => ?_⟩
  · rw [hkj] at hk
    cases hk
  · rw [hcj] at hc
    injection hc with h1 h2
    subst h1 h2
    rw [hsy, hroot]
    refine ⟨hyc, rfl, ?_⟩
    rw [hyj, hoff, show m - c.t + c.t = m by omega]
    exact hjm
  · rw [hcj] at hc
    cases hc

theorem bankRepairDigitWordAccRunPthree {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) (ht : c.t + 1 < n)
    (htok : BankRepairDigitWordTok h)
    (hacc : BankRepairDigitWordAcc ring h p)
    {idx : Fin (c.t + 1)} {z a : Bool}
    (hk : h.workerKind e = .prefix idx z a) (hidx : idx.val = c.t)
    (hyc : (workerW (p e) (p (ring.rightNeighbor e))).y.cur = .BACK)
    (hyj : (workerW (p e) (p (ring.rightNeighbor e))).y.j.val = c.t)
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind =
      BlockA.wordPut (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e) (.target (ring.rightNeighbor e) true))
    (hwc : h'.workerCursor = BlockA.wordPut h.workerCursor
      (ring.rightNeighbor e)
      (.back (ring.rightNeighbor e)
        (workerW (p e) (p (ring.rightNeighbor e))).y.j)) :
    BankRepairDigitWordAccRun ring h' (phiW ring p e) := by
  obtain ⟨hko, hco⟩ := bankRepairDigitWordTokPrefix h htok e hk
  obtain ⟨-, hpos, -, -⟩ := (hacc e).1 idx z a hk
  rw [hidx] at hpos
  have hjm : ring.rightNeighbor e = PPL.shiftRight ring h.root (c.t + 1) := by
    rw [WordPhase.wordPhaseShiftSucc, ← hpos]
  exact bankRepairDigitWordAccRunTarget ring h h' p e hne hko hco hyc hyj
    (Nat.le_succ _) ht hjm hroot hph hwk hwc

/-- A1 never targets the root (the root is a post-E leader), so its
target sits at an offset in (t, n). -/
theorem bankRepairDigitWordAoneOffset {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e))
    (hne : ring.rightNeighbor e ≠ e)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .advance)
    (hke : h.workerKind e = .ready e) :
    ∃ m, c.t ≤ m ∧ m < n ∧
      ring.rightNeighbor e = PPL.shiftRight ring h.root m := by
  rcases hreach with ⟨_, h2⟩ | ⟨_, _, hkd⟩
  · rw [h2] at hke
    cases hke
  · obtain ⟨k, hk1, hk2, hk3⟩ := hkd e e (Or.inr hke)
    have hjk : ring.rightNeighbor e =
        PPL.shiftRight ring h.root (k + 1) := by
      rw [WordPhase.wordPhaseShiftSucc, ← hk3]
    have hkn : k + 1 < n := by
      by_cases hkn : k + 1 < n
      · exact hkn
      · exfalso
        have hroot' : ring.rightNeighbor e = h.root := by
          rw [hjk, show k + 1 = n by omega]
          exact bankRepairDigitShiftFull ring h.root
        have hrow := bankRepairDigitWorkerCaseAdvance _ _ hcase
        have hl := bankRepairDigitSiStepRowAone c _ _ _ _ hrow
        have hl' := hfix'.1
        rw [← hroot'] at hl'
        have hy : (phiW ring p e) (ring.rightNeighbor e) =
            (pairW (p e) (p (ring.rightNeighbor e))).2 := by
          simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
        rw [hy] at hl'
        change (postW (p e) (p (ring.rightNeighbor e))).eY.l = true at hl'
        rw [hl] at hl'
        cases hl'
    exact ⟨k + 1, by omega, hkn, hjk⟩

theorem bankRepairDigitWordAccRunAone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (htok : BankRepairDigitWordTok h)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e))
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .advance)
    (hke : h.workerKind e = .ready e)
    (hyc : (workerW (p e) (p (ring.rightNeighbor e))).y.cur = .BACK)
    (hyj : (workerW (p e) (p (ring.rightNeighbor e))).y.j.val = c.t)
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind =
      BlockA.wordPut (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e) (.target (ring.rightNeighbor e) true))
    (hwc : h'.workerCursor = BlockA.wordPut h.workerCursor
      (ring.rightNeighbor e)
      (.back (ring.rightNeighbor e)
        (workerW (p e) (p (ring.rightNeighbor e))).y.j)) :
    BankRepairDigitWordAccRun ring h' (phiW ring p e) := by
  obtain ⟨hko, hco⟩ := bankRepairDigitWordTokReady h htok e hke
  obtain ⟨m, hm1, hm2, hjm⟩ :=
    bankRepairDigitWordAoneOffset ring h p e hreach hfix' hne hcase hke
  exact bankRepairDigitWordAccRunTarget ring h h' p e hne hko hco hyc hyj
    hm1 hm2 hjm hroot hph hwk hwc

/-- S1 retires the single cursor and turns the target into ready: no
prefix colour and no cursor remain. -/
theorem bankRepairDigitWordAccRunSone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (htok : BankRepairDigitWordTok h)
    {target : Fin n} {idx : Fin (c.t + 1)} {z parity trailing : Bool}
    (hce : h.workerCursor e = .sum target idx z parity trailing)
    (hkj : h.workerKind (ring.rightNeighbor e) =
      .target (ring.rightNeighbor e) true)
    (hph : h'.phase = .worker)
    (hwk : h'.workerKind = BlockA.wordPut h.workerKind
      (ring.rightNeighbor e) (.ready (ring.rightNeighbor e)))
    (hwc : h'.workerCursor = BlockA.wordPut h.workerCursor e .empty) :
    BankRepairDigitWordAccRun ring h' (phiW ring p e) := by
  obtain ⟨T, _, hko, hco⟩ := bankRepairDigitWordTokCursor h htok e
    (by rw [hce]; intro h0; cases h0)
  have hko2 : ∀ i, i ≠ ring.rightNeighbor e → h.workerKind i = .empty :=
    bankRepairDigitUniqueSite _ _ (ring.rightNeighbor e) T
      (by rw [hkj]; intro h0; cases h0) hko
  have hkj' : h'.workerKind (ring.rightNeighbor e) =
      .ready (ring.rightNeighbor e) := by
    rw [hwk, bankRepairDigitPutSame]
  have hko' : ∀ i, i ≠ ring.rightNeighbor e → h'.workerKind i = .empty := by
    intro i hi
    rw [hwk, bankRepairDigitPutOther _ _ _ _ hi]
    exact hko2 i hi
  have hco' : ∀ i, h'.workerCursor i = .empty := by
    rw [hwc]
    exact bankRepairDigitPutClear _ _ e hco
  refine bankRepairDigitWordAccRunWorkerPhase ring h' _ hph
    (Or.inr (Or.inr (Or.inr ⟨_, hkj', hko', hco'⟩))) ?_
  apply bankRepairDigitWordAccNoColour ring h' _ _ hco'
  intro i idx' z' a' h0
  by_cases hi : i = ring.rightNeighbor e
  · rw [hi, hkj'] at h0
    cases h0
  · rw [hko' i hi] at h0
    cases h0

/-- A0 (terminal): the ready tag is the only colour, so the done phase
starts with no prefix colour and no cursor. -/
theorem bankRepairDigitWordAccRunTerminal {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p' : Fin n → ProjW c) (e : Fin n)
    (htok : BankRepairDigitWordTok h)
    (hke : h.workerKind e = .ready e)
    (hph : h'.phase = .done) (hwk : h'.workerKind = h.workerKind)
    (hwc : h'.workerCursor = h.workerCursor) :
    BankRepairDigitWordAccRun ring h' p' := by
  obtain ⟨hko, hco⟩ := bankRepairDigitWordTokReady h htok e hke
  have hk : ∀ i idx z a, h'.workerKind i ≠ .prefix idx z a := by
    intro i idx z a h0
    rw [hwk] at h0
    by_cases hi : i = e
    · rw [hi, hke] at h0
      cases h0
    · rw [hko i hi] at h0
      cases h0
  have hc : ∀ i, h'.workerCursor i = .empty := by
    rw [hwc]
    exact hco
  refine ⟨bankRepairDigitWordTokCongr h h' hwk hwc htok, ?_,
    fun _ => ⟨hk, hc⟩, bankRepairDigitWordAccNoColour ring h' p' hk hc⟩
  intro h0
  rcases h0 with h0 | h0
  · rw [hph] at h0
    cases h0
  · rw [hph] at h0
    cases h0

theorem bankRepairDigitWordAccRunBzero {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (htok : BankRepairDigitWordTok h)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "B0")
    {target : Fin n} {idx : Fin (c.t + 1)}
    (hcj : h.workerCursor (ring.rightNeighbor e) = .back target idx)
    (hcurx : (workerW (p e) (p (ring.rightNeighbor e))).x.cur = .BACK)
    (hjx : (workerW (p e) (p (ring.rightNeighbor e))).x.j.val + 1 =
      idx.val)
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind = h.workerKind)
    (hwc : h'.workerCursor =
      BlockA.wordPut (BlockA.wordPut h.workerCursor (ring.rightNeighbor e)
        .empty) e
        (.back target (workerW (p e) (p (ring.rightNeighbor e))).x.j)) :
    BankRepairDigitWordAccRun ring h' (phiW ring p e) :=
  bankRepairDigitWordAccRunWorkerPhase ring h' _ hph
    (bankRepairDigitWordTokCursorMove h h' htok _ _ _
      (by rw [hcj]; intro h0; cases h0) hwk hwc)
    (bankRepairDigitWordAccBzeroLeaf ring h h' p e hne hacc hrow hcj hcurx
      hjx hroot hwk hwc)

theorem bankRepairDigitWordAccRunBone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (htok : BankRepairDigitWordTok h)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "B1")
    {target : Fin n} {idx : Fin (c.t + 1)}
    (hcj : h.workerCursor (ring.rightNeighbor e) = .back target idx)
    (hidx : idx.val = 1)
    (hjx : (workerW (p e) (p (ring.rightNeighbor e))).x.j.val = 0)
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind = h.workerKind)
    (hwc : h'.workerCursor =
      BlockA.wordPut (BlockA.wordPut h.workerCursor (ring.rightNeighbor e)
        .empty) e
        (.sum target (workerW (p e) (p (ring.rightNeighbor e))).x.j
          false false true)) :
    BankRepairDigitWordAccRun ring h' (phiW ring p e) :=
  bankRepairDigitWordAccRunWorkerPhase ring h' _ hph
    (bankRepairDigitWordTokCursorMove h h' htok _ _ _
      (by rw [hcj]; intro h0; cases h0) hwk hwc)
    (bankRepairDigitWordAccBoneLeaf ring h h' p e hne hacc hrow hcj hidx
      hjx hroot hwk hwc)

theorem bankRepairDigitWordAccRunSzero {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (htok : BankRepairDigitWordTok h)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "S0")
    {target : Fin n} {idx : Fin (c.t + 1)} {z parity trailing : Bool}
    (hce : h.workerCursor e = .sum target idx z parity trailing)
    (hyc : (workerW (p e) (p (ring.rightNeighbor e))).y.cur = .SUM)
    (hyj : (workerW (p e) (p (ring.rightNeighbor e))).y.j.val = idx.val + 1)
    (hyz : (workerW (p e) (p (ring.rightNeighbor e))).y.z =
      (BlockA.wordFold idx z parity trailing (p e).u).1)
    (hyp : (workerW (p e) (p (ring.rightNeighbor e))).y.p =
      (BlockA.wordFold idx z parity trailing (p e).u).2.1)
    (hya : (workerW (p e) (p (ring.rightNeighbor e))).y.a =
      (BlockA.wordFold idx z parity trailing (p e).u).2.2)
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind = h.workerKind)
    (hwc : h'.workerCursor =
      BlockA.wordPut (BlockA.wordPut h.workerCursor e .empty)
        (ring.rightNeighbor e)
        (.sum target (workerW (p e) (p (ring.rightNeighbor e))).y.j
          (workerW (p e) (p (ring.rightNeighbor e))).y.z
          (workerW (p e) (p (ring.rightNeighbor e))).y.p
          (workerW (p e) (p (ring.rightNeighbor e))).y.a)) :
    BankRepairDigitWordAccRun ring h' (phiW ring p e) :=
  bankRepairDigitWordAccRunWorkerPhase ring h' _ hph
    (bankRepairDigitWordTokCursorMove h h' htok _ _ _
      (by rw [hce]; intro h0; cases h0) hwk hwc)
    (bankRepairDigitWordAccSzeroLeaf ring h h' p e hne hacc hrow hce hyc hyj
      hyz hyp hya hroot hwk hwc)

/-- Every worker-phase step preserves the run bundle. -/
theorem bankRepairDigitWordAccRunWorker {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (hn : 3 ≤ n) (ht : c.t + 1 < n)
    (hrun : BankRepairDigitWordAccRun ring h p) (hph : h.phase = .worker)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e)) :
    BankRepairDigitWordAccRun ring (BlockA.wordWorkerNext ring h p e request)
      (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  have htok := hrun.1
  have hacc := hrun.2.2.2
  unfold BlockA.wordWorkerNext
  dsimp only
  cases hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) with
  | init =>
      exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
  | erase =>
      dsimp only
      split
      · exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl)
          (fun _ => rfl)
      · rename_i hkeep
        obtain ⟨hu, hsite⟩ :=
          bankRepairDigitWordEraseSites ring h p e hne hcase hkeep
        exact bankRepairDigitWordAccRunKeep ring h _ p _ hrun hph hu rfl rfl rfl
          hsite
  | prefixExit =>
      exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
  | prefixMove =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseMore _ _).1 hcase
      split
      · rename_i idx z a hk
        split
        · rename_i hC
          obtain ⟨-, -, -, -, -, -, -, -, -, hyk, hyj, hyz, hya, -⟩ := hC
          split
          · exact bankRepairDigitWordAccRunPone ring h _ p e hne htok hacc hrow
              hk hyk hyj hyz hya rfl hph rfl rfl
          · exact bankRepairDigitWordAccRunPone ring h _ p e hne htok hacc hrow
              hk hyk hyj hyz hya rfl hph rfl rfl
        · exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl)
            (fun _ => rfl)
      all_goals exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
  | prefixTerminal =>
      exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
  | prefixPublish =>
      dsimp only
      split
      · rename_i idx z a hk
        repeat' split
        all_goals first
          | exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
          | skip
        all_goals rename_i hC
        all_goals obtain ⟨hidx, -, -, -, -, -, -, -, -, -, -, -, -, -, hyc, hyj⟩ := hC
        all_goals exact bankRepairDigitWordAccRunPthree ring h _ p e hne ht htok hacc hk hidx hyc hyj rfl hph rfl rfl
      all_goals exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
  | backwardsMove =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseRows _ _).1 hcase
      split
      · rename_i target idx hcj
        split
        · rename_i hC
          exact bankRepairDigitWordAccRunBzero ring h _ p e hne htok hacc hrow
            hcj hC.2.2.2.2.1 hC.2.2.2.2.2 rfl hph rfl rfl
        · exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl)
            (fun _ => rfl)
      all_goals exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
  | backwardsInit =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseRows _ _).2.1 hcase
      split
      · rename_i target idx hcj
        split
        · rename_i hC
          exact bankRepairDigitWordAccRunBone ring h _ p e hne htok hacc hrow
            hcj hC.2.2.1 hC.2.2.2.2.2.2 rfl hph rfl rfl
        · exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl)
            (fun _ => rfl)
      all_goals exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
  | sumMove =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseRows _ _).2.2 hcase
      split
      · rename_i target idx z parity trailing hce
        split
        · rename_i hC
          obtain ⟨-, -, -, -, -, -, -, -, -, hyc, hyj, hyz, hyp, hya⟩ := hC
          exact bankRepairDigitWordAccRunSzero ring h _ p e hne htok hacc hrow
            hce hyc hyj hyz hyp hya rfl hph rfl rfl
        · exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl)
            (fun _ => rfl)
      all_goals exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
  | sumPublish =>
      dsimp only
      split
      · rename_i target idx z parity trailing hce
        repeat' split
        all_goals first
          | exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
          | skip
        all_goals rename_i hC
        all_goals exact bankRepairDigitWordAccRunSone ring h _ p e htok hce hC.2.1 hph rfl rfl
      all_goals exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
  | advance =>
      dsimp only
      split
      · rename_i hC
        obtain ⟨hke, -, -, -, -, -, -, -, hyc, hyj⟩ := hC
        exact bankRepairDigitWordAccRunAone ring h _ p e hne htok hreach hfix'
          hcase hke hyc hyj rfl hph rfl rfl
      · exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl)
          (fun _ => rfl)
  | terminal =>
      dsimp only
      split
      · rename_i hC
        exact bankRepairDigitWordAccRunTerminal ring h _ _ e htok hC.1 rfl rfl rfl
      · exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl)
          (fun _ => rfl)
  | frame =>
      obtain ⟨hu, hsi⟩ := bankRepairDigitWordFrameSites ring p e hne hcase
      exact bankRepairDigitWordAccRunKeep ring h _ p _ hrun hph hu rfl rfl rfl
        (fun i => Or.inl (hsi i))

/-- The validate phase carries no colour; it keeps it, cancels, or
launches the single root prefix. -/
theorem bankRepairDigitWordAccRunValidate {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (hrun : BankRepairDigitWordAccRun ring h p) (hph : h.phase = .validate) :
    BankRepairDigitWordAccRun ring
      (BlockA.wordValidateNext ring h p e request) (phiW ring p e) := by
  obtain ⟨hk, hc⟩ := hrun.2.1 (Or.inr hph)
  unfold BlockA.wordValidateNext
  dsimp only
  split
  all_goals (repeat' split)
  all_goals first
    | exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
    | exact bankRepairDigitWordAccRunIdle ring _ _ hk hc
    | skip
  rename_i hg
  obtain ⟨he, -, -, -, -, -, -, -, hx, -⟩ := hg
  exact bankRepairDigitWordAccRunLaunch ring h p e he hx

/-- One complete W monitor step preserves the run bundle. -/
theorem bankRepairDigitWordAccRunStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (hn : 3 ≤ n) (ht : c.t + 1 < n)
    (hrun : BankRepairDigitWordAccRun ring h p)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e)) :
    BankRepairDigitWordAccRun ring
      (BlockA.wordT ring h p e (phiW ring p e)) (phiW ring p e) := by
  unfold BlockA.wordT
  split
  · rename_i hd
    exact bankRepairDigitWordAccRunDone ring h p _ hrun hd
  · dsimp only
    split
    · exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl) (fun _ => rfl)
    · split
      · exact bankRepairDigitWordAccRunIdle ring _ _ (fun _ => rfl)
          (fun _ => rfl)
      · rename_i hph
        exact bankRepairDigitWordAccRunValidate ring h p e _ hrun hph
      · rename_i hph
        exact bankRepairDigitWordAccRunWorker ring h p e _ hn ht hrun hph hreach
          hfix'
      · rename_i hph
        exact bankRepairDigitWordAccRunDone ring h p _ hrun hph

theorem bankRepairDigitWordAccRunAux {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (origin : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (root : Fin n) (h₀ : BlockA.WordControl n c)
    (hγ₀ : γ₀ = .live origin h₀) (hroot₀ : h₀.root = root)
    (hfix₀ : WFixedRoot ring root origin)
    (hcl : ∀ i, h₀.publications i = .absent ∧ h₀.workerKind i = .empty)
    (hcur : ∀ i, h₀.workerCursor i = .empty)
    (hn : 3 ≤ n) (ht : c.t + 1 < n)
    {w : List (Fin n)} {p : Fin n → ProjW c}
    {γ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c)}
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p γ) :
    ∀ shadow h, γ = .live shadow h → BankRepairDigitWordAccRun ring h p := by
  induction hrun with
  | empty =>
      intro shadow h hγ
      rw [hγ₀] at hγ
      injection hγ with h1 h2
      subst h1 h2
      exact bankRepairDigitWordAccRunIdle ring _ _ (fun i => (hcl i).2) hcur
  | @next w p γ hr e ih =>
      intro shadow h hγ
      cases γ with
      | failed =>
          rw [BlockA.update_failed] at hγ
          cases hγ
      | live s h₁ =>
          have hacc₁ := ih s h₁ rfl
          obtain ⟨hs, hfix₁, hreach₁⟩ := bankRepairDigitWordReachRunAux ring
            origin γ₀ root h₀ hγ₀ hroot₀ hfix₀ hcl hn ht hr s h₁ rfl
          rw [hs, AcceptedReceipts.WordEntrance.word_update_live] at hγ
          injection hγ with h1 h2
          subst h1 h2
          exact bankRepairDigitWordAccRunStep ring h₁ p e hn ht hacc₁ hreach₁
            (bankRepairDigitWFixedRootPhiW hn ring h₁.root p e hfix₁)

/-- T12 item 1: along every projected W run from `initializesWord` the
run bundle holds: at most one worker token, no colour outside the worker
and done phases, no prefix colour and no cursor once A0 has fired, and
the accumulator invariant (prefix z/a are the prefix OR/AND at the
tag's own offset; BACK/SUM cursors sit at `target - t + idx`; SUM
z/parity/trailing are the window folds over the sources read). -/
theorem bankRepairDigitWordRunAcc {n : Nat} (ring : DirectedRing n)
    (c : Compiled) :
    ∀ (origin p : Fin n → ProjW c)
      (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
      (w : List (Fin n)) (shadow : Fin n → ProjW c)
      (h : BlockA.WordControl n c),
      BlockA.initializesWord ring origin γ₀ →
      BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
        (.live shadow h) →
      BankRepairDigitWordAccRun ring h p := by
  intro origin p γ₀ w shadow h hinit hrun
  obtain ⟨root, h₀, hγ₀, hroot, hfix, ht2, htn, -, -, hcl, -, -⟩ := hinit
  have hpow := bankRepairDigitPowLower c.t
  exact bankRepairDigitWordAccRunAux ring origin γ₀ root h₀ hγ₀ hroot hfix
    (fun i => ⟨(hcl i).2.2.2.2.1, (hcl i).2.2.1⟩) (fun i => (hcl i).2.2.2.1)
    (by omega) (by omega) hrun shadow h rfl

/-- The done-phase clause on its own: once A0 has fired, no prefix
colour and no cursor remain. -/
theorem bankRepairDigitWordRunDoneClean {n : Nat} (ring : DirectedRing n)
    (c : Compiled) (origin p : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (w : List (Fin n)) (shadow : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hinit : BlockA.initializesWord ring origin γ₀)
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
      (.live shadow h))
    (hdone : h.phase = .done) :
    (∀ i idx z a, h.workerKind i ≠ .prefix idx z a) ∧
      (∀ i, h.workerCursor i = .empty) :=
  (bankRepairDigitWordRunAcc ring c origin p γ₀ w shadow h hinit hrun).2.2.1
    hdone

end L3.RenewalReferenceClock

/-!
T12 item 2: published windows are frozen. Only P1/P2/P3/S1 change a
visible (u, beta) pair; P1 runs under a prefix colour (no window receipt
exists yet), P2 cancels, P3 rewrites only its own site e (offset t,
published in the same step), and S1 rewrites only its target j, whose
window receipts all lie strictly below it. The ordering invariant
`BankRepairDigitWordBelow` is carried along W runs (with the item 1
bundle and `BankRepairDigitWordReach`). See comms/T12-notes.md.
-/

namespace L3.RenewalReferenceClock

open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option linter.unusedSimpArgs false

/-- A window receipt: P3's `.prefixEnd` or S1's `.recurrence`. -/
def BankRepairDigitWordWin (r : BlockA.PublicationReceipt) : Prop :=
  r = .prefixEnd ∨ r = .recurrence

theorem bankRepairDigitWordWinAbsent :
    ¬ BankRepairDigitWordWin .absent := by
  intro h0
  rcases h0 with h0 | h0
  · cases h0
  · cases h0

theorem bankRepairDigitWordWinZero :
    ¬ BankRepairDigitWordWin .prefixZero := by
  intro h0
  rcases h0 with h0 | h0
  · cases h0
  · cases h0

/-- T12 item 2: the ordering invariant. A window receipt exists only in
the worker and done phases, never together with a prefix colour, strictly
below every target colour and at or below every ready colour. -/
def BankRepairDigitWordBelow {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c) : Prop :=
  ∀ i, BankRepairDigitWordWin (h.publications i) →
    h.phase ≠ .awaitRequest ∧ h.phase ≠ .validate ∧
    (∀ s idx z a, h.workerKind s ≠ .prefix idx z a) ∧
    (∀ T s b, h.workerKind T = .target s b →
      PPL.cyclicOffset ring h.root i < PPL.cyclicOffset ring h.root T) ∧
    (∀ T s, h.workerKind T = .ready s →
      PPL.cyclicOffset ring h.root i ≤ PPL.cyclicOffset ring h.root T)

/-- T12 item 2, one step: a site whose visible (u, beta) pair changes
lies strictly above every window receipt of the new control, except a
receipt freshly issued at that very site. -/
def BankRepairDigitWordFreeze {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c) : Prop :=
  ∀ s, AcceptedReceipts.wordVisible p' s ≠ AcceptedReceipts.wordVisible p s →
    ∀ i, BankRepairDigitWordWin (h'.publications i) →
      (i = s ∧ ¬ BankRepairDigitWordWin (h.publications s)) ∨
      PPL.cyclicOffset ring h.root i < PPL.cyclicOffset ring h.root s

def BankRepairDigitWordBelowStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c) : Prop :=
  BankRepairDigitWordBelow ring h' ∧ BankRepairDigitWordFreeze ring h h' p p'

theorem bankRepairDigitPutOr {n : Nat} {A : Type} (f : Fin n → A)
    (r : Fin n) (v : A) (i : Fin n) :
    BlockA.wordPut f r v i = f i ∨ BlockA.wordPut f r v i = v := by
  by_cases hi : i = r
  · rw [hi, bankRepairDigitPutSame]
    exact Or.inr rfl
  · rw [bankRepairDigitPutOther _ _ _ _ hi]
    exact Or.inl rfl

theorem bankRepairDigitKindAt {n : Nat} {A : Type} (f : Fin n → A)
    (a0 v : A) (r : Fin n) (hf : ∀ T, T ≠ r → f T = a0) (hr : f r = v)
    (T : Fin n) (w : A) (hT : f T = w) (hw : w ≠ a0) : T = r ∧ w = v := by
  by_cases h0 : T = r
  · refine ⟨h0, ?_⟩
    rw [← hT, h0, hr]
  · exfalso
    apply hw
    rw [← hT, hf T h0]

theorem bankRepairDigitWorkerCasePublish {c : Compiled} (x y : ProjW c) :
    (BlockA.workerCase x y = .prefixPublish → (workerW x y).row = "P3") ∧
    (BlockA.workerCase x y = .sumPublish → (workerW x y).row = "S1") ∧
    (BlockA.workerCase x y = .terminal → (workerW x y).row = "A0") := by
  have key : bankRepairDigitHolds
      (fun w : BlockA.WorkerReceiptCase =>
        (w = .prefixPublish → (workerW x y).row = "P3") ∧
        (w = .sumPublish → (workerW x y).row = "S1") ∧
        (w = .terminal → (workerW x y).row = "A0"))
      (BlockA.workerCase x y) := by
    unfold BlockA.workerCase
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals simp_all
  exact key

/-- P3 leaves the responder's visible pair alone. -/
theorem bankRepairDigitSiStepRowPthreeY (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row = "P3") :
    (siStep c ox oy post hard).uY = oy.u ∧
      (siStep c ox oy post hard).betaY = oy.beta := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "P3" →
      r.uY = oy.u ∧ r.betaY = oy.beta)
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals simp at hr ⊢
  exact key hr

/-- S1 leaves the initiator's visible pair alone. -/
theorem bankRepairDigitSiStepRowSoneX (c : Compiled) (ox oy : Agent c)
    (post : PostE) (hard : HardFlags)
    (hr : (siStep c ox oy post hard).row = "S1") :
    (siStep c ox oy post hard).uX = ox.u ∧
      (siStep c ox oy post hard).betaX = ox.beta := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "S1" →
      r.uX = ox.u ∧ r.betaX = ox.beta)
      (siStep c ox oy post hard) := by
    unfold siStep
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals simp at hr ⊢
  exact key hr

/-- A visible change sits at an endpoint of the served edge, and that
endpoint's row output differs from its OLD visible pair. -/
theorem bankRepairDigitVisibleChangeSites {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e s : Fin n)
    (hs : AcceptedReceipts.wordVisible (phiW ring p e) s ≠
      AcceptedReceipts.wordVisible p s) :
    (s = e ∧ ¬((workerW (p e) (p (ring.rightNeighbor e))).uX = (p e).u ∧
        (workerW (p e) (p (ring.rightNeighbor e))).betaX = (p e).beta)) ∨
    (s = ring.rightNeighbor e ∧
      ¬((workerW (p e) (p (ring.rightNeighbor e))).uY =
          (p (ring.rightNeighbor e)).u ∧
        (workerW (p e) (p (ring.rightNeighbor e))).betaY =
          (p (ring.rightNeighbor e)).beta)) := by
  by_cases hse : s = e
  · refine Or.inl ⟨hse, fun hxy => hs ?_⟩
    unfold AcceptedReceipts.wordVisible phiW projectedEdge
    rw [if_pos hse, hse]
    exact Prod.ext hxy.1 hxy.2
  · by_cases hsj : s = ring.rightNeighbor e
    · refine Or.inr ⟨hsj, fun hxy => hs ?_⟩
      unfold AcceptedReceipts.wordVisible phiW projectedEdge
      rw [if_neg hse, if_pos hsj, hsj]
      exact Prod.ext hxy.1 hxy.2
    · exfalso
      apply hs
      unfold AcceptedReceipts.wordVisible
      rw [cwPhiWFrame ring p e s hse hsj]

theorem bankRepairDigitWordBelowStepNoWin {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c)
    (hw : ∀ i, ¬ BankRepairDigitWordWin (h'.publications i)) :
    BankRepairDigitWordBelowStep ring h h' p p' :=
  ⟨fun i hi => absurd hi (hw i), fun _ _ i hi => absurd hi (hw i)⟩

theorem bankRepairDigitWordBelowStepCleared {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c)
    (hc : ∀ i, h'.publications i = .absent) :
    BankRepairDigitWordBelowStep ring h h' p p' :=
  bankRepairDigitWordBelowStepNoWin ring h h' p p' (fun i => by
    rw [hc i]
    exact bankRepairDigitWordWinAbsent)

theorem bankRepairDigitWordBelowPrefix {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (hb : BankRepairDigitWordBelow ring h) (e : Fin n)
    {idx : Fin (c.t + 1)} {z a : Bool}
    (hk : h.workerKind e = .prefix idx z a) :
    ∀ i, ¬ BankRepairDigitWordWin (h.publications i) :=
  fun i hi => (hb i hi).2.2.1 e idx z a hk

theorem bankRepairDigitWordBelowIdle {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (hb : BankRepairDigitWordBelow ring h)
    (hph : h.phase = .awaitRequest ∨ h.phase = .validate) :
    ∀ i, ¬ BankRepairDigitWordWin (h.publications i) := by
  intro i hi
  obtain ⟨h1, h2, -⟩ := hb i hi
  rcases hph with hp | hp
  · exact h1 hp
  · exact h2 hp

theorem bankRepairDigitWordBelowKeep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (hb : BankRepairDigitWordBelow ring h) (hroot : h'.root = h.root)
    (hpub : h'.publications = h.publications)
    (hk : h'.workerKind = h.workerKind)
    (hph : h'.phase = h.phase ∨ h'.phase = .done) :
    BankRepairDigitWordBelow ring h' := by
  intro i hi
  rw [hpub] at hi
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb i hi
  rw [hk, hroot]
  refine ⟨?_, ?_, h3, h4, h5⟩
  · rcases hph with hp | hp
    · rw [hp]
      exact h1
    · rw [hp]
      intro h0
      cases h0
  · rcases hph with hp | hp
    · rw [hp]
      exact h2
    · rw [hp]
      intro h0
      cases h0

theorem bankRepairDigitWordFreezeQuiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (h1 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P1")
    (h2 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P2")
    (h3 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P3")
    (h4 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "S1") :
    BankRepairDigitWordFreeze ring h h' p (phiW ring p e) :=
  fun s hs => absurd (bankRepairDigitQuietRowVisible ring p e h1 h2 h3 h4 s) hs

/-- Quiet rows that keep the receipts and colours (I1 keep, frame, B0,
B1, S0, A0). -/
theorem bankRepairDigitWordBelowStepQuiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hb : BankRepairDigitWordBelow ring h)
    (h1 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P1")
    (h2 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P2")
    (h3 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P3")
    (h4 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "S1")
    (hroot : h'.root = h.root) (hpub : h'.publications = h.publications)
    (hk : h'.workerKind = h.workerKind)
    (hph : h'.phase = h.phase ∨ h'.phase = .done) :
    BankRepairDigitWordBelowStep ring h h' p (phiW ring p e) :=
  ⟨bankRepairDigitWordBelowKeep ring h h' hb hroot hpub hk hph,
    bankRepairDigitWordFreezeQuiet ring h h' p e h1 h2 h3 h4⟩

/-- P1 runs under a prefix colour, so no window receipt exists before or
after it (it adds at most a `.prefixZero`). -/
theorem bankRepairDigitWordBelowStepPone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c) (hb : BankRepairDigitWordBelow ring h)
    (e : Fin n) {idx : Fin (c.t + 1)} {z a : Bool}
    (hk : h.workerKind e = .prefix idx z a)
    (hpub : ∀ i, h'.publications i = h.publications i ∨
      h'.publications i = .prefixZero) :
    BankRepairDigitWordBelowStep ring h h' p p' := by
  apply bankRepairDigitWordBelowStepNoWin
  intro i hi
  rcases hpub i with h0 | h0
  · rw [h0] at hi
    exact bankRepairDigitWordBelowPrefix ring h hb e hk i hi
  · rw [h0] at hi
    exact bankRepairDigitWordWinZero hi

/-- P3: the only window receipt is the fresh one at e (offset t); the new
target sits at offset t+1; only e's visible pair can change. -/
theorem bankRepairDigitWordBelowStepPthree {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (ht : c.t + 1 < n)
    (htok : BankRepairDigitWordTok h)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hb : BankRepairDigitWordBelow ring h)
    {idx : Fin (c.t + 1)} {z a : Bool}
    (hk : h.workerKind e = .prefix idx z a) (hidx : idx.val = c.t)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "P3")
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind =
      BlockA.wordPut (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e) (.target (ring.rightNeighbor e) true))
    (hwp : h'.publications = BlockA.wordPut h.publications e .prefixEnd) :
    BankRepairDigitWordBelowStep ring h h' p (phiW ring p e) := by
  obtain ⟨hko, -⟩ := bankRepairDigitWordTokPrefix h htok e hk
  have hnw := bankRepairDigitWordBelowPrefix ring h hb e hk
  obtain ⟨-, hpos, -, -⟩ := (hacc e).1 idx z a hk
  rw [hidx] at hpos
  have hjm : ring.rightNeighbor e = PPL.shiftRight ring h.root (c.t + 1) := by
    rw [WordPhase.wordPhaseShiftSucc, ← hpos]
  have hoe : PPL.cyclicOffset ring h.root e = c.t := by
    rw [hpos]
    exact bankRepairDigitOffsetShift ring h.root c.t (by omega)
  have hoj : PPL.cyclicOffset ring h.root (ring.rightNeighbor e) = c.t + 1 := by
    rw [hjm]
    exact bankRepairDigitOffsetShift ring h.root (c.t + 1) ht
  have hwin : ∀ i, BankRepairDigitWordWin (h'.publications i) → i = e := by
    intro i hi
    rw [hwp] at hi
    by_cases hie : i = e
    · exact hie
    · rw [bankRepairDigitPutOther _ _ _ _ hie] at hi
      exact absurd hi (hnw i)
  have hkind : ∀ T, T ≠ ring.rightNeighbor e → h'.workerKind T = .empty := by
    rw [hwk]
    exact bankRepairDigitPutMove _ _ e _ _ hko
  have hkj : h'.workerKind (ring.rightNeighbor e) =
      .target (ring.rightNeighbor e) true := by
    rw [hwk, bankRepairDigitPutSame]
  refine ⟨fun i hi => ?_, fun s hs i hi => ?_⟩
  · have hie := hwin i hi
    rw [hroot, hph, hie, hoe]
    refine ⟨(by intro h0; cases h0), (by intro h0; cases h0),
      fun T idx' z' a' h0 => ?_, fun T s' b h0 => ?_, fun T s' h0 => ?_⟩
    · obtain ⟨-, hw⟩ := bankRepairDigitKindAt _ _ _ _ hkind hkj T _ h0
        (by intro h1; cases h1)
      cases hw
    · obtain ⟨hT, -⟩ := bankRepairDigitKindAt _ _ _ _ hkind hkj T _ h0
        (by intro h1; cases h1)
      rw [hT, hoj]
      exact Nat.lt_succ_self _
    · obtain ⟨-, hw⟩ := bankRepairDigitKindAt _ _ _ _ hkind hkj T _ h0
        (by intro h1; cases h1)
      cases hw
  · rcases bankRepairDigitVisibleChangeSites ring p e s hs with ⟨hse, -⟩ |
        ⟨-, hy⟩
    · left
      refine ⟨(hwin i hi).trans hse.symm, ?_⟩
      rw [hse]
      exact hnw e
    · exact absurd (bankRepairDigitSiStepRowPthreeY c _ _ _ _ hrow) hy

/-- S1: the fresh `.recurrence` at the target j sits at or above every
older window receipt (strictly above by the target clause); only j's
visible pair can change. -/
theorem bankRepairDigitWordBelowStepSone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (htok : BankRepairDigitWordTok h)
    (hb : BankRepairDigitWordBelow ring h)
    {target : Fin n} {idx : Fin (c.t + 1)} {z parity trailing : Bool}
    (hce : h.workerCursor e = .sum target idx z parity trailing)
    (hkj : h.workerKind (ring.rightNeighbor e) =
      .target (ring.rightNeighbor e) true)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "S1")
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind = BlockA.wordPut h.workerKind
      (ring.rightNeighbor e) (.ready (ring.rightNeighbor e)))
    (hwp : h'.publications = BlockA.wordPut h.publications
      (ring.rightNeighbor e) .recurrence) :
    BankRepairDigitWordBelowStep ring h h' p (phiW ring p e) := by
  obtain ⟨T, _, hko, -⟩ := bankRepairDigitWordTokCursor h htok e
    (by rw [hce]; intro h0; cases h0)
  have hko2 : ∀ i, i ≠ ring.rightNeighbor e → h.workerKind i = .empty :=
    bankRepairDigitUniqueSite _ _ (ring.rightNeighbor e) T
      (by rw [hkj]; intro h0; cases h0) hko
  have hkind : ∀ i, i ≠ ring.rightNeighbor e → h'.workerKind i = .empty := by
    intro i hi
    rw [hwk, bankRepairDigitPutOther _ _ _ _ hi]
    exact hko2 i hi
  have hkj' : h'.workerKind (ring.rightNeighbor e) =
      .ready (ring.rightNeighbor e) := by
    rw [hwk, bankRepairDigitPutSame]
  have hwin : ∀ i, BankRepairDigitWordWin (h'.publications i) →
      i = ring.rightNeighbor e ∨
        PPL.cyclicOffset ring h.root i <
          PPL.cyclicOffset ring h.root (ring.rightNeighbor e) := by
    intro i hi
    rw [hwp] at hi
    by_cases hij : i = ring.rightNeighbor e
    · exact Or.inl hij
    · rw [bankRepairDigitPutOther _ _ _ _ hij] at hi
      exact Or.inr ((hb i hi).2.2.2.1 _ _ true hkj)
  refine ⟨fun i hi => ?_, fun s hs i hi => ?_⟩
  · have hle : PPL.cyclicOffset ring h.root i ≤
        PPL.cyclicOffset ring h.root (ring.rightNeighbor e) := by
      rcases hwin i hi with h0 | h0
      · rw [h0]
        exact Nat.le_refl _
      · exact Nat.le_of_lt h0
    rw [hroot, hph]
    refine ⟨(by intro h0; cases h0), (by intro h0; cases h0),
      fun T idx' z' a' h0 => ?_, fun T s' b h0 => ?_, fun T s' h0 => ?_⟩
    · obtain ⟨-, hw⟩ := bankRepairDigitKindAt _ _ _ _ hkind hkj' T _ h0
        (by intro h1; cases h1)
      cases hw
    · obtain ⟨-, hw⟩ := bankRepairDigitKindAt _ _ _ _ hkind hkj' T _ h0
        (by intro h1; cases h1)
      cases hw
    · obtain ⟨hT, -⟩ := bankRepairDigitKindAt _ _ _ _ hkind hkj' T _ h0
        (by intro h1; cases h1)
      rw [hT]
      exact hle
  · rcases bankRepairDigitVisibleChangeSites ring p e s hs with ⟨-, hx⟩ |
        ⟨hsj, -⟩
    · exact absurd (bankRepairDigitSiStepRowSoneX c _ _ _ _ hrow) hx
    · rw [hsj]
      rcases hwin i hi with h0 | h0
      · left
        refine ⟨h0, fun hw => ?_⟩
        exact Nat.lt_irrefl _ ((hb _ hw).2.2.2.1 _ _ true hkj)
      · exact Or.inr h0

/-- A1 from a ready site at offset k: e = shift k, j = shift (k+1),
k+1 < n. -/
theorem bankRepairDigitWordAoneOffsets {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e))
    (hne : ring.rightNeighbor e ≠ e)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .advance)
    (hke : h.workerKind e = .ready e) :
    ∃ k, k + 1 < n ∧ e = PPL.shiftRight ring h.root k ∧
      ring.rightNeighbor e = PPL.shiftRight ring h.root (k + 1) := by
  rcases hreach with ⟨_, h2⟩ | ⟨_, _, hkd⟩
  · rw [h2] at hke
    cases hke
  · obtain ⟨k, -, hk2, hk3⟩ := hkd e e (Or.inr hke)
    have hjk : ring.rightNeighbor e =
        PPL.shiftRight ring h.root (k + 1) := by
      rw [WordPhase.wordPhaseShiftSucc, ← hk3]
    have hkn : k + 1 < n := by
      by_cases hkn : k + 1 < n
      · exact hkn
      · exfalso
        have hroot' : ring.rightNeighbor e = h.root := by
          rw [hjk, show k + 1 = n by omega]
          exact bankRepairDigitShiftFull ring h.root
        have hrow := bankRepairDigitWorkerCaseAdvance _ _ hcase
        have hl := bankRepairDigitSiStepRowAone c _ _ _ _ hrow
        have hl' := hfix'.1
        rw [← hroot'] at hl'
        have hy : (phiW ring p e) (ring.rightNeighbor e) =
            (pairW (p e) (p (ring.rightNeighbor e))).2 := by
          simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
        rw [hy] at hl'
        change (postW (p e) (p (ring.rightNeighbor e))).eY.l = true at hl'
        rw [hl] at hl'
        cases hl'
    exact ⟨k, hkn, hk3, hjk⟩

/-- A1: the new target at offset k+1 lies above every window receipt,
all of which are at or below the ready site at offset k. -/
theorem bankRepairDigitWordBelowStepAone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (htok : BankRepairDigitWordTok h)
    (hb : BankRepairDigitWordBelow ring h)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e))
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .advance)
    (hke : h.workerKind e = .ready e)
    (hroot : h'.root = h.root) (hph : h'.phase = .worker)
    (hwk : h'.workerKind =
      BlockA.wordPut (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e) (.target (ring.rightNeighbor e) true))
    (hwp : h'.publications = h.publications) :
    BankRepairDigitWordBelowStep ring h h' p (phiW ring p e) := by
  obtain ⟨hko, -⟩ := bankRepairDigitWordTokReady h htok e hke
  obtain ⟨k, hkn, hek, hjk⟩ :=
    bankRepairDigitWordAoneOffsets ring h p e hreach hfix' hne hcase hke
  have hoe : PPL.cyclicOffset ring h.root e = k := by
    rw [hek]
    exact bankRepairDigitOffsetShift ring h.root k (by omega)
  have hoj : PPL.cyclicOffset ring h.root (ring.rightNeighbor e) = k + 1 := by
    rw [hjk]
    exact bankRepairDigitOffsetShift ring h.root (k + 1) hkn
  have hkind : ∀ T, T ≠ ring.rightNeighbor e → h'.workerKind T = .empty := by
    rw [hwk]
    exact bankRepairDigitPutMove _ _ e _ _ hko
  have hkj : h'.workerKind (ring.rightNeighbor e) =
      .target (ring.rightNeighbor e) true := by
    rw [hwk, bankRepairDigitPutSame]
  have hrow := bankRepairDigitWorkerCaseAdvance _ _ hcase
  refine ⟨fun i hi => ?_, bankRepairDigitWordFreezeQuiet ring h h' p e
    (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide)
    (by rw [hrow]; decide)⟩
  rw [hwp] at hi
  have hie := (hb i hi).2.2.2.2 e e hke
  rw [hoe] at hie
  rw [hroot, hph]
  refine ⟨(by intro h0; cases h0), (by intro h0; cases h0),
    fun T idx' z' a' h0 => ?_, fun T s' b h0 => ?_, fun T s' h0 => ?_⟩
  · obtain ⟨-, hw⟩ := bankRepairDigitKindAt _ _ _ _ hkind hkj T _ h0
      (by intro h1; cases h1)
    cases hw
  · obtain ⟨hT, -⟩ := bankRepairDigitKindAt _ _ _ _ hkind hkj T _ h0
      (by intro h1; cases h1)
    rw [hT, hoj]
    omega
  · obtain ⟨-, hw⟩ := bankRepairDigitKindAt _ _ _ _ hkind hkj T _ h0
      (by intro h1; cases h1)
    cases hw

/-- Every worker-phase step keeps the ordering and freezes published
windows. -/
theorem bankRepairDigitWordBelowStepWorker {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (hn : 3 ≤ n) (ht : c.t + 1 < n)
    (hrun : BankRepairDigitWordAccRun ring h p)
    (hb : BankRepairDigitWordBelow ring h) (hph : h.phase = .worker)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e)) :
    BankRepairDigitWordBelowStep ring h
      (BlockA.wordWorkerNext ring h p e request) p (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  have htok := hrun.1
  have hacc := hrun.2.2.2
  unfold BlockA.wordWorkerNext
  dsimp only
  cases hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) with
  | init =>
      exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
  | erase =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseMore _ _).2.1 hcase
      split
      · exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
      · exact bankRepairDigitWordBelowStepQuiet ring h _ p e hb
          (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide)
          (by rw [hrow]; decide) rfl rfl rfl (Or.inl rfl)
  | prefixExit =>
      exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
  | prefixMove =>
      dsimp only
      split
      · rename_i idx z a hk
        repeat' split
        all_goals first
          | exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
          | exact bankRepairDigitWordBelowStepPone ring h _ p _ hb e hk (fun _ => Or.inl rfl)
          | exact bankRepairDigitWordBelowStepPone ring h _ p _ hb e hk (fun i => bankRepairDigitPutOr h.publications _ _ i)
      all_goals exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
  | prefixTerminal =>
      exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
  | prefixPublish =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCasePublish _ _).1 hcase
      split
      · rename_i idx z a hk
        repeat' split
        all_goals first
          | exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
          | skip
        all_goals rename_i hC
        all_goals exact bankRepairDigitWordBelowStepPthree ring h _ p e ht htok hacc hb hk hC.1 hrow rfl hph rfl rfl
      all_goals exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
  | backwardsMove =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseRows _ _).1 hcase
      repeat' split
      all_goals first
        | exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
        | exact bankRepairDigitWordBelowStepQuiet ring h _ p e hb (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) rfl rfl rfl (Or.inl rfl)
  | backwardsInit =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseRows _ _).2.1 hcase
      repeat' split
      all_goals first
        | exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
        | exact bankRepairDigitWordBelowStepQuiet ring h _ p e hb (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) rfl rfl rfl (Or.inl rfl)
  | sumMove =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseRows _ _).2.2 hcase
      repeat' split
      all_goals first
        | exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
        | exact bankRepairDigitWordBelowStepQuiet ring h _ p e hb (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) rfl rfl rfl (Or.inl rfl)
  | sumPublish =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCasePublish _ _).2.1 hcase
      split
      · rename_i target idx z parity trailing hce
        repeat' split
        all_goals first
          | exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
          | skip
        all_goals rename_i hC
        all_goals exact bankRepairDigitWordBelowStepSone ring h _ p e htok hb hce hC.2.1 hrow rfl hph rfl rfl
      all_goals exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
  | advance =>
      dsimp only
      split
      · rename_i hC
        exact bankRepairDigitWordBelowStepAone ring h _ p e hne htok hb hreach
          hfix' hcase hC.1 rfl hph rfl rfl
      · exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
  | terminal =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCasePublish _ _).2.2 hcase
      split
      · exact bankRepairDigitWordBelowStepQuiet ring h _ p e hb
          (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide)
          (by rw [hrow]; decide) rfl rfl rfl (Or.inr rfl)
      · exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
  | frame =>
      obtain ⟨-, -, -, hP1, hP2, hP3, -, -, -, hS1, -, -⟩ :=
        (bankRepairDigitWorkerCaseMore _ _).2.2 hcase
      exact bankRepairDigitWordBelowStepQuiet ring h _ p e hb hP1 hP2 hP3 hS1
        rfl rfl rfl (Or.inl rfl)

/-- The validate phase carries no window receipt and issues none. -/
theorem bankRepairDigitWordBelowStepValidate {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (hb : BankRepairDigitWordBelow ring h) (hph : h.phase = .validate) :
    BankRepairDigitWordBelowStep ring h
      (BlockA.wordValidateNext ring h p e request) p (phiW ring p e) := by
  have hnw := bankRepairDigitWordBelowIdle ring h hb (Or.inr hph)
  unfold BlockA.wordValidateNext
  dsimp only
  split
  all_goals (repeat' split)
  all_goals first
    | exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
    | exact bankRepairDigitWordBelowStepNoWin ring h _ p _ (fun i => hnw i)

/-- One W monitor step outside the done phase. -/
theorem bankRepairDigitWordBelowStepT {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (hn : 3 ≤ n) (ht : c.t + 1 < n)
    (hrun : BankRepairDigitWordAccRun ring h p)
    (hb : BankRepairDigitWordBelow ring h)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e))
    (hd : h.phase ≠ .done) :
    BankRepairDigitWordBelowStep ring h
      (BlockA.wordT ring h p e (phiW ring p e)) p (phiW ring p e) := by
  unfold BlockA.wordT
  split
  · rename_i h0
    exact absurd h0 hd
  · dsimp only
    split
    · exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
    · split
      · exact bankRepairDigitWordBelowStepCleared ring h _ p _ (fun _ => rfl)
      · rename_i hph
        exact bankRepairDigitWordBelowStepValidate ring h p e _ hb hph
      · rename_i hph
        exact bankRepairDigitWordBelowStepWorker ring h p e _ hn ht hrun hb hph
          hreach hfix'
      · rename_i hph
        exact absurd hph hd

theorem bankRepairDigitWordBelowT {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (hn : 3 ≤ n) (ht : c.t + 1 < n)
    (hrun : BankRepairDigitWordAccRun ring h p)
    (hb : BankRepairDigitWordBelow ring h)
    (hreach : BankRepairDigitWordReach ring h p)
    (hfix' : WFixedRoot ring h.root (phiW ring p e)) :
    BankRepairDigitWordBelow ring (BlockA.wordT ring h p e (phiW ring p e)) := by
  by_cases hd : h.phase = .done
  · unfold BlockA.wordT
    rw [if_pos hd]
    exact hb
  · exact (bankRepairDigitWordBelowStepT ring h p e hn ht hrun hb hreach hfix'
      hd).1

theorem bankRepairDigitWordBelowRunAux {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (origin : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (root : Fin n) (h₀ : BlockA.WordControl n c)
    (hγ₀ : γ₀ = .live origin h₀) (hroot₀ : h₀.root = root)
    (hfix₀ : WFixedRoot ring root origin)
    (hcl : ∀ i, h₀.publications i = .absent ∧ h₀.workerKind i = .empty)
    (hcur : ∀ i, h₀.workerCursor i = .empty)
    (hn : 3 ≤ n) (ht : c.t + 1 < n)
    {w : List (Fin n)} {p : Fin n → ProjW c}
    {γ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c)}
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p γ) :
    ∀ shadow h, γ = .live shadow h → BankRepairDigitWordBelow ring h := by
  induction hrun with
  | empty =>
      intro shadow h hγ
      rw [hγ₀] at hγ
      injection hγ with h1 h2
      subst h1 h2
      intro i hi
      rw [(hcl i).1] at hi
      exact absurd hi bankRepairDigitWordWinAbsent
  | @next w p γ hr e ih =>
      intro shadow h hγ
      cases γ with
      | failed =>
          rw [BlockA.update_failed] at hγ
          cases hγ
      | live s h₁ =>
          have hb₁ := ih s h₁ rfl
          have hacc₁ := bankRepairDigitWordAccRunAux ring origin γ₀ root h₀ hγ₀
            hroot₀ hfix₀ hcl hcur hn ht hr s h₁ rfl
          obtain ⟨hs, hfix₁, hreach₁⟩ := bankRepairDigitWordReachRunAux ring
            origin γ₀ root h₀ hγ₀ hroot₀ hfix₀ hcl hn ht hr s h₁ rfl
          rw [hs, AcceptedReceipts.WordEntrance.word_update_live] at hγ
          injection hγ with h1 h2
          subst h1 h2
          exact bankRepairDigitWordBelowT ring h₁ p e hn ht hacc₁ hb₁ hreach₁
            (bankRepairDigitWFixedRootPhiW hn ring h₁.root p e hfix₁)

/-- T12 item 2 (ordering): along every projected W run from
`initializesWord`, window receipts exist only in the worker and done
phases, never together with a prefix colour, strictly below every target
and at or below every ready site. -/
theorem bankRepairDigitWordRunBelow {n : Nat} (ring : DirectedRing n)
    (c : Compiled) :
    ∀ (origin p : Fin n → ProjW c)
      (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
      (w : List (Fin n)) (shadow : Fin n → ProjW c)
      (h : BlockA.WordControl n c),
      BlockA.initializesWord ring origin γ₀ →
      BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
        (.live shadow h) →
      BankRepairDigitWordBelow ring h := by
  intro origin p γ₀ w shadow h hinit hrun
  obtain ⟨root, h₀, hγ₀, hroot, hfix, ht2, htn, -, -, hcl, -, -⟩ := hinit
  have hpow := bankRepairDigitPowLower c.t
  exact bankRepairDigitWordBelowRunAux ring origin γ₀ root h₀ hγ₀ hroot hfix
    (fun i => ⟨(hcl i).2.2.2.2.1, (hcl i).2.2.1⟩) (fun i => (hcl i).2.2.2.1)
    (by omega) (by omega) hrun shadow h rfl

/-- T12 item 2 (step): from every reachable live W state outside the done
phase, each step only changes visible pairs strictly above every window
receipt it keeps or issues (a fresh receipt may sit at the changed site
itself). -/
theorem bankRepairDigitWordRunFreeze {n : Nat} (ring : DirectedRing n)
    (c : Compiled) (origin p : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (w : List (Fin n)) (shadow : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hinit : BlockA.initializesWord ring origin γ₀)
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
      (.live shadow h))
    (hd : h.phase ≠ .done) (e : Fin n) :
    BankRepairDigitWordFreeze ring h (BlockA.wordT ring h p e (phiW ring p e))
      p (phiW ring p e) := by
  have hacc := bankRepairDigitWordRunAcc ring c origin p γ₀ w shadow h hinit hrun
  have hb := bankRepairDigitWordRunBelow ring c origin p γ₀ w shadow h hinit hrun
  obtain ⟨hfix, hreach⟩ :=
    bankRepairDigitWordRunReach ring c origin p γ₀ w shadow h hinit hrun
  obtain ⟨-, -, -, -, -, ht2, htn, -, -, -, -, -⟩ := hinit
  have hpow := bankRepairDigitPowLower c.t
  have hn : 3 ≤ n := by omega
  exact (bankRepairDigitWordBelowStepT ring h p e hn (by omega) hacc hb hreach
    (bankRepairDigitWFixedRootPhiW hn ring h.root p e hfix) hd).2

/-- The frozen window in offsets: a receipt at offset k kept by the step
pins the u and beta bits at every offset m <= k (its window k-t..k and
its own marker). -/
theorem bankRepairDigitWordFreezeWindow {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c)
    (hf : BankRepairDigitWordFreeze ring h h' p p') (k : Nat) (hk : k < n)
    (hold : BankRepairDigitWordWin
      (h.publications (PPL.shiftRight ring h.root k)))
    (hnew : BankRepairDigitWordWin
      (h'.publications (PPL.shiftRight ring h.root k)))
    (m : Nat) (hm : m ≤ k) :
    (p' (PPL.shiftRight ring h.root m)).u = (p (PPL.shiftRight ring h.root m)).u ∧
      (p' (PPL.shiftRight ring h.root m)).beta =
        (p (PPL.shiftRight ring h.root m)).beta := by
  have hvis : AcceptedReceipts.wordVisible p' (PPL.shiftRight ring h.root m) =
      AcceptedReceipts.wordVisible p (PPL.shiftRight ring h.root m) := by
    apply Classical.byContradiction
    intro hne
    rcases hf _ hne _ hnew with ⟨h1, h2⟩ | h1
    · rw [← h1] at h2
      exact h2 hold
    · rw [bankRepairDigitOffsetShift ring h.root k hk,
        bankRepairDigitOffsetShift ring h.root m (by omega)] at h1
      omega
  exact ⟨congrArg Prod.fst hvis, congrArg Prod.snd hvis⟩

/-- T12 item 2: along every W run from `initializesWord`, outside the
done phase, no step rewrites a u (or beta) bit of an already-published
window that the step keeps: for a window receipt at offset k present
before and after the step, the bits at every offset m <= k (the sources
k-t..k-1 and the site itself) are unchanged. -/
theorem bankRepairDigitWordRunWindowFixed {n : Nat} (ring : DirectedRing n)
    (c : Compiled) (origin p : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (w : List (Fin n)) (shadow : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hinit : BlockA.initializesWord ring origin γ₀)
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
      (.live shadow h))
    (hd : h.phase ≠ .done) (e : Fin n) (k : Nat) (hk : k < n)
    (hold : BankRepairDigitWordWin
      (h.publications (PPL.shiftRight ring h.root k)))
    (hnew : BankRepairDigitWordWin
      ((BlockA.wordT ring h p e (phiW ring p e)).publications
        (PPL.shiftRight ring h.root k)))
    (m : Nat) (hm : m ≤ k) :
    ((phiW ring p e) (PPL.shiftRight ring h.root m)).u =
        (p (PPL.shiftRight ring h.root m)).u ∧
      ((phiW ring p e) (PPL.shiftRight ring h.root m)).beta =
        (p (PPL.shiftRight ring h.root m)).beta :=
  bankRepairDigitWordFreezeWindow ring h _ p _
    (bankRepairDigitWordRunFreeze ring c origin p γ₀ w shadow h hinit hrun hd e)
    k hk hold hnew m hm

end L3.RenewalReferenceClock

/-!
T13. Item 1: the done-phase exemption is harmless. Physical records are
arbitrary at `initializesWord`, but the worker launch needs every other
site free, every stray row cancels the worker monitor, and so in the
worker phase uncoloured sites hold OFF records (`BankRepairDigitWordFree`).
The A0 that enters DONE therefore leaves every physical record free, and
from then on every record stays consistent with the bits
(`BankRepairDigitWordPhys`): P1/P3/S1 (and restarted prefixes) only
recompute the published values, so no edge changes the visible word.
Item 2: monitored P3 and S1 preserve `BankRepairDigitWordPublished`.
Item 3: the invariant holds along every W run. See comms/T13-notes.md.
-/

namespace L3.RenewalReferenceClock

open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem bankRepairDigitWOutIzero {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "I0") :
    (serW x y).hard.hardAccept = true ∧ (workerW x y).x = launchPrefix c.t ∧
      (workerW x y).y =
        (if (serW x y).hard.hardRight then offSI c.t else y.si) := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "I0" →
      (serW x y).hard.hardAccept = true ∧ r.x = launchPrefix c.t ∧
        r.y = (if (serW x y).hard.hardRight then offSI c.t else y.si))
      (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutPzero {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "P0") :
    (workerW x y).x = offSI c.t ∧ (workerW x y).y = y.si := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "P0" →
      r.x = offSI c.t ∧ r.y = y.si) (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutPone {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "P1") :
    x.si.kind = .PREFIX ∧ x.si.j.val < c.t ∧
      (workerW x y).x = offSI c.t ∧
      (workerW x y).y.kind = .PREFIX ∧
      (workerW x y).y.cur = .NONE ∧
      (workerW x y).y.j = siJ c.t (x.si.j.val + 1) ∧
      (workerW x y).y.z = (x.si.z || y.u) ∧
      (workerW x y).y.a = (x.si.a && y.u) ∧
      (workerW x y).uX = x.u ∧
      (workerW x y).uY = y.u ∧
      (workerW x y).betaX = x.beta ∧
      (workerW x y).betaY =
        (if x.si.j.val + 1 < c.t then false else y.beta) := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "P1" →
      x.si.kind = .PREFIX ∧ x.si.j.val < c.t ∧
      r.x = offSI c.t ∧ r.y.kind = .PREFIX ∧ r.y.cur = .NONE ∧
      r.y.j = siJ c.t (x.si.j.val + 1) ∧
      r.y.z = (x.si.z || y.u) ∧ r.y.a = (x.si.a && y.u) ∧
      r.uX = x.u ∧ r.uY = y.u ∧ r.betaX = x.beta ∧
      r.betaY = (if x.si.j.val + 1 < c.t then false else y.beta))
      (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutPtwo {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "P2") :
    x.si.kind = .PREFIX ∧ x.si.j.val = c.t ∧ (postW x y).eY.l = true ∧
      (workerW x y).x = offSI c.t ∧ (workerW x y).y = y.si := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "P2" →
      x.si.kind = .PREFIX ∧ x.si.j.val = c.t ∧ (postW x y).eY.l = true ∧
      r.x = offSI c.t ∧ r.y = y.si) (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutPthree {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "P3") :
    x.si.kind = .PREFIX ∧ x.si.j.val = c.t ∧ (postW x y).eY.l = false ∧
      (workerW x y).x = offSI c.t ∧ (workerW x y).y = launchRootBack c.t ∧
      (workerW x y).uX = (if x.si.z == false then true else x.u) ∧
      (workerW x y).betaX = x.si.a ∧
      (workerW x y).uY = y.u ∧ (workerW x y).betaY = y.beta := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "P3" →
      x.si.kind = .PREFIX ∧ x.si.j.val = c.t ∧ (postW x y).eY.l = false ∧
      r.x = offSI c.t ∧ r.y = launchRootBack c.t ∧
      r.uX = (if x.si.z == false then true else x.u) ∧
      r.betaX = x.si.a ∧ r.uY = y.u ∧ r.betaY = y.beta)
      (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutBzero {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "B0") :
    y.si.cur = .BACK ∧ 1 < y.si.j.val ∧ y.si.kind ≠ .PREFIX ∧
      x.si.kind = .OFF ∧
      (workerW x y).x = setCursor x.si .BACK (y.si.j.val - 1) false false true ∧
      (workerW x y).y = clearCursor y.si := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "B0" →
      y.si.cur = .BACK ∧ 1 < y.si.j.val ∧ y.si.kind ≠ .PREFIX ∧
      x.si.kind = .OFF ∧
      r.x = setCursor x.si .BACK (y.si.j.val - 1) false false true ∧
      r.y = clearCursor y.si) (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutBone {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "B1") :
    y.si.cur = .BACK ∧ y.si.j.val = 1 ∧ y.si.kind ≠ .PREFIX ∧
      x.si.kind = .OFF ∧
      (workerW x y).x = setCursor x.si .SUM 0 false false true ∧
      (workerW x y).y = clearCursor y.si := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "B1" →
      y.si.cur = .BACK ∧ y.si.j.val = 1 ∧ y.si.kind ≠ .PREFIX ∧
      x.si.kind = .OFF ∧
      r.x = setCursor x.si .SUM 0 false false true ∧
      r.y = clearCursor y.si) (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutSzero {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "S0") :
    x.si.kind = .OFF ∧ x.si.cur = .SUM ∧ x.si.j.val + 1 < c.t ∧
      y.si.kind = .OFF ∧
      (workerW x y).x = clearCursor x.si ∧
      (workerW x y).y = setCursor y.si .SUM (x.si.j.val + 1) (x.si.z || x.u)
        (Bool.xor x.si.p (c.taps x.si.j.val && x.u))
        (if x.si.j.val == 0 then true else (x.si.a && x.u)) := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "S0" →
      x.si.kind = .OFF ∧ x.si.cur = .SUM ∧ x.si.j.val + 1 < c.t ∧
      y.si.kind = .OFF ∧ r.x = clearCursor x.si ∧
      r.y = setCursor y.si .SUM (x.si.j.val + 1) (x.si.z || x.u)
        (Bool.xor x.si.p (c.taps x.si.j.val && x.u))
        (if x.si.j.val == 0 then true else (x.si.a && x.u))) (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutSone {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "S1") :
    x.si.kind = .OFF ∧ x.si.cur = .SUM ∧ x.si.j.val + 1 = c.t ∧
      y.si.kind = .ROOT ∧
      (workerW x y).x = clearCursor x.si ∧
      (workerW x y).y.kind = y.si.kind ∧ (workerW x y).y.cur = .NONE ∧
      (workerW x y).uY = (if (x.si.z || x.u) == false then true
        else Bool.xor x.si.p (c.taps x.si.j.val && x.u)) ∧
      (workerW x y).betaY =
        ((if x.si.j.val == 0 then true else (x.si.a && x.u)) &&
          (if (x.si.z || x.u) == false then true
            else Bool.xor x.si.p (c.taps x.si.j.val && x.u))) ∧
      (workerW x y).uX = x.u ∧ (workerW x y).betaX = x.beta := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "S1" →
      x.si.kind = .OFF ∧ x.si.cur = .SUM ∧ x.si.j.val + 1 = c.t ∧
      y.si.kind = .ROOT ∧ r.x = clearCursor x.si ∧
      r.y.kind = y.si.kind ∧ r.y.cur = .NONE ∧
      r.uY = (if (x.si.z || x.u) == false then true
        else Bool.xor x.si.p (c.taps x.si.j.val && x.u)) ∧
      r.betaY = ((if x.si.j.val == 0 then true else (x.si.a && x.u)) &&
          (if (x.si.z || x.u) == false then true
            else Bool.xor x.si.p (c.taps x.si.j.val && x.u))) ∧
      r.uX = x.u ∧ r.betaX = x.beta) (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutAzero {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "A0") :
    y.si.kind = .OFF ∧ y.si.cur = .NONE ∧
      (workerW x y).x = offSI c.t ∧ (workerW x y).y = y.si := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "A0" →
      y.si.kind = .OFF ∧ y.si.cur = .NONE ∧
      r.x = offSI c.t ∧ r.y = y.si) (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutAone {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "A1") :
    x.si.kind = .ROOT ∧ (postW x y).eY.l = false ∧
      (workerW x y).x = offSI c.t ∧ (workerW x y).y = launchRootBack c.t := by
  have key : bankRepairDigitHolds (fun r : SIResult c.t => r.row = "A1" →
      x.si.kind = .ROOT ∧ (postW x y).eY.l = false ∧
      r.x = offSI c.t ∧ r.y = launchRootBack c.t) (workerW x y) := by
    unfold workerW siStep
    dsimp only [ProjW.lift]
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals intro hr
    all_goals try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, freeSI,
      Bool.not_eq_true', decide_eq_true_eq, Bool.or_eq_true] at *
    all_goals simp [*] at hr ⊢
  exact key hr

theorem bankRepairDigitWOutIone {c : Compiled} (x y : ProjW c)
    (hr : (workerW x y).row = "I1") :
    (workerW x y).x = (if (serW x y).hard.hardLeft = true then offSI c.t else x.si) ∧
      (workerW x y).y =
        (if (serW x y).hard.hardRight = true then offSI c.t else y.si) :=
  bankRepairDigitSiStepRowIone c _ _ _ _ hr

theorem bankRepairDigitWorkerCaseRest {c : Compiled} (x y : ProjW c) :
    (BlockA.workerCase x y = .init → (workerW x y).row = "I0") ∧
    (BlockA.workerCase x y = .prefixExit → (workerW x y).row = "P0") ∧
    (BlockA.workerCase x y = .prefixTerminal → (workerW x y).row = "P2") := by
  have key : bankRepairDigitHolds
      (fun w : BlockA.WorkerReceiptCase =>
        (w = .init → (workerW x y).row = "I0") ∧
        (w = .prefixExit → (workerW x y).row = "P0") ∧
        (w = .prefixTerminal → (workerW x y).row = "P2"))
      (BlockA.workerCase x y) := by
    unfold BlockA.workerCase
    dsimp only
    repeat' refine bankRepairDigitHoldsIte (fun _ => ?_) (fun _ => ?_)
    all_goals unfold bankRepairDigitHolds
    all_goals simp_all
  exact key

theorem bankRepairDigitSiJVal (t v : Nat) (h : v < t + 1) : (siJ t v).val = v := by
  unfold siJ
  rw [dif_pos h]

/-- The physical record `s` at site `i` is consistent with the bits of
`p`: a PREFIX record sits at its own offset with the prefix OR/AND, a ROOT
record sits at an offset > t, a BACK cursor at offset `T - t + j` of some
target offset t < T < n, and a SUM cursor at `T - t + j` with the window
folds over its first j sources. -/
def BankRepairDigitWordPhysRec {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c)
    (s : SI c.t) (i : Fin n) : Prop :=
  (s.kind = .PREFIX →
    i = PPL.shiftRight ring root s.j.val ∧
    s.z = cwPrefixOr ring root p s.j.val ∧
    s.a = cwPrefixAnd ring root p s.j.val) ∧
  (s.kind = .ROOT → ∃ T, c.t < T ∧ T < n ∧ i = PPL.shiftRight ring root T) ∧
  (s.cur = .BACK → ∃ T, c.t < T ∧ T < n ∧
    i = PPL.shiftRight ring root (T - c.t + s.j.val)) ∧
  (s.cur = .SUM → ∃ T, c.t < T ∧ T < n ∧
    i = PPL.shiftRight ring root (T - c.t + s.j.val) ∧
    s.z = cwSumOr ring root p T s.j.val ∧
    s.p = cwSumParity ring root p T s.j.val ∧
    s.a = cwSumTrailing ring root p T s.j.val)

/-- T13 item 1: every physical SI record is consistent with the bits. -/
def BankRepairDigitWordPhys {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c) : Prop :=
  ∀ i, BankRepairDigitWordPhysRec ring root p (p i).si i

theorem bankRepairDigitWordPhysRecFree {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c)
    (s : SI c.t) (i : Fin n) (hk : s.kind = .OFF) (hc : s.cur = .NONE) :
    BankRepairDigitWordPhysRec ring root p s i := by
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · rw [hk] at h0
    cases h0
  · rw [hk] at h0
    cases h0
  · rw [hc] at h0
    cases h0
  · rw [hc] at h0
    cases h0

theorem bankRepairDigitWordPhysRecOff {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c) (i : Fin n) :
    BankRepairDigitWordPhysRec ring root p (offSI c.t) i :=
  bankRepairDigitWordPhysRecFree ring root p _ i rfl rfl

theorem bankRepairDigitWordPhysRecClear {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c)
    (s : SI c.t) (i : Fin n) (hk : s.kind = .OFF) :
    BankRepairDigitWordPhysRec ring root p (clearCursor s) i :=
  bankRepairDigitWordPhysRecFree ring root p _ i hk rfl

theorem bankRepairDigitWordPhysRecRootBack {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c)
    (T : Nat) (h1 : c.t < T) (h2 : T < n) :
    BankRepairDigitWordPhysRec ring root p (launchRootBack c.t)
      (PPL.shiftRight ring root T) := by
  refine ⟨fun h0 => ?_, fun _ => ⟨T, h1, h2, rfl⟩, fun _ => ⟨T, h1, h2, ?_⟩,
    fun h0 => ?_⟩
  · cases h0
  · show PPL.shiftRight ring root T = PPL.shiftRight ring root (T - c.t + c.t)
    rw [Nat.sub_add_cancel (by omega)]
  · cases h0

theorem bankRepairDigitWordPhysRecCongr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p p' : Fin n → ProjW c)
    (hu : ∀ m, (p' m).u = (p m).u) (s : SI c.t) (i : Fin n)
    (h : BankRepairDigitWordPhysRec ring root p s i) :
    BankRepairDigitWordPhysRec ring root p' s i := by
  have hf := bankRepairDigitWordFoldsCongr ring root p p' hu
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun h0 => ?_, h2, h3, fun h0 => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := h1 h0
    exact ⟨a1, by rw [(hf 0 _).1]; exact a2, by rw [(hf 0 _).2.1]; exact a3⟩
  · obtain ⟨T, a1, a2, a3, a4, a5, a6⟩ := h4 h0
    exact ⟨T, a1, a2, a3, by rw [(hf T _).2.2.1]; exact a4,
      by rw [(hf T _).2.2.2.1]; exact a5, by rw [(hf T _).2.2.2.2]; exact a6⟩

theorem bankRepairDigitWordPhysAllFree {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c)
    (hf : ∀ i, (p i).si.kind = .OFF ∧ (p i).si.cur = .NONE) :
    BankRepairDigitWordPhys ring root p :=
  fun i => bankRepairDigitWordPhysRecFree ring root p _ i (hf i).1 (hf i).2

theorem bankRepairDigitPostEY {n : Nat} {c : Compiled} (ring : DirectedRing n)
    (p : Fin n → ProjW c) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    ((phiW ring p e) (ring.rightNeighbor e)).native.l =
      (postW (p e) (p (ring.rightNeighbor e))).eY.l := by
  have hy : (phiW ring p e) (ring.rightNeighbor e) =
      (pairW (p e) (p (ring.rightNeighbor e))).2 := by
    simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
  rw [hy]
  rfl

theorem bankRepairDigitEYTrue {n : Nat} {c : Compiled} (ring : DirectedRing n)
    (root : Fin n) (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hfix' : WFixedRoot ring root (phiW ring p e))
    (hl : (postW (p e) (p (ring.rightNeighbor e))).eY.l = true) :
    ring.rightNeighbor e = root :=
  hfix'.2.1 _ (by rw [bankRepairDigitPostEY ring p e hne]; exact hl)

theorem bankRepairDigitEYFalse {n : Nat} {c : Compiled} (ring : DirectedRing n)
    (root : Fin n) (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hfix' : WFixedRoot ring root (phiW ring p e))
    (hl : (postW (p e) (p (ring.rightNeighbor e))).eY.l = false) :
    ring.rightNeighbor e ≠ root := by
  intro h0
  have h1 := hfix'.1
  rw [← h0, bankRepairDigitPostEY ring p e hne, hl] at h1
  cases h1

theorem bankRepairDigitVisibleOfOutputs {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n)
    (hux : (workerW (p e) (p (ring.rightNeighbor e))).uX = (p e).u)
    (hbx : (workerW (p e) (p (ring.rightNeighbor e))).betaX = (p e).beta)
    (huy : (workerW (p e) (p (ring.rightNeighbor e))).uY =
      (p (ring.rightNeighbor e)).u)
    (hby : (workerW (p e) (p (ring.rightNeighbor e))).betaY =
      (p (ring.rightNeighbor e)).beta) :
    ∀ i, AcceptedReceipts.wordVisible (phiW ring p e) i =
      AcceptedReceipts.wordVisible p i := by
  intro i
  unfold AcceptedReceipts.wordVisible phiW projectedEdge
  by_cases hie : i = e
  · rw [if_pos hie, hie]
    exact Prod.ext hux hbx
  · rw [if_neg hie]
    by_cases hij : i = ring.rightNeighbor e
    · rw [if_pos hij, hij]
      exact Prod.ext huy hby
    · rw [if_neg hij]

theorem bankRepairDigitAllPublishedAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (hall : BlockA.wordAllPublished ring h) (m : Nat) (h0 : 0 < m)
    (hm : m < n) :
    (m < c.t → h.publications (PPL.shiftRight ring h.root m) = .prefixZero) ∧
    (m = c.t → h.publications (PPL.shiftRight ring h.root m) = .prefixEnd) ∧
    (c.t < m →
      h.publications (PPL.shiftRight ring h.root m) = .recurrence) := by
  have hk := hall ⟨m, hm⟩ h0
  dsimp only at hk
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · rw [if_pos h1] at hk
    exact hk.1
  · rw [if_neg (by omega), if_pos h1] at hk
    exact hk.1
  · rw [if_neg (by omega), if_neg (by omega)] at hk
    exact hk.1

/-- The first-window trailing AND is the prefix AND one step shorter. -/
theorem bankRepairDigitTrailingFirst {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c) :
    ∀ m, cwSumTrailing ring root p c.t (m + 1) = cwPrefixAnd ring root p m := by
  intro m
  induction m with
  | zero =>
      rw [(bankRepairDigitSumFoldStep ring root p c.t 0).2.2, if_pos rfl]
      rfl
  | succ m ih =>
      rw [(bankRepairDigitSumFoldStep ring root p c.t (m + 1)).2.2,
        if_neg (Nat.succ_ne_zero m), ih,
        (bankRepairDigitPrefixFoldStep ring root p m).2]
      unfold cwSourceBit
      rw [Nat.sub_self, Nat.zero_add]

/-- T13 item 1, done phase: with every receipt issued (`wordAllPublished`),
the receipts certifying their equations, and every physical record
consistent with the bits, no projected W edge changes a visible pair.
P1 rewrites a zero marker, P3 and S1 recompute the published value, and
P2 cannot fire (its responder would be the root at offset t+1 < n). -/
theorem bankRepairDigitWordDoneVisible {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n) (ht : c.t + 1 < n) (ht2 : 2 ≤ c.t)
    (hpub : BankRepairDigitWordPublished ring h p)
    (hall : BlockA.wordAllPublished ring h)
    (hphys : BankRepairDigitWordPhys ring h.root p) :
    ∀ i, AcceptedReceipts.wordVisible (phiW ring p e) i =
      AcceptedReceipts.wordVisible p i := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  have hfix' := bankRepairDigitWFixedRootPhiW hn ring h.root p e hpub.rootFixed
  by_cases h1 : (workerW (p e) (p (ring.rightNeighbor e))).row = "P1"
  · obtain ⟨hk, hjt, -, -, -, -, -, -, hux, huy, hbx, hby⟩ :=
      bankRepairDigitWOutPone _ _ h1
    obtain ⟨he, -, -⟩ := (hphys e).1 hk
    have hj : ring.rightNeighbor e =
        PPL.shiftRight ring h.root ((p e).si.j.val + 1) := by
      rw [WordPhase.wordPhaseShiftSucc, ← he]
    refine bankRepairDigitVisibleOfOutputs ring p e hux hbx huy ?_
    rw [hby]
    split
    · rename_i hlt
      have hrec := (bankRepairDigitAllPublishedAt ring h hall _ (by omega)
        (by omega)).1 hlt
      have hm := hpub.prefixZeros ⟨(p e).si.j.val + 1, by omega⟩
        (by show 0 < (p e).si.j.val + 1; omega) hlt hrec
      have hm' : (p (PPL.shiftRight ring h.root ((p e).si.j.val + 1))).beta =
          false := hm
      rw [hj]
      exact hm'.symm
    · rfl
  by_cases h2 : (workerW (p e) (p (ring.rightNeighbor e))).row = "P2"
  · exfalso
    obtain ⟨hk, hjt, hl, -, -⟩ := bankRepairDigitWOutPtwo _ _ h2
    obtain ⟨he, -, -⟩ := (hphys e).1 hk
    rw [hjt] at he
    have hj : ring.rightNeighbor e = PPL.shiftRight ring h.root (c.t + 1) := by
      rw [WordPhase.wordPhaseShiftSucc, ← he]
    have hr := bankRepairDigitEYTrue ring h.root p e hne hfix' hl
    rw [hj] at hr
    have h0 := bankRepairDigitShiftInjective ring h.root (c.t + 1) 0 ht
      (by omega) (hr.trans (WordPhase.wordPhaseShiftZero ring h.root).symm)
    omega
  by_cases h3 : (workerW (p e) (p (ring.rightNeighbor e))).row = "P3"
  · obtain ⟨hk, hjt, -, -, -, hux, hbx, huy, hby⟩ :=
      bankRepairDigitWOutPthree _ _ h3
    obtain ⟨he, hz, ha⟩ := (hphys e).1 hk
    rw [hjt] at he hz ha
    have hrec := (bankRepairDigitAllPublishedAt ring h hall c.t (by omega)
      (by omega)).2.1 rfl
    obtain ⟨hor, hm⟩ := hpub.firstWindow ⟨c.t, by omega⟩ rfl hrec
    have hor' : cwPrefixOr ring h.root p c.t = true := hor
    have hm' : (p (PPL.shiftRight ring h.root c.t)).beta =
        (cwSumTrailing ring h.root p c.t c.t && cwBit ring h.root p c.t) := hm
    have htr : cwSumTrailing ring h.root p c.t c.t =
        cwPrefixAnd ring h.root p (c.t - 1) := by
      have h5 := bankRepairDigitTrailingFirst ring h.root p (c.t - 1)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ c.t)] at h5
    have hand : cwPrefixAnd ring h.root p c.t =
        (cwPrefixAnd ring h.root p (c.t - 1) && cwBit ring h.root p c.t) := by
      have h5 := (bankRepairDigitPrefixFoldStep ring h.root p (c.t - 1)).2
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ c.t)] at h5
    refine bankRepairDigitVisibleOfOutputs ring p e ?_ ?_ huy hby
    · rw [hux, hz, hor']
      rfl
    · rw [hbx, ha, he, hm', htr, hand]
  by_cases h4 : (workerW (p e) (p (ring.rightNeighbor e))).row = "S1"
  · obtain ⟨-, hc, hjt, -, -, -, -, huy, hby, hux, hbx⟩ :=
      bankRepairDigitWOutSone _ _ h4
    obtain ⟨T, hT1, hT2, he, hz, hp, ha⟩ := (hphys e).2.2.2 hc
    have hj : ring.rightNeighbor e = PPL.shiftRight ring h.root T := by
      have h5 : T = T - c.t + (p e).si.j.val + 1 := by omega
      rw [h5, WordPhase.wordPhaseShiftSucc, ← he]
    have hrec := (bankRepairDigitAllPublishedAt ring h hall T (by omega)
      hT2).2.2 hT1
    obtain ⟨hwin, hm⟩ := hpub.laterWindows ⟨T, hT2⟩ hT1 hrec
    have hwin' : (cwSumOr ring h.root p T c.t = true ∧
          cwBit ring h.root p T = cwSumParity ring h.root p T c.t) ∨
        (cwSumOr ring h.root p T c.t = false ∧ cwBit ring h.root p T = true) :=
      hwin
    have hm' : cwMarker ring h.root p T =
        (cwSumTrailing ring h.root p T c.t && cwBit ring h.root p T) := hm
    have hsrc : cwSourceBit ring h.root p T (p e).si.j.val = (p e).u := by
      unfold cwSourceBit cwBit
      rw [← he]
    obtain ⟨hs1, hs2, hs3⟩ :=
      bankRepairDigitSumFoldStep ring h.root p T (p e).si.j.val
    rw [hjt, hsrc, ← hz] at hs1
    rw [hjt, hsrc, ← hp] at hs2
    rw [hjt, hsrc] at hs3
    have hA : (if ((p e).si.j.val == 0) = true then true
        else ((p e).si.a && (p e).u)) = cwSumTrailing ring h.root p T c.t := by
      rw [hs3]
      by_cases hJ0 : (p e).si.j.val = 0
      · simp [hJ0, cwSumTrailing]
      · simp [hJ0, ha]
    have hv : (if (cwSumOr ring h.root p T c.t == false) = true then true
        else cwSumParity ring h.root p T c.t) = cwBit ring h.root p T := by
      rcases hwin' with ⟨h5, h6⟩ | ⟨h5, h6⟩
      · rw [h5, h6]
        rfl
      · rw [h5, h6]
        rfl
    refine bankRepairDigitVisibleOfOutputs ring p e hux hbx ?_ ?_
    · rw [huy, ← hs1, ← hs2, hv, hj]
      rfl
    · rw [hby, ← hs1, ← hs2, hA, hv, hj]
      exact hm'.symm
  exact bankRepairDigitQuietRowVisible ring p e h1 h2 h3 h4

/-- Every projected W edge writes physically consistent records at its two
sites (read against the OLD bits). -/
theorem bankRepairDigitWordPhysRecs {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n) (ht : c.t + 1 < n)
    (hfix : WFixedRoot ring root p)
    (hphys : BankRepairDigitWordPhys ring root p) :
    BankRepairDigitWordPhysRec ring root p
        (workerW (p e) (p (ring.rightNeighbor e))).x e ∧
      BankRepairDigitWordPhysRec ring root p
        (workerW (p e) (p (ring.rightNeighbor e))).y (ring.rightNeighbor e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  have hfix' := bankRepairDigitWFixedRootPhiW hn ring root p e hfix
  cases hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) with
  | init =>
      obtain ⟨hacc, hx, hy⟩ := bankRepairDigitWOutIzero _ _
        ((bankRepairDigitWorkerCaseRest _ _).1 hcase)
      have her : e = root := hfix.2.1 e (bankRepairDigitHardAcceptLeader _ _ hacc)
      refine ⟨?_, ?_⟩
      · rw [hx]
        refine ⟨fun _ => ⟨?_, rfl, rfl⟩, fun h0 => ?_, fun h0 => ?_,
          fun h0 => ?_⟩
        · rw [her]
          exact (WordPhase.wordPhaseShiftZero ring root).symm
        · cases h0
        · cases h0
        · cases h0
      · rw [hy]
        split
        · exact bankRepairDigitWordPhysRecOff ring root p _
        · exact hphys _
  | erase =>
      obtain ⟨hx, hy⟩ := bankRepairDigitWOutIone _ _
        ((bankRepairDigitWorkerCaseMore _ _).2.1 hcase)
      refine ⟨?_, ?_⟩
      · rw [hx]
        split
        · exact bankRepairDigitWordPhysRecOff ring root p _
        · exact hphys _
      · rw [hy]
        split
        · exact bankRepairDigitWordPhysRecOff ring root p _
        · exact hphys _
  | prefixExit =>
      obtain ⟨hx, hy⟩ := bankRepairDigitWOutPzero _ _
        ((bankRepairDigitWorkerCaseRest _ _).2.1 hcase)
      rw [hx, hy]
      exact ⟨bankRepairDigitWordPhysRecOff ring root p _, hphys _⟩
  | prefixTerminal =>
      obtain ⟨-, -, -, hx, hy⟩ := bankRepairDigitWOutPtwo _ _
        ((bankRepairDigitWorkerCaseRest _ _).2.2 hcase)
      rw [hx, hy]
      exact ⟨bankRepairDigitWordPhysRecOff ring root p _, hphys _⟩
  | terminal =>
      obtain ⟨-, -, hx, hy⟩ := bankRepairDigitWOutAzero _ _
        ((bankRepairDigitWorkerCasePublish _ _).2.2 hcase)
      rw [hx, hy]
      exact ⟨bankRepairDigitWordPhysRecOff ring root p _, hphys _⟩
  | frame =>
      have hf := bankRepairDigitSiStepFrame c _ _ _ _
        ((bankRepairDigitWorkerCaseMore _ _).2.2 hcase)
      have hx : (workerW (p e) (p (ring.rightNeighbor e))).x = (p e).si := hf.1
      have hy : (workerW (p e) (p (ring.rightNeighbor e))).y =
          (p (ring.rightNeighbor e)).si := hf.2.1
      rw [hx, hy]
      exact ⟨hphys _, hphys _⟩
  | prefixMove =>
      obtain ⟨hk, hjt, hx, hyk, hyc, hyj, hyz, hya, -⟩ :=
        bankRepairDigitWOutPone _ _ ((bankRepairDigitWorkerCaseMore _ _).1 hcase)
      obtain ⟨he, hz, ha⟩ := (hphys e).1 hk
      have hj : ring.rightNeighbor e =
          PPL.shiftRight ring root ((p e).si.j.val + 1) := by
        rw [WordPhase.wordPhaseShiftSucc, ← he]
      have hjv : (workerW (p e) (p (ring.rightNeighbor e))).y.j.val =
          (p e).si.j.val + 1 := by
        rw [hyj]
        exact bankRepairDigitSiJSucc _ _ hjt
      refine ⟨by rw [hx]; exact bankRepairDigitWordPhysRecOff ring root p _, ?_⟩
      refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
      · rw [hjv]
        exact hj
      · rw [hyz, hjv, (bankRepairDigitPrefixFoldStep ring root p _).1, ← hz, hj]
        rfl
      · rw [hya, hjv, (bankRepairDigitPrefixFoldStep ring root p _).2, ← ha, hj]
        rfl
      · rw [hyk] at h0
        cases h0
      · rw [hyc] at h0
        cases h0
      · rw [hyc] at h0
        cases h0
  | prefixPublish =>
      obtain ⟨hk, hjt, -, hx, hy, -⟩ := bankRepairDigitWOutPthree _ _
        ((bankRepairDigitWorkerCasePublish _ _).1 hcase)
      obtain ⟨he, -, -⟩ := (hphys e).1 hk
      rw [hjt] at he
      have hj : ring.rightNeighbor e = PPL.shiftRight ring root (c.t + 1) := by
        rw [WordPhase.wordPhaseShiftSucc, ← he]
      refine ⟨by rw [hx]; exact bankRepairDigitWordPhysRecOff ring root p _, ?_⟩
      rw [hy, hj]
      exact bankRepairDigitWordPhysRecRootBack ring root p _ (by omega) ht
  | advance =>
      obtain ⟨hk, hl, hx, hy⟩ := bankRepairDigitWOutAone _ _
        (bankRepairDigitWorkerCaseAdvance _ _ hcase)
      obtain ⟨T, hT1, hT2, he⟩ := (hphys e).2.1 hk
      have hj : ring.rightNeighbor e = PPL.shiftRight ring root (T + 1) := by
        rw [WordPhase.wordPhaseShiftSucc, ← he]
      have hjr := bankRepairDigitEYFalse ring root p e hne hfix' hl
      have hT3 : T + 1 < n := by
        by_cases h0 : T + 1 < n
        · exact h0
        · exfalso
          apply hjr
          rw [hj, show T + 1 = n by omega]
          exact bankRepairDigitShiftFull ring root
      refine ⟨by rw [hx]; exact bankRepairDigitWordPhysRecOff ring root p _, ?_⟩
      rw [hy, hj]
      exact bankRepairDigitWordPhysRecRootBack ring root p _ (by omega) hT3
  | backwardsMove =>
      obtain ⟨hc, hj1, hkp, hxk, hx, hy⟩ := bankRepairDigitWOutBzero _ _
        ((bankRepairDigitWorkerCaseRows _ _).1 hcase)
      obtain ⟨T, hT1, hT2, hjpos⟩ := (hphys (ring.rightNeighbor e)).2.2.1 hc
      have hjlt := (p (ring.rightNeighbor e)).si.j.isLt
      have hepos : e = PPL.shiftRight ring root
          (T - c.t + ((p (ring.rightNeighbor e)).si.j.val - 1)) := by
        apply bankRepairDigitShiftPred ring root e
        exact hjpos.trans (congrArg (PPL.shiftRight ring root) (by omega))
      refine ⟨?_, ?_⟩
      · rw [hx]
        refine ⟨fun h0 => ?_, fun h0 => ?_, fun _ => ⟨T, hT1, hT2, ?_⟩,
          fun h0 => ?_⟩
        · have h1 : (p e).si.kind = .PREFIX := h0
          rw [hxk] at h1
          cases h1
        · have h1 : (p e).si.kind = .ROOT := h0
          rw [hxk] at h1
          cases h1
        · show e = PPL.shiftRight ring root (T - c.t +
            (siJ c.t ((p (ring.rightNeighbor e)).si.j.val - 1)).val)
          rw [bankRepairDigitSiJVal _ _ (by omega)]
          exact hepos
        · have h1 : SICur.BACK = .SUM := h0
          cases h1
      · rw [hy]
        refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
        · exact absurd h0 hkp
        · exact (hphys _).2.1 h0
        · cases h0
        · cases h0
  | backwardsInit =>
      obtain ⟨hc, hj1, hkp, hxk, hx, hy⟩ := bankRepairDigitWOutBone _ _
        ((bankRepairDigitWorkerCaseRows _ _).2.1 hcase)
      obtain ⟨T, hT1, hT2, hjpos⟩ := (hphys (ring.rightNeighbor e)).2.2.1 hc
      have hepos : e = PPL.shiftRight ring root (T - c.t + 0) := by
        apply bankRepairDigitShiftPred ring root e
        exact hjpos.trans (congrArg (PPL.shiftRight ring root) (by omega))
      refine ⟨?_, ?_⟩
      · rw [hx]
        refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_,
          fun _ => ⟨T, hT1, hT2, ?_, ?_, ?_, ?_⟩⟩
        · have h1 : (p e).si.kind = .PREFIX := h0
          rw [hxk] at h1
          cases h1
        · have h1 : (p e).si.kind = .ROOT := h0
          rw [hxk] at h1
          cases h1
        · have h1 : SICur.SUM = .BACK := h0
          cases h1
        · show e = PPL.shiftRight ring root (T - c.t + (siJ c.t 0).val)
          rw [bankRepairDigitSiJVal _ _ (by omega)]
          exact hepos
        · show false = cwSumOr ring root p T (siJ c.t 0).val
          rw [bankRepairDigitSiJVal _ _ (by omega)]
          rfl
        · show false = cwSumParity ring root p T (siJ c.t 0).val
          rw [bankRepairDigitSiJVal _ _ (by omega)]
          rfl
        · show true = cwSumTrailing ring root p T (siJ c.t 0).val
          rw [bankRepairDigitSiJVal _ _ (by omega)]
          rfl
      · rw [hy]
        refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
        · exact absurd h0 hkp
        · exact (hphys _).2.1 h0
        · cases h0
        · cases h0
  | sumMove =>
      obtain ⟨hxk, hc, hjt, hyk, hx, hy⟩ := bankRepairDigitWOutSzero _ _
        ((bankRepairDigitWorkerCaseRows _ _).2.2 hcase)
      obtain ⟨T, hT1, hT2, he, hz, hp, ha⟩ := (hphys e).2.2.2 hc
      have hsrc : cwSourceBit ring root p T (p e).si.j.val = (p e).u := by
        unfold cwSourceBit cwBit
        rw [← he]
      obtain ⟨hs1, hs2, hs3⟩ :=
        bankRepairDigitSumFoldStep ring root p T (p e).si.j.val
      rw [hsrc, ← hz] at hs1
      rw [hsrc, ← hp] at hs2
      rw [hsrc] at hs3
      refine ⟨by rw [hx]; exact bankRepairDigitWordPhysRecClear ring root p _ _ hxk,
        ?_⟩
      rw [hy]
      refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_,
        fun _ => ⟨T, hT1, hT2, ?_, ?_, ?_, ?_⟩⟩
      · have h1 : (p (ring.rightNeighbor e)).si.kind = .PREFIX := h0
        rw [hyk] at h1
        cases h1
      · have h1 : (p (ring.rightNeighbor e)).si.kind = .ROOT := h0
        rw [hyk] at h1
        cases h1
      · have h1 : SICur.SUM = .BACK := h0
        cases h1
      · show ring.rightNeighbor e = PPL.shiftRight ring root (T - c.t +
          (siJ c.t ((p e).si.j.val + 1)).val)
        rw [bankRepairDigitSiJVal _ _ (by omega),
          show T - c.t + ((p e).si.j.val + 1) = T - c.t + (p e).si.j.val + 1 by omega,
          WordPhase.wordPhaseShiftSucc, ← he]
      · show ((p e).si.z || (p e).u) =
          cwSumOr ring root p T (siJ c.t ((p e).si.j.val + 1)).val
        rw [bankRepairDigitSiJVal _ _ (by omega), hs1]
      · show Bool.xor (p e).si.p (c.taps (p e).si.j.val && (p e).u) =
          cwSumParity ring root p T (siJ c.t ((p e).si.j.val + 1)).val
        rw [bankRepairDigitSiJVal _ _ (by omega), hs2]
      · show (if ((p e).si.j.val == 0) = true then true
            else ((p e).si.a && (p e).u)) =
          cwSumTrailing ring root p T (siJ c.t ((p e).si.j.val + 1)).val
        rw [bankRepairDigitSiJVal _ _ (by omega), hs3]
        by_cases hJ0 : (p e).si.j.val = 0
        · simp [hJ0, cwSumTrailing]
        · simp [hJ0, ha]
  | sumPublish =>
      obtain ⟨hxk, hc, hjt, hyk0, hx, hyk, hyc, -⟩ := bankRepairDigitWOutSone _ _
        ((bankRepairDigitWorkerCasePublish _ _).2.1 hcase)
      obtain ⟨T, hT1, hT2, he, -⟩ := (hphys e).2.2.2 hc
      have hj : ring.rightNeighbor e = PPL.shiftRight ring root T := by
        have h5 : T = T - c.t + (p e).si.j.val + 1 := by omega
        rw [h5, WordPhase.wordPhaseShiftSucc, ← he]
      refine ⟨by rw [hx]; exact bankRepairDigitWordPhysRecClear ring root p _ _ hxk,
        ?_⟩
      refine ⟨fun h0 => ?_, fun _ => ⟨T, hT1, hT2, hj⟩, fun h0 => ?_, fun h0 => ?_⟩
      · rw [hyk, hyk0] at h0
        cases h0
      · rw [hyc] at h0
        cases h0
      · rw [hyc] at h0
        cases h0

/-- T13 item 1, done phase: if no visible bit changes, the physical
consistency invariant survives every projected W edge. -/
theorem bankRepairDigitWordPhysStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n) (ht : c.t + 1 < n)
    (hfix : WFixedRoot ring root p)
    (hphys : BankRepairDigitWordPhys ring root p)
    (hu : ∀ i, ((phiW ring p e) i).u = (p i).u) :
    BankRepairDigitWordPhys ring root (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  obtain ⟨hrx, hry⟩ := bankRepairDigitWordPhysRecs ring root p e hn ht hfix hphys
  obtain ⟨hsx, hsy⟩ := bankRepairDigitPhiWSites ring p e hne
  intro i
  by_cases hie : i = e
  · rw [hie, hsx]
    exact bankRepairDigitWordPhysRecCongr ring root p _ hu _ _ hrx
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij, hsy]
      exact bankRepairDigitWordPhysRecCongr ring root p _ hu _ _ hry
    · rw [cwPhiWFrame ring p e i hie hij]
      exact bankRepairDigitWordPhysRecCongr ring root p _ hu _ _ (hphys i)

/-- T13 item 1: the invariant on physical records at uncoloured sites. In
the worker phase a site without a kind colour holds an OFF record, which
has no cursor unless the site carries a cursor colour. -/
def BankRepairDigitWordFree {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (p : Fin n → ProjW c) : Prop :=
  h.phase = .worker → ∀ i, h.workerKind i = .empty →
    (p i).si.kind = .OFF ∧ (h.workerCursor i = .empty → (p i).si.cur = .NONE)

theorem bankRepairDigitWordFreeOfPhase {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (p : Fin n → ProjW c)
    (hph : h.phase ≠ .worker) : BankRepairDigitWordFree h p :=
  fun h0 => absurd h0 hph

theorem bankRepairDigitWordFreeClear {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (r : Bool) (p : Fin n → ProjW c) :
    BankRepairDigitWordFree (BlockA.wordClear h r) p :=
  bankRepairDigitWordFreeOfPhase _ p (by intro h0; cases h0)

theorem bankRepairDigitWordFreeSites {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hfree : BankRepairDigitWordFree h p) (hph : h.phase = .worker)
    (hk : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e →
      h'.workerKind i = h.workerKind i)
    (hc : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e →
      h'.workerCursor i = h.workerCursor i)
    (hx : h'.workerKind e = .empty →
      (workerW (p e) (p (ring.rightNeighbor e))).x.kind = .OFF ∧
        (h'.workerCursor e = .empty →
          (workerW (p e) (p (ring.rightNeighbor e))).x.cur = .NONE))
    (hy : h'.workerKind (ring.rightNeighbor e) = .empty →
      (workerW (p e) (p (ring.rightNeighbor e))).y.kind = .OFF ∧
        (h'.workerCursor (ring.rightNeighbor e) = .empty →
          (workerW (p e) (p (ring.rightNeighbor e))).y.cur = .NONE)) :
    BankRepairDigitWordFree h' (phiW ring p e) := by
  intro _ i hki
  obtain ⟨hsx, hsy⟩ := bankRepairDigitPhiWSites ring p e hne
  by_cases hie : i = e
  · rw [hie] at hki ⊢
    rw [hsx]
    exact hx hki
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij] at hki ⊢
      rw [hsy]
      exact hy hki
    · rw [cwPhiWFrame ring p e i hie hij, hc i hie hij]
      rw [hk i hie hij] at hki
      exact hfree hph i hki

theorem bankRepairDigitWordFreeWorker {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool) (hn : 3 ≤ n)
    (hfree : BankRepairDigitWordFree h p) (hph : h.phase = .worker) :
    BankRepairDigitWordFree (BlockA.wordWorkerNext ring h p e request)
      (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  unfold BlockA.wordWorkerNext
  dsimp only
  cases hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) with
  | init => exact bankRepairDigitWordFreeClear h _ _
  | prefixExit => exact bankRepairDigitWordFreeClear h _ _
  | prefixTerminal => exact bankRepairDigitWordFreeClear h _ _
  | erase =>
      dsimp only
      obtain ⟨hx, hy⟩ := bankRepairDigitWOutIone _ _
        ((bankRepairDigitWorkerCaseMore _ _).2.1 hcase)
      split
      · exact bankRepairDigitWordFreeClear h _ _
      · refine bankRepairDigitWordFreeSites ring h _ p e hne hfree hph
          (fun _ _ _ => rfl) (fun _ _ _ => rfl) ?_ ?_
        · intro hke
          rw [hx]
          split
          · exact ⟨rfl, fun _ => rfl⟩
          · exact hfree hph e hke
        · intro hkj
          rw [hy]
          split
          · exact ⟨rfl, fun _ => rfl⟩
          · exact hfree hph _ hkj
  | frame =>
      have hf := bankRepairDigitSiStepFrame c _ _ _ _
        ((bankRepairDigitWorkerCaseMore _ _).2.2 hcase)
      have hx : (workerW (p e) (p (ring.rightNeighbor e))).x = (p e).si := hf.1
      have hy : (workerW (p e) (p (ring.rightNeighbor e))).y =
          (p (ring.rightNeighbor e)).si := hf.2.1
      refine bankRepairDigitWordFreeSites ring h _ p e hne hfree hph
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) ?_ ?_
      · intro hke
        rw [hx]
        exact hfree hph e hke
      · intro hkj
        rw [hy]
        exact hfree hph _ hkj
  | prefixMove =>
      dsimp only
      obtain ⟨-, -, hx, -⟩ := bankRepairDigitWOutPone _ _
        ((bankRepairDigitWorkerCaseMore _ _).1 hcase)
      repeat' split
      all_goals first
        | exact bankRepairDigitWordFreeClear h _ _
        | exact bankRepairDigitWordFreeSites ring h _ p e hne hfree hph (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun _ _ _ => rfl) (fun _ => by rw [hx]; exact ⟨rfl, fun _ => rfl⟩) (fun h0 => by simp [BlockA.wordPut] at h0)
  | prefixPublish =>
      dsimp only
      obtain ⟨-, -, -, hx, -⟩ := bankRepairDigitWOutPthree _ _
        ((bankRepairDigitWorkerCasePublish _ _).1 hcase)
      repeat' split
      all_goals first
        | exact bankRepairDigitWordFreeClear h _ _
        | exact bankRepairDigitWordFreeSites ring h _ p e hne hfree hph (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun _ => by rw [hx]; exact ⟨rfl, fun _ => rfl⟩) (fun h0 => by simp [BlockA.wordPut] at h0)
  | advance =>
      dsimp only
      obtain ⟨-, -, hx, -⟩ := bankRepairDigitWOutAone _ _
        (bankRepairDigitWorkerCaseAdvance _ _ hcase)
      repeat' split
      all_goals first
        | exact bankRepairDigitWordFreeClear h _ _
        | exact bankRepairDigitWordFreeSites ring h _ p e hne hfree hph (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun _ => by rw [hx]; exact ⟨rfl, fun _ => rfl⟩) (fun h0 => by simp [BlockA.wordPut] at h0)
  | sumPublish =>
      dsimp only
      obtain ⟨hxk, -, -, -, hx, -⟩ := bankRepairDigitWOutSone _ _
        ((bankRepairDigitWorkerCasePublish _ _).2.1 hcase)
      repeat' split
      all_goals first
        | exact bankRepairDigitWordFreeClear h _ _
        | exact bankRepairDigitWordFreeSites ring h _ p e hne hfree hph (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun _ => by rw [hx]; exact ⟨hxk, fun _ => rfl⟩) (fun h0 => by simp [BlockA.wordPut] at h0)
  | backwardsMove =>
      dsimp only
      obtain ⟨-, -, -, hxk, hx, hy⟩ := bankRepairDigitWOutBzero _ _
        ((bankRepairDigitWorkerCaseRows _ _).1 hcase)
      repeat' split
      all_goals first
        | exact bankRepairDigitWordFreeClear h _ _
        | exact bankRepairDigitWordFreeSites ring h _ p e hne hfree hph (fun _ _ _ => rfl) (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun _ => by rw [hx]; exact ⟨hxk, fun h0 => by simp [BlockA.wordPut] at h0⟩) (fun hkj => by rw [hy]; exact ⟨(hfree hph _ hkj).1, fun _ => rfl⟩)
  | backwardsInit =>
      dsimp only
      obtain ⟨-, -, -, hxk, hx, hy⟩ := bankRepairDigitWOutBone _ _
        ((bankRepairDigitWorkerCaseRows _ _).2.1 hcase)
      repeat' split
      all_goals first
        | exact bankRepairDigitWordFreeClear h _ _
        | exact bankRepairDigitWordFreeSites ring h _ p e hne hfree hph (fun _ _ _ => rfl) (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun _ => by rw [hx]; exact ⟨hxk, fun h0 => by simp [BlockA.wordPut] at h0⟩) (fun hkj => by rw [hy]; exact ⟨(hfree hph _ hkj).1, fun _ => rfl⟩)
  | sumMove =>
      dsimp only
      obtain ⟨hxk, -, -, hyk, hx, hy⟩ := bankRepairDigitWOutSzero _ _
        ((bankRepairDigitWorkerCaseRows _ _).2.2 hcase)
      repeat' split
      all_goals first
        | exact bankRepairDigitWordFreeClear h _ _
        | exact bankRepairDigitWordFreeSites ring h _ p e hne hfree hph (fun _ _ _ => rfl) (fun i h1 h2 => by simp only [BlockA.wordPut, if_neg h1, if_neg h2]) (fun _ => by rw [hx]; exact ⟨hxk, fun _ => rfl⟩) (fun _ => by rw [hy]; exact ⟨hyk, fun h0 => by simp [BlockA.wordPut] at h0⟩)
  | terminal =>
      dsimp only
      split
      · exact bankRepairDigitWordFreeOfPhase _ _ (by intro h0; cases h0)
      · exact bankRepairDigitWordFreeClear h _ _

theorem bankRepairDigitWordFreeValidate {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool) (hn : 3 ≤ n)
    (hph : h.phase = .validate) :
    BankRepairDigitWordFree (BlockA.wordValidateNext ring h p e request)
      (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  unfold BlockA.wordValidateNext
  dsimp only
  split
  all_goals (repeat' split)
  all_goals first
    | exact bankRepairDigitWordFreeClear h _ _
    | exact bankRepairDigitWordFreeOfPhase _ _ (fun h0 => by have h1 : h.phase = .worker := h0; rw [hph] at h1; cases h1)
    | skip
  rename_i hg
  obtain ⟨he, -, -, -, -, hof, -, -, -, hy⟩ := hg
  obtain ⟨hsx, hsy⟩ := bankRepairDigitPhiWSites ring p e hne
  intro _ i hki
  by_cases hie : i = e
  · exfalso
    rw [hie, he] at hki
    simp [BlockA.wordWorkerLaunch] at hki
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij, hsy]
      simp only [freeSI, Bool.and_eq_true, beq_iff_eq] at hy
      exact ⟨hy.1, fun _ => hy.2⟩
    · rw [cwPhiWFrame ring p e i hie hij]
      have h0 := hof i hie hij
      simp only [freeSI, Bool.and_eq_true, beq_iff_eq] at h0
      exact ⟨h0.1, fun _ => h0.2⟩

/-- One W monitor step keeps the uncoloured-site invariant. -/
theorem bankRepairDigitWordFreeT {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (hn : 3 ≤ n)
    (hfree : BankRepairDigitWordFree h p) :
    BankRepairDigitWordFree (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  unfold BlockA.wordT
  split
  · rename_i hd
    exact bankRepairDigitWordFreeOfPhase _ _ (by rw [hd]; intro h0; cases h0)
  · dsimp only
    split
    · exact bankRepairDigitWordFreeOfPhase _ _ (by intro h0; cases h0)
    · split
      · exact bankRepairDigitWordFreeClear h _ _
      · rename_i hph
        exact bankRepairDigitWordFreeValidate ring h p e _ hn hph
      · rename_i hph
        exact bankRepairDigitWordFreeWorker ring h p e _ hn hfree hph
      · rename_i hph
        exact bankRepairDigitWordFreeOfPhase _ _ (by rw [hph]; intro h0; cases h0)

/-- The only entry into DONE is a valid worker-phase A0 at the ready site. -/
theorem bankRepairDigitWordDoneEnter {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c) (e : Fin n) (hd : h.phase ≠ .done)
    (hdone : (BlockA.wordT ring h p e p').phase = .done) :
    h.phase = .worker ∧
      BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .terminal ∧
      h.workerKind e = .ready e ∧
      BlockA.wordAllPublished ring (BlockA.wordT ring h p e p') := by
  revert hdone
  unfold BlockA.wordT
  rw [if_neg hd]
  dsimp only
  split
  · intro h0
    cases h0
  · split
    · intro h0
      cases h0
    · rename_i hph
      unfold BlockA.wordValidateNext
      dsimp only
      split
      all_goals (repeat' split)
      all_goals first
        | (intro h0; cases h0)
        | (intro h0; have h1 : h.phase = .done := h0; rw [hph] at h1; cases h1)
    · rename_i hph
      unfold BlockA.wordWorkerNext
      dsimp only
      cases hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e))
      all_goals dsimp only
      all_goals (repeat' split)
      all_goals first
        | (intro h0; cases h0)
        | (intro h0; have h1 : h.phase = .done := h0; rw [hph] at h1; cases h1)
        | skip
      rename_i hC
      exact ⟨hph, rfl, hC.1, hC.2.2.2.2.2⟩
    · rename_i hph
      exact absurd hph hd

/-- At the A0 that enters DONE every physical record is free. -/
theorem bankRepairDigitWordDoneEntryPhys {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (hn : 3 ≤ n)
    (htok : BankRepairDigitWordTok h) (hfree : BankRepairDigitWordFree h p)
    (hph : h.phase = .worker) (hke : h.workerKind e = .ready e)
    (hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) = .terminal) :
    BankRepairDigitWordPhys ring root (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  obtain ⟨hko, hco⟩ := bankRepairDigitWordTokReady h htok e hke
  obtain ⟨hyk, hyc, hx, hy⟩ := bankRepairDigitWOutAzero _ _
    ((bankRepairDigitWorkerCasePublish _ _).2.2 hcase)
  obtain ⟨hsx, hsy⟩ := bankRepairDigitPhiWSites ring p e hne
  refine bankRepairDigitWordPhysAllFree ring root _ (fun i => ?_)
  by_cases hie : i = e
  · rw [hie, hsx, hx]
    exact ⟨rfl, rfl⟩
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij, hsy, hy]
      exact ⟨hyk, hyc⟩
    · rw [cwPhiWFrame ring p e i hie hij]
      have h0 := hfree hph i (hko i hie)
      exact ⟨h0.1, h0.2 (hco i)⟩

/-- The DONE clause of the run bundle survives one W step: entered only by
A0 (all records free, all receipts issued), then kept by the frozen
monitor since no edge changes the visible word. -/
theorem bankRepairDigitWordDoneClauseT {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n) (ht : c.t + 1 < n) (ht2 : 2 ≤ c.t)
    (hpub : BankRepairDigitWordPublished ring h p)
    (htok : BankRepairDigitWordTok h) (hfree : BankRepairDigitWordFree h p)
    (hdc : h.phase = .done →
      BlockA.wordAllPublished ring h ∧ BankRepairDigitWordPhys ring h.root p) :
    (BlockA.wordT ring h p e (phiW ring p e)).phase = .done →
      BlockA.wordAllPublished ring (BlockA.wordT ring h p e (phiW ring p e)) ∧
      BankRepairDigitWordPhys ring
        (BlockA.wordT ring h p e (phiW ring p e)).root (phiW ring p e) := by
  intro hd'
  by_cases hd : h.phase = .done
  · have hT : BlockA.wordT ring h p e (phiW ring p e) = h := by
      unfold BlockA.wordT
      rw [if_pos hd]
    rw [hT]
    obtain ⟨hall, hphys⟩ := hdc hd
    have hvis := bankRepairDigitWordDoneVisible ring h p e hn ht ht2 hpub hall
      hphys
    exact ⟨hall, bankRepairDigitWordPhysStep ring h.root p e hn ht hpub.rootFixed
      hphys (fun i => congrArg Prod.fst (hvis i))⟩
  · obtain ⟨hph, hcase, hke, hall⟩ :=
      bankRepairDigitWordDoneEnter ring h p _ e hd hd'
    exact ⟨hall, bankRepairDigitWordDoneEntryPhys ring _ h p e hn htok hfree hph
      hke hcase⟩

/-! T13 item 2: P3 and S1 preserve `BankRepairDigitWordPublished`. -/

theorem bankRepairDigitPrefixCongrUpTo {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p p' : Fin n → ProjW c) :
    ∀ L, (∀ m, 1 ≤ m → m ≤ L → cwBit ring root p' m = cwBit ring root p m) →
      cwPrefixOr ring root p' L = cwPrefixOr ring root p L ∧
      cwPrefixAnd ring root p' L = cwPrefixAnd ring root p L := by
  intro L
  induction L with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ L ih =>
      intro hb
      obtain ⟨h1, h2⟩ := ih (fun m hm1 hm2 => hb m hm1 (by omega))
      rw [(bankRepairDigitPrefixFoldStep ring root p' L).1,
        (bankRepairDigitPrefixFoldStep ring root p L).1,
        (bankRepairDigitPrefixFoldStep ring root p' L).2,
        (bankRepairDigitPrefixFoldStep ring root p L).2,
        h1, h2, hb (L + 1) (by omega) (Nat.le_refl _)]
      exact ⟨rfl, rfl⟩

theorem bankRepairDigitSumCongrUpTo {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p p' : Fin n → ProjW c) (T : Nat) :
    ∀ L, (∀ j, j < L →
        cwSourceBit ring root p' T j = cwSourceBit ring root p T j) →
      cwSumOr ring root p' T L = cwSumOr ring root p T L ∧
      cwSumParity ring root p' T L = cwSumParity ring root p T L ∧
      cwSumTrailing ring root p' T L = cwSumTrailing ring root p T L := by
  intro L
  induction L with
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ L ih =>
      intro hb
      obtain ⟨h1, h2, h3⟩ := ih (fun j hj => hb j (by omega))
      obtain ⟨a1, a2, a3⟩ := bankRepairDigitSumFoldStep ring root p' T L
      obtain ⟨b1, b2, b3⟩ := bankRepairDigitSumFoldStep ring root p T L
      rw [a1, a2, a3, b1, b2, b3, h1, h2, h3, hb L (Nat.lt_succ_self L)]
      exact ⟨rfl, rfl, rfl⟩

theorem bankRepairDigitPrefixOrAnd {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c) (m : Nat)
    (h : cwPrefixOr ring root p (m + 1) = false) :
    cwPrefixAnd ring root p (m + 1) = false := by
  rw [(bankRepairDigitPrefixFoldStep ring root p m).1] at h
  rw [(bankRepairDigitPrefixFoldStep ring root p m).2]
  have hb : cwBit ring root p (m + 1) = false := by
    cases hc : cwBit ring root p (m + 1)
    · rfl
    · rw [hc, Bool.or_true] at h
      cases h
  rw [hb, Bool.and_false]

theorem bankRepairDigitPhiWAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    ((phiW ring p e) e).u = (workerW (p e) (p (ring.rightNeighbor e))).uX ∧
    ((phiW ring p e) e).beta = (workerW (p e) (p (ring.rightNeighbor e))).betaX ∧
    ((phiW ring p e) (ring.rightNeighbor e)).u =
      (workerW (p e) (p (ring.rightNeighbor e))).uY ∧
    ((phiW ring p e) (ring.rightNeighbor e)).beta =
      (workerW (p e) (p (ring.rightNeighbor e))).betaY := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [phiW, projectedEdge, if_pos rfl] <;> rfl
  · simp only [phiW, projectedEdge, if_pos rfl] <;> rfl
  · simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte] <;> rfl
  · simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte] <;> rfl

theorem bankRepairDigitVisibleOnlyE {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n)
    (hy : (workerW (p e) (p (ring.rightNeighbor e))).uY =
        (p (ring.rightNeighbor e)).u ∧
      (workerW (p e) (p (ring.rightNeighbor e))).betaY =
        (p (ring.rightNeighbor e)).beta) :
    ∀ s, s ≠ e → AcceptedReceipts.wordVisible (phiW ring p e) s =
      AcceptedReceipts.wordVisible p s := by
  intro s hs
  apply Classical.byContradiction
  intro h0
  rcases bankRepairDigitVisibleChangeSites ring p e s h0 with ⟨hse, -⟩ | ⟨-, hy'⟩
  · exact hs hse
  · exact hy' hy

theorem bankRepairDigitVisibleOnlyJ {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n)
    (hx : (workerW (p e) (p (ring.rightNeighbor e))).uX = (p e).u ∧
      (workerW (p e) (p (ring.rightNeighbor e))).betaX = (p e).beta) :
    ∀ s, s ≠ ring.rightNeighbor e →
      AcceptedReceipts.wordVisible (phiW ring p e) s =
        AcceptedReceipts.wordVisible p s := by
  intro s hs
  apply Classical.byContradiction
  intro h0
  rcases bankRepairDigitVisibleChangeSites ring p e s h0 with ⟨-, hx'⟩ | ⟨hsj, -⟩
  · exact hx' hx
  · exact hs hsj

/-- T13 item 2: a monitored P3 (prefix tag at offset t) preserves the
invariant. Its only visible change is at e itself (offset t), where it
issues the fresh `.prefixEnd`; no window receipt exists under a prefix
colour, and the zero markers below t are untouched. -/
theorem bankRepairDigitWordPublishedPthree {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (hn : 3 ≤ n) (ht : c.t + 1 < n)
    (ht2 : 2 ≤ c.t)
    (hpub : BankRepairDigitWordPublished ring h p)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hb : BankRepairDigitWordBelow ring h)
    {idx : Fin (c.t + 1)} {z a : Bool}
    (hk : h.workerKind e = .prefix idx z a) (hidx : idx.val = c.t)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "P3")
    (hux : (workerW (p e) (p (ring.rightNeighbor e))).uX =
      (if z = false then true else (p e).u))
    (hbx : (workerW (p e) (p (ring.rightNeighbor e))).betaX = a)
    (hroot : h'.root = h.root)
    (hwp : h'.publications = BlockA.wordPut h.publications e .prefixEnd) :
    BankRepairDigitWordPublished ring h' (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  have hnw := bankRepairDigitWordBelowPrefix ring h hb e hk
  obtain ⟨-, hpos, hz, ha⟩ := (hacc e).1 idx z a hk
  rw [hidx] at hpos hz ha
  obtain ⟨hue, hbe, -, -⟩ := bankRepairDigitPhiWAt ring p e hne
  have hvis := bankRepairDigitVisibleOnlyE ring p e
    (bankRepairDigitSiStepRowPthreeY c _ _ _ _ hrow)
  have hsite : ∀ m, m < n → m ≠ c.t → PPL.shiftRight ring h.root m ≠ e := by
    intro m hm hmt h0
    rw [hpos] at h0
    exact hmt (bankRepairDigitShiftInjective ring h.root m c.t hm (by omega) h0)
  have hbit : ∀ m, m < n → m ≠ c.t →
      cwBit ring h.root (phiW ring p e) m = cwBit ring h.root p m :=
    fun m hm hmt => congrArg Prod.fst (hvis _ (hsite m hm hmt))
  have hmark : ∀ m, m < n → m ≠ c.t →
      cwMarker ring h.root (phiW ring p e) m = cwMarker ring h.root p m :=
    fun m hm hmt => congrArg Prod.snd (hvis _ (hsite m hm hmt))
  have hpk : ∀ m, m < n → m ≠ c.t →
      h'.publications (PPL.shiftRight ring h.root m) =
        h.publications (PPL.shiftRight ring h.root m) := by
    intro m hm hmt
    rw [hwp, bankRepairDigitPutOther _ _ _ _ (hsite m hm hmt)]
  have hbitt : cwBit ring h.root (phiW ring p e) c.t =
      (if z = false then true else (p e).u) := by
    unfold cwBit
    rw [← hpos, hue, hux]
  have hmarkt : cwMarker ring h.root (phiW ring p e) c.t = a := by
    unfold cwMarker
    rw [← hpos, hbe, hbx]
  have hbit0 : cwBit ring h.root p c.t = (p e).u := by
    unfold cwBit
    rw [← hpos]
  have hcong := bankRepairDigitPrefixCongrUpTo ring h.root p (phiW ring p e)
    (c.t - 1) (fun m h1 h2 => hbit m (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hroot]
    exact bankRepairDigitWFixedRootPhiW hn ring h.root p e hpub.rootFixed
  · intro k hk0 hkt hp'
    rw [hroot] at hp' ⊢
    rw [hpk k.val k.isLt (by omega)] at hp'
    rw [hmark k.val k.isLt (by omega)]
    exact hpub.prefixZeros k hk0 hkt hp'
  · intro k hkt hp'
    rw [hroot] at hp' ⊢
    rw [hkt]
    have htr := bankRepairDigitTrailingFirst ring h.root (phiW ring p e) (c.t - 1)
    have hor := (bankRepairDigitPrefixFoldStep ring h.root (phiW ring p e)
      (c.t - 1)).1
    have hor0 := (bankRepairDigitPrefixFoldStep ring h.root p (c.t - 1)).1
    have hand0 := (bankRepairDigitPrefixFoldStep ring h.root p (c.t - 1)).2
    rw [Nat.sub_add_cancel (by omega : 1 ≤ c.t)] at htr hor hor0 hand0
    have hOA : cwPrefixOr ring h.root p (c.t - 1) = false →
        cwPrefixAnd ring h.root p (c.t - 1) = false := by
      have h5 := bankRepairDigitPrefixOrAnd ring h.root p (c.t - 2)
      rw [show c.t - 2 + 1 = c.t - 1 by omega] at h5
      exact h5
    rw [hor, htr, hmarkt, hbitt, hcong.1, hcong.2, hz, ha, hor0, hand0, hbit0]
    have key : ∀ O A B : Bool, (O = false → A = false) →
        (O || (if (O || B) = false then true else B)) = true ∧
          (A && B) = (A && (if (O || B) = false then true else B)) := by
      intro O A B
      cases O <;> cases A <;> cases B <;> simp
    exact key _ _ _ hOA
  · intro k hk hp'
    rw [hroot] at hp'
    rw [hpk k.val k.isLt (by omega)] at hp'
    exact absurd (Or.inr hp') (hnw _)

/-- T13 item 2: a monitored S1 (sum cursor of the target j at offset T)
preserves the invariant against the repaired `laterWindows`. Its only
visible change is at j, where it issues the fresh `.recurrence` with the
value S1 writes (window nonzero: parity; window zero: forced `true`);
every older receipt sits strictly below T, so its window and marker are
untouched. -/
theorem bankRepairDigitWordPublishedSone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h h' : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (hn : 3 ≤ n)
    (hpub : BankRepairDigitWordPublished ring h p)
    (hacc : BankRepairDigitWordAcc ring h p)
    (hb : BankRepairDigitWordBelow ring h)
    (hreach : BankRepairDigitWordReach ring h p)
    {target : Fin n} {idx : Fin (c.t + 1)} {z parity trailing : Bool}
    (hce : h.workerCursor e = .sum target idx z parity trailing)
    (htj : target = ring.rightNeighbor e)
    (hkj : h.workerKind (ring.rightNeighbor e) =
      .target (ring.rightNeighbor e) true)
    (hidx : idx.val + 1 = c.t)
    (hrow : (workerW (p e) (p (ring.rightNeighbor e))).row = "S1")
    (huy : (workerW (p e) (p (ring.rightNeighbor e))).uY =
      (if (BlockA.wordFold idx z parity trailing (p e).u).1 then
        (BlockA.wordFold idx z parity trailing (p e).u).2.1 else true))
    (hby : (workerW (p e) (p (ring.rightNeighbor e))).betaY =
      ((BlockA.wordFold idx z parity trailing (p e).u).2.2 &&
        (if (BlockA.wordFold idx z parity trailing (p e).u).1 then
          (BlockA.wordFold idx z parity trailing (p e).u).2.1 else true)))
    (hroot : h'.root = h.root)
    (hwp : h'.publications =
      BlockA.wordPut h.publications (ring.rightNeighbor e) .recurrence) :
    BankRepairDigitWordPublished ring h' (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega) e
  obtain ⟨T, hT1, hT2, hjT⟩ : ∃ k, c.t < k ∧ k < n ∧
      ring.rightNeighbor e = PPL.shiftRight ring h.root k := by
    rcases hreach with ⟨_, h2⟩ | ⟨_, _, hkd⟩
    · rw [h2] at hkj
      cases hkj
    · exact hkd _ _ (Or.inl ⟨true, hkj⟩)
  have hoT : PPL.cyclicOffset ring h.root target = T := by
    rw [htj, hjT]
    exact bankRepairDigitOffsetShift ring h.root T hT2
  obtain ⟨-, -, -, -, -, -, hpos, hz, hp, ha⟩ :=
    (hacc e).2.2 target idx z parity trailing hce
  rw [hoT] at hpos hz hp ha
  obtain ⟨-, -, huj, hbj⟩ := bankRepairDigitPhiWAt ring p e hne
  have hvis := bankRepairDigitVisibleOnlyJ ring p e
    (bankRepairDigitSiStepRowSoneX c _ _ _ _ hrow)
  have hsite : ∀ m, m < n → m ≠ T →
      PPL.shiftRight ring h.root m ≠ ring.rightNeighbor e := by
    intro m hm hmT h0
    rw [hjT] at h0
    exact hmT (bankRepairDigitShiftInjective ring h.root m T hm hT2 h0)
  have hbit : ∀ m, m < n → m ≠ T →
      cwBit ring h.root (phiW ring p e) m = cwBit ring h.root p m :=
    fun m hm hmT => congrArg Prod.fst (hvis _ (hsite m hm hmT))
  have hmark : ∀ m, m < n → m ≠ T →
      cwMarker ring h.root (phiW ring p e) m = cwMarker ring h.root p m :=
    fun m hm hmT => congrArg Prod.snd (hvis _ (hsite m hm hmT))
  have hpk : ∀ m, m < n → m ≠ T →
      h'.publications (PPL.shiftRight ring h.root m) =
        h.publications (PPL.shiftRight ring h.root m) := by
    intro m hm hmT
    rw [hwp, bankRepairDigitPutOther _ _ _ _ (hsite m hm hmT)]
  have hwinlt : ∀ m, m < n →
      BankRepairDigitWordWin (h.publications (PPL.shiftRight ring h.root m)) →
      m < T := by
    intro m hm hw
    have h0 := (hb _ hw).2.2.2.1 _ _ true hkj
    rw [bankRepairDigitOffsetShift ring h.root m hm, hjT,
      bankRepairDigitOffsetShift ring h.root T hT2] at h0
    exact h0
  have hsum : ∀ k, c.t < k → k ≤ T →
      cwSumOr ring h.root (phiW ring p e) k c.t = cwSumOr ring h.root p k c.t ∧
      cwSumParity ring h.root (phiW ring p e) k c.t =
        cwSumParity ring h.root p k c.t ∧
      cwSumTrailing ring h.root (phiW ring p e) k c.t =
        cwSumTrailing ring h.root p k c.t := by
    intro k hk1 hk2
    refine bankRepairDigitSumCongrUpTo ring h.root p (phiW ring p e) k c.t
      (fun j hj => ?_)
    unfold cwSourceBit
    exact hbit _ (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hroot]
    exact bankRepairDigitWFixedRootPhiW hn ring h.root p e hpub.rootFixed
  · intro k hk0 hkt hp'
    rw [hroot] at hp' ⊢
    rw [hpk k.val k.isLt (by omega)] at hp'
    rw [hmark k.val k.isLt (by omega)]
    exact hpub.prefixZeros k hk0 hkt hp'
  · intro k hkt hp'
    rw [hroot] at hp' ⊢
    rw [hpk k.val k.isLt (by omega)] at hp'
    have hold := hpub.firstWindow k hkt hp'
    rw [hkt] at hold ⊢
    have hcp := bankRepairDigitPrefixCongrUpTo ring h.root p (phiW ring p e) c.t
      (fun m h1 h2 => hbit m (by omega) (by omega))
    have hcs := bankRepairDigitSumCongrUpTo ring h.root p (phiW ring p e) c.t c.t
      (fun j hj => by unfold cwSourceBit; exact hbit _ (by omega) (by omega))
    rw [hcp.1, hmark c.t (by omega) (by omega), hcs.2.2,
      hbit c.t (by omega) (by omega)]
    exact hold
  · intro k hk hp'
    rw [hroot] at hp' ⊢
    by_cases hkT : k.val = T
    · rw [hkT]
      obtain ⟨hc1, hc2, hc3⟩ := hsum T hT1 (Nat.le_refl _)
      have hsrc : cwSourceBit ring h.root p T idx.val = (p e).u := by
        unfold cwSourceBit cwBit
        rw [← hpos]
      obtain ⟨s1, s2, s3⟩ := bankRepairDigitSumFoldStep ring h.root p T idx.val
      rw [hidx, hsrc, ← hz] at s1
      rw [hidx, hsrc, ← hp] at s2
      rw [hidx, hsrc] at s3
      have hA : (if idx.val = 0 then true else (trailing && (p e).u)) =
          cwSumTrailing ring h.root p T c.t := by
        rw [s3]
        by_cases hJ0 : idx.val = 0
        · simp [hJ0, cwSumTrailing]
        · simp [hJ0, ha]
      have hbT : cwBit ring h.root (phiW ring p e) T =
          (workerW (p e) (p (ring.rightNeighbor e))).uY := by
        unfold cwBit
        rw [← hjT, huj]
      have hmT : cwMarker ring h.root (phiW ring p e) T =
          (workerW (p e) (p (ring.rightNeighbor e))).betaY := by
        unfold cwMarker
        rw [← hjT, hbj]
      have huy' : (workerW (p e) (p (ring.rightNeighbor e))).uY =
          (if (z || (p e).u) = true then
            Bool.xor parity (c.taps idx.val && (p e).u) else true) := huy
      have hby' : (workerW (p e) (p (ring.rightNeighbor e))).betaY =
          ((if idx.val = 0 then true else (trailing && (p e).u)) &&
            (if (z || (p e).u) = true then
              Bool.xor parity (c.taps idx.val && (p e).u) else true)) := hby
      rw [← s1, ← s2] at huy'
      rw [← s1, ← s2, hA] at hby'
      rw [hc1, hc2, hc3, hbT, hmT, huy', hby']
      cases cwSumOr ring h.root p T c.t <;> simp
    · rw [hpk k.val k.isLt hkT] at hp'
      have hkl := hwinlt k.val k.isLt (Or.inr hp')
      have hold := hpub.laterWindows k hk hp'
      obtain ⟨hc1, hc2, hc3⟩ := hsum k.val hk (by omega)
      rw [hc1, hc2, hc3, hbit k.val k.isLt hkT, hmark k.val k.isLt hkT]
      exact hold

/-! T13 item 3: the invariant along every W run. -/

/-- The validate phase keeps or drops each receipt and keeps the root. -/
theorem bankRepairDigitWordValidateKeep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool) :
    (BlockA.wordValidateNext ring h p e request).root = h.root ∧
      ∀ i, (BlockA.wordValidateNext ring h p e request).publications i =
          h.publications i ∨
        (BlockA.wordValidateNext ring h p e request).publications i = .absent := by
  unfold BlockA.wordValidateNext
  dsimp only
  split
  all_goals (repeat' split)
  all_goals first
    | exact ⟨rfl, fun _ => Or.inr rfl⟩
    | exact ⟨rfl, fun _ => Or.inl rfl⟩

/-- Every worker-phase step other than P1 preserves the invariant: P3 and
S1 by item 2, cancellations clear it, every other kept row leaves the
visible word and the receipts alone. -/
theorem bankRepairDigitWordPublishedWorker {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n) (request : Bool)
    (hn : 3 ≤ n) (ht : c.t + 1 < n) (ht2 : 2 ≤ c.t)
    (hpub : BankRepairDigitWordPublished ring h p)
    (hrun : BankRepairDigitWordAccRun ring h p)
    (hb : BankRepairDigitWordBelow ring h)
    (hreach : BankRepairDigitWordReach ring h p)
    (hP1 : (workerW (p e) (p (ring.rightNeighbor e))).row ≠ "P1") :
    BankRepairDigitWordPublished ring
      (BlockA.wordWorkerNext ring h p e request) (phiW ring p e) := by
  have hfix' := bankRepairDigitWFixedRootPhiW hn ring h.root p e hpub.rootFixed
  have hacc := hrun.2.2.2
  unfold BlockA.wordWorkerNext
  dsimp only
  cases hcase : BlockA.workerCase (p e) (p (ring.rightNeighbor e)) with
  | init => exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
  | prefixExit => exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
  | prefixTerminal => exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
  | prefixMove => exact absurd ((bankRepairDigitWorkerCaseMore _ _).1 hcase) hP1
  | erase =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseMore _ _).2.1 hcase
      split
      · exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
      · exact bankRepairDigitWordPublishedQuietRow ring h _ p e hpub
          (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide)
          (by rw [hrow]; decide) rfl hfix' (fun _ => Or.inl rfl)
  | frame =>
      obtain ⟨-, -, -, hQ1, hQ2, hQ3, -, -, -, hQ4, -, -⟩ :=
        (bankRepairDigitWorkerCaseMore _ _).2.2 hcase
      exact bankRepairDigitWordPublishedQuietRow ring h _ p e hpub hQ1 hQ2 hQ3 hQ4
        rfl hfix' (fun _ => Or.inl rfl)
  | backwardsMove =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseRows _ _).1 hcase
      repeat' split
      all_goals first
        | exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
        | exact bankRepairDigitWordPublishedQuietRow ring h _ p e hpub (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) rfl hfix' (fun _ => Or.inl rfl)
  | backwardsInit =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseRows _ _).2.1 hcase
      repeat' split
      all_goals first
        | exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
        | exact bankRepairDigitWordPublishedQuietRow ring h _ p e hpub (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) rfl hfix' (fun _ => Or.inl rfl)
  | sumMove =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCaseRows _ _).2.2 hcase
      repeat' split
      all_goals first
        | exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
        | exact bankRepairDigitWordPublishedQuietRow ring h _ p e hpub (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) rfl hfix' (fun _ => Or.inl rfl)
  | advance =>
      dsimp only
      have hrow := bankRepairDigitWorkerCaseAdvance _ _ hcase
      repeat' split
      all_goals first
        | exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
        | exact bankRepairDigitWordPublishedQuietRow ring h _ p e hpub (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) rfl hfix' (fun _ => Or.inl rfl)
  | terminal =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCasePublish _ _).2.2 hcase
      repeat' split
      all_goals first
        | exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
        | exact bankRepairDigitWordPublishedQuietRow ring h _ p e hpub (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) (by rw [hrow]; decide) rfl hfix' (fun _ => Or.inl rfl)
  | prefixPublish =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCasePublish _ _).1 hcase
      split
      · rename_i idx z a hk
        repeat' split
        all_goals first
          | exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
          | skip
        all_goals rename_i hz0 hC
        all_goals obtain ⟨hidx, -, -, -, -, -, -, -, -, -, hux, hbx, -⟩ := hC
        all_goals exact bankRepairDigitWordPublishedPthree ring h _ p e hn ht ht2 hpub hacc hb hk hidx hrow (by first | (rw [if_pos hz0]; exact hux) | (rw [if_neg hz0]; exact hux)) hbx rfl rfl
      all_goals exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
  | sumPublish =>
      dsimp only
      have hrow := (bankRepairDigitWorkerCasePublish _ _).2.1 hcase
      split
      · rename_i target idx z parity trailing hce
        repeat' split
        all_goals first
          | exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
          | skip
        all_goals rename_i hf0 hC
        all_goals obtain ⟨htj, hkj, -, -, -, -, -, -, -, hidx, -, -, huy, hby, -⟩ := hC
        all_goals exact bankRepairDigitWordPublishedSone ring h _ p e hn hpub hacc hb hreach hce htj hkj hidx hrow (by first | (rw [if_pos hf0]; exact huy) | (rw [if_neg hf0]; exact huy)) (by first | (rw [if_pos hf0]; exact hby) | (rw [if_neg hf0]; exact hby)) rfl rfl
      all_goals exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'

/-- One W monitor step preserves the invariant (P1 by T9, the done phase
by item 1, everything else above). -/
theorem bankRepairDigitWordPublishedT {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n) (ht : c.t + 1 < n) (ht2 : 2 ≤ c.t)
    (hpub : BankRepairDigitWordPublished ring h p)
    (hrun : BankRepairDigitWordAccRun ring h p)
    (hb : BankRepairDigitWordBelow ring h)
    (hreach : BankRepairDigitWordReach ring h p)
    (hidle : (h.phase = .awaitRequest ∨ h.phase = .validate) →
      ∀ i, h.publications i = .absent)
    (hdc : h.phase = .done →
      BlockA.wordAllPublished ring h ∧ BankRepairDigitWordPhys ring h.root p) :
    BankRepairDigitWordPublished ring
      (BlockA.wordT ring h p e (phiW ring p e)) (phiW ring p e) := by
  have hfix' := bankRepairDigitWFixedRootPhiW hn ring h.root p e hpub.rootFixed
  by_cases hP1 : (workerW (p e) (p (ring.rightNeighbor e))).row = "P1"
  · exact bankRepairDigitWordPublishedPone hn ring h p e hpub hP1 hreach
  unfold BlockA.wordT
  split
  · rename_i hd
    obtain ⟨hall, hphys⟩ := hdc hd
    exact bankRepairDigitWordPublishedFrame ring h h p (phiW ring p e) hpub rfl
      hfix' (bankRepairDigitWordDoneVisible ring h p e hn ht ht2 hpub hall hphys)
      (fun _ => Or.inl rfl)
  · dsimp only
    split
    · exact bankRepairDigitWordPublishedOfHardLaunch ring h e _ _ hfix'
    · split
      · exact bankRepairDigitWordPublishedOfClear ring h _ _ hfix'
      · rename_i hph
        have hr := (bankRepairDigitWordValidateKeep ring h p e
          (BlockA.wordRequestNext ring h p e)).1
        refine bankRepairDigitWordPublishedOfAbsent ring _ _
          (by rw [hr]; exact hfix') (fun i => ?_)
        rcases (bankRepairDigitWordValidateKeep ring h p e
          (BlockA.wordRequestNext ring h p e)).2 i with h0 | h0
        · rw [h0]
          exact hidle (Or.inr hph) i
        · exact h0
      · rename_i hph
        exact bankRepairDigitWordPublishedWorker ring h p e _ hn ht ht2 hpub hrun
          hb hreach hP1
      · rename_i hd
        obtain ⟨hall, hphys⟩ := hdc hd
        exact bankRepairDigitWordPublishedFrame ring h h p (phiW ring p e) hpub rfl
          hfix' (bankRepairDigitWordDoneVisible ring h p e hn ht ht2 hpub hall
            hphys) (fun _ => Or.inl rfl)

/-- Outside the worker and done phases no receipt is held. -/
theorem bankRepairDigitWordIdleAbsentT {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p p' : Fin n → ProjW c) (e : Fin n)
    (hidle : (h.phase = .awaitRequest ∨ h.phase = .validate) →
      ∀ i, h.publications i = .absent) :
    ((BlockA.wordT ring h p e p').phase = .awaitRequest ∨
        (BlockA.wordT ring h p e p').phase = .validate) →
      ∀ i, (BlockA.wordT ring h p e p').publications i = .absent := by
  unfold BlockA.wordT
  split
  · rename_i hd
    intro h0
    rcases h0 with h0 | h0
    · rw [hd] at h0
      cases h0
    · rw [hd] at h0
      cases h0
  · dsimp only
    split
    · intro _ _
      rfl
    · split
      · intro _ _
        rfl
      · rename_i hph
        intro _ i
        rcases (bankRepairDigitWordValidateKeep ring h p e _).2 i with h0 | h0
        · rw [h0]
          exact hidle (Or.inr hph) i
        · exact h0
      · rename_i hph
        unfold BlockA.wordWorkerNext
        dsimp only
        split
        all_goals (repeat' split)
        all_goals first
          | (intro _ _; rfl)
          | (intro h0; rcases h0 with h0 | h0 <;> first | cases h0 | (have h1 : h.phase = .awaitRequest := h0; rw [hph] at h1; cases h1) | (have h1 : h.phase = .validate := h0; rw [hph] at h1; cases h1))
      · rename_i hd
        intro h0
        rcases h0 with h0 | h0
        · rw [hd] at h0
          cases h0
        · rw [hd] at h0
          cases h0

/-- T13 item 3: the run bundle. The publication invariant, the
uncoloured-site invariant of the worker phase, no receipt outside the
worker and done phases, and in the done phase the full receipt census
with every physical record consistent. -/
def BankRepairDigitWordPubRun {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  BankRepairDigitWordPublished ring h p ∧
  BankRepairDigitWordFree h p ∧
  ((h.phase = .awaitRequest ∨ h.phase = .validate) →
    ∀ i, h.publications i = .absent) ∧
  (h.phase = .done →
    BlockA.wordAllPublished ring h ∧ BankRepairDigitWordPhys ring h.root p)

theorem bankRepairDigitWordPubRunStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n) (ht : c.t + 1 < n) (ht2 : 2 ≤ c.t)
    (hpr : BankRepairDigitWordPubRun ring h p)
    (hrun : BankRepairDigitWordAccRun ring h p)
    (hb : BankRepairDigitWordBelow ring h)
    (hreach : BankRepairDigitWordReach ring h p) :
    BankRepairDigitWordPubRun ring
      (BlockA.wordT ring h p e (phiW ring p e)) (phiW ring p e) := by
  obtain ⟨hpub, hfree, hidle, hdc⟩ := hpr
  exact ⟨bankRepairDigitWordPublishedT ring h p e hn ht ht2 hpub hrun hb hreach
      hidle hdc,
    bankRepairDigitWordFreeT ring h p e hn hfree,
    bankRepairDigitWordIdleAbsentT ring h p _ e hidle,
    bankRepairDigitWordDoneClauseT ring h p e hn ht ht2 hpub hrun.1 hfree hdc⟩

theorem bankRepairDigitWordPubRunAux {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (origin : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (root : Fin n) (h₀ : BlockA.WordControl n c)
    (hγ₀ : γ₀ = .live origin h₀) (hroot₀ : h₀.root = root)
    (hfix₀ : WFixedRoot ring root origin)
    (hph₀ : h₀.phase = .awaitRequest)
    (hcl : ∀ i, h₀.publications i = .absent ∧ h₀.workerKind i = .empty)
    (hcur : ∀ i, h₀.workerCursor i = .empty)
    (hn : 3 ≤ n) (ht : c.t + 1 < n) (ht2 : 2 ≤ c.t)
    {w : List (Fin n)} {p : Fin n → ProjW c}
    {γ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c)}
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p γ) :
    ∀ shadow h, γ = .live shadow h → BankRepairDigitWordPubRun ring h p := by
  induction hrun with
  | empty =>
      intro shadow h hγ
      rw [hγ₀] at hγ
      injection hγ with h1 h2
      subst h1 h2
      refine ⟨bankRepairDigitWordPublishedOfAbsent ring _ _
          (by rw [hroot₀]; exact hfix₀) (fun i => (hcl i).1),
        bankRepairDigitWordFreeOfPhase _ _ (by rw [hph₀]; intro h0; cases h0),
        fun _ i => (hcl i).1, fun h0 => ?_⟩
      rw [hph₀] at h0
      cases h0
  | @next w p γ hr e ih =>
      intro shadow h hγ
      cases γ with
      | failed =>
          rw [BlockA.update_failed] at hγ
          cases hγ
      | live s h₁ =>
          have hpr₁ := ih s h₁ rfl
          have hacc₁ := bankRepairDigitWordAccRunAux ring origin γ₀ root h₀ hγ₀
            hroot₀ hfix₀ hcl hcur hn ht hr s h₁ rfl
          have hb₁ := bankRepairDigitWordBelowRunAux ring origin γ₀ root h₀ hγ₀
            hroot₀ hfix₀ hcl hcur hn ht hr s h₁ rfl
          obtain ⟨hs, -, hreach₁⟩ := bankRepairDigitWordReachRunAux ring
            origin γ₀ root h₀ hγ₀ hroot₀ hfix₀ hcl hn ht hr s h₁ rfl
          rw [hs, AcceptedReceipts.WordEntrance.word_update_live] at hγ
          injection hγ with h1 h2
          subst h1 h2
          exact bankRepairDigitWordPubRunStep ring h₁ p e hn ht ht2 hpr₁ hacc₁ hb₁
            hreach₁

/-- T13 item 3 (with item 1): the run bundle holds along every projected
W run from `initializesWord`. -/
theorem bankRepairDigitWordRunPubRun {n : Nat} (ring : DirectedRing n)
    (c : Compiled) (origin p : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (w : List (Fin n)) (shadow : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hinit : BlockA.initializesWord ring origin γ₀)
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
      (.live shadow h)) :
    BankRepairDigitWordPubRun ring h p := by
  obtain ⟨root, h₀, hγ₀, hroot, hfix, ht2, htn, hph, -, hcl, -, -⟩ := hinit
  have hpow := bankRepairDigitPowLower c.t
  exact bankRepairDigitWordPubRunAux ring origin γ₀ root h₀ hγ₀ hroot hfix hph
    (fun i => ⟨(hcl i).2.2.2.2.1, (hcl i).2.2.1⟩) (fun i => (hcl i).2.2.2.1)
    (by omega) (by omega) ht2 hrun shadow h rfl

/-- T13 item 3: `BankRepairDigitWordPublished` holds at every live control
of every projected W run from `initializesWord`. -/
theorem bankRepairDigitWordRunPublishedHolds {n : Nat} (ring : DirectedRing n)
    (c : Compiled) : BankRepairDigitWordRunPublished ring c :=
  fun origin p γ₀ w shadow h hinit hrun =>
    (bankRepairDigitWordRunPubRun ring c origin p γ₀ w shadow h hinit hrun).1

/-- T13 item 1 (invariant): along every W run, in the worker phase every
site without a kind colour holds an OFF record, without a cursor unless
the site carries a cursor colour. -/
theorem bankRepairDigitWordRunFree {n : Nat} (ring : DirectedRing n)
    (c : Compiled) (origin p : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (w : List (Fin n)) (shadow : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hinit : BlockA.initializesWord ring origin γ₀)
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
      (.live shadow h)) :
    BankRepairDigitWordFree h p :=
  (bankRepairDigitWordRunPubRun ring c origin p γ₀ w shadow h hinit hrun).2.1

/-- T13 item 1 (done phase): along every W run, once DONE holds, every
physical SI record is consistent with the bits, and no projected edge
(in particular no physical P1, P3 or S1 row) changes any visible
(u, beta) pair, so none changes one at or below a window receipt. -/
theorem bankRepairDigitWordRunDoneQuiet {n : Nat} (ring : DirectedRing n)
    (c : Compiled) (origin p : Fin n → ProjW c)
    (γ₀ : BlockA.Decoration (Fin n → ProjW c) (BlockA.WordControl n c))
    (w : List (Fin n)) (shadow : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hinit : BlockA.initializesWord ring origin γ₀)
    (hrun : BlockA.Run ring (phiW ring) (BlockA.wordT ring) origin γ₀ w p
      (.live shadow h))
    (hdone : h.phase = .done) :
    BankRepairDigitWordPhys ring h.root p ∧
      ∀ e i, AcceptedReceipts.wordVisible (phiW ring p e) i =
        AcceptedReceipts.wordVisible p i := by
  have hpr := bankRepairDigitWordRunPubRun ring c origin p γ₀ w shadow h hinit hrun
  obtain ⟨hall, hphys⟩ := hpr.2.2.2 hdone
  obtain ⟨-, -, -, -, -, ht2, htn, -, -, -, -, -⟩ := hinit
  have hpow := bankRepairDigitPowLower c.t
  exact ⟨hphys, fun e => bankRepairDigitWordDoneVisible ring h p e (by omega)
    (by omega) ht2 hpr.1 hall hphys⟩

end L3.RenewalReferenceClock

/-! T14 step 1: the W-run invariant `hrun` is discharged by
`bankRepairDigitWordRunPublishedHolds`, at all three consumers. -/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- `bankRepairDigitWordValuesOfAccepted` without the W-run premise. -/
theorem bankRepairDigitWordValuesOfAcceptedWord {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (hprim : IsPrimitive c.t c.taps)
    (p : Fin n → ProjW c)
    (hacc : AcceptedReceipts.AcceptedWord ring (BlockA.wordT ring)
      (BlockA.wordValidated ring) p) :
    ∃ root, WFixedRoot ring root p ∧
      CleanWorkerWordValues ring root p :=
  bankRepairDigitWordValuesOfAccepted ring
    (bankRepairDigitWordRunPublishedHolds ring c) hprim p hacc

/-- `bankRepairDigitRootWordValuesOfWordRun` without the W-run premise. -/
theorem bankRepairDigitRootWordValuesOfWordStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (y : BankReferenceState ring hbank)
    (hW : BankRepairWord ring hbank y) :
    BankRepairDigitRootWordValues ring hbank y :=
  bankRepairDigitRootWordValuesOfWordRun ring hbank
    (bankRepairDigitWordRunPublishedHolds ring _) y hW

/-- T14 step 1: every R-fold entrance reached after the W stage from a
prepared state carries the single-inherited-label tasks at every site,
with no W-run premise. -/
theorem bankRepairDigitSingleInheritedLabelTasksOfWordStage
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (wordW : List (Fin n))
    (hW : BankRepairWord ring hbank
      (wordW.foldl (bankRepairNext ring hbank) x))
    (wordR : List (Fin n))
    (hR : BankRepairRFoldEstablished ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x))) :
    ∀ site, BankRepairDigitSingleInheritedLabelTasks ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x)) site :=
  bankRepairDigitSingleInheritedLabelTasksOfWordRunPublished ring hn hbank
    (bankRepairDigitWordRunPublishedHolds ring _) x hx wordW hW wordR hR

/-! T14 step 3. `BankRepairDigitBaseExtinctionImpliesFullBoundary` is
false whenever an R-fold entrance exists: the R-fold class reads no
writer top field, so the writer base/input/carry of an entrance can be
scrubbed. That leaves every inherited base label already gone at the
empty word, but the leading-segment writer input is `X`, not `E`. -/

/-- The entrance `z` with writer base NONE, writer input X and writer
carry OFF at every site. Memory (hence stamp validity) is unchanged. -/
def bankRepairDigitScrubbedEntrance {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : BankReferenceState ring hbank :=
  ⟨((fun i => { z.val.1 i with
      wBase := WBase.NONE, wIn := InTok.X, wCarry := WCarry.OFF }),
    z.val.2), z.2⟩

/-- The scrubbed entrance is again an R-fold entrance, has every
inherited base label gone at the empty word, and is not in the
boundary-retired cut. -/
theorem bankRepairDigitScrubbedEntranceSeparates {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairRFoldEstablished ring hbank z) :
    BankRepairRFoldEstablished ring hbank
        (bankRepairDigitScrubbedEntrance ring hbank z) ∧
      bankRepairDigitAllBaseLabelsGone ring hbank
        (bankRepairDigitScrubbedEntrance ring hbank z,
          digitAuditInitial
            (piD (bankRepairDigitScrubbedEntrance ring hbank z).val.1)) ∧
      ¬ BankRepairDigitBoundaryRetiredCut ring hbank
        (bankRepairDigitScrubbedEntrance ring hbank z) := by
  refine ⟨?_, ?_, ?_⟩
  · have hN : nativeProjection
        (bankRepairDigitScrubbedEntrance ring hbank z).val.1 =
        nativeProjection z.val.1 := rfl
    have hC : (fun i => NativeCand.ofAgent
        ((bankRepairDigitScrubbedEntrance ring hbank z).val.1 i)) =
        (fun i => NativeCand.ofAgent (z.val.1 i)) := rfl
    have hW : piW (bankRepairDigitScrubbedEntrance ring hbank z).val.1 =
        piW z.val.1 := rfl
    have hR : piR (bankRepairDigitScrubbedEntrance ring hbank z).val.1 =
        piR z.val.1 := rfl
    obtain ⟨⟨⟨hn1, hc1⟩, hw1⟩, hr1⟩ := hz
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · unfold Closure.NativeFactor at hn1 ⊢
      rw [hN]
      exact hn1
    · unfold Closure.CandidateFactor at hc1 ⊢
      rw [hC]
      exact hc1
    · unfold BankRepairWord Closure.WordFactor at hw1 ⊢
      rw [hW]
      exact hw1
    · unfold BankRepairReader Closure.ReaderFactor at hr1 ⊢
      rw [hR]
      exact hr1
  · rintro ⟨site, i, h⟩
    change (DigitGhost.initial i
      (piD (bankRepairDigitScrubbedEntrance ring hbank z).val.1 i)).base =
        some (DigitBaseOrigin.inherited site) at h
    simp [DigitGhost.initial, piD, ProjD.ofAgent,
      bankRepairDigitScrubbedEntrance] at h
  · rintro ⟨_start, _word, root, _audit, _hstart, _hpair, _hroot, _hat,
      hreceipt, _hbase⟩
    obtain ⟨first, stop, hseg, _hlead, hfirst⟩ := hreceipt.1
    have hlt : first < stop := hseg.2.2.1
    have hk := hfirst DigitLane.writer first (Nat.le_refl first) hlt
    simp [digitEndpointView, digitLaneView, piD, ProjD.ofAgent,
      DigitLastCarryInert, WCarry.isW,
      bankRepairDigitScrubbedEntrance] at hk

/-- T14 step 3 (refutation): the terminal inclusion premise forces the
R-fold class to be empty, so it cannot close any non-vacuous clock. -/
theorem bankRepairDigitBaseExtinctionImpliesFullBoundaryFalse {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hfull : BankRepairDigitBaseExtinctionImpliesFullBoundary ring hbank)
    (z : BankReferenceState ring hbank) :
    ¬ BankRepairRFoldEstablished ring hbank z := by
  intro hz
  obtain ⟨hz', hgone, hnot⟩ :=
    bankRepairDigitScrubbedEntranceSeparates ring hbank z hz
  exact hnot (hfull _ [] hz' hgone)

/-- Generic first-hit transfer: if every scheduler word that reaches `P`
on the second process reaches `Q` on the first, the first-hit cost of
`Q` is at most that of `P`. -/
theorem bankRepairDigitCostTransfer {S₀ S₁ : Type} {n : Nat}
    (next₀ : S₀ → Fin n → S₀) (next₁ : S₁ → Fin n → S₁)
    (Q : S₀ → Prop) (P : S₁ → Prop) :
    ∀ (T : Nat) (x₀ : S₀) (x₁ : S₁),
      (∀ w : List (Fin n), P (w.foldl next₁ x₁) → Q (w.foldl next₀ x₀)) →
      costNumerator next₀ Q x₀ T ≤ costNumerator next₁ P x₁ T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x₀ x₁ _
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro x₀ x₁ h
      by_cases hQ : Q x₀
      · rw [costNumerator_terminal next₀ Q x₀ hQ (T + 1)]
        exact Nat.zero_le _
      · have hP : ¬ P x₁ := fun hp => hQ (h [] hp)
        rw [costNumerator_succ next₀ Q x₀ hQ T,
          costNumerator_succ next₁ P x₁ hP T]
        have hs := ofFn_sum_le
          (fun e : Fin n => costNumerator next₀ Q (next₀ x₀ e) T)
          (fun e : Fin n => costNumerator next₁ P (next₁ x₁ e) T)
          (fun e => ih (next₀ x₀ e) (next₁ x₁ e)
            (fun w hw => h (e :: w) hw))
        exact Nat.add_le_add_left hs _

/-- Replacement premise, at ONE entrance only: along the coupled
BANK x audit run from `start`, base extinction carries the packet
boundary cut. It does not quantify over all R-fold entrances, so the
scrubbed entrance does not refute it at a step-1 entrance. -/
def BankRepairDigitBaseExtinctionBoundaryAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) : Prop :=
  ∀ word : List (Fin n),
    bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))) →
    BankRepairDigitBoundaryRetiredCut ring hbank
      (word.foldl (bankRepairNext ring hbank) start)

/-- The per-entrance premise closes the boundary micro-clock from
every step-1 entrance (W stage from a prepared state, then R). -/
theorem bankRepairDigitBoundaryClockOfWordStage
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (wordW : List (Fin n))
    (hW : BankRepairWord ring hbank
      (wordW.foldl (bankRepairNext ring hbank) x))
    (wordR : List (Fin n))
    (hR : BankRepairRFoldEstablished ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x)))
    (hpacket : BankRepairDigitBaseExtinctionBoundaryAt ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x))) :
    ∀ T : Nat,
      2 * costNumerator (bankRepairNext ring hbank)
        (BankRepairDigitBoundaryRetiredCut ring hbank)
        (wordR.foldl (bankRepairNext ring hbank)
          (wordW.foldl (bankRepairNext ring hbank) x)) T ≤
      n ^ T * bankRepairDigitBoundaryMicroCharge n := by
  intro T
  have htasks := bankRepairDigitSingleInheritedLabelTasksOfWordStage
    ring hn hbank x hx wordW hW wordR hR
  have hbase := bankRepairDigitAllBaseFitsBoundaryMicroOfTasks hn ring hbank
    _ htasks T
  have htransfer := bankRepairDigitCostTransfer
    (bankRepairNext ring hbank) (bankRepairDigitBoundaryAuditNext ring hbank)
    (BankRepairDigitBoundaryRetiredCut ring hbank)
    (bankRepairDigitAllBaseLabelsGone ring hbank) T _ _ hpacket
  exact Nat.le_trans (Nat.mul_le_mul_left 2 htransfer) hbase

/-- Equivalently: on the class of entrances where the per-entrance
premise holds and the label tasks hold, the micro-clock is a theorem. -/
theorem bankRepairDigitBoundaryClockOfTasksAt
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (entrance : BankReferenceState ring hbank → Prop)
    (htasks : ∀ z, entrance z → ∀ site,
      BankRepairDigitSingleInheritedLabelTasks ring hbank z site)
    (hpacket : ∀ z, entrance z →
      BankRepairDigitBaseExtinctionBoundaryAt ring hbank z) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank) entrance
      (BankRepairDigitBoundaryRetiredCut ring hbank)
      (bankRepairDigitBoundaryMicroCharge n) := by
  intro z hz T
  exact Nat.le_trans
    (Nat.mul_le_mul_left 2 (bankRepairDigitCostTransfer
      (bankRepairNext ring hbank) (bankRepairDigitBoundaryAuditNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank)
      (bankRepairDigitAllBaseLabelsGone ring hbank) T _ _ (hpacket z hz)))
    (bankRepairDigitAllBaseFitsBoundaryMicroOfTasks hn ring hbank
      z (htasks z hz) T)

end L3.RenewalReferenceClock

/-! T15. Packet boundary at W-stage entrances.

Step 1 pieces. Along the coupled BANK x audit run from a W-stage entrance:
* `DigitAt` is a run invariant (the prepared root's singleton class is closed
  and grant-free, so no edge FIREs and `piD` follows `phiD`);
* `WFixedRoot` at the prepared root is a run invariant;
* base extinction relative to the audit holds whenever every inherited base
  label is gone (base-ghost soundness is a run invariant).
The fourth piece, `DigitBoundaryReceipt`, is NOT a consequence of the W-stage
hypotheses: the scrubbed state of any prepared R-fold entrance is again a
W-stage entrance (empty W and R words), has every inherited label gone at the
empty word, and fails the receipt there. The weakest true replacement is the
per-entrance receipt condition, which is EQUIVALENT to the per-entrance premise. -/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ### Base-ghost soundness -/

/-- Base-ghost soundness at one site: no base record and no label, or a base
record carrying an inherited label or a root launch after time 0. -/
def BankRepairDigitBaseGhostSound {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (w : WBase) (g : Option (DigitBaseOrigin n)) : Prop :=
  (w = .NONE ∧ g = none) ∨
    (w ≠ .NONE ∧ ((∃ s : Fin n, g = some (.inherited s)) ∨
      ∃ born : Nat, 0 < born ∧
        g = some (.rootLaunch born root (ring.rightNeighbor root))))

theorem bankRepairDigitLiveTopWBaseX (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) :
    (liveTopPair c ox oy bx bY).x.wBase =
      (if oy.l then ((.NONE : WBase), oy.wBase, (none : Option (Fin c.topA)))
       else if ox.l && !oy.l then
         (.NONE, (if oy.wBase == .NONE then .SEEK else oy.wBase), none)
       else if !ox.l && ox.wBase == .ZERO then
         (.NONE, (if !oy.l && !bY && oy.wBase == .NONE then .ZERO else oy.wBase),
          some c.zeroDigit)
       else if !ox.l && ox.wBase == .SEEK then
         (.NONE, (if !oy.l && oy.wBase == .NONE then
            (if bY then .ZERO else .SEEK) else oy.wBase), none)
       else (ox.wBase, oy.wBase, none)).1 := rfl

theorem bankRepairDigitBaseStepXPair {n : Nat} {c : Compiled}
    (time : Nat) (source destination : Fin n)
    (x y : ProjD c) (bx bY : Bool) (gx gy : Option (DigitBaseOrigin n)) :
    ((liveTopPair c x.lift y.lift bx bY).x.wBase = .NONE ∧
      (digitBaseReplay time source destination x y bY gx gy).x = none) ∨
    ((liveTopPair c x.lift y.lift bx bY).x.wBase = x.top.wBase ∧
      (digitBaseReplay time source destination x y bY gx gy).x = gx) := by
  rw [bankRepairDigitLiveTopWBaseX]
  have hl : ∀ a : ProjD c, a.lift.l = a.word.native.l := fun _ => rfl
  have hw : ∀ a : ProjD c, a.lift.wBase = a.top.wBase := fun _ => rfl
  simp only [hl, hw]
  unfold digitBaseReplay
  cases hrx : x.word.native.l <;> cases hry : y.word.native.l <;>
    cases hwx : x.top.wBase <;> simp

theorem bankRepairDigitBaseStepYPair {n : Nat} {c : Compiled}
    (time : Nat) (source destination : Fin n)
    (x y : ProjD c) (bx bY : Bool) (gx gy : Option (DigitBaseOrigin n)) :
    ((liveTopPair c x.lift y.lift bx bY).y.wBase = y.top.wBase ∧
      (digitBaseReplay time source destination x y bY gx gy).y = gy) ∨
    (x.word.native.l = true ∧
      (liveTopPair c x.lift y.lift bx bY).y.wBase ≠ .NONE ∧
      (digitBaseReplay time source destination x y bY gx gy).y =
        some (.rootLaunch time source destination)) ∨
    (x.top.wBase ≠ .NONE ∧
      (liveTopPair c x.lift y.lift bx bY).y.wBase ≠ .NONE ∧
      (digitBaseReplay time source destination x y bY gx gy).y = gx) := by
  rw [bankRepairDigitLiveTopWBaseY]
  have hl : ∀ a : ProjD c, a.lift.l = a.word.native.l := fun _ => rfl
  have hw : ∀ a : ProjD c, a.lift.wBase = a.top.wBase := fun _ => rfl
  simp only [hl, hw]
  unfold digitBaseReplay
  cases hrx : x.word.native.l <;> cases hry : y.word.native.l <;>
    cases hwx : x.top.wBase <;> cases hwy : y.top.wBase <;>
    cases bY <;> simp

/-- One audited edge preserves base-ghost soundness when the only leader
is the root and the stamp is positive. -/
theorem bankRepairDigitBaseGhostSoundStep {n : Nat} {c : Compiled}
    (hn : 2 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (time : Nat) (e : Fin n) (htime : 0 < time)
    (hroot : ∀ i, (S i).word.native.l = true → i = root)
    (hsound : ∀ i, BankRepairDigitBaseGhostSound ring root
      (S i).top.wBase (G i).base) :
    ∀ i, BankRepairDigitBaseGhostSound ring root
      (phiD ring S e i).top.wBase
      (digitGhostStep ring S G time e i).base := by
  intro i
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  by_cases hie : i = e
  · subst i
    have hphi : phiD ring S e e = (pairD (S e) (S (ring.rightNeighbor e))).1 := by
      simp [phiD, projectedEdge]
    have htop : (phiD ring S e e).top.wBase =
        (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
          (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
          (workerW (S e).word
            (S (ring.rightNeighbor e)).word).betaY).x.wBase := by
      rw [hphi]; rfl
    have hg : (digitGhostStep ring S G time e e).base =
        (digitBaseReplay time e (ring.rightNeighbor e)
          (S e) (S (ring.rightNeighbor e))
          (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY
          (G e).base (G (ring.rightNeighbor e)).base).x := by
      simp [digitGhostStep, digitService]
    rw [htop, hg]
    rcases bankRepairDigitBaseStepXPair time e (ring.rightNeighbor e)
        (S e) (S (ring.rightNeighbor e))
        (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
        (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY
        (G e).base (G (ring.rightNeighbor e)).base with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact Or.inl ⟨rfl, rfl⟩
    · rw [h1, h2]; exact hsound e
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      have hphi : phiD ring S e (ring.rightNeighbor e) =
          (pairD (S e) (S (ring.rightNeighbor e))).2 := by
        simp [phiD, projectedEdge, hne]
      have htop : (phiD ring S e (ring.rightNeighbor e)).top.wBase =
          (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
            (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
            (workerW (S e).word
              (S (ring.rightNeighbor e)).word).betaY).y.wBase := by
        rw [hphi]; rfl
      have hg : (digitGhostStep ring S G time e (ring.rightNeighbor e)).base =
          (digitBaseReplay time e (ring.rightNeighbor e)
            (S e) (S (ring.rightNeighbor e))
            (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY
            (G e).base (G (ring.rightNeighbor e)).base).y := by
        simp [digitGhostStep, digitService, hne]
      rw [htop, hg]
      rcases bankRepairDigitBaseStepYPair time e (ring.rightNeighbor e)
          (S e) (S (ring.rightNeighbor e))
          (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
          (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY
          (G e).base (G (ring.rightNeighbor e)).base with
        ⟨h1, h2⟩ | ⟨hl, h1, h2⟩ | ⟨hx, h1, h2⟩
      · rw [h1, h2]; exact hsound _
      · have he : e = root := hroot e hl
        rw [h2]
        refine Or.inr ⟨h1, Or.inr ⟨time, htime, ?_⟩⟩
        rw [he]
      · rw [h2]
        refine Or.inr ⟨h1, ?_⟩
        rcases hsound e with ⟨hnone, _⟩ | ⟨_, hgood⟩
        · exact absurd hnone hx
        · exact hgood
    · have hphi : phiD ring S e i = S i := by
        simp [phiD, projectedEdge, hie, hij]
      rw [hphi, bankRepairDigitInheritedAuditAwayFrame ring S G time e i hie hij]
      exact hsound i

/-! ### The coupled run invariant -/

/-- Run invariant of the coupled BANK x audit chain at a fixed root. -/
def BankRepairDigitBoundaryAuditInvariant {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (p : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  BankPostInheritedSingleton ring hbank root p.1 ∧
  DigitAt ring p.2 p.2.clock (piD p.1.val.1) p.2.current ∧
  ∀ i, BankRepairDigitBaseGhostSound ring root
    (piD p.1.val.1 i).top.wBase (p.2.current i).base

/-- Grant-freeness of the singleton class disables every old FIRE. -/
theorem bankRepairDigitBoundaryNoFireOfSingleton {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedSingleton ring hbank root z) (e : Fin n) :
    oldFire (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) = none := by
  have hg := hz.1.1.2
  simp [oldFire, fireSelect, hg e, hg (ring.rightNeighbor e)]

theorem bankRepairDigitBoundaryAuditInvariantInitial {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (start : BankReferenceState ring hbank)
    (h : BankPostInheritedSingleton ring hbank root start) :
    BankRepairDigitBoundaryAuditInvariant ring hbank root
      (start, digitAuditInitial (piD start.val.1)) := by
  refine ⟨h, Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
  intro i
  change BankRepairDigitBaseGhostSound ring root (start.val.1 i).wBase
    (if (start.val.1 i).wBase == WBase.NONE then none
      else some (DigitBaseOrigin.inherited i))
  unfold BankRepairDigitBaseGhostSound
  cases (start.val.1 i).wBase <;> simp

theorem bankRepairDigitBoundaryAuditInvariantStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (p : BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hp : BankRepairDigitBoundaryAuditInvariant ring hbank root p)
    (e : Fin n) :
    BankRepairDigitBoundaryAuditInvariant ring hbank root
      (bankRepairDigitBoundaryAuditNext ring hbank p e) := by
  obtain ⟨hs, _hat, hsound⟩ := hp
  have hproj := bankRepairDigitMaskedProjectionOfNoFire ring hbank p.1 e
    (bankRepairDigitBoundaryNoFireOfSingleton ring hbank root p.1 hs e)
  have hroot : ∀ i, (piD p.1.val.1 i).word.native.l = true → i = root :=
    fun i hi => hs.2.2.1 i hi
  refine ⟨bankPostInheritedSingletonClosed ring hn hbank root p.1 hs e, ?_, ?_⟩
  · exact Or.inr ⟨_, List.Mem.head _, rfl, hproj, rfl⟩
  · intro i
    change BankRepairDigitBaseGhostSound ring root
      (piD (bankRepairNext ring hbank p.1 e).val.1 i).top.wBase
      (digitGhostStep ring (piD p.1.val.1) p.2.current (p.2.clock + 1) e i).base
    rw [hproj]
    exact bankRepairDigitBaseGhostSoundStep (by omega) ring root _ _ _ e
      (Nat.succ_pos _) hroot hsound i

theorem bankRepairDigitBoundaryAuditInvariantWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (word : List (Fin n)) :
    ∀ p : BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n,
      BankRepairDigitBoundaryAuditInvariant ring hbank root p →
      BankRepairDigitBoundaryAuditInvariant ring hbank root
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p) := by
  induction word with
  | nil => intro p hp; exact hp
  | cons e rest ih =>
      intro p hp
      exact ih _ (bankRepairDigitBoundaryAuditInvariantStep ring hn hbank root p hp e)

theorem bankRepairDigitSingletonWordFold {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank,
      BankPostInheritedSingleton ring hbank root z →
      BankPostInheritedSingleton ring hbank root
        (word.foldl (bankRepairNext ring hbank) z) := by
  induction word with
  | nil => intro z hz; exact hz
  | cons e rest ih =>
      intro z hz
      exact ih _ (bankPostInheritedSingletonClosed ring hn hbank root z hz e)

/-- A W-stage entrance carries the prepared root's singleton class. -/
theorem bankRepairDigitWordStageSingleton {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (wordW wordR : List (Fin n)) :
    ∃ root, BankPostInheritedSingleton ring hbank root
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x)) := by
  obtain ⟨root, hs, _⟩ := hx
  exact ⟨root, bankRepairDigitSingletonWordFold ring hn hbank root wordR _
    (bankRepairDigitSingletonWordFold ring hn hbank root wordW x hs)⟩

theorem bankRepairDigitBoundaryAuditInvariantRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (start : BankReferenceState ring hbank)
    (hs : BankPostInheritedSingleton ring hbank root start)
    (word : List (Fin n)) :
    BankRepairDigitBoundaryAuditInvariant ring hbank root
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))) :=
  bankRepairDigitBoundaryAuditInvariantWord ring hn hbank root word _
    (bankRepairDigitBoundaryAuditInvariantInitial ring hbank root start hs)

/-! ### Step 1 pieces at W-stage entrances -/

/-- Piece `DigitAt`: at every audited state of the run from a W-stage
entrance, `piD` of the BANK state is the audit's last frame endpoint. -/
theorem bankRepairDigitBoundaryDigitAtOfWordStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (wordW wordR : List (Fin n))
    (start : BankReferenceState ring hbank)
    (hstart : start = wordR.foldl (bankRepairNext ring hbank)
      (wordW.foldl (bankRepairNext ring hbank) x))
    (word : List (Fin n)) :
    DigitAt ring
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2.clock
      (piD (word.foldl (bankRepairNext ring hbank) start).val.1)
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2.current := by
  subst hstart
  obtain ⟨root, hs⟩ := bankRepairDigitWordStageSingleton ring hn hbank x hx wordW wordR
  have h := (bankRepairDigitBoundaryAuditInvariantRun ring hn hbank root _ hs word).2.1
  rw [bankRepairDigitBoundaryAuditFirst] at h
  exact h

/-- Piece `WFixedRoot` at a fixed singleton root. -/
theorem bankRepairDigitBoundaryWFixedRootOfSingleton {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (start : BankReferenceState ring hbank)
    (hs : BankPostInheritedSingleton ring hbank root start)
    (word : List (Fin n)) :
    WFixedRoot ring root
      (piW (word.foldl (bankRepairNext ring hbank) start).val.1) :=
  (bankRepairDigitSingletonWordFold ring hn hbank root word start hs).2

/-- Piece `WFixedRoot`: the prepared root is the W fixed root at every
state of the run from a W-stage entrance. -/
theorem bankRepairDigitBoundaryWFixedRootOfWordStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (wordW wordR : List (Fin n))
    (start : BankReferenceState ring hbank)
    (hstart : start = wordR.foldl (bankRepairNext ring hbank)
      (wordW.foldl (bankRepairNext ring hbank) x)) :
    ∃ root : Fin n, BankPostInheritedSingleton ring hbank root start ∧
      ∀ word : List (Fin n), WFixedRoot ring root
        (piW (word.foldl (bankRepairNext ring hbank) start).val.1) := by
  subst hstart
  obtain ⟨root, hs⟩ := bankRepairDigitWordStageSingleton ring hn hbank x hx wordW wordR
  exact ⟨root, hs, bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root _ hs⟩

/-- Piece base extinction: once every inherited label is gone, the audit
witnesses `DigitBaseExtinct` at the singleton root at the current clock. -/
theorem bankRepairDigitBoundaryBaseExtinctOfSingleton {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (start : BankReferenceState ring hbank)
    (hs : BankPostInheritedSingleton ring hbank root start)
    (word : List (Fin n))
    (hgone : bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1)))) :
    DigitBaseExtinct ring root
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2 0
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2.clock := by
  obtain ⟨_, hat, hsound⟩ :=
    bankRepairDigitBoundaryAuditInvariantRun ring hn hbank root start hs word
  refine ⟨Nat.zero_le _, _, _, hat, ?_⟩
  intro i
  rcases hsound i with ⟨hw, hg⟩ | ⟨hw, ⟨s, hg⟩ | ⟨born, hborn, hg⟩⟩
  · exact Or.inl ⟨hw, hg⟩
  · exact absurd ⟨s, i, hg⟩ hgone
  · exact Or.inr ⟨born, hborn, hw, hg⟩

/-- Assembly: the invariant pieces plus a receipt at the singleton root
give the boundary-retired cut. -/
theorem bankRepairDigitBoundaryCutOfReceipt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (start : BankReferenceState ring hbank)
    (hR : BankRepairRFoldEstablished ring hbank start)
    (hs : BankPostInheritedSingleton ring hbank root start)
    (word : List (Fin n))
    (hgone : bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))))
    (hrec : DigitBoundaryReceipt ring root
      (piD (word.foldl (bankRepairNext ring hbank) start).val.1)) :
    BankRepairDigitBoundaryRetiredCut ring hbank
      (word.foldl (bankRepairNext ring hbank) start) := by
  have hinv := bankRepairDigitBoundaryAuditInvariantRun ring hn hbank root start hs word
  have hfirst := bankRepairDigitBoundaryAuditFirst ring hbank start
    (digitAuditInitial (piD start.val.1)) word
  have hat := hinv.2.1
  rw [hfirst] at hat
  refine ⟨start, word, root,
    (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).2, hR, ?_,
    bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root start hs word,
    hat, hrec,
    bankRepairDigitBoundaryBaseExtinctOfSingleton ring hn hbank root start hs word hgone⟩
  exact Prod.ext hfirst rfl

/-- Weakest true replacement: at a W-stage entrance the per-entrance premise
is EQUIVALENT to the packet receipt, at the W fixed root, at every audited
state where every inherited base label is gone. -/
theorem bankRepairDigitBaseExtinctionBoundaryAtIffReceipt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (wordW wordR : List (Fin n))
    (hR : BankRepairRFoldEstablished ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x))) :
    BankRepairDigitBaseExtinctionBoundaryAt ring hbank
        (wordR.foldl (bankRepairNext ring hbank)
          (wordW.foldl (bankRepairNext ring hbank) x)) ↔
      ∀ word : List (Fin n),
        bankRepairDigitAllBaseLabelsGone ring hbank
          (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (wordR.foldl (bankRepairNext ring hbank)
              (wordW.foldl (bankRepairNext ring hbank) x),
             digitAuditInitial (piD (wordR.foldl (bankRepairNext ring hbank)
              (wordW.foldl (bankRepairNext ring hbank) x)).val.1))) →
        ∀ root : Fin n,
          WFixedRoot ring root (piW (word.foldl (bankRepairNext ring hbank)
            (wordR.foldl (bankRepairNext ring hbank)
              (wordW.foldl (bankRepairNext ring hbank) x))).val.1) →
          DigitBoundaryReceipt ring root (piD (word.foldl (bankRepairNext ring hbank)
            (wordR.foldl (bankRepairNext ring hbank)
              (wordW.foldl (bankRepairNext ring hbank) x))).val.1) := by
  constructor
  · intro hat word hgone root hroot
    obtain ⟨_, _, root', _, _, _, hroot', _, hrec, _⟩ := hat word hgone
    have heq : root' = root := hroot.2.1 root' hroot'.1
    rw [← heq]
    exact hrec
  · intro hrec word hgone
    obtain ⟨root, hs⟩ := bankRepairDigitWordStageSingleton ring hn hbank x hx wordW wordR
    exact bankRepairDigitBoundaryCutOfReceipt ring hn hbank root _ hR hs word hgone
      (hrec word hgone root
        (bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root _ hs word))

/-! ### Step 3: the receipt piece is false at a W-stage entrance

Inherited-authority extinction (the only dynamic part of preparedness) reads
only BANK storage, PACK, grants and the BANK ghost memory, and these evolve
independently of the writer top fields. Hence the scrubbed state of a prepared
state is prepared. -/

/-- BANK storage fields read by BANK success, BANK memory and PACK. -/
def bankRepairDigitBankKey {c : Compiled} (a : Agent c) :
    Fin (c.b + 2) × Mode × Bool × BTok × Fin (c.bankLeaseCap + 1) :=
  (a.pack, a.mode, a.bit, a.tok, a.lease)

theorem bankRepairDigitBaseStepBankFields (c : Compiled) (hs : c.useSmall = false)
    (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.mode = (bankPair (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b c.theta).1.mode ∧
    (baseStep c ev x y).1.bit = (bankPair (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b c.theta).1.bit ∧
    (baseStep c ev x y).1.tok = (bankPair (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b c.theta).1.tok ∧
    (baseStep c ev x y).1.lease = (copyBank x (bankPair (bankCell x x.pack.val)
        (bankCell y y.pack.val) (packNext x.pack.val y.pack.val c.b) c.b c.theta).1).lease ∧
    (baseStep c ev x y).2.mode = (bankPair (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b c.theta).2.mode ∧
    (baseStep c ev x y).2.bit = (bankPair (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b c.theta).2.bit ∧
    (baseStep c ev x y).2.tok = (bankPair (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b c.theta).2.tok ∧
    (baseStep c ev x y).2.lease = (copyBank y (bankPair (bankCell x x.pack.val)
        (bankCell y y.pack.val) (packNext x.pack.val y.pack.val c.b) c.b c.theta).2).lease := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [baseStep, hs, Agent.setNative, Agent.setCPriv, copyBank] <;>
    repeat (first | rfl | split)

theorem bankRepairDigitBaseStepPack (c : Compiled)
    (ev : CertEvent) (x y : Agent c) :
    (baseStep c ev x y).1.pack = x.pack ∧
      (baseStep c ev x y).2.pack =
        packFin c (packNext x.pack.val y.pack.val c.b) := by
  constructor <;> by_cases hs : c.useSmall <;>
    simp [baseStep, hs, Agent.setNative, Agent.setCPriv, copyBank] <;>
    repeat (first | rfl | split)

/-- The masked pair's BANK storage depends only on the old BANK storage,
PACK and grants (not on the mask bit, the writer top or the debt fields). -/
theorem bankRepairDigitMaskedBankKey (c : Compiled) (hs : c.useSmall = false)
    (b b' : Bool) (x y x' y' : Agent c)
    (hx : bankRepairDigitBankKey x = bankRepairDigitBankKey x')
    (hy : bankRepairDigitBankKey y = bankRepairDigitBankKey y')
    (hgx : x.grant = x'.grant) (hgy : y.grant = y'.grant) :
    bankRepairDigitBankKey (renewalMaskedPair c b x y).1 =
        bankRepairDigitBankKey (renewalMaskedPair c b' x' y').1 ∧
    bankRepairDigitBankKey (renewalMaskedPair c b x y).2 =
        bankRepairDigitBankKey (renewalMaskedPair c b' x' y').2 := by
  have hm1 : ∀ (s : Bool) (u v : Agent c), bankRepairDigitBankKey (renewalMaskedPair c s u v).1 =
      bankRepairDigitBankKey (baseStep c (certificateStep c u v).2.2 u v).1 := by
    intro s u v; cases s <;> rfl
  have hm2 : ∀ (s : Bool) (u v : Agent c), bankRepairDigitBankKey (renewalMaskedPair c s u v).2 =
      bankRepairDigitBankKey (baseStep c (certificateStep c u v).2.2 u v).2 := by
    intro s u v; cases s <;> rfl
  simp only [bankRepairDigitBankKey, Prod.mk.injEq] at hx hy
  obtain ⟨hxp, hxm, hxb, hxt, hxl⟩ := hx
  obtain ⟨hyp, hym, hyb, hyt, hyl⟩ := hy
  have hcx : bankCell x x.pack.val = bankCell x' x'.pack.val := by
    simp [bankCell, hxp, hxm, hxb, hxt, hxl, hgx]
  have hcy : bankCell y y.pack.val = bankCell y' y'.pack.val := by
    simp [bankCell, hyp, hym, hyb, hyt, hyl, hgy]
  rw [hm1, hm1, hm2, hm2]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    bankRepairDigitBaseStepBankFields c hs (certificateStep c x y).2.2 x y
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ :=
    bankRepairDigitBaseStepBankFields c hs (certificateStep c x' y').2.2 x' y'
  obtain ⟨p1, p2⟩ := bankRepairDigitBaseStepPack c (certificateStep c x y).2.2 x y
  obtain ⟨q1, q2⟩ := bankRepairDigitBaseStepPack c (certificateStep c x' y').2.2 x' y'
  simp only [bankRepairDigitBankKey]
  rw [a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8, p1, p2, q1, q2]
  simp only [copyBank]
  rw [hcx, hcy]
  simp only [hxp, hyp, and_self]

private theorem bankRepairDigitZeroGrantTokenRow {c : Compiled}
    (x y : Agent c) (fx fy : CertNative) (dcc : Bool)
    (hx : x.grant = false) (hy : y.grant = false) :
    (tokenStep x y fx fy none dcc false).1.grant = false ∧
      (tokenStep x y fx fy none dcc false).2.1.grant = false := by
  cases hrx : x.req <;> cases hry : y.req <;>
    cases hfx : fx.l <;> cases hfy : fy.l <;>
    cases hd : dcc <;>
    simp [tokenStep, hx, hy, hrx, hry, hfx, hfy]

private theorem bankRepairDigitSuppressedGrantFree
    (c : Compiled) (x y : Agent c)
    (hx : x.grant = false) (hy : y.grant = false) :
    (renewalNoNewGrantTokens c x y).1.grant = false ∧
      (renewalNoNewGrantTokens c x y).2.1.grant = false := by
  have hf :
      fireSelect x y
        (postEInfo x y).eX (postEInfo x y).eY = none := by
    simp [fireSelect, hx, hy]
  unfold renewalNoNewGrantTokens
  rw [hf]
  exact bankRepairDigitZeroGrantTokenRow x y
    (transition c x y).1.certNative
    (transition c x y).2.certNative
    (dccStep x y (certificateStep c x y).2.2).request hx hy

private theorem bankRepairDigitNoSuccessGrantFree
    (c : Compiled) (x y : Agent c)
    (hbank : c.useSmall = false)
    (hx : x.grant = false) (hy : y.grant = false)
    (hzero : bankSuccess
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b = false) :
    (transition c x y).1.grant = false ∧
      (transition c x y).2.grant = false := by
  have hf :
      fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2 = none := by
    simp [fireSelect, hx, hy]
  have hb :
      baseBankSuccessBit c x y = false := by
    simp [baseBankSuccessBit, hbank, hzero]
  have ht :
      (baseTokenOutputs c (certificateStep c x y).2.2
        x y).1.grant = false ∧
      (baseTokenOutputs c (certificateStep c x y).2.2
        x y).2.1.grant = false := by
    simpa [baseTokenOutputs, hf, hb, fireAtSite] using
      (bankRepairDigitZeroGrantTokenRow x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2
        (dccStep x y (certificateStep c x y).2.2).request hx hy)
  have hframe :=
    baseStep_token_fields c (certificateStep c x y).2.2 x y
  constructor
  · calc
      (transition c x y).1.grant =
          (baseStep c (certificateStep c x y).2.2
            x y).1.grant := rfl
      _ = (baseTokenOutputs c (certificateStep c x y).2.2
            x y).1.grant := hframe.2.1
      _ = false := ht.1
  · calc
      (transition c x y).2.grant =
          (baseStep c (certificateStep c x y).2.2
            x y).2.grant := rfl
      _ = (baseTokenOutputs c (certificateStep c x y).2.2
            x y).2.1.grant := hframe.2.2.2
      _ = false := ht.2

private theorem bankRepairDigitFreshPayerGrantFree {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hbank : c.useSmall = false)
    (hx : x.grant = false) (hy : y.grant = false)
    (hfresh :
      bankSuccess
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b = true →
      renewalBankFreshPayer
        (m.sites e).controller (m.sites dest).worker = true) :
    (renewalMaskedPair c
      (bankSuccess
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b &&
       renewalBankFreshPayer
         (m.sites e).controller (m.sites dest).worker)
      x y).1.grant = false ∧
    (renewalMaskedPair c
      (bankSuccess
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        (packNext x.pack.val y.pack.val c.b) c.b &&
       renewalBankFreshPayer
         (m.sites e).controller (m.sites dest).worker)
      x y).2.grant = false := by
  cases hs : bankSuccess
      (bankCell x x.pack.val) (bankCell y y.pack.val)
      (packNext x.pack.val y.pack.val c.b) c.b with
  | false =>
      rw [Bool.false_and, renewalMaskedPairOff]
      exact bankRepairDigitNoSuccessGrantFree c x y hbank hx hy hs
  | true =>
      have hp := hfresh hs
      rw [Bool.true_and, hp]
      have ht := bankRepairDigitSuppressedGrantFree c x y hx hy
      exact ⟨ht.1, ht.2⟩

private theorem bankRepairDigitIteFrame {α β : Type} (f : α → β)
    (P Q : Prop) [Decidable P] [Decidable Q] (a a' b b' d d' : α)
    (ha : f a = f a') (hb : f b = f b') (hd : f d = f d') :
    f (if P then a else if Q then b else d) =
      f (if P then a' else if Q then b' else d') := by
  by_cases hp : P
  · rw [if_pos hp, if_pos hp]; exact ha
  · rw [if_neg hp, if_neg hp]
    by_cases hq : Q
    · rw [if_pos hq, if_pos hq]; exact hb
    · rw [if_neg hq, if_neg hq]; exact hd

private theorem bankRepairDigitIteBool {α : Type} (f : α → Bool)
    (P Q : Prop) [Decidable P] [Decidable Q] (x y z : α)
    (hx : f x = false) (hy : f y = false) (hz : f z = false) :
    f (if P then x else if Q then y else z) = false := by
  split
  · exact hx
  · split
    · exact hy
    · exact hz

/-- Grant-freeness after one reference edge from the CURRENT
fresh-authority row only (no suffix property). -/
theorem bankRepairDigitFreshGrantFreeStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hgrant : NativeLiftGrantFree z.val.1)
    (hfresh : BankFreshAuthorityAt ring hbank z)
    (e : Fin n) :
    NativeLiftGrantFree (bankRepairNext ring hbank z e).val.1 := by
  have hp := bankRepairDigitFreshPayerGrantFree
    (compileAdvice (ceilLogTwo n)) z.val.2
    e (ring.rightNeighbor e)
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    hbank (hgrant e) (hgrant (ring.rightNeighbor e)) (hfresh e)
  intro i
  change
    (if i = e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1
     else if i = ring.rightNeighbor e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2
     else z.val.1 i).grant = false
  exact bankRepairDigitIteBool (Agent.grant (c := compileAdvice (ceilLogTwo n)))
    _ _ _ _ _ hp.1 hp.2 (hgrant i)

/-- Two BANK reference states with the same ghost memory and the
same BANK storage, PACK and grant at every site. -/
def BankRepairDigitBankRelated {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z s : BankReferenceState ring hbank) : Prop :=
  z.val.2 = s.val.2 ∧
    ∀ i, bankRepairDigitBankKey (z.val.1 i) = bankRepairDigitBankKey (s.val.1 i) ∧
      (z.val.1 i).grant = (s.val.1 i).grant

theorem bankRepairDigitBankKeyCell {c : Compiled} (a b : Agent c)
    (hk : bankRepairDigitBankKey a = bankRepairDigitBankKey b)
    (hg : a.grant = b.grant) :
    bankCell a a.pack.val = bankCell b b.pack.val ∧ a.pack = b.pack := by
  simp only [bankRepairDigitBankKey, Prod.mk.injEq] at hk
  obtain ⟨hp, hm, hb, ht, hl⟩ := hk
  exact ⟨by simp [bankCell, hp, hm, hb, ht, hl, hg], hp⟩

theorem bankRepairDigitBankRelatedFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z s : BankReferenceState ring hbank)
    (hrel : BankRepairDigitBankRelated ring hbank z s)
    (hz : BankFreshAuthorityAt ring hbank z) :
    BankFreshAuthorityAt ring hbank s := by
  intro e hsucc
  have h := hz e
  obtain ⟨hce, hpe⟩ := bankRepairDigitBankKeyCell _ _ (hrel.2 e).1 (hrel.2 e).2
  obtain ⟨hcj, hpj⟩ := bankRepairDigitBankKeyCell _ _
    (hrel.2 (ring.rightNeighbor e)).1 (hrel.2 (ring.rightNeighbor e)).2
  rw [hce, hcj, hpe, hpj, hrel.1] at h
  exact h hsucc

theorem bankRepairDigitPairMemoryCongr {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n) (e dest : Fin n)
    (x y x' y' : Agent c)
    (hcx : bankCell x x.pack.val = bankCell x' x'.pack.val)
    (hcy : bankCell y y.pack.val = bankCell y' y'.pack.val)
    (hpx : x.pack = x'.pack) (hpy : y.pack = y'.pack) :
    renewalBankPairMemory c m e dest x y = renewalBankPairMemory c m e dest x' y' := by
  unfold renewalBankPairMemory
  rw [hcx, hcy, hpx, hpy]

theorem bankRepairDigitBankRelatedStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z s : BankReferenceState ring hbank)
    (hrel : BankRepairDigitBankRelated ring hbank z s)
    (hgz : NativeLiftGrantFree z.val.1)
    (hfz : BankFreshAuthorityAt ring hbank z) (e : Fin n) :
    BankRepairDigitBankRelated ring hbank
      (bankRepairNext ring hbank z e) (bankRepairNext ring hbank s e) := by
  have hgs : NativeLiftGrantFree s.val.1 := fun i =>
    (hrel.2 i).2.symm.trans (hgz i)
  have hfs := bankRepairDigitBankRelatedFresh ring hbank z s hrel hfz
  have hgz' := bankRepairDigitFreshGrantFreeStep ring hbank z hgz hfz e
  have hgs' := bankRepairDigitFreshGrantFreeStep ring hbank s hgs hfs e
  obtain ⟨hce, hpe⟩ := bankRepairDigitBankKeyCell _ _ (hrel.2 e).1 (hrel.2 e).2
  obtain ⟨hcj, hpj⟩ := bankRepairDigitBankKeyCell _ _
    (hrel.2 (ring.rightNeighbor e)).1 (hrel.2 (ring.rightNeighbor e)).2
  have hpm := bankRepairDigitPairMemoryCongr (compileAdvice (ceilLogTwo n)) s.val.2
    e (ring.rightNeighbor e) (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    (s.val.1 e) (s.val.1 (ring.rightNeighbor e)) hce hcj hpe hpj
  have hmask := bankRepairDigitMaskedBankKey (compileAdvice (ceilLogTwo n)) hbank
    (renewalBankCut ring z.val.1 z.val.2 e) (renewalBankCut ring s.val.1 s.val.2 e)
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    (s.val.1 e) (s.val.1 (ring.rightNeighbor e))
    (hrel.2 e).1 (hrel.2 (ring.rightNeighbor e)).1
    (hrel.2 e).2 (hrel.2 (ring.rightNeighbor e)).2
  refine ⟨?_, ?_⟩
  · change renewalBankMemoryNext ring z.val.1 z.val.2 e =
      renewalBankMemoryNext ring s.val.1 s.val.2 e
    unfold renewalBankMemoryNext
    rw [hrel.1, hpm]
  · intro i
    refine ⟨?_, (hgz' i).trans (hgs' i).symm⟩
    change bankRepairDigitBankKey
        (if i = e then
          (renewalMaskedPair (compileAdvice (ceilLogTwo n))
            (renewalBankCut ring z.val.1 z.val.2 e)
            (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1
         else if i = ring.rightNeighbor e then
          (renewalMaskedPair (compileAdvice (ceilLogTwo n))
            (renewalBankCut ring z.val.1 z.val.2 e)
            (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2
         else z.val.1 i) =
      bankRepairDigitBankKey
        (if i = e then
          (renewalMaskedPair (compileAdvice (ceilLogTwo n))
            (renewalBankCut ring s.val.1 s.val.2 e)
            (s.val.1 e) (s.val.1 (ring.rightNeighbor e))).1
         else if i = ring.rightNeighbor e then
          (renewalMaskedPair (compileAdvice (ceilLogTwo n))
            (renewalBankCut ring s.val.1 s.val.2 e)
            (s.val.1 e) (s.val.1 (ring.rightNeighbor e))).2
         else s.val.1 i)
    exact bankRepairDigitIteFrame bankRepairDigitBankKey _ _ _ _ _ _ _ _
      hmask.1 hmask.2 (hrel.2 i).1

theorem bankRepairDigitBankRelatedRunFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (word : List (Fin n)) :
    ∀ z s : BankReferenceState ring hbank,
      NativeLiftGrantFree z.val.1 →
      InheritedAuthorityExtinct ring hbank z →
      BankRepairDigitBankRelated ring hbank z s →
      BankFreshAuthorityAt ring hbank (bankValidAuthorityRun ring hbank s word) := by
  induction word with
  | nil =>
      intro z s _ hi hrel
      exact bankRepairDigitBankRelatedFresh ring hbank z s hrel (hi [])
  | cons e rest ih =>
      intro z s hg hi hrel
      change BankFreshAuthorityAt ring hbank (bankValidAuthorityRun ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext s e) rest)
      exact ih _ _ (bankExtinctGrantFreeStep ring hbank z hg hi e)
        (inheritedAuthorityExtinctStep ring hbank z hi e)
        (bankRepairDigitBankRelatedStep ring hbank z s hrel hg (hi []) e)

/-- Inherited-authority extinction transfers along the BANK relation. -/
theorem bankRepairDigitBankRelatedExtinct {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z s : BankReferenceState ring hbank)
    (hg : NativeLiftGrantFree z.val.1)
    (hi : InheritedAuthorityExtinct ring hbank z)
    (hrel : BankRepairDigitBankRelated ring hbank z s) :
    InheritedAuthorityExtinct ring hbank s := fun word =>
  bankRepairDigitBankRelatedRunFresh ring hbank word z s hg hi hrel

/-- The scrubbed state (T14) of a prepared state is prepared at the same root. -/
theorem bankRepairDigitScrubbedPrepared {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x) :
    BankPreparedAtSomeRoot ring hbank
      (bankRepairDigitScrubbedEntrance ring hbank x) := by
  obtain ⟨root, ⟨⟨⟨hrooted, hgrant⟩, hiae⟩, hR⟩, hcand⟩ := hx
  exact ⟨root, ⟨⟨⟨hrooted, hgrant⟩,
    bankRepairDigitBankRelatedExtinct ring hbank x _ hgrant hiae
      ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩⟩, hR⟩, hcand⟩

/-- Step 3, piece `DigitBoundaryReceipt`: from any state that is both prepared
and R-fold established, the scrubbed state is a W-stage entrance (empty W
and R words) where every inherited label is gone at the empty word, the
boundary cut fails there (leading-segment writer input `X`, not `E`), and
hence the per-entrance premise fails. -/
theorem bankRepairDigitScrubbedWordStageRefutes {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x)
    (hRx : BankRepairRFoldEstablished ring hbank x) :
    BankPreparedAtSomeRoot ring hbank
        (bankRepairDigitScrubbedEntrance ring hbank x) ∧
      BankRepairWord ring hbank (([] : List (Fin n)).foldl
        (bankRepairNext ring hbank) (bankRepairDigitScrubbedEntrance ring hbank x)) ∧
      BankRepairRFoldEstablished ring hbank (([] : List (Fin n)).foldl
        (bankRepairNext ring hbank) (([] : List (Fin n)).foldl
          (bankRepairNext ring hbank) (bankRepairDigitScrubbedEntrance ring hbank x))) ∧
      bankRepairDigitAllBaseLabelsGone ring hbank
        (([] : List (Fin n)).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (bankRepairDigitScrubbedEntrance ring hbank x,
            digitAuditInitial
              (piD (bankRepairDigitScrubbedEntrance ring hbank x).val.1))) ∧
      ¬ BankRepairDigitBoundaryRetiredCut ring hbank
        (([] : List (Fin n)).foldl (bankRepairNext ring hbank)
          (bankRepairDigitScrubbedEntrance ring hbank x)) ∧
      ¬ BankRepairDigitBaseExtinctionBoundaryAt ring hbank
        (([] : List (Fin n)).foldl (bankRepairNext ring hbank)
          (([] : List (Fin n)).foldl (bankRepairNext ring hbank)
            (bankRepairDigitScrubbedEntrance ring hbank x))) := by
  obtain ⟨hR', hgone, hnot⟩ :=
    bankRepairDigitScrubbedEntranceSeparates ring hbank x hRx
  exact ⟨bankRepairDigitScrubbedPrepared ring hbank x hx, hR'.1.2, hR', hgone, hnot,
    fun h => hnot (h [] hgone)⟩

/-- Step 3 (consequence): the step-1 statement for all W-stage entrances
forces that no state is both prepared and R-fold established. -/
theorem bankRepairDigitBoundaryAtAllWordStageForcesDisjoint {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hall : ∀ x : BankReferenceState ring hbank,
      BankPreparedAtSomeRoot ring hbank x →
      ∀ wordW : List (Fin n),
        BankRepairWord ring hbank (wordW.foldl (bankRepairNext ring hbank) x) →
      ∀ wordR : List (Fin n),
        BankRepairRFoldEstablished ring hbank
          (wordR.foldl (bankRepairNext ring hbank)
            (wordW.foldl (bankRepairNext ring hbank) x)) →
        BankRepairDigitBaseExtinctionBoundaryAt ring hbank
          (wordR.foldl (bankRepairNext ring hbank)
            (wordW.foldl (bankRepairNext ring hbank) x)))
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x) :
    ¬ BankRepairRFoldEstablished ring hbank x := by
  intro hRx
  obtain ⟨hp, hW, hR, _, _, hnot⟩ :=
    bankRepairDigitScrubbedWordStageRefutes ring hbank x hx hRx
  exact hnot (hall _ hp [] hW [] hR)

/-! ### Step 2: boundary clocks at W-stage entrances -/

/-- The W-stage entrance class: an R-fold entrance reached by a W word and an
R word from a prepared state (the history is carried existentially). -/
def BankRepairDigitWordStageEntrance {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (x : BankReferenceState ring hbank) (wordW wordR : List (Fin n)),
    BankPreparedAtSomeRoot ring hbank x ∧
    BankRepairWord ring hbank (wordW.foldl (bankRepairNext ring hbank) x) ∧
    BankRepairRFoldEstablished ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x)) ∧
    z = wordR.foldl (bankRepairNext ring hbank)
      (wordW.foldl (bankRepairNext ring hbank) x)

/-- The boundary cut without the packet receipt. -/
def BankRepairDigitBoundaryExtinctCut {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    BankRepairRFoldEstablished ring hbank start ∧
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) ∧
    WFixedRoot ring root (piW z.val.1) ∧
    DigitAt ring audit audit.clock (piD z.val.1) audit.current ∧
    DigitBaseExtinct ring root audit 0 audit.clock

theorem bankRepairDigitBoundaryExtinctCutOfGone {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (start : BankReferenceState ring hbank)
    (hR : BankRepairRFoldEstablished ring hbank start)
    (hs : BankPostInheritedSingleton ring hbank root start)
    (word : List (Fin n))
    (hgone : bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1)))) :
    BankRepairDigitBoundaryExtinctCut ring hbank
      (word.foldl (bankRepairNext ring hbank) start) := by
  have hinv := bankRepairDigitBoundaryAuditInvariantRun ring hn hbank root start hs word
  have hfirst := bankRepairDigitBoundaryAuditFirst ring hbank start
    (digitAuditInitial (piD start.val.1)) word
  have hat := hinv.2.1
  rw [hfirst] at hat
  refine ⟨start, word, root,
    (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).2, hR, ?_,
    bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root start hs word,
    hat,
    bankRepairDigitBoundaryBaseExtinctOfSingleton ring hn hbank root start hs word hgone⟩
  exact Prod.ext hfirst rfl

/-- Step 2, premise-free: the boundary micro-clock to the receipt-free cut
from every W-stage entrance. -/
theorem bankRepairDigitBoundaryExtinctClockOfWordStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (BankRepairDigitBoundaryExtinctCut ring hbank)
      (bankRepairDigitBoundaryMicroCharge n) := by
  rintro z ⟨x, wordW, wordR, hx, hW, hR, rfl⟩ T
  obtain ⟨root, hs⟩ := bankRepairDigitWordStageSingleton ring hn hbank x hx wordW wordR
  have htasks := bankRepairDigitSingleInheritedLabelTasksOfWordStage
    ring hn hbank x hx wordW hW wordR hR
  exact Nat.le_trans
    (Nat.mul_le_mul_left 2 (bankRepairDigitCostTransfer
      (bankRepairNext ring hbank) (bankRepairDigitBoundaryAuditNext ring hbank)
      (BankRepairDigitBoundaryExtinctCut ring hbank)
      (bankRepairDigitAllBaseLabelsGone ring hbank) T _ _
      (fun word hg => bankRepairDigitBoundaryExtinctCutOfGone ring hn hbank root _
        hR hs word hg)))
    (bankRepairDigitAllBaseFitsBoundaryMicroOfTasks hn ring hbank _ htasks T)

/-- W-stage entrances that satisfy the per-entrance receipt condition. -/
def BankRepairDigitWordStageReceiptEntrance {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairDigitWordStageEntrance ring hbank z ∧
  ∀ word : List (Fin n),
    bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (z, digitAuditInitial (piD z.val.1))) →
    ∀ root : Fin n,
      WFixedRoot ring root (piW (word.foldl (bankRepairNext ring hbank) z).val.1) →
      DigitBoundaryReceipt ring root
        (piD (word.foldl (bankRepairNext ring hbank) z).val.1)

/-- Step 2, full cut: the boundary micro-clock to the boundary-retired cut
from every W-stage entrance satisfying the receipt condition. -/
theorem bankRepairDigitBoundaryClockOfWordStageReceipt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageReceiptEntrance ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank)
      (bankRepairDigitBoundaryMicroCharge n) := by
  apply bankRepairDigitBoundaryClockOfTasksAt ring hn hbank
  · rintro z ⟨⟨x, wordW, wordR, hx, hW, hR, rfl⟩, _⟩
    exact bankRepairDigitSingleInheritedLabelTasksOfWordStage
      ring hn hbank x hx wordW hW wordR hR
  · rintro z ⟨⟨x, wordW, wordR, hx, hW, hR, rfl⟩, hrec⟩
    exact (bankRepairDigitBaseExtinctionBoundaryAtIffReceipt
      ring hn hbank x hx wordW wordR hR).2 hrec

/-- The 201-half composition of `bankRepairDigitPreDrain201OfMicroClocks`,
with the first clock from an arbitrary entrance class instead of all R-fold
entrances. The other three clocks are unchanged. -/
theorem bankRepairDigitPreDrain201OfEntranceClocks {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (entrance : BankReferenceState ring hbank → Prop)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hboundary : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      entrance cuts.boundaryRetired (bankRepairDigitBoundaryMicroCharge n))
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.boundaryRetired cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank) entrance preDrain 201 := by
  have hboundaryZero := bankRepairDigitChargedCompose
    (bankRepairNext ring hbank) entrance
    cuts.boundaryRetired cuts.firstBlockZero
    (bankRepairDigitBoundaryMicroCharge n)
    (bankRepairDigitFirstZeroMicroCharge n)
    hboundary hzero
  have hthroughWave := bankRepairDigitChargedCompose
    (bankRepairNext ring hbank) entrance
    cuts.firstBlockZero cuts.successorValuesStable
    (bankRepairDigitBoundaryMicroCharge n +
      bankRepairDigitFirstZeroMicroCharge n)
    (bankRepairDigitValueWaveMicroCharge n)
    hboundaryZero hwave
  have hall := bankRepairDigitChargedCompose
    (bankRepairNext ring hbank) entrance
    cuts.successorValuesStable preDrain
    (bankRepairDigitBoundaryMicroCharge n +
      bankRepairDigitFirstZeroMicroCharge n +
      bankRepairDigitValueWaveMicroCharge n)
    (bankRepairDigitComparisonMicroCharge n)
    hthroughWave hpair
  intro z hz T
  exact Nat.le_trans (hall z hz T)
    (Nat.mul_le_mul_left (n ^ T)
      (bankRepairDigitMicroChargesFit hn hbank))

/-- The 201-half pre-drain from W-stage receipt entrances, with the first
clock DISCHARGED (boundary cut = `BankRepairDigitBoundaryRetiredCut`). -/
theorem bankRepairDigitPreDrain201OfWordStageReceipt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hcut : cuts.boundaryRetired = BankRepairDigitBoundaryRetiredCut ring hbank)
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.boundaryRetired cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageReceiptEntrance ring hbank) preDrain 201 := by
  have hb : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageReceiptEntrance ring hbank) cuts.boundaryRetired
      (bankRepairDigitBoundaryMicroCharge n) := by
    rw [hcut]
    exact bankRepairDigitBoundaryClockOfWordStageReceipt ring hn hbank
  exact bankRepairDigitPreDrain201OfEntranceClocks ring hn hbank _ cuts preDrain
    hb hzero hwave hpair

/-- The 201-half pre-drain from ALL W-stage entrances, premise-free in the
first clock, when the boundary cut is the receipt-free cut (the receipt
obligation then moves into the first-zero clock). -/
theorem bankRepairDigitPreDrain201OfWordStageExtinct {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hcut : cuts.boundaryRetired = BankRepairDigitBoundaryExtinctCut ring hbank)
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.boundaryRetired cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) preDrain 201 := by
  have hb : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) cuts.boundaryRetired
      (bankRepairDigitBoundaryMicroCharge n) := by
    rw [hcut]
    exact bankRepairDigitBoundaryExtinctClockOfWordStage ring hn hbank
  exact bankRepairDigitPreDrain201OfEntranceClocks ring hn hbank _ cuts preDrain
    hb hzero hwave hpair

end L3.RenewalReferenceClock

/-! ## T16: where the packet-lane receipt comes from (route B)

The receipt is produced later by the literal TOP rows, not carried as an
invariant. Row facts first (`liveTopPair`, composed-full.mjs:523-688):

* WI0/WI3: an initiator writer (comparison) input `X` always becomes `E`;
* an `E` input at a delimiter responder changes only by the accept row
  (`acc`), which delivers a `D` output of the left neighbour as `P`;
* a leader endpoint resets both lanes of both endpoints.

Then the composition: the boundary clock lands in the W-stage gone cut, a
receipt flush clock (the remaining obligation, stated as a nominated-edge task
certificate) reaches the full boundary-retired cut, and the original first-zero
clock continues from there. -/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ### Row facts -/

/-- WI0/WI3 (and the leader row): an initiator writer input `X` is cleared. -/
theorem bankRepairDigitWriterXClears (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (h : ox.wIn = .X) :
    (liveTopPair c ox oy bx bY).x.wIn = .E := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  by_cases hr : (ox.l || oy.l) = true
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr]
  · cases hc : ox.wCarry <;> cases hc2 : oy.wCarry <;> cases hi2 : oy.wIn <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr, h, hc,
          hc2, hi2, InTok.isX, InTok.isS, InTok.isP, WCarry.isOff, WCarry.isW,
          InTok.isE] <;> split <;> rfl

/-- The same row on the comparison lane. -/
theorem bankRepairDigitComparisonXClears (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (h : ox.qIn = .X) :
    (liveTopPair c ox oy bx bY).x.qIn = .E := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  by_cases hr : (ox.l || oy.l) = true
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr]
  · cases hc : ox.qCarry <;> cases hc2 : oy.qCarry <;> cases hi2 : oy.qIn <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr, h, hc,
          hc2, hi2, InTok.isX, InTok.isS, InTok.isP, QCarry.isOff, QCarry.isL,
          InTok.isE] <;> split <;> rfl

/-- With input `X`, no writer carry is launched (WC3 needs an `S` input). -/
theorem bankRepairDigitWriterXCarryOff (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (h : ox.wIn = .X) (hc : ox.wCarry = .OFF) :
    (liveTopPair c ox oy bx bY).x.wCarry = .OFF := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  by_cases hr : (ox.l || oy.l) = true
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr, hc,
      WCarry.isW]
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr, h, hc,
      InTok.isS, WCarry.isW, WCarry.isOff]

/-- Delimiter protection, writer lane (resolved responder marker true): an
`E` input at the responder stays `E` unless the accept row delivers the
initiator's `D` output as `P`. -/
theorem bankRepairDigitWriterDelimiterInput (c : Compiled) (ox oy : Agent c)
    (bx : Bool) (hy : oy.wIn = .E) :
    (liveTopPair c ox oy bx true).y.wIn = .E ∨
      (ox.wOut.isD = true ∧
        (liveTopPair c ox oy bx true).y.wIn = .P (outV c ox.wOut) (outT ox.wOut)) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  by_cases hr : (ox.l || oy.l) = true
  · left
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr]
  · cases ho : ox.wOut <;> cases hi : ox.wIn <;> cases hc : ox.wCarry <;>
      cases hc2 : oy.wCarry <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr, hy, ho,
          hi, hc, hc2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW,
          OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder] <;>
      (repeat' split) <;> simp_all

/-- Delimiter protection, comparison lane (old responder marker true). -/
theorem bankRepairDigitComparisonDelimiterInput (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hb : oy.beta = true) (hy : oy.qIn = .E) :
    (liveTopPair c ox oy bx bY).y.qIn = .E ∨
      (ox.qOut.isD = true ∧
        (liveTopPair c ox oy bx bY).y.qIn = .P (outV c ox.qOut) (outT ox.qOut)) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  by_cases hr : (ox.l || oy.l) = true
  · left
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr]
  · cases ho : ox.qOut <;> cases hi : ox.qIn <;> cases hc : ox.qCarry <;>
      cases hc2 : oy.qCarry <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr, hy, hb,
          ho, hi, hc, hc2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL,
          OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder] <;>
      (repeat' split) <;> simp_all

/-- A leader endpoint resets inputs, outputs and carries of both lanes at
both endpoints. -/
theorem bankRepairDigitRootEdgeResets (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hr : (ox.l || oy.l) = true) :
    (liveTopPair c ox oy bx bY).x.wIn = .E ∧ (liveTopPair c ox oy bx bY).y.wIn = .E ∧
    (liveTopPair c ox oy bx bY).x.wOut = .E ∧ (liveTopPair c ox oy bx bY).y.wOut = .E ∧
    (liveTopPair c ox oy bx bY).x.wCarry = .OFF ∧
    (liveTopPair c ox oy bx bY).y.wCarry = .OFF ∧
    (liveTopPair c ox oy bx bY).x.qIn = .E ∧ (liveTopPair c ox oy bx bY).y.qIn = .E ∧
    (liveTopPair c ox oy bx bY).x.qOut = .E ∧ (liveTopPair c ox oy bx bY).y.qOut = .E ∧
    (liveTopPair c ox oy bx bY).x.qCarry = .OFF ∧
    (liveTopPair c ox oy bx bY).y.qCarry = .OFF := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases h1 : ox.wCarry <;> cases h2 : oy.wCarry <;> cases h3 : ox.qCarry <;>
    cases h4 : oy.qCarry <;>
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hr, h1, h2,
        h3, h4, WCarry.isW, QCarry.isL]

/-- The initiator's top fields after a no-FIRE BANK edge are the literal
`liveTopPair` x-row on the projected endpoints. -/
theorem bankRepairDigitSiteTopX {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hfire : oldFire (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) = none) :
    (piD (bankRepairNext ring hbank z e).val.1 e).top =
      (topD (piD z.val.1 e) (piD z.val.1 (ring.rightNeighbor e))).x := by
  rw [bankRepairDigitMaskedProjectionOfNoFire ring hbank z e hfire]
  simp [phiD, projectedEdge, pairD]

/-- On the singleton class, one edge at a site whose writer input is `X`
clears it to `E`, and an `OFF` writer carry stays `OFF`. -/
theorem bankRepairDigitWriterXClearsAtSite {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedSingleton ring hbank root z) (i : Fin n)
    (hX : (z.val.1 i).wIn = .X) :
    ((bankRepairNext ring hbank z i).val.1 i).wIn = .E ∧
      ((z.val.1 i).wCarry = .OFF →
        ((bankRepairNext ring hbank z i).val.1 i).wCarry = .OFF) := by
  have htop := bankRepairDigitSiteTopX ring hbank z i
    (bankRepairDigitBoundaryNoFireOfSingleton ring hbank root z hz i)
  refine ⟨?_, fun hc => ?_⟩
  · have h1 := congrArg TopFields.wIn htop
    change ((bankRepairNext ring hbank z i).val.1 i).wIn = _ at h1
    rw [h1]
    exact bankRepairDigitWriterXClears _ _ _ _ _ hX
  · have h1 := congrArg TopFields.wCarry htop
    change ((bankRepairNext ring hbank z i).val.1 i).wCarry = _ at h1
    rw [h1]
    exact bankRepairDigitWriterXCarryOff _ _ _ _ _ hX hc

/-- Route B on the T15 counterexample: from the scrubbed entrance, one edge at
any site (in particular the first delimiter) restores writer input `E` with
writer carry `OFF` there, which is exactly the receipt conjunct that failed. -/
theorem bankRepairDigitScrubbedObstructionClears {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : BankReferenceState ring hbank)
    (hx : BankPreparedAtSomeRoot ring hbank x) (i : Fin n) :
    ((bankRepairNext ring hbank
        (bankRepairDigitScrubbedEntrance ring hbank x) i).val.1 i).wIn = .E ∧
      ((bankRepairNext ring hbank
        (bankRepairDigitScrubbedEntrance ring hbank x) i).val.1 i).wCarry = .OFF := by
  obtain ⟨root, hs, _⟩ := bankRepairDigitScrubbedPrepared ring hbank x hx
  have h := bankRepairDigitWriterXClearsAtSite ring hbank root _ hs i rfl
  exact ⟨h.1, h.2 rfl⟩

/-! ### The gone cut and the receipt flush interface -/

/-- A state reached from a W-stage entrance by a word at which every inherited
base label is gone; the prepared history is carried. -/
def BankRepairDigitWordStageGoneCut {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (x : BankReferenceState ring hbank) (wordW wordR word : List (Fin n)),
    BankPreparedAtSomeRoot ring hbank x ∧
    BankRepairWord ring hbank (wordW.foldl (bankRepairNext ring hbank) x) ∧
    BankRepairRFoldEstablished ring hbank
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x)) ∧
    bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (wordR.foldl (bankRepairNext ring hbank)
            (wordW.foldl (bankRepairNext ring hbank) x),
          digitAuditInitial (piD (wordR.foldl (bankRepairNext ring hbank)
            (wordW.foldl (bankRepairNext ring hbank) x)).val.1))) ∧
    z = word.foldl (bankRepairNext ring hbank)
      (wordR.foldl (bankRepairNext ring hbank)
        (wordW.foldl (bankRepairNext ring hbank) x))

theorem bankRepairDigitWordStageGoneExtinct {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitWordStageGoneCut ring hbank z) :
    BankRepairDigitBoundaryExtinctCut ring hbank z := by
  obtain ⟨x, wordW, wordR, word, hx, _hW, hR, hg, rfl⟩ := hz
  obtain ⟨root, hs⟩ := bankRepairDigitWordStageSingleton ring hn hbank x hx wordW wordR
  exact bankRepairDigitBoundaryExtinctCutOfGone ring hn hbank root _ hR hs word hg

/-- The premise-free boundary micro-clock, landing in the gone cut. -/
theorem bankRepairDigitWordStageGoneClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (BankRepairDigitWordStageGoneCut ring hbank)
      (bankRepairDigitBoundaryMicroCharge n) := by
  rintro z ⟨x, wordW, wordR, hx, hW, hR, rfl⟩ T
  have htasks := bankRepairDigitSingleInheritedLabelTasksOfWordStage
    ring hn hbank x hx wordW hW wordR hR
  exact Nat.le_trans
    (Nat.mul_le_mul_left 2 (bankRepairDigitCostTransfer
      (bankRepairNext ring hbank) (bankRepairDigitBoundaryAuditNext ring hbank)
      (BankRepairDigitWordStageGoneCut ring hbank)
      (bankRepairDigitAllBaseLabelsGone ring hbank) T _ _
      (fun word hg => ⟨x, wordW, wordR, word, hx, hW, hR, hg, rfl⟩)))
    (bankRepairDigitAllBaseFitsBoundaryMicroOfTasks hn ring hbank _ htasks T)

/-- States reachable from the gone cut. -/
def BankRepairDigitGoneReachable {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (z₀ : BankReferenceState ring hbank) (word : List (Fin n)),
    BankRepairDigitWordStageGoneCut ring hbank z₀ ∧
    z = word.foldl (bankRepairNext ring hbank) z₀

/-- THE REMAINING ROUTE-B OBLIGATION, as a finite task certificate: a flush
rank on states reachable from the gone cut that never increases and drops on a
nominated actual edge until the full boundary-retired cut (receipt included)
is hit, with initial rank at most `budget`. -/
def BankRepairDigitReceiptFlushTasks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (budget : Nat) : Prop :=
  ∃ (rank : BankReferenceState ring hbank → Nat)
    (chosen : BankReferenceState ring hbank → Fin n),
    (∀ z, BankRepairDigitGoneReachable ring hbank z →
      ¬ BankRepairDigitBoundaryRetiredCut ring hbank z →
      rank (bankRepairNext ring hbank z (chosen z)) + 1 ≤ rank z) ∧
    (∀ z, BankRepairDigitGoneReachable ring hbank z →
      ¬ BankRepairDigitBoundaryRetiredCut ring hbank z →
      ∀ e : Fin n, rank (bankRepairNext ring hbank z e) ≤ rank z) ∧
    (∀ z, BankRepairDigitWordStageGoneCut ring hbank z → rank z ≤ budget)

/-- The receipt flush clock: from the gone cut to the full boundary cut. -/
def BankRepairDigitReceiptFlushClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (charge : Nat) : Prop :=
  BankRepairDigitChargedStage (bankRepairNext ring hbank)
    (BankRepairDigitWordStageGoneCut ring hbank)
    (BankRepairDigitBoundaryRetiredCut ring hbank) charge

/-- A flush task certificate gives the flush clock at charge `2 n budget`. -/
theorem bankRepairDigitReceiptFlushClockOfTasks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (budget : Nat)
    (htasks : BankRepairDigitReceiptFlushTasks ring hbank budget) :
    BankRepairDigitReceiptFlushClock ring hbank (2 * (n * budget)) := by
  obtain ⟨rank, chosen, hdrop, hnoninc, hcap⟩ := htasks
  intro z hz T
  have hclosed : ∀ y, BankRepairDigitGoneReachable ring hbank y →
      ¬ BankRepairDigitBoundaryRetiredCut ring hbank y → ∀ e : Fin n,
      BankRepairDigitGoneReachable ring hbank (bankRepairNext ring hbank y e) := by
    rintro y ⟨z₀, word, hz₀, rfl⟩ _ e
    refine ⟨z₀, word ++ [e], hz₀, ?_⟩
    rw [List.foldl_append]
    rfl
  have hsplit : ∀ y, ¬ (BankRepairDigitBoundaryRetiredCut ring hbank y ∨
      ¬ BankRepairDigitGoneReachable ring hbank y) →
      BankRepairDigitGoneReachable ring hbank y ∧
        ¬ BankRepairDigitBoundaryRetiredCut ring hbank y := fun y h =>
    ⟨Classical.byContradiction (fun hb => h (Or.inr hb)), fun ha => h (Or.inl ha)⟩
  have hcost := L3.Prob.costNumerator_le_of_nominated_edge
    (bankRepairNext ring hbank)
    (fun y => BankRepairDigitBoundaryRetiredCut ring hbank y ∨
      ¬ BankRepairDigitGoneReachable ring hbank y) rank chosen
    (fun y hy => hdrop y (hsplit y hy).1 (hsplit y hy).2)
    (fun y hy => hnoninc y (hsplit y hy).1 (hsplit y hy).2) z T
  have hreach : ∀ w : List (Fin n), BankRepairDigitGoneReachable ring hbank
      (w.foldl (bankRepairNext ring hbank) z) := fun w => ⟨z, w, hz, rfl⟩
  have htransfer := bankRepairDigitCostTransfer (bankRepairNext ring hbank)
    (bankRepairNext ring hbank) (BankRepairDigitBoundaryRetiredCut ring hbank)
    (fun y => BankRepairDigitBoundaryRetiredCut ring hbank y ∨
      ¬ BankRepairDigitGoneReachable ring hbank y) T z z
    (fun w hw => hw.resolve_right (fun hn' => hn' (hreach w)))
  have hle : costNumerator (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) z T ≤
      n ^ T * (n * budget) :=
    Nat.le_trans htransfer (Nat.le_trans hcost
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hcap z hz))))
  calc
    2 * costNumerator (bankRepairNext ring hbank)
        (BankRepairDigitBoundaryRetiredCut ring hbank) z T ≤
        2 * (n ^ T * (n * budget)) := Nat.mul_le_mul_left 2 hle
    _ = n ^ T * (2 * (n * budget)) := Nat.mul_left_comm _ _ _

/-- The strengthened first-zero clock (route B): from the gone cut, flush the
receipt, then run the ORIGINAL first-zero clock from the full boundary cut. -/
theorem bankRepairDigitFirstZeroOfReceiptFlush {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank) (charge : Nat)
    (hflush : BankRepairDigitReceiptFlushClock ring hbank charge)
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageGoneCut ring hbank) cuts.firstBlockZero
      (charge + bankRepairDigitFirstZeroMicroCharge n) :=
  bankRepairDigitChargedCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageGoneCut ring hbank)
    (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
    charge (bankRepairDigitFirstZeroMicroCharge n) hflush hzero

/-- The 201-half pre-drain from every W-stage entrance, with the boundary
clock discharged (premise-free) and the receipt carried by the flush clock.
The other clocks are the original ones (first-zero from the FULL boundary
cut). `hfit` is the room the flush charge needs inside the single n^2. -/
theorem bankRepairDigitPreDrain201OfReceiptFlush {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop) (charge : Nat)
    (hfit : bankRepairDigitBoundaryMicroCharge n + charge +
        bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitComparisonMicroCharge n ≤ n ^ 2)
    (hflush : BankRepairDigitReceiptFlushClock ring hbank charge)
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) preDrain 201 := by
  have hzero' := bankRepairDigitFirstZeroOfReceiptFlush ring hbank cuts charge
    hflush hzero
  have h1 := bankRepairDigitChargedCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    (BankRepairDigitWordStageGoneCut ring hbank) cuts.firstBlockZero
    (bankRepairDigitBoundaryMicroCharge n)
    (charge + bankRepairDigitFirstZeroMicroCharge n)
    (bankRepairDigitWordStageGoneClock ring hn hbank) hzero'
  have h2 := bankRepairDigitChargedCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    cuts.firstBlockZero cuts.successorValuesStable _
    (bankRepairDigitValueWaveMicroCharge n) h1 hwave
  have h3 := bankRepairDigitChargedCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    cuts.successorValuesStable preDrain _
    (bankRepairDigitComparisonMicroCharge n) h2 hpair
  intro z hz T
  refine Nat.le_trans (h3 z hz T) (Nat.mul_le_mul_left (n ^ T) ?_)
  unfold bankRepairDigitValueWaveMicroCharge
  omega

/-- The same, from a flush task certificate with budget `budget`. -/
theorem bankRepairDigitPreDrain201OfFlushTasks {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop) (budget : Nat)
    (hfit : bankRepairDigitBoundaryMicroCharge n + 2 * (n * budget) +
        bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitComparisonMicroCharge n ≤ n ^ 2)
    (htasks : BankRepairDigitReceiptFlushTasks ring hbank budget)
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) preDrain 201 :=
  bankRepairDigitPreDrain201OfReceiptFlush ring hn hbank cuts preDrain _ hfit
    (bankRepairDigitReceiptFlushClockOfTasks ring hbank budget htasks)
    hzero hwave hpair

/-! ### Receipt stability: once produced, the receipt is never lost

Local row facts (`liveTopPair`, both lanes) for each adjacent role pair of the
leading prefix, the first segment and the final region, then the global step
on the projected ring, then the actual BANK chain on the layout-fixed class
(singleton class plus `Q_W`, which fixes every marker). -/

theorem bankRepairDigitWriterKeepX (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hl : ox.l = false) (hc : ox.wCarry = .OFF)
    (hi : ox.wIn = .E ∨ ((∃ v, ox.wIn = .S v false) ∧ bx = false)) :
    (liveTopPair c ox oy bx bY).x.wCarry = .OFF ∧
    ((liveTopPair c ox oy bx bY).x.wIn = ox.wIn ∨
      (liveTopPair c ox oy bx bY).x.wIn = .E) ∧
    (ox.wOut = .E → bx = false → (liveTopPair c ox oy bx bY).x.wOut = .E) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  by_cases hr : oy.l = true
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr, hc,
      WCarry.isW]
  · have hr' : oy.l = false := by simpa using hr
    rcases hi with hi | ⟨⟨v, hi⟩, hbx⟩
    · cases ho : ox.wOut <;> cases hc2 : oy.wCarry <;> cases hi2 : oy.wIn <;>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr',
            hc, hi, ho, hc2, hi2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, WCarry.isOff,
            WCarry.isW, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder] <;>
        (repeat' split) <;> simp_all
    · cases ho : ox.wOut <;> cases hc2 : oy.wCarry <;> cases hi2 : oy.wIn <;>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr',
            hc, hi, hbx, ho, hc2, hi2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, WCarry.isOff,
            WCarry.isW, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder,
            inT] <;>
        (repeat' split) <;> simp_all

theorem bankRepairDigitWriterFinalX (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hl : ox.l = false) (hc : ox.wCarry = .OFF)
    (hi : ox.wIn = .E ∨ ∃ v T, ox.wIn = .P v T)
    (hy : oy.l = true ∨
      (bY = false ∧ (oy.wCarry = .OFF → ∀ v T, oy.wIn ≠ .S v T))) :
    (liveTopPair c ox oy bx bY).x.wCarry = .OFF ∧
    ((liveTopPair c ox oy bx bY).x.wIn = .E ∨
      ∃ v T, (liveTopPair c ox oy bx bY).x.wIn = .P v T) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  rcases hy with hr | ⟨hbY, hyS⟩
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr, hc,
      WCarry.isW]
  · by_cases hr : oy.l = true
    · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr, hc,
        WCarry.isW]
    · have hr' : oy.l = false := by simpa using hr
      rcases hi with hi | ⟨v, T, hi⟩
      · cases hc2 : oy.wCarry <;> cases hi2 : oy.wIn <;>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn,
              ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
              ↓liveTopPair_y_qOut, liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
              liveTopPair, hl, hr', hc, hi, hbY, hc2, hi2, InTok.isX, InTok.isS, InTok.isP,
              InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD, OutTok.isU, OutTok.isE, topInternal,
              topTerminal, topBorder] <;>
          (repeat' split) <;> simp_all
      · cases hc2 : oy.wCarry <;> cases hi2 : oy.wIn <;>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn,
              ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
              ↓liveTopPair_y_qOut, liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
              liveTopPair, hl, hr', hc, hi, hbY, hc2, hi2, InTok.isX, InTok.isS, InTok.isP,
              InTok.isE, WCarry.isOff, WCarry.isW, OutTok.isD, OutTok.isU, OutTok.isE, topInternal,
              topTerminal, topBorder] at hyS ⊢ <;>
          (repeat' split) <;> simp_all

theorem bankRepairDigitWriterKeepY (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hl : ox.l = false) (hly : oy.l = false)
    (hc : ox.wCarry = .OFF) (hiX : ox.wIn ≠ .X) (hiP : ∀ v T, ox.wIn ≠ .P v T)
    (ho : ox.wOut.isD = true → bY = false) :
    (liveTopPair c ox oy bx bY).y.wCarry = oy.wCarry ∧
    ((liveTopPair c ox oy bx bY).y.wIn = oy.wIn ∨
      (liveTopPair c ox oy bx bY).y.wIn = .E) ∧
    (ox.wOut.isD = false → (liveTopPair c ox oy bx bY).y.wOut = oy.wOut) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hi : ox.wIn with
  | X => exact absurd hi hiX
  | P v T => exact absurd hi (hiP v T)
  | E =>
      cases ho' : ox.wOut <;> cases hc2 : oy.wCarry <;> cases hi2 : oy.wIn <;>
        cases hbY : bY <;>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly,
            hc, hi, ho', hc2, hi2, hbY, InTok.isX, InTok.isS, InTok.isP, InTok.isE, WCarry.isOff,
            WCarry.isW, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal,
            topBorder] at ho ⊢ <;>
        (repeat' split) <;> simp_all
  | S v T =>
      cases ho' : ox.wOut <;> cases hc2 : oy.wCarry <;> cases hi2 : oy.wIn <;>
        cases hbY : bY <;>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly,
            hc, hi, ho', hc2, hi2, hbY, InTok.isX, InTok.isS, InTok.isP, InTok.isE, WCarry.isOff,
            WCarry.isW, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal,
            topBorder] at ho ⊢ <;>
        (repeat' split) <;> simp_all

theorem bankRepairDigitWriterFinalY (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hl : ox.l = false) (hly : oy.l = false)
    (hx : bY = true ∨
      (ox.wCarry = .OFF ∧ ox.wIn ≠ .X ∧ ∀ v T, ox.wIn ≠ .S v T)) :
    (liveTopPair c ox oy bx bY).y.wCarry = oy.wCarry ∧
    ((liveTopPair c ox oy bx bY).y.wIn = oy.wIn ∨
      (liveTopPair c ox oy bx bY).y.wIn = .E ∨
      ((liveTopPair c ox oy bx bY).y.wIn).isP = true) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  rcases hx with hbY | ⟨hc, hiX, hiS⟩
  · cases hc : ox.wCarry <;> cases hi : ox.wIn <;> cases hc2 : oy.wCarry <;>
      cases hi2 : oy.wIn <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly,
          hc, hi, hbY, hc2, hi2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, WCarry.isOff,
          WCarry.isW, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder] <;>
      (repeat' split) <;> simp_all
  · cases hi : ox.wIn with
    | X => exact absurd hi hiX
    | S v T => exact absurd hi (hiS v T)
    | E =>
        cases hc2 : oy.wCarry <;> cases hi2 : oy.wIn <;> cases bY <;>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn,
              ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
              ↓liveTopPair_y_qOut, liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
              liveTopPair, hl, hly, hc, hi, hc2, hi2, InTok.isX, InTok.isS, InTok.isP, InTok.isE,
              WCarry.isOff, WCarry.isW, OutTok.isD, OutTok.isU, OutTok.isE, topInternal,
              topTerminal, topBorder] <;>
          (repeat' split) <;> simp_all
    | P v T =>
        cases hc2 : oy.wCarry <;> cases hi2 : oy.wIn <;> cases bY <;>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn,
              ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
              ↓liveTopPair_y_qOut, liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
              liveTopPair, hl, hly, hc, hi, hc2, hi2, InTok.isX, InTok.isS, InTok.isP, InTok.isE,
              WCarry.isOff, WCarry.isW, OutTok.isD, OutTok.isU, OutTok.isE, topInternal,
              topTerminal, topBorder] <;>
          (repeat' split) <;> simp_all

theorem bankRepairDigitComparisonKeepX (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hl : ox.l = false) (hc : ox.qCarry = .OFF)
    (hi : ox.qIn = .E ∨ ((∃ v, ox.qIn = .S v false) ∧ ox.beta = false)) :
    (liveTopPair c ox oy bx bY).x.qCarry = .OFF ∧
    ((liveTopPair c ox oy bx bY).x.qIn = ox.qIn ∨
      (liveTopPair c ox oy bx bY).x.qIn = .E) ∧
    (ox.qOut = .E → ox.beta = false → (liveTopPair c ox oy bx bY).x.qOut = .E) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  by_cases hr : oy.l = true
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr, hc,
      QCarry.isL]
  · have hr' : oy.l = false := by simpa using hr
    rcases hi with hi | ⟨⟨v, hi⟩, hbx⟩
    · cases ho : ox.qOut <;> cases hc2 : oy.qCarry <;> cases hi2 : oy.qIn <;>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr',
            hc, hi, ho, hc2, hi2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, QCarry.isOff,
            QCarry.isL, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder] <;>
        (repeat' split) <;> simp_all
    · cases ho : ox.qOut <;> cases hc2 : oy.qCarry <;> cases hi2 : oy.qIn <;>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr',
            hc, hi, hbx, ho, hc2, hi2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, QCarry.isOff,
            QCarry.isL, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder,
            inT] <;>
        (repeat' split) <;> simp_all

theorem bankRepairDigitComparisonFinalX (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hl : ox.l = false) (hc : ox.qCarry = .OFF)
    (hi : ox.qIn = .E ∨ ∃ v T, ox.qIn = .P v T)
    (hy : oy.l = true ∨
      (oy.beta = false ∧ (oy.qCarry = .OFF → ∀ v T, oy.qIn ≠ .S v T))) :
    (liveTopPair c ox oy bx bY).x.qCarry = .OFF ∧
    ((liveTopPair c ox oy bx bY).x.qIn = .E ∨
      ∃ v T, (liveTopPair c ox oy bx bY).x.qIn = .P v T) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  rcases hy with hr | ⟨hbY, hyS⟩
  · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
      ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
      ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
      liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr, hc,
      QCarry.isL]
  · by_cases hr : oy.l = true
    · simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hr, hc,
        QCarry.isL]
    · have hr' : oy.l = false := by simpa using hr
      rcases hi with hi | ⟨v, T, hi⟩
      · cases hc2 : oy.qCarry <;> cases hi2 : oy.qIn <;>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn,
              ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
              ↓liveTopPair_y_qOut, liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
              liveTopPair, hl, hr', hc, hi, hbY, hc2, hi2, InTok.isX, InTok.isS, InTok.isP,
              InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD, OutTok.isU, OutTok.isE, topInternal,
              topTerminal, topBorder] <;>
          (repeat' split) <;> simp_all
      · cases hc2 : oy.qCarry <;> cases hi2 : oy.qIn <;>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn,
              ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
              ↓liveTopPair_y_qOut, liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
              liveTopPair, hl, hr', hc, hi, hbY, hc2, hi2, InTok.isX, InTok.isS, InTok.isP,
              InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD, OutTok.isU, OutTok.isE, topInternal,
              topTerminal, topBorder] at hyS ⊢ <;>
          (repeat' split) <;> simp_all

theorem bankRepairDigitComparisonKeepY (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hl : ox.l = false) (hly : oy.l = false)
    (hc : ox.qCarry = .OFF) (hiX : ox.qIn ≠ .X) (hiP : ∀ v T, ox.qIn ≠ .P v T)
    (ho : ox.qOut.isD = true → oy.beta = false) :
    (liveTopPair c ox oy bx bY).y.qCarry = oy.qCarry ∧
    ((liveTopPair c ox oy bx bY).y.qIn = oy.qIn ∨
      (liveTopPair c ox oy bx bY).y.qIn = .E) ∧
    (ox.qOut.isD = false → (liveTopPair c ox oy bx bY).y.qOut = oy.qOut) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hi : ox.qIn with
  | X => exact absurd hi hiX
  | P v T => exact absurd hi (hiP v T)
  | E =>
      cases ho' : ox.qOut <;> cases hc2 : oy.qCarry <;> cases hi2 : oy.qIn <;>
        cases hbY : oy.beta <;>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly,
            hc, hi, ho', hc2, hi2, hbY, InTok.isX, InTok.isS, InTok.isP, InTok.isE, QCarry.isOff,
            QCarry.isL, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal,
            topBorder] at ho ⊢ <;>
        (repeat' split) <;> simp_all
  | S v T =>
      cases ho' : ox.qOut <;> cases hc2 : oy.qCarry <;> cases hi2 : oy.qIn <;>
        cases hbY : oy.beta <;>
        simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
            ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
            ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
            liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly,
            hc, hi, ho', hc2, hi2, hbY, InTok.isX, InTok.isS, InTok.isP, InTok.isE, QCarry.isOff,
            QCarry.isL, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal,
            topBorder] at ho ⊢ <;>
        (repeat' split) <;> simp_all

theorem bankRepairDigitComparisonFinalY (c : Compiled) (ox oy : Agent c)
    (bx bY : Bool) (hl : ox.l = false) (hly : oy.l = false)
    (hx : oy.beta = true ∨
      (ox.qCarry = .OFF ∧ ox.qIn ≠ .X ∧ ∀ v T, ox.qIn ≠ .S v T)) :
    (liveTopPair c ox oy bx bY).y.qCarry = oy.qCarry ∧
    ((liveTopPair c ox oy bx bY).y.qIn = oy.qIn ∨
      (liveTopPair c ox oy bx bY).y.qIn = .E ∨
      ((liveTopPair c ox oy bx bY).y.qIn).isP = true) := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  rcases hx with hbY | ⟨hc, hiX, hiS⟩
  · cases hc : ox.qCarry <;> cases hi : ox.qIn <;> cases hc2 : oy.qCarry <;>
      cases hi2 : oy.qIn <;>
      simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
          ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
          ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
          liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly,
          hc, hi, hbY, hc2, hi2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, QCarry.isOff,
          QCarry.isL, OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder] <;>
      (repeat' split) <;> simp_all
  · cases hi : ox.qIn with
    | X => exact absurd hi hiX
    | S v T => exact absurd hi (hiS v T)
    | E =>
        cases hc2 : oy.qCarry <;> cases hi2 : oy.qIn <;> cases hbY : oy.beta <;>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn,
              ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
              ↓liveTopPair_y_qOut, liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
              liveTopPair, hl, hly, hc, hi, hbY, hc2, hi2, InTok.isX, InTok.isS, InTok.isP,
              InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD, OutTok.isU, OutTok.isE, topInternal,
              topTerminal, topBorder] <;>
          (repeat' split) <;> simp_all
    | P v T =>
        cases hc2 : oy.qCarry <;> cases hi2 : oy.qIn <;> cases hbY : oy.beta <;>
          simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry,
              ↓liveTopPair_y_wCarry, ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn,
              ↓liveTopPair_y_qIn, ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut,
              ↓liveTopPair_y_qOut, liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO,
              liveTopPair, hl, hly, hc, hi, hbY, hc2, hi2, InTok.isX, InTok.isS, InTok.isP,
              InTok.isE, QCarry.isOff, QCarry.isL, OutTok.isD, OutTok.isU, OutTok.isE, topInternal,
              topTerminal, topBorder] <;>
          (repeat' split) <;> simp_all

def bankRepairDigitLaneIn {c : Compiled} (lane : DigitLane) (f : TopFields c) :
    InTok c.topA :=
  match lane with
  | .writer => f.wIn
  | .comparison => f.qIn

def bankRepairDigitLaneOut {c : Compiled} (lane : DigitLane) (f : TopFields c) :
    OutTok c.topA :=
  match lane with
  | .writer => f.wOut
  | .comparison => f.qOut

def bankRepairDigitLaneLive {c : Compiled} (lane : DigitLane) (f : TopFields c) : Bool :=
  match lane with
  | .writer => f.wCarry.isW
  | .comparison => f.qCarry.isL

theorem bankRepairDigitEndpointViewLane {c : Compiled} {n : Nat} (lane : DigitLane)
    (S : Fin n → ProjD c) (i : Fin n) :
    (digitEndpointView lane S i).input = bankRepairDigitLaneIn lane (S i).top ∧
    (digitEndpointView lane S i).out = bankRepairDigitLaneOut lane (S i).top ∧
    (digitEndpointView lane S i).carryLive = bankRepairDigitLaneLive lane (S i).top := by
  cases lane <;> exact ⟨rfl, rfl, rfl⟩

/-- The literal top row of a projected pair, read with the OLD markers. -/
def bankRepairDigitTopPairOf (c : Compiled) (x y : ProjD c) : TopResult c :=
  liveTopPair c x.lift y.lift x.word.beta y.word.beta

/-- The five lane-generic local row facts used by receipt stability. -/
def BankRepairDigitLaneRowFacts (c : Compiled) : Prop :=
  (∀ (lane : DigitLane) (x y : ProjD c),
    x.word.native.l = false →
    bankRepairDigitLaneLive lane x.top = false →
    (bankRepairDigitLaneIn lane x.top = .E ∨
      ((∃ v, bankRepairDigitLaneIn lane x.top = .S v false) ∧ x.word.beta = false)) →
    bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).x = false ∧
    (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x =
        bankRepairDigitLaneIn lane x.top ∨
      bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x = .E) ∧
    (bankRepairDigitLaneOut lane x.top = .E → x.word.beta = false →
      bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).x = .E)) ∧
  (∀ (lane : DigitLane) (x y : ProjD c),
    x.word.native.l = false →
    bankRepairDigitLaneLive lane x.top = false →
    (bankRepairDigitLaneIn lane x.top = .E ∨
      ∃ v T, bankRepairDigitLaneIn lane x.top = .P v T) →
    (y.word.native.l = true ∨
      (y.word.beta = false ∧ (bankRepairDigitLaneLive lane y.top = false →
        ∀ v T, bankRepairDigitLaneIn lane y.top ≠ .S v T))) →
    bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).x = false ∧
    (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x = .E ∨
      ∃ v T, bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x = .P v T)) ∧
  (∀ (lane : DigitLane) (x y : ProjD c),
    x.word.native.l = false → y.word.native.l = false →
    bankRepairDigitLaneLive lane x.top = false →
    bankRepairDigitLaneIn lane x.top ≠ .X →
    (∀ v T, bankRepairDigitLaneIn lane x.top ≠ .P v T) →
    ((bankRepairDigitLaneOut lane x.top).isD = true → y.word.beta = false) →
    bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).y =
        bankRepairDigitLaneLive lane y.top ∧
    (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y =
        bankRepairDigitLaneIn lane y.top ∨
      bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y = .E) ∧
    ((bankRepairDigitLaneOut lane x.top).isD = false →
      bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).y =
        bankRepairDigitLaneOut lane y.top)) ∧
  (∀ (lane : DigitLane) (x y : ProjD c),
    x.word.native.l = false → y.word.native.l = false →
    (y.word.beta = true ∨
      (bankRepairDigitLaneLive lane x.top = false ∧
        bankRepairDigitLaneIn lane x.top ≠ .X ∧
        ∀ v T, bankRepairDigitLaneIn lane x.top ≠ .S v T)) →
    bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).y =
        bankRepairDigitLaneLive lane y.top ∧
    (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y =
        bankRepairDigitLaneIn lane y.top ∨
      bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y = .E ∨
      (bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y).isP = true)) ∧
  (∀ (lane : DigitLane) (x y : ProjD c),
    (x.word.native.l || y.word.native.l) = true →
    bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).x = .E ∧
    bankRepairDigitLaneIn lane (bankRepairDigitTopPairOf c x y).y = .E ∧
    bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).x = .E ∧
    bankRepairDigitLaneOut lane (bankRepairDigitTopPairOf c x y).y = .E ∧
    bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).x = false ∧
    bankRepairDigitLaneLive lane (bankRepairDigitTopPairOf c x y).y = false)

theorem bankRepairDigitWCarryOff {c : Compiled} (f : TopFields c)
    (h : f.wCarry.isW = false) : f.wCarry = .OFF := by
  cases hc : f.wCarry <;> simp_all [WCarry.isW]

theorem bankRepairDigitQCarryOff {c : Compiled} (f : TopFields c)
    (h : f.qCarry.isL = false) : f.qCarry = .OFF := by
  cases hc : f.qCarry <;> simp_all [QCarry.isL]

/-- The five lane-generic local row facts hold for the literal `liveTopPair`. -/
theorem bankRepairDigitLaneRowFactsHold (c : Compiled) : BankRepairDigitLaneRowFacts c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro lane x y hl hc hi
    cases lane with
    | writer =>
        obtain ⟨r1, r2, r3⟩ := bankRepairDigitWriterKeepX c x.lift y.lift x.word.beta
          y.word.beta hl (bankRepairDigitWCarryOff _ hc) hi
        refine ⟨?_, r2, r3⟩
        show ((bankRepairDigitTopPairOf c x y).x.wCarry).isW = false
        rw [show (bankRepairDigitTopPairOf c x y).x.wCarry = .OFF from r1]
        rfl
    | comparison =>
        obtain ⟨r1, r2, r3⟩ := bankRepairDigitComparisonKeepX c x.lift y.lift x.word.beta
          y.word.beta hl (bankRepairDigitQCarryOff _ hc) hi
        refine ⟨?_, r2, r3⟩
        show ((bankRepairDigitTopPairOf c x y).x.qCarry).isL = false
        rw [show (bankRepairDigitTopPairOf c x y).x.qCarry = .OFF from r1]
        rfl
  · intro lane x y hl hc hi hy
    cases lane with
    | writer =>
        obtain ⟨r1, r2⟩ := bankRepairDigitWriterFinalX c x.lift y.lift x.word.beta
          y.word.beta hl (bankRepairDigitWCarryOff _ hc) hi
          (by
            rcases hy with h | ⟨h1, h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨h1, fun hc' => h2 (by
                show y.top.wCarry.isW = false
                rw [show y.top.wCarry = .OFF from hc']; rfl)⟩)
        refine ⟨?_, r2⟩
        show ((bankRepairDigitTopPairOf c x y).x.wCarry).isW = false
        rw [show (bankRepairDigitTopPairOf c x y).x.wCarry = .OFF from r1]
        rfl
    | comparison =>
        obtain ⟨r1, r2⟩ := bankRepairDigitComparisonFinalX c x.lift y.lift x.word.beta
          y.word.beta hl (bankRepairDigitQCarryOff _ hc) hi
          (by
            rcases hy with h | ⟨h1, h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨h1, fun hc' => h2 (by
                show y.top.qCarry.isL = false
                rw [show y.top.qCarry = .OFF from hc']; rfl)⟩)
        refine ⟨?_, r2⟩
        show ((bankRepairDigitTopPairOf c x y).x.qCarry).isL = false
        rw [show (bankRepairDigitTopPairOf c x y).x.qCarry = .OFF from r1]
        rfl
  · intro lane x y hl hly hc hiX hiP hD
    cases lane with
    | writer =>
        obtain ⟨r1, r2, r3⟩ := bankRepairDigitWriterKeepY c x.lift y.lift x.word.beta
          y.word.beta hl hly (bankRepairDigitWCarryOff _ hc) hiX hiP hD
        exact ⟨congrArg WCarry.isW r1, r2, r3⟩
    | comparison =>
        obtain ⟨r1, r2, r3⟩ := bankRepairDigitComparisonKeepY c x.lift y.lift x.word.beta
          y.word.beta hl hly (bankRepairDigitQCarryOff _ hc) hiX hiP hD
        exact ⟨congrArg QCarry.isL r1, r2, r3⟩
  · intro lane x y hl hly hx
    cases lane with
    | writer =>
        obtain ⟨r1, r2⟩ := bankRepairDigitWriterFinalY c x.lift y.lift x.word.beta
          y.word.beta hl hly
          (by
            rcases hx with h | ⟨h1, h2, h3⟩
            · exact Or.inl h
            · exact Or.inr ⟨bankRepairDigitWCarryOff _ h1, h2, h3⟩)
        exact ⟨congrArg WCarry.isW r1, r2⟩
    | comparison =>
        obtain ⟨r1, r2⟩ := bankRepairDigitComparisonFinalY c x.lift y.lift x.word.beta
          y.word.beta hl hly
          (by
            rcases hx with h | ⟨h1, h2, h3⟩
            · exact Or.inl h
            · exact Or.inr ⟨bankRepairDigitQCarryOff _ h1, h2, h3⟩)
        exact ⟨congrArg QCarry.isL r1, r2⟩
  · intro lane x y hr
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ :=
      bankRepairDigitRootEdgeResets c x.lift y.lift x.word.beta y.word.beta hr
    cases lane with
    | writer =>
        refine ⟨a1, a2, a3, a4, ?_, ?_⟩
        · show ((bankRepairDigitTopPairOf c x y).x.wCarry).isW = false
          rw [show (bankRepairDigitTopPairOf c x y).x.wCarry = .OFF from a5]; rfl
        · show ((bankRepairDigitTopPairOf c x y).y.wCarry).isW = false
          rw [show (bankRepairDigitTopPairOf c x y).y.wCarry = .OFF from a6]; rfl
    | comparison =>
        refine ⟨a7, a8, a9, a10, ?_, ?_⟩
        · show ((bankRepairDigitTopPairOf c x y).x.qCarry).isL = false
          rw [show (bankRepairDigitTopPairOf c x y).x.qCarry = .OFF from a11]; rfl
        · show ((bankRepairDigitTopPairOf c x y).y.qCarry).isL = false
          rw [show (bankRepairDigitTopPairOf c x y).y.qCarry = .OFF from a12]; rfl

/-! #### Ring arithmetic for `digitSite` -/

theorem bankRepairDigitSiteVal {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ k : Nat, (digitSite ring root k).val = (root.val + k) % n := by
  intro k
  induction k with
  | zero => simp [digitSite, Nat.mod_eq_of_lt root.isLt]
  | succ k ih =>
      show (ring.rightNeighbor (digitSite ring root k)).val = _
      simp only [DirectedRing.rightNeighbor, ih, Nat.mod_add_mod, Nat.add_assoc]

private theorem bankRepairDigitModCases {n a : Nat} (h : a < 2 * n) :
    a % n = a ∨ (n ≤ a ∧ a % n = a - n) := by
  by_cases ha : a < n
  · exact Or.inl (Nat.mod_eq_of_lt ha)
  · refine Or.inr ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bankRepairDigitSiteInj {n : Nat} (ring : DirectedRing n) (root : Fin n)
    {k m : Nat} (hk : k < n) (hm : m < n)
    (h : digitSite ring root k = digitSite ring root m) : k = m := by
  have hv := congrArg Fin.val h
  rw [bankRepairDigitSiteVal, bankRepairDigitSiteVal] at hv
  have hr := root.isLt
  rcases bankRepairDigitModCases (n := n) (a := root.val + k) (by omega) with h1 | ⟨h1, h1'⟩ <;>
    rcases bankRepairDigitModCases (n := n) (a := root.val + m) (by omega) with h2 | ⟨h2, h2'⟩ <;>
    omega

theorem bankRepairDigitSiteN {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    digitSite ring root n = root := by
  apply Fin.ext
  rw [bankRepairDigitSiteVal, Nat.add_mod_right, Nat.mod_eq_of_lt root.isLt]

theorem bankRepairDigitRightInj {n : Nat} (ring : DirectedRing n) (a b : Fin n)
    (h : ring.rightNeighbor a = ring.rightNeighbor b) : a = b := by
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  rcases bankRepairDigitModCases (n := n) (a := a.val + 1) (by omega) with h1 | ⟨h1, h1'⟩ <;>
    rcases bankRepairDigitModCases (n := n) (a := b.val + 1) (by omega) with h2 | ⟨h2, h2'⟩ <;>
    omega

theorem bankRepairDigitRightNe {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (a : Fin n) :
    ring.rightNeighbor a ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  have ha := a.isLt
  rcases bankRepairDigitModCases (n := n) (a := a.val + 1) (by omega) with h1 | ⟨h1, h1'⟩ <;>
    omega

theorem bankRepairDigitSiteNonroot {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → ProjD c)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (k : Nat) (hk0 : 0 < k) (hkn : k < n) :
    (S (digitSite ring root k)).word.native.l = false := by
  cases hl : (S (digitSite ring root k)).word.native.l with
  | false => rfl
  | true =>
      have h1 := (hroot _).1 hl
      have h2 := bankRepairDigitSiteInj ring root hkn (by omega : 0 < n)
        (h1.trans (rfl : root = digitSite ring root 0))
      omega

theorem bankRepairDigitIsP {A : Nat} (t : InTok A) (h : t.isP = true) :
    ∃ v T, t = .P v T := by
  cases t <;> simp_all [InTok.isP]

theorem bankRepairDigitPhiDAt {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (S : Fin n → ProjD c) (e : Fin n)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta) :
    (phiD ring S e e).top =
        (bankRepairDigitTopPairOf c (S e) (S (ring.rightNeighbor e))).x ∧
    (phiD ring S e (ring.rightNeighbor e)).top =
        (bankRepairDigitTopPairOf c (S e) (S (ring.rightNeighbor e))).y ∧
    (∀ i, i ≠ e → i ≠ ring.rightNeighbor e → phiD ring S e i = S i) ∧
    (∀ i, (phiD ring S e i).word.beta = (S i).word.beta) := by
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring hn e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [phiD, projectedEdge, pairD, topD, hbX, hbY, bankRepairDigitTopPairOf]
  · simp [phiD, projectedEdge, pairD, topD, hbX, hbY, bankRepairDigitTopPairOf, hne]
  · intro i h1 h2
    simp [phiD, projectedEdge, h1, h2]
  · intro i
    by_cases h1 : i = e
    · subst h1
      simpa [phiD, projectedEdge, pairD] using hbX
    · by_cases h2 : i = ring.rightNeighbor e
      · subst h2
        simpa [phiD, projectedEdge, pairD, hne] using hbY
      · simp [phiD, projectedEdge, h1, h2]

theorem bankRepairDigitLeadNoXP {A : Nat} (t : InTok A) (h : DigitLeadingInput t) :
    t ≠ .X ∧ ∀ v T, t ≠ .P v T := by
  unfold DigitLeadingInput at h
  rcases h with h | ⟨v, h⟩ <;> subst h <;> simp

theorem bankRepairDigitSiteSucc {n : Nat} (ring : DirectedRing n) (root : Fin n) (k : Nat) :
    digitSite ring root (k + 1) = ring.rightNeighbor (digitSite ring root k) := rfl

/-! #### The three regions of the receipt -/

/-- Leading prefix `0 < k < first`: out `E`, carry off, leading input. -/
theorem bankRepairDigitLeadPrefixStep {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c) (e : Fin n)
    (hfacts : BankRepairDigitLaneRowFacts c)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta)
    (first : Nat) (hfn : first < n)
    (hbeta0 : ∀ k, 0 < k → k < first → (S (digitSite ring root k)).word.beta = false)
    (hlead : ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
      bankRepairDigitLaneOut lane (S (digitSite ring root k)).top = .E ∧
      bankRepairDigitLaneLive lane (S (digitSite ring root k)).top = false ∧
      DigitLeadingInput (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top)) :
    ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
      bankRepairDigitLaneOut lane (phiD ring S e (digitSite ring root k)).top = .E ∧
      bankRepairDigitLaneLive lane (phiD ring S e (digitSite ring root k)).top = false ∧
      DigitLeadingInput
        (bankRepairDigitLaneIn lane (phiD ring S e (digitSite ring root k)).top) := by
  intro lane k hk0 hk1
  obtain ⟨hPX, hPY, hPo, _⟩ := bankRepairDigitPhiDAt ring hn S e hbX hbY
  obtain ⟨f1, _f2, f3, _f4, f5⟩ := hfacts
  by_cases hx : digitSite ring root k = e
  · subst hx
    rw [hPX]
    obtain ⟨ho, hl, hi⟩ := hlead lane k hk0 hk1
    have hxl := bankRepairDigitSiteNonroot ring root S hroot k hk0 (by omega)
    have hin : bankRepairDigitLaneIn lane (S (digitSite ring root k)).top = .E ∨
        ((∃ v, bankRepairDigitLaneIn lane (S (digitSite ring root k)).top = .S v false) ∧
          (S (digitSite ring root k)).word.beta = false) := by
      unfold DigitLeadingInput at hi
      rcases hi with hi | hi
      · exact Or.inl hi
      · exact Or.inr ⟨hi, hbeta0 k hk0 hk1⟩
    obtain ⟨r1, r2, r3⟩ := f1 lane _ (S (ring.rightNeighbor (digitSite ring root k)))
      hxl hl hin
    refine ⟨r3 ho (hbeta0 k hk0 hk1), r1, ?_⟩
    rcases r2 with r2 | r2
    · rw [r2]; exact hi
    · rw [r2]; exact Or.inl rfl
  · by_cases hy : digitSite ring root k = ring.rightNeighbor e
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have he : e = digitSite ring root k' :=
        bankRepairDigitRightInj ring _ _ hy.symm
      subst he
      rw [hy, hPY]
      obtain ⟨ho', hl', hi'⟩ := hlead lane (k' + 1) hk0 hk1
      rw [bankRepairDigitSiteSucc] at ho' hl' hi'
      by_cases hk0' : k' = 0
      · have hxl : (S (digitSite ring root k')).word.native.l = true := by
          rw [hk0']; exact (hroot _).2 rfl
        obtain ⟨_, a2, _, a4, _, a6⟩ := f5 lane (S (digitSite ring root k'))
          (S (ring.rightNeighbor (digitSite ring root k'))) (by simp [hxl])
        exact ⟨a4, a6, Or.inl a2⟩
      · obtain ⟨ho, hl, hi⟩ := hlead lane k' (by omega) (by omega)
        have hxl := bankRepairDigitSiteNonroot ring root S hroot k' (by omega) (by omega)
        have hyl := bankRepairDigitSiteNonroot ring root S hroot (k' + 1) hk0 (by omega)
        rw [bankRepairDigitSiteSucc] at hyl
        obtain ⟨hiX, hiP⟩ := bankRepairDigitLeadNoXP _ hi
        have hoD : (bankRepairDigitLaneOut lane (S (digitSite ring root k')).top).isD = false := by
          rw [ho]; rfl
        obtain ⟨r1, r2, r3⟩ := f3 lane _ _ hxl hyl hl hiX hiP
          (fun h => absurd h (by rw [hoD]; simp))
        refine ⟨by rw [r3 hoD]; exact ho', by rw [r1]; exact hl', ?_⟩
        rcases r2 with r2 | r2
        · rw [r2]; exact hi'
        · rw [r2]; exact Or.inl rfl
    · rw [hPo _ hx hy]
      exact hlead lane k hk0 hk1

/-- The first-segment condition at one offset, in lane coordinates. -/
def BankRepairDigitSegOK {A : Nat} (n first k : Nat) (live : Bool) (inp : InTok A) : Prop :=
  (k + 1 = n ∧ live = true) ∨
    (live = false ∧ (if k = first then inp = .E else DigitLeadingInput inp))

theorem bankRepairDigitSegOfE {A : Nat} (first k : Nat) :
    (if k = first then (InTok.E : InTok A) = .E else DigitLeadingInput (InTok.E : InTok A)) := by
  split
  · rfl
  · exact Or.inl rfl

theorem bankRepairDigitRootRight {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (k : Nat) (hkn : k + 1 = n) :
    ring.rightNeighbor (digitSite ring root k) = root := by
  rw [← bankRepairDigitSiteSucc, hkn, bankRepairDigitSiteN]

/-- First segment `first ≤ k < stop`. -/
theorem bankRepairDigitSegStep {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c) (e : Fin n)
    (hfacts : BankRepairDigitLaneRowFacts c)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta)
    (first stop : Nat) (hf0 : 0 < first) (_hfs : first < stop) (hsn : stop ≤ n)
    (hbetaS : ∀ k, first < k → k < stop → (S (digitSite ring root k)).word.beta = false)
    (hlead : ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
      bankRepairDigitLaneOut lane (S (digitSite ring root k)).top = .E ∧
      bankRepairDigitLaneLive lane (S (digitSite ring root k)).top = false ∧
      DigitLeadingInput (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top))
    (hseg : ∀ (lane : DigitLane) (k : Nat), first ≤ k → k < stop →
      BankRepairDigitSegOK n first k
        (bankRepairDigitLaneLive lane (S (digitSite ring root k)).top)
        (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top)) :
    ∀ (lane : DigitLane) (k : Nat), first ≤ k → k < stop →
      BankRepairDigitSegOK n first k
        (bankRepairDigitLaneLive lane (phiD ring S e (digitSite ring root k)).top)
        (bankRepairDigitLaneIn lane (phiD ring S e (digitSite ring root k)).top) := by
  intro lane k hk1 hk2
  obtain ⟨hPX, hPY, hPo, _⟩ := bankRepairDigitPhiDAt ring hn S e hbX hbY
  obtain ⟨f1, _f2, f3, _f4, f5⟩ := hfacts
  by_cases hx : digitSite ring root k = e
  · subst hx
    rw [hPX]
    by_cases hkn : k + 1 = n
    · have hyl : (S (ring.rightNeighbor (digitSite ring root k))).word.native.l = true := by
        rw [bankRepairDigitRootRight ring root k hkn]; exact (hroot _).2 rfl
      obtain ⟨a1, _, _, _, a5, _⟩ := f5 lane (S (digitSite ring root k))
        (S (ring.rightNeighbor (digitSite ring root k))) (by simp [hyl])
      refine Or.inr ⟨a5, ?_⟩
      rw [a1]; exact bankRepairDigitSegOfE first k
    · rcases hseg lane k hk1 hk2 with ⟨h1, _⟩ | ⟨hl, hc⟩
      · exact absurd h1 hkn
      · have hxl := bankRepairDigitSiteNonroot ring root S hroot k (by omega) (by omega)
        have hin : bankRepairDigitLaneIn lane (S (digitSite ring root k)).top = .E ∨
            ((∃ v, bankRepairDigitLaneIn lane (S (digitSite ring root k)).top = .S v false) ∧
              (S (digitSite ring root k)).word.beta = false) := by
          by_cases hkf : k = first
          · rw [if_pos hkf] at hc; exact Or.inl hc
          · rw [if_neg hkf] at hc
            rcases hc with hc | hc
            · exact Or.inl hc
            · exact Or.inr ⟨hc, hbetaS k (by omega) hk2⟩
        obtain ⟨r1, r2, _⟩ := f1 lane _ (S (ring.rightNeighbor (digitSite ring root k)))
          hxl hl hin
        refine Or.inr ⟨r1, ?_⟩
        rcases r2 with r2 | r2
        · rw [r2]; exact hc
        · rw [r2]; exact bankRepairDigitSegOfE first k
  · by_cases hy : digitSite ring root k = ring.rightNeighbor e
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have he : e = digitSite ring root k' :=
        bankRepairDigitRightInj ring _ _ hy.symm
      subst he
      rw [hy, hPY]
      have hold := hseg lane (k' + 1) hk1 hk2
      rw [bankRepairDigitSiteSucc] at hold
      by_cases hk0' : k' = 0
      · have hxl : (S (digitSite ring root k')).word.native.l = true := by
          rw [hk0']; exact (hroot _).2 rfl
        obtain ⟨_, a2, _, _, _, a6⟩ := f5 lane (S (digitSite ring root k'))
          (S (ring.rightNeighbor (digitSite ring root k'))) (by simp [hxl])
        refine Or.inr ⟨a6, ?_⟩
        rw [a2]; exact bankRepairDigitSegOfE first (k' + 1)
      · have hxl := bankRepairDigitSiteNonroot ring root S hroot k' (by omega) (by omega)
        have hyl := bankRepairDigitSiteNonroot ring root S hroot (k' + 1) (by omega) (by omega)
        rw [bankRepairDigitSiteSucc] at hyl
        have hxf : bankRepairDigitLaneLive lane (S (digitSite ring root k')).top = false ∧
            bankRepairDigitLaneIn lane (S (digitSite ring root k')).top ≠ .X ∧
            (∀ v T, bankRepairDigitLaneIn lane (S (digitSite ring root k')).top ≠ .P v T) ∧
            ((bankRepairDigitLaneOut lane (S (digitSite ring root k')).top).isD = true →
              (S (ring.rightNeighbor (digitSite ring root k'))).word.beta = false) := by
          by_cases hkf : k' + 1 = first
          · obtain ⟨ho, hl, hi⟩ := hlead lane k' (by omega) (by omega)
            obtain ⟨hiX, hiP⟩ := bankRepairDigitLeadNoXP _ hi
            exact ⟨hl, hiX, hiP, fun h => by rw [ho] at h; simp [OutTok.isD] at h⟩
          · rcases hseg lane k' (by omega) (by omega) with ⟨h1, _⟩ | ⟨hl, hc⟩
            · omega
            · have hi : DigitLeadingInput
                  (bankRepairDigitLaneIn lane (S (digitSite ring root k')).top) := by
                by_cases hkf' : k' = first
                · rw [if_pos hkf'] at hc; rw [hc]; exact Or.inl rfl
                · rw [if_neg hkf'] at hc; exact hc
              obtain ⟨hiX, hiP⟩ := bankRepairDigitLeadNoXP _ hi
              refine ⟨hl, hiX, hiP, fun _ => ?_⟩
              rw [← bankRepairDigitSiteSucc]
              exact hbetaS (k' + 1) (by omega) hk2
        obtain ⟨hl, hiX, hiP, hD⟩ := hxf
        obtain ⟨r1, r2, _⟩ := f3 lane _ _ hxl hyl hl hiX hiP hD
        rcases hold with ⟨h1, h2⟩ | ⟨hl', hc'⟩
        · exact Or.inl ⟨h1, by rw [r1]; exact h2⟩
        · refine Or.inr ⟨by rw [r1]; exact hl', ?_⟩
          rcases r2 with r2 | r2
          · rw [r2]; exact hc'
          · rw [r2]; exact bankRepairDigitSegOfE first (k' + 1)
    · rw [hPo _ hx hy]
      exact hseg lane k hk1 hk2

/-- The final-region condition at one offset, in lane coordinates. -/
def BankRepairDigitFinalOK {A : Nat} (n k : Nat) (live : Bool) (inp : InTok A) : Prop :=
  (k + 1 = n ∧ live = true) ∨ (live = false ∧ DigitFinalInput inp)

theorem bankRepairDigitFinalNoXS {A : Nat} (t : InTok A) (h : DigitFinalInput t) :
    t ≠ .X ∧ ∀ v T, t ≠ .S v T := by
  unfold DigitFinalInput at h
  rcases h with h | ⟨v, T, h⟩ <;> subst h <;> simp

/-- Final region `last ≤ k < n`. -/
theorem bankRepairDigitFinalStep {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c) (e : Fin n)
    (hfacts : BankRepairDigitLaneRowFacts c)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta)
    (last : Nat) (hl0 : 0 < last) (_hln : last < n)
    (hbetaL : (S (digitSite ring root last)).word.beta = true)
    (hbetaF : ∀ k, last < k → k < n → (S (digitSite ring root k)).word.beta = false)
    (hfin : ∀ (lane : DigitLane) (k : Nat), last ≤ k → k < n →
      BankRepairDigitFinalOK n k
        (bankRepairDigitLaneLive lane (S (digitSite ring root k)).top)
        (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top)) :
    ∀ (lane : DigitLane) (k : Nat), last ≤ k → k < n →
      BankRepairDigitFinalOK n k
        (bankRepairDigitLaneLive lane (phiD ring S e (digitSite ring root k)).top)
        (bankRepairDigitLaneIn lane (phiD ring S e (digitSite ring root k)).top) := by
  intro lane k hk1 hk2
  obtain ⟨hPX, hPY, hPo, _⟩ := bankRepairDigitPhiDAt ring hn S e hbX hbY
  obtain ⟨_f1, f2, _f3, f4, f5⟩ := hfacts
  by_cases hx : digitSite ring root k = e
  · subst hx
    rw [hPX]
    by_cases hkn : k + 1 = n
    · have hyl : (S (ring.rightNeighbor (digitSite ring root k))).word.native.l = true := by
        rw [bankRepairDigitRootRight ring root k hkn]; exact (hroot _).2 rfl
      obtain ⟨a1, _, _, _, a5, _⟩ := f5 lane (S (digitSite ring root k))
        (S (ring.rightNeighbor (digitSite ring root k))) (by simp [hyl])
      exact Or.inr ⟨a5, by rw [a1]; exact Or.inl rfl⟩
    · rcases hfin lane k hk1 hk2 with ⟨h1, _⟩ | ⟨hl, hc⟩
      · exact absurd h1 hkn
      · have hxl := bankRepairDigitSiteNonroot ring root S hroot k (by omega) hk2
        have hyl := bankRepairDigitSiteNonroot ring root S hroot (k + 1) (by omega) (by omega)
        rw [bankRepairDigitSiteSucc] at hyl
        have hy : (S (ring.rightNeighbor (digitSite ring root k))).word.native.l = true ∨
            ((S (ring.rightNeighbor (digitSite ring root k))).word.beta = false ∧
              (bankRepairDigitLaneLive lane
                  (S (ring.rightNeighbor (digitSite ring root k))).top = false →
                ∀ v T, bankRepairDigitLaneIn lane
                  (S (ring.rightNeighbor (digitSite ring root k))).top ≠ .S v T)) := by
          refine Or.inr ⟨?_, fun hl' => ?_⟩
          · rw [← bankRepairDigitSiteSucc]; exact hbetaF (k + 1) (by omega) (by omega)
          · have hy' := hfin lane (k + 1) (by omega) (by omega)
            rw [bankRepairDigitSiteSucc] at hy'
            rcases hy' with ⟨_, h2⟩ | ⟨_, h2⟩
            · rw [hl'] at h2; exact absurd h2 (by simp)
            · exact (bankRepairDigitFinalNoXS _ h2).2
        have hin : bankRepairDigitLaneIn lane (S (digitSite ring root k)).top = .E ∨
            ∃ v T, bankRepairDigitLaneIn lane (S (digitSite ring root k)).top = .P v T := hc
        obtain ⟨r1, r2⟩ := f2 lane _ _ hxl hl hin hy
        exact Or.inr ⟨r1, r2⟩
  · by_cases hy : digitSite ring root k = ring.rightNeighbor e
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have he : e = digitSite ring root k' :=
        bankRepairDigitRightInj ring _ _ hy.symm
      subst he
      rw [hy, hPY]
      have hold := hfin lane (k' + 1) hk1 hk2
      rw [bankRepairDigitSiteSucc] at hold
      by_cases hk0' : k' = 0
      · have hxl : (S (digitSite ring root k')).word.native.l = true := by
          rw [hk0']; exact (hroot _).2 rfl
        obtain ⟨_, a2, _, _, _, a6⟩ := f5 lane (S (digitSite ring root k'))
          (S (ring.rightNeighbor (digitSite ring root k'))) (by simp [hxl])
        exact Or.inr ⟨a6, by rw [a2]; exact Or.inl rfl⟩
      · have hxl := bankRepairDigitSiteNonroot ring root S hroot k' (by omega) (by omega)
        have hyl := bankRepairDigitSiteNonroot ring root S hroot (k' + 1) (by omega) (by omega)
        rw [bankRepairDigitSiteSucc] at hyl
        have hxf : (S (ring.rightNeighbor (digitSite ring root k'))).word.beta = true ∨
            (bankRepairDigitLaneLive lane (S (digitSite ring root k')).top = false ∧
              bankRepairDigitLaneIn lane (S (digitSite ring root k')).top ≠ .X ∧
              ∀ v T, bankRepairDigitLaneIn lane (S (digitSite ring root k')).top ≠ .S v T) := by
          by_cases hkl : k' + 1 = last
          · left; rw [← bankRepairDigitSiteSucc, hkl]; exact hbetaL
          · right
            rcases hfin lane k' (by omega) (by omega) with ⟨h1, _⟩ | ⟨hl, hc⟩
            · omega
            · obtain ⟨hiX, hiS⟩ := bankRepairDigitFinalNoXS _ hc
              exact ⟨hl, hiX, hiS⟩
        obtain ⟨r1, r2⟩ := f4 lane _ _ hxl hyl hxf
        rcases hold with ⟨h1, h2⟩ | ⟨hl', hc'⟩
        · exact Or.inl ⟨h1, by rw [r1]; exact h2⟩
        · refine Or.inr ⟨by rw [r1]; exact hl', ?_⟩
          rcases r2 with r2 | r2 | r2
          · rw [r2]; exact hc'
          · rw [r2]; exact Or.inl rfl
          · exact Or.inr (bankRepairDigitIsP _ r2)
    · rw [hPo _ hx hy]
      exact hfin lane k hk1 hk2

theorem bankRepairDigitFirstSegmentCongr {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S S' : Fin n → ProjD c)
    (hb : ∀ i, (S' i).word.beta = (S i).word.beta) (first stop : Nat) :
    DigitFirstSegment ring root S' first stop ↔ DigitFirstSegment ring root S first stop := by
  simp only [DigitFirstSegment, DigitFirstDelimiter, DigitNextDelimiterOrRoot,
    DigitNonrootDelimiter, hb]

theorem bankRepairDigitNextDelimiterCongr {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S S' : Fin n → ProjD c)
    (hb : ∀ i, (S' i).word.beta = (S i).word.beta) (a b : Nat) :
    DigitNextDelimiterOrRoot ring root S' a b ↔ DigitNextDelimiterOrRoot ring root S a b := by
  simp only [DigitNextDelimiterOrRoot, DigitNonrootDelimiter, hb]

theorem bankRepairDigitCompleteBlockCongr {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S S' : Fin n → ProjD c)
    (hb : ∀ i, (S' i).word.beta = (S i).word.beta) (a : Nat) :
    DigitCompleteBlock ring root S' a ↔ DigitCompleteBlock ring root S a := by
  simp only [DigitCompleteBlock, DigitNextDelimiterOrRoot, DigitNonrootDelimiter, hb]

/-- RECEIPT STABILITY (projected one-step form): on a fixed marker layout with
the leader exactly at the root, one literal digit edge preserves the packet
boundary receipt. -/
theorem bankRepairDigitReceiptStep {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c) (e : Fin n)
    (hfacts : BankRepairDigitLaneRowFacts c)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta)
    (h : DigitBoundaryReceipt ring root S) :
    DigitBoundaryReceipt ring root (phiD ring S e) := by
  have hb := (bankRepairDigitPhiDAt ring hn S e hbX hbY).2.2.2
  have hv := fun lane (T : Fin n → ProjD c) i => bankRepairDigitEndpointViewLane lane T i
  obtain ⟨⟨first, stop, hseg, hlead, hsegc⟩, hfinal⟩ := h
  have hleadL : ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
      bankRepairDigitLaneOut lane (S (digitSite ring root k)).top = .E ∧
      bankRepairDigitLaneLive lane (S (digitSite ring root k)).top = false ∧
      DigitLeadingInput (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top) := by
    intro lane k hk0 hk1
    have h1 := hlead lane k hk0 hk1
    obtain ⟨e1, e2, e3⟩ := hv lane S (digitSite ring root k)
    dsimp only at h1
    rw [e1, e2, e3] at h1
    exact h1
  have hsegL : ∀ (lane : DigitLane) (k : Nat), first ≤ k → k < stop →
      BankRepairDigitSegOK n first k
        (bankRepairDigitLaneLive lane (S (digitSite ring root k)).top)
        (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top) := by
    intro lane k hk0 hk1
    have h1 := hsegc lane k hk0 hk1
    obtain ⟨e1, _, e3⟩ := hv lane S (digitSite ring root k)
    dsimp only [DigitLastCarryInert] at h1
    rw [e1, e3] at h1
    exact h1
  have hf0 : 0 < first := hseg.1.1.1
  have hfn : first < n := hseg.1.1.2.1
  have hfs : first < stop := hseg.2.2.1
  have hsn : stop ≤ n := hseg.2.2.2.1
  have hbeta0 := hseg.1.2
  have hbetaS := hseg.2.2.2.2.2
  refine ⟨⟨first, stop, (bankRepairDigitFirstSegmentCongr ring root S _ hb first stop).2 hseg,
    ?_, ?_⟩, ?_⟩
  · intro lane k hk0 hk1
    have h1 := bankRepairDigitLeadPrefixStep ring hn root S e hfacts hroot hbX hbY first hfn
      hbeta0 hleadL lane k hk0 hk1
    obtain ⟨e1, e2, e3⟩ := hv lane (phiD ring S e) (digitSite ring root k)
    dsimp only
    rw [e1, e2, e3]
    exact h1
  · intro lane k hk0 hk1
    have h1 := bankRepairDigitSegStep ring hn root S e hfacts hroot hbX hbY first stop
      hf0 hfs hsn hbetaS hleadL hsegL lane k hk0 hk1
    obtain ⟨e1, _, e3⟩ := hv lane (phiD ring S e) (digitSite ring root k)
    dsimp only [DigitLastCarryInert]
    rw [e1, e3]
    exact h1
  · intro source last hblock hlast hnext lane k hk1 hk2
    have hblock' := (bankRepairDigitCompleteBlockCongr ring root S _ hb source).1 hblock
    have hnext' := (bankRepairDigitNextDelimiterCongr ring root S _ hb last n).1 hnext
    have hfinL : ∀ (lane : DigitLane) (k : Nat), last ≤ k → k < n →
        BankRepairDigitFinalOK n k
          (bankRepairDigitLaneLive lane (S (digitSite ring root k)).top)
          (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top) := by
      intro lane k hk0 hk1
      have h1 := hfinal source last hblock' hlast hnext' lane k hk0 hk1
      obtain ⟨e1, _, e3⟩ := hv lane S (digitSite ring root k)
      dsimp only [DigitLastCarryInert] at h1
      rw [e1, e3] at h1
      exact h1
    have h1 := bankRepairDigitFinalStep ring hn root S e hfacts hroot hbX hbY last
      hnext'.1.1 hnext'.1.2.1 hnext'.1.2.2 hnext'.2.2.2.2 hfinL lane k hk1 hk2
    obtain ⟨e1, _, e3⟩ := hv lane (phiD ring S e) (digitSite ring root k)
    dsimp only [DigitLastCarryInert]
    rw [e1, e3]
    exact h1

/-! #### BANK-level stability on the layout-fixed class -/

theorem bankRepairDigitQWordOfWord {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (h : BankRepairWord ring hbank z) :
    AcceptedReceipts.QWord ring (piW z.val.1) := by
  obtain ⟨_root, _ρ, _γ₀, _w, γ, _hj, _hr, hacc, _hm⟩ := h
  cases γ with
  | failed => simp [BlockA.acceptsWord] at hacc
  | live shadow hc => exact hacc.2.2.2.2

theorem bankRepairDigitPiWNoFire {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hfire : oldFire (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) = none) :
    piW (bankRepairNext ring hbank z e).val.1 = phiW ring (piW z.val.1) e := by
  have h := bankRepairDigitMaskedProjectionOfNoFire ring hbank z e hfire
  funext i
  have hi : (piD (bankRepairNext ring hbank z e).val.1 i).word =
      (phiD ring (piD z.val.1) e i).word := by rw [h]
  change (piD (bankRepairNext ring hbank z e).val.1 i).word = _
  rw [hi]
  by_cases h1 : i = e
  · subst h1
    simp [phiD, phiW, projectedEdge, pairD, piD, piW, ProjD.ofAgent]
  · by_cases h2 : i = ring.rightNeighbor e
    · subst h2
      simp [phiD, phiW, projectedEdge, pairD, piD, piW, ProjD.ofAgent, h1]
    · simp [phiD, phiW, projectedEdge, h1, h2, piD, piW, ProjD.ofAgent]

/-- Fixed marker layout and fixed leader: the singleton class plus `Q_W`. -/
def BankRepairDigitLayoutFixed {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedSingleton ring hbank root z ∧
    AcceptedReceipts.QWord ring (piW z.val.1)

theorem bankRepairDigitLayoutFixedStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitLayoutFixed ring hbank root z) (e : Fin n) :
    BankRepairDigitLayoutFixed ring hbank root (bankRepairNext ring hbank z e) := by
  refine ⟨bankPostInheritedSingletonClosed ring hn hbank root z hz.1 e, ?_⟩
  rw [bankRepairDigitPiWNoFire ring hbank z e
    (bankRepairDigitBoundaryNoFireOfSingleton ring hbank root z hz.1 e)]
  exact (AcceptedReceipts.qword_step ring _ hz.2 e).2

theorem bankRepairDigitLayoutFixedWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank,
      BankRepairDigitLayoutFixed ring hbank root z →
      BankRepairDigitLayoutFixed ring hbank root (word.foldl (bankRepairNext ring hbank) z) := by
  induction word with
  | nil => intro z hz; exact hz
  | cons e rest ih =>
      intro z hz
      exact ih _ (bankRepairDigitLayoutFixedStep ring hn hbank root z hz e)

/-- RECEIPT STABILITY on the actual BANK chain: on the layout-fixed class the
packet boundary receipt at the root survives every edge. -/
theorem bankRepairDigitReceiptBankStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitLayoutFixed ring hbank root z) (e : Fin n)
    (h : DigitBoundaryReceipt ring root (piD z.val.1)) :
    DigitBoundaryReceipt ring root (piD (bankRepairNext ring hbank z e).val.1) := by
  rw [bankRepairDigitMaskedProjectionOfNoFire ring hbank z e
    (bankRepairDigitBoundaryNoFireOfSingleton ring hbank root z hz.1 e)]
  have hnb := (AcceptedReceipts.qword_step ring _ hz.2 e).1
  have hvis : ∀ i, AcceptedReceipts.wordVisible (phiW ring (piW z.val.1) e) i =
      AcceptedReceipts.wordVisible (piW z.val.1) i := by
    intro i
    exact Classical.byContradiction (fun hne => hnb ⟨i, hne⟩)
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring (by omega) e
  have hbX := congrArg Prod.snd (hvis e)
  have hbY := congrArg Prod.snd (hvis (ring.rightNeighbor e))
  simp only [AcceptedReceipts.wordVisible, phiW, projectedEdge, if_pos rfl,
    if_neg hne] at hbX hbY
  have hroot : ∀ i, (piD z.val.1 i).word.native.l = true ↔ i = root := by
    intro i
    constructor
    · exact fun hi => hz.1.2.2.1 i hi
    · rintro rfl; exact hz.1.2.1
  exact bankRepairDigitReceiptStep ring (by omega) root (piD z.val.1) e
    (bankRepairDigitLaneRowFactsHold _) hroot hbX hbY h

theorem bankRepairDigitReceiptBankWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank,
      BankRepairDigitLayoutFixed ring hbank root z →
      DigitBoundaryReceipt ring root (piD z.val.1) →
      DigitBoundaryReceipt ring root
        (piD (word.foldl (bankRepairNext ring hbank) z).val.1) := by
  induction word with
  | nil => intro z _ h; exact h
  | cons e rest ih =>
      intro z hz h
      exact ih _ (bankRepairDigitLayoutFixedStep ring hn hbank root z hz e)
        (bankRepairDigitReceiptBankStep ring hn hbank root z hz e h)

/-- Every state reachable from the gone cut is layout-fixed at the prepared root. -/
theorem bankRepairDigitGoneReachableLayout {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitGoneReachable ring hbank z) :
    ∃ root, BankRepairDigitLayoutFixed ring hbank root z := by
  obtain ⟨_, word', ⟨x, wordW, wordR, word, hx, hW, _hR, _hg, rfl⟩, rfl⟩ := hz
  obtain ⟨root, hs, _⟩ := hx
  have h0 : BankRepairDigitLayoutFixed ring hbank root
      (wordW.foldl (bankRepairNext ring hbank) x) :=
    ⟨bankRepairDigitSingletonWordFold ring hn hbank root wordW x hs,
      bankRepairDigitQWordOfWord ring hbank _ hW⟩
  exact ⟨root, bankRepairDigitLayoutFixedWord ring hn hbank root word' _
    (bankRepairDigitLayoutFixedWord ring hn hbank root word _
      (bankRepairDigitLayoutFixedWord ring hn hbank root wordR _ h0))⟩

/-- The receipt at the actual (W fixed) leader. -/
def BankRepairDigitLeaderReceipt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ root : Fin n, WFixedRoot ring root (piW z.val.1) ∧
    DigitBoundaryReceipt ring root (piD z.val.1)

theorem bankRepairDigitLeaderReceiptOfRetired {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitBoundaryRetiredCut ring hbank z) :
    BankRepairDigitLeaderReceipt ring hbank z := by
  obtain ⟨_, _, root, _, _, _, hW, _, hrec, _⟩ := hz
  exact ⟨root, hW, hrec⟩

/-- Once produced, the leader receipt is never lost on any run from a state
reachable from the gone cut. -/
theorem bankRepairDigitLeaderReceiptStable {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitGoneReachable ring hbank z)
    (hrec : BankRepairDigitLeaderReceipt ring hbank z) (word : List (Fin n)) :
    BankRepairDigitLeaderReceipt ring hbank (word.foldl (bankRepairNext ring hbank) z) := by
  obtain ⟨root, hL⟩ := bankRepairDigitGoneReachableLayout ring hn hbank z hz
  obtain ⟨r, hW, hr⟩ := hrec
  have hrr : r = root := hL.1.2.2.1 r hW.1
  subst hrr
  exact ⟨r, bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank r z hL.1 word,
    bankRepairDigitReceiptBankWord ring hn hbank r word z hL hr⟩

/-! #### The strengthened first-zero clock carrying the receipt -/

/-- The flush clock lands in the full cut on a state still reachable from the
gone cut. -/
theorem bankRepairDigitFlushReachable {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (charge : Nat)
    (hflush : BankRepairDigitReceiptFlushClock ring hbank charge) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageGoneCut ring hbank)
      (fun z => BankRepairDigitBoundaryRetiredCut ring hbank z ∧
        BankRepairDigitGoneReachable ring hbank z) charge := by
  intro z hz T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (bankRepairDigitCostTransfer
    (bankRepairNext ring hbank) (bankRepairNext ring hbank)
    (fun y => BankRepairDigitBoundaryRetiredCut ring hbank y ∧
      BankRepairDigitGoneReachable ring hbank y)
    (BankRepairDigitBoundaryRetiredCut ring hbank) T z z
    (fun w hw => ⟨hw, z, w, hz, rfl⟩))) (hflush z hz T)

/-- The ORIGINAL first-zero clock, run from a reachable full cut, hits the
first-zero cut with the leader receipt still in force (receipt stability). -/
theorem bankRepairDigitFirstZeroKeepsReceipt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankRepairDigitBoundaryRetiredCut ring hbank z ∧
        BankRepairDigitGoneReachable ring hbank z)
      (fun z => cuts.firstBlockZero z ∧ BankRepairDigitLeaderReceipt ring hbank z)
      (bankRepairDigitFirstZeroMicroCharge n) := by
  rintro z ⟨hr, hg⟩ T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (bankRepairDigitCostTransfer
    (bankRepairNext ring hbank) (bankRepairNext ring hbank)
    (fun y => cuts.firstBlockZero y ∧ BankRepairDigitLeaderReceipt ring hbank y)
    cuts.firstBlockZero T z z
    (fun w hw => ⟨hw, bankRepairDigitLeaderReceiptStable ring hn hbank z hg
      (bankRepairDigitLeaderReceiptOfRetired ring hbank z hr) w⟩))) (hzero z hr T)

/-- ROUTE B, STRENGTHENED FIRST-ZERO CLOCK: from the gone cut (the cut the
premise-free boundary clock reaches) to the first-zero cut WITH the leader
receipt, at the flush charge plus the original first-zero charge. The only
non-row input is the flush clock. -/
theorem bankRepairDigitFirstZeroReceiptOfFlush {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank) (charge : Nat)
    (hflush : BankRepairDigitReceiptFlushClock ring hbank charge)
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageGoneCut ring hbank)
      (fun z => cuts.firstBlockZero z ∧ BankRepairDigitLeaderReceipt ring hbank z)
      (charge + bankRepairDigitFirstZeroMicroCharge n) :=
  bankRepairDigitChargedCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageGoneCut ring hbank)
    (fun z => BankRepairDigitBoundaryRetiredCut ring hbank z ∧
      BankRepairDigitGoneReachable ring hbank z)
    (fun z => cuts.firstBlockZero z ∧ BankRepairDigitLeaderReceipt ring hbank z)
    charge (bankRepairDigitFirstZeroMicroCharge n)
    (bankRepairDigitFlushReachable ring hbank charge hflush)
    (bankRepairDigitFirstZeroKeepsReceipt ring hn hbank cuts hzero)

end L3.RenewalReferenceClock

/-! ## T17: the receipt flush inside the boundary charge

Step 1 splits the boundary micro-charge `2 n (e-numerator)` into the
label-extinction part (item 1 of (e-boundary), the only part the gone clock
uses) and a remainder that pays the flush. Step 2 extracts the delimiter
layout from the accepted word's equations. Step 3 composes: the strengthened
first-zero clock and the 201 pre-drain from every W-stage entrance, with the
fit discharged, from a flush certificate at the remainder budget, and splits
that certificate into a leading stage and a final stage at the paper's budgets
(`2 J` and `F + R + U + r`). The local literal-row weight inequalities for the
leading fragment's interior edges (both lanes) are proved at the end. -/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-! ### Step 1: split of the boundary charge -/

/-- Item 1 of (e-boundary): the label-extinction part, in the same micro units
(doubled, times `n`) as `bankRepairDigitBoundaryMicroCharge`. -/
def bankRepairDigitExtinctionMicroCharge (n : Nat) : Nat :=
  2 * (n * (2 * (ceilLogTwo n +
    bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)) + 2)))

/-- The flush budget: the boundary numerator minus the extinction numerator,
counted in nominated hits. -/
def bankRepairDigitFlushBudget (n : Nat) : Nat :=
  bankRepairDigitBoundaryUpper (ceilLogTwo (ceilLogTwo n)) -
    2 * (ceilLogTwo n +
      bankRepairDigitLeadingLength (ceilLogTwo (ceilLogTwo n)) + 2)

/-- The remainder of the boundary charge after extinction. -/
def bankRepairDigitFlushMicroCharge (n : Nat) : Nat :=
  2 * (n * bankRepairDigitFlushBudget n)

theorem bankRepairDigitSplitArith (n a u : Nat) (h : a ≤ u) :
    2 * (n * a) + 2 * (n * (u - a)) = 2 * u * n := by
  rw [← Nat.mul_add, ← Nat.mul_add, Nat.add_sub_of_le h, Nat.mul_comm n u,
    Nat.mul_assoc]

/-- Step 1: extinction part plus remainder is exactly the boundary charge. -/
theorem bankRepairDigitBoundaryChargeSplit {n : Nat} (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    bankRepairDigitExtinctionMicroCharge n + bankRepairDigitFlushMicroCharge n =
      bankRepairDigitBoundaryMicroCharge n := by
  unfold bankRepairDigitExtinctionMicroCharge bankRepairDigitFlushMicroCharge
    bankRepairDigitFlushBudget bankRepairDigitBoundaryMicroCharge
  exact bankRepairDigitSplitArith n _ _ (bankRepairDigitBoundaryUpperPaysBaseLog hn hbank)

/-- The remainder pays the paper's leading-fragment and final-sink terms:
`2 J + F + R + U + r + 20 r^2 + 2 ≤ budget + 2 E`, and in particular
`2 J + F + R + U + r ≤ budget`. -/
theorem bankRepairDigitFlushBudgetPays {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 * bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n)) +
        bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) +
        20 * (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) ^ 2 + 2 ≤
      bankRepairDigitFlushBudget n +
        2 * bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) ∧
    2 * bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n)) +
        bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) ≤
      bankRepairDigitFlushBudget n := by
  have hs : 7 ≤ ceilLogTwo (ceilLogTwo n) := bankRepairDigitWidthBank hbank
  have hq80 : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have hq : ceilLogTwo n ≤ 2 ^ ceilLogTwo (ceilLogTwo n) :=
    (ceilLogTwo_spec (ceilLogTwo n) (by omega)).2
  have hpower : 2 ^ ceilLogTwo (ceilLogTwo n) =
      2 * bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitExponent
    calc
      2 ^ ceilLogTwo (ceilLogTwo n) =
          2 ^ ((ceilLogTwo (ceilLogTwo n) - 1) + 1) := by congr 1; omega
      _ = 2 ^ (ceilLogTwo (ceilLogTwo n) - 1) * 2 :=
        Nat.pow_succ 2 (ceilLogTwo (ceilLogTwo n) - 1)
      _ = 2 * 2 ^ (ceilLogTwo (ceilLogTwo n) - 1) := by ac_rfl
  have hradius : bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) ≤
      bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitRadius; rw [hpower]
    have : 0 < bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) := by
      unfold bankRepairDigitExponent; exact Nat.pow_pos (by omega)
    omega
  have hserv : 2 * bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) ≤
      bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitBoundaryServices; omega
  have hr2 : bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) ≤
      (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) ^ 2 := by
    rw [Nat.pow_two]; exact Nat.le_mul_self _
  rw [hpower] at hq
  unfold bankRepairDigitFlushBudget bankRepairDigitBoundaryUpper
  constructor <;> omega

/-- STEP 1: the premise-free boundary micro-clock at the EXTINCTION part only. -/
theorem bankRepairDigitWordStageGoneExtinctionClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (BankRepairDigitWordStageGoneCut ring hbank)
      (bankRepairDigitExtinctionMicroCharge n) := by
  rintro z ⟨x, wordW, wordR, hx, hW, hR, rfl⟩ T
  have htasks := bankRepairDigitSingleInheritedLabelTasksOfWordStage
    ring hn hbank x hx wordW hW wordR hR
  have hcost := bankRepairDigitAllBaseCostLogarithmicOfTasks (by omega : 2 ≤ n)
    ring hbank _ htasks T
  have htr := bankRepairDigitCostTransfer
      (bankRepairNext ring hbank) (bankRepairDigitBoundaryAuditNext ring hbank)
      (BankRepairDigitWordStageGoneCut ring hbank)
      (bankRepairDigitAllBaseLabelsGone ring hbank) T _ _
      (fun word hg => ⟨x, wordW, wordR, word, hx, hW, hR, hg, rfl⟩)
  refine Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.le_trans htr hcost))
    (Nat.le_of_eq ?_)
  unfold bankRepairDigitExtinctionMicroCharge
  ac_rfl

theorem bankRepairDigitChargedMono {S : Type} {n : Nat} (next : S → Fin n → S)
    (A B : S → Prop) {a b : Nat} (hab : a ≤ b)
    (h : BankRepairDigitChargedStage next A B a) :
    BankRepairDigitChargedStage next A B b :=
  fun x hx T => Nat.le_trans (h x hx T) (Nat.mul_le_mul_left _ hab)

/-- The flush certificate at the remainder budget gives the flush clock at the
remainder charge. -/
theorem bankRepairDigitFlushClockOfRemainderTasks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (htasks : BankRepairDigitReceiptFlushTasks ring hbank (bankRepairDigitFlushBudget n)) :
    BankRepairDigitReceiptFlushClock ring hbank (bankRepairDigitFlushMicroCharge n) :=
  bankRepairDigitReceiptFlushClockOfTasks ring hbank _ htasks

/-- STEP 3 composition: the strengthened first-zero clock from every W-stage
entrance at the boundary charge plus the first-zero charge. -/
theorem bankRepairDigitFirstZeroReceiptOfWordStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (hflush : BankRepairDigitReceiptFlushClock ring hbank
      (bankRepairDigitFlushMicroCharge n))
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (fun z => cuts.firstBlockZero z ∧ BankRepairDigitLeaderReceipt ring hbank z)
      (bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n) := by
  have h := bankRepairDigitChargedCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    (BankRepairDigitWordStageGoneCut ring hbank)
    (fun z => cuts.firstBlockZero z ∧ BankRepairDigitLeaderReceipt ring hbank z)
    _ _ (bankRepairDigitWordStageGoneExtinctionClock ring hn hbank)
    (bankRepairDigitFirstZeroReceiptOfFlush ring hn hbank cuts _ hflush hzero)
  refine bankRepairDigitChargedMono _ _ _ (Nat.le_of_eq ?_) h
  rw [← bankRepairDigitBoundaryChargeSplit hn hbank, Nat.add_assoc]

/-- STEP 3 composition: the 201-half pre-drain from every W-stage entrance
with the fit DISCHARGED (the flush is paid inside the boundary charge). -/
theorem bankRepairDigitPreDrain201OfRemainderFlush {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hflush : BankRepairDigitReceiptFlushClock ring hbank
      (bankRepairDigitFlushMicroCharge n))
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) preDrain 201 := by
  have h1 := bankRepairDigitChargedCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    (fun z => cuts.firstBlockZero z ∧ BankRepairDigitLeaderReceipt ring hbank z)
    cuts.successorValuesStable _ (bankRepairDigitValueWaveMicroCharge n)
    (bankRepairDigitFirstZeroReceiptOfWordStage ring hn hbank cuts hflush hzero)
    (fun x hx T => hwave x hx.1 T)
  have h2 := bankRepairDigitChargedCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageEntrance ring hbank)
    cuts.successorValuesStable preDrain _
    (bankRepairDigitComparisonMicroCharge n) h1 hpair
  have hfit := bankRepairDigitMicroChargesFit hn hbank
  intro z hz T
  refine Nat.le_trans (h2 z hz T) (Nat.mul_le_mul_left (n ^ T) ?_)
  omega

theorem bankRepairDigitPreDrain201OfRemainderTasks {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (htasks : BankRepairDigitReceiptFlushTasks ring hbank (bankRepairDigitFlushBudget n))
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) preDrain 201 :=
  bankRepairDigitPreDrain201OfRemainderFlush ring hn hbank cuts preDrain
    (bankRepairDigitFlushClockOfRemainderTasks ring hbank htasks) hzero hwave hpair

/-! ### Step 2: the delimiter layout -/

theorem bankRepairDigitTrailingFold (f : Nat → Bool) :
    ∀ (l : List Nat) (a : Bool),
      l.foldl (fun a j => if j = 0 then a else a && f j) a = true ↔
        a = true ∧ ∀ j, j ∈ l → j ≠ 0 → f j = true := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x l ih =>
      intro a
      rw [List.foldl_cons, ih]
      by_cases hx : x = 0
      · subst hx
        simp only [if_pos rfl]
        constructor
        · rintro ⟨ha, h⟩
          refine ⟨ha, fun j hj hj0 => ?_⟩
          rcases List.mem_cons.mp hj with h1 | h1
          · exact absurd h1 hj0
          · exact h j h1 hj0
        · rintro ⟨ha, h⟩
          exact ⟨ha, fun j hj hj0 => h j (List.mem_cons_of_mem _ hj) hj0⟩
      · simp only [if_neg hx]
        constructor
        · rintro ⟨ha, h⟩
          have ha' : a = true ∧ f x = true := by simpa using ha
          refine ⟨ha'.1, fun j hj hj0 => ?_⟩
          rcases List.mem_cons.mp hj with h1 | h1
          · rw [h1]; exact ha'.2
          · exact h j h1 hj0
        · rintro ⟨ha, h⟩
          refine ⟨?_, fun j hj hj0 => h j (List.mem_cons_of_mem _ hj) hj0⟩
          rw [ha, h x (List.mem_cons_self) hx]
          rfl

theorem bankRepairDigitRecIterMulFixed (t : Nat) (taps : Nat → Bool) (r : Nat)
    (w : Fin t → Bool) (hw : recIter t taps r w = w) :
    ∀ j, recIter t taps (j * r) w = w := by
  intro j
  induction j with
  | zero => rw [Nat.zero_mul]; rfl
  | succ j ih =>
      rw [Nat.succ_mul, bankRepairDigitRecIterAdd, hw, ih]

/-- On a primitive recurrence, the all-ones window recurs exactly at the
multiples of the period `2^t - 1`. -/
theorem bankRepairDigitOnesReturn {t : Nat} {taps : Nat → Bool}
    (hp : IsPrimitive t taps) (ht : 1 ≤ t) (m : Nat) :
    recIter t taps m (fun _ => true) = (fun _ => true) ↔ m % (2 ^ t - 1) = 0 := by
  have hones : ∃ i : Fin t, (fun _ => true : Fin t → Bool) i = true := ⟨⟨0, ht⟩, rfl⟩
  have hper := (hp _ hones).1
  have hmin := (hp _ hones).2
  have hpos : 0 < 2 ^ t - 1 := by
    have := bankRepairDigitPowLower t; omega
  have hdecomp : recIter t taps m (fun _ => true) =
      recIter t taps (m % (2 ^ t - 1)) (fun _ => true) := by
    conv => lhs; rw [← Nat.mod_add_div m (2 ^ t - 1)]
    rw [bankRepairDigitRecIterAdd, Nat.mul_comm,
      bankRepairDigitRecIterMulFixed t taps _ _ hper]
  rw [hdecomp]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    exact hmin _ (by omega) (Nat.mod_lt _ hpos) h
  · intro h
    rw [h]
    rfl

/-- STEP 2 (word level): from the clean-worker word equations at `root`, there
is a phase `d < 2^t - 1` such that the markers at offsets `0 < k < n` are
exactly `k = t + d + j (2^t - 1)`. The first delimiter is at `t + d`, NOT
necessarily at `t`: the first window (offsets `1..t`) is only certified
nonzero, and `d` is its orbit distance to the all-ones window. -/
theorem bankRepairDigitDelimiterLayout {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n) (p : Fin n → ProjW c)
    (hv : CleanWorkerWordValues ring root p)
    (ht : 1 ≤ c.t) (hprim : IsPrimitive c.t c.taps) :
    ∃ d : Nat, d < 2 ^ c.t - 1 ∧
      ∀ k : Nat, 0 < k → k < n →
        (cwMarker ring root p k = true ↔
          c.t + d ≤ k ∧ (k - (c.t + d)) % (2 ^ c.t - 1) = 0) := by
  let ub : Nat → Bool := fun m => cwBit ring root p m
  let W : Nat → Fin c.t → Bool := bankRepairDigitOffsetWindow c.t ub
  have hrec : ∀ k, c.t < k → k < n →
      ub k = (List.range c.t).foldl
        (fun parity j => Bool.xor parity (c.taps j && ub (k - c.t + j))) false :=
    fun k h1 h2 => hv.recurrence ⟨k, h2⟩ h1
  have hiter : ∀ e, e + c.t < n → W (1 + e) = recIter c.t c.taps e (W 1) := by
    intro e
    induction e with
    | zero => intro _; rfl
    | succ e ih =>
        intro he
        rw [show 1 + (e + 1) = (1 + e) + 1 by omega, recIter_succ, ← ih (by omega)]
        exact bankRepairDigitOffsetWindowStep n c.t c.taps ub hrec (1 + e) (by omega)
          (by omega)
  have hW1 : ∃ i, W 1 i = true := by
    rcases bankRepairDigitOrFoldTrue (fun j => ub (j + 1)) (List.range c.t) false
        hv.firstNonzero with h0 | ⟨j, hj, hs⟩
    · exact absurd h0 (by decide)
    · refine ⟨⟨j, List.mem_range.mp hj⟩, ?_⟩
      show ub (1 + j) = true
      rw [Nat.add_comm]; exact hs
  obtain ⟨d, hd, hdeq⟩ := isPrimitive_orbit_covers hprim (W 1) (fun _ => true) hW1
    ⟨⟨0, ht⟩, rfl⟩
  have hpos : 0 < 2 ^ c.t - 1 := by
    have := bankRepairDigitPowLower c.t; omega
  -- the marker at `k ≥ t` is the all-ones test of the window ending at `k`
  have hmark : ∀ k, c.t ≤ k → k < n →
      (cwMarker ring root p k = true ↔ W (1 + (k - c.t)) = fun _ => true) := by
    intro k hk hkn
    rw [hv.markers ⟨k, hkn⟩ hk]
    have htr := bankRepairDigitTrailingFold (fun j => ub (k - c.t + j))
      (List.range c.t) true
    constructor
    · intro h
      have h' : cwSumTrailing ring root p k c.t = true ∧ cwBit ring root p k = true := by
        simpa using h
      have hall := (htr.mp h'.1).2
      funext j
      show ub (1 + (k - c.t) + j.val) = true
      by_cases hj : j.val + 1 < c.t
      · have := hall (j.val + 1) (List.mem_range.mpr hj) (by omega)
        rw [show 1 + (k - c.t) + j.val = k - c.t + (j.val + 1) by omega]
        exact this
      · rw [show 1 + (k - c.t) + j.val = k by have := j.isLt; omega]
        exact h'.2
    · intro h
      have hb : ∀ j : Fin c.t, ub (1 + (k - c.t) + j.val) = true := fun j => congrFun h j
      have h1 : cwSumTrailing ring root p k c.t = true := by
        refine htr.mpr ⟨rfl, fun j hj hj0 => ?_⟩
        have hjl := List.mem_range.mp hj
        have := hb ⟨j - 1, by omega⟩
        rw [show 1 + (k - c.t) + (j - 1) = k - c.t + j by omega] at this
        exact this
      have h2 : cwBit ring root p k = true := by
        have := hb ⟨c.t - 1, by omega⟩
        rw [show 1 + (k - c.t) + (c.t - 1) = k by omega] at this
        exact this
      rw [h1, h2]; rfl
  refine ⟨d, hd, fun k hk0 hkn => ?_⟩
  by_cases hkt : k < c.t
  · rw [hv.prefixZeros ⟨k, hkn⟩ hk0 hkt]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; omega
  · rw [hmark k (by omega) hkn, hiter (k - c.t) (by omega)]
    by_cases hdk : d ≤ k - c.t
    · rw [show k - c.t = (k - c.t - d) + d by omega, bankRepairDigitRecIterAdd, hdeq,
        bankRepairDigitOnesReturn hprim ht]
      constructor
      · intro h; exact ⟨by omega, by rw [show k - (c.t + d) = k - c.t - d by omega]; exact h⟩
      · intro h; rw [show k - c.t - d = k - (c.t + d) by omega]; exact h.2
    · constructor
      · intro h
        exfalso
        have h2 : recIter c.t c.taps d (W 1) = recIter c.t c.taps (d - (k - c.t))
            (recIter c.t c.taps (k - c.t) (W 1)) := by
          rw [← bankRepairDigitRecIterAdd, show d - (k - c.t) + (k - c.t) = d by omega]
        rw [h, hdeq] at h2
        have h3 := (bankRepairDigitOnesReturn hprim ht (d - (k - c.t))).mp h2.symm
        have h4 : d - (k - c.t) < 2 ^ c.t - 1 := by omega
        rw [Nat.mod_eq_of_lt h4] at h3
        omega
      · intro h; omega

/-- The layout-fixed class together with the word equations at its root. -/
def BankRepairDigitLayoutValues {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairDigitLayoutFixed ring hbank root z ∧
    CleanWorkerWordValues ring root (piW z.val.1)

theorem bankRepairDigitLayoutValuesStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitLayoutValues ring hbank root z) (e : Fin n) :
    BankRepairDigitLayoutValues ring hbank root (bankRepairNext ring hbank z e) := by
  refine ⟨bankRepairDigitLayoutFixedStep ring hn hbank root z hz.1 e, ?_⟩
  rw [bankRepairDigitPiWNoFire ring hbank z e
    (bankRepairDigitBoundaryNoFireOfSingleton ring hbank root z hz.1.1 e)]
  have hnb := (AcceptedReceipts.qword_step ring _ hz.1.2 e).1
  exact cleanWorkerWordValues_congr ring root _ _
    (fun i => Classical.byContradiction (fun hne => hnb ⟨i, hne⟩)) hz.2

theorem bankRepairDigitLayoutValuesWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n)
    (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank,
      BankRepairDigitLayoutValues ring hbank root z →
      BankRepairDigitLayoutValues ring hbank root
        (word.foldl (bankRepairNext ring hbank) z) := by
  induction word with
  | nil => intro z hz; exact hz
  | cons e rest ih =>
      intro z hz
      exact ih _ (bankRepairDigitLayoutValuesStep ring hn hbank root z hz e)

/-- Every state reachable from the gone cut is in the layout-values class. -/
theorem bankRepairDigitGoneReachableValues {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitGoneReachable ring hbank z) :
    ∃ root, BankRepairDigitLayoutValues ring hbank root z := by
  obtain ⟨_, word', ⟨x, wordW, wordR, word, hx, hW, _hR, _hg, rfl⟩, rfl⟩ := hz
  obtain ⟨root, hs, _⟩ := hx
  have hs' := bankRepairDigitSingletonWordFold ring hn hbank root wordW x hs
  have h0 : BankRepairDigitLayoutValues ring hbank root
      (wordW.foldl (bankRepairNext ring hbank) x) :=
    ⟨⟨hs', bankRepairDigitQWordOfWord ring hbank _ hW⟩,
      bankRepairDigitRootWordValuesOfWordStage ring hbank _ hW root hs'.2.1⟩
  exact ⟨root, bankRepairDigitLayoutValuesWord ring hn hbank root word' _
    (bankRepairDigitLayoutValuesWord ring hn hbank root word _
      (bankRepairDigitLayoutValuesWord ring hn hbank root wordR _ h0))⟩

theorem bankRepairDigitSiteShift {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (k : Nat) : digitSite ring root k = PPL.shiftRight ring root k := by
  apply Fin.ext
  rw [bankRepairDigitSiteVal]
  rfl

/-- STEP 2 (BANK level, in the form the flush rank reads): at every state
reachable from the gone cut, with the fixed leader `root`, the delimiters of
`piD` along `digitSite ring root` are exactly the offsets
`first + j * digitSpan`, with `t ≤ first < t + digitSpan`. In particular the
leading prefix has `first - 1 ≤ t + digitSpan - 2 = m_t` sites. -/
theorem bankRepairDigitGoneReachableDelimiters {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitGoneReachable ring hbank z) :
    ∃ (root : Fin n) (first : Nat),
      BankRepairDigitLayoutValues ring hbank root z ∧
      (compileAdvice (ceilLogTwo n)).t ≤ first ∧
      first < (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) ∧
      ∀ k : Nat, 0 < k → k < n →
        ((piD z.val.1 (digitSite ring root k)).word.beta = true ↔
          first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0) := by
  obtain ⟨root, hL⟩ := bankRepairDigitGoneReachableValues ring hn hbank z hz
  have hq := ringQ_facts n hn
  have ht : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) hq.1
  have hprim := tapTablePrimitive (compileAdvice (ceilLogTwo n)).t ht
  obtain ⟨d, hd, hk⟩ := bankRepairDigitDelimiterLayout ring root _ hL.2 (by omega) hprim
  refine ⟨root, (compileAdvice (ceilLogTwo n)).t + d, hL, by omega, ?_, fun k h0 hkn => ?_⟩
  · unfold digitSpan; omega
  · rw [bankRepairDigitSiteShift]
    exact hk k h0 hkn

/-! ### Step 3: the flush split by region -/

/-- The leading half of receipt stability on the projected ring. -/
theorem bankRepairDigitLeadingStep {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c) (e : Fin n)
    (hfacts : BankRepairDigitLaneRowFacts c)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta)
    (h : DigitLeadingBoundary ring root S) :
    DigitLeadingBoundary ring root (phiD ring S e) := by
  have hb := (bankRepairDigitPhiDAt ring hn S e hbX hbY).2.2.2
  have hv := fun lane (T : Fin n → ProjD c) i => bankRepairDigitEndpointViewLane lane T i
  obtain ⟨first, stop, hseg, hlead, hsegc⟩ := h
  have hleadL : ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
      bankRepairDigitLaneOut lane (S (digitSite ring root k)).top = .E ∧
      bankRepairDigitLaneLive lane (S (digitSite ring root k)).top = false ∧
      DigitLeadingInput (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top) := by
    intro lane k hk0 hk1
    have h1 := hlead lane k hk0 hk1
    obtain ⟨e1, e2, e3⟩ := hv lane S (digitSite ring root k)
    dsimp only at h1
    rw [e1, e2, e3] at h1
    exact h1
  have hsegL : ∀ (lane : DigitLane) (k : Nat), first ≤ k → k < stop →
      BankRepairDigitSegOK n first k
        (bankRepairDigitLaneLive lane (S (digitSite ring root k)).top)
        (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top) := by
    intro lane k hk0 hk1
    have h1 := hsegc lane k hk0 hk1
    obtain ⟨e1, _, e3⟩ := hv lane S (digitSite ring root k)
    dsimp only [DigitLastCarryInert] at h1
    rw [e1, e3] at h1
    exact h1
  have hf0 : 0 < first := hseg.1.1.1
  have hfn : first < n := hseg.1.1.2.1
  have hfs : first < stop := hseg.2.2.1
  have hsn : stop ≤ n := hseg.2.2.2.1
  have hbeta0 := hseg.1.2
  have hbetaS := hseg.2.2.2.2.2
  refine ⟨first, stop, (bankRepairDigitFirstSegmentCongr ring root S _ hb first stop).2 hseg,
    ?_, ?_⟩
  · intro lane k hk0 hk1
    have h1 := bankRepairDigitLeadPrefixStep ring hn root S e hfacts hroot hbX hbY first hfn
      hbeta0 hleadL lane k hk0 hk1
    obtain ⟨e1, e2, e3⟩ := hv lane (phiD ring S e) (digitSite ring root k)
    dsimp only
    rw [e1, e2, e3]
    exact h1
  · intro lane k hk0 hk1
    have h1 := bankRepairDigitSegStep ring hn root S e hfacts hroot hbX hbY first stop
      hf0 hfs hsn hbetaS hleadL hsegL lane k hk0 hk1
    obtain ⟨e1, _, e3⟩ := hv lane (phiD ring S e) (digitSite ring root k)
    dsimp only [DigitLastCarryInert]
    rw [e1, e3]
    exact h1

/-- The final half of receipt stability on the projected ring. -/
theorem bankRepairDigitFinalBoundaryStep {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (root : Fin n) (S : Fin n → ProjD c) (e : Fin n)
    (hfacts : BankRepairDigitLaneRowFacts c)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta)
    (hfinal : DigitFinalBoundary ring root S) :
    DigitFinalBoundary ring root (phiD ring S e) := by
  have hb := (bankRepairDigitPhiDAt ring hn S e hbX hbY).2.2.2
  have hv := fun lane (T : Fin n → ProjD c) i => bankRepairDigitEndpointViewLane lane T i
  intro source last hblock hlast hnext lane k hk1 hk2
  have hblock' := (bankRepairDigitCompleteBlockCongr ring root S _ hb source).1 hblock
  have hnext' := (bankRepairDigitNextDelimiterCongr ring root S _ hb last n).1 hnext
  have hfinL : ∀ (lane : DigitLane) (k : Nat), last ≤ k → k < n →
      BankRepairDigitFinalOK n k
        (bankRepairDigitLaneLive lane (S (digitSite ring root k)).top)
        (bankRepairDigitLaneIn lane (S (digitSite ring root k)).top) := by
    intro lane k hk0 hk1
    have h1 := hfinal source last hblock' hlast hnext' lane k hk0 hk1
    obtain ⟨e1, _, e3⟩ := hv lane S (digitSite ring root k)
    dsimp only [DigitLastCarryInert] at h1
    rw [e1, e3] at h1
    exact h1
  have h1 := bankRepairDigitFinalStep ring hn root S e hfacts hroot hbX hbY last
    hnext'.1.1 hnext'.1.2.1 hnext'.1.2.2 hnext'.2.2.2.2 hfinL lane k hk1 hk2
  obtain ⟨e1, _, e3⟩ := hv lane (phiD ring S e) (digitSite ring root k)
  dsimp only [DigitLastCarryInert]
  rw [e1, e3]
  exact h1

/-- Lifting a projected-ring stable predicate to the BANK chain on the
layout-fixed class (no FIRE, no visible marker change, fixed leader). -/
theorem bankRepairDigitBankStepOf {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (P : (Fin n → ProjD (compileAdvice (ceilLogTwo n))) → Prop)
    (hP : ∀ (S : Fin n → ProjD (compileAdvice (ceilLogTwo n))) (e : Fin n),
      (∀ i, (S i).word.native.l = true ↔ i = root) →
      (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta →
      (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
        (S (ring.rightNeighbor e)).word.beta →
      P S → P (phiD ring S e))
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitLayoutFixed ring hbank root z) (e : Fin n)
    (h : P (piD z.val.1)) :
    P (piD (bankRepairNext ring hbank z e).val.1) := by
  rw [bankRepairDigitMaskedProjectionOfNoFire ring hbank z e
    (bankRepairDigitBoundaryNoFireOfSingleton ring hbank root z hz.1 e)]
  have hnb := (AcceptedReceipts.qword_step ring _ hz.2 e).1
  have hvis : ∀ i, AcceptedReceipts.wordVisible (phiW ring (piW z.val.1) e) i =
      AcceptedReceipts.wordVisible (piW z.val.1) i := by
    intro i
    exact Classical.byContradiction (fun hne => hnb ⟨i, hne⟩)
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring (by omega) e
  have hbX := congrArg Prod.snd (hvis e)
  have hbY := congrArg Prod.snd (hvis (ring.rightNeighbor e))
  simp only [AcceptedReceipts.wordVisible, phiW, projectedEdge, if_pos rfl,
    if_neg hne] at hbX hbY
  have hroot : ∀ i, (piD z.val.1 i).word.native.l = true ↔ i = root := by
    intro i
    constructor
    · exact fun hi => hz.1.2.2.1 i hi
    · rintro rfl; exact hz.1.2.1
  exact hP (piD z.val.1) e hroot hbX hbY h

/-- The leading half of the receipt at the actual (W fixed) leader. -/
def BankRepairDigitLeaderLeading {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ root : Fin n, WFixedRoot ring root (piW z.val.1) ∧
    DigitLeadingBoundary ring root (piD z.val.1)

/-- Gone-reachable states are closed under edges. -/
theorem bankRepairDigitGoneReachableStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitGoneReachable ring hbank z) (word : List (Fin n)) :
    BankRepairDigitGoneReachable ring hbank (word.foldl (bankRepairNext ring hbank) z) := by
  obtain ⟨z₀, w, hz₀, rfl⟩ := hz
  exact ⟨z₀, w ++ word, hz₀, by rw [List.foldl_append]⟩

/-- Once produced, the leading half of the receipt is never lost. -/
theorem bankRepairDigitLeaderLeadingStable {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitGoneReachable ring hbank z)
    (hrec : BankRepairDigitLeaderLeading ring hbank z) (word : List (Fin n)) :
    BankRepairDigitLeaderLeading ring hbank (word.foldl (bankRepairNext ring hbank) z) := by
  obtain ⟨root, hL⟩ := bankRepairDigitGoneReachableLayout ring hn hbank z hz
  obtain ⟨r, hW, hr⟩ := hrec
  have hrr : r = root := hL.1.2.2.1 r hW.1
  subst hrr
  refine ⟨r, bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank r z hL.1 word, ?_⟩
  have key : ∀ (w : List (Fin n)) (y : BankReferenceState ring hbank),
      BankRepairDigitLayoutFixed ring hbank r y →
      DigitLeadingBoundary ring r (piD y.val.1) →
      DigitLeadingBoundary ring r (piD (w.foldl (bankRepairNext ring hbank) y).val.1) := by
    intro w
    induction w with
    | nil => intro y _ h; exact h
    | cons e rest ih =>
        intro y hy h
        exact ih _ (bankRepairDigitLayoutFixedStep ring hn hbank r y hy e)
          (bankRepairDigitBankStepOf ring hn hbank r (DigitLeadingBoundary ring r)
            (fun S e hroot hbX hbY h => bankRepairDigitLeadingStep ring (by omega) r S e
              (bankRepairDigitLaneRowFactsHold _) hroot hbX hbY h) y hy e h)
  exact key word z hL hr

/-- A region task certificate: on every state reachable from `start`, a rank
that never increases before `target` and drops on one nominated edge, with
initial rank at most `budget`. -/
def BankRepairDigitRegionTasks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start target : BankReferenceState ring hbank → Prop) (budget : Nat) : Prop :=
  ∃ (rank : BankReferenceState ring hbank → Nat)
    (chosen : BankReferenceState ring hbank → Fin n),
    (∀ z₀ (word : List (Fin n)), start z₀ →
      ¬ target (word.foldl (bankRepairNext ring hbank) z₀) →
      rank (bankRepairNext ring hbank (word.foldl (bankRepairNext ring hbank) z₀)
          (chosen (word.foldl (bankRepairNext ring hbank) z₀))) + 1 ≤
        rank (word.foldl (bankRepairNext ring hbank) z₀)) ∧
    (∀ z₀ (word : List (Fin n)), start z₀ →
      ¬ target (word.foldl (bankRepairNext ring hbank) z₀) → ∀ e : Fin n,
      rank (bankRepairNext ring hbank (word.foldl (bankRepairNext ring hbank) z₀) e) ≤
        rank (word.foldl (bankRepairNext ring hbank) z₀)) ∧
    (∀ z, start z → rank z ≤ budget)

theorem bankRepairDigitRegionClockOfTasks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start target : BankReferenceState ring hbank → Prop) (budget : Nat)
    (htasks : BankRepairDigitRegionTasks ring hbank start target budget) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank) start target
      (2 * (n * budget)) := by
  obtain ⟨rank, chosen, hdrop, hnoninc, hcap⟩ := htasks
  intro z hz T
  let Reach : BankReferenceState ring hbank → Prop := fun y =>
    ∃ w : List (Fin n), y = w.foldl (bankRepairNext ring hbank) z
  have hsplit : ∀ y, ¬ (target y ∨ ¬ Reach y) → Reach y ∧ ¬ target y := fun y h =>
    ⟨Classical.byContradiction (fun hb => h (Or.inr hb)), fun ha => h (Or.inl ha)⟩
  have hcost := L3.Prob.costNumerator_le_of_nominated_edge
    (bankRepairNext ring hbank) (fun y => target y ∨ ¬ Reach y) rank chosen
    (fun y hy => by
      obtain ⟨⟨w, rfl⟩, ht⟩ := hsplit y hy
      exact hdrop z w hz ht)
    (fun y hy => by
      obtain ⟨⟨w, rfl⟩, ht⟩ := hsplit y hy
      exact hnoninc z w hz ht) z T
  have htransfer := bankRepairDigitCostTransfer (bankRepairNext ring hbank)
    (bankRepairNext ring hbank) target (fun y => target y ∨ ¬ Reach y) T z z
    (fun w hw => hw.resolve_right (fun hn' => hn' ⟨w, rfl⟩))
  have hle : costNumerator (bankRepairNext ring hbank) target z T ≤
      n ^ T * (n * budget) :=
    Nat.le_trans htransfer (Nat.le_trans hcost
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hcap z hz))))
  calc
    2 * costNumerator (bankRepairNext ring hbank) target z T ≤
        2 * (n ^ T * (n * budget)) := Nat.mul_le_mul_left 2 hle
    _ = n ^ T * (2 * (n * budget)) := Nat.mul_left_comm _ _ _

/-- The leading stage: from the gone cut to the leading half of the receipt. -/
def BankRepairDigitLeadingFlushTasks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (budget : Nat) : Prop :=
  BankRepairDigitRegionTasks ring hbank (BankRepairDigitWordStageGoneCut ring hbank)
    (fun z => BankRepairDigitGoneReachable ring hbank z ∧
      BankRepairDigitLeaderLeading ring hbank z) budget

/-- The final stage: from the leading half to the whole receipt. -/
def BankRepairDigitFinalFlushTasks {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (budget : Nat) : Prop :=
  BankRepairDigitRegionTasks ring hbank
    (fun z => BankRepairDigitGoneReachable ring hbank z ∧
      BankRepairDigitLeaderLeading ring hbank z)
    (fun z => BankRepairDigitGoneReachable ring hbank z ∧
      BankRepairDigitLeaderReceipt ring hbank z) budget

theorem bankRepairDigitAllGoneWord {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (w : List (Fin n)) (a : BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n),
      bankRepairDigitAllBaseLabelsGone ring hbank a →
      bankRepairDigitAllBaseLabelsGone ring hbank
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) a) := by
  intro w
  induction w with
  | nil => intro a h; exact h
  | cons e rest ih =>
      intro a h
      exact ih _ (bankRepairDigitAllBaseLabelsGoneClosed (by omega) ring hbank a e h)

/-- A gone-reachable state with the leader receipt is a boundary-retired cut. -/
theorem bankRepairDigitRetiredOfGoneReceipt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairDigitGoneReachable ring hbank z)
    (hrec : BankRepairDigitLeaderReceipt ring hbank z) :
    BankRepairDigitBoundaryRetiredCut ring hbank z := by
  obtain ⟨_, word', ⟨x, wordW, wordR, word, hx, _hW, hR, hg, rfl⟩, rfl⟩ := hz
  obtain ⟨root, hs⟩ := bankRepairDigitWordStageSingleton ring hn hbank x hx wordW wordR
  have hg' : bankRepairDigitAllBaseLabelsGone ring hbank
      ((word ++ word').foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (wordR.foldl (bankRepairNext ring hbank) (wordW.foldl (bankRepairNext ring hbank) x),
          digitAuditInitial (piD (wordR.foldl (bankRepairNext ring hbank)
            (wordW.foldl (bankRepairNext ring hbank) x)).val.1))) := by
    rw [List.foldl_append]
    exact bankRepairDigitAllGoneWord hn ring hbank word' _ hg
  obtain ⟨r, hW, hr⟩ := hrec
  have hr' : r = root := by
    have hfix := bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root _ hs
      (word ++ word')
    rw [List.foldl_append] at hfix
    exact hfix.2.1 r hW.1
  subst hr'
  have hcut := bankRepairDigitBoundaryCutOfReceipt ring hn hbank r _ hR hs (word ++ word') hg'
    (by rw [List.foldl_append]; exact hr)
  rw [List.foldl_append] at hcut
  exact hcut

/-- STEP 3, region split: two stage certificates whose budgets fit the
remainder give the flush clock at the REMAINDER of the boundary charge. -/
theorem bankRepairDigitFlushClockOfRegions {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (lead fin : Nat)
    (hfit : lead + fin ≤ bankRepairDigitFlushBudget n)
    (hlead : BankRepairDigitLeadingFlushTasks ring hbank lead)
    (hfin : BankRepairDigitFinalFlushTasks ring hbank fin) :
    BankRepairDigitReceiptFlushClock ring hbank (bankRepairDigitFlushMicroCharge n) := by
  have h := bankRepairDigitChargedCompose (bankRepairNext ring hbank)
    (BankRepairDigitWordStageGoneCut ring hbank)
    (fun z => BankRepairDigitGoneReachable ring hbank z ∧
      BankRepairDigitLeaderLeading ring hbank z)
    (fun z => BankRepairDigitGoneReachable ring hbank z ∧
      BankRepairDigitLeaderReceipt ring hbank z) _ _
    (bankRepairDigitRegionClockOfTasks ring hbank _ _ lead hlead)
    (bankRepairDigitRegionClockOfTasks ring hbank _ _ fin hfin)
  intro z hz T
  have htr := bankRepairDigitCostTransfer (bankRepairNext ring hbank)
    (bankRepairNext ring hbank) (BankRepairDigitBoundaryRetiredCut ring hbank)
    (fun z => BankRepairDigitGoneReachable ring hbank z ∧
      BankRepairDigitLeaderReceipt ring hbank z) T z z
    (fun w hw => bankRepairDigitRetiredOfGoneReceipt ring hn hbank _ hw.1 hw.2)
  refine Nat.le_trans (Nat.mul_le_mul_left 2 htr) (Nat.le_trans (h z hz T) ?_)
  apply Nat.mul_le_mul_left
  unfold bankRepairDigitFlushMicroCharge
  rw [← Nat.mul_add, ← Nat.mul_add]
  exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left n hfit)

/-- The flush clock at the remainder from the two region certificates at the
paper's budgets: `2 J` (leading fragment, `J` per lane) and `F + R + U + r`
(final leader sink). The fit is discharged by `bankRepairDigitFlushBudgetPays`. -/
theorem bankRepairDigitFlushClockOfPaperRegions {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hlead : BankRepairDigitLeadingFlushTasks ring hbank
      (2 * bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n))))
    (hfin : BankRepairDigitFinalFlushTasks ring hbank
      (bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)))) :
    BankRepairDigitReceiptFlushClock ring hbank (bankRepairDigitFlushMicroCharge n) :=
  bankRepairDigitFlushClockOfRegions ring hn hbank _ _
    (by have h := (bankRepairDigitFlushBudgetPays hbank).2; omega) hlead hfin

/-- STEP 3 composition from the region certificates: the strengthened
first-zero clock from every W-stage entrance at boundary plus first-zero. -/
theorem bankRepairDigitFirstZeroReceiptOfRegions {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (hlead : BankRepairDigitLeadingFlushTasks ring hbank
      (2 * bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n))))
    (hfin : BankRepairDigitFinalFlushTasks ring hbank
      (bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))))
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank)
      (fun z => cuts.firstBlockZero z ∧ BankRepairDigitLeaderReceipt ring hbank z)
      (bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n) :=
  bankRepairDigitFirstZeroReceiptOfWordStage ring hn hbank cuts
    (bankRepairDigitFlushClockOfPaperRegions ring hn hbank hlead hfin) hzero

/-- STEP 3 composition from the region certificates: the 201-half pre-drain
from every W-stage entrance, no fit hypothesis. -/
theorem bankRepairDigitPreDrain201OfRegions {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hlead : BankRepairDigitLeadingFlushTasks ring hbank
      (2 * bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n))))
    (hfin : BankRepairDigitFinalFlushTasks ring hbank
      (bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))))
    (hzero : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankRepairDigitBoundaryRetiredCut ring hbank) cuts.firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n))
    (hwave : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.firstBlockZero cuts.successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n))
    (hpair : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      cuts.successorValuesStable preDrain
      (bankRepairDigitComparisonMicroCharge n)) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDigitWordStageEntrance ring hbank) preDrain 201 :=
  bankRepairDigitPreDrain201OfRemainderFlush ring hn hbank cuts preDrain
    (bankRepairDigitFlushClockOfPaperRegions ring hn hbank hlead hfin) hzero hwave hpair

/-! ### Leading-fragment weights: the interior literal-row inequalities

Weights for one lane of the leading fragment. An internal input at distance `L`
to the next delimiter weighs `0` (empty or settled non-tail), `L` (front), `L+1`
(settled tail, which becomes a front), `L+R+2` (moving operand); a live carry
weighs `L`. A prefix output at distance `a` from the first delimiter weighs
`a+2R+2` (non-tail), `a+2R+3` (reread request), and the quadratic tail weight
`bankRepairDigitTailW`, because a passing tail leaves a reread at every site.
For every interior edge (both endpoints non-leader, non-delimiter) the literal
row never increases the two-site weight, and it drops when the initiator
carries weight and the responder none. -/

/-- Leading-fragment input weight at an internal site at distance `L` to the
next delimiter (`R` = segment length). -/
def bankRepairDigitSegInW {A : Nat} (R L : Nat) : InTok A → Nat
  | .E => 0
  | .X => L
  | .P _ _ => L + R + 2
  | .S _ T => if T then L + 1 else 0

def bankRepairDigitLiveW (L : Nat) (b : Bool) : Nat := if b then L else 0

/-- A tail output at distance `a` from the first delimiter: it leaves a reread
behind at every site it passes. -/
def bankRepairDigitTailW (R : Nat) : Nat → Nat
  | 0 => 2 * R + 2
  | a + 1 => bankRepairDigitTailW R a + a + 2 * R + 5

theorem bankRepairDigitTailWPos (R : Nat) : ∀ a, 2 * R + 2 ≤ bankRepairDigitTailW R a := by
  intro a
  induction a with
  | zero => simp [bankRepairDigitTailW]
  | succ a ih => simp only [bankRepairDigitTailW]; omega

/-- Output weight at a prefix site at distance `a` from the first delimiter. -/
def bankRepairDigitPreOutW {A : Nat} (R a : Nat) : OutTok A → Nat
  | .E => 0
  | .U => a + 2 * R + 3
  | .D _ T => if T then bankRepairDigitTailW R a else a + 2 * R + 2

theorem bankRepairDigitWriterSegSeg (c : Compiled) (ox oy : Agent c) (R d : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = false) :
    bankRepairDigitSegInW R (d + 1) (liveTopPair c ox oy).x.wIn +
      bankRepairDigitLiveW (d + 1) (liveTopPair c ox oy).x.wCarry.isW +
      bankRepairDigitSegInW R d (liveTopPair c ox oy).y.wIn +
      bankRepairDigitLiveW d (liveTopPair c ox oy).y.wCarry.isW ≤
    bankRepairDigitSegInW R (d + 1) ox.wIn + bankRepairDigitLiveW (d + 1) ox.wCarry.isW +
      bankRepairDigitSegInW R d oy.wIn + bankRepairDigitLiveW d oy.wCarry.isW := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hi : ox.wIn <;> cases hc : ox.wCarry <;> cases hi2 : oy.wIn <;>
    cases hc2 : oy.wCarry <;>
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly, hb,
        hby, hi, hc, hi2, hc2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW,
        OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT,
        bankRepairDigitSegInW, bankRepairDigitLiveW] <;>
    (repeat' split) <;> (try simp_all) <;> omega

theorem bankRepairDigitWriterSegSegStrict (c : Compiled) (ox oy : Agent c) (R d : Nat)
    (hd : 1 ≤ d) (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false)
    (hby : oy.beta = false)
    (hx : 1 ≤ bankRepairDigitSegInW R (d + 1) ox.wIn +
      bankRepairDigitLiveW (d + 1) ox.wCarry.isW)
    (hy : bankRepairDigitSegInW R d oy.wIn + bankRepairDigitLiveW d oy.wCarry.isW = 0) :
    bankRepairDigitSegInW R (d + 1) (liveTopPair c ox oy).x.wIn +
      bankRepairDigitLiveW (d + 1) (liveTopPair c ox oy).x.wCarry.isW +
      bankRepairDigitSegInW R d (liveTopPair c ox oy).y.wIn +
      bankRepairDigitLiveW d (liveTopPair c ox oy).y.wCarry.isW + 1 ≤
    bankRepairDigitSegInW R (d + 1) ox.wIn + bankRepairDigitLiveW (d + 1) ox.wCarry.isW +
      bankRepairDigitSegInW R d oy.wIn + bankRepairDigitLiveW d oy.wCarry.isW := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hi : ox.wIn <;> cases hc : ox.wCarry <;> cases hi2 : oy.wIn <;>
    cases hc2 : oy.wCarry <;>
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly, hb,
        hby, hi, hc, hi2, hc2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, WCarry.isOff, WCarry.isW,
        OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT,
        bankRepairDigitSegInW, bankRepairDigitLiveW] at hx hy ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> omega

theorem bankRepairDigitWriterPreOut (c : Compiled) (ox oy : Agent c) (R a : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = false) :
    bankRepairDigitPreOutW R (a + 1) (liveTopPair c ox oy).x.wOut +
      bankRepairDigitPreOutW R a (liveTopPair c ox oy).y.wOut ≤
    bankRepairDigitPreOutW R (a + 1) ox.wOut + bankRepairDigitPreOutW R a oy.wOut := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases ho : ox.wOut <;> cases ho2 : oy.wOut <;>
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly, hb,
        hby, ho, ho2, OutTok.isD, OutTok.isU, OutTok.isE, outT, bankRepairDigitPreOutW,
        bankRepairDigitTailW] <;>
    (repeat' split) <;> (try simp_all [bankRepairDigitTailW]) <;> omega

theorem bankRepairDigitWriterPreOutStrict (c : Compiled) (ox oy : Agent c) (R a : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = false)
    (hx : 1 ≤ bankRepairDigitPreOutW R (a + 1) ox.wOut)
    (hy : bankRepairDigitPreOutW R a oy.wOut = 0) :
    bankRepairDigitPreOutW R (a + 1) (liveTopPair c ox oy).x.wOut +
      bankRepairDigitPreOutW R a (liveTopPair c ox oy).y.wOut + 1 ≤
    bankRepairDigitPreOutW R (a + 1) ox.wOut + bankRepairDigitPreOutW R a oy.wOut := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  have hpos := bankRepairDigitTailWPos R a
  cases ho : ox.wOut <;> cases ho2 : oy.wOut <;>
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly, hb,
        hby, ho, ho2, OutTok.isD, OutTok.isU, OutTok.isE, outT, bankRepairDigitPreOutW,
        bankRepairDigitTailW] at hx hy ⊢ <;>
    (try split at hx) <;> (try split at hy) <;>
    (repeat' split) <;> (try simp_all [bankRepairDigitTailW]) <;> omega

theorem bankRepairDigitComparisonSegSeg (c : Compiled) (ox oy : Agent c) (R d : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = false) :
    bankRepairDigitSegInW R (d + 1) (liveTopPair c ox oy).x.qIn +
      bankRepairDigitLiveW (d + 1) (liveTopPair c ox oy).x.qCarry.isL +
      bankRepairDigitSegInW R d (liveTopPair c ox oy).y.qIn +
      bankRepairDigitLiveW d (liveTopPair c ox oy).y.qCarry.isL ≤
    bankRepairDigitSegInW R (d + 1) ox.qIn + bankRepairDigitLiveW (d + 1) ox.qCarry.isL +
      bankRepairDigitSegInW R d oy.qIn + bankRepairDigitLiveW d oy.qCarry.isL := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hi : ox.qIn <;> cases hc : ox.qCarry <;> cases hi2 : oy.qIn <;>
    cases hc2 : oy.qCarry <;>
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly, hb,
        hby, hi, hc, hi2, hc2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL,
        OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT,
        bankRepairDigitSegInW, bankRepairDigitLiveW] <;>
    (repeat' split) <;> (try simp_all) <;> omega

theorem bankRepairDigitComparisonSegSegStrict (c : Compiled) (ox oy : Agent c) (R d : Nat)
    (hd : 1 ≤ d) (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false)
    (hby : oy.beta = false)
    (hx : 1 ≤ bankRepairDigitSegInW R (d + 1) ox.qIn +
      bankRepairDigitLiveW (d + 1) ox.qCarry.isL)
    (hy : bankRepairDigitSegInW R d oy.qIn + bankRepairDigitLiveW d oy.qCarry.isL = 0) :
    bankRepairDigitSegInW R (d + 1) (liveTopPair c ox oy).x.qIn +
      bankRepairDigitLiveW (d + 1) (liveTopPair c ox oy).x.qCarry.isL +
      bankRepairDigitSegInW R d (liveTopPair c ox oy).y.qIn +
      bankRepairDigitLiveW d (liveTopPair c ox oy).y.qCarry.isL + 1 ≤
    bankRepairDigitSegInW R (d + 1) ox.qIn + bankRepairDigitLiveW (d + 1) ox.qCarry.isL +
      bankRepairDigitSegInW R d oy.qIn + bankRepairDigitLiveW d oy.qCarry.isL := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hi : ox.qIn <;> cases hc : ox.qCarry <;> cases hi2 : oy.qIn <;>
    cases hc2 : oy.qCarry <;>
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly, hb,
        hby, hi, hc, hi2, hc2, InTok.isX, InTok.isS, InTok.isP, InTok.isE, QCarry.isOff, QCarry.isL,
        OutTok.isD, OutTok.isU, OutTok.isE, topInternal, topTerminal, topBorder, inT,
        bankRepairDigitSegInW, bankRepairDigitLiveW] at hx hy ⊢ <;>
    (repeat' split) <;> (try simp_all) <;> omega

theorem bankRepairDigitComparisonPreOut (c : Compiled) (ox oy : Agent c) (R a : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = false) :
    bankRepairDigitPreOutW R (a + 1) (liveTopPair c ox oy).x.qOut +
      bankRepairDigitPreOutW R a (liveTopPair c ox oy).y.qOut ≤
    bankRepairDigitPreOutW R (a + 1) ox.qOut + bankRepairDigitPreOutW R a oy.qOut := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases ho : ox.qOut <;> cases ho2 : oy.qOut <;>
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly, hb,
        hby, ho, ho2, OutTok.isD, OutTok.isU, OutTok.isE, outT, bankRepairDigitPreOutW,
        bankRepairDigitTailW] <;>
    (repeat' split) <;> (try simp_all [bankRepairDigitTailW]) <;> omega

theorem bankRepairDigitComparisonPreOutStrict (c : Compiled) (ox oy : Agent c) (R a : Nat)
    (hl : ox.l = false) (hly : oy.l = false) (hb : ox.beta = false) (hby : oy.beta = false)
    (hx : 1 ≤ bankRepairDigitPreOutW R (a + 1) ox.qOut)
    (hy : bankRepairDigitPreOutW R a oy.qOut = 0) :
    bankRepairDigitPreOutW R (a + 1) (liveTopPair c ox oy).x.qOut +
      bankRepairDigitPreOutW R a (liveTopPair c ox oy).y.qOut + 1 ≤
    bankRepairDigitPreOutW R (a + 1) ox.qOut + bankRepairDigitPreOutW R a oy.qOut := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
      liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
      liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  have hpos := bankRepairDigitTailWPos R a
  cases ho : ox.qOut <;> cases ho2 : oy.qOut <;>
    simp [↓liveTopPair_x_wIn, ↓liveTopPair_y_wIn, ↓liveTopPair_x_wCarry, ↓liveTopPair_y_wCarry,
        ↓liveTopPair_x_wOut, ↓liveTopPair_y_wOut, ↓liveTopPair_x_qIn, ↓liveTopPair_y_qIn,
        ↓liveTopPair_x_qCarry, ↓liveTopPair_y_qCarry, ↓liveTopPair_x_qOut, ↓liveTopPair_y_qOut,
        liveTopWC, liveTopWI, liveTopWO, liveTopQC, liveTopQI, liveTopQO, liveTopPair, hl, hly, hb,
        hby, ho, ho2, OutTok.isD, OutTok.isU, OutTok.isE, outT, bankRepairDigitPreOutW,
        bankRepairDigitTailW] at hx hy ⊢ <;>
    (try split at hx) <;> (try split at hy) <;>
    (repeat' split) <;> (try simp_all [bankRepairDigitTailW]) <;> omega

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitSplitArith
#print axioms L3.RenewalReferenceClock.bankRepairDigitBoundaryChargeSplit
#print axioms L3.RenewalReferenceClock.bankRepairDigitFlushBudgetPays
#print axioms L3.RenewalReferenceClock.bankRepairDigitWordStageGoneExtinctionClock
#print axioms L3.RenewalReferenceClock.bankRepairDigitChargedMono
#print axioms L3.RenewalReferenceClock.bankRepairDigitFlushClockOfRemainderTasks
#print axioms L3.RenewalReferenceClock.bankRepairDigitFirstZeroReceiptOfWordStage
#print axioms L3.RenewalReferenceClock.bankRepairDigitPreDrain201OfRemainderFlush
#print axioms L3.RenewalReferenceClock.bankRepairDigitPreDrain201OfRemainderTasks
#print axioms L3.RenewalReferenceClock.bankRepairDigitTrailingFold
#print axioms L3.RenewalReferenceClock.bankRepairDigitRecIterMulFixed
#print axioms L3.RenewalReferenceClock.bankRepairDigitOnesReturn
#print axioms L3.RenewalReferenceClock.bankRepairDigitDelimiterLayout
#print axioms L3.RenewalReferenceClock.bankRepairDigitLayoutValuesStep
#print axioms L3.RenewalReferenceClock.bankRepairDigitLayoutValuesWord
#print axioms L3.RenewalReferenceClock.bankRepairDigitGoneReachableValues
#print axioms L3.RenewalReferenceClock.bankRepairDigitSiteShift
#print axioms L3.RenewalReferenceClock.bankRepairDigitGoneReachableDelimiters
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeadingStep
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalBoundaryStep
#print axioms L3.RenewalReferenceClock.bankRepairDigitBankStepOf
#print axioms L3.RenewalReferenceClock.bankRepairDigitGoneReachableStep
#print axioms L3.RenewalReferenceClock.bankRepairDigitLeaderLeadingStable
#print axioms L3.RenewalReferenceClock.bankRepairDigitRegionClockOfTasks
#print axioms L3.RenewalReferenceClock.bankRepairDigitAllGoneWord
#print axioms L3.RenewalReferenceClock.bankRepairDigitRetiredOfGoneReceipt
#print axioms L3.RenewalReferenceClock.bankRepairDigitFlushClockOfRegions
#print axioms L3.RenewalReferenceClock.bankRepairDigitFlushClockOfPaperRegions
#print axioms L3.RenewalReferenceClock.bankRepairDigitFirstZeroReceiptOfRegions
#print axioms L3.RenewalReferenceClock.bankRepairDigitPreDrain201OfRegions
#print axioms L3.RenewalReferenceClock.bankRepairDigitTailWPos
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterSegSeg
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterSegSegStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterPreOut
#print axioms L3.RenewalReferenceClock.bankRepairDigitWriterPreOutStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonSegSeg
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonSegSegStrict
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonPreOut
#print axioms L3.RenewalReferenceClock.bankRepairDigitComparisonPreOutStrict

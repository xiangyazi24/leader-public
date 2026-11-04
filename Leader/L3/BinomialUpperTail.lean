import Leader.L3.Grant.DrainLabelTail

/-!
Upper binomial tail of a predictable nominated-edge count.

The short count is imported unchanged. The long count and its
base-two weight obey the same two-branch recurrence.
This module proves the exact upper-tail moment inequality.
The final numerical quarter-tail rate remains an explicit premise.

Paper: research/paper/l3/appendices/repair.tex 1054--1084.
-/

namespace L3.BinomialUpperTail

open L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-- The number of length-T words with at least Q nominated hits.
A hit has one letter, a miss has n-1 possible letters. -/
def binomialUpperLong (n : Nat) : Nat → Nat → Nat
  | 0, Q => if Q = 0 then 1 else 0
  | T + 1, 0 => n * binomialUpperLong n T 0
  | T + 1, Q + 1 =>
      binomialUpperLong n T Q +
        (n - 1) * binomialUpperLong n T (Q + 1)

/-- On the same upper tail, the weight is 2^(hits).
The hit branch doubles its contribution, while misses do not. -/
def binomialUpperWeighted (n : Nat) : Nat → Nat → Nat
  | 0, Q => if Q = 0 then 1 else 0
  | T + 1, 0 => (n + 1) * binomialUpperWeighted n T 0
  | T + 1, Q + 1 =>
      2 * binomialUpperWeighted n T Q +
        (n - 1) * binomialUpperWeighted n T (Q + 1)

/-- The imported strict lower tail has no words below zero hits. -/
private theorem binomialUpperShortZero (n T : Nat) :
    grantDrainLabelBinomialShort n T 0 = 0 := by
  induction T with
  | zero => rfl
  | succ T ih =>
      simp [grantDrainLabelBinomialShort, ih]

private theorem binomialUpperShortPositive (n T Q : Nat) :
    grantDrainLabelBinomialShort n (T + 1) (Q + 1) =
      grantDrainLabelBinomialShort n T Q +
        (n - 1) *
          grantDrainLabelBinomialShort n T (Q + 1) := by
  simp [grantDrainLabelBinomialShort]

private theorem binomialUpperLongZero (n T : Nat) :
    binomialUpperLong n T 0 = n ^ T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      change n * binomialUpperLong n T 0 = n ^ (T + 1)
      rw [ih, Nat.pow_succ, Nat.mul_comm]

private theorem binomialUpperWeightedZero (n T : Nat) :
    binomialUpperWeighted n T 0 = (n + 1) ^ T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      change (n + 1) * binomialUpperWeighted n T 0 =
        (n + 1) ^ (T + 1)
      rw [ih, Nat.pow_succ, Nat.mul_comm]

/-- Every length-T word lies in exactly one of the strict
lower tail and the inclusive upper tail. -/
theorem binomialUpperShortLongPartition
    (n T Q : Nat) (hn : 0 < n) :
    grantDrainLabelBinomialShort n T Q +
      binomialUpperLong n T Q = n ^ T := by
  induction T generalizing Q with
  | zero =>
      cases Q with
      | zero => rfl
      | succ Q => rfl
  | succ T ih =>
      cases Q with
      | zero =>
          rw [binomialUpperShortZero]
          change 0 + n * binomialUpperLong n T 0 = n ^ (T + 1)
          rw [binomialUpperLongZero, Nat.zero_add, Nat.pow_succ]
          exact Nat.mul_comm _ _
      | succ Q =>
          rw [binomialUpperShortPositive]
          change
            (grantDrainLabelBinomialShort n T Q +
                (n - 1) *
                  grantDrainLabelBinomialShort n T (Q + 1)) +
              (binomialUpperLong n T Q +
                (n - 1) *
                  binomialUpperLong n T (Q + 1)) =
              n ^ (T + 1)
          calc
            _ = (grantDrainLabelBinomialShort n T Q +
                  binomialUpperLong n T Q) +
                (n - 1) *
                  (grantDrainLabelBinomialShort n T (Q + 1) +
                    binomialUpperLong n T (Q + 1)) := by
                simp only [Nat.mul_add, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm]
            _ = n ^ T + (n - 1) * n ^ T := by
                rw [ih Q, ih (Q + 1)]
            _ = n ^ (T + 1) := by
                have hcoef : 1 + (n - 1) = n := by omega
                rw [Nat.pow_succ]
                calc
                  n ^ T + (n - 1) * n ^ T =
                      (1 + (n - 1)) * n ^ T := by
                        rw [Nat.add_mul, Nat.one_mul]
                  _ = n * n ^ T := by rw [hcoef]
                  _ = n ^ T * n := Nat.mul_comm _ _

/-- On the upper-tail event, 2^hits is at least 2^Q.
This follows by induction on the weighted-count recurrence. -/
theorem binomialUpperLongWeightLower (n T Q : Nat) :
    2 ^ Q * binomialUpperLong n T Q ≤
      binomialUpperWeighted n T Q := by
  induction T generalizing Q with
  | zero =>
      cases Q with
      | zero => simp [binomialUpperLong, binomialUpperWeighted]
      | succ Q => simp [binomialUpperLong, binomialUpperWeighted]
  | succ T ih =>
      cases Q with
      | zero =>
          rw [Nat.pow_zero, Nat.one_mul]
          change n * binomialUpperLong n T 0 ≤
            (n + 1) * binomialUpperWeighted n T 0
          have hprev : binomialUpperLong n T 0 ≤
              binomialUpperWeighted n T 0 := by
            simpa only [Nat.pow_zero, Nat.one_mul] using ih 0
          calc
            n * binomialUpperLong n T 0 ≤
                n * binomialUpperWeighted n T 0 :=
              Nat.mul_le_mul_left n hprev
            _ ≤ (n + 1) * binomialUpperWeighted n T 0 :=
              Nat.mul_le_mul_right _ (Nat.le_succ n)
      | succ Q =>
          change
            2 ^ (Q + 1) *
                (binomialUpperLong n T Q +
                  (n - 1) * binomialUpperLong n T (Q + 1)) ≤
              2 * binomialUpperWeighted n T Q +
                (n - 1) * binomialUpperWeighted n T (Q + 1)
          calc
            _ = 2 * (2 ^ Q * binomialUpperLong n T Q) +
                (n - 1) *
                  (2 ^ (Q + 1) *
                    binomialUpperLong n T (Q + 1)) := by
                  rw [Nat.mul_add]
                  simp only [Nat.pow_succ, Nat.mul_assoc,
                    Nat.mul_left_comm, Nat.mul_comm]
            _ ≤ 2 * binomialUpperWeighted n T Q +
                  (n - 1) * binomialUpperWeighted n T (Q + 1) :=
              Nat.add_le_add
                (Nat.mul_le_mul_left 2 (ih Q))
                (Nat.mul_le_mul_left (n - 1) (ih (Q + 1)))

/-- The full exponential moment is (n+1)^T:
one nominated hit has weight two; each other letter weight one.
The upper-tail contribution cannot exceed the full sum. -/
theorem binomialUpperWeightedTotal
    (n T Q : Nat) (hn : 0 < n) :
    binomialUpperWeighted n T Q ≤ (n + 1) ^ T := by
  induction T generalizing Q with
  | zero =>
      cases Q with
      | zero => simp [binomialUpperWeighted]
      | succ Q => simp [binomialUpperWeighted]
  | succ T ih =>
      cases Q with
      | zero =>
          change (n + 1) * binomialUpperWeighted n T 0 ≤
            (n + 1) ^ (T + 1)
          rw [binomialUpperWeightedZero, Nat.pow_succ,
            Nat.mul_comm]
          exact Nat.le_refl _
      | succ Q =>
          change
            2 * binomialUpperWeighted n T Q +
              (n - 1) * binomialUpperWeighted n T (Q + 1) ≤
                (n + 1) ^ (T + 1)
          have hc : 2 + (n - 1) = n + 1 := by omega
          calc
            _ ≤ 2 * (n + 1) ^ T +
                (n - 1) * (n + 1) ^ T :=
              Nat.add_le_add
                (Nat.mul_le_mul_left 2 (ih Q))
                (Nat.mul_le_mul_left (n - 1) (ih (Q + 1)))
            _ = (2 + (n - 1)) * (n + 1) ^ T := by
              rw [Nat.add_mul]
            _ = (n + 1) ^ (T + 1) := by
              rw [hc, Nat.pow_succ, Nat.mul_comm]

/-- Main R10a exponential moment, all n>0, T and Q.
The cumulative mass of >=Q nominated hits is bounded by (n+1)^T. -/
theorem grantDrainLabelBinomialUpperMoment
    (n T Q : Nat) (hn : 0 < n) :
    2 ^ Q *
      (n ^ T - grantDrainLabelBinomialShort n T Q) ≤
        (n + 1) ^ T := by
  have hpartition :=
    binomialUpperShortLongPartition n T Q hn
  have hsub :
      n ^ T - grantDrainLabelBinomialShort n T Q =
        binomialUpperLong n T Q := by
    rw [← hpartition]
    omega
  rw [hsub]
  exact Nat.le_trans
    (binomialUpperLongWeightLower n T Q)
    (binomialUpperWeightedTotal n T Q hn)

/-- Exact R10a quarter-tail consumer. An independently established
numerical moment rate yields the 1/4 bound. The parameter-specific
moment rate has NOT been proved here. -/
theorem grantDrainLabelBinomialUpperQuarterOfMoment
    (n T Q : Nat) (hn : 0 < n)
    (hrate : 4 * (n + 1) ^ T ≤ 2 ^ Q * n ^ T) :
    4 * (n ^ T - grantDrainLabelBinomialShort n T Q) ≤
      n ^ T := by
  have hmoment := grantDrainLabelBinomialUpperMoment n T Q hn
  have hscaled := Nat.mul_le_mul_left 4 hmoment
  have htotal : 2 ^ Q *
      (4 * (n ^ T - grantDrainLabelBinomialShort n T Q)) ≤
      2 ^ Q * n ^ T := by
    calc
      2 ^ Q *
          (4 * (n ^ T - grantDrainLabelBinomialShort n T Q)) =
        4 * (2 ^ Q *
          (n ^ T - grantDrainLabelBinomialShort n T Q)) := by
            simp only [Nat.mul_assoc, Nat.mul_comm,
              Nat.mul_left_comm]
      _ ≤ 4 * (n + 1) ^ T := hscaled
      _ ≤ 2 ^ Q * n ^ T := hrate
  exact Nat.le_of_mul_le_mul_left htotal
    (by exact Nat.pow_pos (by decide : 0 < (2 : Nat)))

end L3.BinomialUpperTail

/-!
R10a BANK-band upper-tail exponent argument.
Intended continuation: Leader/L3/BinomialUpperTail.lean.
Paper repair.tex 1054--1084.
-/

namespace L3.BinomialUpperTail

open L3
open L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-- Quadratic induction step for the paper's unit exponential
moment: (n+1)^n <= 3*n^n, without Nat.choose or factorial. -/
private theorem bankUpperQuadraticStep
    (n k : Nat) (hk : k < n) :
    (n + 1) * (n * n + k * n + k * k) ≤
      n * (n * n + (k + 1) * n + (k + 1) * (k + 1)) := by
  have hquad : k * k ≤ (k + 1) * n := by
    calc
      k * k ≤ k * n :=
        Nat.mul_le_mul_left k (Nat.le_of_lt hk)
      _ ≤ (k + 1) * n :=
        Nat.mul_le_mul_right n (Nat.le_succ k)
  have hcoef : k * n + (k + 1) * n =
      (2 * k + 1) * n := by
    calc
      k * n + (k + 1) * n =
          (k + (k + 1)) * n := (Nat.add_mul _ _ _).symm
      _ = (2 * k + 1) * n := by
        rw [show k + (k + 1) = 2 * k + 1 by omega]
  have hcharge :
      n * n + k * n + k * k ≤ n * (n + 2 * k + 1) := by
    calc
      n * n + k * n + k * k =
          n * n + (k * n + k * k) := by omega
      _ ≤ n * n + (k * n + (k + 1) * n) :=
        Nat.add_le_add_left
          (Nat.add_le_add_left hquad (k * n)) (n * n)
      _ = n * (n + 2 * k + 1) := by
        rw [hcoef]
        rw [show n + 2 * k + 1 = n + (2 * k + 1) by omega,
          Nat.mul_add, Nat.mul_comm n (2 * k + 1)]
  have hsquare :
      (k + 1) * (k + 1) = k * k + (2 * k + 1) := by
    calc
      (k + 1) * (k + 1) =
          (k + 1) * k + (k + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
      _ = k * k + (2 * k + 1) := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
  have hnext :
      (n * n + k * n + k * k) + (n + 2 * k + 1) =
        n * n + (k + 1) * n + (k + 1) * (k + 1) := by
    rw [hsquare, Nat.add_mul, Nat.one_mul]
    omega
  calc
    (n + 1) * (n * n + k * n + k * k) =
        n * (n * n + k * n + k * k) +
          (n * n + k * n + k * k) := by
            rw [Nat.add_mul, Nat.one_mul]
    _ ≤ n * (n * n + k * n + k * k) +
          n * (n + 2 * k + 1) :=
      Nat.add_le_add_left hcharge _
    _ = n * ((n * n + k * n + k * k) +
          (n + 2 * k + 1)) := (Nat.mul_add n _ _).symm
    _ = n * (n * n + (k + 1) * n +
          (k + 1) * (k + 1)) := by rw [hnext]

/-- Quadratic strengthening, valid for every k<=n.
At k=n the coefficient on the right is exactly 3*n^2. -/
private theorem bankUpperQuadraticPower
    (n : Nat) :
    ∀ k : Nat, k ≤ n →
      (n * n) * (n + 1) ^ k ≤
        n ^ k * (n * n + k * n + k * k) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro hk
      have hprevious := ih (show k ≤ n by omega)
      have hstep := bankUpperQuadraticStep n k
        (show k < n by omega)
      calc
        (n * n) * (n + 1) ^ (k + 1) =
            ((n * n) * (n + 1) ^ k) * (n + 1) := by
              rw [Nat.pow_succ]; simp only [Nat.mul_assoc]
        _ ≤ (n ^ k * (n * n + k * n + k * k)) *
              (n + 1) := Nat.mul_le_mul_right _ hprevious
        _ = n ^ k *
              ((n + 1) * (n * n + k * n + k * k)) := by
              simp only [Nat.mul_assoc, Nat.mul_comm,
                Nat.mul_left_comm]
        _ ≤ n ^ k *
              (n * (n * n + (k + 1) * n +
                (k + 1) * (k + 1))) :=
          Nat.mul_le_mul_left _ hstep
        _ = n ^ (k + 1) *
              (n * n + (k + 1) * n +
                (k + 1) * (k + 1)) := by
              rw [Nat.pow_succ, Nat.mul_assoc]

/-- The promised core-only bound from repair.tex 1067.
Its proof uses a quadratic invariant, not a binomial library. -/
theorem bankUpperUnitPower
    (n : Nat) (hn : 0 < n) :
    (n + 1) ^ n ≤ 3 * n ^ n := by
  have hratio := bankUpperQuadraticPower n n (Nat.le_refl n)
  have hcoef : n * n + n * n + n * n = 3 * (n * n) := by
    omega
  have hscaled :
      (n * n) * (n + 1) ^ n ≤
        (n * n) * (3 * n ^ n) := by
    calc
      (n * n) * (n + 1) ^ n ≤
          n ^ n * (n * n + n * n + n * n) := hratio
      _ = (n * n) * (3 * n ^ n) := by
        rw [hcoef]
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.mul_pos hn hn)

/-- Opaque-block exponentiation: this is the reusable
power conversion consumed by the R10a H=2Cn² rate. -/
private theorem bankUpperUnitBlockPower
    (n blocks : Nat) (h : (n + 1) ^ n ≤ 3 * n ^ n) :
    (n + 1) ^ (n * blocks) ≤
      3 ^ blocks * n ^ (n * blocks) := by
  have hp := Nat.pow_le_pow_left h blocks
  simpa only [Nat.mul_pow, ← Nat.pow_mul] using hp

/-- Correct coarse inequality starts at n=8 for every C>=1.
The old n>=6,C>=1 route is false; this base avoids it. -/
private theorem bankUpperThreeBaseEight
    (n : Nat) (hn : 8 ≤ n) :
    4 * 3 ^ (2 * n) ≤ 2 ^ (4 * (n - 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, n = 8 + k :=
    ⟨n - 8, by omega⟩
  subst n
  induction k with
  | zero =>
      change (172186884 : Nat) ≤ 268435456
      omega
  | succ k ih =>
      have hleft : 2 * (8 + (k + 1)) =
          2 * (8 + k) + 2 := by omega
      have hright : 4 * ((8 + (k + 1)) - 1) =
          4 * ((8 + k) - 1) + 4 := by omega
      rw [hleft, hright, Nat.pow_add, Nat.pow_add]
      have hf : 3 ^ 2 ≤ 2 ^ 4 := by decide
      calc
        4 * (3 ^ (2 * (8 + k)) * 3 ^ 2) =
            (4 * 3 ^ (2 * (8 + k))) * 3 ^ 2 := by
              rw [Nat.mul_assoc]
        _ ≤ 2 ^ (4 * ((8 + k) - 1)) * 3 ^ 2 :=
          Nat.mul_le_mul_right _ (ih (by omega))
        _ ≤ 2 ^ (4 * ((8 + k) - 1)) * 2 ^ 4 :=
          Nat.mul_le_mul_left _ hf

/-- The exact paper coarse rate is valid for every C>=1
once n>=8. In particular, the actual BANK band is included. -/
theorem bankUpperThreeEpoch
    (n C : Nat) (hn : 8 ≤ n) (hC : 1 ≤ C) :
    4 * 3 ^ (2 * C * n) ≤
      2 ^ (4 * C * (n - 1)) := by
  have hpow :
      4 ^ C * 3 ^ (2 * C * n) ≤
        2 ^ (4 * C * (n - 1)) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (Nat.pow_le_pow_left (bankUpperThreeBaseEight n hn) C)
  have hfour : 4 ≤ 4 ^ C := by
    simpa only [Nat.pow_one] using
      (Nat.pow_le_pow_right (by decide : 0 < (4 : Nat)) hC)
  calc
    4 * 3 ^ (2 * C * n) ≤
        4 ^ C * 3 ^ (2 * C * n) :=
      Nat.mul_le_mul_right _ hfour
    _ ≤ 2 ^ (4 * C * (n - 1)) := hpow

/-- Opaque-parameter bridge: raise the single n-service
unit bound to 2Cn blocks and pay for it with the coarse rate. -/
private theorem bankUpperRateOfCoefficient
    (n C : Nat) (hn : 8 ≤ n) (hC : 1 ≤ C) :
    4 * (n + 1) ^ (2 * C * n ^ 2) ≤
      2 ^ (4 * C * (n - 1)) * n ^ (2 * C * n ^ 2) := by
  have hnpos : 0 < n := by omega
  have hcanonical :
      n * (2 * C * n) = 2 * C * n ^ 2 := by
    simp only [Nat.pow_two, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm]
  have hpower := bankUpperUnitBlockPower n (2 * C * n)
    (bankUpperUnitPower n hnpos)
  rw [hcanonical] at hpower
  have hcoarse := bankUpperThreeEpoch n C hn hC
  calc
    4 * (n + 1) ^ (2 * C * n ^ 2) ≤
        4 * (3 ^ (2 * C * n) *
          n ^ (2 * C * n ^ 2)) :=
      Nat.mul_le_mul_left 4 hpower
    _ = (4 * 3 ^ (2 * C * n)) *
          n ^ (2 * C * n ^ 2) := (Nat.mul_assoc _ _ _).symm
    _ ≤ 2 ^ (4 * C * (n - 1)) *
          n ^ (2 * C * n ^ 2) :=
      Nat.mul_le_mul_right _ hcoarse

/-- qStar=79: the BANK predicate forces ceilLogTwo n>=80,
hence n>=9 by Nat.le_log2. No production band is assumed. -/
private theorem bankUpperBankBandEight
    (n : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    8 ≤ n := by
  have hs :
      (compileAdvice (ceilLogTwo n)).useSmall =
        decide (ceilLogTwo n ≤ qStar) := rfl
  have hb := hbank
  rw [hs] at hb
  have hnot : ¬ ceilLogTwo n ≤ 79 := by
    have hh := of_decide_eq_false hb
    change ¬ ceilLogTwo n ≤ 79 at hh
    exact hh
  have hq : 80 ≤ ceilLogTwo n := by omega
  have hnlarge : ¬ n ≤ 1 := by
    intro hsmall
    have hz : ceilLogTwo n = 0 := by
      unfold ceilLogTwo
      rw [if_pos hsmall]
    omega
  have hqvalue :
      ceilLogTwo n = Nat.log2 (n - 1) + 1 := by
    unfold ceilLogTwo
    rw [if_neg hnlarge]
  have hnonzero : n - 1 ≠ 0 := by omega
  have hlog : 3 ≤ Nat.log2 (n - 1) := by omega
  have hpow : 2 ^ 3 ≤ n - 1 :=
    (Nat.le_log2 hnonzero).1 hlog
  change 8 ≤ n - 1 at hpow
  omega

/-- R10a paper 1067--1078, fully instantiated exponential
rate in the real BANK band, with H=2Cn² and Q=4C(n-1). -/
theorem bankUpperBankBandMomentRate
    (n : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    4 * (n + 1) ^
        (2 * (2 * ceilLogTwo (ceilLogTwo n) + 1) * n ^ 2) ≤
      2 ^ ((8 * ceilLogTwo (ceilLogTwo n) + 4) * (n - 1)) *
        n ^ (2 * (2 * ceilLogTwo (ceilLogTwo n) + 1) *
          n ^ 2) := by
  have hn := bankUpperBankBandEight n hbank
  have hC : 1 ≤ 2 * ceilLogTwo (ceilLogTwo n) + 1 := by
    omega
  have hrate := bankUpperRateOfCoefficient
    n (2 * ceilLogTwo (ceilLogTwo n) + 1) hn hC
  have hcoef :
      4 * (2 * ceilLogTwo (ceilLogTwo n) + 1) =
        8 * ceilLogTwo (ceilLogTwo n) + 4 := by
          omega
  rw [hcoef] at hrate
  exact hrate

/-- Unconditional R10a BANK-band 1/4 upper-tail numerator,
consuming grantDrainLabelBinomialUpperQuarterOfMoment. -/
theorem bankUpperBankBandInterruptionQuarter
    (n : Nat)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    4 * (n ^
          (2 * (2 * ceilLogTwo (ceilLogTwo n) + 1) * n ^ 2) -
        grantDrainLabelBinomialShort n
          (2 * (2 * ceilLogTwo (ceilLogTwo n) + 1) * n ^ 2)
          ((8 * ceilLogTwo (ceilLogTwo n) + 4) * (n - 1))) ≤
      n ^ (2 * (2 * ceilLogTwo (ceilLogTwo n) + 1) *
        n ^ 2) := by
  have hn := bankUpperBankBandEight n hbank
  exact grantDrainLabelBinomialUpperQuarterOfMoment
    n (2 * (2 * ceilLogTwo (ceilLogTwo n) + 1) * n ^ 2)
    ((8 * ceilLogTwo (ceilLogTwo n) + 4) * (n - 1))
    (by omega : 0 < n)
    (bankUpperBankBandMomentRate n hbank)

end L3.BinomialUpperTail

#print axioms L3.BinomialUpperTail.bankUpperUnitPower
#print axioms L3.BinomialUpperTail.bankUpperThreeEpoch
#print axioms L3.BinomialUpperTail.bankUpperBankBandMomentRate
#print axioms L3.BinomialUpperTail.bankUpperBankBandInterruptionQuarter

#print axioms L3.BinomialUpperTail.binomialUpperShortLongPartition
#print axioms L3.BinomialUpperTail.binomialUpperLongWeightLower
#print axioms L3.BinomialUpperTail.binomialUpperWeightedTotal
#print axioms L3.BinomialUpperTail.grantDrainLabelBinomialUpperMoment
#print axioms L3.BinomialUpperTail.grantDrainLabelBinomialUpperQuarterOfMoment
#print axioms L3.BinomialUpperTail.bankUpperUnitPower
#print axioms L3.BinomialUpperTail.bankUpperThreeEpoch
#print axioms L3.BinomialUpperTail.bankUpperBankBandMomentRate
#print axioms L3.BinomialUpperTail.bankUpperBankBandInterruptionQuarter

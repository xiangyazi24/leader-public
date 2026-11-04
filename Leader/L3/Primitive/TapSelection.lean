import Leader.L3.Primitive.FeedbackMask
import Leader.L3.Primitive.RecurrenceBridge
import Leader.L3.Primitive.NatFactors

/-!
The literal search for a primitive feedback mask and the exact
boolean-test/quotient-order bridge. Core Lean 4.33 only.
Consumers: the Params compiler switch and compileAdvice.

-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Unreduced polynomial powers add exponents.
Consumer: tapPolyPowModCorrect, then the Params compiler switch. -/
private theorem tapPolyPowerAdd (a m k : Nat) :
    tapPolyPow a (m + k) =
      tapPolyMul (tapPolyPow a m) (tapPolyPow a k) := by
  induction k with
  | zero =>
      simp only [Nat.add_zero, tapPolyPow]
      exact (tapPolyMulOneRight _).symm
  | succ k ih =>
      calc
        tapPolyPow a (m + (k + 1)) =
            tapPolyMul (tapPolyPow a (m + k)) a := by
          rw [Nat.add_succ]
          rfl
        _ = tapPolyMul (tapPolyMul (tapPolyPow a m)
              (tapPolyPow a k)) a := by rw [ih]
        _ = tapPolyMul (tapPolyPow a m)
              (tapPolyMul (tapPolyPow a k) a) :=
          tapPolyMulAssociative _ _ _
        _ = tapPolyMul (tapPolyPow a m)
              (tapPolyPow a (k + 1)) := rfl

/-- Unreduced polynomial powers multiply exponents.
Consumer: the exact repeated-square fuel proof. -/
private theorem tapPolyPowerMul (a m k : Nat) :
    tapPolyPow a (m * k) =
      tapPolyPow (tapPolyPow a m) k := by
  induction k with
  | zero =>
      simp only [Nat.mul_zero, tapPolyPow]
  | succ k ih =>
      calc
        tapPolyPow a (m * (k + 1)) =
            tapPolyPow a (m * k + m) := by rw [Nat.mul_succ]
        _ = tapPolyMul (tapPolyPow a (m * k))
              (tapPolyPow a m) := tapPolyPowerAdd a (m * k) m
        _ = tapPolyMul (tapPolyPow (tapPolyPow a m) k)
              (tapPolyPow a m) := by rw [ih]
        _ = tapPolyPow (tapPolyPow a m) (k + 1) := rfl

/-- Squaring the base and halving the exponent is algebraically
the same as doubling the exponent.
Consumer: tapPolyPowModCorrect. -/
private theorem tapPolyPowerSquare (a k : Nat) :
    tapPolyPow (tapPolyMul a a) k =
      tapPolyPow a (2 * k) := by
  have hsquare : tapPolyPow a 2 = tapPolyMul a a := by
    change tapPolyMul (tapPolyMul 1 a) a = tapPolyMul a a
    rw [tapPolyMulOneLeft]
  rw [← hsquare]
  exact (tapPolyPowerMul a 2 k).symm

/-- Product remainders depend only on each factor's canonical
class; the formula uses the actual polynomial remainder.
Consumer: tapPolyPowModCorrect, tapPeriodDvd, compileAdvice. -/
private theorem tapPolyRemProductClasses (a b f : Nat)
    (hf : f ≠ 0) :
    tapPolyRem (tapPolyMul a b) f =
      tapPolyRem
        (tapPolyMul (tapPolyRem a f) (tapPolyRem b f)) f := by
  calc
    tapPolyRem (tapPolyMul a b) f =
        tapPolyRem (tapPolyMul (tapPolyRem a f) b) f :=
      (tapPolyRemMulLeft a b f hf).symm
    _ = tapPolyRem
          (tapPolyMul (tapPolyRem a f) (tapPolyRem b f)) f :=
      (tapPolyRemMulRight (tapPolyRem a f) b f hf).symm

/-- Reducing the base before powering preserves the residue of
every unreduced polynomial power. Consumer: the fuel invariant. -/
private theorem tapPolyPowerReducedBase (a f k : Nat)
    (hf : f ≠ 0) :
    tapPolyRem (tapPolyPow (tapPolyRem a f) k) f =
      tapPolyRem (tapPolyPow a k) f := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        tapPolyRem (tapPolyPow (tapPolyRem a f) (k + 1)) f =
            tapPolyRem (tapPolyMul
              (tapPolyPow (tapPolyRem a f) k)
              (tapPolyRem a f)) f := rfl
        _ = tapPolyRem
              (tapPolyMul (tapPolyPow (tapPolyRem a f) k) a) f :=
          tapPolyRemMulRight _ a f hf
        _ = tapPolyRem
              (tapPolyMul
                (tapPolyRem (tapPolyPow (tapPolyRem a f) k) f)
                a) f :=
          (tapPolyRemMulLeft _ a f hf).symm
        _ = tapPolyRem
              (tapPolyMul
                (tapPolyRem (tapPolyPow a k) f) a) f := by rw [ih]
        _ = tapPolyRem (tapPolyMul (tapPolyPow a k) a) f :=
          tapPolyRemMulLeft _ a f hf
        _ = tapPolyRem (tapPolyPow a (k + 1)) f := rfl

/-- The loop invariant is the class of acc times base^exponent;
one nonzero iteration halves the exponent. Exact log-fuel is
enough even for exponent zero and modulus one.
Consumer: tapPolyPowModCorrect and the compiler's finite tests. -/
private theorem tapPolyPowModFuelInvariant
    (f base exponent acc fuel : Nat)
    (hf : f ≠ 0)
    (hacc : tapPolyRem acc f = acc)
    (hbudget : exponent = 0 ∨ Nat.log2 exponent < fuel) :
    tapPolyPowModFuel f base exponent acc fuel =
      tapPolyRem (tapPolyMul acc (tapPolyPow base exponent)) f := by
  induction fuel generalizing base exponent acc with
  | zero =>
      rcases hbudget with hz | hlt
      · subst exponent
        change acc = tapPolyRem (tapPolyMul acc 1) f
        rw [tapPolyMulOneRight, hacc]
      · omega
  | succ fuel ih =>
      by_cases hz : exponent = 0
      · subst exponent
        change acc = tapPolyRem (tapPolyMul acc 1) f
        rw [tapPolyMulOneRight, hacc]
      · have hhalf :
            exponent / 2 = 0 ∨ Nat.log2 (exponent / 2) < fuel := by
          by_cases hsmall : exponent / 2 = 0
          · exact Or.inl hsmall
          · have htwo : 2 ≤ exponent := by omega
            have hlog := Nat.log2_def exponent
            rw [if_pos htwo] at hlog
            rcases hbudget with he | hl
            · exact False.elim (hz he)
            · exact Or.inr (by omega)
        have haccNext :
            tapPolyRem
              (if exponent % 2 = 1 then
                tapPolyRem (tapPolyMul acc base) f else acc) f =
              (if exponent % 2 = 1 then
                tapPolyRem (tapPolyMul acc base) f else acc) := by
          by_cases hodd : exponent % 2 = 1
          · simp only [if_pos hodd]
            exact tapPolyRemIdem _ f hf
          · simp only [if_neg hodd]
            exact hacc
        have hrecursive :=
          ih (tapPolyRem (tapPolyMul base base) f)
            (exponent / 2)
            (if exponent % 2 = 1 then
              tapPolyRem (tapPolyMul acc base) f else acc)
            haccNext hhalf
        have hsquare :
            tapPolyRem (tapPolyMul
              (if exponent % 2 = 1 then
                tapPolyRem (tapPolyMul acc base) f else acc)
              (tapPolyPow
                (tapPolyRem (tapPolyMul base base) f)
                (exponent / 2))) f =
            tapPolyRem (tapPolyMul
              (if exponent % 2 = 1 then
                tapPolyRem (tapPolyMul acc base) f else acc)
              (tapPolyPow base (2 * (exponent / 2)))) f := by
          calc
            tapPolyRem (tapPolyMul
                (if exponent % 2 = 1 then
                  tapPolyRem (tapPolyMul acc base) f else acc)
                (tapPolyPow (tapPolyRem (tapPolyMul base base) f)
                  (exponent / 2))) f =
              tapPolyRem (tapPolyMul
                (if exponent % 2 = 1 then
                  tapPolyRem (tapPolyMul acc base) f else acc)
                (tapPolyRem
                  (tapPolyPow (tapPolyRem (tapPolyMul base base) f)
                    (exponent / 2)) f)) f :=
                (tapPolyRemMulRight _ _ f hf).symm
            _ = tapPolyRem (tapPolyMul
                  (if exponent % 2 = 1 then
                    tapPolyRem (tapPolyMul acc base) f else acc)
                  (tapPolyRem
                    (tapPolyPow (tapPolyMul base base)
                      (exponent / 2)) f)) f := by
                rw [tapPolyPowerReducedBase (tapPolyMul base base) f
                  (exponent / 2) hf]
            _ = tapPolyRem (tapPolyMul
                  (if exponent % 2 = 1 then
                    tapPolyRem (tapPolyMul acc base) f else acc)
                  (tapPolyPow (tapPolyMul base base)
                    (exponent / 2))) f :=
                tapPolyRemMulRight _ _ f hf
            _ = tapPolyRem (tapPolyMul
                  (if exponent % 2 = 1 then
                    tapPolyRem (tapPolyMul acc base) f else acc)
                  (tapPolyPow base (2 * (exponent / 2)))) f := by
                rw [tapPolyPowerSquare]
        have hdivision :
            exponent = 2 * (exponent / 2) + exponent % 2 := by omega
        calc
          tapPolyPowModFuel f base exponent acc (fuel + 1) =
              tapPolyRem (tapPolyMul
                (if exponent % 2 = 1 then
                  tapPolyRem (tapPolyMul acc base) f else acc)
                (tapPolyPow
                  (tapPolyRem (tapPolyMul base base) f)
                  (exponent / 2))) f := by
            simp only [tapPolyPowModFuel, if_neg hz]
            exact hrecursive
          _ = tapPolyRem (tapPolyMul
                (if exponent % 2 = 1 then
                  tapPolyRem (tapPolyMul acc base) f else acc)
                (tapPolyPow base (2 * (exponent / 2)))) f := hsquare
          _ = tapPolyRem (tapPolyMul acc (tapPolyPow base exponent)) f := by
            have hmodBound : exponent % 2 < 2 :=
              Nat.mod_lt _ (by decide : 0 < 2)
            by_cases hodd : exponent % 2 = 1
            · have hexponent :
                  exponent = 2 * (exponent / 2) + 1 := by omega
              rw [if_pos hodd]
              rw [tapPolyRemMulLeft (tapPolyMul acc base)
                (tapPolyPow base (2 * (exponent / 2))) f hf]
              rw [tapPolyMulAssociative]
              rw [tapPolyMulCommutative base
                (tapPolyPow base (2 * (exponent / 2)))]
              have hpowE : tapPolyPow base exponent =
                  tapPolyMul (tapPolyPow base (2 * (exponent / 2)))
                    base :=
                congrArg (tapPolyPow base) hexponent
              rw [hpowE]
            · have heven : exponent % 2 = 0 := by omega
              simp only [if_neg hodd]
              have hexp : exponent = 2 * (exponent / 2) := by omega
              rw [← hexp]

/-- The literal log2-fuel repeated-square routine computes
the exact polynomial quotient power, for every nonzero modulus.
Consumer: passesTests, the Params switch and compileAdvice. -/
theorem tapPolyPowModCorrect (a k f : Nat) (hf : f ≠ 0) :
    tapPolyPowMod a k f =
      tapPolyRem (tapPolyPow a k) f := by
  have hbudget : k = 0 ∨ Nat.log2 k < Nat.log2 k + 1 :=
    Or.inr (Nat.lt_succ_self _)
  have hacc := tapPolyRemIdem 1 f hf
  have hrun :=
    tapPolyPowModFuelInvariant f (tapPolyRem a f) k
      (tapPolyRem 1 f) (Nat.log2 k + 1)
      hf hacc hbudget
  unfold tapPolyPowMod
  rw [hrun]
  have hbase := tapPolyPowerReducedBase a f k hf
  calc
    tapPolyRem
        (tapPolyMul (tapPolyRem 1 f)
          (tapPolyPow (tapPolyRem a f) k)) f =
      tapPolyRem
        (tapPolyMul 1 (tapPolyPow (tapPolyRem a f) k)) f :=
      tapPolyRemMulLeft 1 _ f hf
    _ = tapPolyRem (tapPolyPow (tapPolyRem a f) k) f := by
      rw [tapPolyMulOneLeft]
    _ = tapPolyRem (tapPolyPow a k) f := hbase

/-- A period remains a period at every positive multiple,
using genuine canonical quotient multiplication.
Consumer: tapPeriodDvd and the primitive checks in compileAdvice. -/
private theorem tapPolyPowerPeriodMultiple
    (a f d q : Nat) (hf : f ≠ 0)
    (hone : tapPolyRem 1 f = 1)
    (hd : tapPolyRem (tapPolyPow a d) f = 1) :
    tapPolyRem (tapPolyPow a (d * q)) f = 1 := by
  induction q with
  | zero =>
      change tapPolyRem 1 f = 1
      exact hone
  | succ q ih =>
      calc
        tapPolyRem (tapPolyPow a (d * (q + 1))) f =
            tapPolyRem
              (tapPolyMul (tapPolyPow a (d * q))
                (tapPolyPow a d)) f := by
          rw [Nat.mul_succ, tapPolyPowerAdd]
        _ = tapPolyRem
              (tapPolyMul
                (tapPolyRem (tapPolyPow a (d * q)) f)
                (tapPolyRem (tapPolyPow a d) f)) f :=
          tapPolyRemProductClasses _ _ f hf
        _ = tapPolyRem (tapPolyMul 1 1) f := by
          rw [ih, hd]
        _ = 1 := by rw [tapPolyMulOneLeft, hone]

/-- Division with remainder on the exponent: the least positive
return time d divides any return time M. This does not appeal to
a forbidden Nat.find and does not assume irreducibility.
Consumer: tapOrderOfChecks, then the Params compiler switch. -/
theorem tapPeriodDvd
    (f M d : Nat) (hf : f ≠ 0)
    (hone : tapPolyRem 1 f = 1)
    (hdpos : 0 < d)
    (hperiod : tapPolyRem (tapPolyPow 2 d) f = 1)
    (hminimal : ∀ k : Nat, 0 < k → k < d →
      tapPolyRem (tapPolyPow 2 k) f ≠ 1)
    (hM : tapPolyRem (tapPolyPow 2 M) f = 1) :
    d ∣ M := by
  have hmultiple :=
    tapPolyPowerPeriodMultiple 2 f d (M / d) hf hone hperiod
  have hdecomp : M = d * (M / d) + M % d :=
    (Nat.div_add_mod M d).symm
  have hsmall : M % d < d := Nat.mod_lt M hdpos
  have hrem : tapPolyRem (tapPolyPow 2 (M % d)) f = 1 := by
    have hproduct :
        tapPolyRem (tapPolyPow 2 M) f =
          tapPolyRem
            (tapPolyMul
              (tapPolyPow 2 (d * (M / d)))
              (tapPolyPow 2 (M % d))) f := by
      calc
        tapPolyRem (tapPolyPow 2 M) f =
            tapPolyRem (tapPolyPow 2 (d * (M / d) + M % d)) f :=
          congrArg (fun n : Nat => tapPolyRem (tapPolyPow 2 n) f)
            hdecomp
        _ = _ := by rw [tapPolyPowerAdd]
    have hclasses :=
      tapPolyRemProductClasses
        (tapPolyPow 2 (d * (M / d)))
        (tapPolyPow 2 (M % d)) f hf
    rw [hclasses, hmultiple] at hproduct
    rw [hM] at hproduct
    have hunit : tapPolyRem
          (tapPolyMul 1
            (tapPolyRem (tapPolyPow 2 (M % d)) f)) f =
        tapPolyRem (tapPolyPow 2 (M % d)) f := by
      rw [tapPolyMulOneLeft, tapPolyRemIdem _ f hf]
    exact hunit.symm.trans hproduct.symm
  have hzero : M % d = 0 := by
    by_cases hr : M % d = 0
    · exact hr
    · have hpositive : 0 < M % d := Nat.pos_of_ne_zero hr
      exact False.elim ((hminimal (M % d) hpositive hsmall) hrem)
  exact Nat.dvd_of_mod_eq_zero hzero

/-- Finite least positive return time, obtained by strong
induction on a witnessed positive return rather than Nat.find.
Consumer: tapOrderOfChecks and compileAdvice. -/
private theorem tapLeastPositiveReturn (f : Nat) :
    ∀ bound : Nat,
      0 < bound →
      tapPolyRem (tapPolyPow 2 bound) f = 1 →
      ∃ d : Nat,
        0 < d ∧ d ≤ bound ∧
        tapPolyRem (tapPolyPow 2 d) f = 1 ∧
        ∀ k : Nat, 0 < k → k < d →
          tapPolyRem (tapPolyPow 2 k) f ≠ 1 := by
  intro bound
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
      intro hb hperiod
      by_cases hshort :
          ∃ k : Nat, 0 < k ∧ k < bound ∧
            tapPolyRem (tapPolyPow 2 k) f = 1
      · obtain ⟨k, hkpos, hklt, hkpow⟩ := hshort
        obtain ⟨d, hdpos, hdle, hdpow, hmin⟩ :=
          ih k hklt hkpos hkpow
        exact ⟨d, hdpos, Nat.le_trans hdle (Nat.le_of_lt hklt),
          hdpow, hmin⟩
      · refine ⟨bound, hb, Nat.le_refl _, hperiod, ?_⟩
        intro k hkpos hklt hpow
        exact hshort ⟨k, hkpos, hklt, hpow⟩

/-- Every literal prime-order Boolean test that returned true
excludes precisely its enumerated exponent M / p.
Consumer: tapOrderOfChecks, hence passesTests in Params. -/
private theorem tapPrimitivePrimeChecksExclude
    (m f : Nat) (factors : List Nat)
    (hchecks : tapPrimitivePrimeChecks m f factors = true) :
    ∀ p : Nat, p ∈ factors →
      tapPolyPowMod 2 (m / p) f ≠ 1 := by
  induction factors with
  | nil =>
      intro p hmem
      cases hmem
  | cons q rest ih =>
      by_cases heq : tapPolyPowMod 2 (m / q) f = 1
      · simp [tapPrimitivePrimeChecks, heq] at hchecks
      · have htail :
            tapPrimitivePrimeChecks m f rest = true := by
          simpa only [tapPrimitivePrimeChecks, if_neg heq] using hchecks
        intro p hmem
        rcases List.mem_cons.mp hmem with hhead | hrest
        · rw [hhead]
          exact heq
        · exact ih htail p hrest

/-- The two order families of the literal finite test rule out
every proper return exponent, using the least period and a
prime factor of M/d from the actual enumerated factor list.
Consumer: tapPassesTestsSound and compileAdvice. -/
theorem tapOrderOfChecks (t b : Nat)
    (ht : 2 ≤ t) (hb : b < 2 ^ t)
    (hM :
      tapPolyPowMod 2 (2 ^ t - 1) (2 ^ t + b) = 1)
    (hchecks :
      tapPrimitivePrimeChecks
        (2 ^ t - 1) (2 ^ t + b)
        (tapPrimeFactors (2 ^ t - 1)) = true) :
    ∀ k : Nat, 0 < k → k < 2 ^ t - 1 →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1 := by
  have htwo : 2 < 2 ^ t := by
    have hbound : 2 ^ 2 ≤ 2 ^ t :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) ht
    omega
  have hf : 2 ^ t + b ≠ 0 := by omega
  have hone : tapPolyRem 1 (2 ^ t + b) = 1 :=
    tapPolyRemSmall t b 1 hb (by omega)
  have hMpos : 0 < 2 ^ t - 1 := by omega
  have hMpow :
      tapPolyRem (tapPolyPow 2 (2 ^ t - 1)) (2 ^ t + b) = 1 := by
    rw [← tapPolyPowModCorrect 2 (2 ^ t - 1) (2 ^ t + b) hf]
    exact hM
  obtain ⟨d, hdpos, hdle, hdpow, hmin⟩ :=
    tapLeastPositiveReturn (2 ^ t + b)
      (2 ^ t - 1) hMpos hMpow
  have hdiv :
      d ∣ 2 ^ t - 1 :=
    tapPeriodDvd (2 ^ t + b) (2 ^ t - 1) d hf
      hone hdpos hdpow hmin hMpow
  have htotal : d = 2 ^ t - 1 := by
    by_cases hproper : d < 2 ^ t - 1
    · obtain ⟨p, hmem, hdp⟩ :=
        tapProperDivisorFactor (2 ^ t - 1) d
          hMpos hdiv hproper
      obtain hnot := tapPrimitivePrimeChecksExclude
        (2 ^ t - 1) (2 ^ t + b)
        (tapPrimeFactors (2 ^ t - 1)) hchecks p hmem
      exact False.elim
        (hnot ((tapPolyPowModCorrect
          2 ((2 ^ t - 1) / p) (2 ^ t + b) hf).trans
            (by
              obtain ⟨q, hq⟩ := hdp
              rw [hq]
              exact tapPolyPowerPeriodMultiple 2 (2 ^ t + b) d q
                hf hone hdpow)))
    · omega
  intro k hkpos hklt hreturn
  have hdivK :=
    tapPeriodDvd (2 ^ t + b) k d hf
      hone hdpos hdpow hmin hreturn
  have hbound := Nat.le_of_dvd hkpos hdivK
  omega

/-- A passing test has maximal quotient order, hence its
recurrence is primitive through the installed companion bridge.
Only the two proper-order test families are needed.
Consumer: Params, compileAdvice. -/
theorem tapPassesTestsSound
    (t b : Nat)
    (ht : 2 ≤ t) (hb : b < 2 ^ t) (hodd : b % 2 = 1)
    (h : passesTests t b = true) :
    IsPrimitive t (fun j => Nat.testBit b j) := by
  have hnotSmall : ¬ t < 2 := by omega
  have hnotEven : ¬ b % 2 = 0 := by omega
  have hnotLarge : ¬ 2 ^ t ≤ b := by omega
  unfold passesTests at h
  simp only [if_neg hnotSmall, if_neg hnotEven,
    if_neg hnotLarge] at h
  have hcombined :=
    (Bool.and_eq_true_iff.mp h).1
  have horderChecks :=
    (Bool.and_eq_true_iff.mp hcombined).2
  have hlast :=
    (Bool.and_eq_true_iff.mp h).2
  have htwo : 2 < 2 ^ t := by
    have hpow : 2 ^ 2 ≤ 2 ^ t :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) ht
    omega
  have hf : 2 ^ t + b ≠ 0 := by omega
  have hone : tapPolyRem 1 (2 ^ t + b) = 1 :=
    tapPolyRemSmall t b 1 hb (by omega)
  have hlastEqual :
      tapPolyPowMod 2 (2 ^ t - 1) (2 ^ t + b) = 1 := by
    have hh :
        tapPolyPowMod 2 (2 ^ t - 1) (2 ^ t + b) =
          tapPolyRem 1 (2 ^ t + b) := by
      simpa only [beq_iff_eq] using hlast
    rw [hone] at hh
    exact hh
  have hpower :
      tapPolyRem (tapPolyPow 2 (2 ^ t - 1))
        (2 ^ t + b) = 1 := by
    rw [← tapPolyPowModCorrect 2 (2 ^ t - 1) (2 ^ t + b) hf]
    exact hlastEqual
  have hproper :=
    tapOrderOfChecks t b ht hb hlastEqual horderChecks
  exact tapPrimitiveOfOrder t b ht hb hodd hpower hproper

/-- If every listed prime-divisor order test excludes 1,
the literal primitive-order loop returns true.
Consumer: tapPassesTestsOfOrder and compileAdvice. -/
private theorem tapPrimitivePrimeChecksAll
    (m f : Nat) (factors : List Nat)
    (h : ∀ p : Nat, p ∈ factors →
      tapPolyPowMod 2 (m / p) f ≠ 1) :
    tapPrimitivePrimeChecks m f factors = true := by
  induction factors with
  | nil =>
      rfl
  | cons p rest ih =>
      have hp : tapPolyPowMod 2 (m / p) f ≠ 1 :=
        h p (by simp)
      have ht :
          tapPrimitivePrimeChecks m f rest = true := by
        apply ih
        intro q hq
        exact h q (List.mem_cons_of_mem p hq)
      simp only [tapPrimitivePrimeChecks, if_neg hp, ht]

/-- If each specified gcd of a prime exponent quotient is one,
the literal irreducibility-check recursion returns true.
Consumer: tapPassesTestsOfOrder and compileAdvice. -/
private theorem tapIrreduciblePrimeChecksAll
    (t f : Nat) (factors : List Nat)
    (h : ∀ ell : Nat, ell ∈ factors →
      tapPolyGcd f
        (tapPolyAdd (tapPolyPowMod 2 (2 ^ (t / ell)) f) 2) = 1) :
    tapIrreduciblePrimeChecks t f factors = true := by
  induction factors with
  | nil =>
      rfl
  | cons ell rest ih =>
      have hhead :
          tapPolyGcd f
            (tapPolyAdd (tapPolyPowMod 2 (2 ^ (t / ell)) f) 2) = 1 :=
        h ell (by simp)
      have htail :
          tapIrreduciblePrimeChecks t f rest = true := by
        apply ih
        intro q hmem
        exact h q (List.mem_cons_of_mem ell hmem)
      simp only [tapIrreduciblePrimeChecks, if_pos hhead, htail]

/-- Literal characteristic-two factorization
X^(k+1)+X = X (X^k+1). The divisor and gcd arguments for
the Rabin test use this exact mask identity.
Consumer: tapPassesTestsOfOrder, compileAdvice. -/
private theorem tapPolyPowerAddX (k : Nat) :
    tapPolyAdd (tapPolyPow 2 (k + 1)) 2 =
      tapPolyMul 2 (tapPolyAdd (tapPolyPow 2 k) 1) := by
  calc
    tapPolyAdd (tapPolyPow 2 (k + 1)) 2 =
        tapPolyAdd (tapPolyMul (tapPolyPow 2 k) 2)
          (tapPolyMul 1 2) := by
      change tapPolyAdd (tapPolyMul (tapPolyPow 2 k) 2) 2 =
        tapPolyAdd (tapPolyMul (tapPolyPow 2 k) 2)
          (tapPolyMul 1 2)
      rw [tapPolyMulOneLeft]
    _ = tapPolyMul (tapPolyAdd (tapPolyPow 2 k) 1) 2 :=
      (tapPolyMulXorLeft (tapPolyPow 2 k) 1 2).symm
    _ = tapPolyMul 2 (tapPolyAdd (tapPolyPow 2 k) 1) := by
      rw [tapPolyMulCommutative]

/-- An irreducible polynomial with maximal X order passes
every listed Rabin gcd test: a nonunit common divisor would
divide X^(2^(t/ell))+X and hence force a proper X period.
Consumer: tapPassesTestsOfOrder and compileAdvice. -/
private theorem tapIrreduciblePrimeGcdOfOrder
    (t b ell : Nat)
    (ht : 2 ≤ t) (hb : b < 2 ^ t)
    (hirr : TapIrreducible (2 ^ t + b))
    (hprime : TapNatPrime ell) (hell : ell ∣ t)
    (hord : ∀ k : Nat, 0 < k → k < 2 ^ t - 1 →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1) :
    tapPolyGcd (2 ^ t + b)
      (tapPolyAdd
        (tapPolyPowMod 2 (2 ^ (t / ell)) (2 ^ t + b)) 2) = 1 := by
  have htwo : 2 < 2 ^ t := by
    have hpow : 2 ^ 2 ≤ 2 ^ t :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) ht
    omega
  have hf : 2 ^ t + b ≠ 0 := by omega
  have hone : tapPolyRem 1 (2 ^ t + b) = 1 :=
    tapPolyRemSmall t b 1 hb (by omega)
  have htwoReduced : tapPolyRem 2 (2 ^ t + b) = 2 :=
    tapPolyRemSmall t b 2 hb htwo
  have hell2 : 2 ≤ ell := hprime.1
  have hellpos : 0 < ell := by omega
  have hpos : 0 < t := by omega
  have hle : ell ≤ t := Nat.le_of_dvd hpos hell
  have hquotpos : 0 < t / ell :=
    Nat.div_pos hle hellpos
  have hquotlt : t / ell < t :=
    Nat.div_lt_self hpos (by omega : 1 < ell)
  have hpowLow : 2 ≤ 2 ^ (t / ell) := by
    have hh := Nat.pow_le_pow_right
      (by decide : 0 < (2 : Nat))
      (by omega : 1 ≤ t / ell)
    change 2 ≤ 2 ^ (t / ell) at hh
    exact hh
  have hpowHigh : 2 ^ (t / ell) < 2 ^ t := by
    have hh := Nat.pow_le_pow_right
      (by decide : 0 < (2 : Nat))
      (by omega : t / ell + 1 ≤ t)
    rw [Nat.pow_succ] at hh
    have hp := Nat.two_pow_pos (t / ell)
    omega
  have hkpos : 0 < 2 ^ (t / ell) - 1 := by omega
  have hklt : 2 ^ (t / ell) - 1 < 2 ^ t - 1 := by omega
  have hmodPower :
      tapPolyRem
        (tapPolyPowMod 2 (2 ^ (t / ell)) (2 ^ t + b))
        (2 ^ t + b) =
      tapPolyRem (tapPolyPow 2 (2 ^ (t / ell))) (2 ^ t + b) := by
    rw [tapPolyPowModCorrect 2 (2 ^ (t / ell)) (2 ^ t + b) hf]
    rw [tapPolyRemIdem _ (2 ^ t + b) hf]
  have hremEquivalent :
      tapPolyRem
        (tapPolyAdd (tapPolyPow 2 (2 ^ (t / ell))) 2)
        (2 ^ t + b) =
      tapPolyRem
        (tapPolyAdd
          (tapPolyPowMod 2 (2 ^ (t / ell)) (2 ^ t + b)) 2)
        (2 ^ t + b) := by
    rw [tapPolyRemAdd _ _ (2 ^ t + b) hf]
    rw [tapPolyRemAdd _ _ (2 ^ t + b) hf]
    rw [hmodPower]
  apply tapPolyGcdEqOneOfCoprime
    (2 ^ t + b)
    (tapPolyAdd
      (tapPolyPowMod 2 (2 ^ (t / ell)) (2 ^ t + b)) 2)
    (Or.inl hf)
  intro divisor hdivF hdivMask
  obtain ⟨quot, hfactorF⟩ := hdivF
  rcases hirr.2 quot divisor hfactorF with hunit | hdivUnit
  · have hsame : divisor = 2 ^ t + b := by
      rw [hunit, tapPolyMulOneLeft] at hfactorF
      exact hfactorF.symm
    have hmaskDvd :
        tapPolyDvd (2 ^ t + b)
          (tapPolyAdd
            (tapPolyPowMod 2 (2 ^ (t / ell)) (2 ^ t + b)) 2) := by
      rw [hsame] at hdivMask
      exact hdivMask
    have hmaskZero :=
      (tapPolyDvdIffRemZero _ (2 ^ t + b) hf).1 hmaskDvd
    have hsumZero :
        tapPolyRem
          (tapPolyAdd (tapPolyPow 2 (2 ^ (t / ell))) 2)
          (2 ^ t + b) = 0 :=
      hremEquivalent.trans hmaskZero
    have hfactor :
        tapPolyAdd (tapPolyPow 2 (2 ^ (t / ell))) 2 =
          tapPolyMul 2
            (tapPolyAdd
              (tapPolyPow 2 (2 ^ (t / ell) - 1)) 1) := by
      have hexp : (2 ^ (t / ell) - 1) + 1 =
          2 ^ (t / ell) := by omega
      rw [← hexp]
      exact tapPolyPowerAddX (2 ^ (t / ell) - 1)
    have hdivFull :
        tapPolyDvd (2 ^ t + b)
          (tapPolyMul 2
            (tapPolyAdd
              (tapPolyPow 2 (2 ^ (t / ell) - 1)) 1)) := by
      apply (tapPolyDvdIffRemZero _ (2 ^ t + b) hf).2
      rw [← hfactor]
      exact hsumZero
    rcases tapPolyEuclid (2 ^ t + b) 2
        (tapPolyAdd (tapPolyPow 2 (2 ^ (t / ell) - 1)) 1)
        hirr hdivFull with hdivTwo | hdivShort
    · have hz := (tapPolyDvdIffRemZero 2 (2 ^ t + b) hf).1
          hdivTwo
      rw [htwoReduced] at hz
      exact False.elim (by omega)
    · have hz :=
        (tapPolyDvdIffRemZero
          (tapPolyAdd (tapPolyPow 2 (2 ^ (t / ell) - 1)) 1)
          (2 ^ t + b) hf).1 hdivShort
      rw [tapPolyRemAdd _ _ (2 ^ t + b) hf, hone] at hz
      have hreturn :=
        (tapPolyAddEqZeroIff
          (tapPolyRem (tapPolyPow 2 (2 ^ (t / ell) - 1))
            (2 ^ t + b)) 1).1 hz
      exact False.elim (hord (2 ^ (t / ell) - 1)
        hkpos hklt hreturn)
  · exact hdivUnit

/-- All four literal families hold from an irreducible maximal
order mask, including the Frobenius and every gcd test.
Consumer: tapSelectedMaskSpec and the Params compiler switch. -/
theorem tapPassesTestsOfOrder
    (t b : Nat)
    (ht : 2 ≤ t) (hb : b < 2 ^ t) (hodd : b % 2 = 1)
    (hirr : TapIrreducible (2 ^ t + b))
    (hM :
      tapPolyRem (tapPolyPow 2 (2 ^ t - 1)) (2 ^ t + b) = 1)
    (hord : ∀ k : Nat, 0 < k → k < 2 ^ t - 1 →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1) :
    passesTests t b = true := by
  have htwo : 2 < 2 ^ t := by
    have hpow : 2 ^ 2 ≤ 2 ^ t :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) ht
    omega
  have hone : tapPolyRem 1 (2 ^ t + b) = 1 :=
    tapPolyRemSmall t b 1 hb (by omega)
  have htwoReduced : tapPolyRem 2 (2 ^ t + b) = 2 :=
    tapPolyRemSmall t b 2 hb htwo
  have hf : 2 ^ t + b ≠ 0 := by omega
  have hMpos : 0 < 2 ^ t - 1 := by omega
  have hMnext : 2 ^ t = (2 ^ t - 1) + 1 := by omega
  have hFrobenius :
      tapPolyPowMod 2 (2 ^ t) (2 ^ t + b) =
        tapPolyRem 2 (2 ^ t + b) := by
    rw [tapPolyPowModCorrect 2 (2 ^ t) (2 ^ t + b) hf]
    have hpowShift : tapPolyPow 2 (2 ^ t) =
        tapPolyPow 2 ((2 ^ t - 1) + 1) :=
      congrArg (tapPolyPow 2) hMnext
    rw [hpowShift]
    have hpowOne : tapPolyPow 2 1 = 2 := by
      change tapPolyMul 1 2 = 2
      exact tapPolyMulOneLeft 2
    calc
      tapPolyRem (tapPolyPow 2 ((2 ^ t - 1) + 1)) (2 ^ t + b) =
          tapPolyRem
            (tapPolyMul
              (tapPolyPow 2 (2 ^ t - 1))
              (tapPolyPow 2 1)) (2 ^ t + b) :=
        congrArg (fun x : Nat => tapPolyRem x (2 ^ t + b))
          (tapPolyPowerAdd 2 (2 ^ t - 1) 1)
      _ = tapPolyRem
            (tapPolyMul
              (tapPolyRem (tapPolyPow 2 (2 ^ t - 1)) (2 ^ t + b))
              (tapPolyRem (tapPolyPow 2 1) (2 ^ t + b)))
              (2 ^ t + b) :=
        tapPolyRemProductClasses _ _ (2 ^ t + b) hf
      _ = tapPolyRem (tapPolyMul 1 2) (2 ^ t + b) := by
        rw [hM, hpowOne, htwoReduced]
      _ = tapPolyRem 2 (2 ^ t + b) := by rw [tapPolyMulOneLeft]
  have hOrderChecks :
      tapPrimitivePrimeChecks (2 ^ t - 1) (2 ^ t + b)
        (tapPrimeFactors (2 ^ t - 1)) = true := by
    apply tapPrimitivePrimeChecksAll
    intro p hpMem
    obtain ⟨hp, hpDiv⟩ :=
      tapPrimeFactorsSound (2 ^ t - 1) p
        (by omega : 2 ≤ 2 ^ t - 1) hpMem
    have hppos : 0 < p := by have h := hp.1; omega
    have hpLt : 1 < p := by have h := hp.1; omega
    have hquotpos : 0 < (2 ^ t - 1) / p :=
      Nat.div_pos (Nat.le_of_dvd hMpos hpDiv) hppos
    have hquotlt : (2 ^ t - 1) / p < 2 ^ t - 1 :=
      Nat.div_lt_self hMpos hpLt
    intro hreturn
    exact hord ((2 ^ t - 1) / p) hquotpos hquotlt
      ((tapPolyPowModCorrect 2 ((2 ^ t - 1) / p)
        (2 ^ t + b) hf).symm ▸ hreturn)
  have hIrrChecks :
      tapIrreduciblePrimeChecks t (2 ^ t + b)
        (tapPrimeFactors t) = true := by
    apply tapIrreduciblePrimeChecksAll
    intro ell hmem
    obtain ⟨hprime, hdiv⟩ :=
      tapPrimeFactorsSound t ell ht hmem
    exact tapIrreduciblePrimeGcdOfOrder
      t b ell ht hb hirr hprime hdiv hord
  have hModPeriod :
      tapPolyPowMod 2 (2 ^ t - 1) (2 ^ t + b) =
        tapPolyRem 1 (2 ^ t + b) := by
    rw [tapPolyPowModCorrect 2 (2 ^ t - 1) (2 ^ t + b) hf]
    rw [hM, hone]
  have hnotSmall : ¬ t < 2 := by omega
  have hnotEven : ¬ b % 2 = 0 := by omega
  have hnotLarge : ¬ 2 ^ t ≤ b := by omega
  unfold passesTests
  simp only [if_neg hnotSmall, if_neg hnotEven, if_neg hnotLarge]
  simp [hIrrChecks, hFrobenius, hOrderChecks, hModPeriod]

/-- The uncached odd-mask choice used by Params for widths
at least eighteen. It is the literal first passing candidate
scanned by the finite 2^t-call search.
Consumer: the Params switch and compileAdvice. -/
def tapSelectedMask (t : Nat) : Nat :=
  tapSearchFuel t 0 1 (2 ^ t)

/-- Existence of a primitive odd mask provides an actual passing
odd witness in range; the installed search-fuel theorem returns
an in-range odd passing choice.
Consumer: tapSelectedPrimitive and compileAdvice. -/
theorem tapSelectedMaskSpec (t : Nat) (ht : 18 ≤ t) :
    (tapSelectedMask t) % 2 = 1 ∧
    tapSelectedMask t < 2 ^ t ∧
    passesTests t (tapSelectedMask t) = true := by
  obtain ⟨b, hb, hodd, hirr, hM, hord⟩ :=
    tapPrimitiveMaskExists t ht
  have htTwo : 2 ≤ t := by omega
  have hpass :=
    tapPassesTestsOfOrder t b htTwo hb hodd hirr hM hord
  have hoddForm : b = 1 + 2 * (b / 2) := by
    have hdecomp : b % 2 + 2 * (b / 2) = b :=
      Nat.mod_add_div b 2
    omega
  have hbound : 1 + 2 * (b / 2) < 2 ^ t := by
    rw [← hoddForm]
    exact hb
  have hformPass : passesTests t (1 + 2 * (b / 2)) = true := by
    rw [← hoddForm]
    exact hpass
  have hresult :=
    tapSearchReturnsPassing t (b / 2) hbound hformPass
  change
    (tapSelectedMask t) % 2 = 1 ∧
      tapSelectedMask t < 2 ^ t ∧
      passesTests t (tapSelectedMask t) = true
  exact hresult

/-- The selected uncached polynomial is primitive, from the
actual order soundness theorem and the finite search witness.
Consumer: the Params switch and compileAdvice. -/
theorem tapSelectedPrimitive (t : Nat) (ht : 18 ≤ t) :
    IsPrimitive t (fun j => Nat.testBit (tapSelectedMask t) j) := by
  obtain ⟨hodd, hbound, hpass⟩ :=
    tapSelectedMaskSpec t ht
  exact tapPassesTestsSound t (tapSelectedMask t)
    (by omega : 2 ≤ t) hbound hodd hpass

/-- The selected primitive mask has its constant coefficient
set: its least-significant bit is true.
Consumer: the Params switch and compileAdvice. -/
theorem tapSelectedZeroBit (t : Nat) (ht : 18 ≤ t) :
    Nat.testBit (tapSelectedMask t) 0 = true := by
  have hodd := (tapSelectedMaskSpec t ht).1
  rw [Nat.testBit_zero]
  exact decide_eq_true hodd

end L3

#print axioms L3.tapPassesTestsSound
#print axioms L3.tapPassesTestsOfOrder
#print axioms L3.tapSelectedPrimitive

/-!
F_2[X] arithmetic for the tap selection of main.tex rem:primitive-taps, below `Params`
so that the compiler can use it (R-TAPS).

A binary polynomial is encoded by a natural number whose bit j is
the coefficient of X^j.  The selected mask records the lower t
coefficients of X^t + sum_j b_j X^j, with b_0 = 1.
-/

namespace L3

set_option autoImplicit false

/-- Addition in F_2[X]. -/
def tapPolyAdd (a b : Nat) : Nat := Nat.xor a b

/-- Carry-less multiplication, scanning the second argument's bits. -/
def tapPolyMulFuel (a b acc : Nat) : Nat → Nat
  | 0 => acc
  | fuel + 1 =>
      if b = 0 then acc
      else
        tapPolyMulFuel (2 * a) (b / 2)
          (if b % 2 = 1 then tapPolyAdd acc a else acc) fuel

def tapPolyMul (a b : Nat) : Nat :=
  tapPolyMulFuel a b 0 (Nat.log2 b + 1)

/-- Remainder after cancelling leading bits of the dividend.
    Every nonzero polynomial over F_2 is monic. -/
def tapPolyRemFuel (f p : Nat) : Nat → Nat
  | 0 => p
  | fuel + 1 =>
      if f = 0 then p
      else if p = 0 then p
      else if Nat.log2 p < Nat.log2 f then p
      else
        tapPolyRemFuel f
          (tapPolyAdd p (f * 2 ^ (Nat.log2 p - Nat.log2 f)))
          fuel

def tapPolyRem (p f : Nat) : Nat :=
  if f = 0 then p
  else tapPolyRemFuel f p (Nat.log2 p + 1)

/-- Euclidean gcd in F_2[X], with a degree-bounded number of steps. -/
def tapPolyGcdFuel (a b : Nat) : Nat → Nat
  | 0 => a
  | fuel + 1 =>
      if b = 0 then a
      else tapPolyGcdFuel b (tapPolyRem a b) fuel

def tapPolyGcd (a b : Nat) : Nat :=
  tapPolyGcdFuel a b (Nat.log2 (max a b) + 2)

/-- Repeated squaring in F_2[X]/(f). -/
def tapPolyPowModFuel (f base exponent acc : Nat) : Nat → Nat
  | 0 => acc
  | fuel + 1 =>
      if exponent = 0 then acc
      else
        tapPolyPowModFuel f
          (tapPolyRem (tapPolyMul base base) f)
          (exponent / 2)
          (if exponent % 2 = 1 then
            tapPolyRem (tapPolyMul acc base) f
           else acc)
          fuel

def tapPolyPowMod (base exponent f : Nat) : Nat :=
  tapPolyPowModFuel f (tapPolyRem base f) exponent
    (tapPolyRem 1 f) (Nat.log2 exponent + 1)

/-- Strip all factors d, where the caller uses d >= 2. -/
def tapStripFactorFuel (m d : Nat) : Nat → Nat
  | 0 => m
  | fuel + 1 =>
      if d < 2 then m
      else if m % d != 0 then m
      else tapStripFactorFuel (m / d) d fuel

/-- Trial division in increasing order, retaining each prime divisor once. -/
def tapPrimeFactorsFuel (m d : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
      if m ≤ 1 then []
      else if m < d * d then [m]
      else if m % d = 0 then
        d :: tapPrimeFactorsFuel
          (tapStripFactorFuel m d (Nat.log2 m + 1))
          (d + 1) fuel
      else tapPrimeFactorsFuel m (d + 1) fuel

def tapPrimeFactors (m : Nat) : List Nat :=
  tapPrimeFactorsFuel m 2 m

/-- The gcd tests for all distinct prime divisors of t. -/
def tapIrreduciblePrimeChecks (t f : Nat) : List Nat → Bool
  | [] => true
  | ell :: rest =>
      if tapPolyGcd f
          (tapPolyAdd (tapPolyPowMod 2 (2 ^ (t / ell)) f) 2) = 1 then
        tapIrreduciblePrimeChecks t f rest
      else false

/-- The proper-order tests for all distinct prime divisors of M. -/
def tapPrimitivePrimeChecks (m f : Nat) : List Nat → Bool
  | [] => true
  | p :: rest =>
      if tapPolyPowMod 2 (m / p) f = 1 then false
      else tapPrimitivePrimeChecks m f rest

/-- The two finite tests of Remark rem:primitive-taps, for
    f = X^t + b and M = 2^t - 1. -/
def passesTests (t b : Nat) : Bool :=
  if t < 2 then false
  else if b % 2 = 0 then false
  else if 2 ^ t ≤ b then false
  else
    tapIrreduciblePrimeChecks t (2 ^ t + b) (tapPrimeFactors t) &&
    (tapPolyPowMod 2 (2 ^ t) (2 ^ t + b) ==
      tapPolyRem 2 (2 ^ t + b)) &&
    tapPrimitivePrimeChecks (2 ^ t - 1) (2 ^ t + b)
      (tapPrimeFactors (2 ^ t - 1)) &&
    (tapPolyPowMod 2 (2 ^ t - 1) (2 ^ t + b) ==
      tapPolyRem 1 (2 ^ t + b))

/-- Search the odd coefficient masks in numerical order, except
    for the cached candidate already considered first.  Exhausting
    the fuel returns 0. -/
def tapSearchFuel (t skip candidate : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      if 2 ^ t ≤ candidate then 0
      else if candidate = skip then
        tapSearchFuel t skip (candidate + 2) fuel
      else if passesTests t candidate then candidate
      else tapSearchFuel t skip (candidate + 2) fuel


/-!
Normalization and ring laws of the bit-mask polynomials.
-/

private theorem tapPowTwoSucc (k : Nat) :
    2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [Nat.pow_succ]
  omega

private theorem tapModulusDegree (t b : Nat)
    (hb : b < 2 ^ t) :
    Nat.log2 (2 ^ t + b) = t := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hp : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  apply (Nat.log2_eq_iff hf).2
  constructor
  · omega
  · rw [tapPowTwoSucc]
    omega

private theorem tapShiftTop (t b d : Nat)
    (hb : b < 2 ^ t) (hd : t ≤ d) :
    2 ^ d ≤ (2 ^ t + b) * 2 ^ (d - t) ∧
    (2 ^ t + b) * 2 ^ (d - t) < 2 ^ (d + 1) := by
  have he : t + (d - t) = d := by omega
  have hpow : 2 ^ t * 2 ^ (d - t) = 2 ^ d := by
    calc
      2 ^ t * 2 ^ (d - t) = 2 ^ (t + (d - t)) :=
        (Nat.pow_add 2 t (d - t)).symm
      _ = 2 ^ d := by rw [he]
  have hscaled : b * 2 ^ (d - t) < 2 ^ d := by
    rw [← hpow]
    exact Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
  have hrepr :
      (2 ^ t + b) * 2 ^ (d - t) =
        2 ^ d + b * 2 ^ (d - t) := by
    rw [Nat.add_mul, hpow]
  constructor
  · rw [hrepr]
    omega
  · rw [hrepr, tapPowTwoSucc]
    omega

private theorem tapCancelTop (p z d : Nat)
    (hpLo : 2 ^ d ≤ p) (hpHi : p < 2 ^ (d + 1))
    (hzLo : 2 ^ d ≤ z) (hzHi : z < 2 ^ (d + 1)) :
    tapPolyAdd p z < 2 ^ d := by
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have hpDivLo : 1 ≤ p / 2 ^ d :=
    (Nat.one_le_div_iff hpos).2 hpLo
  have hpDivHi : p / 2 ^ d ≤ 1 :=
    (Nat.div_le_iff_le_mul_add_pred hpos).2 (by
      rw [tapPowTwoSucc] at hpHi
      omega)
  have hzDivLo : 1 ≤ z / 2 ^ d :=
    (Nat.one_le_div_iff hpos).2 hzLo
  have hzDivHi : z / 2 ^ d ≤ 1 :=
    (Nat.div_le_iff_le_mul_add_pred hpos).2 (by
      rw [tapPowTwoSucc] at hzHi
      omega)
  have hpDiv : p / 2 ^ d = 1 := by omega
  have hzDiv : z / 2 ^ d = 1 := by omega
  have hcancel : (p ^^^ z) / 2 ^ d = 0 := by
    rw [Nat.xor_div_two_pow, hpDiv, hzDiv, Nat.xor_self]
  change (p ^^^ z) < 2 ^ d
  rcases (Nat.div_eq_zero_iff.mp hcancel) with hzero | hlt
  · omega
  · exact hlt

private theorem tapPolyRemFuelSmall (t b : Nat)
    (hb : b < 2 ^ t) :
    ∀ (fuel p : Nat), (p = 0 ∨ Nat.log2 p < fuel) →
      tapPolyRemFuel (2 ^ t + b) p fuel < 2 ^ t := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hp : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  have hdeg : Nat.log2 (2 ^ t + b) = t :=
    tapModulusDegree t b hb
  intro fuel
  induction fuel with
  | zero =>
      intro p h
      rcases h with hz | hl
      · subst p
        simpa [tapPolyRemFuel] using (Nat.two_pow_pos t)
      · omega
  | succ fuel ih =>
      intro p h
      by_cases hp : p = 0
      · simpa [tapPolyRemFuel, hf, hp] using (Nat.two_pow_pos t)
      · have hbudget : Nat.log2 p < fuel + 1 := by
          rcases h with hz | hl
          · exact False.elim (hp hz)
          · exact hl
        by_cases hlow : Nat.log2 p < t
        · have hpSmall : p < 2 ^ t :=
            (Nat.log2_lt hp).1 hlow
          have hstep :
              tapPolyRemFuel (2 ^ t + b) p (fuel + 1) = p := by
            simp [tapPolyRemFuel, hf, hp, hdeg, hlow]
          rw [hstep]
          exact hpSmall
        · have hd : t ≤ Nat.log2 p := by omega
          have hprange :
              2 ^ (Nat.log2 p) ≤ p ∧
                p < 2 ^ (Nat.log2 p + 1) :=
            (Nat.log2_eq_iff hp).1 rfl
          have hshift :=
            tapShiftTop t b (Nat.log2 p) hb hd
          have hsmaller :
              tapPolyAdd p
                ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)) <
                2 ^ (Nat.log2 p) :=
            tapCancelTop p
              ((2 ^ t + b) * 2 ^ (Nat.log2 p - t))
              (Nat.log2 p) hprange.1 hprange.2
              hshift.1 hshift.2
          have hstep :
              tapPolyRemFuel (2 ^ t + b) p (fuel + 1) =
              tapPolyRemFuel (2 ^ t + b)
                (tapPolyAdd p
                  ((2 ^ t + b) * 2 ^ (Nat.log2 p - t))) fuel := by
            simp [tapPolyRemFuel, hf, hp, hdeg, hlow]
          rw [hstep]
          by_cases hz :
              tapPolyAdd p
                ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)) = 0
          · exact ih _ (Or.inl hz)
          · have hdrop :
                Nat.log2 (tapPolyAdd p
                  ((2 ^ t + b) * 2 ^ (Nat.log2 p - t))) <
                  Nat.log2 p :=
              (Nat.log2_lt hz).2 hsmaller
            have hnext :
                Nat.log2 (tapPolyAdd p
                  ((2 ^ t + b) * 2 ^ (Nat.log2 p - t))) <
                  fuel := by omega
            exact ih _ (Or.inr hnext)

/-- Item (1)(a): every remainder lies below degree t. -/
theorem tapPolyRemBelow (t b a : Nat)
    (hb : b < 2 ^ t) :
    tapPolyRem a (2 ^ t + b) < 2 ^ t := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hp : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  unfold tapPolyRem
  rw [if_neg hf]
  exact tapPolyRemFuelSmall t b hb (Nat.log2 a + 1) a
    (Or.inr (Nat.lt_succ_self _))

/-- Item (1)(a): already reduced masks are unchanged. -/
theorem tapPolyRemSmall (t b a : Nat)
    (hb : b < 2 ^ t) (ha : a < 2 ^ t) :
    tapPolyRem a (2 ^ t + b) = a := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hp : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  have hdeg : Nat.log2 (2 ^ t + b) = t :=
    tapModulusDegree t b hb
  by_cases hz : a = 0
  · subst a
    simp [tapPolyRem, hf, tapPolyRemFuel]
  · have hlow : Nat.log2 a < t :=
      (Nat.log2_lt hz).2 ha
    simp [tapPolyRem, hf, tapPolyRemFuel, hz, hdeg, hlow]

theorem tapPolyRemIdempotent (t b a : Nat)
    (hb : b < 2 ^ t) :
    tapPolyRem (tapPolyRem a (2 ^ t + b)) (2 ^ t + b) =
      tapPolyRem a (2 ^ t + b) := by
  exact tapPolyRemSmall t b _ hb (tapPolyRemBelow t b a hb)

/-- The source file has no separately named reduced product. -/
def tapPolyMulMod (a b f : Nat) : Nat :=
  tapPolyRem (tapPolyMul a b) f

theorem tapPolyMulModBelow (t b a c : Nat)
    (hb : b < 2 ^ t) :
    tapPolyMulMod a c (2 ^ t + b) < 2 ^ t := by
  exact tapPolyRemBelow t b (tapPolyMul a c) hb

theorem tapPolyAddCommutative (a b : Nat) :
    tapPolyAdd a b = tapPolyAdd b a := by
  exact Nat.xor_comm a b

theorem tapPolyAddAssociative (a b c : Nat) :
    tapPolyAdd (tapPolyAdd a b) c =
      tapPolyAdd a (tapPolyAdd b c) := by
  exact Nat.xor_assoc a b c

theorem tapPolyAddSelf (a : Nat) :
    tapPolyAdd a a = 0 := by
  exact Nat.xor_self a

end L3

namespace L3

set_option autoImplicit false

/-!
The full distributivity of tapPolyRem over Nat.xor for arbitrary
dividends is not claimed. The results below cover already reduced
masks and identify one leading-degree cancellation exactly.
They preserve the prefix without modification.
-/

/-- The XOR of two masks below the same power of two is still
below that power. -/
private theorem tapXorBelowPower (t a c : Nat)
    (ha : a < 2 ^ t) (hc : c < 2 ^ t) :
    a ^^^ c < 2 ^ t := by
  have hadiv : a / 2 ^ t = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr ha)
  have hcdiv : c / 2 ^ t = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr hc)
  have hdiv : (a ^^^ c) / 2 ^ t = 0 := by
    rw [Nat.xor_div_two_pow, hadiv, hcdiv]
    exact Nat.xor_self 0
  rcases Nat.div_eq_zero_iff.mp hdiv with hz | hlt
  · have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  · exact hlt

/-- XOR-linearity of the actual remainder routine when both
dividends are already reduced. This does not extend the proof
to arbitrary dividends. -/
theorem tapPolyRemXorReduced (t b a c : Nat)
    (hb : b < 2 ^ t)
    (ha : a < 2 ^ t) (hc : c < 2 ^ t) :
    tapPolyRem (a ^^^ c) (2 ^ t + b) =
      tapPolyRem a (2 ^ t + b) ^^^
        tapPolyRem c (2 ^ t + b) := by
  calc
    tapPolyRem (a ^^^ c) (2 ^ t + b) =
        a ^^^ c :=
      tapPolyRemSmall t b (a ^^^ c) hb
        (tapXorBelowPower t a c ha hc)
    _ = tapPolyRem a (2 ^ t + b) ^^^
          tapPolyRem c (2 ^ t + b) := by
      rw [tapPolyRemSmall t b a hb ha,
        tapPolyRemSmall t b c hb hc]

/-- Fuel cannot change a mask whose degree is below the modulus. -/
private theorem tapPolyRemFuelBelowPower (t b p fuel : Nat)
    (hb : b < 2 ^ t) (hp : p < 2 ^ t) :
    tapPolyRemFuel (2 ^ t + b) p fuel = p := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have hf : 2 ^ t + b ≠ 0 := by
        have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
        omega
      by_cases hz : p = 0
      · subst p
        simp [tapPolyRemFuel]
      · have hd : Nat.log2 (2 ^ t + b) = t :=
          tapModulusDegree t b hb
        have hlow : Nat.log2 p < t :=
          (Nat.log2_lt hz).2 hp
        simp [tapPolyRemFuel, hf, hz, hd, hlow]

/-- A dividend with exactly one bit above the reduced range
requires exactly one leading-degree cancellation. -/
theorem tapPolyRemSingleTop (t b p : Nat)
    (hb : b < 2 ^ t)
    (hlo : 2 ^ t ≤ p)
    (hhi : p < 2 ^ (t + 1)) :
    tapPolyRem p (2 ^ t + b) =
      p ^^^ (2 ^ t + b) := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  have hp : p ≠ 0 := by
    have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  have hd : Nat.log2 p = t :=
    (Nat.log2_eq_iff hp).2 ⟨hlo, hhi⟩
  have hdeg : Nat.log2 (2 ^ t + b) = t :=
    tapModulusDegree t b hb
  have hlow : ¬ Nat.log2 p < Nat.log2 (2 ^ t + b) := by
    rw [hd, hdeg]
    omega
  have hflo : 2 ^ t ≤ 2 ^ t + b := by omega
  have hfhi : 2 ^ t + b < 2 ^ (t + 1) := by
    rw [tapPowTwoSucc]
    omega
  have hsmall : p ^^^ (2 ^ t + b) < 2 ^ t :=
    tapCancelTop p (2 ^ t + b) t hlo hhi hflo hfhi
  have hstep :
      tapPolyRemFuel (2 ^ t + b) p (t + 1) =
        tapPolyRemFuel (2 ^ t + b)
          (p ^^^ (2 ^ t + b)) t := by
    simp [tapPolyRemFuel, hf, hp, hlow, hd, hdeg, tapPolyAdd]
  unfold tapPolyRem
  rw [if_neg hf, hd, hstep]
  exact tapPolyRemFuelBelowPower t b
    (p ^^^ (2 ^ t + b)) t hb hsmall

/-- Explicit reduced-mask doubling rule: no cancellation below
the top coefficient, one XOR with the modulus at the top. -/
theorem tapPolyRemDoubleReduced (t b a : Nat)
    (hb : b < 2 ^ t) (ha : a < 2 ^ t) :
    tapPolyRem (2 * a) (2 ^ t + b) =
      if 2 * a < 2 ^ t then 2 * a
      else (2 * a) ^^^ (2 ^ t + b) := by
  have hupper : 2 * a < 2 ^ (t + 1) := by
    rw [tapPowTwoSucc]
    omega
  by_cases hsmall : 2 * a < 2 ^ t
  · rw [if_pos hsmall]
    exact tapPolyRemSmall t b (2 * a) hb hsmall
  · rw [if_neg hsmall]
    have hlo : 2 ^ t ≤ 2 * a := by omega
    exact tapPolyRemSingleTop t b (2 * a) hb hlo hupper

/-- The requested shift-comparison identity on already reduced
inputs; the arbitrary-input identity remains open. -/
theorem tapPolyRemShiftReduced (t b a : Nat)
    (hb : b < 2 ^ t) (ha : a < 2 ^ t) :
    tapPolyRem (a <<< 1) (2 ^ t + b) =
      tapPolyRem ((tapPolyRem a (2 ^ t + b)) <<< 1)
        (2 ^ t + b) := by
  rw [tapPolyRemSmall t b a hb ha]

/-- The zero modulus has the stated XOR law independently
of any leading-bit cancellation. -/
theorem tapPolyRemXorZeroModulus (a c : Nat) :
    tapPolyRem (a ^^^ c) 0 =
      tapPolyRem a 0 ^^^ tapPolyRem c 0 := by
  rfl

end L3

namespace L3

set_option autoImplicit false

/-!
Arbitrary shift cancellation
and XOR-linearity of the finite-fuel polynomial remainder.

The calculation uses canonical fuel stability, fixed-degree
elimination, and strong induction on the maximum dividend.
-/

private theorem tapRemFuelZero (f fuel : Nat) :
    tapPolyRemFuel f 0 fuel = 0 := by
  cases fuel <;> simp [tapPolyRemFuel]

/-- Adding one fuel unit after covering the current degree
does not change the answer. -/
private theorem tapRemFuelAdjacent (t b : Nat) (hb : b < 2 ^ t) :
    ∀ fuel p : Nat, (p = 0 ∨ Nat.log2 p < fuel) →
      tapPolyRemFuel (2 ^ t + b) p (fuel + 1) =
        tapPolyRemFuel (2 ^ t + b) p fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro p h
      rcases h with hz | hl
      · subst p
        simp [tapPolyRemFuel]
      · omega
  | succ fuel ih =>
      intro p hbudget
      have hf : 2 ^ t + b ≠ 0 := by
        have hp : 0 < 2 ^ t := Nat.two_pow_pos t
        omega
      have hdeg : Nat.log2 (2 ^ t + b) = t :=
        tapModulusDegree t b hb
      by_cases hz : p = 0
      · subst p
        simp [tapPolyRemFuel]
      · by_cases hlow : Nat.log2 p < t
        · simp [tapPolyRemFuel, hf, hz, hdeg, hlow]
        · have hd : t ≤ Nat.log2 p := by omega
          have hprange :
              2 ^ Nat.log2 p ≤ p ∧
                p < 2 ^ (Nat.log2 p + 1) :=
            (Nat.log2_eq_iff hz).1 rfl
          have hshift := tapShiftTop t b (Nat.log2 p) hb hd
          have hsmall :
              p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)) <
                2 ^ Nat.log2 p :=
            tapCancelTop p
              ((2 ^ t + b) * 2 ^ (Nat.log2 p - t))
              (Nat.log2 p) hprange.1 hprange.2
              hshift.1 hshift.2
          have hnext :
              p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)) = 0 ∨
              Nat.log2 (p ^^^ ((2 ^ t + b) *
                2 ^ (Nat.log2 p - t))) < fuel := by
            by_cases hh :
                p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)) = 0
            · exact Or.inl hh
            · have hdrop :
                  Nat.log2 (p ^^^ ((2 ^ t + b) *
                    2 ^ (Nat.log2 p - t))) < Nat.log2 p :=
                (Nat.log2_lt hh).2 hsmall
              rcases hbudget with hpzero | hlt
              · exact False.elim (hz hpzero)
              · exact Or.inr (by omega)
          have hlong :
              tapPolyRemFuel (2 ^ t + b) p ((fuel + 1) + 1) =
                tapPolyRemFuel (2 ^ t + b)
                  (p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)))
                  (fuel + 1) := by
            simp [tapPolyRemFuel, hf, hz, hdeg, hlow, tapPolyAdd]
          have hshort :
              tapPolyRemFuel (2 ^ t + b) p (fuel + 1) =
                tapPolyRemFuel (2 ^ t + b)
                  (p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)))
                  fuel := by
            simp [tapPolyRemFuel, hf, hz, hdeg, hlow, tapPolyAdd]
          rw [hlong, hshort]
          exact ih _ hnext

private theorem tapRemFuelExtend (t b fuel p extra : Nat)
    (hb : b < 2 ^ t)
    (hbudget : p = 0 ∨ Nat.log2 p < fuel) :
    tapPolyRemFuel (2 ^ t + b) p (fuel + extra) =
      tapPolyRemFuel (2 ^ t + b) p fuel := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      have hnext : p = 0 ∨ Nat.log2 p < fuel + extra := by
        rcases hbudget with hz | hl
        · exact Or.inl hz
        · exact Or.inr (by omega)
      calc
        tapPolyRemFuel (2 ^ t + b) p (fuel + (extra + 1)) =
            tapPolyRemFuel (2 ^ t + b) p ((fuel + extra) + 1) := by
          rw [Nat.add_assoc]
        _ = tapPolyRemFuel (2 ^ t + b) p (fuel + extra) :=
          tapRemFuelAdjacent t b hb (fuel + extra) p hnext
        _ = tapPolyRemFuel (2 ^ t + b) p fuel := ih

private theorem tapRemFuelCanonical (t b fuel p : Nat)
    (hb : b < 2 ^ t)
    (hbudget : p = 0 ∨ Nat.log2 p < fuel) :
    tapPolyRemFuel (2 ^ t + b) p fuel =
      tapPolyRem p (2 ^ t + b) := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hp : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  by_cases hz : p = 0
  · subst p
    rw [tapRemFuelZero]
    simp [tapPolyRem, hf, tapPolyRemFuel]
  · have hle : Nat.log2 p + 1 ≤ fuel := by
      rcases hbudget with hzero | hlt
      · exact False.elim (hz hzero)
      · omega
    have heq : Nat.log2 p + 1 +
        (fuel - (Nat.log2 p + 1)) = fuel := by omega
    calc
      tapPolyRemFuel (2 ^ t + b) p fuel =
          tapPolyRemFuel (2 ^ t + b) p
            ((Nat.log2 p + 1) +
              (fuel - (Nat.log2 p + 1))) := by
          rw [heq]
      _ = tapPolyRemFuel (2 ^ t + b) p
            (Nat.log2 p + 1) :=
          tapRemFuelExtend t b (Nat.log2 p + 1) p
            (fuel - (Nat.log2 p + 1)) hb
            (Or.inr (Nat.lt_succ_self _))
      _ = tapPolyRem p (2 ^ t + b) := by
          simp [tapPolyRem, hf]

/-- Exactly one leading-term cancellation preserves the full
canonical remainder, including its variable fuel budget. -/
private theorem tapRemCancelTop (t b p : Nat)
    (hb : b < 2 ^ t) (hlarge : 2 ^ t ≤ p) :
    tapPolyRem p (2 ^ t + b) =
      tapPolyRem
        (p ^^^ ((2 ^ t + b) *
          2 ^ (Nat.log2 p - t))) (2 ^ t + b) := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hp : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  have hp : p ≠ 0 := by
    have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  have hd : t ≤ Nat.log2 p := by
    by_cases hlow : Nat.log2 p < t
    · have hsmall : p < 2 ^ t := (Nat.log2_lt hp).1 hlow
      omega
    · omega
  have hprange :
      2 ^ Nat.log2 p ≤ p ∧
        p < 2 ^ (Nat.log2 p + 1) :=
    (Nat.log2_eq_iff hp).1 rfl
  have hshift := tapShiftTop t b (Nat.log2 p) hb hd
  have hsmall :
      p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)) <
        2 ^ Nat.log2 p :=
    tapCancelTop p
      ((2 ^ t + b) * 2 ^ (Nat.log2 p - t))
      (Nat.log2 p) hprange.1 hprange.2
      hshift.1 hshift.2
  have hnot : ¬ Nat.log2 p < Nat.log2 (2 ^ t + b) := by
    rw [tapModulusDegree t b hb]
    omega
  have hstep :
      tapPolyRemFuel (2 ^ t + b) p (Nat.log2 p + 1) =
        tapPolyRemFuel (2 ^ t + b)
          (p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)))
          (Nat.log2 p) := by
    simp [tapPolyRemFuel, tapPolyAdd, hp, tapModulusDegree t b hb,
      Nat.not_lt.mpr hd]
  have hbudget :
      p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)) = 0 ∨
      Nat.log2 (p ^^^ ((2 ^ t + b) *
        2 ^ (Nat.log2 p - t))) < Nat.log2 p := by
    by_cases hz :
        p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)) = 0
    · exact Or.inl hz
    · exact Or.inr ((Nat.log2_lt hz).2 hsmall)
  calc
    tapPolyRem p (2 ^ t + b) =
        tapPolyRemFuel (2 ^ t + b) p (Nat.log2 p + 1) := by
      simp [tapPolyRem, hf]
    _ = tapPolyRemFuel (2 ^ t + b)
          (p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)))
          (Nat.log2 p) := hstep
    _ = tapPolyRem
          (p ^^^ ((2 ^ t + b) * 2 ^ (Nat.log2 p - t)))
          (2 ^ t + b) :=
      tapRemFuelCanonical t b (Nat.log2 p) _ hb hbudget

private theorem tapXorOneHigh (d x y : Nat)
    (hx : 2 ^ d ≤ x) (hupper : x < 2 ^ (d + 1))
    (hy : y < 2 ^ d) :
    2 ^ d ≤ x ^^^ y ∧ x ^^^ y < 2 ^ (d + 1) := by
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have hxlo : 1 ≤ x / 2 ^ d :=
    (Nat.one_le_div_iff hpos).2 hx
  have hxhi : x / 2 ^ d ≤ 1 :=
    (Nat.div_le_iff_le_mul_add_pred hpos).2 (by
      rw [tapPowTwoSucc] at hupper
      omega)
  have hxdiv : x / 2 ^ d = 1 := by omega
  have hydiv : y / 2 ^ d = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr hy)
  have hdiv : (x ^^^ y) / 2 ^ d = 1 := by
    rw [Nat.xor_div_two_pow, hxdiv, hydiv]
    rfl
  have hpow : 2 ^ d < 2 ^ (d + 1) := by
    rw [tapPowTwoSucc]
    omega
  constructor
  · exact (Nat.one_le_div_iff hpos).1 (by omega)
  · exact Nat.xor_lt_two_pow hupper (by omega)

private theorem tapXorSwap (a c z : Nat) :
    (a ^^^ c) ^^^ z = (a ^^^ z) ^^^ c := by
  ac_rfl

private theorem tapXorTwice (a c z : Nat) :
    (a ^^^ z) ^^^ (c ^^^ z) = a ^^^ c := by
  calc
    (a ^^^ z) ^^^ (c ^^^ z) =
        a ^^^ (z ^^^ (c ^^^ z)) := Nat.xor_assoc _ _ _
    _ = a ^^^ (z ^^^ (z ^^^ c)) := by
      rw [Nat.xor_comm c z]
    _ = a ^^^ ((z ^^^ z) ^^^ c) := by
      rw [← Nat.xor_assoc z z c]
    _ = a ^^^ c := by
      simp

/-- Cancel the bit at the fixed degree d, if present. -/
private def tapReduceAt (t b d p : Nat) : Nat :=
  if 2 ^ d ≤ p then
    p ^^^ ((2 ^ t + b) * 2 ^ (d - t))
  else p

private theorem tapReduceAtBelow (t b d p : Nat)
    (hb : b < 2 ^ t) (hd : t ≤ d)
    (hp : p < 2 ^ (d + 1)) :
    tapReduceAt t b d p < 2 ^ d := by
  by_cases htop : 2 ^ d ≤ p
  · have hshift := tapShiftTop t b d hb hd
    have hh :
        p ^^^ ((2 ^ t + b) * 2 ^ (d - t)) < 2 ^ d :=
      tapCancelTop p ((2 ^ t + b) * 2 ^ (d - t))
        d htop hp hshift.1 hshift.2
    simpa [tapReduceAt, htop] using hh
  · have hsmall : p < 2 ^ d := by omega
    simpa [tapReduceAt, htop] using hsmall

private theorem tapReduceAtRem (t b d p : Nat)
    (hb : b < 2 ^ t) (hd : t ≤ d)
    (hp : p < 2 ^ (d + 1)) :
    tapPolyRem p (2 ^ t + b) =
      tapPolyRem (tapReduceAt t b d p) (2 ^ t + b) := by
  by_cases htop : 2 ^ d ≤ p
  · have hnz : p ≠ 0 := by
      have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
      omega
    have hlog : Nat.log2 p = d :=
      (Nat.log2_eq_iff hnz).2 ⟨htop, hp⟩
    have hle : 2 ^ t ≤ 2 ^ d :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hd
    have hstep := tapRemCancelTop t b p hb (by omega)
    rw [hlog] at hstep
    simpa [tapReduceAt, htop] using hstep
  · simp [tapReduceAt, htop]

private theorem tapReduceAtXor (t b d a c : Nat)
    (hb : b < 2 ^ t) (hd : t ≤ d)
    (ha : a < 2 ^ (d + 1)) (hc : c < 2 ^ (d + 1)) :
    tapReduceAt t b d (a ^^^ c) =
      tapReduceAt t b d a ^^^ tapReduceAt t b d c := by
  by_cases hta : 2 ^ d ≤ a
  · by_cases htc : 2 ^ d ≤ c
    · have hsum : a ^^^ c < 2 ^ d :=
        tapCancelTop a c d hta ha htc hc
      have hn : ¬ 2 ^ d ≤ a ^^^ c := by omega
      simp only [tapReduceAt, if_neg hn,
        if_pos hta, if_pos htc]
      exact (tapXorTwice a c
        ((2 ^ t + b) * 2 ^ (d - t))).symm
    · have hclow : c < 2 ^ d := by omega
      have hsum : 2 ^ d ≤ a ^^^ c :=
        (tapXorOneHigh d a c hta ha hclow).1
      simp only [tapReduceAt, if_pos hsum,
        if_pos hta, if_neg htc]
      exact tapXorSwap a c ((2 ^ t + b) * 2 ^ (d - t))
  · by_cases htc : 2 ^ d ≤ c
    · have halow : a < 2 ^ d := by omega
      have hsum : 2 ^ d ≤ a ^^^ c := by
        rw [Nat.xor_comm a c]
        exact (tapXorOneHigh d c a htc hc halow).1
      simp only [tapReduceAt, if_pos hsum,
        if_neg hta, if_pos htc]
      exact Nat.xor_assoc a c ((2 ^ t + b) * 2 ^ (d - t))
    · have halow : a < 2 ^ d := by omega
      have hclow : c < 2 ^ d := by omega
      have hsum : a ^^^ c < 2 ^ d :=
        Nat.xor_lt_two_pow halow hclow
      have hn : ¬ 2 ^ d ≤ a ^^^ c := by omega
      simp [tapReduceAt, hn, hta, htc]

/-- All masks: XOR-linearity of the finite-fuel reduction, for
a monic modulus with leading degree t. -/
private theorem tapRemXorMonic (t b : Nat) (hb : b < 2 ^ t) :
    ∀ a c : Nat,
      tapPolyRem (a ^^^ c) (2 ^ t + b) =
        tapPolyRem a (2 ^ t + b) ^^^
          tapPolyRem c (2 ^ t + b) := by
  have main : ∀ m a c : Nat, max a c ≤ m →
      tapPolyRem (a ^^^ c) (2 ^ t + b) =
        tapPolyRem a (2 ^ t + b) ^^^
          tapPolyRem c (2 ^ t + b) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro a c hm
        by_cases hsmall : max a c < 2 ^ t
        · have ha : a < 2 ^ t :=
            Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hsmall
          have hc : c < 2 ^ t :=
            Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hsmall
          exact tapPolyRemXorReduced t b a c hb ha hc
        · have hbig : 2 ^ t ≤ max a c := by omega
          have hnz : max a c ≠ 0 := by
            have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
            omega
          have hrange :
              2 ^ Nat.log2 (max a c) ≤ max a c ∧
                max a c < 2 ^ (Nat.log2 (max a c) + 1) :=
            (Nat.log2_eq_iff hnz).1 rfl
          have hd : t ≤ Nat.log2 (max a c) := by
            by_cases hlt : Nat.log2 (max a c) < t
            · have hbound : max a c < 2 ^ t :=
                (Nat.log2_lt hnz).1 hlt
              omega
            · omega
          have haUpper :
              a < 2 ^ (Nat.log2 (max a c) + 1) :=
            Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hrange.2
          have hcUpper :
              c < 2 ^ (Nat.log2 (max a c) + 1) :=
            Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hrange.2
          have hxorUpper :
              a ^^^ c < 2 ^ (Nat.log2 (max a c) + 1) :=
            Nat.xor_lt_two_pow haUpper hcUpper
          have hra :
              tapReduceAt t b (Nat.log2 (max a c)) a <
                2 ^ Nat.log2 (max a c) :=
            tapReduceAtBelow t b _ a hb hd haUpper
          have hrc :
              tapReduceAt t b (Nat.log2 (max a c)) c <
                2 ^ Nat.log2 (max a c) :=
            tapReduceAtBelow t b _ c hb hd hcUpper
          have hsmaller :
              max (tapReduceAt t b (Nat.log2 (max a c)) a)
                (tapReduceAt t b (Nat.log2 (max a c)) c) < m := by
            have hmax :
                max (tapReduceAt t b (Nat.log2 (max a c)) a)
                  (tapReduceAt t b (Nat.log2 (max a c)) c) <
                    2 ^ Nat.log2 (max a c) := by omega
            omega
          have hrec := ih
            (max (tapReduceAt t b (Nat.log2 (max a c)) a)
              (tapReduceAt t b (Nat.log2 (max a c)) c))
            hsmaller
            (tapReduceAt t b (Nat.log2 (max a c)) a)
            (tapReduceAt t b (Nat.log2 (max a c)) c)
            (Nat.le_refl _)
          calc
            tapPolyRem (a ^^^ c) (2 ^ t + b) =
                tapPolyRem
                  (tapReduceAt t b (Nat.log2 (max a c)) (a ^^^ c))
                  (2 ^ t + b) :=
              tapReduceAtRem t b _ (a ^^^ c) hb hd hxorUpper
            _ = tapPolyRem
                  (tapReduceAt t b (Nat.log2 (max a c)) a ^^^
                    tapReduceAt t b (Nat.log2 (max a c)) c)
                  (2 ^ t + b) := by
              rw [tapReduceAtXor t b _ a c hb hd haUpper hcUpper]
            _ = tapPolyRem
                  (tapReduceAt t b (Nat.log2 (max a c)) a)
                  (2 ^ t + b) ^^^
                tapPolyRem
                  (tapReduceAt t b (Nat.log2 (max a c)) c)
                  (2 ^ t + b) := hrec
            _ = tapPolyRem a (2 ^ t + b) ^^^
                  tapPolyRem c (2 ^ t + b) := by
              rw [← tapReduceAtRem t b _ a hb hd haUpper,
                ← tapReduceAtRem t b _ c hb hd hcUpper]
  intro a c
  exact main (max a c) a c (Nat.le_refl _)

/-- (2): XOR-linearity also holds for modulus zero. -/
theorem tapPolyRemXor (a c f : Nat) :
    tapPolyRem (a ^^^ c) f =
      tapPolyRem a f ^^^ tapPolyRem c f := by
  by_cases hf : f = 0
  · subst f
    exact tapPolyRemXorZeroModulus a c
  · have hrange :
        2 ^ Nat.log2 f ≤ f ∧
          f < 2 ^ (Nat.log2 f + 1) :=
      (Nat.log2_eq_iff hf).1 rfl
    have hupper :
        f < 2 ^ Nat.log2 f + 2 ^ Nat.log2 f := by
      rw [← tapPowTwoSucc]
      exact hrange.2
    have hb :
        f - 2 ^ Nat.log2 f < 2 ^ Nat.log2 f := by omega
    have heq : 2 ^ Nat.log2 f +
        (f - 2 ^ Nat.log2 f) = f := by omega
    simpa only [heq] using
      tapRemXorMonic (Nat.log2 f)
        (f - 2 ^ Nat.log2 f) hb a c

private theorem tapRemShiftMonicZero (t b k : Nat)
    (hb : b < 2 ^ t) :
    tapPolyRem ((2 ^ t + b) <<< k) (2 ^ t + b) = 0 := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hp : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  have hk : t + k - t = k := by omega
  have hshift :
      2 ^ (t + k) ≤ (2 ^ t + b) * 2 ^ k ∧
        (2 ^ t + b) * 2 ^ k < 2 ^ (t + k + 1) := by
    simpa only [hk] using
      tapShiftTop t b (t + k) hb (by omega)
  have hnonzero : (2 ^ t + b) * 2 ^ k ≠ 0 := by
    have hp : 0 < 2 ^ (t + k) := Nat.two_pow_pos _
    omega
  have hlog :
      Nat.log2 ((2 ^ t + b) * 2 ^ k) = t + k :=
    (Nat.log2_eq_iff hnonzero).2 hshift
  have htop := tapRemCancelTop t b
    ((2 ^ t + b) * 2 ^ k) hb
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right t k)) hshift.1)
  rw [hlog, hk, Nat.xor_self] at htop
  have hzero : tapPolyRem 0 (2 ^ t + b) = 0 := by
    simp [tapPolyRem, hf, tapPolyRemFuel]
  rw [Nat.shiftLeft_eq]
  exact htop.trans hzero

private theorem tapRemShiftZero (f k : Nat) (hf : f ≠ 0) :
    tapPolyRem (f <<< k) f = 0 := by
  have hrange :
      2 ^ Nat.log2 f ≤ f ∧
        f < 2 ^ (Nat.log2 f + 1) :=
    (Nat.log2_eq_iff hf).1 rfl
  have hupper :
      f < 2 ^ Nat.log2 f + 2 ^ Nat.log2 f := by
    rw [← tapPowTwoSucc]
    exact hrange.2
  have hb :
      f - 2 ^ Nat.log2 f < 2 ^ Nat.log2 f := by omega
  have heq : 2 ^ Nat.log2 f +
      (f - 2 ^ Nat.log2 f) = f := by omega
  simpa only [heq] using
    tapRemShiftMonicZero (Nat.log2 f)
      (f - 2 ^ Nat.log2 f) k hb

/-- (1): cancellation of any shifted nonzero modulus. -/
theorem tapPolyRemCancelShift (p k f : Nat) :
    tapPolyRem (p ^^^ (f <<< k)) f = tapPolyRem p f := by
  by_cases hf : f = 0
  · subst f
    simp [tapPolyRem]
  · calc
      tapPolyRem (p ^^^ (f <<< k)) f =
          tapPolyRem p f ^^^ tapPolyRem (f <<< k) f :=
        tapPolyRemXor p (f <<< k) f
      _ = tapPolyRem p f := by
        rw [tapRemShiftZero f k hf, Nat.xor_zero]

end L3


namespace L3

set_option autoImplicit false

/-!
(b2):
All arguments concern the literal fuel-bounded carry-less product.
No field or quotient-ring law is assumed.
-/

/-- Left shifting by one bit respects polynomial XOR. -/
private theorem tapMulXorDouble (a b : Nat) :
    2 * (a ^^^ b) = (2 * a) ^^^ (2 * b) := by
  calc
    2 * (a ^^^ b) = (a ^^^ b) * 2 := Nat.mul_comm _ _
    _ = (a * 2) ^^^ (b * 2) := by
      simpa only [Nat.shiftLeft_eq, Nat.pow_one] using
        (Nat.shiftLeft_xor_distrib (i := 1) (a := a) (b := b))
    _ = (2 * a) ^^^ (2 * b) := by
      rw [Nat.mul_comm a 2, Nat.mul_comm b 2]

/-- The scanner is equivariant under XOR in its accumulator. -/
private theorem tapMulFuelAccXor :
    ∀ fuel a b acc d : Nat,
      tapPolyMulFuel a b (acc ^^^ d) fuel =
        tapPolyMulFuel a b acc fuel ^^^ d := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b acc d
      rfl
  | succ fuel ih =>
      intro a b acc d
      by_cases hzero : b = 0
      · simp [tapPolyMulFuel, hzero]
      · by_cases hbit : b % 2 = 1
        · have hswap :
              Nat.xor (acc ^^^ d) a = (acc ^^^ a) ^^^ d := by
            change (acc ^^^ d) ^^^ a = (acc ^^^ a) ^^^ d
            ac_rfl
          simp only [tapPolyMulFuel, if_neg hzero, if_pos hbit,
            tapPolyAdd]
          rw [hswap]
          exact ih (2 * a) (b / 2) (acc ^^^ a) d
        · simp only [tapPolyMulFuel, if_neg hzero, if_neg hbit]
          exact ih (2 * a) (b / 2) acc d

/-- The finite scanner is XOR-linear in its first argument, for
every fuel, including insufficient fuel. -/
private theorem tapMulFuelLinear :
    ∀ fuel a c b acc d : Nat,
      tapPolyMulFuel (a ^^^ c) b (acc ^^^ d) fuel =
        tapPolyMulFuel a b acc fuel ^^^
          tapPolyMulFuel c b d fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro a c b acc d
      rfl
  | succ fuel ih =>
      intro a c b acc d
      by_cases hzero : b = 0
      · simp [tapPolyMulFuel, hzero]
      · by_cases hbit : b % 2 = 1
        · have hacc :
              Nat.xor (acc ^^^ d) (a ^^^ c) =
                (acc ^^^ a) ^^^ (d ^^^ c) := by
            change (acc ^^^ d) ^^^ (a ^^^ c) =
              (acc ^^^ a) ^^^ (d ^^^ c)
            ac_rfl
          simp only [tapPolyMulFuel, if_neg hzero, if_pos hbit,
            tapPolyAdd]
          rw [tapMulXorDouble a c, hacc]
          exact ih (2 * a) (2 * c) (b / 2) (acc ^^^ a) (d ^^^ c)
        · simp only [tapPolyMulFuel, if_neg hzero, if_neg hbit]
          rw [tapMulXorDouble a c]
          exact ih (2 * a) (2 * c) (b / 2) acc d

/-- The finite scanner commutes with doubling its first input
and accumulator. -/
private theorem tapMulFuelDouble :
    ∀ fuel a b acc : Nat,
      tapPolyMulFuel (2 * a) b (2 * acc) fuel =
        2 * tapPolyMulFuel a b acc fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b acc
      rfl
  | succ fuel ih =>
      intro a b acc
      by_cases hzero : b = 0
      · simp [tapPolyMulFuel, hzero]
      · by_cases hbit : b % 2 = 1
        · simp only [tapPolyMulFuel, if_neg hzero, if_pos hbit,
            tapPolyAdd]
          have hdouble :
              Nat.xor (2 * acc) (2 * a) = 2 * (acc ^^^ a) := by
            change (2 * acc) ^^^ (2 * a) = 2 * (acc ^^^ a)
            exact (tapMulXorDouble acc a).symm
          rw [hdouble]
          exact ih (2 * a) (b / 2) (acc ^^^ a)
        · simp only [tapPolyMulFuel, if_neg hzero, if_neg hbit]
          exact ih (2 * a) (b / 2) acc

/-- The complete product is XOR-linear in the first argument. -/
theorem tapPolyMulXorLeft (a c b : Nat) :
    tapPolyMul (a ^^^ c) b =
      tapPolyMul a b ^^^ tapPolyMul c b := by
  unfold tapPolyMul
  simpa only [Nat.xor_zero] using
    (tapMulFuelLinear (Nat.log2 b + 1) a c b 0 0)

/-- Doubling a factor shifts the carry-less product one bit. -/
theorem tapPolyMulDoubleLeft (a b : Nat) :
    tapPolyMul (2 * a) b = 2 * tapPolyMul a b := by
  unfold tapPolyMul
  simpa only [Nat.mul_zero] using
    (tapMulFuelDouble (Nat.log2 b + 1) a b 0)

/-- An all-zero first operand never contributes an XOR summand. -/
private theorem tapMulFuelZeroLeft :
    ∀ fuel b acc : Nat, tapPolyMulFuel 0 b acc fuel = acc := by
  intro fuel
  induction fuel with
  | zero =>
      intro b acc
      rfl
  | succ fuel ih =>
      intro b acc
      by_cases hzero : b = 0
      · simp [tapPolyMulFuel, hzero]
      · by_cases hbit : b % 2 = 1
        · simp [tapPolyMulFuel, hzero, hbit, tapPolyAdd, ih]
        · simp [tapPolyMulFuel, hzero, hbit, ih]

theorem tapPolyMulZeroLeft (b : Nat) : tapPolyMul 0 b = 0 := by
  unfold tapPolyMul
  exact tapMulFuelZeroLeft (Nat.log2 b + 1) b 0

theorem tapPolyMulZeroRight (a : Nat) : tapPolyMul a 0 = 0 := by
  rfl

/-- Once fuel covers all input bits, adding one unit is inert. -/
private theorem tapMulFuelStable :
    ∀ fuel a b acc : Nat,
      (b = 0 ∨ Nat.log2 b < fuel) →
      tapPolyMulFuel a b acc (fuel + 1) =
        tapPolyMulFuel a b acc fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b acc hbudget
      rcases hbudget with hzero | hlt
      · subst b
        simp [tapPolyMulFuel]
      · omega
  | succ fuel ih =>
      intro a b acc hbudget
      by_cases hzero : b = 0
      · simp [tapPolyMulFuel, hzero]
      · have hnext :
            b / 2 = 0 ∨ Nat.log2 (b / 2) < fuel := by
          by_cases hsmall : b < 2
          · exact Or.inl (by omega)
          · have hlarge : 2 ≤ b := by omega
            have hlog := Nat.log2_def b
            rw [if_pos hlarge] at hlog
            rcases hbudget with hz | hl
            · exact False.elim (hzero hz)
            · exact Or.inr (by omega)
        by_cases hbit : b % 2 = 1
        · simp only [tapPolyMulFuel, if_neg hzero, if_pos hbit]
          exact ih (2 * a) (b / 2) (tapPolyAdd acc a) hnext
        · simp only [tapPolyMulFuel, if_neg hzero, if_neg hbit]
          exact ih (2 * a) (b / 2) acc hnext

private theorem tapMulFuelExtend (a b acc fuel extra : Nat)
    (hbudget : b = 0 ∨ Nat.log2 b < fuel) :
    tapPolyMulFuel a b acc (fuel + extra) =
      tapPolyMulFuel a b acc fuel := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      have hnext : b = 0 ∨ Nat.log2 b < fuel + extra := by
        rcases hbudget with hzero | hlt
        · exact Or.inl hzero
        · exact Or.inr (by omega)
      calc
        tapPolyMulFuel a b acc (fuel + (extra + 1)) =
            tapPolyMulFuel a b acc ((fuel + extra) + 1) := by
          rw [Nat.add_assoc]
        _ = tapPolyMulFuel a b acc (fuel + extra) :=
          tapMulFuelStable (fuel + extra) a b acc hnext
        _ = tapPolyMulFuel a b acc fuel := ih

/-- The public log2 fuel is a canonical representative of every
sufficient scanning budget. -/
private theorem tapMulFuelCanonical (a b acc fuel : Nat)
    (hbudget : b = 0 ∨ Nat.log2 b < fuel) :
    tapPolyMulFuel a b acc fuel =
      tapPolyMulFuel a b acc (Nat.log2 b + 1) := by
  by_cases hzero : b = 0
  · subst b
    cases fuel <;> simp [tapPolyMulFuel]
  · have hle : Nat.log2 b + 1 ≤ fuel := by
      rcases hbudget with hz | hlt
      · exact False.elim (hzero hz)
      · omega
    have hsum :
        Nat.log2 b + 1 + (fuel - (Nat.log2 b + 1)) = fuel := by
      omega
    calc
      tapPolyMulFuel a b acc fuel =
          tapPolyMulFuel a b acc
            ((Nat.log2 b + 1) + (fuel - (Nat.log2 b + 1))) := by
        rw [hsum]
      _ = tapPolyMulFuel a b acc (Nat.log2 b + 1) :=
        tapMulFuelExtend a b acc (Nat.log2 b + 1)
          (fuel - (Nat.log2 b + 1))
          (Or.inr (Nat.lt_succ_self _))

/-- Interpret a sufficient scanner budget using the public product. -/
private theorem tapMulFuelEvaluated (a b acc fuel : Nat)
    (hbudget : b = 0 ∨ Nat.log2 b < fuel) :
    tapPolyMulFuel a b acc fuel = acc ^^^ tapPolyMul a b := by
  calc
    tapPolyMulFuel a b acc fuel =
        tapPolyMulFuel a b acc (Nat.log2 b + 1) :=
      tapMulFuelCanonical a b acc fuel hbudget
    _ = tapPolyMulFuel a b 0 (Nat.log2 b + 1) ^^^ acc := by
      simpa only [Nat.zero_xor] using
        (tapMulFuelAccXor (Nat.log2 b + 1) a b 0 acc)
    _ = acc ^^^ tapPolyMul a b :=
      Nat.xor_comm _ _

/-- Literal least-significant-bit recurrence for the public product. -/
theorem tapPolyMulStep (a b : Nat) :
    tapPolyMul a b =
      (if b % 2 = 1 then a else 0) ^^^
        tapPolyMul (2 * a) (b / 2) := by
  by_cases hzero : b = 0
  · subst b
    simp [tapPolyMul, tapPolyMulFuel]
  · have hbudget :
        b / 2 = 0 ∨ Nat.log2 (b / 2) < Nat.log2 b := by
      by_cases hsmall : b < 2
      · exact Or.inl (by omega)
      · have hlarge : 2 ≤ b := by omega
        have hlog := Nat.log2_def b
        rw [if_pos hlarge] at hlog
        exact Or.inr (by omega)
    calc
      tapPolyMul a b =
          tapPolyMulFuel (2 * a) (b / 2)
            (if b % 2 = 1 then a else 0) (Nat.log2 b) := by
        have hzeroXor : Nat.xor 0 a = a := by
          change (0 ^^^ a) = a
          exact Nat.zero_xor a
        unfold tapPolyMul
        simp only [tapPolyMulFuel, if_neg hzero,
          tapPolyAdd, hzeroXor]
      _ = (if b % 2 = 1 then a else 0) ^^^
            tapPolyMul (2 * a) (b / 2) :=
        tapMulFuelEvaluated (2 * a) (b / 2)
          (if b % 2 = 1 then a else 0) (Nat.log2 b) hbudget

/-- For the low bit, XOR against a doubled word is ordinary addition. -/
private theorem tapMulEvenXorLow (b r : Nat) (hr : r < 2) :
    (2 * b) ^^^ r = 2 * b + r := by
  have hquot : ((2 * b) ^^^ r) / 2 = b := by
    rw [Nat.xor_div_two]
    have hleft : (2 * b) / 2 = b := by omega
    have hright : r / 2 = 0 := by omega
    rw [hleft, hright, Nat.xor_zero]
  have hmodRaw :
      ((2 * b) ^^^ r) % 2 = (2 * b) % 2 ^^^ r % 2 := by
    simpa only [Nat.pow_one] using
      (Nat.xor_mod_two_pow (a := 2 * b) (b := r) (n := 1))
  have hleft : (2 * b) % 2 = 0 := by omega
  have hright : r % 2 = r := by omega
  rw [hleft, hright, Nat.zero_xor] at hmodRaw
  omega

private theorem tapMulBinaryXor (a : Nat) :
    (2 * (a / 2)) ^^^ (a % 2) = a := by
  rw [tapMulEvenXorLow (a / 2) (a % 2) (by omega)]
  omega

/-- The multiplicative unit on the left is the bit string itself. -/
theorem tapPolyMulOneLeft (b : Nat) : tapPolyMul 1 b = b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      by_cases hzero : b = 0
      · subst b
        rfl
      · have hsmaller : b / 2 < b := by omega
        have hlow : b % 2 < 2 := by omega
        have hbit :
            (if b % 2 = 1 then (1 : Nat) else 0) = b % 2 := by
          by_cases hone : b % 2 = 1
          · simp [hone]
          · have hz : b % 2 = 0 := by omega
            simp [hz]
        calc
          tapPolyMul 1 b =
              (if b % 2 = 1 then 1 else 0) ^^^
                tapPolyMul (2 * 1) (b / 2) :=
            tapPolyMulStep 1 b
          _ = (b % 2) ^^^ (2 * tapPolyMul 1 (b / 2)) := by
            rw [tapPolyMulDoubleLeft 1 (b / 2), hbit]
          _ = b := by
            rw [ih (b / 2) hsmaller, Nat.xor_comm]
            rw [tapMulEvenXorLow (b / 2) (b % 2) hlow]
            omega

/-- Commutativity is induced by the left XOR law and the right-bit
recurrence; its induction measure is the first operand. -/
theorem tapPolyMulCommutative (a b : Nat) :
    tapPolyMul a b = tapPolyMul b a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
      by_cases hzero : a = 0
      · subst a
        rw [tapPolyMulZeroLeft, tapPolyMulZeroRight]
      · have hsmaller : a / 2 < a := by omega
        have hlow :
            tapPolyMul (a % 2) b =
              if a % 2 = 1 then b else 0 := by
          by_cases hone : a % 2 = 1
          · rw [hone, tapPolyMulOneLeft]
            rfl
          · have hz : a % 2 = 0 := by omega
            rw [hz, tapPolyMulZeroLeft]
            rfl
        have hleft :
            tapPolyMul a b =
              (if a % 2 = 1 then b else 0) ^^^
                (2 * tapPolyMul (a / 2) b) := by
          calc
            tapPolyMul a b =
                tapPolyMul ((2 * (a / 2)) ^^^ (a % 2)) b := by
              rw [tapMulBinaryXor a]
            _ = tapPolyMul (2 * (a / 2)) b ^^^
                  tapPolyMul (a % 2) b :=
              tapPolyMulXorLeft (2 * (a / 2)) (a % 2) b
            _ = (if a % 2 = 1 then b else 0) ^^^
                  (2 * tapPolyMul (a / 2) b) := by
              rw [tapPolyMulDoubleLeft (a / 2) b, hlow]
              exact Nat.xor_comm _ _
        calc
          tapPolyMul a b =
              (if a % 2 = 1 then b else 0) ^^^
                (2 * tapPolyMul (a / 2) b) := hleft
          _ = (if a % 2 = 1 then b else 0) ^^^
                (2 * tapPolyMul b (a / 2)) := by
              rw [ih (a / 2) hsmaller]
          _ = tapPolyMul b a := by
              rw [tapPolyMulStep b a, tapPolyMulDoubleLeft b (a / 2)]

/-- Commutativity transfers left XOR distributivity to the right. -/
theorem tapPolyMulXorRight (a b c : Nat) :
    tapPolyMul a (b ^^^ c) =
      tapPolyMul a b ^^^ tapPolyMul a c := by
  calc
    tapPolyMul a (b ^^^ c) = tapPolyMul (b ^^^ c) a :=
      tapPolyMulCommutative a (b ^^^ c)
    _ = tapPolyMul b a ^^^ tapPolyMul c a :=
      tapPolyMulXorLeft b c a
    _ = tapPolyMul a b ^^^ tapPolyMul a c := by
      rw [tapPolyMulCommutative b a, tapPolyMulCommutative c a]

/-- Multiplying by a monomial in the first input shifts the other. -/
private theorem tapPolyMulPowerTwoLeft (a k : Nat) :
    tapPolyMul (2 ^ k) a = a <<< k := by
  induction k with
  | zero =>
      simpa [Nat.shiftLeft_eq] using (tapPolyMulOneLeft a)
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 * (2 ^ k) := by
        rw [Nat.pow_succ]
        exact Nat.mul_comm _ _
      calc
        tapPolyMul (2 ^ (k + 1)) a =
            tapPolyMul (2 * (2 ^ k)) a := by
          rw [hpow]
        _ = 2 * tapPolyMul (2 ^ k) a :=
          tapPolyMulDoubleLeft (2 ^ k) a
        _ = 2 * (a <<< k) := by rw [ih]
        _ = a <<< (k + 1) := by
          simp only [Nat.shiftLeft_eq, Nat.pow_succ]
          ac_rfl

/-- The requested monomial law, on the literal bit-mask encoding. -/
theorem tapPolyMulPowerTwo (a k : Nat) :
    tapPolyMul a (2 ^ k) = a <<< k := by
  calc
    tapPolyMul a (2 ^ k) = tapPolyMul (2 ^ k) a :=
      tapPolyMulCommutative a (2 ^ k)
    _ = a <<< k := tapPolyMulPowerTwoLeft a k

end L3


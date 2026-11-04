import Leader.L3.Primitive.TapPoly

/-!
Binary polynomial masks: associativity, leading-bit degree bounds,
XOR cancellation, squares and monomials.

Consumer: PrimitiveMaskDivision, PrimitiveMaskFactors and
PrimitiveMaskQuotient.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The product respects doubling in its second input.
Consumer: tapPolyMulAssociative and PrimitiveMaskDivision. -/
private theorem tapPolyMulDoubleRight (a b : Nat) :
    tapPolyMul a (2 * b) = 2 * tapPolyMul a b := by
  calc
    tapPolyMul a (2 * b) =
        tapPolyMul (2 * b) a :=
      tapPolyMulCommutative a (2 * b)
    _ = 2 * tapPolyMul b a :=
      tapPolyMulDoubleLeft b a
    _ = 2 * tapPolyMul a b := by
      rw [tapPolyMulCommutative b a]

/-- Carryless multiplication is associative, by the literal
low-bit recurrence and the two distributive laws.
Consumer: PrimitiveMaskDivision and PrimitiveMaskQuotient. -/
theorem tapPolyMulAssociative (a b c : Nat) :
    tapPolyMul (tapPolyMul a b) c =
      tapPolyMul a (tapPolyMul b c) := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      by_cases hz : c = 0
      · subst c
        simp only [tapPolyMulZeroRight]
      · have hsmall : c / 2 < c := by omega
        have hbit :
            tapPolyMul a (if c % 2 = 1 then b else 0) =
              (if c % 2 = 1 then tapPolyMul a b else 0) := by
          by_cases hone : c % 2 = 1
          · simp only [if_pos hone]
          · simp only [if_neg hone]
            exact tapPolyMulZeroRight a
        calc
          tapPolyMul (tapPolyMul a b) c =
              (if c % 2 = 1 then tapPolyMul a b else 0) ^^^
                tapPolyMul (2 * tapPolyMul a b) (c / 2) :=
            tapPolyMulStep (tapPolyMul a b) c
          _ = (if c % 2 = 1 then tapPolyMul a b else 0) ^^^
                (2 * tapPolyMul (tapPolyMul a b) (c / 2)) := by
            rw [tapPolyMulDoubleLeft]
          _ = (if c % 2 = 1 then tapPolyMul a b else 0) ^^^
                (2 * tapPolyMul a (tapPolyMul b (c / 2))) := by
            rw [ih (c / 2) hsmall]
          _ = tapPolyMul a (if c % 2 = 1 then b else 0) ^^^
                tapPolyMul a (tapPolyMul (2 * b) (c / 2)) := by
            rw [hbit, tapPolyMulDoubleLeft b (c / 2),
              tapPolyMulDoubleRight a (tapPolyMul b (c / 2))]
          _ = tapPolyMul a
                ((if c % 2 = 1 then b else 0) ^^^
                  tapPolyMul (2 * b) (c / 2)) :=
            (tapPolyMulXorRight a _ _).symm
          _ = tapPolyMul a (tapPolyMul b c) := by
            rw [tapPolyMulStep b c]

/-- The right unit follows from the existing left unit.
Consumer: PrimitiveMaskDivision and PrimitiveMaskQuotient. -/
theorem tapPolyMulOneRight (a : Nat) :
    tapPolyMul a 1 = a := by
  rw [tapPolyMulCommutative a 1]
  exact tapPolyMulOneLeft a

/-- A nonzero mask's highest coefficient index.
Consumer: PrimitiveMaskDivision and PrimitiveMaskFactors. -/
abbrev tapPolyDegree (p : Nat) : Nat := Nat.log2 p

/-- The highest bit of a nonzero mask gives its exact bounds.
Consumer: tapPolyMulLog and PrimitiveMaskDivision. -/
theorem tapMaskLog (p : Nat) (hp : p ≠ 0) :
    2 ^ Nat.log2 p ≤ p ∧
      p < 2 ^ (Nat.log2 p + 1) := by
  exact (Nat.log2_eq_iff hp).1 rfl

/-- The converse characterization of the highest bit.
Consumer: PrimitiveMaskFactors and PrimitiveMaskDivision. -/
theorem tapMaskLogOfBounds (p d : Nat)
    (hlo : 2 ^ d ≤ p) (hhi : p < 2 ^ (d + 1)) :
    Nat.log2 p = d := by
  have hp : p ≠ 0 := by
    have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
    omega
  exact (Nat.log2_eq_iff hp).2 ⟨hlo, hhi⟩

/-- The quotient by a power of two detects a unique top bit.
Consumer: tapMaskXorPreservesTop and tapMaskXorCancelTop. -/
private theorem tapMaskDivTop (p d : Nat)
    (hlo : 2 ^ d ≤ p) (hhi : p < 2 ^ (d + 1)) :
    p / 2 ^ d = 1 := by
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have hlow : 1 ≤ p / 2 ^ d :=
    (Nat.one_le_div_iff hpos).2 hlo
  have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
    rw [Nat.pow_succ]
    omega
  have hhigh : p / 2 ^ d ≤ 1 :=
    (Nat.div_le_iff_le_mul_add_pred hpos).2 (by
      rw [hpow] at hhi
      omega)
  omega

/-- XOR with a strictly lower-degree mask preserves the leading
bit and leaves all higher bits zero.
Consumer: tapPolyMulBounds and PrimitiveMaskFactors. -/
private theorem tapMaskXorPreservesTop (d low high : Nat)
    (hlow : low < 2 ^ d)
    (hhighLo : 2 ^ d ≤ high)
    (hhighHi : high < 2 ^ (d + 1)) :
    2 ^ d ≤ low ^^^ high ∧
      low ^^^ high < 2 ^ (d + 1) := by
  have hlowDiv : low / 2 ^ d = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr hlow)
  have hhighDiv : high / 2 ^ d = 1 :=
    tapMaskDivTop high d hhighLo hhighHi
  have hxorDiv : (low ^^^ high) / 2 ^ d = 1 := by
    rw [Nat.xor_div_two_pow, hlowDiv, hhighDiv]
    rfl
  have hresultLo : 2 ^ d ≤ low ^^^ high :=
    (Nat.one_le_div_iff (Nat.two_pow_pos d)).1 (by
      rw [hxorDiv]; exact Nat.le_refl 1)
  have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
    rw [Nat.pow_succ]
    omega
  have hlowHigh : low < 2 ^ (d + 1) := by
    rw [hpow]
    omega
  have hlowDivHigh : low / 2 ^ (d + 1) = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr hlowHigh)
  have hhighDivHigh : high / 2 ^ (d + 1) = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr hhighHi)
  have hxorDivHigh :
      (low ^^^ high) / 2 ^ (d + 1) = 0 := by
    rw [Nat.xor_div_two_pow, hlowDivHigh, hhighDivHigh]
    rfl
  have hresultHi : low ^^^ high < 2 ^ (d + 1) := by
    rcases Nat.div_eq_zero_iff.mp hxorDivHigh with hz | hlt
    · have hpos : 0 < 2 ^ (d + 1) :=
        Nat.two_pow_pos (d + 1)
      omega
    · exact hlt
  exact ⟨hresultLo, hresultHi⟩

/-- A power of two cannot decrease when its exponent is extended.
Consumer: tapPolyMulBounds. -/
private theorem tapMaskPowExtend (d k : Nat) :
    2 ^ d ≤ 2 ^ (d + k) := by
  have hpos : 1 ≤ 2 ^ k := by
    have h := Nat.two_pow_pos k
    omega
  calc
    2 ^ d = (2 ^ d) * 1 := by
      rw [Nat.mul_one]
    _ ≤ (2 ^ d) * (2 ^ k) :=
      Nat.mul_le_mul_left _ hpos
    _ = 2 ^ (d + k) := (Nat.pow_add 2 d k).symm

/-- Multiplication of two nonzero mask-degree intervals adds their
top indices: the shifted product has a strictly higher leading bit
than the optional low-term XOR contribution.
Consumer: PrimitiveMaskDivision and PrimitiveMaskFactors. -/
theorem tapPolyMulBounds (a c d e : Nat)
    (haLo : 2 ^ d ≤ a) (haHi : a < 2 ^ (d + 1))
    (hcLo : 2 ^ e ≤ c) (hcHi : c < 2 ^ (e + 1)) :
    2 ^ (d + e) ≤ tapPolyMul a c ∧
      tapPolyMul a c < 2 ^ (d + e + 1) := by
  have hbounds : ∀ e c : Nat,
      2 ^ e ≤ c → c < 2 ^ (e + 1) →
      2 ^ (d + e) ≤ tapPolyMul a c ∧
        tapPolyMul a c < 2 ^ (d + e + 1) := by
    intro e
    induction e with
    | zero =>
        intro c hlo hhi
        have hone : c = 1 := by
          change 1 ≤ c at hlo
          change c < 2 at hhi
          omega
        subst c
        rw [tapPolyMulOneRight]
        simpa only [Nat.add_zero] using
          (show 2 ^ d ≤ a ∧ a < 2 ^ (d + 1) from
            ⟨haLo, haHi⟩)
    | succ e ih =>
        intro c hlo hhi
        have hpowLo : 2 ^ (e + 1) = 2 * 2 ^ e := by
          rw [Nat.pow_succ]
          omega
        have hpowHi :
            2 ^ ((e + 1) + 1) = 2 * 2 ^ (e + 1) := by
          rw [Nat.pow_succ]
          omega
        have hhalfLo : 2 ^ e ≤ c / 2 := by
          rw [hpowLo] at hlo
          omega
        have hhalfHi : c / 2 < 2 ^ (e + 1) := by
          rw [hpowHi] at hhi
          omega
        have hrec := ih (c / 2) hhalfLo hhalfHi
        have hpowProductLo :
            2 ^ (d + (e + 1)) = 2 * 2 ^ (d + e) := by
          have hindex : d + (e + 1) = (d + e) + 1 := by omega
          rw [hindex, Nat.pow_succ]
          omega
        have hpowProductHi :
            2 ^ (d + (e + 1) + 1) =
              2 * 2 ^ (d + e + 1) := by
          have hindex :
              d + (e + 1) + 1 = (d + e + 1) + 1 := by omega
          rw [hindex, Nat.pow_succ]
          omega
        have hdoubleLo :
            2 ^ (d + (e + 1)) ≤
              2 * tapPolyMul a (c / 2) := by
          rw [hpowProductLo]
          exact Nat.mul_le_mul_left 2 hrec.1
        have hdoubleHi :
            2 * tapPolyMul a (c / 2) <
              2 ^ (d + (e + 1) + 1) := by
          rw [hpowProductHi]
          omega
        have haSmall : a < 2 ^ (d + (e + 1)) := by
          have hindex :
              d + (e + 1) = (d + 1) + e := by omega
          rw [hindex]
          exact Nat.lt_of_lt_of_le haHi
            (tapMaskPowExtend (d + 1) e)
        have hsmall :
            (if c % 2 = 1 then a else 0) <
              2 ^ (d + (e + 1)) := by
          split
          · exact haSmall
          · exact Nat.two_pow_pos _
        have htop := tapMaskXorPreservesTop
          (d + (e + 1))
          (if c % 2 = 1 then a else 0)
          (2 * tapPolyMul a (c / 2))
          hsmall hdoubleLo hdoubleHi
        have hformula :
            tapPolyMul a c =
              (if c % 2 = 1 then a else 0) ^^^
                (2 * tapPolyMul a (c / 2)) := by
          rw [tapPolyMulStep a c,
            tapPolyMulDoubleLeft a (c / 2)]
        rw [hformula]
        exact htop
  exact hbounds e c hcLo hcHi

/-- A nonzero mask product has the sum of the two highest-bit
indices. Consumer: PrimitiveMaskDivision and PrimitiveMaskFactors. -/
theorem tapPolyMulLog (a c : Nat)
    (ha : a ≠ 0) (hc : c ≠ 0) :
    Nat.log2 (tapPolyMul a c) =
      Nat.log2 a + Nat.log2 c := by
  have hb := tapPolyMulBounds a c
    (Nat.log2 a) (Nat.log2 c)
    (tapMaskLog a ha).1 (tapMaskLog a ha).2
    (tapMaskLog c hc).1 (tapMaskLog c hc).2
  have hnonzero : tapPolyMul a c ≠ 0 := by
    intro hz
    rw [hz] at hb
    have hpos : 0 < 2 ^ (Nat.log2 a + Nat.log2 c) :=
      Nat.two_pow_pos _
    omega
  exact (Nat.log2_eq_iff hnonzero).2 hb

/-- The top-bit bound excludes zero divisors for nonzero masks.
Consumer: PrimitiveMaskDivision and PrimitiveMaskQuotient. -/
theorem tapPolyMulNeZero (a c : Nat)
    (ha : a ≠ 0) (hc : c ≠ 0) :
    tapPolyMul a c ≠ 0 := by
  have hb := tapPolyMulBounds a c
    (Nat.log2 a) (Nat.log2 c)
    (tapMaskLog a ha).1 (tapMaskLog a ha).2
    (tapMaskLog c hc).1 (tapMaskLog c hc).2
  intro hz
  rw [hz] at hb
  have hpos : 0 < 2 ^ (Nat.log2 a + Nat.log2 c) :=
    Nat.two_pow_pos _
  omega

/-- XOR is zero exactly when the two polynomial masks coincide.
Consumer: PrimitiveMaskDivision and PrimitiveMaskFactors. -/
theorem tapPolyAddEqZeroIff (a c : Nat) :
    tapPolyAdd a c = 0 ↔ a = c := by
  constructor
  · intro h
    change a ^^^ c = 0 at h
    have hh := congrArg (fun v : Nat => a ^^^ v) h
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor,
      Nat.xor_zero] at hh
    exact hh.symm
  · intro h
    rw [h]
    exact tapPolyAddSelf c

/-- XOR does not introduce a set bit beyond either input's
degree limit. Consumer: PrimitiveMaskDivision. -/
theorem tapPolyAddBelow (a c d : Nat)
    (ha : a < 2 ^ d) (hc : c < 2 ^ d) :
    tapPolyAdd a c < 2 ^ d := by
  have hadiv : a / 2 ^ d = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr ha)
  have hcdiv : c / 2 ^ d = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr hc)
  have hdiv : (a ^^^ c) / 2 ^ d = 0 := by
    rw [Nat.xor_div_two_pow, hadiv, hcdiv]
    exact Nat.xor_self 0
  change a ^^^ c < 2 ^ d
  rcases Nat.div_eq_zero_iff.mp hdiv with hz | hlt
  · have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
    omega
  · exact hlt

/-- Two masks with the same highest bit cancel that bit under XOR.
Consumer: tapPolyAddLogLt and PrimitiveMaskDivision. -/
private theorem tapMaskXorCancelTop (d a c : Nat)
    (haLo : 2 ^ d ≤ a) (haHi : a < 2 ^ (d + 1))
    (hcLo : 2 ^ d ≤ c) (hcHi : c < 2 ^ (d + 1)) :
    tapPolyAdd a c < 2 ^ d := by
  have haDiv : a / 2 ^ d = 1 :=
    tapMaskDivTop a d haLo haHi
  have hcDiv : c / 2 ^ d = 1 :=
    tapMaskDivTop c d hcLo hcHi
  have hxorDiv : (a ^^^ c) / 2 ^ d = 0 := by
    rw [Nat.xor_div_two_pow, haDiv, hcDiv]
    exact Nat.xor_self 1
  change a ^^^ c < 2 ^ d
  rcases Nat.div_eq_zero_iff.mp hxorDiv with hz | hlt
  · have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
    omega
  · exact hlt

/-- Equal-degree unequal nonzero masks have a nonzero XOR of
strictly smaller degree. Consumer: PrimitiveMaskDivision. -/
theorem tapPolyAddLogLt (a c : Nat)
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hne : a ≠ c) (hlog : Nat.log2 a = Nat.log2 c) :
    tapPolyAdd a c ≠ 0 ∧
      Nat.log2 (tapPolyAdd a c) < Nat.log2 a := by
  have hnonzero : tapPolyAdd a c ≠ 0 := by
    intro hz
    exact hne ((tapPolyAddEqZeroIff a c).1 hz)
  have hboundsA := tapMaskLog a ha
  have hboundsC := tapMaskLog c hc
  have hcLo : 2 ^ Nat.log2 a ≤ c := by
    rw [hlog]
    exact hboundsC.1
  have hcHi : c < 2 ^ (Nat.log2 a + 1) := by
    rw [hlog]
    exact hboundsC.2
  have hbelow := tapMaskXorCancelTop (Nat.log2 a)
    a c hboundsA.1 hboundsA.2 hcLo hcHi
  have hdegree :
      Nat.log2 (tapPolyAdd a c) < Nat.log2 a :=
    (Nat.log2_lt hnonzero).2 hbelow
  exact ⟨hnonzero, hdegree⟩

/-- In characteristic two, the cross terms in a square cancel.
Consumer: PrimitiveMaskFactors and PrimitiveMaskQuotient. -/
theorem tapPolySquare (a c : Nat) :
    tapPolyMul (tapPolyAdd a c) (tapPolyAdd a c) =
      tapPolyAdd (tapPolyMul a a) (tapPolyMul c c) := by
  calc
    tapPolyMul (tapPolyAdd a c) (tapPolyAdd a c) =
        tapPolyAdd (tapPolyMul (tapPolyAdd a c) a)
          (tapPolyMul (tapPolyAdd a c) c) := by
      change tapPolyMul (a ^^^ c) (a ^^^ c) =
        tapPolyMul (a ^^^ c) a ^^^ tapPolyMul (a ^^^ c) c
      exact tapPolyMulXorRight (a ^^^ c) a c
    _ = tapPolyAdd
          (tapPolyAdd (tapPolyMul a a) (tapPolyMul c a))
          (tapPolyAdd (tapPolyMul a c) (tapPolyMul c c)) := by
      change tapPolyMul (a ^^^ c) a ^^^
        tapPolyMul (a ^^^ c) c =
          (tapPolyMul a a ^^^ tapPolyMul c a) ^^^
            (tapPolyMul a c ^^^ tapPolyMul c c)
      rw [tapPolyMulXorLeft a c a, tapPolyMulXorLeft a c c]
    _ = tapPolyAdd (tapPolyMul a a) (tapPolyMul c c) := by
      change (tapPolyMul a a ^^^ tapPolyMul c a) ^^^
        (tapPolyMul a c ^^^ tapPolyMul c c) =
          tapPolyMul a a ^^^ tapPolyMul c c
      rw [tapPolyMulCommutative c a, Nat.xor_assoc,
        ← Nat.xor_assoc (tapPolyMul a c)
          (tapPolyMul a c) (tapPolyMul c c),
        Nat.xor_self, Nat.zero_xor]

/-- Multiplication of two monomials adds their exponents.
Consumer: PrimitiveMaskDivision and PrimitiveMaskFactors. -/
theorem tapPolyPowerOfX (j k : Nat) :
    tapPolyMul (2 ^ j) (2 ^ k) = 2 ^ (j + k) := by
  rw [tapPolyMulPowerTwo, Nat.shiftLeft_eq]
  exact (Nat.pow_add 2 j k).symm

end L3

#print axioms L3.tapPolyMulAssociative
#print axioms L3.tapPolyMulBounds
#print axioms L3.tapPolySquare

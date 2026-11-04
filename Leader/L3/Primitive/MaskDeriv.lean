import Leader.L3.Primitive.MaskFactors

/-!
Formal derivatives of binary-polynomial Nat masks, squarefreeness of
X^(2^t) + X, and the no-duplicate irreducible-factor property.

This module works with the already imported L3.tapPolyDeriv and
L3.tapFrobeniusMask definitions. It does not redeclare either name.
Consumer: PrimitiveIrreducibleExistence.

Core Lean 4.33 only.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- An accessible recursive description of the even-position bit
mask used by the imported derivative. Consumer: tapPolyDerivTestBit. -/
private def tapDerivVisibleEvenMask : Nat → Nat
  | 0 => 0
  | k + 1 => 1 + 4 * tapDerivVisibleEvenMask k

/-- The imported derivative's private mask agrees extensionally
with this recursive mask. Consumer: tapPolyDerivTestBit. -/
private theorem tapDerivVisibleMaskAgrees (p : Nat) :
    tapPolyDeriv p =
      (p / 2) &&& tapDerivVisibleEvenMask (Nat.log2 p + 1) := by
  unfold tapPolyDeriv
  apply congrArg (fun x : Nat => (p / 2) &&& x)
  generalize Nat.log2 p + 1 = fuel
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      exact congrArg (fun x : Nat => 1 + 4 * x) ih

/-- The recursive mask has exactly the even bits below twice
its fuel. Consumer: tapPolyDerivTestBit. -/
private theorem tapDerivVisibleEvenMaskBit (fuel j : Nat) :
    Nat.testBit (tapDerivVisibleEvenMask fuel) j =
      ((j % 2 == 0) && decide (j < 2 * fuel)) := by
  induction fuel generalizing j with
  | zero =>
      simp [tapDerivVisibleEvenMask]
  | succ fuel ih =>
      have hshift : ∀ k : Nat,
          Nat.testBit (tapDerivVisibleEvenMask (fuel + 1)) k =
            if k < 2 then Nat.testBit 1 k
            else Nat.testBit (tapDerivVisibleEvenMask fuel) (k - 2) := by
        intro k
        change Nat.testBit
            (1 + 4 * tapDerivVisibleEvenMask fuel) k = _
        rw [Nat.add_comm 1 (4 * tapDerivVisibleEvenMask fuel)]
        change Nat.testBit
          (2 ^ 2 * tapDerivVisibleEvenMask fuel + 1) k = _
        exact Nat.testBit_two_pow_mul_add
          (tapDerivVisibleEvenMask fuel)
          (by decide : 1 < 2 ^ 2) k
      rw [hshift]
      cases j with
      | zero =>
          simp
      | succ j =>
          cases j with
          | zero =>
              simp
              decide
          | succ j =>
              have hnot : ¬ j + 1 + 1 < 2 := by omega
              have hsub : j + 1 + 1 - 2 = j := by omega
              have hparity : (j + 1 + 1) % 2 = j % 2 := by omega
              have hdec :
                  decide (j + 1 + 1 < 2 * (fuel + 1)) =
                    decide (j < 2 * fuel) :=
                decide_eq_decide.mpr (by omega)
              rw [if_neg hnot, hsub, ih j, hparity, hdec]

/-- A set bit at a positive source position is below
the derivative's mask-fuel bound.
Consumer: tapPolyDerivTestBit. -/
private theorem tapDerivSetBitWithinMask (p j : Nat)
    (hbit : Nat.testBit p (j + 1) = true) :
    j < 2 * (Nat.log2 p + 1) := by
  have hp : p ≠ 0 := by
    intro hz
    rw [hz, Nat.zero_testBit] at hbit
    cases hbit
  have hmax := (tapMaskLog p hp).2
  by_cases hge : Nat.log2 p + 1 ≤ j + 1
  · have hpow :
        2 ^ (Nat.log2 p + 1) ≤ 2 ^ (j + 1) :=
      Nat.pow_le_pow_right (by decide) hge
    have hsmall : p < 2 ^ (j + 1) :=
      Nat.lt_of_lt_of_le hmax hpow
    have hz : Nat.testBit p (j + 1) = false :=
      Nat.testBit_lt_two_pow hsmall
    rw [hz] at hbit
    cases hbit
  · omega

/-- Bit-level specification of the imported formal derivative.
Consumer: tapPolyDerivAdd, tapPolyDerivDouble,
tapFrobeniusMaskDeriv, and PrimitiveIrreducibleExistence. -/
theorem tapPolyDerivTestBit (p j : Nat) :
    Nat.testBit (tapPolyDeriv p) j =
      (Nat.testBit p (j + 1) && (j % 2 == 0)) := by
  rw [tapDerivVisibleMaskAgrees,
    Nat.testBit_and, Nat.testBit_div_two,
    tapDerivVisibleEvenMaskBit]
  by_cases hbit : Nat.testBit p (j + 1) = true
  · have hbound := tapDerivSetBitWithinMask p j hbit
    simp [hbit, hbound]
  · simp [hbit]

/-- The derivative of the zero mask is zero.
Consumer: tapPolyDerivMul. -/
private theorem tapPolyDerivZero : tapPolyDeriv 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [tapPolyDerivTestBit, Nat.zero_testBit, Nat.zero_testBit]
  rfl

/-- The derivative is additive in the binary polynomial mask.
Consumer: tapPolyDerivMul and PrimitiveIrreducibleExistence. -/
theorem tapPolyDerivAdd (a c : Nat) :
    tapPolyDeriv (tapPolyAdd a c) =
      tapPolyAdd (tapPolyDeriv a) (tapPolyDeriv c) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change Nat.testBit (tapPolyDeriv (a ^^^ c)) j =
    Nat.testBit (tapPolyDeriv a ^^^ tapPolyDeriv c) j
  rw [tapPolyDerivTestBit, Nat.testBit_xor,
    Nat.testBit_xor, tapPolyDerivTestBit,
    tapPolyDerivTestBit]
  cases hpar : (j % 2 == 0) with
  | false =>
      simp [hpar]
  | true =>
      cases Nat.testBit a (j + 1) <;>
        cases Nat.testBit c (j + 1) <;>
        rfl

/-- Bits of a mask shifted by one place, at positive indices.
Consumer: tapPolyDerivDouble and tapPolyDerivIgnoresLow. -/
private theorem tapDerivDoubleBit (p j : Nat) :
    Nat.testBit (2 * p) (j + 1) = Nat.testBit p j := by
  exact (Nat.testBit_succ (2 * p) j).trans
    (by rw [Nat.mul_div_cancel_left p (by decide : 0 < 2)])

/-- The zero bit of a doubled mask vanishes.
Consumer: tapPolyDerivDouble. -/
private theorem tapDerivDoubleZeroBit (p : Nat) :
    Nat.testBit (2 * p) 0 = false := by
  simp [Nat.testBit_zero, Nat.mul_mod_right]

/-- Formal differentiation of X times a polynomial:
D(Xp) = p + X D(p) in characteristic two.
Consumer: tapPolyDerivMul and PrimitiveIrreducibleExistence. -/
theorem tapPolyDerivDouble (p : Nat) :
    tapPolyDeriv (2 * p) =
      tapPolyAdd p (2 * tapPolyDeriv p) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change Nat.testBit (tapPolyDeriv (2 * p)) j =
    Nat.testBit (p ^^^ 2 * tapPolyDeriv p) j
  rw [tapPolyDerivTestBit, Nat.testBit_xor]
  cases j with
  | zero =>
      rw [tapDerivDoubleBit p 0,
        tapDerivDoubleZeroBit (tapPolyDeriv p)]
      simp
  | succ j =>
      have hbit :
          Nat.testBit (2 * p) ((j + 1) + 1) =
            Nat.testBit p (j + 1) :=
        tapDerivDoubleBit p (j + 1)
      have hother :
          Nat.testBit (2 * tapPolyDeriv p) (j + 1) =
            Nat.testBit (tapPolyDeriv p) j :=
        tapDerivDoubleBit (tapPolyDeriv p) j
      rw [hbit, hother, tapPolyDerivTestBit]
      by_cases heven : j % 2 = 0
      · have hodd : (j + 1) % 2 ≠ 0 := by omega
        simp [heven, hodd]
      · have hodd : j % 2 = 1 := by omega
        have hevenNext : (j + 1) % 2 = 0 := by omega
        simp [hodd, hevenNext]

/-- Multiplication by two distributes over polynomial XOR.
Consumer: tapPolyDerivMul. -/
private theorem tapDerivDoubleXor (a c : Nat) :
    2 * (a ^^^ c) = (2 * a) ^^^ (2 * c) := by
  have h := Nat.shiftLeft_xor_distrib
    (a := a) (b := c) (i := 1)
  simpa only [Nat.shiftLeft_eq, Nat.pow_one,
    Nat.mul_comm] using h

/-- The derivative ignores the constant coefficient.
Consumer: tapPolyDerivQuot and tapPolyDerivMul. -/
private theorem tapPolyDerivIgnoresLow (p : Nat) :
    tapPolyDeriv p =
      tapPolyDeriv (2 * (p / 2)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [tapPolyDerivTestBit, tapPolyDerivTestBit,
    tapDerivDoubleBit (p / 2) j, Nat.testBit_div_two]

/-- The source recurrence for the derivative reads the high
bits of the literal multiplier:
D(p) = p/2 + X D(p/2).
Consumer: tapPolyDerivMul. -/
private theorem tapPolyDerivQuot (p : Nat) :
    tapPolyDeriv p =
      tapPolyAdd (p / 2) (2 * tapPolyDeriv (p / 2)) := by
  rw [tapPolyDerivIgnoresLow p, tapPolyDerivDouble]

/-- Multiplication by two on the second factor agrees with
doubling the polynomial product.
Consumer: tapPolyDerivMul. -/
private theorem tapDerivMulDoubleRight (a c : Nat) :
    tapPolyMul a (2 * c) = 2 * tapPolyMul a c := by
  calc
    tapPolyMul a (2 * c) = tapPolyMul (2 * c) a :=
      tapPolyMulCommutative a (2 * c)
    _ = 2 * tapPolyMul c a :=
      tapPolyMulDoubleLeft c a
    _ = 2 * tapPolyMul a c := by
      rw [tapPolyMulCommutative c a]

/-- A four-term XOR shuffle preserving both pairwise groups.
Consumer: tapPolyDerivMul. -/
private theorem tapDerivXorShuffle (w x y z : Nat) :
    w ^^^ (x ^^^ (y ^^^ z)) =
      (w ^^^ y) ^^^ (x ^^^ z) := by
  calc
    w ^^^ (x ^^^ (y ^^^ z)) =
        w ^^^ (y ^^^ (x ^^^ z)) := by
      have inner : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
        rw [← Nat.xor_assoc, Nat.xor_comm x y, Nat.xor_assoc]
      rw [inner]
    _ = (w ^^^ y) ^^^ (x ^^^ z) :=
      (Nat.xor_assoc w y (x ^^^ z)).symm

/-- Product rule for the actual carryless product and the
imported mask derivative, obtained by strong induction on
the low-bit recurrence for the multiplier.
Consumer: tapFrobeniusSquarefree and PrimitiveIrreducibleExistence. -/
theorem tapPolyDerivMul (a c : Nat) :
    tapPolyDeriv (tapPolyMul a c) =
      tapPolyAdd (tapPolyMul (tapPolyDeriv a) c)
        (tapPolyMul a (tapPolyDeriv c)) := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
      by_cases hz : c = 0
      · subst c
        simp only [tapPolyMulZeroRight, tapPolyDerivZero]
        change (0 : Nat) = 0 ^^^ 0
        rfl
      · have hsmall : c / 2 < c := by omega
        have hrec := ih (c / 2) hsmall
        have hbit :
            tapPolyDeriv
                (if c % 2 = 1 then a else 0) =
              (if c % 2 = 1 then tapPolyDeriv a else 0) := by
          split
          · rfl
          · exact tapPolyDerivZero
        have hfactor :
            tapPolyMul a c =
              (if c % 2 = 1 then a else 0) ^^^
                (2 * tapPolyMul a (c / 2)) := by
          rw [tapPolyMulStep a c,
            tapPolyMulDoubleLeft a (c / 2)]
        have hsource :
            tapPolyMul (tapPolyDeriv a) c =
              (if c % 2 = 1 then tapPolyDeriv a else 0) ^^^
                (2 * tapPolyMul (tapPolyDeriv a) (c / 2)) := by
          rw [tapPolyMulStep (tapPolyDeriv a) c,
            tapPolyMulDoubleLeft (tapPolyDeriv a) (c / 2)]
        have hdest :
            tapPolyMul a (tapPolyDeriv c) =
              tapPolyMul a (c / 2) ^^^
                (2 * tapPolyMul a (tapPolyDeriv (c / 2))) := by
          rw [tapPolyDerivQuot c]
          change tapPolyMul a
              ((c / 2) ^^^ 2 * tapPolyDeriv (c / 2)) =
            tapPolyMul a (c / 2) ^^^
              (2 * tapPolyMul a (tapPolyDeriv (c / 2)))
          rw [tapPolyMulXorRight,
            tapDerivMulDoubleRight]
        have hDerivXor : ∀ x y : Nat,
            tapPolyDeriv (x ^^^ y) =
              tapPolyDeriv x ^^^ tapPolyDeriv y :=
          fun x y => tapPolyDerivAdd x y
        have hDouble : ∀ q : Nat,
            tapPolyDeriv (2 * q) = q ^^^ 2 * tapPolyDeriv q :=
          fun q => tapPolyDerivDouble q
        have hrecXor :
            tapPolyDeriv (tapPolyMul a (c / 2)) =
              tapPolyMul (tapPolyDeriv a) (c / 2) ^^^
                tapPolyMul a (tapPolyDeriv (c / 2)) := hrec
        change tapPolyDeriv (tapPolyMul a c) =
          tapPolyMul (tapPolyDeriv a) c ^^^
            tapPolyMul a (tapPolyDeriv c)
        calc
          tapPolyDeriv (tapPolyMul a c) =
              tapPolyDeriv
                ((if c % 2 = 1 then a else 0) ^^^
                  2 * tapPolyMul a (c / 2)) := by
            rw [hfactor]
          _ = (if c % 2 = 1 then tapPolyDeriv a else 0) ^^^
                (tapPolyMul a (c / 2) ^^^
                  2 * tapPolyDeriv (tapPolyMul a (c / 2))) := by
            rw [hDerivXor, hbit, hDouble]
          _ = (if c % 2 = 1 then tapPolyDeriv a else 0) ^^^
                (tapPolyMul a (c / 2) ^^^
                  2 * (tapPolyMul (tapPolyDeriv a) (c / 2) ^^^
                    tapPolyMul a (tapPolyDeriv (c / 2)))) := by
            rw [hrecXor]
          _ = (if c % 2 = 1 then tapPolyDeriv a else 0) ^^^
                (tapPolyMul a (c / 2) ^^^
                  ((2 * tapPolyMul (tapPolyDeriv a) (c / 2)) ^^^
                    (2 * tapPolyMul a (tapPolyDeriv (c / 2))))) := by
            rw [tapDerivDoubleXor]
          _ = ((if c % 2 = 1 then tapPolyDeriv a else 0) ^^^
                (2 * tapPolyMul (tapPolyDeriv a) (c / 2))) ^^^
                (tapPolyMul a (c / 2) ^^^
                  2 * tapPolyMul a (tapPolyDeriv (c / 2))) :=
            tapDerivXorShuffle _ _ _ _
          _ = tapPolyMul (tapPolyDeriv a) c ^^^
                tapPolyMul a (tapPolyDeriv c) := by
            rw [hsource, hdest]

/-- Derivative of a monomial with an even exponent is zero.
Consumer: tapFrobeniusMaskDeriv. -/
private theorem tapPolyDerivEvenPower (n : Nat)
    (heven : n % 2 = 0) :
    tapPolyDeriv (2 ^ n) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [tapPolyDerivTestBit, Nat.zero_testBit,
    Nat.testBit_two_pow]
  by_cases hindex : n = j + 1
  · have hodd : j % 2 ≠ 0 := by omega
    simp [hindex, hodd]
  · simp [hindex]

/-- The inner exponent of X^(2^t) is even for positive t.
Consumer: tapFrobeniusMaskDeriv. -/
private theorem tapFrobeniusInnerEven (t : Nat) (ht : 1 ≤ t) :
    (2 ^ t) % 2 = 0 := by
  have hindex : t - 1 + 1 = t := by omega
  have hpow : 2 ^ t = 2 * 2 ^ (t - 1) :=
    calc
      2 ^ t = 2 ^ (t - 1 + 1) := by rw [hindex]
      _ = 2 ^ (t - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (t - 1) := Nat.mul_comm _ _
  rw [hpow]
  exact Nat.mul_mod_right 2 _

/-- The lower singleton monomial is strictly below the top
bit of the Frobenius mask.
Consumer: tapFrobeniusMaskLog. -/
private theorem tapFrobeniusSmallTerm (t : Nat) (ht : 1 ≤ t) :
    2 < 2 ^ (2 ^ t) := by
  have htwo : 2 ≤ 2 ^ t := by
    have hpower :
        2 ^ 1 ≤ 2 ^ t :=
      Nat.pow_le_pow_right (by decide) ht
    simpa only [Nat.pow_one] using hpower
  have hpower :
      2 ^ 2 ≤ 2 ^ (2 ^ t) :=
    Nat.pow_le_pow_right (by decide) htwo
  have hfour : 2 < 2 ^ 2 := by decide
  exact Nat.lt_of_lt_of_le hfour hpower

/-- The Frobenius mask has exactly top degree 2^t.
Consumer: PrimitiveIrreducibleExistence. -/
theorem tapFrobeniusMaskLog (t : Nat) (ht : 1 ≤ t) :
    Nat.log2 (tapFrobeniusMask t) = 2 ^ t := by
  have hsmall := tapFrobeniusSmallTerm t ht
  have hsmallBit :
      Nat.testBit 2 (2 ^ t) = false :=
    Nat.testBit_lt_two_pow hsmall
  have htopBit :
      Nat.testBit (tapFrobeniusMask t) (2 ^ t) = true := by
    unfold tapFrobeniusMask
    change Nat.testBit ((2 ^ (2 ^ t)) ^^^ 2) (2 ^ t) = true
    rw [Nat.testBit_xor, Nat.testBit_two_pow_self,
      hsmallBit]
    try rfl
  have hlo : 2 ^ (2 ^ t) ≤ tapFrobeniusMask t :=
    Nat.ge_two_pow_of_testBit htopBit
  have hhigh :
      2 ^ (2 ^ t) < 2 ^ (2 ^ t + 1) := by
    rw [Nat.pow_succ]
    have hpos : 0 < 2 ^ (2 ^ t) :=
      Nat.two_pow_pos _
    omega
  have hlow : 2 < 2 ^ (2 ^ t + 1) :=
    Nat.lt_trans hsmall hhigh
  have hhi : tapFrobeniusMask t < 2 ^ (2 ^ t + 1) :=
    tapPolyAddBelow (2 ^ (2 ^ t)) 2
      (2 ^ t + 1) hhigh hlow
  exact tapMaskLogOfBounds (tapFrobeniusMask t)
    (2 ^ t) hlo hhi

/-- The Frobenius mask's derivative is exactly one:
the even-degree top monomial disappears and X differentiates
to one. Consumer: tapFrobeniusSquarefree. -/
theorem tapFrobeniusMaskDeriv (t : Nat) (ht : 1 ≤ t) :
    tapPolyDeriv (tapFrobeniusMask t) = 1 := by
  unfold tapFrobeniusMask
  rw [tapPolyDerivAdd,
    tapPolyDerivEvenPower (2 ^ t)
      (tapFrobeniusInnerEven t ht)]
  have hlinear : tapPolyDeriv 2 = 1 := by
    rfl
  rw [hlinear]
  change (0 : Nat) ^^^ 1 = 1
  rfl

/-- The Frobenius mask is nonzero, as its highest bit lies
at a positive power-of-two index.
Consumer: tapFrobeniusSquarefree and PrimitiveIrreducibleExistence. -/
theorem tapFrobeniusMaskNeZero (t : Nat) (ht : 1 ≤ t) :
    tapFrobeniusMask t ≠ 0 := by
  intro hz
  have hlog := tapFrobeniusMaskLog t ht
  rw [hz] at hlog
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  have h0 : Nat.log2 0 = 0 := by simp
  omega

/-- No nonunit polynomial square can divide the Frobenius mask.
Its derivative is one, whereas the derivative of any square
multiple is a multiple of that square.
Consumer: PrimitiveIrreducibleExistence. -/
theorem tapFrobeniusSquarefree (t a c : Nat)
    (ht : 1 ≤ t) (ha : a ≠ 1)
    (h : tapFrobeniusMask t =
      tapPolyMul (tapPolyMul a a) c) : False := by
  have hDerivativeSquare :
      tapPolyDeriv (tapPolyMul a a) = 0 := by
    rw [tapPolyDerivMul,
      tapPolyMulCommutative (tapPolyDeriv a) a]
    exact tapPolyAddSelf _
  have hDerivative :
      tapPolyDeriv (tapFrobeniusMask t) =
        tapPolyMul (tapPolyMul a a) (tapPolyDeriv c) := by
    rw [h, tapPolyDerivMul, hDerivativeSquare,
      tapPolyMulZeroLeft]
    change (0 : Nat) ^^^
      tapPolyMul (tapPolyMul a a) (tapPolyDeriv c) =
        tapPolyMul (tapPolyMul a a) (tapPolyDeriv c)
    exact Nat.zero_xor _
  have hone :
      1 = tapPolyMul (tapPolyDeriv c) (tapPolyMul a a) := by
    calc
      1 = tapPolyDeriv (tapFrobeniusMask t) :=
        (tapFrobeniusMaskDeriv t ht).symm
      _ = tapPolyMul (tapPolyMul a a) (tapPolyDeriv c) :=
        hDerivative
      _ = tapPolyMul (tapPolyDeriv c) (tapPolyMul a a) :=
        tapPolyMulCommutative _ _
  have hSquareOne : tapPolyMul a a = 1 :=
    tapPolyDvdOneEq (tapPolyMul a a) ⟨tapPolyDeriv c, hone⟩
  have hAOne : a = 1 :=
    tapPolyDvdOneEq a ⟨a, hSquareOne.symm⟩
  exact ha hAOne

/-- Extract a selected occurrence as a left polynomial factor,
without sorting or unique factorization.
Consumer: tapFrobeniusFactorsDistinct. -/
private theorem tapPolyListProdMember (l : List Nat) (f : Nat)
    (hmem : f ∈ l) :
    ∃ q : Nat, tapPolyListProd l = tapPolyMul f q := by
  induction l with
  | nil =>
      cases hmem
  | cons a rest ih =>
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst f
        exact ⟨tapPolyListProd rest, rfl⟩
      · obtain ⟨q, hprod⟩ := ih hrest
        refine ⟨tapPolyMul a q, ?_⟩
        change tapPolyMul a (tapPolyListProd rest) =
          tapPolyMul f (tapPolyMul a q)
        rw [hprod]
        calc
          tapPolyMul a (tapPolyMul f q) =
              tapPolyMul (tapPolyMul a f) q :=
            (tapPolyMulAssociative a f q).symm
          _ = tapPolyMul (tapPolyMul f a) q := by
            rw [tapPolyMulCommutative a f]
          _ = tapPolyMul f (tapPolyMul a q) :=
            tapPolyMulAssociative f a q

/-- The tail's polynomial product divides the whole cons product.
Consumer: tapFrobeniusFactorsDistinct. -/
private theorem tapPolyListProdTailDvd (a : Nat) (rest : List Nat) :
    tapPolyDvd (tapPolyListProd rest)
      (tapPolyListProd (a :: rest)) := by
  exact ⟨a, rfl⟩

/-- If an irreducible-factor product divides the Frobenius mask,
no factor occurs twice. The induction descends through the
literal polynomial divisibility of list tails.
Consumer: PrimitiveIrreducibleExistence. -/
private theorem tapFrobeniusListNodupOfDvd (t : Nat)
    (ht : 1 ≤ t) :
    ∀ l : List Nat,
      tapPolyDvd (tapPolyListProd l) (tapFrobeniusMask t) →
      (∀ f : Nat, f ∈ l → TapIrreducible f) →
      l.Nodup := by
  intro l
  induction l with
  | nil =>
      intro _ _
      exact List.nodup_nil
  | cons a rest ih =>
      intro hdiv hfactor
      have htail :
          tapPolyDvd (tapPolyListProd rest)
            (tapFrobeniusMask t) :=
        tapPolyDvdTrans (tapPolyListProd rest)
          (tapPolyListProd (a :: rest))
          (tapFrobeniusMask t)
          (tapPolyListProdTailDvd a rest) hdiv
      have hrestIrr :
          ∀ f : Nat, f ∈ rest → TapIrreducible f := by
        intro f hf
        exact hfactor f (List.mem_cons_of_mem a hf)
      have hrestNodup : rest.Nodup :=
        ih htail hrestIrr
      have haIrr : TapIrreducible a :=
        hfactor a (List.mem_cons.mpr (Or.inl rfl))
      have haNe : a ≠ 1 := by
        have hge := haIrr.1
        omega
      have hnotMem : a ∉ rest := by
        intro hmem
        obtain ⟨q, hprod⟩ :=
          tapPolyListProdMember rest a hmem
        have hdouble :
            tapPolyListProd (a :: rest) =
              tapPolyMul (tapPolyMul a a) q := by
          change tapPolyMul a (tapPolyListProd rest) =
            tapPolyMul (tapPolyMul a a) q
          rw [hprod]
          exact (tapPolyMulAssociative a a q).symm
        have hsquare :
            tapPolyDvd (tapPolyMul a a)
              (tapPolyListProd (a :: rest)) := by
          refine ⟨q, ?_⟩
          rw [hdouble]
          exact tapPolyMulCommutative (tapPolyMul a a) q
        have hwhole :
            tapPolyDvd (tapPolyMul a a)
              (tapFrobeniusMask t) :=
          tapPolyDvdTrans (tapPolyMul a a)
            (tapPolyListProd (a :: rest))
            (tapFrobeniusMask t) hsquare hdiv
        obtain ⟨multiplier, hP⟩ := hwhole
        have hfactorization :
            tapFrobeniusMask t =
              tapPolyMul (tapPolyMul a a) multiplier := by
          calc
            tapFrobeniusMask t =
                tapPolyMul multiplier (tapPolyMul a a) := hP
            _ = tapPolyMul (tapPolyMul a a) multiplier :=
              tapPolyMulCommutative _ _
        exact tapFrobeniusSquarefree t a multiplier
          ht haNe hfactorization
      exact List.nodup_cons.mpr ⟨hnotMem, hrestNodup⟩

/-- The actual irreducible factors of X^(2^t)+X are pairwise
distinct. No uniqueness of factorization is assumed.
Consumer: PrimitiveIrreducibleExistence. -/
theorem tapFrobeniusFactorsDistinct (t : Nat) (l : List Nat)
    (ht : 1 ≤ t)
    (hp : tapPolyListProd l = tapFrobeniusMask t)
    (hl : ∀ f : Nat, f ∈ l → TapIrreducible f) :
    l.Nodup := by
  apply tapFrobeniusListNodupOfDvd t ht l
  · rw [hp]
    exact tapPolyDvdRefl (tapFrobeniusMask t)
  · exact hl

end L3

#print axioms L3.tapPolyDerivMul
#print axioms L3.tapFrobeniusSquarefree
#print axioms L3.tapFrobeniusFactorsDistinct

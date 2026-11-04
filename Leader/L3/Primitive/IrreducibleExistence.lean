import Leader.L3.Primitive.MaskDeriv
import Leader.L3.Primitive.MaskQuotient
import Leader.L3.Primitive.AbstractField

/-!
Existence of an irreducible binary polynomial of degree exactly t, for t >= 18.

Every irreducible factor g of X^(2^t) + X has degree dividing t: in the field
K_g = F_2[X]/(g) the Frobenius map has order dividing both t (since X^(2^t) = X)
and deg g (Fermat), hence dividing their gcd, and the root bound then forces
deg g to divide t.  The factors are pairwise distinct (the derivative of
X^(2^t) + X is one), so if none had degree t, their degrees would be at most
t / 2 and could not sum to 2^t.

Consumer: PrimitiveFeedbackMask.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Frobenius iterate of zero is zero in any binary field.
Consumer: tapResidueFrobeniusFixes. -/
private theorem tapFrobeniusZero {F : Type} (K : TapField.BinaryField F)
    (s : Nat) : K.pow K.zero (2 ^ s) = K.zero := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ s = m + 1 :=
    ⟨2 ^ s - 1, by
      have := Nat.two_pow_pos s
      omega⟩
  rw [hm]
  change K.mul (K.pow K.zero m) K.zero = K.zero
  exact TapField.BinaryField.mul_zero K _

/-- If the Frobenius iterate fixes x, it fixes every polynomial in x.
Consumer: tapResidueFrobeniusFixes. -/
private theorem tapFrobeniusPolyEval {F : Type}
    (K : TapField.BinaryField F) (x : F) (s : Nat)
    (hx : K.pow x (2 ^ s) = x) :
    ∀ n : Nat, K.pow (tapMaskPolyEval K n x) (2 ^ s) =
      tapMaskPolyEval K n x := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hz : n = 0
      · subst n
        rw [tapMaskPolyEvalZero]
        exact tapFrobeniusZero K s
      · have hsmall : n / 2 < n :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide : 1 < 2)
        have hrec := ih (n / 2) hsmall
        have hite : K.pow (if n % 2 = 1 then K.one else K.zero) (2 ^ s) =
            (if n % 2 = 1 then K.one else K.zero) := by
          by_cases hodd : n % 2 = 1
          · simp only [if_pos hodd]
            exact TapField.BinaryField.one_pow K _
          · simp only [if_neg hodd]
            exact tapFrobeniusZero K s
        rw [tapMaskPolyEvalStep K n x]
        rw [TapField.frobeniusIterAdd, TapField.frobeniusIterMul,
          hx, hrec, hite]

/-- A Frobenius iterate fixing the residue of X fixes every residue of the
quotient field, including the degree-one case.
Consumer: PrimitiveFeedbackMask via tapIrreducibleFactorDegreeDivides. -/
theorem tapResidueFrobeniusFixes (d g : Nat) (hd : 1 ≤ d)
    (hlog : Nat.log2 g = d) (hg : TapIrreducible g) (s : Nat)
    (hx : (tapMaskField d g hd hlog hg).pow
        (tapResidueOfMask d g hlog hg 2) (2 ^ s) =
      tapResidueOfMask d g hlog hg 2)
    (a : TapResidue d) :
    (tapMaskField d g hd hlog hg).pow a (2 ^ s) = a := by
  by_cases hd2 : 2 ≤ d
  · have hX : tapResidueOfMask d g hlog hg 2 = tapResidueX d hd2 :=
      Subtype.ext (tapPolyRemOfBelow d g 2 hlog hg
        (tapResidueX d hd2).property)
    rw [hX] at hx
    have h1 := tapFrobeniusPolyEval (tapMaskField d g hd hlog hg)
      (tapResidueX d hd2) s hx a.val
    rw [tapMaskPolyEvalOfResidue d g hd2 hlog hg a] at h1
    exact h1
  · have hd1 : d = 1 := by omega
    subst hd1
    have hcases : a.val = 0 ∨ a.val = 1 := by
      have := a.property
      omega
    rcases hcases with h0 | h1
    · have ha : a = (tapMaskField 1 g hd hlog hg).zero := Subtype.ext h0
      rw [ha]
      exact tapFrobeniusZero _ s
    · have ha : a = (tapMaskField 1 g hd hlog hg).one := Subtype.ext h1
      rw [ha]
      exact TapField.BinaryField.one_pow _ _

/-- Frobenius iterates are the powers with exponent a power of two.
Consumer: tapIrreducibleFactorDegreeDivides. -/
private theorem tapIterateFrobenius {F : Type} (K : TapField.BinaryField F)
    (n : Nat) :
    ∀ y : F, TapField.Nat.iterate (fun z => K.pow z 2) n y =
      K.pow y (2 ^ n) := by
  induction n with
  | zero =>
      intro y
      change y = K.pow y (2 ^ 0)
      rw [Nat.pow_zero]
      exact (K.one_mul y).symm
  | succ n ih =>
      intro y
      change TapField.Nat.iterate (fun z => K.pow z 2) n (K.pow y 2) = _
      rw [ih]
      have hexp : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hexp]
      exact (TapField.BinaryField.pow_mul K y 2 (2 ^ n)).symm

/-- The abstract finite-field core: Frobenius order dividing t and the field
cardinality 2^d force d to divide t.
Consumer: tapIrreducibleFactorDegreeDivides. -/
private theorem tapDegreeDividesOfFrobenius {F : Type}
    (K : TapField.BinaryField F) (E : TapField.Enumeration F)
    (t d : Nat) (ht : 1 ≤ t) (hd : 1 ≤ d)
    (hE : E.elems.length = 2 ^ d)
    (hfix : ∀ a : F, K.pow a (2 ^ t) = a) : d ∣ t := by
  have hdd : ∀ a : F, K.pow a (2 ^ d) = a := by
    intro a
    have h := TapField.binaryFiniteFieldFermatSelf K E a
    rw [hE] at h
    exact h
  have hit : ∀ y : F,
      TapField.Nat.iterate (fun z => K.pow z 2) t y = y := by
    intro y
    rw [tapIterateFrobenius K t y]
    exact hfix y
  have hid : ∀ y : F,
      TapField.Nat.iterate (fun z => K.pow z 2) d y = y := by
    intro y
    rw [tapIterateFrobenius K d y]
    exact hdd y
  have hgcd := TapField.functionPeriodGcd (fun z => K.pow z 2) t d hit hid
  have hgcdPos : 0 < Nat.gcd t d := Nat.gcd_pos_of_pos_left d ht
  have hroots : ∀ a : F, a ∈ E.elems →
      K.pow a (2 ^ Nat.gcd t d) = a := by
    intro a _
    have h := hgcd a
    rw [tapIterateFrobenius K (Nat.gcd t d) a] at h
    exact h
  have hm : 2 ≤ 2 ^ Nat.gcd t d := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hgcdPos
    simpa only [Nat.pow_one] using h
  have hbound := TapField.rootBoundPowSelf K (2 ^ Nat.gcd t d) hm
    E.elems E.nodup hroots
  rw [hE] at hbound
  have hle : Nat.gcd t d ≤ d := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right t d)
  have heq : Nat.gcd t d = d := by
    by_cases hlt : Nat.gcd t d < d
    · have hpow := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
      omega
    · omega
  have hdvd := Nat.gcd_dvd_left t d
  rw [heq] at hdvd
  exact hdvd

/-- Every irreducible factor of X^(2^t) + X has degree dividing t.
Consumer: PrimitiveFeedbackMask via tapLargeIrreducibleExists. -/
theorem tapIrreducibleFactorDegreeDivides (t g : Nat) (ht : 1 ≤ t)
    (hg : TapIrreducible g)
    (hdvd : tapPolyDvd g (tapFrobeniusMask t)) :
    Nat.log2 g ∣ t := by
  obtain ⟨d, hlog⟩ : ∃ d, Nat.log2 g = d := ⟨_, rfl⟩
  rw [hlog]
  have hg0 : g ≠ 0 := by
    have := hg.1
    omega
  have hd : 1 ≤ d := by
    have hb := (tapMaskLog g hg0).2
    rw [hlog] at hb
    have h2 := hg.1
    by_cases hd0 : d = 0
    · subst hd0
      omega
    · omega
  have hzero := (tapMaskFieldDvdIffZero d g hd hlog hg
    (tapFrobeniusMask t)).1 hdvd
  have hadd : tapFrobeniusMask t = tapPolyAdd (2 ^ 2 ^ t) 2 := rfl
  rw [hadd, tapResidueOfMaskAdd] at hzero
  have hzero' : (tapMaskField d g hd hlog hg).add
      (tapResidueOfMask d g hlog hg (2 ^ 2 ^ t))
      (tapResidueOfMask d g hlog hg 2) =
      (tapMaskField d g hd hlog hg).zero := hzero
  have hsame := (TapField.BinaryField.add_eq_zero_iff
    (tapMaskField d g hd hlog hg) _ _).1 hzero'
  have hx : (tapMaskField d g hd hlog hg).pow
      (tapResidueOfMask d g hlog hg 2) (2 ^ t) =
      tapResidueOfMask d g hlog hg 2 := by
    have hpow : (tapMaskField d g hd hlog hg).pow
        (tapResidueOfMask d g hlog hg 2) (2 ^ t) =
        tapResidueOfMask d g hlog hg (2 ^ 2 ^ t) := by
      apply Subtype.ext
      rw [tapMaskFieldPow d g hd hlog hg 2 (2 ^ t), tapPolyPowTwoPow]
      rfl
    exact hpow.trans hsame
  exact tapDegreeDividesOfFrobenius (tapMaskField d g hd hlog hg)
    (tapMaskEnumeration d) t d ht hd (tapMaskEnumerationLength d)
    (fun a => tapResidueFrobeniusFixes d g hd hlog hg t hx a)

/-- A listed factor divides the list product.
Consumer: tapLargeIrreducibleExists. -/
private theorem tapPolyListProdDvdMember (l : List Nat) (f : Nat)
    (hmem : f ∈ l) : tapPolyDvd f (tapPolyListProd l) := by
  induction l with
  | nil => cases hmem
  | cons a rest ih =>
      rcases List.mem_cons.mp hmem with heq | hrest
      · rw [heq]
        exact ⟨tapPolyListProd rest,
          tapPolyMulCommutative a (tapPolyListProd rest)⟩
      · obtain ⟨q, hq⟩ := ih hrest
        refine ⟨tapPolyMul a q, ?_⟩
        change tapPolyMul a (tapPolyListProd rest) =
          tapPolyMul (tapPolyMul a q) f
        rw [hq]
        exact (tapPolyMulAssociative a q f).symm

/-- A divisor of t other than t is at most t / 2.
Consumer: tapLargeIrreducibleExists. -/
private theorem tapProperDivisorHalf (d t : Nat) (ht : 1 ≤ t)
    (hdvd : d ∣ t) (hne : d ≠ t) : d ≤ t / 2 := by
  obtain ⟨k, hk⟩ := hdvd
  by_cases hk2 : 2 ≤ k
  · have h := Nat.mul_le_mul_left d hk2
    omega
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with h0 | h1
    · subst h0
      rw [Nat.mul_zero] at hk
      omega
    · subst h1
      rw [Nat.mul_one] at hk
      exact False.elim (hne hk.symm)

/-- For t >= 18, there is an irreducible binary polynomial of degree
exactly t.
Consumer: PrimitiveFeedbackMask. -/
theorem tapLargeIrreducibleExists (t : Nat) (ht : 18 ≤ t) :
    ∃ f : Nat, 2 ^ t ≤ f ∧ f < 2 ^ (t + 1) ∧ TapIrreducible f := by
  have ht1 : 1 ≤ t := by omega
  have hP0 := tapFrobeniusMaskNeZero t ht1
  obtain ⟨l, hprod, hirr, hsum⟩ := tapIrreducibleFactorList _ hP0
  have hnd := tapFrobeniusFactorsDistinct t l ht1 hprod hirr
  have hlogP := tapFrobeniusMaskLog t ht1
  have hdiv : ∀ f : Nat, f ∈ l → Nat.log2 f ∣ t := by
    intro f hf
    apply tapIrreducibleFactorDegreeDivides t f ht1 (hirr f hf)
    rw [← hprod]
    exact tapPolyListProdDvdMember l f hf
  by_cases hex : ∃ f : Nat, f ∈ l ∧ Nat.log2 f = t
  · obtain ⟨f, hf, hft⟩ := hex
    have hf0 : f ≠ 0 := by
      have := (hirr f hf).1
      omega
    have hb := tapMaskLog f hf0
    rw [hft] at hb
    exact ⟨f, hb.1, hb.2, hirr f hf⟩
  · exfalso
    have hhalf : ∀ f : Nat, f ∈ l → f ≠ 0 ∧ Nat.log2 f ≤ t / 2 := by
      intro f hf
      refine ⟨?_, ?_⟩
      · have := (hirr f hf).1
        omega
      · apply tapProperDivisorHalf _ t ht1 (hdiv f hf)
        intro hft
        exact hex ⟨f, hf, hft⟩
    have hbound := tapFactorDegreeSumBound l (t / 2) hnd hhalf
    rw [hsum, hlogP] at hbound
    have hlt := tapLogBelowOfHalf t ht
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hbound hlt)

end L3

#print axioms L3.tapIrreducibleFactorDegreeDivides
#print axioms L3.tapLargeIrreducibleExists

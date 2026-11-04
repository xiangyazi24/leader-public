import Leader.L3.Primitive.MaskRing

/-!
Euclidean division for arbitrary nonzero binary-polynomial masks.

The existing literal remainder already satisfies shifted-modulus
cancellation and XOR-linearity. We use these proved laws to reconstruct
a quotient by strict leading-bit descent; no alternate division
algorithm or extra polynomial representation is introduced.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Divisibility of literal binary polynomial masks.
Consumer: PrimitiveMaskGcd and PrimitiveMaskFactors. -/
def tapPolyDvd (a b : Nat) : Prop :=
  ∃ q : Nat, b = tapPolyMul q a

/-- The modulus aligned with the dividend's leading set bit.
Consumer: tapPolyRemLog and tapPolyDivExists. -/
private def tapPolyShiftToTop (p f : Nat) : Nat :=
  f * 2 ^ (Nat.log2 p - Nat.log2 f)

/-- The next leading-bit cancellation in the existing remainder
recurrence. Consumer: tapPolyRemLog and tapPolyDivExists. -/
private def tapPolyCancelLeading (p f : Nat) : Nat :=
  tapPolyAdd p (tapPolyShiftToTop p f)

/-- Already smaller masks are fixed by the real fuelled remainder.
Consumer: tapPolyRemLog and tapPolyDivExists. -/
private theorem tapPolyRemOfLogLt (p f : Nat) (hf : f ≠ 0)
    (hlow : p = 0 ∨ Nat.log2 p < Nat.log2 f) :
    tapPolyRem p f = p := by
  rcases hlow with hz | hlt
  · subst p
    simp [tapPolyRem, tapPolyRemFuel, hf]
  · by_cases hp : p = 0
    · subst p
      simp [tapPolyRem, tapPolyRemFuel, hf]
    · simp [tapPolyRem, tapPolyRemFuel, hf, hp, hlt]

/-- An aligned nonzero modulus has precisely the dividend's
leading-bit interval. Consumer: the strict descent used by
tapPolyRemLog and tapPolyDivExists. -/
private theorem tapPolyShiftToTopBounds (p f : Nat)
    (hp : p ≠ 0) (hf : f ≠ 0)
    (hdegree : Nat.log2 f ≤ Nat.log2 p) :
    2 ^ Nat.log2 p ≤ tapPolyShiftToTop p f ∧
      tapPolyShiftToTop p f < 2 ^ (Nat.log2 p + 1) := by
  have hpower :
      2 ^ (Nat.log2 p - Nat.log2 f) <
        2 ^ ((Nat.log2 p - Nat.log2 f) + 1) := by
    rw [Nat.pow_succ]
    have hpos : 0 < 2 ^ (Nat.log2 p - Nat.log2 f) :=
      Nat.two_pow_pos _
    omega
  have hbase :=
    tapPolyMulBounds f
      (2 ^ (Nat.log2 p - Nat.log2 f))
      (Nat.log2 f) (Nat.log2 p - Nat.log2 f)
      (tapMaskLog f hf).1 (tapMaskLog f hf).2
      (Nat.le_refl _) hpower
  rw [tapPolyMulPowerTwo, Nat.shiftLeft_eq] at hbase
  have hindex :
      Nat.log2 f + (Nat.log2 p - Nat.log2 f) =
        Nat.log2 p := by omega
  rw [hindex] at hbase
  exact hbase

/-- Cancelled leading bits strictly decrease the natural-number
mask, including the exact-cancellation zero case.
Consumer: tapPolyRemLog and tapPolyDivExists. -/
private theorem tapPolyCancelLeadingLt (p f : Nat)
    (hp : p ≠ 0) (hf : f ≠ 0)
    (hdegree : Nat.log2 f ≤ Nat.log2 p) :
    tapPolyCancelLeading p f < p := by
  have hs := tapPolyShiftToTopBounds p f hp hf hdegree
  have hshift : tapPolyShiftToTop p f ≠ 0 := by
    intro hz
    rw [hz] at hs
    have hpos : 0 < 2 ^ Nat.log2 p := Nat.two_pow_pos _
    omega
  have hlog : Nat.log2 (tapPolyShiftToTop p f) =
      Nat.log2 p :=
    tapMaskLogOfBounds (tapPolyShiftToTop p f)
      (Nat.log2 p) hs.1 hs.2
  by_cases heq : p = tapPolyShiftToTop p f
  · have hzero : tapPolyCancelLeading p f = 0 := by
      unfold tapPolyCancelLeading
      exact (tapPolyAddEqZeroIff p (tapPolyShiftToTop p f)).2 heq
    rw [hzero]
    exact Nat.pos_of_ne_zero hp
  · have hdrop :=
      tapPolyAddLogLt p (tapPolyShiftToTop p f)
        hp hshift heq hlog.symm
    have hsmall :
        tapPolyAdd p (tapPolyShiftToTop p f) <
          2 ^ Nat.log2 p :=
      (Nat.log2_lt hdrop.1).1 hdrop.2
    unfold tapPolyCancelLeading
    exact Nat.lt_of_lt_of_le hsmall (tapMaskLog p hp).1

/-- The cancelled dividend has the same exact remainder, using
the already proved arbitrary-modulus shifted cancellation.
Consumer: tapPolyRemLog and tapPolyDivExists. -/
private theorem tapPolyRemCancelLeading (p f : Nat) :
    tapPolyRem (tapPolyCancelLeading p f) f =
      tapPolyRem p f := by
  have h := tapPolyRemCancelShift p (Nat.log2 p - Nat.log2 f) f
  rw [Nat.shiftLeft_eq] at h
  exact h

/-- The literal remainder is zero or has degree below any nonzero
modulus. The existing shifted-modulus law supplies the connection
to the real fuelled algorithm.
Consumer: PrimitiveMaskGcd and PrimitiveMaskQuotient. -/
theorem tapPolyRemLog (p f : Nat) (hf : f ≠ 0) :
    tapPolyRem p f = 0 ∨
      Nat.log2 (tapPolyRem p f) < Nat.log2 f := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
      by_cases hp : p = 0
      · have hzero := tapPolyRemOfLogLt p f hf (Or.inl hp)
        exact Or.inl (hzero.trans hp)
      · by_cases hlow : Nat.log2 p < Nat.log2 f
        · have hsame :=
            tapPolyRemOfLogLt p f hf (Or.inr hlow)
          rw [hsame]
          exact Or.inr hlow
        · have hdegree : Nat.log2 f ≤ Nat.log2 p := by omega
          have hsmaller :=
            tapPolyCancelLeadingLt p f hp hf hdegree
          have hrec := ih (tapPolyCancelLeading p f) hsmaller
          rw [tapPolyRemCancelLeading p f] at hrec
          exact hrec

/-- Cancelling a shifted modulus can be reversed using XOR.
Consumer: tapPolyDivExists and PrimitiveMaskFactors. -/
private theorem tapPolyCancelUndo (p f : Nat) :
    p = tapPolyAdd (tapPolyCancelLeading p f)
      (tapPolyShiftToTop p f) := by
  show p = (p ^^^ tapPolyShiftToTop p f) ^^^ tapPolyShiftToTop p f
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- An aligned modulus is a literal polynomial monomial multiple.
Consumer: tapPolyDivExists and PrimitiveMaskFactors. -/
private theorem tapPolyShiftToTopMul (p f : Nat) :
    tapPolyShiftToTop p f =
      tapPolyMul (2 ^ (Nat.log2 p - Nat.log2 f)) f := by
  unfold tapPolyShiftToTop
  calc
    f * 2 ^ (Nat.log2 p - Nat.log2 f) =
        f <<< (Nat.log2 p - Nat.log2 f) :=
      (Nat.shiftLeft_eq _ _).symm
    _ = tapPolyMul f
        (2 ^ (Nat.log2 p - Nat.log2 f)) :=
      (tapPolyMulPowerTwo f _).symm
    _ = tapPolyMul
        (2 ^ (Nat.log2 p - Nat.log2 f)) f :=
      tapPolyMulCommutative f _

/-- Swap the final two XOR summands without a normalization
tactic. Consumer: tapPolyDivExists. -/
private theorem tapPolyXorSwapLast (a b c : Nat) :
    (a ^^^ b) ^^^ c = (a ^^^ c) ^^^ b := by
  rw [Nat.xor_assoc, Nat.xor_comm b c, ← Nat.xor_assoc]

/-- Reconstruct the original dividend from a quotient of the
cancelled dividend. Consumer: tapPolyDivExists. -/
private theorem tapPolyCancelRecompose (p f q r : Nat)
    (h : tapPolyCancelLeading p f =
      tapPolyAdd (tapPolyMul q f) r) :
    p = tapPolyAdd
      (tapPolyMul
        (tapPolyAdd q (2 ^ (Nat.log2 p - Nat.log2 f))) f) r := by
  calc
    p = tapPolyAdd (tapPolyCancelLeading p f)
          (tapPolyShiftToTop p f) :=
      tapPolyCancelUndo p f
    _ = (tapPolyMul q f ^^^ r) ^^^
          tapPolyShiftToTop p f := by rw [h]; rfl
    _ = (tapPolyMul q f ^^^ tapPolyShiftToTop p f) ^^^ r :=
      tapPolyXorSwapLast _ _ _
    _ = tapPolyAdd
          (tapPolyMul
            (tapPolyAdd q (2 ^ (Nat.log2 p - Nat.log2 f))) f) r := by
      change (tapPolyMul q f ^^^ tapPolyShiftToTop p f) ^^^ r =
        (tapPolyMul (q ^^^ (2 ^ (Nat.log2 p - Nat.log2 f))) f) ^^^ r
      rw [tapPolyMulXorLeft q
        (2 ^ (Nat.log2 p - Nat.log2 f)) f,
        ← tapPolyShiftToTopMul p f]

/-- Every mask has a Euclidean quotient by an arbitrary nonzero
modulus, with exactly the pre-existing tapPolyRem as remainder.
Consumer: PrimitiveMaskGcd, PrimitiveMaskFactors and
PrimitiveMaskQuotient. -/
theorem tapPolyDivExists (p f : Nat) (hf : f ≠ 0) :
    ∃ q : Nat,
      p = tapPolyAdd (tapPolyMul q f) (tapPolyRem p f) := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
      by_cases hp : p = 0
      · subst p
        refine ⟨0, ?_⟩
        have hrem := tapPolyRemOfLogLt 0 f hf (Or.inl rfl)
        rw [tapPolyMulZeroLeft, hrem]
        change 0 = 0 ^^^ 0
        rfl
      · by_cases hlow : Nat.log2 p < Nat.log2 f
        · refine ⟨0, ?_⟩
          have hrem := tapPolyRemOfLogLt p f hf (Or.inr hlow)
          rw [tapPolyMulZeroLeft, hrem]
          change p = 0 ^^^ p
          exact (Nat.zero_xor p).symm
        · have hdegree : Nat.log2 f ≤ Nat.log2 p := by omega
          have hsmaller :=
            tapPolyCancelLeadingLt p f hp hf hdegree
          obtain ⟨q, hq⟩ :=
            ih (tapPolyCancelLeading p f) hsmaller
          rw [tapPolyRemCancelLeading p f] at hq
          exact ⟨tapPolyAdd q (2 ^ (Nat.log2 p - Nat.log2 f)),
            tapPolyCancelRecompose p f q (tapPolyRem p f) hq⟩

/-- Recover equal opposite XOR terms from a comparison of two
two-term sums. Consumer: tapPolyRemUnique. -/
private theorem tapPolyXorCross (a b c d : Nat)
    (h : a ^^^ b = c ^^^ d) :
    a ^^^ c = b ^^^ d := by
  have hh := congrArg (fun v : Nat => (a ^^^ v) ^^^ d) h
  have hl : (a ^^^ (a ^^^ b)) ^^^ d = b ^^^ d := by
    rw [← Nat.xor_assoc a a b, Nat.xor_self, Nat.zero_xor]
  have hr : (a ^^^ (c ^^^ d)) ^^^ d = a ^^^ c := by
    rw [Nat.xor_assoc a (c ^^^ d) d, Nat.xor_assoc c d d,
      Nat.xor_self, Nat.xor_zero]
  rw [hl, hr] at hh
  exact hh.symm

/-- A mask of zero or strictly smaller log degree lies below
the modulus's leading bit. Consumer: tapPolyRemUnique. -/
private theorem tapPolySmallOfLog (r f : Nat) (hf : f ≠ 0)
    (hr : r = 0 ∨ Nat.log2 r < Nat.log2 f) :
    r < 2 ^ Nat.log2 f := by
  by_cases hz : r = 0
  · rw [hz]
    exact Nat.two_pow_pos _
  · rcases hr with heq | hlt
    · exact False.elim (hz heq)
    · exact (Nat.log2_lt hz).1 hlt

/-- No nonzero multiple of a nonzero modulus can lie strictly
below its leading-bit power. Consumer: tapPolyRemUnique and
PrimitiveMaskQuotient. -/
private theorem tapPolySmallMultipleZero (q f : Nat) (hf : f ≠ 0)
    (hsmall : tapPolyMul q f < 2 ^ Nat.log2 f) :
    q = 0 := by
  by_cases hq : q = 0
  · exact hq
  · have hnonzero := tapPolyMulNeZero q f hq hf
    have hlog := tapPolyMulLog q f hq hf
    have hlt : Nat.log2 (tapPolyMul q f) < Nat.log2 f :=
      (Nat.log2_lt hnonzero).2 hsmall
    omega

/-- The degree-bounded Euclidean remainder is unique for any
nonzero modulus. Consumer: PrimitiveMaskGcd and
PrimitiveMaskQuotient. -/
theorem tapPolyRemUnique (p f q r : Nat) (hf : f ≠ 0)
    (hp : p = tapPolyAdd (tapPolyMul q f) r)
    (hr : r = 0 ∨ Nat.log2 r < Nat.log2 f) :
    tapPolyRem p f = r := by
  obtain ⟨qold, hold⟩ := tapPolyDivExists p f hf
  have hnew : tapPolyMul q f ^^^ r =
      tapPolyMul qold f ^^^ tapPolyRem p f := by
    calc
      tapPolyMul q f ^^^ r = p := hp.symm
      _ = tapPolyMul qold f ^^^ tapPolyRem p f := hold
  have hcross :=
    tapPolyXorCross (tapPolyMul q f) r
      (tapPolyMul qold f) (tapPolyRem p f) hnew
  have hfactor :
      tapPolyMul (tapPolyAdd q qold) f =
        tapPolyAdd r (tapPolyRem p f) := by
    change tapPolyMul (q ^^^ qold) f = _
    rw [tapPolyMulXorLeft q qold f]
    exact hcross
  have hrSmall := tapPolySmallOfLog r f hf hr
  have hremSmall :=
    tapPolySmallOfLog (tapPolyRem p f) f hf
      (tapPolyRemLog p f hf)
  have hsmall :
      tapPolyAdd r (tapPolyRem p f) < 2 ^ Nat.log2 f :=
    tapPolyAddBelow r (tapPolyRem p f) (Nat.log2 f)
      hrSmall hremSmall
  have hquotZero :
      tapPolyAdd q qold = 0 :=
    tapPolySmallMultipleZero (tapPolyAdd q qold) f hf (by
      rw [hfactor]
      exact hsmall)
  have hxorZero : tapPolyAdd r (tapPolyRem p f) = 0 := by
    rw [← hfactor, hquotZero, tapPolyMulZeroLeft]
  have heq := (tapPolyAddEqZeroIff r (tapPolyRem p f)).1 hxorZero
  exact heq.symm

/-- An explicit multiple has remainder zero.
Consumer: PrimitiveMaskGcd and PrimitiveMaskFactors. -/
theorem tapPolyRemMulSelf (q f : Nat) (hf : f ≠ 0) :
    tapPolyRem (tapPolyMul q f) f = 0 := by
  have hp : tapPolyMul q f =
      tapPolyAdd (tapPolyMul q f) 0 := by
    change tapPolyMul q f = tapPolyMul q f ^^^ 0
    exact (Nat.xor_zero _).symm
  exact tapPolyRemUnique (tapPolyMul q f) f q 0 hf hp
    (Or.inl rfl)

/-- Divisibility is precisely vanishing of the actual remainder.
Consumer: PrimitiveMaskGcd, PrimitiveMaskFactors and
PrimitiveTapSelection. -/
theorem tapPolyDvdIffRemZero (p f : Nat) (hf : f ≠ 0) :
    tapPolyDvd f p ↔ tapPolyRem p f = 0 := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h
    rw [hq]
    exact tapPolyRemMulSelf q f hf
  · intro h
    obtain ⟨q, hq⟩ := tapPolyDivExists p f hf
    rw [h] at hq
    change p = tapPolyMul q f ^^^ 0 at hq
    rw [Nat.xor_zero] at hq
    exact ⟨q, hq⟩

/-- Remainder preserves addition of binary masks.
Consumer: PrimitiveMaskQuotient and PrimitiveTapSelection. -/
theorem tapPolyRemAdd (a c f : Nat) (hf : f ≠ 0) :
    tapPolyRem (tapPolyAdd a c) f =
      tapPolyAdd (tapPolyRem a f) (tapPolyRem c f) := by
  exact tapPolyRemXor a c f

/-- Multiplication is unchanged modulo f when its left factor
is first reduced. Consumer: PrimitiveMaskQuotient. -/
theorem tapPolyRemMulLeft (a c f : Nat) (hf : f ≠ 0) :
    tapPolyRem (tapPolyMul (tapPolyRem a f) c) f =
      tapPolyRem (tapPolyMul a c) f := by
  obtain ⟨q, hq⟩ := tapPolyDivExists a f hf
  have hproduct : tapPolyMul a c =
      tapPolyAdd
        (tapPolyMul (tapPolyMul q c) f)
        (tapPolyMul (tapPolyRem a f) c) := by
    calc
      tapPolyMul a c =
          tapPolyMul (tapPolyAdd (tapPolyMul q f)
            (tapPolyRem a f)) c := by rw [← hq]
      _ = tapPolyAdd (tapPolyMul (tapPolyMul q f) c)
            (tapPolyMul (tapPolyRem a f) c) := by
        exact tapPolyMulXorLeft (tapPolyMul q f)
          (tapPolyRem a f) c
      _ = tapPolyAdd (tapPolyMul (tapPolyMul q c) f)
            (tapPolyMul (tapPolyRem a f) c) := by
        rw [tapPolyMulAssociative q f c,
          tapPolyMulCommutative f c,
          ← tapPolyMulAssociative q c f]
  have hmod := congrArg (fun p : Nat => tapPolyRem p f) hproduct
  rw [tapPolyRemAdd
      (tapPolyMul (tapPolyMul q c) f)
      (tapPolyMul (tapPolyRem a f) c) f hf,
      tapPolyRemMulSelf (tapPolyMul q c) f hf] at hmod
  change tapPolyRem (tapPolyMul a c) f =
      0 ^^^ tapPolyRem (tapPolyMul (tapPolyRem a f) c) f at hmod
  simpa only [Nat.zero_xor] using hmod.symm

/-- Multiplication is unchanged modulo f when its right factor
is first reduced. Consumer: PrimitiveMaskQuotient. -/
theorem tapPolyRemMulRight (a c f : Nat) (hf : f ≠ 0) :
    tapPolyRem (tapPolyMul a (tapPolyRem c f)) f =
      tapPolyRem (tapPolyMul a c) f := by
  calc
    tapPolyRem (tapPolyMul a (tapPolyRem c f)) f =
        tapPolyRem (tapPolyMul (tapPolyRem c f) a) f := by
      rw [tapPolyMulCommutative a (tapPolyRem c f)]
    _ = tapPolyRem (tapPolyMul c a) f :=
      tapPolyRemMulLeft c a f hf
    _ = tapPolyRem (tapPolyMul a c) f := by
      rw [tapPolyMulCommutative c a]

/-- The actual remainder is idempotent for every nonzero modulus.
Consumer: PrimitiveMaskQuotient and PrimitiveTapSelection. -/
theorem tapPolyRemIdem (a f : Nat) (hf : f ≠ 0) :
    tapPolyRem (tapPolyRem a f) f = tapPolyRem a f := by
  have hp : tapPolyRem a f =
      tapPolyAdd (tapPolyMul 0 f) (tapPolyRem a f) := by
    rw [tapPolyMulZeroLeft]
    change tapPolyRem a f = 0 ^^^ tapPolyRem a f
    exact (Nat.zero_xor _).symm
  exact tapPolyRemUnique (tapPolyRem a f) f 0
    (tapPolyRem a f) hf hp (tapPolyRemLog a f hf)

/-- A divisor of b also divides any product b*c.
Consumer: PrimitiveMaskFactors and PrimitiveMaskGcd. -/
theorem tapPolyDvdMul (a b c : Nat) (h : tapPolyDvd a b) :
    tapPolyDvd a (tapPolyMul b c) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨tapPolyMul q c, ?_⟩
  rw [hq]
  calc
    tapPolyMul (tapPolyMul q a) c =
        tapPolyMul q (tapPolyMul a c) :=
      tapPolyMulAssociative q a c
    _ = tapPolyMul q (tapPolyMul c a) := by
      rw [tapPolyMulCommutative a c]
    _ = tapPolyMul (tapPolyMul q c) a :=
      (tapPolyMulAssociative q c a).symm

/-- Common divisors are closed under mask addition.
Consumer: PrimitiveMaskGcd and PrimitiveMaskFactors. -/
theorem tapPolyDvdAdd (a b c : Nat)
    (hb : tapPolyDvd a b) (hc : tapPolyDvd a c) :
    tapPolyDvd a (tapPolyAdd b c) := by
  obtain ⟨q, hq⟩ := hb
  obtain ⟨r, hr⟩ := hc
  refine ⟨tapPolyAdd q r, ?_⟩
  rw [hq, hr]
  exact (tapPolyMulXorLeft q r a).symm

/-- Each mask divides itself through the unit multiplier.
Consumer: PrimitiveMaskGcd and PrimitiveMaskFactors. -/
theorem tapPolyDvdRefl (a : Nat) : tapPolyDvd a a := by
  refine ⟨1, ?_⟩
  rw [tapPolyMulOneLeft]

/-- Divisibility is transitive by multiplication associativity.
Consumer: PrimitiveMaskGcd and PrimitiveMaskFactors. -/
theorem tapPolyDvdTrans (a b c : Nat)
    (hab : tapPolyDvd a b) (hbc : tapPolyDvd b c) :
    tapPolyDvd a c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨r, hr⟩ := hbc
  refine ⟨tapPolyMul r q, ?_⟩
  rw [hr, hq]
  exact (tapPolyMulAssociative r q a).symm

/-- The constant polynomial one divides every mask.
Consumer: PrimitiveMaskGcd and PrimitiveMaskFactors. -/
theorem tapPolyOneDvd (a : Nat) : tapPolyDvd 1 a := by
  refine ⟨a, ?_⟩
  rw [tapPolyMulOneRight]

/-- Nonzero divisibility entails an inequality of polynomial
degrees. Consumer: PrimitiveMaskGcd and PrimitiveMaskFactors. -/
theorem tapPolyDvdLog (a b : Nat)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : tapPolyDvd a b) :
    Nat.log2 a ≤ Nat.log2 b := by
  obtain ⟨q, hq⟩ := h
  have hqnonzero : q ≠ 0 := by
    intro hz
    rw [hz, tapPolyMulZeroLeft] at hq
    exact hb hq
  have hlog := tapPolyMulLog q a hqnonzero ha
  rw [hq, hlog]
  omega

/-- A multiple strictly below a nonzero modulus's degree
must vanish. Consumer: PrimitiveMaskGcd and PrimitiveMaskFactors. -/
theorem tapPolyEqOfDvdLogLt (f r : Nat) (hf : f ≠ 0)
    (h : tapPolyDvd f r)
    (hr : r = 0 ∨ Nat.log2 r < Nat.log2 f) :
    r = 0 := by
  by_cases hz : r = 0
  · exact hz
  · have hdegree := tapPolyDvdLog f r hf hz h
    rcases hr with hzero | hlt
    · exact hzero
    · omega

end L3

#print axioms L3.tapPolyDivExists
#print axioms L3.tapPolyRemUnique
#print axioms L3.tapPolyRemAdd
#print axioms L3.tapPolyRemMulLeft
#print axioms L3.tapPolyRemMulRight
#print axioms L3.tapPolyRemIdem

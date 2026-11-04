import Leader.L3.Primitive.MaskGcd
import Leader.L3.Primitive.Field
import Leader.L3.Primitive.AbstractField

/-!
Bit-mask quotient of the binary polynomial ring by an irreducible
mask. Core Lean 4.33. Compiled construction, with no changes to the
compiled mask operations, remainder, gcd or abstract field record.

Consumers: PrimitiveIrreducibleExistence, PrimitiveFeedbackMask,
PrimitiveRecurrenceBridge.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Reduced bit masks representing classes modulo a monic
irreducible polynomial. Consumer: PrimitiveIrreducibleExistence. -/
def TapResidue (d : Nat) : Type :=
  { a : Nat // a < 2 ^ d }

/-- The original literal remainder is reduced below the given
degree, and therefore supplies a quotient representative.
Consumer: PrimitiveIrreducibleExistence. -/
def tapResidueOfMask (d f : Nat)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (p : Nat) : TapResidue d :=
  ⟨tapPolyRem p f, by
    have hfzero : f ≠ 0 := by
      have htwo := hf.1
      omega
    rcases tapPolyRemLog p f hfzero with hzero | hsmaller
    · rw [hzero]
      exact Nat.two_pow_pos d
    · by_cases hz : tapPolyRem p f = 0
      · rw [hz]
        exact Nat.two_pow_pos d
      · have hh : Nat.log2 (tapPolyRem p f) < d := by
          rw [← hlog]
          exact hsmaller
        exact (Nat.log2_lt hz).1 hh⟩

/-- Every already-reduced mask is fixed by the exact
fuelled Euclidean remainder.
Consumer: PrimitiveIrreducibleExistence, quotient field laws. -/
theorem tapPolyRemOfBelow (d f a : Nat)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (ha : a < 2 ^ d) :
    tapPolyRem a f = a := by
  have hfzero : f ≠ 0 := by
    have hh := hf.1
    omega
  have hlow : a = 0 ∨ Nat.log2 a < Nat.log2 f := by
    by_cases hz : a = 0
    · exact Or.inl hz
    · exact Or.inr (by
        rw [hlog]
        exact (Nat.log2_lt hz).2 ha)
  have hrepr :
      a = tapPolyAdd (tapPolyMul 0 f) a := by
    rw [tapPolyMulZeroLeft]
    change a = 0 ^^^ a
    exact (Nat.zero_xor a).symm
  exact tapPolyRemUnique a f 0 a hfzero hrepr hlow

/-- Zero representative. Consumer: PrimitiveIrreducibleExistence. -/
def tapResidueZero (d : Nat) : TapResidue d :=
  ⟨0, Nat.two_pow_pos d⟩

/-- Unit representative at positive degree.
Consumer: PrimitiveIrreducibleExistence. -/
def tapResidueOne (d : Nat) (hd : 1 ≤ d) : TapResidue d :=
  ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩

/-- XOR addition on reduced masks.
Consumer: PrimitiveIrreducibleExistence and PrimitiveRecurrenceBridge. -/
def tapResidueAdd (d : Nat)
    (a c : TapResidue d) : TapResidue d :=
  ⟨tapPolyAdd a.val c.val,
    tapPolyAddBelow a.val c.val d a.property c.property⟩

/-- Reduced polynomial multiplication on quotient masks.
Consumer: PrimitiveIrreducibleExistence. -/
def tapResidueMul (d f : Nat)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (a c : TapResidue d) : TapResidue d :=
  tapResidueOfMask d f hlog hf (tapPolyMul a.val c.val)

/-- A literal Bezout coefficient gives each nonzero reduced
mask a multiplicative inverse. The zero inverse is defined to
be the zero mask; no law is claimed for division by zero.
Consumer: PrimitiveIrreducibleExistence. -/
noncomputable def tapResidueInverse (d f : Nat)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (a : TapResidue d) : TapResidue d :=
  if ha : a.val = 0 then tapResidueZero d
  else tapResidueOfMask d f hlog hf
    (Classical.choose (tapPolyInverseExists f a.val hf ha
      (by rw [hlog]; exact (Nat.log2_lt ha).2 a.property)))

/-- The quotient carries all twelve explicit characteristic-two
field laws in TapField.BinaryField, from the literal polynomial
and remainder theorems; no external field assumptions are introduced.
Consumer: PrimitiveIrreducibleExistence and PrimitiveFeedbackMask. -/
noncomputable def tapMaskField (d f : Nat)
    (hd : 1 ≤ d) (hlog : Nat.log2 f = d)
    (hf : TapIrreducible f) :
    TapField.BinaryField (TapResidue d) := by
  have hfzero : f ≠ 0 := by
    have hh := hf.1
    omega
  refine {
    zero := tapResidueZero d
    one := tapResidueOne d hd
    add := tapResidueAdd d
    mul := tapResidueMul d f hlog hf
    inv := tapResidueInverse d f hlog hf
    add_comm := ?_
    add_assoc := ?_
    zero_add := ?_
    add_self := ?_
    mul_comm := ?_
    mul_assoc := ?_
    one_mul := ?_
    left_distrib := ?_
    one_ne_zero := ?_
    mul_inv := ?_
  }
  · intro a b
    apply Subtype.ext
    change tapPolyAdd a.val b.val = tapPolyAdd b.val a.val
    exact tapPolyAddCommutative a.val b.val
  · intro a b c
    apply Subtype.ext
    change tapPolyAdd (tapPolyAdd a.val b.val) c.val =
      tapPolyAdd a.val (tapPolyAdd b.val c.val)
    exact tapPolyAddAssociative a.val b.val c.val
  · intro a
    apply Subtype.ext
    change tapPolyAdd 0 a.val = a.val
    exact Nat.zero_xor a.val
  · intro a
    apply Subtype.ext
    change tapPolyAdd a.val a.val = 0
    exact tapPolyAddSelf a.val
  · intro a b
    apply Subtype.ext
    change tapPolyRem (tapPolyMul a.val b.val) f =
      tapPolyRem (tapPolyMul b.val a.val) f
    rw [tapPolyMulCommutative a.val b.val]
  · intro a b c
    apply Subtype.ext
    change
      tapPolyRem
        (tapPolyMul
          (tapPolyRem (tapPolyMul a.val b.val) f)
          c.val) f =
      tapPolyRem
        (tapPolyMul a.val
          (tapPolyRem (tapPolyMul b.val c.val) f)) f
    calc
      tapPolyRem
          (tapPolyMul
            (tapPolyRem (tapPolyMul a.val b.val) f)
            c.val) f =
          tapPolyRem
            (tapPolyMul (tapPolyMul a.val b.val) c.val) f :=
        tapPolyRemMulLeft (tapPolyMul a.val b.val) c.val f hfzero
      _ = tapPolyRem
            (tapPolyMul a.val (tapPolyMul b.val c.val)) f := by
        rw [tapPolyMulAssociative]
      _ = tapPolyRem
            (tapPolyMul a.val
              (tapPolyRem (tapPolyMul b.val c.val) f)) f :=
        (tapPolyRemMulRight a.val
          (tapPolyMul b.val c.val) f hfzero).symm
  · intro a
    apply Subtype.ext
    change tapPolyRem (tapPolyMul 1 a.val) f = a.val
    rw [tapPolyMulOneLeft]
    exact tapPolyRemOfBelow d f a.val hlog hf a.property
  · intro a b c
    apply Subtype.ext
    change
      tapPolyRem (tapPolyMul a.val
        (b.val ^^^ c.val)) f =
      tapPolyAdd
        (tapPolyRem (tapPolyMul a.val b.val) f)
        (tapPolyRem (tapPolyMul a.val c.val) f)
    rw [tapPolyMulXorRight]
    exact tapPolyRemAdd _ _ f hfzero
  · intro h
    have hv := congrArg Subtype.val h
    change (1 : Nat) = 0 at hv
    omega
  · intro a hnot
    have ha : a.val ≠ 0 := by
      intro hz
      apply hnot
      apply Subtype.ext
      exact hz
    have hlogA : Nat.log2 a.val < Nat.log2 f := by
      rw [hlog]
      exact (Nat.log2_lt ha).2 a.property
    have hu :=
      Classical.choose_spec
        (tapPolyInverseExists f a.val hf ha hlogA)
    have hvalue :
        (tapResidueInverse d f hlog hf a).val =
          tapPolyRem
            (Classical.choose
              (tapPolyInverseExists f a.val hf ha hlogA)) f := by
      simp [tapResidueInverse, ha, tapResidueOfMask]
    apply Subtype.ext
    change
      tapPolyRem
        (tapPolyMul a.val
          (tapResidueInverse d f hlog hf a).val) f = 1
    rw [hvalue]
    rw [tapPolyRemMulRight a.val _ f hfzero]
    rw [tapPolyMulCommutative a.val]
    exact hu


/-- The canonical finite enumeration is the image of the
literal interval List.range (2^d), with each index reduced
to the unique mask in the subtype.
Consumer: PrimitiveIrreducibleExistence, finite-field cardinality. -/
def tapMaskEnumeration (d : Nat) :
    TapField.Enumeration (TapResidue d) := by
  refine {
    elems := (List.range (2 ^ d)).map
      (fun i : Nat =>
        (⟨i % (2 ^ d), Nat.mod_lt i (Nat.two_pow_pos d)⟩ :
          TapResidue d))
    nodup := ?_
    complete := ?_
  }
  · have hpair : (List.range (2 ^ d)).Pairwise
        (fun a b : Nat => a ≠ b) :=
      List.nodup_range
    apply (List.pairwise_map).2
    apply hpair.imp_of_mem
    intro a b ha hb hne heq
    have haLt : a < 2 ^ d := (List.mem_range).1 ha
    have hbLt : b < 2 ^ d := (List.mem_range).1 hb
    have hv := congrArg Subtype.val heq
    change a % 2 ^ d = b % 2 ^ d at hv
    rw [Nat.mod_eq_of_lt haLt,
      Nat.mod_eq_of_lt hbLt] at hv
    exact hne hv
  · intro a
    apply List.mem_map.mpr
    refine ⟨a.val, (List.mem_range).2 a.property, ?_⟩
    apply Subtype.ext
    change a.val % 2 ^ d = a.val
    exact Nat.mod_eq_of_lt a.property

/-- The enumeration contains precisely the expected 2^d
positions, without assuming cardinality externally.
Consumer: PrimitiveIrreducibleExistence. -/
theorem tapMaskEnumerationLength (d : Nat) :
    (tapMaskEnumeration d).elems.length = 2 ^ d := by
  change
    ((List.range (2 ^ d)).map
      (fun i : Nat =>
        (⟨i % (2 ^ d), Nat.mod_lt i (Nat.two_pow_pos d)⟩ :
          TapResidue d))).length = 2 ^ d
  simp only [List.length_map, List.length_range]

/-- The residue of X at positive degree at least two.
Consumer: PrimitiveFeedbackMask and PrimitiveRecurrenceBridge. -/
def tapResidueX (d : Nat) (hd : 2 ≤ d) : TapResidue d :=
  ⟨2, by
    have hpow : 2 ^ 2 ≤ 2 ^ d :=
      Nat.pow_le_pow_of_le (by decide : 1 < (2 : Nat)) hd
    have hsmall : 2 < 2 ^ 2 := by decide
    omega⟩


/-- Polynomial multiplication power in the literal mask
representation. Consumer: PrimitiveRecurrenceBridge. -/
def tapPolyPow (a : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => tapPolyMul (tapPolyPow a k) a

/-- In the mask model, X^k is exactly the single-bit mask
2^k, by the existing monomial product theorem.
Consumer: PrimitiveRecurrenceBridge, feedback basis. -/
theorem tapPolyPowTwoPow (k : Nat) :
    tapPolyPow 2 k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change tapPolyMul (tapPolyPow 2 k) 2 = 2 ^ (k + 1)
      rw [ih]
      calc
        tapPolyMul (2 ^ k) 2 =
            tapPolyMul (2 ^ k) (2 ^ 1) := by rfl
        _ = 2 ^ (k + 1) := tapPolyPowerOfX k 1

/-- An iterated product in the quotient is exactly the
remainder of the corresponding unreduced mask product.
Consumer: PrimitiveRecurrenceBridge, multiplicative order. -/
theorem tapMaskFieldPow (d f : Nat)
    (hd : 1 ≤ d)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (p k : Nat) :
    ((tapMaskField d f hd hlog hf).pow
      (tapResidueOfMask d f hlog hf p) k).val =
      tapPolyRem (tapPolyPow p k) f := by
  have hfzero : f ≠ 0 := by
    have hh := hf.1
    omega
  induction k with
  | zero =>
      change (1 : Nat) = tapPolyRem 1 f
      exact (tapPolyRemOfBelow d f 1 hlog hf
        (Nat.one_lt_two_pow (by omega : d ≠ 0))).symm
  | succ k ih =>
      change
        tapPolyRem
          (tapPolyMul
            ((tapMaskField d f hd hlog hf).pow
              (tapResidueOfMask d f hlog hf p) k).val
            (tapPolyRem p f)) f =
        tapPolyRem (tapPolyMul (tapPolyPow p k) p) f
      rw [ih]
      rw [tapPolyRemMulLeft (tapPolyPow p k)
        (tapPolyRem p f) f hfzero]
      exact tapPolyRemMulRight (tapPolyPow p k) p f hfzero


/-- Universal bit-mask Horner evaluation in ANY BinaryField.
Each low bit contributes one unit and the higher bits are
multiplied by x; this is the finite polynomial sum
over the binary digits, not an interpretation restricted
to this particular quotient.
Consumer: PrimitiveFeedbackMask and PrimitiveRecurrenceBridge. -/
def tapMaskPolyEval {F : Type}
    (K : TapField.BinaryField F) (a : Nat) (x : F) : F :=
  if ha : a = 0 then K.zero
  else
    K.add (if a % 2 = 1 then K.one else K.zero)
      (K.mul x (tapMaskPolyEval K (a / 2) x))
termination_by a
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ha)
    (by decide : 1 < 2)

/-- A zero mask evaluates to zero in any binary field.
Consumer: PrimitiveRecurrenceBridge. -/
theorem tapMaskPolyEvalZero {F : Type}
    (K : TapField.BinaryField F) (x : F) :
    tapMaskPolyEval K 0 x = K.zero := by
  rw [tapMaskPolyEval.eq_1]
  simp

/-- One least-significant-bit recursion step gives the
finite characteristic-two Horner sum for every mask,
including the zero mask.
Consumer: PrimitiveFeedbackMask, evaluation arithmetic. -/
theorem tapMaskPolyEvalStep {F : Type}
    (K : TapField.BinaryField F) (a : Nat) (x : F) :
    tapMaskPolyEval K a x =
      K.add (if a % 2 = 1 then K.one else K.zero)
        (K.mul x (tapMaskPolyEval K (a / 2) x)) := by
  rw [tapMaskPolyEval.eq_1]
  split
  · next hzero =>
      subst a
      rw [tapMaskPolyEvalZero]
      change K.zero =
        K.add K.zero (K.mul x K.zero)
      rw [TapField.BinaryField.mul_zero K x]
      exact (K.zero_add K.zero).symm
  · rfl

/-- A unit bit mask evaluates to the field unit.
Consumer: PrimitiveFeedbackMask. -/
theorem tapMaskPolyEvalOne {F : Type}
    (K : TapField.BinaryField F) (x : F) :
    tapMaskPolyEval K 1 x = K.one := by
  rw [tapMaskPolyEvalStep]
  change K.add K.one
    (K.mul x (tapMaskPolyEval K 0 x)) = K.one
  rw [tapMaskPolyEvalZero,
    TapField.BinaryField.mul_zero K x,
    TapField.BinaryField.add_zero K K.one]

/-- Multiplication of a bit mask by 2 shifts its
polynomial evaluation by one power of x.
Consumer: PrimitiveRecurrenceBridge, multiplication law. -/
theorem tapMaskPolyEvalDouble {F : Type}
    (K : TapField.BinaryField F) (a : Nat) (x : F) :
    tapMaskPolyEval K (2 * a) x =
      K.mul x (tapMaskPolyEval K a x) := by
  rw [tapMaskPolyEvalStep]
  have hmod : (2 * a) % 2 ≠ 1 := by omega
  have hdiv : (2 * a) / 2 = a := by omega
  rw [if_neg hmod, hdiv]
  exact K.zero_add _

/-- Constant bits add like the XOR of their parities.
Consumer: PrimitiveFeedbackMask, evaluation-add law. -/
private theorem tapMaskParityAdd {F : Type}
    (K : TapField.BinaryField F) (a b : Nat) :
    K.add (if a % 2 = 1 then K.one else K.zero)
      (if b % 2 = 1 then K.one else K.zero) =
      (if (a ^^^ b) % 2 = 1 then K.one else K.zero) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · simp [ha, hb, Nat.xor_mod_two_eq_one, K.zero_add]
  · simp [ha, hb, Nat.xor_mod_two_eq_one, K.zero_add]
  · simp [ha, hb, Nat.xor_mod_two_eq_one,
      TapField.BinaryField.add_zero K]
  · simp [ha, hb, Nat.xor_mod_two_eq_one, K.add_self]

/-- Commutative rebracketing of four characteristic-two
summands, from the explicit BinaryField add laws.
Consumer: PrimitiveFeedbackMask, evaluation-add law. -/
private theorem tapMaskAddShuffle {F : Type}
    (K : TapField.BinaryField F) (a b c d : F) :
    K.add (K.add a b) (K.add c d) =
      K.add (K.add a c) (K.add b d) := by
  calc
    K.add (K.add a b) (K.add c d) =
        K.add a (K.add b (K.add c d)) :=
      K.add_assoc a b (K.add c d)
    _ = K.add a (K.add c (K.add b d)) := by
      rw [← K.add_assoc b c d,
        K.add_comm b c, K.add_assoc c b d]
    _ = K.add (K.add a c) (K.add b d) :=
      (K.add_assoc a c (K.add b d)).symm

/-- Polynomial evaluation respects the literal Nat.xor
encoding of characteristic-two addition in every field.
Consumer: PrimitiveFeedbackMask, PrimitiveRecurrenceBridge. -/
theorem tapMaskPolyEvalAdd {F : Type}
    (K : TapField.BinaryField F) (a b : Nat) (x : F) :
    tapMaskPolyEval K (tapPolyAdd a b) x =
      K.add (tapMaskPolyEval K a x)
        (tapMaskPolyEval K b x) := by
  change
    tapMaskPolyEval K (a ^^^ b) x =
      K.add (tapMaskPolyEval K a x)
        (tapMaskPolyEval K b x)
  have hmain :
      ∀ n : Nat, ∀ a b : Nat, a + b = n →
        tapMaskPolyEval K (a ^^^ b) x =
          K.add (tapMaskPolyEval K a x)
            (tapMaskPolyEval K b x) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro a b hsum
        by_cases hzero : n = 0
        · have ha : a = 0 := by omega
          have hb : b = 0 := by omega
          subst a
          subst b
          rw [Nat.xor_self, tapMaskPolyEvalZero]
          exact (K.zero_add K.zero).symm
        · have halim : a / 2 ≤ a := Nat.div_le_self a 2
          have hblim : b / 2 ≤ b := Nat.div_le_self b 2
          have hdecrease : a / 2 + b / 2 < n := by
            by_cases ha : a = 0
            · have hbpos : 0 < b := by omega
              have hbsmall := Nat.div_lt_self hbpos
                (by decide : 1 < 2)
              omega
            · have hasmall := Nat.div_lt_self
                (Nat.pos_of_ne_zero ha) (by decide : 1 < 2)
              omega
          have hrec :=
            ih (a / 2 + b / 2) hdecrease
              (a / 2) (b / 2) rfl
          rw [tapMaskPolyEvalStep K (a ^^^ b) x,
            tapMaskPolyEvalStep K a x,
            tapMaskPolyEvalStep K b x]
          have hquot :
              (a ^^^ b) / 2 =
                a / 2 ^^^ b / 2 :=
            Nat.xor_div_two
          rw [hquot, hrec]
          rw [← tapMaskParityAdd K a b,
            K.left_distrib]
          exact
            (tapMaskAddShuffle K
              (if a % 2 = 1 then K.one else K.zero)
              (K.mul x (tapMaskPolyEval K (a / 2) x))
              (if b % 2 = 1 then K.one else K.zero)
              (K.mul x (tapMaskPolyEval K (b / 2) x))).symm
  exact hmain (a + b) a b rfl


/-- Reassociating two commuting quotient-field factors.
Consumer: PrimitiveRecurrenceBridge, polynomial evaluation product. -/
private theorem tapMaskMulShuffle {F : Type}
    (K : TapField.BinaryField F) (a x b : F) :
    K.mul (K.mul x a) b = K.mul a (K.mul x b) := by
  calc
    K.mul (K.mul x a) b =
        K.mul x (K.mul a b) := K.mul_assoc x a b
    _ = K.mul (K.mul a b) x := K.mul_comm x _
    _ = K.mul a (K.mul b x) := K.mul_assoc a b x
    _ = K.mul a (K.mul x b) := by rw [K.mul_comm b x]

/-- Polynomial evaluation respects the literal carry-less
binary-polynomial multiplication, proved by induction on
the source's actual second-operand bit-scanning recurrence.
Consumer: PrimitiveFeedbackMask, PrimitiveRecurrenceBridge. -/
theorem tapMaskPolyEvalMul {F : Type}
    (K : TapField.BinaryField F) (a b : Nat) (x : F) :
    tapMaskPolyEval K (tapPolyMul a b) x =
      K.mul (tapMaskPolyEval K a x)
        (tapMaskPolyEval K b x) := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
      by_cases hzero : b = 0
      · subst b
        rw [tapPolyMulZeroRight, tapMaskPolyEvalZero]
        exact (TapField.BinaryField.mul_zero K
          (tapMaskPolyEval K a x)).symm
      · have hsmall : b / 2 < b :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hzero)
            (by decide : 1 < 2)
        have hbit :
            tapMaskPolyEval K (if b % 2 = 1 then a else 0) x =
              K.mul (tapMaskPolyEval K a x)
                (if b % 2 = 1 then K.one else K.zero) := by
          by_cases hodd : b % 2 = 1
          · simp only [if_pos hodd]
            exact (TapField.BinaryField.mul_one K
              (tapMaskPolyEval K a x)).symm
          · simp only [if_neg hodd]
            rw [tapMaskPolyEvalZero,
              TapField.BinaryField.mul_zero]
        calc
          tapMaskPolyEval K (tapPolyMul a b) x =
              K.add
                (tapMaskPolyEval K
                  (if b % 2 = 1 then a else 0) x)
                (tapMaskPolyEval K
                  (tapPolyMul (2 * a) (b / 2)) x) := by
            rw [tapPolyMulStep a b]
            exact tapMaskPolyEvalAdd K
              (if b % 2 = 1 then a else 0)
              (tapPolyMul (2 * a) (b / 2)) x
          _ = K.add
                (K.mul (tapMaskPolyEval K a x)
                  (if b % 2 = 1 then K.one else K.zero))
                (K.mul (tapMaskPolyEval K (2 * a) x)
                  (tapMaskPolyEval K (b / 2) x)) := by
            rw [hbit, ih (b / 2) hsmall (2 * a)]
          _ = K.add
                (K.mul (tapMaskPolyEval K a x)
                  (if b % 2 = 1 then K.one else K.zero))
                (K.mul (tapMaskPolyEval K a x)
                  (K.mul x (tapMaskPolyEval K (b / 2) x))) := by
            rw [tapMaskPolyEvalDouble]
            exact congrArg
              (fun z : F =>
                K.add
                  (K.mul (tapMaskPolyEval K a x)
                    (if b % 2 = 1 then K.one else K.zero))
                  z)
              (tapMaskMulShuffle K
                (tapMaskPolyEval K a x) x
                (tapMaskPolyEval K (b / 2) x))
          _ = K.mul (tapMaskPolyEval K a x)
                (K.add (if b % 2 = 1 then K.one else K.zero)
                  (K.mul x (tapMaskPolyEval K (b / 2) x))) :=
            (K.left_distrib _ _ _).symm
          _ = K.mul (tapMaskPolyEval K a x)
                (tapMaskPolyEval K b x) := by
            rw [tapMaskPolyEvalStep K b x]


/-- The low bit and the doubled quotient reconstruct the
exact binary polynomial mask by XOR, with no addition carries.
Consumer: PrimitiveFeedbackMask, quotient evaluation. -/
theorem tapMaskPolyBitDecomposition (a : Nat) :
    tapPolyAdd (if a % 2 = 1 then 1 else 0)
      (tapPolyMul 2 (a / 2)) = a := by
  have hbit :
      (if a % 2 = 1 then 1 else 0) = a % 2 := by
    rcases Nat.mod_two_eq_zero_or_one a with hz | hone
    · simp [hz]
    · simp [hone]
  have hdouble : tapPolyMul 2 (a / 2) = 2 * (a / 2) := by
    calc
      tapPolyMul 2 (a / 2) =
          tapPolyMul (2 * 1) (a / 2) := by simp
      _ = 2 * tapPolyMul 1 (a / 2) :=
        tapPolyMulDoubleLeft 1 (a / 2)
      _ = 2 * (a / 2) := by rw [tapPolyMulOneLeft]
  change
    (if a % 2 = 1 then 1 else 0) ^^^
      tapPolyMul 2 (a / 2) = a
  rw [hbit, hdouble]
  have hquot :
      ((a % 2) ^^^ (2 * (a / 2))) / 2 = a / 2 := by
    rw [Nat.xor_div_two]
    have hlow : (a % 2) / 2 = 0 := by
      have hm := Nat.mod_lt a (by decide : 0 < 2)
      omega
    have hhigh : (2 * (a / 2)) / 2 = a / 2 := by omega
    rw [hlow, hhigh, Nat.zero_xor]
  have hmod :
      ((a % 2) ^^^ (2 * (a / 2))) % 2 = a % 2 := by
    change
      ((a % 2) ^^^ (2 * (a / 2))) % 2 ^ 1 = a % 2
    rw [Nat.xor_mod_two_pow]
    have hlow : (a % 2) % 2 = a % 2 := Nat.mod_mod a 2
    have hhigh : (2 * (a / 2)) % 2 = 0 := by omega
    rw [hlow, hhigh, Nat.xor_zero]
  calc
    (a % 2) ^^^ (2 * (a / 2)) =
        (((a % 2) ^^^ (2 * (a / 2))) % 2) +
          2 * (((a % 2) ^^^ (2 * (a / 2))) / 2) :=
      (Nat.mod_add_div _ 2).symm
    _ = a % 2 + 2 * (a / 2) := by rw [hmod, hquot]
    _ = a := Nat.mod_add_div a 2

/-- The evaluation of a binary mask is the unique
characteristic-two ring-homomorphic extension of the unit
and a chosen image x of the bit-mask polynomial X.
Consumer: PrimitiveFeedbackMask, PrimitiveRecurrenceBridge. -/
theorem tapMaskPolyEvalOfHom {F : Type}
    (K : TapField.BinaryField F)
    (q : Nat → F) (x : F)
    (hzero : q 0 = K.zero)
    (hone : q 1 = K.one)
    (hadd : ∀ a b : Nat,
      q (tapPolyAdd a b) = K.add (q a) (q b))
    (hmul : ∀ a b : Nat,
      q (tapPolyMul a b) = K.mul (q a) (q b))
    (hx : q 2 = x)
    (a : Nat) :
    tapMaskPolyEval K a x = q a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
      by_cases hz : a = 0
      · subst a
        rw [tapMaskPolyEvalZero, hzero]
      · have hsmall : a / 2 < a :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hz)
            (by decide : 1 < 2)
        have hrec := ih (a / 2) hsmall
        have hbit :
            (if a % 2 = 1 then K.one else K.zero) =
              q (if a % 2 = 1 then 1 else 0) := by
          by_cases hodd : a % 2 = 1
          · simp only [if_pos hodd]
            exact hone.symm
          · simp only [if_neg hodd]
            exact hzero.symm
        calc
          tapMaskPolyEval K a x =
              K.add (if a % 2 = 1 then K.one else K.zero)
                (K.mul x (tapMaskPolyEval K (a / 2) x)) :=
            tapMaskPolyEvalStep K a x
          _ = K.add (q (if a % 2 = 1 then 1 else 0))
                (K.mul (q 2) (q (a / 2))) := by
            rw [hbit, hrec, hx]
          _ = K.add (q (if a % 2 = 1 then 1 else 0))
                (q (tapPolyMul 2 (a / 2))) := by
            rw [hmul 2 (a / 2)]
          _ = q
                (tapPolyAdd
                  (if a % 2 = 1 then 1 else 0)
                  (tapPolyMul 2 (a / 2))) :=
            (hadd _ _).symm
          _ = q a := by rw [tapMaskPolyBitDecomposition]

/-- Reduction commutes with polynomial XOR at the level
of actual quotient carrier values.
Consumer: PrimitiveFeedbackMask, evaluation at residue X. -/
theorem tapResidueOfMaskAdd (d f : Nat)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (a b : Nat) :
    tapResidueOfMask d f hlog hf (tapPolyAdd a b) =
      tapResidueAdd d
        (tapResidueOfMask d f hlog hf a)
        (tapResidueOfMask d f hlog hf b) := by
  have hfzero : f ≠ 0 := by
    have htwo := hf.1
    omega
  apply Subtype.ext
  change
    tapPolyRem (tapPolyAdd a b) f =
      tapPolyAdd (tapPolyRem a f) (tapPolyRem b f)
  exact tapPolyRemAdd a b f hfzero

/-- Reduction commutes with literal polynomial multiplication,
even when the operands are not themselves reduced.
Consumer: PrimitiveFeedbackMask, quotient evaluation. -/
theorem tapResidueOfMaskMul (d f : Nat)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (a b : Nat) :
    tapResidueOfMask d f hlog hf (tapPolyMul a b) =
      tapResidueMul d f hlog hf
        (tapResidueOfMask d f hlog hf a)
        (tapResidueOfMask d f hlog hf b) := by
  have hfzero : f ≠ 0 := by
    have htwo := hf.1
    omega
  apply Subtype.ext
  change
    tapPolyRem (tapPolyMul a b) f =
      tapPolyRem
        (tapPolyMul (tapPolyRem a f) (tapPolyRem b f)) f
  calc
    tapPolyRem (tapPolyMul a b) f =
        tapPolyRem (tapPolyMul (tapPolyRem a f) b) f :=
      (tapPolyRemMulLeft a b f hfzero).symm
    _ = tapPolyRem
          (tapPolyMul (tapPolyRem a f) (tapPolyRem b f)) f :=
      (tapPolyRemMulRight (tapPolyRem a f) b f hfzero).symm


/-- Evaluate a literal binary-polynomial mask in its
irreducible quotient at the residue of X: the result is
exactly the original mask reduced modulo f.
Consumer: PrimitiveFeedbackMask and PrimitiveRecurrenceBridge. -/
theorem tapMaskFieldEval (d f : Nat)
    (hd : 2 ≤ d)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (a : Nat) :
    tapMaskPolyEval
      (tapMaskField d f (by omega : 1 ≤ d) hlog hf)
      a (tapResidueX d hd) =
    tapResidueOfMask d f hlog hf a := by
  apply tapMaskPolyEvalOfHom
    (tapMaskField d f (by omega : 1 ≤ d) hlog hf)
    (fun p => tapResidueOfMask d f hlog hf p)
    (tapResidueX d hd)
  · apply Subtype.ext
    change tapPolyRem 0 f = 0
    exact tapPolyRemOfBelow d f 0 hlog hf
      (Nat.two_pow_pos d)
  · apply Subtype.ext
    change tapPolyRem 1 f = 1
    exact tapPolyRemOfBelow d f 1 hlog hf
      (Nat.one_lt_two_pow (by omega : d ≠ 0))
  · intro a b
    exact tapResidueOfMaskAdd d f hlog hf a b
  · intro a b
    exact tapResidueOfMaskMul d f hlog hf a b
  · apply Subtype.ext
    change tapPolyRem 2 f = 2
    exact tapPolyRemOfBelow d f 2 hlog hf
      (tapResidueX d hd).property

/-- Every quotient residue is a polynomial in the
distinguished class X, and evaluation returns the residue
itself rather than an arbitrary equivalent representative.
Consumer: PrimitiveFeedbackMask, PrimitiveRecurrenceBridge. -/
theorem tapMaskPolyEvalOfResidue (d f : Nat)
    (hd : 2 ≤ d)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (a : TapResidue d) :
    tapMaskPolyEval
      (tapMaskField d f (by omega : 1 ≤ d) hlog hf)
      a.val (tapResidueX d hd) = a := by
  rw [tapMaskFieldEval d f hd hlog hf a.val]
  apply Subtype.ext
  change tapPolyRem a.val f = a.val
  exact tapPolyRemOfBelow d f a.val hlog hf a.property

/-- Exact quotient-kernel characterization: f divides p
if and only if the reduced representative is the zero of
the constructed binary field.
Consumer: PrimitiveIrreducibleExistence,
PrimitiveFeedbackMask and PrimitiveRecurrenceBridge. -/
theorem tapMaskFieldDvdIffZero (d f : Nat)
    (hd : 1 ≤ d)
    (hlog : Nat.log2 f = d) (hf : TapIrreducible f)
    (p : Nat) :
    tapPolyDvd f p ↔
      tapResidueOfMask d f hlog hf p =
        (tapMaskField d f hd hlog hf).zero := by
  have hfzero : f ≠ 0 := by
    have hh := hf.1
    omega
  constructor
  · intro hdvd
    have hrem := (tapPolyDvdIffRemZero p f hfzero).1 hdvd
    apply Subtype.ext
    exact hrem
  · intro hzero
    have hrem := congrArg Subtype.val hzero
    exact (tapPolyDvdIffRemZero p f hfzero).2 hrem

end L3

#print axioms L3.tapMaskField
#print axioms L3.tapMaskPolyEval
#print axioms L3.tapMaskPolyEvalZero
#print axioms L3.tapMaskPolyEvalOne
#print axioms L3.tapMaskPolyEvalAdd
#print axioms L3.tapMaskPolyEvalMul
#print axioms L3.tapMaskFieldEval
#print axioms L3.tapMaskPolyEvalOfResidue

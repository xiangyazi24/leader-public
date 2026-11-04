import Leader.L3.Primitive.FieldGenerator
import Leader.L3.Primitive.IrreducibleExistence

namespace L3

open Classical
open TapField

set_option autoImplicit false
set_option Elab.async false

variable {F : Type}

/-- The polynomial bit mask for X evaluates to its chosen image.
Consumer: PrimitiveFeedbackMask and PrimitiveRecurrenceBridge. -/
private theorem tapGeneratorEvalX (K : TapField.BinaryField F) (g : F) :
    tapMaskPolyEval K 2 g = g := by
  rw [tapMaskPolyEvalStep K 2 g]
  change K.add K.zero (K.mul g (tapMaskPolyEval K 1 g)) = g
  rw [tapMaskPolyEvalOne, TapField.BinaryField.mul_one, K.zero_add]

/-- Each monomial X^k evaluates to the corresponding field power.
Consumer: binaryGeneratorSpanClosure, tapPrimitiveFeedbackOrder. -/
private theorem tapGeneratorEvalMonomial
    (K : TapField.BinaryField F) (g : F) (k : Nat) :
    tapMaskPolyEval K (2 ^ k) g = K.pow g k := by
  induction k with
  | zero =>
      change tapMaskPolyEval K 1 g = K.one
      exact tapMaskPolyEvalOne K g
  | succ k ih =>
      have hmask : tapPolyMul (2 ^ k) 2 = 2 ^ (k + 1) := by
        simpa only [Nat.pow_one] using tapPolyPowerOfX k 1
      calc
        tapMaskPolyEval K (2 ^ (k + 1)) g =
            tapMaskPolyEval K (tapPolyMul (2 ^ k) 2) g := by
          rw [hmask]
        _ = K.mul (tapMaskPolyEval K (2 ^ k) g)
              (tapMaskPolyEval K 2 g) :=
          tapMaskPolyEvalMul K (2 ^ k) 2 g
        _ = K.mul (K.pow g k) g := by
          rw [ih, tapGeneratorEvalX]
        _ = K.pow g (k + 1) := rfl

/-- Dividing a polynomial by a vanishing polynomial does not
change its evaluation. Consumer: binaryGeneratorSpanClosure
and tapPrimitiveFeedbackOrder. -/
private theorem tapGeneratorEvalRemAtRoot
    (K : TapField.BinaryField F) (g : F) (f p : Nat)
    (hf : f ≠ 0)
    (hroot : tapMaskPolyEval K f g = K.zero) :
    tapMaskPolyEval K (tapPolyRem p f) g =
      tapMaskPolyEval K p g := by
  obtain ⟨q, hdiv⟩ := tapPolyDivExists p f hf
  have hh := congrArg (fun z : Nat => tapMaskPolyEval K z g) hdiv
  rw [tapMaskPolyEvalAdd, tapMaskPolyEvalMul, hroot,
    TapField.BinaryField.mul_zero, K.zero_add] at hh
  exact hh.symm

/-- The literal remainder is smaller than the leading bit of
its modulus. Consumer: binaryGeneratorSpanClosure and
tapPrimitiveFeedbackOrder. -/
private theorem tapGeneratorRemBelow (p f d : Nat)
    (hf : f ≠ 0) (hlog : Nat.log2 f = d) :
    tapPolyRem p f < 2 ^ d := by
  rcases tapPolyRemLog p f hf with hz | hlt
  · rw [hz]
    exact Nat.two_pow_pos d
  · by_cases hzero : tapPolyRem p f = 0
    · rw [hzero]
      exact Nat.two_pow_pos d
    · apply (Nat.log2_lt hzero).1
      rw [← hlog]
      exact hlt

/-- Strict monotonicity for the binary polynomial-mask range.
Consumers: binaryGeneratorEvalInjective and tapPrimitiveFeedbackMask. -/
private theorem tapGeneratorPowerRangeStrict (a b : Nat) (h : a < b) :
    2 ^ a < 2 ^ b := by
  have hstep : 2 ^ a < 2 ^ (a + 1) := by
    rw [Nat.pow_succ]
    have hpos := Nat.two_pow_pos a
    omega
  have hmon : 2 ^ (a + 1) ≤ 2 ^ b :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  exact Nat.lt_of_lt_of_le hstep hmon

/-- A polynomial relation of positive degree makes every
generator power representable by a lower-degree mask, using
the literal Euclidean remainder. Consumer: PrimitiveFeedbackMask
and PrimitiveRecurrenceBridge. -/
theorem binaryGeneratorSpanClosure
    (K : TapField.BinaryField F) (E : TapField.Enumeration F)
    (t : Nat) (ht : 1 ≤ t)
    (hlen : E.elems.length = 2 ^ t)
    (g : F) (hg : TapField.HasExactOrder K g (2 ^ t - 1))
    (c d : Nat) (hc : c ≠ 0)
    (hlog : Nat.log2 c = d) (hd : 1 ≤ d)
    (hroot : tapMaskPolyEval K c g = K.zero)
    (k : Nat) :
    ∃ a : Nat, a < 2 ^ d ∧
      K.pow g k = tapMaskPolyEval K a g := by
  refine ⟨tapPolyRem (2 ^ k) c, ?_, ?_⟩
  · exact tapGeneratorRemBelow (2 ^ k) c d hc hlog
  · calc
      K.pow g k = tapMaskPolyEval K (2 ^ k) g :=
        (tapGeneratorEvalMonomial K g k).symm
      _ = tapMaskPolyEval K (tapPolyRem (2 ^ k) c) g :=
        (tapGeneratorEvalRemAtRoot K g c (2 ^ k) hc hroot).symm

/-- A normalized nonzero mask of degree zero is the constant
one polynomial. Consumer: binaryGeneratorEvalInjective
and tapPrimitiveFeedbackIrreducible. -/
private theorem tapGeneratorDegreeZero (a : Nat)
    (ha : a ≠ 0) (hlog : Nat.log2 a = 0) : a = 1 := by
  have hbounds := tapMaskLog a ha
  rw [hlog] at hbounds
  change (1 : Nat) ≤ a ∧ a < 2 at hbounds
  omega

/-- A nonunit nonzero polynomial has positive degree.
Consumer: tapPrimitiveFeedbackIrreducible. -/
private theorem tapGeneratorNonunitDegree (a : Nat)
    (ha : a ≠ 0) (hone : a ≠ 1) :
    0 < Nat.log2 a := by
  by_cases hzero : Nat.log2 a = 0
  · exact False.elim (hone (tapGeneratorDegreeZero a ha hzero))
  · omega

/-- Evaluating the xor of two masks at equal field values gives
zero. Consumer: binaryGeneratorEvalInjective. -/
private theorem tapGeneratorEvalXorZero
    (K : TapField.BinaryField F) (g : F) (a b : Nat)
    (heq : tapMaskPolyEval K a g = tapMaskPolyEval K b g) :
    tapMaskPolyEval K (tapPolyAdd a b) g = K.zero := by
  rw [tapMaskPolyEvalAdd, heq, K.add_self]

/-- A generator of exact order 2^t-1 has no nontrivial
binary-polynomial relation of degree < t.
Consumer: PrimitiveFeedbackMask, PrimitiveRecurrenceBridge. -/
theorem binaryGeneratorEvalInjective
    (K : TapField.BinaryField F) (E : TapField.Enumeration F)
    (t : Nat) (ht : 1 ≤ t)
    (hlen : E.elems.length = 2 ^ t)
    (g : F) (hg : TapField.HasExactOrder K g (2 ^ t - 1))
    (a a' : Nat) (ha : a < 2 ^ t) (ha' : a' < 2 ^ t)
    (heq : tapMaskPolyEval K a g = tapMaskPolyEval K a' g) :
    a = a' := by
  by_cases hsame : a = a'
  · exact hsame
  · have hvnonzero : tapPolyAdd a a' ≠ 0 := by
      intro hz
      exact hsame ((tapPolyAddEqZeroIff a a').1 hz)
    have hvbelow : tapPolyAdd a a' < 2 ^ t :=
      tapPolyAddBelow a a' t ha ha'
    have hvroot : tapMaskPolyEval K (tapPolyAdd a a') g = K.zero :=
      tapGeneratorEvalXorZero K g a a' heq
    have hdlt : Nat.log2 (tapPolyAdd a a') < t :=
      (Nat.log2_lt hvnonzero).2 hvbelow
    by_cases hd0 : Nat.log2 (tapPolyAdd a a') = 0
    · have hone : tapPolyAdd a a' = 1 :=
        tapGeneratorDegreeZero (tapPolyAdd a a') hvnonzero hd0
      rw [hone, tapMaskPolyEvalOne] at hvroot
      exact False.elim (K.one_ne_zero hvroot)
    · have hdpos : 1 ≤ Nat.log2 (tapPolyAdd a a') := by omega
      have hgE : TapField.HasExactOrder K g (E.elems.length - 1) := by
        rw [hlen]
        exact hg
      have hcover : ∀ z : F, z ∈ E.elems →
          z ∈ (List.range (2 ^ Nat.log2 (tapPolyAdd a a'))).map
            (fun j : Nat => tapMaskPolyEval K j g) := by
        intro z hz
        by_cases hzero : z = K.zero
        · subst z
          apply List.mem_map.mpr
          refine ⟨0, (List.mem_range).2 (Nat.two_pow_pos _), ?_⟩
          exact tapMaskPolyEvalZero K g
        · obtain ⟨k, hk, hpow⟩ :=
            TapField.generatorPowersExhaust K E g hgE z hzero
          obtain ⟨j, hj, heval⟩ :=
            binaryGeneratorSpanClosure K E t ht hlen g hg
              (tapPolyAdd a a')
              (Nat.log2 (tapPolyAdd a a'))
              hvnonzero rfl hdpos hvroot k
          apply List.mem_map.mpr
          exact ⟨j, (List.mem_range).2 hj, heval.symm.trans hpow⟩
      have hcard : E.elems.length ≤
          ((List.range (2 ^ Nat.log2 (tapPolyAdd a a'))).map
            (fun j : Nat => tapMaskPolyEval K j g)).length :=
        List.Nodup.length_le_of_subset E.nodup hcover
      simp only [List.length_map, List.length_range] at hcard
      rw [hlen] at hcard
      have hsmall :
          2 ^ Nat.log2 (tapPolyAdd a a') < 2 ^ t :=
        tapGeneratorPowerRangeStrict _ _ hdlt
      exact False.elim ((Nat.not_le_of_gt hsmall) hcard)

/-- Evaluation is injective on a list of distinct masks in
the complete degree-t range.
Consumer: binaryGeneratorEvalSurjective and PrimitiveFeedbackMask. -/
private theorem tapGeneratorEvalRangeNodup
    (K : TapField.BinaryField F) (E : TapField.Enumeration F)
    (t : Nat) (ht : 1 ≤ t)
    (hlen : E.elems.length = 2 ^ t)
    (g : F) (hg : TapField.HasExactOrder K g (2 ^ t - 1)) :
    ((List.range (2 ^ t)).map
      (fun j : Nat => tapMaskPolyEval K j g)).Nodup := by
  have hbase : (List.range (2 ^ t)).Pairwise
      (fun a b : Nat => a ≠ b) :=
    List.nodup_range
  apply (List.pairwise_map).2
  apply hbase.imp_of_mem
  intro a b ha hb hne heq
  exact hne (binaryGeneratorEvalInjective
    K E t ht hlen g hg a b
    ((List.mem_range).1 ha) ((List.mem_range).1 hb) heq)

/-- An injective map on all 2^t polynomial masks exhausts the
enumerated field of the same size. Consumer: PrimitiveFeedbackMask
and PrimitiveRecurrenceBridge. -/
theorem binaryGeneratorEvalSurjective
    (K : TapField.BinaryField F) (E : TapField.Enumeration F)
    (t : Nat) (ht : 1 ≤ t)
    (hlen : E.elems.length = 2 ^ t)
    (g : F) (hg : TapField.HasExactOrder K g (2 ^ t - 1))
    (z : F) :
    ∃ a : Nat, a < 2 ^ t ∧ tapMaskPolyEval K a g = z := by
  by_cases hmem : z ∈ (List.range (2 ^ t)).map
      (fun j : Nat => tapMaskPolyEval K j g)
  · obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
    exact ⟨a, (List.mem_range).1 ha, heq⟩
  · have hnodup :
        (z :: (List.range (2 ^ t)).map
          (fun j : Nat => tapMaskPolyEval K j g)).Nodup :=
      List.nodup_cons.mpr
        ⟨hmem, tapGeneratorEvalRangeNodup K E t ht hlen g hg⟩
    have hsubset : ∀ v : F,
        v ∈ (z :: (List.range (2 ^ t)).map
          (fun j : Nat => tapMaskPolyEval K j g)) →
        v ∈ E.elems := by
      intro v _
      exact E.complete v
    have hbound := List.Nodup.length_le_of_subset hnodup hsubset
    simp only [List.length_cons, List.length_map, List.length_range] at hbound
    rw [hlen] at hbound
    omega

/-- Adding a fresh leading bit to a lower-degree mask is
numerically the same as xor. Consumer: tapPrimitiveFeedbackMask,
tapPrimitiveFeedbackIrreducible. -/
private theorem tapGeneratorTopBit (t b : Nat) (hb : b < 2 ^ t) :
    tapPolyAdd (2 ^ t) b = 2 ^ t + b := by
  have hbdiv : b / 2 ^ t = 0 :=
    Nat.div_eq_zero_iff.mpr (Or.inr hb)
  have hdiv : ((2 ^ t) ^^^ b) / 2 ^ t = 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self (Nat.two_pow_pos t), hbdiv]
    rfl
  have hmod : ((2 ^ t) ^^^ b) % 2 ^ t = b := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self,
      Nat.mod_eq_of_lt hb, Nat.zero_xor]
  change (2 ^ t) ^^^ b = 2 ^ t + b
  calc
    (2 ^ t) ^^^ b =
        (((2 ^ t) ^^^ b) % 2 ^ t) +
          (2 ^ t) * (((2 ^ t) ^^^ b) / 2 ^ t) :=
      (Nat.mod_add_div _ _).symm
    _ = b + 2 ^ t := by rw [hmod, hdiv]; omega
    _ = 2 ^ t + b := Nat.add_comm _ _

/-- The defining degree bound gives the exact degree of X^t+b.
Consumer: tapPrimitiveFeedbackIrreducible and
tapPrimitiveFeedbackOrder. -/
private theorem tapGeneratorFeedbackDegree (t b : Nat)
    (hb : b < 2 ^ t) :
    Nat.log2 (2 ^ t + b) = t := by
  have hupper : 2 ^ t + b < 2 ^ (t + 1) := by
    calc
      2 ^ t + b < 2 ^ t + 2 ^ t :=
        Nat.add_lt_add_left hb _
      _ = 2 ^ (t + 1) := by
        rw [Nat.pow_succ]
        omega
  exact tapMaskLogOfBounds (2 ^ t + b) t (by omega) hupper

/-- The selected coefficient representation must have odd
constant term. Consumer: PrimitiveRecurrenceBridge and
PrimitiveTapSelection. -/
theorem tapPrimitiveFeedbackMask
    (K : TapField.BinaryField F) (E : TapField.Enumeration F)
    (t : Nat) (ht : 2 ≤ t)
    (hlen : E.elems.length = 2 ^ t)
    (g : F) (hg : TapField.HasExactOrder K g (2 ^ t - 1)) :
    ∃ b : Nat, b < 2 ^ t ∧ b % 2 = 1 ∧
      K.pow g t = tapMaskPolyEval K b g := by
  obtain ⟨b, hb, heval⟩ :=
    binaryGeneratorEvalSurjective K E t
      (by omega) hlen g hg (K.pow g t)
  refine ⟨b, hb, ?_, heval.symm⟩
  rcases Nat.mod_two_eq_zero_or_one b with hzero | hone
  · have heven : b = 2 * (b / 2) := by
      have hdiv := Nat.mod_add_div b 2
      rw [hzero] at hdiv
      omega
    have htprev : t - 1 + 1 = t := Nat.sub_add_cancel (by omega : 1 ≤ t)
    have htop : 2 ^ (t - 1) < 2 ^ t :=
      tapGeneratorPowerRangeStrict _ _ (by omega)
    have hmaskBound : b / 2 < 2 ^ (t - 1) := by
      have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
        calc
          2 ^ t = 2 ^ (t - 1 + 1) := by rw [htprev]
          _ = 2 * 2 ^ (t - 1) := by
            rw [Nat.pow_succ, Nat.mul_comm]
      have hq : 2 * (b / 2) < 2 * 2 ^ (t - 1) := by
        rw [← heven, ← hpow]
        exact hb
      omega
    have hglast : K.pow g (t - 1) =
        tapMaskPolyEval K (b / 2) g := by
      apply K.mul_left_cancel g _ _ hg.1
      calc
        K.mul g (K.pow g (t - 1)) =
            K.pow g (t - 1 + 1) := by
          change K.mul g (K.pow g (t - 1)) =
            K.mul (K.pow g (t - 1)) g
          exact K.mul_comm _ _
        _ = K.pow g t := by rw [htprev]
        _ = tapMaskPolyEval K b g := heval.symm
        _ = tapMaskPolyEval K (2 * (b / 2)) g :=
          congrArg (fun z : Nat => tapMaskPolyEval K z g) heven
        _ = K.mul g (tapMaskPolyEval K (b / 2) g) :=
          tapMaskPolyEvalDouble K (b / 2) g
    have hxorBound : tapPolyAdd (2 ^ (t - 1)) (b / 2) < 2 ^ t :=
      tapPolyAddBelow _ _ t htop
        (Nat.lt_trans hmaskBound htop)
    have hxorNonzero : tapPolyAdd (2 ^ (t - 1)) (b / 2) ≠ 0 := by
      intro hz
      have heq := (tapPolyAddEqZeroIff
        (2 ^ (t - 1)) (b / 2)).1 hz
      omega
    have hxorEval :
        tapMaskPolyEval K (tapPolyAdd (2 ^ (t - 1)) (b / 2)) g =
          K.zero := by
      rw [tapMaskPolyEvalAdd, tapGeneratorEvalMonomial, hglast,
        K.add_self]
    have hzeroEq :
        tapMaskPolyEval K (tapPolyAdd (2 ^ (t - 1)) (b / 2)) g =
          tapMaskPolyEval K 0 g := by
      rw [tapMaskPolyEvalZero]
      exact hxorEval
    have hbad := binaryGeneratorEvalInjective K E t
      (by omega) hlen g hg
      (tapPolyAdd (2 ^ (t - 1)) (b / 2)) 0
      hxorBound (Nat.two_pow_pos t) hzeroEq
    exact False.elim (hxorNonzero hbad)
  · exact hone

/-- Feedback polynomial vanishes at its selected generator
and is irreducible: a proper factor would give a forbidden
lower-degree relation. Consumer: PrimitiveRecurrenceBridge
and PrimitiveTapSelection. -/
theorem tapPrimitiveFeedbackIrreducible
    (K : TapField.BinaryField F) (E : TapField.Enumeration F)
    (t : Nat) (ht : 2 ≤ t)
    (hlen : E.elems.length = 2 ^ t)
    (g : F) (hg : TapField.HasExactOrder K g (2 ^ t - 1))
    (b : Nat) (hb : b < 2 ^ t)
    (hcoeff : K.pow g t = tapMaskPolyEval K b g) :
    TapIrreducible (2 ^ t + b) ∧
      tapMaskPolyEval K (2 ^ t + b) g = K.zero := by
  have heval : tapMaskPolyEval K (2 ^ t + b) g = K.zero := by
    rw [← tapGeneratorTopBit t b hb, tapMaskPolyEvalAdd,
      tapGeneratorEvalMonomial, hcoeff, K.add_self]
  have hlog : Nat.log2 (2 ^ t + b) = t :=
    tapGeneratorFeedbackDegree t b hb
  have hge : 2 ≤ 2 ^ t + b := by
    have hpow : 2 ≤ 2 ^ t := by
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
        (by omega : 1 ≤ t)
      simpa only [Nat.pow_one] using hp
    omega
  constructor
  · refine ⟨hge, ?_⟩
    intro a c hfactor
    by_cases honeA : a = 1
    · exact Or.inl honeA
    · by_cases honeC : c = 1
      · exact Or.inr honeC
      · have ha : a ≠ 0 := by
          intro hz
          rw [hz, tapPolyMulZeroLeft] at hfactor
          omega
        have hc : c ≠ 0 := by
          intro hz
          rw [hz, tapPolyMulZeroRight] at hfactor
          omega
        have hadeg : 0 < Nat.log2 a :=
          tapGeneratorNonunitDegree a ha honeA
        have hcdeg : 0 < Nat.log2 c :=
          tapGeneratorNonunitDegree c hc honeC
        have hprod := tapPolyMulLog a c ha hc
        rw [← hfactor, hlog] at hprod
        have haSmall : a < 2 ^ t :=
          (Nat.log2_lt ha).1 (by omega)
        have hcSmall : c < 2 ^ t :=
          (Nat.log2_lt hc).1 (by omega)
        have hprodZero :
            K.mul (tapMaskPolyEval K a g)
              (tapMaskPolyEval K c g) = K.zero := by
          calc
            K.mul (tapMaskPolyEval K a g) (tapMaskPolyEval K c g) =
                tapMaskPolyEval K (tapPolyMul a c) g :=
              (tapMaskPolyEvalMul K a c g).symm
            _ = tapMaskPolyEval K (2 ^ t + b) g := by rw [hfactor]
            _ = K.zero := heval
        rcases K.mul_eq_zero _ _ hprodZero with hza | hzc
        · have heq : a = 0 :=
            binaryGeneratorEvalInjective K E t
              (by omega) hlen g hg a 0 haSmall
              (Nat.two_pow_pos t) (by
                rw [tapMaskPolyEvalZero]
                exact hza)
          exact False.elim (ha heq)
        · have heq : c = 0 :=
            binaryGeneratorEvalInjective K E t
              (by omega) hlen g hg c 0 hcSmall
              (Nat.two_pow_pos t) (by
                rw [tapMaskPolyEvalZero]
                exact hzc)
          exact False.elim (hc heq)
  · exact heval

/-- The literal recurrence field modulus is nonzero.
Consumer: tapPrimitiveFeedbackOrder. -/
private theorem tapGeneratorFeedbackNonzero (t b : Nat) :
    2 ^ t + b ≠ 0 := by
  have hpos := Nat.two_pow_pos t
  omega

/-- The polynomial powers of X reduce to 1 exactly when the
selected generator has corresponding power 1.
Consumer: PrimitiveRecurrenceBridge and PrimitiveTapSelection. -/
theorem tapPrimitiveFeedbackOrder
    (K : TapField.BinaryField F) (E : TapField.Enumeration F)
    (t : Nat) (ht : 2 ≤ t)
    (hlen : E.elems.length = 2 ^ t)
    (g : F) (hg : TapField.HasExactOrder K g (2 ^ t - 1))
    (b : Nat) (hb : b < 2 ^ t)
    (hirr : TapIrreducible (2 ^ t + b))
    (hroot : tapMaskPolyEval K (2 ^ t + b) g = K.zero)
    (k : Nat) :
    tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) = 1 ↔
      K.pow g k = K.one := by
  have hlog : Nat.log2 (2 ^ t + b) = t :=
    tapGeneratorFeedbackDegree t b hb
  have hf : 2 ^ t + b ≠ 0 := tapGeneratorFeedbackNonzero t b
  have hremBelow : tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) < 2 ^ t :=
    tapGeneratorRemBelow _ _ _ hf hlog
  have honeBelow : (1 : Nat) < 2 ^ t := by
    exact Nat.one_lt_two_pow (by omega : t ≠ 0)
  have heval :
      tapMaskPolyEval K (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) g =
        K.pow g k := by
    calc
      tapMaskPolyEval K (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) g =
          tapMaskPolyEval K (tapPolyPow 2 k) g :=
        tapGeneratorEvalRemAtRoot K g _ _ hf hroot
      _ = tapMaskPolyEval K (2 ^ k) g := by
        rw [tapPolyPowTwoPow]
      _ = K.pow g k := tapGeneratorEvalMonomial K g k
  constructor
  · intro hrem
    have hh := heval
    rw [hrem, tapMaskPolyEvalOne] at hh
    exact hh.symm
  · intro hpow
    apply binaryGeneratorEvalInjective K E t
      (by omega) hlen g hg
      (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1
      hremBelow honeBelow
    calc
      tapMaskPolyEval K (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) g =
          K.pow g k := heval
      _ = K.one := hpow
      _ = tapMaskPolyEval K 1 g :=
        (tapMaskPolyEvalOne K g).symm

/-- An irreducible binary mask of degree t supports a primitive
feedback polynomial whose residue of X has exact order 2^t-1.
Consumer: PrimitiveRecurrenceBridge and PrimitiveTapSelection. -/
theorem tapPrimitiveMaskExists (t : Nat) (ht : 18 ≤ t) :
    ∃ b : Nat, b < 2 ^ t ∧ b % 2 = 1 ∧
      TapIrreducible (2 ^ t + b) ∧
      tapPolyRem (tapPolyPow 2 (2 ^ t - 1)) (2 ^ t + b) = 1 ∧
      ∀ k : Nat, 0 < k → k < 2 ^ t - 1 →
        tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1 := by
  obtain ⟨f, hflo, hfhi, hfIrr⟩ := tapLargeIrreducibleExists t ht
  have ht2 : 2 ≤ t := by omega
  have hlog : Nat.log2 f = t :=
    tapMaskLogOfBounds f t hflo hfhi
  have hlen : (tapMaskEnumeration t).elems.length = 2 ^ t :=
    tapMaskEnumerationLength t
  have hunitCount : 1 ≤ (tapMaskEnumeration t).elems.length - 1 := by
    rw [hlen]
    have hpow : 2 ≤ 2 ^ t := by
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2)
        (by omega : 1 ≤ t)
      simpa only [Nat.pow_one] using hh
    omega
  obtain ⟨g, hg0⟩ :=
    TapField.binaryFiniteFieldGenerator
      (tapMaskField t f (by omega : 1 ≤ t) hlog hfIrr)
      (tapMaskEnumeration t) hunitCount
  have hg : TapField.HasExactOrder
      (tapMaskField t f (by omega : 1 ≤ t) hlog hfIrr)
      g (2 ^ t - 1) := by
    simpa only [tapMaskEnumerationLength] using hg0
  obtain ⟨b, hb, hodd, hcoeff⟩ :=
    tapPrimitiveFeedbackMask
      (tapMaskField t f (by omega : 1 ≤ t) hlog hfIrr)
      (tapMaskEnumeration t) t ht2 hlen g hg
  obtain ⟨hnewIrr, hnewRoot⟩ :=
    tapPrimitiveFeedbackIrreducible
      (tapMaskField t f (by omega : 1 ≤ t) hlog hfIrr)
      (tapMaskEnumeration t) t ht2 hlen g hg b hb hcoeff
  have hfull : tapPolyRem (tapPolyPow 2 (2 ^ t - 1))
      (2 ^ t + b) = 1 := by
    apply (tapPrimitiveFeedbackOrder
      (tapMaskField t f (by omega : 1 ≤ t) hlog hfIrr)
      (tapMaskEnumeration t) t ht2 hlen g hg
      b hb hnewIrr hnewRoot (2 ^ t - 1)).2
    exact hg.2.2.1
  refine ⟨b, hb, hodd, hnewIrr, hfull, ?_⟩
  intro k hk hlt hbad
  have hpow : (tapMaskField t f (by omega : 1 ≤ t) hlog hfIrr).pow
      g k =
      (tapMaskField t f (by omega : 1 ≤ t) hlog hfIrr).one :=
    (tapPrimitiveFeedbackOrder
      (tapMaskField t f (by omega : 1 ≤ t) hlog hfIrr)
      (tapMaskEnumeration t) t ht2 hlen g hg b hb
      hnewIrr hnewRoot k).1 hbad
  have hdiv : 2 ^ t - 1 ∣ k :=
    TapField.orderDividesOfPow
      (tapMaskField t f (by omega : 1 ≤ t) hlog hfIrr)
      g (2 ^ t - 1) k hg hpow
  have hbound : 2 ^ t - 1 ≤ k := Nat.le_of_dvd hk hdiv
  omega

#print axioms binaryGeneratorEvalInjective
#print axioms tapPrimitiveFeedbackMask
#print axioms tapPrimitiveMaskExists

end L3

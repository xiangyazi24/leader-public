import Leader.L3.Primitive.MaskDivision

/-!
A complete Euclidean-gcd and Bezout interface for Nat bit-mask
polynomials. The literal tapPolyGcdFuel is the algorithm analyzed;
its fuel is bounded by the successive remainder degrees.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- A nonconstant mask without a factorization into two nonunits.
Consumer: PrimitiveMaskFactors and PrimitiveMaskQuotient. -/
def TapIrreducible (f : Nat) : Prop :=
  2 ≤ f ∧
    ∀ a c : Nat, f = tapPolyMul a c → a = 1 ∨ c = 1

/-- The literal GCD routine returns its first argument when its
second argument is zero.
Consumer: tapPolyGcdFuelInvariant. -/
private theorem tapPolyGcdFuelZero (a fuel : Nat) :
    tapPolyGcdFuel a 0 fuel = a := by
  cases fuel <;> rfl

/-- Euclid's zero-remainder endpoint has the full divisor and
Bezout certificates, not merely an arithmetic terminal value.
Consumer: tapPolyGcdFuelInvariant. -/
private theorem tapPolyGcdFuelZeroSpec (a fuel : Nat)
    (ha : a ≠ 0) :
    tapPolyGcdFuel a 0 fuel ≠ 0 ∧
      tapPolyDvd (tapPolyGcdFuel a 0 fuel) a ∧
      tapPolyDvd (tapPolyGcdFuel a 0 fuel) 0 ∧
      ∃ u v : Nat,
        tapPolyGcdFuel a 0 fuel =
          tapPolyAdd (tapPolyMul u a) (tapPolyMul v 0) := by
  rw [tapPolyGcdFuelZero]
  refine ⟨ha, tapPolyDvdRefl a, ?_, ?_⟩
  · exact ⟨0, (tapPolyMulZeroLeft a).symm⟩
  · refine ⟨1, 0, ?_⟩
    change a = tapPolyMul 1 a ^^^ tapPolyMul 0 0
    rw [tapPolyMulOneLeft, tapPolyMulZeroLeft, Nat.xor_zero]

/-- Multiplying a known divisible mask on the left preserves
divisibility. Consumer: the GCD invariant and PrimitiveMaskFactors. -/
private theorem tapPolyDvdMulLeft (d a q : Nat)
    (h : tapPolyDvd d a) :
    tapPolyDvd d (tapPolyMul q a) := by
  rw [tapPolyMulCommutative q a]
  exact tapPolyDvdMul d a q h

/-- Reversing the exact Euclidean XOR quotient equality gives
the residual polynomial as dividend plus quotient times divisor.
Consumer: tapPolyGcdFuelInvariant. -/
private theorem tapPolyRemFromDivision (a b q : Nat)
    (h : a = tapPolyAdd (tapPolyMul q b) (tapPolyRem a b)) :
    tapPolyRem a b = tapPolyAdd a (tapPolyMul q b) := by
  change a = tapPolyMul q b ^^^ tapPolyRem a b at h
  have hh :=
    congrArg (fun z : Nat => z ^^^ tapPolyMul q b) h
  change a ^^^ tapPolyMul q b =
    (tapPolyMul q b ^^^ tapPolyRem a b) ^^^
      tapPolyMul q b at hh
  rw [Nat.xor_comm (tapPolyMul q b) (tapPolyRem a b),
    Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hh
  change tapPolyRem a b = a ^^^ tapPolyMul q b
  exact hh.symm

/-- Transport a Bezout representation across one real Euclidean
division step. The characteristic-two subtraction is XOR.
Consumer: tapPolyGcdFuelInvariant. -/
private theorem tapPolyBezoutRemTransport
    (a b q u v d : Nat)
    (hrem : tapPolyRem a b =
      tapPolyAdd a (tapPolyMul q b))
    (hbez : d =
      tapPolyAdd (tapPolyMul u b)
        (tapPolyMul v (tapPolyRem a b))) :
    d = tapPolyAdd (tapPolyMul v a)
      (tapPolyMul (tapPolyAdd u (tapPolyMul v q)) b) := by
  change d =
    tapPolyMul v a ^^^ tapPolyMul (u ^^^ tapPolyMul v q) b
  calc
    d = tapPolyMul u b ^^^
        tapPolyMul v (tapPolyRem a b) := hbez
    _ = tapPolyMul u b ^^^
          tapPolyMul v (a ^^^ tapPolyMul q b) := by
      rw [hrem]
      rfl
    _ = tapPolyMul u b ^^^
          (tapPolyMul v a ^^^
            tapPolyMul v (tapPolyMul q b)) := by
      rw [tapPolyMulXorRight v a (tapPolyMul q b)]
    _ = tapPolyMul u b ^^^
          (tapPolyMul v a ^^^
            tapPolyMul (tapPolyMul v q) b) := by
      rw [← tapPolyMulAssociative v q b]
    _ = tapPolyMul v a ^^^
          (tapPolyMul u b ^^^
            tapPolyMul (tapPolyMul v q) b) := by
      rw [← Nat.xor_assoc,
        Nat.xor_comm (tapPolyMul u b) (tapPolyMul v a),
        Nat.xor_assoc]
    _ = tapPolyMul v a ^^^
          tapPolyMul (u ^^^ tapPolyMul v q) b := by
      rw [tapPolyMulXorLeft u (tapPolyMul v q) b]

/-- A sufficient GCD fuel budget is one greater than the degree
of the nonzero second argument. Each recursive remainder lowers
that degree, retaining both common-divisor facts and a literal
Bezout combination.
Consumer: tapPolyGcdSpec, then PrimitiveMaskQuotient. -/
private theorem tapPolyGcdFuelInvariant :
    ∀ fuel a b : Nat,
      (a ≠ 0 ∨ b ≠ 0) →
      (b = 0 ∨ Nat.log2 b < fuel) →
      tapPolyGcdFuel a b fuel ≠ 0 ∧
        tapPolyDvd (tapPolyGcdFuel a b fuel) a ∧
        tapPolyDvd (tapPolyGcdFuel a b fuel) b ∧
        ∃ u v : Nat,
          tapPolyGcdFuel a b fuel =
            tapPolyAdd (tapPolyMul u a) (tapPolyMul v b) := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b hnonzero hbudget
      have hb : b = 0 := by
        rcases hbudget with hz | hlt
        · exact hz
        · omega
      have ha : a ≠ 0 := by
        rcases hnonzero with ha | hbnonzero
        · exact ha
        · exact False.elim (hbnonzero hb)
      rw [hb]
      exact tapPolyGcdFuelZeroSpec a 0 ha
  | succ fuel ih =>
      intro a b hnonzero hbudget
      by_cases hb : b = 0
      · have ha : a ≠ 0 := by
          rcases hnonzero with ha | hbnonzero
          · exact ha
          · exact False.elim (hbnonzero hb)
        rw [hb]
        exact tapPolyGcdFuelZeroSpec a (fuel + 1) ha
      · have hbudgetB : Nat.log2 b < fuel + 1 := by
          rcases hbudget with hz | hlt
          · exact False.elim (hb hz)
          · exact hlt
        have hnext :
            tapPolyRem a b = 0 ∨
              Nat.log2 (tapPolyRem a b) < fuel := by
          rcases tapPolyRemLog a b hb with hz | hlt
          · exact Or.inl hz
          · exact Or.inr (by omega)
        obtain ⟨hdnonzero, hdb, hdr, u, v, hbez⟩ :=
          ih b (tapPolyRem a b) (Or.inl hb) hnext
        obtain ⟨q, hdiv⟩ := tapPolyDivExists a b hb
        have hqdiv :
            tapPolyDvd
              (tapPolyGcdFuel b (tapPolyRem a b) fuel)
              (tapPolyMul q b) :=
          tapPolyDvdMulLeft _ b q hdb
        have hda :
            tapPolyDvd
              (tapPolyGcdFuel b (tapPolyRem a b) fuel)
              a := by
          have hsum :=
            tapPolyDvdAdd
              (tapPolyGcdFuel b (tapPolyRem a b) fuel)
              (tapPolyMul q b) (tapPolyRem a b) hqdiv hdr
          rw [← hdiv] at hsum
          exact hsum
        have hrem :
            tapPolyRem a b =
              tapPolyAdd a (tapPolyMul q b) :=
          tapPolyRemFromDivision a b q hdiv
        have hbezNew :=
          tapPolyBezoutRemTransport a b q u v
            (tapPolyGcdFuel b (tapPolyRem a b) fuel)
            hrem hbez
        have hstep :
            tapPolyGcdFuel a b (fuel + 1) =
              tapPolyGcdFuel b (tapPolyRem a b) fuel := by
          simp only [tapPolyGcdFuel, if_neg hb]
        rw [hstep]
        exact ⟨hdnonzero, hda, hdb,
          v, tapPolyAdd u (tapPolyMul v q), hbezNew⟩

/-- A nonzero mask below a maximum has no greater log degree
than the maximum. Consumer: the literal-GCD fuel bound. -/
private theorem tapPolyLogLeOfLe (a b : Nat)
    (ha : a ≠ 0) (hb : b ≠ 0) (hle : a ≤ b) :
    Nat.log2 a ≤ Nat.log2 b := by
  by_cases hlog : Nat.log2 a ≤ Nat.log2 b
  · exact hlog
  · have hindex : Nat.log2 b + 1 ≤ Nat.log2 a := by omega
    have hpow : 2 ^ (Nat.log2 b + 1) ≤
        2 ^ Nat.log2 a :=
      Nat.pow_le_pow_right (by decide) hindex
    have hlow := (tapMaskLog a ha).1
    have hhigh := (tapMaskLog b hb).2
    omega

/-- The actual fuelled GCD returns a nonzero common divisor
with explicit Bezout coefficients. The published fuel
Nat.log2 (max a b) + 2 is sufficient.
Consumer: PrimitiveMaskFactors, PrimitiveMaskQuotient and
PrimitiveTapSelection. -/
theorem tapPolyGcdSpec (a b : Nat)
    (h : a ≠ 0 ∨ b ≠ 0) :
    tapPolyGcd a b ≠ 0 ∧
      tapPolyDvd (tapPolyGcd a b) a ∧
      tapPolyDvd (tapPolyGcd a b) b ∧
      ∃ u v : Nat,
        tapPolyGcd a b =
          tapPolyAdd (tapPolyMul u a) (tapPolyMul v b) := by
  have hbudget :
      b = 0 ∨ Nat.log2 b <
        Nat.log2 (max a b) + 2 := by
    by_cases hb : b = 0
    · exact Or.inl hb
    · have hmax : max a b ≠ 0 := by
        intro hz
        have hle : b ≤ max a b := Nat.le_max_right a b
        omega
      have hle : b ≤ max a b := Nat.le_max_right a b
      have hlog :=
        tapPolyLogLeOfLe b (max a b) hb hmax hle
      exact Or.inr (by omega)
  exact tapPolyGcdFuelInvariant
    (Nat.log2 (max a b) + 2) a b h hbudget

/-- Every common divisor divides the actual Euclidean GCD,
because the GCD is a Bezout combination of its two arguments.
Consumer: PrimitiveMaskFactors and PrimitiveMaskQuotient. -/
theorem tapPolyDvdGcd (a b c : Nat)
    (h : a ≠ 0 ∨ b ≠ 0)
    (hca : tapPolyDvd c a)
    (hcb : tapPolyDvd c b) :
    tapPolyDvd c (tapPolyGcd a b) := by
  obtain ⟨_, _, _, u, v, hbez⟩ :=
    tapPolyGcdSpec a b h
  have hua : tapPolyDvd c (tapPolyMul u a) :=
    tapPolyDvdMulLeft c a u hca
  have hvb : tapPolyDvd c (tapPolyMul v b) :=
    tapPolyDvdMulLeft c b v hcb
  have hsum :=
    tapPolyDvdAdd c (tapPolyMul u a)
      (tapPolyMul v b) hua hvb
  rw [← hbez] at hsum
  exact hsum

/-- When every common divisor is the unit, the literal GCD is
the unit. Consumer: PrimitiveMaskFactors and PrimitiveMaskQuotient. -/
theorem tapPolyGcdEqOneOfCoprime (a b : Nat)
    (h : a ≠ 0 ∨ b ≠ 0)
    (hcoprime :
      ∀ c : Nat, tapPolyDvd c a → tapPolyDvd c b → c = 1) :
    tapPolyGcd a b = 1 := by
  obtain ⟨_, hda, hdb, _⟩ :=
    tapPolyGcdSpec a b h
  exact hcoprime (tapPolyGcd a b) hda hdb

/-- The only polynomial-mask divisor of one is the unit one.
Consumer: PrimitiveMaskFactors and PrimitiveTapSelection. -/
theorem tapPolyDvdOneEq (c : Nat)
    (h : tapPolyDvd c 1) : c = 1 := by
  have hc : c ≠ 0 := by
    intro hz
    obtain ⟨q, hq⟩ := h
    rw [hz, tapPolyMulZeroRight] at hq
    omega
  have hdegree :=
    tapPolyDvdLog c 1 hc (by decide) h
  have hzero : Nat.log2 c = 0 := by
    change Nat.log2 c ≤ 0 at hdegree
    omega
  have hbounds := tapMaskLog c hc
  rw [hzero] at hbounds
  change 1 ≤ c ∧ c < 2 at hbounds
  omega

/-- A proper irreducible divisor cannot occur in a factorization
without being one of its two factors. This constructs the coprime
GCD interface needed by Euclid's lemma and inverses.
Consumer: PrimitiveMaskQuotient. -/
private theorem tapPolyIrreducibleCoprime (f a : Nat)
    (hf : TapIrreducible f)
    (hnot : ¬ tapPolyDvd f a) :
    tapPolyGcd f a = 1 := by
  have hfnonzero : f ≠ 0 := by
    have hbound := hf.1
    omega
  apply tapPolyGcdEqOneOfCoprime f a (Or.inl hfnonzero)
  intro d hdf hda
  obtain ⟨q, hfactor⟩ := hdf
  rcases hf.2 q d hfactor with hq | hd
  · have hsame : f = d := by
      rw [hq, tapPolyMulOneLeft] at hfactor
      exact hfactor
    have hfa : tapPolyDvd f a := by
      rw [hsame]
      exact hda
    exact False.elim (hnot hfa)
  · exact hd

/-- An irreducible mask dividing a product divides one factor.
This uses the actual Euclidean Bezout certificate, not an
assumed unique factorization theorem.
Consumer: PrimitiveMaskFactors and PrimitiveMaskQuotient. -/
theorem tapPolyEuclid (f a c : Nat)
    (hf : TapIrreducible f)
    (h : tapPolyDvd f (tapPolyMul a c)) :
    tapPolyDvd f a ∨ tapPolyDvd f c := by
  by_cases hfa : tapPolyDvd f a
  · exact Or.inl hfa
  · have hfnonzero : f ≠ 0 := by
      have hbound := hf.1
      omega
    have hcoprime :=
      tapPolyIrreducibleCoprime f a hf hfa
    obtain ⟨_, _, _, u, v, hbez⟩ :=
      tapPolyGcdSpec f a (Or.inl hfnonzero)
    have hone :
        1 = tapPolyAdd (tapPolyMul u f)
          (tapPolyMul v a) :=
      hcoprime.symm.trans hbez
    have hvalue :
        c = tapPolyAdd
          (tapPolyMul (tapPolyMul u f) c)
          (tapPolyMul (tapPolyMul v a) c) := by
      calc
        c = tapPolyMul 1 c :=
          (tapPolyMulOneLeft c).symm
        _ = tapPolyMul
              (tapPolyAdd (tapPolyMul u f)
                (tapPolyMul v a)) c := by
          rw [← hone]
        _ = tapPolyAdd
              (tapPolyMul (tapPolyMul u f) c)
              (tapPolyMul (tapPolyMul v a) c) :=
          tapPolyMulXorLeft _ _ c
    have huf : tapPolyDvd f (tapPolyMul u f) :=
      ⟨u, rfl⟩
    have hu :
        tapPolyDvd f (tapPolyMul (tapPolyMul u f) c) :=
      tapPolyDvdMul f (tapPolyMul u f) c huf
    have hv :
        tapPolyDvd f (tapPolyMul (tapPolyMul v a) c) := by
      have hbig :=
        tapPolyDvdMul f (tapPolyMul a c) v h
      have heq :
          tapPolyMul (tapPolyMul v a) c =
            tapPolyMul (tapPolyMul a c) v := by
        calc
          tapPolyMul (tapPolyMul v a) c =
              tapPolyMul v (tapPolyMul a c) :=
            tapPolyMulAssociative v a c
          _ = tapPolyMul (tapPolyMul a c) v :=
            tapPolyMulCommutative v (tapPolyMul a c)
      rw [heq]
      exact hbig
    have hsum :=
      tapPolyDvdAdd f
        (tapPolyMul (tapPolyMul u f) c)
        (tapPolyMul (tapPolyMul v a) c) hu hv
    rw [← hvalue] at hsum
    exact Or.inr hsum

/-- A nonzero reduced mask has a modular inverse modulo an
irreducible mask. Its inverse is a literal Bezout coefficient.
Consumer: PrimitiveMaskQuotient and PrimitiveTapSelection. -/
theorem tapPolyInverseExists (f a : Nat)
    (hf : TapIrreducible f)
    (ha : a ≠ 0)
    (hlt : Nat.log2 a < Nat.log2 f) :
    ∃ u : Nat, tapPolyRem (tapPolyMul u a) f = 1 := by
  have hfnonzero : f ≠ 0 := by
    have hbound := hf.1
    omega
  have hnot : ¬ tapPolyDvd f a := by
    intro hfa
    have hdegree :=
      tapPolyDvdLog f a hfnonzero ha hfa
    omega
  have hcoprime :=
    tapPolyIrreducibleCoprime f a hf hnot
  obtain ⟨_, _, _, u, v, hbez⟩ :=
    tapPolyGcdSpec f a (Or.inl hfnonzero)
  have hone :
      1 = tapPolyAdd (tapPolyMul u f) (tapPolyMul v a) :=
    hcoprime.symm.trans hbez
  have hlogPositive : 0 < Nat.log2 f := by
    by_cases hz : Nat.log2 f = 0
    · have hbound := (tapMaskLog f hfnonzero).2
      rw [hz] at hbound
      change f < 2 at hbound
      have hge := hf.1
      omega
    · omega
  have hlogOne : Nat.log2 1 < Nat.log2 f := by
    change 0 < Nat.log2 f
    exact hlogPositive
  have hrepr :
      (1 : Nat) = tapPolyAdd (tapPolyMul 0 f) 1 := by
    rw [tapPolyMulZeroLeft]
    change 1 = 0 ^^^ 1
    rfl
  have hremOne :
      tapPolyRem 1 f = 1 :=
    tapPolyRemUnique 1 f 0 1 hfnonzero hrepr
      (Or.inr hlogOne)
  have hmod :=
    congrArg (fun z : Nat => tapPolyRem z f) hone
  rw [hremOne,
    tapPolyRemAdd (tapPolyMul u f) (tapPolyMul v a) f hfnonzero,
    tapPolyRemMulSelf u f hfnonzero] at hmod
  change 1 = 0 ^^^ tapPolyRem (tapPolyMul v a) f at hmod
  rw [Nat.zero_xor] at hmod
  exact ⟨v, hmod.symm⟩

/-- Euclid's lemma iterated over the literal List.foldr product.
The empty list is impossible because an irreducible cannot
divide the unit.
Consumer: PrimitiveMaskFactors and PrimitiveTapSelection. -/
theorem tapPolyEuclidList (f : Nat)
    (hf : TapIrreducible f) (l : List Nat)
    (h : tapPolyDvd f (l.foldr tapPolyMul 1)) :
    ∃ a : Nat, a ∈ l ∧ tapPolyDvd f a := by
  induction l with
  | nil =>
      have hone : tapPolyDvd f 1 := by
        exact h
      have hunit := tapPolyDvdOneEq f hone
      have hbound := hf.1
      omega
  | cons a rest ih =>
      have hstep :
          tapPolyDvd f
            (tapPolyMul a (rest.foldr tapPolyMul 1)) := by
        exact h
      rcases tapPolyEuclid f a
        (rest.foldr tapPolyMul 1) hf hstep with ha | hrest
      · exact ⟨a, by simp, ha⟩
      · obtain ⟨b, hmem, hdiv⟩ := ih hrest
        exact ⟨b, List.mem_cons_of_mem a hmem, hdiv⟩

end L3

#print axioms L3.tapPolyGcdSpec
#print axioms L3.tapPolyEuclid
#print axioms L3.tapPolyInverseExists

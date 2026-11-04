import Leader.L3.Primitive.MaskGcd

/-!
Binary-polynomial factor lists and finite counting bounds, for
PrimitiveIrreducibleExistence. The derivative product rule and squarefree
factor extraction are in PrimitiveMaskDeriv.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Product of literal polynomial masks.
Consumer: PrimitiveIrreducibleExistence. -/
def tapPolyListProd : List Nat → Nat
  | [] => 1
  | a :: rest => tapPolyMul a (tapPolyListProd rest)

/-- Sum of the degrees of a factor list.
Consumer: PrimitiveIrreducibleExistence. -/
def tapPolyListDegreeSum : List Nat → Nat
  | [] => 0
  | a :: rest => Nat.log2 a + tapPolyListDegreeSum rest

/-- A list append corresponds to multiplying polynomial products.
Consumer: tapIrreducibleFactorList and PrimitiveIrreducibleExistence. -/
private theorem tapPolyListProdAppend (left right : List Nat) :
    tapPolyListProd (left ++ right) =
      tapPolyMul (tapPolyListProd left) (tapPolyListProd right) := by
  induction left with
  | nil =>
      change tapPolyListProd right =
        tapPolyMul 1 (tapPolyListProd right)
      exact (tapPolyMulOneLeft _).symm
  | cons x rest ih =>
      change tapPolyMul x (tapPolyListProd (rest ++ right)) =
        tapPolyMul (tapPolyMul x (tapPolyListProd rest))
          (tapPolyListProd right)
      rw [ih]
      exact (tapPolyMulAssociative x
        (tapPolyListProd rest) (tapPolyListProd right)).symm

/-- List-degree sum is additive under append.
Consumer: tapIrreducibleFactorList. -/
private theorem tapPolyListDegreeSumAppend (left right : List Nat) :
    tapPolyListDegreeSum (left ++ right) =
      tapPolyListDegreeSum left + tapPolyListDegreeSum right := by
  induction left with
  | nil =>
      change tapPolyListDegreeSum right = 0 + tapPolyListDegreeSum right
      omega
  | cons x rest ih =>
      change Nat.log2 x + tapPolyListDegreeSum (rest ++ right) =
        (Nat.log2 x + tapPolyListDegreeSum rest) +
          tapPolyListDegreeSum right
      rw [ih, Nat.add_assoc]

/-- A nonzero nonunit mask has positive degree.
Consumer: tapIrreducibleFactorList. -/
private theorem tapPolyNonunitLogPos (p : Nat)
    (hp : p ≠ 0) (hone : p ≠ 1) :
    0 < Nat.log2 p := by
  by_cases hz : Nat.log2 p = 0
  · have hb := tapMaskLog p hp
    rw [hz] at hb
    have hpOne : p = 1 := by
      change 1 ≤ p ∧ p < 2 at hb
      omega
    exact False.elim (hone hpOne)
  · omega

/-- Multiplying a nonzero mask by a nonzero nonunit strictly
increases its numeric mask: the degree rises.
Consumer: tapIrreducibleFactorList. -/
private theorem tapPolyFactorLt (a c : Nat)
    (ha : a ≠ 0) (hc : c ≠ 0) (hcOne : c ≠ 1) :
    a < tapPolyMul a c := by
  have hcPos := tapPolyNonunitLogPos c hc hcOne
  have hlog := tapPolyMulLog a c ha hc
  have hindex :
      Nat.log2 a + 1 ≤ Nat.log2 (tapPolyMul a c) := by
    omega
  have hpower :
      2 ^ (Nat.log2 a + 1) ≤
        2 ^ Nat.log2 (tapPolyMul a c) :=
    Nat.pow_le_pow_right (by decide) hindex
  have hupper := (tapMaskLog a ha).2
  have hbottom :=
    (tapMaskLog (tapPolyMul a c)
      (tapPolyMulNeZero a c ha hc)).1
  exact Nat.lt_of_lt_of_le
    (Nat.lt_of_lt_of_le hupper hpower) hbottom

/-- Strong induction on the exact numeric polynomial mask
produces irreducible factors with an additive degree ledger.
This makes no assertion of factor uniqueness.
Consumer: PrimitiveIrreducibleExistence. -/
theorem tapIrreducibleFactorList (p : Nat) (hp : p ≠ 0) :
    ∃ l : List Nat,
      tapPolyListProd l = p ∧
      (∀ f : Nat, f ∈ l → TapIrreducible f) ∧
      tapPolyListDegreeSum l = Nat.log2 p := by
  classical
  induction p using Nat.strongRecOn with
  | ind p ih =>
      by_cases hone : p = 1
      · subst p
        refine ⟨[], ?_, ?_, ?_⟩
        · rfl
        · intro f hf
          cases hf
        · rfl
      · by_cases hirr : TapIrreducible p
        · refine ⟨[p], ?_, ?_, ?_⟩
          · change tapPolyMul p 1 = p
            exact tapPolyMulOneRight p
          · intro f hf
            have hfp : f = p := by
              simpa only [List.mem_singleton] using hf
            rw [hfp]
            exact hirr
          · change Nat.log2 p + 0 = Nat.log2 p
            exact Nat.add_zero _
        · have hpge : 2 ≤ p := by omega
          have hnot :
              ¬ ∀ a c : Nat,
                p = tapPolyMul a c → a = 1 ∨ c = 1 := by
            intro hall
            exact hirr ⟨hpge, hall⟩
          have hsplit :
              ∃ a c : Nat,
                p = tapPolyMul a c ∧ a ≠ 1 ∧ c ≠ 1 := by
            apply Classical.byContradiction
            intro hno
            apply hnot
            intro a c hac
            by_cases ha1 : a = 1
            · exact Or.inl ha1
            · right
              by_cases hc1 : c = 1
              · exact hc1
              · exact False.elim (hno ⟨a, c, hac, ha1, hc1⟩)
          obtain ⟨a, c, hfactor, haOne, hcOne⟩ := hsplit
          have ha : a ≠ 0 := by
            intro hz
            rw [hz, tapPolyMulZeroLeft] at hfactor
            exact hp hfactor
          have hc : c ≠ 0 := by
            intro hz
            rw [hz, tapPolyMulZeroRight] at hfactor
            exact hp hfactor
          have haLt : a < p := by
            rw [hfactor]
            exact tapPolyFactorLt a c ha hc hcOne
          have hcLt : c < p := by
            rw [hfactor, tapPolyMulCommutative a c]
            exact tapPolyFactorLt c a hc ha haOne
          obtain ⟨left, hleft, hleftIrr, hleftDegree⟩ :=
            ih a haLt ha
          obtain ⟨right, hright, hrightIrr, hrightDegree⟩ :=
            ih c hcLt hc
          refine ⟨left ++ right, ?_, ?_, ?_⟩
          · rw [tapPolyListProdAppend, hleft, hright]
            exact hfactor.symm
          · intro f hf
            rcases List.mem_append.mp hf with hfl | hfr
            · exact hleftIrr f hfl
            · exact hrightIrr f hfr
          · rw [tapPolyListDegreeSumAppend,
              hleftDegree, hrightDegree]
            have hlog := tapPolyMulLog a c ha hc
            rw [← hfactor] at hlog
            exact hlog.symm

/-- A finite mask with ones at the even bit positions below
twice its fuel. The derivative uses this bit-selection mask.
Consumer: PrimitiveIrreducibleExistence. -/
private def tapPolyEvenBitMask : Nat → Nat
  | 0 => 0
  | fuel + 1 => 1 + 4 * tapPolyEvenBitMask fuel

/-- Formal derivative by dropping one low coefficient and keeping
only even-indexed bits. Bit j is taken from input j+1 exactly
when j is even. Consumer: PrimitiveIrreducibleExistence.

The corresponding testBit theorem and product rule are NOT yet
proved in this module. -/
def tapPolyDeriv (p : Nat) : Nat :=
  (p / 2) &&& tapPolyEvenBitMask (Nat.log2 p + 1)

/-- The polynomial X^(2^t) + X as a binary mask.
Consumer: PrimitiveIrreducibleExistence. -/
def tapFrobeniusMask (t : Nat) : Nat :=
  tapPolyAdd (2 ^ (2 ^ t)) 2

/-- A Nodup list of natural numbers below B has length <= B.
Consumer: tapFactorDegreeSumBound and PrimitiveIrreducibleExistence. -/
theorem tapNodupBelowLength (l : List Nat) (B : Nat)
    (hl : l.Nodup) (hb : ∀ x : Nat, x ∈ l → x < B) :
    l.length ≤ B := by
  have hsubset : ∀ x : Nat, x ∈ l → x ∈ List.range B := by
    intro x hx
    exact List.mem_range.mpr (hb x hx)
  have hlen : l.length ≤ (List.range B).length :=
    List.Nodup.length_le_of_subset hl hsubset
  simpa only [List.length_range] using hlen

/-- Any nonzero mask with log-degree at most h lies below
the bound 2^(h+1). Consumer: tapFactorDegreeSumBound. -/
private theorem tapPolyLogBoundMask (f h : Nat)
    (hf : f ≠ 0) (hlog : Nat.log2 f ≤ h) :
    f < 2 ^ (h + 1) := by
  have hpower :
      2 ^ (Nat.log2 f + 1) ≤ 2 ^ (h + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.lt_of_lt_of_le (tapMaskLog f hf).2 hpower

/-- Sum of the degrees of a bounded-degree list.
Consumer: tapFactorDegreeSumBound. -/
private theorem tapPolyListDegreeSumLe (l : List Nat) (h : Nat)
    (hb : ∀ f : Nat, f ∈ l → Nat.log2 f ≤ h) :
    tapPolyListDegreeSum l ≤ h * l.length := by
  induction l with
  | nil =>
      simp [tapPolyListDegreeSum]
  | cons a rest ih =>
      have ha : Nat.log2 a ≤ h :=
        hb a (List.mem_cons.mpr (Or.inl rfl))
      have hrest : ∀ f : Nat, f ∈ rest → Nat.log2 f ≤ h := by
        intro f hf
        exact hb f (List.mem_cons_of_mem a hf)
      have htail := ih hrest
      change Nat.log2 a + tapPolyListDegreeSum rest ≤
        h * (rest.length + 1)
      have hrepr : h * (rest.length + 1) =
          h * rest.length + h := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [hrepr]
      omega

/-- Distinct nonzero factors of degree <= h have total degree
at most h * 2^(h+1). Consumer: PrimitiveIrreducibleExistence. -/
theorem tapFactorDegreeSumBound (l : List Nat) (h : Nat)
    (hl : l.Nodup)
    (hb : ∀ f : Nat, f ∈ l →
      f ≠ 0 ∧ Nat.log2 f ≤ h) :
    tapPolyListDegreeSum l ≤ h * 2 ^ (h + 1) := by
  have hmask :
      ∀ f : Nat, f ∈ l → f < 2 ^ (h + 1) := by
    intro f hf
    exact tapPolyLogBoundMask f h (hb f hf).1 (hb f hf).2
  have hlength :=
    tapNodupBelowLength l (2 ^ (h + 1)) hl hmask
  have hsum :=
    tapPolyListDegreeSumLe l h (by
      intro f hf
      exact (hb f hf).2)
  exact Nat.le_trans hsum (Nat.mul_le_mul_left h hlength)

/-- The exponential dominates 2(k+3)+1; a simple step
multiplies its right side by two.
Consumer: tapLogBelowOfHalf and PrimitiveIrreducibleExistence. -/
private theorem tapHalfExponentialGrowth (k : Nat) :
    2 * (k + 3) + 1 < 2 ^ (k + 3) := by
  induction k with
  | zero =>
      decide
  | succ k ih =>
      have hindex : k + 1 + 3 = k + 3 + 1 := by omega
      have hpow :
          2 ^ (k + 3 + 1) = (2 ^ (k + 3)) * 2 := by
        rw [Nat.pow_succ]
      change 2 * (k + 1 + 3) + 1 < 2 ^ (k + 1 + 3)
      rw [hindex, hpow]
      have hlarge : 2 ≤ 2 ^ (k + 3) := by omega
      omega

/-- For t >= 18, the proposed upper bound on the degree sum
of all proper-divisor-degree factors is smaller than 2^t.
Consumer: PrimitiveIrreducibleExistence. -/
theorem tapLogBelowOfHalf (t : Nat) (ht : 18 ≤ t) :
    (t / 2) * 2 ^ (t / 2 + 1) < 2 ^ t := by
  have hhalf : 3 ≤ t / 2 := by omega
  have hgrowth := tapHalfExponentialGrowth (t / 2 - 3)
  have hindex : (t / 2 - 3) + 3 = t / 2 := by omega
  rw [hindex] at hgrowth
  have hclock : t ≤ 2 * (t / 2) + 1 := by omega
  have htlt : t < 2 ^ (t / 2) := by omega
  have hsmall : 2 * (t / 2) ≤ t := by omega
  have hle :
      (2 * (t / 2)) * 2 ^ (t / 2) ≤
        t * 2 ^ (t / 2) :=
    Nat.mul_le_mul_right (2 ^ (t / 2)) hsmall
  have hlt :
      t * 2 ^ (t / 2) <
        2 ^ (t / 2) * 2 ^ (t / 2) :=
    Nat.mul_lt_mul_of_pos_right htlt (Nat.two_pow_pos _)
  have hproduct :
      2 ^ (t / 2) * 2 ^ (t / 2) =
        2 ^ (t / 2 + t / 2) :=
    (Nat.pow_add 2 (t / 2) (t / 2)).symm
  have hbound : t / 2 + t / 2 ≤ t := by omega
  have hpower :
      2 ^ (t / 2 + t / 2) ≤ 2 ^ t :=
    Nat.pow_le_pow_right (by decide) hbound
  calc
    (t / 2) * 2 ^ (t / 2 + 1) =
        (2 * (t / 2)) * 2 ^ (t / 2) := by
      rw [Nat.pow_succ]
      calc
        (t / 2) * (2 ^ (t / 2) * 2) =
            (t / 2) * (2 * 2 ^ (t / 2)) := by
          rw [Nat.mul_comm (2 ^ (t / 2)) 2]
        _ = ((t / 2) * 2) * 2 ^ (t / 2) :=
          (Nat.mul_assoc (t / 2) 2 (2 ^ (t / 2))).symm
        _ = (2 * (t / 2)) * 2 ^ (t / 2) := by
          rw [Nat.mul_comm (t / 2) 2]
    _ ≤ t * 2 ^ (t / 2) := hle
    _ < 2 ^ (t / 2) * 2 ^ (t / 2) := hlt
    _ = 2 ^ (t / 2 + t / 2) := hproduct
    _ ≤ 2 ^ t := hpower

end L3

#print axioms L3.tapIrreducibleFactorList
#print axioms L3.tapFactorDegreeSumBound
#print axioms L3.tapLogBelowOfHalf

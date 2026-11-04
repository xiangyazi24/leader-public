import Leader.L3.Primitive.MaskQuotient
import Leader.L3.Primitive.TapCert

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Fin-fold XOR pairing for the PrimitiveTapSelection functional bridge. -/
def tapFunctional (t : Nat) (u : Fin t → Bool) (p : Nat) : Bool :=
  Fin.foldl t
    (fun acc j => Bool.xor acc (Bool.and (Nat.testBit p j.val) (u j)))
    false

private theorem tapBoolXorShuffle (a b c d : Bool) :
    Bool.xor (Bool.xor a b) (Bool.xor c d) =
      Bool.xor (Bool.xor a c) (Bool.xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem tapFoldXorZero (t : Nat) (v : Fin t → Bool)
    (hv : ∀ j, v j = false) :
    Fin.foldl t (fun acc j => Bool.xor acc (v j)) false = false := by
  induction t with
  | zero =>
      rfl
  | succ n ih =>
      rw [Fin.foldl_succ_last]
      have hp : ∀ j : Fin n, v j.castSucc = false := by
        intro j
        exact hv j.castSucc
      rw [ih (fun j => v j.castSucc) hp, hv (Fin.last n)]
      rfl

private theorem tapFoldXorAdd (t : Nat) (v w : Fin t → Bool) :
    Fin.foldl t
      (fun acc j => Bool.xor acc (Bool.xor (v j) (w j))) false =
    Bool.xor
      (Fin.foldl t (fun acc j => Bool.xor acc (v j)) false)
      (Fin.foldl t (fun acc j => Bool.xor acc (w j)) false) := by
  induction t with
  | zero =>
      rfl
  | succ n ih =>
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last,
        Fin.foldl_succ_last]
      rw [ih (fun j => v j.castSucc) (fun j => w j.castSucc)]
      exact tapBoolXorShuffle _ _ _ _

/-- XOR-additivity of the literal finite functional.
Consumer: PrimitiveTapSelection via tapRecStepFunctional. -/
theorem tapFunctionalAdd (t : Nat) (u : Fin t → Bool) (p q : Nat) :
    tapFunctional t u (tapPolyAdd p q) =
      Bool.xor (tapFunctional t u p) (tapFunctional t u q) := by
  have h : ∀ j : Fin t,
      Bool.and (Nat.testBit (tapPolyAdd p q) j.val) (u j) =
        Bool.xor (Bool.and (Nat.testBit p j.val) (u j))
          (Bool.and (Nat.testBit q j.val) (u j)) := by
    intro j
    change Bool.and (Nat.testBit (p ^^^ q) j.val) (u j) = _
    rw [Nat.testBit_xor]
    cases Nat.testBit p j.val <;> cases Nat.testBit q j.val <;>
      cases u j <;> rfl
  unfold tapFunctional
  simp only [h]
  exact tapFoldXorAdd t
    (fun j => Bool.and (Nat.testBit p j.val) (u j))
    (fun j => Bool.and (Nat.testBit q j.val) (u j))

/-- The zero mask has zero pairing with every state.
Consumer: PrimitiveTapSelection and tapRecStepFunctional. -/
private theorem tapFunctionalZeroMask (t : Nat) (u : Fin t → Bool) :
    tapFunctional t u 0 = false := by
  unfold tapFunctional
  apply tapFoldXorZero
  intro j
  simp

/-- The singleton monomial extracts precisely its coordinate.
Consumer: PrimitiveTapSelection and tapPrimitiveOfOrder. -/
theorem tapFunctionalBit (t : Nat) (u : Fin t → Bool)
    (j : Nat) (hj : j < t) :
    tapFunctional t u (2 ^ j) = u ⟨j, hj⟩ := by
  induction t generalizing j with
  | zero =>
      omega
  | succ n ih =>
      have hsplit :
          tapFunctional (n + 1) u (2 ^ j) =
            Bool.xor
              (tapFunctional n (fun i => u i.castSucc) (2 ^ j))
              (Bool.and (Nat.testBit (2 ^ j) n) (u (Fin.last n))) := by
        unfold tapFunctional
        rw [Fin.foldl_succ_last]
        rfl
      rw [hsplit]
      by_cases hbelow : j < n
      · have hne : j ≠ n := by omega
        rw [ih (fun i => u i.castSucc) j hbelow,
          Nat.testBit_two_pow_of_ne hne]
        simp only [Bool.false_and, Bool.xor_false]
        rfl
      · have hjlast : j = n := by omega
        subst j
        have hpref :
            tapFunctional n (fun i => u i.castSucc) (2 ^ n) = false := by
          unfold tapFunctional
          apply tapFoldXorZero
          intro i
          have hne : n ≠ i.val := by omega
          rw [Nat.testBit_two_pow_of_ne hne]
          rfl
        rw [hpref, Nat.testBit_two_pow_self]
        simp only [Bool.true_and, Bool.false_xor]
        rfl

/-- If every reduced mask annihilates a functional, no state
coordinate is true. Consumer: PrimitiveTapSelection. -/
theorem tapFunctionalZero (t : Nat) (u : Fin t → Bool)
    (hzero : ∀ p : Nat, p < 2 ^ t → tapFunctional t u p = false) :
    ∀ j : Fin t, u j ≠ true := by
  intro j hj
  have hle : 2 ^ (j.val + 1) ≤ 2 ^ t :=
    Nat.pow_le_pow_of_le (by decide : 1 < (2 : Nat)) (by omega)
  have hpos : 0 < 2 ^ j.val := Nat.two_pow_pos j.val
  have hpow : 2 ^ j.val < 2 ^ t := by
    rw [Nat.pow_succ] at hle
    omega
  have hh := hzero (2 ^ j.val) hpow
  rw [tapFunctionalBit t u j.val j.isLt] at hh
  rw [hj] at hh
  cases hh

/-- The feedback fold is exactly the functional applied to b.
Consumer: PrimitiveTapSelection via tapRecStepFunctional. -/
theorem tapFoldEqFunctional (t b : Nat) (u : Fin t → Bool) :
    Fin.foldl t
      (fun acc j =>
        Bool.xor acc (Bool.and (Nat.testBit b j.val) (u j))) false =
      tapFunctional t u b := rfl

private theorem tapFoldBits (t p : Nat) :
    Fin.foldl t
      (fun acc j =>
        acc ^^^ (if Nat.testBit p j.val then 2 ^ j.val else 0)) 0 =
      p % 2 ^ t := by
  induction t with
  | zero =>
      simp only [Fin.foldl_zero, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
      rw [Fin.foldl_succ_last]
      change
        (Fin.foldl n
          (fun acc j =>
            acc ^^^ (if Nat.testBit p j.val then 2 ^ j.val else 0)) 0) ^^^
          (if Nat.testBit p n then 2 ^ n else 0) =
        p % 2 ^ (n + 1)
      rw [ih]
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_xor, Nat.testBit_mod_two_pow,
        Nat.testBit_mod_two_pow]
      by_cases hi : i < n
      · have hne : n ≠ i := by omega
        have his : i < n + 1 := by omega
        cases hv : Nat.testBit p n <;>
          simp [hi, his, hv, Nat.testBit_two_pow, hne]
      · by_cases heq : i = n
        · subst i
          cases hv : Nat.testBit p n <;>
            simp [hi, hv, Nat.testBit_two_pow]
        · have his : ¬ i < n + 1 := by omega
          have hne : n ≠ i := by omega
          cases hv : Nat.testBit p n <;>
            simp [hi, his, hv, Nat.testBit_two_pow, hne]

private theorem tapFoldEvaluation (t : Nat) (F : Nat → Bool)
    (hadd : ∀ a c, F (tapPolyAdd a c) =
      Bool.xor (F a) (F c))
    (hzero : F 0 = false) (p : Nat) :
    F (Fin.foldl t
      (fun acc j =>
        acc ^^^ (if Nat.testBit p j.val then 2 ^ j.val else 0)) 0) =
    Fin.foldl t
      (fun acc j =>
        Bool.xor acc (Bool.and (Nat.testBit p j.val) (F (2 ^ j.val))))
      false := by
  induction t with
  | zero =>
      simpa only [Fin.foldl_zero] using hzero
  | succ n ih =>
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      change
        F (tapPolyAdd
          (Fin.foldl n
            (fun acc j =>
              acc ^^^ (if Nat.testBit p j.val then 2 ^ j.val else 0)) 0)
          (if Nat.testBit p n then 2 ^ n else 0)) = _
      rw [hadd, ih]
      cases hv : Nat.testBit p n <;> simp [hv, hzero]

private theorem tapLinearDetermined (t : Nat)
    (F G : Nat → Bool)
    (hF : ∀ a c, F (tapPolyAdd a c) =
      Bool.xor (F a) (F c))
    (hG : ∀ a c, G (tapPolyAdd a c) =
      Bool.xor (G a) (G c))
    (hFzero : F 0 = false) (hGzero : G 0 = false)
    (hbasis : ∀ j : Nat, j < t → F (2 ^ j) = G (2 ^ j))
    (p : Nat) (hp : p < 2 ^ t) : F p = G p := by
  have hrepr := tapFoldBits t p
  rw [Nat.mod_eq_of_lt hp] at hrepr
  have hfold :
      Fin.foldl t
        (fun acc j =>
          Bool.xor acc
            (Bool.and (Nat.testBit p j.val) (F (2 ^ j.val)))) false =
      Fin.foldl t
        (fun acc j =>
          Bool.xor acc
            (Bool.and (Nat.testBit p j.val) (G (2 ^ j.val)))) false := by
    have hfun :
        (fun acc (j : Fin t) =>
          Bool.xor acc
            (Bool.and (Nat.testBit p j.val) (F (2 ^ j.val)))) =
        (fun acc (j : Fin t) =>
          Bool.xor acc
            (Bool.and (Nat.testBit p j.val) (G (2 ^ j.val)))) := by
      funext acc j
      rw [hbasis j.val j.isLt]
    rw [hfun]
  calc
    F p = F (Fin.foldl t
        (fun acc j =>
          acc ^^^ (if Nat.testBit p j.val then 2 ^ j.val else 0)) 0) :=
      congrArg F hrepr.symm
    _ = Fin.foldl t
        (fun acc j =>
          Bool.xor acc
            (Bool.and (Nat.testBit p j.val) (F (2 ^ j.val)))) false :=
      tapFoldEvaluation t F hF hFzero p
    _ = Fin.foldl t
        (fun acc j =>
          Bool.xor acc
            (Bool.and (Nat.testBit p j.val) (G (2 ^ j.val)))) false := hfold
    _ = G (Fin.foldl t
        (fun acc j =>
          acc ^^^ (if Nat.testBit p j.val then 2 ^ j.val else 0)) 0) :=
      (tapFoldEvaluation t G hG hGzero p).symm
    _ = G p := congrArg G hrepr

private theorem tapHighXor (t b : Nat) (hb : b < 2 ^ t) :
    (2 ^ t) ^^^ b = 2 ^ t + b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hlow : i < t
  · have hne : t ≠ i := by omega
    rw [Nat.testBit_two_pow_add_gt hlow b]
    simp [hne]
  · by_cases heq : i = t
    · subst i
      have hbit : Nat.testBit b t = false :=
        Nat.testBit_lt_two_pow hb
      rw [Nat.testBit_two_pow_add_eq b t]
      simp [hbit]
    · have hle : t + 1 ≤ i := by omega
      have hlarge : 2 ^ t + b < 2 ^ (t + 1) := by
        rw [Nat.pow_succ]
        omega
      have hpowers :
          2 ^ (t + 1) ≤ 2 ^ i :=
        Nat.pow_le_pow_of_le (by decide : 1 < (2 : Nat)) hle
      have hsum : 2 ^ t + b < 2 ^ i :=
        Nat.lt_of_lt_of_le hlarge hpowers
      have hbsmall : b < 2 ^ i :=
        Nat.lt_of_lt_of_le hb
          (Nat.pow_le_pow_of_le (by decide : 1 < (2 : Nat))
            (by omega : t ≤ i))
      have hbitSum : Nat.testBit (2 ^ t + b) i = false :=
        Nat.testBit_lt_two_pow hsum
      have hbitB : Nat.testBit b i = false :=
        Nat.testBit_lt_two_pow hbsmall
      have hne : t ≠ i := by omega
      simp [hne, hbitSum, hbitB]

private theorem tapTopRemainder (t b : Nat)
    (hb : b < 2 ^ t) :
    tapPolyRem (2 ^ t) (2 ^ t + b) = b := by
  have hupper : 2 ^ t < 2 ^ (t + 1) := by
    rw [Nat.pow_succ]
    have hpositive := Nat.two_pow_pos t
    omega
  rw [tapPolyRemSingleTop t b (2 ^ t) hb (Nat.le_refl _) hupper]
  rw [← tapHighXor t b hb]
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- Multiplication of reduced masks; its laws come from the literal
remainder, not an irreducibility assumption. Consumer: PrimitiveTapSelection. -/
def tapMulr (t b a c : Nat) : Nat :=
  tapPolyRem (tapPolyMul a c) (2 ^ t + b)

/-- The companion recurrence acts dually to multiplication by X.
Consumer: PrimitiveTapSelection. -/
theorem tapRecStepFunctional (t b : Nat)
    (ht : 2 ≤ t) (hb : b < 2 ^ t)
    (u : Fin t → Bool) (z : Nat) (hz : z < 2 ^ t) :
    tapFunctional t (recStep t (fun j => Nat.testBit b j) u) z =
      tapFunctional t u (tapMulr t b 2 z) := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hpositive := Nat.two_pow_pos t
    omega
  apply tapLinearDetermined t
    (fun p => tapFunctional t
      (recStep t (fun j => Nat.testBit b j) u) p)
    (fun p => tapFunctional t u (tapMulr t b 2 p))
  · intro p q
    exact tapFunctionalAdd t
      (recStep t (fun j => Nat.testBit b j) u) p q
  · intro p q
    change
      tapFunctional t u
        (tapPolyRem (tapPolyMul 2 (tapPolyAdd p q)) (2 ^ t + b)) =
        Bool.xor
          (tapFunctional t u (tapMulr t b 2 p))
          (tapFunctional t u (tapMulr t b 2 q))
    rw [show tapPolyMul 2 (tapPolyAdd p q) =
        tapPolyAdd (tapPolyMul 2 p) (tapPolyMul 2 q) from
        tapPolyMulXorRight 2 p q,
      tapPolyRemAdd _ _ (2 ^ t + b) hf]
    exact tapFunctionalAdd t u (tapMulr t b 2 p)
      (tapMulr t b 2 q)
  · exact tapFunctionalZeroMask t
      (recStep t (fun j => Nat.testBit b j) u)
  · change tapFunctional t u
      (tapPolyRem (tapPolyMul 2 0) (2 ^ t + b)) = false
    rw [tapPolyMulZeroRight,
      tapPolyRemSmall t b 0 hb (Nat.two_pow_pos t)]
    exact tapFunctionalZeroMask t u
  · intro j hj
    have hmul : tapPolyMul 2 (2 ^ j) = 2 ^ (j + 1) := by
      calc
        tapPolyMul 2 (2 ^ j) =
            tapPolyMul (2 ^ 1) (2 ^ j) := by rfl
        _ = 2 ^ (1 + j) := tapPolyPowerOfX 1 j
        _ = 2 ^ (j + 1) := by
          congr 1
          omega
    rw [tapFunctionalBit t
      (recStep t (fun i => Nat.testBit b i) u) j hj]
    change (recStep t (fun i => Nat.testBit b i) u)
      ⟨j, hj⟩ =
      tapFunctional t u
        (tapPolyRem (tapPolyMul 2 (2 ^ j)) (2 ^ t + b))
    rw [hmul]
    by_cases hnext : j + 1 < t
    · have hle : 2 ^ (j + 2) ≤ 2 ^ t :=
        Nat.pow_le_pow_of_le (by decide : 1 < (2 : Nat))
          (by omega)
      have hp : 2 ^ (j + 1) < 2 ^ t := by
        have hpositive := Nat.two_pow_pos (j + 1)
        have hpow : 2 ^ (j + 2) = 2 ^ (j + 1) * 2 := by
          have hindex : j + 2 = (j + 1) + 1 := by omega
          rw [hindex, Nat.pow_succ]
        rw [hpow] at hle
        omega
      rw [tapPolyRemSmall t b _ hb hp,
        tapFunctionalBit t u (j + 1) hnext]
      simp only [recStep, dif_pos hnext]
    · have heq : j + 1 = t := by omega
      rw [heq, tapTopRemainder t b hb]
      rw [← tapFoldEqFunctional t b u]
      simp only [recStep, dif_neg hnext]
  · exact hz

#print axioms L3.tapRecStepFunctional

/-- Iteration is multiplication by X^k on every reduced argument.
Consumer: PrimitiveTapSelection. -/
theorem tapRecIterFunctional (t b : Nat)
    (ht : 2 ≤ t) (hb : b < 2 ^ t)
    (k : Nat) (u : Fin t → Bool) (z : Nat) (hz : z < 2 ^ t) :
    tapFunctional t (recIter t (fun j => Nat.testBit b j) k u) z =
      tapFunctional t u
        (tapMulr t b (tapPolyPow 2 k) z) := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hpositive := Nat.two_pow_pos t
    omega
  induction k generalizing z with
  | zero =>
      change tapFunctional t u z =
        tapFunctional t u
          (tapPolyRem (tapPolyMul 1 z) (2 ^ t + b))
      rw [tapPolyMulOneLeft, tapPolyRemSmall t b z hb hz]
  | succ k ih =>
      change
        tapFunctional t
          (recStep t (fun j => Nat.testBit b j)
            (recIter t (fun j => Nat.testBit b j) k u)) z =
        tapFunctional t u
          (tapMulr t b (tapPolyPow 2 (k + 1)) z)
      rw [tapRecStepFunctional t b ht hb _ z hz]
      have hbound :
          tapMulr t b 2 z < 2 ^ t :=
        tapPolyRemBelow t b (tapPolyMul 2 z) hb
      rw [ih (tapMulr t b 2 z) hbound]
      change
        tapFunctional t u
          (tapPolyRem
            (tapPolyMul (tapPolyPow 2 k)
              (tapPolyRem (tapPolyMul 2 z) (2 ^ t + b)))
            (2 ^ t + b)) =
        tapFunctional t u
          (tapPolyRem
            (tapPolyMul (tapPolyPow 2 (k + 1)) z)
            (2 ^ t + b))
      rw [tapPolyRemMulRight (tapPolyPow 2 k)
        (tapPolyMul 2 z) (2 ^ t + b) hf]
      rw [← tapPolyMulAssociative]
      rfl

private theorem tapPolyPowAdd (a i j : Nat) :
    tapPolyPow a (i + j) =
      tapPolyMul (tapPolyPow a i) (tapPolyPow a j) := by
  induction j with
  | zero =>
      simp only [Nat.add_zero]
      change tapPolyPow a i = tapPolyMul (tapPolyPow a i) 1
      exact (tapPolyMulOneRight _).symm
  | succ j ih =>
      rw [Nat.add_succ]
      change
        tapPolyMul (tapPolyPow a (i + j)) a =
        tapPolyMul (tapPolyPow a i)
          (tapPolyMul (tapPolyPow a j) a)
      rw [ih, tapPolyMulAssociative]

private theorem tapMulrPower (t b i j : Nat) :
    tapMulr t b
        (tapPolyRem (tapPolyPow 2 i) (2 ^ t + b))
        (tapPolyRem (tapPolyPow 2 j) (2 ^ t + b)) =
      tapPolyRem (tapPolyPow 2 (i + j)) (2 ^ t + b) := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hpositive := Nat.two_pow_pos t
    omega
  change
    tapPolyRem
      (tapPolyMul
        (tapPolyRem (tapPolyPow 2 i) (2 ^ t + b))
        (tapPolyRem (tapPolyPow 2 j) (2 ^ t + b)))
      (2 ^ t + b) =
    tapPolyRem (tapPolyPow 2 (i + j)) (2 ^ t + b)
  calc
    tapPolyRem
      (tapPolyMul
        (tapPolyRem (tapPolyPow 2 i) (2 ^ t + b))
        (tapPolyRem (tapPolyPow 2 j) (2 ^ t + b)))
      (2 ^ t + b) =
      tapPolyRem
        (tapPolyMul (tapPolyPow 2 i)
          (tapPolyRem (tapPolyPow 2 j) (2 ^ t + b)))
        (2 ^ t + b) :=
      tapPolyRemMulLeft _ _ _ hf
    _ = tapPolyRem
        (tapPolyMul (tapPolyPow 2 i) (tapPolyPow 2 j))
        (2 ^ t + b) :=
      tapPolyRemMulRight _ _ _ hf
    _ = tapPolyRem (tapPolyPow 2 (i + j)) (2 ^ t + b) := by
      rw [tapPolyPowAdd]

private theorem tapMulrZeroBounded (t b z : Nat)
    (hb : b < 2 ^ t) :
    tapMulr t b 0 z = 0 := by
  change tapPolyRem (tapPolyMul 0 z) (2 ^ t + b) = 0
  rw [tapPolyMulZeroLeft]
  exact tapPolyRemSmall t b 0 hb (Nat.two_pow_pos t)

private theorem tapMulrOneBounded (t b z : Nat)
    (hb : b < 2 ^ t) (hz : z < 2 ^ t) :
    tapMulr t b 1 z = z := by
  change tapPolyRem (tapPolyMul 1 z) (2 ^ t + b) = z
  rw [tapPolyMulOneLeft]
  exact tapPolyRemSmall t b z hb hz

private theorem tapMulrAssoc (t b a c d : Nat) :
    tapMulr t b (tapMulr t b a c) d =
      tapMulr t b a (tapMulr t b c d) := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hpositive := Nat.two_pow_pos t
    omega
  change
    tapPolyRem
      (tapPolyMul (tapPolyRem (tapPolyMul a c) (2 ^ t + b)) d)
      (2 ^ t + b) =
    tapPolyRem
      (tapPolyMul a (tapPolyRem (tapPolyMul c d) (2 ^ t + b)))
      (2 ^ t + b)
  calc
    tapPolyRem
      (tapPolyMul (tapPolyRem (tapPolyMul a c) (2 ^ t + b)) d)
      (2 ^ t + b) =
    tapPolyRem (tapPolyMul (tapPolyMul a c) d) (2 ^ t + b) :=
      tapPolyRemMulLeft _ _ _ hf
    _ = tapPolyRem (tapPolyMul a (tapPolyMul c d)) (2 ^ t + b) := by
      rw [tapPolyMulAssociative]
    _ = tapPolyRem
      (tapPolyMul a (tapPolyRem (tapPolyMul c d) (2 ^ t + b)))
      (2 ^ t + b) :=
      (tapPolyRemMulRight _ _ _ hf).symm

private theorem tapMulrPowerNonzero (t b m i : Nat)
    (hb : b < 2 ^ t)
    (hm : tapPolyRem (tapPolyPow 2 m) (2 ^ t + b) = 1)
    (hi : i < m) :
    tapPolyRem (tapPolyPow 2 i) (2 ^ t + b) ≠ 0 := by
  intro hzero
  have hindex : i + (m - i) = m := by omega
  have hprod := tapMulrPower t b i (m - i)
  rw [hzero, tapMulrZeroBounded t b _ hb,
    hindex, hm] at hprod
  cases hprod

private theorem tapMulrPowersDistinctStrict (t b m i j : Nat)
    (hb : b < 2 ^ t)
    (hm : tapPolyRem (tapPolyPow 2 m) (2 ^ t + b) = 1)
    (hord : ∀ k : Nat, 0 < k → k < m →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1)
    (hij : i < j) (hj : j < m) :
    tapPolyRem (tapPolyPow 2 i) (2 ^ t + b) ≠
      tapPolyRem (tapPolyPow 2 j) (2 ^ t + b) := by
  intro heq
  have hmul := congrArg
    (fun a => tapMulr t b a
      (tapPolyRem (tapPolyPow 2 (m - j)) (2 ^ t + b))) heq
  rw [tapMulrPower t b i (m - j),
    tapMulrPower t b j (m - j)] at hmul
  have hlast : j + (m - j) = m := by omega
  rw [hlast, hm] at hmul
  have hlo : 0 < i + (m - j) := by omega
  have hhi : i + (m - j) < m := by omega
  exact hord (i + (m - j)) hlo hhi hmul

private theorem tapMulrPowersInjective (t b m i j : Nat)
    (hb : b < 2 ^ t)
    (hm : tapPolyRem (tapPolyPow 2 m) (2 ^ t + b) = 1)
    (hord : ∀ k : Nat, 0 < k → k < m →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1)
    (hi : i < m) (hj : j < m)
    (heq : tapPolyRem (tapPolyPow 2 i) (2 ^ t + b) =
      tapPolyRem (tapPolyPow 2 j) (2 ^ t + b)) :
    i = j := by
  by_cases hij : i < j
  · exact False.elim
      (tapMulrPowersDistinctStrict t b m i j hb hm hord hij hj heq)
  · by_cases hji : j < i
    · exact False.elim
        (tapMulrPowersDistinctStrict t b m j i hb hm hord
          hji hi heq.symm)
    · omega

private theorem tapPowersMapNodup (t b m : Nat)
    (hb : b < 2 ^ t)
    (hm : tapPolyRem (tapPolyPow 2 m) (2 ^ t + b) = 1)
    (hord : ∀ k : Nat, 0 < k → k < m →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1) :
    ∀ l : List Nat, l.Nodup →
      (∀ i, i ∈ l → i < m) →
      (l.map (fun i =>
        tapPolyRem (tapPolyPow 2 i) (2 ^ t + b))).Nodup := by
  intro l
  induction l with
  | nil =>
      intro _ _
      exact List.nodup_nil
  | cons i is ih =>
      intro hn hrange
      have hi : i < m := hrange i (by simp)
      have his : i ∉ is := (List.nodup_cons.mp hn).1
      have hNoTail : is.Nodup := (List.nodup_cons.mp hn).2
      have hRangeTail : ∀ j, j ∈ is → j < m := by
        intro j hj
        exact hrange j (List.mem_cons_of_mem i hj)
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨j, hj, hpow⟩ := List.mem_map.mp hmem
        have hij : i = j := tapMulrPowersInjective t b m i j
          hb hm hord hi (hRangeTail j hj) hpow.symm
        exact his (hij ▸ hj)
      · exact ih hNoTail hRangeTail

private theorem tapSplitAtMember {a : Nat} {ys : List Nat}
    (ha : a ∈ ys) :
    ∃ pre post : List Nat, ys = pre ++ a :: post := by
  induction ys with
  | nil =>
      cases ha
  | cons y ys ih =>
      rcases List.mem_cons.mp ha with hy | htail
      · subst y
        exact ⟨[], ys, rfl⟩
      · obtain ⟨pre, post, heq⟩ := ih htail
        exact ⟨y :: pre, post, by rw [heq]; rfl⟩

private theorem tapNodupSubsetLength :
    ∀ (xs ys : List Nat), xs.Nodup →
      (∀ a : Nat, a ∈ xs → a ∈ ys) →
      xs.length ≤ ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _
      exact Nat.zero_le _
  | cons a xs ih =>
      intro ys hn hsubset
      have ha : a ∈ ys := hsubset a (by simp)
      obtain ⟨pre, post, heq⟩ := tapSplitAtMember ha
      have hnot : a ∉ xs := (List.nodup_cons.mp hn).1
      have htailSubset : ∀ z : Nat, z ∈ xs → z ∈ pre ++ post := by
        intro z hz
        have hzy : z ∈ pre ++ a :: post := by
          rw [← heq]
          exact hsubset z (List.mem_cons_of_mem a hz)
        have hzne : z ≠ a := by
          intro heqza
          exact hnot (heqza ▸ hz)
        rcases List.mem_append.mp hzy with hp | ht
        · exact List.mem_append.mpr (Or.inl hp)
        · rcases List.mem_cons.mp ht with hhead | hpost
          · exact False.elim (hzne hhead)
          · exact List.mem_append.mpr (Or.inr hpost)
      have hlen := ih (pre ++ post)
        (List.nodup_cons.mp hn).2 htailSubset
      rw [heq]
      simp only [List.length_cons, List.length_append] at hlen ⊢
      omega

private theorem tapPowersExhaustAux (t b m p : Nat)
    (hb : b < 2 ^ t) (hcount : m + 1 = 2 ^ t)
    (hm : tapPolyRem (tapPolyPow 2 m) (2 ^ t + b) = 1)
    (hord : ∀ k : Nat, 0 < k → k < m →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1)
    (hp : 0 < p) (hbound : p < 2 ^ t) :
    ∃ i : Nat, i < m ∧
      tapPolyRem (tapPolyPow 2 i) (2 ^ t + b) = p := by
  have hRange : ∀ i : Nat, i ∈ List.range m → i < m := by
    intro i hi
    exact List.mem_range.mp hi
  have hPowersNo :
      ((List.range m).map
        (fun i => tapPolyRem (tapPolyPow 2 i) (2 ^ t + b))).Nodup :=
    tapPowersMapNodup t b m hb hm hord _
      List.nodup_range hRange
  have hNonzeroMember : ∀ z : Nat,
      0 < z → z < 2 ^ t →
      z ∈ (List.range m).map (fun i => i + 1) := by
    intro z hz hzlt
    apply List.mem_map.mpr
    refine ⟨z - 1, List.mem_range.mpr (by omega), ?_⟩
    omega
  have hPowersSubset : ∀ z : Nat,
      z ∈ (List.range m).map
        (fun i => tapPolyRem (tapPolyPow 2 i) (2 ^ t + b)) →
      z ∈ (List.range m).map (fun i => i + 1) := by
    intro z hz
    obtain ⟨i, hi, hpow⟩ := List.mem_map.mp hz
    have hilt : i < m := List.mem_range.mp hi
    have hnz : z ≠ 0 := by
      intro heq
      have hbad :
          tapPolyRem (tapPolyPow 2 i) (2 ^ t + b) = 0 :=
        hpow.trans heq
      exact tapMulrPowerNonzero t b m i hb hm hilt hbad
    have hzpos : 0 < z := Nat.pos_of_ne_zero hnz
    have hzlt : z < 2 ^ t := by
      rw [← hpow]
      exact tapPolyRemBelow t b (tapPolyPow 2 i) hb
    exact hNonzeroMember z hzpos hzlt
  by_cases hmem : p ∈ (List.range m).map
      (fun i => tapPolyRem (tapPolyPow 2 i) (2 ^ t + b))
  · obtain ⟨i, hi, heq⟩ := List.mem_map.mp hmem
    exact ⟨i, List.mem_range.mp hi, heq⟩
  · have hBigNo :
        (p :: (List.range m).map
          (fun i =>
            tapPolyRem (tapPolyPow 2 i) (2 ^ t + b))).Nodup :=
      List.nodup_cons.mpr ⟨hmem, hPowersNo⟩
    have hBigSubset : ∀ z : Nat,
        z ∈ p :: (List.range m).map
          (fun i =>
            tapPolyRem (tapPolyPow 2 i) (2 ^ t + b)) →
        z ∈ (List.range m).map (fun i => i + 1) := by
      intro z hz
      rcases List.mem_cons.mp hz with heq | ht
      · rw [heq]
        exact hNonzeroMember p hp hbound
      · exact hPowersSubset z ht
    have hlen := tapNodupSubsetLength
      (p :: (List.range m).map
        (fun i => tapPolyRem (tapPolyPow 2 i) (2 ^ t + b)))
      ((List.range m).map (fun i => i + 1))
      hBigNo hBigSubset
    simp only [List.length_cons, List.length_map, List.length_range] at hlen
    omega

/-- Exact order forces all M distinct nonzero power masks to exhaust
the reduced nonzero masks, without irreducibility.
Consumer: PrimitiveTapSelection and tapResidueUnit. -/
theorem tapPowersExhaust (t b : Nat)
    (ht : 2 ≤ t) (hb : b < 2 ^ t)
    (hM : tapPolyRem
      (tapPolyPow 2 (2 ^ t - 1)) (2 ^ t + b) = 1)
    (hord : ∀ k : Nat, 0 < k → k < 2 ^ t - 1 →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1) :
    (∀ i : Nat, i < 2 ^ t - 1 →
      tapPolyRem (tapPolyPow 2 i) (2 ^ t + b) ≠ 0) ∧
    (∀ i j : Nat, i < 2 ^ t - 1 → j < 2 ^ t - 1 →
      i ≠ j →
      tapPolyRem (tapPolyPow 2 i) (2 ^ t + b) ≠
        tapPolyRem (tapPolyPow 2 j) (2 ^ t + b)) ∧
    (∀ p : Nat, 0 < p → p < 2 ^ t →
      ∃ i : Nat, i < 2 ^ t - 1 ∧
        tapPolyRem (tapPolyPow 2 i) (2 ^ t + b) = p) := by
  have hcount : (2 ^ t - 1) + 1 = 2 ^ t := by
    have hpositive := Nat.two_pow_pos t
    omega
  constructor
  · intro i hi
    exact tapMulrPowerNonzero t b (2 ^ t - 1) i hb hM hi
  constructor
  · intro i j hi hj hne heq
    exact hne
      (tapMulrPowersInjective t b (2 ^ t - 1) i j
        hb hM hord hi hj heq)
  · intro p hp hbound
    exact tapPowersExhaustAux t b (2 ^ t - 1) p
      hb hcount hM hord hp hbound

#print axioms L3.tapPowersExhaust

/-- Every nonzero reduced mask has an explicit multiplicative
inverse represented by a reduced mask. No irreducibility assumption.
Consumer: PrimitiveTapSelection and tapPrimitiveOfOrder. -/
theorem tapResidueUnit (t b : Nat)
    (ht : 2 ≤ t) (hb : b < 2 ^ t)
    (hM : tapPolyRem
      (tapPolyPow 2 (2 ^ t - 1)) (2 ^ t + b) = 1)
    (hord : ∀ k : Nat, 0 < k → k < 2 ^ t - 1 →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1)
    (p : Nat) (hp : 0 < p) (hbound : p < 2 ^ t) :
    ∃ q : Nat, q < 2 ^ t ∧ tapMulr t b p q = 1 := by
  obtain ⟨i, hi, heq⟩ :=
    (tapPowersExhaust t b ht hb hM hord).2.2 p hp hbound
  refine ⟨tapPolyRem
    (tapPolyPow 2 ((2 ^ t - 1) - i)) (2 ^ t + b),
    tapPolyRemBelow t b
      (tapPolyPow 2 ((2 ^ t - 1) - i)) hb, ?_⟩
  rw [← heq, tapMulrPower]
  have hindex : i + ((2 ^ t - 1) - i) = 2 ^ t - 1 := by
    omega
  rw [hindex]
  exact hM

private theorem tapPowerActsAsOne (t b m z : Nat)
    (hb : b < 2 ^ t)
    (hm : tapPolyRem (tapPolyPow 2 m) (2 ^ t + b) = 1)
    (hz : z < 2 ^ t) :
    tapMulr t b (tapPolyPow 2 m) z = z := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hpositive := Nat.two_pow_pos t
    omega
  change
    tapPolyRem (tapPolyMul (tapPolyPow 2 m) z) (2 ^ t + b) = z
  calc
    tapPolyRem (tapPolyMul (tapPolyPow 2 m) z) (2 ^ t + b) =
      tapPolyRem
        (tapPolyMul
          (tapPolyRem (tapPolyPow 2 m) (2 ^ t + b)) z)
        (2 ^ t + b) :=
      (tapPolyRemMulLeft _ _ _ hf).symm
    _ = tapPolyRem (tapPolyMul 1 z) (2 ^ t + b) := by
      rw [hm]
    _ = z := by
      rw [tapPolyMulOneLeft]
      exact tapPolyRemSmall t b z hb hz

private theorem tapPowerPlusOneAction (t b k z : Nat)
    (hb : b < 2 ^ t) (hz : z < 2 ^ t) :
    tapMulr t b
      (tapPolyAdd
        (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1) z =
    tapPolyAdd (tapMulr t b (tapPolyPow 2 k) z) z := by
  have hf : 2 ^ t + b ≠ 0 := by
    have hpositive := Nat.two_pow_pos t
    omega
  change
    tapPolyRem
      (tapPolyMul
        (tapPolyAdd (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1)
        z) (2 ^ t + b) =
    tapPolyAdd
      (tapPolyRem (tapPolyMul (tapPolyPow 2 k) z) (2 ^ t + b)) z
  have hx : tapPolyMul
      (tapPolyAdd (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1) z =
      tapPolyAdd
        (tapPolyMul (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) z)
        (tapPolyMul 1 z) := tapPolyMulXorLeft _ _ _
  rw [hx, tapPolyRemAdd _ _ (2 ^ t + b) hf]
  rw [tapPolyRemMulLeft (tapPolyPow 2 k) z (2 ^ t + b) hf]
  rw [tapPolyMulOneLeft, tapPolyRemSmall t b z hb hz]

/-- The two order clauses imply IsPrimitive of the original
recStep/recIter protocol, for every nonzero Boolean state.
Consumer: PrimitiveTapSelection. -/
theorem tapPrimitiveOfOrder (t b : Nat)
    (ht : 2 ≤ t) (hb : b < 2 ^ t) (hodd : b % 2 = 1)
    (hM : tapPolyRem
      (tapPolyPow 2 (2 ^ t - 1)) (2 ^ t + b) = 1)
    (hord : ∀ k : Nat, 0 < k → k < 2 ^ t - 1 →
      tapPolyRem (tapPolyPow 2 k) (2 ^ t + b) ≠ 1) :
    IsPrimitive t (fun j => Nat.testBit b j) := by
  intro u hnonzero
  constructor
  · funext j
    have hle : 2 ^ (j.val + 1) ≤ 2 ^ t :=
      Nat.pow_le_pow_of_le (by decide : 1 < (2 : Nat))
        (by omega)
    have hpositive := Nat.two_pow_pos j.val
    have hbitbound : 2 ^ j.val < 2 ^ t := by
      rw [Nat.pow_succ] at hle
      omega
    have hiter := tapRecIterFunctional t b ht hb
      (2 ^ t - 1) u (2 ^ j.val) hbitbound
    have hacted := tapPowerActsAsOne t b (2 ^ t - 1)
      (2 ^ j.val) hb hM hbitbound
    rw [hacted] at hiter
    rw [tapFunctionalBit t
        (recIter t (fun i => Nat.testBit b i) (2 ^ t - 1) u)
        j.val j.isLt,
      tapFunctionalBit t u j.val j.isLt] at hiter
    exact hiter
  · intro k hk hkm hreturn
    have hone : 1 < 2 ^ t := by
      have hle : 2 ^ 2 ≤ 2 ^ t :=
        Nat.pow_le_pow_of_le (by decide : 1 < (2 : Nat)) ht
      omega
    have haNe :
        tapPolyAdd
          (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1 ≠ 0 := by
      intro hzero
      have heq :=
        (tapPolyAddEqZeroIff
          (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1).1 hzero
      exact hord k hk hkm heq
    have haPos :
        0 < tapPolyAdd
          (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1 :=
      Nat.pos_of_ne_zero haNe
    have haBelow :
        tapPolyAdd
          (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1 <
          2 ^ t :=
      tapPolyAddBelow _ _ t
        (tapPolyRemBelow t b (tapPolyPow 2 k) hb) hone
    obtain ⟨q, hqBelow, hqUnit⟩ :=
      tapResidueUnit t b ht hb hM hord
        (tapPolyAdd
          (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1)
        haPos haBelow
    have hvanish : ∀ p : Nat, p < 2 ^ t →
        tapFunctional t u p = false := by
      intro p hp
      have hz :
          tapMulr t b q p < 2 ^ t :=
        tapPolyRemBelow t b (tapPolyMul q p) hb
      have hiter := tapRecIterFunctional t b ht hb k u
        (tapMulr t b q p) hz
      rw [hreturn] at hiter
      have hzero :
          tapFunctional t u
            (tapMulr t b
              (tapPolyAdd
                (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1)
              (tapMulr t b q p)) = false := by
        rw [tapPowerPlusOneAction t b k (tapMulr t b q p)
          hb hz]
        rw [tapFunctionalAdd]
        rw [← hiter]
        exact Bool.xor_self _
      have hreduce :
          tapMulr t b
            (tapPolyAdd
              (tapPolyRem (tapPolyPow 2 k) (2 ^ t + b)) 1)
            (tapMulr t b q p) = p := by
        rw [← tapMulrAssoc, hqUnit]
        exact tapMulrOneBounded t b p hb hp
      rw [hreduce] at hzero
      exact hzero
    obtain ⟨j, hj⟩ := hnonzero
    exact (tapFunctionalZero t u hvanish j) hj

#print axioms L3.tapPrimitiveOfOrder

end L3

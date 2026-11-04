import Leader.L3.Primitive.Field

namespace L3.TapField

set_option autoImplicit false

open Classical

variable {F : Type}

/-- Function iteration, `Nat.iterate T n x = T (T (... x))`; core Lean 4 has no such constant.
Consumer: functionPeriodGcd and unitPeriodGcd. -/
def Nat.iterate {α : Type} (op : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => Nat.iterate op n (op a)

namespace BinaryField

/-- Powers used by PrimitiveFieldGenerator and PrimitiveIrreducibleExistence. -/
def pow (K : BinaryField F) (a : F) : Nat → F
  | 0 => K.one
  | n + 1 => K.mul (pow K a n) a

/-- Right multiplicative identity; consumer PrimitiveFieldGenerator. -/
theorem mul_one (K : BinaryField F) (a : F) :
    K.mul a K.one = a := by
  rw [K.mul_comm]
  exact K.one_mul a

/-- Right additive identity; consumer PrimitiveIrreducibleExistence. -/
theorem add_zero (K : BinaryField F) (a : F) :
    K.add a K.zero = a := by
  rw [K.add_comm]
  exact K.zero_add a

/-- Doubling a sum by the same term cancels; consumer PrimitiveFieldGenerator. -/
private theorem add_cancel_self (K : BinaryField F) (a b : F) :
    K.add a (K.add a b) = b := by
  rw [← K.add_assoc, K.add_self, K.zero_add]

/-- Interleaved repeated terms cancel; consumer PrimitiveAbstractField.rootBound. -/
private theorem add_interleave (K : BinaryField F) (a b c : F) :
    K.add (K.add a b) (K.add b c) = K.add a c := by
  rw [K.add_assoc, add_cancel_self]

/-- Interchange adjacent addends; consumer the synthetic-division identity. -/
private theorem add_left_comm (K : BinaryField F) (a b c : F) :
    K.add a (K.add b c) = K.add b (K.add a c) := by
  calc
    K.add a (K.add b c) = K.add (K.add a b) c :=
      (K.add_assoc a b c).symm
    _ = K.add (K.add b a) c := by rw [K.add_comm a b]
    _ = K.add b (K.add a c) := K.add_assoc b a c

/-- Interchange adjacent factors; consumer PrimitiveAbstractField.rootBound. -/
private theorem mul_left_comm (K : BinaryField F) (a b c : F) :
    K.mul a (K.mul b c) = K.mul b (K.mul a c) := by
  calc
    K.mul a (K.mul b c) = K.mul (K.mul a b) c :=
      (K.mul_assoc a b c).symm
    _ = K.mul (K.mul b a) c := by rw [K.mul_comm a b]
    _ = K.mul b (K.mul a c) := K.mul_assoc b a c

/-- Multiplication annihilates zero on the right; consumer PrimitiveMaskQuotient. -/
theorem mul_zero (K : BinaryField F) (a : F) :
    K.mul a K.zero = K.zero := by
  have h := K.left_distrib a K.zero K.zero
  rw [K.add_self] at h
  exact h.trans (K.add_self _)

/-- Multiplication annihilates zero on the left; consumer PrimitiveMaskQuotient. -/
theorem zero_mul (K : BinaryField F) (a : F) :
    K.mul K.zero a = K.zero := by
  rw [K.mul_comm]
  exact mul_zero K a

/-- Distribution in the left argument; consumer PrimitiveMaskQuotient. -/
theorem right_distrib (K : BinaryField F) (a b c : F) :
    K.mul (K.add a b) c =
      K.add (K.mul a c) (K.mul b c) := by
  calc
    K.mul (K.add a b) c = K.mul c (K.add a b) :=
      K.mul_comm _ _
    _ = K.add (K.mul c a) (K.mul c b) :=
      K.left_distrib c a b
    _ = K.add (K.mul a c) (K.mul b c) := by
      rw [K.mul_comm c a, K.mul_comm c b]

/-- Characteristic-two sum is zero exactly for equal terms;
consumer PrimitiveIrreducibleExistence. -/
theorem add_eq_zero_iff (K : BinaryField F) (a b : F) :
    K.add a b = K.zero ↔ a = b := by
  constructor
  · intro h
    calc
      a = K.add a K.zero := (add_zero K a).symm
      _ = K.add a (K.add a b) := by rw [h]
      _ = K.add (K.add a a) b :=
        (K.add_assoc a a b).symm
      _ = b := by rw [K.add_self, K.zero_add]
  · intro h
    rw [h]
    exact K.add_self b

/-- No nontrivial zero divisors; consumer rootBound and PrimitiveFieldGenerator. -/
theorem mul_eq_zero (K : BinaryField F) (a b : F)
    (h : K.mul a b = K.zero) : a = K.zero ∨ b = K.zero := by
  by_cases ha : a = K.zero
  · exact Or.inl ha
  · right
    have hi : K.mul (K.inv a) a = K.one := by
      rw [K.mul_comm]
      exact K.mul_inv a ha
    calc
      b = K.mul K.one b := (K.one_mul b).symm
      _ = K.mul (K.mul (K.inv a) a) b := by rw [hi]
      _ = K.mul (K.inv a) (K.mul a b) :=
        K.mul_assoc (K.inv a) a b
      _ = K.mul (K.inv a) K.zero := by rw [h]
      _ = K.zero := mul_zero K _

/-- Cancel a nonzero multiplier; consumer PrimitiveFieldGenerator. -/
theorem mul_left_cancel (K : BinaryField F) (a b c : F)
    (ha : a ≠ K.zero) (h : K.mul a b = K.mul a c) : b = c := by
  have hi : K.mul (K.inv a) a = K.one := by
    rw [K.mul_comm]
    exact K.mul_inv a ha
  calc
    b = K.mul K.one b := (K.one_mul b).symm
    _ = K.mul (K.mul (K.inv a) a) b := by rw [hi]
    _ = K.mul (K.inv a) (K.mul a b) :=
      K.mul_assoc (K.inv a) a b
    _ = K.mul (K.inv a) (K.mul a c) := by rw [h]
    _ = K.mul (K.mul (K.inv a) a) c :=
      (K.mul_assoc (K.inv a) a c).symm
    _ = K.mul K.one c := by rw [hi]
    _ = c := K.one_mul c

/-- Reassociate four factors; consumer PrimitiveAbstractField.frobeniusAdd. -/
private theorem mul_four (K : BinaryField F) (a b c d : F) :
    K.mul (K.mul a b) (K.mul c d) =
      K.mul (K.mul a c) (K.mul b d) := by
  calc
    K.mul (K.mul a b) (K.mul c d) =
        K.mul a (K.mul b (K.mul c d)) :=
      K.mul_assoc a b (K.mul c d)
    _ = K.mul a (K.mul c (K.mul b d)) := by
      rw [← K.mul_assoc b c d, K.mul_comm b c, K.mul_assoc c b d]
    _ = K.mul (K.mul a c) (K.mul b d) :=
      (K.mul_assoc a c (K.mul b d)).symm

/-- Exponent addition; consumer PrimitiveFieldGenerator. -/
theorem pow_add (K : BinaryField F) (a : F) (m n : Nat) :
    pow K a (m + n) = K.mul (pow K a m) (pow K a n) := by
  induction n with
  | zero =>
      change pow K a m = K.mul (pow K a m) K.one
      exact (mul_one K _).symm
  | succ n ih =>
      calc
        pow K a (m + (n + 1)) =
            K.mul (pow K a (m + n)) a := by
          rw [Nat.add_succ]
          rfl
        _ = K.mul (K.mul (pow K a m) (pow K a n)) a := by
          rw [ih]
        _ = K.mul (pow K a m) (K.mul (pow K a n) a) :=
          K.mul_assoc _ _ _
        _ = K.mul (pow K a m) (pow K a (n + 1)) := rfl

/-- Exponent multiplication; consumer PrimitiveFieldGenerator. -/
theorem pow_mul (K : BinaryField F) (a : F) (m n : Nat) :
    pow K a (m * n) = pow K (pow K a m) n := by
  induction n with
  | zero =>
      simp only [Nat.mul_zero]
      rfl
  | succ n ih =>
      calc
        pow K a (m * (n + 1)) =
            pow K a (m * n + m) := by rw [Nat.mul_succ]
        _ = K.mul (pow K a (m * n)) (pow K a m) :=
          pow_add K a (m * n) m
        _ = K.mul (pow K (pow K a m) n) (pow K a m) := by rw [ih]
        _ = pow K (pow K a m) (n + 1) := rfl

/-- One is fixed by every power; consumer PrimitiveFieldGenerator. -/
theorem one_pow (K : BinaryField F) (n : Nat) :
    pow K K.one n = K.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change K.mul (pow K K.one n) K.one = K.one
      rw [ih, K.one_mul]

/-- Product powers distribute in a commutative field;
consumer PrimitiveFieldGenerator. -/
theorem mul_pow (K : BinaryField F) (a b : F) (n : Nat) :
    pow K (K.mul a b) n = K.mul (pow K a n) (pow K b n) := by
  induction n with
  | zero =>
      change K.one = K.mul K.one K.one
      exact (K.one_mul K.one).symm
  | succ n ih =>
      calc
        pow K (K.mul a b) (n + 1) =
            K.mul (pow K (K.mul a b) n) (K.mul a b) := rfl
        _ = K.mul (K.mul (pow K a n) (pow K b n))
            (K.mul a b) := by rw [ih]
        _ = K.mul (K.mul (pow K a n) a)
            (K.mul (pow K b n) b) :=
          mul_four K (pow K a n) (pow K b n) a b
        _ = K.mul (pow K a (n + 1)) (pow K b (n + 1)) := rfl

/-- Powers of nonzero elements remain nonzero;
consumer PrimitiveFieldGenerator. -/
theorem pow_ne_zero (K : BinaryField F) (a : F) (ha : a ≠ K.zero)
    (n : Nat) : pow K a n ≠ K.zero := by
  induction n with
  | zero => exact K.one_ne_zero
  | succ n ih =>
      change K.mul (pow K a n) a ≠ K.zero
      intro hz
      rcases mul_eq_zero K _ _ hz with hzero | hzero
      · exact ih hzero
      · exact ha hzero

/-- A convenient square identity; consumer PrimitiveIrreducibleExistence. -/
private theorem pow_two (K : BinaryField F) (a : F) :
    pow K a 2 = K.mul a a := by
  calc
    pow K a 2 = K.mul (K.mul K.one a) a := rfl
    _ = K.mul a a := by rw [K.one_mul]

/-- A convenient first-power identity; consumer PrimitiveFieldGenerator. -/
private theorem pow_one (K : BinaryField F) (a : F) :
    pow K a 1 = a := by
  change K.mul K.one a = a
  exact K.one_mul a

end BinaryField

/-- Low-degree-first Horner evaluation; consumer PrimitiveIrreducibleExistence. -/
def polyEval (K : BinaryField F) : List F → F → F
  | [], _ => K.zero
  | c :: cs, a => K.add c (K.mul a (polyEval K cs a))

/-- Characteristic-two Horner synthetic quotient.
Consumer: PrimitiveIrreducibleExistence through rootBound. -/
def syntheticQuot (K : BinaryField F) (a : F) : List F → List F
  | [] => []
  | [_] => []
  | _ :: d :: ds =>
      polyEval K (d :: ds) a :: syntheticQuot K a (d :: ds)

/-- The quotient has one fewer coefficient.
Consumer: PrimitiveIrreducibleExistence.rootBound. -/
private theorem syntheticQuot_length (K : BinaryField F) (a : F) :
    ∀ P : List F, P ≠ [] →
      (syntheticQuot K a P).length + 1 = P.length := by
  intro P
  induction P with
  | nil =>
      intro hn
      exact False.elim (hn rfl)
  | cons c cs ih =>
      cases cs with
      | nil =>
          intro _
          rfl
      | cons d ds =>
          intro _
          have htail := ih (by simp)
          change
            (polyEval K (d :: ds) a ::
              syntheticQuot K a (d :: ds)).length + 1 =
            (c :: d :: ds).length
          simp only [List.length_cons] at htail ⊢
          omega

/-- The highest coefficient is unchanged under synthetic division.
Consumer: PrimitiveIrreducibleExistence.rootBound. -/
private theorem syntheticQuot_last (K : BinaryField F) (a : F) :
    ∀ P : List F, 1 < P.length →
      (syntheticQuot K a P).getLast? = P.getLast? := by
  intro P
  induction P with
  | nil =>
      intro h
      simp at h
  | cons c cs ih =>
      cases cs with
      | nil =>
          intro h
          simp at h
      | cons d ds =>
          cases ds with
          | nil =>
              intro _
              simp [syntheticQuot, polyEval,
                BinaryField.mul_zero, BinaryField.add_zero]
          | cons e es =>
              intro _
              have htail := ih (by simp)
              simpa [syntheticQuot] using htail

/-- The characteristic-two algebra of Horner division.
Consumer: PrimitiveIrreducibleExistence.rootBound. -/
private theorem syntheticAlgebra (K : BinaryField F)
    (c r q a x : F) :
    K.add c (K.mul x
      (K.add r (K.mul (K.add x a) q))) =
    K.add (K.add c (K.mul a r))
      (K.mul (K.add x a) (K.add r (K.mul x q))) := by
  simp only [K.left_distrib, BinaryField.right_distrib]
  simp [K.mul_assoc, K.mul_comm, BinaryField.mul_left_comm,
    K.add_assoc, K.add_comm, BinaryField.add_left_comm,
    K.add_self, K.zero_add, BinaryField.add_zero,
    BinaryField.add_cancel_self]

/-- Characteristic-two synthetic-division identity, before setting
the root evaluation to zero. Consumer: PrimitiveIrreducibleExistence. -/
private theorem syntheticIdentity (K : BinaryField F) :
    ∀ P : List F, ∀ a x : F,
      polyEval K P x =
        K.add (polyEval K P a)
          (K.mul (K.add x a)
            (polyEval K (syntheticQuot K a P) x)) := by
  intro P
  induction P with
  | nil =>
      intro a x
      change K.zero =
        K.add K.zero (K.mul (K.add x a) K.zero)
      rw [BinaryField.mul_zero, K.zero_add]
  | cons c cs ih =>
      intro a x
      cases cs with
      | nil =>
          change K.add c (K.mul x K.zero) =
            K.add (K.add c (K.mul a K.zero))
              (K.mul (K.add x a) K.zero)
          simp only [BinaryField.mul_zero, BinaryField.add_zero]
      | cons d ds =>
          calc
            polyEval K (c :: d :: ds) x =
                K.add c (K.mul x
                  (K.add (polyEval K (d :: ds) a)
                    (K.mul (K.add x a)
                      (polyEval K (syntheticQuot K a (d :: ds)) x)))) := by
              change K.add c (K.mul x (polyEval K (d :: ds) x)) = _
              rw [ih a x]
            _ = K.add (polyEval K (c :: d :: ds) a)
                (K.mul (K.add x a)
                  (polyEval K (syntheticQuot K a (c :: d :: ds)) x)) := by
              change K.add c (K.mul x
                  (K.add (polyEval K (d :: ds) a)
                    (K.mul (K.add x a)
                      (polyEval K (syntheticQuot K a (d :: ds)) x)))) =
                K.add (K.add c (K.mul a (polyEval K (d :: ds) a)))
                  (K.mul (K.add x a)
                    (K.add (polyEval K (d :: ds) a)
                      (K.mul x
                        (polyEval K (syntheticQuot K a (d :: ds)) x))))
              exact syntheticAlgebra K _ _ _ _ _

/-- A nonzero low-degree-first polynomial has at most its degree
many distinct roots. Consumer: PrimitiveIrreducibleExistence,
PrimitiveFieldGenerator. -/
theorem rootBound (K : BinaryField F) (P : List F) (c : F)
    (hLast : P.getLast? = some c) (hc : c ≠ K.zero)
    (L : List F) (hNo : L.Nodup)
    (hRoots : ∀ a, a ∈ L → polyEval K P a = K.zero) :
    L.length + 1 ≤ P.length := by
  have main : ∀ n : Nat, ∀ (P L : List F) (c : F),
      P.length = n → P.getLast? = some c → c ≠ K.zero →
      L.Nodup →
      (∀ a, a ∈ L → polyEval K P a = K.zero) →
      L.length + 1 ≤ P.length := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro P L c hLen hLast hc hNo hRoots
        cases L with
        | nil =>
            cases P with
            | nil => cases hLast
            | cons p ps =>
                simp only [List.length_nil, List.length_cons]
                omega
        | cons a rest =>
            have hRootA : polyEval K P a = K.zero :=
              hRoots a (by simp)
            have hPnonempty : P ≠ [] := by
              intro hp
              rw [hp] at hLast
              cases hLast
            have hPLong : 1 < P.length := by
              cases P with
              | nil => exact False.elim (hPnonempty rfl)
              | cons d ds =>
                  cases ds with
                  | nil =>
                      have hd : d = c := by simpa using hLast
                      have hroot : d = K.zero := by
                        simpa [polyEval, BinaryField.mul_zero,
                          BinaryField.add_zero] using hRootA
                      exact False.elim (hc (hd ▸ hroot))
                  | cons e es =>
                      simp only [List.length_cons]
                      omega
            have hQLen := syntheticQuot_length K a P hPnonempty
            have hQLast : (syntheticQuot K a P).getLast? = some c :=
              (syntheticQuot_last K a P hPLong).trans hLast
            have hQSmall : (syntheticQuot K a P).length < n := by omega
            have hRestNo : rest.Nodup := (List.nodup_cons.mp hNo).2
            have hNotMem : a ∉ rest := (List.nodup_cons.mp hNo).1
            have hQRoots : ∀ x, x ∈ rest →
                polyEval K (syntheticQuot K a P) x = K.zero := by
              intro x hx
              have hPx : polyEval K P x = K.zero :=
                hRoots x (by simp [hx])
              have hFactor := syntheticIdentity K P a x
              rw [hRootA, K.zero_add] at hFactor
              have hz : K.mul (K.add x a)
                  (polyEval K (syntheticQuot K a P) x) = K.zero :=
                hFactor.symm.trans hPx
              rcases BinaryField.mul_eq_zero K _ _ hz with hxa | hq
              · have heq : x = a :=
                  (BinaryField.add_eq_zero_iff K x a).1 hxa
                exact False.elim (hNotMem (heq ▸ hx))
              · exact hq
            have hShort := ih (syntheticQuot K a P).length hQSmall
              (syntheticQuot K a P) rest c rfl hQLast hc hRestNo hQRoots
            simp only [List.length_cons]
            omega
  exact main P.length P L c rfl hLast hc hNo hRoots

/-- Evaluation of the explicit monomial coefficient list.
Consumer: PrimitiveFieldGenerator and PrimitiveIrreducibleExistence. -/
private theorem polyEval_monomial (K : BinaryField F) (n : Nat) (a : F) :
    polyEval K (List.replicate n K.zero ++ [K.one]) a =
      BinaryField.pow K a n := by
  induction n with
  | zero =>
      change K.add K.one (K.mul a K.zero) = K.one
      rw [BinaryField.mul_zero, BinaryField.add_zero]
  | succ n ih =>
      change K.add K.zero
          (K.mul a (polyEval K (List.replicate n K.zero ++ [K.one]) a)) =
        K.mul (BinaryField.pow K a n) a
      rw [K.zero_add, ih, K.mul_comm]

/-- A list ending in an appended singleton has that last entry;
consumer rootBoundPowOne and rootBoundPowSelf. -/
private theorem getLast_cons_append_singleton (y x : F) (l : List F) :
    (y :: (l ++ [x])).getLast? = some x := by
  induction l generalizing y with
  | nil => rfl
  | cons z zs ih =>
      have := ih z
      simpa [List.getLast?_cons_cons] using this

/-- The explicit polynomial X^m + 1 bounds unit roots.
Consumer: PrimitiveFieldGenerator. -/
theorem rootBoundPowOne (K : BinaryField F) (m : Nat) (hm : 0 < m)
    (L : List F) (hNo : L.Nodup)
    (hRoots : ∀ a, a ∈ L → BinaryField.pow K a m = K.one) :
    L.length ≤ m := by
  have hLast :
      (K.one :: (List.replicate (m - 1) K.zero ++ [K.one])).getLast? =
        some K.one :=
    getLast_cons_append_singleton _ _ _
  have hRootsPoly : ∀ a, a ∈ L →
      polyEval K (K.one :: (List.replicate (m - 1) K.zero ++ [K.one])) a =
        K.zero := by
    intro a ha
    have hmRewrite : m - 1 + 1 = m := by omega
    have hpow : K.mul a (BinaryField.pow K a (m - 1)) =
        BinaryField.pow K a m := by
      rw [← hmRewrite]
      change K.mul a (BinaryField.pow K a (m - 1)) =
        K.mul (BinaryField.pow K a (m - 1)) a
      exact K.mul_comm _ _
    change K.add K.one
      (K.mul a (polyEval K (List.replicate (m - 1) K.zero ++ [K.one]) a)) =
      K.zero
    rw [polyEval_monomial, hpow, hRoots a ha, K.add_self]
  have hbound := rootBound K
    (K.one :: (List.replicate (m - 1) K.zero ++ [K.one]))
    K.one hLast K.one_ne_zero L hNo hRootsPoly
  simp only [List.length_cons, List.length_append,
    List.length_replicate, List.length_nil] at hbound
  omega

/-- The explicit polynomial X^m + X bounds Frobenius fixed points.
Consumer: PrimitiveIrreducibleExistence. -/
theorem rootBoundPowSelf (K : BinaryField F) (m : Nat) (hm : 2 ≤ m)
    (L : List F) (hNo : L.Nodup)
    (hRoots : ∀ a, a ∈ L → BinaryField.pow K a m = a) :
    L.length ≤ m := by
  have hLast :
      (K.zero :: K.one ::
        (List.replicate (m - 2) K.zero ++ [K.one])).getLast? =
        some K.one := by
    have := getLast_cons_append_singleton K.zero K.one
      (K.one :: List.replicate (m - 2) K.zero)
    simpa using this
  have hRootsPoly : ∀ a, a ∈ L →
      polyEval K
          (K.zero :: K.one ::
            (List.replicate (m - 2) K.zero ++ [K.one])) a =
        K.zero := by
    intro a ha
    have hmRewrite : m - 2 + 2 = m := by omega
    have hpow : K.mul a
        (K.mul a (BinaryField.pow K a (m - 2))) =
        BinaryField.pow K a m := by
      rw [← hmRewrite]
      change K.mul a (K.mul a (BinaryField.pow K a (m - 2))) =
        K.mul (K.mul (BinaryField.pow K a (m - 2)) a) a
      calc
        K.mul a (K.mul a (BinaryField.pow K a (m - 2))) =
            K.mul a (K.mul (BinaryField.pow K a (m - 2)) a) := by
          rw [K.mul_comm a (BinaryField.pow K a (m - 2))]
        _ = K.mul (K.mul a (BinaryField.pow K a (m - 2))) a :=
          (K.mul_assoc _ _ _).symm
        _ = K.mul (K.mul (BinaryField.pow K a (m - 2)) a) a := by
          rw [K.mul_comm a (BinaryField.pow K a (m - 2))]
    change
      K.add K.zero
        (K.mul a (K.add K.one
          (K.mul a
            (polyEval K (List.replicate (m - 2) K.zero ++ [K.one]) a)))) =
      K.zero
    rw [K.zero_add, K.left_distrib, BinaryField.mul_one,
      polyEval_monomial, hpow, hRoots a ha, K.add_self]
  have hbound := rootBound K
    (K.zero :: K.one ::
      (List.replicate (m - 2) K.zero ++ [K.one]))
    K.one hLast K.one_ne_zero L hNo hRootsPoly
  simp only [List.length_cons, List.length_append,
    List.length_replicate, List.length_nil] at hbound
  omega

/-- Products of finite lists, used in PrimitiveFieldGenerator. -/
def listProd (K : BinaryField F) : List F → F
  | [] => K.one
  | a :: as => K.mul a (listProd K as)

/-- List-product concatenation; consumer binaryFiniteFieldFermat. -/
private theorem listProd_append (K : BinaryField F) (l r : List F) :
    listProd K (l ++ r) = K.mul (listProd K l) (listProd K r) := by
  induction l with
  | nil =>
      change listProd K r = K.mul K.one (listProd K r)
      exact (K.one_mul _).symm
  | cons x xs ih =>
      change K.mul x (listProd K (xs ++ r)) =
        K.mul (K.mul x (listProd K xs)) (listProd K r)
      rw [ih]
      exact (K.mul_assoc _ _ _).symm

/-- List-product commutes with adjacent transpositions;
consumer binaryFiniteFieldFermat. -/
private theorem listProd_perm (K : BinaryField F) {l r : List F}
    (h : l.Perm r) : listProd K l = listProd K r := by
  induction h with
  | nil => rfl
  | @cons x l r h ih =>
      change K.mul x (listProd K l) = K.mul x (listProd K r)
      rw [ih]
  | swap x y l =>
      change K.mul y (K.mul x (listProd K l)) =
        K.mul x (K.mul y (listProd K l))
      exact BinaryField.mul_left_comm K y x _
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Remove the first occurrence of a member by splitting a list;
consumer binaryFiniteFieldFermat. -/
private theorem mem_split {a : F} {l : List F} (h : a ∈ l) :
    ∃ pre post : List F, l = pre ++ a :: post := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
      rcases List.mem_cons.mp h with hhead | htail
      · subst x
        exact ⟨[], xs, rfl⟩
      · obtain ⟨pre, post, heq⟩ := ih htail
        exact ⟨x :: pre, post, by rw [heq]; rfl⟩

/-- Pull a selected element to the front by adjacent swaps;
consumer binaryFiniteFieldFermat. -/
private theorem perm_pull (a : F) (pre post : List F) :
    (pre ++ a :: post).Perm (a :: (pre ++ post)) := by
  induction pre with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      exact (List.Perm.cons x ih).trans (List.Perm.swap a x (xs ++ post))

/-- Removing one selected element preserves Nodup;
consumer binaryFiniteFieldFermat. -/
private theorem nodup_remove_middle (a : F) :
    ∀ pre post : List F, (pre ++ a :: post).Nodup →
      (pre ++ post).Nodup ∧ a ∉ pre ++ post := by
  intro pre
  induction pre with
  | nil =>
      intro post h
      exact ⟨(List.nodup_cons.mp h).2, (List.nodup_cons.mp h).1⟩
  | cons x xs ih =>
      intro post h
      have hx := List.nodup_cons.mp h
      have ht := ih post hx.2
      constructor
      · apply List.nodup_cons.mpr
        constructor
        · intro hmem
          apply hx.1
          rcases List.mem_append.mp hmem with hxs | hpost
          · exact List.mem_append.mpr (Or.inl hxs)
          · exact List.mem_append.mpr
              (Or.inr (List.mem_cons.mpr (Or.inr hpost)))
        · exact ht.1
      · intro hmem
        rcases List.mem_cons.mp hmem with heq | hrest
        · apply hx.1
          subst x
          exact List.mem_append.mpr
            (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        · exact ht.2 hrest

/-- Equal Nodup membership gives a permutation, by elementary extraction;
consumer binaryFiniteFieldFermat. -/
private theorem perm_of_nodup_same_members (l : List F) :
    ∀ r : List F, l.Nodup → r.Nodup →
      (∀ x : F, x ∈ l ↔ x ∈ r) → l.Perm r := by
  induction l with
  | nil =>
      intro r hl hr hm
      cases r with
      | nil => exact List.Perm.nil
      | cons x xs =>
          have hbad : x ∈ ([] : List F) := (hm x).2 (by simp)
          cases hbad
  | cons a xs ih =>
      intro r hl hr hm
      have ha : a ∈ r := (hm a).1 (by simp)
      obtain ⟨pre, post, heq⟩ := mem_split ha
      subst r
      have hremove := nodup_remove_middle a pre post hr
      have ha_not : a ∉ xs := (List.nodup_cons.mp hl).1
      have hmrest : ∀ x : F, x ∈ xs ↔ x ∈ pre ++ post := by
        intro x
        by_cases hxa : x = a
        · subst x
          constructor
          · intro hx
            exact False.elim (ha_not hx)
          · intro hx
            exact False.elim (hremove.2 hx)
        · have hfull := hm x
          simpa only [List.mem_cons, List.mem_append, hxa, false_or,
            or_false] using hfull
      have hrec := ih (pre ++ post) (List.nodup_cons.mp hl).2
        hremove.1 hmrest
      exact (List.Perm.cons a hrec).trans
        (perm_pull a pre post).symm

/-- Nonzero elements selected from an enumeration;
consumer binaryFiniteFieldFermat. -/
noncomputable def nonzeroElems (K : BinaryField F) (l : List F) : List F :=
  l.filter (fun a => decide (a ≠ K.zero))

/-- Filtering keeps a nonzero head; consumer binaryFiniteFieldFermat. -/
private theorem nonzeroElems_cons_ne (K : BinaryField F) (x : F) (xs : List F)
    (hx : x ≠ K.zero) : nonzeroElems K (x :: xs) = x :: nonzeroElems K xs := by
  simp [nonzeroElems, List.filter_cons, hx]

/-- Filtering drops a zero head; consumer binaryFiniteFieldFermat. -/
private theorem nonzeroElems_cons_zero (K : BinaryField F) (xs : List F) :
    nonzeroElems K (K.zero :: xs) = nonzeroElems K xs := by
  simp [nonzeroElems, List.filter_cons]

/-- If zero is absent, filtering nonzero elements is the identity.
Consumer: binaryFiniteFieldFermat. -/
private theorem nonzero_filter_id (K : BinaryField F) :
    ∀ l : List F, K.zero ∉ l → nonzeroElems K l = l := by
  intro l
  induction l with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro hnot
      have hx : x ≠ K.zero := by
        intro heq
        exact hnot (by simp [heq])
      have htail : K.zero ∉ xs := by
        intro hm
        exact hnot (by simp [hm])
      rw [nonzeroElems_cons_ne K x xs hx, ih htail]

/-- Filtering out the unique zero removes exactly one entry;
consumer binaryFiniteFieldFermat. -/
private theorem nonzero_length (K : BinaryField F) :
    ∀ l : List F, l.Nodup → K.zero ∈ l →
      (nonzeroElems K l).length + 1 = l.length := by
  intro l
  induction l with
  | nil =>
      intro _ hz
      cases hz
  | cons x xs ih =>
      intro hn hz
      have hnodup := List.nodup_cons.mp hn
      by_cases hx : x = K.zero
      · subst x
        have hrest := nonzero_filter_id K xs hnodup.1
        rw [nonzeroElems_cons_zero, hrest]
        rfl
      · have htail : K.zero ∈ xs := by
          rcases List.mem_cons.mp hz with hhead | hrest
          · exact False.elim (hx hhead.symm)
          · exact hrest
        have hlen := ih hnodup.2 htail
        rw [nonzeroElems_cons_ne K x xs hx]
        simp only [List.length_cons]
        omega

/-- A filtered enumeration lists exactly the nonzero elements;
consumer binaryFiniteFieldFermat. -/
private theorem nonzero_complete (K : BinaryField F)
    (E : Enumeration F) (x : F) :
    x ∈ nonzeroElems K E.elems ↔ x ≠ K.zero := by
  simp [nonzeroElems, E.complete x]

/-- The filtered enumeration has no duplicates;
consumer binaryFiniteFieldFermat. -/
private theorem nonzero_nodup (K : BinaryField F)
    (E : Enumeration F) : (nonzeroElems K E.elems).Nodup := by
  exact E.nodup.filter _

/-- The product of a nonzero list is nonzero;
consumer binaryFiniteFieldFermat. -/
private theorem listProd_ne_zero (K : BinaryField F) :
    ∀ l : List F, (∀ x, x ∈ l → x ≠ K.zero) →
      listProd K l ≠ K.zero := by
  intro l
  induction l with
  | nil =>
      intro _
      exact K.one_ne_zero
  | cons x xs ih =>
      intro hn hz
      change K.mul x (listProd K xs) = K.zero at hz
      rcases BinaryField.mul_eq_zero K _ _ hz with hx | hs
      · exact (hn x (by simp)) hx
      · exact (ih (by
          intro y hy
          exact hn y (by simp [hy])) hs)

/-- Multiplication by a unit preserves nonzero-element lists;
consumer binaryFiniteFieldFermat. -/
private theorem map_mul_nodup (K : BinaryField F) (a : F)
    (ha : a ≠ K.zero) :
    ∀ l : List F, l.Nodup →
      (l.map (fun x => K.mul a x)).Nodup := by
  intro l
  induction l with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons x xs ih =>
      intro hn
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
        have hxy : x = y :=
          BinaryField.mul_left_cancel K a x y ha heq.symm
        exact (List.nodup_cons.mp hn).1 (hxy ▸ hy)
      · exact ih (List.nodup_cons.mp hn).2

/-- Multiplication by a unit maps all nonzero elements onto themselves;
consumer binaryFiniteFieldFermat. -/
private theorem map_mul_complete (K : BinaryField F)
    (E : Enumeration F) (a : F) (ha : a ≠ K.zero) (x : F) :
    x ∈ (nonzeroElems K E.elems).map (fun y => K.mul a y) ↔
      x ≠ K.zero := by
  constructor
  · intro hx hz
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hx
    have hyne := (nonzero_complete K E y).1 hy
    have heqzero : K.mul a y = K.zero := heq.trans hz
    rcases BinaryField.mul_eq_zero K _ _ heqzero with hzero | hzero
    · exact ha hzero
    · exact hyne hzero
  · intro hx
    have hi : K.mul a (K.inv a) = K.one := K.mul_inv a ha
    have hyid : K.mul a (K.mul (K.inv a) x) = x := by
      rw [← K.mul_assoc, hi, K.one_mul]
    have hyne : K.mul (K.inv a) x ≠ K.zero := by
      intro hz
      have hxzero : x = K.zero := by
        calc
          x = K.mul a (K.mul (K.inv a) x) := hyid.symm
          _ = K.mul a K.zero := by rw [hz]
          _ = K.zero := BinaryField.mul_zero K _
      exact hx hxzero
    apply List.mem_map.mpr
    exact ⟨K.mul (K.inv a) x,
      (nonzero_complete K E _).2 hyne, hyid⟩

/-- Multiplying every list element multiplies its product by a power;
consumer binaryFiniteFieldFermat. -/
private theorem listProd_map_mul (K : BinaryField F) (a : F)
    (l : List F) :
    listProd K (l.map (fun x => K.mul a x)) =
      K.mul (BinaryField.pow K a l.length) (listProd K l) := by
  induction l with
  | nil =>
      change K.one = K.mul K.one K.one
      exact (K.one_mul _).symm
  | cons x xs ih =>
      change K.mul (K.mul a x)
          (listProd K (xs.map (fun y => K.mul a y))) =
        K.mul (K.mul (BinaryField.pow K a xs.length) a)
          (K.mul x (listProd K xs))
      rw [ih, BinaryField.mul_four]
      rw [K.mul_comm a (BinaryField.pow K a xs.length)]

/-- Finite field Fermat by the permutation-product argument;
consumer PrimitiveFieldGenerator and PrimitiveIrreducibleExistence. -/
theorem binaryFiniteFieldFermat (K : BinaryField F)
    (E : Enumeration F) (a : F) (ha : a ≠ K.zero) :
    BinaryField.pow K a (E.elems.length - 1) = K.one := by
  have hn : (nonzeroElems K E.elems).Nodup :=
    nonzero_nodup K E
  have hm : ((nonzeroElems K E.elems).map
      (fun x => K.mul a x)).Perm (nonzeroElems K E.elems) := by
    exact perm_of_nodup_same_members _
      (nonzeroElems K E.elems)
      (map_mul_nodup K a ha _ hn) hn
      (by
        intro x
        rw [map_mul_complete K E a ha x, nonzero_complete K E x])
  have hp := listProd_perm K hm
  have hprod : listProd K (nonzeroElems K E.elems) ≠ K.zero :=
    listProd_ne_zero K _ (by
      intro x hx
      exact (nonzero_complete K E x).1 hx)
  have hresult : BinaryField.pow K a
      (nonzeroElems K E.elems).length = K.one := by
    apply BinaryField.mul_left_cancel K
      (listProd K (nonzeroElems K E.elems)) _ _ hprod
    calc
      K.mul (listProd K (nonzeroElems K E.elems))
          (BinaryField.pow K a (nonzeroElems K E.elems).length) =
        K.mul (BinaryField.pow K a (nonzeroElems K E.elems).length)
          (listProd K (nonzeroElems K E.elems)) :=
        K.mul_comm _ _
      _ = listProd K
          ((nonzeroElems K E.elems).map (fun x => K.mul a x)) :=
        (listProd_map_mul K a _).symm
      _ = listProd K (nonzeroElems K E.elems) := hp
      _ = K.mul (listProd K (nonzeroElems K E.elems)) K.one :=
        (BinaryField.mul_one K _).symm
  have hlen := nonzero_length K E.elems E.nodup (E.complete K.zero)
  have heq : (nonzeroElems K E.elems).length = E.elems.length - 1 := by
    omega
  rw [← heq]
  exact hresult

/-- Every element satisfies the cardinality Frobenius equation;
consumer PrimitiveIrreducibleExistence. -/
theorem binaryFiniteFieldFermatSelf (K : BinaryField F)
    (E : Enumeration F) (a : F) :
    BinaryField.pow K a E.elems.length = a := by
  have hpositive : 0 < E.elems.length := by
    cases h : E.elems with
    | nil =>
        have hz := E.complete K.zero
        rw [h] at hz
        cases hz
    | cons x xs =>
        simp only [List.length_cons]
        omega
  have hn : E.elems.length = (E.elems.length - 1) + 1 := by omega
  rw [hn]
  change K.mul (BinaryField.pow K a (E.elems.length - 1)) a = a
  by_cases ha : a = K.zero
  · rw [ha]
    exact BinaryField.mul_zero K _
  · rw [binaryFiniteFieldFermat K E a ha, K.one_mul]

/-- Frobenius is additive in characteristic two;
consumer PrimitiveIrreducibleExistence. -/
theorem frobeniusAdd (K : BinaryField F) (a b : F) :
    BinaryField.pow K (K.add a b) 2 =
      K.add (BinaryField.pow K a 2) (BinaryField.pow K b 2) := by
  rw [BinaryField.pow_two, BinaryField.pow_two, BinaryField.pow_two]
  calc
    K.mul (K.add a b) (K.add a b) =
        K.add (K.mul (K.add a b) a) (K.mul (K.add a b) b) :=
      K.left_distrib (K.add a b) a b
    _ = K.add (K.add (K.mul a a) (K.mul b a))
          (K.add (K.mul a b) (K.mul b b)) := by
      rw [BinaryField.right_distrib, BinaryField.right_distrib]
    _ = K.add (K.add (K.mul a a) (K.mul a b))
          (K.add (K.mul a b) (K.mul b b)) := by
      rw [K.mul_comm b a]
    _ = K.add (K.mul a a) (K.mul b b) :=
      BinaryField.add_interleave K _ _ _

/-- Iterated Frobenius preserves addition;
consumer PrimitiveIrreducibleExistence. -/
theorem frobeniusIterAdd (K : BinaryField F) (a b : F) (m : Nat) :
    BinaryField.pow K (K.add a b) (2 ^ m) =
      K.add (BinaryField.pow K a (2 ^ m))
        (BinaryField.pow K b (2 ^ m)) := by
  induction m with
  | zero =>
      simp only [Nat.pow_zero]
      rw [BinaryField.pow_one, BinaryField.pow_one,
        BinaryField.pow_one]
  | succ m ih =>
      have he : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [Nat.pow_succ]
      calc
        BinaryField.pow K (K.add a b) (2 ^ (m + 1)) =
            BinaryField.pow K (BinaryField.pow K (K.add a b) (2 ^ m)) 2 := by
          rw [he, BinaryField.pow_mul]
        _ = BinaryField.pow K
            (K.add (BinaryField.pow K a (2 ^ m))
              (BinaryField.pow K b (2 ^ m))) 2 := by rw [ih]
        _ = K.add
            (BinaryField.pow K (BinaryField.pow K a (2 ^ m)) 2)
            (BinaryField.pow K (BinaryField.pow K b (2 ^ m)) 2) :=
          frobeniusAdd K _ _
        _ = K.add (BinaryField.pow K a (2 ^ (m + 1)))
            (BinaryField.pow K b (2 ^ (m + 1))) := by
          rw [he, BinaryField.pow_mul, BinaryField.pow_mul]

/-- Iterated Frobenius preserves multiplication;
consumer PrimitiveIrreducibleExistence. -/
theorem frobeniusIterMul (K : BinaryField F) (a b : F) (m : Nat) :
    BinaryField.pow K (K.mul a b) (2 ^ m) =
      K.mul (BinaryField.pow K a (2 ^ m))
        (BinaryField.pow K b (2 ^ m)) :=
  BinaryField.mul_pow K a b (2 ^ m)

/-- Iteration has an additive exponent law; consumer functionPeriodGcd. -/
private theorem iterate_add (T : F → F) (m n : Nat) (x : F) :
    Nat.iterate T (m + n) x =
      Nat.iterate T m (Nat.iterate T n x) := by
  induction m with
  | zero =>
      exact congrArg (fun k => Nat.iterate T k x) (Nat.zero_add n)
  | succ m ih =>
      have hcomm : ∀ k : Nat, ∀ y : F,
          Nat.iterate T (k + 1) y = T (Nat.iterate T k y) := by
        intro k
        induction k with
        | zero =>
            intro y
            rfl
        | succ k ihk =>
            intro y
            change Nat.iterate T (k + 1) (T y) =
              T (Nat.iterate T (k + 1) y)
            exact ihk (T y)
      calc
        Nat.iterate T ((m + 1) + n) x =
            T (Nat.iterate T (m + n) x) := by
          rw [Nat.succ_add]
          exact hcomm (m + n) x
        _ = T (Nat.iterate T m (Nat.iterate T n x)) := by rw [ih]
        _ = Nat.iterate T (m + 1) (Nat.iterate T n x) :=
          (hcomm m _).symm

/-- An identity iterate remains the identity after any multiple;
consumer functionPeriodGcd. -/
private theorem iterate_period_mul (T : F → F) (n k : Nat)
    (hn : ∀ x : F, Nat.iterate T n x = x) :
    ∀ x : F, Nat.iterate T (n * k) x = x := by
  induction k with
  | zero =>
      intro x
      rfl
  | succ k ih =>
      intro x
      rw [Nat.mul_succ, iterate_add, ih, hn]

/-- Euclidean remainder of two identity periods is an identity period;
consumer functionPeriodGcd. -/
private theorem iterate_period_mod (T : F → F) (v w : Nat)
    (hv : ∀ x : F, Nat.iterate T v x = x)
    (hw : ∀ x : F, Nat.iterate T w x = x) :
    ∀ x : F, Nat.iterate T (v % w) x = x := by
  intro x
  by_cases hwzero : w = 0
  · subst w
    simpa using hv x
  · have hd : w * (v / w) + v % w = v := by
      have hh := Nat.mod_add_div v w
      omega
    have hperiod := iterate_period_mul T w (v / w) hw
    have ht : Nat.iterate T v x = Nat.iterate T (v % w) x := by
      calc
        Nat.iterate T v x =
            Nat.iterate T (w * (v / w) + v % w) x := by rw [hd]
        _ = Nat.iterate T (w * (v / w))
            (Nat.iterate T (v % w) x) := iterate_add T _ _ _
        _ = Nat.iterate T (v % w) x := hperiod _
    exact ht.symm.trans (hv x)

/-- The gcd of two global identity periods is an identity period.
Consumer: PrimitiveIrreducibleExistence. -/
theorem functionPeriodGcd (T : F → F) (v w : Nat)
    (hv : ∀ x : F, Nat.iterate T v x = x)
    (hw : ∀ x : F, Nat.iterate T w x = x) :
    ∀ x : F, Nat.iterate T (Nat.gcd v w) x = x := by
  have main : ∀ w v : Nat,
      (∀ x : F, Nat.iterate T v x = x) →
      (∀ x : F, Nat.iterate T w x = x) →
      ∀ x : F, Nat.iterate T (Nat.gcd v w) x = x := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
        intro v hv hw
        by_cases hwzero : w = 0
        · subst w
          simpa using hv
        · have hmod := iterate_period_mod T v w hv hw
          have hsmaller : v % w < w := Nat.mod_lt v (Nat.pos_of_ne_zero hwzero)
          have hrec := ih (v % w) hsmaller w hw hmod
          have hg : Nat.gcd v w = Nat.gcd w (v % w) := by
            calc
              Nat.gcd v w = Nat.gcd w v := Nat.gcd_comm _ _
              _ = Nat.gcd (v % w) w := Nat.gcd_rec w v
              _ = Nat.gcd w (v % w) := Nat.gcd_comm _ _
          intro x
          rw [hg]
          exact hrec x
  exact main w v hv hw

/-- Multiplication iteration realizes the requested power;
consumer unitPeriodGcd and PrimitiveFieldGenerator. -/
private theorem iterate_mul_power (K : BinaryField F) (a x : F) (n : Nat) :
    Nat.iterate (fun z => K.mul z a) n x =
      K.mul x (BinaryField.pow K a n) := by
  induction n generalizing x with
  | zero =>
      change x = K.mul x K.one
      exact (BinaryField.mul_one K x).symm
  | succ n ih =>
      change Nat.iterate (fun z => K.mul z a) n (K.mul x a) =
        K.mul x (K.mul (BinaryField.pow K a n) a)
      rw [ih]
      calc
        K.mul (K.mul x a) (BinaryField.pow K a n) =
            K.mul x (K.mul a (BinaryField.pow K a n)) :=
          K.mul_assoc _ _ _
        _ = K.mul x (K.mul (BinaryField.pow K a n) a) := by
          rw [K.mul_comm a (BinaryField.pow K a n)]

/-- The gcd of two unit periods is again a period.
Consumer: PrimitiveFieldGenerator. -/
theorem unitPeriodGcd (K : BinaryField F) (a : F) (ha : a ≠ K.zero)
    (v w : Nat)
    (hv : BinaryField.pow K a v = K.one)
    (hw : BinaryField.pow K a w = K.one) :
    BinaryField.pow K a (Nat.gcd v w) = K.one := by
  have hperiodV : ∀ x : F,
      Nat.iterate (fun z => K.mul z a) v x = x := by
    intro x
    rw [iterate_mul_power, hv, BinaryField.mul_one]
  have hperiodW : ∀ x : F,
      Nat.iterate (fun z => K.mul z a) w x = x := by
    intro x
    rw [iterate_mul_power, hw, BinaryField.mul_one]
  have hg := functionPeriodGcd (fun z => K.mul z a) v w
    hperiodV hperiodW K.one
  rw [iterate_mul_power, K.one_mul] at hg
  exact hg

end L3.TapField

#print axioms L3.TapField.rootBound
#print axioms L3.TapField.binaryFiniteFieldFermat
#print axioms L3.TapField.frobeniusIterAdd
#print axioms L3.TapField.unitPeriodGcd

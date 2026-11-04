import Leader.L3.Params

namespace L3

set_option autoImplicit false

/-!
Executable GF(2) certificate substrate.

The matrix checker below is polynomial in the matrix width and in
the length of the binary exponent.  No theorem here reduces recIter
(2^t-1) on all Boolean words.  The missing generic correctness and
orbit theorems are identified after the code block in the delivery.
-/

/-- The recurrence (u₀,...,uₜ₋₁) ↦
    (u₁,...,uₜ₋₁, XOR_j (taps j && u_j)).
    In particular, the oldest bit is coordinate zero. -/
def recStep (t : Nat) (taps : Nat → Bool)
    (u : Fin t → Bool) : Fin t → Bool :=
  fun i =>
    if h : i.val + 1 < t then
      u ⟨i.val + 1, h⟩
    else
      Fin.foldl t
        (fun acc j => Bool.xor acc (Bool.and (taps j.val) (u j)))
        false

/-- Genuine k-fold composition, defined without any matrix assumptions. -/
def recIter (t : Nat) (taps : Nat → Bool) :
    Nat → (Fin t → Bool) → (Fin t → Bool)
  | 0, u => u
  | k + 1, u => recStep t taps (recIter t taps k u)

/-- The exact maximal-period assertion. -/
def IsPrimitive (t : Nat) (taps : Nat → Bool) : Prop :=
  ∀ u : Fin t → Bool, (∃ i, u i = true) →
    recIter t taps (2 ^ t - 1) u = u ∧
    ∀ k, 0 < k → k < 2 ^ t - 1 → recIter t taps k u ≠ u

theorem recIter_zero (t : Nat) (taps : Nat → Bool)
    (u : Fin t → Bool) :
    recIter t taps 0 u = u := rfl

theorem recIter_succ (t : Nat) (taps : Nat → Bool)
    (k : Nat) (u : Fin t → Bool) :
    recIter t taps (k + 1) u =
      recStep t taps (recIter t taps k u) := rfl

/-!
Bitmasks store rows of a t × t matrix over GF(2).
Each bit j in a row is the coefficient of input coordinate j.
The list length is t for matrices produced by rowsId/recRows/rowsMul.
-/

/-- Row masks of the identity matrix. -/
def rowsId (t : Nat) : List Nat :=
  (List.range t).map (fun i => 2 ^ i)

/-- Feedback row: bit j is taps j. -/
def feedbackMask (t : Nat) (taps : Nat → Bool) : Nat :=
  (List.range t).foldl
    (fun acc j => if taps j then Nat.xor acc (2 ^ j) else acc) 0

/-- The companion matrix in the JS SI orientation. -/
def recRows (t : Nat) (taps : Nat → Bool) : List Nat :=
  (List.range t).map (fun i =>
    if i + 1 < t then 2 ^ (i + 1)
    else feedbackMask t taps)

/-- Apply a row-mask matrix to a Boolean column vector. -/
def rowsApply (t : Nat) (A : List Nat)
    (u : Fin t → Bool) : Fin t → Bool :=
  fun i =>
    Fin.foldl t
      (fun acc j =>
        Bool.xor acc
          (Bool.and (Nat.testBit (A.getD i.val 0) j.val) (u j)))
      false

/-- GF(2) matrix product: output row i XORs the rows B_j
    selected by the set bits in row A_i. -/
def rowsMul (t : Nat) (A B : List Nat) : List Nat :=
  (List.range t).map (fun i =>
    (List.range t).foldl
      (fun acc j =>
        if Nat.testBit (A.getD i 0) j then
          Nat.xor acc (B.getD j 0)
        else acc)
      0)

/-- GF(2) sum, equal to subtraction in characteristic two. -/
def rowsXor (t : Nat) (A B : List Nat) : List Nat :=
  (List.range t).map
    (fun i => Nat.xor (A.getD i 0) (B.getD i 0))

/-- Binary powering, using a structurally decreasing fuel.
    Nonzero exponent is halved in every recursive call.
    The initial fuel exponent+1 is deliberately conservative. -/
def rowsPowAux (t : Nat) :
    Nat → Nat → List Nat → List Nat → List Nat
  | 0, _, _, acc => acc
  | fuel + 1, exponent, base, acc =>
      if exponent == 0 then acc
      else
        rowsPowAux t fuel (exponent / 2) (rowsMul t base base)
          (if exponent % 2 == 1 then rowsMul t acc base else acc)

def rowsPowFast (t : Nat) (A : List Nat) (exponent : Nat) :
    List Nat :=
  rowsPowAux t (exponent + 1) exponent A (rowsId t)

theorem rowsPowFast_zero (t : Nat) (A : List Nat) :
    rowsPowFast t A 0 = rowsId t := rfl

/-- Fast matrix evaluation; its equality to recIter is an OPEN
    proof obligation, not an assumption used by a theorem below. -/
def matrixIter (t : Nat) (taps : Nat → Bool)
    (k : Nat) (u : Fin t → Bool) : Fin t → Bool :=
  rowsApply t (rowsPowFast t (recRows t taps) k) u

/-!
Gauss–Jordan produces a candidate left inverse.  We do not assume
the elimination is correct: certificateCheck independently verifies
that the computed candidate times the proposed matrix is identity.
-/

def swapRows (A : List Nat) (i j : Nat) : List Nat :=
  let ai := A.getD i 0
  let aj := A.getD j 0
  (A.set i aj).set j ai

def gaussStep (t : Nat) (s : List Nat × List Nat)
    (col : Nat) : List Nat × List Nat :=
  let candidates := (List.range (t - col)).map (fun k => col + k)
  match candidates.find? (fun row => Nat.testBit (s.1.getD row 0) col) with
  | none => s
  | some pivot =>
      let left := swapRows s.1 col pivot
      let right := swapRows s.2 col pivot
      let pivotLeft := left.getD col 0
      let pivotRight := right.getD col 0
      (List.range t).foldl
        (fun z j =>
          if (j != col) && Nat.testBit (z.1.getD j 0) col then
            (z.1.set j (Nat.xor (z.1.getD j 0) pivotLeft),
             z.2.set j (Nat.xor (z.2.getD j 0) pivotRight))
          else z)
        (left, right)

def rowsInverseCandidate (t : Nat) (A : List Nat) : List Nat :=
  ((List.range t).foldl (gaussStep t) (A, rowsId t)).2

/-!
These are complete PRIME MULTISETS, not just distinct prime factors.
The two repeated factors 3 at degrees 6 and 12 matter for product
verification.  The largest factor is 131071 at degree 17.
-/
def tapFactorList : Nat → List Nat
  | 2 => [3]
  | 3 => [7]
  | 4 => [3, 5]
  | 5 => [31]
  | 6 => [3, 3, 7]
  | 7 => [127]
  | 8 => [3, 5, 17]
  | 9 => [7, 73]
  | 10 => [3, 11, 31]
  | 11 => [23, 89]
  | 12 => [3, 3, 5, 7, 13]
  | 13 => [8191]
  | 14 => [3, 43, 127]
  | 15 => [7, 31, 151]
  | 16 => [3, 5, 17, 257]
  | 17 => [131071]
  | _ => []

/-- Trial division through 362.  This is enough for all factors
    in tapFactorList at widths 2..17, whose factors are <= 131071.
    It is a Boolean test, not a theorem about Nat.Prime. -/
def smallPrimeTrial (p : Nat) : Bool :=
  decide (2 ≤ p) &&
    (List.range 361).all (fun k =>
      let d := k + 2
      if d * d ≤ p then decide (p % d ≠ 0) else true)

/-- Polynomial-size computational certificate:
  1. declared prime factors multiply to 2^t-1;
  2. every declared factor passes the bounded prime trial;
  3. A^(2^t-1) is identity;
  4. for every factor p, the computed left inverse of
     A^((2^t-1)/p) + I is checked by multiplication.

    The critical soundness bridge from these tests to IsPrimitive
    is not included: a matrix being nonidentity would not suffice. -/
def certificateCheck (t : Nat) : Bool :=
  let taps := fun j => (tapTable t).getD j false
  let A := recRows t taps
  let M := 2 ^ t - 1
  let factors := tapFactorList t
  (factors.foldl (fun acc p => acc * p) 1 == M) &&
  factors.all smallPrimeTrial &&
  (rowsPowFast t A M == rowsId t) &&
  factors.all (fun p =>
    let C := rowsXor t (rowsPowFast t A (M / p)) (rowsId t)
    rowsMul t (rowsInverseCandidate t C) C == rowsId t)

/-- Small, explicit product control for the 17-bit Mersenne number. -/
theorem degree17_factor_product :
    (tapFactorList 17).foldl (fun acc p => acc * p) 1 =
      2 ^ 17 - 1 := by decide

/-- Trial division through sqrt(131071); no vector enumeration. -/
theorem degree17_prime_trial :
    smallPrimeTrial 131071 = true := by decide +kernel

/-!
An external repeated-squaring/rank calculation predicts:
certificateCheck t = true for every 2 <= t <= 17.
A Lean kernel proof of this Boolean computation and, more importantly,
its general soundness theorem remain to be completed.
-/

/-- Kernel evaluation of the Boolean certificate for every installed width (polynomial-size
work: binary powering of `t × t` GF(2) matrices).  This is a computation, not yet `IsPrimitive`:
the soundness bridge `certificateCheck t = true → IsPrimitive t _` is still open. -/
theorem certificateCheck_installed :
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17].all certificateCheck = true := by
  decide +kernel

end L3

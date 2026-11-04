import Leader.L3.Top.MarkedCells

/-!
# Q7: the register weight as a linear form in the position

The window-edge inequalities of the marked rank (`pair_strict`, `pair_local_old`,
`pair_strict_old`) are finite in the register values and flags and linear in `r` and the
position `p` (with `p + 1 < r`). Writing `r = p + m + d` and `j = p + k` with `k ≤ m`, the
register weight `wt r j ob vb c` is a linear form `a * p + b * d + c` with natural coefficients
(`wtF`, `wt_eq`); an inequality of two such forms holds for all `p, d` exactly when it holds
coefficient-wise (`LF.le_sound`). The consumers check every register pair and flag pattern
coefficient-wise in one closed Boolean evaluation and read their case off it, instead of
splitting into thousands of cases with `simp` and `omega` at symbolic `r, p`.

Consumer: `Leader/L3/Top/MarkedProgress.lean`, `Leader/L3/Top/OldMark.lean`,
`Leader/L3/Top/OldMarkProgress.lean`.
-/

namespace L3
namespace MarkedCells
namespace Forms

set_option autoImplicit false

/-- A linear form `a * p + b * d + c`. Consumer: `wt_eq`. -/
structure LF where
  a : Nat
  b : Nat
  c : Nat

/-- Value of a linear form. Consumer: `wt_eq`. -/
def LF.ev (A : LF) (p d : Nat) : Nat := A.a * p + A.b * d + A.c

/-- Sum of linear forms. Consumer: `wtF`. -/
def LF.add (A B : LF) : LF := ⟨A.a + B.a, A.b + B.b, A.c + B.c⟩

/-- The zero form. Consumer: `wtF`. -/
def LF.zero : LF := ⟨0, 0, 0⟩

/-- The constant form `1`. Consumer: strict window-edge checks. -/
def LF.one : LF := ⟨0, 0, 1⟩

/-- Coefficient-wise comparison. Consumer: window-edge checks. -/
def LF.le (A B : LF) : Bool :=
  decide (A.a ≤ B.a) && decide (A.b ≤ B.b) && decide (A.c ≤ B.c)

theorem LF.ev_add (A B : LF) (p d : Nat) : (A.add B).ev p d = A.ev p d + B.ev p d := by
  simp only [LF.add, LF.ev, Nat.add_mul]
  omega

theorem LF.ev_one (p d : Nat) : LF.one.ev p d = 1 := by
  simp [LF.one, LF.ev]

theorem LF.ev_ite {P : Prop} [Decidable P] (A : LF) (p d : Nat) :
    (if P then A else LF.zero).ev p d = if P then A.ev p d else 0 := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]; simp [LF.ev, LF.zero]

theorem LF.le_sound {A B : LF} (h : A.le B = true) (p d : Nat) : A.ev p d ≤ B.ev p d := by
  simp only [LF.le, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold LF.ev
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul h1 (Nat.le_refl p)) (Nat.mul_le_mul h2 (Nat.le_refl d))) h3

/-- `2 r + 2 - j` at `r = p + m + d`, `j = p + k`. -/
def fV (m k : Nat) : LF := ⟨1, 2, 2 * m + 2 - k⟩

/-- `r - j + 1` at `r = p + m + d`, `j = p + k`. -/
def fD (m k : Nat) : LF := ⟨0, 1, m + 1 - k⟩

/-- `r + 1` at `r = p + m + d`. -/
def fS (m : Nat) : LF := ⟨1, 1, m + 1⟩

/-- `gateW` as a linear form. Consumer: `wtF`. -/
def gateF (m k : Nat) (c : Cell) : LF :=
  LF.add
    (match c.i with
      | .st => fS m
      | .sn => fS m
      | .x => fD m k
      | _ => LF.zero)
    (if c.c = .off then LF.zero else fD m k)

/-- `wt` as a linear form. Consumer: window-edge checks. -/
def wtF (m k : Nat) (ob vb : Bool) (c : Cell) : LF :=
  LF.add
    (LF.add (if violC ob c = true then fV m k else LF.zero)
      (if vb = true then gateF m k c else LF.zero))
    (if c.c = .inh then fD m k else LF.zero)

theorem gateW_eq (p d m k : Nat) (hk : k ≤ m) (c : Cell) :
    gateW (p + m + d) (p + k) c = (gateF m k c).ev p d := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> simp [gateW, gateF, LF.ev, LF.add, LF.zero, fS, fD] <;> omega

/-- The register weight at `r = p + m + d`, `j = p + k`, `k ≤ m`, is the form `wtF m k`. -/
theorem wt_eq (r j p d m k : Nat) (hr : r = p + m + d) (hj : j = p + k) (hk : k ≤ m)
    (ob vb : Bool) (c : Cell) : wt r j ob vb c = (wtF m k ob vb c).ev p d := by
  subst hr hj
  unfold wt wtF
  rw [LF.ev_add, LF.ev_add, LF.ev_ite, LF.ev_ite, LF.ev_ite, gateW_eq p d m k hk]
  have h1 : 2 * (p + m + d) + 2 - (p + k) = (fV m k).ev p d := by simp only [fV, LF.ev]; omega
  have h3 : p + m + d - (p + k) + 1 = (fD m k).ev p d := by simp only [fD, LF.ev]; omega
  rw [h1, h3]

/-! ### Enumeration of the register values -/

/-- Both Booleans. Consumer: window-edge checks. -/
def allBool : List Bool := [false, true]

/-- Every register. Consumer: window-edge checks. -/
def allCell : List Cell :=
  [Inp.e, .pt, .pn, .st, .sn, .x].flatMap fun i =>
    [Car.off, .fresh, .inh].map fun c => ({ i := i, c := c } : Cell)

theorem memB (b : Bool) : b ∈ allBool := by cases b <;> decide

theorem memC (x : Cell) : x ∈ allCell := by
  rcases x with ⟨i, c⟩
  cases i <;> cases c <;> decide

theorem allB {α : Type} {l : List α} {f : α → Bool} (h : l.all f = true) {a : α}
    (ha : a ∈ l) : f a = true :=
  List.all_eq_true.mp h a ha

theorem impB {a b : Bool} (h : (!a || b) = true) : a = true → b = true := by
  cases a <;> cases b <;> simp_all

theorem and3B {a b c : Bool} (h : (a && b && c) = true) :
    a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Continue with an input class evaluated to a constructor. -/
def withInp (i : Inp) (k : Inp → Bool) : Bool :=
  match i with
  | .e => k .e
  | .pt => k .pt
  | .pn => k .pn
  | .st => k .st
  | .sn => k .sn
  | .x => k .x

/-- Continue with a carry class evaluated to a constructor. -/
def withCar (c : Car) (k : Car → Bool) : Bool :=
  match c with
  | .off => k .off
  | .fresh => k .fresh
  | .inh => k .inh

/-- Continue with a register evaluated to constructors, so that a closed check evaluates the
register once (`pair` is evaluated once per edge input). -/
def withCell (c : Cell) (k : Cell → Bool) : Bool :=
  withInp c.i fun i => withCar c.c fun cc => k { i := i, c := cc }

theorem withCell_eq (c : Cell) (k : Cell → Bool) : withCell c k = k c := by
  rcases c with ⟨i, cc⟩
  cases i <;> cases cc <;> rfl

/-- An implication of Booleans as a Boolean. -/
theorem impI {a b : Bool} (h : a = true → b = true) : (!a || b) = true := by
  cases a <;> cases b <;> simp_all

/-- An implication of decidable propositions as a Boolean. -/
theorem impD {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) :
    (!decide P || decide Q) = true := by
  by_cases hp : P
  · simp [hp, h hp]
  · simp [hp]

end Forms
end MarkedCells
end L3

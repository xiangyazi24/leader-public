import Lean

namespace L4
namespace Compiler
namespace Digits

abbrev Nib := Fin 16
abbrev Word (r : Nat) := Fin r → Nib

/-- Little-endian value of the first j digits. -/
def valJ {r : Nat} (w : Word r) : (j : Nat) → j ≤ r → Nat
  | 0, _ => 0
  | j + 1, h =>
      valJ w j (Nat.le_of_succ_le h) +
        16 ^ j * (w ⟨j, Nat.lt_of_succ_le h⟩).val

def val {r : Nat} (w : Word r) : Nat :=
  valJ w r (Nat.le_refl r)

theorem val_succ {r : Nat} (w : Word r) (j : Nat) (h : j + 1 ≤ r) :
    valJ w (j + 1) h =
      valJ w j (Nat.le_of_succ_le h) +
        16 ^ j * (w ⟨j, Nat.lt_of_succ_le h⟩).val := rfl

theorem val_zero {r : Nat} (w : Word r) :
    valJ w 0 (Nat.zero_le r) = 0 := rfl

structure Position where
  first : Bool
  second : Bool
  penultimateOrLater : Bool
  last : Bool
deriving DecidableEq, Repr

def positionAt (r j : Nat) : Position :=
  ⟨decide (j = 0), decide (j = 1),
   decide (r ≤ j + 2), decide (j + 1 = r)⟩

def PositionCorrect (r j : Nat) (p : Position) : Prop :=
  p.first = decide (j = 0) ∧
  p.second = decide (j = 1) ∧
  p.penultimateOrLater = decide (r ≤ j + 2) ∧
  p.last = decide (j + 1 = r)

theorem positionAt_correct (r j : Nat) :
    PositionCorrect r j (positionAt r j) := by
  simp [PositionCorrect, positionAt]

def copyStep (u : Nib) : Nib := u
def constSmallStep (c : Nib) (p : Position) : Nib :=
  if p.first then c else 0
def constMaxStep : Nib := 15
def constPStep (p : Position) : Nib := if p.last then 8 else 0
def constBM1Step (p : Position) : Nib :=
  if p.penultimateOrLater then 0 else 15
def maskStep (u : Nib) (p : Position) : Nib :=
  if p.penultimateOrLater then 0 else u

def addStep (u v : Nib) (c : Fin 2) : Nib × Fin 2 :=
  let t := u.val + v.val + c.val
  (⟨t % 16, Nat.mod_lt _ (by decide)⟩,
   ⟨t / 16, by omega⟩)

/-- Borrow is proved by an explicit split, not by omega on an if-term. -/
def subStep (u v : Nib) (b : Fin 2) : Nib × Fin 2 :=
  let borrow := if u.val < v.val + b.val then 1 else 0
  let digit :=
    if u.val < v.val + b.val
    then u.val + 16 - v.val - b.val
    else u.val - v.val - b.val
  (⟨digit, by
      by_cases h : u.val < v.val + b.val
      · simp [digit, h] <;> omega
      · simp [digit, h] <;> omega⟩,
   ⟨borrow, by
      by_cases h : u.val < v.val + b.val
      · simp [borrow, h] <;> omega
      · simp [borrow, h] <;> omega⟩)

def shl3Step (u : Nib) (c : Fin 8) : Nib × Fin 8 :=
  let t := 8 * u.val + c.val
  (⟨t % 16, Nat.mod_lt _ (by decide)⟩,
   ⟨t / 16, by omega⟩)

def muxStep (q : Bool) (a b : Nib) : Nib := if q then a else b

def cmpStep (eq lt : Bool) (u v : Nib) : Bool × Bool :=
  (eq && decide (u.val = v.val),
   if u.val = v.val then lt else decide (u.val < v.val))

def scan5Step (j : Nat) (acc : Fin 32) (u : Nib) : Fin 32 :=
  if j = 0 then ⟨u.val, by omega⟩
  else if j = 1 then
    ⟨(acc.val + 16 * (u.val % 2)) % 32, Nat.mod_lt _ (by decide)⟩
  else acc

theorem copy_digit_fact (u : Nib) : (copyStep u).val = u.val := by
  rfl

theorem const_max_digit_fact : constMaxStep.val = 15 := by
  decide

theorem add_digit_fact (u v : Nib) (c : Fin 2) :
    let t := u.val + v.val + c.val
    (addStep u v c).1.val + 16 * (addStep u v c).2.val = t ∧
    (addStep u v c).2.val ≤ 1 := by
  revert u v c
  decide

/-- The one-digit subtraction equation. -/
theorem sub_digit_fact (u v : Nib) (b : Fin 2) :
    (subStep u v b).1.val + v.val + b.val =
      u.val + 16 * (subStep u v b).2.val ∧
    (subStep u v b).2.val ≤ 1 := by
  by_cases h : u.val < v.val + b.val <;>
    simp [subStep, h] <;> omega

theorem shl3_digit_fact (u : Nib) (c : Fin 8) :
    let t := 8 * u.val + c.val
    (shl3Step u c).1.val + 16 * (shl3Step u c).2.val = t ∧
    (shl3Step u c).2.val ≤ 7 := by
  revert u c
  decide

theorem mux_digit_fact (q : Bool) (a b : Nib) :
    (muxStep q a b).val = if q then a.val else b.val := by
  cases q <;> rfl

theorem cmp_digit_fact (eq lt : Bool) (u v : Nib) :
    let z := cmpStep eq lt u v
    z.1 = (eq && decide (u.val = v.val)) ∧
    z.2 = (if u.val = v.val then lt else decide (u.val < v.val)) := by
  revert eq lt u v
  decide

theorem scan5_digit_fact (j : Nat) (a : Fin 32) (u : Nib) :
    (j = 0 → (scan5Step j a u).val = u.val) ∧
    (j = 1 → (scan5Step j a u).val =
      (a.val + 16 * (u.val % 2)) % 32) ∧
    (j ≥ 2 → scan5Step j a u = a) := by
  by_cases h0 : j = 0
  · subst j
    simp [scan5Step]
  · by_cases h1 : j = 1
    · subst j
      simp [scan5Step]
    · have h2 : j ≥ 2 := by omega
      simp [scan5Step, h0, h1, h2]

theorem const_small_digit_fact (c : Nib) (p : Position) :
    constSmallStep c p = (if p.first then c else 0) := rfl
theorem const_p_digit_fact (p : Position) :
    constPStep p = (if p.last then 8 else 0) := rfl
theorem const_bm1_digit_fact (p : Position) :
    constBM1Step p = (if p.penultimateOrLater then 0 else 15) := rfl
theorem mask_digit_fact (u : Nib) (p : Position) :
    maskStep u p = (if p.penultimateOrLater then 0 else u) := rfl

theorem prefix_induction {r : Nat} (P : Nat → Prop)
    (hzero : P 0)
    (hstep : ∀ j, j < r → P j → P (j + 1)) :
    ∀ j, j ≤ r → P j := by
  intro j
  induction j with
  | zero =>
      intro _
      exact hzero
  | succ j ih =>
      intro hj
      apply hstep j
      · omega
      · exact ih (by omega)

/-! These laws expose the per-position output equations explicitly.
    The generic induction is proved; connecting the actual generated output
    words to these equations is the remaining geometry/IN-padding obligation. -/

/-- One digit position: the low digit and the carry recombine. -/
theorem digit_shift (P s : Nat) : P * (s % 16) + P * 16 * (s / 16) = P * s := by
  rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]

def CopyLaw {r : Nat} (a y : Word r) (j : Nat) : Prop :=
  ∀ hj : j ≤ r, valJ y j hj = valJ a j hj

theorem copy_prefix {r : Nat} (a y : Word r)
    (hzero : CopyLaw a y 0)
    (hdigit : ∀ j (hj : j < r),
      (y ⟨j, hj⟩).val = (a ⟨j, hj⟩).val) :
    ∀ j, j ≤ r → CopyLaw a y j := by
  apply prefix_induction
  · exact hzero
  · intro j hj ih
    unfold CopyLaw at ih ⊢
    intro hk
    rw [val_succ, val_succ, ih (Nat.le_of_succ_le hk), hdigit j hj]

theorem copy_word {r : Nat} (a y : Word r)
    (hzero : CopyLaw a y 0)
    (hdigit : ∀ j (hj : j < r),
      (y ⟨j, hj⟩).val = (a ⟨j, hj⟩).val) :
    val y = val a := by
  have h := copy_prefix a y hzero hdigit r (Nat.le_refl r)
  exact h (Nat.le_refl r)

def AddLaw {r : Nat} (a b y : Word r) (carry : Nat → Nat) (j : Nat) : Prop :=
  ∀ hj : j ≤ r,
    valJ y j hj + 16 ^ j * carry j =
      valJ a j hj + valJ b j hj

theorem add_prefix {r : Nat} (a b y : Word r) (carry : Nat → Nat)
    (hzero : AddLaw a b y carry 0)
    (hdigit : ∀ j (hj : j < r),
      ∃ c : Fin 2,
        carry j = c.val ∧
        (y ⟨j, hj⟩).val =
          ((a ⟨j, hj⟩).val + (b ⟨j, hj⟩).val + c.val) % 16 ∧
        carry (j + 1) =
          ((a ⟨j, hj⟩).val + (b ⟨j, hj⟩).val + c.val) / 16) :
    ∀ j, j ≤ r → AddLaw a b y carry j := by
  apply prefix_induction
  · exact hzero
  · intro j hj ih
    unfold AddLaw at ih ⊢
    intro hk
    obtain ⟨c, hc, hy, hcarry⟩ := hdigit j hj
    have old := ih (Nat.le_of_succ_le hk)
    rw [hc] at old
    have key := digit_shift (16 ^ j) ((a ⟨j, hj⟩).val + (b ⟨j, hj⟩).val + c.val)
    rw [Nat.mul_add, Nat.mul_add] at key
    rw [val_succ, val_succ, val_succ, Nat.pow_succ, hcarry, hy]
    omega

theorem add_word {r : Nat} (a b y : Word r) (carry : Nat → Nat)
    (hzero : AddLaw a b y carry 0)
    (hdigit : ∀ j (hj : j < r),
      ∃ c : Fin 2,
        carry j = c.val ∧
        (y ⟨j, hj⟩).val =
          ((a ⟨j, hj⟩).val + (b ⟨j, hj⟩).val + c.val) % 16 ∧
        carry (j + 1) =
          ((a ⟨j, hj⟩).val + (b ⟨j, hj⟩).val + c.val) / 16) :
    val y + 16 ^ r * carry r = val a + val b := by
  have h := add_prefix a b y carry hzero hdigit r (Nat.le_refl r)
  exact h (Nat.le_refl r)

def SubLaw {r : Nat} (a b y : Word r) (borrow : Nat → Nat) (j : Nat) : Prop :=
  ∀ hj : j ≤ r,
    valJ y j hj + valJ b j hj =
      valJ a j hj + 16 ^ j * borrow j

theorem sub_prefix {r : Nat} (a b y : Word r) (borrow : Nat → Nat)
    (hzero : SubLaw a b y borrow 0)
    (hdigit : ∀ j (hj : j < r),
      ∃ c : Fin 2,
        borrow j = c.val ∧
        (y ⟨j, hj⟩).val + (b ⟨j, hj⟩).val + c.val =
          (a ⟨j, hj⟩).val + 16 * borrow (j + 1)) :
    ∀ j, j ≤ r → SubLaw a b y borrow j := by
  apply prefix_induction
  · exact hzero
  · intro j hj ih
    unfold SubLaw at ih ⊢
    intro hk
    obtain ⟨c, hc, hlocal⟩ := hdigit j hj
    have old := ih (Nat.le_of_succ_le hk)
    rw [hc] at old
    have key := congrArg (fun t => 16 ^ j * t) hlocal
    simp only [Nat.mul_add] at key
    rw [← Nat.mul_assoc] at key
    rw [val_succ, val_succ, val_succ, Nat.pow_succ]
    omega

theorem sub_word {r : Nat} (a b y : Word r) (borrow : Nat → Nat)
    (hzero : SubLaw a b y borrow 0)
    (hdigit : ∀ j (hj : j < r),
      ∃ c : Fin 2,
        borrow j = c.val ∧
        (y ⟨j, hj⟩).val + (b ⟨j, hj⟩).val + c.val =
          (a ⟨j, hj⟩).val + 16 * borrow (j + 1)) :
    val y + val b = val a + 16 ^ r * borrow r := by
  have h := sub_prefix a b y borrow hzero hdigit r (Nat.le_refl r)
  exact h (Nat.le_refl r)

def Shl3Law {r : Nat} (a y : Word r) (carry : Nat → Nat) (j : Nat) : Prop :=
  ∀ hj : j ≤ r,
    valJ y j hj + 16 ^ j * carry j = 8 * valJ a j hj

theorem shl3_prefix {r : Nat} (a y : Word r) (carry : Nat → Nat)
    (hzero : Shl3Law a y carry 0)
    (hdigit : ∀ j (hj : j < r),
      ∃ c : Fin 8,
        carry j = c.val ∧
        (y ⟨j, hj⟩).val =
          (8 * (a ⟨j, hj⟩).val + c.val) % 16 ∧
        carry (j + 1) =
          (8 * (a ⟨j, hj⟩).val + c.val) / 16) :
    ∀ j, j ≤ r → Shl3Law a y carry j := by
  apply prefix_induction
  · exact hzero
  · intro j hj ih
    unfold Shl3Law at ih ⊢
    intro hk
    obtain ⟨c, hc, hy, hcarry⟩ := hdigit j hj
    have old := ih (Nat.le_of_succ_le hk)
    rw [hc] at old
    have key := digit_shift (16 ^ j) (8 * (a ⟨j, hj⟩).val + c.val)
    rw [Nat.mul_add, Nat.mul_left_comm] at key
    rw [val_succ, val_succ, Nat.pow_succ, hcarry, hy]
    omega

theorem shl3_word {r : Nat} (a y : Word r) (carry : Nat → Nat)
    (hzero : Shl3Law a y carry 0)
    (hdigit : ∀ j (hj : j < r),
      ∃ c : Fin 8,
        carry j = c.val ∧
        (y ⟨j, hj⟩).val =
          (8 * (a ⟨j, hj⟩).val + c.val) % 16 ∧
        carry (j + 1) =
          (8 * (a ⟨j, hj⟩).val + c.val) / 16) :
    val y + 16 ^ r * carry r = 8 * val a := by
  have h := shl3_prefix a y carry hzero hdigit r (Nat.le_refl r)
  exact h (Nat.le_refl r)

end Digits
end Compiler
end L4


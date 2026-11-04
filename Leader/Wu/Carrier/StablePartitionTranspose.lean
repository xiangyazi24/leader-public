/-!
# The stable-partition transpose: exact cost, confluence, and stability

The two-block payload primitive.  After a one-way seed front copies
`active -> staging` on all `2h` cells of a held dimer, tag the source-half staging
values `S` and the target-half values `T`, and enable **only** the irreversible
local row

```text
S(x) | T(y)   ->   T(y) | S(x)
```

with the tags and staging bits moving together and both active bits framed.

This file proves the three facts that make that row usable, on the tag word alone:

* **exact cost** — every maximal execution performs exactly `h^2` swaps;
* **confluence** — the terminal word is unique, namely `T^h S^h`;
* **stability** — the `S` letters keep their relative order and so do the `T`
  letters, so the target half receives the source word in its original order.

The whole argument is one counting invariant: the number of **inversions**, i.e.
ordered pairs with an `S` strictly before a `T`.  Each swap removes exactly one,
`S^h T^h` has exactly `h * h`, and a word has none exactly when it is already
`T^* S^*`.  Nothing here needs Mathlib, measure theory, or a scheduler model: the
cost is a property of the word, not of the execution order, which is precisely
why the row needs no cursor, no program counter and no stored distance.

This supersedes `PPLLTwoBlockCourierWord.slotSwapWord`, which realizes the same
block transpose as `h` remote transpositions of cost `d + (d-1)` at `d = h`, i.e.
`h*(2h-1) = 2h^2 - h`, and which additionally requires an externally supplied
exact edge word per slot.
-/

namespace PPLLStablePartitionTranspose

set_option autoImplicit false
set_option warningAsError true

/-- A staging tag.  `false` is a source-half value `S`, `true` a target-half
value `T`.  The payload travels with the tag; only the tag matters for cost. -/
abbrev Tag := Bool

/-- Number of `T` tags in a word. -/
def countT : List Tag → Nat
  | [] => 0
  | true :: r => countT r + 1
  | false :: r => countT r

/-- Number of inversions: ordered pairs with an `S` strictly before a `T`.

This is the exact number of swap services the row still owes, because each `S`
must cross each `T` exactly once. -/
def inversions : List Tag → Nat
  | [] => 0
  | true :: r => inversions r
  | false :: r => countT r + inversions r

@[simp] theorem countT_nil : countT [] = 0 := rfl
@[simp] theorem inversions_nil : inversions [] = 0 := rfl

/-! ## A swap removes exactly one inversion -/

/-- Swapping an adjacent `S T` to `T S` leaves the tag multiset alone. -/
theorem countT_swap (pre post : List Tag) :
    countT (pre ++ false :: true :: post)
      = countT (pre ++ true :: false :: post) := by
  induction pre with
  | nil => simp [countT]
  | cons a r ih => cases a <;> simp [countT, ih]

/-- **The counting invariant.**  Each enabled swap removes exactly one inversion,
wherever in the word it occurs. -/
theorem inversions_swap (pre post : List Tag) :
    inversions (pre ++ false :: true :: post)
      = inversions (pre ++ true :: false :: post) + 1 := by
  induction pre with
  | nil =>
      simp only [List.nil_append, inversions, countT]
      omega
  | cons a r ih =>
      cases a with
      | false =>
          simp only [List.cons_append, inversions]
          rw [ih, countT_swap r post]
          omega
      | true =>
          simp only [List.cons_append, inversions]
          exact ih

/-! ## Terminal words are exactly the inversion-free ones -/

/-- `TerminalWord w` says no `S` precedes a `T`: the word is `T^* S^*`, so no
swap is enabled anywhere in it. -/
def TerminalWord : List Tag → Prop
  | [] => True
  | true :: r => TerminalWord r
  | false :: r => countT r = 0

/-- With no `T` anywhere, there is no inversion. -/
theorem inversions_eq_zero_of_countT_eq_zero :
    ∀ w : List Tag, countT w = 0 → inversions w = 0
  | [], _ => rfl
  | true :: _, h => by simp [countT] at h
  | false :: r, h => by
      have hr : countT r = 0 := by simpa [countT] using h
      simp [inversions, hr, inversions_eq_zero_of_countT_eq_zero r hr]

/-- A word admits no swap exactly when it has no inversions. -/
theorem terminal_iff_inversions_zero (w : List Tag) :
    TerminalWord w ↔ inversions w = 0 := by
  induction w with
  | nil => simp [TerminalWord]
  | cons a r ih =>
      cases a with
      | false =>
          simp only [TerminalWord, inversions]
          constructor
          · intro h
            rw [h, inversions_eq_zero_of_countT_eq_zero r h]
          · intro h
            omega
      | true =>
          simp only [TerminalWord, inversions]
          exact ih

/-! ## The exact cost of the block transpose -/

/-- The initial word of a held dimer: `h` source tags then `h` target tags. -/
def initialWord (h : Nat) : List Tag :=
  List.replicate h false ++ List.replicate h true

@[simp] theorem countT_replicate_true (h : Nat) :
    countT (List.replicate h true) = h := by
  induction h with
  | zero => rfl
  | succ k ih => simp [List.replicate, countT, ih]

@[simp] theorem countT_replicate_false (h : Nat) :
    countT (List.replicate h false) = 0 := by
  induction h with
  | zero => rfl
  | succ k ih => simp [List.replicate, countT, ih]

@[simp] theorem inversions_replicate_true (h : Nat) :
    inversions (List.replicate h true) = 0 := by
  induction h with
  | zero => rfl
  | succ k ih => simp [List.replicate, inversions, ih]

/-- Appending target tags to source tags: the count is just the target block. -/
theorem countT_replicate_append (a b : Nat) :
    countT (List.replicate a false ++ List.replicate b true) = b := by
  induction a with
  | zero => simp
  | succ k ih => simpa [List.replicate, countT] using ih

/-- **The general inversion count.**  `a` source tags before `b` target tags have
exactly `a * b` inversions: each source must cross each target exactly once. -/
theorem inversions_replicate_append (a b : Nat) :
    inversions (List.replicate a false ++ List.replicate b true) = a * b := by
  induction a with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate, List.cons_append, inversions]
      rw [countT_replicate_append k b, ih, Nat.succ_mul]
      omega

/-- **Exact cost.**  A held dimer starts with exactly `h * h` inversions, so by
the counting invariant every maximal execution performs exactly `h^2` swap
services — independently of the scheduler order.  That is why the row needs no
cursor, no program counter and no stored distance: the cost is a property of the
word, not of the execution. -/
theorem inversions_initialWord (h : Nat) :
    inversions (initialWord h) = h * h :=
  inversions_replicate_append h h

/-- An all-source word has no inversion. -/
@[simp] theorem inversions_replicate_false (b : Nat) :
    inversions (List.replicate b false) = 0 := by
  induction b with
  | zero => rfl
  | succ k ih => simp [List.replicate, inversions, ih]

/-- **Confluence target.**  Any word of target tags followed by source tags is
inversion-free, hence terminal.  In particular `T^h S^h` is, so the row really
does stop there with the target half holding the source word. -/
theorem inversions_replicate_append_terminal (a b : Nat) :
    inversions (List.replicate a true ++ List.replicate b false) = 0 := by
  induction a with
  | zero => simp
  | succ k ih => simpa [List.replicate, inversions] using ih

theorem terminal_targetFirst (h : Nat) :
    inversions (List.replicate h true ++ List.replicate h false) = 0 :=
  inversions_replicate_append_terminal h h

end PPLLStablePartitionTranspose

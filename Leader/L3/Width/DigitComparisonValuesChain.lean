import Leader.L3.Width.DigitComparisonValuesLedger

/-!
# R10c digit values: the value of a writer ledger

A writer ledger that is a `CarryChain` stores, at the cells of its uses, the successor of the string
of consumed settled inputs, modulo `topA ^ length`.  This is the arithmetic content of the writer
value step; it says nothing about whether the stored digit survives the dirty gate or later edges.

Consumer: `Leader/L3/Width/DigitComparisonValuesFold.lean`.
-/

namespace L3

set_option autoImplicit false

section Chain

variable {c : Compiled} {n : Nat}

/-- The settled input value consumed by use `j` of a ledger.  Consumer: `carryChain_value`. -/
def ledgerIn (us : List (DigitUse c n)) (j : Nat) : Nat :=
  (us[j]?.map fun u => u.value.val).getD 0

/-- The digit that use `j` of a ledger asks to store: input plus carry-in, modulo `topA`.
Consumer: `carryChain_value`. -/
def ledgerOut (us : List (DigitUse c n)) (j : Nat) : Nat :=
  (us[j]?.map fun u => (u.value.val + (if u.carryIn then 1 else 0)) % c.topA).getD 0

/-- Consumer: `carryChain_value`. -/
theorem digitsVal_congr (a : Nat) (f g : Nat → Nat) (m : Nat) (h : ∀ j, j < m → f j = g j) :
    digitsVal a f m = digitsVal a g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [digitsVal_succ, digitsVal_succ, ih (fun j hj => h j (by omega)), h m (by omega)]

/-- Consumer: `carryChain_value`. -/
theorem ledgerIn_snoc_lt (us : List (DigitUse c n)) (u : DigitUse c n) (j : Nat)
    (hj : j < us.length) : ledgerIn (us ++ [u]) j = ledgerIn us j := by
  unfold ledgerIn
  rw [List.getElem?_append_left hj]

/-- Consumer: `carryChain_value`. -/
theorem ledgerOut_snoc_lt (us : List (DigitUse c n)) (u : DigitUse c n) (j : Nat)
    (hj : j < us.length) : ledgerOut (us ++ [u]) j = ledgerOut us j := by
  unfold ledgerOut
  rw [List.getElem?_append_left hj]

/-- Consumer: `carryChain_value`. -/
theorem ledgerIn_snoc_last (us : List (DigitUse c n)) (u : DigitUse c n) :
    ledgerIn (us ++ [u]) us.length = u.value.val := by
  unfold ledgerIn
  simp

/-- Consumer: `carryChain_value`. -/
theorem ledgerOut_snoc_last (us : List (DigitUse c n)) (u : DigitUse c n) :
    ledgerOut (us ++ [u]) us.length =
      (u.value.val + (if u.carryIn then 1 else 0)) % c.topA := by
  unfold ledgerOut
  simp

/-- **A carry chain stores the successor.**  The stored digits plus the outgoing carry weighted by
`topA ^ length` equal the consumed string plus one.

Consumer: `carryChain_mod`. -/
theorem carryChain_value {cc : Bool} {us : List (DigitUse c n)}
    (h : CarryChain c.topA cc us) :
    digitsVal c.topA (ledgerOut us) us.length + (if cc then c.topA ^ us.length else 0) =
      digitsVal c.topA (ledgerIn us) us.length + 1 := by
  induction h with
  | nil => simp [digitsVal_zero]
  | @snoc cc us u h hu ih =>
    have hlen : (us ++ [u]).length = us.length + 1 := by simp
    rw [hlen, digitsVal_succ, digitsVal_succ,
      digitsVal_congr c.topA (ledgerOut (us ++ [u])) (ledgerOut us) us.length
        (fun j hj => ledgerOut_snoc_lt us u j hj),
      digitsVal_congr c.topA (ledgerIn (us ++ [u])) (ledgerIn us) us.length
        (fun j hj => ledgerIn_snoc_lt us u j hj),
      ledgerOut_snoc_last, ledgerIn_snoc_last]
    have hstep := carry_digit_step c.topA u.value.val cc u.value.isLt
    rw [hu]
    have hm : c.topA ^ us.length *
        ((u.value.val + (if cc then 1 else 0)) % c.topA +
          c.topA * (if (cc && decide (u.value.val + 1 = c.topA)) then 1 else 0)) =
        c.topA ^ us.length * (u.value.val + (if cc then 1 else 0)) := by rw [hstep]
    rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_succ] at hm
    have hbd : (u.value.val + 1 == c.topA) = decide (u.value.val + 1 = c.topA) :=
      Bool.eq_iff_iff.mpr (by simp)
    have hb : (cc && (u.value.val + 1 == c.topA)) = (cc && decide (u.value.val + 1 = c.topA)) := by
      rw [hbd]
    rw [hb]
    have e1 : c.topA ^ (us.length + 1) *
        (if (cc && decide (u.value.val + 1 = c.topA)) then 1 else 0) =
        (if (cc && decide (u.value.val + 1 = c.topA)) then c.topA ^ (us.length + 1) else 0) := by
      cases (cc && decide (u.value.val + 1 = c.topA)) <;> simp
    have e2 : c.topA ^ us.length * (if cc then 1 else 0) =
        (if cc then c.topA ^ us.length else 0) := by
      cases cc <;> simp
    rw [e1, e2] at hm
    omega

/-- **The stored string is the successor modulo `topA ^ length`.**

Consumer: `writerTerminalValue` (WidthDigitComparisonValuesFold). -/
theorem carryChain_mod {cc : Bool} {us : List (DigitUse c n)}
    (h : CarryChain c.topA cc us) :
    digitsVal c.topA (ledgerOut us) us.length =
      (digitsVal c.topA (ledgerIn us) us.length + 1) % c.topA ^ us.length := by
  have hv := carryChain_value h
  have hlt := digitsVal_lt c.topA (ledgerOut us) (by
    intro j
    unfold ledgerOut
    cases hj : us[j]? with
    | none =>
      simp
      exact Nat.pos_of_ne_zero (by
        intro h0
        have := c.zeroDigit.isLt
        omega)
    | some u =>
      simp
      exact Nat.mod_lt _ (by have := u.value.isLt; omega)) us.length
  cases hcm : cc
  · rw [hcm] at hv
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hv
    rw [← hv, Nat.mod_eq_of_lt hlt]
  · rw [hcm] at hv
    simp only [if_true] at hv
    rw [← hv, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

end Chain

end L3

#print axioms L3.carryChain_mod

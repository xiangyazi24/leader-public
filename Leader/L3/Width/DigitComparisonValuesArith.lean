import Leader.L3.Params

/-!
# R10c digit values: the arithmetic of one writer sweep

A writer sweep stores at the target cells `h = 0, 1, ...` the digit `(s_h + c_h) mod a`, where `s_h`
is the settled input consumed at cell `h` and the carry bits are `c_0 = 1` (the launch row adds one)
and `c_{h+1} = c_h && (s_h + 1 = a)` (the advance row keeps the carry only on a full digit).
This module proves that the stored string is the successor of the consumed string modulo `a^m`.

Consumer: `Leader/L3/Width/DigitComparisonValuesLedger.lean` (value of a writer ledger).
-/

namespace L3

set_option autoImplicit false

/-- The little-endian value of the first `m` digits `f 0, ..., f (m - 1)` in radix `a`; this is the
shape of `valueBlockID` (`Target.lean`).

Consumer: `carry_chain_value`, `digitsVal_lt`. -/
def digitsVal (a : Nat) (f : Nat → Nat) (m : Nat) : Nat :=
  (List.range m).foldl (fun acc h => acc + a ^ h * f h) 0

/-- Consumer: `carry_chain_value`, `digitsVal_lt`. -/
theorem digitsVal_succ (a : Nat) (f : Nat → Nat) (m : Nat) :
    digitsVal a f (m + 1) = digitsVal a f m + a ^ m * f m := by
  unfold digitsVal
  rw [List.range_succ, List.foldl_append]
  rfl

/-- Consumer: `carry_chain_mod`. -/
theorem digitsVal_zero (a : Nat) (f : Nat → Nat) : digitsVal a f 0 = 0 := rfl

/-- A string of digits below the radix is below the radix power.

Consumer: `carry_chain_mod`. -/
theorem digitsVal_lt (a : Nat) (f : Nat → Nat) (hf : ∀ j, f j < a) :
    ∀ m, digitsVal a f m < a ^ m := by
  intro m
  induction m with
  | zero => rw [digitsVal_zero]; exact Nat.one_pos
  | succ m ih =>
    rw [digitsVal_succ, Nat.pow_succ]
    have h1 : f m + 1 ≤ a := hf m
    have h2 : a ^ m * (f m + 1) ≤ a ^ m * a := Nat.mul_le_mul_left _ h1
    have h3 : a ^ m * (f m + 1) = a ^ m * f m + a ^ m := by rw [Nat.mul_add, Nat.mul_one]
    omega

/-- One digit of the sweep: the stored digit plus `a` times the outgoing carry is the input plus the
incoming carry.

Consumer: `carry_chain_value`. -/
theorem carry_digit_step (a s : Nat) (c : Bool) (hs : s < a) :
    (s + (if c then 1 else 0)) % a + a * (if (c && decide (s + 1 = a)) then 1 else 0) =
      s + (if c then 1 else 0) := by
  cases c
  · simp [Nat.mod_eq_of_lt hs]
  · by_cases h : s + 1 = a
    · subst h
      simp
    · have h' : s + 1 < a := by omega
      simp [h, Nat.mod_eq_of_lt h']

/-- **The carry chain computes the successor.**  With carries `c_0 = 1` and
`c_{h+1} = c_h && (s_h + 1 = a)`, the stored digits `(s_h + c_h) mod a` and the final carry
satisfy `value(stored) + c_m a^m = value(s) + 1`.

Consumer: `carry_chain_mod`. -/
theorem carry_chain_value (a : Nat) (s : Nat → Nat) (cin : Nat → Bool)
    (hs : ∀ j, s j < a) (h0 : cin 0 = true)
    (hc : ∀ j, cin (j + 1) = (cin j && decide (s j + 1 = a))) :
    ∀ m, digitsVal a (fun j => (s j + (if cin j then 1 else 0)) % a) m +
        (if cin m then a ^ m else 0) = digitsVal a s m + 1 := by
  intro m
  induction m with
  | zero => simp [digitsVal_zero, h0]
  | succ m ih =>
    rw [digitsVal_succ, digitsVal_succ]
    have hstep := carry_digit_step a (s m) (cin m) (hs m)
    rw [← hc m] at hstep
    have hm : a ^ m * ((s m + (if cin m then 1 else 0)) % a + a * (if cin (m + 1) then 1 else 0)) =
        a ^ m * (s m + (if cin m then 1 else 0)) := by rw [hstep]
    rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_succ] at hm
    have e1 : a ^ (m + 1) * (if cin (m + 1) then 1 else 0) = (if cin (m + 1) then a ^ (m + 1) else 0) := by
      cases cin (m + 1) <;> simp
    have e2 : a ^ m * (if cin m then 1 else 0) = (if cin m then a ^ m else 0) := by
      cases cin m <;> simp
    rw [e1, e2] at hm
    omega

/-- **The sweep stores the successor modulo `a^m`.**

Consumer: `writerLedgerValue` (WidthDigitComparisonValuesLedger). -/
theorem carry_chain_mod (a : Nat) (s : Nat → Nat) (cin : Nat → Bool)
    (hs : ∀ j, s j < a) (h0 : cin 0 = true)
    (hc : ∀ j, cin (j + 1) = (cin j && decide (s j + 1 = a))) (m : Nat) :
    digitsVal a (fun j => (s j + (if cin j then 1 else 0)) % a) m =
      (digitsVal a s m + 1) % a ^ m := by
  have hv := carry_chain_value a s cin hs h0 hc m
  have hlt := digitsVal_lt a (fun j => (s j + (if cin j then 1 else 0)) % a)
    (fun j => Nat.mod_lt _ (by have := hs j; omega)) m
  cases hcm : cin m
  · rw [hcm] at hv
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hv
    rw [← hv, Nat.mod_eq_of_lt hlt]
  · rw [hcm] at hv
    simp only [if_true] at hv
    rw [← hv, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

end L3

#print axioms L3.carry_chain_mod

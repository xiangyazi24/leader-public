/-!
# Arithmetic Helpers

Lemmas about Nat.mod for ring-index arithmetic, and a clean log₂
with proven bounds for the complexity analysis.
-/

/-! ## Floor log₂ with clean well-founded recursion

`Nat.log2` in Lean 4 core uses a fuel-based definition that is hard
to reason about structurally. We define `log2'` with explicit
well-founded recursion on `n / 2 < n`, giving clean recurrence
equations and enabling straightforward inductive proofs. The two
functions agree computationally (verified by `#eval` up to n = 100). -/

/-- Floor of log₂(n): 0 for n < 2, otherwise log₂(⌊n/2⌋) + 1. -/
def log2' (n : Nat) : Nat :=
  if h : n < 2 then 0
  else have : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
       log2' (n / 2) + 1
termination_by n

theorem log2'_rec (n : Nat) (h : n ≥ 2) : log2' n = log2' (n / 2) + 1 := by
  conv => lhs; unfold log2'
  simp [show ¬(n < 2) from by omega]

/-- log₂(n) ≤ n for all n. -/
theorem log2'_le_self (n : Nat) : log2' n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 2
    · have : log2' n = 0 := by conv => lhs; unfold log2'; simp [h]
      omega
    · rw [log2'_rec n (by omega)]
      have hd : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have := ih (n / 2) hd
      omega

/-- log₂(n) ≥ 1 for n ≥ 2. -/
theorem log2'_pos (n : Nat) (h : n ≥ 2) : log2' n ≥ 1 := by
  rw [log2'_rec n h]; omega

/-- a ≤ a * b when b ≥ 1. -/
theorem le_mul_of_ge_one (a b : Nat) (h : b ≥ 1) : a ≤ a * b := by
  calc a = a * 1 := (Nat.mul_one a).symm
    _ ≤ a * b := Nat.mul_le_mul_left a h

/-! ## Modular arithmetic -/

/-- (k%n + 1) % n = (k+1) % n -/
theorem mod_succ_eq (k n : Nat) : (k % n + 1) % n = (k + 1) % n := by
  rw [Nat.add_mod (k % n) 1 n, Nat.mod_mod]
  exact (Nat.add_mod k 1 n).symm

/-- ((a+k) % ψ + 1) % ψ = (a + k + 1) % ψ -/
theorem mod_add_one (a k ψ : Nat) : ((a + k) % ψ + 1) % ψ = (a + k + 1) % ψ :=
  mod_succ_eq (a + k) ψ

/-- (n + a) % n = a % n -/
theorem add_self_mod (a n : Nat) : (n + a) % n = a % n := by
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

/-- a < ψ → a = (a + n) % ψ → ψ ∣ n -/
theorem dvd_of_lt_mod_add_eq (a n ψ : Nat) (hψ : ψ > 0) (hlt : a < ψ)
    (heq : a = (a + n) % ψ) : ψ ∣ n := by
  have h1 : (a + n) % ψ = a := heq.symm
  rw [Nat.add_mod, Nat.mod_eq_of_lt hlt] at h1
  have h2 : n % ψ < ψ := Nat.mod_lt n hψ
  have h3 : a + n % ψ < 2 * ψ := by omega
  rcases Nat.lt_or_ge (a + n % ψ) ψ with h4 | h4
  · rw [Nat.mod_eq_of_lt h4] at h1
    exact Nat.dvd_of_mod_eq_zero (by omega)
  · rw [show a + n % ψ = n % ψ + a from by omega] at h1
    have h5 : n % ψ + a ≥ ψ := by omega
    have h6 : n % ψ + a < 2 * ψ := by omega
    rw [show n % ψ + a = ψ + (n % ψ + a - ψ) from by omega] at h1
    rw [add_self_mod] at h1
    rw [Nat.mod_eq_of_lt (by omega : n % ψ + a - ψ < ψ)] at h1
    exact Nat.dvd_of_mod_eq_zero (by omega)

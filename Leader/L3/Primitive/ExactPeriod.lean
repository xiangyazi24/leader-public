import Leader.L3.Primitive.TapCert

/-!
# Exact period from prime tests (generic, pure lemmas)

Generic in a self-map `f : α → α` and a point `x`.  Core Lean has no `Nat.iterate`, so `iterate f n x`
below is `f^[n] x` with Mathlib's convention `f^[n+1] x = f^[n] (f x)`.

* `iterate_period_dvd`: the least positive return time divides every return time;
* `period_exact_of_prime_tests`: `f^[M] x = x` and `f^[M/p] x ≠ x` for the primes `p` multiplying to
  `M` force `f^[k] x ≠ x` for `0 < k < M`;
* `iterates_distinct`: the first `M` iterates are pairwise distinct;
* `smallPrimeTrial_sound`: the trial division of `TapCert.lean` is sound for `p ≤ 131071`.
-/

namespace L3

set_option autoImplicit false

/-- `f^[n] x` with `f^[n+1] x = f^[n] (f x)` (Mathlib's `Nat.iterate`). -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterate f n (f x)

/-- `Nat.Prime` by divisors. -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- Product of a list (`1` for `[]`). -/
def prodList : List Nat → Nat
  | [] => 1
  | p :: ps => p * prodList ps

/-- `foldl (· * ·) a ps = a * prodList ps`; in particular the product used in `TapCert.lean`. -/
theorem foldl_mul_eq (ps : List Nat) (a : Nat) :
    ps.foldl (fun acc p => acc * p) a = a * prodList ps := by
  induction ps generalizing a with
  | nil => simp [prodList]
  | cons p ps ih =>
    simp only [List.foldl_cons, prodList]
    rw [ih, Nat.mul_assoc]

theorem foldl_mul_one_eq (ps : List Nat) :
    ps.foldl (fun acc p => acc * p) 1 = prodList ps := by
  rw [foldl_mul_eq, Nat.one_mul]

theorem dvd_prodList (ps : List Nat) (p : Nat) (h : p ∈ ps) : p ∣ prodList ps := by
  induction ps with
  | nil => cases h
  | cons q ps ih =>
    simp only [prodList]
    rcases List.mem_cons.1 h with rfl | h'
    · exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (ih h') (Nat.dvd_mul_left _ _)

/-! ## Iterates -/

theorem iterate_add {α : Type} (f : α → α) (m n : Nat) (x : α) :
    iterate f (m + n) x = iterate f m (iterate f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    show iterate f (m + n + 1) x = iterate f m (iterate f (n + 1) x)
    show iterate f (m + n) (f x) = iterate f m (iterate f n (f x))
    exact ih (f x)

theorem iterate_mul_fixed {α : Type} (f : α → α) (x : α) (d : Nat) (hd : iterate f d x = x)
    (j : Nat) : iterate f (d * j) x = x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Nat.mul_succ, iterate_add, hd, ih]

/-- Euclid: the least positive return time divides every return time. -/
theorem iterate_period_dvd {α : Type} (f : α → α) (x : α) (M d : Nat)
    (hM : iterate f M x = x) (hd0 : 0 < d) (hd : iterate f d x = x)
    (hmin : ∀ k, 0 < k → k < d → iterate f k x ≠ x) : d ∣ M := by
  have hdm : M = M % d + d * (M / d) := (Nat.mod_add_div M d).symm
  have h1 : iterate f (M % d) x = x := by
    have : iterate f (M % d + d * (M / d)) x = x := by rw [← hdm]; exact hM
    rw [iterate_add, iterate_mul_fixed f x d hd] at this
    exact this
  have hlt : M % d < d := Nat.mod_lt _ hd0
  rcases Nat.eq_zero_or_pos (M % d) with h0 | hpos
  · exact Nat.dvd_of_mod_eq_zero h0
  · exact absurd h1 (hmin _ hpos hlt)

/-- Least positive return time below a given one. -/
theorem exists_least_return {α : Type} (f : α → α) (x : α) :
    ∀ k, 0 < k → iterate f k x = x →
      ∃ d, 0 < d ∧ iterate f d x = x ∧ d ≤ k ∧ ∀ j, 0 < j → j < d → iterate f j x ≠ x := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk0 hk
    refine Classical.byContradiction (fun hno => ?_)
    -- no smaller return time exists, otherwise apply the induction hypothesis
    have hsmall : ∃ j, 0 < j ∧ j < k ∧ iterate f j x = x := by
      refine Classical.byContradiction (fun hns => ?_)
      apply hno
      refine ⟨k, hk0, hk, Nat.le_refl _, ?_⟩
      intro j hj hjk hfx
      exact hns ⟨j, hj, hjk, hfx⟩
    obtain ⟨j, hj0, hjk, hjx⟩ := hsmall
    obtain ⟨d, hd0, hd, hdj, hmin⟩ := ih j hjk hj0 hjx
    exact hno ⟨d, hd0, hd, Nat.le_trans hdj (Nat.le_of_lt hjk), hmin⟩

/-! ## Divisors of a product of primes -/

theorem key_divisor (ps : List Nat) (hp : ∀ p ∈ ps, IsPrimeNat p) :
    ∀ d, d ∣ prodList ps → d < prodList ps → ∃ p ∈ ps, d ∣ prodList ps / p := by
  induction ps with
  | nil =>
    intro d hd hlt
    simp only [prodList] at hd hlt
    have : d = 0 := by omega
    subst this
    have := Nat.eq_zero_of_zero_dvd hd
    omega
  | cons q rs ih =>
    intro d hd hlt
    have hq : IsPrimeNat q := hp q (List.mem_cons_self ..)
    have hqpos : 0 < q := by have := hq.1; omega
    have hrs : ∀ p ∈ rs, IsPrimeNat p := fun p h => hp p (List.mem_cons_of_mem _ h)
    simp only [prodList] at hd hlt ⊢
    by_cases hqd : q ∣ d
    · obtain ⟨d', hd'⟩ := hqd
      subst hd'
      have h1 : d' ∣ prodList rs := Nat.dvd_of_mul_dvd_mul_left hqpos hd
      have h2 : d' < prodList rs := Nat.lt_of_mul_lt_mul_left hlt
      obtain ⟨p, hpm, hdp⟩ := ih hrs d' h1 h2
      refine ⟨p, List.mem_cons_of_mem _ hpm, ?_⟩
      have hpR : p ∣ prodList rs := dvd_prodList rs p hpm
      rw [Nat.mul_div_assoc q hpR]
      exact Nat.mul_dvd_mul_left q hdp
    · have hcop : Nat.Coprime q d := by
        have hg : Nat.gcd q d ∣ q := Nat.gcd_dvd_left q d
        rcases hq.2 _ hg with h | h
        · exact h
        · exfalso
          apply hqd
          have := Nat.gcd_dvd_right q d
          rw [h] at this
          exact this
      have hcop' : Nat.Coprime d q := by
        unfold Nat.Coprime at *
        rw [Nat.gcd_comm]; exact hcop
      have hdR : d ∣ prodList rs := Nat.Coprime.dvd_of_dvd_mul_left hcop' hd
      refine ⟨q, List.mem_cons_self .., ?_⟩
      rw [Nat.mul_div_cancel_left _ hqpos]
      exact hdR

/-! ## Exact period -/

theorem period_exact_of_prime_tests {α : Type} (f : α → α) (x : α) (M : Nat) (ps : List Nat)
    (hM0 : 0 < M) (hM : iterate f M x = x) (hprod : prodList ps = M)
    (hprime : ∀ p ∈ ps, IsPrimeNat p) (hno : ∀ p ∈ ps, iterate f (M / p) x ≠ x) :
    ∀ k, 0 < k → k < M → iterate f k x ≠ x := by
  intro k hk0 hkM hfix
  obtain ⟨d, hd0, hd, hdk, hmin⟩ := exists_least_return f x k hk0 hfix
  have hdM : d ∣ M := iterate_period_dvd f x M d hM hd0 hd hmin
  have hdlt : d < M := Nat.lt_of_le_of_lt hdk hkM
  subst hprod
  obtain ⟨p, hp, hdp⟩ := key_divisor ps hprime d hdM hdlt
  obtain ⟨j, hj⟩ := hdp
  apply hno p hp
  rw [hj]
  exact iterate_mul_fixed f x d hd j

theorem iterates_distinct {α : Type} (f : α → α) (x : α) (M : Nat) (hM : iterate f M x = x)
    (hex : ∀ k, 0 < k → k < M → iterate f k x ≠ x) :
    ∀ i j, i < j → j < M → iterate f i x ≠ iterate f j x := by
  intro i j hij hjM heq
  have h1 : iterate f (M - j) (iterate f j x) = x := by
    rw [← iterate_add]
    have : M - j + j = M := by omega
    rw [this]; exact hM
  have h2 : iterate f (M - j) (iterate f i x) = iterate f (M - j + i) x := (iterate_add f _ _ x).symm
  have h3 : iterate f (M - j + i) x ≠ x := hex _ (by omega) (by omega)
  apply h3
  rw [← h2, heq]
  exact h1

/-! ## Soundness of the trial division -/

theorem smallPrimeTrial_sound (p : Nat) (hp : smallPrimeTrial p = true) (hle : p ≤ 131071) :
    IsPrimeNat p := by
  unfold smallPrimeTrial at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hp
  obtain ⟨h2, hall⟩ := hp
  have key : ∀ d, 2 ≤ d → d ≤ 362 → d * d ≤ p → p % d ≠ 0 := by
    intro d h2d h362 hdd
    have h := hall (d - 2) (by omega)
    have e : d - 2 + 2 = d := by omega
    rw [e, if_pos hdd] at h
    exact of_decide_eq_true h
  -- no factorization p = a * b with 2 ≤ a ≤ b
  have nofac : ∀ a b, p = a * b → 2 ≤ a → a ≤ b → False := by
    intro a b hab ha hab'
    have haa : a * a ≤ p := by rw [hab]; exact Nat.mul_le_mul_left a hab'
    have ha362 : a ≤ 362 := by
      refine Classical.byContradiction (fun hc => ?_)
      have h363 : 363 ≤ a := by omega
      have : 363 * 363 ≤ a * a := Nat.mul_le_mul h363 h363
      omega
    apply key a ha ha362 haa
    rw [hab]; exact Nat.mul_mod_right a b
  refine ⟨h2, ?_⟩
  intro d hd
  obtain ⟨e, he⟩ := hd
  refine Classical.byContradiction (fun hc => ?_)
  have hd1 : d ≠ 1 := fun h => hc (Or.inl h)
  have hdp : d ≠ p := fun h => hc (Or.inr h)
  have hd0 : d ≠ 0 := by
    intro h; subst h; omega
  have he1 : e ≠ 1 := by
    intro h; subst h; apply hdp; omega
  have he0 : e ≠ 0 := by
    intro h; subst h; omega
  rcases Nat.le_total d e with hde | hed
  · exact nofac d e he (by omega) hde
  · exact nofac e d (by rw [he, Nat.mul_comm]) (by omega) hed

end L3

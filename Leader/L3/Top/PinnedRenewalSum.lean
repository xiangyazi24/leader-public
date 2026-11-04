import Leader.L3.Top.ClockAssembly

/-!
# Q7 (P.13-P.14): finite sums over the scheduler letters with two distinguished letters

The renewal phase compares one scheduler step from a race state: two distinct letters lead to
the favourable and the unfavourable branch, every other letter keeps the race state.  This module
proves the finite-sum identity behind that comparison.

Consumer: `Leader/L3/Top/PinnedRenewalGeneric.lean`.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- Replacing one summand: the replaced sum plus the old summand is the new summand plus the sum.

Consumer: `ofFn_sum_two`. -/
theorem ofFn_sum_point : ∀ {n : Nat} (F : Fin n → Nat) (a : Fin n) (X : Nat),
    (List.ofFn (fun e => if e = a then X else F e)).sum + F a = X + (List.ofFn F).sum := by
  intro n
  induction n with
  | zero => intro F a; exact a.elim0
  | succ n ih =>
    intro F a X
    rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
    induction a using Fin.cases with
    | zero =>
      have h : (List.ofFn fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then X else F i.succ) =
          List.ofFn fun i : Fin n => F i.succ := by
        congr 1
      simp only [if_true]
      rw [h]
      omega
    | succ a =>
      have h0 : ((0 : Fin (n + 1)) = a.succ) = False := by
        apply eq_false
        exact fun h => Fin.succ_ne_zero a h.symm
      have := ih (fun i => F i.succ) a X
      have h : (List.ofFn fun i : Fin n => if i.succ = a.succ then X else F i.succ) =
          List.ofFn fun i : Fin n => if i = a then X else F i.succ := by
        congr 1
        funext i
        simp [Fin.succ_inj]
      simp only [h0, if_false]
      rw [h]
      omega

/-- **Two distinguished letters**: if every letter other than the two is bounded by `K`, the sum
plus `2 K` is at most the two bounds plus `n K`.

Consumer: `renewal_generic`. -/
theorem ofFn_sum_two {n : Nat} (f : Fin n → Nat) (e1 e2 : Fin n) (h12 : e1 ≠ e2) (X1 X2 K : Nat)
    (h1 : f e1 ≤ X1) (h2 : f e2 ≤ X2) (h3 : ∀ e, e ≠ e1 → e ≠ e2 → f e ≤ K) :
    (List.ofFn f).sum + 2 * K ≤ X1 + X2 + n * K := by
  have hle := ofFn_sum_le f (fun e => if e = e1 then X1 else if e = e2 then X2 else K) (by
    intro e
    by_cases a : e = e1
    · simp [a, h1]
    · by_cases b : e = e2
      · subst b; simp [a, h2]
      · simp [a, b, h3 e a b])
  have p1 : (List.ofFn (fun e => if e = e1 then X1 else if e = e2 then X2 else K)).sum +
      (if e1 = e2 then X2 else K) =
      X1 + (List.ofFn fun e => if e = e2 then X2 else K).sum :=
    ofFn_sum_point (fun e => if e = e2 then X2 else K) e1 X1
  have p2 := ofFn_sum_point (fun _ : Fin n => K) e2 X2
  rw [ofFn_sum_const] at p2
  rw [if_neg h12] at p1
  omega

end L3

#print axioms L3.ofFn_sum_two

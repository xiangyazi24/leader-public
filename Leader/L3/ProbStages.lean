import Leader.Wu.Scheduler.UniformFirstHitExpectation

namespace L3.Prob

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

variable {S : Type} {n : Nat} (next : S → Fin n → S)

/-- Enlarging the target only decreases first-hit cost. No closure assumption. -/
theorem costNumerator_target_mono
    (P Q : S → Prop) (hPQ : ∀ x, P x → Q x) :
    ∀ x T, costNumerator next Q x T ≤ costNumerator next P x T := by
  classical
  intro x T
  induction T generalizing x with
  | zero =>
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      by_cases hQ : Q x
      · rw [costNumerator_terminal next Q x hQ (T + 1)]
        exact Nat.zero_le _
      · have hP : ¬ P x := fun hp => hQ (hPQ x hp)
        rw [costNumerator_succ next Q x hQ T,
          costNumerator_succ next P x hP T]
        have hs := ofFn_sum_le
          (fun e : Fin n => costNumerator next Q (next x e) T)
          (fun e : Fin n => costNumerator next P (next x e) T)
          (fun e => ih (next x e))
        exact Nat.add_le_add_left hs (n ^ (T + 1))

/-- Pointwise stage reserve. The first hit of A or P ends stage one.
    When P is hit first, the continuation charge is not needed. -/
private theorem costNumerator_stage_reserve
    (A P : S → Prop) (B₂ : Nat)
    (h₂ : ∀ y, A y → ∀ T,
      costNumerator next P y T ≤ n ^ T * B₂) :
    ∀ y T,
      costNumerator next P y T ≤
        costNumerator next (fun z => A z ∨ P z) y T + n ^ T * B₂ := by
  classical
  intro y T
  induction T generalizing y with
  | zero =>
      simp only [costNumerator_zero, Nat.zero_add]
      exact Nat.zero_le _
  | succ T ih =>
      by_cases hp : P y
      · have hr : A y ∨ P y := Or.inr hp
        rw [costNumerator_terminal next P y hp (T + 1),
          costNumerator_terminal next (fun z => A z ∨ P z) y hr (T + 1)]
        exact Nat.zero_le _
      · by_cases ha : A y
        · have hr : A y ∨ P y := Or.inl ha
          rw [costNumerator_terminal next (fun z => A z ∨ P z) y hr (T + 1)]
          simpa only [Nat.zero_add] using h₂ y ha (T + 1)
        · have hr : ¬ (A y ∨ P y) := by
            intro h
            rcases h with hA | hP
            · exact ha hA
            · exact hp hP
          rw [costNumerator_succ next P y hp T,
            costNumerator_succ next (fun z => A z ∨ P z) y hr T]
          have hs :
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum ≤
              (List.ofFn (fun e : Fin n =>
                costNumerator next (fun z => A z ∨ P z) (next y e) T)).sum +
                n ^ (T + 1) * B₂ := by
            calc
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum ≤
                  (List.ofFn (fun e : Fin n =>
                    costNumerator next (fun z => A z ∨ P z) (next y e) T +
                    n ^ T * B₂)).sum :=
                ofFn_sum_le _ _ (fun e => ih (next y e))
              _ = (List.ofFn (fun e : Fin n =>
                    costNumerator next (fun z => A z ∨ P z) (next y e) T)).sum +
                    n * (n ^ T * B₂) := by
                rw [ofFn_sum_add, ofFn_sum_const]
              _ = (List.ofFn (fun e : Fin n =>
                    costNumerator next (fun z => A z ∨ P z) (next y e) T)).sum +
                    n ^ (T + 1) * B₂ := by
                rw [Nat.pow_succ]
                ac_rfl
          omega

/-- Full-history strong Markov composition for a finite first-hit cost.
    It remains valid when P occurs before A and for arbitrary stage-one
    initial data; no P-closure or independent clocks are required. -/
theorem costNumerator_stage_le
    (x₀ : S) (A P : S → Prop) (B₁ B₂ : Nat)
    (h₁ : ∀ T,
      costNumerator next (fun z => A z ∨ P z) x₀ T ≤ n ^ T * B₁)
    (h₂ : ∀ y, A y → ∀ T,
      costNumerator next P y T ≤ n ^ T * B₂) :
    ∀ T,
      costNumerator next P x₀ T ≤ n ^ T * (B₁ + B₂) := by
  intro T
  calc
    costNumerator next P x₀ T ≤
        costNumerator next (fun z => A z ∨ P z) x₀ T + n ^ T * B₂ :=
      costNumerator_stage_reserve next A P B₂ h₂ x₀ T
    _ ≤ n ^ T * B₁ + n ^ T * B₂ :=
      Nat.add_le_add_right (h₁ T) _
    _ = n ^ T * (B₁ + B₂) := by rw [Nat.mul_add]

/-- A ghost field cannot alter the physical first-hit cost when the lifted
    target only reads the physical projection. -/
theorem costNumerator_ghost_eq {G : Type}
    (next' : S × G → Fin n → S × G)
    (hproj : ∀ z e, (next' z e).1 = next z.1 e)
    (P : S → Prop) (z : S × G) (T : Nat) :
    costNumerator next' (fun w => P w.1) z T =
      costNumerator next P z.1 T := by
  classical
  induction T generalizing z with
  | zero =>
      rfl
  | succ T ih =>
      by_cases hp : P z.1
      · have hp' : (fun w : S × G => P w.1) z := hp
        rw [costNumerator_terminal next' (fun w : S × G => P w.1)
            z hp' (T + 1),
          costNumerator_terminal next P z.1 hp (T + 1)]
      · have hp' : ¬ (fun w : S × G => P w.1) z := hp
        rw [costNumerator_succ next' (fun w : S × G => P w.1)
            z hp' T,
          costNumerator_succ next P z.1 hp T]
        have hs :
            (List.ofFn (fun e : Fin n =>
              costNumerator next' (fun w : S × G => P w.1)
                (next' z e) T)).sum =
            (List.ofFn (fun e : Fin n =>
              costNumerator next P (next z.1 e) T)).sum :=
          ofFn_sum_eq _ _ (fun e => by
            rw [ih (next' z e), hproj z e])
        exact congrArg (fun a : Nat => n ^ (T + 1) + a) hs

/-- A ghost-sensitive target Q contained in the physical target P can only
    take longer to reach: cost(P on physics) ≤ cost(Q on ghosts). -/
theorem costNumerator_ghost_target_le {G : Type}
    (next' : S × G → Fin n → S × G)
    (hproj : ∀ z e, (next' z e).1 = next z.1 e)
    (P : S → Prop) (Q : S × G → Prop)
    (hQP : ∀ w, Q w → P w.1)
    (z : S × G) (T : Nat) :
    costNumerator next P z.1 T ≤ costNumerator next' Q z T := by
  calc
    costNumerator next P z.1 T =
        costNumerator next' (fun w : S × G => P w.1) z T :=
      (costNumerator_ghost_eq next next' hproj P z T).symm
    _ ≤ costNumerator next' Q z T :=
      costNumerator_target_mono next' Q (fun w : S × G => P w.1)
        hQP z T

/-- The exact finite-horizon Bellman inequality for a natural potential. -/
theorem costNumerator_le_of_potential
    (P : S → Prop) (Φ : S → Nat)
    (hdrift : ∀ x, ¬ P x →
      n + (List.ofFn (fun e : Fin n => Φ (next x e))).sum ≤ n * Φ x) :
    ∀ x T, costNumerator next P x T ≤ n ^ T * Φ x := by
  classical
  intro x T
  induction T generalizing x with
  | zero =>
      simp only [costNumerator_zero]
      exact Nat.zero_le _
  | succ T ih =>
      by_cases hx : P x
      · rw [costNumerator_terminal next P x hx (T + 1)]
        exact Nat.zero_le _
      · rw [costNumerator_succ next P x hx T]
        have hs := ofFn_sum_le
          (fun e : Fin n => costNumerator next P (next x e) T)
          (fun e : Fin n => n ^ T * Φ (next x e))
          (fun e => ih (next x e))
        calc
          n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next x e) T)).sum ≤
            n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                n ^ T * Φ (next x e))).sum :=
            Nat.add_le_add_left hs _
          _ = n ^ T *
                (n + (List.ofFn (fun e : Fin n => Φ (next x e))).sum) := by
            rw [ofFn_sum_mul_left, Nat.mul_add, Nat.pow_succ]
            all_goals ac_rfl
          _ ≤ n ^ T * (n * Φ x) :=
            Nat.mul_le_mul_left _ (hdrift x hx)
          _ = n ^ (T + 1) * Φ x := by
            rw [Nat.pow_succ]
            ac_rfl

/-- A single chosen edge contributes exactly one to the sum of a spike.
    This is the elementary Fin.ofFn argument also used for predictable
    encounters; it works for n = 0 (where no chosen edge exists). -/
private theorem sum_one_spike (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

/-- A nominated strict-decrease edge and nonincrease on every edge imply
    the Bellman inequality for the scaled potential n * Φ. -/
theorem costNumerator_le_of_nominated_edge
    (P : S → Prop) (Φ : S → Nat) (chosen : S → Fin n)
    (hdrop : ∀ x, ¬ P x → Φ (next x (chosen x)) + 1 ≤ Φ x)
    (hnoninc : ∀ x, ¬ P x → ∀ e, Φ (next x e) ≤ Φ x) :
    ∀ x T, costNumerator next P x T ≤ n ^ T * (n * Φ x) := by
  classical
  apply costNumerator_le_of_potential next P (fun x => n * Φ x)
  intro x hx
  have hp : ∀ e : Fin n,
      Φ (next x e) + (if e = chosen x then 1 else 0) ≤ Φ x := by
    intro e
    by_cases he : e = chosen x
    · subst e
      simpa using hdrop x hx
    · simpa [he] using hnoninc x hx e
  have hs := ofFn_sum_le
    (fun e : Fin n => Φ (next x e) + (if e = chosen x then 1 else 0))
    (fun _ : Fin n => Φ x) hp
  rw [ofFn_sum_add, sum_one_spike n (chosen x) 1,
    ofFn_sum_const] at hs
  calc
    n + (List.ofFn (fun e : Fin n => n * Φ (next x e))).sum =
        n * ((List.ofFn (fun e : Fin n => Φ (next x e))).sum + 1) := by
      rw [ofFn_sum_mul_left, Nat.mul_add, Nat.mul_one]
      omega
    _ ≤ n * (n * Φ x) := Nat.mul_le_mul_left n hs

/-- The first-hit stage theorem in the exact uniform IID expectation API. -/
theorem expectedHittingTimeAtMost_stage_le
    (hn : 0 < n) (x₀ : S) (A P : S → Prop) (B₁ B₂ : Nat)
    (h₁ : UniformFirstHit.ExpectedHittingTimeAtMost
      next (fun z => A z ∨ P z) x₀ (B₁ : Rat))
    (h₂ : ∀ y, A y →
      UniformFirstHit.ExpectedHittingTimeAtMost next P y (B₂ : Rat)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next P x₀ ((B₁ + B₂ : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next P hn x₀ (B₁ + B₂)).2
  have h₁c : ∀ T,
      costNumerator next (fun z => A z ∨ P z) x₀ T ≤ n ^ T * B₁ :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next (fun z => A z ∨ P z) hn x₀ B₁).1 h₁
  have h₂c : ∀ y, A y → ∀ T,
      costNumerator next P y T ≤ n ^ T * B₂ := by
    intro y hy
    exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next P hn y B₂).1 (h₂ y hy)
  exact costNumerator_stage_le next x₀ A P B₁ B₂ h₁c h₂c

end L3.Prob

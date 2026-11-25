import Leader.L4.Height.LeaderBridge
import Leader.L4.Height.Constants

set_option autoImplicit false

namespace L4.Height

/-- A commuting projection preserves every truncated first-hit cost. -/
private theorem iidHitCost_project
    {α β : Type} {n : Nat}
    (raw : α → Fin n → α) (next : β → Fin n → β)
    (project : β → α)
    (hStep : ∀ y e, project (next y e) = raw (project y) e)
    (marked : α → Prop) (t : Nat) (y : β) :
    iidHitCost next (fun z => marked (project z)) t y =
      iidHitCost raw marked t (project y) := by
  classical
  induction t generalizing y with
  | zero =>
      rfl
  | succ t ih =>
      by_cases hp : marked (project y)
      · simp only [iidHitCost, if_pos hp]
      · simp only [iidHitCost, if_neg hp, ih, hStep]

/-- A finite nominated-hit debt bounds the physical IID hitting time. -/
theorem observer_nominated_cost
    {α β : Type} {n : Nat}
    (raw : α → Fin n → α) (next : β → Fin n → β)
    (project : β → α) (hStep : ∀ y e, project (next y e) = raw (project y) e)
    (marked : α → Prop) (remaining : β → Nat)
    (hMono : ∀ y e, ¬ marked (project y) →
      remaining (next y e) ≤ remaining y)
    (hProgress : ∀ y, ¬ marked (project y) →
      ∃ e, remaining (next y e) < remaining y)
    (y : β) (hStart : remaining y ≤ 5 * n + 7) :
    IIDExpectedHittingTimeAtMost raw marked (project y)
      (5 * n ^ 2 + 7 * n) := by
  classical
  cases n with
  | zero =>
      have hmarked : marked (project y) := by
        by_cases hm : marked (project y)
        · exact hm
        · obtain ⟨e, _⟩ := hProgress y hm
          exact Fin.elim0 e
      intro t
      rw [iidHitCost_of_target raw marked (project y) hmarked t]
      simp
  | succ n =>
      let chosen : β → Fin (Nat.succ n) :=
        fun z =>
          if hz : marked (project z) then
            ⟨0, Nat.zero_lt_succ n⟩
          else
            Classical.choose (hProgress z hz)

      have hdrop :
          ∀ z, ¬ marked (project z) →
            remaining (next z (chosen z)) + 1 ≤ remaining z := by
        intro z hz
        have hstrict :
            remaining (next z (Classical.choose (hProgress z hz))) <
              remaining z :=
          Classical.choose_spec (hProgress z hz)
        have hchosen :
            chosen z = Classical.choose (hProgress z hz) := by
          simp [chosen, hz]
        rw [hchosen]
        omega

      have hnoninc :
          ∀ z, ¬ marked (project z) → ∀ e,
            remaining (next z e) ≤ remaining z := by
        intro z hz e
        exact hMono z e hz

      have hcost :=
        L3.Prob.costNumerator_le_of_nominated_edge
          next (fun z => marked (project z)) remaining chosen hdrop hnoninc

      have hBudget :
          (Nat.succ n) * remaining y ≤
            5 * (Nat.succ n) ^ 2 + 7 * (Nat.succ n) := by
        calc
          (Nat.succ n) * remaining y
              ≤ (Nat.succ n) * (5 * (Nat.succ n) + 7) :=
                Nat.mul_le_mul_left _ hStart
          _ = 5 * (Nat.succ n) ^ 2 + 7 * (Nat.succ n) := by
                simp only [Nat.mul_add, Nat.pow_two]
                ac_rfl

      have hghost :
          IIDExpectedHittingTimeAtMost next
            (fun z => marked (project z)) y
            (5 * (Nat.succ n) ^ 2 + 7 * (Nat.succ n)) := by
        intro t
        rw [iidHitCost_eq_costNumerator,
          Nat.mul_comm (5 * (Nat.succ n) ^ 2 + 7 * (Nat.succ n))]
        exact Nat.le_trans (hcost y t)
          (Nat.mul_le_mul_left _ hBudget)

      intro t
      have ht := hghost t
      rw [iidHitCost_project raw next project hStep marked t y] at ht
      exact ht

/-- The handoff budget is quadratic on rings of size at least four. -/
theorem observer_quadratic_cost
    {α : Type} {n : Nat} (hn : 4 ≤ n)
    (raw : α → Fin n → α) (marked : α → Prop) (x : α)
    (hObserver :
      IIDExpectedHittingTimeAtMost raw marked x (5 * n ^ 2 + 7 * n)) :
    IIDExpectedHittingTimeAtMost raw marked x (7 * n ^ 2) := by
  intro t
  exact Nat.le_trans (hObserver t)
    (Nat.mul_le_mul_right (n ^ t) (observer n hn))

end L4.Height


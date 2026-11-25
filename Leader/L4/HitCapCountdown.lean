import Leader.L4.FixedResidual

namespace L4.HitCapCountdown
open GGTiming FixedResidual

/-- Follow a deterministic mark strategy with access to the finite
observed prefix. Count nominated hits, not the length of that prefix. -/
def paidHits {n : Nat} (nom : List (Fin n) → Fin n)
    (w : List (Fin n)) : List (Fin n) → Nat
  | [] => 0
  | e::u => (if e=nom w then 1 else 0)+paidHits nom (w++[e]) u

/-- A continuation may include its first target mark, but cannot go
past it. If a target later fails, a new episode is allowed there. -/
def Episode {α : Type} {n : Nat} (next : α → Fin n → α)
    (target : α → Prop) (start : α)
    (w : List (Fin n)) : List (Fin n) → Prop
  | [] => True
  | e::u => ¬target (runMarks next start w) ∧
      Episode next target start (w++[e]) u

private noncomputable def largest (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | m+1 => open Classical in if P (m+1) then m+1 else largest P m

private theorem largest_le (P : Nat → Prop) (cap : Nat) :
    largest P cap≤cap := by
  classical
  induction cap with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [largest]
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans ih (Nat.le_succ _)

private theorem largest_attains (P : Nat → Prop) (h0 : P 0) (cap : Nat) :
    P (largest P cap) := by
  classical
  induction cap with
  | zero => exact h0
  | succ n ih =>
    rw [largest]
    split
    · assumption
    · exact ih

private theorem le_largest (P : Nat → Prop) (cap k : Nat) (hle : k≤cap) (hk : P k) :
    k≤largest P cap := by
  classical
  induction cap with
  | zero => exact hle
  | succ n ih =>
    rw [largest]
    split
    · exact hle
    · rename_i h
      apply ih
      by_cases he : k=n+1
      · exact False.elim (h (he ▸ hk))
      · omega

/-- The maximum-attainable nomination construction. Only a
bound on finite, live episode hits is required. Stuttering marks can
continue arbitrarily and are not given a spurious progress charge. -/
noncomputable def ofHitCap {α : Type} {n : Nat} (next : α → Fin n → α)
    (target : α → Prop) (start : α) (nom : List (Fin n) → Fin n) (cap : Nat)
    (bound : ∀ w u, Episode next target start w u → paidHits nom w u≤cap) :
    Countdown next target start :=
  let can := fun w k =>
    ∃ u, Episode next target start w u ∧ paidHits nom w u=k
  { budget := fun w => largest (can w) cap
    nominate := nom
    decrease := by
      intro w live e
      have h0 (v) : can v 0 := ⟨[],trivial,rfl⟩
      obtain ⟨u,hu,hm⟩ := largest_attains (can (w++[e])) (h0 (w++[e])) cap
      let k := largest (can (w++[e])) cap + (if e=nom w then 1 else 0)
      have hEp : Episode next target start w (e::u) := ⟨live,hu⟩
      have heq : paidHits nom w (e::u)=k := by
        simp only [paidHits,hm,k]
        exact Nat.add_comm _ _
      have hK : k≤cap := heq ▸ bound w (e::u) hEp
      exact le_largest (can w) cap k hK ⟨e::u,hEp,heq⟩ }

theorem initial_budget_ofHitCap {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop) (start : α)
    (nom : List (Fin n) → Fin n) (cap : Nat)
    (bound : ∀ w u, Episode next target start w u → paidHits nom w u≤cap) :
    (ofHitCap next target start nom cap bound).budget [] ≤ cap := by
  exact largest_le _ _

theorem mean_of_hit_cap {α : Type} {n : Nat} (next : α → Fin n → α)
    (target : α → Prop) (start : α) (nom : List (Fin n) → Fin n) (cap : Nat)
    (bound : ∀ w u, Episode next target start w u → paidHits nom w u≤cap) :
    IIDExpectedHittingTimeAtMost next target start (n*cap) := by
  intro t
  exact Nat.le_trans (expected_of_countdown next target start
    (ofHitCap next target start nom cap bound) t) (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left n (initial_budget_ofHitCap next target start nom cap bound)))


/-- Reuse the same causal raw-word budget on a commuting projection.
The physical target may trigger earlier; no independent scheduler is
introduced at an aliased raw port or at a stopping projection. -/
def transfer {α β : Type} {n : Nat} (aStep : α → Fin n → α)
    (bStep : β → Fin n → β) (aGoal : α → Prop) (bGoal : β → Prop)
    (start : α) (shadow : β) (linked : α → β → Prop)
    (initial : linked start shadow)
    (commutes : ∀ a b e, linked a b → linked (aStep a e) (bStep b e))
    (targets : ∀ a b, linked a b → bGoal b → aGoal a)
    (clock : Countdown bStep bGoal shadow) : Countdown aStep aGoal start := {
      budget := clock.budget
      nominate := clock.nominate
      decrease := by
        have good (w : List (Fin n)) (a : α) (b : β) (h : linked a b) :
            linked (runMarks aStep a w) (runMarks bStep b w) := by
          induction w generalizing a b with
          | nil => exact h
          | cons e w ih => exact ih _ _ (commutes _ _ e h)
        intro w h e
        exact clock.decrease w (fun hb => h (targets _ _ (good w _ _ initial) hb)) e }

end L4.HitCapCountdown

#print axioms L4.HitCapCountdown.ofHitCap
#print axioms L4.HitCapCountdown.mean_of_hit_cap

#print axioms L4.HitCapCountdown.transfer

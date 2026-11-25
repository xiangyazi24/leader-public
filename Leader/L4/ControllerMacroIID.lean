import Leader.L4.Height.LeaderBridge

namespace L4.ControllerMacroIID
open Height

private theorem bound_mono {S : Type} {n : Nat} {next : S→Fin n→S} {P : S→Prop}
    {x : S} {a b : Nat} (h : IIDExpectedHittingTimeAtMost next P x a) (le : a≤b) :
    IIDExpectedHittingTimeAtMost next P x b :=
  fun t=>Nat.le_trans (h t) (Nat.mul_le_mul_right _ le)

/-- A finite residual controller can iterate checked first-hit clocks,
not existential forcing words. Each stage either hits the final
target or returns to the boundary at strictly smaller residual rank. -/
theorem expected_of_rank_stages {S : Type} {n : Nat} (hn : 0<n) (next : S→Fin n→S)
    (boundary final : S→Prop) (rank : S→Nat) (budget : Nat)
    (zero : ∀ x,boundary x→rank x=0→final x)
    (stage : ∀ x,boundary x→¬final x→
      IIDExpectedHittingTimeAtMost next (fun y=>(boundary y∧rank y<rank x)∨final y) x budget)
    (x : S) (B : boundary x) :
    IIDExpectedHittingTimeAtMost next final x (rank x*budget) := by
  have general (k : Nat) : ∀ x : S,boundary x→rank x=k→
      IIDExpectedHittingTimeAtMost next final x (k*budget) := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro x hx R
      by_cases hit : final x
      · intro t; rw [iidHitCost_of_target _ _ _ hit]
        exact Nat.zero_le _
      have pos : 0<k := Nat.pos_of_ne_zero (fun eq=>hit (zero x hx (R.trans eq)))
      let A := fun y => boundary y ∧ rank y<rank x
      have lower : ∀ y,A y→IIDExpectedHittingTimeAtMost next final y ((k-1)*budget) := by
        intro y hy
        have lt : rank y<k := R ▸ hy.2
        exact bound_mono (ih (rank y) lt y hy.1 rfl)
          (Nat.mul_le_mul_right _ (by omega))
      have estimate := iid_stage_le next hn x A final budget ((k-1)*budget) (stage x hx hit) lower
      rwa [show budget+(k-1)*budget=k*budget from by
        simpa only [Nat.add_mul,Nat.one_mul] using congrArg (·*budget) (show 1+(k-1)=k from by omega)] at estimate
  exact general (rank x) x B rfl

#print axioms expected_of_rank_stages
end L4.ControllerMacroIID

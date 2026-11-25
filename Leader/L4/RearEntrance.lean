import Leader.L4.RearTailWeight
import Leader.L4.RearTailNumerics
import Leader.L4.RootedFresh
import Leader.L4.RootedEntrance

/-! # The rear-clock conditional entrance bound -/

namespace L4
open TaggedTrace

theorem concreteAllTags_mean_of_rearDebt (hDebt : RearTrace.ConcreteRearDebt)
    {p c n : Nat} (x : Config p c n) (hp : 2 ≤ p) (hcal : 12 ≤ c)
    (hn : 4 ≤ n) (hnd : (∃ j : Fin n, (x j).mark = true)) (hm : MCOV x) (hc : COV x) :
    IIDExpectedHittingTimeAtMost allAdvance allEnded (allInit x) (48*n^2) := by
  apply RearTailNumerics.allTags_expected_of_weighted_tail allAdvance
    (fun (i : Fin n) y => ¬ ended (y i)) (allInit x) (by omega) (Nat.le_refl n)
  · intro i y e h he
    exact h (ended_step he e)
  · intro i T
    rw [allSurvival_proj]
    exact RearTailNumerics.cancel_extra_shift
      (RearTrace.rear_horizon_weight_of_kernel (fun hn => RearTailNumerics.rear_kernel (by omega))
        hDebt x i T hp hcal hn hnd hm hc)

/-- Literal L4 entrance conditional on an actual live debt bound (new-bullet peacefulness is the literal peacefulness theorem). The ordered cover and the all-tag
maximum are both included: no tail or mean is assumed additionally. -/
theorem entrance_mean_of_rearDebt
    (hDebt : RearTrace.ConcreteRearDebt)
    {p c1 n : Nat} (x : Config p c1 n) (hp : 2 ≤ p) (hcal : 12 ≤ c1)
    (hn : 4 ≤ n) (hnd : RootedEntrance.RootNonempty x) :
    IIDExpectedHittingTimeAtMost step QuietEntrance x (49*n^2) := by
  let i : Fin n := ⟨0, by omega⟩
  let project := fun s : AllObs p c1 n => (s i).config
  let target := fun s : AllObs p c1 n => allEnded s ∧ QuietEntrance (project s)
  have hx (x : Config p c1 n) (hm : MCOV x) (hc : COV x) (hM : RootedEntrance.MarkNonempty x) :
      IIDExpectedHittingTimeAtMost allAdvance target (allInit x) (48*n^2) := by
    have hbase := concreteAllTags_mean_of_rearDebt hDebt
      x hp hcal hn hM hm hc
    let good := fun s : AllObs p c1 n => ∃ w, trackAll (allInit x) w = s
    have hnext (s : AllObs p c1 n) (e : Fin n) (hs : good s) : good (allAdvance s e) := by
      obtain ⟨w,rfl⟩ := hs
      exact ⟨w++[e], by rw [trackAll_append]; rfl⟩
    have hstop (s : AllObs p c1 n) (hs : good s) : target s ↔ allEnded s := by
      constructor
      · exact And.left
      · intro hd
        obtain ⟨w,rfl⟩ := hs
        have hproj : project (trackAll (allInit x) w) = run x w :=
          allTrack_config (allInit x) i w
        have ⟨hm',hc'⟩ := cover_run hn x ⟨hm,hc⟩ w
        have hmark := (RootedEntrance.mark_iff_root_of_cover (run x w) hm').mpr (RootedEntrance.root_nonempty_run hn x w (RootedEntrance.rootNonempty_of_mark hM))
        exact ⟨hd, hproj ▸ ⟨hm',hc',hmark,RootedFresh.peace_after_extinction x w hp hcal hn hm hc hd⟩⟩
    intro t
    rw [hitCost_equiv_on_invariant allAdvance target allEnded good
      hnext hstop t (allInit x) ⟨[],rfl⟩]
    exact hbase t
  have hfinal := RootedEntrance.rooted_after_cover_bound hn QuietEntrance (48*n^2)
    (fun y hm hc hM t => by
      have hh := EntranceCover.iidHitCost_le_of_projection step allAdvance QuietEntrance target
        project (fun s e => projection_step (s i) e) (fun _ h => h.2) t (allInit y)
      exact Nat.le_trans hh (hx y hm hc hM t)) x hnd
  have heq : n*n+48*n^2 = 49*n^2 := by
    rw [show n*n = n^2 by rw [Nat.pow_succ,Nat.pow_one]]
    omega
  rwa [heq] at hfinal

end L4


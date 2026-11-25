import Leader.L4.RootedFresh
import Leader.L4.AliasLiteralClock
import Leader.L4.Absorb

/-! A nonempty covered singleton does not use the cyclic-sum existence
argument. The known mark supplies the drainage head and the exact
aliased top/door port. No extra endpoint stock/timer assumptions. -/
namespace L4.RootedSingleton

open RankRootless RankPhysical SingletonFinish

private theorem at_most_sum {n : Nat} (f : Fin n → Nat) (i : Fin n) :
    f i≤TaggedTail.sumEdge f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [TaggedTail.sumEdge,List.ofFn_succ,List.sum_cons]
    refine Fin.cases (Nat.le_add_right ..) (fun j => ?_) i
    exact Nat.le_trans (ih (fun e => f e.succ) j) (Nat.le_add_left ..)

private theorem rank_pos {p c n : Nat} {x : Config p c n} (hQ : QuietEntrance x) :
    1≤rank x := by
  obtain ⟨e,he⟩ := hQ.2.2.1
  simpa [rank,he] using at_most_sum (fun i => (x i).mark.toNat) e

/-- The first birth on the literal aliased port, valid at any size and
modulus, has the same cost as the already verified pure alias clock. -/
theorem zero_stock_mean {p c n : Nat} (x : Config p c n)
    (hc : 12≤c) (hn : 4≤n) (hQ : QuietEntrance x)
    (hR : rank x=1) (hL : NoLiving x) (hS : NoStock x) :
    IIDExpectedHittingTimeAtMost step (fun y => ¬NoLiving y) x
      (n*(32*(2*c+1)*(n+1))) := by
  obtain ⟨seam,hseam⟩ := Absorb.rank_one_unique_mark x hR
  obtain ⟨clock,hB⟩ := AliasLiteralClock.pureAliasClock seam
    (aliasProject seam x) hc hn (hL (rightNeighbor seam))
  intro t
  rw [alias_cost_eq hn x seam hQ.1 hQ.2.1 hS hseam hL t]
  exact Nat.le_trans (FixedResidual.expected_of_countdown _ _ _ clock t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hB))

/-- Only the literal invariant is needed for the stage composition;
the rooted antecedent supplies a drainage head at every entry. -/
theorem living_mean_of_quiet_closed {p c n : Nat} (x : Config p c n)
    (hc : 12≤c) (hn : 4≤n)
    (closure : ∀ (y : Config p c n) (e : Fin n), QuietEntrance y → QuietEntrance (step y e))
    (hQ : QuietEntrance x) (hR : rank x=1) :
    IIDExpectedHittingTimeAtMost step LivingSingleton x
      (17*n^2+n*(32*(2*c+1)*(n+1))) := by
  classical
  let good := fun y : Config p c n => QuietEntrance y ∧ rank y=1
  have closed : ∀ y e, good y → good (step y e) := by
    intro y e hy
    have hq := closure y e hy.1
    have hlo := rank_pos hq
    have hhi := rank_step_le hn y e hy.1.1
    exact ⟨hq,by have h := hy.2; omega⟩
  obtain ⟨e,he⟩ := hQ.2.2.1
  have hpre := RootlessFIFO.rootless_drain_mean hn x (rightNeighbor e) hQ.1
    (by rwa [RearTrace.predecessor_right])
  refine expected_then step good RootlessFIFO.DrainTarget LivingSingleton closed
    (fun y h => .inl h.2.2) _ ?_ x ⟨hQ,hR⟩ _ hpre
  intro y hy hCut t
  by_cases hL : NoLiving y
  · have hS := hCut.resolve_left (fun h => h hL)
    rw [hitCost_equiv_on_invariant step LivingSingleton (fun w => ¬ NoLiving w)
      good closed (fun w hw => ⟨fun h => h.2.2,fun h => ⟨hw.1,hw.2,h⟩⟩) t y hy]
    exact zero_stock_mean y hc hn hy.1 hy.2 hL hS t
  · rw [iidHitCost_of_target step LivingSingleton y ⟨hy.1,hy.2,hL⟩]
    exact Nat.zero_le _

/-- The absorbing all-word target contains every living peaceful
singleton. Target inclusion transfers the exact finite cost bound. -/
theorem safe_mean_of_quiet_closed {p c n : Nat} (x : Config p c n)
    (hc : 12≤c) (hn : 4≤n)
    (closure : ∀ (y : Config p c n) (e : Fin n), QuietEntrance y → QuietEntrance (step y e))
    (hQ : QuietEntrance x) (hR : rank x=1) :
    IIDExpectedHittingTimeAtMost step SafeOneLeader x ((17+64*(2*c+1))*n^2) := by
  have ha := living_mean_of_quiet_closed x hc hn closure hQ hR
  have costs := EntranceCover.iidHitCost_le_of_projection step step SafeOneLeader LivingSingleton
    (fun y : Config p c n => y) (fun _ _ => rfl) (fun _ => Absorb.singleton_live_safe hn)
  intro t
  refine Nat.le_trans (costs t x) (Nat.le_trans (ha t) (Nat.mul_le_mul_right _ ?_))
  have hupper : 32*(2*c+1)*(n+1) ≤ (64*(2*c+1))*n := by
    calc
      _ ≤ (32*(2*c+1))*(2*n) :=
        Nat.mul_le_mul_left _ (show n+1≤2*n by omega)
      _ = _ := by
        calc
          _ = (32*2)*(2*c+1)*n := by ac_rfl
          _ = _ := rfl
  rw [Nat.add_mul, Nat.pow_two]
  exact Nat.add_le_add_left (Nat.le_trans (Nat.mul_le_mul_left n hupper) (Nat.le_of_eq (by ac_rfl))) _

/-- Unconditional singleton finish on every covered rooted residue
chamber, including p dividing n. -/
theorem singletonSafeMean {p c n : Nat} (x : Config p c n)
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (hQ : QuietEntrance x) (hR : RankPhysical.rank x=1) :
    IIDExpectedHittingTimeAtMost step SafeOneLeader x ((17+64*(2*c+1))*n^2) :=
  safe_mean_of_quiet_closed x hc hn (fun y e hy => RootedFresh.quiet_step y e hp hc hn hy) hQ hR

end L4.RootedSingleton


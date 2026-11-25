import Leader.L4.RearDebt
import Leader.L4.Count
import Leader.L4.RankAttempt
import Leader.L4.TripleRenewal
import Leader.L4.RankBlockContraction
import Leader.L4.SingletonFinish
import Leader.L4.Absorb

namespace L4
open RankPhysical TripleRenewal

/-- Entrances at rank one preserve the literal paper domain. -/
def QuietRankOne {p c n : Nat} (x : Config p c n) : Prop :=
  QuietEntrance x ∧ rank x ≤ 1

/-- The high-rank phase plus the bounded-rank phase. The existential
coefficient cannot depend on the initial configuration or the ring size. -/
def ConcreteRankOneMean : Prop :=
  ∀ c : Nat, 12 ≤ c → ∃ A : Nat, ∀ {p n : Nat} (x : Config p c n),
    2 ≤ p → 4 ≤ n → (¬ p ∣ n) → QuietEntrance x →
      IIDExpectedHittingTimeAtMost step QuietRankOne x (A*n^2)

def ConcreteSingletonSafeMean : Prop :=
  ∀ c : Nat, 12 ≤ c → ∃ A : Nat, ∀ {p n : Nat} (x : Config p c n),
    2 ≤ p → 4 ≤ n → (¬ p ∣ n) → QuietRankOne x →
      IIDExpectedHittingTimeAtMost step SafeOneLeader x (A*n^2)

theorem safeOneLeader_exactlyOne {p c n : Nat} {x : Config p c n}
    (h : SafeOneLeader x) : ∃ i : Fin n, UniqueLeaderAt x i := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi []⟩

private def observe {α : Type} {n : Nat} (f : α → Fin n → α) (x : α)
    (stop loop : α → Prop) (h : loop x)
    (closed : ∀ y e, loop y → loop (f y e)) : Stage f x where
  State := α
  start := x
  next := f
  project := id
  ready := stop
  reachable := loop
  projInit := rfl
  projStep := fun _ _ => rfl
  reachStart := h
  reachStep := closed

theorem quiet_rankOne_closed {p c n : Nat} (hp : 2≤p) (hc : 12≤c)
    (hn : 4≤n) (hpnd : ¬p ∣ n) (x : Config p c n) (e : Fin n)
    (h : QuietRankOne x) : QuietRankOne (step x e) :=
  ⟨quiet_step x e hp hc hn hpnd h.1, Nat.le_trans (rank_step_le hn x e h.1.1) h.2⟩

/-- The headline statement assembled, assuming exactly the explicitly
stated rank and singleton clock endpoints. The entrance cost charges
the cover and initial bullets once, not on every renewal. -/
theorem main_of_rankOne_and_singleton (hRank : ConcreteRankOneMean)
    (hSingle : ConcreteSingletonSafeMean) : row175Statement := by
  intro c hc
  obtain ⟨A,hA⟩ := hRank c hc
  obtain ⟨B,hB⟩ := hSingle c hc
  refine ⟨A+B, ?_⟩
  intro p hp
  refine ⟨stateCount_headline p c, ?_⟩
  intro n hn hpnd x
  have quietToSafe (y : Config p c n) (hy : QuietEntrance y) :
      IIDExpectedHittingTimeAtMost step SafeOneLeader y (A*n^2 + B*n^2) := by
    let s := observe step y QuietRankOne QuietEntrance hy
      (fun z e hz => quiet_step z e hp hc hn hpnd hz)
    exact expected_with_preparation s SafeOneLeader _ _ (hA y hp hn hpnd hy)
      (fun z _ hz _ => hB z hp hn hpnd hz)
  let first := observe step x QuietEntrance (fun _ => True) trivial (fun _ _ _ => trivial)
  have htotal := expected_with_preparation first SafeOneLeader (2049*n^2)
    (A*n^2+B*n^2) (rear_entrance_printed x hp hc hn hpnd)
    (fun z _ hz _ => quietToSafe z hz)
  simpa only [Nat.add_mul,Nat.add_assoc] using htotal


theorem quietRankOne_of_local_blocks (retire : RankPhysical.ConcreteBoundedRank)
    (blocks : RankBlockContraction.ConcreteRankBlock) : ConcreteRankOneMean := by
  have h := RankBlockContraction.rankOne_mean_of_boundedRank_and_block retire blocks
  intro c hc
  obtain ⟨A,hA⟩ := h c hc
  refine ⟨A,?_⟩
  intro p n x hp hn hnd hx
  let s := observe step x (fun y => rank y=1) QuietEntrance hx
    (fun y e hy => quiet_step y e hp hc hn hnd hy)
  have ht := expected_with_preparation s QuietRankOne (A*n^2) 0
    (hA x hp hn hnd hx) (by
      intro y hy hr hf
      exact False.elim (hf ⟨hy,Nat.le_of_eq hr⟩))
  simpa only [Nat.add_zero] using ht

theorem singletonSafeMean_of_alias (timer : SingletonFinish.PureAliasClock) :
    ConcreteSingletonSafeMean := by
  intro c hc
  refine ⟨17+64*(2*c+1),?_⟩
  intro p n x hp hn hnd hx
  have hr : rank x=1 := Nat.le_antisymm hx.2 (RankBlockContraction.quiet_rank_pos hx.1)
  have ha := SingletonFinish.singleton_expected_of_zero_mean
    (SingletonFinish.zero_mean_of_alias timer) x hp hc hn hnd hx.1 hr
  let s := observe step x SingletonFinish.LivingSingleton (fun _ => True)
    trivial (fun _ _ _ => trivial)
  have hb := expected_with_preparation s SafeOneLeader _ 0 ha (by
    intro y _ hy hf
    exact False.elim (hf (Absorb.singleton_live_safe hn hy)))
  rw [Nat.add_zero] at hb
  apply expected_mono hb
  have hh : 32*(2*c+1)*(n+1) ≤ (64*(2*c+1))*n := by
    have h := Nat.mul_le_mul_left (32*(2*c+1)) (show n+1≤2*n by omega)
    calc
      _ ≤ (32*(2*c+1))*(2*n) := h
      _ = (64*(2*c+1))*n := by
        calc
          _ = (32*2)*(2*c+1)*n := by ac_rfl
          _ = _ := rfl
  rw [Nat.add_mul, Nat.pow_two]
  exact Nat.add_le_add_left (Nat.le_trans (Nat.mul_le_mul_left n hh) (Nat.le_of_eq (by ac_rfl))) _

/-- The headline under the three explicit uninstantiated proof
interfaces. The block-local and full-circuit timer inputs are separate
from the global bounded-rank restart theorem. -/
theorem mainTheorem_of_block (restart : RankPhysical.ConcreteRestartTrial)
    (blocks : RankBlockContraction.ConcreteRankBlock)
    (singletonTimer : SingletonFinish.PureAliasClock) : row175Statement :=
  main_of_rankOne_and_singleton
    (quietRankOne_of_local_blocks (boundedRank_of_restartTrial restart) blocks)
    (singletonSafeMean_of_alias singletonTimer)


/-- Refined headline: instead of assuming the whole affine block law,
take only the physical seven-group simultaneous-progress certificate.
All subsequent averaging, iterations, rank halving, absorption and
calibration of the headline constant are derived. -/
theorem mainTheorem (restart : RankPhysical.ConcreteRestartTrial)
    (groups : RankBlockContraction.ConcreteSevenGroups)
    (singletonTimer : SingletonFinish.PureAliasClock) : row175Statement :=
  mainTheorem_of_block restart
    (RankBlockContraction.rank_block_of_seven_data groups) singletonTimer

end L4

#print axioms L4.main_of_rankOne_and_singleton
#print axioms L4.safeOneLeader_exactlyOne

#print axioms L4.quietRankOne_of_local_blocks
#print axioms L4.singletonSafeMean_of_alias
#print axioms L4.mainTheorem_of_block
#print axioms L4.mainTheorem

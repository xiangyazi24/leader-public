import Leader.Wu.Elimination.AdjacentLeaderCollision
import Leader.Wu.Elimination.NearestPeaceful

/-!
# Nearest-leader support through the actual adjacent collision

The collision row and physical carrier are the frozen implementation in
`AdjacentLeaderElimination`. The interval calculations below use the actual
clockwise geometry and physical fields. No future closure, exterior safety,
or probability inequality is a hypothesis.
-/

namespace AdjacentLeaderPeaceful

open StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination
open AdjacentLeaderElimination PPLLNoCheckBirthConditionTwoGeometry
open K2PeacefulGlobal

set_option autoImplicit false

variable {ψ κ n : Nat}

/-- A collision only strengthens shields: the source keeps its old shield,
the survivor is shielded, and every other physical site is unchanged. -/
theorem collision_shield_of_old (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e i : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true)
    (hs : (C i).legacy.shield = true) :
    (AdjacentLeaderElimination.step hψ ring C e i).legacy.shield = true := by
  rw [step_of_adjacent hψ ring C e hl hr]
  dsimp only
  split
  · rename_i hi; subst i; exact hs
  · split
    · rfl
    · exact hs

/-- A nearest support ending at the deleted source cannot occupy n-1
clockwise edges: its start would then be the adjacent surviving leader,
contradicting the required follower at offset zero. -/
theorem extension_distance_lt (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e start : Fin n) (d : Nat) (hd : d < n)
    (ht : cwPos ring start d = e)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true)
    (hf : ∀ k, k < d → (C (cwPos ring start k)).legacy.leader = false) :
    d + 1 < n := by
  apply Classical.byContradiction
  intro hbad
  have heq : d + 1 = n := by omega
  have hnext : cwPos ring start (d + 1) = ring.rightNeighbor e := by
    rw [cwPos_succ, ht]
  have hcycle : cwPos ring start n = start := by
    apply Fin.ext
    simp [cwPos, Nat.mod_eq_of_lt start.isLt]
  rw [heq, hcycle] at hnext
  have hzero := hf 0 (by omega)
  rw [cwPos_zero, hnext, hr] at hzero
  cases hzero

/-- Clearing both endpoint signals extends the old zero-signal interval
through the one new endpoint, without reading any exterior state. -/
theorem extended_signals_zero (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e start : Fin n) (d : Nat)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true)
    (ht : cwPos ring start d = e)
    (hz : ∀ k, k ≤ d → (C (cwPos ring start k)).legacy.signal_B = 0) :
    ∀ k, k ≤ d + 1 →
      (AdjacentLeaderElimination.step hψ ring C e (cwPos ring start k)).legacy.signal_B = 0 := by
  intro k hk
  apply adjacent_signal_zero hψ ring C e _ hl hr
  by_cases hkd : k ≤ d
  · exact Or.inr (Or.inr (hz k hkd))
  · have heq : k = d + 1 := by omega
    subst k
    exact Or.inr (Or.inl (by rw [cwPos_succ, ht]))

/-- Every old strict-interior follower stays a follower, and the former
target becomes the final follower before the new nearest target. -/
theorem extended_before_follower (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e start : Fin n) (d : Nat)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true)
    (ht : cwPos ring start d = e)
    (hf : ∀ k, k < d → (C (cwPos ring start k)).legacy.leader = false) :
    ∀ k, k < d + 1 →
      (AdjacentLeaderElimination.step hψ ring C e (cwPos ring start k)).legacy.leader = false := by
  intro k hk
  by_cases hkd : k < d
  · exact step_follower hψ ring C e _ (hf k hkd)
  · have heq : k = d := by omega
    subst k
    rw [ht]
    exact adjacent_deletes_source hψ ring C e hl hr

/-- The collision itself always retains its actual right-hand leader on
nontrivial rings, independently of all bullet and signal fields. -/
theorem collision_hasLeader (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true) :
    hasLeader n (observe (AdjacentLeaderElimination.step hψ ring C e)) := by
  exact ⟨ring.rightNeighbor e,
    (step_leader_away hψ ring C e _ (rightNeighbor_ne_self_of_one_lt ring hn e)).trans hr⟩

/-- An old nearest target other than the deleted source remains the nearest
target at the identical distance. Endpoint signal resets preserve its path. -/
theorem support_kept (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e start : Fin n) (d : Nat)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true)
    (hs : Support ring (observe C) start d) (ht : cwPos ring start d ≠ e) :
    Support ring (observe (AdjacentLeaderElimination.step hψ ring C e)) start d := by
  refine ⟨hs.distance_lt, ?_, ?_, ?_, ?_⟩
  · exact (step_leader_away hψ ring C e _ ht).trans hs.target_leader
  · exact collision_shield_of_old hψ ring C e _ hl hr hs.target_shield
  · intro k hk
    exact adjacent_signal_zero hψ ring C e _ hl hr (Or.inr (Or.inr (hs.signal_zero k hk)))
  · intro k hk
    exact step_follower hψ ring C e _ (hs.before_follower k hk)

/-- Removing a nearest target extends its support by one physical edge to
the adjacent survivor. The new interior includes the now-demoted source. -/
theorem support_extended (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e start : Fin n) (d : Nat)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true)
    (hs : Support ring (observe C) start d) (ht : cwPos ring start d = e) :
    Support ring (observe (AdjacentLeaderElimination.step hψ ring C e)) start (d + 1) := by
  refine ⟨extension_distance_lt hn ring C e start d hs.distance_lt ht hr hs.before_follower,
    ?_, ?_, ?_, ?_⟩
  · change (AdjacentLeaderElimination.step hψ ring C e (cwPos ring start (d + 1))).legacy.leader = true
    rw [cwPos_succ, ht]
    exact (step_leader_away hψ ring C e _ (rightNeighbor_ne_self_of_one_lt ring hn e)).trans hr
  · change (AdjacentLeaderElimination.step hψ ring C e (cwPos ring start (d + 1))).legacy.shield = true
    rw [cwPos_succ, ht]
    exact adjacent_shield hψ hn ring C e hl hr
  · exact extended_signals_zero hψ ring C e start d hl hr ht hs.signal_zero
  · exact extended_before_follower hψ ring C e start d hl hr ht hs.before_follower

/-- Every post-collision live bullet is exactly an old live bullet; its
support either stays at d or extends to d+1. No new bullet origin is assumed. -/
theorem nearest_collision (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true)
    (hC : NearestPeaceful ring (observe C)) :
    NearestPeaceful ring (observe (AdjacentLeaderElimination.step hψ ring C e)) := by
  intro start hb
  have hold : (observe C start).bullet = 2 := by
    change (C start).legacy.bullet = 2
    rw [← adjacent_bullet hψ ring C e start hl hr]
    exact hb
  obtain ⟨d, hs⟩ := hC start hold
  by_cases ht : cwPos ring start d = e
  · exact ⟨d + 1, support_extended hψ hn ring C e start d hl hr hs ht⟩
  · exact ⟨d, support_kept hψ ring C e start d hl hr hs ht⟩

/-- Nearest peacefulness alone is preserved by every actual physical row;
the no-collision branch uses the actual modulus-one kernel closure. -/
theorem nearest_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : NearestPeaceful ring (observe C)) (e : Fin n) :
    NearestPeaceful ring (observe (AdjacentLeaderElimination.step hψ ring C e)) := by
  by_cases hboth : (C e).legacy.leader = true ∧
      (C (ring.rightNeighbor e)).legacy.leader = true
  · exact nearest_collision hψ hn ring C e hboth.1 hboth.2 hC
  · rw [step_eq_old hψ ring C e hboth, LabelFreeElimination.observe_step]
    exact K2PeacefulGlobal.nearest_rawStep hn ring (observe C) hC e

/-- The existing physical nearest-peaceful, nonempty-leader class is closed
for the whole collision protocol. Noncollision rows are exactly the frozen
label-free row and use its separately proved closure theorem. -/
theorem peacefulGlobal_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : PeacefulGlobal ring C) (e : Fin n) :
    PeacefulGlobal ring (AdjacentLeaderElimination.step hψ ring C e) := by
  by_cases hboth : (C e).legacy.leader = true ∧
      (C (ring.rightNeighbor e)).legacy.leader = true
  · exact ⟨collision_hasLeader hψ hn ring C e hboth.2,
      nearest_collision hψ hn ring C e hboth.1 hboth.2 hC.2⟩
  · rw [step_eq_old hψ ring C e hboth]
    exact K2PeacefulGlobal.peacefulGlobal_step hψ hn ring C hC e

/-- An actual closed predicate, derived from both physical branches. -/
theorem peacefulGlobal_closed (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (AdjacentLeaderElimination.protocol hψ κ) ring
      (PeacefulGlobal ring) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  exact peacefulGlobal_step hψ hn ring C hC e

/-- On the nearest-peaceful class, neither branch can delete the last
physical leader. This uses present-state support and existence only. -/
theorem hasLeader_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hN : NearestPeaceful ring (observe C))
    (hL : hasLeader n (observe C)) (e : Fin n) :
    hasLeader n (observe (AdjacentLeaderElimination.step hψ ring C e)) :=
  (peacefulGlobal_step hψ hn ring C ⟨hL, hN⟩ e).1

theorem peacefulGlobal_run (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : PeacefulGlobal ring C) (es : List (Fin n)) :
    PeacefulGlobal ring (run (AdjacentLeaderElimination.step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (peacefulGlobal_step hψ hn ring C hC e)

/-- Every actual word preserves at least one physical leader. -/
theorem run_hasLeader (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : PeacefulGlobal ring C) (es : List (Fin n)) :
    hasLeader n (observe (run (AdjacentLeaderElimination.step hψ ring) C es)) :=
  (peacefulGlobal_run hψ hn ring C hC es).1

/-- Count one in the closed nearest-peaceful class implies actual future
output safety for the collision protocol, through the existing SignalSafe
consumer. The premise is the real current count, not post-state safety. -/
theorem count_one_isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : PeacefulGlobal ring C)
    (hc : K2FiniteProgress.count C = 1) :
    PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol hψ κ) ring C id :=
  AdjacentLeaderElimination.isSafe hψ hn ring C
    (K2PeacefulGlobal.count_one_signalSafe ring C hC hc)

/-- The same semantic handoff after any real collision-protocol word. -/
theorem run_count_one_isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : PeacefulGlobal ring C) (es : List (Fin n))
    (hc : K2FiniteProgress.count (run (AdjacentLeaderElimination.step hψ ring) C es) = 1) :
    PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol hψ κ) ring
      (run (AdjacentLeaderElimination.step hψ ring) C es) id :=
  count_one_isSafe hψ hn ring _ (peacefulGlobal_run hψ hn ring C hC es) hc

/-- Zero-distance support uses only the three actual target fields. -/
theorem support_zero (ring : DirectedRing n) (C : Fin n → UCell ψ κ) (i : Fin n)
    (hl : (C i).legacy.leader = true) (hs : (C i).legacy.shield = true)
    (hz : (C i).legacy.signal_B = 0) : Support ring (observe C) i 0 := by
  refine ⟨ring.hn, ?_, ?_, ?_, ?_⟩
  · rw [cwPos_zero]; exact hl
  · rw [cwPos_zero]; exact hs
  · intro k hk
    have heq : k = 0 := by omega
    subst k
    rw [cwPos_zero]; exact hz
  · intro k hk; omega

namespace RepeatedCollision

theorem ring5 : DirectedRing 5 := ⟨by decide⟩

/-- Three adjacent leaders and live bullets at all five sites. Physical
labels are all one at modulus two; controllers retain an existing UCell
value. The two followers initially target leader zero clockwise. -/
def seed (i : Fin 5) : UCell 2 1 :=
  { legacy := { K2OutputSafety.boundedCanonical (by decide) 1 i with
      leader := decide (i = 0 ∨ i = 1 ∨ i = 2), label := 1,
      shield := true, bullet := 2, signal_B := 0 }
    control := (K2OutputSafety.finiteCut 0).control }

theorem nondivisible : ¬ 2 ∣ 5 := by decide

theorem all_live (i : Fin 5) : (seed i).legacy.bullet = 2 := rfl

theorem support3 : Support ring5 (observe seed) 3 2 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro k _; rfl
  · intro k hk
    have heq : k = 0 ∨ k = 1 := by omega
    rcases heq with rfl | rfl <;> decide

theorem support4 : Support ring5 (observe seed) 4 1 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro k _; rfl
  · intro k hk
    have heq : k = 0 := by omega
    subst k; decide

/-- A nonempty multi-leader witness with nonlocal, nearest-target live
bullets. No exterior-safety or future-closure premise is supplied. -/
theorem seed_peaceful : PeacefulGlobal ring5 seed := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  intro i _
  have heq : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases heq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, support_zero ring5 seed 0 (by decide) rfl rfl⟩
  · exact ⟨0, support_zero ring5 seed 1 (by decide) rfl rfl⟩
  · exact ⟨0, support_zero ring5 seed 2 (by decide) rfl rfl⟩
  · exact ⟨2, support3⟩
  · exact ⟨1, support4⟩

/-- The remote bullet at site three gets two consecutive support extensions:
distance two to leader zero, three to leader one, then four to leader two. -/
theorem twice_extended :
    Support ring5
      (observe (run (AdjacentLeaderElimination.step (by decide) ring5) seed [0, 1])) 3 4 := by
  have hfirst : Support ring5
      (observe (AdjacentLeaderElimination.step (by decide) ring5 seed 0)) 3 (2 + 1) :=
    support_extended (by decide) (by decide) ring5 seed 0 3 2
      (by decide) (by decide) support3 (by decide)
  exact support_extended (by decide) (by decide) ring5
    (AdjacentLeaderElimination.step (by decide) ring5 seed 0) 1 3 (2 + 1)
    (by decide) (by decide) hfirst (by decide)

theorem count_after_two :
    K2FiniteProgress.count
      (run (AdjacentLeaderElimination.step (by decide) ring5) seed [0, 1]) = 1 := by
  decide

/-- The two actual collisions yield semantic safety for every future
physical scheduler word, with all five bullets still live at this endpoint. -/
theorem after_two_isSafe :
    PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol (by decide) 1) ring5
      (run (AdjacentLeaderElimination.step (by decide) ring5) seed [0, 1]) id :=
  run_count_one_isSafe (by decide) (by decide) ring5 seed seed_peaceful [0, 1] count_after_two

theorem after_two_all_live : ∀ i : Fin 5,
    (run (AdjacentLeaderElimination.step (by decide) ring5) seed [0, 1] i).legacy.bullet = 2 := by
  decide

end RepeatedCollision

/-- The previously checked remote-dirty-bullet extinction witness is
outside this invariant: its live bullet already has signal one at offset
zero. Thus closure here does not assert arbitrary-state stabilization. -/
theorem dirty_counterexample_not_nearest :
    ¬ NearestPeaceful AdjacentLeaderElimination.FieldNecessity.ring3
      (observe AdjacentLeaderElimination.ExteriorResidual.seed) := by
  intro h
  obtain ⟨d, hs⟩ := h 2 (by rfl)
  have hz := hs.signal_zero 0 (Nat.zero_le d)
  rw [cwPos_zero] at hz
  change (1 : Fin 2) = 0 at hz
  exact (by decide : (1 : Fin 2) ≠ 0) hz

end AdjacentLeaderPeaceful

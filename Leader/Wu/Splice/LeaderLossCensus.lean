import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Elimination.GapClosure
import Leader.Wu.Splice.Controller

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9LeaderLossCensus

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open K2BirthDispatcher ExpiringK2Projection LDSinkKernelC
open BirthShortDoneTerminalHost BirthShortDoneTerminalConsumer

variable {n psi width kappa tau : Nat}

/-! ## The two physical deletion guards -/

/-- Exact guard at the MOVE input which takes the physical left-leader kill
branch.  `right.bullet = 2` already implies the outer positive-bullet test. -/
def MoveDeleteGuard {psi : Nat} (l r : AgentState psi) : Prop :=
  l.leader = true /\ l.shield = false /\ r.bullet = (2 : Fin 3)

/-- The literal MOVE branch really clears the left leader. -/
theorem zeroLeaderEgressMove_clears_left
    (hpsi : 0 < psi) (nextLabel : Fin psi) (l r : AgentState psi)
    (h : MoveDeleteGuard l r) :
    (eliminateLeadersNoCollisionZeroLeaderEgressMove
      hpsi nextLabel l r).1.leader = false := by
  rcases h with ⟨hl, hs, hb⟩
  have hpos : r.bullet.val > 0 := by
    rw [hb]
    decide
  simp [eliminateLeadersNoCollisionZeroLeaderEgressMove,
    hpos, hl, hs, hb]

/-- Explicit adjacent-collision guard, evaluated after newborn initialization. -/
def CollisionDeleteGuard
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  l.core.core.leader = true /\ r.core.core.leader = true

/-- Exact pre-FIRE K2 deletion guard in the ordinary final-physical branch.
The responder-follower clause is forced by the preceding non-collision test
whenever the left endpoint is a leader. -/
def OrdinaryK2DeleteGuard
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  let L := ExpiringK2Projection.observeCell l
  let R := ExpiringK2Projection.observeCell r
  L.leader = true /\ R.leader = false /\
    L.shield = false /\ L.signal_B = (0 : Fin 2) /\
    R.bullet = (2 : Fin 3)

/-- Stage 1: the explicit two-leader collision clears exactly the left leader. -/
theorem collision_guard_clears_left
    (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau)
    (h : CollisionDeleteGuard l r) :
    (K2BirthDispatcher.collisionRow hpsi l r).1.core.core.leader = false := by
  rcases h with ⟨hl, hr⟩
  exact (K2BirthDispatcher.collisionRow_of_both hpsi l r hl hr).1

/-- Stage 2: if the explicit collision is absent, the exact K2 live-hit
criterion clears the left leader. -/
theorem ordinary_k2_guard_clears_left
    (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau)
    (h : OrdinaryK2DeleteGuard l r) :
    (K2BirthDispatcher.collisionRow hpsi l r).1.core.core.leader = false := by
  unfold OrdinaryK2DeleteGuard at h
  dsimp only at h
  have hl0 : l.core.core.leader = true := h.1
  have hr0 : r.core.core.leader = false := h.2.1
  have hnot :
      ¬ (l.core.core.leader = true /\ r.core.core.leader = true) := by
    intro hb
    have hbad : (false : Bool) = true := hr0.symm.trans hb.2
    cases hbad
  rw [K2BirthDispatcher.collisionRow_of_not_both hpsi l r hnot]
  have hk :=
    (K2GlobalGapClosure.kernel_delete_iff
      (by decide : 0 < 1)
      (ExpiringK2Projection.observeCell l)
      (ExpiringK2Projection.observeCell r)
      h.1 h.2.1).2
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have ho := ExpiringK2Projection.observe_row hpsi l r
  have he := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.1.leader) ho
  change
    (ExpiringK2Projection.row hpsi l r).1.core.core.leader =
      (sinkKernelC (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r)).1.leader at he
  exact he.trans hk

/-! ## Right endpoint: exact framing -/

/-- The K2 projection frames the responder leader bit exactly. -/
theorem projection_right_leader_eq
    (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau) :
    (ExpiringK2Projection.row hpsi l r).2.core.core.leader =
      r.core.core.leader := by
  have ho := ExpiringK2Projection.observe_row hpsi l r
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_right_leader_eq
    (by decide : 0 < 1)
    (ExpiringK2Projection.observeCell l)
    (ExpiringK2Projection.observeCell r)
  have he := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.2.leader) ho
  change
    (ExpiringK2Projection.row hpsi l r).2.core.core.leader =
      (sinkKernelC (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r)).2.leader at he
  exact he.trans hk

/-- `collisionRow` also frames the right leader exactly: its explicit branch
keeps the right leader, and its ordinary branch is K2. -/
theorem collisionRow_right_leader_eq
    (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau) :
    (K2BirthDispatcher.collisionRow hpsi l r).2.core.core.leader =
      r.core.core.leader := by
  by_cases h : CollisionDeleteGuard l r
  · rcases h with ⟨hl, hr⟩
    exact
      (K2BirthDispatcher.collisionRow_of_both hpsi l r hl hr).2.1.trans
        hr.symm
  · have hnot :
        ¬ (l.core.core.leader = true /\ r.core.core.leader = true) := by
      simpa [CollisionDeleteGuard] using h
    rw [K2BirthDispatcher.collisionRow_of_not_both hpsi l r hnot]
    exact projection_right_leader_eq hpsi l r

/-! ## Exhaustiveness of the two left-deletion guards -/

theorem collisionRow_left_leader_eq_of_no_delete
    (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau)
    (hcollision : ¬ CollisionDeleteGuard l r)
    (hk2 : ¬ OrdinaryK2DeleteGuard l r) :
    (K2BirthDispatcher.collisionRow hpsi l r).1.core.core.leader =
      l.core.core.leader := by
  have hnot :
      ¬ (l.core.core.leader = true /\ r.core.core.leader = true) := by
    simpa [CollisionDeleteGuard] using hcollision
  rw [K2BirthDispatcher.collisionRow_of_not_both hpsi l r hnot]
  have ho := ExpiringK2Projection.observe_row hpsi l r
  have he := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.1.leader) ho
  change
    (ExpiringK2Projection.row hpsi l r).1.core.core.leader =
      (sinkKernelC (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r)).1.leader at he
  cases hl : (ExpiringK2Projection.observeCell l).leader with
  | false =>
      have hlf : l.core.core.leader = false := hl
      have hkleft := LDSinkTwoGapEpochSuccessor.kernelC_left_follower
        (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r) hl
      exact he.trans (hkleft.trans hlf.symm)
  | true =>
      have hr : (ExpiringK2Projection.observeCell r).leader = false := by
        cases hrv : (ExpiringK2Projection.observeCell r).leader with
        | false => rfl
        | true =>
            have hl0 : l.core.core.leader = true := hl
            have hr0 : r.core.core.leader = true := hrv
            exact (hcollision ⟨hl0, hr0⟩).elim
      have hiff := K2GlobalGapClosure.kernel_delete_iff
        (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r) hl hr
      have hsurvive :
          (sinkKernelC (by decide : 0 < 1)
            (ExpiringK2Projection.observeCell l)
            (ExpiringK2Projection.observeCell r)).1.leader = true := by
        cases hout :
            (sinkKernelC (by decide : 0 < 1)
              (ExpiringK2Projection.observeCell l)
              (ExpiringK2Projection.observeCell r)).1.leader with
        | true => rfl
        | false =>
            have hd := hiff.mp hout
            have hbad : OrdinaryK2DeleteGuard l r := by
              unfold OrdinaryK2DeleteGuard
              dsimp only
              exact ⟨hl, hr, hd.1, hd.2.1, hd.2.2⟩
            exact (hk2 hbad).elim
      have hl0 : l.core.core.leader = true := hl
      exact he.trans (hsurvive.trans hl0.symm)

/-- No enabled deletion stage means both final-tail leader bits are framed. -/
theorem collisionRow_leaders_eq_of_no_delete
    (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau)
    (hcollision : ¬ CollisionDeleteGuard l r)
    (hk2 : ¬ OrdinaryK2DeleteGuard l r) :
    (K2BirthDispatcher.collisionRow hpsi l r).1.core.core.leader =
        l.core.core.leader /\
      (K2BirthDispatcher.collisionRow hpsi l r).2.core.core.leader =
        r.core.core.leader := by
  exact ⟨collisionRow_left_leader_eq_of_no_delete
      hpsi l r hcollision hk2,
    collisionRow_right_leader_eq hpsi l r⟩

/-! ## Lift through newborn initialization and the complete host -/

/-- Collision guard on the actual pair passed to `collisionRow`. -/
def FinalCollisionDeleteGuard
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau) : Prop :=
  CollisionDeleteGuard
    (K2BirthDispatcher.initializeNewborn oldL metaL)
    (K2BirthDispatcher.initializeNewborn oldR metaR)

/-- Ordinary K2 guard on the actual initialized pair passed to `collisionRow`. -/
def FinalOrdinaryK2DeleteGuard
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau) : Prop :=
  OrdinaryK2DeleteGuard
    (K2BirthDispatcher.initializeNewborn oldL metaL)
    (K2BirthDispatcher.initializeNewborn oldR metaR)

/-- With neither final deletion guard enabled, `finalPhysical` frames both
metadata leader bits. -/
theorem finalPhysical_leaders_eq_metadata_of_no_delete
    (hpsi : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau)
    (hcollision : ¬ FinalCollisionDeleteGuard oldL oldR metaL metaR)
    (hk2 : ¬ FinalOrdinaryK2DeleteGuard oldL oldR metaL metaR) :
    (K2BirthDispatcher.finalPhysical hpsi oldL oldR metaL metaR).1.core.core.leader =
        metaL.core.core.leader /\
      (K2BirthDispatcher.finalPhysical hpsi oldL oldR metaL metaR).2.core.core.leader =
        metaR.core.core.leader := by
  have hcollision' :
      ¬ CollisionDeleteGuard
        (K2BirthDispatcher.initializeNewborn oldL metaL)
        (K2BirthDispatcher.initializeNewborn oldR metaR) := by
    simpa [FinalCollisionDeleteGuard] using hcollision
  have hk2' :
      ¬ OrdinaryK2DeleteGuard
        (K2BirthDispatcher.initializeNewborn oldL metaL)
        (K2BirthDispatcher.initializeNewborn oldR metaR) := by
    simpa [FinalOrdinaryK2DeleteGuard] using hk2
  have h := collisionRow_leaders_eq_of_no_delete hpsi
    (K2BirthDispatcher.initializeNewborn oldL metaL)
    (K2BirthDispatcher.initializeNewborn oldR metaR)
    hcollision' hk2'
  unfold K2BirthDispatcher.finalPhysical
  exact ⟨h.1.trans
      (K2BirthDispatcher.initializeNewborn_leader oldL metaL),
    h.2.trans
      (K2BirthDispatcher.initializeNewborn_leader oldR metaR)⟩

/-- The right endpoint is framed by `finalPhysical` with no guard at all. -/
theorem finalPhysical_right_leader_eq_metadata
    (hpsi : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau) :
    (K2BirthDispatcher.finalPhysical hpsi oldL oldR metaL metaR).2.core.core.leader =
      metaR.core.core.leader := by
  unfold K2BirthDispatcher.finalPhysical
  exact
    (collisionRow_right_leader_eq hpsi
      (K2BirthDispatcher.initializeNewborn oldL metaL)
      (K2BirthDispatcher.initializeNewborn oldR metaR)).trans
      (K2BirthDispatcher.initializeNewborn_leader oldR metaR)

/-- The two deletion guards specialized to the actual host metadata. -/
def HostCollisionDeleteGuard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  FinalCollisionDeleteGuard l r
    (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1
    (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2

def HostOrdinaryK2DeleteGuard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  FinalOrdinaryK2DeleteGuard l r
    (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1
    (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2

/-- Complete-row preservation statement requested by the census: if neither
of the only two clearing stages is enabled, both pre-existing endpoint leaders
survive the host row.  False-to-true birth is intentionally not excluded. -/
theorem host_row_no_delete_preserves_existing_leaders
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hcollision : ¬ HostCollisionDeleteGuard hpsi hwidth hle l r)
    (hk2 : ¬ HostOrdinaryK2DeleteGuard hpsi hwidth hle l r) :
    (l.core.core.leader = true ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.leader = true) /\
    (r.core.core.leader = true ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.leader = true) := by
  have hm := BirthShortDoneTerminalConsumer.metadata_existing_leaders
    hpsi hwidth hle l r
  have hcollision' :
      ¬ FinalCollisionDeleteGuard l r
        (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1
        (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2 := by
    simpa [HostCollisionDeleteGuard] using hcollision
  have hk2' :
      ¬ FinalOrdinaryK2DeleteGuard l r
        (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1
        (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2 := by
    simpa [HostOrdinaryK2DeleteGuard] using hk2
  have hf := finalPhysical_leaders_eq_metadata_of_no_delete hpsi l r
    (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1
    (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2
    hcollision' hk2'
  unfold BirthShortDoneTerminalHost.row
  dsimp only
  exact ⟨fun hl => hf.1.trans (hm.1 hl),
    fun hr => hf.2.trans (hm.2 hr)⟩

/-- Stronger right-side census: an old right leader survives every host row,
without excluding either left-deletion guard. -/
theorem host_right_existing_leader_survives
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hr : r.core.core.leader = true) :
    (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.leader = true := by
  have hm :=
    (BirthShortDoneTerminalConsumer.metadata_existing_leaders
      hpsi hwidth hle l r).2 hr
  have hf := finalPhysical_right_leader_eq_metadata hpsi l r
    (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1
    (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2
  unfold BirthShortDoneTerminalHost.row
  dsimp only
  exact hf.trans hm

/-- Therefore the output-level `LeftDeletionCandidate` cannot occur
unless one of the two classified final deletion guards is enabled. -/
theorem leftDeletionCandidate_has_delete_guard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Q11593SpliceControllerDesign.SpliceAgentState psi kappa tau)
    (hdel : Q11593SpliceControllerDesign.LeftDeletionCandidate
      hpsi hwidth hle l r) :
    HostCollisionDeleteGuard hpsi hwidth hle l.base r.base ∨
      HostOrdinaryK2DeleteGuard hpsi hwidth hle l.base r.base := by
  by_cases hcollision :
      HostCollisionDeleteGuard hpsi hwidth hle l.base r.base
  · exact Or.inl hcollision
  · by_cases hk2 :
      HostOrdinaryK2DeleteGuard hpsi hwidth hle l.base r.base
    · exact Or.inr hk2
    · have hp := host_row_no_delete_preserves_existing_leaders
        hpsi hwidth hle l.base r.base hcollision hk2
      have hs := hp.1 hdel.1
      have hbad : (true : Bool) = false := hs.symm.trans hdel.2
      cases hbad

/-- A site outside the interacting pair is unchanged by the complete consumer
step, so no intermediate left deletion is synchronously visible there. -/
theorem outside_site_unchanged
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n)
    (C : Fin n -> ExpiringAgentState psi kappa tau)
    (e i : Fin n) (hi : i ≠ e) (hr : i ≠ ring.rightNeighbor e) :
    BirthShortDoneTerminalConsumer.step
      hpsi hwidth hle ring C e i = C i :=
  BirthShortDoneTerminalConsumer.step_other
    hpsi hwidth hle ring C e i hi hr

#print axioms B9LeaderLossCensus.zeroLeaderEgressMove_clears_left
#print axioms B9LeaderLossCensus.collision_guard_clears_left
#print axioms B9LeaderLossCensus.ordinary_k2_guard_clears_left
#print axioms B9LeaderLossCensus.projection_right_leader_eq
#print axioms B9LeaderLossCensus.collisionRow_leaders_eq_of_no_delete
#print axioms B9LeaderLossCensus.finalPhysical_leaders_eq_metadata_of_no_delete
#print axioms B9LeaderLossCensus.host_row_no_delete_preserves_existing_leaders
#print axioms B9LeaderLossCensus.host_right_existing_leader_survives
#print axioms B9LeaderLossCensus.leftDeletionCandidate_has_delete_guard
#print axioms B9LeaderLossCensus.outside_site_unchanged

end B9LeaderLossCensus

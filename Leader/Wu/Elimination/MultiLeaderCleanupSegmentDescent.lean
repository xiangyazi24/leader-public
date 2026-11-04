import Leader.Wu.Elimination.MultiLeaderCleanupPhysicalBridge
import Leader.Wu.Elimination.MultiLeaderCleanupSegmentPlan

/-!
# Physical multi-leader cleanup round

This module joins the arbitrary selected-segment raw trace to the exact
full-transition quotient simulation.  The only remaining hypothesis is the
prefixwise hidden-field contract; no second execution proof is required once
that contract is produced.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PhysicalBridge

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical

variable {psi n kappa tau : Nat}

/-- Prefixwise readiness composes along concatenated literal schedules.  This
lets the selected word be discharged phase by phase without unfolding the
whole recursion at every join. -/
theorem MultiLeaderCleanupPhysicalReadyAlong.append
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (xs ys : DetSchedule n)
    (hxs : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C xs)
    (hys : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring
        (runLocalSchedule ring
          (multiLeaderCleanupTransition hpsi kappa tau) C xs) ys) :
    MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C (xs ++ ys) := by
  induction xs generalizing C with
  | nil =>
      simpa [runLocalSchedule] using hys
  | cons e rest ih =>
      change ExpiringMultiLeaderCleanupPhysicalPairReady
          hpsi kappa (C e) (C (ring.rightNeighbor e)) ∧
        MultiLeaderCleanupPhysicalReadyAlong hpsi kappa tau ring
          (localStep ring
            (multiLeaderCleanupTransition hpsi kappa tau) C e) rest
        at hxs
      rcases hxs with ⟨hedge, hrest⟩
      constructor
      · exact hedge
      · apply ih
          (C := localStep ring
            (multiLeaderCleanupTransition hpsi kappa tau) C e)
          hrest
        simpa [runLocalSchedule] using hys

/-- A single scheduled edge needs exactly one instance of the pair contract. -/
theorem MultiLeaderCleanupPhysicalReadyAlong.singleton
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n)
    (hedge : ExpiringMultiLeaderCleanupPhysicalPairReady
      hpsi kappa (C e) (C (ring.rightNeighbor e))) :
    MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C [e] := by
  exact ⟨hedge, trivial⟩

/-- The raw egress-sink execution used by a segment plan is definitionally the
same literal schedule as `runLocalSchedule`. -/
theorem runLocalSchedule_egressSink_eq_segment_output
    (hpsi : psi > 0) (ring : DirectedRing n)
    (plan : SegmentCleanupPlan ring)
    (C : Fin n → AgentState psi) :
    runLocalSchedule ring
        (eliminateLeadersNoCollisionEgressSink hpsi) C plan.word =
      plan.output hpsi C := by
  unfold SegmentCleanupPlan.output
  exact runLocalSchedule_eq_applySchedule_egressSink
    hpsi ring C plan.word

/-- A general selected-segment raw trace and the complete expiring execution
have identical cleanup-physical outputs whenever the hidden pair contract is
available at every prefix. -/
theorem SegmentCleanupReady.trace_with_multiLeaderCleanup_simulation
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (plan : SegmentCleanupPlan ring)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hready : SegmentCleanupReady
      hpsi ring plan (eraseExpiringCleanupConfig C))
    (halong : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C plan.word) :
    (let D := runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau) C plan.word
      ∀ i,
        cleanupPhysicalViewOfState (D i).core.erase.core =
          cleanupPhysicalViewOfState
            ((plan.output hpsi (eraseExpiringCleanupConfig C)) i)) ∧
      SegmentCleanupTrace
        hpsi ring plan (eraseExpiringCleanupConfig C) := by
  constructor
  · have hsim :=
      runLocalSchedule_multiLeaderCleanup_cleanupPhysicalView_eq_raw
        hpsi kappa tau ring C plan.word halong
    have hout := runLocalSchedule_egressSink_eq_segment_output
      hpsi ring plan (eraseExpiringCleanupConfig C)
    rw [hout] at hsim
    exact hsim
  · exact hready.trace

private theorem rawPhysicalLeaderCount_eq_of_cleanupPhysicalView
    {C D : Fin n → AgentState psi}
    (hview : ∀ i,
      cleanupPhysicalViewOfState (C i) =
        cleanupPhysicalViewOfState (D i)) :
    rawPhysicalLeaderCount C = rawPhysicalLeaderCount D := by
  have hmass :
      (fun i : Fin n => rawLeaderMass (C i)) =
        (fun i : Fin n => rawLeaderMass (D i)) := by
    funext i
    unfold rawLeaderMass
    have hleader := congrArg CleanupPhysicalView.leader (hview i)
    change (C i).leader = (D i).leader at hleader
    rw [hleader]
  unfold rawPhysicalLeaderCount
  rw [hmass]

/-- The complete expiring execution strictly lowers the physical leader count
under exactly the prefixwise hidden-field obligation exposed by the bridge.
This is the strict-round conclusion needed by the global count induction. -/
theorem SegmentCleanupReady.expiringPhysicalLeaderCount_lt_of_readyAlong
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (plan : SegmentCleanupPlan ring)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hready : SegmentCleanupReady
      hpsi ring plan (eraseExpiringCleanupConfig C))
    (halong : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C plan.word) :
    let D := runLocalSchedule ring
      (multiLeaderCleanupTransition hpsi kappa tau) C plan.word
    rawPhysicalLeaderCount (eraseExpiringCleanupConfig D) <
      rawPhysicalLeaderCount (eraseExpiringCleanupConfig C) := by
  let D := runLocalSchedule ring
    (multiLeaderCleanupTransition hpsi kappa tau) C plan.word
  have hjoined :=
    trace_with_multiLeaderCleanup_simulation
      hpsi kappa tau ring plan C hready halong
  have hview : ∀ i,
      cleanupPhysicalViewOfState ((eraseExpiringCleanupConfig D) i) =
        cleanupPhysicalViewOfState
          ((plan.output hpsi (eraseExpiringCleanupConfig C)) i) := by
    exact hjoined.1
  have hcount :
      rawPhysicalLeaderCount (eraseExpiringCleanupConfig D) =
        rawPhysicalLeaderCount
          (plan.output hpsi (eraseExpiringCleanupConfig C)) :=
    rawPhysicalLeaderCount_eq_of_cleanupPhysicalView hview
  change rawPhysicalLeaderCount (eraseExpiringCleanupConfig D) <
    rawPhysicalLeaderCount (eraseExpiringCleanupConfig C)
  rw [hcount]
  exact hready.rawPhysicalLeaderCount_lt

end PhysicalBridge
end PPLLCompleteMultiLeaderCleanup

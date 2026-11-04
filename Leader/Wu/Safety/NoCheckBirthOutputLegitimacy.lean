import Leader.Wu.Safety.NoCheckBirthConditionThreeProtocol
import Leader.Wu.Safety.CorrectedFormulation

/-!
# Closed output legitimacy for the exact finite no-CHECK-birth protocol

Wu's write-side conditions 4 and 5 are not preserved by the current repaired
transition, but they are also unnecessary for Definition-1 leader-output
safety.  The condition-1/2/3 proofs consume exactly four facts: one leader, that
leader at label zero, peaceful bullets, and no free barrier.  `OutputSafeConfig`
records this output-relevant kernel, and the preceding modules now prove those
facts directly from that weaker hypothesis.

This module supplies the strongest currently verified replacement for the
closedness role of Lemma 4.1.1.  For every nontrivial ring, the exact bounded
authorization/timer no-CHECK-birth protocol has a concrete inhabited
`OutputLegit`; the predicate is closed under every packaged interaction; every
member has one leader output and a pointwise invariant output vector in every
reachable future, exactly Wu's Definition 1.  Authorization bits and timers
remain arbitrary because legitimacy constrains only their physical erasure.

This is not five-condition closedness and does not repair the dead write
lifecycle.  It cleanly separates the output-safety theorem from arbitrary-state
entry, then proves that entry is impossible for this transition on divisible
rings by constructing a closed leaderless barrier-free class.
-/

namespace PPLLNoCheckBirthOutputLegitimacy

open PPLL PPLLRepair PPLLNoCheckBirthRepair PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLNoCheckBirthPhysicalConditionOne
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
  PPLLNoCheckBirthConditionTwoGlobal PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthConditionThreeProtocol PPLLResearchFormulation PPLLVerify
  PPLLCombinedLocalRepair PPLLTerminalEqualSupportRepair

private def outputView (hψ : ψ > 0) (i : Fin n) : PeaceView ψ :=
  { leader := decide (i.val = 0)
    label := ⟨i.val % ψ, Nat.mod_lt _ hψ⟩
    shield := false
    bullet := ⟨0, by omega⟩
    signal_B := ⟨0, by omega⟩ }

/-- Canonical raw witness: leader at position zero, clockwise modulo-`ψ`
labels, no bullets, and no active auxiliary field. -/
def outputCore (hψ : ψ > 0) (i : Fin n) : AgentState ψ :=
  PeaceView.toState (outputView hψ i)

/-- The canonical raw witness belongs to every declared numeric domain. -/
theorem outputCore_domain (hψ : ψ > 0) (i : Fin n) :
    (outputCore hψ i).inProtocolDomain κ := by
  simp [outputCore, outputView, PeaceView.toState,
    AgentState.inProtocolDomain]

/-- Exact finite reification of the canonical witness. -/
def outputFinite (hψ : ψ > 0) (κ τ : Nat) (i : Fin n) :
    ExpiringAgentState ψ κ τ :=
  ⟨⟨BoundedAgentState.ofDomain (outputCore hψ i)
      (outputCore_domain hψ i), false⟩, ⟨0, Nat.zero_lt_succ τ⟩⟩

/-- Reification erases exactly to the canonical raw witness. -/
theorem erase_outputFinite (hψ : ψ > 0) (κ τ : Nat) :
    eraseExpiringConfig (outputFinite (n := n) hψ κ τ) = outputCore hψ := by
  funext i
  change BoundedAgentState.erase
    (BoundedAgentState.ofDomain (outputCore hψ i)
      (outputCore_domain hψ i)) = outputCore hψ i
  exact BoundedAgentState.erase_ofDomain _ _

private theorem outputCore_unique (hψ : ψ > 0) (ring : DirectedRing n) :
    hasUniqueLeader n (outputCore hψ) := by
  let zero : Fin n := ⟨0, ring.hn⟩
  refine ⟨zero, ?_, ?_⟩
  · simp [zero, outputCore, outputView, PeaceView.toState,
      AgentState.isLeader]
  · intro j hj
    have hjv : j.val = 0 := by
      simpa [outputCore, outputView, PeaceView.toState,
        AgentState.isLeader] using hj
    exact Fin.ext hjv

private theorem outputCore_leader_zero (hψ : ψ > 0)
    (_ring : DirectedRing n) :
    ∀ i : Fin n, (outputCore hψ i).isLeader →
      (outputCore hψ i).label = ⟨0, hψ⟩ := by
  intro i hi
  have hiv : i.val = 0 := by
    simpa [outputCore, outputView, PeaceView.toState,
      AgentState.isLeader] using hi
  apply Fin.ext
  simp [outputCore, outputView, PeaceView.toState, hiv]

private theorem outputCore_no_bullet (hψ : ψ > 0)
    (ring : DirectedRing n) :
    noNonPeacefulBullet hψ ring (outputCore hψ) := by
  intro i hlive
  have hz : (outputCore hψ i).bullet.val = 0 := by
    rfl
  have hv := congrArg Fin.val hlive
  change (outputCore hψ i).bullet.val = 2 at hv
  omega

private theorem outputCore_no_barrier (hψ : ψ > 0)
    (ring : DirectedRing n) :
    noFreeBarrier hψ ring (outputCore hψ) := by
  intro i
  dsimp only
  intro hbarrier
  by_cases hnext : i.val + 1 < n
  · exfalso
    apply hbarrier
    apply Fin.ext
    simp only [outputCore, outputView, PeaceView.toState]
    have hj : (ring.rightNeighbor i).val = i.val + 1 := by
      simp [DirectedRing.rightNeighbor, Nat.mod_eq_of_lt hnext]
    rw [hj]
    exact (mod_succ_eq i.val ψ).symm
  · have hi : i.val + 1 = n := by omega
    have hj : ring.rightNeighbor i = (⟨0, ring.hn⟩ : Fin n) := by
      apply Fin.ext
      simp [DirectedRing.rightNeighbor, hi]
    rw [hj]
    simp [outputCore, outputView, PeaceView.toState, AgentState.isLeader]

/-- The canonical raw witness satisfies the output-relevant kernel. -/
theorem outputCore_safe (hψ : ψ > 0) (ring : DirectedRing n) :
    OutputSafeConfig hψ ring (outputCore hψ) where
  unique_leader := outputCore_unique hψ ring
  leader_label_zero := outputCore_leader_zero hψ ring
  no_nonpeaceful_bullet := outputCore_no_bullet hψ ring
  no_free_barrier := outputCore_no_barrier hψ ring

/-- Exact finite output legitimacy.  Auxiliary authorization bits and timers
are deliberately absent from the predicate. -/
def OutputLegit (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  OutputSafeConfig hψ ring (eraseExpiringConfig C)

/-- `OutputLegit` is nonempty for every finite parameter choice and ring. -/
theorem outputLegit_inhabited (hψ : ψ > 0) (κ τ : Nat)
    (ring : DirectedRing n) :
    OutputLegit hψ ring (outputFinite (n := n) hψ κ τ) := by
  unfold OutputLegit
  rw [erase_outputFinite]
  exact outputCore_safe hψ ring

/-- One exact packaged interaction preserves all four output-legitimacy fields. -/
theorem outputLegit_step (hψ : ψ > 0) (κ τ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : OutputLegit hψ ring C) (e : Fin n) :
    OutputLegit hψ ring
      ((noCheckBirthProtocol hψ κ τ).step ring C e) := by
  unfold OutputLegit at hC ⊢
  refine
    { unique_leader := ?_
      leader_label_zero := ?_
      no_nonpeaceful_bullet := ?_
      no_free_barrier := ?_ }
  · exact
      PPLLNoCheckBirthPhysicalConditionOne.uniqueLeader_preserved_noCheckBirthProtocol
        hψ κ τ hn2 ring C hC e
  · intro i hi
    have hleader := noCheckBirthProtocol_step_leader_eq
      hψ κ τ ring C hC e i
    have hiOld : (eraseExpiringConfig C i).isLeader := by
      unfold AgentState.isLeader at hi ⊢
      exact hleader.symm.trans hi
    have hzero := hC.leader_label_zero i hiOld
    have hlabel := noCheckBirthProtocol_step_label_eq
      hψ κ τ ring C hC e i
    exact hlabel.trans hzero
  · exact
      PPLLNoCheckBirthConditionTwoProtocol.noNonPeacefulBullet_preserved_noCheckBirthProtocol
        hψ κ τ hn2 ring C hC e
  · exact noFreeBarrier_preserved_noCheckBirthProtocol
      hψ κ τ ring C hC e

/-- `OutputLegit` is closed under every exact packaged interaction. -/
theorem outputLegit_closed (hψ : ψ > 0) (κ τ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (noCheckBirthProtocol hψ κ τ) ring
      (OutputLegit hψ ring) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  exact outputLegit_step hψ κ τ hn2 ring C hC e

/-- Every output-legitimate finite configuration has exactly one leader output. -/
theorem outputLegit_unique_output (hψ : ψ > 0) (κ τ : Nat)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : OutputLegit hψ ring C) :
    UniqueLeaderOutput (noCheckBirthProtocol hψ κ τ) n C
      isLeaderOutput := by
  obtain ⟨leader, hleader, honly⟩ := hC.unique_leader
  refine ⟨leader, ?_, ?_⟩
  · change (C leader).core.core.leader = true at hleader
    simp [noCheckBirthProtocol, isLeaderOutput, hleader]
  · intro i hi
    apply honly i
    change (C i).core.core.leader = true
    cases h : (C i).core.core.leader
    · simp [noCheckBirthProtocol, isLeaderOutput, h] at hi
    · rfl

/-- Every exact step inside `OutputLegit` preserves the complete pointwise
leader-output vector. -/
theorem outputLegit_step_output_preserving
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n) :
    StepOutputPreservingOn (noCheckBirthProtocol hψ κ τ) ring
      (OutputLegit hψ ring) := by
  intro C hC C' hstep i
  obtain ⟨e, rfl⟩ := hstep
  have hleader := noCheckBirthProtocol_step_leader_eq
    hψ κ τ ring C hC e i
  change (if
      (eraseExpiringConfig
        ((noCheckBirthProtocol hψ κ τ).step ring C e) i).leader then
      LeaderOutput.leader else LeaderOutput.follower) =
    (if (eraseExpiringConfig C i).leader then
      LeaderOutput.leader else LeaderOutput.follower)
  rw [hleader]

/-- Membership in the closed output-relevant kernel implies Wu's exact
Definition-1 semantic safety, with no write-lifecycle assumption. -/
theorem outputLegit_isSafe (hψ : ψ > 0) (κ τ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : OutputLegit hψ ring C) :
    PopulationProtocol.IsSafe (noCheckBirthProtocol hψ κ τ) ring C
      isLeaderOutput := by
  exact isSafe_of_operational_legitimacy
    (noCheckBirthProtocol hψ κ τ) ring isLeaderOutput
    (OutputLegit hψ ring)
    (outputLegit_closed hψ κ τ hn2 ring)
    (outputLegit_unique_output hψ κ τ ring)
    (outputLegit_step_output_preserving hψ κ τ ring) hC

/-- **Closed, inhabited, Definition-1-safe repaired legitimacy.**  The exact
finite no-CHECK-birth protocol has an explicit output-legitimate configuration;
the predicate is closed, and every member is semantically safe. -/
theorem outputLegit_capstone (hψ : ψ > 0) (κ τ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) :
    (∃ C : Fin n → ExpiringAgentState ψ κ τ, OutputLegit hψ ring C) ∧
    PopulationProtocol.ClosedPred (noCheckBirthProtocol hψ κ τ) ring
      (OutputLegit hψ ring) ∧
    (∀ C : Fin n → ExpiringAgentState ψ κ τ,
      OutputLegit hψ ring C →
      PopulationProtocol.IsSafe (noCheckBirthProtocol hψ κ τ) ring C
        isLeaderOutput) := by
  exact ⟨⟨outputFinite (n := n) hψ κ τ,
      outputLegit_inhabited hψ κ τ ring⟩,
    outputLegit_closed hψ κ τ hn2 ring,
    outputLegit_isSafe hψ κ τ hn2 ring⟩

/-! ## A divisible-ring obstruction to arbitrary-state entry

The closed `OutputLegit` set above is useful only if the repaired protocol can
reach it from every finite state.  For the current no-CHECK-birth transition,
divisibility of the ring length by `ψ` creates the opposite closed class:
clockwise modulo-`ψ` labels have no barrier, all agents are followers, P'_ψ
cannot create the first leader without a barrier, and CHECK is no longer a
leader writer.  The complete finite protocol consequently preserves both
leaderlessness and the barrier-free label cycle.

This section is a `REPAIR-VERIFIED` obstruction for the separately named
no-CHECK-birth protocol.  It is not a source-lane claim about literal P_PLL and
does not rule out a different repair that adds a genuine first-leader mechanism.
-/

/-- A raw configuration is in the leaderless barrier-free class when every
agent is a follower and every clockwise edge fails the P'_ψ barrier test.  The
two clauses isolate exactly the two possible sources of a first leader after
CHECK birth has been removed. -/
structure LeaderlessNoBarrier (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop where
  no_leader : ∀ i, (C i).leader = false
  no_barrier : ∀ i, ¬isBarrier hψ (C i) (C (ring.rightNeighbor i))

/-- Finite leaderless trap: authorization bits and timers are ignored, while
the erased physical configuration is required to be leaderless and
barrier-free. -/
def LeaderlessTrap (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  LeaderlessNoBarrier hψ ring (eraseExpiringConfig C)

/-- On a leaderless non-barrier edge, P'_ψ preserves both endpoint leaders and
labels.  Any new responder leader would require the very barrier excluded by
the class invariant. -/
theorem pPsi_frame_of_leaderlessNoBarrier
    (hψ : ψ > 0) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : LeaderlessNoBarrier hψ ring C) (e : Fin n) :
    let r := ring.rightNeighbor e
    let q := pPsi hψ (C e) (C r)
    q.1.leader = (C e).leader ∧ q.1.label = (C e).label ∧
      q.2.leader = (C r).leader ∧ q.2.label = (C r).label := by
  let r := ring.rightNeighbor e
  let q := pPsi hψ (C e) (C r)
  refine ⟨pPsi_initiator_leader_eq hψ (C e) (C r),
    pPsi_initiator_label_eq hψ (C e) (C r), ?_,
    pPsi_responder_label_of_nonbarrier hψ (C e) (C r)
      (hC.no_barrier e)⟩
  rw [hC.no_leader]
  cases hq : q.2.leader
  · rfl
  · have hbirth := pPsi_new_responder_leader_requires_probe_barrier
      hψ (C e) (C r) hq (hC.no_leader r)
    exact (hC.no_barrier e hbirth.2).elim

/-- The leaderless non-barrier facts instantiate the edge-local five-field
frame used by the exact physical refinement.  The responder-label premise is
vacuous because the responder is a follower. -/
theorem peaceEdgeFrame_of_leaderlessNoBarrier
    (hψ : ψ > 0) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : LeaderlessNoBarrier hψ ring C) (e : Fin n) :
    PeaceEdgeFrame hψ (C e) (C (ring.rightNeighbor e)) where
  pPsi_frame := pPsi_frame_of_leaderlessNoBarrier hψ ring C hC e
  responder_zero := by
    intro h
    rw [hC.no_leader] at h
    contradiction

/-- The isolated no-collision Algorithm-15 kernel cannot create a leader from
an all-follower configuration.  Each possible output leader has an explicit
input origin in the leader-frame API. -/
theorem noCollisionStep_leader_false
    (hψ : ψ > 0) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : ∀ i, (C i).leader = false) (e k : Fin n) :
    (noCollisionStep hψ ring C e k).leader = false := by
  unfold noCollisionStep updatePair
  by_cases hke : k = e
  · subst k
    simp only [if_true]
    cases hq : (eliminateLeadersNoCollision hψ (C e)
      (C (ring.rightNeighbor e))).1.leader
    · rfl
    · have horigin := eliminateLeadersNoCollision_initiator_origin
        hψ (C e) (C (ring.rightNeighbor e)) hq
      rw [hC] at horigin
      contradiction
  · by_cases hkr : k = ring.rightNeighbor e
    · rw [if_neg hke, if_pos hkr]
      rw [eliminateLeadersNoCollision_responder_leader_eq]
      exact hC _
    · rw [if_neg hke, if_neg hkr]
      exact hC k

/-- One exact finite no-CHECK-birth interaction preserves leaderlessness in
the trap.  The edge-local physical classification reduces the step either to
identity on `PeaceView` or to the no-collision kernel. -/
theorem leaderlessTrap_step_leader_false
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : LeaderlessTrap hψ ring C) (e k : Fin n) :
    (eraseExpiringConfig
      ((noCheckBirthProtocol hψ κ τ).step ring C e) k).leader = false := by
  rcases noCheckBirthProtocol_step_peaceView_classification_of_frame
      hψ κ τ ring C e
      (peaceEdgeFrame_of_leaderlessNoBarrier hψ ring
        (eraseExpiringConfig C) hC e) with hid | hkernel
  · exact (congrArg PeaceView.leader (hid k)).trans (hC.no_leader k)
  · exact (congrArg PeaceView.leader (hkernel k)).trans
      (noCollisionStep_leader_false hψ ring _ hC.no_leader e k)

/-- One exact finite no-CHECK-birth interaction preserves every erased label
in the trap.  Hence the barrier pattern, which depends only on adjacent labels,
cannot change. -/
theorem leaderlessTrap_step_label_eq
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : LeaderlessTrap hψ ring C) (e k : Fin n) :
    (eraseExpiringConfig
      ((noCheckBirthProtocol hψ κ τ).step ring C e) k).label =
      (eraseExpiringConfig C k).label := by
  rcases noCheckBirthProtocol_step_peaceView_classification_of_frame
      hψ κ τ ring C e
      (peaceEdgeFrame_of_leaderlessNoBarrier hψ ring
        (eraseExpiringConfig C) hC e) with hid | hkernel
  · exact congrArg PeaceView.label (hid k)
  · exact (congrArg PeaceView.label (hkernel k)).trans
      (noCollisionStep_label_eq hψ ring _ e k)

/-- The two trap invariants—no leaders and no barriers—are preserved by one
packaged interaction. -/
theorem leaderlessTrap_step
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : LeaderlessTrap hψ ring C) (e : Fin n) :
    LeaderlessTrap hψ ring
      ((noCheckBirthProtocol hψ κ τ).step ring C e) where
  no_leader := leaderlessTrap_step_leader_false hψ κ τ ring C hC e
  no_barrier := by
    intro i hbarrier
    apply hC.no_barrier i
    unfold isBarrier at hbarrier ⊢
    simpa only [leaderlessTrap_step_label_eq hψ κ τ ring C hC e i,
      leaderlessTrap_step_label_eq hψ κ τ ring C hC e
        (ring.rightNeighbor i)] using hbarrier

/-- The leaderless barrier-free class is closed under the exact finite
no-CHECK-birth protocol. -/
theorem leaderlessTrap_closed
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (noCheckBirthProtocol hψ κ τ) ring
      (LeaderlessTrap hψ ring) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  exact leaderlessTrap_step hψ κ τ ring C hC e

/-- A leaderless trap member cannot lie in `OutputLegit`, whose first field
requires exactly one leader. -/
theorem leaderlessTrap_not_outputLegit
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : LeaderlessTrap hψ ring C) :
    ¬OutputLegit hψ ring C := by
  intro hlegit
  obtain ⟨i, hi, _⟩ := hlegit.unique_leader
  change (eraseExpiringConfig C i).leader = true at hi
  rw [hC.no_leader i] at hi
  contradiction

/-- A leaderless trap member also fails Definition-1 semantic safety: its
present output vector has no leader output at all. -/
theorem leaderlessTrap_not_isSafe
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : LeaderlessTrap hψ ring C) :
    ¬PopulationProtocol.IsSafe (noCheckBirthProtocol hψ κ τ) ring C
      isLeaderOutput := by
  intro hsafe
  obtain ⟨i, hi, _⟩ := hsafe.1
  have hnone := hC.no_leader i
  change (C i).core.core.leader = false at hnone
  simp [noCheckBirthProtocol, isLeaderOutput, hnone] at hi

/-- Every configuration reachable from a leaderless trap remains outside both
the closed output-legitimacy predicate and Definition-1 semantic safety. -/
theorem leaderlessTrap_reachable
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C C' : Fin n → ExpiringAgentState ψ κ τ)
    (hC : LeaderlessTrap hψ ring C)
    (hreach : PopulationProtocol.Reachable
      (noCheckBirthProtocol hψ κ τ) ring C C') :
    ¬OutputLegit hψ ring C' ∧
      ¬PopulationProtocol.IsSafe (noCheckBirthProtocol hψ κ τ) ring C'
        isLeaderOutput := by
  have htrap := (leaderlessTrap_closed hψ κ τ ring).reachable hC hreach
  exact ⟨leaderlessTrap_not_outputLegit hψ ring C' htrap,
    leaderlessTrap_not_isSafe hψ κ τ ring C' htrap⟩

/-! ### Canonical divisible-ring witness

The label at position `i` is `i mod ψ`.  It advances by one on every ordinary
clockwise edge; on the wrap edge it advances by one exactly when `ψ ∣ n`.
All other output-relevant fields are zero, so the witness belongs to the finite
carrier for arbitrary authorization and timer bounds.
-/

/-- Five-field projection of the canonical all-follower modulo-`ψ` label
cycle. -/
private def trapView (hψ : ψ > 0) (i : Fin n) : PeaceView ψ :=
  { leader := false
    label := ⟨i.val % ψ, Nat.mod_lt _ hψ⟩
    shield := false
    bullet := ⟨0, by omega⟩
    signal_B := ⟨0, by omega⟩ }

/-- Raw canonical trap state, with every field outside `PeaceView` set to its
neutral value by `PeaceView.toState`. -/
def trapCore (hψ : ψ > 0) (i : Fin n) : AgentState ψ :=
  PeaceView.toState (trapView hψ i)

/-- Every canonical trap state lies in every declared count domain. -/
theorem trapCore_domain (hψ : ψ > 0) (i : Fin n) :
    (trapCore hψ i).inProtocolDomain κ := by
  simp [trapCore, trapView, PeaceView.toState, AgentState.inProtocolDomain]

/-- Exact finite reification of the canonical trap with authorization false
and timer zero. -/
def trapFinite (hψ : ψ > 0) (κ τ : Nat) (i : Fin n) :
    ExpiringAgentState ψ κ τ :=
  ⟨⟨BoundedAgentState.ofDomain (trapCore hψ i)
      (trapCore_domain hψ i), false⟩, ⟨0, Nat.zero_lt_succ τ⟩⟩

/-- Finite reification erases exactly to the canonical raw trap. -/
theorem erase_trapFinite (hψ : ψ > 0) (κ τ : Nat) :
    eraseExpiringConfig (trapFinite (n := n) hψ κ τ) = trapCore hψ := by
  funext i
  change BoundedAgentState.erase
    (BoundedAgentState.ofDomain (trapCore hψ i) (trapCore_domain hψ i)) = _
  exact BoundedAgentState.erase_ofDomain _ _

/-- When `ψ ∣ n`, the canonical modulo-`ψ` labels advance by one even across
the ring wrap, so no clockwise edge is a barrier. -/
theorem trapCore_no_barrier
    (hψ : ψ > 0) (hdvd : ψ ∣ n) (ring : DirectedRing n) (i : Fin n) :
    ¬isBarrier hψ (trapCore hψ i)
      (trapCore hψ (ring.rightNeighbor i)) := by
  intro hbarrier
  apply hbarrier
  apply Fin.ext
  simp only [trapCore, trapView, PeaceView.toState,
    DirectedRing.rightNeighbor]
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt]
    exact (mod_succ_eq i.val ψ).symm
  · have hn : i.val + 1 = n := by omega
    have hnmod : n % ψ = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hsucc : (i.val + 1) % ψ = 0 := by
      rw [hn]
      exact hnmod
    calc
      ((i.val + 1) % n) % ψ = 0 := by
        rw [hn, Nat.mod_self, Nat.zero_mod]
      _ = (i.val % ψ + 1) % ψ :=
        hsucc.symm.trans (mod_succ_eq i.val ψ).symm

/-- The canonical finite witness belongs to the leaderless trap whenever
`ψ ∣ n`. -/
theorem trapFinite_mem
    (hψ : ψ > 0) (κ τ : Nat) (hdvd : ψ ∣ n)
    (ring : DirectedRing n) :
    LeaderlessTrap hψ ring (trapFinite (n := n) hψ κ τ) := by
  unfold LeaderlessTrap
  rw [erase_trapFinite]
  exact ⟨fun _ => rfl, trapCore_no_barrier hψ hdvd ring⟩

/-- **Divisible-ring convergence obstruction.**  From the canonical finite
leaderless state, no reachable configuration is output-legitimate or
Definition-1 safe for the current no-CHECK-birth protocol. -/
theorem noCheckBirth_no_reachable_outputLegit_of_dvd
    (hψ : ψ > 0) (κ τ : Nat) (hdvd : ψ ∣ n)
    (ring : DirectedRing n)
    (C' : Fin n → ExpiringAgentState ψ κ τ)
    (hreach : PopulationProtocol.Reachable (noCheckBirthProtocol hψ κ τ) ring
      (trapFinite (n := n) hψ κ τ) C') :
    ¬OutputLegit hψ ring C' ∧
      ¬PopulationProtocol.IsSafe (noCheckBirthProtocol hψ κ τ) ring C'
        isLeaderOutput := by
  exact leaderlessTrap_reachable hψ κ τ ring _ C'
    (trapFinite_mem hψ κ τ hdvd ring) hreach

/-- Consequently, when `ψ ∣ n`, the current repaired protocol does not have
universal arbitrary-state reachability into `OutputLegit`. -/
theorem noCheckBirth_not_all_reach_outputLegit_of_dvd
    (hψ : ψ > 0) (κ τ : Nat) (hdvd : ψ ∣ n)
    (ring : DirectedRing n) :
    ¬(∀ C : Fin n → ExpiringAgentState ψ κ τ,
      ∃ C', PopulationProtocol.Reachable (noCheckBirthProtocol hψ κ τ) ring
        C C' ∧ OutputLegit hψ ring C') := by
  intro hall
  obtain ⟨C', hreach, hlegit⟩ :=
    hall (trapFinite (n := n) hψ κ τ)
  exact (noCheckBirth_no_reachable_outputLegit_of_dvd
    hψ κ τ hdvd ring C' hreach).1 hlegit

/-- Barrier-free leaderless raw configurations exist exactly in the divisible
regime.  The forward direction uses the ring arithmetic theorem that a
non-divisible label cycle must contain a barrier; the reverse direction is the
canonical modulo-`ψ` witness. -/
theorem leaderlessNoBarrier_iff_dvd
    (hψ : ψ > 0) (ring : DirectedRing n) :
    (∃ C : Fin n → AgentState ψ, LeaderlessNoBarrier hψ ring C) ↔ ψ ∣ n := by
  constructor
  · rintro ⟨C, hC⟩
    apply Classical.byContradiction
    intro hndvd
    obtain ⟨i, hi⟩ := barrier_exists_of_not_dvd ring.hn hψ hndvd C ring
    exact hC.no_barrier i hi
  · intro hdvd
    exact ⟨trapCore hψ, ⟨fun _ => rfl,
      trapCore_no_barrier hψ hdvd ring⟩⟩

/-- Smallest nontrivial concrete instance: on the two-agent, `ψ=2` ring, no
configuration reachable from the canonical trap is output-legitimate. -/
theorem twoTwo_no_reachable_outputLegit
    (C' : Fin 2 → ExpiringAgentState 2 0 0)
    (hreach : PopulationProtocol.Reachable
      (noCheckBirthProtocol (by omega : 2 > 0) 0 0) (⟨by omega⟩ : DirectedRing 2)
      (trapFinite (n := 2) (by omega) 0 0) C') :
    ¬OutputLegit (by omega : 2 > 0) (⟨by omega⟩ : DirectedRing 2) C' := by
  exact (noCheckBirth_no_reachable_outputLegit_of_dvd
    (by omega : 2 > 0) 0 0 (Nat.dvd_refl 2) (⟨by omega⟩ : DirectedRing 2) C'
    hreach).1

/-! ## Positive control: restoring CHECK escapes the divisible trap -/

/-- The canonical two-group trap, reified with enough local path-stall budget
for one genuine comparison traversal. -/
def twoGroupTrap : Fin 4 → ExpiringAgentState 2 0 6 :=
  trapFinite (by omega : 2 > 0) 0 6

/-- Generate the source signal, move its two components into the second group,
and compare there. -/
def twoGroupTrapEscapeSchedule : DetSchedule 4 := [0, 1, 0, 2, 1, 2]

private abbrev twoGroupRing : DirectedRing 4 := ⟨by omega⟩

def twoGroupTrapAfter : Fin 4 → ExpiringAgentState 2 0 6 :=
  runLocalSchedule twoGroupRing
    (combinedLocalPathStallTransition (by omega) 0 6)
    twoGroupTrap twoGroupTrapEscapeSchedule

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- **Positive divisible-ring escape.**  The existing combined local stack,
which retains CHECK birth, escapes the same barrier-free leaderless shape that
is closed under the no-CHECK-birth protocol.  The six-edge schedule leaves one
leader at the label-zero initiator after WRITE_SEQ migration. -/
theorem combinedLocal_twoGroup_trap_escape :
    (twoGroupTrapAfter 0).core.core.leader = false ∧
      (twoGroupTrapAfter 1).core.core.leader = false ∧
      (twoGroupTrapAfter 2).core.core.leader = true ∧
      (twoGroupTrapAfter 3).core.core.leader = false := by
  decide

/-- State immediately before the final comparison edge. -/
def twoGroupTrapBeforeFinal : Fin 4 → ExpiringAgentState 2 0 6 :=
  runLocalSchedule twoGroupRing
    (combinedLocalPathStallTransition (by omega) 0 6)
    twoGroupTrap [0, 1, 0, 2, 1]

private def twoGroupFinalInput :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  ((twoGroupTrapBeforeFinal 2).core.erase,
    (twoGroupTrapBeforeFinal 3).core.erase)

private def twoGroupFinalBeforeCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let q := authorizedBeforeCheck (by omega) 0
    twoGroupFinalInput.1 twoGroupFinalInput.2
  sanitizeAuthorizedPair (by omega) q

private def twoGroupFinalAfterCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedCheckSig (by omega)
    twoGroupFinalBeforeCheck.1 twoGroupFinalBeforeCheck.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The final edge has two aligned CHECK-ready components and no leader before
CHECK.  CHECK creates the terminal responder leader; the unchanged suffix then
migrates it left to label zero. -/
theorem combinedLocal_twoGroup_birth_occurs_at_check :
    twoGroupFinalBeforeCheck.1.core.leader = false ∧
      twoGroupFinalBeforeCheck.2.core.leader = false ∧
      twoGroupFinalBeforeCheck.1.core.state = .CHECK_ready ∧
      twoGroupFinalBeforeCheck.2.core.state = .CHECK_ready ∧
      twoGroupFinalAfterCheck.1.core.state = .equal ∧
      twoGroupFinalAfterCheck.2.core.state = .equal ∧
      twoGroupFinalAfterCheck.1.core.leader = false ∧
      twoGroupFinalAfterCheck.2.core.leader = true ∧
      (combinedLocalAuthorizedTransition (by omega) 0
        twoGroupFinalInput.1 twoGroupFinalInput.2).1.core.leader = true ∧
      (combinedLocalAuthorizedTransition (by omega) 0
        twoGroupFinalInput.1 twoGroupFinalInput.2).2.core.leader = false := by
  decide

end PPLLNoCheckBirthOutputLegitimacy

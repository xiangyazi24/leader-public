import Leader.Wu.Birth.PreparedRulerBlocksPPrime
import Leader.Wu.Birth.ShortDoneTerminalPositiveWitness
import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Elimination.BirthDispatcherDoneNormalize
import Leader.Wu.Safety.SafeConfig


/-!
# Actual-consumer deletion counterexample to the rooted ruler


The fixture uses the smallest finite wrapper parameters accepted by the actual
consumer: `kappa = 0`, `tau = 0`.  Every raw numeric field is zero and every
optional bounded payload is absent, so the records lie in
`AgentState.inProtocolDomain 0`; the expiry carrier then has the unique
`Fin (0 + 1)` clock value.
-/


namespace B9RulerDeletionCounterexample


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open PPLLPpsiLeaderCreationRepair
open Q11583PPrimePeakSafe


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hFour : 0 < 4 := by decide


abbrev E := ExpiringAgentState 2 0 0


def ring4 : DirectedRing 4 := ⟨hFour⟩


/-- Raw rooted-ruler predicate. -/
def RawRootedRuler {n psi : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Fin n -> AgentState psi) : Prop :=
  (forall i, (C i).leader = true ->
      (C i).label = ⟨0, hpsi⟩) ∧
    noFreeBarrier hpsi ring C


private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  omega


private theorem ring4_right0 :
    ring4.rightNeighbor (0 : Fin 4) = (1 : Fin 4) := by
  decide


private theorem ring4_right1 :
    ring4.rightNeighbor (1 : Fin 4) = (2 : Fin 4) := by
  decide


private theorem ring4_right2 :
    ring4.rightNeighbor (2 : Fin 4) = (3 : Fin 4) := by
  decide


private theorem ring4_right3 :
    ring4.rightNeighbor (3 : Fin 4) = (0 : Fin 4) := by
  decide


/-! ## Literal finite fixture -/


/-- Canonical neutral raw record, changing only the two fields relevant to the
raw rooted-ruler picture. -/
def rawCell (leader : Bool) (label : Fin 2) : AgentState 2 :=
  { BirthShortDoneTerminalPositiveWitness.raw false with
    leader := leader
    label := label }


private theorem rawCell_domain (leader : Bool) (label : Fin 2) :
    (rawCell leader label).inProtocolDomain 0 := by
  simp [rawCell, BirthShortDoneTerminalPositiveWitness.raw,
    AgentState.inProtocolDomain]


/-- Minimal bounded/authorized/expiring realization: kappa=tau=0. -/
def cell (leader : Bool) (label : Fin 2) : E :=
  ⟨⟨BoundedAgentState.ofDomain
      (rawCell leader label) (rawCell_domain leader label), false⟩, 0⟩


private theorem cell_erase (leader : Bool) (label : Fin 2) :
    (cell leader label).core.erase.core = rawCell leader label := by
  simp [cell, AuthorizedBoundedAgentState.erase,
    BoundedAgentState.erase_ofDomain]


/--
site       0      1      2      3
leader     F      T      T      F
label      0      0      0      1
-/
def start : Fin 4 -> E := fun i =>
  if i = 0 then cell false 0
  else if i = 1 then cell true 0
  else if i = 2 then cell true 0
  else cell false 1


/-! Staged input-field certificates. -/


private theorem start0_follower :
    (eraseExpiringConfig start 0).leader = false := by
  decide


private theorem start1_leader :
    (eraseExpiringConfig start 1).leader = true := by
  decide


private theorem start2_leader :
    (eraseExpiringConfig start 2).leader = true := by
  decide


private theorem start3_follower :
    (eraseExpiringConfig start 3).leader = false := by
  decide


private theorem start0_label_zero :
    (eraseExpiringConfig start 0).label = (⟨0, hTwo⟩ : Fin 2) := by
  decide


private theorem start1_label_zero :
    (eraseExpiringConfig start 1).label = (⟨0, hTwo⟩ : Fin 2) := by
  decide


private theorem start2_label_zero :
    (eraseExpiringConfig start 2).label = (⟨0, hTwo⟩ : Fin 2) := by
  decide


private theorem start3_label_one :
    (eraseExpiringConfig start 3).label = (1 : Fin 2) := by
  decide


private theorem start_edge2_aligned :
    (eraseExpiringConfig start (ring4.rightNeighbor (2 : Fin 4))).label =
      ⟨((eraseExpiringConfig start 2).label.val + 1) % 2,
        Nat.mod_lt _ hTwo⟩ := by
  decide


private theorem start_edge3_aligned :
    (eraseExpiringConfig start (ring4.rightNeighbor (3 : Fin 4))).label =
      ⟨((eraseExpiringConfig start 3).label.val + 1) % 2,
        Nat.mod_lt _ hTwo⟩ := by
  decide


private theorem start_leaders_label_zero :
    forall i, (eraseExpiringConfig start i).leader = true ->
      (eraseExpiringConfig start i).label = ⟨0, hTwo⟩ := by
  intro i hi
  rcases fin4_cases i with h0 | h1 | h2 | h3
  · subst i
    rw [start0_follower] at hi
    cases hi
  · subst i
    exact start1_label_zero
  · subst i
    exact start2_label_zero
  · subst i
    rw [start3_follower] at hi
    cases hi


private theorem start_noFreeBarrier :
    noFreeBarrier hTwo ring4 (eraseExpiringConfig start) := by
  intro i
  rcases fin4_cases i with h0 | h1 | h2 | h3
  · subst i
    dsimp only
    intro _hbarrier
    simpa only [ring4_right0, AgentState.isLeader] using start1_leader
  · subst i
    dsimp only
    intro _hbarrier
    simpa only [ring4_right1, AgentState.isLeader] using start2_leader
  · subst i
    dsimp only
    intro hbarrier
    unfold isBarrier at hbarrier
    exact (hbarrier start_edge2_aligned).elim
  · subst i
    dsimp only
    intro hbarrier
    unfold isBarrier at hbarrier
    exact (hbarrier start_edge3_aligned).elim


private theorem start_raw_rooted_ruler :
    RawRootedRuler hTwo ring4 (eraseExpiringConfig start) := by
  exact ⟨start_leaders_label_zero, start_noFreeBarrier⟩


/-! ## One literal current-consumer row at edge 1 -> 2 -/


/-- This is the actual current consumer, at full width `2 = psi`, not an
abstract K2 row.  `ring4_right1` certifies that the scheduled pair is 1 -> 2. -/
def afterDeletion : Fin 4 -> E :=
  BirthShortDoneTerminalConsumer.step
    hTwo hTwo hTwoLe ring4 start (1 : Fin 4)


/-! Staged post-row fields.  These are deliberately separate closed decisions,
not one monolithic `decide` over the counterexample proposition. -/


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after0_follower :
    (eraseExpiringConfig afterDeletion 0).leader = false := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after0_label_zero :
    (eraseExpiringConfig afterDeletion 0).label = (⟨0, hTwo⟩ : Fin 2) := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after1_follower :
    (eraseExpiringConfig afterDeletion 1).leader = false := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after1_label_zero :
    (eraseExpiringConfig afterDeletion 1).label = (⟨0, hTwo⟩ : Fin 2) := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after1_probe_false :
    (eraseExpiringConfig afterDeletion 1).probe = false := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after1_phase_true :
    (eraseExpiringConfig afterDeletion 1).phase = true := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after2_leader :
    (eraseExpiringConfig afterDeletion 2).leader = true := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after2_label_zero :
    (eraseExpiringConfig afterDeletion 2).label = (⟨0, hTwo⟩ : Fin 2) := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after3_follower :
    (eraseExpiringConfig afterDeletion 3).leader = false := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after3_label_one :
    (eraseExpiringConfig afterDeletion 3).label = (1 : Fin 2) := by
  decide


private theorem isBarrier_of_label_vals {psi : Nat} (hpsi : 0 < psi)
    (u v : AgentState psi) (a b : Nat)
    (ha : u.label.val = a) (hb : v.label.val = b)
    (hne : b ≠ (a + 1) % psi) : isBarrier hpsi u v := by
  unfold isBarrier
  intro h
  apply hne
  have hval : v.label.val = (u.label.val + 1) % psi :=
    congrArg Fin.val h
  simpa only [ha, hb] using hval

private theorem after_edge0_barrier :
    isBarrier hTwo
      (eraseExpiringConfig afterDeletion 0)
      (eraseExpiringConfig afterDeletion (ring4.rightNeighbor 0)) := by
  simpa only [ring4_right0] using
    (isBarrier_of_label_vals hTwo
      (eraseExpiringConfig afterDeletion 0)
      (eraseExpiringConfig afterDeletion 1)
      (a := 0) (b := 0)
      (ha := congrArg Fin.val after0_label_zero)
      (hb := congrArg Fin.val after1_label_zero)
      (hne := by decide))


private theorem after_not_raw_rooted_ruler :
    ¬ RawRootedRuler hTwo ring4 (eraseExpiringConfig afterDeletion) := by
  intro h
  have hright := h.2 (0 : Fin 4) after_edge0_barrier
  have hleader :
      (eraseExpiringConfig afterDeletion 1).leader = true := by
    simpa only [ring4_right0, AgentState.isLeader] using hright
  rw [after1_follower] at hleader
  cases hleader


/-- Item 1: literal-current-consumer certification of the raw picture. -/
theorem actual_consumer_deletion_breaks_raw_rooted_ruler :
    ∃ C : Fin 4 -> E,
      RawRootedRuler hTwo ring4 (eraseExpiringConfig C) ∧
      (∃ i, (eraseExpiringConfig C i).leader = true) ∧
      (let D := BirthShortDoneTerminalConsumer.step
          hTwo hTwo hTwoLe ring4 C (1 : Fin 4)
       (∃ i, (eraseExpiringConfig D i).leader = true) ∧
         ¬ RawRootedRuler hTwo ring4 (eraseExpiringConfig D)) := by
  refine ⟨start, start_raw_rooted_ruler, ⟨1, start1_leader⟩, ?_⟩
  change
    (∃ i, (eraseExpiringConfig afterDeletion i).leader = true) ∧
      ¬ RawRootedRuler hTwo ring4 (eraseExpiringConfig afterDeletion)
  exact ⟨⟨2, after2_leader⟩, after_not_raw_rooted_ruler⟩


/-! ## The prepared form used by the actual P-prime blocker -/


/-- Exact preparation/normalization used in `PreparedFollowerRulerAt`. -/
def preparedPair {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Fin n -> ExpiringAgentState psi kappa tau) (e : Fin n) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  (normalizeDeletion pl.core.erase, normalizeDeletion pr.core.erase)


/-- Prepared copy of the newly exposed edge 0 -> 1. -/
def badPrepared : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  preparedPair hTwo ring4 afterDeletion (0 : Fin 4)


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem badPrepared_left_follower :
    badPrepared.1.core.leader = false := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem badPrepared_right_follower :
    badPrepared.2.core.leader = false := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem badPrepared_left_label_zero :
    badPrepared.1.core.label = (⟨0, hTwo⟩ : Fin 2) := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem badPrepared_right_label_zero :
    badPrepared.2.core.label = (⟨0, hTwo⟩ : Fin 2) := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem badPrepared_right_probe_false :
    badPrepared.2.core.probe = false := by
  decide


private theorem badPrepared_barrier :
    isBarrier hTwo badPrepared.1.core badPrepared.2.core := by
  exact isBarrier_of_label_vals hTwo
    badPrepared.1.core badPrepared.2.core
    (a := 0) (b := 0)
    (ha := congrArg Fin.val badPrepared_left_label_zero)
    (hb := congrArg Fin.val badPrepared_right_label_zero)
    (hne := by decide)


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem after_not_prepared_follower_ruler :
    ¬ (forall e,
      Q11583PPrimePeakSafe.PreparedFollowerRulerAt
        hTwo ring4 afterDeletion e) := by
  intro h
  have h0 := h (0 : Fin 4)
  unfold Q11583PPrimePeakSafe.PreparedFollowerRulerAt at h0
  dsimp only at h0
  change
    badPrepared.2.core.leader = false ->
      badPrepared.2.core.label =
        ⟨(badPrepared.1.core.label.val + 1) % 2,
          Nat.mod_lt _ hTwo⟩ at h0
  have haligned := h0 badPrepared_right_follower
  have hbarrier := badPrepared_barrier
  unfold isBarrier at hbarrier
  exact hbarrier haligned


/-- Item 2: the same literal successor fails the prepared ruler that implies
`PPrimeBlockedAt`. -/
theorem actual_consumer_deletion_breaks_prepared_ruler :
    let D := BirthShortDoneTerminalConsumer.step
      hTwo hTwo hTwoLe ring4 start (1 : Fin 4)
    ¬ (forall e,
      Q11583PPrimePeakSafe.PreparedFollowerRulerAt hTwo ring4 D e) := by
  change
    ¬ (forall e,
      Q11583PPrimePeakSafe.PreparedFollowerRulerAt
        hTwo ring4 afterDeletion e)
  exact after_not_prepared_follower_ruler


/-! ## Item 3 audit: the exposed seam is not immediately birth-ready -/


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
/-- Despite being a free prepared barrier, the exposed edge does not immediately
fire P-prime: the deleted responder's probe is false.  This is why items 1-2
are an invariant failure, not yet a one-row rebirth theorem. -/
theorem exposed_seam_not_immediate_pprime_birth :
    pPrimeBirth hTwo badPrepared.1 badPrepared.2 = false := by
  decide


/-- The clockwise edge from the deleted site points into the surviving leader. -/
def retryPrepared : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  preparedPair hTwo ring4 afterDeletion (1 : Fin 4)


/-- Exact reset-aware P-prime cut on that prospective re-arm edge. -/
def retryPprime : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall
    hTwo retryPrepared.1 retryPrepared.2


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem retryPrepared_left_probe_false :
    retryPrepared.1.core.probe = false := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem retryPrepared_right_leader :
    retryPrepared.2.core.leader = true := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem retryPprime_left_probe_false :
    retryPprime.1.core.probe = false := by
  decide


/-- One more literal current row on 1 -> 2, included only to certify that the
obvious re-arm move still does not arm site 1 while site 2 survives. -/
def afterRetry : Fin 4 -> E :=
  BirthShortDoneTerminalConsumer.step
    hTwo hTwo hTwoLe ring4 afterDeletion (1 : Fin 4)


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem afterRetry1_probe_false :
    (eraseExpiringConfig afterRetry 1).probe = false := by
  decide


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
private theorem afterRetry2_leader :
    (eraseExpiringConfig afterRetry 2).leader = true := by
  decide


/-- What can be certified about item 3 without overclaiming: the exact exposed
edge is not birth-ready, and the natural re-arm edge is blocked by the
surviving leader both at the P-prime cut and after one complete literal row.
This theorem is deliberately *not* a global nonreachability claim. -/
theorem surviving_leader_blocks_short_q11531_rearm :
    badPrepared.2.core.probe = false ∧
      retryPrepared.2.core.leader = true ∧
      retryPrepared.1.core.probe = false ∧
      retryPprime.1.core.probe = false ∧
      (eraseExpiringConfig afterRetry 1).probe = false ∧
      (eraseExpiringConfig afterRetry 2).leader = true := by
  exact ⟨badPrepared_right_probe_false,
    retryPrepared_right_leader,
    retryPrepared_left_probe_false,
    retryPprime_left_probe_false,
    afterRetry1_probe_false,
    afterRetry2_leader⟩


end B9RulerDeletionCounterexample


#print axioms B9RulerDeletionCounterexample.actual_consumer_deletion_breaks_raw_rooted_ruler
#print axioms B9RulerDeletionCounterexample.actual_consumer_deletion_breaks_prepared_ruler
#print axioms B9RulerDeletionCounterexample.exposed_seam_not_immediate_pprime_birth
#print axioms B9RulerDeletionCounterexample.surviving_leader_blocks_short_q11531_rearm

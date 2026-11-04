import Leader.Wu.Birth.PreparedRulerBlocksPPrime
import Leader.Wu.Birth.PPrimeRearmThenBirthRingSix
import Leader.Wu.Birth.ShortDoneTerminalDeletionPpsiFrame
import Leader.Wu.Birth.ShortDoneTerminalPositiveWitness

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9DivisibleBranchRuler

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
  BirthPhaseCohortDesign

variable {n psi kappa tau : Nat}

/-- Exact preparation used by the current P-prime source predicate. -/
def preparedPair
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  (normalizeDeletion pl.core.erase, normalizeDeletion pr.core.erase)

/-- Global barrier-free prepared ruler: every edge, including leader seams,
is already in cyclic successor order. -/
def AllSuccessorLabels
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  forall e,
    let q := preparedPair hpsi ring C e
    q.2.core.label =
      ⟨(q.1.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩

/-- The global ruler is stronger than the follower-only prepared ruler. -/
theorem allSuccessorLabels_preparedFollowerRuler
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (hall : AllSuccessorLabels hpsi ring C) :
    forall e,
      Q11583PPrimePeakSafe.PreparedFollowerRulerAt hpsi ring C e := by
  unfold AllSuccessorLabels at hall
  intro e
  unfold Q11583PPrimePeakSafe.PreparedFollowerRulerAt
  dsimp only
  intro _
  simpa [preparedPair] using hall e

/-- No leader premise is needed: successor geometry alone blocks every actual
prepared P-prime source. -/
theorem allSuccessorLabels_pprimeBlocked
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (hall : AllSuccessorLabels hpsi ring C) :
    forall e, PPrimeBlockedAt hpsi ring C e := by
  exact Q11583PPrimePeakSafe.preparedFollowerRuler_pprimeBlocked
    hpsi ring C
      (allSuccessorLabels_preparedFollowerRuler hpsi ring C hall)

/-! ## Literal n=4, psi=2 divisible-branch counterexample -/

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hFour : 0 < 4 := by decide

abbrev E0 := ExpiringAgentState 2 0 0

def ring4 : DirectedRing 4 := ⟨hFour⟩

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases h with h | h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (.inl (Fin.ext h)))
  · exact .inr (.inr (.inr (Fin.ext h)))

/-- Neutral follower used only at the untouched zero-labelled site. -/
def neutralRaw (label : Fin 2) : AgentState 2 :=
  { BirthShortDoneTerminalPositiveWitness.raw false with label := label }

private theorem neutralRaw_domain (label : Fin 2) :
    (neutralRaw label).inProtocolDomain 0 := by
  simp [neutralRaw, BirthShortDoneTerminalPositiveWitness.raw,
    AgentState.inProtocolDomain]

def neutralCell (label : Fin 2) : E0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (neutralRaw label) (neutralRaw_domain label), false⟩, 0⟩

/-- Prepared labels are literally 0,1,0,1.  Sites 1 and 3 are leaders at
label 1; site 2 is the accepted active-responder deletion fixture. -/
def alignedStart : Fin 4 -> E0 := fun i =>
  if i = (0 : Fin 4) then neutralCell 0
  else if i = (1 : Fin 4) then
    BirthShortDoneTerminalDeletionPpsiFrame.counterexampleLeft
  else if i = (2 : Fin 4) then
    BirthShortDoneTerminalDeletionPpsiFrame.counterexampleRight
  else BirthShortDoneTerminalDeletionPpsiFrame.counterexampleLeft

private theorem alignedStart_edge0 :
    let q := preparedPair hTwo ring4 alignedStart (0 : Fin 4)
    q.2.core.label =
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

private theorem alignedStart_edge1 :
    let q := preparedPair hTwo ring4 alignedStart (1 : Fin 4)
    q.2.core.label =
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

private theorem alignedStart_edge2 :
    let q := preparedPair hTwo ring4 alignedStart (2 : Fin 4)
    q.2.core.label =
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

private theorem alignedStart_edge3 :
    let q := preparedPair hTwo ring4 alignedStart (3 : Fin 4)
    q.2.core.label =
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

theorem alignedStart_allSuccessorLabels :
    AllSuccessorLabels hTwo ring4 alignedStart := by
  unfold AllSuccessorLabels
  intro e
  rcases fin4_cases e with h | h | h | h
  · subst e
    exact alignedStart_edge0
  · subst e
    exact alignedStart_edge1
  · subst e
    exact alignedStart_edge2
  · subst e
    exact alignedStart_edge3

private theorem alignedStart_remote_leader :
    (alignedStart (3 : Fin 4)).core.core.leader = true := by
  decide

/-- Exact metadata result immediately before endpoint leader normalization. -/
def breakingPre : E0 × E0 :=
  BirthShortDoneTerminalHost.doneMetadataEntryWidth
    hTwo hTwo hTwoLe
    (alignedStart (1 : Fin 4)) (alignedStart (2 : Fin 4))

/-- Exact normalized metadata on the same literal row. -/
def breakingMetadata : E0 × E0 :=
  BirthShortDoneTerminalHost.metadata
    hTwo hTwo hTwoLe
    (alignedStart (1 : Fin 4)) (alignedStart (2 : Fin 4))

/-- One literal current-consumer row on edge 1 -> 2. -/
def afterBreaking : Fin 4 -> E0 :=
  BirthShortDoneTerminalConsumer.step
    hTwo hTwo hTwoLe ring4 alignedStart (1 : Fin 4)

private theorem breaking_prepared_right_active :
    deletionActive
      (normalizeDeletion
        (prepareExpiringDisposal hTwo
          (alignedStart (2 : Fin 4))).core.erase) = true := by
  decide

private theorem breakingPre_left_leader :
    breakingPre.1.core.core.leader = true := by
  decide

private theorem breakingPre_left_label_one :
    breakingPre.1.core.core.label = (1 : Fin 2) := by
  decide

private theorem breakingMetadata_left_is_normalize :
    breakingMetadata.1 =
      K2BirthLeaderNormalize.normalizeLeader hTwo breakingPre.1 := by
  rfl

private theorem breakingMetadata_left_label_zero :
    breakingMetadata.1.core.core.label = (0 : Fin 2) := by
  decide

private theorem afterBreaking_site0_eq :
    afterBreaking (0 : Fin 4) = alignedStart (0 : Fin 4) := by
  unfold afterBreaking
  exact BirthShortDoneTerminalConsumer.step_other
    hTwo hTwo hTwoLe ring4 alignedStart
    (1 : Fin 4) (0 : Fin 4) (by decide) (by decide)

private theorem afterBreaking_site3_eq :
    afterBreaking (3 : Fin 4) = alignedStart (3 : Fin 4) := by
  unfold afterBreaking
  exact BirthShortDoneTerminalConsumer.step_other
    hTwo hTwo hTwoLe ring4 alignedStart
    (1 : Fin 4) (3 : Fin 4) (by decide) (by decide)

private theorem afterBreaking_site0_label_zero :
    (afterBreaking (0 : Fin 4)).core.core.label = (0 : Fin 2) := by
  rw [afterBreaking_site0_eq]
  decide

private theorem afterBreaking_site1_label_zero :
    (afterBreaking (1 : Fin 4)).core.core.label = (0 : Fin 2) := by
  decide

private theorem afterBreaking_remote_leader :
    (afterBreaking (3 : Fin 4)).core.core.leader = true := by
  rw [afterBreaking_site3_eq]
  exact alignedStart_remote_leader

private theorem afterBreaking_edge0_not_successor :
    let q := preparedPair hTwo ring4 afterBreaking (0 : Fin 4)
    q.2.core.label ≠
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

/-- Staged certificate that the active-responder path reaches the exact
normalization seam with a leader at label one and leaves the physical row with
zero at that site. -/
theorem normalizeLeader_breaks_literal_aligned_row :
    deletionActive
        (normalizeDeletion
          (prepareExpiringDisposal hTwo
            (alignedStart (2 : Fin 4))).core.erase) = true ∧
      breakingPre.1.core.core.leader = true ∧
      breakingPre.1.core.core.label = (1 : Fin 2) ∧
      breakingMetadata.1 =
        K2BirthLeaderNormalize.normalizeLeader hTwo breakingPre.1 ∧
      breakingMetadata.1.core.core.label = (0 : Fin 2) ∧
      (afterBreaking (0 : Fin 4)).core.core.label = (0 : Fin 2) ∧
      (afterBreaking (1 : Fin 4)).core.core.label = (0 : Fin 2) := by
  exact ⟨breaking_prepared_right_active,
    breakingPre_left_leader,
    breakingPre_left_label_one,
    breakingMetadata_left_is_normalize,
    breakingMetadata_left_label_zero,
    afterBreaking_site0_label_zero,
    afterBreaking_site1_label_zero⟩

/-- Bare global successor geometry is not one-row invariant even in the
literal divisible case 2 | 4, and a remote leader survives the row. -/
theorem literal_consumer_breaks_allSuccessorLabels :
    2 ∣ 4 ∧
      AllSuccessorLabels hTwo ring4 alignedStart ∧
      (exists i, (alignedStart i).core.core.leader = true) ∧
      (exists i, (afterBreaking i).core.core.leader = true) ∧
      ¬ AllSuccessorLabels hTwo ring4 afterBreaking := by
  refine ⟨by decide, alignedStart_allSuccessorLabels,
    ⟨3, alignedStart_remote_leader⟩,
    ⟨3, afterBreaking_remote_leader⟩, ?_⟩
  intro hall
  exact afterBreaking_edge0_not_successor (hall (0 : Fin 4))

/-! ## The genuine first-birth trace never reaches the global ruler -/

private theorem badEdge_not_allSuccessorLabels
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n)
    (hbad :
      let q := preparedPair hpsi ring C e
      q.2.core.label ≠
        ⟨(q.1.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    ¬ AllSuccessorLabels hpsi ring C := by
  intro hall
  exact hbad (hall e)

private theorem q11541_C0_edge0_bad :
    let q := preparedPair hTwo Q11541PPrimeReachability.ring6
      Q11541PPrimeReachability.C0 Q11541PPrimeReachability.s0
    q.2.core.label ≠
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_C1_edge0_bad :
    let q := preparedPair hTwo Q11541PPrimeReachability.ring6
      Q11541PPrimeReachability.C1 Q11541PPrimeReachability.s0
    q.2.core.label ≠
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_C2_edge0_bad :
    let q := preparedPair hTwo Q11541PPrimeReachability.ring6
      Q11541PPrimeReachability.C2 Q11541PPrimeReachability.s0
    q.2.core.label ≠
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_C3_edge0_bad :
    let q := preparedPair hTwo Q11541PPrimeReachability.ring6
      Q11541PPrimeReachability.C3 Q11541PPrimeReachability.s0
    q.2.core.label ≠
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_C4_edge0_bad :
    let q := preparedPair hTwo Q11541PPrimeReachability.ring6
      Q11541PPrimeReachability.C4 Q11541PPrimeReachability.s0
    q.2.core.label ≠
      ⟨(q.1.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩ := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_C2_s0_label_zero :
    (Q11541PPrimeReachability.C2
      Q11541PPrimeReachability.s0).core.core.label = (0 : Fin 2) := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_C2_s1_label_zero :
    (Q11541PPrimeReachability.C2
      Q11541PPrimeReachability.s1).core.core.label = (0 : Fin 2) := by
  decide

/-- The certified first positive birth is the row s0 -> s1, and its successor
still violates the global ruler on that same edge. -/
theorem q11541_first_birth_row_keeps_edge_zero_bad :
    BirthShortDoneTerminalObserver.birthEvent
        hTwo hTwo hTwoLe
        (Q11541PPrimeReachability.C1 Q11541PPrimeReachability.s0)
        (Q11541PPrimeReachability.C1
          (Q11541PPrimeReachability.ring6.rightNeighbor
            Q11541PPrimeReachability.s0)) = true ∧
      (Q11541PPrimeReachability.C2
        Q11541PPrimeReachability.s0).core.core.label = (0 : Fin 2) ∧
      (Q11541PPrimeReachability.C2
        Q11541PPrimeReachability.s1).core.core.label = (0 : Fin 2) ∧
      ¬ AllSuccessorLabels hTwo Q11541PPrimeReachability.ring6
        Q11541PPrimeReachability.C2 := by
  exact ⟨Q11541PPrimeReachability.second_row_birth,
    q11541_C2_s0_label_zero,
    q11541_C2_s1_label_zero,
    badEdge_not_allSuccessorLabels hTwo
      Q11541PPrimeReachability.ring6
      Q11541PPrimeReachability.C2
      Q11541PPrimeReachability.s0 q11541_C2_edge0_bad⟩

/-- Every named prefix of the four-row trace retains the same obstruction
somewhere; in fact edge s0 -> s1 witnesses all five failures here. -/
theorem q11541_trace_never_reaches_allSuccessorLabels :
    ¬ AllSuccessorLabels hTwo Q11541PPrimeReachability.ring6
        Q11541PPrimeReachability.C0 ∧
      ¬ AllSuccessorLabels hTwo Q11541PPrimeReachability.ring6
        Q11541PPrimeReachability.C1 ∧
      ¬ AllSuccessorLabels hTwo Q11541PPrimeReachability.ring6
        Q11541PPrimeReachability.C2 ∧
      ¬ AllSuccessorLabels hTwo Q11541PPrimeReachability.ring6
        Q11541PPrimeReachability.C3 ∧
      ¬ AllSuccessorLabels hTwo Q11541PPrimeReachability.ring6
        Q11541PPrimeReachability.C4 := by
  exact ⟨
    badEdge_not_allSuccessorLabels hTwo
      Q11541PPrimeReachability.ring6 Q11541PPrimeReachability.C0
      Q11541PPrimeReachability.s0 q11541_C0_edge0_bad,
    badEdge_not_allSuccessorLabels hTwo
      Q11541PPrimeReachability.ring6 Q11541PPrimeReachability.C1
      Q11541PPrimeReachability.s0 q11541_C1_edge0_bad,
    badEdge_not_allSuccessorLabels hTwo
      Q11541PPrimeReachability.ring6 Q11541PPrimeReachability.C2
      Q11541PPrimeReachability.s0 q11541_C2_edge0_bad,
    badEdge_not_allSuccessorLabels hTwo
      Q11541PPrimeReachability.ring6 Q11541PPrimeReachability.C3
      Q11541PPrimeReachability.s0 q11541_C3_edge0_bad,
    badEdge_not_allSuccessorLabels hTwo
      Q11541PPrimeReachability.ring6 Q11541PPrimeReachability.C4
      Q11541PPrimeReachability.s0 q11541_C4_edge0_bad⟩

end B9DivisibleBranchRuler

#print axioms B9DivisibleBranchRuler.allSuccessorLabels_preparedFollowerRuler
#print axioms B9DivisibleBranchRuler.allSuccessorLabels_pprimeBlocked
#print axioms B9DivisibleBranchRuler.alignedStart_allSuccessorLabels
#print axioms B9DivisibleBranchRuler.normalizeLeader_breaks_literal_aligned_row
#print axioms B9DivisibleBranchRuler.literal_consumer_breaks_allSuccessorLabels
#print axioms B9DivisibleBranchRuler.q11541_first_birth_row_keeps_edge_zero_bad
#print axioms B9DivisibleBranchRuler.q11541_trace_never_reaches_allSuccessorLabels

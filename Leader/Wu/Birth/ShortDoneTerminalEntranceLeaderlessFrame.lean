import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Birth.ShortDoneTerminalDeletionPpsiFrame
import Leader.Wu.Birth.ShortDoneTerminalFirstHit
import Leader.Wu.Elimination.BirthDispatcherMetadata

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthShortDoneTerminalB1EntranceLeaderlessFrame

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  PPLLWallSweepFiniteCleanup BirthSigMoveDisposalRepair
open PPLLPpsiLeaderCreationRepair
open BirthShortDoneTerminalDeletionRank
open BirthShortDoneTerminalDeletionPpsiFrame

variable {n psi width kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  Fin n → ExpiringAgentState psi kappa tau

/-- Same exact stopping predicate as the rank recursion, restated here so this file does not
import the currently separate B1-entrance repair module. -/
def CurrentNoPreparedDeletion (hpsi : 0 < psi)
    (C : FC n psi kappa tau) : Prop :=
  ∀ i,
    deletionActive
      (normalizeDeletion
        (prepareExpiringDisposal hpsi (C i)).core.erase) = false

/-- Exact execution of a finite word under the current terminal host row. -/
def currentHostRun
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) : FC n psi kappa tau :=
  runLocalSchedule ring
    (BirthShortDoneTerminalHost.row hpsi hwidth hle) C w

/-- The named current consumer step is definitionally the explicit local step
for the current terminal-host row. -/
private theorem consumerStep_eq_localStep
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (e : Fin n) :
    BirthShortDoneTerminalConsumer.step
        hpsi hwidth hle ring C e =
      localStep ring
        (BirthShortDoneTerminalHost.row hpsi hwidth hle) C e := by
  simpa [BirthShortDoneTerminalConsumer.step,
    BirthShortDoneTerminalConsumer.protocol] using
    (PPLLResearchFormulation.localStep_eq_protocol_step
      (BirthShortDoneTerminalConsumer.protocol
        hpsi hwidth hle kappa tau) ring C e).symm

/-- On the responder-deletion priority branch, authorized metadata preserves
all four physical signal fields, in particular both leader bits. -/
private theorem
    doneMetadataAuthorizedEntryWidth_active_responder_signalPair
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = true) :
    K2BirthDispatcher.authSignalPair
        (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hpsi hwidth hle kappa l r) =
      K2BirthDispatcher.authSignalPair (l, r) := by
  unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
  dsimp only
  rw [if_pos hr]
  exact
    (K2BirthDispatcher.eliminate_signal hpsi
      (normalizeDeletion l) (normalizeDeletion r)).trans
      (K2BirthDispatcher.normalize_pair_signal l r)

/-- Preparation, bounded reification and the two expiry calls do not introduce
leaders on an active-responder deletion step. -/
private theorem doneMetadataEntryWidth_active_responder_leaders
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hactive : CurrentPreparedDeletionActive hpsi r) :
    let q := BirthShortDoneTerminalHost.doneMetadataEntryWidth
      hpsi hwidth hle l r
    q.1.core.core.leader = l.core.core.leader ∧
      q.2.core.core.leader = r.core.core.leader := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := BirthShortDoneTerminalHost.doneMetadataEntryWidth
    hpsi hwidth hle l r

  have hactive0 :
      deletionActive (normalizeDeletion r0.core.erase) = true := by
    simpa only [r0, CurrentPreparedDeletionActive] using hactive

  have hauth :=
    doneMetadataAuthorizedEntryWidth_active_responder_signalPair
      hpsi hwidth hle kappa l0.core.erase r0.core.erase hactive0

  have hentry :=
    BirthShortDoneTerminalConsumer.doneMetadataEntryWidth_observation
      hpsi hwidth hle l r

  have hsignal :
      (ExpiringK2Projection.observeCell q.1,
        ExpiringK2Projection.observeCell q.2) =
      (ExpiringK2Projection.observeCell l,
        ExpiringK2Projection.observeCell r) := by
    calc
      (ExpiringK2Projection.observeCell q.1,
          ExpiringK2Projection.observeCell q.2) =
          K2BirthDispatcher.authSignalPair
            (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
              hpsi hwidth hle kappa l0.core.erase r0.core.erase) := by
        simpa only [q, l0, r0] using hentry
      _ = K2BirthDispatcher.authSignalPair
          (l0.core.erase, r0.core.erase) := hauth
      _ = (ExpiringK2Projection.observeCell l0,
          ExpiringK2Projection.observeCell r0) := rfl
      _ = (ExpiringK2Projection.observeCell l,
          ExpiringK2Projection.observeCell r) :=
        Prod.ext
          (K2BirthDispatcher.prepareExpiring_signal hpsi l)
          (K2BirthDispatcher.prepareExpiring_signal hpsi r)

  have hleft := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.1.leader) hsignal
  have hright := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.2.leader) hsignal
  change q.1.core.core.leader = l.core.core.leader at hleft
  change q.2.core.core.leader = r.core.core.leader at hright
  exact ⟨hleft, hright⟩

/-- Hence leaderless input supplies exactly the two normalization-readiness
premises required by the existing current-row P′ψ deletion frame. -/
private theorem doneMetadataEntryWidth_ready_of_leaderless_inputs
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hactive : CurrentPreparedDeletionActive hpsi r) :
    LeaderLabelReady hpsi
        (BirthShortDoneTerminalHost.doneMetadataEntryWidth
          hpsi hwidth hle l r).1 ∧
      LeaderLabelReady hpsi
        (BirthShortDoneTerminalHost.doneMetadataEntryWidth
          hpsi hwidth hle l r).2 := by
  have hleaders :=
    doneMetadataEntryWidth_active_responder_leaders
      hpsi hwidth hle l r hactive
  dsimp only at hleaders
  constructor
  · intro hleader
    have hbad : (false : Bool) = true :=
      hl.symm.trans (hleaders.1.symm.trans hleader)
    have hfalse : False := by simpa using hbad
    exact hfalse.elim
  · intro hleader
    have hbad : (false : Bool) = true :=
      hr.symm.trans (hleaders.2.symm.trans hleader)
    have hfalse : False := by simpa using hbad
    exact hfalse.elim

/-- Strong one-step form used below: leaderlessness discharges the only extra
premise of the existing deletion P′ψ theorem. -/
private theorem
    current_prepared_delete_leaderless_count_lt_and_ppsiControlFrame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : FC n psi kappa tau) (e : Fin n)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hactive : CurrentPreparedDeletionActive hpsi
      (C (ring.rightNeighbor e))) :
    let D := localStep ring
      (BirthShortDoneTerminalHost.row hpsi hwidth hle) C e
    comparisonPathCount D < comparisonPathCount C ∧
      PpsiControlConfigFrame C D := by
  have hready :=
    doneMetadataEntryWidth_ready_of_leaderless_inputs
      hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
      (hzero e) (hzero (ring.rightNeighbor e)) hactive
  exact
    BirthShortDoneTerminalDeletionPpsiFrame.localStep_prepared_responder_delete_count_lt_and_ppsiControlFrame
        hpsi hwidth hle ring hn C e hactive hready.1 hready.2

/-- B1 entrance seam: a current prepared-responder deletion step from a
leaderless configuration either creates a physical leader, or remains
leaderless and preserves every ruler label. -/
theorem current_prepared_delete_leaderless_label_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : FC n psi kappa tau) (e : Fin n)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hactive : CurrentPreparedDeletionActive hpsi
      (C (ring.rightNeighbor e))) :
    let D := BirthShortDoneTerminalConsumer.step
      hpsi hwidth hle ring C e
    (∃ i, (D i).core.core.leader = true) ∨
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        ∀ i, (D i).core.core.label = (C i).core.core.label) := by
  let D := localStep ring
    (BirthShortDoneTerminalHost.row hpsi hwidth hle) C e

  have hlocal :=
    current_prepared_delete_leaderless_count_lt_and_ppsiControlFrame
      hpsi hwidth hle ring hn C e hzero hactive
  change comparisonPathCount D < comparisonPathCount C ∧
    PpsiControlConfigFrame C D at hlocal

  have hlabels : ∀ i,
      (D i).core.core.label = (C i).core.core.label := by
    intro i
    have hi := congrArg PpsiControlView.label (hlocal.2 i)
    change (D i).core.core.label = (C i).core.core.label at hi
    exact hi

  have hstep :
      BirthShortDoneTerminalConsumer.step
        hpsi hwidth hle ring C e = D := by
    simpa only [D] using
      consumerStep_eq_localStep hpsi hwidth hle ring C e

  dsimp only
  rw [hstep]
  by_cases hleader : ∃ i, (D i).core.core.leader = true
  · exact Or.inl hleader
  · refine Or.inr ⟨?_, hlabels⟩
    intro i
    cases hi : (D i).core.core.leader with
    | false => rfl
    | true =>
        exact False.elim (hleader ⟨i, hi⟩)

/-- If the global prepared-deletion stopping predicate fails, some site is
prepared-active.  This is the Boolean extraction used by the drain. -/
private theorem exists_prepared_active_of_not_noPrepared
    (hpsi : 0 < psi) (C : FC n psi kappa tau)
    (hnot : ¬ CurrentNoPreparedDeletion hpsi C) :
    ∃ j : Fin n, CurrentPreparedDeletionActive hpsi (C j) := by
  apply Classical.byContradiction
  intro hnone
  apply hnot
  intro i
  cases hi :
      deletionActive
        (normalizeDeletion
          (prepareExpiringDisposal hpsi (C i)).core.erase) with
  | false => rfl
  | true =>
      exact False.elim
        (hnone ⟨i, by
          simpa [CurrentPreparedDeletionActive] using hi⟩)

/-- Internal stopped-drain outcome.  The quiet branch retains the whole P′ψ
control frame, stronger than label preservation alone. -/
private def DrainOutcome
    (hpsi : 0 < psi)
    (C D : FC n psi kappa tau) : Prop :=
  (∃ i, (D i).core.core.leader = true) ∨
    (BirthShortDoneTerminalFirstHit.Leaderless D ∧
      CurrentNoPreparedDeletion hpsi D ∧
      PpsiControlConfigFrame C D)

/-- Fuelled form of the rank recursion.  A quiet prepared-responder
step strictly lowers `comparisonPathCount`; its P′ψ frame composes with the
recursive tail. -/
private theorem drain_leader_or_ppsiFrame_aux
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : FC n psi kappa tau)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (fuel : Nat) (hfuel : comparisonPathCount C ≤ fuel) :
    ∃ schedule : List (Fin n),
      schedule.length ≤ comparisonPathCount C ∧
      DrainOutcome hpsi C
        (currentHostRun hpsi hwidth hle ring C schedule) := by
  induction fuel generalizing C with
  | zero =>
      by_cases hnone : CurrentNoPreparedDeletion hpsi C
      · refine ⟨[], by simp, ?_⟩
        change DrainOutcome hpsi C C
        exact Or.inr
          ⟨hzero, hnone,
            PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame.refl C⟩
      · obtain ⟨j, hj⟩ :=
          exists_prepared_active_of_not_noPrepared hpsi C hnone
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j := by
          exact rightNeighbor_leftNeighbor_wall ring j
        have hlocal :=
          current_prepared_delete_leaderless_count_lt_and_ppsiControlFrame
            hpsi hwidth hle ring hn C e hzero
              (by simpa [hneighbor] using hj)
        dsimp only at hlocal
        omega
  | succ fuel ih =>
      by_cases hnone : CurrentNoPreparedDeletion hpsi C
      · refine ⟨[], by simp, ?_⟩
        change DrainOutcome hpsi C C
        exact Or.inr
          ⟨hzero, hnone,
            PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame.refl C⟩
      · obtain ⟨j, hj⟩ :=
          exists_prepared_active_of_not_noPrepared hpsi C hnone
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j := by
          exact rightNeighbor_leftNeighbor_wall ring j
        let C₁ := localStep ring
          (BirthShortDoneTerminalHost.row hpsi hwidth hle) C e

        have hlocal :=
          current_prepared_delete_leaderless_count_lt_and_ppsiControlFrame
            hpsi hwidth hle ring hn C e hzero
              (by simpa [hneighbor] using hj)
        change comparisonPathCount C₁ < comparisonPathCount C ∧
          PpsiControlConfigFrame C C₁ at hlocal

        by_cases hleader : ∃ i, (C₁ i).core.core.leader = true
        · refine ⟨[e], ?_, ?_⟩
          · simp only [List.length_cons, List.length_nil]
            omega
          · have hrun :
                currentHostRun hpsi hwidth hle ring C [e] = C₁ := by
              rfl
            rw [hrun]
            exact Or.inl hleader
        · have hzero₁ : BirthShortDoneTerminalFirstHit.Leaderless C₁ := by
            intro i
            cases hi : (C₁ i).core.core.leader with
            | false => rfl
            | true =>
                exact False.elim (hleader ⟨i, hi⟩)
          have hfuel₁ : comparisonPathCount C₁ ≤ fuel := by
            omega
          obtain ⟨tail, htailLength, htailOutcome⟩ :=
            ih (C := C₁) hzero₁ hfuel₁
          refine ⟨e :: tail, ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · have hrun :
                currentHostRun hpsi hwidth hle ring C (e :: tail) =
                  currentHostRun hpsi hwidth hle ring C₁ tail := by
              rfl
            rw [hrun]
            unfold DrainOutcome at htailOutcome ⊢
            rcases htailOutcome with hleaderTail | hquietTail
            · exact Or.inl hleaderTail
            · exact Or.inr
                ⟨hquietTail.1, hquietTail.2.1,
                  PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame.trans
                    hlocal.2 hquietTail.2.2⟩

/-- Word-level B1 entrance lift of the prepared-deletion drain.
The construction uses the same predecessor-of-active-site schedule.  It stops
at the first physical leader; otherwise it completely drains the prepared
ordinary gate, remains leaderless, preserves the full P′ψ control projection,
and therefore preserves every ruler label. -/
theorem exists_currentPreparedDeletionDrain_leader_or_label_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : FC n psi kappa tau)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C) :
    ∃ schedule : List (Fin n),
      schedule.length ≤ comparisonPathCount C ∧
      (let D := currentHostRun hpsi hwidth hle ring C schedule;
       (∃ i, (D i).core.core.leader = true) ∨
        (BirthShortDoneTerminalFirstHit.Leaderless D ∧
          CurrentNoPreparedDeletion hpsi D ∧
          PpsiControlConfigFrame C D ∧
          ∀ i, (D i).core.core.label = (C i).core.core.label)) := by
  obtain ⟨schedule, hlength, hout⟩ :=
    drain_leader_or_ppsiFrame_aux
      hpsi hwidth hle ring hn C hzero
        (comparisonPathCount C) (Nat.le_refl _)
  refine ⟨schedule, hlength, ?_⟩
  dsimp only
  unfold DrainOutcome at hout
  rcases hout with hleader | hquiet
  · exact Or.inl hleader
  · have hlabels : ∀ i,
        (currentHostRun hpsi hwidth hle ring C schedule i).core.core.label =
          (C i).core.core.label := by
      intro i
      have hi := congrArg PpsiControlView.label (hquiet.2.2 i)
      change
        (currentHostRun hpsi hwidth hle ring C schedule i).core.core.label =
          (C i).core.core.label at hi
      exact hi
    exact Or.inr
      ⟨hquiet.1, hquiet.2.1, hquiet.2.2, hlabels⟩

end BirthShortDoneTerminalB1EntranceLeaderlessFrame

#print axioms BirthShortDoneTerminalB1EntranceLeaderlessFrame.current_prepared_delete_leaderless_label_frame
#print axioms BirthShortDoneTerminalB1EntranceLeaderlessFrame.exists_currentPreparedDeletionDrain_leader_or_label_frame

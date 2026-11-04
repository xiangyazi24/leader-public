import Leader.Wu.Birth.ShortDoneTerminalEntranceDrain
import Leader.Wu.Birth.ShortDoneTerminalPassivePreCapRow
import Leader.Wu.Birth.ShortDoneTerminalEntranceLeaderlessFrame

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthShortDoneTerminalB1NextGateR2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  PPLLWallSweepFiniteCleanup BirthSigMoveDisposalRepair
open BirthWaitPassive BirthShortWait BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalDeletionRank
open BirthShortDoneTerminalB1EntranceR2
open LDSinkBoundedKernel
open PPLLWriteSeqPersistenceRegression PPLLWriteSeqRelocation

variable {n psi kappa tau : Nat}

/-! ## 1. The displayed next-gate theorem is false already by locality -/


-- Constructive half of the B1 next-gate file; the n=3 refutation
-- (ordinary_ruler_step_opens_next_gate_refuted) lives in BirthShortDoneTerminalB1NextGateR2_Q11566.lean until repaired.

def LeaderlessPreparedDeletionStepFrame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
      (e : Fin n),
    BirthShortDoneTerminalFirstHit.Leaderless C →
    CurrentPreparedDeletionActive hpsi (C (ring.rightNeighbor e)) →
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring C e
    (∃ i, (D i).core.core.leader = true) ∨
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        ∀ i, (D i).core.core.label = (C i).core.core.label)

/-- Word-level framed strengthening of `exists_currentPreparedDeletionDrain`.
The length bound and global prepared-drain endpoint are the same; the only new
content is the leader-or-pointwise-label frame needed by the ruler induction. -/
def FramedPreparedDeletionDrainLaw
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau),
    BirthShortDoneTerminalFirstHit.Leaderless C →
    ∃ schedule : List (Fin n),
      schedule.length ≤ comparisonPathCount C ∧
      let D := currentRun hpsi h2 ring C schedule
      (∃ i, (D i).core.core.leader = true) ∨
        (BirthShortDoneTerminalFirstHit.Leaderless D ∧
          CurrentNoPreparedDeletion hpsi D ∧
          ∀ i, (D i).core.core.label = (C i).core.core.label)

private theorem currentConsumerStep_eq_localStep
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
    (e : Fin n) :
    BirthShortDoneTerminalConsumer.step
        hpsi (by decide : 0 < 2) h2 ring C e =
      localStep ring
        (BirthShortDoneTerminalHost.row
          hpsi (by decide : 0 < 2) h2) C e := by
  simpa [BirthShortDoneTerminalConsumer.step,
    BirthShortDoneTerminalConsumer.protocol] using
    (PPLLResearchFormulation.localStep_eq_protocol_step
      (BirthShortDoneTerminalConsumer.protocol
        hpsi (by decide : 0 < 2) h2 kappa tau) ring C e).symm

private theorem currentHostRun_two_eq_currentRun
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
    (w : List (Fin n)) :
    BirthShortDoneTerminalB1EntranceLeaderlessFrame.currentHostRun
        hpsi (by decide : 0 < 2) h2 ring C w =
      currentRun hpsi h2 ring C w := by
  induction w generalizing C with
  | nil => rfl
  | cons e rest ih =>
      change
        BirthShortDoneTerminalB1EntranceLeaderlessFrame.currentHostRun
            hpsi (by decide : 0 < 2) h2 ring
            (localStep ring
              (BirthShortDoneTerminalHost.row
                hpsi (by decide : 0 < 2) h2) C e) rest =
          currentRun hpsi h2 ring
            (BirthShortDoneTerminalConsumer.step
              hpsi (by decide : 0 < 2) h2 ring C e) rest
      rw [currentConsumerStep_eq_localStep hpsi h2 ring C e]
      exact ih
        (C := localStep ring
          (BirthShortDoneTerminalHost.row
            hpsi (by decide : 0 < 2) h2) C e)

/-- Statement change: the proved stopped current-row drain now
    discharges the former `LeaderlessPreparedDeletionStepFrame` premise, so
    that premise is intentionally removed. -/
theorem leaderlessPreparedDeletionStepFrame_implies_framedDrain
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n) :
    FramedPreparedDeletionDrainLaw
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C hzero
  obtain ⟨schedule, hlength, hout⟩ :=
    BirthShortDoneTerminalB1EntranceLeaderlessFrame.exists_currentPreparedDeletionDrain_leader_or_label_frame
        (kappa := kappa) (tau := tau)
        hpsi (by decide : 0 < 2) h2 ring hn C hzero
  have hrun :=
    currentHostRun_two_eq_currentRun hpsi h2 ring C schedule
  refine ⟨schedule, hlength, ?_⟩
  dsimp only at hout ⊢
  rw [← hrun]
  rcases hout with hleader | hquiet
  · exact Or.inl hleader
  · refine Or.inr ⟨hquiet.1, ?_, hquiet.2.2.2⟩
    intro i
    exact hquiet.2.1 i

/-- Pointwise physical-label equality is exactly what is needed to transport
an already established non-wrapping ruler prefix. -/
theorem currentRawAlignedPrefix_of_label_frame
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (root : Fin n)
    (C D : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
    (steps : Nat)
    (hlabels : ∀ i, (D i).core.core.label = (C i).core.core.label)
    (haligned : CurrentRawAlignedPrefix hpsi ring root C steps) :
    CurrentRawAlignedPrefix hpsi ring root D steps := by
  intro k hk
  have hold := haligned k hk
  calc
    (D (groupOffset ring root (k + 1))).core.core.label =
        (C (groupOffset ring root (k + 1))).core.core.label :=
      hlabels _
    _ = ⟨((C (groupOffset ring root k)).core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := hold
    _ = ⟨((D (groupOffset ring root k)).core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
      rw [hlabels _]

/-- Consequently a framed deletion drain either exposes a leader or leaves the
whole processed ruler prefix intact while globally reopening the ordinary gate. -/
theorem framedDrain_preserves_processed_prefix
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (hdrain : FramedPreparedDeletionDrainLaw
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (root : Fin n)
    (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
    (steps : Nat)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (haligned : CurrentRawAlignedPrefix hpsi ring root C steps) :
    ∃ schedule : List (Fin n),
      schedule.length ≤ comparisonPathCount C ∧
      let D := currentRun hpsi h2 ring C schedule
      (∃ i, (D i).core.core.leader = true) ∨
        (BirthShortDoneTerminalFirstHit.Leaderless D ∧
          CurrentNoPreparedDeletion hpsi D ∧
          CurrentRawAlignedPrefix hpsi ring root D steps) := by
  obtain ⟨schedule, hlength, hout⟩ := hdrain C hzero
  refine ⟨schedule, hlength, ?_⟩
  dsimp only at hout ⊢
  rcases hout with hleader | hquiet
  · exact Or.inl hleader
  · exact Or.inr
      ⟨hquiet.1, hquiet.2.1,
        currentRawAlignedPrefix_of_label_frame
          hpsi ring root C
          (currentRun hpsi h2 ring C schedule) steps
          hquiet.2.2 haligned⟩

private theorem currentRun_append_local
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
    (left right : List (Fin n)) :
    currentRun hpsi h2 ring C (left ++ right) =
      currentRun hpsi h2 ring
        (currentRun hpsi h2 ring C left) right := by
  let step :
      BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau →
        Fin n → BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau :=
    BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring
  change LDSinkBoundedKernel.run step C (left ++ right) =
    LDSinkBoundedKernel.run step
      (LDSinkBoundedKernel.run step C left) right
  induction left generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, LDSinkBoundedKernel.run]
      exact ih (C := step C e)

/-- One ordinary ruler edge extends an already processed prefix or exposes a
leader.  This is the same local argument as the leaderless-frame drain, kept here because the
original helper is private. -/
private theorem alignedPrefix_step_or_leader_of_open
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (hone : WidthTwoOrdinaryEdgeLaw (kappa := kappa) (tau := tau)
      hpsi h2 hn ring)
    (root : Fin n)
    (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
    (steps : Nat) (hsteps : steps + 1 < n)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (haligned : CurrentRawAlignedPrefix hpsi ring root C steps)
    (hopen : PreparedOrdinaryOpen hpsi
      (C (groupOffset ring root steps))
      (C (ring.rightNeighbor (groupOffset ring root steps)))) :
    let e := groupOffset ring root steps
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring C e
    (∃ i, (D i).core.core.leader = true) ∨
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        CurrentRawAlignedPrefix hpsi ring root D (steps + 1)) := by
  let e := groupOffset ring root steps
  let j := groupOffset ring root (steps + 1)
  have hneighbor : ring.rightNeighbor e = j := by
    simpa only [e, j] using rightNeighbor_groupOffset ring root steps
  have hje : j ≠ e := by
    rw [← hneighbor]
    exact rightNeighbor_ne_self_of_one_lt ring hn e
  let D := BirthShortDoneTerminalConsumer.step
    hpsi (by decide : 0 < 2) h2 ring C e
  have hlocal := hone C e hzero (by simpa only [e] using hopen)
  change
    (∃ i, (D i).core.core.leader = true) ∨
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        (D e).core.core.label = (C e).core.core.label ∧
        (D (ring.rightNeighbor e)).core.core.label =
          ⟨((C e).core.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩) at hlocal
  rcases hlocal with hleader | hquiet
  · exact Or.inl hleader
  · have hleft :
        (D e).core.core.label = (C e).core.core.label := hquiet.2.1
    have hright :
        (D j).core.core.label =
          ⟨((C e).core.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ := by
      rw [← hneighbor]
      exact hquiet.2.2
    have hlabelFrame : ∀ i, i ≠ j →
        (D i).core.core.label = (C i).core.core.label := by
      intro i hij
      by_cases hie : i = e
      · subst i
        exact hleft
      · have hsame := BirthShortDoneTerminalConsumer.step_other
          hpsi (by decide : 0 < 2) h2 ring C e i hie
            (by simpa only [hneighbor] using hij)
        change D i = C i at hsame
        exact congrArg
          (fun u : ExpiringAgentState psi kappa tau => u.core.core.label) hsame
    refine Or.inr ⟨hquiet.1, ?_⟩
    intro k hk
    by_cases hnew : k = steps
    · subst k
      have hnewAligned :
          (D j).core.core.label =
            ⟨((D e).core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := by
        calc
          (D j).core.core.label =
              ⟨((C e).core.core.label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ := hright
          _ = ⟨((D e).core.core.label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ := by
              simpa only [hleft]
      simpa only [e, j] using hnewAligned
    · have hkOld : k < steps := by omega
      have hkBound : k < n := by omega
      have hksBound : k + 1 < n := by omega
      have hkNe : groupOffset ring root k ≠ j := by
        dsimp only [j]
        apply groupOffset_ne_of_lt ring root hkBound hsteps
        omega
      have hksNe : groupOffset ring root (k + 1) ≠ j := by
        dsimp only [j]
        apply groupOffset_ne_of_lt ring root hksBound hsteps
        omega
      have hold := haligned k hkOld
      calc
        (D (groupOffset ring root (k + 1))).core.core.label =
            (C (groupOffset ring root (k + 1))).core.core.label :=
          hlabelFrame _ hksNe
        _ = ⟨((C (groupOffset ring root k)).core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := hold
        _ = ⟨((D (groupOffset ring root k)).core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := by
          rw [hlabelFrame _ hkNe]

/-! ## 4. Corrected interleaved B1 capstone -/

private theorem interleaved_from_aligned
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (hone : WidthTwoOrdinaryEdgeLaw (kappa := kappa) (tau := tau)
      hpsi h2 hn ring)
    (hdrain : FramedPreparedDeletionDrainLaw
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (root : Fin n)
    (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
    (done todo : Nat) (hbound : done + todo < n)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (haligned : CurrentRawAlignedPrefix hpsi ring root C done) :
    ∃ w : List (Fin n),
      let D := currentRun hpsi h2 ring C w
      (∃ i, (D i).core.core.leader = true) ∨
        (BirthShortDoneTerminalFirstHit.Leaderless D ∧
          CurrentNoPreparedDeletion hpsi D ∧
          CurrentRawAlignedPrefix hpsi ring root D (done + todo)) := by
  induction todo generalizing C done with
  | zero =>
      obtain ⟨drain, _hlen, hout⟩ :=
        framedDrain_preserves_processed_prefix
          hpsi h2 ring hdrain root C done hzero haligned
      refine ⟨drain, ?_⟩
      dsimp only at hout ⊢
      rcases hout with hleader | hquiet
      · exact Or.inl hleader
      · exact Or.inr
          ⟨hquiet.1, hquiet.2.1,
            by simpa only [Nat.add_zero] using hquiet.2.2⟩
  | succ todo ih =>
      obtain ⟨drain, _hlen, hout⟩ :=
        framedDrain_preserves_processed_prefix
          hpsi h2 ring hdrain root C done hzero haligned
      let E := currentRun hpsi h2 ring C drain
      change
        (∃ i, (E i).core.core.leader = true) ∨
          (BirthShortDoneTerminalFirstHit.Leaderless E ∧
            CurrentNoPreparedDeletion hpsi E ∧
            CurrentRawAlignedPrefix hpsi ring root E done) at hout
      rcases hout with hleader | hquiet
      · refine ⟨drain, ?_⟩
        change
          (∃ i, (E i).core.core.leader = true) ∨
            (BirthShortDoneTerminalFirstHit.Leaderless E ∧
              CurrentNoPreparedDeletion hpsi E ∧
              CurrentRawAlignedPrefix hpsi ring root E
                (done + Nat.succ todo))
        exact Or.inl hleader
      · let e := groupOffset ring root done
        have hopen : PreparedOrdinaryOpen hpsi
            (E e) (E (ring.rightNeighbor e)) :=
          currentNoPreparedDeletion_edge_open hpsi ring E hquiet.2.1 e
        have hstep := alignedPrefix_step_or_leader_of_open
          hpsi h2 ring hn hone root E done (by omega)
          hquiet.1 hquiet.2.2 (by simpa only [e] using hopen)
        let F := BirthShortDoneTerminalConsumer.step
          hpsi (by decide : 0 < 2) h2 ring E e
        change
          (∃ i, (F i).core.core.leader = true) ∨
            (BirthShortDoneTerminalFirstHit.Leaderless F ∧
              CurrentRawAlignedPrefix hpsi ring root F (done + 1)) at hstep
        have hprefix :
            currentRun hpsi h2 ring C (drain ++ [e]) = F := by
          rw [currentRun_append_local]
          change currentRun hpsi h2 ring E [e] = F
          rfl
        rcases hstep with hleaderStep | hquietStep
        · refine ⟨drain ++ [e], ?_⟩
          rw [hprefix]
          exact Or.inl hleaderStep
        · obtain ⟨tail, htail⟩ :=
            ih (C := F) (done := done + 1) (by omega)
              hquietStep.1 hquietStep.2
          have hfull :
              currentRun hpsi h2 ring C ((drain ++ [e]) ++ tail) =
                currentRun hpsi h2 ring F tail := by
            rw [currentRun_append_local, hprefix]
          refine ⟨(drain ++ [e]) ++ tail, ?_⟩
          rw [hfull]
          dsimp only at htail
          have hsum :
              (done + 1) + todo = done + Nat.succ todo := by
            omega
          simpa only [hsum] using htail

/-- Statement change: `LeaderlessPreparedDeletionStepFrame` is no
    longer an input because the proved stopped leaderless frame supplies the
    drain law.  `WidthTwoOrdinaryEdgeLaw` remains explicit. -/
theorem exists_B1_interleaved_drain_or_leader
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (hone : WidthTwoOrdinaryEdgeLaw (kappa := kappa) (tau := tau)
      hpsi h2 hn ring)
    (root : Fin n)
    (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
    (hleaderless : BirthShortDoneTerminalFirstHit.Leaderless C)
    (steps : Nat) (hsteps : steps < n) :
    ∃ w : List (Fin n),
      let D := currentRun hpsi h2 ring C w
      (∃ i, (D i).core.core.leader = true) ∨
        (BirthShortDoneTerminalFirstHit.Leaderless D ∧
          CurrentNoPreparedDeletion hpsi D ∧
          CurrentRawAlignedPrefix hpsi ring root D steps) := by
  have hdrain : FramedPreparedDeletionDrainLaw
      (kappa := kappa) (tau := tau) hpsi h2 ring :=
    leaderlessPreparedDeletionStepFrame_implies_framedDrain
      hpsi h2 ring hn
  have hstart : CurrentRawAlignedPrefix hpsi ring root C 0 := by
    intro k hk
    omega
  have h := interleaved_from_aligned
    hpsi h2 ring hn hone hdrain root C 0 steps
    (by simpa using hsteps) hleaderless hstart
  simpa only [Nat.zero_add] using h

#print axioms BirthShortDoneTerminalB1NextGateR2.leaderlessPreparedDeletionStepFrame_implies_framedDrain
#print axioms BirthShortDoneTerminalB1NextGateR2.currentRawAlignedPrefix_of_label_frame
#print axioms BirthShortDoneTerminalB1NextGateR2.framedDrain_preserves_processed_prefix
#print axioms BirthShortDoneTerminalB1NextGateR2.exists_B1_interleaved_drain_or_leader

end BirthShortDoneTerminalB1NextGateR2

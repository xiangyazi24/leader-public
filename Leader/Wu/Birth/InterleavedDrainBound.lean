import Leader.Wu.Birth.ShortDoneTerminalInterleavedDrain
import Leader.Wu.WriteSeq.PersistenceRegression
import Leader.Wu.WriteSeq.Relocation

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB1CapstoneDrainLength

/-- Core Lean has no `Nat.le.trans`; this enables `h.trans` on Nat inequalities. -/
theorem _root_.Nat.le.trans {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Nat.le_trans h1 h2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  PPLLWallSweepFiniteCleanup
open BirthSigMoveDisposalRepair BirthShortDoneTerminalDeletionRank
open BirthShortDoneTerminalB1EntranceR2 BirthShortDoneTerminalB1NextGateR2
open LDSinkBoundedKernel
open PPLLWriteSeqRelocation
open PPLLWriteSeqPersistenceRegression

variable {n psi kappa tau : Nat}

/-- Uniform bound for the whole interleaved B1 entrance.  The deletion-rank
accounting itself is independent of `tau`. -/
def L_drain (n tau : Nat) : Nat := n * n + n

private theorem rawActive_preparedActive
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau)
    (hraw : deletionActive u.core.erase = true) :
    deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi u).core.erase) = true := by
  have hs : u.core.erase.core.state = .eliminate_signal := by
    have h := hraw
    simp only [deletionActive, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hp : u.core.erase.core.path ≠ .bot := by
    intro hb
    have h := hraw
    simp [deletionActive, pathPresent, hb] at h
  change deletionActive
    (normalizeDeletion (prepareBoundedDisposal hpsi u.core).erase) = true
  rw [erase_prepareBoundedDisposal]
  have hp' : (prepareDisposal hpsi u.core.erase).core.path ≠ .bot := by
    rw [prepareDisposal_path]
    exact hp
  have hs' :
      (prepareDisposal hpsi u.core.erase).core.state = .eliminate_signal := by
    unfold prepareDisposal
    split
    · cases hx : u.core.erase.core.path with
      | bot => exact (hp hx).elim
      | some label bit => simp [markComparisonForDeletion, hx]
    · exact hs
  rw [normalizeDeletion_eq_of_path_present _ hp']
  exact deletionActive_eq_true _ hs' hp'

/-- The current-host drain predicate implies the older raw cleanup predicate. -/
theorem noActiveDeletion_of_currentNoPreparedDeletion
    (hpsi : 0 < psi) (C : FC n psi kappa tau)
    (hno : CurrentNoPreparedDeletion hpsi C) : NoActiveDeletion C := by
  intro i
  cases hraw : deletionActive (C i).core.erase with
  | false => rfl
  | true =>
      have hp := rawActive_preparedActive hpsi (C i) hraw
      have hn := hno i
      rw [hp] at hn
      cases hn

private theorem currentRun_append_local
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (left right : List (Fin n)) :
    currentRun hpsi h2 ring C (left ++ right) =
      currentRun hpsi h2 ring (currentRun hpsi h2 ring C left) right := by
  let step : FC n psi kappa tau → Fin n → FC n psi kappa tau :=
    BirthShortDoneTerminalConsumer.step hpsi (by decide : 0 < 2) h2 ring
  change LDSinkBoundedKernel.run step C (left ++ right) =
    LDSinkBoundedKernel.run step (LDSinkBoundedKernel.run step C left) right
  induction left generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, LDSinkBoundedKernel.run]
      exact ih (C := step C e)

private theorem alignedStep_or_leader
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (hone : WidthTwoOrdinaryEdgeLaw (kappa := kappa) (tau := tau)
      hpsi h2 hn ring)
    (root : Fin n) (C : FC n psi kappa tau)
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
  let D := BirthShortDoneTerminalConsumer.step
    hpsi (by decide : 0 < 2) h2 ring C e
  have hlocal := hone C e hzero (by simpa only [e] using hopen)
  change
    (∃ i, (D i).core.core.leader = true) ∨
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        (D e).core.core.label = (C e).core.core.label ∧
        (D (ring.rightNeighbor e)).core.core.label =
          ⟨((C e).core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) at hlocal
  rcases hlocal with hleader | hquiet
  · exact Or.inl hleader
  · have hleft := hquiet.2.1
    have hright : (D j).core.core.label =
        ⟨((C e).core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
      rw [← hneighbor]
      exact hquiet.2.2
    have hframe : ∀ i, i ≠ j →
        (D i).core.core.label = (C i).core.core.label := by
      intro i hij
      by_cases hie : i = e
      · subst i
        exact hleft
      · have hs := BirthShortDoneTerminalConsumer.step_other
          hpsi (by decide : 0 < 2) h2 ring C e i hie
            (by simpa only [hneighbor] using hij)
        change D i = C i at hs
        exact congrArg
          (fun u : ExpiringAgentState psi kappa tau => u.core.core.label) hs
    refine Or.inr ⟨hquiet.1, ?_⟩
    intro k hk
    by_cases hnew : k = steps
    · subst k
      have hnewAligned : (D j).core.core.label =
          ⟨((D e).core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
        calc
          _ = ⟨((C e).core.core.label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ := hright
          _ = _ := by simpa only [hleft]
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
            (C (groupOffset ring root (k + 1))).core.core.label := hframe _ hksNe
        _ = ⟨((C (groupOffset ring root k)).core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := hold
        _ = ⟨((D (groupOffset ring root k)).core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := by rw [hframe _ hkNe]

private theorem interleaved_bounded
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (hn : 1 < n)
    (hone : WidthTwoOrdinaryEdgeLaw (kappa := kappa) (tau := tau)
      hpsi h2 hn ring)
    (hdrain : FramedPreparedDeletionDrainLaw
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (root : Fin n) (C : FC n psi kappa tau)
    (done todo : Nat) (hbound : done + todo < n)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (haligned : CurrentRawAlignedPrefix hpsi ring root C done) :
    ∃ w : List (Fin n),
      w.length ≤ (todo + 1) * n + todo ∧
      let D := currentRun hpsi h2 ring C w
      (∃ i, (D i).core.core.leader = true) ∨
        (BirthShortDoneTerminalFirstHit.Leaderless D ∧
          CurrentNoPreparedDeletion hpsi D ∧
          CurrentRawAlignedPrefix hpsi ring root D (done + todo)) := by
  induction todo generalizing C done with
  | zero =>
      obtain ⟨drain, hlen, hout⟩ :=
        framedDrain_preserves_processed_prefix
          hpsi h2 ring hdrain root C done hzero haligned
      refine ⟨drain, ?_, ?_⟩
      · simpa using hlen.trans (comparisonPathCount_le C)
      · dsimp only at hout ⊢
        rcases hout with hleader | hquiet
        · exact Or.inl hleader
        · exact Or.inr
            ⟨hquiet.1, hquiet.2.1,
              by simpa only [Nat.add_zero] using hquiet.2.2⟩
  | succ todo ih =>
      obtain ⟨drain, hlen, hout⟩ :=
        framedDrain_preserves_processed_prefix
          hpsi h2 ring hdrain root C done hzero haligned
      have hlenN : drain.length ≤ n := hlen.trans (comparisonPathCount_le C)
      let E := currentRun hpsi h2 ring C drain
      change
        (∃ i, (E i).core.core.leader = true) ∨
          (BirthShortDoneTerminalFirstHit.Leaderless E ∧
            CurrentNoPreparedDeletion hpsi E ∧
            CurrentRawAlignedPrefix hpsi ring root E done) at hout
      rcases hout with hleader | hquiet
      · refine ⟨drain, ?_, Or.inl hleader⟩
        have hm : n ≤ (Nat.succ todo + 1) * n := by
          have h := Nat.mul_le_mul_right n
            (show 1 ≤ Nat.succ todo + 1 by omega)
          simpa only [Nat.one_mul] using h
        exact hlenN.trans (hm.trans (Nat.le_add_right _ _))
      · let e := groupOffset ring root done
        have hopen : PreparedOrdinaryOpen hpsi
            (E e) (E (ring.rightNeighbor e)) :=
          currentNoPreparedDeletion_edge_open hpsi ring E hquiet.2.1 e
        have hs := alignedStep_or_leader hpsi h2 ring hn hone root E done
          (by omega) hquiet.1 hquiet.2.2 (by simpa only [e] using hopen)
        let F := BirthShortDoneTerminalConsumer.step
          hpsi (by decide : 0 < 2) h2 ring E e
        change
          (∃ i, (F i).core.core.leader = true) ∨
            (BirthShortDoneTerminalFirstHit.Leaderless F ∧
              CurrentRawAlignedPrefix hpsi ring root F (done + 1)) at hs
        have hprefix : currentRun hpsi h2 ring C (drain ++ [e]) = F := by
          rw [currentRun_append_local]
          change currentRun hpsi h2 ring E [e] = F
          rfl
        rcases hs with hleaderStep | hquietStep
        · refine ⟨drain ++ [e], ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            have hm : n ≤ (Nat.succ todo + 1) * n := by
              have h := Nat.mul_le_mul_right n
                (show 1 ≤ Nat.succ todo + 1 by omega)
              simpa only [Nat.one_mul] using h
            exact (Nat.add_le_add_right hlenN 1).trans
              (Nat.add_le_add hm (by omega))
          · rw [hprefix]
            exact Or.inl hleaderStep
        · obtain ⟨tail, htailLen, htail⟩ :=
            ih (C := F) (done := done + 1) (by omega)
              hquietStep.1 hquietStep.2
          have hfull : currentRun hpsi h2 ring C ((drain ++ [e]) ++ tail) =
              currentRun hpsi h2 ring F tail := by
            rw [currentRun_append_local, hprefix]
          refine ⟨(drain ++ [e]) ++ tail, ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            calc
              drain.length + 1 + tail.length ≤
                  n + 1 + ((todo + 1) * n + todo) :=
                Nat.add_le_add (Nat.add_le_add_right hlenN 1) htailLen
              _ = (Nat.succ todo + 1) * n + Nat.succ todo := by
                simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
                ac_rfl
          · rw [hfull]
            dsimp only at htail ⊢
            have hsum : (done + 1) + todo = done + Nat.succ todo := by omega
            simpa only [hsum] using htail

/-- Bounded form of the unconditional B1 capstone. -/
theorem exists_B1_interleaved_drain_or_leader_bounded
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n) (root : Fin n)
    (C : FC n psi kappa tau)
    (hleaderless : BirthShortDoneTerminalFirstHit.Leaderless C)
    (steps : Nat) (hsteps : steps < n) :
    ∃ w : List (Fin n),
      w.length ≤ L_drain n tau ∧
      let D := currentRun hpsi h2 ring C w
      (∃ i, (D i).core.core.leader = true) ∨
        (BirthShortDoneTerminalFirstHit.Leaderless D ∧
          CurrentNoPreparedDeletion hpsi D ∧
          NoActiveDeletion D ∧
          CurrentRawAlignedPrefix hpsi ring root D steps) := by
  have hone := BirthShortDoneTerminalB1EntranceR3.widthTwoOrdinaryEdgeLaw
    (kappa := kappa) (tau := tau) hpsi h2 hn ring
  have hdrain : FramedPreparedDeletionDrainLaw
      (kappa := kappa) (tau := tau) hpsi h2 ring :=
    leaderlessPreparedDeletionStepFrame_implies_framedDrain hpsi h2 ring hn
  have hstart : CurrentRawAlignedPrefix hpsi ring root C 0 := by
    intro k hk
    omega
  obtain ⟨w, hlen, hout⟩ :=
    interleaved_bounded hpsi h2 ring hn hone hdrain root C 0 steps
      (by simpa using hsteps) hleaderless hstart
  refine ⟨w, ?_, ?_⟩
  · have hm : (steps + 1) * n ≤ n * n :=
      Nat.mul_le_mul_right n (by omega)
    have hb := Nat.add_le_add hm (Nat.le_of_lt hsteps)
    exact hlen.trans (by simpa [L_drain] using hb)
  · dsimp only at hout ⊢
    rcases hout with hleader | hquiet
    · exact Or.inl hleader
    · exact Or.inr
        ⟨hquiet.1, hquiet.2.1,
          noActiveDeletion_of_currentNoPreparedDeletion hpsi _ hquiet.2.1,
          by simpa only [Nat.zero_add] using hquiet.2.2⟩

end BirthB1CapstoneDrainLength

#print axioms BirthB1CapstoneDrainLength.noActiveDeletion_of_currentNoPreparedDeletion
#print axioms BirthB1CapstoneDrainLength.exists_B1_interleaved_drain_or_leader_bounded

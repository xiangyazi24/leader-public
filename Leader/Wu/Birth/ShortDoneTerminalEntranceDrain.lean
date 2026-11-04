import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Birth.ShortDoneTerminalDeletionRank
import Leader.Wu.Birth.ShortDoneTerminalDeletionPpsiFrame
import Leader.Wu.Birth.ShortDoneTerminalNoHitCount
import Leader.Wu.Birth.LabelGeometryStabilization

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthShortDoneTerminalB1EntranceR2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  PPLLWallSweepFiniteCleanup BirthSigMoveDisposalRepair
open BirthShortDoneTerminalDeletionRank
open PPLLWriteSeqPersistenceRegression PPLLWriteSeqRelocation
open LDSinkBoundedKernel

variable {n psi width kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  Fin n → ExpiringAgentState psi kappa tau

/-- Copy of the exact gate from the currently noncompiling
`BirthShortDoneTerminalOrdinaryLabelR1`.  No theorem from that module is used. -/
def PreparedOrdinaryOpen (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  deletionActive r0 = false ∧ deletionActive l0 = false

/-- Every site is inactive after the exact preparation+normalization used by
current dispatch. -/
def CurrentNoPreparedDeletion (hpsi : 0 < psi)
    (C : FC n psi kappa tau) : Prop :=
  ∀ i,
    deletionActive
      (normalizeDeletion
        (prepareExpiringDisposal hpsi (C i)).core.erase) = false

/-- A globally prepared-drained state opens the current ordinary gate on every
edge immediately. -/
theorem currentNoPreparedDeletion_edge_open
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau)
    (hno : CurrentNoPreparedDeletion hpsi C) (e : Fin n) :
    PreparedOrdinaryOpen hpsi (C e) (C (ring.rightNeighbor e)) := by
  change
    deletionActive
        (normalizeDeletion
          (prepareExpiringDisposal hpsi
            (C (ring.rightNeighbor e))).core.erase) = false ∧
      deletionActive
        (normalizeDeletion
          (prepareExpiringDisposal hpsi (C e)).core.erase) = false
  exact ⟨hno (ring.rightNeighbor e), hno e⟩

/-- Exact execution of a finite word under the current terminal host row. -/
def currentHostRun
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) : FC n psi kappa tau :=
  runLocalSchedule ring
    (BirthShortDoneTerminalHost.row hpsi hwidth hle) C w

/-- The old finite-deletion strong recursion ports to the current host when the
stopping predicate is the exact prepared/normalized gate.  Pending terminal
3/4 disposal is already included because preparation converts it to active
deletion before this predicate is tested. -/
theorem exists_currentPreparedDeletionDrain
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : FC n psi kappa tau) :
    ∃ schedule : List (Fin n),
      schedule.length ≤ comparisonPathCount C ∧
      CurrentNoPreparedDeletion hpsi
        (currentHostRun hpsi hwidth hle ring C schedule) := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : CurrentNoPreparedDeletion hpsi C
      · refine ⟨[], ?_, ?_⟩
        · simp
        · simpa [currentHostRun, runLocalSchedule] using hnone
      · have hexists : ∃ j : Fin n,
            CurrentPreparedDeletionActive hpsi (C j) := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi :
              deletionActive
                (normalizeDeletion
                  (prepareExpiringDisposal hpsi (C i)).core.erase) with
          | false => rfl
          | true =>
              exact False.elim
                (hnot ⟨i, by
                  simpa [CurrentPreparedDeletionActive] using hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j := by
          exact rightNeighbor_leftNeighbor_wall ring j
        let C₁ := localStep ring
          (BirthShortDoneTerminalHost.row hpsi hwidth hle) C e
        have hstep :=
          BirthShortDoneTerminalDeletionRank.localStep_prepared_responder_delete_count_lt
            hpsi hwidth hle ring hn C e
              (by simpa [hneighbor] using hj)
        change comparisonPathCount C₁ < comparisonPathCount C at hstep
        have hlt : comparisonPathCount C₁ < k := by
          rw [← hk]
          exact hstep
        obtain ⟨tail, htailLength, htailNoPrepared⟩ :=
          ih (comparisonPathCount C₁) hlt C₁ rfl
        refine ⟨e :: tail, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · simpa [currentHostRun, C₁, runLocalSchedule] using
            htailNoPrepared

/-- Literal width-two execution of the exact current terminal consumer. -/
def currentRun
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) : FC n psi kappa tau :=
  LDSinkBoundedKernel.run
    (BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring) C w

/-- Recursive gate: the exact ordinary gate must hold before every
edge of the supplied current-consumer word. -/
def OrdinaryOpenAlong
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) :
    FC n psi kappa tau → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es =>
      PreparedOrdinaryOpen hpsi (C e) (C (ring.rightNeighbor e)) ∧
      OrdinaryOpenAlong hpsi h2 ring
        (BirthShortDoneTerminalConsumer.step
          hpsi (by decide : 0 < 2) h2 ring C e) es

/-- Current full-state version of the non-wrapping aligned ruler prefix. -/
def CurrentRawAlignedPrefix
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (root : Fin n) (C : FC n psi kappa tau) (steps : Nat) : Prop :=
  ∀ k, k < steps →
    (C (groupOffset ring root (k + 1))).core.core.label =
      ⟨((C (groupOffset ring root k)).core.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

/-- Explicit hypothesis replacing the theorem in the currently noncompiling
`BirthShortDoneTerminalOrdinaryLabelR1`.  This is its width-two type, not a new
protocol assumption hidden in execution. -/
def WidthTwoOrdinaryEdgeLaw
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 1 < n)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n psi kappa tau) (e : Fin n),
    BirthShortDoneTerminalFirstHit.Leaderless C →
    PreparedOrdinaryOpen hpsi (C e) (C (ring.rightNeighbor e)) →
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring C e
    (∃ i, (D i).core.core.leader = true) ∨
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        (D e).core.core.label = (C e).core.core.label ∧
        (D (ring.rightNeighbor e)).core.core.label =
          ⟨((C e).core.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩)

private theorem currentRun_append
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (left right : List (Fin n)) :
    currentRun hpsi h2 ring C (left ++ right) =
      currentRun hpsi h2 ring
        (currentRun hpsi h2 ring C left) right := by
  let step : FC n psi kappa tau → Fin n → FC n psi kappa tau :=
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

private theorem ordinaryOpenAlong_append
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (left right : List (Fin n)) :
    OrdinaryOpenAlong hpsi h2 ring C (left ++ right) ↔
      OrdinaryOpenAlong hpsi h2 ring C left ∧
        OrdinaryOpenAlong hpsi h2 ring
          (currentRun hpsi h2 ring C left) right := by
  induction left generalizing C with
  | nil =>
      simp [OrdinaryOpenAlong, currentRun, LDSinkBoundedKernel.run]
  | cons e rest ih =>
      let C₁ := BirthShortDoneTerminalConsumer.step
        hpsi (by decide : 0 < 2) h2 ring C e
      change
        (PreparedOrdinaryOpen hpsi
            (C e) (C (ring.rightNeighbor e)) ∧
          OrdinaryOpenAlong hpsi h2 ring C₁ (rest ++ right)) ↔
        (PreparedOrdinaryOpen hpsi
            (C e) (C (ring.rightNeighbor e)) ∧
          OrdinaryOpenAlong hpsi h2 ring C₁ rest) ∧
          OrdinaryOpenAlong hpsi h2 ring
            (currentRun hpsi h2 ring C₁ rest) right
      rw [ih (C := C₁)]
      constructor
      · rintro ⟨ha, hb, hc⟩
        exact ⟨⟨ha, hb⟩, hc⟩
      · rintro ⟨⟨ha, hb⟩, hc⟩
        exact ⟨ha, hb, hc⟩

private theorem currentRawAlignedPrefix_step_or_leader_of_open
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (hone : WidthTwoOrdinaryEdgeLaw (kappa := kappa) (tau := tau)
      hpsi h2 hn ring)
    (root : Fin n) (C : FC n psi kappa tau) (steps : Nat)
    (hsteps : steps + 1 < n)
    (hleaderless : BirthShortDoneTerminalFirstHit.Leaderless C)
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
    simpa only [e, j] using
      (rightNeighbor_groupOffset ring root steps)
  have hje : j ≠ e := by
    rw [← hneighbor]
    exact rightNeighbor_ne_self_of_one_lt ring hn e
  let D := BirthShortDoneTerminalConsumer.step
    hpsi (by decide : 0 < 2) h2 ring C e
  have hlocal := hone C e hleaderless (by simpa only [e] using hopen)
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
        (D e).core.core.label = (C e).core.core.label :=
      hquiet.2.1
    have hright :
        (D j).core.core.label =
          ⟨((C e).core.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ := by
      rw [← hneighbor]
      exact hquiet.2.2
    have hframe : ∀ i, i ≠ j →
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
          (fun u : ExpiringAgentState psi kappa tau =>
            u.core.core.label) hsame
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
          hframe _ hksNe
        _ = ⟨((C (groupOffset ring root k)).core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := hold
        _ = ⟨((D (groupOffset ring root k)).core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := by
          rw [hframe _ hkNe]

/-- Current-host lift of the stopped ruler-prefix theorem.  The only physical
input not proved in this file is the explicitly supplied one-edge ordinary law;
`OrdinaryOpenAlong` supplies its gate at the exact current state of every edge. -/
theorem current_stopped_labelSweepPrefix_outcome_of_open
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (hone : WidthTwoOrdinaryEdgeLaw (kappa := kappa) (tau := tau)
      hpsi h2 hn ring)
    (root : Fin n) (C : FC n psi kappa tau)
    (hleaderless : BirthShortDoneTerminalFirstHit.Leaderless C)
    (steps : Nat) (hsteps : steps < n)
    (hopen : OrdinaryOpenAlong hpsi h2 ring C
      (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root steps)) :
    (∃ t, t ≤ steps ∧
        ∃ i,
          ((currentRun hpsi h2 ring C
            (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root t)) i).core.core.leader =
            true) ∨
      (let D := currentRun hpsi h2 ring C
          (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root steps)
       BirthShortDoneTerminalFirstHit.Leaderless D ∧
         CurrentRawAlignedPrefix hpsi ring root D steps) := by
  induction steps with
  | zero =>
      refine Or.inr ?_
      change
        BirthShortDoneTerminalFirstHit.Leaderless
            (currentRun hpsi h2 ring C
              (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root 0)) ∧
          CurrentRawAlignedPrefix hpsi ring root
            (currentRun hpsi h2 ring C
              (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root 0)) 0
      have hrun :
          currentRun hpsi h2 ring C
              (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root 0) = C := by
        simp [currentRun,
          PPLLPpsiLabelGeometry.labelSweepPrefixSchedule,
          LDSinkBoundedKernel.run]
      rw [hrun]
      exact ⟨hleaderless, by intro k hk; omega⟩
  | succ steps ih =>
      have hprevBound : steps < n := by omega
      let pre :=
        PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root steps
      let e := groupOffset ring root steps
      let M := currentRun hpsi h2 ring C pre
      have hopenAppend :
          OrdinaryOpenAlong hpsi h2 ring C (pre ++ [e]) := by
        simpa only [pre, e,
          PPLLPpsiLabelGeometry.labelSweepPrefixSchedule_succ] using hopen
      have hopenParts :=
        (ordinaryOpenAlong_append hpsi h2 ring C pre [e]).1 hopenAppend
      change
        OrdinaryOpenAlong hpsi h2 ring C pre ∧
          OrdinaryOpenAlong hpsi h2 ring M [e] at hopenParts
      have hopenPrev :
          OrdinaryOpenAlong hpsi h2 ring C
            (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root steps) := by
        simpa only [pre] using hopenParts.1
      rcases ih hprevBound hopenPrev with hfound | hquiet
      · exact Or.inl
          ⟨hfound.choose, by omega, hfound.choose_spec.2⟩
      · have hquietM :
            BirthShortDoneTerminalFirstHit.Leaderless M ∧
              CurrentRawAlignedPrefix hpsi ring root M steps := by
          simpa only [M, pre] using hquiet
        have hopenLast :
            PreparedOrdinaryOpen hpsi
              (M e) (M (ring.rightNeighbor e)) := by
          simpa only [OrdinaryOpenAlong, and_true] using hopenParts.2
        let D := BirthShortDoneTerminalConsumer.step
          hpsi (by decide : 0 < 2) h2 ring M e
        have hlocal :=
          currentRawAlignedPrefix_step_or_leader_of_open
            hpsi h2 ring hn hone root M steps (by omega)
              hquietM.1 hquietM.2 hopenLast
        change
          (∃ i, (D i).core.core.leader = true) ∨
            (BirthShortDoneTerminalFirstHit.Leaderless D ∧
              CurrentRawAlignedPrefix hpsi ring root D (steps + 1)) at hlocal
        have hrunD :
            currentRun hpsi h2 ring C
              (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule
                ring root (steps + 1)) = D := by
          rw [PPLLPpsiLabelGeometry.labelSweepPrefixSchedule_succ]
          rw [currentRun_append]
          rfl
        rcases hlocal with hleaderD | hquietD
        · refine Or.inl ⟨steps + 1, by omega, ?_⟩
          rw [hrunD]
          exact hleaderD
        · refine Or.inr ?_
          rw [hrunD]
          exact hquietD

end BirthShortDoneTerminalB1EntranceR2

#print axioms BirthShortDoneTerminalB1EntranceR2.currentNoPreparedDeletion_edge_open
#print axioms BirthShortDoneTerminalB1EntranceR2.exists_currentPreparedDeletionDrain
#print axioms BirthShortDoneTerminalB1EntranceR2.current_stopped_labelSweepPrefix_outcome_of_open

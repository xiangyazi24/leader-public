import Leader.Wu.Entrance.RelabelBreaksOuterNeutral
import Leader.Wu.Splice.HostRightFollowerLabel


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open B9Host B9FullCarrierHost
open WriterProducerRepair
open BirthLeaderlessBirthMassRenewal


variable {n ψ κ τ : Nat}


/-!
Truth check.


`ConcreteB7AdmittedPassive` requires `ProposalNoWrite` on every edge.
`ProposalNoWrite` contains `pairRelabels = false`, so its right proposal
cannot have a different resident label.  This is the obstruction to composing
the bare-R1 witness with the concrete R2C port.
-/


private theorem proposalNoWrite_right_label
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2Coherence.Cell ψ κ τ)
    (hNo : R2Coherence.ProposalNoWrite
      hψ (by decide : 0 < 2) h2 l r) :
    ((R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2).base.core.core.label =
      r.phys.base.core.core.label := by
  change
    R2Coherence.pairWrites l.phys r.phys
        (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).1
        (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2 = false ∧
      R2Coherence.pairRelabels l.phys r.phys
        (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).1
        (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2 = false at hNo
  by_cases hEq :
      ((R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2).base.core.core.label =
        r.phys.base.core.core.label
  · exact hEq
  · have hNe :
        r.phys.base.core.core.label ≠
          ((R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2).base.core.core.label := by
      intro h
      exact hEq h.symm
    have hchg :
        R2Coherence.labelChanged r.phys
          (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2 = true := by
      unfold R2Coherence.labelChanged
      simp [hNe]
    have hfalse : False := by
      have hrel := hNo.2
      unfold R2Coherence.pairRelabels at hrel
      rw [hchg] at hrel
      simpa using hrel
    exact hfalse.elim


private theorem hostR2C_right_label_of_open_noWrite
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2Coherence.Cell ψ κ τ)
    (hOpenL : R2Coherence.OpenControl l)
    (hOpenR : R2Coherence.OpenControl r)
    (hNo : R2Coherence.ProposalNoWrite
      hψ (by decide : 0 < 2) h2 l r) :
    (((hostR2C (κ := κ) (τ := τ) hψ h2).row l r).2).phys.base.core.core.label =
      r.phys.base.core.core.label := by
  rcases hOpenL with ⟨hlm, hlt⟩
  rcases hOpenR with ⟨hrm, hrt⟩
  have hrow := R2Coherence.row_eq_r2_of_open_no_write
    hψ (by decide : 0 < 2) h2 l r hlm hrm hlt hrt hNo
  have hlabel := proposalNoWrite_right_label hψ h2 l r hNo
  change
    ((R2Coherence.row hψ (by decide : 0 < 2) h2 l r).2).phys.base.core.core.label =
      r.phys.base.core.core.label
  rw [hrow]
  simpa [R2Coherence.install] using hlabel


/-- An actual concrete-host relabel exit.  The served right endpoint is a
follower before and after the selected physical HOST service, but its resident
label changes.  `j ≠ e` makes "responder" literal rather than the self-edge
alias case. -/
def RelabelExitAt
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : Config n ψ κ τ) (e : Fin n) : Prop :=
  let j := ring.rightNeighbor e
  let r := C j
  let q := (hostR2C (κ := κ) (τ := τ) hψ h2).row (C e).phys r.phys
  j ≠ e ∧
    outputFinal r = false ∧
    q.2.phys.base.core.core.leader = false ∧
    q.2.phys.base.core.core.label ≠
      r.phys.phys.base.core.core.label


/-- The relabel exit is impossible from the CURRENT passive
admission class: its per-edge `ProposalNoWrite` already forbids the label
change that would trigger `rightFollowerRelabelledV7`. -/
theorem relabelExitAt_false_of_passive_admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : Config n ψ κ τ) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hψ h2 ring C) :
    ¬ RelabelExitAt hψ h2 ring C e := by
  intro hExit
  unfold RelabelExitAt at hExit
  dsimp only at hExit
  have hOpenL : R2Coherence.OpenControl (C e).phys :=
    hA.2.2.1 e
  have hOpenR :
      R2Coherence.OpenControl (C (ring.rightNeighbor e)).phys :=
    hA.2.2.1 (ring.rightNeighbor e)
  have hNo :
      R2Coherence.ProposalNoWrite hψ (by decide : 0 < 2) h2
        (C e).phys (C (ring.rightNeighbor e)).phys :=
    (hA.2.2.2 e).2.2
  have hframe := hostR2C_right_label_of_open_noWrite
    hψ h2 (C e).phys (C (ring.rightNeighbor e)).phys
    hOpenL hOpenR hNo
  exact hExit.2.2.2 hframe


/-- Therefore the concrete witness cannot exist.
This is stronger than failing to find a `cleanPhys3` instance. -/
theorem no_passive_admitted_relabel_exit_witness
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) :
    ¬ ∃ (C : Config n ψ κ τ) (e : Fin n),
      ConcreteB7AdmittedPassive hψ h2 ring C ∧
      FinalLeaderless C ∧
      RelabelExitAt hψ h2 ring C e := by
  rintro ⟨C, e, hA, _hL, hExit⟩
  exact relabelExitAt_false_of_passive_admitted
    hψ h2 ring C e hA hExit

/-- Closure with an explicit relabel-exit stopping event. -/
def ConcreteB7PassiveClosedOrExitObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e
    HasLeader D ∨
      ConcreteB7AdmittedPassive hψ h2 ring D ∨
      RelabelExitAt hψ h2 ring C e


/-- Because `RelabelExitAt` is incompatible with the current admission
predicate, Closed-or-Exit collapses to the old two-way closure obligation. -/
theorem concreteB7PassiveClosed_of_closedOrExit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hX : ConcreteB7PassiveClosedOrExitObligation
      (κ := κ) (τ := τ) hψ h2 ring) :
    ConcreteB7AdmittedPassiveClosedObligation
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hA hL
  have h := hX C e hA hL
  dsimp only at h
  rcases h with hLead | hAdm | hExit
  · exact Or.inl hLead
  · exact Or.inr hAdm
  · exact False.elim
      (relabelExitAt_false_of_passive_admitted
        hψ h2 ring C e hA hExit)


/-- Conversely, ordinary passive closure trivially implies closure-or-exit. -/
theorem concreteB7PassiveClosedOrExit_of_closed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hC : ConcreteB7AdmittedPassiveClosedObligation
      (κ := κ) (τ := τ) hψ h2 ring) :
    ConcreteB7PassiveClosedOrExitObligation
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hA hL
  dsimp only
  rcases hC C e hA hL with hLead | hAdm
  · exact Or.inl hLead
  · exact Or.inr (Or.inl hAdm)


/-- Exact status of the proposed repair under the current admission boundary. -/
theorem concreteB7PassiveClosedOrExit_iff_closed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) :
    ConcreteB7PassiveClosedOrExitObligation
        (κ := κ) (τ := τ) hψ h2 ring ↔
      ConcreteB7AdmittedPassiveClosedObligation
        (κ := κ) (τ := τ) hψ h2 ring := by
  constructor
  · exact concreteB7PassiveClosed_of_closedOrExit hψ h2 ring
  · exact concreteB7PassiveClosedOrExit_of_closed hψ h2 ring


/-- No relabel exit has occurred along the literal prefix. -/
def NoRelabelExitAlong
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : Config n ψ κ τ) :
    List (Fin n) → Prop
  | [] => True
  | e :: rest =>
      ¬ RelabelExitAt hψ h2 ring C e ∧
      NoRelabelExitAlong hψ h2 ring
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) rest


/-- Along a leaderless word, a Closed-or-Exit hypothesis plus current passive
admission actually gives no exit at every prefix, because the exit case is
locally incompatible with admission. -/
theorem noRelabelExitAlong_of_closedOrExit_alive
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hX : ConcreteB7PassiveClosedOrExitObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : Config n ψ κ τ) (u : List (Fin n))
    (hA : ConcreteB7AdmittedPassive hψ h2 ring C)
    (hAlive : AliveAlong
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      FinalLeaderless C u) :
    NoRelabelExitAlong hψ h2 ring C u := by
  have hClosed :
      ConcreteB7AdmittedPassiveClosedObligation
        (κ := κ) (τ := τ) hψ h2 ring :=
    concreteB7PassiveClosed_of_closedOrExit hψ h2 ring hX
  induction u generalizing C with
  | nil =>
      exact True.intro
  | cons e rest ih =>
      have hAliveCons :
          FinalLeaderless C ∧
            AliveAlong
              (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
              FinalLeaderless
              (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)
              rest := hAlive
      change
        ¬ RelabelExitAt hψ h2 ring C e ∧
          NoRelabelExitAlong hψ h2 ring
            (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) rest
      refine ⟨relabelExitAt_false_of_passive_admitted
        hψ h2 ring C e hA, ?_⟩
      have hLnext :
          FinalLeaderless
            (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) :=
        aliveAlong_good hAliveCons.2
      have hnext := hClosed C e hA hAliveCons.1
      have hA' :
          ConcreteB7AdmittedPassive hψ h2 ring
            (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) := by
        rcases hnext with hLead | hAdm
        · rcases hLead with ⟨i, hi⟩
          have hf := hLnext i
          rw [hf] at hi
          cases hi
        · exact hAdm
      exact ih
        (C := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)
        hA' hAliveCons.2

private theorem b4_noEqualAlong_append_left_exit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (C : BirthPhaseWait2Transfer.FC n ψ κ τ)
    (u v : List (Fin n))
    (hNo : B2NoEqualAlong hψ h2 ring C (u ++ v)) :
    B2NoEqualAlong hψ h2 ring C u := by
  induction u generalizing C with
  | nil =>
      exact True.intro
  | cons e u ih =>
      change BirthCheckPermitRepairAgree.NoEqualAlong
        hψ h2 ring C (e :: (u ++ v)) at hNo
      change BirthCheckPermitRepairAgree.NoEqualAlong
        hψ h2 ring C (e :: u)
      refine ⟨hNo.1, ?_⟩
      exact ih
        (C := BirthPhaseWait2BlockProgress.currentStep2
          hψ h2 ring C e) hNo.2


/-- Up-to-first-exit form of the existing B4 word theorem.


For every literal prefix `pre` of `u`, the prefix is certified exit-free and
the already-proved `concreteB4CapOrEndpointProgress_of_passive_word` applies
to that prefix.  Under the current admission definition this is stronger than
"before the first exit": no such relabel exit can occur while the induction
remains passive-admitted and leaderless. -/
theorem concreteB4CapOrEndpointProgress_up_to_first_exit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (anchor : Fin n) (hn : 2 ≤ n)
    (hClosedExit : ConcreteB7PassiveClosedOrExitObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : Config n ψ κ τ) (u : List (Fin n))
    (hA : ConcreteB7AdmittedPassive hψ h2 ring C)
    (hAlive : AliveAlong
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      FinalLeaderless C u)
    (hNo : B2NoEqualAlong hψ h2 ring (finalBase C) u)
    (pre post : List (Fin n))
    (hu : u = pre ++ post)
    (hOldPre : BirthPhaseWait2BlockProgress.CapOrEndpointProgress
      hψ h2 κ ring anchor (finalBase C) pre) :
    NoRelabelExitAlong hψ h2 ring C pre ∧
      ConcreteB4CapOrEndpointProgress hψ h2 ring anchor C pre := by
  have hClosed :
      ConcreteB7AdmittedPassiveClosedObligation
        (κ := κ) (τ := τ) hψ h2 ring :=
    concreteB7PassiveClosed_of_closedOrExit
      hψ h2 ring hClosedExit
  rw [hu] at hAlive hNo
  have hAlivePre :
      AliveAlong
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
        FinalLeaderless C pre :=
    ((aliveAlong_append
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      FinalLeaderless C pre post).1 hAlive).1
  have hNoPre :
      B2NoEqualAlong hψ h2 ring (finalBase C) pre :=
    b4_noEqualAlong_append_left_exit
      hψ h2 ring (finalBase C) pre post hNo
  constructor
  · exact noRelabelExitAlong_of_closedOrExit_alive
      hψ h2 ring hClosedExit C pre hA hAlivePre
  · exact concreteB4CapOrEndpointProgress_of_passive_word
      hψ h2 ring anchor hn hClosed hR2
      C pre hA hAlivePre hNoPre hOldPre








end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C

import Leader.Wu.Entrance.ConcretePort
import Leader.Wu.Entrance.Admission
import Leader.Wu.Birth.WidthTwoWaitTransfer

set_option autoImplicit false
set_option Elab.async false

/-!
# B2 transfer to the concrete final step

`BirthPhaseWait2Transfer.local_wait2_transfer_until_stop` is not a theorem
about `BirthCheckPermitRepairLeaf.step1`.  Its recursive `hostStep` is
`BirthShortDoneTerminalPassiveR4.hostStep`, i.e. the width-two
`BirthShortDoneTerminalHost.row` inserted by `localStep`.  The repository's
`BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2` identifies that step
with `BirthShortDoneTerminalConsumer.step` (`currentStep2`).

The checked R1/consumer agreement is
`BirthCheckPermitRepairAgree.step1_eq`, whose exact row premise is
`NoEqualOutcome`: after `doneThroughCheckEntryWidth`, the initiator CHECK state
is not `.equal`.  This is the precise repair point.  On an equal outcome R1's
`BirthCheckPermitRepair.permitFix` clears the crossing permit before
`afterCheckMetadataWidth`, while the terminal consumer does not.  Therefore
this file exposes the missing pre-cap-word no-equal fact as the named
`B2PreCapR1ConsumerAgreementObligation` instead of assuming global R1/consumer
identity.
-/

namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthLeaderlessBirthMassRenewal

variable {n ψ κ τ : Nat}

/-- The concrete admission class is exactly the generic admission class
at the frozen port; the only differently named conjunct is writer-clear. -/
private theorem concreteB7Admitted_to_finalB7Admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : Config n ψ κ τ)
    (hA : ConcreteB7Admitted hψ h2 ring C) :
    FinalB7Admitted hψ h2
      (concretePort (κ := κ) (τ := τ) hψ h2) ring C := by
  simpa [ConcreteB7Admitted, FinalB7Admitted,
    ConcreteWriterClear, FinalWriterClear] using hA

/-- `AliveAlong` always includes its current starting state, including for the
empty suffix. -/
private theorem aliveAlong_start
    {S : Type} {m : Nat}
    {step : S → Fin m → S} {Good : S → Prop}
    {x : S} {es : List (Fin m)}
    (h : AliveAlong step Good x es) : Good x := by
  cases es with
  | nil =>
      exact h
  | cons e rest =>
      exact h.1

attribute [local irreducible] stepFinal concretePort

theorem runConcrete_base_eq_runStep1_of_admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hClosed : ConcreteB7AdmissionClosedObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : Config n ψ κ τ) (es : List (Fin n))
    (hA : ConcreteB7Admitted hψ h2 ring C)
    (hAlive : AliveAlong
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      FinalLeaderless C es) :
    finalBase
        (es.foldl
          (stepConcrete (κ := κ) (τ := τ) hψ h2 ring) C) =
      es.foldl (BirthCheckPermitRepairLeaf.step1 hψ h2 ring)
        (finalBase C) := by
  induction es generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      have hAliveCons :
          FinalLeaderless C ∧
            AliveAlong
              (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
              FinalLeaderless
              (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)
              rest := hAlive
      have hL : FinalLeaderless C := hAliveCons.1
      have hAFinal :
          FinalB7Admitted hψ h2
            (concretePort (κ := κ) (τ := τ) hψ h2) ring C :=
        concreteB7Admitted_to_finalB7Admitted hψ h2 ring C hA
      generalize hD :
        stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e = D
        at hAliveCons
      have hAliveRest :
          AliveAlong
            (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
            FinalLeaderless D rest :=
        hAliveCons.2
      have hLnext : FinalLeaderless D :=
        aliveAlong_start hAliveRest
      have hstepD :
          finalBase D =
            BirthCheckPermitRepairLeaf.step1 hψ h2 ring
              (finalBase C) e := by
        rw [← hD]
        change
          finalBase
              (stepFinal hψ h2
                (concretePort (κ := κ) (τ := τ) hψ h2)
                ring C e) =
            BirthCheckPermitRepairLeaf.step1 hψ h2 ring
              (finalBase C) e
        exact stepFinal_base_eq_step1_of_admitted
          hψ h2 (concretePort (κ := κ) (τ := τ) hψ h2)
          ring hn hR2 C e hAFinal hL
      have hnext0 := hClosed C e hA hL
      have hnext :
          HasLeader D ∨ ConcreteB7Admitted hψ h2 ring D := by
        rw [hD] at hnext0
        exact hnext0
      have hA' : ConcreteB7Admitted hψ h2 ring D := by
        rcases hnext with hLead | hAdm
        · rcases hLead with ⟨i, hi⟩
          have hf := hLnext i
          rw [hf] at hi
          cases hi
        · exact hAdm
      have htail := ih (C := D) hA' hAliveRest
      rw [List.foldl_cons, List.foldl_cons, hD]
      calc
        finalBase
            (rest.foldl
              (stepConcrete (κ := κ) (τ := τ) hψ h2 ring) D) =
          rest.foldl (BirthCheckPermitRepairLeaf.step1 hψ h2 ring)
            (finalBase D) := htail
        _ = rest.foldl (BirthCheckPermitRepairLeaf.step1 hψ h2 ring)
            (BirthCheckPermitRepairLeaf.step1 hψ h2 ring
              (finalBase C) e) := by
          rw [hstepD]


def B2NoEqualAlong
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : BirthPhaseWait2Transfer.FC n ψ κ τ)
    (es : List (Fin n)) : Prop :=
  BirthCheckPermitRepairAgree.NoEqualAlong hψ h2 ring C es


/-- Remaining B2-specific R1/consumer adapter leaf.

For every B2 Local3 start and every literal word accepted by
`LocalWait2RunSource`, no executed row may hit the one CHECK outcome where R1
and the terminal consumer can differ: initiator state `.equal` immediately
after `doneThroughCheckEntryWidth`. -/
def B2PreCapR1ConsumerAgreementObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (hn : 4 ≤ n)
    (κ τ : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  ∀ (C : BirthPhaseWait2Transfer.FC n ψ κ τ)
      (es : List (Fin n)),
    BirthPhaseWait2Transfer.LocalWait2Carrier
        hψ h2 hn ring anchor C →
    BirthPhaseWait2Transfer.LocalWait2RunSource
        hψ h2 hn κ τ ring anchor C es →
    B2NoEqualAlong hψ h2 ring C es

/-- One B2 letter: the old B2 host is the terminal consumer, not `step1`.
The checked `NoEqualOutcome` bridge is exactly what identifies it with R1. -/
theorem b2_step1_eq_hostStep_of_noEqual
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (C : BirthPhaseWait2Transfer.FC n ψ κ τ) (e : Fin n)
    (hNo : BirthCheckPermitRepairAgree.NoEqualOutcome hψ h2
      (C e) (C (ring.rightNeighbor e))) :
    BirthCheckPermitRepairLeaf.step1 hψ h2 ring C e =
      BirthPhaseWait2Transfer.hostStep hψ h2 ring C e := by
  calc
    BirthCheckPermitRepairLeaf.step1 hψ h2 ring C e =
        BirthPhaseWait2BlockProgress.currentStep2 hψ h2 ring C e :=
      BirthCheckPermitRepairAgree.step1_eq hψ h2 ring C e hNo
    _ = BirthPhaseWait2Transfer.hostStep hψ h2 ring C e :=
      (BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
        hψ h2 ring C e).symm

theorem runStep1_eq_runB2Host_of_noEqual
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (C : BirthPhaseWait2Transfer.FC n ψ κ τ)
    (es : List (Fin n))
    (hNo : B2NoEqualAlong hψ h2 ring C es) :
    es.foldl (BirthCheckPermitRepairLeaf.step1 hψ h2 ring) C =
      es.foldl (BirthPhaseWait2Transfer.hostStep hψ h2 ring) C := by
  have hRunConsumer :
      es.foldl (BirthCheckPermitRepairLeaf.step1 hψ h2 ring) C =
        es.foldl (BirthPhaseWait2BlockProgress.currentStep2 hψ h2 ring) C :=
    BirthCheckPermitRepairAgree.run_eq hψ h2 ring es C hNo
  calc
    es.foldl (BirthCheckPermitRepairLeaf.step1 hψ h2 ring) C =
        es.foldl (BirthPhaseWait2BlockProgress.currentStep2 hψ h2 ring) C :=
      hRunConsumer
    _ = es.foldl (BirthPhaseWait2Transfer.hostStep hψ h2 ring) C := by
      clear hRunConsumer hNo
      induction es generalizing C with
      | nil =>
          rfl
      | cons e rest ih =>
          rw [List.foldl_cons, List.foldl_cons]
          rw [← BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
            hψ h2 ring C e]
          exact ih
            (C := BirthPhaseWait2Transfer.hostStep hψ h2 ring C e)



/-- B2 on the frozen concrete final step, with every still-open hypothesis
named.

The scheduler word `es` is literally unchanged.  `hLeaderlessAlong` plus
`hAdmissionClosed` keeps the concrete run inside the admission class, `hR2R1`
projects that run letter-for-letter to R1, and `hB2R1` identifies R1 with B2's
terminal-consumer host on the pre-stop word.  The original B2 theorem then
supplies both the restarted Local3 carrier and its WAIT2 projection record. -/
theorem b2_wait2_transfer_concrete
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (hn4 : 4 ≤ n)
    (κ τ : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hAdmissionClosed : ConcreteB7AdmissionClosedObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR2R1 : R2Coherence.R2R1AgreementObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hB2R1 : B2PreCapR1ConsumerAgreementObligation
      hψ h2 hn4 κ τ ring anchor)
    (C : Config n ψ κ τ) (es : List (Fin n))
    (hAdmitted : ConcreteB7Admitted hψ h2 ring C)
    (hLeaderlessAlong : AliveAlong
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      FinalLeaderless C es)
    (hCarrier : BirthPhaseWait2Transfer.LocalWait2Carrier
      hψ h2 hn4 ring anchor (finalBase C))
    (hPreCapWord : BirthPhaseWait2Transfer.LocalWait2RunSource
      hψ h2 hn4 κ τ ring anchor (finalBase C) es) :
    BirthPhaseWait2Transfer.LocalWait2Carrier
        hψ h2 hn4 ring anchor
        (finalBase
          (es.foldl
            (stepConcrete (κ := κ) (τ := τ) hψ h2 ring) C)) ∧
      BirthPhaseWait2Transfer.LocalProjectionAlong2At
        hψ h2 hn4 κ τ ring anchor (finalBase C) es := by
  have hn2 : 2 ≤ n :=
    Nat.le_trans (by decide : 2 ≤ 4) hn4
  have hNoEq : B2NoEqualAlong hψ h2 ring (finalBase C) es :=
    hB2R1 (finalBase C) es hCarrier hPreCapWord
  have hConcreteR1 :=
    runConcrete_base_eq_runStep1_of_admitted
      hψ h2 ring hn2 hAdmissionClosed hR2R1
      C es hAdmitted hLeaderlessAlong
  have hR1Host :=
    runStep1_eq_runB2Host_of_noEqual
      hψ h2 ring (finalBase C) es hNoEq
  have hB2 :=
    BirthPhaseWait2Transfer.local_wait2_transfer_until_stop
      hψ h2 hn4 κ τ ring anchor
      (finalBase C) hCarrier es hPreCapWord
  constructor
  · rw [hConcreteR1, hR1Host]
    exact hB2.1
  · exact hB2.2

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C

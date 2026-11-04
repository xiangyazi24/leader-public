import Leader.Wu.Entrance.PassiveProjection

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
open BirthLeaderlessBirthMassRenewal

variable {n ψ κ τ : Nat}

/-- Exact passive analogue of `ConcreteB7AdmissionClosedObligation`.

As in the old interface, a leader may be the stopping event.  Hence closure is
stated as `HasLeader next ∨ admitted next`; on an `AliveAlong FinalLeaderless`
word the first disjunct is impossible, so the word induction really does stay
inside `ConcreteB7AdmittedPassive`. -/
def ConcreteB7AdmittedPassiveClosedObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    HasLeader
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) ∨
      ConcreteB7AdmittedPassive hψ h2 ring
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)

/-- `NoEqualAlong` is prefix closed.  This is the no-equal counterpart of
`aliveAlong_append`; it is kept local because the recursive state here is the
terminal consumer state. -/
private theorem b4_noEqualAlong_append_left
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

/-- Passive-admitted same-word projection all the way to the literal terminal
consumer.  This is the one-letter theorem iterated under the passive
closure interface; `AliveAlong` supplies leaderlessness at every current
state, and `B2NoEqualAlong` supplies the checked R1/consumer bridge at every
letter. -/
theorem runConcrete_base_eq_runConsumer_of_passive_admitted_noEqual
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : Config n ψ κ τ) (u : List (Fin n))
    (hA : ConcreteB7AdmittedPassive hψ h2 ring C)
    (hAlive : AliveAlong
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      FinalLeaderless C u)
    (hNo : B2NoEqualAlong hψ h2 ring (finalBase C) u) :
    finalBase
        (u.foldl
          (stepConcrete (κ := κ) (τ := τ) hψ h2 ring) C) =
      u.foldl (BirthPhaseWait2BlockProgress.currentStep2 hψ h2 ring)
        (finalBase C) := by
  induction u generalizing C with
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
      have hNoCons :
          BirthCheckPermitRepairAgree.NoEqualOutcome hψ h2
              ((finalBase C) e)
              ((finalBase C) (ring.rightNeighbor e)) ∧
            BirthCheckPermitRepairAgree.NoEqualAlong hψ h2 ring
              (BirthPhaseWait2BlockProgress.currentStep2
                hψ h2 ring (finalBase C) e) rest :=
        (BirthCheckPermitRepairAgree.noEqualAlong_cons
          hψ h2 ring (finalBase C) e rest).1 hNo
      have hstep :=
        stepConcrete_base_eq_currentStep2_of_passive_admitted
          hψ h2 ring hn hR2 C e hA hAliveCons.1 hNoCons.1
      have hAliveRest := hAliveCons.2
      have hLnext :
          FinalLeaderless
            (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) :=
        aliveAlong_good hAliveRest
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
      have hNoRest :
          B2NoEqualAlong hψ h2 ring
            (finalBase
              (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e))
            rest := by
        unfold B2NoEqualAlong
        rw [hstep]
        exact hNoCons.2
      have htail := ih
        (C := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)
        hA' hAliveRest hNoRest
      rw [List.foldl_cons, List.foldl_cons]
      calc
        finalBase
            (rest.foldl
              (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
              (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)) =
          rest.foldl
            (BirthPhaseWait2BlockProgress.currentStep2 hψ h2 ring)
            (finalBase
              (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)) :=
          htail
        _ = rest.foldl
            (BirthPhaseWait2BlockProgress.currentStep2 hψ h2 ring)
            (BirthPhaseWait2BlockProgress.currentStep2
              hψ h2 ring (finalBase C) e) := by
          rw [hstep]

/-- Every literal prefix has the same concrete-base/consumer endpoint identity.
The full-word `AliveAlong` and `B2NoEqualAlong` assumptions restrict to `pre`,
then the preceding word theorem is applied to that prefix. -/
theorem runConcrete_base_eq_runConsumer_prefix_of_passive_admitted_noEqual
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
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
    (hu : u = pre ++ post) :
    finalBase
        (pre.foldl
          (stepConcrete (κ := κ) (τ := τ) hψ h2 ring) C) =
      pre.foldl
        (BirthPhaseWait2BlockProgress.currentStep2 hψ h2 ring)
        (finalBase C) := by
  rw [hu] at hAlive hNo
  have hAlivePre :
      AliveAlong
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
        FinalLeaderless C pre :=
    ((aliveAlong_append
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      FinalLeaderless C pre post).1 hAlive).1
  have hNoPre : B2NoEqualAlong hψ h2 ring (finalBase C) pre :=
    b4_noEqualAlong_append_left
      hψ h2 ring (finalBase C) pre post hNo
  exact runConcrete_base_eq_runConsumer_of_passive_admitted_noEqual
    hψ h2 ring hn hClosed hR2 C pre hA hAlivePre hNoPre

/-- Pointwise B4 pullback on the literal scheduler word.

If the old terminal-consumer target fires, then the same concrete word realizes
`ConcreteB4CapOrEndpointProgress`.  In the first-cap branch, the prefix
identity at `pre` transports `RowCap2`, while the identity at `pre ++ [e]`
supplies the equality component of `ConcreteB4CapFireAt`.  In the endpoint
branch, the whole-word identity transports the final `shortCountAt`. -/
theorem concreteB4CapOrEndpointProgress_of_passive_word
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (anchor : Fin n) (hn : 2 ≤ n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : Config n ψ κ τ) (u : List (Fin n))
    (hA : ConcreteB7AdmittedPassive hψ h2 ring C)
    (hAlive : AliveAlong
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
      FinalLeaderless C u)
    (hNo : B2NoEqualAlong hψ h2 ring (finalBase C) u)
    (hOld : BirthPhaseWait2BlockProgress.CapOrEndpointProgress
      hψ h2 κ ring anchor (finalBase C) u) :
    ConcreteB4CapOrEndpointProgress hψ h2 ring anchor C u := by
  rcases hOld with hCap | hEnd
  · left
    rcases hCap with ⟨pre, e, post, hu, hRow⟩
    have hPre :=
      runConcrete_base_eq_runConsumer_prefix_of_passive_admitted_noEqual
        hψ h2 ring hn hClosed hR2 C u hA hAlive hNo
        pre (e :: post) hu
    have hue : u = (pre ++ [e]) ++ post := by
      rw [hu]
      simp [List.append_assoc]
    have hPreE :=
      runConcrete_base_eq_runConsumer_prefix_of_passive_admitted_noEqual
        hψ h2 ring hn hClosed hR2 C u hA hAlive hNo
        (pre ++ [e]) post hue
    refine ⟨pre, e, post, hu, ?_⟩
    unfold ConcreteB4CapFireAt
    constructor
    · rw [hPre]
      exact hRow
    · rw [hPre]
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hPreE
  · right
    have hRun :=
      runConcrete_base_eq_runConsumer_of_passive_admitted_noEqual
        hψ h2 ring hn hClosed hR2 C u hA hAlive hNo
    rw [hRun]
    exact hEnd

/-- Mass-side statement surface only.

Every word actually counted by the old `capOrEndpointProgressNumerator` is
required to lie on the concrete leaderless/no-equal lane.  Together with the
single global passive-closure obligation, the pointwise theorem above is then
exactly the injection-free Boolean domination needed for the numerator
inequality.  This file deliberately states that consequence as a `Prop`; it
does not re-prove `wordSum` monotonicity here. -/
def ConcreteB4PassiveProgressNumeratorTransferObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (anchor : Fin n) (hn : 2 ≤ n) : Prop :=
  ∀ C : Config n ψ κ τ,
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    ConcreteB7AdmittedPassiveClosedObligation
      (κ := κ) (τ := τ) hψ h2 ring →
    (∀ u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n →
      BirthPhaseWait2BlockProgress.CapOrEndpointProgress
        hψ h2 κ ring anchor (finalBase C) u →
      AliveAlong
          (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
          FinalLeaderless C u ∧
        B2NoEqualAlong hψ h2 ring (finalBase C) u) →
    BirthPhaseWait2BlockProgress.capOrEndpointProgressNumerator
        hψ h2 κ ring anchor (finalBase C) ≤
      concreteB4ProgressNumerator hψ h2 ring anchor C

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C



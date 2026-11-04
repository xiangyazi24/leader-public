import Leader.Wu.Entrance.PassiveClosure

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
open WriterProducerRepair

variable {n ψ κ τ : Nat}

/-- The clean part: an open/no-write R2C service leaves every
quarantine controller open and token-free.  This is about the inner R2C
controller only; it does not claim anything about the outer B9 splice control. -/
theorem r2cAllOpen_step_of_open_no_write
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (C : R2Coherence.FC n ψ κ τ) (e : Fin n)
    (hOpen : R2Coherence.AllOpen C)
    (hNo : R2Coherence.NoHazardAt hψ h2 ring C e) :
    R2Coherence.AllOpen (R2Coherence.step hψ h2 ring C e) := by
  have hL := hOpen e
  have hR := hOpen (ring.rightNeighbor e)
  rcases hL with ⟨hLM, hLN⟩
  rcases hR with ⟨hRM, hRN⟩
  have hc := R2Coherence.row_control_eq_of_open_no_write
    hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
    hLM hRM hLN hRN hNo
  have hqL :
      (R2Coherence.row hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).1.ctl = (C e).ctl := hc.1
  have hqR :
      (R2Coherence.row hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).2.ctl =
        (C (ring.rightNeighbor e)).ctl := hc.2
  intro p
  by_cases hpe : p = e
  · subst p
    have hq : R2Coherence.OpenControl
        (R2Coherence.row hψ (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e))).1 := by
      unfold R2Coherence.OpenControl
      rw [hqL]
      exact ⟨hLM, hLN⟩
    simpa [R2Coherence.step, R2Coherence.protocol,
      PopulationProtocol.step] using hq
  · by_cases hpj : p = ring.rightNeighbor e
    · subst p
      have hq : R2Coherence.OpenControl
          (R2Coherence.row hψ (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e))).2 := by
        unfold R2Coherence.OpenControl
        rw [hqR]
        exact ⟨hRM, hRN⟩
      simpa [R2Coherence.step, R2Coherence.protocol,
        PopulationProtocol.step, hpe] using hq
    · simpa [R2Coherence.step, R2Coherence.protocol,
        PopulationProtocol.step, hpe, hpj] using hOpen p

/-- Passive writer boundary implies absence of a live R2 writer producer.
This makes the no-producer conjunct logically redundant once writer-passive
post-preservation is available. -/
theorem finalNoProducer_of_finalWriterPassive
    (C : Config n ψ κ τ) (hP : FinalWriterPassive C) :
    FinalNoProducer C := by
  intro i
  have hi := hP i
  dsimp only at hi
  rcases hi.2.2 with hs | hs
  · simp [WriterProducerRepair.producerActive, hs]
  · simp [WriterProducerRepair.producerActive, hs]

/-- Exact writer-passive postcondition still needed for the concrete HOST step. -/
def ConcreteB7PassiveWriterPostObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e
    FinalLeaderless D → FinalWriterPassive D

/-- The no-producer half, stated independently. -/
def ConcreteB7PassiveNoProducerPostObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e
    FinalLeaderless D → FinalNoProducer D

theorem concreteB7PassiveNoProducerPost_of_writerPost
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hW : ConcreteB7PassiveWriterPostObligation
      (κ := κ) (τ := τ) hψ h2 ring) :
    ConcreteB7PassiveNoProducerPostObligation
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hA hL
  dsimp only
  intro hDL
  exact finalNoProducer_of_finalWriterPassive
    (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)
    (hW C e hA hL hDL)

/-- Exact final all-open postcondition.  The underlying R2C row-control frame
is proved above; lifting it through `stepConcrete` only needs the already-used
physical HOST projection from B4PassiveProjection, whose helper is currently
private there. -/
def ConcreteB7PassiveAllOpenPostObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalAllOpen
      (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)

/-- Genuine residual: every successor edge must again have an
R2 proposal which changes neither resident bit nor resident label.  This is a
second-step/adjacent-edge frame; `R2Coherence.R2R1AgreementObligation` does not
supply it. -/
def ConcreteB7PassiveProposalNoWritePostObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e
    FinalLeaderless D →
      ∀ a : Fin n,
        R2Coherence.ProposalNoWrite hψ (by decide : 0 < 2) h2
          (D a).phys (D (ring.rightNeighbor a)).phys

/-- The requested controller postcondition remains exactly this residual on
current main.  `row_control_eq_of_open_no_write` proves only the inner R2C
`ctl`; the outer B9 HOST/no-garbage closure still needs the all-HOST-neutral
priority-table lemma. -/
abbrev ConcreteB7PassiveControllerPostResidual
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ConcreteB7PassiveControllerPostObligation
    (κ := κ) (τ := τ) hψ h2 ring

theorem concreteB7PassivePhysicalPost_of_writer_open_noWrite
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hW : ConcreteB7PassiveWriterPostObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hO : ConcreteB7PassiveAllOpenPostObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hN : ConcreteB7PassiveProposalNoWritePostObligation
      (κ := κ) (τ := τ) hψ h2 ring) :
    ConcreteB7PassivePhysicalPostObligation
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hA hL
  dsimp only
  intro hDL
  have hWriter :
      FinalWriterPassive
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) :=
    hW C e hA hL hDL
  exact
    ⟨finalNoProducer_of_finalWriterPassive
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) hWriter,
      hWriter,
      hO C e hA,
      hN C e hA hL hDL⟩

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C



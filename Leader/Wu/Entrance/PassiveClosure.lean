import Leader.Wu.Entrance.PassiveWord


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


instance r1WriterPassiveCellDec (u : PPLLExpiringComparisonRepair.ExpiringAgentState ψ κ τ) :
    Decidable (R1WriterPassiveCell u) := by
  unfold R1WriterPassiveCell
  infer_instance

/-- The writer-clear counterexample is *inside* the repaired passive
boundary after the row.  In particular, the responder's `.depart` is now an
allowed terminal writer state rather than a closure violation. -/
theorem quiet_pair_writerClear_failure_is_passive :
    QuietPairCounterexample.out.2.core.core.write_state = .depart ∧
      R1WriterPassiveCell QuietPairCounterexample.out.1 ∧
      R1WriterPassiveCell QuietPairCounterexample.out.2 := by
  refine ⟨QuietPairCounterexample.quiet_pair_output_right_depart, ?_⟩
  decide +kernel


/-- Exact physical post-step contract still needed for unconditional passive
closure on current main.  This separates the R2/R1/writer side from the outer
B9 controller side.


`FinalAllOpen` is source-derivable from the open/no-write R2C row-control
frame, but is kept in this bundle so the eventual capstone has one complete
physical contract. -/
def ConcreteB7PassivePhysicalPostObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e
    FinalLeaderless D →
      FinalNoProducer D ∧
      FinalWriterPassive D ∧
      FinalAllOpen D ∧
      (∀ a : Fin n,
        R2Coherence.ProposalNoWrite hψ (by decide : 0 < 2) h2
          (D a).phys (D (ring.rightNeighbor a)).phys)


/-- Exact outer-controller successor contract still needed for the intended
`fullRowPort`: no recovery garbage reappears and every successor edge remains
on the HOST lane. -/
def ConcreteB7PassiveControllerPostObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e
    FinalLeaderless D →
      ∀ a : Fin n,
        ¬ FinalGarbage hψ (D a) (D (ring.rightNeighbor a)) ∧
        (concretePortLocal (κ := κ) (τ := τ) hψ h2).action
          (D a) (D (ring.rightNeighbor a)) = .host


/-- Once the two actual post-step contracts above are proved, the
closure Prop assembles immediately.  This theorem is intentionally
conditional: current main does not yet inhabit either contract in full. -/
theorem concreteB7AdmittedPassiveClosed_of_post_obligations
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hPhys : ConcreteB7PassivePhysicalPostObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hCtl : ConcreteB7PassiveControllerPostObligation
      (κ := κ) (τ := τ) hψ h2 ring) :
    ConcreteB7AdmittedPassiveClosedObligation
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hA hL
  let D := stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e
  by_cases hLead : HasLeader D
  · exact Or.inl hLead
  · right
    have hDL : FinalLeaderless D :=
      (finalLeaderless_iff_not_hasLeader D).2 hLead
    have hp := hPhys C e hA hL hDL
    have hc := hCtl C e hA hL hDL
    rcases hp with ⟨hProd, hPassive, hOpen, hNoWrite⟩
    refine ⟨hProd, hPassive, hOpen, ?_⟩
    intro a
    have ha := hc a
    exact ⟨ha.1, ha.2, hNoWrite a⟩


end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C



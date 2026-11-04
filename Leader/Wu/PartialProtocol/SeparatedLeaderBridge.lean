import Leader.Wu.PartialProtocol.SeparatedLeaderObstruction
import Leader.Wu.PartialProtocol.OutputKernelNoGo

/-!
# Exact `P_partial` bridge to arbitrary-singleton stability

`ArbitrarySingletonOutputStable4` protects every complete four-agent carrier
assignment whose current output has one leader.  The perpetual-uniqueness
interface has no pointwise output-equality field, so it cannot be used as this
bridge merely by projecting one of its stated conclusions.

The irredundant local premise is the existing `StepOutputPreservingOn` applied
to current unique leadership.  Its output equality itself makes uniqueness
closed, so no separate closure assumption is needed.  The old
`PPartialLocalLegitimacyUnconditional` premise implies this frame and therefore
also implies the generic property.  These are conditional bridges only.  The
concrete T1 configuration proves that the frame, the generic property, and the
old local premise are all false for the current protocol at `psi = 2`,
`kappa = 10`, and `tau = 0` on the four-agent audit ring.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSeparatedLeaderBridgeSol

open PPLL PPLLResearchFormulation
open PPartialSeparatedLeaderRepairSol
open PPartialOutputKernelNoGoSol
open PPLLCounterexample

set_option autoImplicit false

variable {psi : Nat}

/-- The one-step pointwise output frame on *all* current unique-leader carrier
assignments already implies arbitrary-singleton stability.  A separate
closedness premise is unnecessary: unchanged outputs preserve the same unique
leader position. -/
theorem PPartialLegitStepOutputPreserving_to_arbitrarySingletonOutputStable4
    (hpsi : psi > 0) (kappa tau : Nat)
    (hFrame : StepOutputPreservingOn
      (P_partialProtocolUnconditional hpsi kappa tau)
      separatedAuditRing
      (PPartialLegitUnconditional hpsi kappa tau)) :
    ArbitrarySingletonOutputStable4
      (P_partialProtocolUnconditional hpsi kappa tau)
      isLeaderOutput := by
  have hClosed : PopulationProtocol.ClosedPred
      (P_partialProtocolUnconditional hpsi kappa tau)
      separatedAuditRing
      (PPartialLegitUnconditional hpsi kappa tau) := by
    intro C hC C' hStep
    change UniqueLeaderOutput
      (P_partialProtocolUnconditional hpsi kappa tau)
      4 C isLeaderOutput at hC
    change UniqueLeaderOutput
      (P_partialProtocolUnconditional hpsi kappa tau)
      4 C' isLeaderOutput
    obtain ⟨leader, hLeader, hOnly⟩ := hC
    have hOutput := hFrame C ⟨leader, hLeader, hOnly⟩ C' hStep
    refine ⟨leader, ?_, ?_⟩
    · rw [hOutput leader]
      exact hLeader
    · intro i hi
      rw [hOutput i] at hi
      exact hOnly i hi
  intro C hUnique
  change PPartialLegitUnconditional hpsi kappa tau C at hUnique
  exact (isSafe_of_operational_legitimacy
    (P_partialProtocolUnconditional hpsi kappa tau)
    separatedAuditRing isLeaderOutput
    (PPartialLegitUnconditional hpsi kappa tau)
    hClosed (fun _ h => h) hFrame hUnique).2

/-- The exact existing local closure-plus-output-frame premise therefore
implies the generic arbitrary-complete-carrier singleton-stability hypothesis. -/
theorem PPartialLocalLegitimacyUnconditional_to_arbitrarySingletonOutputStable4
    (hpsi : psi > 0) (kappa tau : Nat)
    (hLocal : PPartialLocalLegitimacyUnconditional
      hpsi kappa tau separatedAuditRing) :
    ArbitrarySingletonOutputStable4
      (P_partialProtocolUnconditional hpsi kappa tau)
      isLeaderOutput := by
  apply PPartialLegitStepOutputPreserving_to_arbitrarySingletonOutputStable4
  change StepOutputPreservingOn
    (P_partialProtocol hpsi kappa tau
      (PPartialAuthorizedDomainClosure_q5776 hpsi kappa))
    separatedAuditRing
    (PPartialLegit hpsi kappa tau
      (PPartialAuthorizedDomainClosure_q5776 hpsi kappa))
  exact PPartialLegit_stepOutputPreserving
    hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa)
    separatedAuditRing hLocal

private theorem ring4_eq_separatedAuditRing :
    ring4 = separatedAuditRing := by
  cases ring4
  rfl

/-- T1 shows that current unique leadership does not imply the generic
arbitrary-singleton property for the exact current `P_partial` transition. -/
theorem P_partial_t1_not_arbitrarySingletonOutputStable4 :
    ∀ hpsi : (2 : Nat) > 0,
    ¬ ArbitrarySingletonOutputStable4
      (P_partialProtocolUnconditional hpsi 10 0)
      isLeaderOutput := by
  intro hpsi hStable
  have hUnique : UniqueLeaderOutput
      (P_partialProtocolUnconditional hpsi 10 0)
      4 t1FiniteConfig isLeaderOutput := by
    exact PPartialOutputLegit.toLegit
      hpsi 10 0 ring4 t1FiniteConfig t1FiniteConfig_outputLegit
  have hOutputStable := hStable t1FiniteConfig hUnique
  rw [← ring4_eq_separatedAuditRing] at hOutputStable
  exact t1FiniteConfig_not_outputStable hOutputStable

/-- Consequently the exact old local premise is already false on T1's
four-agent instance; the bridge does not discharge that premise. -/
theorem PPartialLocalLegitimacyUnconditional_false_t1_four :
    ∀ hpsi : (2 : Nat) > 0,
    ¬ PPartialLocalLegitimacyUnconditional
      hpsi 10 0 separatedAuditRing := by
  intro hpsi hLocal
  exact P_partial_t1_not_arbitrarySingletonOutputStable4
    hpsi
    (PPartialLocalLegitimacyUnconditional_to_arbitrarySingletonOutputStable4
      hpsi 10 0 hLocal)

end PPartialSeparatedLeaderBridgeSol
end PPLLCompleteMultiLeaderCleanup

import Leader.Wu.Scheduler.ClosedDomainAmplification


namespace PPLLClosedDomainSchedulerAmplificationSol


open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks


set_option autoImplicit false


/-- Remove the explicit `True` premise from the domain-restricted bound. -/
theorem uniformOneOverNFailureAtHorizon_of_trueDomain
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (c t : Nat)
    (hOn : UniformOneOverNFailureAtHorizonOn
      P ring isLeader (fun _ : P.Configuration n => True) c t) :
    UniformOneOverNFailureAtHorizon P ring isLeader c t := by
  refine ⟨hOn.1, hOn.2.1, ?_⟩
  intro C
  exact hOn.2.2 C trivial


#print axioms uniformOneOverNFailureAtHorizon_of_trueDomain


/-- Unrestricted explicit finite `1/n` failure bound from a bounded
safe-schedule producer on every configuration. -/
theorem boundedIsSafeProducer_explicitOneOverNSSLE
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (safeTest : P.Configuration n → Bool)
    (hdec : ∀ C, safeTest C = true ↔
      PopulationProtocol.IsSafe P ring C isLeader)
    (hn2 : 1 < n) (L : Nat) (hL : 0 < L)
    (hproducer : ∀ C : P.Configuration n,
      ¬ PopulationProtocol.IsSafe P ring C isLeader →
        ∃ word : DetSchedule n,
          word.length ≤ L ∧
            PopulationProtocol.IsSafe P ring
              (runLocalSchedule ring P.transition C word) isLeader) :
    let k := (n - 1) * (n ^ L - 1) + 1
    UniformOneOverNFailureAtHorizon P ring isLeader 1 (k * L) := by
  have hDomainClosed : LocalStepClosed ring P.transition
      (fun _ : P.Configuration n => True) := by
    intro C hC e
    trivial
  have hproducer' : BoundedSafeScheduleProducer
      ring P.transition (fun _ : P.Configuration n => True)
      (fun C => PopulationProtocol.IsSafe P ring C isLeader) L := by
    intro C hC hnot
    exact hproducer C hnot
  let k := (n - 1) * (n ^ L - 1) + 1
  have hOn : UniformOneOverNFailureAtHorizonOn
      P ring isLeader (fun _ : P.Configuration n => True)
      1 (k * L) := by
    exact boundedIsSafeProducer_explicitOneOverNSSLEOn
      P ring isLeader (fun _ : P.Configuration n => True)
      safeTest hdec hDomainClosed hn2 L hL hproducer'
  exact uniformOneOverNFailureAtHorizon_of_trueDomain
    P ring isLeader 1 (k * L) hOn


end PPLLClosedDomainSchedulerAmplificationSol


#print axioms PPLLClosedDomainSchedulerAmplificationSol.boundedIsSafeProducer_explicitOneOverNSSLE

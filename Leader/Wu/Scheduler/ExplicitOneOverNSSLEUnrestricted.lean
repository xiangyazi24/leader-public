import Leader.Wu.Scheduler.ClosedDomainAmplification

namespace PPLLClosedDomainSchedulerAmplificationSol

open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks

set_option autoImplicit false

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
  have hOn := boundedIsSafeProducer_explicitOneOverNSSLEOn
    P ring isLeader (fun _ : P.Configuration n => True)
    safeTest hdec
    (by
      intro C hC e
      trivial)
    hn2 L hL
    (by
      intro C hC hnot
      exact hproducer C hnot)
  refine ⟨hOn.1, hOn.2.1, ?_⟩
  intro C
  exact hOn.2.2 C trivial

end PPLLClosedDomainSchedulerAmplificationSol

#print axioms PPLLClosedDomainSchedulerAmplificationSol.boundedIsSafeProducer_explicitOneOverNSSLE

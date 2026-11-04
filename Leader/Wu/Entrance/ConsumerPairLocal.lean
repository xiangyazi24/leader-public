import Leader.Wu.Entrance.WindowLocality
import Leader.Wu.Birth.WidthTwoWaitBlockProgress

set_option autoImplicit false

/-! # The width-two terminal consumer is pair-local

`consumer_pairLocal`: `BirthShortDoneTerminalConsumer.step` changes only the served pair, and the new pair depends only
on the old pair, so `B6WindowLocality` applies to the literal host (`currentStep2_pairLocal`). -/

namespace B6WindowLocalityHost

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair B6WindowLocality

variable {n psi width kappa tau : Nat}

theorem consumer_pairLocal (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    PairLocal ring (BirthShortDoneTerminalConsumer.step (κ := kappa) (τ := tau) hpsi hwidth hle ring) := by
  refine ⟨fun C e i hi hj => BirthShortDoneTerminalConsumer.step_other hpsi hwidth hle ring C e i hi hj, ?_⟩
  intro C D e hl hr
  simp only [BirthShortDoneTerminalConsumer.step, PopulationProtocol.step, BirthShortDoneTerminalConsumer.protocol,
    hl, hr]
  exact ⟨trivial, trivial⟩

theorem currentStep2_pairLocal (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    PairLocal ring (BirthPhaseWait2BlockProgress.currentStep2 (kappa := kappa) (tau := tau) hpsi h2 ring) :=
  consumer_pairLocal hpsi (by decide) h2 ring

end B6WindowLocalityHost

import Leader.Wu.Coherence.CarrierViewGate
import Leader.Wu.Splice.RecoveryGate
import Leader.Wu.Entrance.K2EnvelopeGate
import Leader.Wu.Entrance.ConcretePort
import Leader.Wu.Birth.LeaderlessBirthMassFirstLeaderGeneric


set_option autoImplicit false
set_option Elab.async false


namespace CFinalAssembly


open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open B6EntranceEnvelopeFrame B6EntranceEnvelopeWord
open B6EntranceAdmissionV3 B6EntranceAdmissionR1
open B6EntranceExpiryWord B6EntranceK2ChainCollar
open B4PassiveResetEcho


variable {n psi : Nat}


abbrev FinalLeafH (n : Nat) : Nat := 256 * n ^ 2


def FinalB7OneOverN
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi psi (16 * psi),
    FinalLeaderless C →
    n * BirthLeaderlessBirthMassB7Generic.firstLeaderFailureNumerator
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless C
        (6 * (Nat.log2 n + 1) * FinalLeafH n) ≤
      n ^ (6 * (Nat.log2 n + 1) * FinalLeafH n)


/-- Current C4 gate, with its witness parameters existentially bundled. -/
def C4GateBundle
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∃ WP : WriterProtected ring psi (Phys psi psi (16 * psi)),
    ∃ b : EntranceBudgets,
      ∃ hlaws : EntranceHostLawsV3b hpsi h2
          (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
          (fun q : Phys psi psi (16 * psi) => q) ring WP b,
        B6EntranceK2Gate.C4K2EnvelopeGate hpsi h2 ring WP b hlaws


def J1C1FinalCarrierJoin
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring =
    FinalCandidateR2C.stepFinal
      (n := n) (ψ := psi) (κ := psi) (τ := 16 * psi)
      hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring


/-- J2: C1's final-carrier geometry/coherence facts must land in the exact
writer-passive admission predicates, in reusable one-letter closure form. -/
def J2C1AdmissionLanding
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  J1C1FinalCarrierJoin hpsi h2 ring →
  R2CoherenceV31MissionGate.C1CoherenceGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring →
  ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring


def J3C2FinalCarrierJoin
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring =
    FinalCandidateR2C.stepFinal
      (n := n) (ψ := psi) (κ := psi) (τ := 16 * psi)
      hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring


def C2PassiveAdmissionMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi psi (16 * psi),
    B9RecoveryGate.C2PassiveLeaderless C →
    let H := B9ControllerRecovery.RecoveryB n
    let Q := B9ControllerRecovery.RecoveryQ n
    Q * avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
        (fun D => HasLeader D ∨ ConcreteB7AdmittedPassive hpsi h2 ring D)
        C H ≤
      (Q - 1) * n ^ H


/-- J4: recovery success is not identified with B7 admission; it is drained
into that lane without changing the C2 first-hit constants. -/
def J4C2RecoveryLanding
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  J3C2FinalCarrierJoin hpsi h2 ring →
  B9RecoveryGate.C2RecoveryGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring →
  C2PassiveAdmissionMass hpsi h2 ring

def J5C4FinalCarrierJoin
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring =
    FinalCandidateR2C.stepFinal
      (n := n) (ψ := psi) (κ := psi) (τ := 16 * psi)
      hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring


/-- J6 is exactly the census gap from existential/internal K2 words to the
uniform Q=8 literal scheduler-word mass already named by the C4 file. -/
def J6C4WitnessToUniformMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  J5C4FinalCarrierJoin hpsi h2 ring →
  C4GateBundle hpsi h2 ring →
  B6EntranceK2Gate.C4K2EnvelopeUniformMassObligation hpsi h2 ring


def J7PassiveAdmissionComposition
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn4 : 4 ≤ n)
    (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor ∧
  (ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor →
    ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring →
    C2PassiveAdmissionMass hpsi h2 ring →
    B6EntranceK2Gate.C4K2EnvelopeUniformMassObligation hpsi h2 ring →
    B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
      (FinalLeafH n) 8)


/-- J1 is now definitionally closed. -/
theorem j1C1FinalCarrierJoin_rfl
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    J1C1FinalCarrierJoin hpsi h2 ring := by
  rfl


/-- J3 is now definitionally closed. -/
theorem j3C2FinalCarrierJoin_rfl
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    J3C2FinalCarrierJoin hpsi h2 ring := by
  rfl


/-- J5 is now definitionally closed. -/
theorem j5C4FinalCarrierJoin_rfl
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    J5C4FinalCarrierJoin hpsi h2 ring := by
  rfl


theorem uniformLeaf_of_b7ComposedMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hMass : B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
      (FinalLeafH n) 8) :
    BirthLeaderlessBirthMassB7Generic.UniformFirstHitBirthMass
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless (FinalLeafH n) := by
  unfold BirthLeaderlessBirthMassB7Generic.UniformFirstHitBirthMass
    BirthLeaderlessBirthMassRenewal.UniformEscapeMass
  intro C hL
  rw [B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
    (kappa := psi) (tau := 16 * psi) hpsi h2 ring C (FinalLeafH n)]
  exact hMass.2 C ⟨trivial, hL⟩

theorem b7_bound_of_gates
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn4 : 4 ≤ n)
    (ring : DirectedRing n) (anchor : Fin n)
    (hC1 : R2CoherenceV31MissionGate.C1CoherenceGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hC2 : B9RecoveryGate.C2RecoveryGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hC4 : C4GateBundle hpsi h2 ring)
    (hJ1 : J1C1FinalCarrierJoin hpsi h2 ring)
    (hJ2 : J2C1AdmissionLanding hpsi h2 ring)
    (hJ3 : J3C2FinalCarrierJoin hpsi h2 ring)
    (hJ4 : J4C2RecoveryLanding hpsi h2 ring)
    (hJ5 : J5C4FinalCarrierJoin hpsi h2 ring)
    (hJ6 : J6C4WitnessToUniformMass hpsi h2 ring)
    (hJ7 : J7PassiveAdmissionComposition hpsi h2 hn4 ring anchor) :
    FinalB7OneOverN hpsi h2 ring := by
  have hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring :=
    hJ2 hJ1 hC1
  have hRecovery : C2PassiveAdmissionMass hpsi h2 ring :=
    hJ4 hJ3 hC2
  have hK2Mass :
      B6EntranceK2Gate.C4K2EnvelopeUniformMassObligation hpsi h2 ring :=
    hJ6 hJ5 hC4
  rcases hJ7 with ⟨hB4, hCompose⟩
  have hMass : B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
      (FinalLeafH n) 8 :=
    hCompose hB4 hClosed hRecovery hK2Mass
  have hLeaf := uniformLeaf_of_b7ComposedMass hpsi h2 ring hMass
  have hn2 : 2 ≤ n := Nat.le_trans (by decide : 2 ≤ 4) hn4
  unfold FinalB7OneOverN
  intro C hC
  exact
    BirthLeaderlessBirthMassB7Generic.firstLeader_failure_le_one_over_n_of_uniformBirthMass
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless (FinalLeafH n) hLeaf hn2 C hC


end CFinalAssembly

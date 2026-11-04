import Leader.Wu.Entrance.CalibratedLeaf
import Leader.Wu.Splice.RecoveryGateBirthLeaf
import Leader.Wu.Splice.RecoveryGateInstance
import Leader.Wu.Entrance.SharedBirthWordMass
import Leader.Wu.Entrance.ReadyWindowMassSimulation

set_option autoImplicit false
set_option Elab.async false

namespace CFinalAssembly3

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open B4PassiveResetEcho
open CFinalAssembly2

variable {n psi : Nat}

/-- C2 recovery followed by the calibrated C-final birth leaf. -/
def C2RecoveryH3 (n psi : Nat) : Nat :=
  B9ControllerRecovery.RecoveryB n + FinalLeafHV2 n psi

def C2RecoveryQ3 (n : Nat) : Nat :=
  B9ControllerRecovery.RecoveryQ n * 8

@[simp] theorem C2RecoveryH3_eq (n psi : Nat) :
    C2RecoveryH3 n psi =
      6 * n +
        B6EntranceK2Budget.B6EntranceK2Budget.c4FrozenCoeff
          psi (Q2star psi) * n ^ 2 := by
  rfl

@[simp] theorem C2RecoveryQ3_eq (n : Nat) :
    C2RecoveryQ3 n = n ^ (6 * n) * 8 := by
  rfl

def C2FinalAliveMassV3
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi)) : Prop :=
  let H := C2RecoveryH3 n psi
  let Q := C2RecoveryQ3 n
  Q * aliveCount
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C H <=
    (Q - 1) * n ^ H

def C2FinalHasLeaderAvoidMassV3
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi)) : Prop :=
  let H := C2RecoveryH3 n psi
  let Q := C2RecoveryQ3 n
  Q * avoidCount
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      (fun _ : Config n psi psi (16 * psi) => True)
      HasLeader C H <=
    (Q - 1) * n ^ H

private theorem two_stage_escape_at_v3
    {S : Type} {m : Nat}
    (step : S -> Fin m -> S) (Good R : S -> Prop)
    (B1 B2 Q1 Q2 : Nat) (hQ2 : 1 <= Q2) (x : S)
    (h1 : Q1 * avoidCount step Good R x B1 <=
      (Q1 - 1) * m ^ B1)
    (h2 : forall y, Good y -> R y ->
      Q2 * aliveCount step Good y B2 <=
        (Q2 - 1) * m ^ B2) :
    Q1 * Q2 * aliveCount step Good x (B1 + B2) <=
      (Q1 * Q2 - 1) * m ^ (B1 + B2) := by
  by_cases hQ1z : Q1 = 0
  · subst Q1
    simp
  · have hQ1 : 1 <= Q1 := Nat.one_le_iff_ne_zero.mpr hQ1z
    have hc := BirthTwoStageEscape.two_stage_core
      step Good R B2 Q2 hQ2 h2 B1 x
    generalize aliveCount step Good x (B1 + B2) = A at hc ⊢
    generalize avoidCount step Good R x B1 = V at hc h1
    have hN : m ^ (B1 + B2) = m ^ B2 * m ^ B1 := by
      rw [Nat.pow_add, Nat.mul_comm]
    rw [hN]
    generalize m ^ B2 = M at hc ⊢
    generalize m ^ B1 = N at hc h1 ⊢
    have s1 : Q1 * (Q2 * A) <=
        M * (Q1 * ((Q2 - 1) * N) + Q1 * V) := by
      calc
        Q1 * (Q2 * A) <= Q1 * (M * ((Q2 - 1) * N + V)) :=
          Nat.mul_le_mul_left _ hc
        _ = M * (Q1 * ((Q2 - 1) * N) + Q1 * V) := by
          rw [Nat.mul_left_comm, Nat.mul_add]
    have s2 : M * (Q1 * ((Q2 - 1) * N) + Q1 * V) <=
        M * (Q1 * ((Q2 - 1) * N) + (Q1 - 1) * N) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left h1 _)
    have e3 : Q1 * ((Q2 - 1) * N) + (Q1 - 1) * N =
        (Q1 * Q2 - 1) * N := by
      have hq : Q1 * (Q2 - 1) + (Q1 - 1) = Q1 * Q2 - 1 := by
        have ht : Q1 * (Q2 - 1) = Q1 * Q2 - Q1 :=
          Nat.mul_sub_one Q1 Q2
        have hle : Q1 <= Q1 * Q2 := Nat.le_mul_of_pos_right Q1 hQ2
        omega
      rw [← Nat.mul_assoc, ← Nat.add_mul, hq]
    rw [e3] at s2
    calc
      Q1 * Q2 * A = Q1 * (Q2 * A) := Nat.mul_assoc _ _ _
      _ <= M * ((Q1 * Q2 - 1) * N) := Nat.le_trans s1 s2
      _ = (Q1 * Q2 - 1) * (M * N) := by rw [Nat.mul_left_comm]

theorem c2FinalAliveMassV3_of_recovery_and_leaf
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi))
    (hRecovery : B9RecoveryGate.C2FinalRecoveryMass hpsi h2 ring C)
    (hLeaf : C4C5SharedBirthWordMassAt
      hpsi h2 ring (FinalLeafHV2 n psi)) :
    C2FinalAliveMassV3 hpsi h2 ring C := by
  have hm := B6LocalReverseFill.avoidCount_mono_good
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    FinalLeaderless
    (fun _ : Config n psi psi (16 * psi) => True)
    (FinalRecoveryTarget hpsi ring)
    (fun _ _ => trivial) C (B9ControllerRecovery.RecoveryB n)
  have hr := hRecovery
  unfold B9RecoveryGate.C2FinalRecoveryMass at hr
  dsimp only at hr
  have h1 : B9ControllerRecovery.RecoveryQ n *
      avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless (FinalRecoveryTarget hpsi ring) C
        (B9ControllerRecovery.RecoveryB n) <=
      (B9ControllerRecovery.RecoveryQ n - 1) *
        n ^ B9ControllerRecovery.RecoveryB n := by
    exact (Nat.mul_le_mul_left _ hm).trans hr
  have hStage2 : forall D : Config n psi psi (16 * psi),
      FinalLeaderless D -> FinalRecoveryTarget hpsi ring D ->
      8 * aliveCount
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
          FinalLeaderless D (FinalLeafHV2 n psi) <=
        (8 - 1) * n ^ FinalLeafHV2 n psi := by
    intro D hL _hR
    rw [B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
      (kappa := psi) (tau := 16 * psi)
      hpsi h2 ring D (FinalLeafHV2 n psi)]
    exact hLeaf D hL
  have h := two_stage_escape_at_v3
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    FinalLeaderless (FinalRecoveryTarget hpsi ring)
    (B9ControllerRecovery.RecoveryB n) (FinalLeafHV2 n psi)
    (B9ControllerRecovery.RecoveryQ n) 8 (by decide) C h1 hStage2
  simpa [C2FinalAliveMassV3, C2RecoveryH3, C2RecoveryQ3] using h

theorem c2FinalHasLeaderAvoidMassV3_of_alive
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi))
    (hAlive : C2FinalAliveMassV3 hpsi h2 ring C) :
    C2FinalHasLeaderAvoidMassV3 hpsi h2 ring C := by
  unfold C2FinalAliveMassV3 at hAlive
  unfold C2FinalHasLeaderAvoidMassV3
  dsimp only at hAlive ⊢
  rw [← B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
    (kappa := psi) (tau := 16 * psi)
    hpsi h2 ring C (C2RecoveryH3 n psi)]
  exact hAlive

/-- V3 keeps the accepted RecoveryB/RecoveryQ first stage and replaces only
V2's hard-coded 256*n^2 birth stage by FinalLeafHV2. -/
def C2RecoveryGateV3
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  B9RiskRefinement2C.HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) hpsi ∧
    B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause ∧
    forall C : Config n psi psi (16 * psi),
      B9RecoveryGate.C2PassiveLeaderless C ->
      B9RecoveryGate.C2FinalRecoveryMass hpsi h2 ring C ∧
        C2FinalAliveMassV3 hpsi h2 ring C ∧
        C2FinalHasLeaderAvoidMassV3 hpsi h2 ring C

theorem c2RecoveryGateV3_of_recovery_and_leaf
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hHold : B9RiskRefinement2C.HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) hpsi)
    (hCompletion : B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause)
    (hRecovery : forall C : Config n psi psi (16 * psi),
      B9RecoveryGate.C2PassiveLeaderless C ->
      B9RecoveryGate.C2FinalRecoveryMass hpsi h2 ring C)
    (hLeaf : C4C5SharedBirthWordMassAt
      hpsi h2 ring (FinalLeafHV2 n psi)) :
    C2RecoveryGateV3 hpsi h2 ring := by
  refine ⟨hHold, hCompletion, ?_⟩
  intro C hPassive
  have hr := hRecovery C hPassive
  have ha := c2FinalAliveMassV3_of_recovery_and_leaf
    hpsi h2 ring C hr hLeaf
  have hh := c2FinalHasLeaderAvoidMassV3_of_alive hpsi h2 ring C ha
  exact ⟨hr, ha, hh⟩

theorem c2RecoveryGateV3_of_v1_and_leaf
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hV1 : B9RecoveryGate.C2RecoveryGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hLeaf : C4C5SharedBirthWordMassAt
      hpsi h2 ring (FinalLeafHV2 n psi)) :
    C2RecoveryGateV3 hpsi h2 ring := by
  exact c2RecoveryGateV3_of_recovery_and_leaf hpsi h2 ring
    hV1.1 hV1.2.1 (fun C h => (hV1.2.2 C h).1) hLeaf

theorem c2RecoveryGateV3_of_v2_and_leaf
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hV2 : B9RecoveryGateV2.C2RecoveryGateV2 hpsi h2 ring)
    (hLeaf : C4C5SharedBirthWordMassAt
      hpsi h2 ring (FinalLeafHV2 n psi)) :
    C2RecoveryGateV3 hpsi h2 ring := by
  exact c2RecoveryGateV3_of_recovery_and_leaf hpsi h2 ring
    hV2.1 hV2.2.1 (fun C h => (hV2.2.2 C h).1) hLeaf

theorem c2RecoveryGateV3_of_installed
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hDomain : B9RiskRefinementPhys5.R1Row10gHostRiskViewResidual)
    (hJ4 : B9RecoveryGate.C2J4RecoveryToB7Mass
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hLeaf : C4C5SharedBirthWordMassAt
      hpsi h2 ring (FinalLeafHV2 n psi)) :
    C2RecoveryGateV3 hpsi h2 ring := by
  apply c2RecoveryGateV3_of_v1_and_leaf hpsi h2 ring
  · exact B9RecoveryGateInstance.c2RecoveryGate_of_installed
      (n := n) (psi := psi) (kappa := psi) (tau := 16 * psi)
      hpsi h2 ring hDomain hJ4
  · exact hLeaf

def C2PassiveAdmissionMassV3
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall C : Config n psi psi (16 * psi),
    B9RecoveryGate.C2PassiveLeaderless C ->
    let H := C2RecoveryH3 n psi
    let Q := C2RecoveryQ3 n
    Q * avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (fun _ : Config n psi psi (16 * psi) => True)
        (fun D => HasLeader D ∨ ConcreteB7AdmittedPassive hpsi h2 ring D)
        C H <=
      (Q - 1) * n ^ H

def J4C2RecoveryLandingV3
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  CFinalAssembly.J3C2FinalCarrierJoin hpsi h2 ring ->
  C2RecoveryGateV3 hpsi h2 ring ->
  C2PassiveAdmissionMassV3 hpsi h2 ring

/-- Same target-monotonicity proof as
`B9RecoveryGateV2.j4C2RecoveryLandingV2_of_gate`, now specialized to the
composed V3 H/Q. -/
theorem j4C2RecoveryLandingV3_of_gate
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) :
    J4C2RecoveryLandingV3 hpsi h2 ring := by
  intro _hJ3 hGate
  rcases hGate with ⟨_hHold, _hCompletion, hMass⟩
  unfold C2PassiveAdmissionMassV3
  intro C hPassive
  have hHas := (hMass C hPassive).2.2
  unfold C2FinalHasLeaderAvoidMassV3 at hHas
  dsimp only at hHas ⊢
  have hmono := B6EntranceCompose.avoidCount_mono_target
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (fun _ : Config n psi psi (16 * psi) => True)
    HasLeader
    (fun D => HasLeader D ∨ ConcreteB7AdmittedPassive hpsi h2 ring D)
    (fun _ h => Or.inl h) C (C2RecoveryH3 n psi)
  exact (Nat.mul_le_mul_left (C2RecoveryQ3 n) hmono).trans hHas

/-- V3 J7 changes only the type of the C2 landing currency.  As in V2, the
final B7 mass itself is the shared Q=8 leaf. -/
def J7PassiveAdmissionCompositionV3
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn4 : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor ∧
  (ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor ->
    ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring ->
    C2PassiveAdmissionMassV3 hpsi h2 ring ->
    C4K2EnvelopeUniformMassObligationAt
      hpsi h2 ring (FinalLeafHV2 n psi) ->
    B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : Config n psi psi (16 * psi) => True)
      (FinalLeafHV2 n psi) 8)

theorem j7_v3_of_b4_and_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn4 : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (hB4 : ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor)
    (hLeaf : C4C5SharedBirthWordMassAt
      hpsi h2 ring (FinalLeafHV2 n psi)) :
    J7PassiveAdmissionCompositionV3 hpsi h2 hn4 ring anchor := by
  refine ⟨hB4, ?_⟩
  intro _hB4 _hClosed _hRecovery _hC4
  exact b7ComposedMass_of_sharedBirthWordMassAt
    hpsi h2 ring (FinalLeafHV2 n psi) hLeaf

/-- Calibrated consumer.  J4 is no longer an external old-C2 join: it is
closed from the V3 gate by `j4C2RecoveryLandingV3_of_gate`. -/
theorem b7_bound_of_gates_v3
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn4 : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (hC1 : R2CoherenceV31MissionGate.C1CoherenceGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hC2 : C2RecoveryGateV3 hpsi h2 ring)
    (hC4 :
      B6EntranceK2Budget.B6EntranceK2Budget.B6EntranceK2Budget.FrozenC4GateBundle
        hpsi h2 ring)
    (hJ1 : CFinalAssembly.J1C1FinalCarrierJoin hpsi h2 ring)
    (hJ2 : CFinalAssembly.J2C1AdmissionLanding hpsi h2 ring)
    (hJ3 : CFinalAssembly.J3C2FinalCarrierJoin hpsi h2 ring)
    (hJ5 : CFinalAssembly.J5C4FinalCarrierJoin hpsi h2 ring)
    (hJ6 : J6C4WitnessToUniformMassV2 hpsi h2 ring)
    (hJ7 : J7PassiveAdmissionCompositionV3
      hpsi h2 hn4 ring anchor) :
    FinalB7OneOverN hpsi h2 ring (FinalLeafHV2 n psi) := by
  have hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring :=
    hJ2 hJ1 hC1
  have hRecovery : C2PassiveAdmissionMassV3 hpsi h2 ring :=
    (j4C2RecoveryLandingV3_of_gate hpsi h2 ring) hJ3 hC2
  have hK2Mass := hJ6 hJ5 hC4
  rcases hJ7 with ⟨hB4, hCompose⟩
  have hMass : B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : Config n psi psi (16 * psi) => True)
      (FinalLeafHV2 n psi) 8 :=
    hCompose hB4 hClosed hRecovery hK2Mass
  have hLeaf := uniformLeaf_of_b7ComposedMass_v2
    hpsi h2 ring (FinalLeafHV2 n psi) hMass
  have hn2 : 2 <= n := Nat.le_trans (by decide : 2 <= 4) hn4
  unfold FinalB7OneOverN
  intro C hC
  exact
    BirthLeaderlessBirthMassB7Generic.firstLeader_failure_le_one_over_n_of_uniformBirthMass
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless (FinalLeafHV2 n psi) hLeaf hn2 C hC

end CFinalAssembly3

import Leader.Wu.Splice.RecoveryGate
import Leader.Wu.Entrance.SharedBirthWordMass


set_option autoImplicit false
set_option Elab.async false


namespace B9RecoveryGateV2


open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C


variable {n psi : Nat}


def C2BirthH (n : Nat) : Nat := 256 * n ^ 2


def C2RecoveryH2 (n : Nat) : Nat :=
  B9ControllerRecovery.RecoveryB n + C2BirthH n


def C2RecoveryQ2 (n : Nat) : Nat :=
  B9ControllerRecovery.RecoveryQ n * 8


/-- Recalibrated C2 failure mass after recovery followed by the shared birth
leaf.  This supersedes the old gate's same-horizon `C2FinalAliveMass`
conjunct; the old gate remains only as a compatibility API. -/
def C2FinalAliveMassV2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi)) : Prop :=
  let H := C2RecoveryH2 n
  let Q := C2RecoveryQ2 n
  Q * aliveCount
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C H ≤
    (Q - 1) * n ^ H


def C2FinalHasLeaderAvoidMassV2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi)) : Prop :=
  let H := C2RecoveryH2 n
  let Q := C2RecoveryQ2 n
  Q * avoidCount
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      (fun _ : Config n psi psi (16 * psi) => True)
      HasLeader C H ≤
    (Q - 1) * n ^ H


/-- Named landing interface for the stage-two leaf.  It is not an extra
residual: the shared leaf proves it outright, and the recovery-target premise
is intentionally unused. -/
def RecoveryLeafLanding
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ D : Config n psi psi (16 * psi),
    FinalLeaderless D → FinalRecoveryTarget hpsi ring D →
    8 * aliveCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless D (C2BirthH n) ≤
      (8 - 1) * n ^ C2BirthH n


theorem recoveryLeafLanding_of_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hLeaf : B6EntranceK2Mass2.C4C5SharedBirthWordMass hpsi h2 ring) :
    RecoveryLeafLanding hpsi h2 ring := by
  unfold RecoveryLeafLanding
  unfold B6EntranceK2Mass2.C4C5SharedBirthWordMass at hLeaf
  intro D hL _hRecovery
  have h := hLeaf D hL
  rw [B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
    hpsi h2 ring D (C2BirthH n)]
  simpa [C2BirthH] using h


private theorem two_stage_escape_at
    {S : Type} {m : Nat}
    (step : S → Fin m → S) (Good R : S → Prop)
    (B1 B2 Q1 Q2 : Nat) (hQ2 : 1 ≤ Q2) (x : S)
    (h1 : Q1 * avoidCount step Good R x B1 ≤
      (Q1 - 1) * m ^ B1)
    (h2 : ∀ y, Good y → R y →
      Q2 * aliveCount step Good y B2 ≤
        (Q2 - 1) * m ^ B2) :
    Q1 * Q2 * aliveCount step Good x (B1 + B2) ≤
      (Q1 * Q2 - 1) * m ^ (B1 + B2) := by
  by_cases hQ1z : Q1 = 0
  · subst Q1
    simp
  · have hQ1 : 1 ≤ Q1 := Nat.one_le_iff_ne_zero.mpr hQ1z
    have hc := BirthTwoStageEscape.two_stage_core
      step Good R B2 Q2 hQ2 h2 B1 x
    generalize aliveCount step Good x (B1 + B2) = A at hc ⊢
    generalize avoidCount step Good R x B1 = V at hc h1
    have hN : m ^ (B1 + B2) = m ^ B2 * m ^ B1 := by
      rw [Nat.pow_add, Nat.mul_comm]
    rw [hN]
    generalize m ^ B2 = M at hc ⊢
    generalize m ^ B1 = N at hc h1 ⊢
    have s1 : Q1 * (Q2 * A) ≤
        M * (Q1 * ((Q2 - 1) * N) + Q1 * V) := by
      calc
        Q1 * (Q2 * A) ≤ Q1 * (M * ((Q2 - 1) * N + V)) :=
          Nat.mul_le_mul_left _ hc
        _ = M * (Q1 * ((Q2 - 1) * N) + Q1 * V) := by
          rw [Nat.mul_left_comm, Nat.mul_add]
    have s2 : M * (Q1 * ((Q2 - 1) * N) + Q1 * V) ≤
        M * (Q1 * ((Q2 - 1) * N) + (Q1 - 1) * N) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left h1 _)
    have e3 : Q1 * ((Q2 - 1) * N) + (Q1 - 1) * N =
        (Q1 * Q2 - 1) * N := by
      have hq : Q1 * (Q2 - 1) + (Q1 - 1) = Q1 * Q2 - 1 := by
        have ht : Q1 * (Q2 - 1) = Q1 * Q2 - Q1 :=
          Nat.mul_sub_one Q1 Q2
        have hle : Q1 ≤ Q1 * Q2 := Nat.le_mul_of_pos_right Q1 hQ2
        omega
      rw [← Nat.mul_assoc, ← Nat.add_mul, hq]
    rw [e3] at s2
    calc
      Q1 * Q2 * A = Q1 * (Q2 * A) := Nat.mul_assoc _ _ _
      _ ≤ M * ((Q1 * Q2 - 1) * N) := Nat.le_trans s1 s2
      _ = (Q1 * Q2 - 1) * (M * N) := by rw [Nat.mul_left_comm]

theorem c2FinalAliveMassV2_of_recovery_and_leaf
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi))
    (hRecovery : B9RecoveryGate.C2FinalRecoveryMass hpsi h2 ring C)
    (hLeaf : B6EntranceK2Mass2.C4C5SharedBirthWordMass hpsi h2 ring) :
    C2FinalAliveMassV2 hpsi h2 ring C := by
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
        (B9ControllerRecovery.RecoveryB n) ≤
      (B9ControllerRecovery.RecoveryQ n - 1) *
        n ^ B9ControllerRecovery.RecoveryB n := by
    exact (Nat.mul_le_mul_left _ hm).trans hr
  have hLanding :=
    recoveryLeafLanding_of_sharedBirthWordMass hpsi h2 ring hLeaf
  have hStage2 : ∀ D : Config n psi psi (16 * psi),
      FinalLeaderless D → FinalRecoveryTarget hpsi ring D →
      8 * aliveCount
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
          FinalLeaderless D (C2BirthH n) ≤
        (8 - 1) * n ^ C2BirthH n := by
    intro D hL hR
    exact hLanding D hL hR
  have h := two_stage_escape_at
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    FinalLeaderless (FinalRecoveryTarget hpsi ring)
    (B9ControllerRecovery.RecoveryB n) (C2BirthH n)
    (B9ControllerRecovery.RecoveryQ n) 8 (by decide) C h1 hStage2
  simpa [C2FinalAliveMassV2, C2RecoveryH2, C2RecoveryQ2] using h


theorem c2FinalHasLeaderAvoidMassV2_of_alive
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi))
    (hAlive : C2FinalAliveMassV2 hpsi h2 ring C) :
    C2FinalHasLeaderAvoidMassV2 hpsi h2 ring C := by
  unfold C2FinalAliveMassV2 at hAlive
  unfold C2FinalHasLeaderAvoidMassV2
  dsimp only at hAlive ⊢
  rw [← B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
    hpsi h2 ring C (C2RecoveryH2 n)]
  exact hAlive


/-- Recalibrated C2 gate.  The old `C2RecoveryGate` same-horizon alive
conjunct is superseded: V2 keeps the original recovery mass at `RecoveryB/Q`
and records the post-birth failure currencies at `H2/Q2`. -/
def C2RecoveryGateV2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  B9RiskRefinement2C.HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) hpsi ∧
    B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause ∧
    ∀ C : Config n psi psi (16 * psi),
      B9RecoveryGate.C2PassiveLeaderless C →
      B9RecoveryGate.C2FinalRecoveryMass hpsi h2 ring C ∧
        C2FinalAliveMassV2 hpsi h2 ring C ∧
        C2FinalHasLeaderAvoidMassV2 hpsi h2 ring C


theorem c2RecoveryGateV2_of_recovery_and_leaf
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hHold : B9RiskRefinement2C.HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) hpsi)
    (hCompletion : B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause)
    (hRecovery : ∀ C : Config n psi psi (16 * psi),
      B9RecoveryGate.C2PassiveLeaderless C →
      B9RecoveryGate.C2FinalRecoveryMass hpsi h2 ring C)
    (hLeaf : B6EntranceK2Mass2.C4C5SharedBirthWordMass hpsi h2 ring) :
    C2RecoveryGateV2 hpsi h2 ring := by
  refine ⟨hHold, hCompletion, ?_⟩
  intro C hPassive
  have hr := hRecovery C hPassive
  have ha := c2FinalAliveMassV2_of_recovery_and_leaf
    hpsi h2 ring C hr hLeaf
  have hh := c2FinalHasLeaderAvoidMassV2_of_alive
    hpsi h2 ring C ha
  exact ⟨hr, ha, hh⟩


def C2PassiveAdmissionMassV2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : Config n psi psi (16 * psi),
    B9RecoveryGate.C2PassiveLeaderless C →
    let H := C2RecoveryH2 n
    let Q := C2RecoveryQ2 n
    Q * avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (fun _ : Config n psi psi (16 * psi) => True)
        (fun D => HasLeader D ∨ ConcreteB7AdmittedPassive hpsi h2 ring D)
        C H ≤
      (Q - 1) * n ^ H


def J4C2RecoveryLandingV2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  CFinalAssembly.J3C2FinalCarrierJoin hpsi h2 ring →
  C2RecoveryGateV2 hpsi h2 ring →
  C2PassiveAdmissionMassV2 hpsi h2 ring


theorem j4C2RecoveryLandingV2_of_gate
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    J4C2RecoveryLandingV2 hpsi h2 ring := by
  intro _hJ3 hGate
  rcases hGate with ⟨_hHold, _hCompletion, hMass⟩
  unfold C2PassiveAdmissionMassV2
  intro C hPassive
  have hHas := (hMass C hPassive).2.2
  unfold C2FinalHasLeaderAvoidMassV2 at hHas
  dsimp only at hHas ⊢
  have hmono := B6EntranceCompose.avoidCount_mono_target
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (fun _ : Config n psi psi (16 * psi) => True)
    HasLeader
    (fun D => HasLeader D ∨ ConcreteB7AdmittedPassive hpsi h2 ring D)
    (fun _ h => Or.inl h) C (C2RecoveryH2 n)
  exact (Nat.mul_le_mul_left (C2RecoveryQ2 n) hmono).trans hHas

end B9RecoveryGateV2

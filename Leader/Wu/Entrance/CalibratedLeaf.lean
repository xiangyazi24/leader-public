import Leader.Wu.Entrance.JoinObligations
import Leader.Wu.Entrance.StageBudget
import Leader.Wu.Entrance.ReadyWindowMassSimulation

set_option autoImplicit false
set_option Elab.async false

namespace CFinalAssembly2

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open BirthCheckPermitRepairLeaf BirthCheckChainR1PerBlock
open B6EntranceV2 B6EntranceK2Mass3 B6EntranceK2Budget
open B4PassiveResetEcho
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi : Nat}

/--
`CFinalAssembly.FinalLeafH = 256 * n^2` and its old final theorem are kept
for audit history, but are superseded for the calibrated C-final route by
`FinalLeafHV2` and `b7_bound_of_gates_v2` below.
-/
def ReadyWindowQ2 (psi Q2 : Nat) : Prop :=
  (4 * (psi + 1)) ^ (psi - 1) <= 3 ^ (psi - 1) * Q2

private theorem readyWindowQ2_exists (psi : Nat) :
    exists Q2, ReadyWindowQ2 psi Q2 := by
  refine ⟨(4 * (psi + 1)) ^ (psi - 1), ?_⟩
  unfold ReadyWindowQ2
  have h3 : 1 <= 3 ^ (psi - 1) :=
    Nat.one_le_pow (psi - 1) 3 (by decide)
  calc
    (4 * (psi + 1)) ^ (psi - 1) =
        1 * ((4 * (psi + 1)) ^ (psi - 1)) := by simp
    _ <= 3 ^ (psi - 1) * ((4 * (psi + 1)) ^ (psi - 1)) :=
      Nat.mul_le_mul_right _ h3

/-- Explicit ReadyWindow denominator correction depending only on `psi`. -/
def Q2star (psi : Nat) : Nat :=
  (4 * (psi + 1)) ^ (psi - 1)

theorem Q2star_spec (psi : Nat) : ReadyWindowQ2 psi (Q2star psi) := by
  unfold ReadyWindowQ2 Q2star
  have h3 : 1 <= 3 ^ (psi - 1) :=
    Nat.one_le_pow (psi - 1) 3 (by decide)
  calc
    (4 * (psi + 1)) ^ (psi - 1) =
        1 * ((4 * (psi + 1)) ^ (psi - 1)) := by simp
    _ <= 3 ^ (psi - 1) * ((4 * (psi + 1)) ^ (psi - 1)) :=
      Nat.mul_le_mul_right _ h3

/-- Honest calibrated C4 leaf; its coefficient is `psi`-only. -/
def FinalLeafHV2 (n psi : Nat) : Nat :=
  B6EntranceK2Budget.B6EntranceK2Budget.C4CorrectedFinalLeafH
    n psi (Q2star psi)

@[simp] theorem FinalLeafHV2_eq (n psi : Nat) :
    FinalLeafHV2 n psi =
      B6EntranceK2Budget.B6EntranceK2Budget.c4FrozenCoeff
        psi (Q2star psi) * n ^ 2 := by
  rfl

/-- Horizon-parametric replacement of `CFinalAssembly.FinalB7OneOverN`. -/
def FinalB7OneOverN
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (H : Nat) : Prop :=
  forall C : FinalCandidateR2C.Config n psi psi (16 * psi),
    FinalLeaderless C ->
    n * BirthLeaderlessBirthMassB7Generic.firstLeaderFailureNumerator
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless C
        (6 * (Nat.log2 n + 1) * H) <=
      n ^ (6 * (Nat.log2 n + 1) * H)

/-- Shared final Q=8 leaf at an arbitrary leaf horizon. -/
def C4C5SharedBirthWordMassAt
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (H : Nat) : Prop :=
  forall C : FinalCandidateR2C.Config n psi psi (16 * psi),
    FinalLeaderless C ->
    8 * avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
        HasLeader C H <=
      (8 - 1) * n ^ H

/-- Local copy of the private padding lemma in `B6EntranceK2Mass3`. -/
private theorem uniformEscapeMass_pad_v2 {S : Type} {m : Nat}
    (step : S -> Fin m -> S) (Good : S -> Prop)
    (B H Q : Nat) (hBH : B <= H)
    (hMass : UniformEscapeMass step Good B Q) :
    UniformEscapeMass step Good H Q := by
  intro x hx
  have hb := hMass x hx
  have hp := alive_pad step Good (H - B) B x
  have hsum : B + (H - B) = H := by omega
  rw [hsum] at hp
  calc
    Q * aliveCount step Good x H
        <= Q * (aliveCount step Good x B * m ^ (H - B)) :=
      Nat.mul_le_mul_left Q hp
    _ = (Q * aliveCount step Good x B) * m ^ (H - B) := by
      rw [Nat.mul_assoc]
    _ <= ((Q - 1) * m ^ B) * m ^ (H - B) :=
      Nat.mul_le_mul_right _ hb
    _ = (Q - 1) * m ^ H := by
      rw [Nat.mul_assoc, <- Nat.pow_add, hsum]


/-- Horizon-parametric form of the Mass3 ReadyWindow -> final-leaf producer. -/
theorem sharedBirthWordMassAt_of_r1ReadyWindowMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (h3 : 2 < psi)
    (hpsin : psi <= n) (ring : DirectedRing n)
    (B1 Q1 Q2 H : Nat) (hQ1 : 1 <= Q1)
    (hQ2 : ReadyWindowQ2 psi Q2)
    (hReady : forall C : BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi),
      BirthShortDoneTerminalFirstHit.Leaderless C ->
      Q1 * avoidCount (step1 hpsi h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless
          (ReadyWindow ring) C B1 <=
        (Q1 - 1) * n ^ B1)
    (hSim : C4C5FinalR1MassSimulation hpsi h2 ring)
    (hH : 3 * (Q1 * Q2) * (B1 + 2 * n * (psi - 1)) <= H) :
    C4C5SharedBirthWordMassAt hpsi h2 ring H := by
  let H0 := 3 * (Q1 * Q2) * (B1 + 2 * n * (psi - 1))
  have hR1 : UniformEscapeMass
      (step1 (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
      BirthShortDoneTerminalFirstHit.Leaderless H0 8 := by
    dsimp only [H0]
    exact BirthCheckChainR1PerBlock.leaf_of_ready_window_mass
      (κ := psi) (τ := 16 * psi) hpsi h3 ring hpsin
      B1 Q1 Q2 hQ1 hQ2 hReady
  have hFinal0 : UniformEscapeMass
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless H0 8 := by
    intro C hC
    have hs := hSim H0 C hC
    have hr := hR1 (finalBase C) hs.1
    exact (Nat.mul_le_mul_left 8 hs.2).trans hr
  have hFinal := uniformEscapeMass_pad_v2
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    FinalLeaderless H0 H 8 hH hFinal0
  unfold C4C5SharedBirthWordMassAt
  intro C hC
  have hm := hFinal C hC
  rw [B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
    (kappa := psi) (tau := 16 * psi) hpsi h2 ring C H] at hm
  exact hm

/-- The frozen C4 bundle supplies the ReadyWindow mass at its exact B,Q. -/
theorem sharedBirthWordMassV2_of_frozenC4
    (hpsi : 0 < psi) (h2 : 2 <= psi) (h3 : 2 < psi)
    (hpsin : psi <= n) (ring : DirectedRing n)
    (hC4 :
      B6EntranceK2Budget.B6EntranceK2Budget.B6EntranceK2Budget.FrozenC4GateBundle
        hpsi h2 ring)
    (hSim : C4C5FinalR1MassSimulation hpsi h2 ring) :
    C4C5SharedBirthWordMassAt hpsi h2 ring (FinalLeafHV2 n psi) := by
  obtain ⟨WP, hlaws, hReadyHost⟩ :=
    B6EntranceK2Budget.B6EntranceK2Budget.B6EntranceK2Budget.frozenC4GateBundle_readyWindow
      hpsi h2 ring hC4
  have hstep :
      B9Host.hostStep
          (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring =
        step1 hpsi h2 ring := by
    funext C e
    exact B9Host.hostStep_r1_eq_step1
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring C e
  have hReady :
      forall C : BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi),
        BirthShortDoneTerminalFirstHit.Leaderless C ->
        entranceQ (c4Budget n psi) *
            avoidCount (step1 hpsi h2 ring)
              BirthShortDoneTerminalFirstHit.Leaderless
              (ReadyWindow ring) C (entranceB n (c4Budget n psi)) <=
          (entranceQ (c4Budget n psi) - 1) *
            n ^ (entranceB n (c4Budget n psi)) := by
    intro C hC
    have hm := hReadyHost C hC
    rw [hstep] at hm
    change entranceQ (c4Budget n psi) *
        avoidCount (step1 hpsi h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless
          (ReadyWindow ring) C (entranceB n (c4Budget n psi)) <=
      (entranceQ (c4Budget n psi) - 1) *
        n ^ (entranceB n (c4Budget n psi)) at hm
    exact hm
  have hQ1 : 1 <= entranceQ (c4Budget n psi) := by
    rw [c4Budget_entranceQ]
    exact Nat.one_le_pow _ _ (by
      have h := one_le_envelopeTouchBound psi
      omega)
  have hn : 1 <= n := by omega
  have hH :
      3 * (entranceQ (c4Budget n psi) * Q2star psi) *
          (entranceB n (c4Budget n psi) + 2 * n * (psi - 1)) <=
        FinalLeafHV2 n psi := by
    simpa [B6EntranceK2Mass4.c4BoostedH, FinalLeafHV2] using
      B6EntranceK2Budget.B6EntranceK2Budget.c4BoostedH_le_correctedFinalLeafH
        n psi (Q2star psi) hn
  exact sharedBirthWordMassAt_of_r1ReadyWindowMass
    hpsi h2 h3 hpsin ring
    (entranceB n (c4Budget n psi))
    (entranceQ (c4Budget n psi))
    (Q2star psi) (FinalLeafHV2 n psi)
    hQ1 (Q2star_spec psi) hReady hSim hH


private theorem aliveAlong_end_v2
    {S : Type} {m : Nat}
    (step : S -> Fin m -> S) (Good : S -> Prop)
    (x : S) (u : List (Fin m))
    (h : AliveAlong step Good x u) : Good (u.foldl step x) := by
  induction u generalizing x with
  | nil => exact h
  | cons e rest ih =>
      simpa only [List.foldl_cons] using (ih (x := step x e) h.2)

/-- Horizon-parametric replacement of C4's hard-coded `256*n^2` mass. -/
def C4K2EnvelopeUniformMassObligationAt
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (H : Nat) : Prop :=
  forall (C0 : FinalCandidateR2C.Config n psi psi (16 * psi))
    (lineage : List (Fin n)),
    ConcreteB7AdmittedPassive hpsi h2 ring C0 ->
    FinalResetEchoClear C0 ->
    AliveAlong
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless C0 lineage ->
    let C := lineage.foldl
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring) C0
    8 * avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
        HasLeader C H <= (8 - 1) * n ^ H

theorem c4K2EnvelopeUniformMassAt_of_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (H : Nat)
    (hLeaf : C4C5SharedBirthWordMassAt hpsi h2 ring H) :
    C4K2EnvelopeUniformMassObligationAt hpsi h2 ring H := by
  unfold C4K2EnvelopeUniformMassObligationAt
  intro C0 lineage _hA _hClear hAlive
  dsimp only
  apply hLeaf
  exact aliveAlong_end_v2
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    FinalLeaderless C0 lineage hAlive

theorem b7ComposedMass_of_sharedBirthWordMassAt
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (H : Nat)
    (hLeaf : C4C5SharedBirthWordMassAt hpsi h2 ring H) :
    B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True) H 8 := by
  unfold C4C5SharedBirthWordMassAt at hLeaf
  unfold B7ComposedMassObligation
  constructor
  · decide
  · intro C hC
    have h := hLeaf C hC.2
    simpa only [stepConcrete] using h

/-- Same J6 wiring as CFinalAssembly, with only the leaf horizon replaced. -/
def J6C4WitnessToUniformMassV2
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  CFinalAssembly.J5C4FinalCarrierJoin hpsi h2 ring ->
  B6EntranceK2Budget.B6EntranceK2Budget.B6EntranceK2Budget.FrozenC4GateBundle
      hpsi h2 ring ->
  C4K2EnvelopeUniformMassObligationAt
    hpsi h2 ring (FinalLeafHV2 n psi)

/-- Same J7 composition shape, with the V2 C4 and B7 leaf currencies. -/
def J7PassiveAdmissionCompositionV2
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn4 : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor /\
  (ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor ->
    ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring ->
    CFinalAssembly.C2PassiveAdmissionMass hpsi h2 ring ->
    C4K2EnvelopeUniformMassObligationAt
      hpsi h2 ring (FinalLeafHV2 n psi) ->
    B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
      (FinalLeafHV2 n psi) 8)

theorem j6_v2_of_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hLeaf : C4C5SharedBirthWordMassAt
      hpsi h2 ring (FinalLeafHV2 n psi)) :
    J6C4WitnessToUniformMassV2 hpsi h2 ring := by
  unfold J6C4WitnessToUniformMassV2
  intro _hJ5 _hC4
  exact c4K2EnvelopeUniformMassAt_of_sharedBirthWordMass
    hpsi h2 ring (FinalLeafHV2 n psi) hLeaf

theorem j7_v2_of_b4_and_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn4 : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (hB4 : ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor)
    (hLeaf : C4C5SharedBirthWordMassAt
      hpsi h2 ring (FinalLeafHV2 n psi)) :
    J7PassiveAdmissionCompositionV2 hpsi h2 hn4 ring anchor := by
  unfold J7PassiveAdmissionCompositionV2
  refine ⟨hB4, ?_⟩
  intro _hB4 _hClosed _hRecovery _hC4
  exact b7ComposedMass_of_sharedBirthWordMassAt
    hpsi h2 ring (FinalLeafHV2 n psi) hLeaf


theorem uniformLeaf_of_b7ComposedMass_v2
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (H : Nat)
    (hMass : B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True) H 8) :
    BirthLeaderlessBirthMassB7Generic.UniformFirstHitBirthMass
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless H := by
  unfold BirthLeaderlessBirthMassB7Generic.UniformFirstHitBirthMass
    BirthLeaderlessBirthMassRenewal.UniformEscapeMass
  intro C hL
  rw [B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
    (kappa := psi) (tau := 16 * psi) hpsi h2 ring C H]
  exact hMass.2 C ⟨trivial, hL⟩

theorem b7_bound_of_gates_v2
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn4 : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (hC1 : R2CoherenceV31MissionGate.C1CoherenceGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hC2 : B9RecoveryGate.C2RecoveryGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hC4 :
      B6EntranceK2Budget.B6EntranceK2Budget.B6EntranceK2Budget.FrozenC4GateBundle
        hpsi h2 ring)
    (hJ1 : CFinalAssembly.J1C1FinalCarrierJoin hpsi h2 ring)
    (hJ2 : CFinalAssembly.J2C1AdmissionLanding hpsi h2 ring)
    (hJ3 : CFinalAssembly.J3C2FinalCarrierJoin hpsi h2 ring)
    (hJ4 : CFinalAssembly.J4C2RecoveryLanding hpsi h2 ring)
    (hJ5 : CFinalAssembly.J5C4FinalCarrierJoin hpsi h2 ring)
    (hJ6 : J6C4WitnessToUniformMassV2 hpsi h2 ring)
    (hJ7 : J7PassiveAdmissionCompositionV2 hpsi h2 hn4 ring anchor) :
    FinalB7OneOverN hpsi h2 ring (FinalLeafHV2 n psi) := by
  have hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring :=
    hJ2 hJ1 hC1
  have hRecovery : CFinalAssembly.C2PassiveAdmissionMass hpsi h2 ring :=
    hJ4 hJ3 hC2
  have hK2Mass := hJ6 hJ5 hC4
  rcases hJ7 with ⟨hB4, hCompose⟩
  have hMass : B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
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

theorem b7_bound_of_gates_v2_of_producers
    (hpsi : 0 < psi) (h2 : 2 <= psi) (h3 : 2 < psi)
    (hpsin : psi <= n) (hn4 : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (hC1 : R2CoherenceV31MissionGate.C1CoherenceGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hC2 : B9RecoveryGate.C2RecoveryGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hC4 :
      B6EntranceK2Budget.B6EntranceK2Budget.B6EntranceK2Budget.FrozenC4GateBundle
        hpsi h2 ring)
    (hSim : C4C5FinalR1MassSimulation hpsi h2 ring)
    (hB4 : ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor)
    (hJ1 : CFinalAssembly.J1C1FinalCarrierJoin hpsi h2 ring)
    (hJ2 : CFinalAssembly.J2C1AdmissionLanding hpsi h2 ring)
    (hJ3 : CFinalAssembly.J3C2FinalCarrierJoin hpsi h2 ring)
    (hJ4 : CFinalAssembly.J4C2RecoveryLanding hpsi h2 ring)
    (hJ5 : CFinalAssembly.J5C4FinalCarrierJoin hpsi h2 ring) :
    FinalB7OneOverN hpsi h2 ring (FinalLeafHV2 n psi) := by
  have hLeaf := sharedBirthWordMassV2_of_frozenC4
    hpsi h2 h3 hpsin ring hC4 hSim
  exact b7_bound_of_gates_v2 hpsi h2 hn4 ring anchor
    hC1 hC2 hC4 hJ1 hJ2 hJ3 hJ4 hJ5
    (j6_v2_of_sharedBirthWordMass hpsi h2 ring hLeaf)
    (j7_v2_of_b4_and_sharedBirthWordMass
      hpsi h2 hn4 ring anchor hB4 hLeaf)

end CFinalAssembly2

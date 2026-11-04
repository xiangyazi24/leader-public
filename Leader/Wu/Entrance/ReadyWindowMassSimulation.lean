import Leader.Wu.Entrance.SharedBirthWordMass
import Leader.Wu.Entrance.CapProgressStatement

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceK2Mass3

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open BirthCheckPermitRepairLeaf BirthCheckChainR1PerBlock
open B6EntranceV2 B6EntranceV3 B6EntranceAdmissionV3
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open B6EntranceK2Mass2

variable {n psi : Nat}


def C5ProgressToReadyWindowMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn4 : 4 ≤ n)
    (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor →
    ∀ C : BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi),
      BirthShortDoneTerminalFirstHit.Leaderless C →
      BirthPhaseWait2BlockProgress.Q *
          avoidCount (step1 hpsi h2 ring)
            BirthShortDoneTerminalFirstHit.Leaderless
            (ReadyWindow ring) C (BirthPhaseWait2BlockProgress.L n) ≤
        (BirthPhaseWait2BlockProgress.Q - 1) *
          n ^ BirthPhaseWait2BlockProgress.L n


/-- Mass-level final-to-R1 simulation.  It also records that final
leaderlessness descends to the bare-R1 projection. -/
def C4C5FinalR1MassSimulation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (H : Nat) (C : FinalCandidateR2C.Config n psi psi (16 * psi)),
    FinalLeaderless C →
      BirthShortDoneTerminalFirstHit.Leaderless (finalBase C) ∧
      aliveCount
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
          FinalLeaderless C H ≤
        aliveCount (step1 hpsi h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless (finalBase C) H


/-- J13 in the exact leaf units consumed by `leaf_of_ready_window_mass`. -/
def R1LeafHorizonFits
    (n psi B₁ Q₁ Q₂ : Nat) : Prop :=
  3 * (Q₁ * Q₂) * (B₁ + 2 * n * (psi - 1)) ≤ 256 * n ^ 2


/-- C5-specialized J13: B₁ is the 6n block and Q₁ is 128. -/
abbrev C4C5LeafHorizonArithmetic
    (n psi Q₂ : Nat) : Prop :=
  R1LeafHorizonFits n psi
    (BirthPhaseWait2BlockProgress.L n)
    BirthPhaseWait2BlockProgress.Q Q₂


/-- Exact missing `b.Valid` component of the current existential C4 bundle. -/
def C4GateBudgetValidity
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (WP : WriterProtected ring psi (Phys psi psi (16 * psi)))
    (b : EntranceBudgets)
    (hlaws : EntranceHostLawsV3b hpsi h2
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q) ring WP b),
    B6EntranceK2Gate.C4K2EnvelopeGate hpsi h2 ring WP b hlaws →
      b.Valid n psi


private theorem uniformEscapeMass_pad {S : Type} {m : Nat}
    (step : S → Fin m → S) (Good : S → Prop)
    (B H Q : Nat) (hBH : B ≤ H)
    (hMass : UniformEscapeMass step Good B Q) :
    UniformEscapeMass step Good H Q := by
  intro x hx
  have hb := hMass x hx
  have hp := alive_pad step Good (H - B) B x
  have hsum : B + (H - B) = H := by omega
  rw [hsum] at hp
  calc
    Q * aliveCount step Good x H
        ≤ Q * (aliveCount step Good x B * m ^ (H - B)) :=
      Nat.mul_le_mul_left Q hp
    _ = (Q * aliveCount step Good x B) * m ^ (H - B) := by
      rw [Nat.mul_assoc]
    _ ≤ ((Q - 1) * m ^ B) * m ^ (H - B) :=
      Nat.mul_le_mul_right _ hb
    _ = (Q - 1) * m ^ H := by
      rw [Nat.mul_assoc, ← Nat.pow_add, hsum]

/-- Once the first-stage ReadyWindow mass, final/R1 mass simulation, and J13
inequality are supplied, the shared final leaf is only wiring plus padding. -/
theorem c4C5SharedBirthWordMass_of_r1ReadyWindowMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (hpsin : psi ≤ n) (ring : DirectedRing n)
    (B₁ Q₁ Q₂ : Nat) (hQ₁ : 1 ≤ Q₁)
    (hQ₂ : (4 * (psi + 1)) ^ (psi - 1) ≤
      3 ^ (psi - 1) * Q₂)
    (hReady : ∀ C : BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi),
      BirthShortDoneTerminalFirstHit.Leaderless C →
      Q₁ * avoidCount (step1 hpsi h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless
          (ReadyWindow ring) C B₁ ≤
        (Q₁ - 1) * n ^ B₁)
    (hSim : C4C5FinalR1MassSimulation hpsi h2 ring)
    (hH : R1LeafHorizonFits n psi B₁ Q₁ Q₂) :
    C4C5SharedBirthWordMass hpsi h2 ring := by
  let H₀ := 3 * (Q₁ * Q₂) * (B₁ + 2 * n * (psi - 1))
  have hR1 : UniformEscapeMass
      (step1 (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
      BirthShortDoneTerminalFirstHit.Leaderless H₀ 8 := by
    dsimp only [H₀]
    exact BirthCheckChainR1PerBlock.leaf_of_ready_window_mass
      (κ := psi) (τ := 16 * psi) hpsi h3 ring hpsin
      B₁ Q₁ Q₂ hQ₁ hQ₂ hReady
  have hFinal₀ : UniformEscapeMass
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless H₀ 8 := by
    intro C hC
    have hs := hSim H₀ C hC
    have hr := hR1 (finalBase C) hs.1
    exact (Nat.mul_le_mul_left 8 hs.2).trans hr
  have hfit : H₀ ≤ 256 * n ^ 2 := by
    unfold R1LeafHorizonFits at hH
    simpa only [H₀] using hH
  have hFinal := uniformEscapeMass_pad
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    FinalLeaderless H₀ (256 * n ^ 2) 8 hfit hFinal₀
  unfold C4C5SharedBirthWordMass
  intro C hC
  have hm := hFinal C hC
  rw [B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
    (kappa := psi) (tau := 16 * psi)
    hpsi h2 ring C (256 * n ^ 2)] at hm
  exact hm


/-- C5-facing wrapper.  The only extra target seam is
`C5ProgressToReadyWindowMass`; the remaining hypotheses are exactly the
final/R1 simulation and J13 arithmetic. -/
theorem c4C5SharedBirthWordMass_of_c5
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (hpsin : psi ≤ n) (hn4 : 4 ≤ n)
    (ring : DirectedRing n) (anchor : Fin n) (Q₂ : Nat)
    (hQ₂ : (4 * (psi + 1)) ^ (psi - 1) ≤
      3 ^ (psi - 1) * Q₂)
    (hC5 : ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor)
    (hBridge : C5ProgressToReadyWindowMass
      hpsi h2 hn4 ring anchor)
    (hSim : C4C5FinalR1MassSimulation hpsi h2 ring)
    (hH : C4C5LeafHorizonArithmetic n psi Q₂) :
    C4C5SharedBirthWordMass hpsi h2 ring := by
  exact c4C5SharedBirthWordMass_of_r1ReadyWindowMass
    hpsi h2 h3 hpsin ring
    (BirthPhaseWait2BlockProgress.L n)
    BirthPhaseWait2BlockProgress.Q Q₂
    (by decide) hQ₂ (hBridge hC5) hSim hH


end B6EntranceK2Mass3

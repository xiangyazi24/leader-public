import Leader.Wu.Splice.RecoveryGate

set_option autoImplicit false
set_option Elab.async false

namespace B9RecoveryJ4Internal

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi kappa tau : Nat}

/-- Exact remaining content of internal J4 at its frozen C2 constants:
among the length-`RecoveryB n = 6*n` words, at least one prefix history
hits `HasLeader`.  The recovery-mass premise is retained because this is the
residual interface demanded by `C2J4RecoveryToB7Mass`. -/
def RecoveryToLeaderDrain
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : Config n psi kappa tau,
    B9RecoveryGate.C2PassiveLeaderless C →
    B9RecoveryGate.C2FinalRecoveryMass hpsi h2 ring C →
    avoidCount
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
        (fun _ : Config n psi kappa tau => True)
        HasLeader C (B9ControllerRecovery.RecoveryB n) <
      n ^ B9ControllerRecovery.RecoveryB n

/-- The strict one-cylinder loss is exactly sufficient for the gate-internal
J4 mass, because `RecoveryQ n = n ^ RecoveryB n`; alive-count is the same
word count as avoiding `HasLeader`. -/
theorem c2J4RecoveryToB7Mass_of_drain
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hDrain : RecoveryToLeaderDrain
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    B9RecoveryGate.C2J4RecoveryToB7Mass
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  unfold B9RecoveryGate.C2J4RecoveryToB7Mass
  intro C hPassive hRecovery
  have hd := hDrain C hPassive hRecovery
  unfold B9RecoveryGate.C2FinalAliveMass
  dsimp only
  rw [B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
    hpsi h2 ring C (B9ControllerRecovery.RecoveryB n)]
  unfold B9ControllerRecovery.RecoveryQ
  have hle :
      avoidCount
          (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
          (fun _ : Config n psi kappa tau => True)
          HasLeader C (B9ControllerRecovery.RecoveryB n) ≤
        n ^ B9ControllerRecovery.RecoveryB n - 1 := by
    omega
  calc
    n ^ B9ControllerRecovery.RecoveryB n *
        avoidCount
          (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
          (fun _ : Config n psi kappa tau => True)
          HasLeader C (B9ControllerRecovery.RecoveryB n)
        ≤ n ^ B9ControllerRecovery.RecoveryB n *
            (n ^ B9ControllerRecovery.RecoveryB n - 1) :=
      Nat.mul_le_mul_left _ hle
    _ = (n ^ B9ControllerRecovery.RecoveryB n - 1) *
        n ^ B9ControllerRecovery.RecoveryB n := Nat.mul_comm _ _

end B9RecoveryJ4Internal

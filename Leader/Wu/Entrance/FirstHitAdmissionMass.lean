import Leader.Wu.Splice.RecoveryFinalStepMass
import Leader.Wu.Entrance.PassiveAdmission


set_option autoImplicit false


namespace CFinalAdmissionEntrance


open BirthTwoStageEscape
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C


variable {n psi : Nat}


def firstHitToAdmittedPassiveOrLeaderMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (H Q : Nat) : Prop :=
  1 ≤ Q ∧
  ∀ C : Config n psi psi (16 * psi),
    Q * avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (fun _ : Config n psi psi (16 * psi) => True)
        (fun D : Config n psi psi (16 * psi) =>
          HasLeader D ∨ ConcreteB7AdmittedPassive hpsi h2 ring D)
        C H ≤
      (Q - 1) * n ^ H


end CFinalAdmissionEntrance

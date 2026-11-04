import Leader.Wu.Birth.ReacquireReentryMass
import Leader.Wu.Birth.LeaderlessResetFree

set_option autoImplicit false

namespace BirthB1ResetFreeCountMono

open BirthPhaseWait2BlockProgress

variable {n psi kappa tau : Nat}

def CountMonoStep (C D : BirthPhaseWait2BlockProgress.FC n psi kappa tau) : Prop :=
  forall i, (BirthB1ResetFreeControlled.rawAt C i).count <=
    (BirthB1ResetFreeControlled.rawAt D i).count

structure CountFrame (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop where
  step_frame : BirthB1LeaderlessResetFree.StepFrame (kappa := kappa) (tau := tau) hpsi h2 ring
  count_step : forall (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (e : Fin n),
    BirthB1LeaderlessResetFree.Leaderless C ->
      BirthB1LeaderlessResetFree.ResetFree C ->
      CountMonoStep C (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e)


theorem count_mono_along
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (hF : CountFrame (kappa := kappa) (tau := tau) hpsi h2 ring) :
    forall (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (u : List (Fin n)),
      BirthB1LeaderlessResetFree.Leaderless C ->
      BirthB1LeaderlessResetFree.ResetFree C ->
        CountMonoStep C (BirthB1ReacquireReentryMass.prefixEndpoint hpsi h2 ring C u) := by
  intro C u hL hR
  induction u generalizing C with
  | nil =>
      intro i
      exact Nat.le_refl _
  | cons e u ih =>
      have hstep : CountMonoStep C (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) :=
        hF.count_step C e hL hR
      have hD :
          BirthB1LeaderlessResetFree.ResetFree (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) ∧
          BirthB1LeaderlessResetFree.Leaderless (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) :=
        BirthB1LeaderlessResetFree.resetFree_prefix_closed hpsi h2 ring
          hF.step_frame C [e] hL hR
      have htail := ih (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) hD.2 hD.1
      show CountMonoStep C (BirthB1ReacquireReentryMass.prefixEndpoint hpsi h2 ring (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) u)
      intro i
      exact Nat.le_trans (hstep i) (htail i)


def shortCountAt' (ring : DirectedRing n) (anchor : Fin n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) : Nat :=
  (BirthB1ResetFreeControlled.rawAt C (ring.rightNeighbor anchor)).count


theorem shortCountAt_mono_along
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (hF : CountFrame (kappa := kappa) (tau := tau) hpsi h2 ring) (anchor : Fin n) :
    forall (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (u : List (Fin n))
      (hL : BirthB1LeaderlessResetFree.Leaderless C)
      (hR : BirthB1LeaderlessResetFree.ResetFree C),
      shortCountAt' ring anchor
        (BirthB1ReacquireReentryMass.prefixEndpoint hpsi h2 ring C u) >=
      shortCountAt' ring anchor C := by
  intro C u hL hR
  exact count_mono_along hpsi h2 ring hF C u hL hR (ring.rightNeighbor anchor)

end BirthB1ResetFreeCountMono

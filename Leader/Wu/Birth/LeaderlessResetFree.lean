import Leader.Wu.Birth.ResetFreeEntranceMass
import Leader.Wu.Birth.ReacquireReentryMass

namespace BirthB1LeaderlessResetFree

open PPLL
open BirthPhaseWait2BlockProgress
open BirthB1ResetFreeEntranceMass
open BirthB1ReacquireReentryMass

set_option autoImplicit false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

def ResetFree (C : FC n psi kappa tau) : Prop :=
  forall i, (BirthB1ResetFreeControlled.rawAt C i).reset_cmd = false

def Leaderless (C : FC n psi kappa tau) : Prop :=
  forall i, (BirthB1ResetFreeControlled.rawAt C i).leader = false

structure StepFrame
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop where
  resetFree_step : forall (C : FC n psi kappa tau) (e : Fin n),
    Leaderless C -> ResetFree C ->
      ResetFree (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e)
  leaderless_step : forall (C : FC n psi kappa tau) (e : Fin n),
    Leaderless C -> ResetFree C ->
      Leaderless (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e)


theorem resetFree_prefix_closed
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hF : StepFrame (kappa := kappa) (tau := tau) hpsi h2 ring)
    (C : FC n psi kappa tau) (u : List (Fin n))
    (hL : Leaderless C) (hR : ResetFree C) :
    ResetFree (prefixEndpoint hpsi h2 ring C u) /\
      Leaderless (prefixEndpoint hpsi h2 ring C u) := by
  induction u generalizing C with
  | nil =>
      exact ⟨hR, hL⟩
  | cons e u ih =>
      let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e
      have hRD : ResetFree D := hF.resetFree_step C e hL hR
      have hLD : Leaderless D := hF.leaderless_step C e hL hR
      exact ih D hLD hRD

end BirthB1LeaderlessResetFree

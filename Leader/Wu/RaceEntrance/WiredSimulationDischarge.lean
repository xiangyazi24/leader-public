import Leader.Wu.Elimination.LDSinkTwoGapPhysPortSpec

set_option autoImplicit false

open FiniteUniformStoppingTree
open PredictableRenewalOverlap
open PPLLRepair
open LDSinkGapCleanup
open LDTwoGapFrame
open LDSinkTwoGapEpochKernel
open LDSinkTwoGapNoResetKernel
open LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance
open LDSinkTwoGapDeletion
open LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant
open LDSinkTwoGapRestartClosure
open CleanBoundaryDecision
open LDSinkTwoGapWiredInstance
open LDSinkTwoGapPhysPortSpecInstance

namespace WiredSimulationDischarge

variable {n psi : Nat}

theorem secondSupport_gapPair
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (firstGood : AState n psi → Fin n)
    (b : AState n psi)
    (hb : SecondSupport hpsi F firstGood b) :
    GapPair hpsi F b := by
  induction hb with
  | enter a hpair hn =>
      exact gapPair_postState hpsi F a (firstGood a) hpair hn
  | step b e hsupport hn ih =>
      exact gapPair_postState hpsi F b e ih hn

def SecondSuccessEdge
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (firstGood : AState n psi → Fin n) : Prop :=
  ∀ b : AState n psi,
    SecondSupport hpsi F firstGood b →
      ∃ e : Fin n,
        NoResetSuccess F (attemptStepConf hpsi F b e)

noncomputable def secondGoodOf
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (firstGood : AState n psi → Fin n)
    (H : SecondSuccessEdge hpsi F firstGood)
    (b : AState n psi) : Fin n := by
  classical
  exact if h : SecondSupport hpsi F firstGood b then
    Classical.choose (H b h)
  else
    F.attack.pos 0

theorem secondGoodOf_success
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (firstGood : AState n psi → Fin n)
    (H : SecondSuccessEdge hpsi F firstGood)
    (b : AState n psi)
    (hb : SecondSupport hpsi F firstGood b) :
    NoResetSuccess F
      (attemptStepConf hpsi F b
        (secondGoodOf hpsi F firstGood H b)) := by
  classical
  unfold secondGoodOf
  rw [dif_pos hb]
  exact Classical.choose_spec (H b hb)

noncomputable def racePortResidualOfSecondSuccessEdge
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (firstGood : AState n psi → Fin n)
    (H : SecondSuccessEdge hpsi F firstGood) :
    RacePortResidual hpsi F where
  firstGood := firstGood
  secondGood := secondGoodOf hpsi F firstGood H
  success := by
    intro b hb
    exact secondGoodOf_success hpsi F firstGood H b hb

theorem secondSuccessEdge_of_racePortResidual
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : RacePortResidual hpsi F) :
    SecondSuccessEdge hpsi F H.firstGood := by
  intro b hb
  exact ⟨H.secondGood b, H.success b hb⟩

theorem racePortResidual_nonempty_iff
    (hpsi : psi > 0) (F : TwoGapFrame n) :
    Nonempty (RacePortResidual hpsi F) ↔
      ∃ firstGood : AState n psi → Fin n,
        SecondSuccessEdge hpsi F firstGood := by
  constructor
  · intro h
    rcases h with ⟨H⟩
    exact ⟨H.firstGood, secondSuccessEdge_of_racePortResidual hpsi F H⟩
  · intro h
    rcases h with ⟨firstGood, hs⟩
    exact ⟨racePortResidualOfSecondSuccessEdge hpsi F firstGood hs⟩

theorem wired_gapPair_of_secondSuccessEdge
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (firstGood : AState n psi → Fin n)
    (H : SecondSuccessEdge hpsi F firstGood) :
    WiredResidualGapPair hpsi F
      (physD hpsi F
        (physPortSpec hpsi F
          (racePortResidualOfSecondSuccessEdge hpsi F firstGood H)))
      (ready hpsi F)
      (Rel hpsi F
        (physPortSpec hpsi F
          (racePortResidualOfSecondSuccessEdge hpsi F firstGood H))) := by
  exact wired_gapPair_of_racePort hpsi F
    (racePortResidualOfSecondSuccessEdge hpsi F firstGood H)

end WiredSimulationDischarge

#print axioms WiredSimulationDischarge.secondSupport_gapPair
#print axioms WiredSimulationDischarge.secondGoodOf_success
#print axioms WiredSimulationDischarge.secondSuccessEdge_of_racePortResidual
#print axioms WiredSimulationDischarge.racePortResidual_nonempty_iff
#print axioms WiredSimulationDischarge.wired_gapPair_of_secondSuccessEdge

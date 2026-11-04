import Leader.Wu.Elimination.SinkTwoGapRestartClosure

set_option autoImplicit false

open FiniteUniformStoppingTree
open PPLLRepair
open LDSinkGapCleanup
open LDSinkTwoGapEpochDefs
open LDSinkTwoGapAttemptCells
open LDSinkTwoGapAttemptResidual
open LDSinkKernelC
open LDSinkProtectedAbsorption
open LDSinkGapDoneInvariant
open LDSinkGapBlockedPreStep
open LDSinkGapServiceRank
open LDSinkGapCleanupBound
open LDTwoGapFrame
open LDSinkTwoGapEpochKernel
open LDSinkTwoGapEpochSuccessor
open LDSinkTwoGapNoResetKernel
open LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance
open LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant
open LDSinkTwoGapRestartClosure

namespace CleanBoundaryDecision

variable {n psi : Nat}

theorem failure_not_attack_clean
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AState n psi) (e : Fin n)
    (hf : attemptStepRaw hpsi F x e = .failure) :
    ¬ CleanReady F.attack x.conf := by
  intro hClean
  have ha : AbsorbedAt F x.conf (attemptStepConf hpsi F x e) :=
    ((attemptStepRaw_failure_iff hpsi F x e).mp hf).2.2.2
  have hz : (x.conf (F.attack.pos 1)).bullet = (0 : Fin 3) :=
    hClean.2 1 (Nat.le_refl 1)
      (Nat.le_trans (by decide : 1 ≤ 2) F.attack.hd)
  rw [ha.1] at hz
  exact (by decide : (2 : Fin 3) ≠ (0 : Fin 3)) hz

theorem clean_gap_signal_K2
    (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (e : Fin n)
    (hi : GapInvariant hpsi G C)
    (hClean : CleanReady G C) :
    GapSignalBelowBullets G (sinkStepC hpsi G C e) := by
  intro k j hk hkd hbullet hkj hjd
  by_cases ht : Touched G e (G.pos k)
  · exact clean_gap_signal_touched hpsi G C e hi hClean
      k j hk hkd hbullet hkj hjd ht
  · have hneL : G.pos k ≠ e := by
      intro h
      apply ht
      exact Or.inl h
    have hneR : G.pos k ≠ G.ring.rightNeighbor e := by
      intro h
      apply ht
      exact Or.inr h
    have hframe := sinkStepC_other hpsi G C e (G.pos k) hneL hneR
    rw [hframe] at hbullet
    exact (hbullet (hClean.2 k hk hkd)).elim

theorem restartCleanBoundarySignalResidual_K2
    (hpsi : psi > 0) (F : TwoGapFrame n) :
    RestartCleanBoundarySignalResidual hpsi F := by
  refine ⟨?_⟩
  intro x e G hG hPair _hExceptional _hNoSuccess hClean _hNotClean
  have hatt :
      attemptStepConf hpsi F x e = sinkStepC hpsi F.attack x.conf e :=
    attemptStepConf_eq_sinkStepC hpsi F x e
  rcases hG with hG | hG
  · subst G
    have hrec :
        attemptStepConf hpsi F x e =
          sinkStepC hpsi F.recovery x.conf e :=
      hatt.trans (twoGap_sinkStepC_eq hpsi F x.conf e).symm
    rw [hrec]
    exact clean_gap_signal_K2 hpsi F.recovery x.conf e
      hPair.recovery hClean
  · subst G
    rw [hatt]
    exact clean_gap_signal_K2 hpsi F.attack x.conf e
      hPair.attack hClean

end CleanBoundaryDecision

#print axioms CleanBoundaryDecision.failure_not_attack_clean
#print axioms CleanBoundaryDecision.clean_gap_signal_K2
#print axioms CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2

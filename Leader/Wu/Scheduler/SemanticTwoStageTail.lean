import Leader.Wu.Scheduler.SemanticBulletSignalRank
import Leader.Wu.Scheduler.EscapeMassRungs
import Leader.Wu.Scheduler.BellmanRankMass
import Leader.Wu.Birth.LeafBoost

set_option autoImplicit false
set_option Elab.async false

namespace ZZSemanticTwoStage

open PPLLRepair PPLLResearchFormulation
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open IntegratedSemanticMassInventory

variable {n ψ : Nat}

abbrev SemCfg
    (regime : OperationalRegime n ψ) (κ : Nat) :=
  IntegratedSemanticMassInventory.SemCfg regime κ

structure Stage2SafetyRankLaws
    (regime : OperationalRegime n ψ) (κ : Nat)
    (rank : SemCfg regime κ → Nat) (K : Nat) : Prop where
  bound :
    ∀ C : SemCfg regime κ, rank C ≤ K
  nonincrease :
    ∀ (C : SemCfg regime κ) (e : Fin n),
      rank (semStep regime κ C e) ≤ rank C
  descent :
    ∀ C : SemCfg regime κ,
      SemanticBad regime κ C →
      ∃ e : Fin n,
        rank (semStep regime κ C e) < rank C

theorem stage2_rank_row_sum
    (regime : OperationalRegime n ψ) (κ : Nat)
    (rank : SemCfg regime κ → Nat) (K : Nat)
    (laws : Stage2SafetyRankLaws regime κ rank K) :
    ∀ C : SemCfg regime κ,
      SemanticBad regime κ C →
      (List.ofFn (fun e : Fin n =>
        rank (semStep regime κ C e))).sum + 1 ≤
        n * rank C := by
  intro C hC
  exact ZZMassTemplate.rank_row_sum_generic
    (semStep regime κ)
    (SemanticBad regime κ)
    rank
    laws.nonincrease
    laws.descent
    C hC

theorem integratedStage2SafetyMass_of_rank
    (regime : OperationalRegime n ψ) (κ : Nat)
    (R : SemCfg regime κ → Prop)
    (rank : SemCfg regime κ → Nat) (K : Nat)
    (laws : Stage2SafetyRankLaws regime κ rank K) :
    IntegratedStage2SafetyMass
      regime κ R (ZZBellmanTemplate.rankHalfH n K) 2 := by
  unfold IntegratedStage2SafetyMass
  intro C hBad _hR
  have hMass :=
    ZZBellmanTemplate.rank_half_uniformEscapeMass
      (step := semStep regime κ)
      (Bad := SemanticBad regime κ)
      (rank := rank)
      (K := K)
      laws.bound
      laws.nonincrease
      laws.descent
  exact hMass C hBad

def SemanticTwoStageH (n B1 K : Nat) : Nat :=
  B1 + ZZBellmanTemplate.rankHalfH n K

def SemanticBoostedH (n B1 K : Nat) : Nat :=
  3 * (2 * 2) * SemanticTwoStageH n B1 K

theorem integratedSemanticBlockEscape4
    (regime : OperationalRegime n ψ) (κ : Nat)
    (R : SemCfg regime κ → Prop)
    (B1 : Nat)
    (rank : SemCfg regime κ → Nat) (K : Nat)
    (hFirst :
      IntegratedRecoveryFirstHitMass regime κ R B1 2)
    (laws : Stage2SafetyRankLaws regime κ rank K) :
    IntegratedSemanticBlockEscape
      regime κ (SemanticTwoStageH n B1 K) 4 := by
  have hStage2 :=
    integratedStage2SafetyMass_of_rank
      regime κ R rank K laws
  unfold IntegratedRecoveryFirstHitMass at hFirst
  unfold IntegratedStage2SafetyMass at hStage2
  unfold IntegratedSemanticBlockEscape SemanticTwoStageH
  exact BirthTwoStageEscape.two_stage_escape
    (semStep regime κ)
    (SemanticBad regime κ)
    R
    B1
    (ZZBellmanTemplate.rankHalfH n K)
    2 2
    (by omega)
    (by omega)
    hFirst
    hStage2

theorem integratedSemanticBlockEscape8_of_half_and_rank
    (regime : OperationalRegime n ψ) (κ : Nat)
    (R : SemCfg regime κ → Prop)
    (B1 : Nat)
    (rank : SemCfg regime κ → Nat) (K : Nat)
    (hFirst :
      IntegratedRecoveryFirstHitMass regime κ R B1 2)
    (laws : Stage2SafetyRankLaws regime κ rank K) :
    IntegratedSemanticBlockEscape8
      regime κ (SemanticBoostedH n B1 K) := by
  have h4 :=
    integratedSemanticBlockEscape4
      regime κ R B1 rank K hFirst laws
  unfold IntegratedSemanticBlockEscape at h4
  unfold IntegratedSemanticBlockEscape8
    IntegratedSemanticBlockEscape
    SemanticBoostedH SemanticTwoStageH
  exact BirthLeafBoost.escape_boost
    (semStep regime κ)
    (SemanticBad regime κ)
    (B1 + ZZBellmanTemplate.rankHalfH n K)
    4
    (by omega)
    h4

theorem integratedSemantic_tail_one_over_n
    (regime : OperationalRegime n ψ) (κ : Nat)
    (R : SemCfg regime κ → Prop)
    (B1 : Nat)
    (rank : SemCfg regime κ → Nat) (K : Nat)
    (hFirst :
      IntegratedRecoveryFirstHitMass regime κ R B1 2)
    (laws : Stage2SafetyRankLaws regime κ rank K)
    (C : SemCfg regime κ)
    (hC : SemanticBad regime κ C) :
    n * aliveCount
        (semStep regime κ)
        (SemanticBad regime κ) C
        (6 * (Nat.log2 n + 1) *
          SemanticBoostedH n B1 K) ≤
      n ^ (6 * (Nat.log2 n + 1) *
        SemanticBoostedH n B1 K) := by
  have h8 :=
    integratedSemanticBlockEscape8_of_half_and_rank
      regime κ R B1 rank K hFirst laws
  unfold IntegratedSemanticBlockEscape8
    IntegratedSemanticBlockEscape at h8
  have hn : 2 ≤ n := regime.nontrivial
  exact BirthLeaderlessBirthMassRenewal.tail_one_over_n
    (semStep regime κ)
    (SemanticBad regime κ)
    (SemanticBoostedH n B1 K)
    h8 hn C hC

theorem integratedBoundedProtocol_tail_one_over_n
    (regime : OperationalRegime n ψ) (κ : Nat)
    (R : SemCfg regime κ → Prop)
    (B1 : Nat)
    (rank : SemCfg regime κ → Nat) (K : Nat)
    (hFirst :
      IntegratedRecoveryFirstHitMass regime κ R B1 2)
    (laws : Stage2SafetyRankLaws regime κ rank K)
    (C : SemCfg regime κ)
    (hC : SemanticBad regime κ C) :
    n * aliveCount
        ((PPLLRepair.integratedBoundedProtocol
          regime.hψ κ).step regime.ring)
        (SemanticBad regime κ) C
        (6 * (Nat.log2 n + 1) *
          SemanticBoostedH n B1 K) ≤
      n ^ (6 * (Nat.log2 n + 1) *
        SemanticBoostedH n B1 K) := by
  simpa [IntegratedSemanticMassInventory.semStep] using
    (integratedSemantic_tail_one_over_n
      regime κ R B1 rank K hFirst laws C hC)

theorem integratedSemanticBlockEscape8_of_t7_service_and_rank
    (regime : OperationalRegime n ψ) (κ : Nat)
    (rank : SemCfg regime κ → Nat) (K : Nat)
    (hT7 : ZZSemanticT7Rank.ServiceT7Laws regime κ)
    (laws : Stage2SafetyRankLaws regime κ rank K) :
    IntegratedSemanticBlockEscape8 regime κ
      (SemanticBoostedH n
        (ZZBellmanTemplate.rankHalfH n n) K) := by
  have hFirst :=
    ZZSemanticT7Rank.integratedRecoveryFirstHitMass_of_service
      regime κ hT7
  exact integratedSemanticBlockEscape8_of_half_and_rank
    regime κ
    (ZZSemanticRecoveryC.SemanticRepairTarget regime κ)
    (ZZBellmanTemplate.rankHalfH n n)
    rank K hFirst laws

#print axioms ZZSemanticTwoStage.stage2_rank_row_sum
#print axioms ZZSemanticTwoStage.integratedStage2SafetyMass_of_rank
#print axioms ZZSemanticTwoStage.integratedSemanticBlockEscape4
#print axioms ZZSemanticTwoStage.integratedSemanticBlockEscape8_of_half_and_rank
#print axioms ZZSemanticTwoStage.integratedSemantic_tail_one_over_n
#print axioms ZZSemanticTwoStage.integratedBoundedProtocol_tail_one_over_n
#print axioms ZZSemanticTwoStage.integratedSemanticBlockEscape8_of_t7_service_and_rank

end ZZSemanticTwoStage

import Leader.Wu.Scheduler.SemanticBulletSignalRank

set_option autoImplicit false
set_option Elab.async false

namespace ZZH16160

variable {n ψ : Nat}

theorem rankHalfH_self (n : Nat) :
    ZZBellmanTemplate.rankHalfH n n = 2 * (n * n) := by
  rfl

theorem integratedRecoveryFirstHitMass_of_service
    (regime : PPLLResearchFormulation.OperationalRegime n ψ)
    (κ : Nat)
    (laws : ZZSemanticT7Rank.ServiceT7Laws regime κ) :
    IntegratedSemanticMassInventory.IntegratedRecoveryFirstHitMass
      regime κ
      (ZZSemanticRecoveryC.SemanticRepairTarget regime κ)
      (ZZBellmanTemplate.rankHalfH n n) 2 := by
  exact ZZSemanticT7Rank.integratedRecoveryFirstHitMass_of_service
    regime κ laws

theorem semanticRepairTarget_half_first_hit_of_service
    (regime : PPLLResearchFormulation.OperationalRegime n ψ)
    (κ : Nat)
    (laws : ZZSemanticT7Rank.ServiceT7Laws regime κ) :
    ∀ C : IntegratedSemanticMassInventory.SemCfg regime κ,
      2 *
        BirthTwoStageEscape.avoidCount
          (IntegratedSemanticMassInventory.semStep regime κ)
          (fun _ : IntegratedSemanticMassInventory.SemCfg regime κ => True)
          (ZZSemanticRecoveryC.SemanticRepairTarget regime κ)
          C
          (ZZBellmanTemplate.rankHalfH n n)
      ≤ n ^ ZZBellmanTemplate.rankHalfH n n := by
  intro C
  classical
  by_cases hT : ZZSemanticRecoveryC.SemanticRepairTarget regime κ C
  · have hz := BirthTwoStageEscape.avoidCount_zero_of
      (IntegratedSemanticMassInventory.semStep regime κ)
      (fun _ : IntegratedSemanticMassInventory.SemCfg regime κ => True)
      (ZZSemanticRecoveryC.SemanticRepairTarget regime κ)
      C
      (fun h => h.2 hT)
      (ZZBellmanTemplate.rankHalfH n n)
    rw [hz]
    simp
  · have hMono :
        ∀ X e,
          ZZSemanticRecoveryC.semanticRepairRank regime κ
              (IntegratedSemanticMassInventory.semStep regime κ X e) ≤
            ZZSemanticRecoveryC.semanticRepairRank regime κ X := by
      simpa only [ZZSemanticRecoveryC.SemanticRankNonincrease] using
        (ZZSemanticT7Rank.semanticRankNonincrease_of_service
          regime κ laws)
    have hDesc :
        ∀ X,
          ZZSemanticRecoveryC.SemanticRepairBad regime κ X →
          ∃ e : Fin n,
            ZZSemanticRecoveryC.semanticRepairRank regime κ
                (IntegratedSemanticMassInventory.semStep regime κ X e) <
              ZZSemanticRecoveryC.semanticRepairRank regime κ X := by
      simpa only [ZZSemanticRecoveryC.SemanticRankDescent] using
        (ZZSemanticT7Rank.semanticRankDescent_of_service
          regime κ laws)
    have hBad : ZZSemanticRecoveryC.SemanticRepairBad regime κ C := by
      exact hT
    have h := ZZBellmanTemplate.rank_half_avoidCount
      (step := IntegratedSemanticMassInventory.semStep regime κ)
      (Bad := ZZSemanticRecoveryC.SemanticRepairBad regime κ)
      (rank := ZZSemanticRecoveryC.semanticRepairRank regime κ)
      (K := n)
      (hbound := ZZSemanticRecoveryC.semanticRepairRank_le_n regime κ)
      (hmono := hMono)
      (hdesc := hDesc)
      C hBad
    simpa [ZZSemanticRecoveryC.SemanticRepairBad] using h

#print axioms ZZH16160.rankHalfH_self
#print axioms ZZH16160.integratedRecoveryFirstHitMass_of_service
#print axioms ZZH16160.semanticRepairTarget_half_first_hit_of_service

end ZZH16160

import Leader.Wu.Scheduler.SemanticRepairRank
import Leader.Wu.WallSweep.FiniteCleanup

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace ZZSemanticT7Rank

open PPLL PPLLRepair PPLLResearchFormulation
open IntegratedSemanticMassInventory
open ZZSemanticRecoveryC
open FiniteUniformStoppingTree

variable {n ψ κ : Nat}

abbrev SemCfg (regime : OperationalRegime n ψ) (κ : Nat) :=
  ZZSemanticRecoveryC.SemCfg regime κ

/-- The rank is exactly the already-green T7 defect count. -/
noncomputable def rank
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) : Nat :=
  semanticRepairRank regime κ C

/-- Re-export the green K=n bound. -/
theorem rank_le_n
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) :
    rank regime κ C ≤ n := by
  simpa [rank] using semanticRepairRank_le_n regime κ C

/-- Re-export the green zero characterization.  The target expands to
`∀ i, PPLLRepair.LiveBulletSignalExclusive (BoundedAgentState.erase (C i))`. -/
theorem rank_eq_zero_iff_target
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) :
    rank regime κ C = 0 ↔ SemanticRepairTarget regime κ C := by
  simpa [rank] using
    semanticRepairRank_eq_zero_iff_target regime κ C

/-!
The only genuinely protocol-specific local facts needed after the stage audit.
The first is stronger than pair-total nonincrease: a defect cannot be moved
from responder to initiator.  The second says every serviced responder is
T7-clean at the end of the complete integrated raw transition.
-/
structure RawIntegratedT7Laws (hψ : 0 < ψ) (κ : Nat) : Prop where
  initiator_nonincrease :
    ∀ l r : AgentState ψ,
      rawT7DefectBit (ppllIntegratedRepair hψ κ l r).1 ≤
        rawT7DefectBit l
  responder_clean :
    ∀ l r : AgentState ψ,
      LiveBulletSignalExclusive (ppllIntegratedRepair hψ κ l r).2

/-!
This is the configuration-level pointwise form obtained from the raw laws via
`erase_integratedBoundedTransition` and the definition of
`PopulationProtocol.step`.  It is intentionally separated from the sum rank:
once this structure is produced, the rest is pure finite-sum arithmetic.
-/
structure ServiceT7Laws
    (regime : OperationalRegime n ψ) (κ : Nat) : Prop where
  pointwise_nonincrease :
    ∀ (C : SemCfg regime κ) (e i : Fin n),
      t7DefectBit
          (IntegratedSemanticMassInventory.semStep regime κ C e i) ≤
        t7DefectBit (C i)
  responder_clean :
    ∀ (C : SemCfg regime κ) (e : Fin n),
      T7RepairedCell
        (IntegratedSemanticMassInventory.semStep regime κ C e
          (regime.ring.rightNeighbor e))

/-- Pointwise service nonincrease immediately gives rank nonincrease. -/
theorem semanticRankNonincrease_of_service
    (regime : OperationalRegime n ψ) (κ : Nat)
    (laws : ServiceT7Laws regime κ) :
    SemanticRankNonincrease regime κ := by
  unfold SemanticRankNonincrease
  intro C e
  unfold semanticRepairRank
  exact FiniteUniformStoppingTree.ofFn_sum_le _ _
    (fun i => laws.pointwise_nonincrease C e i)

/-- If a T7 defect remains, serve that cell as the responder.  The distinguished
bit goes 1->0 and every other bit is non-increasing, so the global sum drops. -/
theorem semanticRankDescent_of_service
    (regime : OperationalRegime n ψ) (κ : Nat)
    (laws : ServiceT7Laws regime κ) :
    SemanticRankDescent regime κ := by
  unfold SemanticRankDescent
  intro C hBad
  classical
  unfold SemanticRepairBad at hBad
  have hex : ∃ j : Fin n, ¬ T7RepairedCell (C j) := by
    apply Classical.byContradiction
    intro hnone
    apply hBad
    unfold SemanticRepairTarget
    intro i
    apply Classical.byContradiction
    intro hi
    exact hnone ⟨i, hi⟩
  obtain ⟨j, hj⟩ := hex
  let e : Fin n := regime.ring.leftNeighbor j
  have hej : regime.ring.rightNeighbor e = j := by
    simpa [e] using
      (PPLLWallSweepFiniteCleanup.rightNeighbor_leftNeighbor_wall
        regime.ring j)
  have hmono : ∀ i : Fin n,
      t7DefectBit
          (IntegratedSemanticMassInventory.semStep regime κ C e i) ≤
        t7DefectBit (C i) :=
    fun i => laws.pointwise_nonincrease C e i
  have hclean0 := laws.responder_clean C e
  have hclean : T7RepairedCell
      (IntegratedSemanticMassInventory.semStep regime κ C e j) := by
    rw [← hej]
    exact hclean0
  have hnew0 :
      t7DefectBit
          (IntegratedSemanticMassInventory.semStep regime κ C e j) = 0 :=
    (t7DefectBit_eq_zero_iff _).2 hclean
  have holdne : t7DefectBit (C j) ≠ 0 := by
    intro hz
    exact hj ((t7DefectBit_eq_zero_iff (C j)).1 hz)
  have holdpos : 0 < t7DefectBit (C j) := by
    omega
  have hs := B9SpliceTableV10d.ofFn_sum_split
    (fun i : Fin n =>
      t7DefectBit
        (IntegratedSemanticMassInventory.semStep regime κ C e i))
    (fun i : Fin n => t7DefectBit (C i)) j
    (fun i _ => hmono i)
  refine ⟨e, ?_⟩
  unfold semanticRepairRank
  rw [hnew0] at hs
  omega

/-- Both Bellman transition ingredients reduce to `ServiceT7Laws`. -/
theorem semanticRankLaws_of_service
    (regime : OperationalRegime n ψ) (κ : Nat)
    (laws : ServiceT7Laws regime κ) :
    SemanticRankNonincrease regime κ ∧ SemanticRankDescent regime κ := by
  exact ⟨semanticRankNonincrease_of_service regime κ laws,
    semanticRankDescent_of_service regime κ laws⟩

/-- Once the service law is kernelized, the already-green wiring closes
this semantic-recovery first-hit stage with K=n and Q=2. -/
theorem integratedRecoveryFirstHitMass_of_service
    (regime : OperationalRegime n ψ) (κ : Nat)
    (laws : ServiceT7Laws regime κ) :
    IntegratedSemanticMassInventory.IntegratedRecoveryFirstHitMass
      regime κ (SemanticRepairTarget regime κ)
      (ZZBellmanTemplate.rankHalfH n n) 2 := by
  exact ZZSemanticRecoveryC.integratedRecoveryFirstHitMass_of_rank
    regime κ
    (semanticRankNonincrease_of_service regime κ laws)
    (semanticRankDescent_of_service regime κ laws)

/-!
Exact raw substage leaves to prove next.

* `IntegratedBeforeSuppressT7Frame`, `SuppressSigT7Frame`, and
  `WriteSeqT7Frame` are already stated in `ZZSemanticRecoveryC`.
* `NoCollisionT7PairNonincrease` and
  `NoCollisionT7RepairsResponder` are also stated there.

For the global pointwise lift, pair-total nonincrease is slightly weaker than
we want, so expose the branch fact that the initiator itself cannot gain a
T7 defect.  The MOVE transfer branch is the load-bearing case: it writes the
new initiator `signal_B := 0` at the same time it copies the responder bullet.
-/
def NoCollisionT7InitiatorNonincrease (hψ : 0 < ψ) : Prop :=
  ∀ l r : AgentState ψ,
    rawT7DefectBit (eliminateLeadersNoCollision hψ l r).1 ≤
      rawT7DefectBit l

/-- Strong responder form supported by the complete FIRE/MOVE/SIGNAL split. -/
def NoCollisionT7ResponderClean (hψ : 0 < ψ) : Prop :=
  ∀ l r : AgentState ψ,
    LiveBulletSignalExclusive
      (eliminateLeadersNoCollision hψ l r).2

/-!
Source audit:

1. pre-SUPPRESS stages frame bullet/signal_B;
2. SUPPRESS frames bullet/signal_B;
3. Algorithm 15 satisfies the two declarations immediately above;
4. WRITE_SEQ frames bullet/signal_B;
5. bounded reification erases exactly to the raw output;
6. `OperationalRegime.nontrivial` makes scheduler endpoints distinct.

There is therefore no source-level residual family or counterexample branch.
The remaining task is to expose/copy the private frame lemmas and perform the
small FIRE/MOVE/SIGNAL case split that produces `ServiceT7Laws`.
-/

#print axioms ZZSemanticT7Rank.rank_le_n
#print axioms ZZSemanticT7Rank.rank_eq_zero_iff_target
#print axioms ZZSemanticT7Rank.semanticRankNonincrease_of_service
#print axioms ZZSemanticT7Rank.semanticRankDescent_of_service
#print axioms ZZSemanticT7Rank.integratedRecoveryFirstHitMass_of_service

end ZZSemanticT7Rank

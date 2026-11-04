import Leader.Wu.Splice.InstalledRecoveryStep
import Leader.Wu.Birth.InstalledTwoStageSlots

set_option autoImplicit false
set_option Elab.async false

namespace ZZRecoveryFirstHitV3

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceTableHost B9SpliceV10hControllerRowsSafe
open B9ControllerRecovery B9FullCarrierRows B9SpliceTableV10g
open BirthTwoStageEscape
open ZZFinalCarrierV3

variable {n ψ κ τ : Nat}

abbrev V3Cell (ψ κ τ : Nat) := ZZFinalCarrierV3.Cell ψ κ τ
abbrev V3Config (n ψ κ τ : Nat) := ZZFinalCarrierV3.Config n ψ κ τ

/-- `ZZStage2Leaf.stepV3` is definitionally the exact installed final carrier
step, so the compiled `ZZRecoveryJ3V3B` bridge retypes directly. -/
theorem stepV3_oldConfigV3_eq_stepRecover_of_finalGarbage
    (oldHost : HostRow (OldPhys ψ κ τ))
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : V3Config n ψ κ τ) (e : Fin n)
    (hg : FinalGarbageV3 hψ (C e) (C (ring.rightNeighbor e))) :
    oldConfigV3
        (ZZStage2Leaf.stepV3
          (κ := κ) (τ := τ) hψ h2 ring C e) =
      stepRecover oldHost hψ ring (oldConfigV3 C) e := by
  change oldConfigV3
      (stepConcreteV3 (κ := κ) (τ := τ) hψ h2 ring C e) =
    stepRecover oldHost hψ ring (oldConfigV3 C) e
  exact
    ZZRecoveryJ3V3B.stepConcreteV3_oldConfigV3_eq_stepRecover_of_finalGarbage
      (κ := κ) (τ := τ) oldHost hψ h2 ring C e hg

/-- Producer for the declaration recorded as a `Prop` in `ZZStage2Leaf`. -/
theorem v3GarbageProjection
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    ZZStage2Leaf.V3GarbageProjection
      (κ := κ) (τ := τ) hψ h2 ring := by
  unfold ZZStage2Leaf.V3GarbageProjection
  intro oldHost C e hg
  exact stepV3_oldConfigV3_eq_stepRecover_of_finalGarbage
    (κ := κ) (τ := τ) oldHost hψ h2 ring C e hg

/-!
The next four private lemmas are the old-shadow garbage-existence argument.
They are deliberately the same argument as the already compiled
`B9RecoveryJ3Direct` proof.  That file keeps its copies private, so this file
must restate them rather than refer to the private declarations.
-/

private theorem localDanger_iff_at_v3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n ψ κ τ) (e : Fin n) :
    LocalDanger hψ (C e) (C (ring.rightNeighbor e)) ↔
      PreparedDangerAt hψ ring
        (B9SpliceControllerR1TableV6.projectV6 C) e := by
  rfl

private theorem pairCovered_iff_at_v3
    (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n ψ κ τ) (e : Fin n) :
    PairCovered (C e) (C (ring.rightNeighbor e)) ↔
      ProtectedSpliceEdgeV7g ring C e := by
  rfl

private theorem safe_of_no_garbage_v3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n ψ κ τ)
    (hN : ∀ e, ¬ Garbage hψ (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7g hψ ring C := by
  classical
  constructor
  · intro e hd
    have hld : LocalDanger hψ (C e) (C (ring.rightNeighbor e)) :=
      (localDanger_iff_at_v3 hψ ring C e).mpr hd
    by_cases hc : PairCovered (C e) (C (ring.rightNeighbor e))
    · exact (pairCovered_iff_at_v3 ring C e).mp hc
    · exact False.elim (hN e (Or.inr ⟨hld, hc⟩))
  · constructor
    · intro i ht
      by_cases hs :
          ReservedFrontHoldGuard (C i).carrier ∨ HostFenceShapeV7 (C i)
      · exact hs
      · exact False.elim (hN i (Or.inl (Or.inl ⟨ht, hs⟩)))
    · intro i hr hp
      by_cases hb :
          ReservedFrontHoldGuard (C (ring.rightNeighbor i)).carrier ∧
            (C (ring.rightNeighbor i)).acquireTicket = false
      · exact hb
      · exact False.elim
          (hN i (Or.inl (Or.inr (Or.inr ⟨⟨hr, hp⟩, hb⟩))))

private theorem garbage_exists_of_not_safe_v3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n ψ κ τ)
    (hS : ¬ SpliceSafeV7g hψ ring C) :
    ∃ e, Garbage hψ (C e) (C (ring.rightNeighbor e)) := by
  classical
  by_cases h : ∃ e, Garbage hψ (C e) (C (ring.rightNeighbor e))
  · exact h
  · exact False.elim (hS (safe_of_no_garbage_v3 hψ ring C
      (fun e hg => h ⟨e, hg⟩)))

/-- Accepted stopped recovery rank, evaluated on the V3 old projection. -/
noncomputable def finalRecoveryRankV3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : V3Config n ψ κ τ) : Nat :=
  recoveryRank hψ ring (oldConfigV3 C)

theorem finalRecoveryRankV3_le
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : V3Config n ψ κ τ) :
    finalRecoveryRankV3 hψ ring C ≤ RecoveryB n := by
  unfold finalRecoveryRankV3
  simpa [RecoveryB] using
    (recoveryRank_le_six_mul hψ ring (oldConfigV3 C))

/-- Outside `RecoveryTargetV3`, choose a garbage edge; the exact installed V3
step projects to `stepRecover` on that edge and strictly lowers the stopped
old recovery rank. -/
theorem finalRecoveryRankV3_descent
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : V3Config n ψ κ τ)
    (hnot : ¬ ZZStage2Leaf.RecoveryTargetV3 hψ ring C) :
    ∃ e : Fin n,
      finalRecoveryRankV3 hψ ring
          (ZZStage2Leaf.stepV3
            (κ := κ) (τ := τ) hψ h2 ring C e) <
        finalRecoveryRankV3 hψ ring C := by
  have hnotOld : ¬ RecoveryTarget hψ ring (oldConfigV3 C) := by
    simpa only [ZZStage2Leaf.RecoveryTargetV3] using hnot
  have hns : ¬ SpliceSafeV7g hψ ring (oldConfigV3 C) :=
    fun hS => hnotOld (Or.inl hS)
  obtain ⟨e, hg⟩ :=
    garbage_exists_of_not_safe_v3 hψ ring (oldConfigV3 C) hns
  have hgF : FinalGarbageV3 hψ
      (C e) (C (ring.rightNeighbor e)) := by
    change Garbage hψ
      ((oldConfigV3 C) e)
      ((oldConfigV3 C) (ring.rightNeighbor e))
    exact hg
  let host := B9Host.r1Host (kappa := κ) (tau := τ) hψ h2
  have hproj := stepV3_oldConfigV3_eq_stepRecover_of_finalGarbage
    (κ := κ) (τ := τ) host hψ h2 ring C e hgF
  have hdrop := recoveryRank_drop_active
    host hψ ring (oldConfigV3 C) e hnotOld hg
  refine ⟨e, ?_⟩
  unfold finalRecoveryRankV3
  rw [hproj]
  exact hdrop

/-- The exact `Good=True` first-hit mass declaration consumed by
`ZZStage2Leaf`. -/
theorem recoveryFirstHitMassV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    ZZStage2Leaf.RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring := by
  unfold ZZStage2Leaf.RecoveryFirstHitMassV3
  intro C
  classical
  let B := RecoveryB n
  have hRank : finalRecoveryRankV3 hψ ring C ≤ B := by
    dsimp only [B]
    exact finalRecoveryRankV3_le hψ ring C
  by_cases hT : ZZStage2Leaf.RecoveryTargetV3 hψ ring C
  · have hz := avoidCount_zero_of
      (ZZStage2Leaf.stepV3
        (κ := κ) (τ := τ) hψ h2 ring)
      (fun _ : V3Config n ψ κ τ => True)
      (ZZStage2Leaf.RecoveryTargetV3 hψ ring)
      C (fun h => h.2 hT) B
    unfold RecoveryQ
    change n ^ B * avoidCount
      (ZZStage2Leaf.stepV3
        (κ := κ) (τ := τ) hψ h2 ring)
      (fun _ : V3Config n ψ κ τ => True)
      (ZZStage2Leaf.RecoveryTargetV3 hψ ring) C B ≤
        (n ^ B - 1) * n ^ B
    rw [hz]
    simp
  · have hlt := B9ControllerRecovery.avoidCount_lt_pow_of_rank_descent
      (ZZStage2Leaf.stepV3
        (κ := κ) (τ := τ) hψ h2 ring)
      (ZZStage2Leaf.RecoveryTargetV3 hψ ring)
      (finalRecoveryRankV3 hψ ring) ring.hn
      (fun X hX => finalRecoveryRankV3_descent
        (κ := κ) (τ := τ) hψ h2 ring X hX)
      B C hRank hT
    have hle : avoidCount
        (ZZStage2Leaf.stepV3
          (κ := κ) (τ := τ) hψ h2 ring)
        (fun _ : V3Config n ψ κ τ => True)
        (ZZStage2Leaf.RecoveryTargetV3 hψ ring) C B ≤ n ^ B - 1 := by
      exact Nat.le_sub_one_of_lt hlt
    unfold RecoveryQ
    change n ^ B * avoidCount
      (ZZStage2Leaf.stepV3
        (κ := κ) (τ := τ) hψ h2 ring)
      (fun _ : V3Config n ψ κ τ => True)
      (ZZStage2Leaf.RecoveryTargetV3 hψ ring) C B ≤
        (n ^ B - 1) * n ^ B
    calc
      n ^ B * avoidCount
          (ZZStage2Leaf.stepV3
            (κ := κ) (τ := τ) hψ h2 ring)
          (fun _ : V3Config n ψ κ τ => True)
          (ZZStage2Leaf.RecoveryTargetV3 hψ ring) C B
          ≤ n ^ B * (n ^ B - 1) := Nat.mul_le_mul_left _ hle
      _ = (n ^ B - 1) * n ^ B := Nat.mul_comm _ _

/-- The already compiled monotonicity wrapper changes only the first-hit Good
predicate from `True` to the exact `B` needed by `two_stage_escape`. -/
theorem recoveryFirstHitMassOnB
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    ZZStage2Leaf.RecoveryFirstHitMassOnB
      (κ := κ) (τ := τ) hψ h2 ring := by
  exact ZZStage2Leaf.recoveryFirstHitMassOnB_of_true
    (κ := κ) (τ := τ) hψ h2 ring
    (recoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring)

end ZZRecoveryFirstHitV3

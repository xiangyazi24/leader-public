import Leader.Wu.Elimination.SinkTwoGapEpochLaws

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
  LDSinkGapBlockedPreStep LDSinkGapCleanupBound LDTwoGapFrame
  LDSinkTwoGapEpochDefs LDSinkTwoGapEpochCost LDSinkTwoGapEpochLaws
  PPLLRepair FiniteUniformStoppingTree
open Classical

namespace LDSinkTwoGapEpochKernel

set_option autoImplicit false

variable {n ψ : Nat}

/-! ## The common physical step -/

/-- `DirectedRing n` has no computational choice: any two witnesses are equal.
This is the same proof pattern already used privately in `LDTwoGapFrame`. -/
private theorem directedRing_eq_kernel (R R' : DirectedRing n) : R = R' := by
  cases R
  cases R'
  rfl

/-- `sinkStepC` depends on a gap frame only through its directed ring. -/
theorem sinkStepC_frame_irrelevant (hψ : ψ > 0)
    (G1 G2 : GapFrame n) (C : Fin n → AgentState ψ) (e : Fin n)
    (hRing : G1.ring = G2.ring) :
    sinkStepC hψ G1 C e = sinkStepC hψ G2 C e := by
  unfold sinkStepC
  rw [hRing]

/-- The two gaps of a `TwoGapFrame` use the same directed ring.  No extra field
is required because `DirectedRing n` itself is unique. -/
theorem twoGap_ring_eq (F : TwoGapFrame n) :
    F.recovery.ring = F.attack.ring :=
  LDTwoGapFrame.TwoGapFrame.same_ring F

/-- Hence the checked C-kernel physical step is literally the same whole-ring
step whether viewed through the recovery or attack frame. -/
theorem twoGap_sinkStepC_eq (hψ : ψ > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ F.recovery C e = sinkStepC hψ F.attack C e :=
  sinkStepC_frame_irrelevant hψ F.recovery F.attack C e (twoGap_ring_eq F)

/-! ## Residual field (3): active-gap projection -/

/-- Complete discharge of `RoundKernelResidual.activeGapProjection`. -/
theorem activeGapProjection (hψ : ψ > 0) (F : TwoGapFrame n) :
    ∀ (x : RoundActive (ψ := ψ) F) (e : Fin n),
      match x.1.phase with
      | .seekK =>
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.attack
              (sinkStepC hψ F.attack x.1.conf e)
      | .transit =>
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.attack
              (sinkStepC hψ F.attack x.1.conf e)
      | .parked =>
          LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.recovery
              (sinkStepC hψ F.recovery x.1.conf e)
      | .resetK =>
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.attack
              (sinkStepC hψ F.attack x.1.conf e)
      | .seekJ =>
          LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.recovery
              (sinkStepC hψ F.recovery x.1.conf e)
      | .favorable => True := by
  intro x e
  have hstep :
      sinkStepC hψ F.attack x.1.conf e =
        sinkStepC hψ F.recovery x.1.conf e :=
    (twoGap_sinkStepC_eq hψ F x.1.conf e).symm
  cases x.1.phase with
  | seekK => rfl
  | transit => rfl
  | parked =>
      simpa only [epochStepConf] using
        congrArg (LDSinkGapServiceRank.gapWC F.recovery) hstep
  | resetK => rfl
  | seekJ =>
      simpa only [epochStepConf] using
        congrArg (LDSinkGapServiceRank.gapWC F.recovery) hstep
  | favorable =>
      exact True.intro

/-! ## Exact CleanReady consequence -/

/-- `CleanReady` makes `GapSignalBelowBullets` vacuous: every bullet in the
sector is zero.  It does not by itself supply the other three invariant
conjuncts. -/
theorem gapSignalBelowBullets_of_cleanReady (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hClean : CleanReady F C) :
    GapSignalBelowBullets F C := by
  intro k j hk hkd hBullet _ _
  exact False.elim (hBullet (hClean.2 k hk hkd))

/-- This states precisely what is missing from `CleanReady` for recovery of the
full invariant: endpoint presence, interior followers, and label alignment. -/
theorem gapInvariant_of_cleanReady_and_shape (hψ : ψ > 0)
    (F : GapFrame n) (C : Fin n → AgentState ψ)
    (hEndpoints : GapEndpointsPresent F C)
    (hFollowers : GapInteriorFollowers F C)
    (hLabels : GapLabelAligned hψ F C)
    (hClean : CleanReady F C) :
    GapInvariant hψ F C := by
  exact ⟨hEndpoints, hFollowers, hLabels,
    gapSignalBelowBullets_of_cleanReady F C hClean⟩

/-! ## Exact Entrance consequence -/

/-- `Entrance` supplies exactly the two gap invariants plus its escrow
disjunction.  The missing direction for `activeEntrance` is a reachability /
carrier theorem showing that every `RoundActive` state is an entrance. -/
theorem entrance_components (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F) (hE : Entrance hψ F x) :
    GapInvariant hψ F.recovery x.conf ∧
      GapInvariant hψ F.attack x.conf ∧
      ((x.conf (F.attack.pos F.attack.d)).signal_B = (1 : Fin 2) ∨
        x.phase = .transit ∨ x.phase = .parked) := by
  exact hE

#print axioms LDSinkTwoGapEpochKernel.sinkStepC_frame_irrelevant
#print axioms LDSinkTwoGapEpochKernel.twoGap_ring_eq
#print axioms LDSinkTwoGapEpochKernel.twoGap_sinkStepC_eq
#print axioms LDSinkTwoGapEpochKernel.activeGapProjection
#print axioms LDSinkTwoGapEpochKernel.gapSignalBelowBullets_of_cleanReady
#print axioms LDSinkTwoGapEpochKernel.gapInvariant_of_cleanReady_and_shape
#print axioms LDSinkTwoGapEpochKernel.entrance_components

end LDSinkTwoGapEpochKernel

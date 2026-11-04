import Leader.Wu.Splice.RiskHoldSelectors

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace B9RiskRefinementPhys8

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open Q11593SpliceControllerDesign
open B9Host B9SpliceTableHost
open B9RiskRefinementPhys3 B9RiskRefinementPhys7

variable {n psi : Nat}

/-- V4 stores completion only on an actual passive C2 configuration and only
on the two row10g hold selectors isolated by Phys7. -/
def C2PassiveHoldCompletion
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : C2Config n psi) : Prop :=
  ∀ e : Fin n, C2HoldSelected hpsi h2 ring C e →
    BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hpsi
      (base (c2OldAt C e))
      (base (c2OldAt C (ring.rightNeighbor e)))

/-- Recovery gate with the completion datum under `C2PassiveLeaderless`.
The three mass currencies are unchanged. -/
def C2RecoveryGateV4
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  B9RiskRefinement2C.HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) hpsi ∧
    ∀ C : C2Config n psi,
      B9RecoveryGate.C2PassiveLeaderless C →
      C2PassiveHoldCompletion hpsi h2 ring C ∧
        B9RecoveryGate.C2FinalRecoveryMass hpsi h2 ring C ∧
        B9RecoveryGate.C2FinalAliveMass hpsi h2 ring C ∧
        B9RecoveryGate.C2FinalHasLeaderAvoidMass hpsi h2 ring C

/-- Compatibility: the old global completion clause specializes to the exact
passive hold edge required by V4. -/
theorem c2PassiveHoldCompletion_of_global
    (hGlobal : B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause)
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : C2Config n psi)
    (hC : B9RecoveryGate.C2PassiveLeaderless C) :
    C2PassiveHoldCompletion hpsi h2 ring C := by
  intro e hs
  have hNot := c2Passive_not_ldc hpsi h2 ring C hC e
  dsimp only at hNot
  have hFacts :
      SpliceProjectionFacts (B9RecoveryGateResiduals.C2R1Host hpsi h2) :=
    r1Host_spliceProjectionFacts
      (kappa := psi) (tau := 16 * psi) hpsi h2
  have hPhys :
      PhysRow (B9RecoveryGateResiduals.C2R1Host hpsi h2)
        (c2OldAt C e) (c2OldAt C (ring.rightNeighbor e))
        (row10gH (B9RecoveryGateResiduals.C2R1Host hpsi h2) hpsi
          (c2OldAt C e) (c2OldAt C (ring.rightNeighbor e))) := by
    change
      Row10gPlainHoldSelected (B9RecoveryGateResiduals.C2R1Host hpsi h2)
          hpsi (c2OldAt C e) (c2OldAt C (ring.rightNeighbor e)) ∨
        Row10gFencedHoldSelected (B9RecoveryGateResiduals.C2R1Host hpsi h2)
          hpsi (c2OldAt C e) (c2OldAt C (ring.rightNeighbor e)) at hs
    rcases hs with hp | hf
    · exact row10g_plainHold_physRow _ hpsi _ _ hp
    · exact row10g_fencedHold_physRow _ hpsi _ _ hf
  have hc := hGlobal
    (psi := psi) (kappa := psi) (tau := 16 * psi) hpsi h2
    (c2OldAt C e) (c2OldAt C (ring.rightNeighbor e))
  dsimp only at hc
  have hd := hc hFacts hNot
  exact (hd.2.1 hPhys).2.2.1

/-- Existing V1 instances remain valid after the API repair. -/
theorem c2RecoveryGateV4_of_v1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hGate : B9RecoveryGate.C2RecoveryGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring) :
    C2RecoveryGateV4 hpsi h2 ring := by
  refine ⟨hGate.1, ?_⟩
  intro C hC
  have hLocal := c2PassiveHoldCompletion_of_global
    hGate.2.1 hpsi h2 ring C hC
  have hm := hGate.2.2 C hC
  exact ⟨hLocal, hm.1, hm.2.1, hm.2.2⟩



open B9RiskRefinementPhys7

variable {n psi : Nat}

/-- This is definitionally the one local clause left by Phys7. -/
theorem physHoldDomainClause_iff_v4_local
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    PhysHoldDomainClause hpsi h2 ring ↔
      ∀ C : C2Config n psi,
        B9RecoveryGate.C2PassiveLeaderless C →
        C2PassiveHoldCompletion hpsi h2 ring C := by
  rfl

/-- New instance wrapper: J3 is proved directly and therefore no longer asks
for a global Phys4 completion witness. -/
theorem c2RecoveryGateV4_of_physHold_and_j4
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hHoldDomain : PhysHoldDomainClause hpsi h2 ring)
    (hJ4 : B9RecoveryGate.C2J4RecoveryToB7Mass
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring) :
    C2RecoveryGateV4 hpsi h2 ring := by
  refine ⟨B9RiskRefinement2D.r1Host_holdRepairControllerProjectionObligation
    (kappa := psi) (tau := 16 * psi) hpsi h2, ?_⟩
  intro C hC
  have hLocal : C2PassiveHoldCompletion hpsi h2 ring C := by
    intro e hs
    exact hHoldDomain C hC e hs
  have hRecovery :
      B9RecoveryGate.C2FinalRecoveryMass hpsi h2 ring C := by
    unfold B9RecoveryGate.C2FinalRecoveryMass
    dsimp only
    exact B9RecoveryJ3Direct.finalRecovery_first_hit_mass_j3
      (κ := psi) (τ := 16 * psi) hpsi h2 ring C
  have hAlive : B9RecoveryGate.C2FinalAliveMass hpsi h2 ring C :=
    hJ4 C hC hRecovery
  have hHas :
      B9RecoveryGate.C2FinalHasLeaderAvoidMass hpsi h2 ring C := by
    unfold B9RecoveryGate.C2FinalAliveMass at hAlive
    unfold B9RecoveryGate.C2FinalHasLeaderAvoidMass
    dsimp only at hAlive ⊢
    rw [← B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
      (kappa := psi) (tau := 16 * psi)
      hpsi h2 ring C (B9ControllerRecovery.RecoveryB n)]
    exact hAlive
  exact ⟨hLocal, hRecovery, hAlive, hHas⟩

/-- Same wrapper when the already-isolated internal J4 drain is the available
input.  Once that drain is supplied by the landed J4 proof, the only argument
left here is `PhysHoldDomainClause`. -/
theorem c2RecoveryGateV4_of_physHold_and_internalDrain
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hHoldDomain : PhysHoldDomainClause hpsi h2 ring)
    (hDrain : B9RecoveryGateResiduals.C2InternalJ4Drain hpsi h2 ring) :
    C2RecoveryGateV4 hpsi h2 ring := by
  exact c2RecoveryGateV4_of_physHold_and_j4 hpsi h2 ring hHoldDomain
    (B9RecoveryGateResiduals.internalJ4Residual_of_drain
      hpsi h2 ring hDrain)


end B9RiskRefinementPhys8

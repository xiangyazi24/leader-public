import Leader.Wu.Epoch.VoterSumTools
import Leader.Wu.Epoch.VoterColorDrift
import Leader.Wu.Epoch.VoterActionTree
import Leader.Wu.Epoch.FilterProtectedPotential
import Leader.Wu.Epoch.FilterProtectedActionTree
import Leader.Wu.Epoch.FilterCubicBlock
import Leader.Wu.Scheduler.EndpointMissTreeSchedulerBridge

/-!
# Exact block amplification for the filtered epoch protocol

The epoch-specific miss tree is definitionally the generic endpoint-failure
tree.  This bridge transports the uniform one-eighth cubic block bound through
exact action-tree concatenation.  At `Nat.log2 n + 1` blocks the final failure
numerator is at most a `1/n` fraction of all scheduler words.
-/

namespace PPLLEpochVoterPolynomialUpper

open PPLLResearchFormulation PPLLProtectedEpochProtocol
  PPLLDerivedEpochRepair PPLLFinalMissTreeAmplification
  PPLLFinalMissTreeSchedulerBridge
open PPLLEpochVoterSumTools

/-- The historical epoch-specific recursion and the generic endpoint-failure
tree count the same scheduler leaves with the same multiplicities. -/
theorem filteredDefinitionOneFinalMissTree_eq_finalMissTree
    {n psi : Nat}
    (hpsi : psi > 0) (kappa : Nat) (ring : DirectedRing n)
    (C : Fin n -> EpochAgentState n psi kappa) (t : Nat) :
    filteredDefinitionOneFinalMissTree hpsi kappa ring C t =
      PPLLFinalMissTreeAmplification.finalMissTree
        ring (ppllEpochFilterTransition hpsi kappa ring.hn)
        (fun D => PopulationProtocol.IsSafe
          (ppllEpochFilterProtocol hpsi kappa ring.hn)
          ring D isLeaderOutput)
        C t := by
  induction t generalizing C with
  | zero => rfl
  | succ t ih =>
      rw [filteredDefinitionOneFinalMissTree,
        PPLLFinalMissTreeAmplification.finalMissTree]
      apply sum_ofFn_eq
      intro e
      exact ih
        (localStep ring
          (ppllEpochFilterTransition hpsi kappa ring.hn) C e)

/-- Repeating the exact cubic one-eighth block `Nat.log2 n + 1` times gives
an exact Definition-1 failure numerator at most `1/n`, from every physical
initial configuration and without an independence assumption. -/
theorem epochFilter_arbitrary_initialization_oneOverN_definitionOne
    {n psi : Nat} (hn2 : 1 < n) (hpsi : psi > 0) (kappa : Nat)
    (ring : DirectedRing n) (C : Fin n -> EpochAgentState n psi kappa) :
    let blockLength := 8 * n ^ 3
    let blocks := n.log2 + 1
    n * filteredDefinitionOneFinalMissTree hpsi kappa ring C
          (blocks * blockLength) <=
      n ^ (blocks * blockLength) := by
  let blockLength := 8 * n ^ 3
  let blocks := n.log2 + 1
  dsimp only
  rw [filteredDefinitionOneFinalMissTree_eq_finalMissTree]
  apply finalMissTree_oneOverN_at_log2Blocks
    ring (ppllEpochFilterTransition hpsi kappa ring.hn)
    (fun D => PopulationProtocol.IsSafe
      (ppllEpochFilterProtocol hpsi kappa ring.hn)
      ring D isLeaderOutput)
    (isSafe_localStepClosed
      (ppllEpochFilterProtocol hpsi kappa ring.hn) ring isLeaderOutput)
    blockLength
  intro D
  rw [← filteredDefinitionOneFinalMissTree_eq_finalMissTree]
  apply filteredDefinitionOne_failure_eighth_at_eight_cubic
    hn2 hpsi kappa ring D blockLength
  dsimp [blockLength]
  omega

/-- The exact endpoint numerator supplies the repository's genuine
prefix-reaching one-over-`n` safety currency at the same positive horizon. -/
theorem epochFilter_uniformOneOverNFailureAtHorizon
    {n psi : Nat} (hn2 : 1 < n) (hpsi : psi > 0) (kappa : Nat)
    (ring : DirectedRing n) :
    let horizon := (n.log2 + 1) * (8 * n ^ 3)
    UniformOneOverNFailureAtHorizon
      (ppllEpochFilterProtocol hpsi kappa ring.hn)
      ring isLeaderOutput 1 horizon := by
  let horizon := (n.log2 + 1) * (8 * n ^ 3)
  dsimp only
  have hhorizon : 0 < horizon := by
    have hn : 0 < n := by omega
    have hblocks : 0 < n.log2 + 1 := by omega
    have hblock : 0 < 8 * n ^ 3 :=
      Nat.mul_pos (by omega) (Nat.pow_pos hn)
    exact Nat.mul_pos hblocks hblock
  apply uniformOneOverNFailureAtHorizon_of_finalMissTree_le
    (ppllEpochFilterProtocol hpsi kappa ring.hn)
    ring isLeaderOutput hn2 horizon hhorizon
  change ∀ C : Fin n → EpochAgentState n psi kappa,
    n * PPLLFinalMissTreeAmplification.finalMissTree
        ring (ppllEpochFilterTransition hpsi kappa ring.hn)
        (fun D : Fin n → EpochAgentState n psi kappa =>
          PopulationProtocol.IsSafe
            (ppllEpochFilterProtocol hpsi kappa ring.hn)
            ring D isLeaderOutput)
        C horizon ≤
      n ^ horizon
  intro C
  rw [← filteredDefinitionOneFinalMissTree_eq_finalMissTree]
  simpa [horizon] using
    epochFilter_arbitrary_initialization_oneOverN_definitionOne
      hn2 hpsi kappa ring C

end PPLLEpochVoterPolynomialUpper

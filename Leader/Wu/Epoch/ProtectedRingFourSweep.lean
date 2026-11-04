import Leader.Wu.Epoch.ProtectedProtocol

/-!
# Exact four-agent entry into the protected epoch

For `n=4`, the deterministic directed-edge sweep `[0,1,2,3]` sends every
arbitrary epoch state into the protected rotation.  This is a genuine
arbitrary-state convergence witness for one fixed ring size; it is not the
claimed scalable P_PLL bound.  The proof symbolically executes four local edge
repairs and checks rotation, edge coverage, and cleanliness—no state-space
enumeration is used.
-/

namespace PPLLProtectedEpochConvergence

open PPLL PPLLResearchFormulation PPLLProtectedEpochProtocol

/-- Shared positivity proof keeps protocol and local-run proof arguments aligned. -/
theorem epochFourPos : 4 > 0 := by omega

/-- Concrete non-self four-agent ring with reducible neighbor arithmetic. -/
abbrev epochRing4 : DirectedRing 4 := ⟨epochFourPos⟩

/-- One full directed edge sweep. -/
def epochSweep4Schedule : DetSchedule 4 := [0, 1, 2, 3]

/-- First edge of the deterministic sweep. -/
def epochSweepAfter1 (C : Fin 4 → EpochAgentState 4 ψ κ) :=
  PopulationProtocol.step (epochProtocol epochFourPos ψ κ) epochRing4 C 0

/-- Second edge of the deterministic sweep. -/
def epochSweepAfter2 (C : Fin 4 → EpochAgentState 4 ψ κ) :=
  PopulationProtocol.step (epochProtocol epochFourPos ψ κ) epochRing4
    (epochSweepAfter1 C) 1

/-- Third edge of the deterministic sweep. -/
def epochSweepAfter3 (C : Fin 4 → EpochAgentState 4 ψ κ) :=
  PopulationProtocol.step (epochProtocol epochFourPos ψ κ) epochRing4
    (epochSweepAfter2 C) 2

/-- Endpoint after the fourth edge of the fixed sweep. -/
def epochSweep4 (C : Fin 4 → EpochAgentState 4 ψ κ) :=
  PopulationProtocol.step (epochProtocol epochFourPos ψ κ) epochRing4
    (epochSweepAfter3 C) 3

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi := i.isLt
  omega

private theorem edge01 : epochRing4.rightNeighbor 0 = 1 := by decide
private theorem edge12 : epochRing4.rightNeighbor 1 = 2 := by decide
private theorem edge23 : epochRing4.rightNeighbor 2 = 3 := by decide
private theorem edge30 : epochRing4.rightNeighbor 3 = 0 := by decide
private theorem fin3_val : (3 : Fin 4).val = 3 := rfl

/-- Every arbitrary four-agent configuration reaches a clean protected slot
rotation after the fixed sweep. -/
theorem epochSweep4_enters_protected
    (C : Fin 4 → EpochAgentState 4 ψ κ) :
    ProtectedEpoch epochFourPos epochRing4 (epochSweep4 C) := by
  refine ⟨(C 0).slot, ?_, ?_, ?_⟩
  · intro i
    rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
      simp [epochSweep4, epochSweepAfter1, epochSweepAfter2,
        epochSweepAfter3, PopulationProtocol.step, epochProtocol,
        epochTransition, sanitizeEpochState, nextSlot,
        edge01, edge12, edge23, edge30, fin3_val]
    all_goals have hs : (C 0).slot.val = 0 ∨ (C 0).slot.val = 1 ∨
        (C 0).slot.val = 2 ∨ (C 0).slot.val = 3 := by omega
    all_goals rcases hs with hs | hs | hs | hs <;> simp_all
  · intro i
    rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
      apply Fin.ext <;>
      simp [epochSweep4, epochSweepAfter1, epochSweepAfter2,
        epochSweepAfter3, PopulationProtocol.step, epochProtocol,
        epochTransition, sanitizeEpochState, nextSlot,
        edge01, edge12, edge23, edge30]
    all_goals have hs : (C 0).slot.val = 0 ∨ (C 0).slot.val = 1 ∨
        (C 0).slot.val = 2 ∨ (C 0).slot.val = 3 := by omega
    all_goals rcases hs with hs | hs | hs | hs <;> simp_all
  · intro i
    rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
      simp [epochSweep4, epochSweepAfter1, epochSweepAfter2,
        epochSweepAfter3, PopulationProtocol.step, epochProtocol,
        epochTransition, EpochClean, sanitizeEpochState_idempotent,
        edge01, edge12, edge23, edge30]

/-- The sweep endpoint is already Definition-1 safe. -/
theorem epochSweep4_isSafe (C : Fin 4 → EpochAgentState 4 ψ κ) :
    PopulationProtocol.IsSafe
      (epochProtocol epochFourPos ψ κ)
      epochRing4 (epochSweep4 C) isLeaderOutput :=
  protectedEpoch_isSafe epochFourPos epochRing4
    (epochSweep4_enters_protected C)

/-- The deterministic sweep endpoint is reachable in the abstract protocol. -/
theorem epochSweep4_reachable (C : Fin 4 → EpochAgentState 4 ψ κ) :
    PopulationProtocol.Reachable
      (epochProtocol epochFourPos ψ κ)
      epochRing4 C (epochSweep4 C) := by
  have h1 : PopulationProtocol.Reachable
      (epochProtocol epochFourPos ψ κ) epochRing4 C (epochSweepAfter1 C) :=
    PopulationProtocol.OneStep.to_reachable ⟨0, rfl⟩
  have h2 : PopulationProtocol.Reachable
      (epochProtocol epochFourPos ψ κ) epochRing4
      (epochSweepAfter1 C) (epochSweepAfter2 C) :=
    PopulationProtocol.OneStep.to_reachable ⟨1, rfl⟩
  have h3 : PopulationProtocol.Reachable
      (epochProtocol epochFourPos ψ κ) epochRing4
      (epochSweepAfter2 C) (epochSweepAfter3 C) :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have h4 : PopulationProtocol.Reachable
      (epochProtocol epochFourPos ψ κ) epochRing4
      (epochSweepAfter3 C) (epochSweep4 C) :=
    PopulationProtocol.OneStep.to_reachable ⟨3, rfl⟩
  exact ((h1.trans h2).trans h3).trans h4

/-- The named scheduler outcome reaches semantic safety at its full prefix. -/
theorem epochSweep4_reachesSafeWithinSchedule
    (C : Fin 4 → EpochAgentState 4 ψ κ) :
    ReachesSafeWithinSchedule (epochProtocol epochFourPos ψ κ)
      epochRing4 isLeaderOutput C epochSweep4Schedule := by
  refine ⟨4, by decide, ?_⟩
  simpa [epochSweep4Schedule, runSchedule, epochSweep4,
    epochSweepAfter1, epochSweepAfter2, epochSweepAfter3]
    using epochSweep4_isSafe C

/-- At least one of the `4^4` uniform length-four outcomes reaches genuine
Definition-1 safety from every initial configuration. -/
theorem epochSweep4_stabilizingScheduleCount_pos
    (C : Fin 4 → EpochAgentState 4 ψ κ) :
    0 < stabilizingScheduleCount (epochProtocol epochFourPos ψ κ)
      epochRing4 isLeaderOutput C 4 := by
  classical
  unfold stabilizingScheduleCount
  apply List.countP_pos_iff.mpr
  refine ⟨epochSweep4Schedule,
    mem_allSchedules_of_length 4 4 epochSweep4Schedule (by decide), ?_⟩
  simp [epochSweep4_reachesSafeWithinSchedule C]

/-- Honest finite uniform phase: one known favorable outcome among 256 gives
failure budget 255 from every four-agent state. -/
theorem epochFour_uniformFiniteHorizon :
    UniformFiniteHorizonSSLE (epochProtocol epochFourPos ψ κ)
      epochRing4 isLeaderOutput 4 255 := by
  intro C
  rw [allSchedules_length]
  have hpos := epochSweep4_stabilizingScheduleCount_pos C
  change 256 ≤ stabilizingScheduleCount (epochProtocol epochFourPos ψ κ)
    epochRing4 isLeaderOutput C 4 + 255
  omega

/-- Fixed-size arbitrary-state convergence witness: every four-agent start has
a reachable Definition-1-safe future after exactly the named four-edge sweep. -/
theorem epochFour_exists_reachable_safe
    (C : Fin 4 → EpochAgentState 4 ψ κ) :
    ∃ C' : Fin 4 → EpochAgentState 4 ψ κ,
      PopulationProtocol.Reachable
        (epochProtocol epochFourPos ψ κ) epochRing4 C C' ∧
      PopulationProtocol.IsSafe
        (epochProtocol epochFourPos ψ κ) epochRing4 C' isLeaderOutput :=
  ⟨epochSweep4 C, epochSweep4_reachable C, epochSweep4_isSafe C⟩

end PPLLProtectedEpochConvergence

import Leader.Wu.Birth.ResetFreeControlled
import Leader.Wu.WallSweep.ClockwiseRetry

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB1ResetCorridorBridge

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
open BirthWaitPassive BirthShortDoneTerminalPassiveR4
  BirthShortDoneTerminalPassiveLocal3
open BirthB1ReacquireReentryMass BirthB1ResetFreeControlled
open PPLLWallSweepFiniteCleanup PPLLWallSweepClockwiseAttempt
open BirthShortDoneTerminalPassiveLocal3Rotation

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

abbrev B1NoActiveDeletion (C : FC n psi kappa tau) : Prop :=
  PPLLWallSweepFiniteCleanup.NoActiveDeletion C

def B1Leaderless (C : FC n psi kappa tau) : Prop :=
  forall i, (rawAt C i).leader = false

private theorem currentStep2_other
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e i = C i := by
  simpa only [BirthPhaseWait2BlockProgress.currentStep2] using
    BirthShortDoneTerminalConsumer.step_other
      hpsi (by decide : 0 < 2) h2 ring C e i hi hj

private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private theorem hn5 : 4 <= 5 := by decide
private def ring5 : DirectedRing 5 := ⟨by decide⟩
private def anchor5 : Fin 5 := 0
private def boundaryEdge5 : Fin 5 := 2

private theorem right0 : ring5.rightNeighbor anchor5 = (1 : Fin 5) := by decide
private theorem right1 :
    ring5.rightNeighbor (ring5.rightNeighbor anchor5) = (2 : Fin 5) := by decide

private def regs (label : Fin 2) (count : Nat) : Registers 2 where
  label := label
  h := false
  carry := false
  reset := false
  count := count
  wait := true
  bit := false
  phase := false
  writer := .none

private def sourceRaw (i : Fin 5) : AgentState 2 :=
  if i = 0 then cell (regs 0 0)
  else if i = 1 then cell (regs 1 1)
  else if i = 2 then cell (regs 0 0)
  else if i = 3 then { cell (regs 1 0) with reset_cmd := true }
  else { cell (regs 0 0) with state := .eliminate_signal, path := .some 0 0 }

private theorem sourceRaw_domain (i : Fin 5) :
    (sourceRaw i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, regs, cell, AgentState.inProtocolDomain]

private def sourcePack (i : Fin 5) : ExpiringAgentState 2 2 0 :=
  ⟨⟨BoundedAgentState.ofDomain (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩
private def sourceC : FC 5 2 2 0 := fun i => sourcePack i

@[simp] private theorem raw_sourceC (i : Fin 5) : raw (sourceC i) = sourceRaw i := by
  simp [sourceC, sourcePack, raw, BoundedAgentState.erase_ofDomain]

private instance instDecidableRowCap2
    (C : FC 5 2 2 0) (e : Fin 5) : Decidable (RowCap2 hpsi2 h2 2 ring5 C e) := by
  unfold RowCap2
  dsimp only
  infer_instance

private instance instDecidableRowPreCap2
    (C : FC 5 2 2 0) (e : Fin 5) : Decidable (RowPreCap2 hpsi2 h2 2 ring5 C e) := by
  unfold RowPreCap2
  infer_instance

private theorem source_count :
    BirthPhaseWait2BlockProgress.shortCountAt ring5 anchor5 sourceC = 1 := by
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  rw [right0]
  change (raw (sourceC (1 : Fin 5))).count = 1
  rw [raw_sourceC]
  rfl

private theorem source_carrier :
    BirthPhaseWait2BlockProgress.Carrier hpsi2 h2 hn5 ring5 anchor5 sourceC := by
  unfold BirthPhaseWait2BlockProgress.Carrier
    BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [anchor5, sourceRaw, regs, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · rw [right0]; simp [sourceRaw, regs, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · rw [right1]; simp [sourceRaw, regs, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · simp [anchor5, sourceRaw, regs, BirthWaitPassive.cell]
    · rw [right0]; simp [sourceRaw, regs, BirthWaitPassive.cell]
    · rw [right1]; simp [sourceRaw, regs, BirthWaitPassive.cell]
  · rw [source_count]
    omega

private theorem source_boundary_preCap :
    RowPreCap2 hpsi2 h2 2 ring5 sourceC boundaryEdge5 := by
  apply of_decide_eq_true
  rfl

private theorem source_boundary :
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow hn5 ring5 anchor5 boundaryEdge5 := by
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow SafeLine3EdgeAt SafeLine3Edge
  decide

private def afterBoundary : FC 5 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring5 sourceC boundaryEdge5

private theorem afterBoundary_site1 : afterBoundary 1 = sourceC 1 := by
  apply currentStep2_other <;> decide
private theorem afterBoundary_site4 : afterBoundary 4 = sourceC 4 := by
  apply currentStep2_other <;> decide
set_option maxRecDepth 131072 in
private theorem afterBoundary_echo2 : (rawAt afterBoundary 2).echo = true := by
  apply of_decide_eq_true
  rfl
private theorem afterBoundary_count :
    BirthPhaseWait2BlockProgress.shortCountAt ring5 anchor5 afterBoundary = 1 := by
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  rw [right0, afterBoundary_site1]
  exact source_count

private theorem afterBoundary_reacquire :
    BirthPhaseWait2BlockProgress.Reacquire hpsi2 h2 hn5 2 0 ring5 anchor5 afterBoundary := by
  refine ⟨⟨sourceC, boundaryEdge5, [], source_carrier,
    source_boundary_preCap, source_boundary, rfl⟩, ?_, ?_⟩
  · intro hlocal
    unfold BirthPhaseWait2BlockProgress.LocalCarrier
      BirthPhaseWait2Transfer.LocalWait2Carrier at hlocal
    have hm := hlocal.pass2.1
    rw [right1] at hm
    unfold Metadata at hm
    have he := congrArg AgentState.echo hm
    change (rawAt afterBoundary (2 : Fin 5)).echo = false at he
    rw [afterBoundary_echo2] at he
    cases he
  · rw [afterBoundary_count]
    omega

set_option maxRecDepth 131072 in
private theorem afterBoundary_leaderless : B1Leaderless afterBoundary := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 131072 in
private theorem afterBoundary_reset_free :
    ResetFreeTrackedTerminal hpsi2 h2 2 ring5 anchor5 afterBoundary := by
  refine ⟨by decide, by decide, ?_⟩
  intro e _
  have hi : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    (unfold TrackedResetZeroingBranch; decide)

private def TrivialControlled (_ : FC 5 2 2 0) : Prop := True

private theorem afterBoundary_active4 :
    deletionActive (afterBoundary 4).core.erase = true := by
  rw [afterBoundary_site4]
  decide

/-- Item 1 counterexample: even reset-free controlled Reacquire need not be deletion-open. -/
theorem resetFreeControlled_reacquire_not_deletion_open :
    B1Leaderless afterBoundary ∧
    BirthPhaseWait2BlockProgress.Reacquire hpsi2 h2 hn5 2 0 ring5 anchor5 afterBoundary ∧
    ResetFreeControlled hpsi2 h2 2 ring5 anchor5 TrivialControlled afterBoundary ∧
    ¬ B1NoActiveDeletion afterBoundary := by
  refine ⟨afterBoundary_leaderless, afterBoundary_reacquire,
    ⟨trivial, afterBoundary_reset_free⟩, ?_⟩
  intro h
  have hbad : (true : Bool) = false := afterBoundary_active4.symm.trans (h 4)
  cases hbad

set_option maxRecDepth 131072 in
/-- The live reset's first clockwise edge is already diverted by deletion priority. -/
theorem reset_corridor_first_edge_closed :
    (rawAt afterBoundary (3 : Fin 5)).reset_cmd = true ∧
    ¬ WallPriorityOpen (afterBoundary 3) (afterBoundary (ring5.rightNeighbor 3)) := by
  decide

/-- `tau` is not a deletion-drain clock: active deletion refreshes its stall. -/
theorem activeDeletion_survives_priority_expiry
    (old out : ExpiringAgentState psi kappa tau)
    (h : deletionActive out.core.erase = true) :
    deletionActive (deletionPriorityExpireOne tau old out).core.erase = true := by
  simpa [deletionPriorityExpireOne, h] using h

/-- The exact extra entrance premise opens every scheduled edge. -/
theorem noActiveDeletion_opens_edge
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (h : B1NoActiveDeletion C) (e : Fin n) :
    WallPriorityOpen (C e) (C (ring.rightNeighbor e)) := by
  exact WallPriorityOpen.of_noActiveDeletion C h ring e

/-- Item 2: exact missing one-edge semantic bridge. -/
def B1ResetFollowerStepAgreement
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall (C : FC n psi kappa tau) (e : Fin n),
    B1NoActiveDeletion C ->
    (rawAt C e).leader = false ->
    (rawAt C e).reset_cmd = true ->
    (rawAt C (ring.rightNeighbor e)).leader = false ->
    let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e
    ResetAwareFollowerGlobalStepFrame hpsi ring C D e

def runB1 (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) :
    FC n psi kappa tau -> List (Fin n) -> FC n psi kappa tau
  | C, [] => C
  | C, e :: es => runB1 hpsi h2 ring
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) es

/-- Item 3a: one stale reset after the item-2 bridge. -/
def B1OneResetDrain
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hpsiLe : psi <= n)
    (ring : DirectedRing n) : Prop :=
  forall (root : Fin n) (C : FC n psi kappa tau),
    B1NoActiveDeletion C -> B1Leaderless C -> (rawAt C root).reset_cmd = true ->
    exists word : List (Fin n), word.length <= 2 * n ∧
      let D := runB1 hpsi h2 ring C word
      B1NoActiveDeletion D ∧ B1Leaderless D ∧
        resetCommandCount D < resetCommandCount C

/-- Item 3b: the all-reset composition target inside the adopted entrance block. -/
def B1AllResetDrainWithinEntrance
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall C : FC n psi kappa tau, B1NoActiveDeletion C -> B1Leaderless C ->
    exists word : List (Fin n), word.length <= 16 * n * n ∧
      let D := runB1 hpsi h2 ring C word
      B1NoActiveDeletion D ∧ B1Leaderless D ∧ resetCommandCount D = 0

theorem resetDrainBudget_fits_entrance (n : Nat) :
    2 * n * n <= 16 * n * n :=
  Nat.mul_le_mul_right n (by omega)

end BirthB1ResetCorridorBridge

#print axioms BirthB1ResetCorridorBridge.resetFreeControlled_reacquire_not_deletion_open
#print axioms BirthB1ResetCorridorBridge.reset_corridor_first_edge_closed
#print axioms BirthB1ResetCorridorBridge.activeDeletion_survives_priority_expiry
#print axioms BirthB1ResetCorridorBridge.noActiveDeletion_opens_edge
#print axioms BirthB1ResetCorridorBridge.resetDrainBudget_fits_entrance

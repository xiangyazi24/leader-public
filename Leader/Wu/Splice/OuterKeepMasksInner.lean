import Std
import Leader.Wu.Splice.InstalledCarrier
import Leader.Wu.Coherence.TokenFreeMixedRowMoves
import Leader.Wu.WriteSeq.WriterProducerRepair

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZOuterKeepMasks

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair WriterProducerRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows
  B9SpliceTableHost B9SpliceTableV10e B9OrphanToFence
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9ControllerRecovery B9SpliceTableV10g
open ZZFinalCarrierV3

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private theorem hn2 : 0 < 2 := by decide
private theorem h22 : 2 ≤ 2 := by decide

private def ring2 : DirectedRing 2 := ⟨hn2⟩

private abbrev Carrier := ZZFinalCarrierV3.P 3 3 48
private abbrev FCell := ZZFinalCarrierV3.Cell 3 3 48

/-- Repository-standard seed-plus-override construction. -/
private def literalFollower (lab : Fin 3) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

/-- Same old physical base, but two different token-free V3.1 marks. -/
private def predPhys : Carrier :=
  ⟨literalFollower 1, ⟨.closing, .none⟩⟩

private def frontPhys : Carrier :=
  ⟨literalFollower 1, ⟨.releasing, .none⟩⟩

/-- P -> F is a legitimate pending-owner seam for the recovery view. -/
private def predCell : FCell :=
  ⟨predPhys, .predecessorArmed, true, false⟩

private def frontCell : FCell :=
  ⟨frontPhys, .front, true, false⟩

/-- The two-site ring is P,F. -/
private def C : ZZFinalCarrierV3.Config 2 3 3 48 :=
  fun i => if i = (0 : Fin 2) then predCell else frontCell

/-- Forget only the *outer* B9 coordinates. -/
private def innerC : R2CoherenceV31.FC 2 3 3 48 :=
  fun i => (C i).phys

@[simp] private theorem ring01 :
    ring2.rightNeighbor (0 : Fin 2) = 1 := by
  rfl

@[simp] private theorem ring10 :
    ring2.rightNeighbor (1 : Fin 2) = 0 := by
  rfl

private theorem ring0_ne :
    ring2.rightNeighbor (0 : Fin 2) ≠ 0 := by
  rw [ring01]
  decide

@[simp] private theorem C0 : C 0 = predCell := by
  simp [C]

@[simp] private theorem C1 : C 1 = frontCell := by
  simp [C]

/-- Core-only replacement for `fin_cases`. -/
private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  obtain ⟨v, hv⟩ := i
  match v, hv with
  | 0, _ => exact Or.inl (Fin.ext rfl)
  | 1, _ => exact Or.inr (Fin.ext rfl)
  | (_ + 2), h => exact absurd h (by omega)

/-- Both directed edges are token-free mixed in the inner V3.1 carrier. -/
theorem all_inner_edges_tokenFreeMixed :
    ZZV31RowEscapesTokenFreeMixed.AllEdgesTokenFreeMixed ring2 innerC := by
  intro e
  rcases fin2_cases e with h0 | h1
  · subst e
    simp [ZZV31RowEscapesTokenFreeMixed.TokenFreeMixedAt,
      innerC, C, predCell, frontCell, predPhys, frontPhys]
  · subst e
    simp [ZZV31RowEscapesTokenFreeMixed.TokenFreeMixedAt,
      innerC, C, predCell, frontCell, predPhys, frontPhys]

/-- The accepted inner theorem says edge 0 really moves. -/
theorem inner_edge0_moves :
    R2CoherenceV31.stepV3 h3 h23 ring2 innerC (0 : Fin 2) ≠ innerC := by
  exact
    ZZV31RowEscapesTokenFreeMixed.stepV3_allEdgesTokenFreeMixed_ne
      h3 h23 ring2 h22 innerC all_inner_edges_tokenFreeMixed (0 : Fin 2)

private def laws : PhysCarrierLaws Carrier 3 3 48 :=
  ZZFinalCarrierV3.carrierLawsV3

private def host : HostRow Carrier :=
  ZZFinalCarrierV3.hostR2CV3 h3 h23

@[simp] private theorem pred_role :
    role (toOld laws predCell).carrier = .predecessorArmed := rfl
@[simp] private theorem pred_pending :
    (toOld laws predCell).carrier.repairPending = true := rfl
@[simp] private theorem pred_ticket :
    (toOld laws predCell).acquireTicket = false := rfl

@[simp] private theorem front_role :
    role (toOld laws frontCell).carrier = .front := rfl
@[simp] private theorem front_pending :
    (toOld laws frontCell).carrier.repairPending = true := rfl
@[simp] private theorem front_ticket :
    (toOld laws frontCell).acquireTicket = false := rfl

@[simp] private theorem pred_old_leader :
    B9Host.leader (toOld laws predCell).carrier.splice.base = false := rfl

@[simp] private theorem pred_stall :
    (laws.stall predCell.phys).val = 48 := rfl

@[simp] private theorem roundtrip (u : FCell) :
    ofOldWith (toOld laws u) u.phys = u := by
  cases u
  rfl

/-- The old row-7 classifier already selects KEEP on P -> F. -/
private theorem row7_action_keep :
    row7ActionP laws host h3 predCell frontCell = .keep := by
  rw [B9FullCarrierHost.row7ActionP.eq_1 laws host h3 predCell frontCell]
  simp [HostFenceShapeV7, ReservedFrontHoldGuard,
    MoveAcquireFrontGuardV6, B9SpliceTableHost.ArmAGuardH, ArmBGuard,
    B9SpliceTableHost.DeleteGuardH, B9SpliceTableHost.PendingHoldGuardH,
    B9SpliceTableHost.PendingAbortGuardH, MoveCommitGuard,
    MoveStopGuardV3, MoveSeekGuardV3, MoveSeekHoldGuardV3,
    PendingOwnerAbortGuardV3]

/-- The KEEP branch also leaves every outer coordinate unchanged. -/
private theorem row7_pair_fixed :
    row7P laws host h3 predCell frontCell = (predCell, frontCell) := by
  unfold B9FullCarrierHost.row7P
  simp only [row7_action_keep]
  rw [B9SpliceTableHost.row7H.eq_1
    (shadowHostAt laws host predCell.phys frontCell.phys)
    h3 (toOld laws predCell) (toOld laws frontCell)]
  simp [HostFenceShapeV7, ReservedFrontHoldGuard,
    MoveAcquireFrontGuardV6, B9SpliceTableHost.ArmAGuardH, ArmBGuard,
    B9SpliceTableHost.DeleteGuardH, B9SpliceTableHost.PendingHoldGuardH,
    B9SpliceTableHost.PendingAbortGuardH, MoveCommitGuard,
    MoveStopGuardV3, MoveSeekGuardV3, MoveSeekHoldGuardV3,
    PendingOwnerAbortGuardV3, pendingOwnerHoldWriteV6]

private theorem not_v8 :
    ¬ RightStalePredecessorHoldGuardV8
      (toOld laws predCell) (toOld laws frontCell) := by
  simp [RightStalePredecessorHoldGuardV8]

private theorem not_v9 :
    ¬ HostFenceBusyFrontGuardV9 h3
      (toOld laws predCell) (toOld laws frontCell) := by
  simp [HostFenceBusyFrontGuardV9, HostFenceShapeV7]

private theorem not_v10b :
    ¬ HostFenceAdvanceGuardV10b h3
      (toOld laws predCell) (toOld laws frontCell) := by
  simp [HostFenceAdvanceGuardV10b, HostFenceShapeV7]

/-- Use the literal nonzero stall; do not decide this semantic guard. -/
private theorem not_zeroRefresh :
    ¬ ZeroRefreshOnlyGuardP laws host h3 predCell frontCell := by
  intro h
  have hz : (laws.stall predCell.phys).val = 0 := h.2.1
  rw [pred_stall] at hz
  omega

private theorem not_orphan_reserved :
    ¬ OrphanReservedFrontGuardV3
      (toOld laws predCell).carrier (toOld laws frontCell).carrier := by
  simp [OrphanReservedFrontGuardV3, ReservedFrontHoldGuard]

private theorem not_orphan_victim :
    ¬ OrphanVictimGuard (toOld laws predCell) (toOld laws frontCell) := by
  simp [OrphanVictimGuard]

private theorem not_owned_pending_victim :
    ¬ OwnedPendingVictimGuard (toOld laws predCell) (toOld laws frontCell) := by
  simp [OwnedPendingVictimGuard]

private theorem not_ownerless_pending_pred :
    ¬ OwnerlessPendingPredGuard (toOld laws predCell) (toOld laws frontCell) := by
  simp [OwnerlessPendingPredGuard]

/-- Same layer-by-layer stutter transport used by the checked J2 probe. -/
private theorem row10dg_fixed :
    row10dgP laws host h3 predCell frontCell = (predCell, frontCell) := by
  simp only [row10dgP, row10dgPlanP, row10cP, row10cPlanP,
    row10bP, row10bPlanP, row9P, row9PlanP, row8P, row8PlanP,
    row10cActionP, row10bActionP, row9ActionP, row8ActionP,
    runPlan, transportPair, planFromRow]
  simp [row7_action_keep, row7_pair_fixed,
    not_v8, not_v9, not_v10b, not_zeroRefresh,
    not_orphan_reserved, not_orphan_victim,
    not_owned_pending_victim, not_ownerless_pending_pred]

/-- This is the decisive constructor: the complete lower pair stutters, and
P's pending predecessor makes row10g choose literal KEEP. -/
private theorem row10g_plan_keep :
    row10gPlanP laws host h3 predCell frontCell =
      ⟨(toOld laws predCell, toOld laws frontCell), .keep⟩ := by
  rw [B9FullCarrierRows.row10gPlanP.eq_1, if_pos row10dg_fixed]
  simp

private theorem row10g_action_keep :
    row10gActionP laws host h3 predCell frontCell = .keep := by
  unfold B9FullCarrierRows.row10gActionP
  rw [row10g_plan_keep]

private theorem row10g_pair_fixed :
    row10gP laws host h3 predCell frontCell = (predCell, frontCell) := by
  unfold B9FullCarrierRows.row10gP
  rw [row10g_plan_keep]
  simp [B9FullCarrierRows.runPlan, B9FullCarrierRows.transportPair]

/-- Top-level deletion detection is impossible because P's physical initiator
is a follower. -/
private theorem no_ldc :
    ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host predCell.phys frontCell.phys)
      (toOld laws predCell).carrier (toOld laws frontCell).carrier := by
  intro h
  unfold B9SpliceTableHost.ldc B9Host.LeftDeletionCandidate at h
  have hl := h.1
  rw [pred_old_leader] at hl
  cases hl

private theorem full_plan_keep :
    fullPlanP laws host h3 predCell frontCell =
      ⟨(toOld laws predCell, toOld laws frontCell), .keep⟩ := by
  rw [B9FullCarrierRows.fullPlanP.eq_1, if_neg no_ldc]
  simp [B9FullCarrierRows.planFromRow,
    row10g_action_keep, row10g_pair_fixed]

private theorem full_action_keep :
    fullActionP laws host h3 predCell frontCell = .keep := by
  unfold B9FullCarrierRows.fullActionP
  rw [full_plan_keep]

private theorem full_pair_fixed :
    fullRowP laws host h3 predCell frontCell = (predCell, frontCell) := by
  unfold B9FullCarrierRows.fullRowP
  rw [full_plan_keep]
  simp [B9FullCarrierRows.runPlan, B9FullCarrierRows.transportPair]

/-- Concrete route-frozen B9 port selects KEEP. -/
theorem concrete_port_action_keep :
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action predCell frontCell = .keep := by
  change fullActionP laws host h3 predCell frontCell = .keep
  exact full_action_keep

/-- And that KEEP returns the entire pair literally unchanged. -/
theorem concrete_port_pair_fixed :
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).row predCell frontCell =
      (predCell, frontCell) := by
  change fullRowP laws host h3 predCell frontCell = (predCell, frontCell)
  exact full_pair_fixed

/-- Recovery does not pre-empt this P -> F seam. -/
theorem pf_noGarbage :
    ¬ ZZFinalCarrierV3.FinalGarbageV3 h3 predCell frontCell := by
  simp [ZZFinalCarrierV3.FinalGarbageV3,
    B9ControllerRecovery.Garbage, B9ControllerRecovery.ScrubGarbage,
    B9ControllerRecovery.Hole, B9ControllerRecovery.PairCovered,
    B9ControllerRecovery.BadTicket, B9ControllerRecovery.BadBacking,
    B9ControllerRecovery.Pending, ZZFinalCarrierV3.oldCellV3,
    B9FullCarrierHost.toOld, B9SpliceControllerR1Table.role,
    ReservedFrontHoldGuard, PendingOwnerHoldShapeV7, HostFenceShapeV7,
    predCell, frontCell]

private theorem final_action_keep :
    ZZFinalCarrierV3.finalActionV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      predCell frontCell = .keep := by
  classical
  unfold ZZFinalCarrierV3.finalActionV3
  rw [if_neg pf_noGarbage, concrete_port_action_keep]

/-- The final local row is therefore exactly the original pair. -/
theorem final_pair_fixed :
    ZZFinalCarrierV3.rowFinalV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      predCell frontCell = (predCell, frontCell) := by
  unfold ZZFinalCarrierV3.rowFinalV3
  rw [final_action_keep]
  exact concrete_port_pair_fixed

/-- CENTRAL WITNESS: the outer installed step stutters at edge 0 even though
its inner V3.1 projection provably moves at that same edge. -/
theorem outer_edge0_fixed :
    ZZFinalCarrierV3.stepConcreteV3
      (κ := 3) (τ := 48) h3 h23 ring2 C (0 : Fin 2) = C := by
  funext i
  unfold ZZFinalCarrierV3.stepConcreteV3 ZZFinalCarrierV3.stepFinalV3
  rw [if_neg ring0_ne]
  rw [ring01, C0, C1, final_pair_fixed]
  unfold B9FullCarrierHost.writeAtP
  by_cases h0 : i = (0 : Fin 2)
  · subst i
    simp [C]
  · by_cases h1 : i = (1 : Fin 2)
    · subst i
      simp [C]
    · simp [h0, h1]

/-- One packaged statement showing the masking, not merely a stuttering row. -/
theorem outer_keep_masks_inner :
    ZZV31RowEscapesTokenFreeMixed.AllEdgesTokenFreeMixed ring2 innerC ∧
    R2CoherenceV31.stepV3 h3 h23 ring2 innerC (0 : Fin 2) ≠ innerC ∧
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action predCell frontCell = .keep ∧
    ZZFinalCarrierV3.stepConcreteV3
      (κ := 3) (τ := 48) h3 h23 ring2 C (0 : Fin 2) = C := by
  exact ⟨all_inner_edges_tokenFreeMixed, inner_edge0_moves,
    concrete_port_action_keep, outer_edge0_fixed⟩

#print axioms ZZOuterKeepMasks.all_inner_edges_tokenFreeMixed
#print axioms ZZOuterKeepMasks.inner_edge0_moves
#print axioms ZZOuterKeepMasks.concrete_port_action_keep
#print axioms ZZOuterKeepMasks.outer_edge0_fixed
#print axioms ZZOuterKeepMasks.outer_keep_masks_inner

end ZZOuterKeepMasks

import Std
import Leader.Wu.Coherence.SealedRowIdentity

set_option autoImplicit false
set_option Elab.async false

namespace ZZFamilyKHH

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

def ring2 : DirectedRing 2 := ZZV31SealedInstalled.ring2

private abbrev Carrier := ZZFinalCarrierV3.P 3 3 48
private abbrev FCell := ZZFinalCarrierV3.Cell 3 3 48

/-- The exact frozen sealed V3.1 physical carrier. -/
def u : Carrier := ZZV31SealedInstalled.inner

/-- H = (.none,false,true). -/
def H : FCell := ⟨u, .none, false, true⟩

/-- F = (.front,true,false). -/
def F : FCell := ⟨u, .front, true, false⟩

/-- S = (.predecessorArmed,false,false). -/
def S : FCell := ⟨u, .predecessorArmed, false, false⟩

/-- HH on the two-ring. -/
def CHH : ZZFinalCarrierV3.Config 2 3 3 48 := fun _ => H

/-- Site 0 = S, site 1 = F. -/
def CSF : ZZFinalCarrierV3.Config 2 3 3 48 :=
  fun i => if i = (0 : Fin 2) then S else F

/-- Site 0 = F, site 1 = S. -/
def CFS : ZZFinalCarrierV3.Config 2 3 3 48 :=
  fun i => if i = (0 : Fin 2) then F else S

private def laws : PhysCarrierLaws Carrier 3 3 48 :=
  ZZFinalCarrierV3.carrierLawsV3

private def host : HostRow Carrier :=
  ZZFinalCarrierV3.hostR2CV3 h3 h23

@[simp] private theorem h_role :
    role (toOld laws H).carrier = .none := rfl

@[simp] private theorem h_pending :
    (toOld laws H).carrier.repairPending = false := rfl

@[simp] private theorem h_ticket :
    (toOld laws H).acquireTicket = true := rfl

@[simp] private theorem h_old_leader :
    B9Host.leader (toOld laws H).carrier.splice.base = false := rfl

@[simp] private theorem h_stall :
    (laws.stall H.phys).val = 48 := rfl

private theorem hostFence :
    HostFenceShapeV7 (toOld laws H) :=
  ⟨h_role, h_pending, h_ticket⟩

private theorem targetClear :
    HostFenceTargetClearV7 (toOld laws H) :=
  ⟨h_role, h_pending⟩

/-- Equal frozen follower labels 0,0 form the prepared barrier required by
the host-fence advance guard. -/
private theorem localBarrier :
    LocalPreparedBarrier h3
      (toOld laws H).carrier (toOld laws H).carrier := by
  decide +kernel

private theorem advanceGuard :
    HostFenceAdvanceGuardV10b h3
      (toOld laws H) (toOld laws H) :=
  ⟨hostFence, localBarrier, targetClear⟩

/-- The V10b writer's old-controller output is exactly S,F. -/
private theorem handoff_old_pair :
    hostFenceHandoffWriteV10b (toOld laws H) (toOld laws H) =
      (toOld laws S, toOld laws F) := by
  rfl

/-- Load-bearing plan fact: HH selects KEEP with plan output S,F. -/
theorem hh_row10b_plan :
    row10bPlanP laws host h3 H H =
      ⟨(toOld laws S, toOld laws F), .keep⟩ := by
  rw [B9FullCarrierRows.row10bPlanP.eq_1 laws host h3 H H]
  rw [if_pos advanceGuard, handoff_old_pair]

private theorem row10b_action_keep :
    row10bActionP laws host h3 H H = .keep := by
  unfold B9FullCarrierRows.row10bActionP
  rw [hh_row10b_plan]

private theorem row10b_pair :
    row10bP laws host h3 H H = (S, F) := by
  unfold B9FullCarrierRows.row10bP
  rw [hh_row10b_plan]
  rfl

/-- V10c cannot replace the handoff by its zero-refresh stutter because the
frozen carrier has stall 48, not 0. -/
private theorem no_zeroRefresh :
    ¬ ZeroRefreshOnlyGuardP laws host h3 H H := by
  intro hz
  unfold ZeroRefreshOnlyGuardP at hz
  dsimp only at hz
  have hs := hz.2.1
  rw [h_stall] at hs
  omega

private theorem row10c_action_keep :
    row10cActionP laws host h3 H H = .keep := by
  unfold B9FullCarrierRows.row10cActionP
  rw [B9FullCarrierRows.row10cPlanP.eq_1 laws host h3 H H]
  rw [if_neg no_zeroRefresh]
  simp only [B9FullCarrierRows.planFromRow]
  exact row10b_action_keep

private theorem row10c_pair :
    row10cP laws host h3 H H = (S, F) := by
  unfold B9FullCarrierRows.row10cP
  rw [B9FullCarrierRows.row10cPlanP.eq_1 laws host h3 H H]
  rw [if_neg no_zeroRefresh]
  rw [row10b_action_keep, row10b_pair]
  rfl

private theorem no_d1 :
    ¬ OrphanReservedFrontGuardV3
      (toOld laws H).carrier (toOld laws H).carrier := by
  decide +kernel

private theorem no_d2 :
    ¬ OrphanVictimGuard (toOld laws H) (toOld laws H) := by
  decide +kernel

private theorem no_d3 :
    ¬ OwnedPendingVictimGuard (toOld laws H) (toOld laws H) := by
  decide +kernel

private theorem no_d4 :
    ¬ OwnerlessPendingPredGuard (toOld laws H) (toOld laws H) := by
  decide +kernel

private theorem dg_action_keep :
    row10dgActionP laws host h3 H H = .keep := by
  unfold B9FullCarrierRows.row10dgActionP
  rw [B9FullCarrierRows.row10dgPlanP.eq_1 laws host h3 H H]
  rw [if_neg no_d1, if_neg no_d2, if_neg no_d3, if_neg no_d4]
  simp only [B9FullCarrierRows.planFromRow]
  exact row10c_action_keep

private theorem dg_pair :
    row10dgP laws host h3 H H = (S, F) := by
  unfold B9FullCarrierRows.row10dgP
  rw [B9FullCarrierRows.row10dgPlanP.eq_1 laws host h3 H H]
  rw [if_neg no_d1, if_neg no_d2, if_neg no_d3, if_neg no_d4]
  rw [row10c_action_keep, row10c_pair]
  rfl

private theorem dg_ne :
    row10dgP laws host h3 H H ≠ (H, H) := by
  rw [dg_pair]
  intro h
  have hr := congrArg (fun q : FCell × FCell => q.1.spliceRole) h
  change SpliceRole.predecessorArmed = SpliceRole.none at hr
  cases hr

private theorem g_action_keep :
    row10gActionP laws host h3 H H = .keep := by
  unfold B9FullCarrierRows.row10gActionP
  rw [B9FullCarrierRows.row10gPlanP.eq_1 laws host h3 H H]
  rw [if_neg dg_ne]
  simp only [B9FullCarrierRows.planFromRow]
  exact dg_action_keep

private theorem g_pair :
    row10gP laws host h3 H H = (S, F) := by
  unfold B9FullCarrierRows.row10gP
  rw [B9FullCarrierRows.row10gPlanP.eq_1 laws host h3 H H]
  rw [if_neg dg_ne]
  rw [dg_action_keep, dg_pair]
  rfl

/-- Top-level deletion detection is impossible because u is a follower. -/
private theorem no_ldc :
    ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host H.phys H.phys)
      (toOld laws H).carrier (toOld laws H).carrier := by
  intro h
  unfold B9SpliceTableHost.ldc B9Host.LeftDeletionCandidate at h
  have hl := h.1
  rw [h_old_leader] at hl
  cases hl

private theorem full_plan_keep :
    fullPlanP laws host h3 H H =
      ⟨(toOld laws S, toOld laws F), .keep⟩ := by
  rw [B9FullCarrierRows.fullPlanP.eq_1, if_neg no_ldc]
  simp [B9FullCarrierRows.planFromRow, g_action_keep, g_pair]

private theorem full_action_keep :
    fullActionP laws host h3 H H = .keep := by
  unfold B9FullCarrierRows.fullActionP
  rw [full_plan_keep]

private theorem full_pair :
    fullRowP laws host h3 H H = (S, F) := by
  unfold B9FullCarrierRows.fullRowP
  rw [full_plan_keep]
  rfl

private theorem pairCovered :
    PairCovered (toOld laws H) (toOld laws H) :=
  Or.inl (Or.inr hostFence)

/-- Recovery does not pre-empt HH. -/
theorem hh_noGarbage :
    ¬ ZZFinalCarrierV3.FinalGarbageV3 h3 H H := by
  change ¬ Garbage h3 (toOld laws H) (toOld laws H)
  intro hg
  rcases hg with hscrub | hhole
  · rcases hscrub with hbadL | hbadR | hback
    · exact hbadL.2 (Or.inr hostFence)
    · exact hbadR.2 (Or.inr hostFence)
    · have hp := hback.1.1
      rw [h_role] at hp
      cases hp
  · exact hhole.2 pairCovered

/-- Concrete route-frozen B9 port selects KEEP on HH. -/
theorem hh_port_action_keep :
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action H H = .keep := by
  change fullActionP laws host h3 H H = .keep
  exact full_action_keep

/-- The KEEP plan writes exactly S,F while preserving the complete phys=u. -/
theorem hh_port_pair :
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).row H H = (S, F) := by
  change fullRowP laws host h3 H H = (S, F)
  exact full_pair

private theorem hh_final_action_keep :
    ZZFinalCarrierV3.finalActionV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      H H = .keep := by
  classical
  unfold ZZFinalCarrierV3.finalActionV3
  rw [if_neg hh_noGarbage, hh_port_action_keep]

private theorem hh_final_pair :
    ZZFinalCarrierV3.rowFinalV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      H H = (S, F) := by
  unfold ZZFinalCarrierV3.rowFinalV3
  rw [hh_final_action_keep]
  exact hh_port_pair

@[simp] theorem ring2_right0 :
    ring2.rightNeighbor (0 : Fin 2) = 1 := by rfl

@[simp] theorem ring2_right1 :
    ring2.rightNeighbor (1 : Fin 2) = 0 := by rfl

private theorem nonself0 :
    ring2.rightNeighbor (0 : Fin 2) ≠ (0 : Fin 2) := by
  rw [ring2_right0]
  decide

private theorem nonself1 :
    ring2.rightNeighbor (1 : Fin 2) ≠ (1 : Fin 2) := by
  rw [ring2_right1]
  decide

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  obtain ⟨v, hv⟩ := i
  match v, hv with
  | 0, _ => exact Or.inl (Fin.ext rfl)
  | 1, _ => exact Or.inr (Fin.ext rfl)
  | (_ + 2), h => exact absurd h (by omega)

/-- First requested kernel row: edge 0 writes S at site 0 and F at site 1. -/
theorem step0_eq_CSF :
    ZZFinalCarrierV3.stepConcreteV3
      (κ := 3) (τ := 48) h3 h23 ring2 CHH (0 : Fin 2) = CSF := by
  unfold ZZFinalCarrierV3.stepConcreteV3 ZZFinalCarrierV3.stepFinalV3
  rw [if_neg nonself0]
  change B9FullCarrierHost.writeAtP ring2 CHH 0
      (ZZFinalCarrierV3.rowFinalV3 h3 h23
        (ZZFinalCarrierV3.concretePortV3
          (κ := 3) (τ := 48) h3 h23) H H) = CSF
  rw [hh_final_pair]
  funext i
  rcases fin2_cases i with rfl | rfl <;> rfl

/-- Second requested kernel row: edge 1 writes S at site 1 and F at site 0. -/
theorem step1_eq_CFS :
    ZZFinalCarrierV3.stepConcreteV3
      (κ := 3) (τ := 48) h3 h23 ring2 CHH (1 : Fin 2) = CFS := by
  unfold ZZFinalCarrierV3.stepConcreteV3 ZZFinalCarrierV3.stepFinalV3
  rw [if_neg nonself1]
  change B9FullCarrierHost.writeAtP ring2 CHH 1
      (ZZFinalCarrierV3.rowFinalV3 h3 h23
        (ZZFinalCarrierV3.concretePortV3
          (κ := 3) (τ := 48) h3 h23) H H) = CFS
  rw [hh_final_pair]
  funext i
  rcases fin2_cases i with rfl | rfl <;> rfl

#print axioms ZZFamilyKHH.step0_eq_CSF
#print axioms ZZFamilyKHH.step1_eq_CFS

end ZZFamilyKHH

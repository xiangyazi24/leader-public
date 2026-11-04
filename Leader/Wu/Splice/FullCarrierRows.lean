import Leader.Wu.Splice.FullCarrierHost
import Leader.Wu.Splice.ControllerRecovery


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9FullCarrierRows


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceV10cLiveness
open B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
open B9SpliceTableHost B9ControllerRecovery


variable {n psi kappa tau width : Nat} {P : Type}


attribute [local irreducible]
  B9FullCarrierHost.row7ActionP B9FullCarrierHost.row7P
  B9SpliceTableHost.row7H B9SpliceTableHost.row8H
  B9SpliceTableHost.row9H B9SpliceTableHost.row10bH
  B9SpliceTableHost.row10cH B9SpliceTableHost.row10dgH
  B9SpliceTableHost.row10gH B9SpliceTableHost.rowB9
  B9SpliceTableHost.stepB9
  B9ControllerRecovery.rowScrubH B9ControllerRecovery.rowRecoverH


abbrev OldPair (psi kappa tau : Nat) :=
  OldCell psi kappa tau × OldCell psi kappa tau


structure RowPlan (psi kappa tau : Nat) where
  out : OldPair psi kappa tau
  action : PhysicalAction


/-- Copy controller coordinates from `q`, but install the full physical action. -/
noncomputable def transportPair
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (q : OldPair psi kappa tau)
    (a : PhysicalAction) : CellP P × CellP P :=
  let hp := host.row l.phys r.phys
  match a with
  | .keep => (ofOldWith q.1 l.phys, ofOldWith q.2 r.phys)
  | .host => (ofOldWith q.1 hp.1, ofOldWith q.2 hp.2)
  | .relabel =>
      (ofOldWith q.1 l.phys,
        ofOldWith q.2 (laws.relabel hpsi l.phys r.phys))


def ActionSpecP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (a : PhysicalAction)
    (w : CellP P × CellP P) : Prop :=
  match a with
  | .keep => w.1.phys = l.phys ∧ w.2.phys = r.phys
  | .host =>
      w.1.phys = (host.row l.phys r.phys).1 ∧
      w.2.phys = (host.row l.phys r.phys).2
  | .relabel =>
      w.1.phys = l.phys ∧
      w.2.phys = laws.relabel hpsi l.phys r.phys


theorem transportPair_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (q : OldPair psi kappa tau)
    (a : PhysicalAction) :
    ActionSpecP laws host hpsi l r a
      (transportPair laws host hpsi l r q a) := by
  unfold ActionSpecP transportPair
  cases a <;> exact ⟨rfl, rfl⟩


def planFromRow
    (laws : PhysCarrierLaws P psi kappa tau)
    (a : PhysicalAction) (w : CellP P × CellP P) :
    RowPlan psi kappa tau :=
  ⟨(toOld laws w.1, toOld laws w.2), a⟩


noncomputable def runPlan
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (p : RowPlan psi kappa tau) :
    CellP P × CellP P :=
  transportPair laws host hpsi l r p.out p.action


theorem runPlan_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (p : RowPlan psi kappa tau) :
    ActionSpecP laws host hpsi l r p.action
      (runPlan laws host hpsi l r p) :=
  transportPair_action_spec laws host hpsi l r p.out p.action


theorem runPlan_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (p : RowPlan psi kappa tau) :
    TriRowP laws host hpsi l r (runPlan laws host hpsi l r p) := by
  have hs := runPlan_action_spec laws host hpsi l r p
  unfold ActionSpecP at hs
  cases ha : p.action with
  | keep =>
      simp only [ha] at hs
      exact Or.inl hs
  | host =>
      simp only [ha] at hs
      exact Or.inr (Or.inl hs)
  | relabel =>
      simp only [ha] at hs
      exact Or.inr (Or.inr hs)


noncomputable def row8PlanP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : RowPlan psi kappa tau := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  exact if RightStalePredecessorHoldGuardV8 lo ro then
    ⟨(lo, ro), .keep⟩
  else
    planFromRow laws (row7ActionP laws host hpsi l r)
      (row7P laws host hpsi l r)


noncomputable def row8ActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction :=
  (row8PlanP laws host hpsi l r).action


noncomputable def row8P
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P :=
  runPlan laws host hpsi l r (row8PlanP laws host hpsi l r)


theorem row8P_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    ActionSpecP laws host hpsi l r
      (row8ActionP laws host hpsi l r)
      (row8P laws host hpsi l r) :=
  runPlan_action_spec laws host hpsi l r (row8PlanP laws host hpsi l r)


theorem row8P_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (row8P laws host hpsi l r) :=
  runPlan_trichotomy laws host hpsi l r (row8PlanP laws host hpsi l r)


noncomputable def row8Port
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := row8ActionP laws host hpsi
  row := row8P laws host hpsi
  physical_spec := by
    intro l r
    have hs := row8P_action_spec laws host hpsi l r
    unfold ActionSpecP at hs
    cases ha : row8ActionP laws host hpsi l r with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs



noncomputable def row9PlanP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : RowPlan psi kappa tau := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  exact if HostFenceBusyFrontGuardV9 hpsi lo ro then
    ⟨hostFenceBusyFrontRepairWriteV9 hpsi lo ro, .relabel⟩
  else
    planFromRow laws (row8ActionP laws host hpsi l r)
      (row8P laws host hpsi l r)


noncomputable def row9ActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction :=
  (row9PlanP laws host hpsi l r).action


noncomputable def row9P
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P :=
  runPlan laws host hpsi l r (row9PlanP laws host hpsi l r)


theorem row9P_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    ActionSpecP laws host hpsi l r
      (row9ActionP laws host hpsi l r)
      (row9P laws host hpsi l r) :=
  runPlan_action_spec laws host hpsi l r (row9PlanP laws host hpsi l r)


theorem row9P_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (row9P laws host hpsi l r) :=
  runPlan_trichotomy laws host hpsi l r (row9PlanP laws host hpsi l r)


noncomputable def row9Port
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := row9ActionP laws host hpsi
  row := row9P laws host hpsi
  physical_spec := by
    intro l r
    have hs := row9P_action_spec laws host hpsi l r
    unfold ActionSpecP at hs
    cases ha : row9ActionP laws host hpsi l r with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs



noncomputable def row10bPlanP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : RowPlan psi kappa tau := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  exact if HostFenceAdvanceGuardV10b hpsi lo ro then
    ⟨hostFenceHandoffWriteV10b lo ro, .keep⟩
  else
    planFromRow laws (row9ActionP laws host hpsi l r)
      (row9P laws host hpsi l r)


noncomputable def row10bActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction :=
  (row10bPlanP laws host hpsi l r).action


noncomputable def row10bP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P :=
  runPlan laws host hpsi l r (row10bPlanP laws host hpsi l r)


theorem row10bP_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    ActionSpecP laws host hpsi l r
      (row10bActionP laws host hpsi l r)
      (row10bP laws host hpsi l r) :=
  runPlan_action_spec laws host hpsi l r (row10bPlanP laws host hpsi l r)


theorem row10bP_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (row10bP laws host hpsi l r) :=
  runPlan_trichotomy laws host hpsi l r (row10bPlanP laws host hpsi l r)


noncomputable def row10bPort
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := row10bActionP laws host hpsi
  row := row10bP laws host hpsi
  physical_spec := by
    intro l r
    have hs := row10bP_action_spec laws host hpsi l r
    unfold ActionSpecP at hs
    cases ha : row10bActionP laws host hpsi l r with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs



/-- V10c's comparison must frame controller coordinates and every extension
coordinate that is not allowed to tick during a stutter. -/
def SameExceptStallP
    (laws : PhysCarrierLaws P psi kappa tau)
    (u v : CellP P) : Prop :=
  laws.sameExceptStall u.phys v.phys ∧
    u.spliceRole = v.spliceRole ∧
    u.repairPending = v.repairPending ∧
    u.acquireTicket = v.acquireTicket

/-- Full-carrier version of `ZeroRefreshOnlyGuardH`.  The prospective old
controller output must be the ordinary-host output, both old stall budgets are
zero, and the complete P outputs differ from the inputs only in stall. -/
noncomputable def ZeroRefreshOnlyGuardP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : Prop :=
  let q := row10bP laws host hpsi l r
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  (toOld laws q.1, toOld laws q.2) = ordinaryHostWriteH oh lo ro ∧
    (laws.stall l.phys).val = 0 ∧
    (laws.stall r.phys).val = 0 ∧
    SameExceptStallP laws q.1 l ∧
    SameExceptStallP laws q.2 r

noncomputable def row10cPlanP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : RowPlan psi kappa tau := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  exact if ZeroRefreshOnlyGuardP laws host hpsi l r then
    ⟨(lo, ro), .keep⟩
  else
    planFromRow laws (row10bActionP laws host hpsi l r)
      (row10bP laws host hpsi l r)

noncomputable def row10cActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction :=
  (row10cPlanP laws host hpsi l r).action

noncomputable def row10cP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P :=
  runPlan laws host hpsi l r (row10cPlanP laws host hpsi l r)

theorem row10cP_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    ActionSpecP laws host hpsi l r
      (row10cActionP laws host hpsi l r)
      (row10cP laws host hpsi l r) :=
  runPlan_action_spec laws host hpsi l r (row10cPlanP laws host hpsi l r)

theorem row10cP_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (row10cP laws host hpsi l r) :=
  runPlan_trichotomy laws host hpsi l r (row10cPlanP laws host hpsi l r)

noncomputable def row10cPort
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := row10cActionP laws host hpsi
  row := row10cP laws host hpsi
  physical_spec := by
    intro l r
    have hs := row10cP_action_spec laws host hpsi l r
    unfold ActionSpecP at hs
    cases ha : row10cActionP laws host hpsi l r with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs


noncomputable def row10dgPlanP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : RowPlan psi kappa tau := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  exact
    if OrphanReservedFrontGuardV3 lo.carrier ro.carrier then
      ⟨(lo, fenceV6 ro), .keep⟩
    else if OrphanVictimGuard lo ro then
      ⟨(lo, clearControlV6 ro), .keep⟩
    else if OwnedPendingVictimGuard lo ro then
      ⟨(fenceV6 lo, fenceV6 ro), .keep⟩
    else if OwnerlessPendingPredGuard lo ro then
      ⟨(fenceV6 lo, settleV6 ro), .keep⟩
    else
      planFromRow laws (row10cActionP laws host hpsi l r)
        (row10cP laws host hpsi l r)

noncomputable def row10dgActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction :=
  (row10dgPlanP laws host hpsi l r).action

noncomputable def row10dgP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P :=
  runPlan laws host hpsi l r (row10dgPlanP laws host hpsi l r)

theorem row10dgP_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    ActionSpecP laws host hpsi l r
      (row10dgActionP laws host hpsi l r)
      (row10dgP laws host hpsi l r) :=
  runPlan_action_spec laws host hpsi l r (row10dgPlanP laws host hpsi l r)

theorem row10dgP_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (row10dgP laws host hpsi l r) :=
  runPlan_trichotomy laws host hpsi l r (row10dgPlanP laws host hpsi l r)

noncomputable def row10dgPort
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := row10dgActionP laws host hpsi
  row := row10dgP laws host hpsi
  physical_spec := by
    intro l r
    have hs := row10dgP_action_spec laws host hpsi l r
    unfold ActionSpecP at hs
    cases ha : row10dgActionP laws host hpsi l r with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs


/-- Full V10g plan.  The test `q = (l,r)` is on the complete P pair, so a
fuel-only host change cannot be mistaken for a controller stutter. -/
noncomputable def row10gPlanP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : RowPlan psi kappa tau := by
  classical
  let q := row10dgP laws host hpsi l r
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  exact
    if q = (l, r) then
      if role lo.carrier = .predecessorArmed ∧
          lo.carrier.repairPending = true then
        ⟨(lo, ro), .keep⟩
      else if VictimRightScrubGuardV6 ro then
        ⟨(lo, clearControlV6 ro), .keep⟩
      else if FrontRightScrubGuardV6 ro then
        ⟨(lo, clearControlV6 ro), .keep⟩
      else if MalformedRightPendingGuardV6 ro then
        ⟨(lo, clearControlV6 ro), .keep⟩
      else if role ro.carrier = .predecessorArmed then
        if ro.carrier.repairPending then
          if ReservedFrontHoldGuard lo.carrier then
            ⟨(lo, settleV6 ro), .keep⟩
          else if LeftScrubGuardV10e lo then
            ⟨(clearControlV6 lo, ro), .keep⟩
          else
            ⟨(lo, ro), .keep⟩
        else
          let q' := physicalHoldH oh lo ro
          ⟨(q'.1, fenceV6 q'.2), .host⟩
      else
        ⟨physicalHoldH oh lo ro, .host⟩
    else
      planFromRow laws (row10dgActionP laws host hpsi l r) q

noncomputable def row10gActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction :=
  (row10gPlanP laws host hpsi l r).action

noncomputable def row10gP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P :=
  runPlan laws host hpsi l r (row10gPlanP laws host hpsi l r)

theorem row10gP_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    ActionSpecP laws host hpsi l r
      (row10gActionP laws host hpsi l r)
      (row10gP laws host hpsi l r) :=
  runPlan_action_spec laws host hpsi l r (row10gPlanP laws host hpsi l r)

theorem row10gP_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (row10gP laws host hpsi l r) :=
  runPlan_trichotomy laws host hpsi l r (row10gPlanP laws host hpsi l r)

noncomputable def row10gPort
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := row10gActionP laws host hpsi
  row := row10gP laws host hpsi
  physical_spec := by
    intro l r
    have hs := row10gP_action_spec laws host hpsi l r
    unfold ActionSpecP at hs
    cases ha : row10gActionP laws host hpsi l r with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs


/-- Complete B9 plan.  Reserved-front hold repair is controller-only; DELETE
is a genuine host action; every other branch inherits V10g's action. -/
noncomputable def fullPlanP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : RowPlan psi kappa tau := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  exact
    if ldc oh lo.carrier ro.carrier then
      if ReservedFrontHoldGuard lo.carrier then
        ⟨B9SpliceTableV10j.holdRepairV10j lo ro, .keep⟩
      else
        ⟨deleteWriteH oh lo ro, .host⟩
    else
      planFromRow laws (row10gActionP laws host hpsi l r)
        (row10gP laws host hpsi l r)

noncomputable def fullActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction :=
  (fullPlanP laws host hpsi l r).action

noncomputable def fullRowP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P :=
  runPlan laws host hpsi l r (fullPlanP laws host hpsi l r)

theorem fullRowP_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    ActionSpecP laws host hpsi l r
      (fullActionP laws host hpsi l r)
      (fullRowP laws host hpsi l r) :=
  runPlan_action_spec laws host hpsi l r (fullPlanP laws host hpsi l r)

theorem fullRowP_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (fullRowP laws host hpsi l r) :=
  runPlan_trichotomy laws host hpsi l r (fullPlanP laws host hpsi l r)

noncomputable def fullRowPort
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := fullActionP laws host hpsi
  row := fullRowP laws host hpsi
  physical_spec := by
    intro l r
    have hs := fullRowP_action_spec laws host hpsi l r
    unfold ActionSpecP at hs
    cases ha : fullActionP laws host hpsi l r with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs


/-- Clear-only recovery plan.  Recovery writes are controller-only and hence
KEEP; the fallback inherits the complete B9 action. -/
noncomputable def rowScrubPlanP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : RowPlan psi kappa tau := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  exact
    if B9ControllerRecovery.BadTicket lo then
      ⟨(clearControlV6 lo, ro), .keep⟩
    else if B9ControllerRecovery.BadTicket ro then
      ⟨(lo, clearControlV6 ro), .keep⟩
    else if B9ControllerRecovery.BadBacking lo ro then
      ⟨(clearControlV6 lo, ro), .keep⟩
    else
      planFromRow laws (fullActionP laws host hpsi l r)
        (fullRowP laws host hpsi l r)

noncomputable def rowScrubActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction :=
  (rowScrubPlanP laws host hpsi l r).action

noncomputable def rowScrubP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P :=
  runPlan laws host hpsi l r (rowScrubPlanP laws host hpsi l r)

theorem rowScrubP_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    ActionSpecP laws host hpsi l r
      (rowScrubActionP laws host hpsi l r)
      (rowScrubP laws host hpsi l r) :=
  runPlan_action_spec laws host hpsi l r (rowScrubPlanP laws host hpsi l r)

theorem rowScrubP_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (rowScrubP laws host hpsi l r) :=
  runPlan_trichotomy laws host hpsi l r (rowScrubPlanP laws host hpsi l r)

noncomputable def rowScrubPort
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := rowScrubActionP laws host hpsi
  row := rowScrubP laws host hpsi
  physical_spec := by
    intro l r
    have hs := rowScrubP_action_spec laws host hpsi l r
    unfold ActionSpecP at hs
    cases ha : rowScrubActionP laws host hpsi l r with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs


/-- Complete controller recovery.  Hole cover is also controller-only. -/
noncomputable def rowRecoverPlanP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : RowPlan psi kappa tau := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  exact
    if B9ControllerRecovery.BadTicket lo then
      ⟨(clearControlV6 lo, ro), .keep⟩
    else if B9ControllerRecovery.BadTicket ro then
      ⟨(lo, clearControlV6 ro), .keep⟩
    else if B9ControllerRecovery.BadBacking lo ro then
      ⟨(clearControlV6 lo, ro), .keep⟩
    else if B9ControllerRecovery.Hole hpsi lo ro then
      ⟨B9ControllerRecovery.coverWrite lo ro, .keep⟩
    else
      planFromRow laws (fullActionP laws host hpsi l r)
        (fullRowP laws host hpsi l r)

noncomputable def rowRecoverActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction :=
  (rowRecoverPlanP laws host hpsi l r).action

noncomputable def rowRecoverP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P :=
  runPlan laws host hpsi l r (rowRecoverPlanP laws host hpsi l r)

theorem rowRecoverP_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    ActionSpecP laws host hpsi l r
      (rowRecoverActionP laws host hpsi l r)
      (rowRecoverP laws host hpsi l r) :=
  runPlan_action_spec laws host hpsi l r (rowRecoverPlanP laws host hpsi l r)

theorem rowRecoverP_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (rowRecoverP laws host hpsi l r) :=
  runPlan_trichotomy laws host hpsi l r (rowRecoverPlanP laws host hpsi l r)

noncomputable def rowRecoverPort
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := rowRecoverActionP laws host hpsi
  row := rowRecoverP laws host hpsi
  physical_spec := by
    intro l r
    have hs := rowRecoverP_action_spec laws host hpsi l r
    unfold ActionSpecP at hs
    cases ha : rowRecoverActionP laws host hpsi l r with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs


attribute [local irreducible]
  row8P row9P row10bP row10cP row10dgP row10gP
  fullRowP rowScrubP rowRecoverP

/-! ## Exact old-carrier regressions: no table unfolding -/

noncomputable def exactOldRowP
    (f : OldCell psi kappa tau -> OldCell psi kappa tau ->
      OldPair psi kappa tau)
    (l r : CellP (OldPhys psi kappa tau)) :
    CellP (OldPhys psi kappa tau) × CellP (OldPhys psi kappa tau) :=
  let q := f (toOld oldLaws l) (toOld oldLaws r)
  (oldToP q.1, oldToP q.2)

theorem exactOldRowP_toOld
    (f : OldCell psi kappa tau -> OldCell psi kappa tau ->
      OldPair psi kappa tau)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (exactOldRowP f l r).1,
      toOld oldLaws (exactOldRowP f l r).2) =
      f (toOld oldLaws l) (toOld oldLaws r) := by
  simp only [exactOldRowP, toOld_oldToP]

noncomputable def row8OldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :=
  exactOldRowP (B9SpliceTableHost.row8H host hpsi)

theorem row8OldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (row8OldP host hpsi l r).1,
      toOld oldLaws (row8OldP host hpsi l r).2) =
      B9SpliceTableHost.row8H host hpsi
        (toOld oldLaws l) (toOld oldLaws r) :=
  exactOldRowP_toOld (B9SpliceTableHost.row8H host hpsi) l r

noncomputable def row9OldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :=
  exactOldRowP (B9SpliceTableHost.row9H host hpsi)

theorem row9OldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (row9OldP host hpsi l r).1,
      toOld oldLaws (row9OldP host hpsi l r).2) =
      B9SpliceTableHost.row9H host hpsi
        (toOld oldLaws l) (toOld oldLaws r) :=
  exactOldRowP_toOld (B9SpliceTableHost.row9H host hpsi) l r

noncomputable def row10bOldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :=
  exactOldRowP (B9SpliceTableHost.row10bH host hpsi)

theorem row10bOldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (row10bOldP host hpsi l r).1,
      toOld oldLaws (row10bOldP host hpsi l r).2) =
      B9SpliceTableHost.row10bH host hpsi
        (toOld oldLaws l) (toOld oldLaws r) :=
  exactOldRowP_toOld (B9SpliceTableHost.row10bH host hpsi) l r

noncomputable def row10cOldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :=
  exactOldRowP (B9SpliceTableHost.row10cH host hpsi)

theorem row10cOldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (row10cOldP host hpsi l r).1,
      toOld oldLaws (row10cOldP host hpsi l r).2) =
      B9SpliceTableHost.row10cH host hpsi
        (toOld oldLaws l) (toOld oldLaws r) :=
  exactOldRowP_toOld (B9SpliceTableHost.row10cH host hpsi) l r

noncomputable def row10dgOldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :=
  exactOldRowP (B9SpliceTableHost.row10dgH host hpsi)

theorem row10dgOldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (row10dgOldP host hpsi l r).1,
      toOld oldLaws (row10dgOldP host hpsi l r).2) =
      B9SpliceTableHost.row10dgH host hpsi
        (toOld oldLaws l) (toOld oldLaws r) :=
  exactOldRowP_toOld (B9SpliceTableHost.row10dgH host hpsi) l r

noncomputable def row10gOldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :=
  exactOldRowP (B9SpliceTableHost.row10gH host hpsi)

theorem row10gOldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (row10gOldP host hpsi l r).1,
      toOld oldLaws (row10gOldP host hpsi l r).2) =
      B9SpliceTableHost.row10gH host hpsi
        (toOld oldLaws l) (toOld oldLaws r) :=
  exactOldRowP_toOld (B9SpliceTableHost.row10gH host hpsi) l r

noncomputable def rowB9OldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :=
  exactOldRowP (B9SpliceTableHost.rowB9 host hpsi)

theorem rowB9OldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (rowB9OldP host hpsi l r).1,
      toOld oldLaws (rowB9OldP host hpsi l r).2) =
      B9SpliceTableHost.rowB9 host hpsi
        (toOld oldLaws l) (toOld oldLaws r) :=
  exactOldRowP_toOld (B9SpliceTableHost.rowB9 host hpsi) l r

noncomputable def rowScrubOldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :=
  exactOldRowP (B9ControllerRecovery.rowScrubH host hpsi)

theorem rowScrubOldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (rowScrubOldP host hpsi l r).1,
      toOld oldLaws (rowScrubOldP host hpsi l r).2) =
      B9ControllerRecovery.rowScrubH host hpsi
        (toOld oldLaws l) (toOld oldLaws r) :=
  exactOldRowP_toOld (B9ControllerRecovery.rowScrubH host hpsi) l r

noncomputable def rowRecoverOldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :=
  exactOldRowP (B9ControllerRecovery.rowRecoverH host hpsi)

theorem rowRecoverOldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (rowRecoverOldP host hpsi l r).1,
      toOld oldLaws (rowRecoverOldP host hpsi l r).2) =
      B9ControllerRecovery.rowRecoverH host hpsi
        (toOld oldLaws l) (toOld oldLaws r) :=
  exactOldRowP_toOld (B9ControllerRecovery.rowRecoverH host hpsi) l r

@[simp] theorem oldToP_phys (u : OldCell psi kappa tau) :
    (oldToP u).phys = B9SpliceTableHost.base u := rfl

@[simp] theorem base_toOld_oldLaws
    (u : CellP (OldPhys psi kappa tau)) :
    B9SpliceTableHost.base (toOld oldLaws u) = u.phys := rfl

/-- Select a tag from the already-proved old physical trichotomy.  This is
used only for the exact old regression port, so no R2 host call is inferred
from erasure equality. -/
noncomputable def oldActionOf
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : OldCell psi kappa tau) (q : OldPair psi kappa tau) :
    PhysicalAction := by
  classical
  exact
    if B9SpliceTableHost.base q.1 = B9SpliceTableHost.base l ∧
        B9SpliceTableHost.base q.2 = B9SpliceTableHost.base r then .keep
    else if B9SpliceTableHost.base q.1 =
          (host.row (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)).1 ∧
        B9SpliceTableHost.base q.2 =
          (host.row (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)).2 then .host
    else .relabel

theorem oldActionOf_spec
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : OldCell psi kappa tau) (q : OldPair psi kappa tau)
    (ht : B9SpliceTableHost.TriRow host hpsi l r q) :
    match oldActionOf host hpsi l r q with
    | .keep =>
        B9SpliceTableHost.base q.1 = B9SpliceTableHost.base l ∧
        B9SpliceTableHost.base q.2 = B9SpliceTableHost.base r
    | .host =>
        B9SpliceTableHost.base q.1 =
          (host.row (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)).1 ∧
        B9SpliceTableHost.base q.2 =
          (host.row (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)).2
    | .relabel =>
        B9SpliceTableHost.base q.1 = B9SpliceTableHost.base l ∧
        B9SpliceTableHost.base q.2 =
          B9SpliceTableHost.relabelCell hpsi
            (B9SpliceTableHost.base l) (B9SpliceTableHost.base r) := by
  classical
  have ht' :
      (B9SpliceTableHost.base q.1 = B9SpliceTableHost.base l ∧
        B9SpliceTableHost.base q.2 = B9SpliceTableHost.base r) ∨
      (B9SpliceTableHost.base q.1 =
          (host.row (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)).1 ∧
        B9SpliceTableHost.base q.2 =
          (host.row (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)).2) ∨
      (B9SpliceTableHost.base q.1 = B9SpliceTableHost.base l ∧
        B9SpliceTableHost.base q.2 =
          B9SpliceTableHost.relabelCell hpsi
            (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)) := by
    simpa only [B9SpliceTableHost.TriRow, B9SpliceTableHost.PhysRow] using ht
  unfold oldActionOf
  by_cases hk :
      B9SpliceTableHost.base q.1 = B9SpliceTableHost.base l ∧
      B9SpliceTableHost.base q.2 = B9SpliceTableHost.base r
  · rw [if_pos hk]
    exact hk
  · rw [if_neg hk]
    by_cases hh :
        B9SpliceTableHost.base q.1 =
            (host.row (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)).1 ∧
        B9SpliceTableHost.base q.2 =
            (host.row (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)).2
    · rw [if_pos hh]
      exact hh
    · rw [if_neg hh]
      rcases ht' with h | h | h
      · exact (hk h).elim
      · exact (hh h).elim
      · exact h

theorem exactOldRowP_action_spec
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (f : OldCell psi kappa tau -> OldCell psi kappa tau ->
      OldPair psi kappa tau)
    (htri : ∀ l r, B9SpliceTableHost.TriRow host hpsi l r (f l r))
    (l r : CellP (OldPhys psi kappa tau)) :
    ActionSpecP oldLaws host hpsi l r
      (oldActionOf host hpsi (toOld oldLaws l) (toOld oldLaws r)
        (f (toOld oldLaws l) (toOld oldLaws r)))
      (exactOldRowP f l r) := by
  let lo := toOld oldLaws l
  let ro := toOld oldLaws r
  let q := f lo ro
  have hs := oldActionOf_spec host hpsi lo ro q (htri lo ro)
  change ActionSpecP oldLaws host hpsi l r
    (oldActionOf host hpsi lo ro q) (exactOldRowP f l r)
  unfold ActionSpecP
  cases ha : oldActionOf host hpsi lo ro q with
  | keep =>
      simp only [ha] at hs ⊢
      simpa only [exactOldRowP, oldToP_phys,
        base_toOld_oldLaws, lo, ro, q] using hs
  | host =>
      simp only [ha] at hs ⊢
      simpa only [exactOldRowP, oldToP_phys,
        base_toOld_oldLaws, lo, ro, q] using hs
  | relabel =>
      simp only [ha] at hs ⊢
      simp only [exactOldRowP, oldToP_phys,
        base_toOld_oldLaws, lo, ro, q] at hs ⊢
      simpa only [oldLaws] using hs


noncomputable def fullRowPort_old
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi) :
    FullRowPort oldLaws host hpsi where
  action := fun l r =>
    let lo := toOld oldLaws l
    let ro := toOld oldLaws r
    let q := B9SpliceTableHost.rowB9 host hpsi lo ro
    oldActionOf host hpsi lo ro q
  row := exactOldRowP (B9SpliceTableHost.rowB9 host hpsi)
  physical_spec := by
    intro l r
    have hs := exactOldRowP_action_spec host hpsi
      (B9SpliceTableHost.rowB9 host hpsi)
      (fun a b => B9SpliceTableHost.rowB9_trichotomy host hpsi a b) l r
    unfold ActionSpecP at hs
    cases ha :
        oldActionOf host hpsi
          (toOld oldLaws l) (toOld oldLaws r)
          (B9SpliceTableHost.rowB9 host hpsi
            (toOld oldLaws l) (toOld oldLaws r)) with
    | keep =>
        simp only [ha] at hs ⊢
        exact hs
    | host =>
        simp only [ha] at hs ⊢
        exact hs
    | relabel =>
        simp only [ha] at hs ⊢
        exact hs


/-- This is the requested old-instance equality: after the representation
isomorphism, `rowB9P` with `fullRowPort_old` is literally accepted `rowB9`. -/
theorem fullRowPort_old_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws
        (B9FullCarrierHost.rowB9P (fullRowPort_old host hpsi) l r).1,
      toOld oldLaws
        (B9FullCarrierHost.rowB9P (fullRowPort_old host hpsi) l r).2) =
      B9SpliceTableHost.rowB9 host hpsi
        (toOld oldLaws l) (toOld oldLaws r) := by
  simpa only [B9FullCarrierHost.rowB9P, fullRowPort_old] using
    (exactOldRowP_toOld (B9SpliceTableHost.rowB9 host hpsi) l r)

/-- Generic fuel theorem for every plan-based R2 row. -/
theorem r2_nonhost_fuel_of_plan
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (p : RowPlan psi kappa tau)
    (ha : p.action ≠ PhysicalAction.host) :
    let q := runPlan r2Laws (r2Host hpsi hwidth hle) hpsi l r p
    q.1.phys.fuel = l.phys.fuel ∧
      q.2.phys.fuel = r.phys.fuel := by
  dsimp only
  have hs := runPlan_action_spec r2Laws
    (r2Host hpsi hwidth hle) hpsi l r p
  unfold ActionSpecP at hs
  cases hact : p.action with
  | keep =>
      simp only [hact] at hs
      exact ⟨
        congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.1,
        congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.2⟩
  | host =>
      exact False.elim (ha hact)
  | relabel =>
      simp only [hact] at hs
      constructor
      · exact congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.1
      · calc
          (runPlan r2Laws (r2Host hpsi hwidth hle) hpsi l r p).2.phys.fuel =
              (r2Laws.relabel hpsi l.phys r.phys).fuel :=
            congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.2
          _ = r.phys.fuel := r2_relabel_fuel hpsi l.phys r.phys

theorem row8P_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row8ActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠ .host) :
    let q := row8P r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  simpa only [row8ActionP, row8P] using
    r2_nonhost_fuel_of_plan hpsi hwidth hle l r
      (row8PlanP r2Laws (r2Host hpsi hwidth hle) hpsi l r) ha

theorem row9P_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row9ActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠ .host) :
    let q := row9P r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  simpa only [row9ActionP, row9P] using
    r2_nonhost_fuel_of_plan hpsi hwidth hle l r
      (row9PlanP r2Laws (r2Host hpsi hwidth hle) hpsi l r) ha

theorem row10bP_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row10bActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠ .host) :
    let q := row10bP r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  simpa only [row10bActionP, row10bP] using
    r2_nonhost_fuel_of_plan hpsi hwidth hle l r
      (row10bPlanP r2Laws (r2Host hpsi hwidth hle) hpsi l r) ha

theorem row10cP_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row10cActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠ .host) :
    let q := row10cP r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  simpa only [row10cActionP, row10cP] using
    r2_nonhost_fuel_of_plan hpsi hwidth hle l r
      (row10cPlanP r2Laws (r2Host hpsi hwidth hle) hpsi l r) ha

theorem row10dgP_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row10dgActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠ .host) :
    let q := row10dgP r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  simpa only [row10dgActionP, row10dgP] using
    r2_nonhost_fuel_of_plan hpsi hwidth hle l r
      (row10dgPlanP r2Laws (r2Host hpsi hwidth hle) hpsi l r) ha

theorem row10gP_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row10gActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠ .host) :
    let q := row10gP r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  simpa only [row10gActionP, row10gP] using
    r2_nonhost_fuel_of_plan hpsi hwidth hle l r
      (row10gPlanP r2Laws (r2Host hpsi hwidth hle) hpsi l r) ha

theorem fullRowP_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : fullActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠ .host) :
    let q := fullRowP r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  simpa only [fullActionP, fullRowP] using
    r2_nonhost_fuel_of_plan hpsi hwidth hle l r
      (fullPlanP r2Laws (r2Host hpsi hwidth hle) hpsi l r) ha

theorem rowScrubP_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : rowScrubActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠ .host) :
    let q := rowScrubP r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  simpa only [rowScrubActionP, rowScrubP] using
    r2_nonhost_fuel_of_plan hpsi hwidth hle l r
      (rowScrubPlanP r2Laws (r2Host hpsi hwidth hle) hpsi l r) ha

theorem rowRecoverP_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : rowRecoverActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠ .host) :
    let q := rowRecoverP r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  simpa only [rowRecoverActionP, rowRecoverP] using
    r2_nonhost_fuel_of_plan hpsi hwidth hle l r
      (rowRecoverPlanP r2Laws (r2Host hpsi hwidth hle) hpsi l r) ha

noncomputable def fullRowPort_r2
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) :
    FullRowPort
      (r2Laws (psi := psi) (kappa := kappa) (tau := tau))
      (r2Host (psi := psi) (kappa := kappa) (tau := tau)
        (width := width) hpsi hwidth hle)
      hpsi :=
  fullRowPort
    (r2Laws (psi := psi) (kappa := kappa) (tau := tau))
    (r2Host (psi := psi) (kappa := kappa) (tau := tau)
      (width := width) hpsi hwidth hle)
    hpsi


noncomputable def rowScrubPort_r2
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) :
    FullRowPort
      (r2Laws (psi := psi) (kappa := kappa) (tau := tau))
      (r2Host (psi := psi) (kappa := kappa) (tau := tau)
        (width := width) hpsi hwidth hle)
      hpsi :=
  rowScrubPort
    (r2Laws (psi := psi) (kappa := kappa) (tau := tau))
    (r2Host (psi := psi) (kappa := kappa) (tau := tau)
      (width := width) hpsi hwidth hle)
    hpsi


noncomputable def rowRecoverPort_r2
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) :
    FullRowPort
      (r2Laws (psi := psi) (kappa := kappa) (tau := tau))
      (r2Host (psi := psi) (kappa := kappa) (tau := tau)
        (width := width) hpsi hwidth hle)
      hpsi :=
  rowRecoverPort
    (r2Laws (psi := psi) (kappa := kappa) (tau := tau))
    (r2Host (psi := psi) (kappa := kappa) (tau := tau)
      (width := width) hpsi hwidth hle)
    hpsi


end B9FullCarrierRows

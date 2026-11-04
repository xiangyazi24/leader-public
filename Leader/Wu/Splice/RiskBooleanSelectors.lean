import Leader.Wu.Splice.RiskGuardMirrors

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9RiskRefinement2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceV10cLiveness
open B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
open B9Host B9SpliceTableHost B9RiskAbstraction B9RiskRefinement

variable {psi kappa tau : Nat}

private theorem guard_imp_or_nf {P Q : Prop} [Decidable P] :
    (P → Q) ↔ (¬ P ∨ Q) := by
  constructor
  · intro h
    by_cases hp : P
    · exact Or.inr (h hp)
    · exact Or.inl hp
  · intro h hp
    rcases h with hn | hq
    · exact hn hp |>.elim
    · exact hq

abbrev ControllerPair := AbsController × AbsController

def ctlOf (u : B9SpliceTableHost.Cell psi kappa tau) : AbsController :=
  { spliceRole := role u.carrier
    repairPending := u.carrier.repairPending
    acquireTicket := u.acquireTicket }

def ctlPair
    (q : B9SpliceTableHost.Cell psi kappa tau ×
      B9SpliceTableHost.Cell psi kappa tau) : ControllerPair :=
  (ctlOf q.1, ctlOf q.2)

@[simp] theorem ctlPair_mk
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    ctlPair (l, r) = (ctlOf l, ctlOf r) := rfl

@[simp] theorem riskView_left_ctl
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (riskViewOf host hpsi l r).left = ctlOf l := by
  unfold B9RiskAbstraction.riskViewOf ctlOf
  rfl

@[simp] theorem riskView_right_ctl
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (riskViewOf host hpsi l r).right = ctlOf r := by
  unfold B9RiskAbstraction.riskViewOf ctlOf
  rfl

@[simp] theorem riskView_inLeaderR
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (riskViewOf host hpsi l r).inLeaderR = B9Host.leader (base r) := by
  unfold B9RiskAbstraction.riskViewOf
  rfl

/-! Exact public controller copies of the private abstract writer vocabulary. -/

@[simp] def absCtlSetControl
    (c : AbsController) (rr : SpliceRole) (p : Bool) : AbsController :=
  { spliceRole := rr, repairPending := p, acquireTicket := false }

@[simp] def absCtlClearControl (c : AbsController) : AbsController :=
  absCtlSetControl c .none false

@[simp] def absCtlSetTicket (c : AbsController) (b : Bool) : AbsController :=
  { c with acquireTicket := b }

@[simp] def absCtlClearTicket (c : AbsController) : AbsController :=
  absCtlSetTicket c false

@[simp] def absCtlClearPending (c : AbsController) : AbsController :=
  { c with repairPending := false, acquireTicket := false }

@[simp] def absCtlFence (_c : AbsController) : AbsController :=
  { spliceRole := .none, repairPending := false, acquireTicket := true }

@[simp] def absCtlSettle (_c : AbsController) : AbsController :=
  { spliceRole := .predecessorArmed,
    repairPending := false, acquireTicket := false }

/-! Exact Boolean copies of the private abstract selectors.  Their `= true`
forms are normalized to the public Prop mirrors from `B9RiskRefinement`. -/

private def bRoleEq (c : AbsController) (r : SpliceRole) : Bool :=
  decide (c.spliceRole = r)
private def bReservedFront (c : AbsController) : Bool :=
  bRoleEq c .front && c.repairPending
private def bHostFence (c : AbsController) : Bool :=
  bRoleEq c .none && !c.repairPending && c.acquireTicket
private def bTargetClear (c : AbsController) : Bool :=
  bRoleEq c .none && !c.repairPending
private def bPendingPred (c : AbsController) : Bool :=
  bRoleEq c .predecessorArmed && c.repairPending
private def bSettledPred (c : AbsController) : Bool :=
  bRoleEq c .predecessorArmed && !c.repairPending
private def bVictimPending (c : AbsController) : Bool :=
  bRoleEq c .victimArmed && c.repairPending
private def bVictimClear (c : AbsController) : Bool :=
  bRoleEq c .victimArmed && !c.repairPending
private def bFrontClear (c : AbsController) : Bool :=
  bRoleEq c .front && !c.repairPending
private def bMalformedPending (c : AbsController) : Bool :=
  c.repairPending && !bRoleEq c .predecessorArmed &&
    !bRoleEq c .front && !bRoleEq c .victimArmed

private def bLdc (v : RiskView) : Bool := v.inLeaderL && !v.hostLeaderL
private def bLocalBarrier (v : RiskView) : Bool :=
  !v.inLeaderR && !v.alignedBefore
private def bRightFollowerRelabelled (v : RiskView) : Bool :=
  bRoleEq v.right .none && !v.right.repairPending &&
    !v.hostLeaderR && !v.hostLabelEqR
private def bMoveAcquireFront (v : RiskView) : Bool :=
  bReservedFront v.left && !v.inLeaderL && v.left.acquireTicket &&
    bReservedFront v.right && !v.inLeaderR && !v.right.acquireTicket &&
    !bLocalBarrier v
private def bArmA (v : RiskView) : Bool :=
  bRoleEq v.left .none && bRoleEq v.right .none &&
    !v.left.repairPending && !v.right.repairPending && bLdc v
private def bArmB (v : RiskView) : Bool :=
  bRoleEq v.left .none && !v.left.repairPending &&
    bRoleEq v.right .victimArmed && !v.right.repairPending && v.inLeaderR
private def bDelete (v : RiskView) : Bool :=
  bRoleEq v.left .front && bRoleEq v.right .front &&
    !v.left.repairPending && !v.right.repairPending && bLdc v
private def bPendingHold (v : RiskView) : Bool :=
  bRoleEq v.left .victimArmed && bRoleEq v.right .front &&
    !v.left.repairPending && !v.right.repairPending && bLdc v
private def bPendingAbort (v : RiskView) : Bool :=
  bRoleEq v.left .victimArmed && bRoleEq v.right .front &&
    !v.left.repairPending && !v.right.repairPending &&
    v.inLeaderL && !bLdc v
private def bMoveCommit (v : RiskView) : Bool :=
  bSettledPred v.left && bPendingPred v.right && !v.inLeaderR
private def bMoveStop (v : RiskView) : Bool :=
  bSettledPred v.left && bReservedFront v.right && !bLocalBarrier v
private def bMoveSeek (v : RiskView) : Bool :=
  bSettledPred v.left && bReservedFront v.right && bLocalBarrier v
private def bMoveSeekHold (v : RiskView) : Bool :=
  bSettledPred v.left && bVictimPending v.right && !v.inLeaderR
private def bPendingOwnerAbort (v : RiskView) : Bool :=
  bPendingPred v.right && !bSettledPred v.left
private def bPendingOwnerHold (v : RiskView) : Bool := bPendingPred v.left
private def bMoveAcquireLegacy (v : RiskView) : Bool :=
  bVictimPending v.left && !v.inLeaderL && bReservedFront v.right &&
    !v.right.acquireTicket
private def bMoveAcquireAbort (v : RiskView) : Bool :=
  bVictimPending v.left && !v.inLeaderL && !bReservedFront v.right
private def bOrphanReservedFront (v : RiskView) : Bool :=
  bReservedFront v.right && !bRoleEq v.left .predecessorArmed
private def bMarkedHold (v : RiskView) : Bool :=
  !bRoleEq v.left .none ||
    (!bRoleEq v.right .none &&
      (v.left.repairPending || v.right.repairPending))
private def bRightStale (v : RiskView) : Bool :=
  bRoleEq v.left .none && !v.left.repairPending && !v.left.acquireTicket &&
    bRoleEq v.right .predecessorArmed && !v.right.repairPending &&
    !v.right.acquireTicket
private def bFenceBusy (v : RiskView) : Bool :=
  bHostFence v.left && bLocalBarrier v && bReservedFront v.right
private def bFenceAdvance (v : RiskView) : Bool :=
  bHostFence v.left && bLocalBarrier v && bTargetClear v.right
private def bOrphanVictim (v : RiskView) : Bool :=
  bVictimPending v.right && !bSettledPred v.left
private def bOwnedPendingVictim (v : RiskView) : Bool :=
  bSettledPred v.left && bVictimPending v.right
private def bOwnerlessPendingPred (v : RiskView) : Bool :=
  bRoleEq v.left .none && bPendingPred v.right
private def bLeftScrub (v : RiskView) : Bool :=
  bVictimClear v.left || bFrontClear v.left || bMalformedPending v.left
private def bLeftPred (v : RiskView) : Bool :=
  bRoleEq v.left .predecessorArmed
private def bLeftFront (v : RiskView) : Bool := bRoleEq v.left .front
private def bRightPred (v : RiskView) : Bool :=
  bRoleEq v.right .predecessorArmed

@[simp] theorem bReservedFront_true_iff (c : AbsController) :
    bReservedFront c = true ↔ absReservedFront c := by
  simp [bReservedFront, bRoleEq, absReservedFront, and_assoc]
@[simp] theorem bHostFence_true_iff (c : AbsController) :
    bHostFence c = true ↔ absHostFence c := by
  simp [bHostFence, bRoleEq, absHostFence, and_assoc]
@[simp] theorem bTargetClear_true_iff (c : AbsController) :
    bTargetClear c = true ↔ absTargetClear c := by
  simp [bTargetClear, bRoleEq, absTargetClear, and_assoc]
@[simp] theorem bPendingPred_true_iff (c : AbsController) :
    bPendingPred c = true ↔ absPendingPred c := by
  simp [bPendingPred, bRoleEq, absPendingPred, and_assoc]
@[simp] theorem bVictimClear_true_iff (c : AbsController) :
    bVictimClear c = true ↔ absVictimClear c := by
  simp [bVictimClear, bRoleEq, absVictimClear, and_assoc]
@[simp] theorem bFrontClear_true_iff (c : AbsController) :
    bFrontClear c = true ↔ absFrontClear c := by
  simp [bFrontClear, bRoleEq, absFrontClear, and_assoc]
@[simp] theorem bMalformedPending_true_iff (c : AbsController) :
    bMalformedPending c = true ↔ absMalformedPending c := by
  simp [bMalformedPending, bRoleEq, absMalformedPending, and_assoc]

@[simp] theorem bLdc_true_iff (v : RiskView) :
    bLdc v = true ↔ absGuardLdc v := by simp [bLdc, absGuardLdc]
@[simp] theorem bLocalBarrier_true_iff (v : RiskView) :
    bLocalBarrier v = true ↔ absGuardLocalBarrier v := by
  simp [bLocalBarrier, absGuardLocalBarrier]
@[simp] theorem bMoveAcquireFront_true_iff (v : RiskView) :
    bMoveAcquireFront v = true ↔ absGuardMoveAcquireFront v := by
  cases hR : v.inLeaderR <;>
    simp [bMoveAcquireFront, bReservedFront, bLocalBarrier, bRoleEq,
      absGuardMoveAcquireFront, absReservedFront, absGuardLocalBarrier,
      hR, guard_imp_or_nf, and_assoc, or_assoc]
@[simp] theorem bArmA_true_iff (v : RiskView) :
    bArmA v = true ↔ absGuardArmA v := by
  simp [bArmA, bLdc, bRoleEq, absGuardArmA, absGuardLdc,
    guard_imp_or_nf, and_assoc, or_assoc]
@[simp] theorem bArmB_true_iff (v : RiskView) :
    bArmB v = true ↔ absGuardArmB v := by
  simp [bArmB, bRoleEq, absGuardArmB, and_assoc]
@[simp] theorem bDelete_true_iff (v : RiskView) :
    bDelete v = true ↔ absGuardDelete v := by
  simp [bDelete, bLdc, bRoleEq, absGuardDelete, absGuardLdc,
    guard_imp_or_nf, and_assoc, or_assoc]
@[simp] theorem bPendingHold_true_iff (v : RiskView) :
    bPendingHold v = true ↔ absGuardPendingHold v := by
  simp [bPendingHold, bLdc, bRoleEq, absGuardPendingHold, absGuardLdc,
    guard_imp_or_nf, and_assoc, or_assoc]
@[simp] theorem bPendingAbort_true_iff (v : RiskView) :
    bPendingAbort v = true ↔ absGuardPendingAbort v := by
  cases hL : v.inLeaderL <;>
    simp [bPendingAbort, bLdc, bRoleEq, absGuardPendingAbort, absGuardLdc,
      hL, guard_imp_or_nf, and_assoc, or_assoc]
@[simp] theorem bMoveCommit_true_iff (v : RiskView) :
    bMoveCommit v = true ↔ absGuardMoveCommit v := by
  simp [bMoveCommit, bSettledPred, bPendingPred, bRoleEq,
    absGuardMoveCommit, absSettledPred, absPendingPred,
    guard_imp_or_nf, and_assoc, or_assoc]
@[simp] theorem bMoveStop_true_iff (v : RiskView) :
    bMoveStop v = true ↔ absGuardMoveStop v := by
  cases hR : v.inLeaderR <;>
    simp [bMoveStop, bSettledPred, bReservedFront, bLocalBarrier, bRoleEq,
      absGuardMoveStop, absSettledPred, absReservedFront, absGuardLocalBarrier,
      hR, guard_imp_or_nf, and_assoc, or_assoc]
@[simp] theorem bMoveSeek_true_iff (v : RiskView) :
    bMoveSeek v = true ↔ absGuardMoveSeek v := by
  simp [bMoveSeek, bSettledPred, bReservedFront, bLocalBarrier, bRoleEq,
    absGuardMoveSeek, absSettledPred, absReservedFront, absGuardLocalBarrier,
    guard_imp_or_nf, and_assoc, or_assoc]
@[simp] theorem bMoveSeekHold_true_iff (v : RiskView) :
    bMoveSeekHold v = true ↔ absGuardMoveSeekHold v := by
  simp [bMoveSeekHold, bSettledPred, bVictimPending, bRoleEq,
    absGuardMoveSeekHold, absSettledPred, absVictimPending, and_assoc]
@[simp] theorem bPendingOwnerAbort_true_iff (v : RiskView) :
    bPendingOwnerAbort v = true ↔ absGuardPendingOwnerAbort v := by
  simp [bPendingOwnerAbort, bPendingPred, bSettledPred, bRoleEq,
    absGuardPendingOwnerAbort, absPendingPred, absSettledPred,
    guard_imp_or_nf]
@[simp] theorem bPendingOwnerHold_true_iff (v : RiskView) :
    bPendingOwnerHold v = true ↔ absGuardPendingOwnerHold v := by
  simp [bPendingOwnerHold, bPendingPred, bRoleEq,
    absGuardPendingOwnerHold, absPendingPred]
@[simp] theorem bMoveAcquireLegacy_true_iff (v : RiskView) :
    bMoveAcquireLegacy v = true ↔ absGuardMoveAcquireLegacy v := by
  simp [bMoveAcquireLegacy, bVictimPending, bReservedFront, bRoleEq,
    absGuardMoveAcquireLegacy, absVictimPending, absReservedFront, and_assoc]
@[simp] theorem bMoveAcquireAbort_true_iff (v : RiskView) :
    bMoveAcquireAbort v = true ↔ absGuardMoveAcquireAbort v := by
  simp [bMoveAcquireAbort, bVictimPending, bReservedFront, bRoleEq,
    absGuardMoveAcquireAbort, absVictimPending, absReservedFront,
    guard_imp_or_nf, and_assoc]
@[simp] theorem bOrphanReservedFront_true_iff (v : RiskView) :
    bOrphanReservedFront v = true ↔ absGuardOrphanReservedFront v := by
  simp [bOrphanReservedFront, bReservedFront, bRoleEq,
    absGuardOrphanReservedFront, absReservedFront]
@[simp] theorem bMarkedHold_true_iff (v : RiskView) :
    bMarkedHold v = true ↔ absGuardMarkedHold v := by
  simp [bMarkedHold, bRoleEq, absGuardMarkedHold, and_assoc]
@[simp] theorem bRightStale_true_iff (v : RiskView) :
    bRightStale v = true ↔ absGuardRightStale v := by
  simp [bRightStale, bRoleEq, absGuardRightStale, and_assoc]
@[simp] theorem bFenceBusy_true_iff (v : RiskView) :
    bFenceBusy v = true ↔ absGuardFenceBusy v := by
  simp [bFenceBusy, bHostFence, bLocalBarrier, bReservedFront, bRoleEq,
    absGuardFenceBusy, absHostFence, absGuardLocalBarrier, absReservedFront,
    and_assoc]
@[simp] theorem bFenceAdvance_true_iff (v : RiskView) :
    bFenceAdvance v = true ↔ absGuardFenceAdvance v := by
  simp [bFenceAdvance, bHostFence, bLocalBarrier, bTargetClear, bRoleEq,
    absGuardFenceAdvance, absHostFence, absGuardLocalBarrier, absTargetClear,
    and_assoc]
@[simp] theorem bOrphanVictim_true_iff (v : RiskView) :
    bOrphanVictim v = true ↔ absGuardOrphanVictim v := by
  simp [bOrphanVictim, bVictimPending, bSettledPred, bRoleEq,
    absGuardOrphanVictim, absVictimPending, absSettledPred,
    guard_imp_or_nf]
@[simp] theorem bOwnedPendingVictim_true_iff (v : RiskView) :
    bOwnedPendingVictim v = true ↔ absGuardOwnedPendingVictim v := by
  simp [bOwnedPendingVictim, bSettledPred, bVictimPending, bRoleEq,
    absGuardOwnedPendingVictim, absSettledPred, absVictimPending]
@[simp] theorem bOwnerlessPendingPred_true_iff (v : RiskView) :
    bOwnerlessPendingPred v = true ↔ absGuardOwnerlessPendingPred v := by
  simp [bOwnerlessPendingPred, bPendingPred, bRoleEq,
    absGuardOwnerlessPendingPred, absPendingPred]
@[simp] theorem bLeftScrub_true_iff (v : RiskView) :
    bLeftScrub v = true ↔ absGuardLeftScrub v := by
  simp [bLeftScrub, bVictimClear, bFrontClear, bMalformedPending, bRoleEq,
    absGuardLeftScrub, absVictimClear, absFrontClear, absMalformedPending,
    and_assoc, or_assoc]
@[simp] theorem bLeftPred_true_iff (v : RiskView) :
    bLeftPred v = true ↔ absGuardLeftPred v := by
  simp [bLeftPred, bRoleEq, absGuardLeftPred, and_assoc]
@[simp] theorem bLeftFront_true_iff (v : RiskView) :
    bLeftFront v = true ↔ absGuardLeftFront v := by
  simp [bLeftFront, bRoleEq, absGuardLeftFront, and_assoc]
@[simp] theorem bRightPred_true_iff (v : RiskView) :
    bRightPred v = true ↔ absGuardRightPred v := by
  simp [bRightPred, bRoleEq, absGuardRightPred, and_assoc]

/-! Controller-only copies of each abstract output. -/

@[simp] def absCtlFenceLeftStop (v : RiskView) : ControllerPair :=
  (absCtlClearTicket v.left, v.right)
@[simp] def absCtlFenceLeftAdvance (v : RiskView) : ControllerPair :=
  (absCtlClearTicket v.left, absCtlSetTicket v.right true)
@[simp] def absCtlFenceBusy (v : RiskView) : ControllerPair := (v.left, v.right)
@[simp] def absCtlHandoff (v : RiskView) : ControllerPair :=
  (absCtlSetControl v.left .predecessorArmed false,
    absCtlSetControl v.right .front true)
@[simp] def absCtlMoveAcquire (v : RiskView) : ControllerPair :=
  (absCtlSetControl v.left .predecessorArmed true, v.right)
@[simp] def absCtlArmA (v : RiskView) : ControllerPair :=
  (absCtlSetControl v.left .victimArmed false,
    absCtlSetControl v.right .front false)
@[simp] def absCtlArmB (v : RiskView) : ControllerPair :=
  (absCtlSetControl v.left .predecessorArmed false,
    absCtlSetControl v.right .front false)
@[simp] def absCtlDelete (v : RiskView) : ControllerPair :=
  (absCtlSetControl v.left .predecessorArmed true,
    absCtlSetControl v.right .front true)
@[simp] def absCtlPendingAbort (v : RiskView) : ControllerPair :=
  (absCtlClearControl v.left, absCtlClearControl v.right)
@[simp] def absCtlMoveCommit (v : RiskView) : ControllerPair :=
  (absCtlClearControl v.left,
    absCtlSetControl v.right .predecessorArmed false)
@[simp] def absCtlMoveStopAt
    (leaderR : Bool) (l r : AbsController) : ControllerPair :=
  if leaderR then (absCtlClearControl l, absCtlClearControl r)
  else (absCtlClearControl l, absCtlClearTicket r)
@[simp] def absCtlMoveStop (v : RiskView) : ControllerPair :=
  absCtlMoveStopAt v.inLeaderR v.left v.right
@[simp] def absCtlMoveSeek (v : RiskView) : ControllerPair :=
  (v.left, absCtlSetTicket v.right true)
@[simp] def absCtlPendingOwnerAbort (v : RiskView) : ControllerPair :=
  (v.left, absCtlClearTicket v.right)
@[simp] def absCtlClearRight (v : RiskView) : ControllerPair :=
  (v.left, absCtlClearControl v.right)
@[simp] def absCtlClearLeft (v : RiskView) : ControllerPair :=
  (absCtlClearControl v.left, v.right)
@[simp] def absCtlClearPendingLeft (v : RiskView) : ControllerPair :=
  (absCtlClearPending v.left, v.right)
@[simp] def absCtlClearPendingRight (v : RiskView) : ControllerPair :=
  (v.left, absCtlClearPending v.right)
@[simp] def absCtlOrdinaryAt
    (rf : Bool) (l r : AbsController) : ControllerPair :=
  let rr := absCtlClearTicket r
  let rr := if rf then absCtlSetTicket rr true else rr
  (absCtlClearTicket l, rr)
@[simp] def absCtlOrdinaryHost (v : RiskView) : ControllerPair :=
  absCtlOrdinaryAt (bRightFollowerRelabelled v) v.left v.right
@[simp] def absCtlPhysicalHoldAt
    (rf : Bool) (l r : AbsController) : ControllerPair :=
  (l, if rf then absCtlSetTicket r true else r)
@[simp] def absCtlPhysicalHold (v : RiskView) : ControllerPair :=
  absCtlPhysicalHoldAt (bRightFollowerRelabelled v) v.left v.right
@[simp] def absCtlPhysicalFence (v : RiskView) : ControllerPair :=
  let q := absCtlPhysicalHold v
  (q.1, absCtlFence q.2)

def absCtlHoldRepairPair (l r : AbsController) : ControllerPair :=
  if bReservedFront r then (l, absCtlFence r)
  else if bPendingPred r then (l, absCtlSettle r)
  else if bVictimPending r then (l, absCtlClearControl r)
  else if bVictimClear r || bFrontClear r || bMalformedPending r then
    (l, absCtlClearControl r)
  else (l, r)

def absCtlHoldRepair (v : RiskView) : ControllerPair :=
  absCtlHoldRepairPair v.left v.right

/-! Exact controller copy of the abstract dispatcher. -/

def absCtlRow7 (v : RiskView) : ControllerPair :=
  if bHostFence v.left then
    if bLocalBarrier v then
      if bTargetClear v.right then absCtlFenceLeftAdvance v else (v.left, v.right)
    else absCtlFenceLeftStop v
  else if bHostFence v.right then (v.left, v.right)
  else if bMoveAcquireFront v then absCtlMoveAcquire v
  else if bArmA v then absCtlArmA v
  else if bArmB v then absCtlArmB v
  else if bDelete v then absCtlDelete v
  else if bPendingHold v then (v.left, v.right)
  else if bPendingAbort v then absCtlPendingAbort v
  else if bMoveCommit v then absCtlMoveCommit v
  else if bMoveStop v then absCtlMoveStop v
  else if bMoveSeek v then absCtlMoveSeek v
  else if bMoveSeekHold v then (v.left, v.right)
  else if bPendingOwnerAbort v then absCtlPendingOwnerAbort v
  else if bPendingOwnerHold v then (v.left, v.right)
  else if bMoveAcquireLegacy v then absCtlMoveAcquire v
  else if bMoveAcquireAbort v then (absCtlClearTicket v.left, v.right)
  else if bOrphanReservedFront v then (v.left, v.right)
  else if bReservedFront v.left then (v.left, v.right)
  else if bVictimClear v.right then absCtlClearRight v
  else if bVictimClear v.left then absCtlClearLeft v
  else if bFrontClear v.right then absCtlClearRight v
  else if bMalformedPending v.left then absCtlClearPendingLeft v
  else if bMalformedPending v.right then absCtlClearPendingRight v
  else if bLeftPred v then absCtlClearLeft v
  else if bLeftFront v then (v.left, v.right)
  else if bMarkedHold v then (v.left, v.right)
  else absCtlOrdinaryHost v

def absCtlRow8 (v : RiskView) : ControllerPair :=
  if bRightStale v then (v.left, v.right) else absCtlRow7 v

def absCtlRow9 (v : RiskView) : ControllerPair :=
  if bFenceBusy v then absCtlFenceBusy v else absCtlRow8 v

def absCtlRow10b (v : RiskView) : ControllerPair :=
  if bFenceAdvance v then absCtlHandoff v else absCtlRow9 v

def absCtlRow10c (v : RiskView) : ControllerPair := absCtlRow10b v

def absCtlRow10dg (v : RiskView) : ControllerPair :=
  if bOrphanReservedFront v then (v.left, absCtlFence v.right)
  else if bOrphanVictim v then absCtlClearRight v
  else if bOwnedPendingVictim v then
    (absCtlFence v.left, absCtlFence v.right)
  else if bOwnerlessPendingPred v then
    (absCtlFence v.left, absCtlSettle v.right)
  else absCtlRow10c v

def absCtlRow10g (v : RiskView) : ControllerPair :=
  if v.row10dgStutters then
    if bPendingOwnerHold v then (v.left, v.right)
    else if bVictimClear v.right then absCtlClearRight v
    else if bFrontClear v.right then absCtlClearRight v
    else if bMalformedPending v.right then absCtlClearRight v
    else if bRightPred v then
      if v.right.repairPending then
        if bReservedFront v.left then (v.left, absCtlSettle v.right)
        else if bLeftScrub v then absCtlClearLeft v
        else (v.left, v.right)
      else absCtlPhysicalFence v
    else absCtlPhysicalHold v
  else absCtlRow10dg v

/-- Use the abstract row itself as the canonical controller-coordinate output.
The branch-local public copies above remain available for branch proofs, while
this definition avoids a separate theorem commuting projections through every
private `AbsOut` `if` in `B9RiskAbstraction`. -/
def absCtlRowB9 (v : RiskView) : ControllerPair :=
  ((B9RiskAbstraction.absRowB9 v).left,
    (B9RiskAbstraction.absRowB9 v).right)


/-- Canonical controller projection of the abstract dispatcher. -/
theorem absRowB9_controller_projection (v : RiskView) :
    ((B9RiskAbstraction.absRowB9 v).left,
      (B9RiskAbstraction.absRowB9 v).right) = absCtlRowB9 v := by
  rfl

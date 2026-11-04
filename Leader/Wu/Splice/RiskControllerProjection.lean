import Leader.Wu.Splice.RiskBooleanSelectors

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9RiskRefinement2C

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
open B9RiskRefinement2

variable {psi kappa tau : Nat}

def ConcreteRowB9ControllerProjectionObligation : Prop :=
  ∀ {psi kappa tau : Nat}
    (host : B9Host.HostRow (B9Host.Phys psi kappa tau))
    (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau),
    let v := B9RiskAbstraction.riskViewOf host hpsi l r
    let w := B9SpliceTableHost.rowB9 host hpsi l r
    B9RiskRefinement2.ctlPair w =
      ((B9RiskAbstraction.absRowB9 v).left,
        (B9RiskAbstraction.absRowB9 v).right)

def ConcreteRowB9PhysicalProjectionObligation : Prop :=
  ∀ {psi kappa tau : Nat}
    (host : B9Host.HostRow (B9Host.Phys psi kappa tau))
    (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau),
    let v := B9RiskAbstraction.riskViewOf host hpsi l r
    let w := B9SpliceTableHost.rowB9 host hpsi l r
    B9RiskAbstraction.concreteOutPhys l r w.1 w.2 =
      (B9RiskAbstraction.absRowB9 v).phys

/-- The already-isolated concrete host-row residual for the `row10gH` branch. -/
def ConcreteRow10gControllerProjectionResidual : Prop :=
  ∀ {psi kappa tau : Nat}
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau),
    ctlPair (row10gH host hpsi l r) =
      absCtlRow10g (riskViewOf host hpsi l r)

/-- Residual: controller projection of the V10j reserved-front repair.

The failed field cases are exactly discharged by these six V6 facts:
* `role (clearControlV6 r).carrier = .none`,
* `(clearControlV6 r).carrier.repairPending = false`,
* `(clearControlV6 r).acquireTicket = false`,
* `role (settleV6 r).carrier = .predecessorArmed`,
* `(settleV6 r).carrier.repairPending = false`,
* `(settleV6 r).acquireTicket = false`.

Source definitions/field lemmas:
`Leader/Wu/Splice/ProvenanceTicketTable.lean:69-72` (`setControlV6`),
`:74-76` (`clearControlV6`), `:104-118` (ticket/role/pending for
`setControlV6`), and `:121-134` (role/pending/ticket for `clearControlV6`).
`settleV6` is the plain `setControlV6 _ .predecessorArmed false` wrapper at
`Leader/Wu/Splice/OrphanToFence.lean:254-255`, so its three facts are those same V6
field lemmas after unfolding `settleV6`.  The fence branch is likewise a plain
record-update composition (`B9OrphanToFence.lean:13-14`). -/
def HoldRepairControllerProjectionObligation
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi) : Prop :=
  ∀ (l r : Cell psi kappa tau),
    ctlPair (B9SpliceTableV10j.holdRepairV10j l r) =
      absCtlHoldRepair (riskViewOf host hpsi l r)

@[simp] theorem ctlOf_clearControlV6_q13708
    (u : Cell psi kappa tau) :
    ctlOf (clearControlV6 u) = absCtlClearControl (ctlOf u) := by rfl

@[simp] theorem ctlOf_fenceV6_q13708
    (u : Cell psi kappa tau) :
    ctlOf (fenceV6 u) = absCtlFence (ctlOf u) := by rfl

@[simp] theorem ctlOf_settleV6_q13708
    (u : Cell psi kappa tau) :
    ctlOf (settleV6 u) = absCtlSettle (ctlOf u) := by rfl

private def roleEqC (c : AbsController) (r : SpliceRole) : Bool :=
  decide (c.spliceRole = r)
private def reservedFrontC (c : AbsController) : Bool :=
  roleEqC c .front && c.repairPending
private def pendingPredC (c : AbsController) : Bool :=
  roleEqC c .predecessorArmed && c.repairPending
private def victimPendingC (c : AbsController) : Bool :=
  roleEqC c .victimArmed && c.repairPending
private def victimClearC (c : AbsController) : Bool :=
  roleEqC c .victimArmed && !c.repairPending
private def frontClearC (c : AbsController) : Bool :=
  roleEqC c .front && !c.repairPending
private def malformedPendingC (c : AbsController) : Bool :=
  c.repairPending && !roleEqC c .predecessorArmed &&
    !roleEqC c .front && !roleEqC c .victimArmed
private def rightFollowerRelabelledC (v : RiskView) : Bool :=
  roleEqC v.right .none && !v.right.repairPending &&
    !v.hostLeaderR && !v.hostLabelEqR

private def holdRepairCtlC (l r : AbsController) : ControllerPair :=
  if reservedFrontC r then (l, absCtlFence r)
  else if pendingPredC r then (l, absCtlSettle r)
  else if victimPendingC r then (l, absCtlClearControl r)
  else if victimClearC r || frontClearC r || malformedPendingC r then
    (l, absCtlClearControl r)
  else (l, r)

private theorem absCtlHoldRepair_eq_C (v : RiskView) :
    absCtlHoldRepair v = holdRepairCtlC v.left v.right := by rfl
private theorem absCtlOrdinaryHost_eq_C (v : RiskView) :
    absCtlOrdinaryHost v =
      absCtlOrdinaryAt (rightFollowerRelabelledC v) v.left v.right := by rfl
private theorem absCtlPhysicalHold_eq_C (v : RiskView) :
    absCtlPhysicalHold v =
      absCtlPhysicalHoldAt (rightFollowerRelabelledC v) v.left v.right := by rfl

namespace WriterProjectionQ13708

@[simp] theorem deleteH
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) :
    ctlPair (deleteWriteH host l r) =
      absCtlDelete (riskViewOf host hpsi l r) := by rfl

end WriterProjectionQ13708
open WriterProjectionQ13708


private def hostFenceC (c : AbsController) : Bool :=
  roleEqC c .none && !c.repairPending && c.acquireTicket
private def targetClearC (c : AbsController) : Bool :=
  roleEqC c .none && !c.repairPending
private def settledPredC (c : AbsController) : Bool :=
  roleEqC c .predecessorArmed && !c.repairPending
private def ldcC (v : RiskView) : Bool := v.inLeaderL && !v.hostLeaderL
private def localBarrierC (v : RiskView) : Bool :=
  !v.inLeaderR && !v.alignedBefore
private def moveAcquireFrontC (v : RiskView) : Bool :=
  reservedFrontC v.left && !v.inLeaderL && v.left.acquireTicket &&
  reservedFrontC v.right && !v.inLeaderR && !v.right.acquireTicket &&
  !localBarrierC v
private def armAC (v : RiskView) : Bool :=
  roleEqC v.left .none && roleEqC v.right .none &&
  !v.left.repairPending && !v.right.repairPending && ldcC v
private def armBC (v : RiskView) : Bool :=
  roleEqC v.left .none && !v.left.repairPending &&
  roleEqC v.right .victimArmed && !v.right.repairPending && v.inLeaderR
private def deleteC (v : RiskView) : Bool :=
  roleEqC v.left .front && roleEqC v.right .front &&
  !v.left.repairPending && !v.right.repairPending && ldcC v
private def pendingHoldC (v : RiskView) : Bool :=
  roleEqC v.left .victimArmed && roleEqC v.right .front &&
  !v.left.repairPending && !v.right.repairPending && ldcC v
private def pendingAbortC (v : RiskView) : Bool :=
  roleEqC v.left .victimArmed && roleEqC v.right .front &&
  !v.left.repairPending && !v.right.repairPending &&
  v.inLeaderL && !ldcC v
private def moveCommitC (v : RiskView) : Bool :=
  settledPredC v.left && pendingPredC v.right && !v.inLeaderR
private def moveStopC (v : RiskView) : Bool :=
  settledPredC v.left && reservedFrontC v.right && !localBarrierC v
private def moveSeekC (v : RiskView) : Bool :=
  settledPredC v.left && reservedFrontC v.right && localBarrierC v
private def moveSeekHoldC (v : RiskView) : Bool :=
  settledPredC v.left && victimPendingC v.right && !v.inLeaderR
private def pendingOwnerAbortC (v : RiskView) : Bool :=
  pendingPredC v.right && !settledPredC v.left
private def pendingOwnerHoldC (v : RiskView) : Bool := pendingPredC v.left
private def moveAcquireLegacyC (v : RiskView) : Bool :=
  victimPendingC v.left && !v.inLeaderL && reservedFrontC v.right &&
  !v.right.acquireTicket
private def moveAcquireAbortC (v : RiskView) : Bool :=
  victimPendingC v.left && !v.inLeaderL && !reservedFrontC v.right
private def orphanReservedFrontC (v : RiskView) : Bool :=
  reservedFrontC v.right && !roleEqC v.left .predecessorArmed
private def markedHoldC (v : RiskView) : Bool :=
  !roleEqC v.left .none ||
    (!roleEqC v.right .none &&
      (v.left.repairPending || v.right.repairPending))
private def rightStaleC (v : RiskView) : Bool :=
  roleEqC v.left .none && !v.left.repairPending && !v.left.acquireTicket &&
  roleEqC v.right .predecessorArmed && !v.right.repairPending &&
  !v.right.acquireTicket
private def fenceBusyC (v : RiskView) : Bool :=
  hostFenceC v.left && localBarrierC v && reservedFrontC v.right
private def fenceAdvanceC (v : RiskView) : Bool :=
  hostFenceC v.left && localBarrierC v && targetClearC v.right
private def orphanVictimC (v : RiskView) : Bool :=
  victimPendingC v.right && !settledPredC v.left
private def ownedPendingVictimC (v : RiskView) : Bool :=
  settledPredC v.left && victimPendingC v.right
private def ownerlessPendingPredC (v : RiskView) : Bool :=
  roleEqC v.left .none && pendingPredC v.right
private def leftScrubC (v : RiskView) : Bool :=
  victimClearC v.left || frontClearC v.left || malformedPendingC v.left

private def inputPhysC (v : RiskView) : AbsPairPhys :=
  { leaderL := v.inLeaderL, leaderR := v.inLeaderR,
    aligned := v.alignedBefore, labelEqL := true, labelEqR := true }
private def hostPhysC (v : RiskView) : AbsPairPhys :=
  { leaderL := v.hostLeaderL, leaderR := v.hostLeaderR,
    aligned := v.alignedHost,
    labelEqL := v.hostLabelEqL, labelEqR := v.hostLabelEqR }
private def relabelPhysC (v : RiskView) : AbsPairPhys :=
  { leaderL := v.inLeaderL, leaderR := v.inLeaderR,
    aligned := true, labelEqL := true, labelEqR := v.alignedBefore }
private def keepOutC (v : RiskView) (l r : AbsController) : AbsOut :=
  { left := l, right := r, phys := inputPhysC v }
private def hostOutC (v : RiskView) (l r : AbsController) : AbsOut :=
  { left := l, right := r, phys := hostPhysC v }
private def relabelOutC (v : RiskView) (l r : AbsController) : AbsOut :=
  { left := l, right := r, phys := relabelPhysC v }

private def wFenceLeftStopC (v : RiskView) : AbsOut :=
  keepOutC v (absCtlClearTicket v.left) v.right
private def wFenceLeftAdvanceC (v : RiskView) : AbsOut :=
  relabelOutC v (absCtlClearTicket v.left) (absCtlSetTicket v.right true)
private def wFenceBusyC (v : RiskView) : AbsOut := relabelOutC v v.left v.right
private def wHandoffC (v : RiskView) : AbsOut :=
  keepOutC v (absCtlSetControl v.left .predecessorArmed false)
    (absCtlSetControl v.right .front true)
private def wMoveAcquireC (v : RiskView) : AbsOut :=
  keepOutC v (absCtlSetControl v.left .predecessorArmed true) v.right
private def wArmAC (v : RiskView) : AbsOut :=
  keepOutC v (absCtlSetControl v.left .victimArmed false)
    (absCtlSetControl v.right .front false)
private def wArmBC (v : RiskView) : AbsOut :=
  keepOutC v (absCtlSetControl v.left .predecessorArmed false)
    (absCtlSetControl v.right .front false)
private def wDeleteC (v : RiskView) : AbsOut :=
  hostOutC v (absCtlSetControl v.left .predecessorArmed true)
    (absCtlSetControl v.right .front true)
private def wPendingAbortC (v : RiskView) : AbsOut :=
  keepOutC v (absCtlClearControl v.left) (absCtlClearControl v.right)
private def wMoveCommitC (v : RiskView) : AbsOut :=
  relabelOutC v (absCtlClearControl v.left)
    (absCtlSetControl v.right .predecessorArmed false)
private def wMoveStopC (v : RiskView) : AbsOut :=
  if v.inLeaderR then
    keepOutC v (absCtlClearControl v.left) (absCtlClearControl v.right)
  else keepOutC v (absCtlClearControl v.left) (absCtlClearTicket v.right)
private def wMoveSeekC (v : RiskView) : AbsOut :=
  keepOutC v v.left (absCtlSetTicket v.right true)
private def wPendingOwnerAbortC (v : RiskView) : AbsOut :=
  keepOutC v v.left (absCtlClearTicket v.right)
private def wClearRightC (v : RiskView) : AbsOut :=
  keepOutC v v.left (absCtlClearControl v.right)
private def wClearLeftC (v : RiskView) : AbsOut :=
  keepOutC v (absCtlClearControl v.left) v.right
private def wClearPendingLeftC (v : RiskView) : AbsOut :=
  keepOutC v (absCtlClearPending v.left) v.right
private def wClearPendingRightC (v : RiskView) : AbsOut :=
  keepOutC v v.left (absCtlClearPending v.right)
private def wOrdinaryHostC (v : RiskView) : AbsOut :=
  let rr := absCtlClearTicket v.right
  let rr := if rightFollowerRelabelledC v then absCtlSetTicket rr true else rr
  hostOutC v (absCtlClearTicket v.left) rr
private def wPhysicalHoldC (v : RiskView) : AbsOut :=
  let rr := if rightFollowerRelabelledC v then absCtlSetTicket v.right true else v.right
  hostOutC v v.left rr
private def wPhysicalFenceC (v : RiskView) : AbsOut :=
  let q := wPhysicalHoldC v
  { left := q.left, right := absCtlFence q.right, phys := q.phys }
private def wHoldRepairC (v : RiskView) : AbsOut :=
  if reservedFrontC v.right then keepOutC v v.left (absCtlFence v.right)
  else if pendingPredC v.right then keepOutC v v.left (absCtlSettle v.right)
  else if victimPendingC v.right then wClearRightC v
  else if victimClearC v.right || frontClearC v.right || malformedPendingC v.right then
    wClearRightC v
  else keepOutC v v.left v.right


private def row7OutC (v : RiskView) : AbsOut :=
  if hostFenceC v.left then
    if localBarrierC v then
      if targetClearC v.right then wFenceLeftAdvanceC v else keepOutC v v.left v.right
    else wFenceLeftStopC v
  else if hostFenceC v.right then keepOutC v v.left v.right
  else if moveAcquireFrontC v then wMoveAcquireC v
  else if armAC v then wArmAC v
  else if armBC v then wArmBC v
  else if deleteC v then wDeleteC v
  else if pendingHoldC v then keepOutC v v.left v.right
  else if pendingAbortC v then wPendingAbortC v
  else if moveCommitC v then wMoveCommitC v
  else if moveStopC v then wMoveStopC v
  else if moveSeekC v then wMoveSeekC v
  else if moveSeekHoldC v then keepOutC v v.left v.right
  else if pendingOwnerAbortC v then wPendingOwnerAbortC v
  else if pendingOwnerHoldC v then keepOutC v v.left v.right
  else if moveAcquireLegacyC v then wMoveAcquireC v
  else if moveAcquireAbortC v then keepOutC v (absCtlClearTicket v.left) v.right
  else if orphanReservedFrontC v then keepOutC v v.left v.right
  else if reservedFrontC v.left then keepOutC v v.left v.right
  else if victimClearC v.right then wClearRightC v
  else if victimClearC v.left then wClearLeftC v
  else if frontClearC v.right then wClearRightC v
  else if malformedPendingC v.left then wClearPendingLeftC v
  else if malformedPendingC v.right then wClearPendingRightC v
  else if roleEqC v.left .predecessorArmed then wClearLeftC v
  else if roleEqC v.left .front then keepOutC v v.left v.right
  else if markedHoldC v then keepOutC v v.left v.right
  else wOrdinaryHostC v

private def row8OutC (v : RiskView) : AbsOut :=
  if rightStaleC v then keepOutC v v.left v.right else row7OutC v
private def row9OutC (v : RiskView) : AbsOut :=
  if fenceBusyC v then wFenceBusyC v else row8OutC v
private def row10bOutC (v : RiskView) : AbsOut :=
  if fenceAdvanceC v then wHandoffC v else row9OutC v
private def row10cOutC (v : RiskView) : AbsOut := row10bOutC v
private def row10dgOutC (v : RiskView) : AbsOut :=
  if orphanReservedFrontC v then keepOutC v v.left (absCtlFence v.right)
  else if orphanVictimC v then wClearRightC v
  else if ownedPendingVictimC v then
    keepOutC v (absCtlFence v.left) (absCtlFence v.right)
  else if ownerlessPendingPredC v then
    keepOutC v (absCtlFence v.left) (absCtlSettle v.right)
  else row10cOutC v
private def row10gOutC (v : RiskView) : AbsOut :=
  if v.row10dgStutters then
    if pendingPredC v.left then keepOutC v v.left v.right
    else if victimClearC v.right then wClearRightC v
    else if frontClearC v.right then wClearRightC v
    else if malformedPendingC v.right then wClearRightC v
    else if roleEqC v.right .predecessorArmed then
      if v.right.repairPending then
        if reservedFrontC v.left then keepOutC v v.left (absCtlSettle v.right)
        else if leftScrubC v then wClearLeftC v
        else keepOutC v v.left v.right
      else wPhysicalFenceC v
    else wPhysicalHoldC v
  else row10dgOutC v
private def rowB9OutC (v : RiskView) : AbsOut :=
  if ldcC v then
    if reservedFrontC v.left then wHoldRepairC v else wDeleteC v
  else row10gOutC v

private def row7CtlC (v : RiskView) : ControllerPair :=
  if hostFenceC v.left then
    if localBarrierC v then
      if targetClearC v.right then absCtlFenceLeftAdvance v else (v.left, v.right)
    else absCtlFenceLeftStop v
  else if hostFenceC v.right then (v.left, v.right)
  else if moveAcquireFrontC v then absCtlMoveAcquire v
  else if armAC v then absCtlArmA v
  else if armBC v then absCtlArmB v
  else if deleteC v then absCtlDelete v
  else if pendingHoldC v then (v.left, v.right)
  else if pendingAbortC v then absCtlPendingAbort v
  else if moveCommitC v then absCtlMoveCommit v
  else if moveStopC v then absCtlMoveStop v
  else if moveSeekC v then absCtlMoveSeek v
  else if moveSeekHoldC v then (v.left, v.right)
  else if pendingOwnerAbortC v then absCtlPendingOwnerAbort v
  else if pendingOwnerHoldC v then (v.left, v.right)
  else if moveAcquireLegacyC v then absCtlMoveAcquire v
  else if moveAcquireAbortC v then (absCtlClearTicket v.left, v.right)
  else if orphanReservedFrontC v then (v.left, v.right)
  else if reservedFrontC v.left then (v.left, v.right)
  else if victimClearC v.right then absCtlClearRight v
  else if victimClearC v.left then absCtlClearLeft v
  else if frontClearC v.right then absCtlClearRight v
  else if malformedPendingC v.left then absCtlClearPendingLeft v
  else if malformedPendingC v.right then absCtlClearPendingRight v
  else if roleEqC v.left .predecessorArmed then absCtlClearLeft v
  else if roleEqC v.left .front then (v.left, v.right)
  else if markedHoldC v then (v.left, v.right)
  else absCtlOrdinaryAt (rightFollowerRelabelledC v) v.left v.right

private def row8CtlC (v : RiskView) : ControllerPair :=
  if rightStaleC v then (v.left, v.right) else row7CtlC v
private def row9CtlC (v : RiskView) : ControllerPair :=
  if fenceBusyC v then absCtlFenceBusy v else row8CtlC v
private def row10bCtlC (v : RiskView) : ControllerPair :=
  if fenceAdvanceC v then absCtlHandoff v else row9CtlC v
private def row10cCtlC (v : RiskView) : ControllerPair := row10bCtlC v
private def row10dgCtlC (v : RiskView) : ControllerPair :=
  if orphanReservedFrontC v then (v.left, absCtlFence v.right)
  else if orphanVictimC v then absCtlClearRight v
  else if ownedPendingVictimC v then (absCtlFence v.left, absCtlFence v.right)
  else if ownerlessPendingPredC v then (absCtlFence v.left, absCtlSettle v.right)
  else row10cCtlC v
private def row10gCtlC (v : RiskView) : ControllerPair :=
  if v.row10dgStutters then
    if pendingPredC v.left then (v.left, v.right)
    else if victimClearC v.right then absCtlClearRight v
    else if frontClearC v.right then absCtlClearRight v
    else if malformedPendingC v.right then absCtlClearRight v
    else if roleEqC v.right .predecessorArmed then
      if v.right.repairPending then
        if reservedFrontC v.left then (v.left, absCtlSettle v.right)
        else if leftScrubC v then absCtlClearLeft v
        else (v.left, v.right)
      else absCtlPhysicalFence v
    else absCtlPhysicalHold v
  else row10dgCtlC v
private def rowB9CtlC (v : RiskView) : ControllerPair :=
  if ldcC v then
    if reservedFrontC v.left then absCtlHoldRepair v else absCtlDelete v
  else row10gCtlC v

private def controllersC (o : AbsOut) : ControllerPair := (o.left, o.right)
@[simp] private theorem controllersC_ifC (b : Bool) (x y : AbsOut) :
    controllersC (if b then x else y) =
      (if b then controllersC x else controllersC y) := by
  cases b <;> rfl
@[simp] private theorem controllersC_keepOutC
    (v : RiskView) (l r : AbsController) :
    controllersC (keepOutC v l r) = (l, r) := by rfl
@[simp] private theorem controllersC_hostOutC
    (v : RiskView) (l r : AbsController) :
    controllersC (hostOutC v l r) = (l, r) := by rfl
@[simp] private theorem controllersC_relabelOutC
    (v : RiskView) (l r : AbsController) :
    controllersC (relabelOutC v l r) = (l, r) := by rfl


@[simp] private theorem controllersC_wFenceLeftStopC (v : RiskView) :
    controllersC (wFenceLeftStopC v) = absCtlFenceLeftStop v := by rfl
@[simp] private theorem controllersC_wFenceLeftAdvanceC (v : RiskView) :
    controllersC (wFenceLeftAdvanceC v) = absCtlFenceLeftAdvance v := by rfl
@[simp] private theorem controllersC_wFenceBusyC (v : RiskView) :
    controllersC (wFenceBusyC v) = absCtlFenceBusy v := by rfl
@[simp] private theorem controllersC_wHandoffC (v : RiskView) :
    controllersC (wHandoffC v) = absCtlHandoff v := by rfl
@[simp] private theorem controllersC_wMoveAcquireC (v : RiskView) :
    controllersC (wMoveAcquireC v) = absCtlMoveAcquire v := by rfl
@[simp] private theorem controllersC_wArmAC (v : RiskView) :
    controllersC (wArmAC v) = absCtlArmA v := by rfl
@[simp] private theorem controllersC_wArmBC (v : RiskView) :
    controllersC (wArmBC v) = absCtlArmB v := by rfl
@[simp] private theorem controllersC_wDeleteC (v : RiskView) :
    controllersC (wDeleteC v) = absCtlDelete v := by rfl
@[simp] private theorem controllersC_wPendingAbortC (v : RiskView) :
    controllersC (wPendingAbortC v) = absCtlPendingAbort v := by rfl
@[simp] private theorem controllersC_wMoveCommitC (v : RiskView) :
    controllersC (wMoveCommitC v) = absCtlMoveCommit v := by rfl
@[simp] private theorem controllersC_wMoveStopC (v : RiskView) :
    controllersC (wMoveStopC v) = absCtlMoveStop v := by
  unfold wMoveStopC B9RiskRefinement2.absCtlMoveStop
    B9RiskRefinement2.absCtlMoveStopAt
  cases v.inLeaderR <;> rfl
@[simp] private theorem controllersC_wMoveSeekC (v : RiskView) :
    controllersC (wMoveSeekC v) = absCtlMoveSeek v := by rfl
@[simp] private theorem controllersC_wPendingOwnerAbortC (v : RiskView) :
    controllersC (wPendingOwnerAbortC v) = absCtlPendingOwnerAbort v := by rfl
@[simp] private theorem controllersC_wClearRightC (v : RiskView) :
    controllersC (wClearRightC v) = absCtlClearRight v := by rfl
@[simp] private theorem controllersC_wClearLeftC (v : RiskView) :
    controllersC (wClearLeftC v) = absCtlClearLeft v := by rfl
@[simp] private theorem controllersC_wClearPendingLeftC (v : RiskView) :
    controllersC (wClearPendingLeftC v) = absCtlClearPendingLeft v := by rfl
@[simp] private theorem controllersC_wClearPendingRightC (v : RiskView) :
    controllersC (wClearPendingRightC v) = absCtlClearPendingRight v := by rfl
@[simp] private theorem controllersC_wOrdinaryHostC (v : RiskView) :
    controllersC (wOrdinaryHostC v) = absCtlOrdinaryHost v := by
  rw [absCtlOrdinaryHost_eq_C]
  rfl
@[simp] private theorem controllersC_wPhysicalHoldC (v : RiskView) :
    controllersC (wPhysicalHoldC v) = absCtlPhysicalHold v := by
  rw [absCtlPhysicalHold_eq_C]
  rfl
@[simp] private theorem controllersC_wPhysicalFenceC (v : RiskView) :
    controllersC (wPhysicalFenceC v) = absCtlPhysicalFence v := by
  have hp := controllersC_wPhysicalHoldC v
  change
    ((wPhysicalHoldC v).left, absCtlFence (wPhysicalHoldC v).right) =
      ((absCtlPhysicalHold v).1, absCtlFence (absCtlPhysicalHold v).2)
  exact congrArg (fun q : ControllerPair => (q.1, absCtlFence q.2)) hp
@[simp] private theorem controllersC_wHoldRepairC (v : RiskView) :
    controllersC (wHoldRepairC v) = absCtlHoldRepair v := by
  rw [absCtlHoldRepair_eq_C]
  unfold wHoldRepairC holdRepairCtlC
  by_cases hReserved : reservedFrontC v.right = true
  · simp [hReserved]
  by_cases hPred : pendingPredC v.right = true
  · simp [hReserved, hPred]
  by_cases hVictimPending : victimPendingC v.right = true
  · simp [hReserved, hPred, hVictimPending,
      controllersC_wClearRightC]
  by_cases hScrub :
      (victimClearC v.right || frontClearC v.right ||
        malformedPendingC v.right) = true
  · simp [hReserved, hPred, hVictimPending, hScrub,
      controllersC_wClearRightC]
  · simp [hReserved, hPred, hVictimPending, hScrub]

private theorem controllersC_row7OutC (v : RiskView) :
    controllersC (row7OutC v) = row7CtlC v := by
  unfold row7OutC row7CtlC
  simp only [controllersC_ifC, controllersC_keepOutC,
    controllersC_wFenceLeftStopC, controllersC_wFenceLeftAdvanceC,
    controllersC_wMoveAcquireC, controllersC_wArmAC, controllersC_wArmBC,
    controllersC_wDeleteC, controllersC_wPendingAbortC,
    controllersC_wMoveCommitC, controllersC_wMoveStopC,
    controllersC_wMoveSeekC, controllersC_wPendingOwnerAbortC,
    controllersC_wClearRightC, controllersC_wClearLeftC,
    controllersC_wClearPendingLeftC, controllersC_wClearPendingRightC,
    controllersC_wOrdinaryHostC, absCtlOrdinaryHost_eq_C]
private theorem controllersC_row8OutC (v : RiskView) :
    controllersC (row8OutC v) = row8CtlC v := by
  unfold row8OutC row8CtlC
  simp only [controllersC_ifC, controllersC_keepOutC, controllersC_row7OutC]
private theorem controllersC_row9OutC (v : RiskView) :
    controllersC (row9OutC v) = row9CtlC v := by
  unfold row9OutC row9CtlC
  simp only [controllersC_ifC, controllersC_wFenceBusyC, controllersC_row8OutC]
private theorem controllersC_row10bOutC (v : RiskView) :
    controllersC (row10bOutC v) = row10bCtlC v := by
  unfold row10bOutC row10bCtlC
  simp only [controllersC_ifC, controllersC_wHandoffC, controllersC_row9OutC]
private theorem controllersC_row10cOutC (v : RiskView) :
    controllersC (row10cOutC v) = row10cCtlC v :=
  controllersC_row10bOutC v
private theorem controllersC_row10dgOutC (v : RiskView) :
    controllersC (row10dgOutC v) = row10dgCtlC v := by
  unfold row10dgOutC row10dgCtlC
  simp only [controllersC_ifC, controllersC_keepOutC,
    controllersC_wClearRightC, controllersC_row10cOutC]
private theorem controllersC_row10gOutC (v : RiskView) :
    controllersC (row10gOutC v) = row10gCtlC v := by
  unfold row10gOutC row10gCtlC
  simp only [controllersC_ifC, controllersC_keepOutC,
    controllersC_wClearRightC, controllersC_wClearLeftC,
    controllersC_wPhysicalFenceC, controllersC_wPhysicalHoldC,
    controllersC_row10dgOutC]
private theorem controllersC_rowB9OutC (v : RiskView) :
    controllersC (rowB9OutC v) = rowB9CtlC v := by
  unfold rowB9OutC rowB9CtlC
  simp only [controllersC_ifC, controllersC_wHoldRepairC,
    controllersC_wDeleteC, controllersC_row10gOutC]

private theorem absRowB9_eq_outC (v : RiskView) :
    B9RiskAbstraction.absRowB9 v = rowB9OutC v := by rfl
private theorem absCtlRow10g_eq_C (v : RiskView) :
    absCtlRow10g v = row10gCtlC v := by rfl

private theorem absCtlRowB9_eq_C (v : RiskView) :
    absCtlRowB9 v = rowB9CtlC v := by
  unfold B9RiskRefinement2.absCtlRowB9
  change controllersC (B9RiskAbstraction.absRowB9 v) = rowB9CtlC v
  rw [absRowB9_eq_outC]
  exact controllersC_rowB9OutC v

theorem rowB9_controller_projection
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (hHold : HoldRepairControllerProjectionObligation host hpsi)
    (h10g : ConcreteRow10gControllerProjectionResidual)
    (l r : Cell psi kappa tau) :
    ctlPair (rowB9 host hpsi l r) =
      absCtlRowB9 (riskViewOf host hpsi l r) := by
  rw [absCtlRowB9_eq_C]
  classical
  unfold B9SpliceTableHost.rowB9
  repeat' split
  all_goals
    simp_all [rowB9CtlC, ldcC, reservedFrontC, roleEqC,
      guard_ldc_eq_abs host hpsi l r,
      guard_reservedFront_left_eq_abs host hpsi l r,
      B9RiskRefinement.absGuardLdc,
      B9RiskRefinement.absReservedFront,
      hHold l r,
      WriterProjectionQ13708.deleteH host hpsi l r,
      absCtlRow10g_eq_C,
      h10g host hpsi l r]

theorem concreteRowB9ControllerProjection
    (hHold : ∀ {psi kappa tau : Nat}
      (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi),
      HoldRepairControllerProjectionObligation host hpsi)
    (h10g : ConcreteRow10gControllerProjectionResidual) :
    ConcreteRowB9ControllerProjectionObligation := by
  intro psi kappa tau host hpsi l r
  dsimp only
  exact (rowB9_controller_projection host hpsi
      (hHold host hpsi) h10g l r).trans
    (B9RiskRefinement2.absRowB9_controller_projection
      (riskViewOf host hpsi l r)).symm

end B9RiskRefinement2C

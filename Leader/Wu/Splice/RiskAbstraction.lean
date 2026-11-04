import Leader.Wu.Splice.FullCarrierRows


set_option autoImplicit false
set_option Elab.async false


namespace B9RiskAbstraction


open Q11593SpliceControllerDesign
open B9Host B9SpliceTableHost
open B9ControllerRecovery
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g


variable {psi kappa tau : Nat}


instance alignedDecRiskAbs {psi kappa tau : Nat} (a b : B9Host.Phys psi kappa tau) :
    Decidable (B9Host.Aligned a b) := by
  unfold B9Host.Aligned
  infer_instance

/-! ## 1. Finite controller and physical views -/


/-- Exactly the three outer coordinates read by the B9 controller/risk layer. -/
structure AbsController where
  spliceRole : SpliceRole
  repairPending : Bool
  acquireTicket : Bool
  deriving DecidableEq, Repr


/-- Risk-visible physical result of one served pair.
`labelEqL/R` mean equality with the corresponding input endpoint label. -/
structure AbsPairPhys where
  leaderL : Bool
  leaderR : Bool
  aligned : Bool
  labelEqL : Bool
  labelEqR : Bool
  deriving DecidableEq, Repr


/-- Abstract row output.  We store the risk-visible physical result directly,
not a HOST/KEEP tag; this makes the V10c zero-refresh quotient exact. -/
structure AbsOut where
  left : AbsController
  right : AbsController
  phys : AbsPairPhys
  deriving DecidableEq, Repr


/-- Complete finite observation needed by rowB9 and the pair-risk terms.
The first eight booleans are physical observations.  `row10dgStutters` is the
one exact full-state selector that row10g reads and the risk coordinates do not
determine. -/
structure RiskView where
  left : AbsController
  right : AbsController
  inLeaderL : Bool
  inLeaderR : Bool
  hostLeaderL : Bool
  hostLeaderR : Bool
  alignedBefore : Bool
  alignedHost : Bool
  hostLabelEqL : Bool
  hostLabelEqR : Bool
  row10dgStutters : Bool
  deriving DecidableEq, Repr


private def allBools : List Bool := [false, true]


private def allRoles : List SpliceRole :=
  [.none, .predecessorArmed, .victimArmed, .front]


def allControllers : List AbsController :=
  allRoles.flatMap fun r =>
    allBools.flatMap fun p =>
      allBools.map fun t =>
        { spliceRole := r, repairPending := p, acquireTicket := t }


/-- Raw enumeration: 16^2 * 2^9 = 131072 views.  Impossible host combinations
are deliberately retained; `absViewAdmissible` filters them in the checker. -/
def allRiskViews : List RiskView :=
  allControllers.flatMap fun l =>
  allControllers.flatMap fun r =>
  allBools.flatMap fun il =>
  allBools.flatMap fun ir =>
  allBools.flatMap fun hl =>
  allBools.flatMap fun hr =>
  allBools.flatMap fun ab =>
  allBools.flatMap fun ah =>
  allBools.flatMap fun eql =>
  allBools.flatMap fun eqr =>
  allBools.map fun st =>
    { left := l, right := r,
      inLeaderL := il, inLeaderR := ir,
      hostLeaderL := hl, hostLeaderR := hr,
      alignedBefore := ab, alignedHost := ah,
      hostLabelEqL := eql, hostLabelEqR := eqr,
      row10dgStutters := st }


def riskViewCount : Nat := 131072


def riskViewEnumerationSpec : Prop :=
  allRiskViews.length = riskViewCount ∧
    ∀ v : RiskView, v ∈ allRiskViews


/-! ## 2. Boolean controller vocabulary -/


private def roleEq (c : AbsController) (r : SpliceRole) : Bool :=
  decide (c.spliceRole = r)


private def bImp (a b : Bool) : Bool := (!a) || b


private def setControl
    (c : AbsController) (r : SpliceRole) (p : Bool) : AbsController :=
  { spliceRole := r, repairPending := p, acquireTicket := false }


private def clearControl (c : AbsController) : AbsController :=
  setControl c .none false


private def setTicket (c : AbsController) (b : Bool) : AbsController :=
  { c with acquireTicket := b }


private def clearTicket (c : AbsController) : AbsController :=
  setTicket c false


private def clearPending (c : AbsController) : AbsController :=
  { c with repairPending := false, acquireTicket := false }


private def fenceCtl (_ : AbsController) : AbsController :=
  { spliceRole := .none, repairPending := false, acquireTicket := true }


private def settleCtl (_ : AbsController) : AbsController :=
  { spliceRole := .predecessorArmed,
    repairPending := false, acquireTicket := false }


private def reservedFront (c : AbsController) : Bool :=
  roleEq c .front && c.repairPending


private def hostFence (c : AbsController) : Bool :=
  roleEq c .none && !c.repairPending && c.acquireTicket


private def targetClear (c : AbsController) : Bool :=
  roleEq c .none && !c.repairPending


private def pendingPred (c : AbsController) : Bool :=
  roleEq c .predecessorArmed && c.repairPending


private def settledPred (c : AbsController) : Bool :=
  roleEq c .predecessorArmed && !c.repairPending


private def victimPending (c : AbsController) : Bool :=
  roleEq c .victimArmed && c.repairPending


private def victimClear (c : AbsController) : Bool :=
  roleEq c .victimArmed && !c.repairPending


private def frontClear (c : AbsController) : Bool :=
  roleEq c .front && !c.repairPending


private def malformedPending (c : AbsController) : Bool :=
  c.repairPending &&
    !roleEq c .predecessorArmed &&
    !roleEq c .front &&
    !roleEq c .victimArmed


private def pendingOwnerHold (l r : AbsController) : Bool :=
  roleEq l .predecessorArmed && l.repairPending &&
    reservedFront r && !l.acquireTicket && !r.acquireTicket


private def pairCovered (l r : AbsController) : Bool :=
  reservedFront l ||
  pendingPred r ||
  (settledPred l &&
    (reservedFront r || victimPending r || pendingPred r)) ||
  hostFence l ||
  pendingOwnerHold l r


/-! ## 3. Physical summaries and exact guard projections -/


private def inputPhys (v : RiskView) : AbsPairPhys :=
  { leaderL := v.inLeaderL, leaderR := v.inLeaderR,
    aligned := v.alignedBefore, labelEqL := true, labelEqR := true }


private def hostPhys (v : RiskView) : AbsPairPhys :=
  { leaderL := v.hostLeaderL, leaderR := v.hostLeaderR,
    aligned := v.alignedHost,
    labelEqL := v.hostLabelEqL, labelEqR := v.hostLabelEqR }


/-- `repairResponder` keeps both leaders, keeps the left label, and writes the
right successor label.  The new right label equals the old one exactly when
the input pair was already aligned. -/
private def relabelPhys (v : RiskView) : AbsPairPhys :=
  { leaderL := v.inLeaderL, leaderR := v.inLeaderR,
    aligned := true, labelEqL := true, labelEqR := v.alignedBefore }


private def keepOut (v : RiskView)
    (l r : AbsController) : AbsOut :=
  { left := l, right := r, phys := inputPhys v }


private def hostOut (v : RiskView)
    (l r : AbsController) : AbsOut :=
  { left := l, right := r, phys := hostPhys v }


private def relabelOut (v : RiskView)
    (l r : AbsController) : AbsOut :=
  { left := l, right := r, phys := relabelPhys v }


/-- `ldc`: old left leader and selected-host left output follower. -/
private def gLdc (v : RiskView) : Bool :=
  v.inLeaderL && !v.hostLeaderL


/-- `LocalPreparedBarrier` after the existing prepared leader/label frames. -/
private def gLocalBarrier (v : RiskView) : Bool :=
  !v.inLeaderR && !v.alignedBefore


private def gRightFollowerRelabelled (v : RiskView) : Bool :=
  roleEq v.right .none && !v.right.repairPending &&
    !v.hostLeaderR && !v.hostLabelEqR


private def gMoveAcquireFront (v : RiskView) : Bool :=
  reservedFront v.left && !v.inLeaderL && v.left.acquireTicket &&
  reservedFront v.right && !v.inLeaderR && !v.right.acquireTicket &&
  !gLocalBarrier v


private def gArmA (v : RiskView) : Bool :=
  roleEq v.left .none && roleEq v.right .none &&
  !v.left.repairPending && !v.right.repairPending && gLdc v


private def gArmB (v : RiskView) : Bool :=
  roleEq v.left .none && !v.left.repairPending &&
  roleEq v.right .victimArmed && !v.right.repairPending && v.inLeaderR


private def gDelete (v : RiskView) : Bool :=
  roleEq v.left .front && roleEq v.right .front &&
  !v.left.repairPending && !v.right.repairPending && gLdc v


private def gPendingHold (v : RiskView) : Bool :=
  roleEq v.left .victimArmed && roleEq v.right .front &&
  !v.left.repairPending && !v.right.repairPending && gLdc v


private def gPendingAbort (v : RiskView) : Bool :=
  roleEq v.left .victimArmed && roleEq v.right .front &&
  !v.left.repairPending && !v.right.repairPending &&
  v.inLeaderL && !gLdc v


private def gMoveCommit (v : RiskView) : Bool :=
  settledPred v.left && pendingPred v.right && !v.inLeaderR


private def gMoveStop (v : RiskView) : Bool :=
  settledPred v.left && reservedFront v.right && !gLocalBarrier v


private def gMoveSeek (v : RiskView) : Bool :=
  settledPred v.left && reservedFront v.right && gLocalBarrier v


private def gMoveSeekHold (v : RiskView) : Bool :=
  settledPred v.left && victimPending v.right && !v.inLeaderR


private def gPendingOwnerAbort (v : RiskView) : Bool :=
  pendingPred v.right && !settledPred v.left


private def gPendingOwnerHold (v : RiskView) : Bool :=
  pendingPred v.left


private def gMoveAcquireLegacy (v : RiskView) : Bool :=
  victimPending v.left && !v.inLeaderL &&
    reservedFront v.right && !v.right.acquireTicket


private def gMoveAcquireAbort (v : RiskView) : Bool :=
  victimPending v.left && !v.inLeaderL && !reservedFront v.right


private def gOrphanReservedFront (v : RiskView) : Bool :=
  reservedFront v.right && !roleEq v.left .predecessorArmed


private def gMarkedHold (v : RiskView) : Bool :=
  !roleEq v.left .none ||
    (!roleEq v.right .none &&
      (v.left.repairPending || v.right.repairPending))


private def gRightStale (v : RiskView) : Bool :=
  roleEq v.left .none && !v.left.repairPending && !v.left.acquireTicket &&
  roleEq v.right .predecessorArmed &&
  !v.right.repairPending && !v.right.acquireTicket


private def gFenceBusy (v : RiskView) : Bool :=
  hostFence v.left && gLocalBarrier v && reservedFront v.right


private def gFenceAdvance (v : RiskView) : Bool :=
  hostFence v.left && gLocalBarrier v && targetClear v.right


private def gOrphanVictim (v : RiskView) : Bool :=
  victimPending v.right && !settledPred v.left


private def gOwnedPendingVictim (v : RiskView) : Bool :=
  settledPred v.left && victimPending v.right


private def gOwnerlessPendingPred (v : RiskView) : Bool :=
  roleEq v.left .none && pendingPred v.right


private def gLeftScrub (v : RiskView) : Bool :=
  victimClear v.left || frontClear v.left || malformedPending v.left


/-! ## 4. Abstract writers and the rowB9 priority tree -/


private def wFenceLeftStop (v : RiskView) : AbsOut :=
  keepOut v (clearTicket v.left) v.right


private def wFenceLeftAdvance (v : RiskView) : AbsOut :=
  relabelOut v (clearTicket v.left) (setTicket v.right true)


private def wFenceBusy (v : RiskView) : AbsOut :=
  relabelOut v v.left v.right


private def wHandoff (v : RiskView) : AbsOut :=
  keepOut v
    (setControl v.left .predecessorArmed false)
    (setControl v.right .front true)


private def wMoveAcquire (v : RiskView) : AbsOut :=
  keepOut v (setControl v.left .predecessorArmed true) v.right


private def wArmA (v : RiskView) : AbsOut :=
  keepOut v
    (setControl v.left .victimArmed false)
    (setControl v.right .front false)


private def wArmB (v : RiskView) : AbsOut :=
  keepOut v
    (setControl v.left .predecessorArmed false)
    (setControl v.right .front false)


private def wDelete (v : RiskView) : AbsOut :=
  hostOut v
    (setControl v.left .predecessorArmed true)
    (setControl v.right .front true)


private def wPendingAbort (v : RiskView) : AbsOut :=
  keepOut v (clearControl v.left) (clearControl v.right)


private def wMoveCommit (v : RiskView) : AbsOut :=
  relabelOut v
    (clearControl v.left)
    (setControl v.right .predecessorArmed false)


private def wMoveStop (v : RiskView) : AbsOut :=
  if v.inLeaderR then
    keepOut v (clearControl v.left) (clearControl v.right)
  else
    keepOut v (clearControl v.left) (clearTicket v.right)


private def wMoveSeek (v : RiskView) : AbsOut :=
  keepOut v v.left (setTicket v.right true)


private def wPendingOwnerAbort (v : RiskView) : AbsOut :=
  keepOut v v.left (clearTicket v.right)


private def wClearRight (v : RiskView) : AbsOut :=
  keepOut v v.left (clearControl v.right)


private def wClearLeft (v : RiskView) : AbsOut :=
  keepOut v (clearControl v.left) v.right


private def wClearPendingLeft (v : RiskView) : AbsOut :=
  keepOut v (clearPending v.left) v.right


private def wClearPendingRight (v : RiskView) : AbsOut :=
  keepOut v v.left (clearPending v.right)


private def wOrdinaryHost (v : RiskView) : AbsOut :=
  let rr := clearTicket v.right
  let rr := if gRightFollowerRelabelled v then setTicket rr true else rr
  hostOut v (clearTicket v.left) rr


private def wPhysicalHold (v : RiskView) : AbsOut :=
  let rr := if gRightFollowerRelabelled v then setTicket v.right true else v.right
  hostOut v v.left rr


private def wPhysicalFence (v : RiskView) : AbsOut :=
  let q := wPhysicalHold v
  { left := q.left, right := fenceCtl q.right, phys := q.phys }


private def wHoldRepair (v : RiskView) : AbsOut :=
  if reservedFront v.right then
    keepOut v v.left (fenceCtl v.right)
  else if pendingPred v.right then
    keepOut v v.left (settleCtl v.right)
  else if victimPending v.right then
    wClearRight v
  else if victimClear v.right || frontClear v.right || malformedPending v.right then
    wClearRight v
  else
    keepOut v v.left v.right


private def absRow7 (v : RiskView) : AbsOut :=
  if hostFence v.left then
    if gLocalBarrier v then
      if targetClear v.right then wFenceLeftAdvance v
      else keepOut v v.left v.right
    else wFenceLeftStop v
  else if hostFence v.right then keepOut v v.left v.right
  else if gMoveAcquireFront v then wMoveAcquire v
  else if gArmA v then wArmA v
  else if gArmB v then wArmB v
  else if gDelete v then wDelete v
  else if gPendingHold v then keepOut v v.left v.right
  else if gPendingAbort v then wPendingAbort v
  else if gMoveCommit v then wMoveCommit v
  else if gMoveStop v then wMoveStop v
  else if gMoveSeek v then wMoveSeek v
  else if gMoveSeekHold v then keepOut v v.left v.right
  else if gPendingOwnerAbort v then wPendingOwnerAbort v
  else if gPendingOwnerHold v then keepOut v v.left v.right
  else if gMoveAcquireLegacy v then wMoveAcquire v
  else if gMoveAcquireAbort v then keepOut v (clearTicket v.left) v.right
  else if gOrphanReservedFront v then keepOut v v.left v.right
  else if reservedFront v.left then keepOut v v.left v.right
  else if victimClear v.right then wClearRight v
  else if victimClear v.left then wClearLeft v
  else if frontClear v.right then wClearRight v
  else if malformedPending v.left then wClearPendingLeft v
  else if malformedPending v.right then wClearPendingRight v
  else if roleEq v.left .predecessorArmed then wClearLeft v
  else if roleEq v.left .front then keepOut v v.left v.right
  else if gMarkedHold v then keepOut v v.left v.right
  else wOrdinaryHost v


private def absRow8 (v : RiskView) : AbsOut :=
  if gRightStale v then keepOut v v.left v.right else absRow7 v


private def absRow9 (v : RiskView) : AbsOut :=
  if gFenceBusy v then wFenceBusy v else absRow8 v


private def absRow10b (v : RiskView) : AbsOut :=
  if gFenceAdvance v then wHandoff v else absRow9 v


/-- V10c is quotiented away at this observation level.  If its guard is true,
`SameExceptStall` says row10b has exactly the input controller coordinates and
physical core; therefore stuttering and row10b have the same `AbsOut`. -/
private def absRow10c (v : RiskView) : AbsOut :=
  absRow10b v


private def absRow10dg (v : RiskView) : AbsOut :=
  if gOrphanReservedFront v then
    keepOut v v.left (fenceCtl v.right)
  else if gOrphanVictim v then
    wClearRight v
  else if gOwnedPendingVictim v then
    keepOut v (fenceCtl v.left) (fenceCtl v.right)
  else if gOwnerlessPendingPred v then
    keepOut v (fenceCtl v.left) (settleCtl v.right)
  else
    absRow10c v


private def absRow10g (v : RiskView) : AbsOut :=
  if v.row10dgStutters then
    if pendingPred v.left then
      keepOut v v.left v.right
    else if victimClear v.right then
      wClearRight v
    else if frontClear v.right then
      wClearRight v
    else if malformedPending v.right then
      wClearRight v
    else if roleEq v.right .predecessorArmed then
      if v.right.repairPending then
        if reservedFront v.left then
          keepOut v v.left (settleCtl v.right)
        else if gLeftScrub v then
          wClearLeft v
        else
          keepOut v v.left v.right
      else
        wPhysicalFence v
    else
      wPhysicalHold v
  else
    absRow10dg v


/-- The finite row whose controller priority is rowB9's priority. -/
def absRowB9 (v : RiskView) : AbsOut :=
  if gLdc v then
    if reservedFront v.left then wHoldRepair v else wDelete v
  else
    absRow10g v


/-! ## 5. Abstract recovery risk -/


private def bInd (b : Bool) : Nat := if b then 1 else 0


private def badTicket (c : AbsController) : Bool :=
  c.acquireTicket && !(reservedFront c || hostFence c)


private def badBacking (l r : AbsController) : Bool :=
  pendingPred l && !(reservedFront r && !r.acquireTicket)


private def danger (leaderL leaderR aligned : Bool) : Bool :=
  !leaderL && !leaderR && !aligned


private def hole (l r : AbsController)
    (leaderL leaderR aligned : Bool) : Bool :=
  danger leaderL leaderR aligned && !pairCovered l r


def absTicketRisk (c : AbsController) : Nat :=
  bInd (badTicket c)


def absEdgeRisk (l r : AbsController)
    (leaderL leaderR aligned : Bool) : Nat :=
  2 * bInd (badBacking l r) + bInd (hole l r leaderL leaderR aligned)


private def absGarbage (v : RiskView) : Bool :=
  badTicket v.left || badTicket v.right || badBacking v.left v.right ||
    hole v.left v.right v.inLeaderL v.inLeaderR v.alignedBefore


private def absInputClean (v : RiskView) : Bool := !absGarbage v


/-- One unchanged outside endpoint, enough for incoming/outgoing edge risks. -/
structure AbsBoundary where
  ctl : AbsController
  leader : Bool
  oldAligned : Bool
  deriving DecidableEq, Repr


def allBoundaries : List AbsBoundary :=
  allControllers.flatMap fun c =>
    allBools.flatMap fun lead =>
      allBools.map fun a => { ctl := c, leader := lead, oldAligned := a }


private def incomingBefore (v : RiskView) (b : AbsBoundary) : Nat :=
  absEdgeRisk b.ctl v.left b.leader v.inLeaderL b.oldAligned


private def incomingAfterExact
    (o : AbsOut) (b : AbsBoundary) (alignedAfter : Bool) : Nat :=
  absEdgeRisk b.ctl o.left b.leader o.phys.leaderL alignedAfter


private def incomingAfterWorst (o : AbsOut) (b : AbsBoundary) : Nat :=
  incomingAfterExact o b (b.oldAligned && o.phys.labelEqL)


private def outgoingBefore (v : RiskView) (b : AbsBoundary) : Nat :=
  absEdgeRisk v.right b.ctl v.inLeaderR b.leader b.oldAligned


private def outgoingAfterExact
    (o : AbsOut) (b : AbsBoundary) (alignedAfter : Bool) : Nat :=
  absEdgeRisk o.right b.ctl o.phys.leaderR b.leader alignedAfter


private def outgoingAfterWorst (o : AbsOut) (b : AbsBoundary) : Nat :=
  outgoingAfterExact o b (b.oldAligned && o.phys.labelEqR)


private def reverseBefore (v : RiskView) (oldAligned : Bool) : Nat :=
  absEdgeRisk v.right v.left v.inLeaderR v.inLeaderL oldAligned


private def reverseAfterExact
    (o : AbsOut) (alignedAfter : Bool) : Nat :=
  absEdgeRisk o.right o.left o.phys.leaderR o.phys.leaderL alignedAfter


private def reverseAfterWorst (o : AbsOut) (oldAligned : Bool) : Nat :=
  reverseAfterExact o
    (oldAligned && o.phys.labelEqR && o.phys.labelEqL)


private def riskLe (a b : Nat) : Bool := decide (a ≤ b)


/-- Literal six-field abstract analogue of `PairRiskNoRaise`.
When an endpoint label changes, the boundary checker pessimistically treats the
new outside alignment as false.  Therefore a true result implies the concrete
pointwise field for every actual outside label. -/
def absPairRiskNoRaiseAt (v : RiskView) : Bool :=
  let o := absRowB9 v
  riskLe (absTicketRisk o.left) (absTicketRisk v.left) &&
  riskLe (absTicketRisk o.right) (absTicketRisk v.right) &&
  allBoundaries.all (fun b =>
    riskLe (incomingAfterWorst o b) (incomingBefore v b)) &&
  riskLe
    (absEdgeRisk o.left o.right
      o.phys.leaderL o.phys.leaderR o.phys.aligned)
    (absEdgeRisk v.left v.right
      v.inLeaderL v.inLeaderR v.alignedBefore) &&
  allBoundaries.all (fun b =>
    riskLe (outgoingAfterWorst o b) (outgoingBefore v b)) &&
  allBools.all (fun a =>
    riskLe (reverseAfterWorst o a) (reverseBefore v a))


/-! ## 6. Admissibility and finite statement -/


private def absOutEqInput (v : RiskView) (o : AbsOut) : Bool :=
  decide (o.left = v.left ∧ o.right = v.right ∧ o.phys = inputPhys v)


/-- Exactly the cheap physical consistency facts used by refinement.
The final clause records the consequence of the exact `row10dgH = (l,r)` bit. -/
def absViewAdmissible (v : RiskView) : Bool :=
  bImp (!v.inLeaderL) v.hostLabelEqL &&
  bImp v.inLeaderR v.hostLeaderR &&
  bImp
    (!v.inLeaderL && !v.inLeaderR &&
      !v.hostLeaderL && !v.hostLeaderR && v.alignedBefore)
    v.alignedHost &&
  bImp (v.hostLabelEqL && v.hostLabelEqR)
    (decide (v.alignedHost = v.alignedBefore)) &&
  bImp v.row10dgStutters (absOutEqInput v (absRow10dg v))


/-- Main finite obligation.  Intended proof: reduce this to
`absPairRiskNoRaiseCheck = true` and discharge the closed computation by
kernel `decide` (not `native_decide`). -/
def absPairRiskNoRaise : Prop :=
  ∀ v : RiskView,
    absViewAdmissible v = true →
    absInputClean v = true →
    absPairRiskNoRaiseAt v = true


/-- Executable form of the preceding Prop.  The short-circuit means the 64
boundary contexts are visited only for admissible non-garbage views. -/
def absPairRiskNoRaiseCheck : Bool :=
  allRiskViews.all fun v =>
    !(absViewAdmissible v && absInputClean v) || absPairRiskNoRaiseAt v


/-! ## 7. Concrete view and refinement statement -/


private def controllerOf (u : Cell psi kappa tau) : AbsController :=
  { spliceRole := role u.carrier,
    repairPending := u.carrier.repairPending,
    acquireTicket := u.acquireTicket }


noncomputable def riskViewOf
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : RiskView := by
  classical
  let hp := host.row (base l) (base r)
  exact
    { left := controllerOf l,
      right := controllerOf r,
      inLeaderL := B9Host.leader (base l),
      inLeaderR := B9Host.leader (base r),
      hostLeaderL := B9Host.leader hp.1,
      hostLeaderR := B9Host.leader hp.2,
      alignedBefore := decide (B9Host.Aligned (base l) (base r)),
      alignedHost := decide (B9Host.Aligned hp.1 hp.2),
      hostLabelEqL := decide (B9Host.label hp.1 = B9Host.label (base l)),
      hostLabelEqR := decide (B9Host.label hp.2 = B9Host.label (base r)),
      row10dgStutters := decide
        (B9SpliceTableHost.row10dgH host hpsi l r = (l, r)) }


noncomputable def concreteOutPhys
    (l r wL wR : Cell psi kappa tau) : AbsPairPhys := by
  classical
  exact
    { leaderL := B9Host.leader (base wL),
      leaderR := B9Host.leader (base wR),
      aligned := decide (B9Host.Aligned (base wL) (base wR)),
      labelEqL := decide (B9Host.label (base wL) = B9Host.label (base l)),
      labelEqR := decide (B9Host.label (base wR) = B9Host.label (base r)) }


noncomputable def concreteTicketRisk
    (u : Cell psi kappa tau) : Nat := by
  classical
  exact if BadTicket u then 1 else 0


noncomputable def concreteEdgeRisk
    (hpsi : 0 < psi) (l r : Cell psi kappa tau) : Nat := by
  classical
  exact 2 * (if BadBacking l r then 1 else 0) +
    (if Hole hpsi l r then 1 else 0)


noncomputable def incomingBoundaryOf
    (x l : Cell psi kappa tau) : AbsBoundary := by
  classical
  exact
    { ctl := controllerOf x,
      leader := B9Host.leader (base x),
      oldAligned := decide (B9Host.Aligned (base x) (base l)) }


noncomputable def outgoingBoundaryOf
    (r x : Cell psi kappa tau) : AbsBoundary := by
  classical
  exact
    { ctl := controllerOf x,
      leader := B9Host.leader (base x),
      oldAligned := decide (B9Host.Aligned (base r) (base x)) }


/-- Exact statement that the concrete six risk observations are represented by
the abstract output.  Boundary alignments after the write are supplied by the
concrete cells; the finite theorem used the stronger pessimistic value. -/
def ConcreteRiskAgreement
    (hpsi : 0 < psi) (l r wL wR : Cell psi kappa tau)
    (v : RiskView) : Prop :=
  let o := absRowB9 v
  controllerOf wL = o.left ∧
  controllerOf wR = o.right ∧
  concreteOutPhys l r wL wR = o.phys ∧
  concreteTicketRisk l = absTicketRisk v.left ∧
  concreteTicketRisk r = absTicketRisk v.right ∧
  concreteTicketRisk wL = absTicketRisk o.left ∧
  concreteTicketRisk wR = absTicketRisk o.right ∧
  concreteEdgeRisk hpsi l r =
    absEdgeRisk v.left v.right
      v.inLeaderL v.inLeaderR v.alignedBefore ∧
  concreteEdgeRisk hpsi wL wR =
    absEdgeRisk o.left o.right
      o.phys.leaderL o.phys.leaderR o.phys.aligned ∧
  (∀ x : Cell psi kappa tau,
    concreteEdgeRisk hpsi x wL =
      incomingAfterExact o (incomingBoundaryOf x l)
        (decide (B9Host.Aligned (base x) (base wL)))) ∧
  (∀ x : Cell psi kappa tau,
    concreteEdgeRisk hpsi wR x =
      outgoingAfterExact o (outgoingBoundaryOf r x)
        (decide (B9Host.Aligned (base wR) (base x)))) ∧
  concreteEdgeRisk hpsi wR wL =
    reverseAfterExact o
      (decide (B9Host.Aligned (base wR) (base wL)))


/-- Second main obligation.  This is the only theorem that should ever inspect
concrete rowB9 / host definitions after the finite abstraction is installed. -/
def rowB9_refines_abs : Prop :=
  ∀ {psi kappa tau : Nat}
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau),
    B9Host.SpliceLaws host →
      let v := riskViewOf host hpsi l r
      let w := B9SpliceTableHost.rowB9 host hpsi l r
      absViewAdmissible v = true ∧
      ((Garbage hpsi l r) ↔ absGarbage v = true) ∧
      ConcreteRiskAgreement hpsi l r w.1 w.2 v


end B9RiskAbstraction

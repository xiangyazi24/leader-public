import Leader.Wu.Splice.FollowerStopSeekHold

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceControllerR1TableV6

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerV3Safety
open B9SpliceControllerR1TableV4
open B9SpliceControllerV4Safety

variable {n psi width kappa tau : Nat}

/-! ## 1. V6 carrier and strengthened invariant -/

/-- V6 is the factor-eight V4 carrier plus one acquisition-provenance bit. -/
structure R1AgentStateV6 (psi kappa tau : Nat) where
  carrier : R1AgentStateV4 psi kappa tau
  acquireTicket : Bool
  deriving DecidableEq, Repr

abbrev R1ConfigV6 (n psi kappa tau : Nat) :=
  Fin n -> R1AgentStateV6 psi kappa tau

/-- Forget only the new provenance coordinate. -/
def projectV6
    (C : R1ConfigV6 n psi kappa tau) : R1ConfigV4 n psi kappa tau :=
  fun i => (C i).carrier

/-- Canonical lift of an old state: old states carry no acquisition provenance. -/
def liftAgentV6
    (u : R1AgentStateV4 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  ⟨u, false⟩

def liftConfigV6
    (C : R1ConfigV4 n psi kappa tau) : R1ConfigV6 n psi kappa tau :=
  fun i => liftAgentV6 (C i)

/-- Change only the provenance bit. -/
def setTicketV6
    (u : R1AgentStateV6 psi kappa tau) (b : Bool) :
    R1AgentStateV6 psi kappa tau :=
  { u with acquireTicket := b }

def clearTicketV6
    (u : R1AgentStateV6 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  setTicketV6 u false

/-- Replace the old carrier and, because this is used for role-changing writes,
clear provenance at the same time. -/
def withCarrierClearTicketV6
    (u : R1AgentStateV6 psi kappa tau)
    (b : R1AgentStateV4 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  ⟨b, false⟩

/-- Every role-changing write uses this wrapper and therefore clears the bit. -/
def setControlV6
    (u : R1AgentStateV6 psi kappa tau)
    (r : SpliceRole) (pending : Bool) : R1AgentStateV6 psi kappa tau :=
  withCarrierClearTicketV6 u (setControl u.carrier r pending)

def clearControlV6
    (u : R1AgentStateV6 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  setControlV6 u .none false

/-- Malformed old `repairPending` cleanup also removes forged provenance. -/
def clearPendingV6
    (u : R1AgentStateV6 psi kappa tau) : R1AgentStateV6 psi kappa tau :=
  withCarrierClearTicketV6 u { u.carrier with repairPending := false }

@[simp] theorem carrier_setTicketV6
    (u : R1AgentStateV6 psi kappa tau) (b : Bool) :
    (setTicketV6 u b).carrier = u.carrier := rfl

@[simp] theorem ticket_setTicketV6
    (u : R1AgentStateV6 psi kappa tau) (b : Bool) :
    (setTicketV6 u b).acquireTicket = b := rfl

@[simp] theorem carrier_clearTicketV6
    (u : R1AgentStateV6 psi kappa tau) :
    (clearTicketV6 u).carrier = u.carrier := rfl

@[simp] theorem ticket_clearTicketV6
    (u : R1AgentStateV6 psi kappa tau) :
    (clearTicketV6 u).acquireTicket = false := rfl

@[simp] theorem carrier_setControlV6
    (u : R1AgentStateV6 psi kappa tau)
    (r : SpliceRole) (p : Bool) :
    (setControlV6 u r p).carrier = setControl u.carrier r p := rfl

@[simp] theorem ticket_setControlV6
    (u : R1AgentStateV6 psi kappa tau)
    (r : SpliceRole) (p : Bool) :
    (setControlV6 u r p).acquireTicket = false := rfl

@[simp] theorem role_setControlV6
    (u : R1AgentStateV6 psi kappa tau)
    (r : SpliceRole) (p : Bool) :
    role (setControlV6 u r p).carrier = r := by
  rfl

@[simp] theorem pending_setControlV6
    (u : R1AgentStateV6 psi kappa tau)
    (r : SpliceRole) (p : Bool) :
    (setControlV6 u r p).carrier.repairPending = p := by
  rfl

@[simp] theorem role_clearControlV6
    (u : R1AgentStateV6 psi kappa tau) :
    role (clearControlV6 u).carrier = .none := by
  rfl

@[simp] theorem pending_clearControlV6
    (u : R1AgentStateV6 psi kappa tau) :
    (clearControlV6 u).carrier.repairPending = false := by
  rfl

@[simp] theorem ticket_clearControlV6
    (u : R1AgentStateV6 psi kappa tau) :
    (clearControlV6 u).acquireTicket = false := by
  rfl

@[simp] theorem role_clearPendingV6
    (u : R1AgentStateV6 psi kappa tau) :
    role (clearPendingV6 u).carrier = role u.carrier := by
  rfl

@[simp] theorem pending_clearPendingV6
    (u : R1AgentStateV6 psi kappa tau) :
    (clearPendingV6 u).carrier.repairPending = false := by
  rfl

@[simp] theorem ticket_clearPendingV6
    (u : R1AgentStateV6 psi kappa tau) :
    (clearPendingV6 u).acquireTicket = false := by
  rfl

/-- A true provenance bit is meaningful only on the old reserved-front shape. -/
def TicketShapeV6 (u : R1AgentStateV6 psi kappa tau) : Prop :=
  u.acquireTicket = true -> ReservedFrontHoldGuard u.carrier

/-- Edge-local controller part of the strengthened invariant. -/
def EdgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  TicketShapeV6 l /\
  TicketShapeV6 r /\
  (role l.carrier = .predecessorArmed ->
    l.carrier.repairPending = true ->
      ReservedFrontHoldGuard r.carrier /\ r.acquireTicket = false)

/-- Global provenance discipline.

* every true ticket is on `front,true`;
* every pending predecessor is backed by an explicitly unticketed `front,true`.
-/
def ProvenanceSafeV6
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) : Prop :=
  (forall i, TicketShapeV6 (C i)) /\
  (forall i,
    role (C i).carrier = .predecessorArmed ->
    (C i).carrier.repairPending = true ->
      ReservedFrontHoldGuard (C (ring.rightNeighbor i)).carrier /\
      (C (ring.rightNeighbor i)).acquireTicket = false)

/-- V6 safety is exactly the old V3 safety plus the provenance discipline. -/
def SpliceSafeR1V6
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Prop :=
  SpliceSafeR1V3 hpsi ring (projectV6 C) /\
  ProvenanceSafeV6 ring C

/-- A ticketed site cannot simultaneously be the backing front of an incoming
pending predecessor.  This is the non-local fact that v5 lacked. -/
theorem ticketed_site_not_backing
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau)
    (hsafe : SpliceSafeR1V6 hpsi ring C)
    (i e : Fin n)
    (hre : ring.rightNeighbor i = e)
    (ht : (C e).acquireTicket = true) :
    ¬ (role (C i).carrier = .predecessorArmed /\
       (C i).carrier.repairPending = true) := by
  intro hp
  have hb := hsafe.2.2 i hp.1 hp.2
  rw [hre] at hb
  have hbad : (true : Bool) = false := ht.symm.trans hb.2
  cases hbad

private theorem ticket_false_of_shape_of_not_reserved
    (u : R1AgentStateV6 psi kappa tau)
    (ht : TicketShapeV6 u)
    (hn : ¬ ReservedFrontHoldGuard u.carrier) :
    u.acquireTicket = false := by
  cases h : u.acquireTicket with
  | false => rfl
  | true =>
      exact False.elim (hn (ht h))

/-! ## 2. Closed guard decidability -/

private instance instDecidableReservedFrontV6
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (ReservedFrontHoldGuard u.carrier) := by
  unfold ReservedFrontHoldGuard
  infer_instance

private instance instDecidableArmAV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (ArmAGuard hpsi hwidth hle l.carrier r.carrier) := by
  unfold ArmAGuard LeftDeletionCandidate
  infer_instance

private instance instDecidableArmBV6
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (ArmBGuard l.carrier r.carrier) := by
  unfold ArmBGuard
  infer_instance

private instance instDecidableDeleteV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (DeleteGuard hpsi hwidth hle l.carrier r.carrier) := by
  unfold DeleteGuard LeftDeletionCandidate
  infer_instance

private instance instDecidablePendingHoldV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (PendingHoldGuard hpsi hwidth hle l.carrier r.carrier) := by
  unfold PendingHoldGuard LeftDeletionCandidate
  infer_instance

private instance instDecidablePendingAbortV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (PendingAbortGuard hpsi hwidth hle l.carrier r.carrier) := by
  unfold PendingAbortGuard LeftDeletionCandidate
  infer_instance

private instance instDecidableMoveCommitV6
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveCommitGuard l.carrier r.carrier) := by
  unfold MoveCommitGuard
  infer_instance

private instance instDecidableMoveStopV6
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveStopGuardV3 hpsi l.carrier r.carrier) := by
  unfold MoveStopGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableMoveSeekV6
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveSeekGuardV3 hpsi l.carrier r.carrier) := by
  unfold MoveSeekGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableMoveSeekHoldV6
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveSeekHoldGuardV3 l.carrier r.carrier) := by
  unfold MoveSeekHoldGuardV3
  infer_instance

private instance instDecidablePendingOwnerAbortV6
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (PendingOwnerAbortGuardV3 l.carrier r.carrier) := by
  unfold PendingOwnerAbortGuardV3
  infer_instance

private instance instDecidableMoveAcquireV6
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveAcquireGuardV3 l.carrier r.carrier) := by
  unfold MoveAcquireGuardV3 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableMoveAcquireAbortV6
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveAcquireAbortGuardV3 l.carrier r.carrier) := by
  unfold MoveAcquireAbortGuardV3 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableOrphanReservedFrontV6
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (OrphanReservedFrontGuardV3 l.carrier r.carrier) := by
  unfold OrphanReservedFrontGuardV3 ReservedFrontHoldGuard
  infer_instance

/-! ## 3. V6 guards and writes -/

/-- New front/front ACQUIRE.  The left front must carry the request ticket and
the right backing front must be explicitly unticketed. -/
def MoveAcquireFrontGuardV6
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  ReservedFrontHoldGuard l.carrier /\
  l.carrier.splice.base.core.core.leader = false /\
  l.acquireTicket = true /\
  ReservedFrontHoldGuard r.carrier /\
  r.carrier.splice.base.core.core.leader = false /\
  r.acquireTicket = false /\
  ¬ LocalPreparedBarrier hpsi l.carrier r.carrier

private instance instDecidableMoveAcquireFrontV6
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveAcquireFrontGuardV6 hpsi l r) := by
  unfold MoveAcquireFrontGuardV6 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

/-- The legacy V3 authenticated-victim ACQUIRE is retained only when its target
is an unticketed backing front. -/
def MoveAcquireLegacyGuardV6
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  MoveAcquireGuardV3 l.carrier r.carrier /\ r.acquireTicket = false

private instance instDecidableMoveAcquireLegacyV6
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveAcquireLegacyGuardV6 l r) := by
  unfold MoveAcquireLegacyGuardV6
  infer_instance

/-- Generic victim cleanup is now restricted to the non-certificate false-bit
shape. -/
def VictimRightScrubGuardV6
    (r : R1AgentStateV6 psi kappa tau) : Prop :=
  role r.carrier = .victimArmed /\ r.carrier.repairPending = false

def VictimLeftScrubGuardV6
    (l : R1AgentStateV6 psi kappa tau) : Prop :=
  role l.carrier = .victimArmed /\ l.carrier.repairPending = false

/-- Generic right-front cleanup likewise removes only unreserved `front,false`. -/
def FrontRightScrubGuardV6
    (r : R1AgentStateV6 psi kappa tau) : Prop :=
  role r.carrier = .front /\ r.carrier.repairPending = false

def MalformedLeftPendingGuardV6
    (l : R1AgentStateV6 psi kappa tau) : Prop :=
  l.carrier.repairPending = true /\
  role l.carrier ≠ .predecessorArmed /\
  role l.carrier ≠ .front /\
  role l.carrier ≠ .victimArmed

def MalformedRightPendingGuardV6
    (r : R1AgentStateV6 psi kappa tau) : Prop :=
  r.carrier.repairPending = true /\
  role r.carrier ≠ .predecessorArmed /\
  role r.carrier ≠ .front /\
  role r.carrier ≠ .victimArmed

def MarkedHoldGuardV6
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  role l.carrier ≠ .none \/
    (role r.carrier ≠ .none /\
      (l.carrier.repairPending = true \/ r.carrier.repairPending = true))

def armAWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (setControlV6 l .victimArmed false,
    setControlV6 r .front false)

def armBWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (setControlV6 l .predecessorArmed false,
    setControlV6 r .front false)

def deleteWriteV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :=
  let q := BirthShortDoneTerminalHost.row
    hpsi hwidth hle l.carrier.splice.base r.carrier.splice.base
  (withCarrierClearTicketV6 l
      (setControl (setPhysical l.carrier q.1) .predecessorArmed true),
    withCarrierClearTicketV6 r
      (setControl (setPhysical r.carrier q.2) .front true))

def pendingHoldWriteV6
    (l r : R1AgentStateV6 psi kappa tau) := (l, r)

def pendingAbortWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (clearControlV6 l, clearControlV6 r)

def moveCommitWriteV6
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :=
  (clearControlV6 l,
    withCarrierClearTicketV6 r
      (setControl (repairResponder hpsi l.carrier r.carrier)
        .predecessorArmed false))

/-- V4 STOP is retained, but the follower case also consumes a stale request
bit on the kept front. -/
def moveStopWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  if r.carrier.splice.base.core.core.leader = true then
    (clearControlV6 l, clearControlV6 r)
  else
    (clearControlV6 l, clearTicketV6 r)

/-- SEEK no longer consumes `front,true`: it mints the provenance ticket there. -/
def moveSeekWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (l, setTicketV6 r true)

def moveSeekHoldWriteV6
    (l r : R1AgentStateV6 psi kappa tau) := (l, r)

/-- The old unsafe pending-owner abort now removes only impossible provenance. -/
def pendingOwnerAbortWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (l, clearTicketV6 r)

def pendingOwnerHoldWriteV6
    (l r : R1AgentStateV6 psi kappa tau) := (l, r)

def moveAcquireFrontWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (setControlV6 l .predecessorArmed true, r)

def moveAcquireLegacyWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (setControlV6 l .predecessorArmed true, r)

/-- The old unsafe victim abort also removes only impossible provenance. -/
def moveAcquireAbortWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (clearTicketV6 l, r)

/-- A reserved front is a safety certificate; an orphan observation is HOLD. -/
def orphanReservedFrontWriteV6
    (l r : R1AgentStateV6 psi kappa tau) := (l, r)

def reservedFrontHoldWriteV6
    (l r : R1AgentStateV6 psi kappa tau) := (l, r)

def victimRightScrubWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (l, clearControlV6 r)

def victimLeftScrubWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (clearControlV6 l, r)

def frontRightScrubWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (l, clearControlV6 r)

def malformedLeftPendingWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (clearPendingV6 l, r)

def malformedRightPendingWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (l, clearPendingV6 r)

def predecessorLeftScrubWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :=
  (clearControlV6 l, r)

def leftFrontHoldWriteV6
    (l r : R1AgentStateV6 psi kappa tau) := (l, r)

def markedHoldWriteV6
    (l r : R1AgentStateV6 psi kappa tau) := (l, r)

/-- The ordinary host row keeps the old physical action but clears both
provenance bits. -/
def ordinaryHostWriteV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :=
  let q := ordinaryRow hpsi hwidth hle l.carrier r.carrier
  (withCarrierClearTicketV6 l q.1,
    withCarrierClearTicketV6 r q.2)

/-! ## 4. Executable V6 table -/

/-- V6 keeps the V3/V4 priority order, with front/front ACQUIRE ahead of the
orphan-front cases exactly as in v5. -/
instance instDecidableMarkedHoldGuardV6Local (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MarkedHoldGuardV6 l r) := by
  unfold MarkedHoldGuardV6
  (try dsimp only)
  infer_instance

instance instDecidableMalformedRightPendingGuardV6Local (r : R1AgentStateV6 psi kappa tau) :
    Decidable (MalformedRightPendingGuardV6 r) := by
  unfold MalformedRightPendingGuardV6
  (try dsimp only)
  infer_instance

instance instDecidableMalformedLeftPendingGuardV6Local (l : R1AgentStateV6 psi kappa tau) :
    Decidable (MalformedLeftPendingGuardV6 l) := by
  unfold MalformedLeftPendingGuardV6
  (try dsimp only)
  infer_instance

instance instDecidableFrontRightScrubGuardV6Local (r : R1AgentStateV6 psi kappa tau) :
    Decidable (FrontRightScrubGuardV6 r) := by
  unfold FrontRightScrubGuardV6
  (try dsimp only)
  infer_instance

instance instDecidableVictimLeftScrubGuardV6Local (l : R1AgentStateV6 psi kappa tau) :
    Decidable (VictimLeftScrubGuardV6 l) := by
  unfold VictimLeftScrubGuardV6
  (try dsimp only)
  infer_instance

instance instDecidableVictimRightScrubGuardV6Local (r : R1AgentStateV6 psi kappa tau) :
    Decidable (VictimRightScrubGuardV6 r) := by
  unfold VictimRightScrubGuardV6
  (try dsimp only)
  infer_instance

def rowV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if MoveAcquireFrontGuardV6 hpsi l r then
    moveAcquireFrontWriteV6 l r
  else if ArmAGuard hpsi hwidth hle l.carrier r.carrier then
    armAWriteV6 l r
  else if ArmBGuard l.carrier r.carrier then
    armBWriteV6 l r
  else if DeleteGuard hpsi hwidth hle l.carrier r.carrier then
    deleteWriteV6 hpsi hwidth hle l r
  else if PendingHoldGuard hpsi hwidth hle l.carrier r.carrier then
    pendingHoldWriteV6 l r
  else if PendingAbortGuard hpsi hwidth hle l.carrier r.carrier then
    pendingAbortWriteV6 l r
  else if MoveCommitGuard l.carrier r.carrier then
    moveCommitWriteV6 hpsi l r
  else if MoveStopGuardV3 hpsi l.carrier r.carrier then
    moveStopWriteV6 l r
  else if MoveSeekGuardV3 hpsi l.carrier r.carrier then
    moveSeekWriteV6 l r
  else if MoveSeekHoldGuardV3 l.carrier r.carrier then
    moveSeekHoldWriteV6 l r
  else if PendingOwnerAbortGuardV3 l.carrier r.carrier then
    pendingOwnerAbortWriteV6 l r
  else if role l.carrier = .predecessorArmed /\
      l.carrier.repairPending = true then
    pendingOwnerHoldWriteV6 l r
  else if MoveAcquireLegacyGuardV6 l r then
    moveAcquireLegacyWriteV6 l r
  else if MoveAcquireAbortGuardV3 l.carrier r.carrier then
    moveAcquireAbortWriteV6 l r
  else if OrphanReservedFrontGuardV3 l.carrier r.carrier then
    orphanReservedFrontWriteV6 l r
  else if ReservedFrontHoldGuard l.carrier then
    reservedFrontHoldWriteV6 l r
  else if VictimRightScrubGuardV6 r then
    victimRightScrubWriteV6 l r
  else if VictimLeftScrubGuardV6 l then
    victimLeftScrubWriteV6 l r
  else if FrontRightScrubGuardV6 r then
    frontRightScrubWriteV6 l r
  else if MalformedLeftPendingGuardV6 l then
    malformedLeftPendingWriteV6 l r
  else if MalformedRightPendingGuardV6 r then
    malformedRightPendingWriteV6 l r
  else if role l.carrier = .predecessorArmed then
    predecessorLeftScrubWriteV6 l r
  else if role l.carrier = .front then
    leftFrontHoldWriteV6 l r
  else if MarkedHoldGuardV6 l r then
    markedHoldWriteV6 l r
  else
    ordinaryHostWriteV6 hpsi hwidth hle l r

/-- Ring lift, with the inherited singleton fail-closed convention. -/
def stepV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) : R1ConfigV6 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV6 hpsi hwidth hle (C e) (C j)
    fun i =>
      if i = e then q.1
      else if i = j then q.2
      else C i

/-- One additional Boolean doubles V4's factor eight. -/
def controllerStateFactorV6 : Nat := 2 * controllerStateFactorV4

theorem controllerStateFactorV6_eq : controllerStateFactorV6 = 16 := by
  simp [controllerStateFactorV6, controllerStateFactorV4_eq]

/-! ## 5. Per-rule provenance preservation census -/

/-- ARM-A's role-changing write is provenance-clean by construction. -/
theorem armA_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau) :
    EdgeProvenanceV6 (armAWriteV6 l r).1 (armAWriteV6 l r).2 := by
  simp [armAWriteV6, EdgeProvenanceV6, TicketShapeV6,
    setControlV6, withCarrierClearTicketV6, setControl, role,
    ReservedFrontHoldGuard]

/-- ARM-B leaves a non-pending predecessor and is provenance-clean. -/
theorem armB_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau) :
    EdgeProvenanceV6 (armBWriteV6 l r).1 (armBWriteV6 l r).2 := by
  simp [armBWriteV6, EdgeProvenanceV6, TicketShapeV6,
    setControlV6, withCarrierClearTicketV6, setControl, role,
    ReservedFrontHoldGuard]

/-- DELETE creates a pending predecessor backed by an unticketed `front,true`. -/
theorem delete_preserves_edgeProvenanceV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    EdgeProvenanceV6
      (deleteWriteV6 hpsi hwidth hle l r).1
      (deleteWriteV6 hpsi hwidth hle l r).2 := by
  simp [deleteWriteV6, EdgeProvenanceV6, TicketShapeV6,
    withCarrierClearTicketV6, setControl, setPhysical, role,
    ReservedFrontHoldGuard]

/-- Genuine HOLD rows preserve the edge invariant verbatim. -/
theorem pendingHold_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (pendingHoldWriteV6 l r).1 (pendingHoldWriteV6 l r).2 := by
  simpa [pendingHoldWriteV6] using h

theorem pendingAbort_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau) :
    EdgeProvenanceV6
      (pendingAbortWriteV6 l r).1 (pendingAbortWriteV6 l r).2 := by
  simp [pendingAbortWriteV6, EdgeProvenanceV6, TicketShapeV6,
    clearControlV6, setControlV6, withCarrierClearTicketV6,
    setControl, role, ReservedFrontHoldGuard]

theorem moveCommit_preserves_edgeProvenanceV6
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    EdgeProvenanceV6
      (moveCommitWriteV6 hpsi l r).1 (moveCommitWriteV6 hpsi l r).2 := by
  simp [moveCommitWriteV6, EdgeProvenanceV6, TicketShapeV6,
    clearControlV6, setControlV6, withCarrierClearTicketV6,
    setControl, role, ReservedFrontHoldGuard]

theorem moveStop_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau) :
    EdgeProvenanceV6
      (moveStopWriteV6 l r).1 (moveStopWriteV6 l r).2 := by
  unfold moveStopWriteV6
  split <;>
    simp [EdgeProvenanceV6, TicketShapeV6,
      clearControlV6, setControlV6, withCarrierClearTicketV6,
      clearTicketV6, setTicketV6, setControl, role,
      ReservedFrontHoldGuard]

/-- SEEK keeps the old front carrier and only sets its ticket. -/
theorem moveSeek_preserves_edgeProvenanceV6
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r)
    (hg : MoveSeekGuardV3 hpsi l.carrier r.carrier) :
    EdgeProvenanceV6
      (moveSeekWriteV6 l r).1 (moveSeekWriteV6 l r).2 := by
  change EdgeProvenanceV6 l (setTicketV6 r true)
  rcases hinv with ⟨hlt, _hrt, _hb⟩
  rcases hg with ⟨_hlr, hlp, hr, _⟩
  refine ⟨hlt, ?_, ?_⟩
  · intro _
    simpa using hr
  · intro _ hp
    have hbad : (false : Bool) = true := hlp.symm.trans hp
    cases hbad

theorem moveSeekHold_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (moveSeekHoldWriteV6 l r).1 (moveSeekHoldWriteV6 l r).2 := by
  simpa [moveSeekHoldWriteV6] using h

/-- Clearing a ticket on the right cannot invalidate any existing backing. -/
theorem pendingOwnerAbort_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (pendingOwnerAbortWriteV6 l r).1
      (pendingOwnerAbortWriteV6 l r).2 := by
  change EdgeProvenanceV6 l (clearTicketV6 r)
  rcases h with ⟨hlt, _hrt, hb⟩
  refine ⟨hlt, ?_, ?_⟩
  · simp [TicketShapeV6, clearTicketV6, setTicketV6]
  · intro hl hp
    rcases hb hl hp with ⟨hr, _⟩
    exact ⟨hr, by simp [clearTicketV6, setTicketV6]⟩

theorem pendingOwnerHold_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (pendingOwnerHoldWriteV6 l r).1
      (pendingOwnerHoldWriteV6 l r).2 := by
  simpa [pendingOwnerHoldWriteV6] using h

/-- The new ACQUIRE creates exactly the pending/backing shape demanded by V6. -/
theorem moveAcquireFront_preserves_edgeProvenanceV6
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau)
    (hg : MoveAcquireFrontGuardV6 hpsi l r) :
    EdgeProvenanceV6
      (moveAcquireFrontWriteV6 l r).1
      (moveAcquireFrontWriteV6 l r).2 := by
  change EdgeProvenanceV6 (setControlV6 l .predecessorArmed true) r
  rcases hg with ⟨_hlres, _hllead, _hlt, hrres, _hrlead, hrt, _⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [TicketShapeV6, setControlV6, withCarrierClearTicketV6]
  · intro _
    exact hrres
  · intro _ _
    exact ⟨hrres, hrt⟩

/-- The legacy authenticated-victim ACQUIRE has the same safe post-shape. -/
theorem moveAcquireLegacy_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : MoveAcquireLegacyGuardV6 l r) :
    EdgeProvenanceV6
      (moveAcquireLegacyWriteV6 l r).1
      (moveAcquireLegacyWriteV6 l r).2 := by
  change EdgeProvenanceV6 (setControlV6 l .predecessorArmed true) r
  rcases hg with ⟨hbase, hrt⟩
  rcases hbase with ⟨_hlr, _hlp, _hllead, hrres⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [TicketShapeV6, setControlV6, withCarrierClearTicketV6]
  · intro _
    exact hrres
  · intro _ _
    exact ⟨hrres, hrt⟩

/-- On an invariant state a `victimArmed,true` site cannot carry a ticket, so
the new abort is a stutter; even locally, clearing that impossible bit is safe. -/
theorem moveAcquireAbort_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r)
    (hg : MoveAcquireAbortGuardV3 l.carrier r.carrier) :
    EdgeProvenanceV6
      (moveAcquireAbortWriteV6 l r).1
      (moveAcquireAbortWriteV6 l r).2 := by
  change EdgeProvenanceV6 (clearTicketV6 l) r
  rcases hinv with ⟨_hlt, hrt, _hb⟩
  rcases hg with ⟨hlr, _hlp, _hllead, _⟩
  refine ⟨?_, hrt, ?_⟩
  · simp [TicketShapeV6, clearTicketV6, setTicketV6]
  · intro hp _
    have hp0 : role l.carrier = .predecessorArmed := by simpa using hp
    have hbad : SpliceRole.victimArmed = SpliceRole.predecessorArmed :=
      hlr.symm.trans hp0
    cases hbad

theorem orphanReservedFront_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (orphanReservedFrontWriteV6 l r).1
      (orphanReservedFrontWriteV6 l r).2 := by
  simpa [orphanReservedFrontWriteV6] using h

theorem reservedFrontHold_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (reservedFrontHoldWriteV6 l r).1
      (reservedFrontHoldWriteV6 l r).2 := by
  simpa [reservedFrontHoldWriteV6] using h

/-- A right victim,false cannot be the reserved backing of a pending left
predecessor, so the narrowed scrub is edge-safe. -/
theorem victimRightScrub_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r)
    (hg : VictimRightScrubGuardV6 r) :
    EdgeProvenanceV6
      (victimRightScrubWriteV6 l r).1
      (victimRightScrubWriteV6 l r).2 := by
  change EdgeProvenanceV6 l (clearControlV6 r)
  rcases hinv with ⟨hlt, _hrt, hb⟩
  refine ⟨hlt, ?_, ?_⟩
  · simp [TicketShapeV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6]
  · intro hl hp
    rcases hb hl hp with ⟨hr, _⟩
    unfold ReservedFrontHoldGuard at hr
    have hbad : SpliceRole.victimArmed = SpliceRole.front :=
      hg.1.symm.trans hr.1
    cases hbad

theorem victimLeftScrub_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (victimLeftScrubWriteV6 l r).1
      (victimLeftScrubWriteV6 l r).2 := by
  change EdgeProvenanceV6 (clearControlV6 l) r
  rcases hinv with ⟨_hlt, hrt, _hb⟩
  refine ⟨?_, hrt, ?_⟩
  · simp [TicketShapeV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6]
  · simp [clearControlV6, setControlV6, withCarrierClearTicketV6,
      setControl, role]

/-- A `front,false` is not a V6 backing certificate. -/
theorem frontRightScrub_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r)
    (hg : FrontRightScrubGuardV6 r) :
    EdgeProvenanceV6
      (frontRightScrubWriteV6 l r).1
      (frontRightScrubWriteV6 l r).2 := by
  change EdgeProvenanceV6 l (clearControlV6 r)
  rcases hinv with ⟨hlt, _hrt, hb⟩
  refine ⟨hlt, ?_, ?_⟩
  · simp [TicketShapeV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6]
  · intro hl hp
    rcases hb hl hp with ⟨hr, _⟩
    unfold ReservedFrontHoldGuard at hr
    have hbad : (false : Bool) = true := hg.2.symm.trans hr.2
    cases hbad

theorem malformedLeftPending_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (malformedLeftPendingWriteV6 l r).1
      (malformedLeftPendingWriteV6 l r).2 := by
  change EdgeProvenanceV6 (clearPendingV6 l) r
  rcases hinv with ⟨_hlt, hrt, _hb⟩
  refine ⟨?_, hrt, ?_⟩
  · simp [TicketShapeV6, clearPendingV6, withCarrierClearTicketV6]
  · intro _ hp
    simp [clearPendingV6, withCarrierClearTicketV6] at hp

theorem malformedRightPending_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r)
    (hg : MalformedRightPendingGuardV6 r) :
    EdgeProvenanceV6
      (malformedRightPendingWriteV6 l r).1
      (malformedRightPendingWriteV6 l r).2 := by
  change EdgeProvenanceV6 l (clearPendingV6 r)
  rcases hinv with ⟨hlt, _hrt, hb⟩
  refine ⟨hlt, ?_, ?_⟩
  · simp [TicketShapeV6, clearPendingV6, withCarrierClearTicketV6]
  · intro hl hp
    rcases hb hl hp with ⟨hr, _⟩
    unfold ReservedFrontHoldGuard at hr
    exact False.elim (hg.2.2.1 hr.1)

theorem predecessorLeftScrub_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (predecessorLeftScrubWriteV6 l r).1
      (predecessorLeftScrubWriteV6 l r).2 := by
  change EdgeProvenanceV6 (clearControlV6 l) r
  rcases hinv with ⟨_hlt, hrt, _hb⟩
  refine ⟨?_, hrt, ?_⟩
  · simp [TicketShapeV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6]
  · simp [clearControlV6, setControlV6, withCarrierClearTicketV6,
      setControl, role]

theorem leftFrontHold_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (leftFrontHoldWriteV6 l r).1
      (leftFrontHoldWriteV6 l r).2 := by
  simpa [leftFrontHoldWriteV6] using h

theorem markedHold_preserves_edgeProvenanceV6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (markedHoldWriteV6 l r).1
      (markedHoldWriteV6 l r).2 := by
  simpa [markedHoldWriteV6] using h

/-- The ordinary row is provenance-safe because it changes only physical state
in the old carrier and V6 clears both new bits.  Its remaining status is
`physicalFrameOnly`, exactly as in the v5 census. -/
theorem ordinaryHost_preserves_edgeProvenanceV6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r) :
    EdgeProvenanceV6
      (ordinaryHostWriteV6 hpsi hwidth hle l r).1
      (ordinaryHostWriteV6 hpsi hwidth hle l r).2 := by
  rcases hinv with ⟨_hlt, _hrt, hb⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [ordinaryHostWriteV6, TicketShapeV6,
      withCarrierClearTicketV6]
  · simp [ordinaryHostWriteV6, TicketShapeV6,
      withCarrierClearTicketV6]
  · intro hl hp
    have hl0 : role l.carrier = .predecessorArmed := by
      simpa [ordinaryHostWriteV6, ordinaryRow,
        withCarrierClearTicketV6, setPhysical, role] using hl
    have hp0 : l.carrier.repairPending = true := by
      simpa [ordinaryHostWriteV6, ordinaryRow,
        withCarrierClearTicketV6, setPhysical] using hp
    rcases hb hl0 hp0 with ⟨hr, _⟩
    constructor
    · simpa [ordinaryHostWriteV6, ordinaryRow,
        withCarrierClearTicketV6, setPhysical,
        ReservedFrontHoldGuard, role] using hr
    · simp [ordinaryHostWriteV6, withCarrierClearTicketV6]

inductive V6Rule where
  | armA | armB | deleteStage | pendingHold | pendingAbort
  | moveCommit | moveStop | moveSeek | moveSeekHold
  | pendingOwnerAbort | pendingOwnerHold
  | moveAcquireFront | moveAcquireLegacy | moveAcquireAbort
  | orphanReservedFront | reservedFrontHold
  | victimRightScrub | victimLeftScrub | frontRightScrub
  | malformedLeftPending | malformedRightPending
  | predecessorLeftScrub | leftFrontHold | markedHold | ordinaryHost
  deriving DecidableEq, Repr

inductive SafetyStatusV6 where
  | preserves
  | physicalFrameOnly
  deriving DecidableEq, Repr

/-- All 24 controller rows preserve the strengthened controller invariant.
Only the inherited physical-host obligation remains outside this file. -/
def safetyStatusV6 : V6Rule -> SafetyStatusV6
  | .ordinaryHost => .physicalFrameOnly
  | _ => .preserves

theorem safety_census_statuses_v6 :
    safetyStatusV6 .armA = .preserves /\
    safetyStatusV6 .armB = .preserves /\
    safetyStatusV6 .deleteStage = .preserves /\
    safetyStatusV6 .pendingHold = .preserves /\
    safetyStatusV6 .pendingAbort = .preserves /\
    safetyStatusV6 .moveCommit = .preserves /\
    safetyStatusV6 .moveStop = .preserves /\
    safetyStatusV6 .moveSeek = .preserves /\
    safetyStatusV6 .moveSeekHold = .preserves /\
    safetyStatusV6 .pendingOwnerAbort = .preserves /\
    safetyStatusV6 .pendingOwnerHold = .preserves /\
    safetyStatusV6 .moveAcquireFront = .preserves /\
    safetyStatusV6 .moveAcquireLegacy = .preserves /\
    safetyStatusV6 .moveAcquireAbort = .preserves /\
    safetyStatusV6 .orphanReservedFront = .preserves /\
    safetyStatusV6 .reservedFrontHold = .preserves /\
    safetyStatusV6 .victimRightScrub = .preserves /\
    safetyStatusV6 .victimLeftScrub = .preserves /\
    safetyStatusV6 .frontRightScrub = .preserves /\
    safetyStatusV6 .malformedLeftPending = .preserves /\
    safetyStatusV6 .malformedRightPending = .preserves /\
    safetyStatusV6 .predecessorLeftScrub = .preserves /\
    safetyStatusV6 .leftFrontHold = .preserves /\
    safetyStatusV6 .markedHold = .preserves /\
    safetyStatusV6 .ordinaryHost = .physicalFrameOnly := by
  decide

/-! ## 6. Closed finite deciders and replay helpers -/

private instance instDecidablePreparedDangerBase
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableProtectedBase
    (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (R1ProtectedSpliceEdgeV3 ring C e) := by
  unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard
  dsimp only
  infer_instance

private instance instDecidableSpliceSafeBase
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) :
    Decidable (SpliceSafeR1V3 hpsi ring C) := by
  unfold SpliceSafeR1V3
  infer_instance

private instance instDecidableTicketShapeV6
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (TicketShapeV6 u) := by
  unfold TicketShapeV6 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableProvenanceSafeV6
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV6 ring C) := by
  unfold ProvenanceSafeV6
  infer_instance

private instance instDecidableSpliceSafeV6
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (SpliceSafeR1V6 hpsi ring C) := by
  unfold SpliceSafeR1V6
  infer_instance

private instance instDecidablePPrimeBarrierBirthGuardV6
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    Decidable (PPrimeBarrierBirthGuard hpsi l r) := by
  unfold PPrimeBarrierBirthGuard isBarrier
  infer_instance

private instance instDecidableAmendedPPrimeBase
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (R1AmendedPPrimeAtV3 hpsi ring C e) := by
  unfold R1AmendedPPrimeAtV3
  dsimp only
  infer_instance

private instance instDecidableSourceFreeBase
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) :
    Decidable (R1SourceFreeV3 hpsi ring C) := by
  unfold R1SourceFreeV3
  infer_instance

/-- Physical leaderlessness for the wrapper. -/
def LeaderlessV6
    (C : R1ConfigV6 n psi kappa tau) : Prop :=
  forall i, (C i).carrier.splice.base.core.core.leader = false

/-- The drain target includes clearing the new provenance bit. -/
def RolesClearV6
    (C : R1ConfigV6 n psi kappa tau) : Prop :=
  forall i,
    role (C i).carrier = .none /\
    (C i).carrier.repairPending = false /\
    (C i).acquireTicket = false

private instance instDecidableLeaderlessV6
    (C : R1ConfigV6 n psi kappa tau) : Decidable (LeaderlessV6 C) := by
  unfold LeaderlessV6
  infer_instance

private instance instDecidableRolesClearV6
    (C : R1ConfigV6 n psi kappa tau) : Decidable (RolesClearV6 C) := by
  unfold RolesClearV6
  infer_instance

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hFour : 0 < 4 := by decide
private theorem hFive : 0 < 5 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private theorem hOneThree : 1 <= 3 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hTwoThree : 2 <= 3 := by decide

private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def ring4 : DirectedRing 4 := ⟨hFour⟩
private def ring5 : DirectedRing 5 := ⟨hFive⟩

def serveV6 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV6 n 2 0 0) (e : Fin n) : R1ConfigV6 n 2 0 0 :=
  stepV6 hTwo hTwo hTwoLe ring C e

def runV6 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV6 n 2 0 0)
    (word : List (Fin n)) : R1ConfigV6 n 2 0 0 :=
  List.foldl (fun D e => serveV6 ring D e) C word

def safeAlongV6 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV6 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (SpliceSafeR1V6 hTwo ring C)
  | C, e :: es =>
      decide (SpliceSafeR1V6 hTwo ring C) &&
        safeAlongV6 ring (serveV6 ring C e) es

def sourceFreeAlongV6 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV6 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (R1SourceFreeV3 hTwo ring (projectV6 C))
  | C, e :: es =>
      decide (R1SourceFreeV3 hTwo ring (projectV6 C)) &&
        sourceFreeAlongV6 ring (serveV6 ring C e) es

/-! ## 7. Restated v5 witnesses and historical regressions -/

private def raw3
    (leader : Bool) (label : Fin 3) : AgentState 3 :=
  { leader := leader
    probe := false
    phase := false
    bit := false
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := label
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := true
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }

private theorem raw3_domain0 (leader : Bool) (label : Fin 3) :
    (raw3 leader label).inProtocolDomain 0 := by
  simp [raw3, AgentState.inProtocolDomain]

private theorem raw3_domain3 (leader : Bool) (label : Fin 3) :
    (raw3 leader label).inProtocolDomain 3 := by
  simp [raw3, AgentState.inProtocolDomain]

private def cell3_0
    (leader : Bool) (label : Fin 3) : ExpiringAgentState 3 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (raw3 leader label) (raw3_domain0 leader label), false⟩, 0⟩

private def x3_0Base
    (leader : Bool) (label : Fin 3)
    (r : SpliceRole) (pending : Bool) : R1AgentStateV4 3 0 0 :=
  { splice := { base := cell3_0 leader label, spliceRole := r }
    repairPending := pending }

private def cell3_3_48
    (leader : Bool) (label : Fin 3) : ExpiringAgentState 3 3 48 :=
  ⟨⟨BoundedAgentState.ofDomain
      (raw3 leader label) (raw3_domain3 leader label), false⟩, 0⟩

private def x3_3_48Base
    (leader : Bool) (label : Fin 3)
    (r : SpliceRole) (pending : Bool) : R1AgentStateV4 3 3 48 :=
  { splice := { base := cell3_3_48 leader label, spliceRole := r }
    repairPending := pending }

/-- v5 counterexample 1, restated locally: its site-1 front is now unticketed
because it backs site 0, so front/front ACQUIRE is not enabled. -/
def frontAcquireBackedStart3V6 : R1ConfigV6 3 2 0 0 := fun i =>
  if i = 0 then
    liftAgentV6 (B9SpliceR2AttackRerun.xcell
      true 0 false .predecessorArmed true)
  else if i = 1 then
    liftAgentV6 (B9SpliceR2AttackRerun.xcell false 0 false .front true)
  else
    liftAgentV6 (B9SpliceR2AttackRerun.xcell false 1 false .front true)

def frontAcquireBackedAfter3V6 : R1ConfigV6 3 2 0 0 :=
  serveV6 ring3 frontAcquireBackedStart3V6 (1 : Fin 3)

theorem frontAcquire_v5_witness_repaired_v6 :
    SpliceSafeR1V6 hTwo ring3 frontAcquireBackedStart3V6 /\
    ¬ MoveAcquireFrontGuardV6 hTwo
      (frontAcquireBackedStart3V6 (1 : Fin 3))
      (frontAcquireBackedStart3V6 (2 : Fin 3)) /\
    (forall i, frontAcquireBackedAfter3V6 i = frontAcquireBackedStart3V6 i) /\
    SpliceSafeR1V6 hTwo ring3 frontAcquireBackedAfter3V6 := by
  decide

/-- v5 counterexample 2, restated locally. -/
def pendingOwnerAbortStart3V6 : R1ConfigV6 3 2 0 0 := fun i =>
  if i = 0 then
    liftAgentV6 (B9SpliceR2AttackRerun.xcell false 0 false .none false)
  else if i = 1 then
    liftAgentV6 (B9SpliceR2AttackRerun.xcell
      false 0 false .predecessorArmed true)
  else
    liftAgentV6 (B9SpliceR2AttackRerun.xcell false 1 false .front true)

def pendingOwnerAbortAfter3V6 : R1ConfigV6 3 2 0 0 :=
  serveV6 ring3 pendingOwnerAbortStart3V6 (0 : Fin 3)

theorem pendingOwnerAbort_v5_witness_repaired_v6 :
    SpliceSafeR1V6 hTwo ring3 pendingOwnerAbortStart3V6 /\
    PendingOwnerAbortGuardV3
      (pendingOwnerAbortStart3V6 (0 : Fin 3)).carrier
      (pendingOwnerAbortStart3V6 (1 : Fin 3)).carrier /\
    (forall i, pendingOwnerAbortAfter3V6 i = pendingOwnerAbortStart3V6 i) /\
    SpliceSafeR1V6 hTwo ring3 pendingOwnerAbortAfter3V6 := by
  decide

/-- v5 counterexample 3, restated locally. -/
def moveAcquireAbortStart2V6 : R1ConfigV6 2 3 0 0 := fun i =>
  if i = 0 then liftAgentV6 (x3_0Base false 0 .predecessorArmed false)
  else liftAgentV6 (x3_0Base false 2 .victimArmed true)

def moveAcquireAbortAfter2V6 : R1ConfigV6 2 3 0 0 :=
  stepV6 hThree hOne hOneThree ring2
    moveAcquireAbortStart2V6 (1 : Fin 2)

theorem moveAcquireAbort_v5_witness_repaired_v6 :
    SpliceSafeR1V6 hThree ring2 moveAcquireAbortStart2V6 /\
    MoveAcquireAbortGuardV3
      (moveAcquireAbortStart2V6 (1 : Fin 2)).carrier
      (moveAcquireAbortStart2V6 (0 : Fin 2)).carrier /\
    (forall i, moveAcquireAbortAfter2V6 i = moveAcquireAbortStart2V6 i) /\
    SpliceSafeR1V6 hThree ring2 moveAcquireAbortAfter2V6 := by
  decide

/-- v5 counterexample 4, restated locally. -/
def orphanReservedFrontStart2V6 : R1ConfigV6 2 3 0 0 := fun i =>
  if i = 0 then liftAgentV6 (x3_0Base false 0 .none false)
  else liftAgentV6 (x3_0Base false 1 .front true)

def orphanReservedFrontAfter2V6 : R1ConfigV6 2 3 0 0 :=
  stepV6 hThree hOne hOneThree ring2
    orphanReservedFrontStart2V6 (0 : Fin 2)

theorem orphanReservedFront_v5_witness_repaired_v6 :
    SpliceSafeR1V6 hThree ring2 orphanReservedFrontStart2V6 /\
    OrphanReservedFrontGuardV3
      (orphanReservedFrontStart2V6 (0 : Fin 2)).carrier
      (orphanReservedFrontStart2V6 (1 : Fin 2)).carrier /\
    (forall i, orphanReservedFrontAfter2V6 i = orphanReservedFrontStart2V6 i) /\
    SpliceSafeR1V6 hThree ring2 orphanReservedFrontAfter2V6 := by
  decide

/-! ### MOVE-STOP, protocol-STOP and SEEK witnesses -/

def q11668Start2V6 : R1ConfigV6 2 3 0 0 := fun i =>
  if i = 0 then liftAgentV6 (x3_0Base false 0 .predecessorArmed false)
  else liftAgentV6 (x3_0Base false 1 .front true)

def q11668After2V6 : R1ConfigV6 2 3 0 0 :=
  stepV6 hThree hOne hOneThree ring2 q11668Start2V6 (0 : Fin 2)

theorem q11668_moveStop_rechecked_v6 :
    SpliceSafeR1V6 hThree ring2 q11668Start2V6 /\
    MoveStopGuardV3 hThree
      (q11668Start2V6 (0 : Fin 2)).carrier
      (q11668Start2V6 (1 : Fin 2)).carrier /\
    role (q11668After2V6 (0 : Fin 2)).carrier = .none /\
    ReservedFrontHoldGuard (q11668After2V6 (1 : Fin 2)).carrier /\
    (q11668After2V6 (1 : Fin 2)).acquireTicket = false /\
    SpliceSafeR1V6 hThree ring2 q11668After2V6 := by
  decide

/-- Literal n=4 protocol parameters: psi=3, width=2, kappa=3, tau=48. -/
def protocolStopStart4V6 : R1ConfigV6 4 3 3 48 := fun i =>
  if i = 0 then liftAgentV6 (x3_3_48Base false 0 .predecessorArmed false)
  else if i = 1 then liftAgentV6 (x3_3_48Base false 1 .front true)
  else if i = 2 then liftAgentV6 (x3_3_48Base false 1 .none false)
  else liftAgentV6 (x3_3_48Base true 0 .none false)

def protocolStopAfter4V6 : R1ConfigV6 4 3 3 48 :=
  stepV6 hThree hTwo hTwoThree ring4
    protocolStopStart4V6 (0 : Fin 4)

theorem q11674_protocol_stop_rechecked_v6 :
    Q11497FeasibilityAudit.psiChoice 4 = 3 /\
    Q11497FeasibilityAudit.widthChoice = 2 /\
    Q11497FeasibilityAudit.kappaChoice 4 = 3 /\
    Q11497FeasibilityAudit.tauChoice 4 = 48 /\
    SpliceSafeR1V6 hThree ring4 protocolStopStart4V6 /\
    SpliceSafeR1V6 hThree ring4 protocolStopAfter4V6 /\
    ReservedFrontHoldGuard (protocolStopAfter4V6 (1 : Fin 4)).carrier /\
    PreparedDangerAt hThree ring4 (projectV6 protocolStopAfter4V6) (1 : Fin 4) /\
    R1ProtectedSpliceEdgeV3 ring4
      (projectV6 protocolStopAfter4V6) (1 : Fin 4) := by
  decide

/-- The two-site SEEK witness now preserves the front and sets its ticket. -/
def q11681Start2V6 : R1ConfigV6 2 2 0 0 :=
  liftConfigV6 B9SpliceControllerV4Safety.seekStart2

def q11681After2V6 : R1ConfigV6 2 2 0 0 :=
  stepV6 hTwo hOne hOneTwo ring2 q11681Start2V6 (0 : Fin 2)

theorem q11681_moveSeek_rechecked_v6 :
    SpliceSafeR1V6 hTwo ring2 q11681Start2V6 /\
    MoveSeekGuardV3 hTwo
      (q11681Start2V6 (0 : Fin 2)).carrier
      (q11681Start2V6 (1 : Fin 2)).carrier /\
    (forall i,
      (q11681After2V6 i).carrier = (q11681Start2V6 i).carrier) /\
    (q11681After2V6 (0 : Fin 2)).acquireTicket = false /\
    (q11681After2V6 (1 : Fin 2)).acquireTicket = true /\
    SpliceSafeR1V6 hTwo ring2 q11681After2V6 := by
  decide

/-! ### Three leaderless drains -/

private def drain3 : List (Fin 3) := [0, 1, 0]
private def drain4 : List (Fin 4) := [0, 2, 0, 2]
private def drain5 : List (Fin 5) := [0, 1, 0]

private def loop3StartV6 : R1ConfigV6 3 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.loop3Start

private def loop4StartV6 : R1ConfigV6 4 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.loop4Start

private def loop5StartV6 : R1ConfigV6 5 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.loop5Start

theorem three_leaderless_drains_rechecked_v6 :
    LeaderlessV6 loop3StartV6 /\
    RolesClearV6 (runV6 ring3 loop3StartV6 drain3) /\
    LeaderlessV6 loop4StartV6 /\
    RolesClearV6 (runV6 ring4 loop4StartV6 drain4) /\
    LeaderlessV6 loop5StartV6 /\
    RolesClearV6 (runV6 ring5 loop5StartV6 drain5) := by
  decide

/-! ### The four attacks -/

private def q11592Start4V6 : R1ConfigV6 4 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.q11592Start4

private def q11592Armed4V6 : R1ConfigV6 4 2 0 0 :=
  serveV6 ring4 q11592Start4V6 (1 : Fin 4)

private def q11592Replay4V6 : R1ConfigV6 4 2 0 0 :=
  serveV6 ring4 q11592Armed4V6 (1 : Fin 4)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem q11592_attack_rechecked_v6 :
    PendingHoldGuard hTwo hTwo hTwoLe
      (q11592Armed4V6 (1 : Fin 4)).carrier
      (q11592Armed4V6 (2 : Fin 4)).carrier /\
    SpliceSafeR1V6 hTwo ring4 q11592Armed4V6 /\
    (forall i, q11592Replay4V6 i = q11592Armed4V6 i) := by
  decide

private def followerOldStart5V6 : R1ConfigV6 5 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.followerStart5

private def followerOldFirstV6 : R1ConfigV6 5 2 0 0 :=
  serveV6 ring5 followerOldStart5V6 (0 : Fin 5)

theorem old_follower_attack_rechecked_v6 :
    role (followerOldFirstV6 (0 : Fin 5)).carrier = .predecessorArmed /\
    role (followerOldFirstV6 (1 : Fin 5)).carrier = .none /\
    (followerOldFirstV6 (1 : Fin 5)).acquireTicket = false := by
  decide

private def stagedStart3V6 : R1ConfigV6 3 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.stagedStart3

private def stagedArmed3V6 : R1ConfigV6 3 2 0 0 :=
  serveV6 ring3 stagedStart3V6 (1 : Fin 3)

private def starvationFinal3V6 : R1ConfigV6 3 2 0 0 :=
  runV6 ring3 stagedStart3V6 B9SpliceR2AttackRerun.starvationWord3

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem staged_deletion_attack_rechecked_v6 :
    (forall i,
      serveV6 ring3 stagedArmed3V6 (2 : Fin 3) i = stagedArmed3V6 i) /\
    (forall i,
      serveV6 ring3 stagedArmed3V6 (1 : Fin 3) i = stagedArmed3V6 i) /\
    safeAlongV6 ring3 stagedStart3V6
      B9SpliceR2AttackRerun.starvationWord3 = true /\
    RolesClearV6 starvationFinal3V6 /\
    (starvationFinal3V6 (1 : Fin 3)).carrier.splice.base.core.core.leader = false /\
    (starvationFinal3V6 (2 : Fin 3)).carrier.splice.base.core.core.leader = true := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- One compact theorem covering attack 1 (all three leaderless fixtures) and
attacks 2--4. -/
theorem four_attacks_rechecked_v6 :
    RolesClearV6 (runV6 ring3 loop3StartV6 drain3) /\
    RolesClearV6 (runV6 ring4 loop4StartV6 drain4) /\
    RolesClearV6 (runV6 ring5 loop5StartV6 drain5) /\
    (forall i, q11592Replay4V6 i = q11592Armed4V6 i) /\
    role (followerOldFirstV6 (1 : Fin 5)).carrier = .none /\
    RolesClearV6 starvationFinal3V6 := by
  decide

/-! ### Authenticated follower chain -/

private def followerStart5V6 : R1ConfigV6 5 2 0 0 :=
  liftConfigV6 B9SpliceControllerR1TableV3.followerStart5V3

private def followerAfterSeekV6 : R1ConfigV6 5 2 0 0 :=
  serveV6 ring5 followerStart5V6 (0 : Fin 5)

private def followerAfterAcquireV6 : R1ConfigV6 5 2 0 0 :=
  serveV6 ring5 followerAfterSeekV6 (1 : Fin 5)

def followerAfter5V6 : R1ConfigV6 5 2 0 0 :=
  runV6 ring5 followerStart5V6
    B9SpliceControllerR1TableV3.followerWord5V3

theorem authenticated_follower_chain_progresses_v6 :
    (forall i,
      (followerAfterSeekV6 i).carrier = (followerStart5V6 i).carrier) /\
    (followerAfterSeekV6 (1 : Fin 5)).acquireTicket = true /\
    MoveAcquireFrontGuardV6 hTwo
      (followerAfterSeekV6 (1 : Fin 5))
      (followerAfterSeekV6 (2 : Fin 5)) /\
    role (followerAfterAcquireV6 (1 : Fin 5)).carrier = .predecessorArmed /\
    (followerAfterAcquireV6 (1 : Fin 5)).carrier.repairPending = true /\
    (followerAfterAcquireV6 (1 : Fin 5)).acquireTicket = false /\
    safeAlongV6 ring5 followerStart5V6
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    sourceFreeAlongV6 ring5 followerStart5V6
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    role (followerAfter5V6 (2 : Fin 5)).carrier = .predecessorArmed /\
    (followerAfter5V6 (2 : Fin 5)).carrier.repairPending = false /\
    ReservedFrontHoldGuard (followerAfter5V6 (3 : Fin 5)).carrier /\
    (followerAfter5V6 (3 : Fin 5)).acquireTicket = false /\
    (followerAfter5V6 (2 : Fin 5)).carrier.splice.base.core.core.probe = false := by
  decide

/-! ## 8. V6 drain potential -/

/-- V6 weights.  On certified states the important chain is

`front,true,false` (8) -> `front,true,true` (6)
  -> `predecessorArmed,true,false` (4)
  -> `predecessorArmed,false,false` (3).

Invalid ticketed non-front states are one unit heavier than their cleaned form,
so the two ticket-only aborts also strictly decrease. -/
def controllerWeightV6
    (u : R1AgentStateV6 psi kappa tau) : Nat :=
  match role u.carrier, u.carrier.repairPending, u.acquireTicket with
  | .none, false, false => 0
  | .none, false, true => 1
  | .none, true, false => 1
  | .none, true, true => 2
  | .predecessorArmed, false, false => 3
  | .predecessorArmed, false, true => 4
  | .predecessorArmed, true, false => 4
  | .predecessorArmed, true, true => 5
  | .victimArmed, false, false => 2
  | .victimArmed, false, true => 3
  | .victimArmed, true, false => 5
  | .victimArmed, true, true => 6
  | .front, false, false => 2
  | .front, false, true => 3
  | .front, true, false => 8
  | .front, true, true => 6

def pairPotentialV6
    (l r : R1AgentStateV6 psi kappa tau) : Nat :=
  controllerWeightV6 l + controllerWeightV6 r

def controllerPotentialV6
    (C : R1ConfigV6 n psi kappa tau) : Nat :=
  (List.ofFn (fun i : Fin n => controllerWeightV6 (C i))).sum

/-- The local maximum is still constant. -/
theorem controllerWeightV6_le_eight
    (u : R1AgentStateV6 psi kappa tau) :
    controllerWeightV6 u <= 8 := by
  cases hrole : role u.carrier <;>
    cases hp : u.carrier.repairPending <;>
    cases ht : u.acquireTicket <;>
    simp [controllerWeightV6, hrole, hp, ht]

private theorem ofFn_sum_const_v6 : forall (m c : Nat),
    (List.ofFn (fun _ : Fin m => c)).sum = m * c := by
  intro m
  induction m with
  | zero =>
      intro c
      simp
  | succ m ih =>
      intro c
      rw [List.ofFn_succ, List.sum_cons, ih c]
      rw [Nat.succ_mul]
      exact Nat.add_comm c (m * c)

theorem controllerPotentialV6_le_eight_mul
    (C : R1ConfigV6 n psi kappa tau) :
    controllerPotentialV6 C <= 8 * n := by
  unfold controllerPotentialV6
  have hsum : forall xs : List Nat,
      (forall x, x ∈ xs -> x <= 8) ->
        xs.sum <= 8 * xs.length := by
    intro xs
    induction xs with
    | nil =>
        intro _
        simp
    | cons a xs ih =>
        intro hall
        have ha : a <= 8 := hall a (by simp)
        have htail : forall x, x ∈ xs -> x <= 8 := by
          intro x hx
          exact hall x (by simp [hx])
        calc
          (a :: xs).sum = a + xs.sum := rfl
          _ <= 8 + 8 * xs.length :=
            Nat.add_le_add ha (ih htail)
          _ = 8 * (a :: xs).length := by
            simp [Nat.mul_succ, Nat.add_comm]
  have h := hsum
    (List.ofFn (fun i : Fin n => controllerWeightV6 (C i))) (by
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact controllerWeightV6_le_eight (C i))
  simpa using h

/-- Minting a legitimate SEEK ticket strictly drops 8 -> 6. -/
theorem moveSeek_write_drop_two_v6
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hinv : EdgeProvenanceV6 l r)
    (hg : MoveSeekGuardV3 hpsi l.carrier r.carrier)
    (hrt : r.acquireTicket = false) :
    pairPotentialV6 (moveSeekWriteV6 l r).1 (moveSeekWriteV6 l r).2 + 2 =
      pairPotentialV6 l r := by
  rcases hg with ⟨hlr, hlp, hr, _⟩
  unfold ReservedFrontHoldGuard at hr
  rcases hr with ⟨hrr, hrp⟩
  have hnres : ¬ ReservedFrontHoldGuard l.carrier := by
    intro h
    unfold ReservedFrontHoldGuard at h
    have hbad : SpliceRole.predecessorArmed = SpliceRole.front :=
      hlr.symm.trans h.1
    cases hbad
  have hlt : l.acquireTicket = false :=
    ticket_false_of_shape_of_not_reserved l hinv.1 hnres
  simp [pairPotentialV6, controllerWeightV6, moveSeekWriteV6,
    setTicketV6, hlr, hlp, hrr, hrp, hlt, hrt]

theorem moveAcquireFront_write_drop_two_v6
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : MoveAcquireFrontGuardV6 hpsi l r) :
    pairPotentialV6
        (moveAcquireFrontWriteV6 l r).1
        (moveAcquireFrontWriteV6 l r).2 + 2 =
      pairPotentialV6 l r := by
  rcases hg with ⟨hl, _hllead, hlt, hr, _hrlead, hrt, _⟩
  unfold ReservedFrontHoldGuard at hl hr
  rcases hl with ⟨hlr, hlp⟩
  rcases hr with ⟨hrr, hrp⟩
  change l.carrier.splice.spliceRole = .front at hlr
  change r.carrier.splice.spliceRole = .front at hrr
  simp [pairPotentialV6, controllerWeightV6,
    moveAcquireFrontWriteV6, setControlV6,
    withCarrierClearTicketV6, setControl, role,
    hlr, hlp, hlt, hrr, hrp, hrt]

theorem moveAcquireLegacy_write_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : MoveAcquireLegacyGuardV6 l r) :
    pairPotentialV6
        (moveAcquireLegacyWriteV6 l r).1
        (moveAcquireLegacyWriteV6 l r).2 < pairPotentialV6 l r := by
  rcases hg with ⟨hbase, hrt⟩
  rcases hbase with ⟨hlr, hlp, _hllead, hr⟩
  unfold ReservedFrontHoldGuard at hr
  rcases hr with ⟨hrr, hrp⟩
  change l.carrier.splice.spliceRole = .victimArmed at hlr
  change r.carrier.splice.spliceRole = .front at hrr
  cases hlt : l.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      moveAcquireLegacyWriteV6, setControlV6,
      withCarrierClearTicketV6, setControl, role,
      hlr, hlp, hlt, hrr, hrp, hrt] <;> omega

theorem moveStopFollower_write_drop_v6
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : MoveStopGuardV3 hpsi l.carrier r.carrier)
    (hrlead : r.carrier.splice.base.core.core.leader = false) :
    pairPotentialV6 (moveStopWriteV6 l r).1 (moveStopWriteV6 l r).2 <
      pairPotentialV6 l r := by
  rcases hg with ⟨hlr, hlp, hr, _⟩
  unfold ReservedFrontHoldGuard at hr
  rcases hr with ⟨hrr, hrp⟩
  change l.carrier.splice.spliceRole = .predecessorArmed at hlr
  change r.carrier.splice.spliceRole = .front at hrr
  cases hlt : l.acquireTicket <;>
    cases hrt : r.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      moveStopWriteV6, hrlead, clearControlV6,
      setControlV6, withCarrierClearTicketV6,
      clearTicketV6, setTicketV6, setControl, role,
      hlr, hlp, hrr, hrp, hlt, hrt] <;> omega

theorem moveCommit_write_drop_v6
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : MoveCommitGuard l.carrier r.carrier) :
    pairPotentialV6
        (moveCommitWriteV6 hpsi l r).1
        (moveCommitWriteV6 hpsi l r).2 < pairPotentialV6 l r := by
  rcases hg with ⟨hlr, hlp, hrr, hrp, _⟩
  change l.carrier.splice.spliceRole = .predecessorArmed at hlr
  change r.carrier.splice.spliceRole = .predecessorArmed at hrr
  cases hlt : l.acquireTicket <;>
    cases hrt : r.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      moveCommitWriteV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6, setControl, role,
      hlr, hlp, hrr, hrp, hlt, hrt] <;> omega

/-- The two repaired aborts strictly remove forged provenance whenever they
actually change a state. -/
theorem pendingOwnerAbort_invalid_ticket_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : PendingOwnerAbortGuardV3 l.carrier r.carrier)
    (hrt : r.acquireTicket = true) :
    pairPotentialV6
        (pendingOwnerAbortWriteV6 l r).1
        (pendingOwnerAbortWriteV6 l r).2 + 1 = pairPotentialV6 l r := by
  rcases hg with ⟨hrr, hrp, _⟩
  simp [pairPotentialV6, controllerWeightV6,
    pendingOwnerAbortWriteV6, clearTicketV6, setTicketV6,
    hrr, hrp, hrt]

theorem moveAcquireAbort_invalid_ticket_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : MoveAcquireAbortGuardV3 l.carrier r.carrier)
    (hlt : l.acquireTicket = true) :
    pairPotentialV6
        (moveAcquireAbortWriteV6 l r).1
        (moveAcquireAbortWriteV6 l r).2 + 1 = pairPotentialV6 l r := by
  rcases hg with ⟨hlr, hlp, _hllead, _⟩
  change l.carrier.splice.spliceRole = .victimArmed at hlr
  simp [pairPotentialV6, controllerWeightV6,
    moveAcquireAbortWriteV6, clearTicketV6, setTicketV6,
    role, hlr, hlp, hlt] <;> omega

theorem victimRightScrub_write_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : VictimRightScrubGuardV6 r) :
    pairPotentialV6
        (victimRightScrubWriteV6 l r).1
        (victimRightScrubWriteV6 l r).2 < pairPotentialV6 l r := by
  rcases hg with ⟨hrr, hrp⟩
  change r.carrier.splice.spliceRole = .victimArmed at hrr
  cases hrt : r.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      victimRightScrubWriteV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6, setControl, role,
      hrr, hrp, hrt] <;> omega

theorem victimLeftScrub_write_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : VictimLeftScrubGuardV6 l) :
    pairPotentialV6
        (victimLeftScrubWriteV6 l r).1
        (victimLeftScrubWriteV6 l r).2 < pairPotentialV6 l r := by
  rcases hg with ⟨hlr, hlp⟩
  change l.carrier.splice.spliceRole = .victimArmed at hlr
  cases hlt : l.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      victimLeftScrubWriteV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6, setControl, role,
      hlr, hlp, hlt] <;> omega

theorem frontRightScrub_write_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : FrontRightScrubGuardV6 r) :
    pairPotentialV6
        (frontRightScrubWriteV6 l r).1
        (frontRightScrubWriteV6 l r).2 < pairPotentialV6 l r := by
  rcases hg with ⟨hrr, hrp⟩
  change r.carrier.splice.spliceRole = .front at hrr
  cases hrt : r.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      frontRightScrubWriteV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6, setControl, role,
      hrr, hrp, hrt] <;> omega

private theorem role_none_of_malformed_left
    (l : R1AgentStateV6 psi kappa tau)
    (hg : MalformedLeftPendingGuardV6 l) :
    role l.carrier = .none := by
  rcases hg with ⟨_hp, hpred, hfront, hvictim⟩
  cases h : role l.carrier with
  | none => rfl
  | predecessorArmed => exact False.elim (hpred h)
  | victimArmed => exact False.elim (hvictim h)
  | front => exact False.elim (hfront h)

private theorem role_none_of_malformed_right
    (r : R1AgentStateV6 psi kappa tau)
    (hg : MalformedRightPendingGuardV6 r) :
    role r.carrier = .none := by
  rcases hg with ⟨_hp, hpred, hfront, hvictim⟩
  cases h : role r.carrier with
  | none => rfl
  | predecessorArmed => exact False.elim (hpred h)
  | victimArmed => exact False.elim (hvictim h)
  | front => exact False.elim (hfront h)

theorem malformedLeftPending_write_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : MalformedLeftPendingGuardV6 l) :
    pairPotentialV6
        (malformedLeftPendingWriteV6 l r).1
        (malformedLeftPendingWriteV6 l r).2 < pairPotentialV6 l r := by
  have hrole := role_none_of_malformed_left l hg
  change l.carrier.splice.spliceRole = .none at hrole
  cases hlt : l.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      malformedLeftPendingWriteV6, clearPendingV6,
      withCarrierClearTicketV6, role,
      hrole, hg.1, hlt] <;> omega

theorem malformedRightPending_write_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : MalformedRightPendingGuardV6 r) :
    pairPotentialV6
        (malformedRightPendingWriteV6 l r).1
        (malformedRightPendingWriteV6 l r).2 < pairPotentialV6 l r := by
  have hrole := role_none_of_malformed_right r hg
  change r.carrier.splice.spliceRole = .none at hrole
  cases hrt : r.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      malformedRightPendingWriteV6, clearPendingV6,
      withCarrierClearTicketV6, role,
      hrole, hg.1, hrt] <;> omega

theorem predecessorLeftScrub_write_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : role l.carrier = .predecessorArmed) :
    pairPotentialV6
        (predecessorLeftScrubWriteV6 l r).1
        (predecessorLeftScrubWriteV6 l r).2 < pairPotentialV6 l r := by
  change l.carrier.splice.spliceRole = .predecessorArmed at hg
  cases hp : l.carrier.repairPending <;>
    cases hlt : l.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      predecessorLeftScrubWriteV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6, setControl, role,
      hg, hp, hlt] <;> omega

theorem ordinaryHost_stray_ticket_drop_v6
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hlr : role l.carrier = .none)
    (hlp : l.carrier.repairPending = false)
    (hrr : role r.carrier = .none)
    (hrp : r.carrier.repairPending = false)
    (ht : l.acquireTicket = true \/ r.acquireTicket = true) :
    pairPotentialV6
        (ordinaryHostWriteV6 hpsi hwidth hle l r).1
        (ordinaryHostWriteV6 hpsi hwidth hle l r).2 < pairPotentialV6 l r := by
  change l.carrier.splice.spliceRole = .none at hlr
  change r.carrier.splice.spliceRole = .none at hrr
  cases hlt : l.acquireTicket <;>
    cases hrt : r.acquireTicket <;>
    simp [pairPotentialV6, controllerWeightV6,
      ordinaryHostWriteV6, ordinaryRow,
      withCarrierClearTicketV6, setPhysical, role,
      hlr, hlp, hrr, hrp, hlt, hrt] at ht ⊢ <;> omega

end B9SpliceControllerR1TableV6

#print axioms B9SpliceControllerR1TableV6.controllerStateFactorV6_eq
#print axioms B9SpliceControllerR1TableV6.ticketed_site_not_backing
#print axioms B9SpliceControllerR1TableV6.moveAcquireFront_preserves_edgeProvenanceV6
#print axioms B9SpliceControllerR1TableV6.pendingOwnerAbort_preserves_edgeProvenanceV6
#print axioms B9SpliceControllerR1TableV6.moveAcquireAbort_preserves_edgeProvenanceV6
#print axioms B9SpliceControllerR1TableV6.orphanReservedFront_preserves_edgeProvenanceV6
#print axioms B9SpliceControllerR1TableV6.safety_census_statuses_v6
#print axioms B9SpliceControllerR1TableV6.frontAcquire_v5_witness_repaired_v6
#print axioms B9SpliceControllerR1TableV6.pendingOwnerAbort_v5_witness_repaired_v6
#print axioms B9SpliceControllerR1TableV6.moveAcquireAbort_v5_witness_repaired_v6
#print axioms B9SpliceControllerR1TableV6.orphanReservedFront_v5_witness_repaired_v6
#print axioms B9SpliceControllerR1TableV6.q11668_moveStop_rechecked_v6
#print axioms B9SpliceControllerR1TableV6.q11674_protocol_stop_rechecked_v6
#print axioms B9SpliceControllerR1TableV6.q11681_moveSeek_rechecked_v6
#print axioms B9SpliceControllerR1TableV6.three_leaderless_drains_rechecked_v6
#print axioms B9SpliceControllerR1TableV6.four_attacks_rechecked_v6
#print axioms B9SpliceControllerR1TableV6.authenticated_follower_chain_progresses_v6
#print axioms B9SpliceControllerR1TableV6.controllerWeightV6_le_eight
#print axioms B9SpliceControllerR1TableV6.controllerPotentialV6_le_eight_mul
#print axioms B9SpliceControllerR1TableV6.moveSeek_write_drop_two_v6
#print axioms B9SpliceControllerR1TableV6.moveAcquireFront_write_drop_two_v6
#print axioms B9SpliceControllerR1TableV6.moveStopFollower_write_drop_v6

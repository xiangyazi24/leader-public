import Leader.Wu.Splice.MovingFrontTable
import Leader.Wu.Splice.ReservedFrontTable
import Leader.Wu.Splice.MovingFrontLeaderlessCycles

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceControllerR1TableV3

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2

variable {n psi width kappa tau : Nat}

/-! ## 1. Carrier and V3 move lease

V3 adds no state.  V2 already gave the existing Boolean a role-sensitive
meaning.  V3 uses the previously unused `victimArmed,true` value as the
in-flight form of a consumed `front,true` reservation.
-/

abbrev R1AgentStateV3 (psi kappa tau : Nat) :=
  R1AgentStateV2 psi kappa tau

abbrev R1ConfigV3 (n psi kappa tau : Nat) :=
  R1ConfigV2 n psi kappa tau

/-- STOP is legal only at the reserved front owned by this moving predecessor. -/
def MoveStopGuardV3
    (hpsi : 0 < psi)
    (l r : R1AgentStateV3 psi kappa tau) : Prop :=
  role l = .predecessorArmed /\ l.repairPending = false /\
  ReservedFrontHoldGuard r /\
  ¬ LocalPreparedBarrier hpsi l r

/-- SEEK consumes one reservation.  The responder becomes
`victimArmed,true`; the true bit is the non-renewable lease in flight. -/
def MoveSeekGuardV3
    (hpsi : 0 < psi)
    (l r : R1AgentStateV3 psi kappa tau) : Prop :=
  role l = .predecessorArmed /\ l.repairPending = false /\
  ReservedFrontHoldGuard r /\
  LocalPreparedBarrier hpsi l r

/-- The incoming owner holds while an authenticated request is serviced on
its outgoing edge. -/
def MoveSeekHoldGuardV3
    (l r : R1AgentStateV3 psi kappa tau) : Prop :=
  role l = .predecessorArmed /\ l.repairPending = false /\
  role r = .victimArmed /\ r.repairPending = true /\
  r.splice.base.core.core.leader = false

/-- V3 ACQUIRE cannot mint a lease.  It may only consume a request into a
front that was already reserved.  The target is left literally unchanged. -/
def MoveAcquireGuardV3
    (l r : R1AgentStateV3 psi kappa tau) : Prop :=
  role l = .victimArmed /\ l.repairPending = true /\
  l.splice.base.core.core.leader = false /\
  ReservedFrontHoldGuard r

/-- No reserved target: the authenticated request is out of fuel and aborts.
This is the branch that kills the busy-victim deadlock as well as the end of
an odd-ring circulation. -/
def MoveAcquireAbortGuardV3
    (l r : R1AgentStateV3 psi kappa tau) : Prop :=
  role l = .victimArmed /\ l.repairPending = true /\
  l.splice.base.core.core.leader = false /\
  ¬ ReservedFrontHoldGuard r

/-- A pending predecessor is legitimate on its incoming edge only when the
left endpoint is the normal predecessor that can execute MOVE-COMMIT. -/
def PendingOwnerAbortGuardV3
    (l r : R1AgentStateV3 psi kappa tau) : Prop :=
  role r = .predecessorArmed /\ r.repairPending = true /\
  ¬ (role l = .predecessorArmed /\ l.repairPending = false)

/-- A reserved front is legitimate on its incoming edge only when a
predecessor owns it.  This makes an all-reserved forged leaderless ring
scrub-able instead of a closed HOLD class. -/
def OrphanReservedFrontGuardV3
    (l r : R1AgentStateV3 psi kappa tau) : Prop :=
  ReservedFrontHoldGuard r /\ role l ≠ .predecessorArmed

/-! ## 2. Module-local computable guard instances -/

private instance q11660DecidableArmAGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (ArmAGuard hpsi hwidth hle l r) := by
  unfold ArmAGuard LeftDeletionCandidate
  infer_instance

private instance q11660DecidableArmBGuard
    {psi kappa tau : Nat}
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (ArmBGuard l r) := by
  unfold ArmBGuard
  infer_instance

private instance q11660DecidableDeleteGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (DeleteGuard hpsi hwidth hle l r) := by
  unfold DeleteGuard LeftDeletionCandidate
  infer_instance

private instance q11660DecidablePendingHoldGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (PendingHoldGuard hpsi hwidth hle l r) := by
  unfold PendingHoldGuard LeftDeletionCandidate
  infer_instance

private instance q11660DecidablePendingAbortGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (PendingAbortGuard hpsi hwidth hle l r) := by
  unfold PendingAbortGuard LeftDeletionCandidate
  infer_instance

private instance q11660DecidableMoveCommitGuard
    {psi kappa tau : Nat}
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (MoveCommitGuard l r) := by
  unfold MoveCommitGuard
  infer_instance

private instance q11660DecidableReservedFrontHoldGuard
    {psi kappa tau : Nat}
    (u : R1AgentStateV3 psi kappa tau) :
    Decidable (ReservedFrontHoldGuard u) := by
  unfold ReservedFrontHoldGuard
  infer_instance

private instance q11660DecidableMoveStopGuardV3
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (MoveStopGuardV3 hpsi l r) := by
  unfold MoveStopGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance q11660DecidableMoveSeekGuardV3
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (MoveSeekGuardV3 hpsi l r) := by
  unfold MoveSeekGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance q11660DecidableMoveSeekHoldGuardV3
    {psi kappa tau : Nat}
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (MoveSeekHoldGuardV3 l r) := by
  unfold MoveSeekHoldGuardV3
  infer_instance

private instance q11660DecidableMoveAcquireGuardV3
    {psi kappa tau : Nat}
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (MoveAcquireGuardV3 l r) := by
  unfold MoveAcquireGuardV3 ReservedFrontHoldGuard
  infer_instance

private instance q11660DecidableMoveAcquireAbortGuardV3
    {psi kappa tau : Nat}
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (MoveAcquireAbortGuardV3 l r) := by
  unfold MoveAcquireAbortGuardV3 ReservedFrontHoldGuard
  infer_instance

private instance q11660DecidablePendingOwnerAbortGuardV3
    {psi kappa tau : Nat}
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (PendingOwnerAbortGuardV3 l r) := by
  unfold PendingOwnerAbortGuardV3
  infer_instance

private instance q11660DecidableOrphanReservedFrontGuardV3
    {psi kappa tau : Nat}
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (OrphanReservedFrontGuardV3 l r) := by
  unfold OrphanReservedFrontGuardV3 ReservedFrontHoldGuard
  infer_instance

/-! ## 3. V3 row and ring lift -/

/-- Constant-state V3 table.

Compared with V2:
* DELETE is byte-for-byte the V2 write and still records `front,true`;
* STOP/SEEK require that reservation;
* SEEK changes it to `victimArmed,true`;
* ACQUIRE requires another already-reserved front and does not mint one;
* out-of-fuel requests and orphan reservation/pending shapes scrub.
-/
def rowV3
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV3 psi kappa tau) :
    R1AgentStateV3 psi kappa tau × R1AgentStateV3 psi kappa tau :=
  if ArmAGuard hpsi hwidth hle l r then
    (setControl l .victimArmed false,
      setControl r .front false)
  else if ArmBGuard l r then
    (setControl l .predecessorArmed false,
      setControl r .front false)
  -- V2 DELETE fix, unchanged: reserve the surviving backing front.
  else if DeleteGuard hpsi hwidth hle l r then
    let q := BirthShortDoneTerminalHost.row
      hpsi hwidth hle l.splice.base r.splice.base
    (setControl (setPhysical l q.1) .predecessorArmed true,
      setControl (setPhysical r q.2) .front true)
  else if PendingHoldGuard hpsi hwidth hle l r then
    (l, r)
  else if PendingAbortGuard hpsi hwidth hle l r then
    (clearControl l, clearControl r)
  else if MoveCommitGuard l r then
    (clearControl l,
      setControl (repairResponder hpsi l r) .predecessorArmed false)
  else if MoveStopGuardV3 hpsi l r then
    (clearControl l, clearControl r)
  else if MoveSeekGuardV3 hpsi l r then
    (l, setControl r .victimArmed true)
  else if MoveSeekHoldGuardV3 l r then
    (l, r)
  -- Incoming-edge orphan scrub must precede the pending owner's outgoing hold.
  else if PendingOwnerAbortGuardV3 l r then
    (l, clearControl r)
  -- A pending owner cannot spend its outgoing reservation before commit.
  else if role l = .predecessorArmed /\ l.repairPending = true then
    (l, r)
  else if MoveAcquireGuardV3 l r then
    (setControl l .predecessorArmed true, r)
  else if MoveAcquireAbortGuardV3 l r then
    (clearControl l, r)
  -- Scrub an incoming reserved front that has no predecessor owner.
  else if OrphanReservedFrontGuardV3 l r then
    (l, clearControl r)
  -- A valid reserved front is passive on its outgoing edge; its incoming
  -- owner edge is the only edge allowed to consume it.
  else if ReservedFrontHoldGuard l then
    (l, r)
  -- Old unauthenticated moving requests are stale in V3.
  else if role r = .victimArmed then
    (l, clearControl r)
  else if role l = .victimArmed then
    (clearControl l, r)
  -- Old unreserved fronts are stale unless an earlier deletion guard owns them.
  else if role r = .front then
    (l, clearControl r)
  -- Malformed bits remain scrub-able.  V3's three meaningful true-bit forms
  -- were already consumed above: predecessor pending, reserved front, and
  -- authenticated victim request.
  else if l.repairPending = true /\
      role l ≠ .predecessorArmed /\
      role l ≠ .front /\
      role l ≠ .victimArmed then
    ({ l with repairPending := false }, r)
  else if r.repairPending = true /\
      role r ≠ .predecessorArmed /\
      role r ≠ .front /\
      role r ≠ .victimArmed then
    (l, { r with repairPending := false })
  else if role l = .predecessorArmed then
    (clearControl l, r)
  -- Orientation rule retained for an unreserved left front.  Its incoming edge
  -- can scrub it; it never falls through to the host while marked.
  else if role l = .front then
    (l, r)
  else if role l ≠ .none \/ role r ≠ .none /\
      (l.repairPending = true \/ r.repairPending = true) then
    (l, r)
  else
    ordinaryRow hpsi hwidth hle l r

/-- Ring lift; retain V2's fail-closed one-site behavior. -/
def stepV3
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV3 n psi kappa tau)
    (e : Fin n) : R1ConfigV3 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV3 hpsi hwidth hle (C e) (C j)
    fun i =>
      if i = e then q.1
      else if i = j then q.2
      else C i

/-! ## 4. V3 safety vocabulary used by the finite reruns -/

/-- V3-owned danger shapes.  In addition to the two V2 frozen seam forms,
the moving predecessor may own only a reserved front, an authenticated
victim request, or a pending predecessor. -/
def R1ProtectedSpliceEdgeV3
    (ring : DirectedRing n) (C : R1ConfigV3 n psi kappa tau)
    (e : Fin n) : Prop :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  ReservedFrontHoldGuard l \/
  (role r = .predecessorArmed /\ r.repairPending = true) \/
  (role l = .predecessorArmed /\ l.repairPending = false /\
    (ReservedFrontHoldGuard r \/
     (role r = .victimArmed /\ r.repairPending = true) \/
     (role r = .predecessorArmed /\ r.repairPending = true)))

def SpliceSafeR1V3
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) : Prop :=
  (forall e,
      PreparedDangerAt hpsi ring C e ->
        R1ProtectedSpliceEdgeV3 ring C e) /\
  (forall i,
      role (C i) = .predecessorArmed ->
      (C i).repairPending = true ->
        ReservedFrontHoldGuard (C (ring.rightNeighbor i)))

private instance q11660DecidablePreparedDangerAtLocal
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance

private instance q11660DecidableR1ProtectedSpliceEdgeV3Local
    {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : R1ConfigV3 n psi kappa tau)
    (e : Fin n) :
    Decidable (R1ProtectedSpliceEdgeV3 ring C e) := by
  unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard
  dsimp only
  infer_instance

private instance q11660DecidableSpliceSafeR1V3Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) :
    Decidable (SpliceSafeR1V3 hpsi ring C) := by
  unfold SpliceSafeR1V3
  infer_instance

private instance q11660DecidablePPrimeBarrierBirthGuardLocal
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    Decidable (PPrimeBarrierBirthGuard hpsi l r) := by
  unfold PPrimeBarrierBirthGuard
  unfold isBarrier
  infer_instance

/-- P-prime source predicate with V3 ownership. -/
def R1AmendedPPrimeAtV3
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) (e : Fin n) : Prop :=
  let l0 := preparedR1 hpsi (C e)
  let r0 := preparedR1 hpsi (C (ring.rightNeighbor e))
  PPrimeBarrierBirthGuard hpsi l0 r0 /\
    ¬ R1ProtectedSpliceEdgeV3 ring C e

private instance q11660DecidableR1AmendedPPrimeAtV3Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) (e : Fin n) :
    Decidable (R1AmendedPPrimeAtV3 hpsi ring C e) := by
  unfold R1AmendedPPrimeAtV3
  dsimp only
  infer_instance

def R1SourceFreeV3
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) : Prop :=
  forall e, ¬ R1AmendedPPrimeAtV3 hpsi ring C e

private instance q11660DecidableR1SourceFreeV3Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) :
    Decidable (R1SourceFreeV3 hpsi ring C) := by
  unfold R1SourceFreeV3
  infer_instance

/-! ## 5. State factor -/

/-- V3 reuses V2's role/bit combinations and adds no local field. -/
def controllerStateFactorV3 : Nat := controllerStateFactorV2

theorem controllerStateFactorV3_eq : controllerStateFactorV3 = 8 := by
  decide

/-! ## 6. Closed psi=2 attack reruns -/

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hFour : 0 < 4 := by decide
private theorem hFive : 0 < 5 := by decide

private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def ring4 : DirectedRing 4 := ⟨hFour⟩
private def ring5 : DirectedRing 5 := ⟨hFive⟩

def serveV3 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV3 n 2 0 0) (e : Fin n) :
    R1ConfigV3 n 2 0 0 :=
  stepV3 hTwo hTwo hTwoLe ring C e

def runV3 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV3 n 2 0 0)
    (word : List (Fin n)) : R1ConfigV3 n 2 0 0 :=
  List.foldl (fun D e => serveV3 ring D e) C word

def LeaderlessV3 {n : Nat} (C : R1ConfigV3 n 2 0 0) : Prop :=
  forall i, (C i).splice.base.core.core.leader = false

def RolesClearV3 {n : Nat} (C : R1ConfigV3 n 2 0 0) : Prop :=
  forall i, role (C i) = .none /\ (C i).repairPending = false

private instance q11660DecidableLeaderlessV3Local
    {n : Nat} (C : R1ConfigV3 n 2 0 0) :
    Decidable (LeaderlessV3 C) := by
  unfold LeaderlessV3
  infer_instance

private instance q11660DecidableRolesClearV3Local
    {n : Nat} (C : R1ConfigV3 n 2 0 0) :
    Decidable (RolesClearV3 C) := by
  unfold RolesClearV3
  infer_instance

def safeAlongV3 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV3 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (SpliceSafeR1V3 hTwo ring C)
  | C, e :: es =>
      decide (SpliceSafeR1V3 hTwo ring C) &&
        safeAlongV3 ring (serveV3 ring C e) es

def sourceFreeAlongV3 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV3 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (R1SourceFreeV3 hTwo ring C)
  | C, e :: es =>
      decide (R1SourceFreeV3 hTwo ring C) &&
        sourceFreeAlongV3 ring (serveV3 ring C e) es

/-! ### Former leaderless 3-cycle -/

/-- This is the first three symbols of the certified old cycle word.  V3's
first service scrubs the unreserved front; the third service then scrubs the
orphan predecessor. -/
def loop3DrainPrefixV3 : List (Fin 3) := [0, 1, 0]

theorem leaderless_cycle3_v3_killed :
    LeaderlessV3 B9SpliceR2AttackRerun.loop3Start /\
    RolesClearV3
      (runV3 ring3 B9SpliceR2AttackRerun.loop3Start loop3DrainPrefixV3) /\
    role (serveV3 ring3 B9SpliceR2AttackRerun.loop3Start (0 : Fin 3)
      (1 : Fin 3)) = .none := by
  decide

/-! ### Former leaderless 4-deadlock -/

/-- Use the two old services, then repeat them.  The first pair removes the two
unreserved fronts; the second pair removes the two orphan predecessors. -/
def loop4DrainWordV3 : List (Fin 4) := [0, 2, 0, 2]

def loop4OldPrefixV3 : R1ConfigV3 4 2 0 0 :=
  runV3 ring4 B9SpliceR2AttackRerun.loop4Start [(0 : Fin 4), (2 : Fin 4)]

theorem leaderless_deadlock4_v3_killed :
    LeaderlessV3 B9SpliceR2AttackRerun.loop4Start /\
    role (loop4OldPrefixV3 (0 : Fin 4)) = .predecessorArmed /\
    role (serveV3 ring4 loop4OldPrefixV3 (0 : Fin 4) (0 : Fin 4)) = .none /\
    RolesClearV3
      (runV3 ring4 B9SpliceR2AttackRerun.loop4Start loop4DrainWordV3) := by
  decide

/-! ### Former leaderless 5-cycle -/

def loop5DrainPrefixV3 : List (Fin 5) := [0, 1, 0]

theorem leaderless_cycle5_v3_killed :
    LeaderlessV3 B9SpliceR2AttackRerun.loop5Start /\
    RolesClearV3
      (runV3 ring5 B9SpliceR2AttackRerun.loop5Start loop5DrainPrefixV3) /\
    role (serveV3 ring5 B9SpliceR2AttackRerun.loop5Start (0 : Fin 5)
      (1 : Fin 5)) = .none := by
  decide

/-! ### Same-edge replay remains frozen -/

def q11592Armed4V3 : R1ConfigV3 4 2 0 0 :=
  serveV3 ring4 B9SpliceR2AttackRerun.q11592Start4 (1 : Fin 4)

def q11592Replay4V3 : R1ConfigV3 4 2 0 0 :=
  serveV3 ring4 q11592Armed4V3 (1 : Fin 4)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem q11592_pending_hold_replay_v3 :
    role (q11592Armed4V3 (1 : Fin 4)) = .victimArmed /\
    (q11592Armed4V3 (1 : Fin 4)).repairPending = false /\
    role (q11592Armed4V3 (2 : Fin 4)) = .front /\
    (q11592Armed4V3 (2 : Fin 4)).repairPending = false /\
    PendingHoldGuard hTwo hTwo hTwoLe
      (q11592Armed4V3 (1 : Fin 4))
      (q11592Armed4V3 (2 : Fin 4)) /\
    (forall i, q11592Replay4V3 i = q11592Armed4V3 i) := by
  decide

/-! ### Follower anchor: literal old forged mark is untrusted; authenticated
chain preserves the intended repair -/

/-- Exact old R1 first service.  Because the old fixture has `front,false`, V3
refuses to treat it as a renewable moving lease and scrubs it. -/
def followerOldFirstV3 : R1ConfigV3 5 2 0 0 :=
  serveV3 ring5 B9SpliceR2AttackRerun.followerStart5 (0 : Fin 5)

theorem follower_old_unreserved_front_does_not_move_v3 :
    role (followerOldFirstV3 (0 : Fin 5)) = .predecessorArmed /\
    role (followerOldFirstV3 (1 : Fin 5)) = .none := by
  decide

/-- Same physical follower-anchor picture, now with the V3 ownership lease
already present along the two-hop repair route.  No physical field differs
from the earlier fixture. -/
def followerStart5V3 : R1ConfigV3 5 2 0 0 := fun i =>
  if i = 0 then
    B9SpliceR2AttackRerun.xcell false 1 false .predecessorArmed false
  else if i = 1 then
    B9SpliceR2AttackRerun.xcell false 1 false .front true
  else if i = 2 then
    B9SpliceR2AttackRerun.xcell false 0 true .front true
  else if i = 3 then
    B9SpliceR2AttackRerun.xcell false 1 false .front true
  else
    B9SpliceR2AttackRerun.xcell true 0 false .none false

/-- SEEK, ACQUIRE, COMMIT twice, exactly as in the earlier fixture. -/
def followerWord5V3 : List (Fin 5) := [0, 1, 0, 1, 2, 1]

def followerAfter5V3 : R1ConfigV3 5 2 0 0 :=
  runV3 ring5 followerStart5V3 followerWord5V3

theorem follower_anchor_authenticated_chain_safe_v3 :
    safeAlongV3 ring5 followerStart5V3 followerWord5V3 = true /\
    sourceFreeAlongV3 ring5 followerStart5V3 followerWord5V3 = true /\
    role (followerAfter5V3 (2 : Fin 5)) = .predecessorArmed /\
    (followerAfter5V3 (2 : Fin 5)).repairPending = false /\
    role (followerAfter5V3 (3 : Fin 5)) = .front /\
    (followerAfter5V3 (3 : Fin 5)).repairPending = true /\
    (followerAfter5V3 (2 : Fin 5)).splice.base.core.core.probe = false := by
  decide

/-! ### Staged deletion remains non-starved and uses the V2 reservation -/

def stagedArmed3V3 : R1ConfigV3 3 2 0 0 :=
  serveV3 ring3 B9SpliceR2AttackRerun.stagedStart3 (1 : Fin 3)

def starvationFinal3V3 : R1ConfigV3 3 2 0 0 :=
  runV3 ring3 B9SpliceR2AttackRerun.stagedStart3
    B9SpliceR2AttackRerun.starvationWord3

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem staged_deletion_not_arm_scrub_starved_v3 :
    (forall i,
      serveV3 ring3 stagedArmed3V3 (2 : Fin 3) i = stagedArmed3V3 i) /\
    (forall i,
      serveV3 ring3 stagedArmed3V3 (1 : Fin 3) i = stagedArmed3V3 i) /\
    safeAlongV3 ring3 B9SpliceR2AttackRerun.stagedStart3
      B9SpliceR2AttackRerun.starvationWord3 = true /\
    RolesClearV3 starvationFinal3V3 /\
    (starvationFinal3V3 (1 : Fin 3)).splice.base.core.core.leader = false /\
    (starvationFinal3V3 (2 : Fin 3)).splice.base.core.core.leader = true := by
  decide

end B9SpliceControllerR1TableV3

#print axioms B9SpliceControllerR1TableV3.controllerStateFactorV3_eq
#print axioms B9SpliceControllerR1TableV3.leaderless_cycle3_v3_killed
#print axioms B9SpliceControllerR1TableV3.leaderless_deadlock4_v3_killed
#print axioms B9SpliceControllerR1TableV3.leaderless_cycle5_v3_killed
#print axioms B9SpliceControllerR1TableV3.q11592_pending_hold_replay_v3
#print axioms B9SpliceControllerR1TableV3.follower_old_unreserved_front_does_not_move_v3
#print axioms B9SpliceControllerR1TableV3.follower_anchor_authenticated_chain_safe_v3
#print axioms B9SpliceControllerR1TableV3.staged_deletion_not_arm_scrub_starved_v3

import Leader.Wu.Splice.Controller

set_option autoImplicit false

namespace B9SpliceControllerR1Table

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign

variable {n psi width kappa tau : Nat}

/-- The four-role carrier plus one constant moving-front bit.
`repairPending = true` means that this site is a `predecessorArmed`
owner whose right-hand `front` has already been acquired, but whose own
incoming seam still has to be repaired. -/
structure R1AgentState (psi kappa tau : Nat) where
  splice : SpliceAgentState psi kappa tau
  repairPending : Bool
  deriving DecidableEq, Repr

abbrev R1Config (n psi kappa tau : Nat) :=
  Fin n -> R1AgentState psi kappa tau

/-- Controller role projection. -/
def role (u : R1AgentState psi kappa tau) : SpliceRole :=
  u.splice.spliceRole

/-- Current physical/expiry carrier. -/
def physical
    (u : R1AgentState psi kappa tau) : ExpiringAgentState psi kappa tau :=
  u.splice.base

/-- Change only the controller role. -/
def setRole
    (u : R1AgentState psi kappa tau) (r : SpliceRole) :
    R1AgentState psi kappa tau :=
  { u with splice := { u.splice with spliceRole := r } }

/-- Change role and moving-front bit together. -/
def setControl
    (u : R1AgentState psi kappa tau) (r : SpliceRole) (pending : Bool) :
    R1AgentState psi kappa tau :=
  { u with
    splice := { u.splice with spliceRole := r }
    repairPending := pending }

/-- Change only the physical/expiry carrier. -/
def setPhysical
    (u : R1AgentState psi kappa tau)
    (b : ExpiringAgentState psi kappa tau) :
    R1AgentState psi kappa tau :=
  { u with splice := { u.splice with base := b } }

/-- Return one endpoint to controller-neutral state. -/
def clearControl
    (u : R1AgentState psi kappa tau) : R1AgentState psi kappa tau :=
  setControl u .none false

/-- Local ruler repair: change only responder label/probe/phase. -/
def repairResponder
    (hpsi : 0 < psi)
    (l r : R1AgentState psi kappa tau) :
    R1AgentState psi kappa tau :=
  { r with
    splice :=
      { r.splice with
        base :=
          { r.splice.base with
            core :=
              { r.splice.base.core with
                core :=
                  { r.splice.base.core.core with
                    label :=
                      ⟨(l.splice.base.core.core.label.val + 1) % psi,
                        Nat.mod_lt _ hpsi⟩
                    probe := false
                    phase := false } } } } }

/-- Preparation cut, lifted to R1. -/
def preparedR1
    (hpsi : 0 < psi) (u : R1AgentState psi kappa tau) :
    AuthorizedAgentState psi :=
  prepared hpsi u.splice

/-- Local prepared barrier entering a follower. -/
def LocalPreparedBarrier
    (hpsi : 0 < psi)
    (l r : R1AgentState psi kappa tau) : Prop :=
  let l0 := preparedR1 hpsi l
  let r0 := preparedR1 hpsi r
  r0.core.leader = false /\ isBarrier hpsi l0.core r0.core

/-- R1 projection back to the splice carrier. -/
def projectSpliceConfig
    (C : R1Config n psi kappa tau) : SpliceConfig n psi kappa tau :=
  fun i => (C i).splice

/-- Exact geometric P-prime danger: both prepared endpoints are followers and
there is a barrier.  This is `PreparedBarrierAt` plus the missing left
follower condition from the actual P-prime source. -/
def PreparedDangerAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) (e : Fin n) : Prop :=
  (preparedR1 hpsi (C e)).core.leader = false /\
    PreparedBarrierAt hpsi ring (projectSpliceConfig C) e

/-- Three owned moving shapes.

1. `predecessorArmed -> front`: ordinary owned seam;
2. `predecessorArmed -> victimArmed`: rightward acquisition requested;
3. `predecessorArmed -> predecessorArmed(pending)`: the right site has
   acquired its next `front` and waits for its incoming repair.
-/
def R1ProtectedSpliceEdge
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n) : Prop :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  role l = .predecessorArmed /\
    ((role r = .front /\ r.repairPending = false) \/
     (role r = .victimArmed /\ r.repairPending = false) \/
     (role r = .predecessorArmed /\ r.repairPending = true))

/-- Generalized splice safety.  The first clause says every actual
follower/follower prepared barrier is locally owned.  The second clause is the
moving-front backing invariant: a pending owner already has a right `front`
before any incoming repair is allowed to change its label. -/
def SpliceSafeR1
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) : Prop :=
  (forall e,
      PreparedDangerAt hpsi ring C e ->
        R1ProtectedSpliceEdge ring C e) /\
    (forall i,
      (C i).repairPending = true ->
        role (C i) = .predecessorArmed /\
        role (C (ring.rightNeighbor i)) = .front /\
        (C (ring.rightNeighbor i)).repairPending = false)

/-! ## Exact edge-local guards -/

def ArmAGuard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .none /\ role r = .none /\
  l.repairPending = false /\ r.repairPending = false /\
  LeftDeletionCandidate hpsi hwidth hle l.splice r.splice

/-- ARM-B records predecessor ownership but does not touch physical state. -/
def ArmBGuard
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .none /\ l.repairPending = false /\
  role r = .victimArmed /\ r.repairPending = false /\
  r.splice.base.core.core.leader = true

/-- The old deletion may commit only after ARM-B changed the victim to `front`.
The outside predecessor remains `predecessorArmed`. -/
def DeleteGuard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .front /\ role r = .front /\
  l.repairPending = false /\ r.repairPending = false /\
  LeftDeletionCandidate hpsi hwidth hle l.splice r.splice

/-- Explicit repair: replaying the prospective deletion edge after
ARM-A is a framing HOLD, never the old host row. -/
def PendingHoldGuard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .victimArmed /\ role r = .front /\
  l.repairPending = false /\ r.repairPending = false /\
  LeftDeletionCandidate hpsi hwidth hle l.splice r.splice

/-- If the staged deletion ceases before ARM-B, erase the pending pair. -/
def PendingAbortGuard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .victimArmed /\ role r = .front /\
  l.repairPending = false /\ r.repairPending = false /\
  l.splice.base.core.core.leader = true /\
  ¬ LeftDeletionCandidate hpsi hwidth hle l.splice r.splice

/-- Incoming repair after DELETE or MOVE-ACQUIRE.  The right endpoint already
owns its next seam, so repairing it cannot expose an unowned new barrier. -/
def MoveCommitGuard
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .predecessorArmed /\ l.repairPending = false /\
  role r = .predecessorArmed /\ r.repairPending = true /\
  r.splice.base.core.core.leader = false

/-- Stop when the owned seam has reached a surviving leader or is already
prepared-aligned. -/
def MoveStopGuard
    (hpsi : 0 < psi)
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .predecessorArmed /\ l.repairPending = false /\
  role r = .front /\ r.repairPending = false /\
  ¬ LocalPreparedBarrier hpsi l r

/-- A follower barrier needs one more rightward ownership acquisition. -/
def MoveSeekGuard
    (hpsi : 0 < psi)
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .predecessorArmed /\ l.repairPending = false /\
  role r = .front /\ r.repairPending = false /\
  LocalPreparedBarrier hpsi l r

/-- While a moving request waits for its outgoing acquisition, its incoming
owned barrier is frozen. -/
def MoveSeekHoldGuard
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .predecessorArmed /\ l.repairPending = false /\
  role r = .victimArmed /\ r.repairPending = false /\
  r.splice.base.core.core.leader = false

/-- The follower request acquires its next site before it can be relabelled.
An existing neutral `front` may be adopted; otherwise the target must be
controller-clear. -/
def MoveAcquireGuard
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .victimArmed /\ l.repairPending = false /\
  l.splice.base.core.core.leader = false /\
  r.repairPending = false /\
  (role r = .none \/ role r = .front)

/-- Exact old host row lifted through the R1 wrapper. -/
def ordinaryRow
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) :
    R1AgentState psi kappa tau × R1AgentState psi kappa tau :=
  let q := BirthShortDoneTerminalHost.row
    hpsi hwidth hle l.splice.base r.splice.base
  (setPhysical l q.1, setPhysical r q.2)

/-! ## Repaired transition table -/

private instance q11642DecidableArmAGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) :
    Decidable (ArmAGuard hpsi hwidth hle l r) := by
  unfold ArmAGuard LeftDeletionCandidate
  infer_instance


private instance q11642DecidableArmBGuard
    {psi kappa tau : Nat}
    (l r : R1AgentState psi kappa tau) :
    Decidable (ArmBGuard l r) := by
  unfold ArmBGuard
  infer_instance


private instance q11642DecidableDeleteGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) :
    Decidable (DeleteGuard hpsi hwidth hle l r) := by
  unfold DeleteGuard LeftDeletionCandidate
  infer_instance


private instance q11642DecidablePendingHoldGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) :
    Decidable (PendingHoldGuard hpsi hwidth hle l r) := by
  unfold PendingHoldGuard LeftDeletionCandidate
  infer_instance


private instance q11642DecidablePendingAbortGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) :
    Decidable (PendingAbortGuard hpsi hwidth hle l r) := by
  unfold PendingAbortGuard LeftDeletionCandidate
  infer_instance


private instance q11642DecidableMoveCommitGuard
    {psi kappa tau : Nat}
    (l r : R1AgentState psi kappa tau) :
    Decidable (MoveCommitGuard l r) := by
  unfold MoveCommitGuard
  infer_instance


private instance q11642DecidableMoveStopGuard
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentState psi kappa tau) :
    Decidable (MoveStopGuard hpsi l r) := by
  unfold MoveStopGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance


private instance q11642DecidableMoveSeekGuard
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentState psi kappa tau) :
    Decidable (MoveSeekGuard hpsi l r) := by
  unfold MoveSeekGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance


private instance q11642DecidableMoveSeekHoldGuard
    {psi kappa tau : Nat}
    (l r : R1AgentState psi kappa tau) :
    Decidable (MoveSeekHoldGuard l r) := by
  unfold MoveSeekHoldGuard
  infer_instance


private instance q11642DecidableMoveAcquireGuard
    {psi kappa tau : Nat}
    (l r : R1AgentState psi kappa tau) :
    Decidable (MoveAcquireGuard l r) := by
  unfold MoveAcquireGuard
  infer_instance

/-- Constant-state R1 splice row.

Crucial points:
* PENDING-HOLD is explicit and precedes ordinary execution;
* a left-endpoint `front` is never scrubbed;
* right-front scrub changes only the right endpoint;
* moving ownership acquires the next `front` before `repairResponder` runs. -/
def row
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) :
    R1AgentState psi kappa tau × R1AgentState psi kappa tau :=
  -- ARM-A: seed victim and deletion-edge anchor.
  if ArmAGuard hpsi hwidth hle l r then
    (setControl l .victimArmed false,
      setControl r .front false)
  -- ARM-B: predecessor takes ownership; victim becomes commit-ready front.
  else if ArmBGuard l r then
    (setControl l .predecessorArmed false,
      setControl r .front false)
  -- DELETE: execute exactly the old host row.  The deleted left endpoint
  -- becomes the new moving owner, backed by the existing right front.
  else if DeleteGuard hpsi hwidth hle l r then
    let q := BirthShortDoneTerminalHost.row
      hpsi hwidth hle l.splice.base r.splice.base
    (setControl (setPhysical l q.1) .predecessorArmed true,
      setControl (setPhysical r q.2) .front false)
  -- Explicit pending-deletion freeze.
  else if PendingHoldGuard hpsi hwidth hle l r then
    (l, r)
  -- Pending deletion disappeared before predecessor acquisition.
  else if PendingAbortGuard hpsi hwidth hle l r then
    (clearControl l, clearControl r)
  -- MOVE-COMMIT: repair the pending owner from its predecessor, then release
  -- the predecessor.  The repaired site keeps ownership of its right front.
  else if MoveCommitGuard l r then
    (clearControl l,
      setControl (repairResponder hpsi l r) .predecessorArmed false)
  -- Reached a leader or an aligned seam: release both controller marks.
  else if MoveStopGuard hpsi l r then
    (clearControl l, clearControl r)
  -- Barrier continues: turn the right front into a follower acquisition request.
  else if MoveSeekGuard hpsi l r then
    (l, setControl r .victimArmed false)
  -- Incoming owner waits while the request acquires one site to its right.
  else if MoveSeekHoldGuard l r then
    (l, r)
  -- A pending owner is never allowed to act on its outgoing seam before its
  -- own incoming repair commits.
  else if role l = .predecessorArmed /\ l.repairPending = true then
    (l, r)
  -- Acquire the next seam.  No label is changed here.
  else if MoveAcquireGuard l r then
    (setControl l .predecessorArmed true,
      setControl r .front false)
  -- A follower moving request with a busy target waits; it never falls through.
  else if role l = .victimArmed /\
      l.splice.base.core.core.leader = false then
    (l, r)
  -- Malformed extra bits are removable without touching physical state.
  else if l.repairPending = true /\ role l ≠ .predecessorArmed then
    ({ l with repairPending := false }, r)
  else if r.repairPending = true /\ role r ≠ .predecessorArmed then
    (l, { r with repairPending := false })
  -- Oriented front cleanup: only the RIGHT front is scrubbed.  If both
  -- endpoints are fronts, the left one is literally held.
  else if role r = .front then
    (l, clearControl r)
  -- Stale moving request, scrubbed only when it is the responder.
  else if role r = .victimArmed then
    (l, clearControl r)
  -- Orphan predecessor after all canonical successor shapes were consumed.
  else if role l = .predecessorArmed then
    (clearControl l, r)
  -- Stale leader-side victim marker.
  else if role l = .victimArmed then
    (clearControl l, r)
  -- Orientation rule: a left-endpoint front is held, never self-scrubbed and
  -- never passed to the old host row.
  else if role l = .front then
    (l, r)
  -- Any remaining non-neutral control state fails closed rather than exposing
  -- the old row.
  else if role l ≠ .none \/ role r ≠ .none /\
      (l.repairPending = true \/ r.repairPending = true) then
    (l, r)
  -- Only the controller-neutral pair reaches the current host.
  else
    ordinaryRow hpsi hwidth hle l r

/-- Ring lift of the edge-local table. -/
def step
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n) : R1Config n psi kappa tau :=
  let j := ring.rightNeighbor e
  let q := row hpsi hwidth hle (C e) (C j)
  fun i =>
    if i = e then q.1
    else if i = j then q.2
    else C i

/-- Immediate projection of the first safety clause. -/
theorem spliceSafeR1_danger_owned
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau)
    (hsafe : SpliceSafeR1 hpsi ring C) (e : Fin n)
    (hdanger : PreparedDangerAt hpsi ring C e) :
    R1ProtectedSpliceEdge ring C e :=
  hsafe.1 e hdanger

/-- Immediate projection of the moving-front backing clause. -/
theorem spliceSafeR1_pending_backed
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau)
    (hsafe : SpliceSafeR1 hpsi ring C) (i : Fin n)
    (hp : (C i).repairPending = true) :
    role (C i) = .predecessorArmed /\
      role (C (ring.rightNeighbor i)) = .front /\
      (C (ring.rightNeighbor i)).repairPending = false :=
  hsafe.2 i hp

/-- Per-agent splice-control factor over the original physical carrier:
four splice roles times one Boolean moving-front bit. -/
def controllerStateFactor : Nat := 8

/-- Relative factor over the already-four-way splice carrier. -/
def factorOverQ11593 : Nat := 2

theorem controllerStateFactor_eq :
    controllerStateFactor = 4 * factorOverQ11593 := by
  decide

end B9SpliceControllerR1Table

#print axioms B9SpliceControllerR1Table.spliceSafeR1_danger_owned
#print axioms B9SpliceControllerR1Table.spliceSafeR1_pending_backed
#print axioms B9SpliceControllerR1Table.controllerStateFactor_eq

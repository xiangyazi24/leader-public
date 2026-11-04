import Leader.Wu.Splice.FollowerStopSeekHold
import Leader.Wu.Birth.PPrimeRearmThenBirthRingSix

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9HostBarrierHole

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerR1TableV4

variable {n psi width kappa tau : Nat}

/-! ## Restated V6-sized carrier, without importing the changing V6 table -/

/-- Exactly the V6 state factor needed by this design leaf: the accepted V4
carrier plus the already-existing acquisition-provenance bit.  No new field is
introduced by the host-hole repair. -/
structure HostTicketAgent (psi kappa tau : Nat) where
  carrier : R1AgentStateV4 psi kappa tau
  acquireTicket : Bool
  deriving DecidableEq, Repr

abbrev HostTicketConfig (n psi kappa tau : Nat) :=
  Fin n -> HostTicketAgent psi kappa tau

def liftHostTicket
    (u : R1AgentStateV4 psi kappa tau) : HostTicketAgent psi kappa tau :=
  ⟨u, false⟩

def projectHostTicket
    (C : HostTicketConfig n psi kappa tau) : R1ConfigV4 n psi kappa tau :=
  fun i => (C i).carrier

def setHostTicket
    (u : HostTicketAgent psi kappa tau) (b : Bool) :
    HostTicketAgent psi kappa tau :=
  { u with acquireTicket := b }

def withHostCarrier
    (u : HostTicketAgent psi kappa tau)
    (c : R1AgentStateV4 psi kappa tau) : HostTicketAgent psi kappa tau :=
  { u with carrier := c }

/-- The new meaning of the formerly-invalid neutral ticket shape. -/
def HostFenceShape
    (u : HostTicketAgent psi kappa tau) : Prop :=
  role u.carrier = .none ∧
    u.carrier.repairPending = false ∧
    u.acquireTicket = true

/-- A true ticket is either the old authenticated front request or the new
neutral host fence.  The two shapes are disjoint by role. -/
def HostTicketShape
    (u : HostTicketAgent psi kappa tau) : Prop :=
  u.acquireTicket = true ->
    ReservedFrontHoldGuard u.carrier ∨ HostFenceShape u

/-- V6's pending-predecessor backing condition is unchanged. -/
def HostProvenanceSafe
    (ring : DirectedRing n)
    (C : HostTicketConfig n psi kappa tau) : Prop :=
  (forall i, HostTicketShape (C i)) ∧
    (forall i,
      role (C i).carrier = .predecessorArmed ->
      (C i).carrier.repairPending = true ->
        ReservedFrontHoldGuard (C (ring.rightNeighbor i)).carrier ∧
        (C (ring.rightNeighbor i)).acquireTicket = false)

/-- A prepared danger is protected either by the existing V3 splice ownership
or by a one-sided neutral host fence on its left endpoint. -/
def HostProtectedSpliceEdge
    (ring : DirectedRing n)
    (C : HostTicketConfig n psi kappa tau) (e : Fin n) : Prop :=
  R1ProtectedSpliceEdgeV3 ring (projectHostTicket C) e ∨
    HostFenceShape (C e)

/-- Strengthened whole-controller safety vocabulary for the host-hole repair. -/
def HostSpliceSafe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : HostTicketConfig n psi kappa tau) : Prop :=
  (forall e,
      PreparedDangerAt hpsi ring (projectHostTicket C) e ->
        HostProtectedSpliceEdge ring C e) ∧
    HostProvenanceSafe ring C

/-- The corresponding P-prime source: a physical source is live only when no
splice certificate and no host fence owns the edge. -/
def HostAmendedPPrimeAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : HostTicketConfig n psi kappa tau) (e : Fin n) : Prop :=
  let l0 := preparedR1 hpsi (C e).carrier
  let r0 := preparedR1 hpsi (C (ring.rightNeighbor e)).carrier
  PPrimeBarrierBirthGuard hpsi l0 r0 ∧
    ¬ HostProtectedSpliceEdge ring C e

private instance instDecidableReservedFrontHost
    (u : HostTicketAgent psi kappa tau) :
    Decidable (ReservedFrontHoldGuard u.carrier) := by
  unfold ReservedFrontHoldGuard
  infer_instance

private instance instDecidableHostFenceShape
    (u : HostTicketAgent psi kappa tau) : Decidable (HostFenceShape u) := by
  unfold HostFenceShape
  infer_instance

private instance instDecidableLocalPreparedBarrierHost
    (hpsi : 0 < psi)
    (l r : HostTicketAgent psi kappa tau) :
    Decidable (LocalPreparedBarrier hpsi l.carrier r.carrier) := by
  unfold LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidablePreparedDangerHost
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : HostTicketConfig n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectHostTicket C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectHostTicket
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableHostProtected
    (ring : DirectedRing n)
    (C : HostTicketConfig n psi kappa tau) (e : Fin n) :
    Decidable (HostProtectedSpliceEdge ring C e) := by
  unfold HostProtectedSpliceEdge R1ProtectedSpliceEdgeV3
    HostFenceShape ReservedFrontHoldGuard projectHostTicket
  dsimp only
  infer_instance

private instance instDecidableHostTicketShape
    (u : HostTicketAgent psi kappa tau) : Decidable (HostTicketShape u) := by
  unfold HostTicketShape
  infer_instance

private instance instDecidableHostProvenanceSafe
    (ring : DirectedRing n) (C : HostTicketConfig n psi kappa tau) :
    Decidable (HostProvenanceSafe ring C) := by
  unfold HostProvenanceSafe
  infer_instance

private instance instDecidableHostSpliceSafe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : HostTicketConfig n psi kappa tau) :
    Decidable (HostSpliceSafe hpsi ring C) := by
  unfold HostSpliceSafe
  infer_instance

private instance instDecidableHostAmendedPPrimeAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : HostTicketConfig n psi kappa tau) (e : Fin n) :
    Decidable (HostAmendedPPrimeAt hpsi ring C e) := by
  unfold HostAmendedPPrimeAt
  dsimp only
  unfold PPrimeBarrierBirthGuard HostProtectedSpliceEdge
    R1ProtectedSpliceEdgeV3 HostFenceShape ReservedFrontHoldGuard
    projectHostTicket
  dsimp only
  unfold isBarrier
  infer_instance

/-! ## Same-row arm and the two fence services -/

/-- Exact observable for the only unguarded ordinary-host creator: the final
right endpoint is still controller-neutral and a follower, but its label changed. -/
def rightFollowerRelabelled
    (old out : R1AgentStateV4 psi kappa tau) : Bool :=
  decide
    (role out = .none ∧
      out.repairPending = false ∧
      out.splice.base.core.core.leader = false ∧
      out.splice.base.core.core.label ≠ old.splice.base.core.core.label)

/-- Old V6 ordinary fallback, restated locally: run the physical host and clear
both ticket bits. -/
def ordinaryHostWriteOld
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : HostTicketAgent psi kappa tau) :
    HostTicketAgent psi kappa tau × HostTicketAgent psi kappa tau :=
  let q := ordinaryRow hpsi hwidth hle l.carrier r.carrier
  (⟨q.1, false⟩, ⟨q.2, false⟩)

/-- Chosen repair: keep the exact old physical output, but arm the existing
bit on the relabelled follower before its outgoing edge can run. -/
def ordinaryHostWriteArmed
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : HostTicketAgent psi kappa tau) :
    HostTicketAgent psi kappa tau × HostTicketAgent psi kappa tau :=
  let q := ordinaryRow hpsi hwidth hle l.carrier r.carrier
  let l' : HostTicketAgent psi kappa tau := ⟨q.1, false⟩
  let r' : HostTicketAgent psi kappa tau := ⟨q.2, false⟩
  if rightFollowerRelabelled r.carrier q.2 then
    (l', setHostTicket r' true)
  else
    (l', r')

/-- The same-row arm is proof/controller-only: its carrier erases to the exact
old physical host row. -/
theorem ordinaryHostWriteArmed_physical
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : HostTicketAgent psi kappa tau) :
    let q := ordinaryHostWriteArmed hpsi hwidth hle l r
    (q.1.carrier.splice.base, q.2.carrier.splice.base) =
      BirthShortDoneTerminalHost.row hpsi hwidth hle
        l.carrier.splice.base r.carrier.splice.base := by
  unfold ordinaryHostWriteArmed rightFollowerRelabelled ordinaryRow
  dsimp only
  split <;> rfl

/-- A fence can be moved into this endpoint without overwriting splice control. -/
def HostFenceTargetClear
    (u : HostTicketAgent psi kappa tau) : Prop :=
  role u.carrier = .none ∧ u.carrier.repairPending = false

private instance instDecidableHostFenceTargetClear
    (u : HostTicketAgent psi kappa tau) :
    Decidable (HostFenceTargetClear u) := by
  unfold HostFenceTargetClear
  infer_instance

/-- Priority override to be placed above ARM-A and every existing V6 rule.

* left fence + no barrier: STOP, clearing only the fence bit;
* left fence + barrier + controller-clear target: repair the target and move
  the fence right in the same interaction;
* left fence + busy target: HOLD;
* right fence: HOLD the incoming interaction;
* no fence: return `none`, meaning delegate to the unchanged V6 table. -/
def hostFenceOverride
    (hpsi : 0 < psi)
    (l r : HostTicketAgent psi kappa tau) :
    Option (HostTicketAgent psi kappa tau × HostTicketAgent psi kappa tau) :=
  if HostFenceShape l then
    if LocalPreparedBarrier hpsi l.carrier r.carrier then
      if HostFenceTargetClear r then
        some
          (setHostTicket l false,
            setHostTicket
              (withHostCarrier r
                (repairResponder hpsi l.carrier r.carrier)) true)
      else
        some (l, r)
    else
      some (setHostTicket l false, r)
  else if HostFenceShape r then
    some (l, r)
  else
    none

/-- Closed helper used only by the finite recheck below.  In the real V6 table,
`none` delegates to the unchanged old row rather than framing. -/
def hostFenceServiceWrite
    (hpsi : 0 < psi)
    (l r : HostTicketAgent psi kappa tau) :
    HostTicketAgent psi kappa tau × HostTicketAgent psi kappa tau :=
  match hostFenceOverride hpsi l r with
  | some q => q
  | none => (l, r)

/-- Generic two-site ring update used by the closed fixtures. -/
def stepWith
    (f : HostTicketAgent psi kappa tau ->
      HostTicketAgent psi kappa tau ->
        HostTicketAgent psi kappa tau × HostTicketAgent psi kappa tau)
    (ring : DirectedRing n) (C : HostTicketConfig n psi kappa tau)
    (e : Fin n) : HostTicketConfig n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := f (C e) (C j)
    fun i =>
      if i = e then q.1
      else if i = j then q.2
      else C i

/-- No local state is added relative to V6: V4's factor 8 times the one existing
Boolean ticket is still 16. -/
def controllerStateFactorHostFence : Nat :=
  2 * controllerStateFactorV4

theorem controllerStateFactorHostFence_eq :
    controllerStateFactorHostFence = 16 := by
  unfold controllerStateFactorHostFence
  rw [controllerStateFactorV4_eq]

/-! ## A hot barrier: why a countdown is not the right invariant -/

private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩

/-- Label-1 rotation of the repository's positive P-prime witness. -/
def hotRaw (probe : Bool) : AgentState 2 :=
  { BirthShortDoneTerminalPositiveWitness.raw probe with label := (1 : Fin 2) }

private theorem hotRaw_domain (probe : Bool) :
    (hotRaw probe).inProtocolDomain 1 := by
  simp [hotRaw, BirthShortDoneTerminalPositiveWitness.raw,
    AgentState.inProtocolDomain]

def hotEndpoint (probe : Bool) : ExpiringAgentState 2 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain (hotRaw probe) (hotRaw_domain probe), false⟩, 0⟩

/-- Controller-neutral V4 carrier used by both closed tests. -/
def neutralCarrier
    (b : ExpiringAgentState 2 1 1) : R1AgentStateV4 2 1 1 :=
  { splice := { base := b, spliceRole := .none }
    repairPending := false }

def neutralHost
    (b : ExpiringAgentState 2 1 1) : HostTicketAgent 2 1 1 :=
  liftHostTicket (neutralCarrier b)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- A physically hot barrier can birth on its very next service. -/
theorem hot_barrier_births_next_service :
    BirthShortDoneTerminalObserver.birthEvent
      hTwo hTwo hTwoLe (hotEndpoint false) (hotEndpoint true) = true := by
  decide

/-- The same physical hot pair is blocked by the neutral ticket when interpreted
as a host fence. -/
def hotFenceConfig : HostTicketConfig 2 2 1 1 := fun i =>
  if i = 0 then
    setHostTicket (neutralHost (hotEndpoint false)) true
  else
    neutralHost (hotEndpoint true)

theorem hot_source_blocked_by_host_fence :
    HostFenceShape (hotFenceConfig (0 : Fin 2)) ∧
      ¬ HostAmendedPPrimeAt hTwo ring2 hotFenceConfig (0 : Fin 2) := by
  decide

/-! ## Exact finite recheck -/

/-- Physical carrier of the rebirth hole, with all old controller fields and the
existing ticket initially neutral. -/
def q11703Start : HostTicketConfig 3 2 1 1 := fun i =>
  neutralHost (Q11541PPrimeReachability.strongStart i)

/-- Old unarmed ordinary fallback: this is the rebirth hole. -/
def q11703OldAfter : HostTicketConfig 3 2 1 1 :=
  stepWith (ordinaryHostWriteOld hTwo hTwo hTwoLe)
    ring3 q11703Start (0 : Fin 3)

/-- Chosen repair: exact same physical row, plus the same-row neutral ticket. -/
def q11703ArmedAfter : HostTicketConfig 3 2 1 1 :=
  stepWith (ordinaryHostWriteArmed hTwo hTwo hTwoLe)
    ring3 q11703Start (0 : Fin 3)

/-- First fence service repairs `1 -> 2` and moves the fence to site 2. -/
def q11703Fence1 : HostTicketConfig 3 2 1 1 :=
  stepWith (hostFenceServiceWrite hTwo)
    ring3 q11703ArmedAfter (1 : Fin 3)

/-- Second fence service sees the surviving leader at 0 and stops. -/
def q11703Fence2 : HostTicketConfig 3 2 1 1 :=
  stepWith (hostFenceServiceWrite hTwo)
    ring3 q11703Fence1 (2 : Fin 3)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Reproduce the exact unarmed defect without importing the changing V6 file. -/
theorem q11703_old_hole_by_decide :
    HostSpliceSafe hTwo ring3 q11703Start ∧
      PreparedDangerAt hTwo ring3
        (projectHostTicket q11703OldAfter) (1 : Fin 3) ∧
      ¬ R1ProtectedSpliceEdgeV3 ring3
        (projectHostTicket q11703OldAfter) (1 : Fin 3) ∧
      ¬ HostProtectedSpliceEdge ring3 q11703OldAfter (1 : Fin 3) ∧
      ¬ HostSpliceSafe hTwo ring3 q11703OldAfter := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Same physical/V4 carrier as the bad row, but now the created barrier is
owned immediately by the already-present ticket bit. -/
theorem q11703_same_row_arm_closes_hole_by_decide :
    (forall i,
      (q11703ArmedAfter i).carrier = (q11703OldAfter i).carrier) ∧
      HostFenceShape (q11703ArmedAfter (1 : Fin 3)) ∧
      PreparedDangerAt hTwo ring3
        (projectHostTicket q11703ArmedAfter) (1 : Fin 3) ∧
      HostProtectedSpliceEdge ring3 q11703ArmedAfter (1 : Fin 3) ∧
      HostSpliceSafe hTwo ring3 q11703ArmedAfter := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The fence moves once, then drains at the surviving leader.  Neither fence
service creates another leader, so the rebirth hole is closed on the
literal finite witness. -/
theorem q11703_fence_moves_then_drains_by_decide :
    (q11703Fence1 (1 : Fin 3)).acquireTicket = false ∧
      HostFenceShape (q11703Fence1 (2 : Fin 3)) ∧
      ¬ PreparedDangerAt hTwo ring3
        (projectHostTicket q11703Fence1) (1 : Fin 3) ∧
      HostSpliceSafe hTwo ring3 q11703Fence1 ∧
      (forall i, (q11703Fence2 i).acquireTicket = false) ∧
      HostSpliceSafe hTwo ring3 q11703Fence2 ∧
      (q11703Fence1 (0 : Fin 3)).carrier.splice.base.core.core.leader = true ∧
      (q11703Fence1 (1 : Fin 3)).carrier.splice.base.core.core.leader = false ∧
      (q11703Fence1 (2 : Fin 3)).carrier.splice.base.core.core.leader = false ∧
      (q11703Fence2 (0 : Fin 3)).carrier.splice.base.core.core.leader = true ∧
      (q11703Fence2 (1 : Fin 3)).carrier.splice.base.core.core.leader = false ∧
      (q11703Fence2 (2 : Fin 3)).carrier.splice.base.core.core.leader = false := by
  decide

end B9HostBarrierHole

#print axioms B9HostBarrierHole.ordinaryHostWriteArmed_physical
#print axioms B9HostBarrierHole.controllerStateFactorHostFence_eq
#print axioms B9HostBarrierHole.hot_barrier_births_next_service
#print axioms B9HostBarrierHole.hot_source_blocked_by_host_fence
#print axioms B9HostBarrierHole.q11703_old_hole_by_decide
#print axioms B9HostBarrierHole.q11703_same_row_arm_closes_hole_by_decide
#print axioms B9HostBarrierHole.q11703_fence_moves_then_drains_by_decide

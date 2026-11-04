import Leader.Wu.Splice.ProvenanceTicketTable
import Leader.Wu.Splice.HostBarrierHole

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceControllerR1TableV7

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerV3Safety
open B9SpliceControllerR1TableV4
open B9SpliceControllerV4Safety
open B9SpliceControllerR1TableV6

variable {n psi width kappa tau : Nat}

/-! ## 1. V7 safety vocabulary on the unchanged V6 carrier -/

/-- The repurposed V6 bit is a host fence exactly on a controller-neutral site. -/
def HostFenceShapeV7
    (u : R1AgentStateV6 psi kappa tau) : Prop :=
  role u.carrier = .none /\
    u.carrier.repairPending = false /\
    u.acquireTicket = true

/-- A true bit is either the V6 acquisition ticket or the new neutral host fence. -/
def TicketShapeV7
    (u : R1AgentStateV6 psi kappa tau) : Prop :=
  u.acquireTicket = true ->
    ReservedFrontHoldGuard u.carrier \/ HostFenceShapeV7 u

/-- The pending-predecessor backing clause is unchanged from V6. -/
def ProvenanceSafeV7
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Prop :=
  (forall i, TicketShapeV7 (C i)) /\
    (forall i,
      role (C i).carrier = .predecessorArmed ->
      (C i).carrier.repairPending = true ->
        ReservedFrontHoldGuard (C (ring.rightNeighbor i)).carrier /\
        (C (ring.rightNeighbor i)).acquireTicket = false)

/-- A danger is owned either by the V3 splice certificate or by a host fence
on its left endpoint. -/
def ProtectedSpliceEdgeV7
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) : Prop :=
  R1ProtectedSpliceEdgeV3 ring (projectV6 C) e \/
    HostFenceShapeV7 (C e)

/-- V7 safety: geometric ownership plus the broadened ticket-shape discipline. -/
def SpliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Prop :=
  (forall e,
      PreparedDangerAt hpsi ring (projectV6 C) e ->
        ProtectedSpliceEdgeV7 ring C e) /\
    ProvenanceSafeV7 ring C

/-! ## 2. Closed decidability used by the executable table and census -/

private instance instDecidableHostFenceShapeV7
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceShapeV7 u) := by
  unfold HostFenceShapeV7
  infer_instance

private instance instDecidableTicketShapeV7
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance

private instance instDecidablePreparedDangerV7
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableProtectedSpliceEdgeV7
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance

private instance instDecidableProvenanceSafeV7
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance

private instance instDecidableSpliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance

private instance instDecidableReservedFrontV7
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (ReservedFrontHoldGuard u.carrier) := by
  unfold ReservedFrontHoldGuard
  infer_instance

private instance instDecidableLocalPreparedBarrierV7
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (LocalPreparedBarrier hpsi l.carrier r.carrier) := by
  unfold LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableArmAV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (ArmAGuard hpsi hwidth hle l.carrier r.carrier) := by
  unfold ArmAGuard LeftDeletionCandidate
  infer_instance

private instance instDecidableArmBV7
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (ArmBGuard l.carrier r.carrier) := by
  unfold ArmBGuard
  infer_instance

private instance instDecidableDeleteV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (DeleteGuard hpsi hwidth hle l.carrier r.carrier) := by
  unfold DeleteGuard LeftDeletionCandidate
  infer_instance

private instance instDecidablePendingHoldV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (PendingHoldGuard hpsi hwidth hle l.carrier r.carrier) := by
  unfold PendingHoldGuard LeftDeletionCandidate
  infer_instance

private instance instDecidablePendingAbortV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (PendingAbortGuard hpsi hwidth hle l.carrier r.carrier) := by
  unfold PendingAbortGuard LeftDeletionCandidate
  infer_instance

private instance instDecidableMoveCommitV7
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveCommitGuard l.carrier r.carrier) := by
  unfold MoveCommitGuard
  infer_instance

private instance instDecidableMoveStopV7
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveStopGuardV3 hpsi l.carrier r.carrier) := by
  unfold MoveStopGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableMoveSeekV7
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveSeekGuardV3 hpsi l.carrier r.carrier) := by
  unfold MoveSeekGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableMoveSeekHoldV7
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveSeekHoldGuardV3 l.carrier r.carrier) := by
  unfold MoveSeekHoldGuardV3
  infer_instance

private instance instDecidablePendingOwnerAbortV7
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (PendingOwnerAbortGuardV3 l.carrier r.carrier) := by
  unfold PendingOwnerAbortGuardV3
  infer_instance

private instance instDecidableMoveAcquireFrontV7
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveAcquireFrontGuardV6 hpsi l r) := by
  unfold MoveAcquireFrontGuardV6 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableMoveAcquireLegacyV7
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveAcquireLegacyGuardV6 l r) := by
  unfold MoveAcquireLegacyGuardV6 MoveAcquireGuardV3 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableMoveAcquireAbortV7
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MoveAcquireAbortGuardV3 l.carrier r.carrier) := by
  unfold MoveAcquireAbortGuardV3 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableOrphanReservedFrontV7
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (OrphanReservedFrontGuardV3 l.carrier r.carrier) := by
  unfold OrphanReservedFrontGuardV3 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableVictimRightScrubV7
    (r : R1AgentStateV6 psi kappa tau) :
    Decidable (VictimRightScrubGuardV6 r) := by
  unfold VictimRightScrubGuardV6
  infer_instance

private instance instDecidableVictimLeftScrubV7
    (l : R1AgentStateV6 psi kappa tau) :
    Decidable (VictimLeftScrubGuardV6 l) := by
  unfold VictimLeftScrubGuardV6
  infer_instance

private instance instDecidableFrontRightScrubV7
    (r : R1AgentStateV6 psi kappa tau) :
    Decidable (FrontRightScrubGuardV6 r) := by
  unfold FrontRightScrubGuardV6
  infer_instance

private instance instDecidableMalformedLeftPendingV7
    (l : R1AgentStateV6 psi kappa tau) :
    Decidable (MalformedLeftPendingGuardV6 l) := by
  unfold MalformedLeftPendingGuardV6
  infer_instance

private instance instDecidableMalformedRightPendingV7
    (r : R1AgentStateV6 psi kappa tau) :
    Decidable (MalformedRightPendingGuardV6 r) := by
  unfold MalformedRightPendingGuardV6
  infer_instance

private instance instDecidableMarkedHoldV7
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (MarkedHoldGuardV6 l r) := by
  unfold MarkedHoldGuardV6
  infer_instance

/-! ## 3. Four host-fence rows and armed ordinary fallback -/

/-- A fence may move into a responder only while the old controller is neutral. -/
def HostFenceTargetClearV7
    (u : R1AgentStateV6 psi kappa tau) : Prop :=
  role u.carrier = .none /\ u.carrier.repairPending = false

private instance instDecidableHostFenceTargetClearV7
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceTargetClearV7 u) := by
  unfold HostFenceTargetClearV7
  infer_instance

/-- STOP: current fence has no local barrier, so consume it. -/
def hostFenceLeftStopWriteV7
    (l r : R1AgentStateV6 psi kappa tau) :=
  (clearTicketV6 l, r)

/-- ADVANCE: repair the current barrier and move the fence to the responder. -/
def hostFenceLeftAdvanceWriteV7
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :=
  (clearTicketV6 l,
    setTicketV6
      (withCarrierClearTicketV6 r
        (repairResponder hpsi l.carrier r.carrier)) true)

/-- Busy target: frame both endpoints. -/
def hostFenceLeftHoldWriteV7
    (l r : R1AgentStateV6 psi kappa tau) := (l, r)

/-- A right-hand fence is never consumed by an incoming interaction. -/
def hostFenceRightHoldWriteV7
    (l r : R1AgentStateV6 psi kappa tau) := (l, r)

/-- Exact observable. -/
def rightFollowerRelabelledV7
    (old out : R1AgentStateV4 psi kappa tau) : Bool :=
  decide
    (role out = .none /\
      out.repairPending = false /\
      out.splice.base.core.core.leader = false /\
      out.splice.base.core.core.label ≠ old.splice.base.core.core.label)

/-- Same physical ordinary row as V6.  Both old tickets are cleared, and a
neutral right follower whose label changed is fenced in the same service. -/
def ordinaryHostWriteV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := ordinaryRow hpsi hwidth hle l.carrier r.carrier
  let l' := withCarrierClearTicketV6 l q.1
  let r' := withCarrierClearTicketV6 r q.2
  if rightFollowerRelabelledV7 r.carrier q.2 then
    (l', setTicketV6 r' true)
  else
    (l', r')

/-- V7 is V6 with the four fence cases strictly above every old V6 row, and
with only the final ordinary fallback changed to same-row arming. -/
def rowV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if HostFenceShapeV7 l then
    if LocalPreparedBarrier hpsi l.carrier r.carrier then
      if HostFenceTargetClearV7 r then
        hostFenceLeftAdvanceWriteV7 hpsi l r
      else
        hostFenceLeftHoldWriteV7 l r
    else
      hostFenceLeftStopWriteV7 l r
  else if HostFenceShapeV7 r then
    hostFenceRightHoldWriteV7 l r
  else if MoveAcquireFrontGuardV6 hpsi l r then
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
    ordinaryHostWriteV7 hpsi hwidth hle l r

/-- Ring lift; singleton behavior remains fail-closed. -/
def stepV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) : R1ConfigV6 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV7 hpsi hwidth hle (C e) (C j)
    fun i =>
      if i = e then q.1
      else if i = j then q.2
      else C i

/-- No state is added: V7 still has factor 16. -/
def controllerStateFactorV7 : Nat := controllerStateFactorV6

theorem controllerStateFactorV7_eq : controllerStateFactorV7 = 16 := by
  simpa [controllerStateFactorV7] using controllerStateFactorV6_eq

/-! ## 4. Structural helpers for the four generic fence proofs -/

private theorem rightNeighbor_injectiveV7
    (ring : DirectedRing n) : Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega

private theorem normalizeDeletion_labelV7
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl

private theorem prepareDisposal_labelV7
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.label = u.core.label := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

private theorem prepared_splice_labelV7
    (hpsi : 0 < psi) (u : SpliceAgentState psi kappa tau) :
    (prepared hpsi u).core.label = u.base.core.core.label := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.base.core]
  rw [normalizeDeletion_labelV7, prepareDisposal_labelV7]
  rfl

private theorem preparedR1_labelV7
    (hpsi : 0 < psi) (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.label = u.splice.base.core.core.label := by
  unfold preparedR1
  exact prepared_splice_labelV7 hpsi u.splice

private theorem repairResponder_no_localPreparedBarrierV7
    (hpsi : 0 < psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    ¬ LocalPreparedBarrier hpsi l (repairResponder hpsi l r) := by
  intro h
  unfold LocalPreparedBarrier at h
  dsimp only at h
  unfold isBarrier at h
  apply h.2
  apply Fin.ext
  simp [preparedR1_labelV7, repairResponder]

private theorem localPreparedBarrier_of_dangerV7
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (h : PreparedDangerAt hpsi ring (projectV6 C) e) :
    LocalPreparedBarrier hpsi
      (C e).carrier (C (ring.rightNeighbor e)).carrier := by
  simpa [PreparedBarrierAt, LocalPreparedBarrier,
    projectSpliceConfig, projectV6, preparedR1] using h.2

private theorem danger_congr_carrier_atV7
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hL : (D e).carrier = (C e).carrier)
    (hR : (D (ring.rightNeighbor e)).carrier =
      (C (ring.rightNeighbor e)).carrier) :
    PreparedDangerAt hpsi ring (projectV6 D) e <->
      PreparedDangerAt hpsi ring (projectV6 C) e := by
  unfold PreparedDangerAt PreparedBarrierAt projectSpliceConfig projectV6
  dsimp only
  rw [hL, hR]

private theorem protected_congr_carrier_atV7
    (ring : DirectedRing n)
    (C D : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hL : (D e).carrier = (C e).carrier)
    (hR : (D (ring.rightNeighbor e)).carrier =
      (C (ring.rightNeighbor e)).carrier) :
    R1ProtectedSpliceEdgeV3 ring (projectV6 D) e <->
      R1ProtectedSpliceEdgeV3 ring (projectV6 C) e := by
  unfold R1ProtectedSpliceEdgeV3 projectV6
  dsimp only
  rw [hL, hR]

private theorem stepV7_other
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e i : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    stepV7 hpsi hwidth hle ring C e i = C i := by
  simp [stepV7, hne, hi, hj]

private theorem stepV7_eq_self_of_row_self
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n)
    (hrow : rowV7 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))) :
    stepV7 hpsi hwidth hle ring C e = C := by
  funext i
  by_cases hself : ring.rightNeighbor e = e
  · simp [stepV7, hself]
  · by_cases hi : i = e
    · subst i
      simp [stepV7, hself, hrow]
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simp [stepV7, hself, hrow]
      · simp [stepV7, hself, hrow, hi, hj]

/-! ## 5. The four new rows preserve SpliceSafeV7 on every ring -/

theorem hostFenceLeftStop_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hf : HostFenceShapeV7 (C e))
    (hbar : ¬ LocalPreparedBarrier hpsi
      (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7 hpsi ring
      (stepV7 hpsi hwidth hle ring C e) := by
  by_cases hself : ring.rightNeighbor e = e
  · simpa [stepV7, hself] using hsafe
  · let D := stepV7 hpsi hwidth hle ring C e
    change SpliceSafeV7 hpsi ring D
    have hne : ring.rightNeighbor e ≠ e := hself
    have hE : D e = clearTicketV6 (C e) := by
      dsimp [D]
      simp [stepV7, hne, rowV7, hf, hbar,
        hostFenceLeftStopWriteV7]
    have hOther : forall i, i ≠ e -> D i = C i := by
      intro i hi
      by_cases hj : i = ring.rightNeighbor e
      · subst i
        dsimp [D]
        simp [stepV7, hne, rowV7, hf, hbar,
          hostFenceLeftStopWriteV7]
      · exact stepV7_other hpsi hwidth hle ring C e i hne hi hj
    have hcarrier : forall i, (D i).carrier = (C i).carrier := by
      intro i
      by_cases hi : i = e
      · subst i
        rw [hE]
        rfl
      · rw [hOther i hi]
    constructor
    · intro x hd
      have hd0 :=
        (danger_congr_carrier_atV7 hpsi ring C D x
          (hcarrier x) (hcarrier (ring.rightNeighbor x))).1 hd
      rcases hsafe.1 x hd0 with hv3 | hfx
      · exact Or.inl
          ((protected_congr_carrier_atV7 ring C D x
            (hcarrier x) (hcarrier (ring.rightNeighbor x))).2 hv3)
      · by_cases hxe : x = e
        · subst x
          exact (hbar
            (localPreparedBarrier_of_dangerV7 hpsi ring C e hd0)).elim
        · exact Or.inr (by
            rw [hOther x hxe]
            exact hfx)
    · constructor
      · intro i
        by_cases hi : i = e
        · subst i
          rw [hE]
          intro ht
          exfalso
          simpa [clearTicketV6, setTicketV6] using ht
        · rw [hOther i hi]
          exact hsafe.2.1 i
      · intro i hr hp
        have hci := hcarrier i
        have hr0 : role (C i).carrier = .predecessorArmed := by
          rw [← hci]
          exact hr
        have hp0 : (C i).carrier.repairPending = true := by
          rw [← hci]
          exact hp
        have hb := hsafe.2.2 i hr0 hp0
        constructor
        · have hc := hcarrier (ring.rightNeighbor i)
          rw [hc]
          exact hb.1
        · by_cases hre : ring.rightNeighbor i = e
          · rw [hre, hE]
            rfl
          · rw [hOther (ring.rightNeighbor i) hre]
            exact hb.2

theorem hostFenceLeftAdvance_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hf : HostFenceShapeV7 (C e))
    (hbar : LocalPreparedBarrier hpsi
      (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (htarget : HostFenceTargetClearV7 (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring
      (stepV7 hpsi hwidth hle ring C e) := by
  by_cases hself : ring.rightNeighbor e = e
  · simpa [stepV7, hself] using hsafe
  · let D := stepV7 hpsi hwidth hle ring C e
    change SpliceSafeV7 hpsi ring D
    have hne : ring.rightNeighbor e ≠ e := hself
    have hE : D e = clearTicketV6 (C e) := by
      dsimp [D]
      simp [stepV7, hne, rowV7, hf, hbar, htarget,
        hostFenceLeftAdvanceWriteV7]
    have hJ : D (ring.rightNeighbor e) =
        setTicketV6
          (withCarrierClearTicketV6 (C (ring.rightNeighbor e))
            (repairResponder hpsi
              (C e).carrier (C (ring.rightNeighbor e)).carrier)) true := by
      dsimp [D]
      simp [stepV7, hne, rowV7, hf, hbar, htarget,
        hostFenceLeftAdvanceWriteV7]
    have hOther : forall i,
        i ≠ e -> i ≠ ring.rightNeighbor e -> D i = C i := by
      intro i hi hj
      exact stepV7_other hpsi hwidth hle ring C e i hne hi hj
    have hcarrierNeJ : forall i,
        i ≠ ring.rightNeighbor e -> (D i).carrier = (C i).carrier := by
      intro i hij
      by_cases hie : i = e
      · subst i
        rw [hE]
        rfl
      · rw [hOther i hie hij]
    have hFJ : HostFenceShapeV7 (D (ring.rightNeighbor e)) := by
      rw [hJ]
      constructor
      · change role
          (repairResponder hpsi
            (C e).carrier (C (ring.rightNeighbor e)).carrier) = .none
        simpa [repairResponder, role] using htarget.1
      · constructor
        · change
            (repairResponder hpsi
              (C e).carrier
              (C (ring.rightNeighbor e)).carrier).repairPending = false
          simpa [repairResponder] using htarget.2
        · rfl
    constructor
    · intro x hd
      by_cases hxe : x = e
      · subst x
        have hlb := localPreparedBarrier_of_dangerV7 hpsi ring D e hd
        rw [hE, hJ] at hlb
        change LocalPreparedBarrier hpsi
          (C e).carrier
          (repairResponder hpsi
            (C e).carrier (C (ring.rightNeighbor e)).carrier) at hlb
        exact (repairResponder_no_localPreparedBarrierV7 hpsi
          (C e).carrier (C (ring.rightNeighbor e)).carrier hlb).elim
      · by_cases hxj : x = ring.rightNeighbor e
        · subst x
          exact Or.inr hFJ
        · have hrxj : ring.rightNeighbor x ≠ ring.rightNeighbor e := by
            intro h
            exact hxe (rightNeighbor_injectiveV7 ring h)
          have hL := hcarrierNeJ x hxj
          have hR := hcarrierNeJ (ring.rightNeighbor x) hrxj
          have hd0 :=
            (danger_congr_carrier_atV7 hpsi ring C D x hL hR).1 hd
          rcases hsafe.1 x hd0 with hv3 | hfx
          · exact Or.inl
              ((protected_congr_carrier_atV7 ring C D x hL hR).2 hv3)
          · exact Or.inr (by
              rw [hOther x hxe hxj]
              exact hfx)
    · constructor
      · intro i
        by_cases hie : i = e
        · subst i
          rw [hE]
          intro ht
          exfalso
          simpa [clearTicketV6, setTicketV6] using ht
        · by_cases hij : i = ring.rightNeighbor e
          · subst i
            intro _
            exact Or.inr hFJ
          · rw [hOther i hie hij]
            exact hsafe.2.1 i
      · intro i hr hp
        by_cases hie : i = e
        · subst i
          rw [hE] at hr
          change role (C e).carrier = .predecessorArmed at hr
          have hbad : SpliceRole.none = SpliceRole.predecessorArmed :=
            hf.1.symm.trans hr
          cases hbad
        · by_cases hij : i = ring.rightNeighbor e
          · subst i
            rw [hJ] at hr
            have hr0 :
                role (C (ring.rightNeighbor e)).carrier = .predecessorArmed := by
              simpa [setTicketV6, withCarrierClearTicketV6,
                repairResponder, role] using hr
            have hbad : SpliceRole.none = SpliceRole.predecessorArmed :=
              htarget.1.symm.trans hr0
            cases hbad
          · have hDi := hOther i hie hij
            have hr0 : role (C i).carrier = .predecessorArmed := by
              rw [← hDi]
              exact hr
            have hp0 : (C i).carrier.repairPending = true := by
              rw [← hDi]
              exact hp
            have hb := hsafe.2.2 i hr0 hp0
            have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
              intro h
              exact hie (rightNeighbor_injectiveV7 ring h)
            have hre : ring.rightNeighbor i ≠ e := by
              intro h
              have hres := hb.1
              rw [h] at hres
              unfold ReservedFrontHoldGuard at hres
              have hbad : SpliceRole.none = SpliceRole.front :=
                hf.1.symm.trans hres.1
              cases hbad
            have hDr := hOther (ring.rightNeighbor i) hre hrj
            rw [hDr]
            exact hb

/-- HOST-FENCE-LEFT / HOLD is a literal stutter. -/
theorem hostFenceLeftHold_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hf : HostFenceShapeV7 (C e))
    (hbar : LocalPreparedBarrier hpsi
      (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (hbusy : ¬ HostFenceTargetClearV7 (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring
      (stepV7 hpsi hwidth hle ring C e) := by
  have hrow : rowV7 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e)) := by
    simp [rowV7, hf, hbar, hbusy, hostFenceLeftHoldWriteV7]
  rw [stepV7_eq_self_of_row_self hpsi hwidth hle ring C e hrow]
  exact hsafe

/-- HOST-FENCE-RIGHT-HOLD is also a literal stutter. -/
theorem hostFenceRightHold_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hleft : ¬ HostFenceShapeV7 (C e))
    (hright : HostFenceShapeV7 (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring
      (stepV7 hpsi hwidth hle ring C e) := by
  have hrow : rowV7 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e)) := by
    simp [rowV7, hleft, hright, hostFenceRightHoldWriteV7]
  rw [stepV7_eq_self_of_row_self hpsi hwidth hle ring C e hrow]
  exact hsafe

/-! ## 6. Closed V7 replay helpers -/

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

def serveV7 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV6 n 2 0 0) (e : Fin n) : R1ConfigV6 n 2 0 0 :=
  stepV7 hTwo hTwo hTwoLe ring C e

def runV7 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV6 n 2 0 0)
    (word : List (Fin n)) : R1ConfigV6 n 2 0 0 :=
  List.foldl (fun D e => serveV7 ring D e) C word

def safeAlongV7 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV6 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (SpliceSafeV7 hTwo ring C)
  | C, e :: es =>
      decide (SpliceSafeV7 hTwo ring C) &&
        safeAlongV7 ring (serveV7 ring C e) es

private instance instDecidableAmendedPPrimeV7
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (R1AmendedPPrimeAtV3 hpsi ring C e) := by
  unfold R1AmendedPPrimeAtV3 PPrimeBarrierBirthGuard
  dsimp only
  unfold isBarrier R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableSourceFreeV7
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) :
    Decidable (R1SourceFreeV3 hpsi ring C) := by
  unfold R1SourceFreeV3
  infer_instance

def sourceFreeAlongV7 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV6 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (R1SourceFreeV3 hTwo ring (projectV6 C))
  | C, e :: es =>
      decide (R1SourceFreeV3 hTwo ring (projectV6 C)) &&
        sourceFreeAlongV7 ring (serveV7 ring C e) es

def LeaderlessV7
    (C : R1ConfigV6 n psi kappa tau) : Prop :=
  forall i, (C i).carrier.splice.base.core.core.leader = false

def RolesClearV7
    (C : R1ConfigV6 n psi kappa tau) : Prop :=
  forall i,
    role (C i).carrier = .none /\
    (C i).carrier.repairPending = false /\
    (C i).acquireTicket = false

private instance instDecidableLeaderlessV7
    (C : R1ConfigV6 n psi kappa tau) : Decidable (LeaderlessV7 C) := by
  unfold LeaderlessV7
  infer_instance

private instance instDecidableRolesClearV7
    (C : R1ConfigV6 n psi kappa tau) : Decidable (RolesClearV7 C) := by
  unfold RolesClearV7
  infer_instance

/-! ## 7. Literal neutral witness is repaired and the fence drains -/

def q11703StartV7 : R1ConfigV6 3 2 1 1 := fun i =>
  liftAgentV6
    (B9HostBarrierHole.neutralCarrier
      (Q11541PPrimeReachability.strongStart i))

def q11703ArmedAfterV7 : R1ConfigV6 3 2 1 1 :=
  stepV7 hTwo hTwo hTwoLe ring3 q11703StartV7 (0 : Fin 3)

def q11703Fence1V7 : R1ConfigV6 3 2 1 1 :=
  stepV7 hTwo hTwo hTwoLe ring3 q11703ArmedAfterV7 (1 : Fin 3)

def q11703Fence2V7 : R1ConfigV6 3 2 1 1 :=
  stepV7 hTwo hTwo hTwoLe ring3 q11703Fence1V7 (2 : Fin 3)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem q11703_and_fence_run_rechecked_v7 :
    SpliceSafeV7 hTwo ring3 q11703StartV7 /\
    HostFenceShapeV7 (q11703ArmedAfterV7 (1 : Fin 3)) /\
    PreparedDangerAt hTwo ring3
      (projectV6 q11703ArmedAfterV7) (1 : Fin 3) /\
    ProtectedSpliceEdgeV7 ring3 q11703ArmedAfterV7 (1 : Fin 3) /\
    SpliceSafeV7 hTwo ring3 q11703ArmedAfterV7 /\
    (q11703Fence1V7 (1 : Fin 3)).acquireTicket = false /\
    HostFenceShapeV7 (q11703Fence1V7 (2 : Fin 3)) /\
    ¬ PreparedDangerAt hTwo ring3
      (projectV6 q11703Fence1V7) (1 : Fin 3) /\
    SpliceSafeV7 hTwo ring3 q11703Fence1V7 /\
    (forall i, (q11703Fence2V7 i).acquireTicket = false) /\
    SpliceSafeV7 hTwo ring3 q11703Fence2V7 /\
    (q11703Fence2V7 (0 : Fin 3)).carrier.splice.base.core.core.leader = true /\
    (q11703Fence2V7 (1 : Fin 3)).carrier.splice.base.core.core.leader = false /\
    (q11703Fence2V7 (2 : Fin 3)).carrier.splice.base.core.core.leader = false := by
  decide

/-! ## 8. The generic ordinary-host claim is false -/

/-- Same physical start as the neutral witness, but site 1 carries the stale right-hand shape
`predecessorArmed,false`.  That shape is permitted by `SpliceSafeV7`: it is
not pending, and initially there is no danger requiring ownership. -/
def ordinaryHostStalePredStartV7 : R1ConfigV6 3 2 1 1 := fun i =>
  if i = (1 : Fin 3) then
    liftAgentV6
      (setControl
        (B9HostBarrierHole.neutralCarrier
          (Q11541PPrimeReachability.strongStart i))
        .predecessorArmed false)
  else
    liftAgentV6
      (B9HostBarrierHole.neutralCarrier
        (Q11541PPrimeReachability.strongStart i))

def ordinaryHostStalePredAfterV7 : R1ConfigV6 3 2 1 1 :=
  stepV7 hTwo hTwo hTwoLe ring3 ordinaryHostStalePredStartV7 (0 : Fin 3)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- This is the R2a blocker.  The ordinary row performs the physical
right-follower relabel, but the neutral-only arming predicate refuses to fence
site 1 because its stale role is `predecessorArmed`. -/
theorem ordinaryHost_same_row_arming_fails_v7 :
    SpliceSafeV7 hTwo ring3 ordinaryHostStalePredStartV7 /\
    rowV7 hTwo hTwo hTwoLe
      (ordinaryHostStalePredStartV7 (0 : Fin 3))
      (ordinaryHostStalePredStartV7 (1 : Fin 3)) =
      ordinaryHostWriteV7 hTwo hTwo hTwoLe
        (ordinaryHostStalePredStartV7 (0 : Fin 3))
        (ordinaryHostStalePredStartV7 (1 : Fin 3)) /\
    role (ordinaryHostStalePredAfterV7 (1 : Fin 3)).carrier =
      .predecessorArmed /\
    (ordinaryHostStalePredAfterV7 (1 : Fin 3)).carrier.repairPending = false /\
    (ordinaryHostStalePredAfterV7 (1 : Fin 3)).acquireTicket = false /\
    PreparedDangerAt hTwo ring3
      (projectV6 ordinaryHostStalePredAfterV7) (1 : Fin 3) /\
    ¬ R1ProtectedSpliceEdgeV3 ring3
      (projectV6 ordinaryHostStalePredAfterV7) (1 : Fin 3) /\
    ¬ HostFenceShapeV7 (ordinaryHostStalePredAfterV7 (1 : Fin 3)) /\
    ¬ ProtectedSpliceEdgeV7 ring3 ordinaryHostStalePredAfterV7 (1 : Fin 3) /\
    ¬ SpliceSafeV7 hTwo ring3 ordinaryHostStalePredAfterV7 := by
  decide

/-! ## 9. V6 fixture census under the V7 executable table -/

/-- Four V5 witnesses repaired by V6 remain repaired. -/
def frontAcquireBackedAfter3V7 : R1ConfigV6 3 2 0 0 :=
  serveV7 ring3 frontAcquireBackedStart3V6 (1 : Fin 3)

def pendingOwnerAbortAfter3V7 : R1ConfigV6 3 2 0 0 :=
  serveV7 ring3 pendingOwnerAbortStart3V6 (0 : Fin 3)

def moveAcquireAbortAfter2V7 : R1ConfigV6 2 3 0 0 :=
  stepV7 hThree hOne hOneThree ring2 moveAcquireAbortStart2V6 (1 : Fin 2)

def orphanReservedFrontAfter2V7 : R1ConfigV6 2 3 0 0 :=
  stepV7 hThree hOne hOneThree ring2 orphanReservedFrontStart2V6 (0 : Fin 2)

theorem four_v5_witnesses_rechecked_v7 :
    SpliceSafeV7 hTwo ring3 frontAcquireBackedStart3V6 /\
    (forall i, frontAcquireBackedAfter3V7 i = frontAcquireBackedAfter3V6 i) /\
    SpliceSafeV7 hTwo ring3 frontAcquireBackedAfter3V7 /\
    SpliceSafeV7 hTwo ring3 pendingOwnerAbortStart3V6 /\
    (forall i, pendingOwnerAbortAfter3V7 i = pendingOwnerAbortAfter3V6 i) /\
    SpliceSafeV7 hTwo ring3 pendingOwnerAbortAfter3V7 /\
    SpliceSafeV7 hThree ring2 moveAcquireAbortStart2V6 /\
    (forall i, moveAcquireAbortAfter2V7 i = moveAcquireAbortAfter2V6 i) /\
    SpliceSafeV7 hThree ring2 moveAcquireAbortAfter2V7 /\
    SpliceSafeV7 hThree ring2 orphanReservedFrontStart2V6 /\
    (forall i, orphanReservedFrontAfter2V7 i = orphanReservedFrontAfter2V6 i) /\
    SpliceSafeV7 hThree ring2 orphanReservedFrontAfter2V7 := by
  decide

/-- MOVE-STOP witness. -/
def q11668After2V7 : R1ConfigV6 2 3 0 0 :=
  stepV7 hThree hOne hOneThree ring2 q11668Start2V6 (0 : Fin 2)

theorem q11668_rechecked_v7 :
    SpliceSafeV7 hThree ring2 q11668Start2V6 /\
    (forall i, q11668After2V7 i = q11668After2V6 i) /\
    SpliceSafeV7 hThree ring2 q11668After2V7 := by
  decide

/-- Protocol-STOP witness at n = 4, psi = 3, width = 2, kappa = 3, tau = 48. -/
def protocolStopAfter4V7 : R1ConfigV6 4 3 3 48 :=
  stepV7 hThree hTwo hTwoThree ring4 protocolStopStart4V6 (0 : Fin 4)

theorem q11674_rechecked_v7 :
    Q11497FeasibilityAudit.psiChoice 4 = 3 /\
    Q11497FeasibilityAudit.widthChoice = 2 /\
    Q11497FeasibilityAudit.kappaChoice 4 = 3 /\
    Q11497FeasibilityAudit.tauChoice 4 = 48 /\
    SpliceSafeV7 hThree ring4 protocolStopStart4V6 /\
    (forall i, protocolStopAfter4V7 i = protocolStopAfter4V6 i) /\
    SpliceSafeV7 hThree ring4 protocolStopAfter4V7 := by
  decide

/-- SEEK witness. -/
def q11681After2V7 : R1ConfigV6 2 2 0 0 :=
  stepV7 hTwo hOne hOneTwo ring2 q11681Start2V6 (0 : Fin 2)

theorem q11681_rechecked_v7 :
    SpliceSafeV7 hTwo ring2 q11681Start2V6 /\
    (forall i, q11681After2V7 i = q11681After2V6 i) /\
    SpliceSafeV7 hTwo ring2 q11681After2V7 := by
  decide

/-! ### Three leaderless drains -/

private def drain3 : List (Fin 3) := [0, 1, 0]
private def drain4 : List (Fin 4) := [0, 2, 0, 2]
private def drain5 : List (Fin 5) := [0, 1, 0]

private def loop3StartV7 : R1ConfigV6 3 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.loop3Start

private def loop4StartV7 : R1ConfigV6 4 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.loop4Start

private def loop5StartV7 : R1ConfigV6 5 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.loop5Start

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem three_leaderless_drains_rechecked_v7 :
    LeaderlessV7 loop3StartV7 /\
    RolesClearV7 (runV7 ring3 loop3StartV7 drain3) /\
    LeaderlessV7 loop4StartV7 /\
    RolesClearV7 (runV7 ring4 loop4StartV7 drain4) /\
    LeaderlessV7 loop5StartV7 /\
    RolesClearV7 (runV7 ring5 loop5StartV7 drain5) := by
  decide

/-! ### Four attacks -/

private def q11592Start4V7 : R1ConfigV6 4 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.q11592Start4

private def q11592Armed4V7 : R1ConfigV6 4 2 0 0 :=
  serveV7 ring4 q11592Start4V7 (1 : Fin 4)

private def q11592Replay4V7 : R1ConfigV6 4 2 0 0 :=
  serveV7 ring4 q11592Armed4V7 (1 : Fin 4)

private def followerOldStart5V7 : R1ConfigV6 5 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.followerStart5

private def followerOldFirstV7 : R1ConfigV6 5 2 0 0 :=
  serveV7 ring5 followerOldStart5V7 (0 : Fin 5)

private def stagedStart3V7 : R1ConfigV6 3 2 0 0 :=
  liftConfigV6 B9SpliceR2AttackRerun.stagedStart3

private def stagedArmed3V7 : R1ConfigV6 3 2 0 0 :=
  serveV7 ring3 stagedStart3V7 (1 : Fin 3)

private def starvationFinal3V7 : R1ConfigV6 3 2 0 0 :=
  runV7 ring3 stagedStart3V7 B9SpliceR2AttackRerun.starvationWord3

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem four_attacks_rechecked_v7 :
    RolesClearV7 (runV7 ring3 loop3StartV7 drain3) /\
    RolesClearV7 (runV7 ring4 loop4StartV7 drain4) /\
    RolesClearV7 (runV7 ring5 loop5StartV7 drain5) /\
    PendingHoldGuard hTwo hTwo hTwoLe
      (q11592Armed4V7 (1 : Fin 4)).carrier
      (q11592Armed4V7 (2 : Fin 4)).carrier /\
    (forall i, q11592Replay4V7 i = q11592Armed4V7 i) /\
    role (followerOldFirstV7 (0 : Fin 5)).carrier = .predecessorArmed /\
    role (followerOldFirstV7 (1 : Fin 5)).carrier = .none /\
    (forall i,
      serveV7 ring3 stagedArmed3V7 (2 : Fin 3) i = stagedArmed3V7 i) /\
    (forall i,
      serveV7 ring3 stagedArmed3V7 (1 : Fin 3) i = stagedArmed3V7 i) /\
    safeAlongV7 ring3 stagedStart3V7
      B9SpliceR2AttackRerun.starvationWord3 = true /\
    RolesClearV7 starvationFinal3V7 /\
    (starvationFinal3V7 (1 : Fin 3)).carrier.splice.base.core.core.leader = false /\
    (starvationFinal3V7 (2 : Fin 3)).carrier.splice.base.core.core.leader = true := by
  decide

/-! ### Authenticated follower chain -/

private def followerStart5V7 : R1ConfigV6 5 2 0 0 :=
  liftConfigV6 B9SpliceControllerR1TableV3.followerStart5V3

private def followerAfterSeekV7 : R1ConfigV6 5 2 0 0 :=
  serveV7 ring5 followerStart5V7 (0 : Fin 5)

private def followerAfterAcquireV7 : R1ConfigV6 5 2 0 0 :=
  serveV7 ring5 followerAfterSeekV7 (1 : Fin 5)

def followerAfter5V7 : R1ConfigV6 5 2 0 0 :=
  runV7 ring5 followerStart5V7
    B9SpliceControllerR1TableV3.followerWord5V3

theorem authenticated_follower_chain_rechecked_v7 :
    (forall i,
      (followerAfterSeekV7 i).carrier = (followerStart5V7 i).carrier) /\
    (followerAfterSeekV7 (1 : Fin 5)).acquireTicket = true /\
    MoveAcquireFrontGuardV6 hTwo
      (followerAfterSeekV7 (1 : Fin 5))
      (followerAfterSeekV7 (2 : Fin 5)) /\
    role (followerAfterAcquireV7 (1 : Fin 5)).carrier = .predecessorArmed /\
    (followerAfterAcquireV7 (1 : Fin 5)).carrier.repairPending = true /\
    (followerAfterAcquireV7 (1 : Fin 5)).acquireTicket = false /\
    safeAlongV7 ring5 followerStart5V7
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    sourceFreeAlongV7 ring5 followerStart5V7
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    role (followerAfter5V7 (2 : Fin 5)).carrier = .predecessorArmed /\
    (followerAfter5V7 (2 : Fin 5)).carrier.repairPending = false /\
    ReservedFrontHoldGuard (followerAfter5V7 (3 : Fin 5)).carrier /\
    (followerAfter5V7 (3 : Fin 5)).acquireTicket = false /\
    (followerAfter5V7 (2 : Fin 5)).carrier.splice.base.core.core.probe = false := by
  decide

end B9SpliceControllerR1TableV7

#print axioms B9SpliceControllerR1TableV7.controllerStateFactorV7_eq
#print axioms B9SpliceControllerR1TableV7.hostFenceLeftStop_preserves_spliceSafeV7
#print axioms B9SpliceControllerR1TableV7.hostFenceLeftAdvance_preserves_spliceSafeV7
#print axioms B9SpliceControllerR1TableV7.hostFenceLeftHold_preserves_spliceSafeV7
#print axioms B9SpliceControllerR1TableV7.hostFenceRightHold_preserves_spliceSafeV7
#print axioms B9SpliceControllerR1TableV7.q11703_and_fence_run_rechecked_v7
#print axioms B9SpliceControllerR1TableV7.ordinaryHost_same_row_arming_fails_v7
#print axioms B9SpliceControllerR1TableV7.four_v5_witnesses_rechecked_v7
#print axioms B9SpliceControllerR1TableV7.q11668_rechecked_v7
#print axioms B9SpliceControllerR1TableV7.q11674_rechecked_v7
#print axioms B9SpliceControllerR1TableV7.q11681_rechecked_v7
#print axioms B9SpliceControllerR1TableV7.three_leaderless_drains_rechecked_v7
#print axioms B9SpliceControllerR1TableV7.four_attacks_rechecked_v7
#print axioms B9SpliceControllerR1TableV7.authenticated_follower_chain_rechecked_v7

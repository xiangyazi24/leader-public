import Leader.Wu.Splice.HostRow
import Leader.Wu.Splice.HoldRepairTable


set_option autoImplicit false
set_option Elab.async false


/-!
# V10j's live splice table with an explicit physical host


Every host-evaluating guard and writer in the live chain is parameterized.
The existing carrier, controller-only writers, prepared geometry, and
reserved-front hold repair are reused unchanged.


Projection is structural and does not require B9Host.SpliceLaws.
No old-host/R1 full-row equality is used by the generic definitions or
projection theorems. The old host occurs only in regression statements.
-/


namespace B9SpliceTableHost


open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e B9SpliceV10cLiveness
open B9SpliceV10hControllerRowsSafe
open B9Host (HostRow Phys PhysConfig terminalHost r1Host hostStep)
-- Defining namespaces of the native steps used in the final specialization.
open PopulationProtocol BirthShortDoneTerminalConsumer
  BirthCheckPermitRepairLeaf BirthPhaseWait2BlockProgress


variable {n psi kappa tau width : Nat}


abbrev Cell (psi kappa tau : Nat) := R1AgentStateV6 psi kappa tau
abbrev Config (n psi kappa tau : Nat) := R1ConfigV6 n psi kappa tau


def base (u : Cell psi kappa tau) : Phys psi kappa tau :=
  u.carrier.splice.base


def erase (C : Config n psi kappa tau) : PhysConfig n psi kappa tau :=
  fun i => base (C i)


/-- The deletion detector uses the selected physical row. -/
def ldc (host : HostRow (Phys psi kappa tau))
    (l r : R1AgentState psi kappa tau) : Prop :=
  B9Host.LeftDeletionCandidate host l.splice.base r.splice.base


/-- These four guards are the original guards with only their host test changed. -/
def ArmAGuardH (host : HostRow (Phys psi kappa tau))
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .none ∧ role r = .none ∧
  l.repairPending = false ∧ r.repairPending = false ∧ ldc host l r


def DeleteGuardH (host : HostRow (Phys psi kappa tau))
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .front ∧ role r = .front ∧
  l.repairPending = false ∧ r.repairPending = false ∧ ldc host l r


def PendingHoldGuardH (host : HostRow (Phys psi kappa tau))
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .victimArmed ∧ role r = .front ∧
  l.repairPending = false ∧ r.repairPending = false ∧ ldc host l r


def PendingAbortGuardH (host : HostRow (Phys psi kappa tau))
    (l r : R1AgentState psi kappa tau) : Prop :=
  role l = .victimArmed ∧ role r = .front ∧
  l.repairPending = false ∧ r.repairPending = false ∧
  l.splice.base.core.core.leader = true ∧ ¬ ldc host l r


/-- Install the selected physical pair without changing the R1 controllers. -/
def ordinaryRowH (host : HostRow (Phys psi kappa tau))
    (l r : R1AgentState psi kappa tau) :
    R1AgentState psi kappa tau × R1AgentState psi kappa tau :=
  let q := host.row l.splice.base r.splice.base
  (setPhysical l q.1, setPhysical r q.2)


/-- The live V6 DELETE: both tickets cleared; right front is pending=true. -/
def deleteWriteH (host : HostRow (Phys psi kappa tau))
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau :=
  let q := host.row (base l) (base r)
  (withCarrierClearTicketV6 l
      (setControl (setPhysical l.carrier q.1) .predecessorArmed true),
    withCarrierClearTicketV6 r
      (setControl (setPhysical r.carrier q.2) .front true))


/-- Ordinary fallback clears old tickets, then fences a relabelled right follower. -/
def ordinaryHostWriteH (host : HostRow (Phys psi kappa tau))
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau :=
  let q := ordinaryRowH host l.carrier r.carrier
  let l' := withCarrierClearTicketV6 l q.1
  let r' := withCarrierClearTicketV6 r q.2
  if rightFollowerRelabelledV7 r.carrier q.2 then
    (l', setTicketV6 r' true)
  else (l', r')


/-- Physical hold retains old tickets, except for adding the right relabel fence. -/
def physicalHoldH (host : HostRow (Phys psi kappa tau))
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau :=
  let q := ordinaryRowH host l.carrier r.carrier
  let l' : Cell psi kappa tau := ⟨q.1, l.acquireTicket⟩
  let r' : Cell psi kappa tau := ⟨q.2, r.acquireTicket⟩
  if rightFollowerRelabelledV7 r.carrier q.2 then
    (l', setTicketV6 r' true)
  else (l', r')


/-- The complete V7 priority chain; no host-fixed fallback remains. -/
noncomputable def row7H (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact
    if HostFenceShapeV7 l then
      if LocalPreparedBarrier hpsi l.carrier r.carrier then
        if HostFenceTargetClearV7 r then hostFenceLeftAdvanceWriteV7 hpsi l r
        else hostFenceLeftHoldWriteV7 l r
      else hostFenceLeftStopWriteV7 l r
    else if HostFenceShapeV7 r then hostFenceRightHoldWriteV7 l r
    else if MoveAcquireFrontGuardV6 hpsi l r then moveAcquireFrontWriteV6 l r
    else if ArmAGuardH host l.carrier r.carrier then armAWriteV6 l r
    else if ArmBGuard l.carrier r.carrier then armBWriteV6 l r
    else if DeleteGuardH host l.carrier r.carrier then deleteWriteH host l r
    else if PendingHoldGuardH host l.carrier r.carrier then pendingHoldWriteV6 l r
    else if PendingAbortGuardH host l.carrier r.carrier then pendingAbortWriteV6 l r
    else if MoveCommitGuard l.carrier r.carrier then moveCommitWriteV6 hpsi l r
    else if MoveStopGuardV3 hpsi l.carrier r.carrier then moveStopWriteV6 l r
    else if MoveSeekGuardV3 hpsi l.carrier r.carrier then moveSeekWriteV6 l r
    else if MoveSeekHoldGuardV3 l.carrier r.carrier then moveSeekHoldWriteV6 l r
    else if PendingOwnerAbortGuardV3 l.carrier r.carrier then pendingOwnerAbortWriteV6 l r
    else if role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true then
      pendingOwnerHoldWriteV6 l r
    else if MoveAcquireLegacyGuardV6 l r then moveAcquireLegacyWriteV6 l r
    else if MoveAcquireAbortGuardV3 l.carrier r.carrier then moveAcquireAbortWriteV6 l r
    else if OrphanReservedFrontGuardV3 l.carrier r.carrier then orphanReservedFrontWriteV6 l r
    else if ReservedFrontHoldGuard l.carrier then reservedFrontHoldWriteV6 l r
    else if VictimRightScrubGuardV6 r then victimRightScrubWriteV6 l r
    else if VictimLeftScrubGuardV6 l then victimLeftScrubWriteV6 l r
    else if FrontRightScrubGuardV6 r then frontRightScrubWriteV6 l r
    else if MalformedLeftPendingGuardV6 l then malformedLeftPendingWriteV6 l r
    else if MalformedRightPendingGuardV6 r then malformedRightPendingWriteV6 l r
    else if role l.carrier = .predecessorArmed then predecessorLeftScrubWriteV6 l r
    else if role l.carrier = .front then leftFrontHoldWriteV6 l r
    else if MarkedHoldGuardV6 l r then markedHoldWriteV6 l r
    else ordinaryHostWriteH host l r


noncomputable def row8H (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact if RightStalePredecessorHoldGuardV8 l r then (l, r)
    else row7H host hpsi l r


noncomputable def row9H (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact if HostFenceBusyFrontGuardV9 hpsi l r then
    hostFenceBusyFrontRepairWriteV9 hpsi l r else row8H host hpsi l r


noncomputable def row10bH (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact if HostFenceAdvanceGuardV10b hpsi l r then
    hostFenceHandoffWriteV10b l r else row9H host hpsi l r


/-- Full-core/stall comparison is made against this host's own computed row. -/
def ZeroRefreshOnlyGuardH (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Prop :=
  let q := row10bH host hpsi l r
  q = ordinaryHostWriteH host l r ∧
  l.carrier.splice.base.stall.val = 0 ∧ r.carrier.splice.base.stall.val = 0 ∧
  SameExceptStall q.1 l ∧ SameExceptStall q.2 r


noncomputable def row10cH (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact if ZeroRefreshOnlyGuardH host hpsi l r then (l, r)
    else row10bH host hpsi l r


noncomputable def row10dgH (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact
    if OrphanReservedFrontGuardV3 l.carrier r.carrier then (l, fenceV6 r)
    else if OrphanVictimGuard l r then (l, clearControlV6 r)
    else if OwnedPendingVictimGuard l r then (fenceV6 l, fenceV6 r)
    else if OwnerlessPendingPredGuard l r then (fenceV6 l, settleV6 r)
    else row10cH host hpsi l r


noncomputable def row10gH (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact
    let q := row10dgH host hpsi l r
    if q = (l, r) then
      if role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true then (l, r)
      else if VictimRightScrubGuardV6 r then (l, clearControlV6 r)
      else if FrontRightScrubGuardV6 r then (l, clearControlV6 r)
      else if MalformedRightPendingGuardV6 r then (l, clearControlV6 r)
      else if role r.carrier = .predecessorArmed then
        if r.carrier.repairPending then
          if ReservedFrontHoldGuard l.carrier then (l, settleV6 r)
          else if LeftScrubGuardV10e l then (clearControlV6 l, r)
          else (l, r)
        else
          let q' := physicalHoldH host l r
          (q'.1, fenceV6 q'.2)
      else physicalHoldH host l r
    else q


/-- V10j's top-level deletion/hold-repair priority, with the selected host. -/
noncomputable def rowB9 (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau := by
  classical
  exact
    if ldc host l.carrier r.carrier then
      if ReservedFrontHoldGuard l.carrier then B9SpliceTableV10j.holdRepairV10j l r
      else deleteWriteH host l r
    else row10gH host hpsi l r


/-- Keep V10j's self-edge convention, not the native host's alias convention. -/
noncomputable def stepB9 (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n) :
    Config n psi kappa tau := by
  classical
  exact if ring.rightNeighbor e = e then C
    else writeAt ring C e (rowB9 host hpsi (C e) (C (ring.rightNeighbor e)))


/-- An R1-native successor; it is not an alias for the old V10j step. -/
noncomputable def stepV10kR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n) :
    Config n psi kappa tau :=
  stepB9 (r1Host hpsi h2) hpsi ring C e


-- END PART 1
/-! ## Regression: the terminal instance is exactly V10j

The explicit conditional-congruence helper permits the new classical
Decidable instances and the original tables' executable instances to differ.
It requires equality of the branches and equivalence of their guards, not
an assumption that those Decidable values are definitionally equal.
-/

private theorem ite_congr_ext {A : Type} {p q : Prop}
    [Decidable p] [Decidable q] {a b c d : A}
    (hp : p ↔ q) (ha : a = c) (hb : b = d) :
    (if p then a else b) = (if q then c else d) := by
  by_cases h : p
  · rw [if_pos h, if_pos (hp.mp h)]
    exact ha
  · have hq : ¬ q := fun hq => h (hp.mpr hq)
    rw [if_neg h, if_neg hq]
    exact hb

theorem ldc_terminal (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentState psi kappa tau) :
    ldc (terminalHost hpsi hwidth hle) l r ↔
      Q11593SpliceControllerDesign.LeftDeletionCandidate hpsi hwidth hle l.splice r.splice :=
  Iff.rfl

theorem ordinaryRowH_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentState psi kappa tau) :
    ordinaryRowH (terminalHost hpsi hwidth hle) l r =
      B9SpliceControllerR1Table.ordinaryRow hpsi hwidth hle l r := rfl

theorem deleteWriteH_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    deleteWriteH (terminalHost hpsi hwidth hle) l r =
      B9SpliceControllerR1TableV6.deleteWriteV6 hpsi hwidth hle l r := rfl

theorem ordinaryHostWriteH_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    ordinaryHostWriteH (terminalHost hpsi hwidth hle) l r =
      B9SpliceControllerR1TableV7.ordinaryHostWriteV7 hpsi hwidth hle l r := by
  classical
  unfold ordinaryHostWriteH B9SpliceControllerR1TableV7.ordinaryHostWriteV7
  dsimp only
  repeat' apply ite_congr_ext
  all_goals rfl

theorem physicalHoldH_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    physicalHoldH (terminalHost hpsi hwidth hle) l r =
      B9SpliceTableV10e.physicalHoldV6 hpsi hwidth hle l r := by
  classical
  unfold physicalHoldH B9SpliceTableV10e.physicalHoldV6
  dsimp only
  repeat' apply ite_congr_ext
  all_goals rfl

theorem row7H_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    row7H (terminalHost hpsi hwidth hle) hpsi l r =
      B9SpliceControllerR1TableV7.rowV7 hpsi hwidth hle l r := by
  classical
  unfold row7H B9SpliceControllerR1TableV7.rowV7
  repeat' first
    | exact ordinaryHostWriteH_terminal hpsi hwidth hle l r
    | exact deleteWriteH_terminal hpsi hwidth hle l r
    | exact Iff.rfl
    | rfl
    | apply ite_congr_ext

theorem row8H_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    row8H (terminalHost hpsi hwidth hle) hpsi l r =
      B9SpliceControllerR1TableV8.rowV8 hpsi hwidth hle l r := by
  classical
  unfold row8H B9SpliceControllerR1TableV8.rowV8
  exact ite_congr_ext Iff.rfl rfl (row7H_terminal hpsi hwidth hle l r)

theorem row9H_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    row9H (terminalHost hpsi hwidth hle) hpsi l r =
      B9SpliceControllerR1TableV9.rowV9 hpsi hwidth hle l r := by
  classical
  unfold row9H B9SpliceControllerR1TableV9.rowV9
  exact ite_congr_ext Iff.rfl rfl (row8H_terminal hpsi hwidth hle l r)

theorem row10bH_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    row10bH (terminalHost hpsi hwidth hle) hpsi l r =
      B9SpliceControllerR1TableV10b.rowV10b hpsi hwidth hle l r := by
  classical
  unfold row10bH B9SpliceControllerR1TableV10b.rowV10b
  exact ite_congr_ext Iff.rfl rfl (row9H_terminal hpsi hwidth hle l r)

theorem zeroRefreshH_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    ZeroRefreshOnlyGuardH (terminalHost hpsi hwidth hle) hpsi l r ↔
      B9SpliceV10cLiveness.ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r := by
  simp only [ZeroRefreshOnlyGuardH,
    B9SpliceV10cLiveness.ZeroRefreshOnlyGuardV10c,
    row10bH_terminal, ordinaryHostWriteH_terminal]

theorem row10cH_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    row10cH (terminalHost hpsi hwidth hle) hpsi l r =
      B9SpliceV10cLiveness.rowV10c hpsi hwidth hle l r := by
  classical
  unfold row10cH B9SpliceV10cLiveness.rowV10c
  exact ite_congr_ext (zeroRefreshH_terminal hpsi hwidth hle l r) rfl
    (row10bH_terminal hpsi hwidth hle l r)

theorem row10dgH_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    row10dgH (terminalHost hpsi hwidth hle) hpsi l r =
      B9SpliceTableV10g.rowV10dg hpsi hwidth hle l r := by
  classical
  unfold row10dgH B9SpliceTableV10g.rowV10dg
  repeat' first
    | exact row10cH_terminal hpsi hwidth hle l r
    | exact Iff.rfl
    | rfl
    | apply ite_congr_ext

theorem row10gH_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    row10gH (terminalHost hpsi hwidth hle) hpsi l r =
      B9SpliceTableV10g.rowV10g hpsi hwidth hle l r := by
  classical
  unfold row10gH B9SpliceTableV10g.rowV10g
  dsimp only
  simp only [row10dgH_terminal, physicalHoldH_terminal]
  all_goals
    repeat' apply ite_congr_ext
    all_goals first | exact Iff.rfl | rfl

theorem rowB9_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : Cell psi kappa tau) :
    rowB9 (terminalHost hpsi hwidth hle) hpsi l r =
      B9SpliceTableV10j.rowV10j hpsi hwidth hle l r := by
  classical
  unfold rowB9 B9SpliceTableV10j.rowV10j
  refine ite_congr_ext (ldc_terminal hpsi hwidth hle l.carrier r.carrier) ?_
    (row10gH_terminal hpsi hwidth hle l r)
  exact ite_congr_ext Iff.rfl rfl (deleteWriteH_terminal hpsi hwidth hle l r)

/-- Exact regression, with no safety, leaderlessness, or ring-size premise. -/
theorem stepB9_terminal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n) :
    stepB9 (terminalHost hpsi hwidth hle) hpsi ring C e =
      B9SpliceTableV10j.stepV10j hpsi hwidth hle ring C e := by
  classical
  unfold stepB9 B9SpliceTableV10j.stepV10j
  refine ite_congr_ext Iff.rfl rfl ?_
  exact congrArg (fun w => writeAt ring C e w)
    (rowB9_terminal hpsi hwidth hle (C e) (C (ring.rightNeighbor e)))

theorem stepB9_terminal_fun
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) :
    stepB9 (terminalHost (kappa := kappa) (tau := tau) hpsi hwidth hle) hpsi ring =
      B9SpliceTableV10j.stepV10j hpsi hwidth hle ring := by
  funext C e
  exact stepB9_terminal hpsi hwidth hle ring C e

-- END PART 2
/-! ## Structural projection: keep, selected host, or fixed relabel -/

/-- Physical effect of repairResponder: only right label/probe/phase change. -/
def relabelCell (hpsi : 0 < psi) (l r : Phys psi kappa tau) : Phys psi kappa tau :=
  { r with core := { r.core with core := { r.core.core with
      label := ⟨(l.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
      probe := false
      phase := false } } }

def relabelHost (hpsi : 0 < psi) : HostRow (Phys psi kappa tau) :=
  ⟨fun l r => (l, relabelCell hpsi l r)⟩

def relabelStep (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : PhysConfig n psi kappa tau) (e : Fin n) : PhysConfig n psi kappa tau :=
  hostStep (relabelHost hpsi) ring C e

theorem repairResponder_base_eq (hpsi : 0 < psi) (l r : Cell psi kappa tau) :
    (repairResponder hpsi l.carrier r.carrier).splice.base =
      relabelCell hpsi (base l) (base r) := rfl

theorem relabelCell_leader (hpsi : 0 < psi) (l r : Phys psi kappa tau) :
    B9Host.leader (relabelCell hpsi l r) = B9Host.leader r := rfl

theorem relabelCell_observe (hpsi : 0 < psi) (l r : Phys psi kappa tau) :
    ExpiringK2Projection.observeCell (relabelCell hpsi l r) =
      ExpiringK2Projection.observeCell r := rfl

def PhysRow (host : HostRow (Phys psi kappa tau))
    (l r : Cell psi kappa tau) (w : Cell psi kappa tau × Cell psi kappa tau) : Prop :=
  base w.1 = (host.row (base l) (base r)).1 ∧
  base w.2 = (host.row (base l) (base r)).2

def TriRow (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) (w : Cell psi kappa tau × Cell psi kappa tau) : Prop :=
  (base w.1 = base l ∧ base w.2 = base r) ∨
  PhysRow host l r w ∨
  (base w.1 = base l ∧ base w.2 = relabelCell hpsi (base l) (base r))

/-- Same endpoint-equality notion as the old transparency interface, but host-relative. -/
def PhysicalServiceAt (host : HostRow (Phys psi kappa tau))
    (ring : DirectedRing n) (C D : Config n psi kappa tau) (e : Fin n) : Prop :=
  PhysRow host (C e) (C (ring.rightNeighbor e)) (D e, D (ring.rightNeighbor e))

theorem phys_ordinary (host : HostRow (Phys psi kappa tau)) (l r : Cell psi kappa tau) :
    PhysRow host l r (ordinaryHostWriteH host l r) := by
  unfold ordinaryHostWriteH
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

theorem phys_delete (host : HostRow (Phys psi kappa tau)) (l r : Cell psi kappa tau) :
    PhysRow host l r (deleteWriteH host l r) := ⟨rfl, rfl⟩

theorem phys_hold (host : HostRow (Phys psi kappa tau)) (l r : Cell psi kappa tau) :
    PhysRow host l r (physicalHoldH host l r) := by
  unfold physicalHoldH
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

theorem phys_fence (host : HostRow (Phys psi kappa tau)) (l r : Cell psi kappa tau) :
    PhysRow host l r ((physicalHoldH host l r).1, fenceV6 (physicalHoldH host l r).2) :=
  phys_hold host l r

private theorem tri_keep (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) (w : Cell psi kappa tau × Cell psi kappa tau)
    (h1 : base w.1 = base l) (h2 : base w.2 = base r) :
    TriRow host hpsi l r w := Or.inl ⟨h1, h2⟩

private theorem tri_relabel (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) (w : Cell psi kappa tau × Cell psi kappa tau)
    (h1 : base w.1 = base l)
    (h2 : base w.2 = relabelCell hpsi (base l) (base r)) :
    TriRow host hpsi l r w := Or.inr (Or.inr ⟨h1, h2⟩)

private theorem tri_ite (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) (c : Prop) [Decidable c]
    (a b : Cell psi kappa tau × Cell psi kappa tau)
    (ha : TriRow host hpsi l r a) (hb : TriRow host hpsi l r b) :
    TriRow host hpsi l r (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem row7H_trichotomy (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : TriRow host hpsi l r (row7H host hpsi l r) := by
  classical
  unfold row7H
  repeat' apply tri_ite
  all_goals first
    | exact tri_keep host hpsi l r _ rfl rfl
    | exact tri_relabel host hpsi l r _ rfl rfl
    | exact Or.inr (Or.inl (phys_ordinary host l r))
    | exact Or.inr (Or.inl (phys_delete host l r))
    | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | (unfold moveStopWriteV6; apply tri_ite <;>
        exact tri_keep host hpsi l r _ rfl rfl)

theorem row10dgH_trichotomy (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : TriRow host hpsi l r (row10dgH host hpsi l r) := by
  classical
  unfold row10dgH row10cH row10bH row9H row8H
  repeat' first
    | exact row7H_trichotomy host hpsi l r
    | exact tri_keep host hpsi l r _ rfl rfl
    | exact tri_relabel host hpsi l r _ rfl rfl
    | apply tri_ite

theorem row10gH_trichotomy (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : TriRow host hpsi l r (row10gH host hpsi l r) := by
  classical
  unfold row10gH
  dsimp only
  by_cases hq : row10dgH host hpsi l r = (l, r)
  · rw [if_pos hq]
    repeat' apply tri_ite
    all_goals first
      | exact tri_keep host hpsi l r _ rfl rfl
      | exact Or.inr (Or.inl (phys_hold host l r))
      | exact Or.inr (Or.inl (phys_fence host l r))
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [if_neg hq]
    exact row10dgH_trichotomy host hpsi l r

theorem holdRepair_trichotomy (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) :
    TriRow host hpsi l r (B9SpliceTableV10j.holdRepairV10j l r) := by
  classical
  unfold B9SpliceTableV10j.holdRepairV10j
  repeat' apply tri_ite
  all_goals exact tri_keep host hpsi l r _ rfl rfl

/-- No host law, safety hypothesis, or leader hypothesis is used. -/
theorem rowB9_trichotomy (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : TriRow host hpsi l r (rowB9 host hpsi l r) := by
  classical
  unfold rowB9
  apply tri_ite
  · apply tri_ite
    · exact holdRepair_trichotomy host hpsi l r
    · exact Or.inr (Or.inl (phys_delete host l r))
  · exact row10gH_trichotomy host hpsi l r

/-! ## Configuration-level projection, with the off-pair frame -/

theorem stepB9_other (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    stepB9 host hpsi ring C e i = C i := by
  classical
  unfold stepB9
  by_cases hs : ring.rightNeighbor e = e
  · rw [if_pos hs]
  · rw [if_neg hs]
    exact writeAt_other ring C e _ i hi hj

private theorem erase_writeAt_eq (ring : DirectedRing n) (C : Config n psi kappa tau)
    (e : Fin n) (w : Cell psi kappa tau × Cell psi kappa tau) :
    erase (writeAt ring C e w) =
      (fun i => if i = e then base w.1
        else if i = ring.rightNeighbor e then base w.2 else base (C i)) := by
  funext i
  by_cases h1 : i = e <;> by_cases h2 : i = ring.rightNeighbor e <;>
    simp [erase, writeAt, h1, h2] <;> split <;> rfl

private theorem erase_writeAt_keep (ring : DirectedRing n) (C : Config n psi kappa tau)
    (e : Fin n) (w : Cell psi kappa tau × Cell psi kappa tau)
    (h : base w.1 = base (C e) ∧ base w.2 = base (C (ring.rightNeighbor e))) :
    erase (writeAt ring C e w) = erase C := by
  rw [erase_writeAt_eq, h.1, h.2]
  funext i
  by_cases hi : i = e
  · subst i
    simp [erase]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp [erase, hi]
    · simp [erase, hi, hj]

private theorem erase_writeAt_host (host : HostRow (Phys psi kappa tau))
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (w : Cell psi kappa tau × Cell psi kappa tau)
    (h : PhysRow host (C e) (C (ring.rightNeighbor e)) w) :
    erase (writeAt ring C e w) = hostStep host ring (erase C) e := by
  rw [erase_writeAt_eq, h.1, h.2] <;> rfl

private theorem erase_writeAt_relabel (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (w : Cell psi kappa tau × Cell psi kappa tau)
    (h : base w.1 = base (C e) ∧
      base w.2 = relabelCell hpsi (base (C e)) (base (C (ring.rightNeighbor e)))) :
    erase (writeAt ring C e w) = relabelStep hpsi ring (erase C) e := by
  rw [erase_writeAt_eq, h.1, h.2] <;> rfl

/-- Whole projected configuration: identity, one native host step, or one relabel.
The alternatives need not be disjoint. Self edges take the identity alternative. -/
theorem stepB9_project_trichotomy (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n) :
    erase (stepB9 host hpsi ring C e) = erase C ∨
    erase (stepB9 host hpsi ring C e) = hostStep host ring (erase C) e ∨
    erase (stepB9 host hpsi ring C e) = relabelStep hpsi ring (erase C) e := by
  classical
  by_cases hs : ring.rightNeighbor e = e
  · have hstep : stepB9 host hpsi ring C e = C := by
      simp only [stepB9, if_pos hs]
    exact Or.inl (congrArg (fun D : Config n psi kappa tau => erase D) hstep)
  · have hstep : stepB9 host hpsi ring C e =
        writeAt ring C e (rowB9 host hpsi (C e) (C (ring.rightNeighbor e))) := by
      simp only [stepB9, if_neg hs]
    have hp := congrArg (fun D : Config n psi kappa tau => erase D) hstep
    rcases rowB9_trichotomy host hpsi (C e) (C (ring.rightNeighbor e)) with hk | hh | hr
    · exact Or.inl (hp.trans (erase_writeAt_keep ring C e _ hk))
    · exact Or.inr (Or.inl (hp.trans (erase_writeAt_host host ring C e _ hh)))
    · exact Or.inr (Or.inr (hp.trans (erase_writeAt_relabel hpsi ring C e _ hr)))

/-- The requested input-leaderless specialization of the stronger theorem. -/
theorem stepB9_project_trichotomy_of_leaderless
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (_hlead : ∀ i, B9Host.leader (erase C i) = false) :
    erase (stepB9 host hpsi ring C e) = erase C ∨
    erase (stepB9 host hpsi ring C e) = hostStep host ring (erase C) e ∨
    erase (stepB9 host hpsi ring C e) = relabelStep hpsi ring (erase C) e :=
  stepB9_project_trichotomy host hpsi ring C e

/-- Unconditional R1 specialization: the physical alternative is the actual step1. -/
theorem stepV10kR1_project_trichotomy
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n) :
    erase (stepV10kR1 hpsi h2 ring C e) = erase C ∨
    erase (stepV10kR1 hpsi h2 ring C e) =
      BirthCheckPermitRepairLeaf.step1 hpsi h2 ring (erase C) e ∨
    erase (stepV10kR1 hpsi h2 ring C e) = relabelStep hpsi ring (erase C) e := by
  simpa only [stepV10kR1, B9Host.hostStep_r1_eq_step1] using
    (stepB9_project_trichotomy (r1Host hpsi h2) hpsi ring C e)

/-
PLAN -- future safety work, not active declarations or assumptions.

The unrestricted R1 geometric contract remains unproved in B9HostRow:
  B9Host.SpliceLaws (B9Host.r1Host hpsi h2).
Its active certificates there are:
  B9Host.r1Host_spliceLawsOn_noEqual
  B9Host.r1HostWidth_spliceLawsOn_responder_delete.

The genuine active E class requires ordinary priority, an equal initiator
at doneThroughCheckEntryWidth, and a true crossing permit at that cut.
NoEqualOutcome is narrower than the complement of E. Thus the two existing
guarded certificates must not be called an unrestricted or complete non-E
safety certificate. The equal/false-permit and initiator-wait agreement
extensions, as well as the E geometric bridge, are separate proof work.

The next safety target for this table is:

theorem stepB9_preserves_spliceSafeV7g
    (host : B9Host.HostRow (B9Host.Phys psi kappa tau))
    (laws : B9Host.SpliceLaws host) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Config n psi kappa tau) (e : Fin n)
    (hS : B9SpliceTableV10g.SpliceSafeV7g hpsi ring C) :
    B9SpliceTableV10g.SpliceSafeV7g hpsi ring (stepB9 host hpsi ring C e)

It is intentionally not declared here. In contrast, row/step projection
above needs none of those laws and already specializes to R1 on E too.
No conclusion about birth mass, convergence, or legitimacy closure follows
from the projection trichotomy alone.
-/

end B9SpliceTableHost

-- Audit commands for the subsequent build, not claimed results of a run.
#print axioms B9SpliceTableHost.stepB9_terminal
#print axioms B9SpliceTableHost.stepB9_project_trichotomy
#print axioms B9SpliceTableHost.stepV10kR1_project_trichotomy

-- END PART 3

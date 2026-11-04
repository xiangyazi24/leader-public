import Leader.Wu.Splice.HostTable
import Leader.Wu.WriteSeq.WriterProducerRepair

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9FullCarrierHost

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign
open B9Host
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerR1TableV6
open B9SpliceControllerR1TableV7
open B9SpliceTableHost

variable {n psi kappa tau width : Nat} {P : Type}

/- Do not let proofs in this file expand the accepted controller stack.
The representative transport below treats `row7H` through explicit equations;
the remaining rows are deliberately left as opaque completion obligations. -/
attribute [local irreducible]
  B9SpliceTableHost.row7H
  B9SpliceTableHost.row8H
  B9SpliceTableHost.row9H
  B9SpliceTableHost.row10bH
  B9SpliceTableHost.row10cH
  B9SpliceTableHost.row10dgH
  B9SpliceTableHost.row10gH
  B9SpliceTableHost.rowB9
  B9SpliceTableHost.stepB9

abbrev OldPhys (psi kappa tau : Nat) :=
  ExpiringAgentState psi kappa tau

abbrev OldCell (psi kappa tau : Nat) :=
  B9SpliceTableHost.Cell psi kappa tau

/-- Physical interface needed by the splice controller.

Direct controller tests use leader, label, and stall.  Probe/phase are included
because the controller relabel writes them together with label.  All remaining
old physical fields used by preparation/barrier predicates are read through
`erase`.  `sameExceptStall` is the V10c hook; an extended carrier must include
all extension coordinates that are forbidden to tick during a controller
stutter. -/
structure PhysCarrierLaws (P : Type) (psi kappa tau : Nat) where
  erase : P -> OldPhys psi kappa tau
  leader : P -> Bool
  label : P -> Fin psi
  probe : P -> Bool
  phase : P -> Bool
  stall : P -> Fin (tau + 1)
  relabel : (hpsi : 0 < psi) -> P -> P -> P
  sameExceptStall : P -> P -> Prop
  sameExceptStallB : P -> P -> Bool

  leader_eq : ∀ u, leader u = (erase u).core.core.leader
  label_eq : ∀ u, label u = (erase u).core.core.label
  probe_eq : ∀ u, probe u = (erase u).core.core.probe
  phase_eq : ∀ u, phase u = (erase u).core.core.phase
  stall_eq : ∀ u, stall u = (erase u).stall

  erase_relabel : ∀ hpsi l r,
    erase (relabel hpsi l r) =
      B9SpliceTableHost.relabelCell hpsi (erase l) (erase r)

  sameExceptStallB_spec : ∀ a b,
    sameExceptStallB a b = true ↔ sameExceptStall a b
  sameExceptStall_erase : ∀ {a b}, sameExceptStall a b ->
    (erase a).core = (erase b).core

/-- The V6 controller product, flattened over an arbitrary complete physical
carrier.  Controller-only writes never reconstruct or erase `phys`. -/
structure CellP (P : Type) where
  phys : P
  spliceRole : SpliceRole
  repairPending : Bool
  acquireTicket : Bool

abbrev ConfigP (n : Nat) (P : Type) := Fin n -> CellP P

namespace CellP

variable {P : Type}

@[simp] theorem phys_mk (p : P) (r : SpliceRole) (b t : Bool) :
    (CellP.mk p r b t).phys = p := rfl

def setRole (u : CellP P) (r : SpliceRole) : CellP P :=
  { u with spliceRole := r }

def setPending (u : CellP P) (b : Bool) : CellP P :=
  { u with repairPending := b }

def setTicket (u : CellP P) (b : Bool) : CellP P :=
  { u with acquireTicket := b }

def clearTicket (u : CellP P) : CellP P := setTicket u false

def setControl (u : CellP P) (r : SpliceRole) (b : Bool) : CellP P :=
  { u with spliceRole := r, repairPending := b, acquireTicket := false }

def clearControl (u : CellP P) : CellP P := setControl u .none false

def setPhysical (u : CellP P) (p : P) : CellP P := { u with phys := p }

@[simp] theorem phys_setRole (u : CellP P) (r : SpliceRole) :
    (setRole u r).phys = u.phys := rfl
@[simp] theorem phys_setPending (u : CellP P) (b : Bool) :
    (setPending u b).phys = u.phys := rfl
@[simp] theorem phys_setTicket (u : CellP P) (b : Bool) :
    (setTicket u b).phys = u.phys := rfl
@[simp] theorem phys_clearTicket (u : CellP P) :
    (clearTicket u).phys = u.phys := rfl
@[simp] theorem phys_setControl (u : CellP P) (r : SpliceRole) (b : Bool) :
    (setControl u r b).phys = u.phys := rfl
@[simp] theorem phys_clearControl (u : CellP P) :
    (clearControl u).phys = u.phys := rfl
@[simp] theorem phys_setPhysical (u : CellP P) (p : P) :
    (setPhysical u p).phys = p := rfl

end CellP

/-- Reuse accepted old guards by erasing only the physical coordinate. -/
def toOld (laws : PhysCarrierLaws P psi kappa tau)
    (u : CellP P) : OldCell psi kappa tau :=
  ⟨⟨⟨laws.erase u.phys, u.spliceRole⟩, u.repairPending⟩,
    u.acquireTicket⟩

/-- Copy old controller coordinates onto a chosen complete physical state. -/
def ofOldWith (u : OldCell psi kappa tau) (p : P) : CellP P :=
  ⟨p, B9SpliceControllerR1Table.role u.carrier,
    u.carrier.repairPending, u.acquireTicket⟩

@[simp] theorem phys_ofOldWith (u : OldCell psi kappa tau) (p : P) :
    (ofOldWith u p).phys = p := rfl

/-- Pair-local shadow host used only while evaluating accepted old guards. -/
def shadowHostAt
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (l r : P) : HostRow (OldPhys psi kappa tau) :=
  ⟨fun _ _ =>
    let q := host.row l r
    (laws.erase q.1, laws.erase q.2)⟩

/-- Operational tag.  It is not inferred from endpoint equality: an R2 host
call may change only fuel while its old erasure is unchanged. -/
inductive PhysicalAction where
  | keep
  | host
  | relabel
  deriving DecidableEq, Repr

/-- Exact row-7 branch classifier.  Controller writes are KEEP; DELETE and the
ordinary fallback are HOST; MOVE-COMMIT and fence advance are RELABEL. -/
noncomputable def row7ActionP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : PhysicalAction := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  exact
    if HostFenceShapeV7 lo then
      if LocalPreparedBarrier hpsi lo.carrier ro.carrier then
        if HostFenceTargetClearV7 ro then .relabel else .keep
      else .keep
    else if HostFenceShapeV7 ro then .keep
    else if MoveAcquireFrontGuardV6 hpsi lo ro then .keep
    else if ArmAGuardH oh lo.carrier ro.carrier then .keep
    else if ArmBGuard lo.carrier ro.carrier then .keep
    else if DeleteGuardH oh lo.carrier ro.carrier then .host
    else if PendingHoldGuardH oh lo.carrier ro.carrier then .keep
    else if PendingAbortGuardH oh lo.carrier ro.carrier then .keep
    else if MoveCommitGuard lo.carrier ro.carrier then .relabel
    else if MoveStopGuardV3 hpsi lo.carrier ro.carrier then .keep
    else if MoveSeekGuardV3 hpsi lo.carrier ro.carrier then .keep
    else if MoveSeekHoldGuardV3 lo.carrier ro.carrier then .keep
    else if PendingOwnerAbortGuardV3 lo.carrier ro.carrier then .keep
    else if B9SpliceControllerR1Table.role lo.carrier =
        SpliceRole.predecessorArmed ∧ lo.carrier.repairPending = true then .keep
    else if MoveAcquireLegacyGuardV6 lo ro then .keep
    else if MoveAcquireAbortGuardV3 lo.carrier ro.carrier then .keep
    else if OrphanReservedFrontGuardV3 lo.carrier ro.carrier then .keep
    else if B9SpliceControllerR1TableV2.ReservedFrontHoldGuard lo.carrier then .keep
    else if VictimRightScrubGuardV6 ro then .keep
    else if VictimLeftScrubGuardV6 lo then .keep
    else if FrontRightScrubGuardV6 ro then .keep
    else if MalformedLeftPendingGuardV6 lo then .keep
    else if MalformedRightPendingGuardV6 ro then .keep
    else if B9SpliceControllerR1Table.role lo.carrier =
        SpliceRole.predecessorArmed then .keep
    else if B9SpliceControllerR1Table.role lo.carrier = SpliceRole.front then .keep
    else if MarkedHoldGuardV6 lo ro then .keep
    else .host

/-- Transport row-7 controller coordinates, but install the complete P effect
selected by the explicit action tag. -/
noncomputable def row7P
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) : CellP P × CellP P := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  let q := B9SpliceTableHost.row7H oh hpsi lo ro
  let hp := host.row l.phys r.phys
  exact match row7ActionP laws host hpsi l r with
    | .keep => (ofOldWith q.1 l.phys, ofOldWith q.2 r.phys)
    | .host => (ofOldWith q.1 hp.1, ofOldWith q.2 hp.2)
    | .relabel =>
        (ofOldWith q.1 l.phys,
          ofOldWith q.2 (laws.relabel hpsi l.phys r.phys))

theorem row7P_action_spec
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    let w := row7P laws host hpsi l r
    match row7ActionP laws host hpsi l r with
    | .keep => w.1.phys = l.phys ∧ w.2.phys = r.phys
    | .host =>
        w.1.phys = (host.row l.phys r.phys).1 ∧
        w.2.phys = (host.row l.phys r.phys).2
    | .relabel =>
        w.1.phys = l.phys ∧
        w.2.phys = laws.relabel hpsi l.phys r.phys := by
  classical
  unfold row7P
  generalize ha : row7ActionP laws host hpsi l r = a
  cases a <;> simp only [ha, phys_ofOldWith]
  all_goals exact ⟨True.intro, True.intro⟩


/-- Row-level physical trichotomy without unfolding the controller table. -/
def TriRowP
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (w : CellP P × CellP P) : Prop :=
  (w.1.phys = l.phys ∧ w.2.phys = r.phys) ∨
  (w.1.phys = (host.row l.phys r.phys).1 ∧
    w.2.phys = (host.row l.phys r.phys).2) ∨
  (w.1.phys = l.phys ∧
    w.2.phys = laws.relabel hpsi l.phys r.phys)

theorem row7P_trichotomy
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) (l r : CellP P) :
    TriRowP laws host hpsi l r (row7P laws host hpsi l r) := by
  classical
  cases ha : row7ActionP laws host hpsi l r with
  | keep =>
      have h := row7P_action_spec laws host hpsi l r
      simp only [ha] at h
      exact Or.inl h
  | host =>
      have h := row7P_action_spec laws host hpsi l r
      simp only [ha] at h
      exact Or.inr (Or.inl h)
  | relabel =>
      have h := row7P_action_spec laws host hpsi l r
      simp only [ha] at h
      exact Or.inr (Or.inr h)

/- Do not subsequently re-open the representative classifier/row in proofs. -/
attribute [local irreducible] row7ActionP row7P

/-- A full V10 port carries an operational tag in addition to its row. -/
structure FullRowPort
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) where
  action : CellP P -> CellP P -> PhysicalAction
  row : CellP P -> CellP P -> CellP P × CellP P
  physical_spec : ∀ l r,
    let w := row l r
    match action l r with
    | .keep => w.1.phys = l.phys ∧ w.2.phys = r.phys
    | .host =>
        w.1.phys = (host.row l.phys r.phys).1 ∧
        w.2.phys = (host.row l.phys r.phys).2
    | .relabel =>
        w.1.phys = l.phys ∧
        w.2.phys = laws.relabel hpsi l.phys r.phys

noncomputable def row7Port
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi) :
    FullRowPort laws host hpsi where
  action := row7ActionP laws host hpsi
  row := row7P laws host hpsi
  physical_spec := row7P_action_spec laws host hpsi

/-- Skeleton used by the later V8--B9 transport. -/
def rowB9P
    {P : Type} {psi kappa tau : Nat}
    {laws : PhysCarrierLaws P psi kappa tau}
    {host : HostRow P} {hpsi : 0 < psi}
    (port : FullRowPort laws host hpsi)
    (l r : CellP P) : CellP P × CellP P :=
  port.row l r

def writeAtP
    {P : Type} {n : Nat}
    (ring : DirectedRing n) (C : ConfigP n P) (e : Fin n)
    (w : CellP P × CellP P) : ConfigP n P :=
  fun i =>
    if i = e then w.1
    else if i = ring.rightNeighbor e then w.2
    else C i

/-- Keep V10j's self-edge stutter. -/
def stepB9P
    {P : Type} {n psi kappa tau : Nat}
    {laws : PhysCarrierLaws P psi kappa tau}
    {host : HostRow P} {hpsi : 0 < psi}
    (port : FullRowPort laws host hpsi)
    (ring : DirectedRing n) (C : ConfigP n P) (e : Fin n) : ConfigP n P :=
  if ring.rightNeighbor e = e then C
  else writeAtP ring C e (rowB9P port (C e) (C (ring.rightNeighbor e)))

def physConfig {P : Type} {n : Nat} (C : ConfigP n P) : Fin n -> P :=
  fun i => (C i).phys

def relabelHostP
    (laws : PhysCarrierLaws P psi kappa tau) (hpsi : 0 < psi) : HostRow P :=
  ⟨fun l r => (l, laws.relabel hpsi l r)⟩

def relabelStepP
    (laws : PhysCarrierLaws P psi kappa tau) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : Fin n -> P) (e : Fin n) : Fin n -> P :=
  hostStep (relabelHostP laws hpsi) ring C e

private theorem physConfig_writeAtP_keep
    (ring : DirectedRing n) (C : ConfigP n P) (e : Fin n)
    (w : CellP P × CellP P)
    (hL : w.1.phys = (C e).phys)
    (hR : w.2.phys = (C (ring.rightNeighbor e)).phys) :
    physConfig (writeAtP ring C e w) = physConfig C := by
  funext i
  by_cases hi : i = e
  · simp [writeAtP, physConfig, hi, hL]
  · by_cases hj : i = ring.rightNeighbor e
    · have hself : ring.rightNeighbor e ≠ e := by
        intro h
        apply hi
        exact hj.trans h
      simp [writeAtP, physConfig, hi, hj, hself, hR]
    · simp [writeAtP, physConfig, hi, hj]


private theorem physConfig_writeAtP_host
    (host : HostRow P) (ring : DirectedRing n)
    (C : ConfigP n P) (e : Fin n) (w : CellP P × CellP P)
    (hL : w.1.phys = (host.row (C e).phys (C (ring.rightNeighbor e)).phys).1)
    (hR : w.2.phys = (host.row (C e).phys (C (ring.rightNeighbor e)).phys).2) :
    physConfig (writeAtP ring C e w) =
      hostStep host ring (physConfig C) e := by
  funext i
  by_cases hi : i = e
  · simp [writeAtP, physConfig, B9Host.hostStep, hi, hL]
  · by_cases hj : i = ring.rightNeighbor e
    · have hself : ring.rightNeighbor e ≠ e := by
        intro h
        apply hi
        exact hj.trans h
      simp [writeAtP, physConfig, B9Host.hostStep,
        hi, hj, hself, hR]
    · simp [writeAtP, physConfig, B9Host.hostStep, hi, hj]


private theorem physConfig_writeAtP_relabel
    (laws : PhysCarrierLaws P psi kappa tau) (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : ConfigP n P) (e : Fin n)
    (w : CellP P × CellP P)
    (hL : w.1.phys = (C e).phys)
    (hR : w.2.phys = laws.relabel hpsi
      (C e).phys (C (ring.rightNeighbor e)).phys) :
    physConfig (writeAtP ring C e w) =
      relabelStepP laws hpsi ring (physConfig C) e := by
  funext i
  by_cases hi : i = e
  · simp [writeAtP, physConfig, relabelStepP, relabelHostP,
      B9Host.hostStep, hi, hL]
  · by_cases hj : i = ring.rightNeighbor e
    · have hself : ring.rightNeighbor e ≠ e := by
        intro h
        apply hi
        exact hj.trans h
      simp [writeAtP, physConfig, relabelStepP, relabelHostP,
        B9Host.hostStep, hi, hj, hself, hR]
    · simp [writeAtP, physConfig, relabelStepP, relabelHostP,
        B9Host.hostStep, hi, hj]


/-- Configuration-level two-clock projection for any completed row port. -/
theorem stepB9P_project_trichotomy
    {P : Type} {n psi kappa tau : Nat}
    {laws : PhysCarrierLaws P psi kappa tau}
    {host : HostRow P} {hpsi : 0 < psi}
    (port : FullRowPort laws host hpsi)
    (ring : DirectedRing n) (C : ConfigP n P) (e : Fin n) :
    physConfig (stepB9P port ring C e) = physConfig C ∨
    physConfig (stepB9P port ring C e) =
      hostStep host ring (physConfig C) e ∨
    physConfig (stepB9P port ring C e) =
      relabelStepP laws hpsi ring (physConfig C) e := by
  classical
  by_cases hs : ring.rightNeighbor e = e
  · left
    simp [stepB9P, hs]
  · let w := port.row (C e) (C (ring.rightNeighbor e))
    have hstep : stepB9P port ring C e = writeAtP ring C e w := by
      simp [stepB9P, hs, rowB9P, w]
    cases ha : port.action (C e) (C (ring.rightNeighbor e)) with
    | keep =>
        have hp := port.physical_spec (C e) (C (ring.rightNeighbor e))
        simp only [ha] at hp
        left
        rw [hstep]
        exact physConfig_writeAtP_keep ring C e w hp.1 hp.2
    | host =>
        have hp := port.physical_spec (C e) (C (ring.rightNeighbor e))
        simp only [ha] at hp
        right; left
        rw [hstep]
        exact physConfig_writeAtP_host host ring C e w hp.1 hp.2
    | relabel =>
        have hp := port.physical_spec (C e) (C (ring.rightNeighbor e))
        simp only [ha] at hp
        right; right
        rw [hstep]
        exact physConfig_writeAtP_relabel laws hpsi ring C e w hp.1 hp.2

/-! ## Old physical carrier: exact representative regression -/

def oldLaws : PhysCarrierLaws (OldPhys psi kappa tau) psi kappa tau where
  erase := fun u => u
  leader := fun u => u.core.core.leader
  label := fun u => u.core.core.label
  probe := fun u => u.core.core.probe
  phase := fun u => u.core.core.phase
  stall := fun u => u.stall
  relabel := fun hpsi l r => B9SpliceTableHost.relabelCell hpsi l r
  sameExceptStall := fun a b => a.core = b.core
  sameExceptStallB := fun a b => decide (a.core = b.core)
  leader_eq := by intro u; rfl
  label_eq := by intro u; rfl
  probe_eq := by intro u; rfl
  phase_eq := by intro u; rfl
  stall_eq := by intro u; rfl
  erase_relabel := by intro hpsi l r; rfl
  sameExceptStallB_spec := by intro a b; simp
  sameExceptStall_erase := by intro a b h; exact h

def oldToP (u : OldCell psi kappa tau) : CellP (OldPhys psi kappa tau) :=
  ofOldWith u (B9SpliceTableHost.base u)

@[simp] theorem toOld_oldToP (u : OldCell psi kappa tau) :
    toOld oldLaws (oldToP u) = u := by
  rcases u with ⟨⟨⟨p, r⟩, b⟩, t⟩
  rfl

@[simp] theorem oldToP_toOld
    (u : CellP (OldPhys psi kappa tau)) :
    oldToP (toOld oldLaws u) = u := by
  rcases u with ⟨p, r, b, t⟩
  rfl

/-- Exact old row-7 transport.  Crucially, this wrapper does not unfold
`row7H`; it merely preserves its result and changes representation. -/
noncomputable def row7OldP
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    CellP (OldPhys psi kappa tau) × CellP (OldPhys psi kappa tau) :=
  let q := B9SpliceTableHost.row7H host hpsi
    (toOld oldLaws l) (toOld oldLaws r)
  (oldToP q.1, oldToP q.2)

/-- Representative equality-to-old theorem, proved only through explicit
representation equations. -/
theorem row7OldP_regression
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : OldCell psi kappa tau) :
    row7OldP host hpsi (oldToP l) (oldToP r) =
      (oldToP (B9SpliceTableHost.row7H host hpsi l r).1,
       oldToP (B9SpliceTableHost.row7H host hpsi l r).2) := by
  simp only [row7OldP, toOld_oldToP]

/-- Erasing the exact wrapper gives literally the accepted old row. -/
theorem row7OldP_toOld
    (host : HostRow (OldPhys psi kappa tau)) (hpsi : 0 < psi)
    (l r : CellP (OldPhys psi kappa tau)) :
    (toOld oldLaws (row7OldP host hpsi l r).1,
      toOld oldLaws (row7OldP host hpsi l r).2) =
      B9SpliceTableHost.row7H host hpsi (toOld oldLaws l) (toOld oldLaws r) := by
  simp only [row7OldP, toOld_oldToP]

/-! ## R2 instance and producer-clock framing -/

def r2Laws : PhysCarrierLaws (R2.Cell psi kappa tau) psi kappa tau where
  erase := fun u => u.base
  leader := fun u => u.base.core.core.leader
  label := fun u => u.base.core.core.label
  probe := fun u => u.base.core.core.probe
  phase := fun u => u.base.core.core.phase
  stall := fun u => u.base.stall
  relabel := fun hpsi l r =>
    { r with base := B9SpliceTableHost.relabelCell hpsi l.base r.base }
  sameExceptStall := fun a b => a.base.core = b.base.core ∧ a.fuel = b.fuel
  sameExceptStallB := fun a b =>
    decide (a.base.core = b.base.core ∧ a.fuel = b.fuel)
  leader_eq := by intro u; rfl
  label_eq := by intro u; rfl
  probe_eq := by intro u; rfl
  phase_eq := by intro u; rfl
  stall_eq := by intro u; rfl
  erase_relabel := by intro hpsi l r; rfl
  sameExceptStallB_spec := by intro a b; simp
  sameExceptStall_erase := by intro a b h; exact h.1

def r2Host (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi) :
    HostRow (R2.Cell psi kappa tau) :=
  ⟨R2.row hpsi hwidth hle⟩

@[simp] theorem r2_relabel_fuel
    (hpsi : 0 < psi) (l r : R2.Cell psi kappa tau) :
    (r2Laws.relabel hpsi l r).fuel = r.fuel := rfl

@[simp] theorem r2_controller_setControl_fuel
    (u : CellP (R2.Cell psi kappa tau)) (role : SpliceRole) (p : Bool) :
    ((CellP.setControl u role p).phys).fuel = u.phys.fuel := rfl

@[simp] theorem r2_controller_setTicket_fuel
    (u : CellP (R2.Cell psi kappa tau)) (b : Bool) :
    ((CellP.setTicket u b).phys).fuel = u.phys.fuel := rfl

/-- KEEP is a pure controller service: neither R2 producer clock ticks. -/
theorem row7P_r2_keep_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row7ActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r =
      PhysicalAction.keep) :
    let q := row7P r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  dsimp only
  have hs := row7P_action_spec r2Laws (r2Host hpsi hwidth hle) hpsi l r
  simp only [ha] at hs
  exact ⟨
    congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.1,
    congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.2⟩

/-- RELABEL repairs only old label/probe/phase and frames R2 fuel. -/
theorem row7P_r2_relabel_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row7ActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r =
      PhysicalAction.relabel) :
    let q := row7P r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  dsimp only
  have hs := row7P_action_spec r2Laws (r2Host hpsi hwidth hle) hpsi l r
  simp only [ha] at hs
  constructor
  · exact congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.1
  · calc
      (row7P r2Laws (r2Host hpsi hwidth hle) hpsi l r).2.phys.fuel =
          (r2Laws.relabel hpsi l.phys r.phys).fuel :=
        congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.2
      _ = r.phys.fuel := r2_relabel_fuel hpsi l.phys r.phys

/-- HOST means a genuine R2.row call; its complete fuel output is installed. -/
theorem row7P_r2_host_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row7ActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r =
      PhysicalAction.host) :
    let q := row7P r2Laws (r2Host hpsi hwidth hle) hpsi l r
    let h := R2.row hpsi hwidth hle l.phys r.phys
    q.1.phys.fuel = h.1.fuel ∧ q.2.phys.fuel = h.2.fuel := by
  dsimp only
  have hs := row7P_action_spec r2Laws (r2Host hpsi hwidth hle) hpsi l r
  simp only [ha] at hs
  constructor
  · have h := congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.1
    simpa only [r2Host] using h
  · have h := congrArg (fun u : R2.Cell psi kappa tau => u.fuel) hs.2
    simpa only [r2Host] using h

/-- Hence every non-HOST representative branch frames both producer clocks. -/
theorem row7P_r2_nonhost_fuel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : CellP (R2.Cell psi kappa tau))
    (ha : row7ActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r ≠
      PhysicalAction.host) :
    let q := row7P r2Laws (r2Host hpsi hwidth hle) hpsi l r
    q.1.phys.fuel = l.phys.fuel ∧ q.2.phys.fuel = r.phys.fuel := by
  cases hact : row7ActionP r2Laws (r2Host hpsi hwidth hle) hpsi l r with
  | keep => exact row7P_r2_keep_fuel hpsi hwidth hle l r hact
  | host => exact False.elim (ha hact)
  | relabel => exact row7P_r2_relabel_fuel hpsi hwidth hle l r hact

/-!
PLAN -- full V8/V9/V10/B9 transport, intentionally not unfolded here.

1. For each accepted layer, define an equation lemma `row8P_eq`, `row9P_eq`,
   `row10bP_eq`, ... whose RHS mentions only the preceding full-carrier row and
   that layer's one new guard/write.  Keep all imported old tables irreducible.

2. V10c must use `laws.stall` and `laws.sameExceptStallB`.  For R2 the latter
   includes fuel equality, so an R2 call that only ticks producer fuel cannot be
   mistaken for a controller zero-refresh stutter.

3. `row10dgH` garbage writers are KEEP.  In `row10gH`, `physicalHoldH` and its
   fenced variant are HOST despite the historical name "hold": they execute the
   host and must install the complete P output.  This is the two-clock seam.

4. Top-level DELETE is HOST, V10j `holdRepairV10j` is KEEP, and the ordinary
   branch inherits the `row10gP` tag.  Package the resulting row and action in
   `FullRowPort`; `stepB9P_project_trichotomy` then applies unchanged.

5. Old regression: define every old exact wrapper in the style of `row7OldP`.
   Prove its `toOld` equation by `toOld_oldToP`; never unfold an imported table.
   The final `stepB9P_old = stepB9` theorem is then a short extensional proof.

6. R2: `.keep` and `.relabel` frame fuel; `.host` installs exactly `R2.row`
   fuel.  Scheduler-time recovery must count HOST services separately from B9
   controller services; a controller hold does not spend producer credit.
-/

end B9FullCarrierHost

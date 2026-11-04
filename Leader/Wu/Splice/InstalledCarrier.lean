import Leader.Wu.Coherence.Controller
import Leader.Wu.Splice.FullCarrierRows

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZFinalCarrierV3

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost

variable {n ψ κ τ : Nat}

/-- Repaired complete physical carrier: R2 fuel plus V3.1 quarantine control. -/
abbrev P (ψ κ τ : Nat) := R2CoherenceV31.Cell ψ κ τ

/-- Final local state over the V3.1 physical carrier. -/
abbrev Cell (ψ κ τ : Nat) := B9FullCarrierHost.CellP (P ψ κ τ)

abbrev Config (n ψ κ τ : Nat) :=
  B9FullCarrierHost.ConfigP n (P ψ κ τ)

/-- Raw B9 relabel lifted to the V3.1 carrier.  Fuel and V3.1 control are framed. -/
def rawRelabelR2CV3 (hψ : 0 < ψ) (l r : P ψ κ τ) : P ψ κ τ :=
  { r with
    phys :=
      { r.phys with
        base := B9SpliceTableHost.relabelCell hψ
          l.phys.base r.phys.base } }

/-- Full-carrier laws for the V3.1 carrier. -/
def carrierLawsV3 :
    B9FullCarrierHost.PhysCarrierLaws (P ψ κ τ) ψ κ τ where
  erase := fun u => u.phys.base
  leader := fun u => u.phys.base.core.core.leader
  label := fun u => u.phys.base.core.core.label
  probe := fun u => u.phys.base.core.core.probe
  phase := fun u => u.phys.base.core.core.phase
  stall := fun u => u.phys.base.stall
  relabel := rawRelabelR2CV3
  sameExceptStall := fun a b =>
    a.phys.base.core = b.phys.base.core ∧
      a.phys.fuel = b.phys.fuel ∧ a.ctl = b.ctl
  sameExceptStallB := fun a b =>
    decide (a.phys.base.core = b.phys.base.core ∧
      a.phys.fuel = b.phys.fuel ∧ a.ctl = b.ctl)
  leader_eq := by intro u; rfl
  label_eq := by intro u; rfl
  probe_eq := by intro u; rfl
  phase_eq := by intro u; rfl
  stall_eq := by intro u; rfl
  erase_relabel := by intro hψ l r; rfl
  sameExceptStallB_spec := by intro a b; simp
  sameExceptStall_erase := by intro a b h; exact h.1

/-- Repaired physical host: exactly the V3.1 radius-one row. -/
def hostR2CV3 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :
    B9Host.HostRow (P ψ κ τ) :=
  ⟨R2CoherenceV31.rowV3 hψ (by decide : 0 < 2) h2⟩

/-- Full B9 port type instantiated at the repaired physical carrier. -/
abbrev PortV3 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :=
  B9FullCarrierHost.FullRowPort
    (carrierLawsV3 (ψ := ψ) (κ := κ) (τ := τ))
    (hostR2CV3 (κ := κ) (τ := τ) hψ h2) hψ

/-- Old B9 shadow used only by the accepted recovery predicates. -/
def oldCellV3 (u : Cell ψ κ τ) : B9SpliceTableHost.Cell ψ κ τ :=
  B9FullCarrierHost.toOld
    (carrierLawsV3 (ψ := ψ) (κ := κ) (τ := τ)) u

def oldConfigV3 (C : Config n ψ κ τ) :
    B9SpliceTableHost.Config n ψ κ τ :=
  fun i => oldCellV3 (C i)

def FinalBadTicketV3 (u : Cell ψ κ τ) : Prop :=
  B9ControllerRecovery.BadTicket (oldCellV3 u)

def FinalBadBackingV3 (l r : Cell ψ κ τ) : Prop :=
  B9ControllerRecovery.BadBacking (oldCellV3 l) (oldCellV3 r)

def FinalHoleV3 (hψ : 0 < ψ) (l r : Cell ψ κ τ) : Prop :=
  B9ControllerRecovery.Hole hψ (oldCellV3 l) (oldCellV3 r)

def FinalGarbageV3 (hψ : 0 < ψ) (l r : Cell ψ κ τ) : Prop :=
  B9ControllerRecovery.Garbage hψ (oldCellV3 l) (oldCellV3 r)

/-- Controller-only recovery clear; the complete V3.1 physical carrier is framed. -/
def clearFinalControlV3 (u : Cell ψ κ τ) : Cell ψ κ τ :=
  B9FullCarrierHost.CellP.setControl u .none false

/-- Controller-only local hole cover; the complete V3.1 physical carrier is framed. -/
def coverFinalV3 (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  (B9FullCarrierHost.CellP.setControl l .predecessorArmed true,
   B9FullCarrierHost.CellP.setControl r .front true)

/-- Same recovery priority as the installed final wrapper, retyped to V3.1. -/
noncomputable def recoverPairV3 (hψ : 0 < ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ := by
  classical
  exact if FinalBadTicketV3 l then (clearFinalControlV3 l, r)
    else if FinalBadTicketV3 r then (l, clearFinalControlV3 r)
    else if FinalBadBackingV3 l r then (clearFinalControlV3 l, r)
    else if FinalHoleV3 hψ l r then coverFinalV3 l r
    else (l, r)

/-- V3.1 analogue of the installed relabel gate. -/
def RelabelReadyV3 (l r : P ψ κ τ) : Prop :=
  l.ctl.mark = R2Coherence.Mark.sealed ∧
    l.ctl.tok = R2CoherenceV31.TokenV3.none ∧
    r.ctl.mark = R2Coherence.Mark.sealed ∧
    r.ctl.tok = R2CoherenceV31.TokenV3.none

instance relabelReadyV3Decidable (l r : P ψ κ τ) :
    Decidable (RelabelReadyV3 l r) := by
  unfold RelabelReadyV3
  infer_instance

/-- Hold a projected B9 relabel and launch the V3.1 closing/seek quarantine. -/
def holdRelabelPairV3 (l r : Cell ψ κ τ) :
    Cell ψ κ τ × Cell ψ κ τ :=
  (l, B9FullCarrierHost.CellP.setPhysical r
    (R2CoherenceV31.startClosing r.phys))

inductive FinalActionV3 where
  | recovery
  | keep
  | host
  | quarantineRelabel
  | relabel
  deriving DecidableEq, Repr

/-- Recovery dominates; an unready B9 relabel becomes a V3.1 quarantine request. -/
noncomputable def finalActionV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : PortV3 (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ) : FinalActionV3 := by
  classical
  exact if FinalGarbageV3 hψ l r then .recovery
    else match port.action l r with
      | .keep => .keep
      | .host => .host
      | .relabel =>
          if RelabelReadyV3 l.phys r.phys then .relabel
          else .quarantineRelabel

/-- Exact local final row over the V3.1 carrier. -/
noncomputable def rowFinalV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : PortV3 (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ := by
  classical
  exact match finalActionV3 hψ h2 port l r with
    | .recovery => recoverPairV3 hψ l r
    | .keep => port.row l r
    | .host => port.row l r
    | .quarantineRelabel => holdRelabelPairV3 l r
    | .relabel => port.row l r

/-- V3.1 retyping of the installed `stepFinal`. -/
noncomputable def stepFinalV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : PortV3 (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (C : Config n ψ κ τ) (e : Fin n) :
    Config n ψ κ τ := by
  classical
  exact if ring.rightNeighbor e = e then
    if FinalGarbageV3 hψ (C e) (C e) then
      B9FullCarrierHost.writeAtP ring C e
        (clearFinalControlV3 (C e), C e)
    else C
  else
    B9FullCarrierHost.writeAtP ring C e
      (rowFinalV3 hψ h2 port (C e) (C (ring.rightNeighbor e)))

/-- Route-frozen complete B9 port over `R2CoherenceV31.rowV3`. -/
noncomputable def concretePortV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :
    PortV3 (κ := κ) (τ := τ) hψ h2 :=
  B9FullCarrierRows.fullRowPort
    (carrierLawsV3 (ψ := ψ) (κ := κ) (τ := τ))
    (hostR2CV3 (κ := κ) (τ := τ) hψ h2) hψ

/-- Exact repaired final scheduler step. -/
noncomputable def stepConcreteV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    Config n ψ κ τ → Fin n → Config n ψ κ τ :=
  stepFinalV3 hψ h2
    (concretePortV3 (κ := κ) (τ := τ) hψ h2) ring

end ZZFinalCarrierV3

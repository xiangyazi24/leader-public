import Leader.Wu.Coherence.SixTokenController
import Leader.Wu.Splice.ControllerRecovery
import Leader.Wu.Splice.FullCarrierHost
import Leader.Wu.Splice.AllPendingFixed
import Leader.Wu.Birth.TwoStageEscape

set_option autoImplicit false
set_option Elab.async false

/-!
# Candidate final row: recovery-corrected B9 over R2 coherence

This file fixes one exact successor architecture before the remaining generic
B9 rows are frozen.  The stored physical carrier is `R2Coherence.Cell`:
R2's full fuel-carrying state plus the finite 4 x 6 quarantine controller.
The outer splice controller is `B9FullCarrierHost.CellP`.

Important interface boundary: `PhysCarrierLaws.erase_relabel` requires the
law-level relabel primitive to erase to the old immediate `relabelCell`.
The hold-before-relabel policy is therefore enforced by `rowFinal`, not by
lying about that primitive.  A `.relabel` port action is held while R2C is
unsealed and launches a quarantine seek; the raw relabel is admitted only when
both endpoints are sealed and token-free.
-/

namespace FinalCandidateR2C

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost
open WriterProducerRepair

variable {n ψ κ τ : Nat}

/-- Complete physical carrier: R2 fuel plus the R2C quarantine controller. -/
abbrev P (ψ κ τ : Nat) := R2Coherence.Cell ψ κ τ

/-- Final local state: the full physical carrier plus the B9 controller. -/
abbrev Cell (ψ κ τ : Nat) := B9FullCarrierHost.CellP (P ψ κ τ)

abbrev Config (n ψ κ τ : Nat) :=
  B9FullCarrierHost.ConfigP n (P ψ κ τ)

/-- The raw transport primitive required by the current `PhysCarrierLaws`
interface.  It changes only the old physical relabel fields; R2 fuel and R2C
quarantine control are framed.  `rowFinal` gates every use of this primitive. -/
def rawRelabelR2C (hψ : 0 < ψ) (l r : P ψ κ τ) : P ψ κ τ :=
  { r with
    phys :=
      { r.phys with
        base := B9SpliceTableHost.relabelCell hψ
          l.phys.base r.phys.base } }

@[simp] theorem rawRelabelR2C_fuel
    (hψ : 0 < ψ) (l r : P ψ κ τ) :
    (rawRelabelR2C hψ l r).phys.fuel = r.phys.fuel := by
  rfl

@[simp] theorem rawRelabelR2C_ctl
    (hψ : 0 < ψ) (l r : P ψ κ τ) :
    (rawRelabelR2C hψ l r).ctl = r.ctl := by
  rfl

@[simp] theorem rawRelabelR2C_erase
    (hψ : 0 < ψ) (l r : P ψ κ τ) :
    (rawRelabelR2C hψ l r).phys.base =
      B9SpliceTableHost.relabelCell hψ l.phys.base r.phys.base := by
  rfl

/-- Full-carrier laws for R2C.  `sameExceptStall` includes both producer fuel
and quarantine control, so neither clock/control can disappear inside a B9
controller stutter. -/
def carrierLaws :
    B9FullCarrierHost.PhysCarrierLaws (P ψ κ τ) ψ κ τ where
  erase := fun u => u.phys.base
  leader := fun u => u.phys.base.core.core.leader
  label := fun u => u.phys.base.core.core.label
  probe := fun u => u.phys.base.core.core.probe
  phase := fun u => u.phys.base.core.core.phase
  stall := fun u => u.phys.base.stall
  relabel := rawRelabelR2C
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

/-- The actual physical host is exactly the R2 coherence wrapper. -/
def hostR2C (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : HostRow (P ψ κ τ) :=
  ⟨R2Coherence.row hψ (by decide : 0 < 2) h2⟩

/-- Type of the pending full B9 port. -/
abbrev Port (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :=
  B9FullCarrierHost.FullRowPort
    (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
    (hostR2C (κ := κ) (τ := τ) hψ h2) hψ

/-- Conservative install condition for a controller relabel. -/
def RelabelReady (l r : P ψ κ τ) : Prop :=
  l.ctl.mark = .sealed ∧ l.ctl.tok = .none ∧
    r.ctl.mark = .sealed ∧ r.ctl.tok = .none

instance relabelReadyDecidable (l r : P ψ κ τ) :
    Decidable (RelabelReady l r) := by
  unfold RelabelReady
  infer_instance

/-- Semantic relabel operation: install the raw relabel only in a
sealed pair; otherwise hold the physical base and launch quarantine. -/
def gatedRelabelR2C (hψ : 0 < ψ) (l r : P ψ κ τ) : P ψ κ τ :=
  if RelabelReady l r then rawRelabelR2C hψ l r
  else R2Coherence.startClosing r

@[simp] theorem gatedRelabelR2C_of_ready
    (hψ : 0 < ψ) (l r : P ψ κ τ) (h : RelabelReady l r) :
    gatedRelabelR2C hψ l r = rawRelabelR2C hψ l r := by
  simp [gatedRelabelR2C, h]

@[simp] theorem gatedRelabelR2C_of_not_ready
    (hψ : 0 < ψ) (l r : P ψ κ τ) (h : ¬ RelabelReady l r) :
    gatedRelabelR2C hψ l r = R2Coherence.startClosing r := by
  simp [gatedRelabelR2C, h]

/-- On the hold branch the physical R2 state is unchanged and the exact R2C
`closing/seek` request is installed. -/
theorem gatedRelabelR2C_hold
    (hψ : 0 < ψ) (l r : P ψ κ τ) (h : ¬ RelabelReady l r) :
    (gatedRelabelR2C hψ l r).phys = r.phys ∧
      (gatedRelabelR2C hψ l r).ctl.mark = .closing ∧
      (gatedRelabelR2C hψ l r).ctl.tok = .seek := by
  rw [gatedRelabelR2C_of_not_ready hψ l r h]
  exact ⟨rfl, rfl, rfl⟩

namespace FinalCandidateR2C

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost
open WriterProducerRepair

variable {n ψ κ τ : Nat}

/-- Old B9 view used only for its accepted recovery predicates. -/
def oldCell (u : Cell ψ κ τ) : B9SpliceTableHost.Cell ψ κ τ :=
  B9FullCarrierHost.toOld
    (carrierLaws (ψ := ψ) (κ := κ) (τ := τ)) u

def oldConfig (C : Config n ψ κ τ) :
    B9SpliceTableHost.Config n ψ κ τ :=
  fun i => oldCell (C i)

def FinalBadTicket (u : Cell ψ κ τ) : Prop :=
  B9ControllerRecovery.BadTicket (oldCell u)

def FinalBadBacking (l r : Cell ψ κ τ) : Prop :=
  B9ControllerRecovery.BadBacking (oldCell l) (oldCell r)

def FinalHole (hψ : 0 < ψ) (l r : Cell ψ κ τ) : Prop :=
  B9ControllerRecovery.Hole hψ (oldCell l) (oldCell r)

def FinalGarbage (hψ : 0 < ψ) (l r : Cell ψ κ τ) : Prop :=
  B9ControllerRecovery.Garbage hψ (oldCell l) (oldCell r)

/-- Generic full-carrier version of the recovery clear. -/
def clearFinalControl (u : Cell ψ κ τ) : Cell ψ κ τ :=
  B9FullCarrierHost.CellP.setControl u .none false

/-- Generic full-carrier version of `coverWrite`; physical R2C state is framed. -/
def coverFinal (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  (B9FullCarrierHost.CellP.setControl l .predecessorArmed true,
   B9FullCarrierHost.CellP.setControl r .front true)

/-- Exact recovery priority, lifted through `toOld` and changing only
outer controller coordinates. -/
noncomputable def recoverPair (hψ : 0 < ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ := by
  classical
  exact if FinalBadTicket l then (clearFinalControl l, r)
    else if FinalBadTicket r then (l, clearFinalControl r)
    else if FinalBadBacking l r then (clearFinalControl l, r)
    else if FinalHole hψ l r then coverFinal l r
    else (l, r)

/-- Hold both the B9 controller write and the raw relabel, changing only the
R2C target control to `closing/seek`. -/
def holdRelabelPair (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  (l, B9FullCarrierHost.CellP.setPhysical r
    (R2Coherence.startClosing r.phys))

/-- Operational tag for the exact candidate row. -/
inductive FinalAction where
  | recovery
  | keep
  | host
  | quarantineRelabel
  | relabel
  deriving DecidableEq, Repr

/-- Recovery dominates.  Otherwise a raw B9 relabel is converted into a
quarantine request until both R2C endpoints are sealed. -/
noncomputable def finalAction
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ) : FinalAction := by
  classical
  exact if FinalGarbage hψ l r then .recovery
    else match port.action l r with
      | .keep => .keep
      | .host => .host
      | .relabel =>
          if RelabelReady l.phys r.phys then .relabel
          else .quarantineRelabel

/-- One exact local final row. -/
noncomputable def rowFinal
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ := by
  classical
  exact match finalAction hψ h2 port l r with
    | .recovery => recoverPair hψ l r
    | .keep => port.row l r
    | .host => port.row l r
    | .quarantineRelabel => holdRelabelPair l r
    | .relabel => port.row l r

/-- Cheap relabel gate: the final classifier can select a projected relabel
only after both endpoints are sealed and token-free. -/
theorem finalAction_relabel_ready
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ)
    (h : finalAction hψ h2 port l r = .relabel) :
    RelabelReady l.phys r.phys := by
  classical
  unfold finalAction at h
  by_cases hg : FinalGarbage hψ l r
  · simp [hg] at h
  · rw [if_neg hg] at h
    cases ha : port.action l r with
    | keep => simp [ha] at h
    | host => simp [ha] at h
    | relabel =>
        simp only [ha] at h
        by_cases hr : RelabelReady l.phys r.phys
        · exact hr
        · simp [hr] at h

/-- On an operational final relabel, `rowFinal` installs the port result; the
preceding theorem certifies that this branch is sealed. -/
theorem rowFinal_relabel_action
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ)
    (h : finalAction hψ h2 port l r = .relabel) :
    rowFinal hψ h2 port l r = port.row l r ∧
      RelabelReady l.phys r.phys := by
  constructor
  · unfold rowFinal
    rw [h]
  · exact finalAction_relabel_ready hψ h2 port l r h

/-- Exact final scheduler step.  As in the recovery-corrected old controller,
a malformed self edge may clear controller garbage; a safe self edge stutters. -/
noncomputable def stepFinal
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (C : Config n ψ κ τ) (e : Fin n) :
    Config n ψ κ τ := by
  classical
  exact if ring.rightNeighbor e = e then
    if FinalGarbage hψ (C e) (C e) then
      B9FullCarrierHost.writeAtP ring C e
        (clearFinalControl (C e), C e)
    else C
  else
    B9FullCarrierHost.writeAtP ring C e
      (rowFinal hψ h2 port (C e) (C (ring.rightNeighbor e)))

/-- Final output map: the physical leader bit, with neither controller layer
participating in the observable output. -/
def outputFinal (u : Cell ψ κ τ) : Bool :=
  u.phys.phys.base.core.core.leader

namespace FinalCandidateR2C

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost
open WriterProducerRepair
open BirthTwoStageEscape

variable {n ψ κ τ : Nat}

/-- Old splice invariant, interpreted through the full-carrier erasure. -/
def SpliceSafe (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Config n ψ κ τ) : Prop :=
  B9SpliceTableV10g.SpliceSafeV7g hψ ring (oldConfig C)

/-- Existing old-carrier theorem transfers the recovery guard immediately. -/
theorem no_finalGarbage_of_spliceSafe
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : Config n ψ κ τ)
    (hS : SpliceSafe hψ ring C) (e : Fin n) :
    ¬ FinalGarbage hψ (C e) (C (ring.rightNeighbor e)) := by
  unfold SpliceSafe at hS
  simpa [FinalGarbage, oldConfig, oldCell] using
    (B9ControllerRecovery.no_garbage_of_safe
      hψ ring (oldConfig C) hS e)

/-- “Open/no-write” for the final composition also excludes the *outer* B9
relabel action.  That action is a dependency mutation and is deliberately
quarantined rather than identified with raw `stepB9P`. -/
def SafeOpenNoWriteAt
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (C : Config n ψ κ τ) (e : Fin n) : Prop :=
  SpliceSafe hψ ring C ∧
  R2Coherence.OpenControl (C e).phys ∧
  R2Coherence.OpenControl (C (ring.rightNeighbor e)).phys ∧
  R2Coherence.ProposalNoWrite hψ (by decide : 0 < 2) h2
    (C e).phys (C (ring.rightNeighbor e)).phys ∧
  port.action (C e) (C (ring.rightNeighbor e)) ≠ .relabel

private theorem rowFinal_eq_port_of_no_garbage_no_relabel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ)
    (hg : ¬ FinalGarbage hψ l r)
    (hr : port.action l r ≠ .relabel) :
    rowFinal hψ h2 port l r = port.row l r := by
  classical
  unfold rowFinal finalAction
  rw [if_neg hg]
  cases ha : port.action l r with
  | keep => rfl
  | host => rfl
  | relabel => exact (hr ha).elim

/-- Exact transfer lane used by old B9 safe/open-no-write receipts. -/
theorem stepFinal_eq_stepB9P_of_safe_open_no_write
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (C : Config n ψ κ τ) (e : Fin n)
    (hS : SafeOpenNoWriteAt hψ h2 port ring C e) :
    stepFinal hψ h2 port ring C e =
      B9FullCarrierHost.stepB9P port ring C e := by
  classical
  have hSafe := hS.1
  have hNoRelabel := hS.2.2.2.2
  have hg := no_finalGarbage_of_spliceSafe hψ ring C hSafe e
  by_cases hs : ring.rightNeighbor e = e
  · have hgs : ¬ FinalGarbage hψ (C e) (C e) := by
      simpa only [hs] using hg
    simp [stepFinal, B9FullCarrierHost.stepB9P, hs, hgs]
  · have hr := rowFinal_eq_port_of_no_garbage_no_relabel
      hψ h2 port (C e) (C (ring.rightNeighbor e)) hg hNoRelabel
    simp [stepFinal, B9FullCarrierHost.stepB9P,
      B9FullCarrierHost.rowB9P, hs, hr]

/-- Producer fuel observed through both controller layers. -/
def finalFuel (u : Cell ψ κ τ) : WriterProducerRepair.Credit ψ :=
  u.phys.phys.fuel

theorem recoverPair_fuel
    (hψ : 0 < ψ) (l r : Cell ψ κ τ) :
    let q := recoverPair hψ l r
    finalFuel q.1 = finalFuel l ∧ finalFuel q.2 = finalFuel r := by
  classical
  by_cases hL : FinalBadTicket l
  · simp [recoverPair, hL, clearFinalControl, finalFuel]
  · by_cases hR : FinalBadTicket r
    · simp [recoverPair, hL, hR, clearFinalControl, finalFuel]
    · by_cases hB : FinalBadBacking l r
      · simp [recoverPair, hL, hR, hB, clearFinalControl, finalFuel]
      · by_cases hH : FinalHole hψ l r
        · simp [recoverPair, hL, hR, hB, hH, coverFinal, finalFuel]
        · simp [recoverPair, hL, hR, hB, hH, finalFuel]


@[simp] theorem holdRelabelPair_fuel
    (l r : Cell ψ κ τ) :
    finalFuel (holdRelabelPair l r).1 = finalFuel l ∧
      finalFuel (holdRelabelPair l r).2 = finalFuel r := by
  exact ⟨rfl, rfl⟩

private theorem portRow_fuel_of_not_host
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ) (h : port.action l r ≠ .host) :
    let q := port.row l r
    finalFuel q.1 = finalFuel l ∧ finalFuel q.2 = finalFuel r := by
  dsimp only
  change
    (port.row l r).1.phys.phys.fuel = l.phys.phys.fuel ∧
      (port.row l r).2.phys.phys.fuel = r.phys.phys.fuel
  cases ha : port.action l r with
  | keep =>
      have hp := port.physical_spec l r
      simp only [ha] at hp
      exact ⟨
        congrArg (fun u : P ψ κ τ => u.phys.fuel) hp.1,
        congrArg (fun u : P ψ κ τ => u.phys.fuel) hp.2⟩
  | host => exact (h ha).elim
  | relabel =>
      have hp := port.physical_spec l r
      simp only [ha] at hp
      constructor
      · exact congrArg (fun u : P ψ κ τ => u.phys.fuel) hp.1
      · calc
          (port.row l r).2.phys.phys.fuel =
              ((carrierLaws (ψ := ψ) (κ := κ) (τ := τ)).relabel
                hψ l.phys r.phys).phys.fuel :=
            congrArg (fun u : P ψ κ τ => u.phys.fuel) hp.2
          _ = r.phys.phys.fuel := by rfl

/-- Exactly the pair case in which the outer service really calls R2C. -/
def HostCallPair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ) : Prop :=
  ¬ FinalGarbage hψ l r ∧ port.action l r = .host

/-- Pair-level two-clock law: unless the service is a true HOST action, both
producer-fuel coordinates are framed. -/
theorem rowFinal_fuel_of_not_hostCall
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ) (h : ¬ HostCallPair hψ h2 port l r) :
    let q := rowFinal hψ h2 port l r
    finalFuel q.1 = finalFuel l ∧ finalFuel q.2 = finalFuel r := by
  classical
  by_cases hg : FinalGarbage hψ l r
  · have hf := recoverPair_fuel hψ l r
    simpa [rowFinal, finalAction, hg] using hf
  · cases ha : port.action l r with
    | keep =>
        have hf := portRow_fuel_of_not_host hψ h2 port l r (by simp [ha])
        simpa [rowFinal, finalAction, hg, ha] using hf
    | host =>
        exact (h ⟨hg, ha⟩).elim
    | relabel =>
        by_cases hr : RelabelReady l.phys r.phys
        · have hf := portRow_fuel_of_not_host hψ h2 port l r (by simp [ha])
          simpa [rowFinal, finalAction, hg, ha, hr] using hf
        · have hf := holdRelabelPair_fuel l r
          simpa [rowFinal, finalAction, hg, ha, hr] using hf

/-- Scheduler-level HOST predicate. -/
def HostCallAt
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (C : Config n ψ κ τ) (e : Fin n) : Prop :=
  ring.rightNeighbor e ≠ e ∧
    HostCallPair hψ h2 port (C e) (C (ring.rightNeighbor e))

theorem stepFinal_fuel_of_no_host_call
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (C : Config n ψ κ τ) (e : Fin n)
    (h : ¬ HostCallAt hψ h2 port ring C e) (i : Fin n) :
    finalFuel (stepFinal hψ h2 port ring C e i) = finalFuel (C i) := by
  classical
  by_cases hs : ring.rightNeighbor e = e
  · by_cases hg : FinalGarbage hψ (C e) (C e)
    · by_cases hi : i = e
      · simp [stepFinal, hs, hg, B9FullCarrierHost.writeAtP,
          hi, finalFuel, clearFinalControl]
      · simp [stepFinal, hs, hg, B9FullCarrierHost.writeAtP,
          hi, finalFuel, clearFinalControl]
    · simp [stepFinal, hs, hg]
  · have hp : ¬ HostCallPair hψ h2 port
        (C e) (C (ring.rightNeighbor e)) := by
      intro hh
      exact h ⟨hs, hh⟩
    have hf := rowFinal_fuel_of_not_hostCall hψ h2 port
      (C e) (C (ring.rightNeighbor e)) hp
    dsimp only at hf
    by_cases hi : i = e
    · subst i
      simp [stepFinal, hs, B9FullCarrierHost.writeAtP, hf.1]
    · by_cases hj : i = ring.rightNeighbor e
      · simp [stepFinal, hs, B9FullCarrierHost.writeAtP, hj, hf.2]
      · simp [stepFinal, hs, B9FullCarrierHost.writeAtP, hi, hj]


namespace FinalCandidateR2C

open Q11593SpliceControllerDesign
open B9FullCarrierHost

variable {n ψ κ τ : Nat}

/-- Generic lift of the old Q,Q family to the complete R2C carrier. -/
def pendingCell (x : P ψ κ τ) : Cell ψ κ τ :=
  ⟨x, .predecessorArmed, true, false⟩

def allPending (X : Fin n → P ψ κ τ) : Config n ψ κ τ :=
  fun i => pendingCell (X i)

/-- Its old view is literally the certified old pending cell. -/
@[simp] theorem oldCell_pendingCell (x : P ψ κ τ) :
    oldCell (pendingCell x) =
      B9AllPendingFixed.pendingCell x.phys.base := by
  rfl

private theorem pending_not_badTicket (x : P ψ κ τ) :
    ¬ FinalBadTicket (pendingCell x) := by
  intro h
  have hb : (false : Bool) = true := h.1
  cases hb

private theorem pending_badBacking (l r : P ψ κ τ) :
    FinalBadBacking (pendingCell l) (pendingCell r) := by
  change B9ControllerRecovery.BadBacking
    (B9AllPendingFixed.pendingCell l.phys.base)
    (B9AllPendingFixed.pendingCell r.phys.base)
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rintro ⟨hReserved, _⟩
  exact B9AllPendingFixed.pendingCell_not_reserved r.phys.base hReserved

/-- The generic all-pending pair is recognized by the lifted recovery guard,
independently of the physical R2C fields. -/
theorem finalGarbage_pending_pending
    (hψ : 0 < ψ) (l r : P ψ κ τ) :
    FinalGarbage hψ (pendingCell l) (pendingCell r) := by
  exact Or.inl (Or.inr (Or.inr (pending_badBacking l r)))

/-- First recovery service clears the left pending predecessor exactly as in
`B9ControllerRecovery.rowRecover_pending_pending`. -/
theorem recoverPair_pending_pending
    (hψ : 0 < ψ) (l r : P ψ κ τ) :
    recoverPair hψ (pendingCell l) (pendingCell r) =
      (clearFinalControl (pendingCell l), pendingCell r) := by
  classical
  unfold recoverPair
  rw [if_neg (pending_not_badTicket l),
    if_neg (pending_not_badTicket r),
    if_pos (pending_badBacking l r)]

/-- Port-independent local regression: recovery dominates the old fixed row. -/
theorem rowFinal_pending_pending
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (l r : P ψ κ τ) :
    rowFinal hψ h2 port (pendingCell l) (pendingCell r) =
      (clearFinalControl (pendingCell l), pendingCell r) := by
  have hg := finalGarbage_pending_pending hψ l r
  have ha : finalAction hψ h2 port (pendingCell l) (pendingCell r) =
      .recovery := by
    simp [finalAction, hg]
  unfold rowFinal
  rw [ha]
  exact recoverPair_pending_pending hψ l r

/-- Cheap counterexample gate closed: the Q,Q family is not fixed by
`stepFinal` on any scheduler letter, including an aliased self edge. -/
theorem allPending_not_fixed_final
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (X : Fin n → P ψ κ τ) (e : Fin n) :
    stepFinal hψ h2 port ring (allPending X) e ≠ allPending X := by
  classical
  have hstep :
      stepFinal hψ h2 port ring (allPending X) e e =
        clearFinalControl (pendingCell (X e)) := by
    by_cases hs : ring.rightNeighbor e = e
    · have hg := finalGarbage_pending_pending hψ (X e) (X e)
      simp [stepFinal, hs, hg, allPending,
        B9FullCarrierHost.writeAtP]
    · have hr := rowFinal_pending_pending hψ h2 port
        (X e) (X (ring.rightNeighbor e))
      simp [stepFinal, hs, allPending,
        B9FullCarrierHost.writeAtP, hr]
  intro heq
  have hp := congrArg (fun D : Config n ψ κ τ => D e) heq
  rw [hstep] at hp
  have hrole := congrArg (fun u : Cell ψ κ τ => u.spliceRole) hp
  change SpliceRole.none = SpliceRole.predecessorArmed at hrole
  cases hrole

namespace FinalCandidateR2C

open BirthTwoStageEscape
open WriterProducerRepair

variable {n ψ κ τ : Nat}

/-- Physical R2C projection of a final configuration. -/
def physicalConfig (C : Config n ψ κ τ) : R2Coherence.FC n ψ κ τ :=
  fun i => (C i).phys

def FinalCoherent (ring : DirectedRing n) (C : Config n ψ κ τ) : Prop :=
  R2Coherence.CoherentPrefixes ring (physicalConfig C)

def FinalGeometry (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Config n ψ κ τ) : Prop :=
  R2Coherence.AdmittedPostBirthGeometry hψ ring (physicalConfig C)

/-- Final integration leaf: the outer recovery/controller/relabel arbitration
must preserve R2C coherence on the admitted geometry. -/
def FinalCoherencePreservationObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    FinalGeometry hψ ring C → FinalCoherent ring C →
    FinalCoherent ring (stepFinal hψ h2 port ring C e)

/-- Exact coherence gate: the nine already-named R2C branch leaves plus the
outer final-row integration leaf. -/
def CoherenceBranchObligations
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) : Prop :=
  R2Coherence.PreservationObligations
      (κ := κ) (τ := τ) hψ h2 ring ∧
    FinalCoherencePreservationObligation hψ h2 port ring

/-- Neutral outer B9 controller state. -/
def NeutralController (u : Cell ψ κ τ) : Prop :=
  u.spliceRole = .none ∧ u.repairPending = false ∧
    u.acquireTicket = false

/-- Recovery target, now on the full R2C carrier. -/
def FinalRecoveryTarget (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Config n ψ κ τ) : Prop :=
  SpliceSafe hψ ring C ∨ ∀ i : Fin n, NeutralController (C i)

/-- `LDR-B9-CONTROLLER-RECOVERY`: arbitrary-controller first-hit mass on the
exact final scheduler step. -/
def ControllerRecoveryMassObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) : Prop :=
  ∀ C : Config n ψ κ τ,
    let H := 6 * n
    let Q := n ^ H
    Q * avoidCount (stepFinal hψ h2 port ring)
        (fun _ : Config n ψ κ τ => True)
        (FinalRecoveryTarget hψ ring) C H ≤
      (Q - 1) * n ^ H

/-- Output-level leaderless state for the frozen candidate. -/
def FinalLeaderless (C : Config n ψ κ τ) : Prop :=
  ∀ i : Fin n, outputFinal (C i) = false

/-- No live R2 producer on any physical cell. -/
def FinalNoProducer (C : Config n ψ κ τ) : Prop :=
  ∀ i : Fin n,
    WriterProducerRepair.producerActive
      (R2Coherence.raw (C i).phys) = false

/-- Stopped producer lease target: either the first leader already appeared or
all producer fragments have retired. -/
def LeaseTarget (C : Config n ψ κ τ) : Prop :=
  (∃ i : Fin n, outputFinal (C i) = true) ∨ FinalNoProducer C

/-- `LDR-WRITER-PRODUCER-REPAIR` scheduler-time lift.  This is intentionally a
final-step statement: B9 controller letters do not spend producer fuel. -/
def WriterLeaseMassObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) : Prop :=
  ∀ C : Config n ψ κ τ,
    FinalLeaderless C →
    let H := R2.producerRecoveryB n ψ
    2 * avoidCount (stepFinal hψ h2 port ring)
        (fun _ : Config n ψ κ τ => True)
        LeaseTarget C H ≤ n ^ H

/-- All physical quarantine controls are in the exact open/token-free state. -/
def FinalAllOpen (C : Config n ψ κ τ) : Prop :=
  ∀ i : Fin n, R2Coherence.OpenControl (C i).phys

/-- Generic entrance contract for B1/B6/B8 producers: an original-word mass
from the named source to `Entry`, plus an explicit landing law into the
controller/open admission side needed by later transfers. -/
def EntranceLawsObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n)
    (Source Entry : Config n ψ κ τ → Prop) (H Q : Nat) : Prop :=
  0 < Q ∧
  (∀ C : Config n ψ κ τ, Source C →
    Q * avoidCount (stepFinal hψ h2 port ring)
        (fun _ : Config n ψ κ τ => True) Entry C H ≤
      (Q - 1) * n ^ H) ∧
  (∀ C : Config n ψ κ τ, Entry C →
    SpliceSafe hψ ring C ∧ FinalAllOpen C)

/-- Positive success target for the composed B7 branch. -/
def HasLeader (C : Config n ψ κ τ) : Prop :=
  ∃ i : Fin n, outputFinal (C i) = true

/-- `B7`: one composed-step first-leader escape mass, not a separate bare-host
probability. -/
def B7ComposedMassObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n) (Ready : Config n ψ κ τ → Prop)
    (H Q : Nat) : Prop :=
  0 < Q ∧
  ∀ C : Config n ψ κ τ, Ready C ∧ FinalLeaderless C →
    Q * avoidCount (stepFinal hψ h2 port ring)
        (fun _ : Config n ψ κ τ => True) HasLeader C H ≤
      (Q - 1) * n ^ H

/-- No hidden final state was added by the arbitration layer.  Relative to the
old `ExpiringAgentState` carrier the multiplicative coordinates are:
outer B9 = 4*2*2 = 16; R2C control = 4*6 = 24; producer fuel = 4*ψ+1. -/
def StateCountMultiplier (ψ : Nat) : Nat :=
  16 * 24 * (4 * ψ + 1)

/-- `LDR-STATE-BOUND` exact finite-count target once the old physical carrier
cardinality is supplied by the existing finite certificate. -/
def StateCountObligation
    (oldPhysicalCard finalCard : Nat) : Prop :=
  finalCard = StateCountMultiplier ψ * oldPhysicalCard

/-- The freeze checklist for this exact row.  These are named Props, not
assumptions hidden in `stepFinal`; downstream work must discharge them. -/
structure FreezeGates
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (port : Port (κ := κ) (τ := τ) hψ h2)
    (ring : DirectedRing n)
    (Source Entry Ready : Config n ψ κ τ → Prop)
    (entryH entryQ b7H b7Q oldPhysicalCard finalCard : Nat) : Prop where
  coherenceBranches : CoherenceBranchObligations hψ h2 port ring
  controllerRecoveryMass : ControllerRecoveryMassObligation hψ h2 port ring
  writerLease : WriterLeaseMassObligation hψ h2 port ring
  entranceLaws : EntranceLawsObligation hψ h2 port ring
    Source Entry entryH entryQ
  b7ComposedMass : B7ComposedMassObligation hψ h2 port ring
    Ready b7H b7Q
  stateCount : StateCountObligation (ψ := ψ) oldPhysicalCard finalCard

end FinalCandidateR2C

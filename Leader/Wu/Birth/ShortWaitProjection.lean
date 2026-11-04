import Leader.Wu.Birth.ShortWaitDomainWitness

set_option autoImplicit false

namespace BirthShortWaitProjection

open PPLL PPLLRepair
open BirthShortWait BirthShortWaitDomainWitness

/-- Relabel one active-prefix state into the width-sized carrier.  Every field
except the dependent `Fin` label is copied literally. -/
def waitPrefixProject {psi width : Nat} (u : AgentState psi)
    (hu : u.label.val < width) : AgentState width where
  leader := u.leader
  probe := u.probe
  phase := u.phase
  bit := u.bit
  wait := u.wait
  state := u.state
  path := u.path
  reset := u.reset
  carry := u.carry
  count := u.count
  label := ⟨u.label.val, hu⟩
  h_field := u.h_field
  path2 := u.path2
  path3 := u.path3
  path4 := u.path4
  path5 := u.path5
  p := u.p
  p_carry := u.p_carry
  reset_cmd := u.reset_cmd
  echo := u.echo
  signal_B := u.signal_B
  bullet := u.bullet
  shield := u.shield
  write_state := u.write_state
  write := u.write
  last := u.last
  last_set := u.last_set
  last_unset := u.last_unset
  b_carry := u.b_carry
  gen_ws := u.gen_ws
  ws_echo := u.ws_echo
  signal_ws := u.signal_ws

@[simp] theorem waitPrefixProject_label_val {psi width : Nat}
    (u : AgentState psi) (hu : u.label.val < width) :
    (waitPrefixProject u hu).label.val = u.label.val := rfl

@[simp] theorem waitPrefixProject_h_field {psi width : Nat}
    (u : AgentState psi) (hu : u.label.val < width) :
    (waitPrefixProject u hu).h_field = u.h_field := rfl

@[simp] theorem waitPrefixProject_carry {psi width : Nat}
    (u : AgentState psi) (hu : u.label.val < width) :
    (waitPrefixProject u hu).carry = u.carry := rfl

@[simp] theorem waitPrefixProject_reset {psi width : Nat}
    (u : AgentState psi) (hu : u.label.val < width) :
    (waitPrefixProject u hu).reset = u.reset := rfl

@[simp] theorem waitPrefixProject_count {psi width : Nat}
    (u : AgentState psi) (hu : u.label.val < width) :
    (waitPrefixProject u hu).count = u.count := rfl

/-- Label plus exactly the four internal WAIT registers.  This proof view has
no `wait` field, so it cannot erase the distinction between the physical
`psi - 1` movement boundary and the width-sized one. -/
structure WaitKey where
  label : Nat
  h_field : Bool
  carry : Bool
  reset : Bool
  count : Nat
  deriving DecidableEq, Repr

namespace WaitKey

def ofState {psi : Nat} (u : AgentState psi) : WaitKey :=
  ⟨u.label.val, u.h_field, u.carry, u.reset, u.count⟩

def regs (v : WaitKey) : WaitRegs :=
  ⟨v.h_field, v.carry, v.reset, v.count⟩

end WaitKey

def waitKeyPair {psi : Nat} (q : AgentState psi × AgentState psi) :
    WaitKey × WaitKey :=
  (WaitKey.ofState q.1, WaitKey.ofState q.2)

@[simp] theorem WaitKey_of_waitPrefixProject {psi width : Nat}
    (u : AgentState psi) (hu : u.label.val < width) :
    WaitKey.ofState (waitPrefixProject u hu) = WaitKey.ofState u := rfl

/-- The shortened physical stages before Finish. -/
def waitWidthCore {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let q := waitSaturatedPrepare hpsi l r
  let q := waitWidthCarry hwidth hle kappa q.1 q.2
  waitWidthReset hwidth hle q.1 q.2

/-- Published width-sized WAIT stages before Finish. -/
def waitSaturatedCore {width : Nat} (hwidth : 0 < width)
    (kappa : Nat) (l r : AgentState width) :
    AgentState width × AgentState width :=
  let q := waitSaturatedPrepare hwidth l r
  let q := waitSaturatedCarry hwidth kappa q.1 q.2
  waitSaturatedReset hwidth q.1 q.2

/-- Physical Finish can change only `wait`; it frames all four projected
registers even though its movement guard is still `psi - 1`. -/
private theorem waitWidthFinish_regs {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) :
    waitRegsPair (waitWidthFinish hpsi hwidth hle kappa l r) =
      waitRegsPair (l, r) := by
  simp [waitRegsPair, WaitRegs.ofState, waitWidthFinish]

/-- Published Finish likewise frames these four registers. -/
private theorem waitSaturatedFinish_regs {width kappa : Nat}
    (hwidth : 0 < width) (l r : AgentState width) :
    waitRegsPair (waitSaturatedFinish hwidth kappa l r) =
      waitRegsPair (l, r) := by
  simp [waitRegsPair, WaitRegs.ofState, waitSaturatedFinish]

private theorem waitWidth_regs_core {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) :
    waitRegsPair (waitWidth hpsi hwidth hle kappa l r) =
      waitRegsPair (waitWidthCore hpsi hwidth hle kappa l r) := by
  let q0 := waitSaturatedPrepare hpsi l r
  let q1 := waitWidthCarry hwidth hle kappa q0.1 q0.2
  let q2 := waitWidthReset hwidth hle q1.1 q1.2
  change waitRegsPair (waitWidthFinish hpsi hwidth hle kappa q2.1 q2.2) =
    waitRegsPair q2
  exact waitWidthFinish_regs hpsi hwidth hle q2.1 q2.2

private theorem waitSaturated_regs_core {width kappa : Nat}
    (hwidth : 0 < width) (l r : AgentState width) :
    waitRegsPair (waitSaturated hwidth kappa l r) =
      waitRegsPair (waitSaturatedCore hwidth kappa l r) := by
  let q0 := waitSaturatedPrepare hwidth l r
  let q1 := waitSaturatedCarry hwidth kappa q0.1 q0.2
  let q2 := waitSaturatedReset hwidth q1.1 q1.2
  change waitRegsPair (waitSaturatedFinish hwidth kappa q2.1 q2.2) =
    waitRegsPair q2
  exact waitSaturatedFinish_regs hwidth q2.1 q2.2

private theorem waitRegsPair_eq_of_key_eq
    {psi width : Nat}
    {a : AgentState psi × AgentState psi}
    {b : AgentState width × AgentState width}
    (h : waitKeyPair a = waitKeyPair b) :
    waitRegsPair a = waitRegsPair b := by
  have h' := congrArg
    (fun q : WaitKey × WaitKey => (q.1.regs, q.2.regs)) h
  simpa [waitKeyPair, WaitKey.ofState, WaitKey.regs,
    waitRegsPair, WaitRegs.ofState] using h'

/-- Prepare, shortened Carry and shortened Reset have exactly the same label
and four-register semantics as published WAIT on the explicitly relabeled
width-sized inputs.  The active-pair premise is exactly the two supplied label
bounds. -/
private theorem waitCore_key_projection {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi)
    (hl : l.label.val < width) (hr : r.label.val < width) :
    waitKeyPair (waitWidthCore hpsi hwidth hle kappa l r) =
      waitKeyPair
        (waitSaturatedCore hwidth kappa
          (waitPrefixProject l hl) (waitPrefixProject r hr)) := by
  have hw0 : width ≠ 0 := by omega
  by_cases hl0 : l.label.val = 0 <;>
    by_cases hr0 : r.label.val = 0 <;>
      cases hh : l.h_field <;>
        simp [waitWidthCore, waitSaturatedCore, waitKeyPair, WaitKey.ofState,
          waitSaturatedPrepare, waitWidthCarry, waitSaturatedCarry,
          waitWidthReset, waitSaturatedReset, waitPrefixProject,
          activePair, widthTerminal, Fin.ext_iff, hl, hr, hl0, hr0, hh,
          hwidth, hw0]

/-- LDR-BIRTH-SHORT-WAIT-PROJECTION: uniform cross-psi four-register
projection.  No state-carrier equality and no equality of the `wait` field is
asserted.  In particular the physical `waitWidthFinish` movement guard remains
at `psi - 1`. -/
theorem waitWidth_regs_eq_waitSaturated_prefix
    {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi)
    (hl : l.label.val < width) (hr : r.label.val < width) :
    let lp := waitPrefixProject l hl
    let rp := waitPrefixProject r hr
    waitRegsPair (waitWidth hpsi hwidth hle kappa l r) =
      waitRegsPair (waitSaturated hwidth kappa lp rp) := by
  let lp := waitPrefixProject l hl
  let rp := waitPrefixProject r hr
  change waitRegsPair (waitWidth hpsi hwidth hle kappa l r) =
    waitRegsPair (waitSaturated hwidth kappa lp rp)
  calc
    waitRegsPair (waitWidth hpsi hwidth hle kappa l r) =
        waitRegsPair (waitWidthCore hpsi hwidth hle kappa l r) :=
      waitWidth_regs_core hpsi hwidth hle l r
    _ = waitRegsPair (waitSaturatedCore hwidth kappa lp rp) := by
      exact waitRegsPair_eq_of_key_eq
        (waitCore_key_projection hpsi hwidth hle l r hl hr)
    _ = waitRegsPair (waitSaturated hwidth kappa lp rp) :=
      (waitSaturated_regs_core hwidth lp rp).symm

/-- Actual raw root-incoming frame when the initiator is the physical terminal
and therefore outside the shortened active prefix.  Prepare still installs the
root reset/clock state; shortened Carry/Reset import nothing from the tail.
Finish is present but is invisible to these four registers. -/
theorem rootIncoming_regs_frame {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (hlt : width < psi) (l r : AgentState psi)
    (hl : l.label = (⟨psi - 1, by omega⟩ : Fin psi))
    (hr : r.label = (⟨0, hpsi⟩ : Fin psi)) :
    waitRegsPair (waitWidth hpsi hwidth hle kappa l r) =
      (WaitRegs.ofState l,
        { WaitRegs.ofState r with h_field := false, reset := true }) := by
  have hlv : l.label.val = psi - 1 := by
    simpa using congrArg Fin.val hl
  have hrv : r.label.val = 0 := by
    simpa using congrArg Fin.val hr
  have hpm1_ne : psi - 1 ≠ 0 := by
    omega
  have hpm1_not_lt : ¬ psi - 1 < width := by
    omega
  have hw_le_pm1 : width ≤ psi - 1 := by
    omega
  have hw0 : width ≠ 0 := by
    omega
  calc
    waitRegsPair (waitWidth hpsi hwidth hle kappa l r) =
        waitRegsPair (waitWidthCore hpsi hwidth hle kappa l r) :=
      waitWidth_regs_core hpsi hwidth hle l r
    _ = (WaitRegs.ofState l,
        { WaitRegs.ofState r with h_field := false, reset := true }) := by
      simp [waitWidthCore, waitSaturatedPrepare, waitWidthCarry,
        waitWidthReset, activePair, widthTerminal,
        waitRegsPair, WaitRegs.ofState, Fin.ext_iff,
        hlv, hrv, hpm1_ne, hpm1_not_lt, hw_le_pm1, hwidth, hw0]

/-! ## Literal width-one audit -/

/-- Width one itself is not a defect in the active-prefix projection: both
active labels must be zero and the four internal registers still match the
published singleton-width WAIT. -/
def widthOneActiveLeft : AgentState 2 :=
  { waitRowLeft2 with
    label := (0 : Fin 2)
    h_field := true
    carry := true
    reset := true
    count := 1 }

def widthOneActiveRight : AgentState 2 :=
  { waitRowRight2 with
    label := (0 : Fin 2)
    h_field := true
    carry := false
    reset := false
    count := 3 }

theorem widthOne_active_projection_witness :
    waitRegsPair
      (waitWidth (psi := 2) (width := 1)
        (by decide) (by decide) (by decide) 4
        widthOneActiveLeft widthOneActiveRight) =
    waitRegsPair
      (waitSaturated (ψ := 1) (by decide) 4
        (waitPrefixProject widthOneActiveLeft (by decide))
        (waitPrefixProject widthOneActiveRight (by decide))) := by
  decide

/-- For original raw scheduling with `width = 1 < psi`, the real root incoming
pair is not active: physical terminal label one talks to root label zero.  This
witness keeps arbitrary tail carry/reset material and shows the exact register
frame promised by `rootIncoming_regs_frame`. -/
def widthOneRootLeft : AgentState 2 :=
  { waitRowLeft2 with
    label := (1 : Fin 2)
    h_field := true
    carry := true
    reset := true
    count := 2 }

def widthOneRootRight : AgentState 2 :=
  { waitRowRight2 with
    label := (0 : Fin 2)
    h_field := true
    carry := true
    reset := false
    count := 3 }

theorem widthOne_root_incoming_witness :
    waitRegsPair
      (waitWidth (psi := 2) (width := 1)
        (by decide) (by decide) (by decide) 4
        widthOneRootLeft widthOneRootRight) =
      (⟨true, true, true, 2⟩, ⟨false, true, true, 3⟩) := by
  decide

#print axioms waitWidth_regs_eq_waitSaturated_prefix
#print axioms rootIncoming_regs_frame
#print axioms widthOne_active_projection_witness
#print axioms widthOne_root_incoming_witness

end BirthShortWaitProjection

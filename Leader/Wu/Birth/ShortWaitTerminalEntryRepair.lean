import Leader.Wu.Birth.ShortWaitRawRing
import Leader.Wu.Birth.WaitClockMassResetEntry


/-!
# Local inactive-terminal cleanup for shortened WAIT


Frozen Carry/Reset/Finish are not edited.  One new stage clears only the
width-terminal initiator when those frozen Carry/Reset stages would both be
inactive.  The real outside responder and the full-psi Finish remain literal.
-/


namespace BirthShortWaitTerminalEntryRepair


open PPLL PPLLRepair PPLLDomain
open BirthShortWait BirthShortWaitProjection BirthShortWaitDomainWitness
open BirthWaitClockMass
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing
open BirthWaitClockMass.ResetEntry


set_option autoImplicit false
set_option Elab.async false


/-- Exact missing branch.  It changes only two initiator Booleans. -/
def terminalInactiveClear {psi width : Nat}
    (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) : AgentState psi × AgentState psi :=
  if l.label = widthTerminal hwidth hle ∧ ¬ activePair width l r then
    ({ l with carry := false, reset := false }, r)
  else
    (l, r)


/-- Corrected local WAIT row.  Prepare and all three published later stages
are literal; Finish still uses the full-psi movement boundary. -/
def waitWidthEntry {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let q := waitSaturatedPrepare hpsi l r
  let q := terminalInactiveClear hwidth hle q.1 q.2
  let q := waitWidthCarry hwidth hle kappa q.1 q.2
  let q := waitWidthReset hwidth hle q.1 q.2
  waitWidthFinish hpsi hwidth hle kappa q.1 q.2


/-- On the new branch the responder is exactly untouched and no count moves. -/
theorem terminalInactiveClear_exact {psi width : Nat}
    (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi)
    (ht : l.label = widthTerminal hwidth hle)
    (ha : ¬ activePair width l r) :
    terminalInactiveClear hwidth hle l r =
      ({ l with carry := false, reset := false }, r) := by
  simp [terminalInactiveClear, ht, ha]


theorem terminalInactiveClear_count_frame {psi width : Nat}
    (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) :
    let q := terminalInactiveClear hwidth hle l r
    q.1.count = l.count ∧ q.2.count = r.count := by
  simp [terminalInactiveClear]


theorem terminalInactiveClear_eq_self_of_active {psi width : Nat}
    (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) (ha : activePair width l r) :
    terminalInactiveClear hwidth hle l r = (l, r) := by
  unfold terminalInactiveClear
  rw [if_neg (by intro h; exact h.2 ha)]


theorem terminalInactiveClear_eq_self_of_left_clean {psi width : Nat}
    (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) (hc : l.carry = false) (hz : l.reset = false) :
    terminalInactiveClear hwidth hle l r = (l, r) := by
  cases l
  simp_all [terminalInactiveClear]


private theorem prepare_labels {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    (waitSaturatedPrepare hpsi l r).1.label = l.label ∧
      (waitSaturatedPrepare hpsi l r).2.label = r.label := by
  simp [waitSaturatedPrepare]


private theorem prepare_domain {psi kappa : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    (waitSaturatedPrepare hpsi l r).1.inProtocolDomain kappa ∧
      (waitSaturatedPrepare hpsi l r).2.inProtocolDomain kappa := by
  simpa [waitSaturatedPrepare, AgentState.inProtocolDomain] using And.intro hl hr


theorem terminalInactiveClear_inProtocolDomain {psi width kappa : Nat}
    (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    (terminalInactiveClear hwidth hle l r).1.inProtocolDomain kappa ∧
      (terminalInactiveClear hwidth hle l r).2.inProtocolDomain kappa := by
  simpa [terminalInactiveClear, AgentState.inProtocolDomain] using And.intro hl hr


/-- Numeric-domain closure of the corrected local row. -/
theorem waitWidthEntry_inProtocolDomain {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := waitWidthEntry hpsi hwidth hle kappa l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let q0 := waitSaturatedPrepare hpsi l r
  have h0 := prepare_domain hpsi l r hl hr
  let qc := terminalInactiveClear hwidth hle q0.1 q0.2
  have hc := terminalInactiveClear_inProtocolDomain
    (kappa := kappa) hwidth hle q0.1 q0.2 h0.1 h0.2
  let q1 := waitWidthCarry hwidth hle kappa qc.1 qc.2
  have h1 := BirthShortWait.waitWidthCarry_inProtocolDomain
    hwidth hle qc.1 qc.2 hc.1 hc.2
  let q2 := waitWidthReset hwidth hle q1.1 q1.2
  have h2 := BirthShortWait.waitWidthReset_inProtocolDomain
    (kappa := kappa) hwidth hle q1.1 q1.2 h1.1 h1.2
  exact BirthShortWait.waitWidthFinish_inProtocolDomain
    hpsi hwidth hle q2.1 q2.2 h2.1 h2.2


/-- At full width the new stage is unreachable, hence the whole row is exactly
the published `waitSaturated`. -/
theorem waitWidthEntry_full {psi : Nat} (hpsi : 0 < psi)
    (kappa : Nat) (l r : AgentState psi) :
    waitWidthEntry (psi := psi) (width := psi)
        hpsi hpsi (Nat.le_refl psi) kappa l r =
      waitSaturated hpsi kappa l r := by
  rw [← BirthShortWait.waitWidth_full hpsi kappa l r]
  unfold waitWidthEntry BirthShortWait.waitWidth
  dsimp only
  rw [terminalInactiveClear_eq_self_of_active
    hpsi (Nat.le_refl psi) _ _ ⟨(waitSaturatedPrepare hpsi l r).1.label.isLt,
      (waitSaturatedPrepare hpsi l r).2.label.isLt⟩]


/-- Every old active-prefix row is exactly unchanged. -/
theorem waitWidthEntry_eq_old_of_active_labels {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AgentState psi)
    (hl : l.label.val < width) (hr : r.label.val < width) :
    waitWidthEntry hpsi hwidth hle kappa l r =
      BirthShortWait.waitWidth hpsi hwidth hle kappa l r := by
  let q0 := waitSaturatedPrepare hpsi l r
  have hp : q0.1.label = l.label ∧ q0.2.label = r.label := by
    simpa [q0] using prepare_labels hpsi l r
  have ha : activePair width q0.1 q0.2 := by
    unfold activePair
    rw [hp.1, hp.2]
    exact ⟨hl, hr⟩
  have hc := terminalInactiveClear_eq_self_of_active
    hwidth hle q0.1 q0.2 ha
  unfold waitWidthEntry BirthShortWait.waitWidth
  dsimp only
  rw [hc]


private theorem prepare_left_eq_of_nonzero {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) (h0 : l.label ≠ (⟨0, hpsi⟩ : Fin psi)) :
    (waitSaturatedPrepare hpsi l r).1 = l := by
  simp [waitSaturatedPrepare, h0]


/-- This is the exact existing lawful terminal class: a terminal with the two
`Line` cleanup bits already false sees no semantic change, for arbitrary r. -/
theorem waitWidthEntry_eq_old_of_terminal_clean {psi width : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AgentState psi)
    (ht : l.label = widthTerminal (by omega) hle)
    (hc : l.carry = false) (hz : l.reset = false) :
    waitWidthEntry hpsi (by omega) hle kappa l r =
      BirthShortWait.waitWidth hpsi (by omega) hle kappa l r := by
  have h0 : l.label ≠ (⟨0, hpsi⟩ : Fin psi) := by
    intro h
    have hv := congrArg Fin.val (ht.symm.trans h)
    simp [widthTerminal] at hv
    omega
  let q0 := waitSaturatedPrepare hpsi l r
  have hq0 : q0.1 = l := by
    simpa [q0] using prepare_left_eq_of_nonzero hpsi l r h0
  have hc0 : q0.1.carry = false := by rw [hq0]; exact hc
  have hz0 : q0.1.reset = false := by rw [hq0]; exact hz
  have hclear := terminalInactiveClear_eq_self_of_left_clean
    (by omega : 0 < width) hle q0.1 q0.2 hc0 hz0
  unfold waitWidthEntry BirthShortWait.waitWidth
  dsimp only
  rw [hclear]


/-- The actual physical width terminal is cleaned by the corrected row from
arbitrary reset/carry bits and an arbitrary physical responder. -/
theorem waitWidthEntry_terminal_initiator_clear {psi width : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AgentState psi)
    (ht : l.label = widthTerminal (by omega) hle) :
    (waitWidthEntry hpsi (by omega) hle kappa l r).1.reset = false ∧
      (waitWidthEntry hpsi (by omega) hle kappa l r).1.carry = false := by
  have hl : l.label.val < width := by
    rw [ht]
    simp [widthTerminal]
    omega
  by_cases hr : r.label.val < width
  · have heq := waitWidthEntry_eq_old_of_active_labels
      hpsi (by omega : 0 < width) hle kappa l r hl hr
    have hp := waitWidth_regs_eq_waitSaturated_prefix
      (kappa := kappa) hpsi (by omega : 0 < width) hle l r hl hr
    have hL :
        WaitRegs.ofState
            (BirthShortWait.waitWidth hpsi (by omega) hle kappa l r).1 =
          WaitRegs.ofState
            (waitSaturated (by omega : 0 < width) kappa
              (waitPrefixProject l hl) (waitPrefixProject r hr)).1 := by
      simpa [waitRegsPair] using congrArg Prod.fst hp
    have hs := BirthWaitClockMass.ResetEntry.wait_initiator_clear
      (by omega : 0 < width) kappa
      (waitPrefixProject l hl) (waitPrefixProject r hr)
    rw [heq]
    constructor
    · have h := congrArg WaitRegs.reset hL
      exact Eq.trans (by simpa [WaitRegs.ofState] using h) hs.1
    · have h := congrArg WaitRegs.carry hL
      exact Eq.trans (by simpa [WaitRegs.ofState] using h) hs.2
  · have hl0 : l.label ≠ (⟨0, hpsi⟩ : Fin psi) := by
      intro h
      have hv := congrArg Fin.val (ht.symm.trans h)
      simp [widthTerminal] at hv
      omega
    have hr0 : r.label ≠ (⟨0, hpsi⟩ : Fin psi) := by
      intro h
      have hv := congrArg Fin.val h
      change r.label.val = 0 at hv
      omega
    simp [waitWidthEntry, waitSaturatedPrepare, hl0, hr0,
      terminalInactiveClear, ht, activePair, hr,
      waitWidthCarry, waitWidthReset, waitWidthFinish]


/-- Same physical ring and same scheduler letters, now with the corrected row. -/
def entryRawStep {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n → AgentState psi) (e : Fin n) : Fin n → AgentState psi :=
  updatePair C e ((ring hfit).rightNeighbor e)
    (waitWidthEntry hpsi (by omega) hle cap
      (C e) (C ((ring hfit).rightNeighbor e)))


def entryRawRun {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat) :
    (Fin n → AgentState psi) → List (Fin n) → Fin n → AgentState psi
  | C, [] => C
  | C, e :: es =>
      entryRawRun hpsi hw hle hfit cap
        (entryRawStep hpsi hw hle hfit cap C e) es


/-! Target-range obstruction and repaired witness: psi=4, width=2=psi-2, n=4. -/
private def hpsi4 : 0 < 4 := by decide
private def hw2 : 2 ≤ 2 := by decide
private def hle24 : 2 ≤ 4 := by decide
private def hfit24 : 2 < 4 := by decide


private def base4 (i : Fin 4) : AgentState 4 where
  leader := false; probe := false; phase := false; bit := false
  wait := true; state := .none; path := .bot
  reset := false; carry := false; count := 0; label := i; h_field := false
  path2 := none; path3 := none; path4 := none; path5 := none
  p := false; p_carry := false; reset_cmd := false; echo := false
  signal_B := 0; bullet := 0; shield := false
  write_state := .none; write := .none
  last := false; last_set := false; last_unset := false
  b_carry := false; gen_ws := false; ws_echo := false; signal_ws := false


private def badC4 (i : Fin 4) : AgentState 4 :=
  if i.val = 1 then { base4 i with reset := true, carry := true }
  else base4 i


private def badWord4 : List (Fin 4) := entryWord hfit24


private def oldBadRun4 : Fin 4 → AgentState 4 :=
  BirthShortWaitRawRing.rawRun hpsi4 hw2 hle24 hfit24 4 badC4 badWord4


private def fixedRun4 : Fin 4 → AgentState 4 :=
  entryRawRun hpsi4 hw2 hle24 hfit24 4 badC4 badWord4


theorem target_range4 : 2 = 4 - 2 ∧ 4 ≤ 4 := by decide


theorem bad_initial_labels4 (i : Fin 2) :
    (badC4 (site hfit24 i)).label.val = i.val := by
  unfold badC4
  split <;> rfl


theorem badWord4_avoids_rootIncoming : rootIncoming hfit24 ∉ badWord4 := by
  simpa only [badWord4] using entryWord_avoids_rootIncoming hfit24


/-- The published short row still exhibits the obstruction in the requested
psi>=4, width=psi-2 range. -/
theorem old_terminal_still_dirty4 :
    (oldBadRun4 (site hfit24 (Line.last hw2))).reset = true ∧
      (oldBadRun4 (site hfit24 (Line.last hw2))).carry = true := by
  decide


/-- The corrected literal raw run cleans that same physical terminal. -/
theorem repaired_terminal_clear4 :
    (fixedRun4 (site hfit24 (Line.last hw2))).reset = false ∧
      (fixedRun4 (site hfit24 (Line.last hw2))).carry = false := by
  decide


end BirthShortWaitTerminalEntryRepair


#print axioms BirthShortWaitTerminalEntryRepair.terminalInactiveClear_exact
#print axioms BirthShortWaitTerminalEntryRepair.waitWidthEntry_inProtocolDomain
#print axioms BirthShortWaitTerminalEntryRepair.waitWidthEntry_full
#print axioms BirthShortWaitTerminalEntryRepair.waitWidthEntry_eq_old_of_active_labels
#print axioms BirthShortWaitTerminalEntryRepair.waitWidthEntry_eq_old_of_terminal_clean
#print axioms BirthShortWaitTerminalEntryRepair.waitWidthEntry_terminal_initiator_clear
#print axioms BirthShortWaitTerminalEntryRepair.old_terminal_still_dirty4
#print axioms BirthShortWaitTerminalEntryRepair.repaired_terminal_clear4

import Leader.Wu.Birth.ShortWaitTerminalEntryRepair

namespace BirthShortWaitTerminalEntryAudit

open PPLL PPLLRepair
open BirthShortWait
open BirthShortWaitTerminalEntryRepair
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing

set_option autoImplicit false
set_option Elab.async false

/-- Full-state shape of the only added stage: the responder is exact, and the
initiator is either exact or differs only in carry/reset. -/
theorem terminalInactiveClear_shape {psi width : Nat}
    (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) :
    let q := terminalInactiveClear hwidth hle l r
    q.2 = r /\
      (q.1 = l \/ q.1 = { l with carry := false, reset := false }) := by
  dsimp only
  unfold terminalInactiveClear
  split <;> simp

/-- Terminal spoof + an in-prefix responder label: the pair is active, so the
new stage is unreachable.  No other responder fields are constrained. -/
theorem terminalInactiveClear_terminal_inside_noop {psi width : Nat}
    (hw : 2 <= width) (hle : width <= psi)
    (l r : AgentState psi)
    (ht : l.label = widthTerminal (by omega : 0 < width) hle)
    (hr : r.label.val < width) :
    terminalInactiveClear (by omega : 0 < width) hle l r = (l, r) := by
  apply terminalInactiveClear_eq_self_of_active
  constructor
  · rw [ht]
    simp [widthTerminal]
    omega
  · exact hr

/-- Terminal spoof + an out-of-prefix responder label: this is exactly the new
branch, with the complete responder framed. -/
theorem terminalInactiveClear_terminal_outside_exact {psi width : Nat}
    (hw : 2 <= width) (hle : width <= psi)
    (l r : AgentState psi)
    (ht : l.label = widthTerminal (by omega : 0 < width) hle)
    (hr : ¬ (r.label.val < width)) :
    terminalInactiveClear (by omega : 0 < width) hle l r =
      ({ l with carry := false, reset := false }, r) := by
  apply terminalInactiveClear_exact
  · exact ht
  · intro ha
    exact hr ha.2

@[simp] theorem entryRawStep_initiator {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 <= width) (hle : width <= psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n -> AgentState psi) (e : Fin n) :
    entryRawStep hpsi hw hle hfit cap C e e =
      (waitWidthEntry hpsi (by omega : 0 < width) hle cap
        (C e) (C ((ring hfit).rightNeighbor e))).1 := by
  simp [entryRawStep]

/-- Strong outside-edge noninterference.  If the safe initiator is physically
outside the line, neither endpoint of that raw edge is a line site.  This is
full AgentState equality and is independent of every physical label/state. -/
theorem entryRawStep_outside_line_frame {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 <= width) (hle : width <= psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n -> AgentState psi) (e : Fin n)
    (hk : e ≠ rootIncoming hfit) (hout : width <= e.val)
    (i : Fin width) :
    entryRawStep hpsi hw hle hfit cap C e (site hfit i) =
      C (site hfit i) := by
  have hrval := right_of_safe hfit e hk
  have hne : site hfit i ≠ e := by
    intro h
    have hv := congrArg Fin.val h
    have hi := i.isLt
    simp only [site] at hv
    omega
  have hnr : site hfit i ≠ (ring hfit).rightNeighbor e := by
    intro h
    have hv := congrArg Fin.val h
    rw [hrval] at hv
    have hi := i.isLt
    simp only [site] at hv
    omega
  unfold entryRawStep
  rw [updatePair_other C e ((ring hfit).rightNeighbor e)
    (site hfit i) _ hne hnr]

/-- Explicit spoofed-label wrapper: even an outside initiator pretending to be
the shortened terminal cannot affect a line cell.  The real responder is still
completely arbitrary. -/
theorem entryRawStep_outside_spoof_frame {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 <= width) (hle : width <= psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n -> AgentState psi) (e : Fin n)
    (hk : e ≠ rootIncoming hfit) (hout : width <= e.val)
    (_hspoof : (C e).label = widthTerminal (by omega : 0 < width) hle)
    (i : Fin width) :
    entryRawStep hpsi hw hle hfit cap C e (site hfit i) =
      C (site hfit i) := by
  exact entryRawStep_outside_line_frame
    hpsi hw hle hfit cap C e hk hout i

/-- The one safe external edge that does touch the line: its terminal initiator
is cleaned for an arbitrary physical responder. -/
theorem entryRawStep_terminal_clear {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 <= width) (hle : width <= psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n -> AgentState psi)
    (ht : (C (terminalOutgoing hfit)).label =
      widthTerminal (by omega : 0 < width) hle) :
    (entryRawStep hpsi hw hle hfit cap C (terminalOutgoing hfit)
        (terminalOutgoing hfit)).reset = false /\
      (entryRawStep hpsi hw hle hfit cap C (terminalOutgoing hfit)
        (terminalOutgoing hfit)).carry = false := by
  rw [entryRawStep_initiator]
  exact waitWidthEntry_terminal_initiator_clear
    hpsi hw hle cap
    (C (terminalOutgoing hfit))
    (C ((ring hfit).rightNeighbor (terminalOutgoing hfit))) ht

/-- On terminal-outgoing, every nonterminal line cell is exact full-state
framed; only the terminal line site can be changed. -/
theorem entryRawStep_terminal_other_line_frame {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 <= width) (hle : width <= psi)
    (hfit : width < n) (cap : Nat)
    (C : Fin n -> AgentState psi) (i : Fin width)
    (hi : i ≠ BirthWaitClockMass.Line.last hw) :
    entryRawStep hpsi hw hle hfit cap C (terminalOutgoing hfit)
        (site hfit i) = C (site hfit i) := by
  have hne : site hfit i ≠ terminalOutgoing hfit := by
    intro h
    apply hi
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa only [site, terminalOutgoing, BirthWaitClockMass.Line.last] using hv
  have hrval := right_of_safe hfit (terminalOutgoing hfit)
    (terminalOutgoing_ne_rootIncoming hfit hw)
  have hnr : site hfit i ≠
      (ring hfit).rightNeighbor (terminalOutgoing hfit) := by
    intro h
    have hv := congrArg Fin.val h
    rw [hrval] at hv
    have hii := i.isLt
    simp only [site, terminalOutgoing] at hv
    omega
  unfold entryRawStep
  rw [updatePair_other C (terminalOutgoing hfit)
    ((ring hfit).rightNeighbor (terminalOutgoing hfit))
    (site hfit i) _ hne hnr]

/-- Width = psi: every pair is active, so the added stage is unreachable. -/
theorem terminalInactiveClear_full_noop {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    terminalInactiveClear hpsi (Nat.le_refl psi) l r = (l, r) := by
  exact terminalInactiveClear_eq_self_of_active
    hpsi (Nat.le_refl psi) l r
    <| And.intro l.label.isLt r.label.isLt

/-- Pair-level full-width regression, not a host-substitution claim. -/
theorem waitWidthEntry_full_regression {psi : Nat} (hpsi : 0 < psi)
    (cap : Nat) (l r : AgentState psi) :
    waitWidthEntry (psi := psi) (width := psi)
      hpsi hpsi (Nat.le_refl psi) cap l r =
      waitSaturated hpsi cap l r := by
  exact waitWidthEntry_full hpsi cap l r

/-! Cold width-2 boundary: psi=4, width=2=psi-2, n=4. -/
private def hpsi4 : 0 < 4 := by decide
private def hw2 : 2 <= 2 := by decide
private def hle24 : 2 <= 4 := by decide
private def hfit24 : 2 < 4 := by decide

/-- A spoofed terminal-labelled physical outside initiator at site 2 cannot
change either line site 0 or 1; site 3 is its arbitrary real responder. -/
theorem width2_spoofed_outside_line_frame
    (cap : Nat) (C : Fin 4 -> AgentState 4)
    (_hspoof : (C (2 : Fin 4)).label =
      widthTerminal (psi := 4) (width := 2) (by decide) hle24)
    (i : Fin 2) :
    entryRawStep hpsi4 hw2 hle24 hfit24 cap C (2 : Fin 4)
      (site hfit24 i) = C (site hfit24 i) := by
  exact entryRawStep_outside_line_frame
    hpsi4 hw2 hle24 hfit24 cap C (2 : Fin 4)
    (by decide) (by decide) i

/-- Same boundary, now force the spoofed terminal branch itself: if the
responder label is outside the width prefix, only initiator carry/reset change. -/
theorem width2_spoofed_inactive_exact
    (l r : AgentState 4)
    (ht : l.label =
      widthTerminal (psi := 4) (width := 2) (by decide) hle24)
    (hr : 2 <= r.label.val) :
    terminalInactiveClear (psi := 4) (width := 2)
      (by decide) hle24 l r =
      ({ l with carry := false, reset := false }, r) := by
  apply terminalInactiveClear_exact
  · exact ht
  · intro ha
    exact (Nat.not_lt_of_ge hr) ha.2

#print axioms BirthShortWaitTerminalEntryAudit.terminalInactiveClear_shape
#print axioms BirthShortWaitTerminalEntryAudit.entryRawStep_outside_line_frame
#print axioms BirthShortWaitTerminalEntryAudit.entryRawStep_terminal_clear
#print axioms BirthShortWaitTerminalEntryAudit.waitWidthEntry_full_regression
#print axioms BirthShortWaitTerminalEntryAudit.width2_spoofed_inactive_exact

end BirthShortWaitTerminalEntryAudit

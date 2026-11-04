import Leader.Wu.Birth.ShortWaitRawRing
import Leader.Wu.Birth.WaitClockMassResetEntry

/-!
# Counterexample to unconditional short-carrier reset entry

For width < psi, the terminal-outgoing WAIT row need not be active: its real
outside responder may have a physical label outside the width prefix.  Then
shortened Carry/Reset are both identity on that row.  A dirty physical
terminal therefore survives the exact ascending entry word, so it cannot be
packaged as the existing key-coupled lawful `BirthShortWaitRawRing.State`.
-/

namespace BirthShortWaitResetEntry

open PPLL PPLLRepair
open BirthWaitClockMass
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing
open BirthWaitClockMass.ResetEntry

set_option autoImplicit false
set_option Elab.async false

private def hpsi3 : 0 < 3 := by decide
private def hw2 : 2 ≤ 2 := by decide
private def hle23 : 2 ≤ 3 := by decide
private def hfit23 : 2 < 3 := by decide

/-- Local neutral physical carrier; copied field-for-field from the published
`BirthShortWaitDomainWitness.witnessBase`, which is private there. -/
private def base3 (i : Fin 3) : AgentState 3 where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := i
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := 0
  bullet := 0
  shield := false
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

/-- Physical labels are 0,1,2.  Only the width-terminal site 1 starts dirty. -/
private def badC (i : Fin 3) : AgentState 3 :=
  if i.val = 1 then
    { base3 i with reset := true, carry := true }
  else
    base3 i

/-- The exact checked original-width reset-entry word, now fed unchanged to
the short physical raw runner. -/
private def badWord : List (Fin 3) :=
  entryWord hfit23

private def badRun : Fin 3 → AgentState 3 :=
  BirthShortWaitRawRing.rawRun
    hpsi3 hw2 hle23 hfit23 4 badC badWord

theorem bad_initial_labels (i : Fin 2) :
    (badC (site hfit23 i)).label.val = i.val := by
  unfold badC
  split <;> rfl

theorem badWord_avoids_rootIncoming :
    rootIncoming hfit23 ∉ badWord := by
  simpa only [badWord] using
    (entryWord_avoids_rootIncoming hfit23)

theorem badWord_contains_entry :
    (entryWord hfit23).Sublist badWord := by
  simpa only [badWord] using
    (List.Sublist.refl (entryWord hfit23))

/-- The real edge 1 -> 2 sees responder label 2, hence it is not an active
width-two pair.  The preceding edge 0 -> 1 also cannot clear the responder's
old reset/carry.  Therefore the terminal remains dirty after the exact word. -/
theorem terminal_still_dirty :
    (badRun (site hfit23 (Line.last hw2))).reset = true ∧
      (badRun (site hfit23 (Line.last hw2))).carry = true := by
  decide

/-- No existing short raw-ring State can package this actual endpoint, because
its lawful proof line has terminal reset false (and terminal carry false),
while KeyAgree contains those physical fields. -/
theorem no_state_after_entry :
    ¬ ∃ S : BirthShortWaitRawRing.State (psi := 3) hw2 hfit23,
      S.conf = badRun := by
  rintro ⟨S, hS⟩
  have hag := S.agree (Line.last hw2)
  have hz :
      (S.conf (site hfit23 (Line.last hw2))).reset =
        (S.line.cell (Line.last hw2)).reset := by
    unfold BirthShortWaitRawRing.KeyAgree at hag
    have h := congrArg BirthShortWaitProjection.WaitKey.reset hag
    simpa [BirthShortWaitProjection.WaitKey.ofState] using h
  have hphys :
      (S.conf (site hfit23 (Line.last hw2))).reset = true := by
    rw [hS]
    exact terminal_still_dirty.1
  have hline :
      (S.line.cell (Line.last hw2)).reset = false :=
    S.line.reset_clear (Line.last hw2)
  have hbad : true = false := hphys.symm.trans (hz.trans hline)
  simp at hbad

/-- Direct negation of the requested producer shape at one legal parameter
instance.  This is enough to refute a theorem quantified over every
`2 <= width`, `width < n`, and `width <= psi`. -/
theorem requested_specialization_false :
    ¬ (∀ (cap : Nat) (C : Fin 3 → AgentState 3)
        (es : List (Fin 3)),
      (∀ i : Fin 2, (C (site hfit23 i)).label.val = i.val) →
      rootIncoming hfit23 ∉ es →
      (entryWord hfit23).Sublist es →
      ∃ S : BirthShortWaitRawRing.State (psi := 3) hw2 hfit23,
        S.conf =
          BirthShortWaitRawRing.rawRun
            hpsi3 hw2 hle23 hfit23 cap C es) := by
  intro H
  have hS := H 4 badC badWord bad_initial_labels
    badWord_avoids_rootIncoming badWord_contains_entry
  apply no_state_after_entry
  simpa only [badRun] using hS

end BirthShortWaitResetEntry

#print axioms BirthShortWaitResetEntry.bad_initial_labels
#print axioms BirthShortWaitResetEntry.terminal_still_dirty
#print axioms BirthShortWaitResetEntry.no_state_after_entry
#print axioms BirthShortWaitResetEntry.requested_specialization_false

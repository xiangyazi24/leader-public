import Leader.Wu.Birth.ShortWaitTerminalEntryMass


/-!
# Consumer audit for repaired short-WAIT entry mass


Width is fixed to 2 and the physical ring to n=3.  The generic consumer leaves
all physical fields, including reset/carry, unrestricted except for the two
required line-label values.  No new matcher or stochastic estimate is proved.
-/


namespace BirthShortWaitTerminalEntryMassAudit


open PPLL PPLLRepair
open BirthWaitClockMass.RawRing
open BirthShortWaitTerminalEntryRepair


set_option autoImplicit false
set_option Elab.async false


private theorem hw2 : 2 ≤ 2 := by decide
private theorem hle22 : 2 ≤ 2 := by decide
private theorem hfit23 : 2 < 3 := by decide


/-- Direct public-theorem specialization: horizon 6, multiplier 8.
`C` is otherwise arbitrary, so reset/carry fields are not premises. -/
theorem width2_n3_mass {psi : Nat}
    (hle : 2 ≤ psi) (cap : Nat)
    (C : Fin 3 → AgentState psi)
    (hlabel : ∀ i : Fin 2, (C (site hfit23 i)).label.val = i.val) :
    3 ^ 6 ≤
      8 * BirthShortWaitTerminalEntryMass.entryNumerator
        hw2 hle hfit23 cap C 6 := by
  simpa using
    (BirthShortWaitTerminalEntryMass.raw_entry_mass
      (psi := psi) (width := 2) (n := 3)
      hw2 hle hfit23 cap C hlabel)


/-- Exact event scope at width 2, n=3.  The RHS contains only a repaired
`entryRawRun` prefix packaged as `BirthShortWaitRawRing.State`; there is no
whole-word endpoint or TerminalHost/full-host assertion. -/
theorem width2_n3_scope {psi : Nat}
    (hle : 2 ≤ psi) (cap : Nat)
    (C : Fin 3 → AgentState psi) (es : List (Fin 3)) :
    BirthShortWaitTerminalEntryMass.EntryWithin
        hw2 hle hfit23 cap C es ↔
      ∃ pre post, es = pre ++ post ∧
        ∃ S : BirthShortWaitRawRing.State (psi := psi) hw2 hfit23,
          S.conf = entryRawRun (by omega : 0 < psi)
            hw2 hle hfit23 cap C pre := by
  rfl


/-- Public suffix audit: any scheduler tail remains counted; no state at the
end of that tail is asserted. -/
theorem width2_n3_suffix {psi : Nat}
    (hle : 2 ≤ psi) (cap : Nat)
    (C : Fin 3 → AgentState psi) {es : List (Fin 3)}
    (h : BirthShortWaitTerminalEntryMass.EntryWithin
      hw2 hle hfit23 cap C es) (tail : List (Fin 3)) :
    BirthShortWaitTerminalEntryMass.EntryWithin
      hw2 hle hfit23 cap C (es ++ tail) :=
  BirthShortWaitTerminalEntryMass.EntryWithin_append
    hw2 hle hfit23 cap C h tail


/-- Concrete state with deliberately dirty WAIT cleanup bits. -/
private def dirtyCell (q : Fin 2) : AgentState 2 where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := true
  state := .none
  path := .bot
  reset := true
  carry := true
  count := 0
  label := q
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


/-- Positions 0 and 1 have their physical labels; the outside site is arbitrary. -/
def dirty3 (x : Fin 3) : AgentState 2 :=
  if h : x.val < 2 then dirtyCell ⟨x.val, h⟩ else dirtyCell 0


theorem dirty3_labels (i : Fin 2) :
    (dirty3 (site hfit23 i)).label.val = i.val := by
  simp [dirty3, dirtyCell, site, i.isLt]


/-- Both actual line cells violate the would-be clean reset/carry premise. -/
theorem dirty3_line_dirty :
    (dirty3 (site hfit23 (0 : Fin 2))).reset = true ∧
      (dirty3 (site hfit23 (0 : Fin 2))).carry = true ∧
      (dirty3 (site hfit23 (1 : Fin 2))).reset = true ∧
      (dirty3 (site hfit23 (1 : Fin 2))).carry = true := by
  simp [dirty3, dirtyCell, site]


/-- The same exact 8-at-6 mass bound applies to the dirty concrete carrier,
directly from the public theorem; no clean-bit hypothesis is inserted. -/
theorem dirty3_mass :
    3 ^ 6 ≤
      8 * BirthShortWaitTerminalEntryMass.entryNumerator
        hw2 hle22 hfit23 2 dirty3 6 := by
  simpa using
    (BirthShortWaitTerminalEntryMass.raw_entry_mass
      (psi := 2) (width := 2) (n := 3)
      hw2 hle22 hfit23 2 dirty3 dirty3_labels)


end BirthShortWaitTerminalEntryMassAudit


#print axioms BirthShortWaitTerminalEntryMassAudit.width2_n3_mass
#print axioms BirthShortWaitTerminalEntryMassAudit.width2_n3_scope
#print axioms BirthShortWaitTerminalEntryMassAudit.width2_n3_suffix
#print axioms BirthShortWaitTerminalEntryMassAudit.dirty3_line_dirty
#print axioms BirthShortWaitTerminalEntryMassAudit.dirty3_mass

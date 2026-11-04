import Leader.Wu.Birth.ShortDoneTerminalLoadBoundScope

namespace BirthShortDoneTerminalLoadBoundEventAudit

open PPLL PPLLResearchFormulation
open BirthShortDoneParticipationBudget
open BirthShortDoneParticipationLoadMass
open BirthShortDoneFixedSiteConsumer
open BirthShortDoneTerminalFixedSite
open BirthShortDoneTerminalLoadBound
open BirthShortDoneTerminalLoadBoundScopeAudit
open FixedSpanRenewalPayload FiniteUniformStoppingTree

set_option autoImplicit false
set_option pp.structureInstances false

private def ring8 : DirectedRing 8 := ⟨by decide⟩

private def terminalRow :
    Local 2 2 2 → Local 2 2 2 → Local 2 2 2 × Local 2 2 2 :=
  BirthShortDoneTerminalHost.row
    (κ := 2) (τ := 2)
    (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)

private def step0 (C : Fin 8 → Local 2 2 2) : Fin 8 → Local 2 2 2 :=
  localStep ring8 terminalRow C (0 : Fin 8)

private def word000 : DetSchedule 8 :=
  [(0 : Fin 8), (0 : Fin 8), (0 : Fin 8)]

/-- The nonzero factorial/binomial factor is purely arithmetic. -/
theorem order3_factor_positive :
    0 < chooseCount 3 3 * 2 ^ 3 := by
  decide

set_option maxRecDepth 32768 in
/-- Literal repaired-host timer trace for the selected site in `mixed8one`.
Only the first two rows are executed here. -/
theorem mixed8one_selected_timer_trace :
    (mixed8one (0 : Fin 8)).stall.val = 2 ∧
      (step0 mixed8one (0 : Fin 8)).stall.val = 1 ∧
      (step0 (step0 mixed8one) (0 : Fin 8)).stall.val = 0 := by
  decide

set_option maxRecDepth 32768 in
/-- The same selected-site trace holds when site 1 is also initially fresh. -/
theorem mixed8two_selected_timer_trace :
    (mixed8two (0 : Fin 8)).stall.val = 2 ∧
      (step0 mixed8two (0 : Fin 8)).stall.val = 1 ∧
      (step0 (step0 mixed8two) (0 : Fin 8)).stall.val = 0 := by
  decide

/-- Actual raw-word event witness for `mixed8one`.  The event stops at the
third zero input; this theorem does not claim that a third expiry occurs. -/
theorem mixed8one_word000_event :
    fixedSiteZeroServiceBit ring8 terminalRow (0 : Fin 8)
      mixed8one word000 = 1 := by
  have ht := mixed8one_selected_timer_trace
  have h0 : (mixed8one (0 : Fin 8)).stall.val ≠ 0 := by omega
  have h1 : (step0 mixed8one (0 : Fin 8)).stall.val ≠ 0 := by omega
  have h2 : (step0 (step0 mixed8one) (0 : Fin 8)).stall.val = 0 := ht.2.2
  dsimp only [step0] at h1 h2
  simpa [word000, fixedSiteZeroServiceBit, step0, h0, h1, h2]

/-- The identical raw scheduler word witnesses the selected-site event in
`mixed8two`; changing only site 1's initial timer does not empty this event. -/
theorem mixed8two_word000_event :
    fixedSiteZeroServiceBit ring8 terminalRow (0 : Fin 8)
      mixed8two word000 = 1 := by
  have ht := mixed8two_selected_timer_trace
  have h0 : (mixed8two (0 : Fin 8)).stall.val ≠ 0 := by omega
  have h1 : (step0 mixed8two (0 : Fin 8)).stall.val ≠ 0 := by omega
  have h2 : (step0 (step0 mixed8two) (0 : Fin 8)).stall.val = 0 := ht.2.2
  dsimp only [step0] at h1 h2
  simpa [word000, fixedSiteZeroServiceBit, step0, h0, h1, h2]

/-- Index zero of the repository's complete raw-word enumeration is the same
literal word used above. -/
private theorem rawWord_zero_eq_word000 :
    rawWord 8 3 (0 : Fin (8 ^ 3)) = word000 := by
  decide

/-- A single indexed term is bounded by the complete `8^3` `ofFn` sum. -/
private theorem zeroIndex_le_ofFn_sum (f : Fin (8 ^ 3) → Nat) :
    f (0 : Fin (8 ^ 3)) ≤ (List.ofFn f).sum := by
  rw [List.ofFn_succ, List.sum_cons]
  omega

/-- Hence any weight of the zero-index raw word is bounded by the exact
complete `wordSum`; no alternative scheduler space is introduced. -/
private theorem rawWord_zero_term_le_wordSum
    (f : List (Fin 8) → Nat) :
    f (rawWord 8 3 (0 : Fin (8 ^ 3))) ≤ wordSum 8 3 f := by
  rw [← rawWord_sum 8 3 f]
  exact zeroIndex_le_ofFn_sum
    (fun a : Fin (8 ^ 3) => f (rawWord 8 3 a))

/-- Physical event nonemptiness for the exact `mixed8one` numerator. -/
theorem mixed8one_terminal_numerator_positive :
    0 < terminalZeroServiceNumerator
      (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
      ring8 mixed8one (0 : Fin 8) 3 := by
  have h := rawWord_zero_term_le_wordSum (fun w =>
    fixedSiteZeroServiceBit ring8 terminalRow (0 : Fin 8) mixed8one w)
  rw [rawWord_zero_eq_word000, mixed8one_word000_event] at h
  have h1 :
      1 ≤ terminalZeroServiceNumerator
        (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
        ring8 mixed8one (0 : Fin 8) 3 := by
    simpa [terminalZeroServiceNumerator, terminalRow] using h
  omega

/-- Physical event nonemptiness for the same selected site in `mixed8two`. -/
theorem mixed8two_terminal_numerator_positive :
    0 < terminalZeroServiceNumerator
      (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
      ring8 mixed8two (0 : Fin 8) 3 := by
  have h := rawWord_zero_term_le_wordSum (fun w =>
    fixedSiteZeroServiceBit ring8 terminalRow (0 : Fin 8) mixed8two w)
  rw [rawWord_zero_eq_word000, mixed8two_word000_event] at h
  have h1 :
      1 ≤ terminalZeroServiceNumerator
        (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
        ring8 mixed8two (0 : Fin 8) 3 := by
    simpa [terminalZeroServiceNumerator, terminalRow] using h
  omega

/-- Therefore the two-site multiplicity union charge is also genuinely
positive; this is still not an exact union indicator. -/
theorem mixed8two_listed_terminal_mass_positive :
    0 < listedTerminalZeroServiceMass
      (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
      ring8 mixed8two [(0 : Fin 8), (1 : Fin 8)] 3 := by
  have h0 := mixed8two_terminal_numerator_positive
  unfold listedTerminalZeroServiceMass
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero]
  omega

/-- Arithmetic nonzeroness and physical event nonemptiness are distinct facts. -/
theorem factor_and_events_positive :
    0 < chooseCount 3 3 * 2 ^ 3 ∧
      0 < terminalZeroServiceNumerator
        (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
        ring8 mixed8one (0 : Fin 8) 3 ∧
      0 < listedTerminalZeroServiceMass
        (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
        ring8 mixed8two [(0 : Fin 8), (1 : Fin 8)] 3 :=
  ⟨order3_factor_positive, mixed8one_terminal_numerator_positive,
    mixed8two_listed_terminal_mass_positive⟩

#print axioms BirthShortDoneTerminalLoadBoundEventAudit.mixed8one_selected_timer_trace
#print axioms BirthShortDoneTerminalLoadBoundEventAudit.mixed8two_selected_timer_trace
#print axioms BirthShortDoneTerminalLoadBoundEventAudit.mixed8one_word000_event
#print axioms BirthShortDoneTerminalLoadBoundEventAudit.mixed8two_word000_event
#print axioms BirthShortDoneTerminalLoadBoundEventAudit.mixed8one_terminal_numerator_positive
#print axioms BirthShortDoneTerminalLoadBoundEventAudit.mixed8two_terminal_numerator_positive
#print axioms BirthShortDoneTerminalLoadBoundEventAudit.mixed8two_listed_terminal_mass_positive
#print axioms BirthShortDoneTerminalLoadBoundEventAudit.factor_and_events_positive

end BirthShortDoneTerminalLoadBoundEventAudit

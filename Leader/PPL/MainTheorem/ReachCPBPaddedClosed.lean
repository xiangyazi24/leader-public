import Leader.PPL.TokenCompletion.ServiceGeometry
import Leader.PPL.ReachCPB.MismatchHistFreshLiteralRepaired
import Leader.PPL.TokenCompletion.SecondPowerStart
import Leader.PPL.TokenCompletion.FirstPowerBackstep
import Leader.PPL.TokenCompletion.SweepOldOwnerInteracted
import Leader.PPL.ReachCPB.MismatchHistFreshNoEarlyStepRows
import Leader.PPL.ReachCPB.MismatchHistFreshTerminalFinalBit

/-!
The Lemma 4 deterministic core, unconditionally, and the two closed Lemma 16
rows the reach-CPB layer consumes.

`Lemma4TwoSweepServiceGeometry` is proved, so the deterministic core carries
no remaining hypothesis.  The terminal comparison row takes rows A and B
proved and row C from the selected-pass birth view; the canonical no-early
completion-ID invariant follows from its proved one-step history row.

P_PL Theorem 1 cleanup, phase 2: this file absorbed the live declarations of the former
`Theorem1L16PaddedServiceOnly`, `Theorem1L16PaddedTwoLeaves` and
`Theorem1L16PaddedTerminalRows` (names and statements unchanged).  The
L16 padded-bound wrappers of that series served only the old
psi <= log2 n + 1 route and moved to `Leader/Superseded/Theorem1LogWindow/`.
-/

namespace PPL.Convergence.ReachCPB
set_option autoImplicit false

/-- The uniqueness-repaired terminal comparison row, with rows A and B
discharged and row C taken from the selected-pass birth view. -/
theorem lemma16PostEpochFreshTerminalCompareLiteralRowUnique_of_selectedPassBirthView
    (hSelected : Lemma16TerminalSelectedPassBirthViewRow) :
    Lemma16PostEpochFreshTerminalCompareLiteralRowUnique :=
  lemma16PostEpochFreshTerminalCompareLiteralRowUnique_of_localRows
    lemma16TerminalDoneSourceClassUnique_proved
    lemma16TerminalFinalBitMismatchRow_proved
    (lemma16TerminalDetectMismatchBirthRow_of_selectedPassBirthView hSelected)

end PPL.Convergence.ReachCPB

namespace PPL.Convergence.ReachCPB

/-- The canonical no-early completion-ID invariant, unconditionally. -/
theorem lemma16FreshNoEarlyCompletionIdCanon_proved :
    Lemma16FreshNoEarlyCompletionIdCanon :=
  lemma16FreshNoEarlyCompletionIdCanon_proved_of_stepHistoryRow
    lemma16FreshNoEarlyCompletionIdStepHistoryRow_proved

end PPL.Convergence.ReachCPB

namespace PPL

/-- The Lemma 4 deterministic core from the one-block service geometry. -/
theorem lemma4_deterministic_core_of_serviceGeometry
    (hservice : Lemma4TwoSweepServiceGeometry) :
    lemma4_deterministic_core :=
  lemma4_deterministic_core_of_oldRows_service_firstPower_secondPower
    ⟨lemma4SweepOldOwnerInitiatorRow_proved,
      lemma4SweepOldOwnerResponderRow_proved⟩
    hservice
    lemma4HalfPowerFirstPowerInduction_proved
    lemma4HalfPowerSecondPowerInduction_proved

end PPL

namespace PPL

/-- The Lemma 4 deterministic core, unconditionally. -/
theorem lemma4_deterministic_core_proved :
    lemma4_deterministic_core :=
  lemma4_deterministic_core_of_serviceGeometry
    lemma4TwoSweepServiceGeometry_proved

end PPL

#print axioms PPL.lemma4_deterministic_core_proved
#print axioms PPL.lemma4_deterministic_core_of_serviceGeometry
#print axioms PPL.Convergence.ReachCPB.lemma16FreshNoEarlyCompletionIdCanon_proved
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshTerminalCompareLiteralRowUnique_of_selectedPassBirthView

import Leader.PPL.SPLEntry.BuiltPairSelectedWhite
import Leader.PPL.SPLEntry.CompletionCoreAssembly

/-!
# 18.3: the white selected-token frame is proved

`l18PrimeStepSelectedEstablishedTokensWhite` has exactly the type
`L18PrimeSelectedWhiteFrame`. With it the L18 frame row is unconditional, and
the prime Lemma-4 core, the gapped build phase and the scoped forcing word
depend only on the establishment cut `L18PrimeLemma4EstablishmentCutRow`.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false

/-- The white selected-token frame, from the landed white theorem. -/
theorem l18PrimeSelectedWhiteFrame_proved : L18PrimeSelectedWhiteFrame :=
  @l18PrimeStepSelectedEstablishedTokensWhite

/-- The L18 frame row: a prime step keeps every already-built pair. -/
theorem l18PrimeLemma4FrameRow_proved : L18PrimeLemma4FrameRow :=
  l18PrimeLemma4FrameRow_of_whiteFrame l18PrimeSelectedWhiteFrame_proved

/-- The prime Lemma-4 core from the establishment cut alone. -/
theorem l18PrimeLemma4Core_of_cut
    (hCut : L18PrimeLemma4EstablishmentCutRow) : L18PrimeLemma4Core :=
  l18PrimeLemma4Core_of_inputs l18PrimeSelectedWhiteFrame_proved hCut

/-- The scoped forcing word from the establishment cut alone. -/
theorem l18ForcingWordReachesSPLScoped_of_cut
    (hCut : L18PrimeLemma4EstablishmentCutRow) :
    L18ForcingWordReachesSPLScoped :=
  l18ForcingWordReachesSPLScoped_of_inputs l18PrimeSelectedWhiteFrame_proved hCut

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18PrimeSelectedWhiteFrame_proved
#print axioms PPL.Convergence.L18.l18PrimeLemma4FrameRow_proved
#print axioms PPL.Convergence.L18.l18PrimeLemma4Core_of_cut
#print axioms PPL.Convergence.L18.l18ForcingWordReachesSPLScoped_of_cut

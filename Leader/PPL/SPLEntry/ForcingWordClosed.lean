import Leader.PPL.SPLEntry.EstablishmentCutHalves
import Leader.PPL.SPLEntry.HalfWordTokenHalf
import Leader.PPL.SPLEntry.LateTargetBits

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1PPLFromUpto12.lean`, namespace `PPL.Superseded.LogWindow`: `l18PrimeLemma4Core_proved`, `theorem1L18FirstHitPhaseBound_proved`, `theorem1TinyProducerFrom13_proved`, `theorem1WhpUniform_proved`, `theorem1Statement_of_upto12`.
-/

/-!
# P_PL Theorem 1 from the n ≤ 12 producer alone

Both halves of the L18 establishment cut are proved
(`l18PrimeHalfWordTokenHalfRow_proved`, `l18PrimeEstablishmentIdAtCut_proved`),
so the L18 prime Lemma-4 core, the scoped forcing word, the L18 first-hit
bound and the n ≥ 13 tiny producer are unconditional, and `Theorem1Statement`
rests on `Theorem1TinyProducerUpto12` only.
-/

namespace PPL

set_option autoImplicit false

theorem l18PrimeLemma4EstablishmentCutRow_proved :
    PPL.Convergence.L18.L18PrimeLemma4EstablishmentCutRow :=
  PPL.Convergence.L18.l18PrimeLemma4EstablishmentCutRow_of_halves
    PPL.Convergence.L18.l18PrimeHalfWordTokenHalfRow_proved
    PPL.Convergence.L18.l18PrimeEstablishmentIdAtCut_proved

theorem l18ForcingWordReachesSPLScoped_proved :
    PPL.Convergence.L18.L18ForcingWordReachesSPLScoped :=
  PPL.Convergence.L18.l18ForcingWordReachesSPLScoped_of_cut
    l18PrimeLemma4EstablishmentCutRow_proved

end PPL

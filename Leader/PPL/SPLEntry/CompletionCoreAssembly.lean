import Leader.PPL.SPLEntry.PairRowAssembly
import Leader.PPL.SPLEntry.CompletionFrameAdapter
import Leader.PPL.SPLEntry.CompletionCoreRoute
import Leader.PPL.SPLEntry.BuildBlockAdvance
import Leader.PPL.SPLEntry.BuildGappedAssembly
import Leader.PPL.SPLEntry.GappedCompose
import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.SPLEntry.GappedRiskyFlushPhaseScoped

/-!
# L18 prime Lemma-4 core from its two open inputs (board 18.3)

`L18PrimeLemma4Core` (`L18BuildBlockAdvance.lean`) is split by
`l18PrimeLemma4Core_of_rows` (`L18PrimeLemma4Route.lean`) into a frame row and
a current-pair row.  Both rows are reduced here to the same two explicit
inputs:

* `L18PrimeSelectedWhiteFrame` — white selected-token frame;
* `L18PrimeLemma4EstablishmentCutRow` — establishment-cut trace theorem.

The frame row needs only the white frame: the landed assembler
`l18PrimeStepPreservesBuiltPairPrefix_of_frames` is fed with the protected-ID
frame and the landed black selected-token theorem.

Downstream, the core closes the Build block row
(`l18BuildBlockAdvanceRow_of_primeLemma4Core`) and then the gapped Build
phase `L18GappedLemma4BuildPhase` (`l18GappedLemma4BuildPhase_of_rows`).
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

/-- Frame row of the prime Lemma-4 core from the white selected-token frame.
The built-pair one-step leaf is `l18PrimeStepPreservesBuiltPairPrefix_of_frames`
with `hIds := l18PrimeStepProtectedEstablishedIds` and `hSelected` = landed
black theorem ∧ `hWhite`. -/
theorem l18PrimeLemma4FrameRow_of_whiteFrame
    (hWhite : L18PrimeSelectedWhiteFrame) :
    L18PrimeLemma4FrameRow := by
  apply l18PrimeLemma4FrameRow_of_builtPairStep
  intro n psi kappa hn3 hpsi ring root b C e hb hPrefix
  have hIds :=
    l18PrimeStepProtectedEstablishedIds
      hn3 hpsi ring root b C e hb hPrefix
  apply
    l18PrimeStepPreservesBuiltPairPrefix_of_frames
      hn3 hpsi ring root b C e hb hPrefix hIds
  intro seg hseg i hi
  exact
    ⟨l18PrimeStepSelectedEstablishedTokensBlack
        hn3 hpsi ring root b C e hb hPrefix hIds
        seg hseg i hi,
      hWhite
        hn3 hpsi ring root b C e hb hPrefix hIds
        seg hseg i hi⟩

/-- Board 18.3: the prime Lemma-4 core from the white selected-token frame
and the establishment-cut theorem, via `l18PrimeLemma4Core_of_rows`. -/
theorem l18PrimeLemma4Core_of_inputs
    (hWhite : L18PrimeSelectedWhiteFrame)
    (hCut : L18PrimeLemma4EstablishmentCutRow) :
    L18PrimeLemma4Core :=
  l18PrimeLemma4Core_of_rows
    (l18PrimeLemma4FrameRow_of_whiteFrame hWhite)
    (l18PrimeLemma4PairRow_of_cut hWhite hCut)

/-- One step downstream: the gapped Build phase from the same two inputs,
through `l18BuildBlockAdvanceRow_of_primeLemma4Core` and
`l18GappedLemma4BuildPhase_of_rows`. -/
theorem l18GappedLemma4BuildPhase_of_inputs
    (hWhite : L18PrimeSelectedWhiteFrame)
    (hCut : L18PrimeLemma4EstablishmentCutRow) :
    L18GappedLemma4BuildPhase := by
  intro n psi kappa hn3 hpsi ring root C schedule hlemma4
  exact
    l18GappedLemma4BuildPhase_of_rows
      (l18BuildBlockAdvanceRow_of_primeLemma4Core
        (l18PrimeLemma4Core_of_inputs hWhite hCut))
      hn3 hpsi ring root C schedule hlemma4

/-- Two steps downstream: the scoped Lemma-18 forcing bridge, from the same
two inputs plus the proved gapped phases (18.1 root/distance/last, 18.2
risky flush), through `l18ForcingWordReachesSPLScoped_of_gappedPhases`. -/
theorem l18ForcingWordReachesSPLScoped_of_inputs
    (hWhite : L18PrimeSelectedWhiteFrame)
    (hCut : L18PrimeLemma4EstablishmentCutRow) :
    L18ForcingWordReachesSPLScoped :=
  l18ForcingWordReachesSPLScoped_of_gappedPhases
    l18GappedRootResetPhase_proved
    l18GappedDistanceSweepPhase_proved
    l18GappedLastSweepPhase_proved
    l18GappedRiskyFlushPhaseScoped_proved
    (l18GappedLemma4BuildPhase_of_inputs hWhite hCut)

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18PrimeLemma4FrameRow_of_whiteFrame
#print axioms PPL.Convergence.L18.l18PrimeLemma4Core_of_inputs
#print axioms PPL.Convergence.L18.l18GappedLemma4BuildPhase_of_inputs
#print axioms PPL.Convergence.L18.l18ForcingWordReachesSPLScoped_of_inputs

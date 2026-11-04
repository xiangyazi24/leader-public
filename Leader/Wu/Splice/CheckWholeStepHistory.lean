import Leader.Wu.Splice.CheckWholeStep
import Leader.Wu.Comparison.HistoryDoneCarryFrames

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9CheckWholeStep

open PPLL PPLLRepair PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair
open PPLLComparisonHistory

/-- Full local trust on an authorized marked pair. -/
def AuthorizedPairHistoryTrusted {n psi : Nat}
    (q : MarkedAuthorizedAgentState n psi ×
      MarkedAuthorizedAgentState n psi) : Prop :=
  FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
    FullLocalHistoryTrusted q.2.concrete.core q.2.history

/-- Full local trust on a raw marked pair. -/
def RawPairHistoryTrusted {n psi : Nat}
    (q : MarkedAgentState n psi × MarkedAgentState n psi) : Prop :=
  FullLocalHistoryTrusted q.1.concrete q.1.history ∧
    FullLocalHistoryTrusted q.2.concrete q.2.history

/--
The exact bridge missing from `StepHistoryCuts`.

Each implication is supplied by the literal marked whole-row trace across the
unconditional stages lying between two source-join cuts.  This is proof-side
bookkeeping only; none of these fields is protocol state.
-/
structure WholeStepHistoryTrace {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) where
  input :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi
  output :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi
  cuts : StepHistoryCuts n psi

  input_to_gen :
    AuthorizedPairHistoryTrusted input →
      AuthorizedPairHistoryTrusted cuts.genInput

  gen_to_done :
    let q := markedAuthorizedGenCleanEntryWidth
      hpsi hwidth hle kappa cuts.sourcePos
        cuts.genInput.1 cuts.genInput.2
    AuthorizedPairHistoryTrusted q →
      RawPairHistoryTrusted cuts.doneInput

  done_to_check :
    let q := markedDoneCaptureSigMove
      hpsi cuts.doneInput.1 cuts.doneInput.2
    RawPairHistoryTrusted q →
      AuthorizedPairHistoryTrusted cuts.checkInput

  check_to_disappear :
    let q := markedPreserveDoneCheck
      hpsi cuts.checkInput.1 cuts.checkInput.2
    AuthorizedPairHistoryTrusted q →
      RawPairHistoryTrusted cuts.disappearInput

  disappear_to_compare :
    let q := markedDisappear
      hpsi cuts.disappearInput.1 cuts.disappearInput.2
    RawPairHistoryTrusted q →
      AuthorizedPairHistoryTrusted cuts.compareInput

  compare_to_output :
    let q := markedAuthorizedCompareSigActionOne
      hpsi cuts.compareInput.1 cuts.compareInput.2
    AuthorizedPairHistoryTrusted q →
      AuthorizedPairHistoryTrusted output

/--
Once the literal cut-to-cut trace is supplied, the five compiled source-join
lemmas compose directly.  No global B9 certificate predicate is used here.
-/
theorem markedWholeStep_preserves_fullLocalHistoryTrusted
    {n psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat)
    (trace : WholeStepHistoryTrace (n := n) hpsi hwidth hle kappa)
    (hcompat : StepHistoryCompatible
      hpsi hwidth hle kappa trace.cuts)
    (hin : AuthorizedPairHistoryTrusted trace.input) :
    AuthorizedPairHistoryTrusted trace.output := by
  have hGenIn : AuthorizedPairHistoryTrusted trace.cuts.genInput :=
    trace.input_to_gen hin

  let g := markedAuthorizedGenCleanEntryWidth
    hpsi hwidth hle kappa trace.cuts.sourcePos
      trace.cuts.genInput.1 trace.cuts.genInput.2
  have hGen :=
    markedAuthorizedGenCleanEntryWidth_preserves_fullLocalHistoryTrusted
      hpsi hwidth hle kappa trace.cuts.sourcePos
      trace.cuts.genInput.1 trace.cuts.genInput.2
      hGenIn.1 hGenIn.2
      (StepHistoryCompatible.gen
        hpsi hwidth hle kappa trace.cuts hcompat)
  change AuthorizedPairHistoryTrusted g at hGen
  have hDoneIn : RawPairHistoryTrusted trace.cuts.doneInput :=
    trace.gen_to_done hGen

  let d := markedDoneCaptureSigMove
    hpsi trace.cuts.doneInput.1 trace.cuts.doneInput.2
  have hDone :=
    markedDoneCaptureSigMove_preserves_fullLocalHistoryTrusted
      hpsi trace.cuts.doneInput.1 trace.cuts.doneInput.2
      hDoneIn.1.1 hDoneIn.2.1 hDoneIn.1.2 hDoneIn.2.2
      (StepHistoryCompatible.done
        hpsi hwidth hle kappa trace.cuts hcompat)
  change RawPairHistoryTrusted d at hDone
  have hCheckIn : AuthorizedPairHistoryTrusted trace.cuts.checkInput :=
    trace.done_to_check hDone

  let c := markedPreserveDoneCheck
    hpsi trace.cuts.checkInput.1 trace.cuts.checkInput.2
  have hCheck :=
    markedPreserveDoneCheck_preserves_fullLocalHistoryTrusted
      hpsi trace.cuts.checkInput.1 trace.cuts.checkInput.2
      hCheckIn.1 hCheckIn.2
      (StepHistoryCompatible.check
        hpsi hwidth hle kappa trace.cuts hcompat)
  change AuthorizedPairHistoryTrusted c at hCheck
  have hDisappearIn : RawPairHistoryTrusted trace.cuts.disappearInput :=
    trace.check_to_disappear hCheck

  have hDisappearCompat := StepHistoryCompatible.disappear
    hpsi hwidth hle kappa trace.cuts hcompat
  unfold DisappearCompatibleAt at hDisappearCompat
  let a := markedDisappear
    hpsi trace.cuts.disappearInput.1 trace.cuts.disappearInput.2
  have hDisappear :=
    markedDisappear_preserves_fullLocalHistoryTrusted
      hpsi trace.cuts.disappearInput.1 trace.cuts.disappearInput.2
      hDisappearIn.1 hDisappearIn.2 hDisappearCompat
  change RawPairHistoryTrusted a at hDisappear
  have hCompareIn : AuthorizedPairHistoryTrusted trace.cuts.compareInput :=
    trace.disappear_to_compare hDisappear

  let q := markedAuthorizedCompareSigActionOne
    hpsi trace.cuts.compareInput.1 trace.cuts.compareInput.2
  have hCompare :=
    markedAuthorizedCompareSigActionOne_preserves_fullLocalHistoryTrusted
      hpsi trace.cuts.compareInput.1 trace.cuts.compareInput.2
      hCompareIn.1 hCompareIn.2
      (StepHistoryCompatible.compare
        hpsi hwidth hle kappa trace.cuts hcompat)
  change AuthorizedPairHistoryTrusted q at hCompare
  exact trace.compare_to_output hCompare

end B9CheckWholeStep

#print axioms B9CheckWholeStep.markedWholeStep_preserves_fullLocalHistoryTrusted

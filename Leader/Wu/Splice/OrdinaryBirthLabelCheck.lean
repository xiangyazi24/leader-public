import Leader.Wu.Splice.OrdinaryBirthLabelDone
import Leader.Wu.Birth.ShortWait
import Leader.Wu.WallSweep.FiniteIntegration
import Leader.Wu.Birth.GenerationDone

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV8BirthCaseAdapterLabelCheck

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair
open PPLLWallSweepPreCheckResetContracts PPLLCompleteMultiLeaderCleanup
open BirthShortDoneCuts BirthShortDoneTerminalEntryCut
  BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair
open B9SpliceV8LeftLeaderOpaqueBridge
  B9SpliceV8BirthCaseAdapterLabelGen B9SpliceV8BirthCaseAdapterLabelDone

variable {psi width : Nat}

private theorem preserveCheck_labels (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    authLabels (BirthGenerationDone.preserveDoneCheck hpsi l r) = authLabels (l, r) := by
  by_cases hd : l.core.state = .done ∨ r.core.state = .done
  · simp [BirthGenerationDone.preserveDoneCheck, hd, authLabels]
  · have hdl := fun h => hd (Or.inl h); have hdr := fun h => hd (Or.inr h)
    rw [BirthGenerationDone.preserveDoneCheck_of_no_done hpsi l r hdl hdr]
    by_cases ht : l.core.state = .toss ∨ r.core.state = .toss
    · rw [preserveTossCheck_of_toss hpsi l r ht]
    · have htl := fun h => ht (Or.inl h); have htr := fun h => ht (Or.inr h)
      rw [preserveTossCheck_of_no_toss hpsi l r htl htr]
      by_cases hc : l.core.state = .congest ∨ r.core.state = .congest
      · rw [congestGuardCheck_of_congest hpsi l r hc]
      · have hcl := fun h => hc (Or.inl h); have hcr := fun h => hc (Or.inr h)
        rw [congestGuardCheck_of_clear hpsi l r hcl hcr]
        change rawLabels (checkSig hpsi l.core r.core) =
          (l.core.label, r.core.label)
        exact Prod.ext (PPLLVerify.checkSig_labels_eq hpsi l.core r.core).1
          (PPLLVerify.checkSig_labels_eq hpsi l.core r.core).2

theorem throughCheck_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    authLabels (doneThroughCheckEntryWidth hpsi hwidth hle cap l r) =
      authLabels (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let d := doneBeforeCheckEntryWidth hpsi hwidth hle cap l r
  have hd := doneBefore_labels hpsi hwidth hle cap l r
  have hc := preserveCheck_labels hpsi d.1 d.2
  have hs : doneThroughCheckEntryWidth hpsi hwidth hle cap l r =
      BirthGenerationDone.preserveDoneCheck hpsi d.1 d.2 :=
    doneThrough_eq_stages hpsi hwidth hle cap l r
  exact (congrArg authLabels hs).trans (hc.trans hd)

private theorem suppressWidth_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (l r : AgentState psi) :
    rawLabels (BirthShortWait.suppressSigResetKillWidth hpsi hwidth hle l r) = (l.label, r.label) := by
  let p := BirthShortWait.suppressPrefix l r
  have hp : rawLabels p = (l.label, r.label) := by
    let q0 := suppressSigStart l r
    let q0k := (resetKillComparison q0.1, resetKillComparison q0.2)
    let q1 := suppressSigMoveReset q0k.1 q0k.2
    let q1k := (resetKillComparison q1.1, resetKillComparison q1.2)
    have hk : ∀ u : AgentState psi, (resetKillComparison u).label = u.label := by
      intro u; unfold resetKillComparison; split <;> rfl
    have h0 : rawLabels q0 = (l.label, r.label) := by
      unfold q0 rawLabels suppressSigStart; split <;> rfl
    have h0k : rawLabels q0k = rawLabels q0 := Prod.ext (hk q0.1) (hk q0.2)
    have h1 : rawLabels q1 = rawLabels q0k := by
      unfold q1 rawLabels suppressSigMoveReset; split <;> rfl
    have h1k : rawLabels q1k = rawLabels q1 := Prod.ext (hk q1.1) (hk q1.2)
    change rawLabels q1k = (l.label, r.label)
    exact h1k.trans (h1.trans (h0k.trans h0))
  let c := BirthShortWait.shortCountReset hwidth hle p.1 p.2
  let q2 := suppressSigTerminal hpsi c.1 c.2
  let q3 := suppressSigEcho q2.1 q2.2
  have hc : rawLabels c = rawLabels p := by
    unfold c rawLabels BirthShortWait.shortCountReset; split <;> rfl
  have h2 : rawLabels q2 = rawLabels c := by
    unfold q2 rawLabels suppressSigTerminal; split <;> rfl
  have h3 : rawLabels q3 = rawLabels q2 := by
    unfold q3 rawLabels suppressSigEcho; repeat (first | rfl | split)
  have h4 : rawLabels (suppressSigFinish q3.1 q3.2) = rawLabels q3 := by
    unfold rawLabels suppressSigFinish; split <;> rfl
  change rawLabels (suppressSigFinish q3.1 q3.2) = (l.label, r.label)
  exact h4.trans (h3.trans (h2.trans (hc.trans hp)))

/-- The line-274 repair: name the two pair equalities before composing them. -/
theorem beforeWrite_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (l r : AuthorizedAgentState psi) :
    authLabels (beforeWriteWidth hpsi hwidth hle l r) = authLabels (l, r) := by
  let d := authorizedDisappear hpsi l r
  let c := authorizedCompareSigActionOne hpsi d.1 d.2
  have hd := authorizedDisappear_labels_eq hpsi l r
  have hc := compareActionOne_labels hpsi d.1 d.2
  have hdPair : authLabels d = authLabels (l, r) :=
    Prod.ext hd.1 hd.2
  have hcPair : authLabels c = authLabels d :=
    Prod.ext hc.1 hc.2
  have hs : authLabels (authorizedSuppressWidth hpsi hwidth hle c.1 c.2) =
      authLabels c := by
    change rawLabels (BirthShortWait.suppressSigResetKillWidth hpsi hwidth hle c.1.core c.2.core) =
      (c.1.core.label, c.2.core.label)
    exact suppressWidth_labels hpsi hwidth hle c.1.core c.2.core
  change authLabels (authorizedSuppressWidth hpsi hwidth hle c.1 c.2) = authLabels (l, r)
  exact hs.trans (hcPair.trans hdPair)

end B9SpliceV8BirthCaseAdapterLabelCheck

#print axioms B9SpliceV8BirthCaseAdapterLabelCheck.throughCheck_labels
#print axioms B9SpliceV8BirthCaseAdapterLabelCheck.beforeWrite_labels

import Leader.Wu.Birth.ShortDoneTerminalFirstHit
import Leader.Wu.Birth.ShortDoneTerminalBirthSources
import Leader.Wu.Birth.PpsiLeaderCreationSchedule

namespace BirthShortDoneTerminalOrdinaryLabelR1

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
open PPLLWallSweepPreCheckResetContracts PPLLWallSweepNormalResetContract
  PPLLCompleteMultiLeaderCleanup PPLLPpsiLeaderCreationSchedule
open BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitTerminalEntryRepair
  BirthShortDoneCuts BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
  BirthSigMoveDisposalRepair BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
  BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair
  BirthShortDoneTerminalObserver BirthShortDoneTerminalFirstHit
  BirthShortDoneTerminalBirthSources BirthShortDoneTerminalBirthPhysical
  K2BirthDispatcher K2BirthDispatcherDone K2BirthLeaderNormalize
  ExpiringK2Projection BirthStationaryWrite

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi width kappa tau n : Nat}

private def rawLabels (q : AgentState psi × AgentState psi) : Fin psi × Fin psi :=
  (q.1.label, q.2.label)

private def authLabels
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Fin psi × Fin psi :=
  (q.1.core.label, q.2.core.label)

/-- Exact current expiring deletion guards for reaching the ordinary branch. -/
def PreparedOrdinaryOpen (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  deletionActive r0 = false ∧ deletionActive l0 = false

private theorem prepared_label (hpsi : 0 < psi)
    (u : ExpiringAgentState psi kappa tau) :
    (prepareExpiringDisposal hpsi u).core.erase.core.label =
      u.core.core.label := by
  change (prepareBoundedDisposal hpsi u.core).erase.core.label =
    u.core.core.label
  rw [erase_prepareBoundedDisposal]
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

private theorem waitEntry_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AgentState psi) :
    rawLabels (waitWidthEntry hpsi hwidth hle cap l r) = (l.label, r.label) := by
  apply Prod.ext <;>
    simp [rawLabels, waitWidthEntry, waitSaturatedPrepare,
      terminalInactiveClear, waitWidthCarry, waitWidthReset, waitWidthFinish]

private theorem genAfterWait_labels (hpsi : 0 < psi)
    (l r : AgentState psi) :
    rawLabels (genCleanAfterWait hpsi l r) = (l.label, r.label) := by
  let q0 := genSigSaturatedStart hpsi l r
  let q1 := genCleanEmit hpsi q0.1 q0.2
  let q2 := genCleanPropagate hpsi q1.1 q1.2
  have h0 : rawLabels q0 = (l.label, r.label) := by
    unfold q0 rawLabels genSigSaturatedStart
    repeat (first | rfl | split <;> try dsimp only)
  have h1 : rawLabels q1 = rawLabels q0 := by
    unfold q1 rawLabels genCleanEmit
    repeat (first | rfl | split <;> try dsimp only)
  have h2 : rawLabels q2 = rawLabels q1 := by
    unfold q2 rawLabels genCleanPropagate
    repeat (first | rfl | split <;> try dsimp only)
  have h3 :
      rawLabels (genSigSaturatedFinish hpsi q2.1 q2.2) = rawLabels q2 := by
    unfold rawLabels genSigSaturatedFinish
    repeat (first | rfl | split <;> try dsimp only)
  change rawLabels (genSigSaturatedFinish hpsi q2.1 q2.2) =
    (l.label, r.label)
  exact h3.trans (h2.trans (h1.trans h0))

private theorem genEntry_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AgentState psi) :
    rawLabels (genCleanEntryWidth hpsi hwidth hle cap l r) = (l.label, r.label) := by
  let w := waitWidthEntry hpsi hwidth hle cap l r
  have hw := waitEntry_labels hpsi hwidth hle cap l r
  have hg := genAfterWait_labels hpsi w.1 w.2
  change rawLabels (genCleanAfterWait hpsi w.1 w.2) = (l.label, r.label)
  exact hg.trans hw

private theorem generation_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat)
    (l r : AuthorizedAgentState psi) :
    authLabels (generationBeforeMoveEntryWidth hpsi hwidth hle cap l r) =
      authLabels (authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let p := authorizedPPsiLeaderResetProbeWall hpsi l r
  let g := authorizedGenCleanEntryWidth hpsi hwidth hle cap p.1 p.2
  let c := authorizedCleanSig hpsi g.1 g.2
  have hg : authLabels g = authLabels p := by
    change rawLabels (genCleanEntryWidth hpsi hwidth hle cap p.1.core p.2.core) =
      (p.1.core.label, p.2.core.label)
    exact genEntry_labels hpsi hwidth hle cap p.1.core p.2.core
  have hc : authLabels c = authLabels g := by
    change rawLabels (cleanSig hpsi g.1.core g.2.core) =
      (g.1.core.label, g.2.core.label)
    exact Prod.ext (PPLLVerify.cleanSig_labels_eq hpsi g.1.core g.2.core).1
      (PPLLVerify.cleanSig_labels_eq hpsi g.1.core g.2.core).2
  have he : authLabels (authorizedEliminateSig hpsi c.1 c.2) = authLabels c := by
    change rawLabels (eliminateSig hpsi c.1.core c.2.core) =
      (c.1.core.label, c.2.core.label)
    exact Prod.ext (PPLLVerify.eliminateSig_labels_eq hpsi c.1.core c.2.core).1
      (PPLLVerify.eliminateSig_labels_eq hpsi c.1.core c.2.core).2
  change authLabels (authorizedEliminateSig hpsi c.1 c.2) = authLabels p
  exact he.trans (hc.trans hg)

private theorem holdDoneStep1_labels (l r : AgentState psi) :
    rawLabels (holdDoneStep1 l r) = (l.label, r.label) := by
  unfold holdDoneStep1
  split
  · rfl
  · have h := captureStep1_path_and_sender_control l r
    exact Prod.ext h.2.2.2.1 h.2.2.2.2.1

private theorem sigMoveStep2_labels (l r : AgentState psi) :
    rawLabels (sigMoveStep2 l r) = (l.label, r.label) := by
  unfold rawLabels sigMoveStep2
  repeat (first | rfl | split <;> try dsimp only)

private theorem sigMoveStep3_labels (l r : AgentState psi) :
    rawLabels (sigMoveStep3 l r) = (l.label, r.label) := by
  unfold rawLabels sigMoveStep3
  repeat (first | rfl | split <;> try dsimp only)

private theorem sigMoveStep4_labels (l r : AgentState psi) :
    rawLabels (sigMoveStep4 l r) = (l.label, r.label) := by
  unfold rawLabels sigMoveStep4
  repeat (first | rfl | split <;> try dsimp only)

private theorem sigMoveStep5_labels (l r : AgentState psi) :
    rawLabels (sigMoveStep5 l r) = (l.label, r.label) := by
  unfold rawLabels sigMoveStep5
  repeat (first | rfl | split <;> try dsimp only)

private theorem doneTransfers_labels (l r : AgentState psi) :
    rawLabels (doneTransfers l r) = (l.label, r.label) := by
  let q0 := holdDoneStep1 l r
  let q1 := sigMoveStep2 q0.1 q0.2
  let q2 := sigMoveStep3 q1.1 q1.2
  let q3 := sigMoveStep4 q2.1 q2.2
  have h0 := holdDoneStep1_labels l r
  have h1 := sigMoveStep2_labels q0.1 q0.2
  have h2 := sigMoveStep3_labels q1.1 q1.2
  have h3 := sigMoveStep4_labels q2.1 q2.2
  have h4 := sigMoveStep5_labels q3.1 q3.2
  change rawLabels (sigMoveStep5 q3.1 q3.2) = (l.label, r.label)
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

private theorem preclear_labels (hpsi : 0 < psi) (l r : AgentState psi) :
    rawLabels (sigMoveLeaderPreclear hpsi l r) = (l.label, r.label) := by
  unfold rawLabels sigMoveLeaderPreclear incompleteLeftLeaderBoundary clearIfLeader
  repeat (first | rfl | split <;> try dsimp only)

private theorem leaderWall_labels (l r : AgentState psi) :
    rawLabels (comparisonLeaderWall l r) = (l.label, r.label) := by
  unfold rawLabels comparisonLeaderWall clearComparisonSignal
  repeat (first | rfl | split <;> try dsimp only)

private theorem singleUseTail_labels (hpsi : 0 < psi) (l r : AgentState psi) :
    rawLabels (singleUseControlTail hpsi l r) = (l.label, r.label) := by
  let old := sigMoveControlTail hpsi l r
  have hold : rawLabels old = (l.label, r.label) := by
    let l0 := sigMoveApplyControl hpsi l
    let r0 := sigMoveApplyControl hpsi r
    let l1 := if r0.state = .depart then
      if l0.label.val < psi - 1 ∧ l0.state = .CHECK_ready then
        { l0 with state := .depart }
      else l0
    else l0
    have hl1 : l1.label = l0.label := by
      unfold l1
      repeat (first | rfl | split)
    change (l1.label, r0.label) = (l.label, r.label)
    exact Prod.ext
      (hl1.trans (PPLLVerify.sigMoveApplyControl_label_eq hpsi l))
      (PPLLVerify.sigMoveApplyControl_label_eq hpsi r)
  have ht := singleUseControlTail_preserves_departure hpsi l r
  change
    (singleUseControlTail hpsi l r).1.state = old.1.state ∧
      (singleUseControlTail hpsi l r).2.state = old.2.state ∧
      (singleUseControlTail hpsi l r).1.path = old.1.path ∧
      (singleUseControlTail hpsi l r).2.path = old.2.path ∧
      (singleUseControlTail hpsi l r).1.label = old.1.label ∧
      (singleUseControlTail hpsi l r).2.label = old.2.label at ht
  exact (Prod.ext ht.2.2.2.2.1 ht.2.2.2.2.2).trans hold

private theorem doneCapture_labels (hpsi : 0 < psi) (l r : AgentState psi) :
    rawLabels (doneCaptureSigMove hpsi l r) = (l.label, r.label) := by
  let p := sigMoveLeaderPreclear hpsi l r
  let m := doneTransfers p.1 p.2
  let w := comparisonLeaderWall m.1 m.2
  have hp := preclear_labels hpsi l r
  have hm := doneTransfers_labels p.1 p.2
  have hw := leaderWall_labels m.1 m.2
  have ht := singleUseTail_labels hpsi w.1 w.2
  change rawLabels (singleUseControlTail hpsi w.1 w.2) = (l.label, r.label)
  exact ht.trans (hw.trans (hm.trans hp))

private theorem doneMove_labels (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    authLabels (authorizedDoneMove hpsi l r) = authLabels (l, r) := by
  let q := authorizedDoneMove hpsi l r
  have hc := authorizedDoneMove_core hpsi l r
  have hp := congrArg rawLabels hc
  change authLabels q = rawLabels (doneCaptureSigMove hpsi l.core r.core) at hp
  exact hp.trans (doneCapture_labels hpsi l.core r.core)

private theorem sanitizePreCheck_labels (hpsi : 0 < psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authLabels (sanitizeAuthorizedPair hpsi (preCheckResetWall q.1 q.2)) =
      authLabels q := by
  have h := sanitizePreCheckResetWall_peaceViewPair hpsi q
  have hl := congrArg (fun z => z.1.label) h
  have hr := congrArg (fun z => z.2.label) h
  exact Prod.ext hl hr

private theorem doneBefore_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat)
    (l r : AuthorizedAgentState psi) :
    authLabels (doneBeforeCheckEntryWidth hpsi hwidth hle cap l r) =
      authLabels (authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let b := generationBeforeMoveEntryWidth hpsi hwidth hle cap l r
  let m := authorizedDoneMove hpsi b.1 b.2
  have hb := generation_labels hpsi hwidth hle cap l r
  have hm := doneMove_labels hpsi b.1 b.2
  have hs := sanitizePreCheck_labels hpsi m
  change authLabels (sanitizeAuthorizedPair hpsi (preCheckResetWall m.1 m.2)) =
    authLabels (authorizedPPsiLeaderResetProbeWall hpsi l r)
  exact hs.trans (hm.trans hb)

private theorem preserveDoneCheck_labels (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    authLabels (preserveDoneCheck hpsi l r) = authLabels (l, r) := by
  by_cases hd : l.core.state = .done ∨ r.core.state = .done
  · simp [preserveDoneCheck, hd, authLabels]
  · have hdl := fun h => hd (Or.inl h)
    have hdr := fun h => hd (Or.inr h)
    rw [preserveDoneCheck_of_no_done hpsi l r hdl hdr]
    by_cases ht : l.core.state = .toss ∨ r.core.state = .toss
    · rw [preserveTossCheck_of_toss hpsi l r ht]
    · have htl := fun h => ht (Or.inl h)
      have htr := fun h => ht (Or.inr h)
      rw [preserveTossCheck_of_no_toss hpsi l r htl htr]
      by_cases hc : l.core.state = .congest ∨ r.core.state = .congest
      · rw [congestGuardCheck_of_congest hpsi l r hc]
      · have hcl := fun h => hc (Or.inl h)
        have hcr := fun h => hc (Or.inr h)
        rw [congestGuardCheck_of_clear hpsi l r hcl hcr]
        change rawLabels (checkSig hpsi l.core r.core) =
          (l.core.label, r.core.label)
        exact Prod.ext (PPLLVerify.checkSig_labels_eq hpsi l.core r.core).1
          (PPLLVerify.checkSig_labels_eq hpsi l.core r.core).2

private theorem throughCheck_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat)
    (l r : AuthorizedAgentState psi) :
    authLabels (doneThroughCheckEntryWidth hpsi hwidth hle cap l r) =
      authLabels (authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let b := doneBeforeCheckEntryWidth hpsi hwidth hle cap l r
  have hb := doneBefore_labels hpsi hwidth hle cap l r
  have hc := preserveDoneCheck_labels hpsi b.1 b.2
  change authLabels (preserveDoneCheck hpsi b.1 b.2) =
    authLabels (authorizedPPsiLeaderResetProbeWall hpsi l r)
  exact hc.trans hb

private theorem suppressWidth_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (l r : AgentState psi) :
    rawLabels (suppressSigResetKillWidth hpsi hwidth hle l r) =
      (l.label, r.label) := by
  let p := suppressPrefix l r
  have hp : rawLabels p = (l.label, r.label) := by
    let q0 := suppressSigStart l r
    let q0k := (resetKillComparison q0.1, resetKillComparison q0.2)
    let q1 := suppressSigMoveReset q0k.1 q0k.2
    let q1k := (resetKillComparison q1.1, resetKillComparison q1.2)
    have hkill : ∀ u : AgentState psi, (resetKillComparison u).label = u.label := by
      intro u
      unfold resetKillComparison
      split <;> rfl
    have h0 : rawLabels q0 = (l.label, r.label) := by
      unfold q0 rawLabels suppressSigStart
      split <;> rfl
    have h0k : rawLabels q0k = rawLabels q0 :=
      Prod.ext (hkill q0.1) (hkill q0.2)
    have h1 : rawLabels q1 = rawLabels q0k := by
      unfold q1 rawLabels suppressSigMoveReset
      split <;> rfl
    have h1k : rawLabels q1k = rawLabels q1 :=
      Prod.ext (hkill q1.1) (hkill q1.2)
    change rawLabels q1k = (l.label, r.label)
    exact h1k.trans (h1.trans (h0k.trans h0))
  let c := shortCountReset hwidth hle p.1 p.2
  let q2 := suppressSigTerminal hpsi c.1 c.2
  let q3 := suppressSigEcho q2.1 q2.2
  have hc : rawLabels c = rawLabels p := by
    unfold c rawLabels shortCountReset
    split <;> rfl
  have h2 : rawLabels q2 = rawLabels c := by
    unfold q2 rawLabels suppressSigTerminal
    split <;> rfl
  have h3 : rawLabels q3 = rawLabels q2 := by
    unfold q3 rawLabels suppressSigEcho
    repeat (first | rfl | split)
  have h4 : rawLabels (suppressSigFinish q3.1 q3.2) = rawLabels q3 := by
    unfold rawLabels suppressSigFinish
    split <;> rfl
  change rawLabels (suppressSigFinish q3.1 q3.2) = (l.label, r.label)
  exact h4.trans (h3.trans (h2.trans (hc.trans hp)))

private theorem beforeWrite_labels (hpsi : 0 < psi) (hwidth : 0 < width)
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
    change rawLabels (suppressSigResetKillWidth hpsi hwidth hle c.1.core c.2.core) =
      (c.1.core.label, c.2.core.label)
    exact suppressWidth_labels hpsi hwidth hle c.1.core c.2.core
  change authLabels (authorizedSuppressWidth hpsi hwidth hle c.1 c.2) =
    authLabels (l, r)
  exact hs.trans (hcPair.trans hdPair)

attribute [local irreducible] BirthStationaryWrite.stationaryPersistentAuthorizedRow

private theorem stationaryPersistentAuthorizedRow_labels
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authLabels (stationaryPersistentAuthorizedRow hpsi l r) =
      authLabels (l, r) := by
  have hframe := stationaryPersistentAuthorizedRow_frame hpsi l r
  have hl0 := congrArg (fun q => q.1.2.1) hframe
  have hr0 := congrArg (fun q => q.2.2.1) hframe
  have hl :
      (stationaryPersistentAuthorizedRow hpsi l r).1.core.label =
        l.core.label := by
    simpa only [swPair, swView] using hl0
  have hr :
      (stationaryPersistentAuthorizedRow hpsi l r).2.core.label =
        r.core.label := by
    simpa only [swPair, swView] using hr0
  simpa only [authLabels, hl, hr]

private theorem afterCheckMetadataWidth_stage
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    let b := beforeWriteWidth hpsi hwidth hle l r
    afterCheckMetadataWidth hpsi hwidth hle l r =
      stationaryPersistentAuthorizedRow hpsi b.1 b.2 := by
  rfl

private theorem afterCheck_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (l r : AuthorizedAgentState psi) :
    authLabels (afterCheckMetadataWidth hpsi hwidth hle l r) = authLabels (l, r) := by
  let b := beforeWriteWidth hpsi hwidth hle l r
  have hb := beforeWrite_labels hpsi hwidth hle l r
  have hw := stationaryPersistentAuthorizedRow_labels hpsi b.1 b.2
  have hstage :
      afterCheckMetadataWidth hpsi hwidth hle l r =
        stationaryPersistentAuthorizedRow hpsi b.1 b.2 :=
    afterCheckMetadataWidth_stage hpsi hwidth hle l r
  have hs := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      authLabels q) hstage
  exact hs.trans (hw.trans hb)

private theorem markLeaderBirth_authLabels
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authLabels (markLeaderBirth born q) = authLabels q := by
  have h := markLeaderBirth_labels_eq born q
  exact Prod.ext h.1 h.2

private theorem doneOrdinaryMetadataEntryWidth_stage
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi) (cap : Nat)
    (l r : AuthorizedAgentState psi) :
    let c := doneThroughCheckEntryWidth hpsi hwidth hle cap l r
    let q := afterCheckMetadataWidth hpsi hwidth hle c.1 c.2
    doneOrdinaryMetadataEntryWidth hpsi hwidth hle cap l r =
      markLeaderBirth (authBirth l r q) q := by
  rfl

attribute [local irreducible]
  BirthShortDoneCuts.beforeWriteWidth
  BirthShortDoneCuts.afterCheckMetadataWidth
  BirthShortDoneTerminalEntryCut.doneBeforeCheckEntryWidth
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth

private theorem ordinary_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat)
    (l r : AuthorizedAgentState psi) :
    authLabels (doneOrdinaryMetadataEntryWidth hpsi hwidth hle cap l r) =
      authLabels (authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let c := doneThroughCheckEntryWidth hpsi hwidth hle cap l r
  let a := afterCheckMetadataWidth hpsi hwidth hle c.1 c.2
  have hc := throughCheck_labels hpsi hwidth hle cap l r
  have ha := afterCheck_labels hpsi hwidth hle c.1 c.2
  have hm := markLeaderBirth_authLabels (authBirth l r a) a
  have hstage :
      doneOrdinaryMetadataEntryWidth hpsi hwidth hle cap l r =
        markLeaderBirth (authBirth l r a) a :=
    doneOrdinaryMetadataEntryWidth_stage hpsi hwidth hle cap l r
  have hs := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      authLabels q) hstage
  simp only [authLabels] at hs hm ha hc ⊢
  exact hs.trans (hm.trans (ha.trans hc))

private theorem leaders_of_signal
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authSignalPair q = authSignalPair p) :
    q.1.core.leader = p.1.core.leader ∧ q.2.core.leader = p.2.core.leader := by
  exact ⟨congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) h,
    congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) h⟩

private theorem genStart_signal (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genSigSaturatedStart hpsi l r) = signalPair (l, r) := by
  unfold genSigSaturatedStart; split <;> dsimp only <;> split <;> rfl
private theorem genEmit_signal (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genCleanEmit hpsi l r) = signalPair (l, r) := by
  unfold genCleanEmit; repeat (first | rfl | split)
private theorem genProp_signal (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genCleanPropagate hpsi l r) = signalPair (l, r) := by
  unfold genCleanPropagate; repeat (first | rfl | split)
private theorem genFinish_signal (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genSigSaturatedFinish hpsi l r) = signalPair (l, r) := by
  unfold genSigSaturatedFinish; repeat (first | rfl | split)

private theorem before_signal (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    authSignalPair (doneBeforeCheckEntryWidth hpsi hwidth hle cap l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let p := authorizedPPsiLeaderResetProbeWall hpsi l r
  let w := waitWidthEntry hpsi hwidth hle cap p.1.core p.2.core
  let g := authorizedGenCleanEntryWidth hpsi hwidth hle cap p.1 p.2
  have hw := BirthShortDoneTerminalConsumer.waitWidthEntry_signal
    hpsi hwidth hle cap p.1.core p.2.core
  have hgraw : signalPair (genCleanAfterWait hpsi w.1 w.2) = signalPair (w.1, w.2) := by
    unfold genCleanAfterWait
    dsimp only
    rw [genFinish_signal, genProp_signal, genEmit_signal, genStart_signal]
  have hg : authSignalPair g = authSignalPair p := by
    change signalPair (genCleanAfterWait hpsi w.1 w.2) = signalPair (p.1.core, p.2.core)
    exact hgraw.trans hw
  let c := authorizedCleanSig hpsi g.1 g.2
  let b := authorizedEliminateSig hpsi c.1 c.2
  have hb : authSignalPair b = authSignalPair p :=
    (eliminate_signal hpsi c.1 c.2).trans ((clean_signal hpsi g.1 g.2).trans hg)
  let m := authorizedDoneMove hpsi b.1 b.2
  unfold doneBeforeCheckEntryWidth generationBeforeMoveEntryWidth
  exact (authSignalPair_of_peace
    (sanitizePreCheckResetWall_peaceViewPair hpsi m)).trans
      ((authorizedDoneMove_signal hpsi b.1 b.2).trans hb)

private theorem ordinary_signal (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    authSignalPair (doneOrdinaryMetadataEntryWidth hpsi hwidth hle cap l r) =
      authSignalPair (doneThroughCheckEntryWidth hpsi hwidth hle cap l r) := by
  unfold doneOrdinaryMetadataEntryWidth
  dsimp only
  generalize doneThroughCheckEntryWidth hpsi hwidth hle cap l r = c
  exact (markBirth_signal _ _).trans
    (afterCheckMetadataWidth_signal hpsi hwidth hle c.1 c.2)

private theorem pprime_leaders_reach_ordinary
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (cap : Nat) (l r : AuthorizedAgentState psi) :
    let p := authorizedPPsiLeaderResetProbeWall hpsi l r
    let o := doneOrdinaryMetadataEntryWidth hpsi hwidth hle cap l r
    (p.1.core.leader = true -> o.1.core.leader = true) ∧
      (p.2.core.leader = true -> o.2.core.leader = true) := by
  let p := authorizedPPsiLeaderResetProbeWall hpsi l r
  let b := doneBeforeCheckEntryWidth hpsi hwidth hle cap l r
  let o := doneOrdinaryMetadataEntryWidth hpsi hwidth hle cap l r
  have hb0 := leaders_of_signal (before_signal hpsi hwidth hle cap l r)
  have hb : b.1.core.leader = p.1.core.leader ∧
      b.2.core.leader = p.2.core.leader := by
    simpa only [b, p] using hb0
  have hc := preserveDoneCheck_leaders hpsi b.1 b.2
  have ho0 := leaders_of_signal (ordinary_signal hpsi hwidth hle cap l r)
  have ho :
      o.1.core.leader = (preserveDoneCheck hpsi b.1 b.2).1.core.leader ∧
      o.2.core.leader = (preserveDoneCheck hpsi b.1 b.2).2.core.leader := by
    simpa only [o, doneThroughCheckEntryWidth, b] using ho0
  change
    (p.1.core.leader = true -> o.1.core.leader = true) ∧
      (p.2.core.leader = true -> o.2.core.leader = true)
  exact ⟨fun hp => ho.1.trans (hc.1 (hb.1.trans hp)),
    fun hp => ho.2.trans (hc.2 (hb.2.trans hp))⟩

private theorem pprime_labels_of_follower_output
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hout : (authorizedPPsiLeaderResetProbeWall hpsi l r).2.core.leader = false) :
    let p := authorizedPPsiLeaderResetProbeWall hpsi l r
    p.1.core.label = l.core.label ∧
      p.2.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  let p := authorizedPPsiLeaderResetProbeWall hpsi l r
  let z := pPsiLeaderResetProbeWall hpsi l.core r.core
  have hc := authorizedPPsiLeaderResetProbeWall_core hpsi l r
  change (p.1.core, p.2.core) = z at hc
  have hpFollower : z.2.leader = false :=
    (congrArg (fun q : AgentState psi × AgentState psi => q.2.leader) hc).symm.trans hout
  by_cases hs : l.core.reset_cmd = true
  · have hz := pPsiLeaderResetProbeWall_source_follower_normalizes
      hpsi l.core r.core (Or.inr hs) hr
    change z.1.leader = l.core.leader ∧ z.2.leader = false ∧
      z.1.label = l.core.label ∧
      z.2.label = ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ∧
      z.2.probe = false at hz
    exact ⟨(congrArg (fun q : AgentState psi × AgentState psi => q.1.label) hc).trans hz.2.2.1,
      (congrArg (fun q : AgentState psi × AgentState psi => q.2.label) hc).trans hz.2.2.2.1⟩
  · have hz := pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_no_reset
      hpsi l.core r.core (by cases h : l.core.reset_cmd <;> simp_all)
    have hleft := pPsiLeaderProbeWall_initiator_label hpsi l.core r.core
    have hright :=
      pPsiLeaderProbeWall_responder_aligned_of_followers_of_output_follower
        hpsi l.core r.core hl hr (by simpa [z, hz] using hpFollower)
    exact ⟨(congrArg (fun q : AgentState psi × AgentState psi => q.1.label) hc).trans
        (by simpa [z, hz] using hleft),
      (congrArg (fun q : AgentState psi × AgentState psi => q.2.label) hc).trans
        (by simpa [z, hz] using hright)⟩

private theorem expiry_labels_authorized
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let a := doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa pl.core.erase pr.core.erase
    let d := doneMetadataEntryWidth hpsi hwidth hle l r
    d.1.core.core.label = a.1.core.label ∧ d.2.core.core.label = a.2.core.label := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let b := doneMetadataBoundedEntryWidth hpsi hwidth hle pl.core pr.core
  let xL : ExpiringAgentState psi kappa tau := ⟨b.1, pl.stall⟩
  let xR : ExpiringAgentState psi kappa tau := ⟨b.2, pr.stall⟩
  let a := doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa pl.core.erase pr.core.erase
  have he := doneMetadataBoundedEntryWidth_erase hpsi hwidth hle pl.core pr.core
  have hel := congrArg (fun z : AuthorizedAgentState psi => z.core.label)
    (congrArg Prod.fst he)
  have her := congrArg (fun z : AuthorizedAgentState psi => z.core.label)
    (congrArg Prod.snd he)
  change xL.core.erase.core.label = a.1.core.label at hel
  change xR.core.erase.core.label = a.2.core.label at her
  have hl := congrArg (fun z => z.label)
    (deletionPriorityExpireOne_peaceView_frame pl xL)
  have hr := congrArg (fun z => z.label)
    (deletionPriorityExpireOne_peaceView_frame pr xR)
  change (deletionPriorityExpireOne tau pl xL).core.erase.core.label =
    xL.core.erase.core.label at hl
  change (deletionPriorityExpireOne tau pr xR).core.erase.core.label =
    xR.core.erase.core.label at hr
  unfold doneMetadataEntryWidth
  exact ⟨hl.trans hel, hr.trans her⟩

/-- Current ordinary physical row: false current birth means the completed row
is leaderless and its labels are exactly the P′ψ refinement. -/
theorem ordinary_row_labels_of_no_birth
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl0 : l.core.core.leader = false) (hr0 : r.core.core.leader = false)
    (hopen : PreparedOrdinaryOpen hpsi l r)
    (hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle l r = false) :
    let q := BirthShortDoneTerminalHost.row hpsi hwidth hle l r
    q.1.core.core.label = l.core.core.label ∧
      q.2.core.core.label =
        ⟨(l.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  let p := authorizedPPsiLeaderResetProbeWall hpsi l0 r0
  let o := doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa l0 r0
  let a := doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa pl.core.erase pr.core.erase
  let d := doneMetadataEntryWidth hpsi hwidth hle l r
  let m := BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r
  have hpl : pl.core.erase.core.leader = false := by
    have h := congrArg AgentState.leader (prepareExpiring_signal hpsi l)
    change pl.core.erase.core.leader = l.core.core.leader at h
    exact h.trans hl0
  have hpr : pr.core.erase.core.leader = false := by
    have h := congrArg AgentState.leader (prepareExpiring_signal hpsi r)
    change pr.core.erase.core.leader = r.core.core.leader at h
    exact h.trans hr0
  have hnorm := normalize_pair_signal pl.core.erase pr.core.erase
  have hl : l0.core.leader = false :=
    (congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) hnorm).trans hpl
  have hr : r0.core.leader = false :=
    (congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) hnorm).trans hpr
  have hllabel : l0.core.label = l.core.core.label :=
    (normalizeDeletion_label_eq pl.core.erase).trans (prepared_label hpsi l)
  change deletionActive r0 = false ∧ deletionActive l0 = false at hopen
  have ha : a = o := by
    simp [a, o, doneMetadataAuthorizedEntryWidth, l0, r0, hopen.1, hopen.2]
  have hbe := birthEvent_eq_authorized hpsi hwidth hle l r
  have hba : authBirth pl.core.erase pr.core.erase a = false := hbe.symm.trans hb
  have haf : a.1.core.leader = false ∧ a.2.core.leader = false := by
    constructor
    · cases hx : a.1.core.leader with
      | false => rfl
      | true => simp [authBirth, endpointLeaderBorn, hpl, hpr, hx] at hba
    · cases hx : a.2.core.leader with
      | false => rfl
      | true => simp [authBirth, endpointLeaderBorn, hpl, hpr, hx] at hba
  have hof : o.1.core.leader = false ∧ o.2.core.leader = false := by
    rw [← ha]
    exact haf
  have hpersist := pprime_leaders_reach_ordinary hpsi hwidth hle kappa l0 r0
  have hpf : p.1.core.leader = false ∧ p.2.core.leader = false := by
    constructor
    · cases hx : p.1.core.leader with
      | false => rfl
      | true => have hbad := hpersist.1 hx; rw [hof.1] at hbad; contradiction
    · cases hx : p.2.core.leader with
      | false => rfl
      | true => have hbad := hpersist.2 hx; rw [hof.2] at hbad; contradiction
  have hp := pprime_labels_of_follower_output hpsi l0 r0 hl hr hpf.2
  have ho := ordinary_labels hpsi hwidth hle kappa l0 r0
  change authLabels o = authLabels p at ho
  have halabel : a.1.core.label = l.core.core.label ∧
      a.2.core.label =
        ⟨(l.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    rw [ha]
    exact ⟨(congrArg Prod.fst ho).trans (hp.1.trans hllabel),
      (congrArg Prod.snd ho).trans (hp.2.trans (by rw [hllabel]))⟩
  have hdlabel := expiry_labels_authorized hpsi hwidth hle l r
  change d.1.core.core.label = a.1.core.label ∧
    d.2.core.core.label = a.2.core.label at hdlabel
  have hobs := BirthShortDoneTerminalConsumer.doneMetadataEntryWidth_observation
    hpsi hwidth hle l r
  have hdl := congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) hobs
  have hdr := congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) hobs
  change d.1.core.core.leader = a.1.core.leader at hdl
  change d.2.core.core.leader = a.2.core.leader at hdr
  have hdf : d.1.core.core.leader = false ∧ d.2.core.core.leader = false :=
    ⟨hdl.trans haf.1, hdr.trans haf.2⟩
  have hm : m = d := by
    change (normalizeLeader hpsi d.1, normalizeLeader hpsi d.2) = d
    simp [normalizeLeader, hdf.1, hdf.2]
  have hframe := BirthShortDoneTerminalHost.row_metadata_frame
    hpsi hwidth hle l r
  have hfl := congrArg
    (fun z : ExpiringAgentState psi kappa tau => z.core.core.label) hframe.1
  have hfr := congrArg
    (fun z : ExpiringAgentState psi kappa tau => z.core.core.label) hframe.2
  change (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.label =
    m.1.core.core.label at hfl
  change (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.label =
    m.2.core.core.label at hfr
  rw [hm] at hfl hfr
  exact ⟨hfl.trans (hdlabel.1.trans halabel.1),
    hfr.trans (hdlabel.2.trans halabel.2)⟩

/-- One current scheduler edge, with no future assumption: either this row
physically births, or the actual successor is leaderless and has the repaired
ordered labels on the touched edge. -/
theorem ordinary_edge_label_or_physical_birth
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n -> ExpiringAgentState psi kappa tau) (e : Fin n)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hopen : PreparedOrdinaryOpen hpsi (C e) (C (ring.rightNeighbor e))) :
    let D := BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring C e
    (exists i, (D i).core.core.leader = true) \/
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        (D e).core.core.label = (C e).core.core.label ∧
        (D (ring.rightNeighbor e)).core.core.label =
          ⟨((C e).core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) := by
  let D := BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring C e
  cases hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) with
  | true =>
      exact Or.inl
        (BirthShortDoneTerminalBirthPhysical.birthEvent_true_step_has_physical_leader_of_one_lt
          hpsi hwidth hle ring hn C e hb)
  | false =>
      right
      have hz := BirthShortDoneTerminalFirstHit.step_leaderless_of_no_birth
        hpsi hwidth hle ring C e hzero hb
      have hp := ordinary_row_labels_of_no_birth hpsi hwidth hle
        (C e) (C (ring.rightNeighbor e))
        (hzero e) (hzero (ring.rightNeighbor e)) hopen hb
      have hne := rightNeighbor_ne_self_of_one_lt ring hn e
      have hL : D e =
          (BirthShortDoneTerminalHost.row hpsi hwidth hle
            (C e) (C (ring.rightNeighbor e))).1 := by
        simp only [D, BirthShortDoneTerminalConsumer.step,
          PopulationProtocol.step, BirthShortDoneTerminalConsumer.protocol,
          updatePair, if_true]
      have hR : D (ring.rightNeighbor e) =
          (BirthShortDoneTerminalHost.row hpsi hwidth hle
            (C e) (C (ring.rightNeighbor e))).2 := by
        simp only [D, BirthShortDoneTerminalConsumer.step,
          PopulationProtocol.step, BirthShortDoneTerminalConsumer.protocol,
          updatePair, if_neg hne, if_true]
      refine ⟨hz, ?_, ?_⟩
      · change (D e).core.core.label = (C e).core.core.label
        rw [hL]
        exact hp.1
      · change (D (ring.rightNeighbor e)).core.core.label =
          ⟨((C e).core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
        rw [hR]
        exact hp.2

#print axioms BirthShortDoneTerminalOrdinaryLabelR1.ordinary_row_labels_of_no_birth
#print axioms BirthShortDoneTerminalOrdinaryLabelR1.ordinary_edge_label_or_physical_birth

end BirthShortDoneTerminalOrdinaryLabelR1

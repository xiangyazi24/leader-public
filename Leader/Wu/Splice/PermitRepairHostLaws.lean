import Leader.Wu.Entrance.LocalRulerExceptional
import Leader.Wu.Entrance.WriterSilence
import Leader.Wu.Splice.HostRow

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
open BirthShortDoneCuts BirthShortDoneTerminalEntryCut
  BirthSigMoveDisposalRepair BirthStationaryWrite
open K2BirthDispatcher K2BirthLeaderNormalize ExpiringK2Projection
open B9Host

variable {psi kappa tau width : Nat}

private theorem pprime_left_label
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall
      hpsi l r).1.core.label = l.core.label := by
  have hc := PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall_core
    hpsi l r
  have h := congrArg
    (fun q : AgentState psi × AgentState psi => q.1.label) hc
  change
    (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall
      hpsi l r).1.core.label =
      (PPLLWallSweepRepair.pPsiLeaderResetProbeWall
        hpsi l.core r.core).1.label at h
  apply h.trans
  unfold PPLLWallSweepRepair.pPsiLeaderResetProbeWall
  dsimp only
  exact (PPLLVerify.pPsi_initiator_label_eq hpsi _ _).trans
    (by split <;> rfl)


private theorem authLabels_left
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : B9SpliceV8BirthCaseAdapterLabelGen.authLabels q =
      B9SpliceV8BirthCaseAdapterLabelGen.authLabels p) :
    q.1.core.label = p.1.core.label := by
  have hl := congrArg Prod.fst h
  change q.1.core.label = p.1.core.label at hl
  exact hl

private theorem authSignal_left_leader
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : K2BirthDispatcher.authSignalPair q =
      K2BirthDispatcher.authSignalPair p) :
    q.1.core.leader = p.1.core.leader := by
  have hl := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.1.leader) h
  change q.1.core.leader = p.1.core.leader at hl
  exact hl


private theorem r1_ordinary_left_label
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    (BirthCheckPermitRepair.ordinary
      hpsi hwidth hle kappa l r).1.core.label = l.core.label := by
  have ho := authLabels_left
    (B6LocalRulerE.r1_ordinary_labels_from_check
      hpsi hwidth hle kappa l r)
  have hc := authLabels_left
    (B9SpliceV8BirthCaseAdapterLabelCheck.throughCheck_labels
      hpsi hwidth hle kappa l r)
  exact ho.trans (hc.trans (pprime_left_label hpsi l r))



private theorem r1_ordinary_left_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    (BirthCheckPermitRepair.ordinary
      hpsi hwidth hle kappa l r).1.core.leader = l.core.leader := by
  let p := B6WriterSilence.r1WriterInput
    hpsi hwidth hle kappa l r
  let w := stationaryPersistentAuthorizedRow hpsi p.1 p.2

  have hp := B6WriterSilence.r1WriterInput_left_leader
    hpsi hwidth hle kappa l r
  change p.1.core.leader = l.core.leader at hp

  have hw0 := congrArg (fun q => q.1.1)
    (stationaryPersistentAuthorizedRow_frame hpsi p.1 p.2)
  have hw : w.1.core.leader = p.1.core.leader := by
    simpa only [swPair, swView] using hw0

  have hmL := authSignal_left_leader
    (K2BirthDispatcher.markBirth_signal
      (K2BirthDispatcher.authBirth l r w) w)

  have hs :
      BirthCheckPermitRepair.ordinary hpsi hwidth hle kappa l r =
        markLeaderBirth (authBirth l r w) w := by
    simp only [BirthCheckPermitRepair.ordinary,
      afterCheckMetadataWidth, B6WriterSilence.r1WriterInput]
    rfl
  rw [hs]
  exact hmL.trans (hw.trans hp)


private theorem normalized_left_leader
    (l r : AuthorizedAgentState psi) :
    (normalizeDeletion l).core.leader = l.core.leader := by
  have h := K2BirthDispatcher.normalize_pair_signal l r
  exact congrArg
    (fun z : AgentState 1 × AgentState 1 => z.1.leader) h

private theorem r1_authorized_left_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    let a := BirthCheckPermitRepair.authorized
      hpsi hwidth hle kappa l r
    a.1.core.label = l.core.label ∧
      a.1.core.leader = l.core.leader := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hlabel : l0.core.label = l.core.label :=
    B9SpliceV8BirthCaseAdapterLabelProjection.normalizeDeletion_label_local l
  have hleader : l0.core.leader = l.core.leader :=
    normalized_left_leader l r

  unfold BirthCheckPermitRepair.authorized
  dsimp only
  split
  · constructor
    · change (eliminateSig hpsi l0.core r0.core).1.label = l.core.label
      exact (PPLLVerify.eliminateSig_labels_eq
        hpsi l0.core r0.core).1.trans hlabel
    · change (eliminateSig hpsi l0.core r0.core).1.leader = l.core.leader
      exact (PPLLVerify.eliminateSig_leaders_eq
        hpsi l0.core r0.core).1.trans hleader
  · split
    · exact ⟨hlabel, hleader⟩
    · exact
        ⟨(r1_ordinary_left_label
            (kappa := kappa) hpsi hwidth hle l0 r0).trans hlabel,
          (r1_ordinary_left_leader
            (kappa := kappa) hpsi hwidth hle l0 r0).trans hleader⟩

private theorem r1_bounded_erase
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    ((BirthCheckPermitRepair.bounded hpsi hwidth hle l r).1.erase,
      (BirthCheckPermitRepair.bounded hpsi hwidth hle l r).2.erase) =
      BirthCheckPermitRepair.authorized
        hpsi hwidth hle kappa l.erase r.erase := by
  unfold BirthCheckPermitRepair.bounded
  simp only [AuthorizedBoundedAgentState.erase,
    BoundedAgentState.erase_ofDomain]


private theorem r1_bounded_left_label
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    (BirthCheckPermitRepair.bounded
      hpsi hwidth hle l r).1.erase.core.label =
      (BirthCheckPermitRepair.authorized
        hpsi hwidth hle kappa l.erase r.erase).1.core.label := by
  exact congrArg (fun z : AuthorizedAgentState psi => z.core.label)
    (congrArg Prod.fst (r1_bounded_erase hpsi hwidth hle l r))

private theorem r1_bounded_left_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    (BirthCheckPermitRepair.bounded
      hpsi hwidth hle l r).1.erase.core.leader =
      (BirthCheckPermitRepair.authorized
        hpsi hwidth hle kappa l.erase r.erase).1.core.leader := by
  exact congrArg (fun z : AuthorizedAgentState psi => z.core.leader)
    (congrArg Prod.fst (r1_bounded_erase hpsi hwidth hle l r))

private theorem expireOne_left_label
    (old out : ExpiringAgentState psi kappa tau) :
    (deletionPriorityExpireOne tau old out).core.erase.core.label =
      out.core.erase.core.label := by
  have h := congrArg (fun z => z.label)
    (PPLLWallSweepNormalResetContract.deletionPriorityExpireOne_peaceView_frame
      old out)
  change
    (deletionPriorityExpireOne tau old out).core.erase.core.label =
      out.core.erase.core.label at h
  exact h

private theorem expireOne_left_leader
    (old out : ExpiringAgentState psi kappa tau) :
    (deletionPriorityExpireOne tau old out).core.erase.core.leader =
      out.core.erase.core.leader := by
  have h := congrArg (fun z => z.leader)
    (PPLLWallSweepNormalResetContract.deletionPriorityExpireOne_peaceView_frame
      old out)
  change
    (deletionPriorityExpireOne tau old out).core.erase.core.leader =
      out.core.erase.core.leader at h
  exact h


private theorem r1_expiring_left_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let a := BirthCheckPermitRepair.authorized
      hpsi hwidth hle kappa pl.core.erase pr.core.erase
    let d := BirthCheckPermitRepair.expiring hpsi hwidth hle l r
    d.1.core.core.label = a.1.core.label ∧
      d.1.core.core.leader = a.1.core.leader := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let b := BirthCheckPermitRepair.bounded
    hpsi hwidth hle pl.core pr.core
  let xL : ExpiringAgentState psi kappa tau := ⟨b.1, pl.stall⟩

  have hel := r1_bounded_left_label
    hpsi hwidth hle pl.core pr.core
  have heLeader := r1_bounded_left_leader
    hpsi hwidth hle pl.core pr.core
  have hpl := expireOne_left_label pl xL
  have hpLeader := expireOne_left_leader pl xL

  unfold BirthCheckPermitRepair.expiring
  exact ⟨hpl.trans hel, hpLeader.trans heLeader⟩




private theorem r1_row_stage
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    BirthCheckPermitRepair.row hpsi hwidth hle l r =
      K2BirthDispatcher.finalPhysical hpsi l r
        (normalizeLeader hpsi
          (BirthCheckPermitRepair.expiring hpsi hwidth hle l r).1)
        (normalizeLeader hpsi
          (BirthCheckPermitRepair.expiring hpsi hwidth hle l r).2) := by
  rfl

attribute [local irreducible] BirthCheckPermitRepair.row

theorem r1Host_left_follower_label
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : Phys psi kappa tau) :
    B9Host.leader l = false ->
      B9Host.label ((B9Host.r1Host hpsi h2).row l r).1 =
        B9Host.label l := by
  intro hl
  change l.core.core.leader = false at hl
  change
    (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).1.core.core.label =
      l.core.core.label

  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let a := BirthCheckPermitRepair.authorized
    hpsi (by decide : 0 < 2) h2 kappa pl.core.erase pr.core.erase
  let d := BirthCheckPermitRepair.expiring
    hpsi (by decide : 0 < 2) h2 l r

  have hpLabel :=
    B9SpliceV8BirthCaseAdapterLabelProjection.prepared_label_local hpsi l
  change pl.core.erase.core.label = l.core.core.label at hpLabel
  have hpLeader := congrArg AgentState.leader (prepareExpiring_signal hpsi l)
  change pl.core.erase.core.leader = l.core.core.leader at hpLeader

  have ha := r1_authorized_left_frame
    (kappa := kappa) hpsi (by decide : 0 < 2) h2
      pl.core.erase pr.core.erase
  change a.1.core.label = pl.core.erase.core.label ∧
    a.1.core.leader = pl.core.erase.core.leader at ha

  have hd := r1_expiring_left_frame
    (kappa := kappa) (tau := tau)
    hpsi (by decide : 0 < 2) h2 l r
  change d.1.core.core.label = a.1.core.label ∧
    d.1.core.core.leader = a.1.core.leader at hd

  have hdLabel : d.1.core.core.label = l.core.core.label :=
    hd.1.trans (ha.1.trans hpLabel)
  have hdLeader : d.1.core.core.leader = false :=
    hd.2.trans (ha.2.trans (hpLeader.trans hl))

  let mL := normalizeLeader hpsi d.1
  let mR := normalizeLeader hpsi d.2
  have hn : mL.core.core.label = d.1.core.core.label := by
    change (normalizeLeader hpsi d.1).core.core.label = d.1.core.core.label
    simp only [normalizeLeader, hdLeader, Bool.false_eq_true, if_false]

  have hf := K2BirthDispatcher.finalPhysical_nonK2 hpsi l r mL mR
  have hfl := congrArg
    (fun u : ExpiringAgentState psi kappa tau => u.core.core.label) hf.1
  change
    (K2BirthDispatcher.finalPhysical hpsi l r mL mR).1.core.core.label =
      mL.core.core.label at hfl

  have hrow := r1_row_stage
    (kappa := kappa) (tau := tau)
    hpsi (by decide : 0 < 2) h2 l r
  change
    BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r =
      K2BirthDispatcher.finalPhysical hpsi l r mL mR at hrow
  rw [hrow]
  exact hfl.trans (hn.trans hdLabel)

open PPLLVerify PPLLWallSweepPreCheckResetRepair
  PPLLWallSweepPreCheckResetContracts
open BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthSingleUseReleaseRepair
open K2BirthDispatcherDone


private theorem r1rl_pprime_keeps_existing_leaders
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (l.core.leader = true ->
      (authorizedPPsiLeaderResetProbeWall hpsi l r).1.core.leader = true) ∧
    (r.core.leader = true ->
      (authorizedPPsiLeaderResetProbeWall hpsi l r).2.core.leader = true) := by
  constructor
  · intro hl
    change (pPsiLeaderResetProbeWall hpsi l.core r.core).1.leader = true
    rw [pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_left_leader
      hpsi l.core r.core hl]
    unfold pPsiLeaderProbeWall
    dsimp only
    rw [pPsi_initiator_leader_eq]
    simp [hl]
  · intro hr
    change (pPsiLeaderResetProbeWall hpsi l.core r.core).2.leader = true
    rw [pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_right_leader
      hpsi l.core r.core hr]
    exact
      (PPLLWallSweepNormalResetContract.pPsiLeaderProbeWall_responder_frame_of_responder_leader
        hpsi l.core r.core hr).1.trans hr


private theorem r1rl_permitFix_pair_signal
    (c : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authSignalPair (BirthCheckPermitRepair.permitFix c.1, c.2) =
      authSignalPair c := by
  change signalPair
      ((BirthCheckPermitRepair.permitFix c.1).core, c.2.core) =
    signalPair (c.1.core, c.2.core)
  rw [BirthCheckPermitRepair.permitFix_core]


private theorem r1rl_ordinary_signal_from_check
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (cap : Nat) (l r : AuthorizedAgentState psi) :
    authSignalPair
        (BirthCheckPermitRepair.ordinary
          hpsi hwidth hle cap l r) =
      authSignalPair
        (doneThroughCheckEntryWidth hpsi hwidth hle cap l r) := by
  unfold BirthCheckPermitRepair.ordinary
  dsimp only
  generalize doneThroughCheckEntryWidth hpsi hwidth hle cap l r = c
  let f := BirthCheckPermitRepair.permitFix c.1
  let q := afterCheckMetadataWidth hpsi hwidth hle f c.2
  have hf : authSignalPair (f, c.2) = authSignalPair c := by
    simpa only [f] using r1rl_permitFix_pair_signal c
  have hq := afterCheckMetadataWidth_signal hpsi hwidth hle f c.2
  have hm := markBirth_signal (authBirth l r q) q
  change authSignalPair (markLeaderBirth (authBirth l r q) q) =
    authSignalPair c
  exact hm.trans (hq.trans hf)


private theorem r1rl_leaders_of_signal
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authSignalPair q = authSignalPair p) :
    q.1.core.leader = p.1.core.leader ∧
      q.2.core.leader = p.2.core.leader := by
  exact
    ⟨congrArg
        (fun z : AgentState 1 × AgentState 1 => z.1.leader) h,
      congrArg
        (fun z : AgentState 1 × AgentState 1 => z.2.leader) h⟩


private theorem r1rl_genStart_signal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genSigSaturatedStart hpsi l r) = signalPair (l, r) := by
  unfold genSigSaturatedStart
  split <;> dsimp only <;> split <;> rfl


private theorem r1rl_genEmit_signal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genCleanEmit hpsi l r) = signalPair (l, r) := by
  unfold genCleanEmit
  repeat (first | rfl | split)


private theorem r1rl_genProp_signal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genCleanPropagate hpsi l r) = signalPair (l, r) := by
  unfold genCleanPropagate
  repeat (first | rfl | split)


private theorem r1rl_genFinish_signal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genSigSaturatedFinish hpsi l r) = signalPair (l, r) := by
  unfold genSigSaturatedFinish
  repeat (first | rfl | split)


private theorem r1rl_before_signal
    (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat)
    (l r : AuthorizedAgentState psi) :
    authSignalPair
        (doneBeforeCheckEntryWidth hpsi hwidth hle cap l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let p := authorizedPPsiLeaderResetProbeWall hpsi l r
  let w := waitWidthEntry hpsi hwidth hle cap p.1.core p.2.core
  let g := authorizedGenCleanEntryWidth hpsi hwidth hle cap p.1 p.2
  have hw := BirthShortDoneTerminalConsumer.waitWidthEntry_signal
    hpsi hwidth hle cap p.1.core p.2.core
  have hgraw :
      signalPair (genCleanAfterWait hpsi w.1 w.2) =
        signalPair (w.1, w.2) := by
    unfold genCleanAfterWait
    dsimp only
    rw [r1rl_genFinish_signal, r1rl_genProp_signal,
      r1rl_genEmit_signal, r1rl_genStart_signal]
  have hg : authSignalPair g = authSignalPair p := by
    change signalPair (genCleanAfterWait hpsi w.1 w.2) =
      signalPair (p.1.core, p.2.core)
    exact hgraw.trans hw
  let c := authorizedCleanSig hpsi g.1 g.2
  let b := authorizedEliminateSig hpsi c.1 c.2
  have hb : authSignalPair b = authSignalPair p :=
    (eliminate_signal hpsi c.1 c.2).trans
      ((clean_signal hpsi g.1 g.2).trans hg)
  let m := authorizedDoneMove hpsi b.1 b.2
  unfold doneBeforeCheckEntryWidth generationBeforeMoveEntryWidth
  exact
    (authSignalPair_of_peace
      (sanitizePreCheckResetWall_peaceViewPair hpsi m)).trans
        ((authorizedDoneMove_signal hpsi b.1 b.2).trans hb)


private theorem r1rl_pprime_leaders_reach_ordinary
    (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat)
    (l r : AuthorizedAgentState psi) :
    ((authorizedPPsiLeaderResetProbeWall hpsi l r).1.core.leader = true ->
        (BirthCheckPermitRepair.ordinary
          hpsi hwidth hle cap l r).1.core.leader = true) ∧
      ((authorizedPPsiLeaderResetProbeWall hpsi l r).2.core.leader = true ->
        (BirthCheckPermitRepair.ordinary
          hpsi hwidth hle cap l r).2.core.leader = true) := by
  have hb := r1rl_leaders_of_signal
    (r1rl_before_signal hpsi hwidth hle cap l r)
  have ht :=
    B9SpliceV8LeftLeaderOpaqueBridge.doneThrough_eq_stages
      hpsi hwidth hle cap l r
  have ho := r1rl_leaders_of_signal
    (r1rl_ordinary_signal_from_check hpsi hwidth hle cap l r)


  generalize authorizedPPsiLeaderResetProbeWall hpsi l r = p at hb ⊢
  generalize doneBeforeCheckEntryWidth hpsi hwidth hle cap l r = b at hb ht
  generalize doneThroughCheckEntryWidth hpsi hwidth hle cap l r = c at ht ho
  generalize BirthCheckPermitRepair.ordinary
      hpsi hwidth hle cap l r = o at ho ⊢


  dsimp only at ht
  have hc := K2BirthDispatcherDone.preserveDoneCheck_leaders
    hpsi b.1 b.2
  have htL := congrArg
    (fun z : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      z.1.core.leader) ht
  have htR := congrArg
    (fun z : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      z.2.core.leader) ht


  exact
    ⟨fun hp =>
        ho.1.trans (htL.trans (hc.1 (hb.1.trans hp))),
      fun hp =>
        ho.2.trans (htR.trans (hc.2 (hb.2.trans hp)))⟩


private theorem r1rl_normalized_right_leader
    (l r : AuthorizedAgentState psi) :
    (normalizeDeletion r).core.leader = r.core.leader := by
  have h := K2BirthDispatcher.normalize_pair_signal l r
  exact congrArg
    (fun z : AgentState 1 × AgentState 1 => z.2.leader) h


private theorem r1rl_authorized_right_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi)
    (hr : r.core.leader = true) :
    (BirthCheckPermitRepair.authorized
      hpsi hwidth hle kappa l r).2.core.leader = true := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hr0 : r0.core.leader = true :=
    (r1rl_normalized_right_leader l r).trans hr


  unfold BirthCheckPermitRepair.authorized
  dsimp only
  split
  · have he := eliminate_signal hpsi l0 r0
    have heR := congrArg
      (fun z : AgentState 1 × AgentState 1 => z.2.leader) he
    exact heR.trans hr0
  · split
    · exact hr0
    · have hp := r1rl_pprime_keeps_existing_leaders hpsi l0 r0
      have ho := r1rl_pprime_leaders_reach_ordinary
        (cap := kappa) hpsi hwidth hle l0 r0
      exact ho.2 (hp.2 hr0)


private theorem r1rl_bounded_right_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    (BirthCheckPermitRepair.bounded
      hpsi hwidth hle l r).2.erase.core.leader =
      (BirthCheckPermitRepair.authorized
        hpsi hwidth hle kappa l.erase r.erase).2.core.leader := by
  exact congrArg (fun z : AuthorizedAgentState psi => z.core.leader)
    (congrArg Prod.snd (r1_bounded_erase hpsi hwidth hle l r))


private theorem r1rl_expiring_leaders_authorized
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let a := BirthCheckPermitRepair.authorized
      hpsi hwidth hle kappa pl.core.erase pr.core.erase
    let d := BirthCheckPermitRepair.expiring
      hpsi hwidth hle l r
    d.1.core.core.leader = a.1.core.leader ∧
      d.2.core.core.leader = a.2.core.leader := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let b := BirthCheckPermitRepair.bounded
    hpsi hwidth hle pl.core pr.core
  let xL : ExpiringAgentState psi kappa tau := ⟨b.1, pl.stall⟩
  let xR : ExpiringAgentState psi kappa tau := ⟨b.2, pr.stall⟩


  have hL := r1_bounded_left_leader
    hpsi hwidth hle pl.core pr.core
  have hR := r1rl_bounded_right_leader
    hpsi hwidth hle pl.core pr.core
  have hxL := expireOne_left_leader pl xL
  have hxR := expireOne_left_leader pr xR


  unfold BirthCheckPermitRepair.expiring
  exact ⟨hxL.trans hL, hxR.trans hR⟩


theorem r1Host_right_leader
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : B9Host.Phys psi kappa tau) :
    B9Host.leader r = true ->
      B9Host.leader ((B9Host.r1Host hpsi h2).row l r).2 = true := by
  intro hr
  change r.core.core.leader = true at hr
  change
    (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = true


  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let a := BirthCheckPermitRepair.authorized
    hpsi (by decide : 0 < 2) h2 kappa pl.core.erase pr.core.erase
  let d := BirthCheckPermitRepair.expiring
    hpsi (by decide : 0 < 2) h2 l r


  have hprep := congrArg AgentState.leader (prepareExpiring_signal hpsi r)
  change pr.core.erase.core.leader = r.core.core.leader at hprep


  have ha : a.2.core.leader = true := by
    exact r1rl_authorized_right_leader
      (kappa := kappa) hpsi (by decide : 0 < 2) h2
        pl.core.erase pr.core.erase (hprep.trans hr)


  have hd := r1rl_expiring_leaders_authorized
    (kappa := kappa) (tau := tau)
    hpsi (by decide : 0 < 2) h2 l r
  change d.1.core.core.leader = a.1.core.leader ∧
    d.2.core.core.leader = a.2.core.leader at hd
  have hdtrue : d.2.core.core.leader = true := hd.2.trans ha


  let mL := normalizeLeader hpsi d.1
  let mR := normalizeLeader hpsi d.2
  have hn := K2BirthLeaderNormalize.normalizeLeader_leader hpsi d.2
  change mR.core.core.leader = d.2.core.core.leader at hn
  have hmtrue : mR.core.core.leader = true := hn.trans hdtrue


  have hf :=
    BirthShortDoneTerminalRowRightLeader.finalPhysical_right_leader
      hpsi l r mL mR
  have hrow := r1_row_stage
    (kappa := kappa) (tau := tau)
    hpsi (by decide : 0 < 2) h2 l r
  change
    BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r =
      K2BirthDispatcher.finalPhysical hpsi l r mL mR at hrow
  rw [hrow]
  exact hf.trans hmtrue

private theorem r1af_authorized_right_label_of_initiator_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = true) :
    (BirthCheckPermitRepair.authorized
      hpsi hwidth hle kappa l r).2.core.label = r.core.label := by
  unfold BirthCheckPermitRepair.authorized
  dsimp only
  rw [hr, hl]
  exact
    B9SpliceV8BirthCaseAdapterLabelProjection.normalizeDeletion_label_local r


private theorem r1af_bounded_right_label
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    (BirthCheckPermitRepair.bounded
      hpsi hwidth hle l r).2.erase.core.label =
      (BirthCheckPermitRepair.authorized
        hpsi hwidth hle kappa l.erase r.erase).2.core.label := by
  exact congrArg (fun z : AuthorizedAgentState psi => z.core.label)
    (congrArg Prod.snd (r1_bounded_erase hpsi hwidth hle l r))


private theorem r1af_expiring_right_label_of_initiator_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hr : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = false)
    (hl : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase) = true) :
    (BirthCheckPermitRepair.expiring
      hpsi hwidth hle l r).2.core.core.label = r.core.core.label := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let b := BirthCheckPermitRepair.bounded
    hpsi hwidth hle pl.core pr.core
  let xR : ExpiringAgentState psi kappa tau := ⟨b.2, pr.stall⟩

  have hr' : deletionActive (normalizeDeletion pr.core.erase) = false := by
    simpa only [pr] using hr
  have hl' : deletionActive (normalizeDeletion pl.core.erase) = true := by
    simpa only [pl] using hl

  have hb := r1af_bounded_right_label
    hpsi hwidth hle pl.core pr.core
  have ha := r1af_authorized_right_label_of_initiator_delete
    (kappa := kappa) hpsi hwidth hle
      pl.core.erase pr.core.erase hr' hl'
  have hx := expireOne_left_label pr xR
  have hp :=
    B9SpliceV8BirthCaseAdapterLabelProjection.prepared_label_local hpsi r

  unfold BirthCheckPermitRepair.expiring
  exact hx.trans (hb.trans (ha.trans hp))


private theorem r1af_row_right_label_of_initiator_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hOR : (BirthCheckPermitRepair.row
      hpsi hwidth hle l r).2.core.core.leader = false)
    (hr : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = false)
    (hl : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase) = true) :
    (BirthCheckPermitRepair.row
      hpsi hwidth hle l r).2.core.core.label = r.core.core.label := by
  let d := BirthCheckPermitRepair.expiring hpsi hwidth hle l r
  let mL := normalizeLeader hpsi d.1
  let mR := normalizeLeader hpsi d.2

  have hd := r1af_expiring_right_label_of_initiator_delete
    (kappa := kappa) (tau := tau)
    hpsi hwidth hle l r hr hl
  change d.2.core.core.label = r.core.core.label at hd

  have hrow := r1_row_stage
    (kappa := kappa) (tau := tau) hpsi hwidth hle l r
  change
    BirthCheckPermitRepair.row hpsi hwidth hle l r =
      K2BirthDispatcher.finalPhysical hpsi l r mL mR at hrow

  have hOR' := hOR
  rw [hrow] at hOR'

  have hfLeader :=
    BirthShortDoneTerminalRowRightLeader.finalPhysical_right_leader
      hpsi l r mL mR
  have hmFalse : mR.core.core.leader = false :=
    hfLeader.symm.trans hOR'

  have hnLeader :=
    K2BirthLeaderNormalize.normalizeLeader_leader hpsi d.2
  change mR.core.core.leader = d.2.core.core.leader at hnLeader
  have hdFalse : d.2.core.core.leader = false :=
    hnLeader.symm.trans hmFalse

  have hnLabel : mR.core.core.label = d.2.core.core.label := by
    change (normalizeLeader hpsi d.2).core.core.label =
      d.2.core.core.label
    simp only [normalizeLeader, hdFalse, Bool.false_eq_true, if_false]

  have hf := K2BirthDispatcher.finalPhysical_nonK2 hpsi l r mL mR
  have hfLabel := congrArg
    (fun u : ExpiringAgentState psi kappa tau => u.core.core.label) hf.2
  change
    (K2BirthDispatcher.finalPhysical hpsi l r mL mR).2.core.core.label =
      mR.core.core.label at hfLabel

  rw [hrow]
  exact hfLabel.trans (hnLabel.trans hd)


theorem r1Host_aligned_followers
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : B9Host.Phys psi kappa tau) :
    B9Host.leader l = false ->
    B9Host.leader r = false ->
    B9Host.leader ((B9Host.r1Host hpsi h2).row l r).1 = false ->
    B9Host.leader ((B9Host.r1Host hpsi h2).row l r).2 = false ->
    B9Host.Aligned l r ->
    B9Host.Aligned
      ((B9Host.r1Host hpsi h2).row l r).1
      ((B9Host.r1Host hpsi h2).row l r).2 := by
  intro hl hr hOL hOR hA

  have hLeft :
      B9Host.label ((B9Host.r1Host hpsi h2).row l r).1 =
        B9Host.label l :=
    r1Host_left_follower_label hpsi h2 l r hl

  change l.core.core.leader = false at hl
  change r.core.core.leader = false at hr
  change
    (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader = false at hOL
  change
    (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = false at hOR
  change
    r.core.core.label.val =
      (l.core.core.label.val + 1) % psi at hA

  cases hdR : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) with
  | true =>
      have hactive :
          BirthShortDoneTerminalDeletionRank.CurrentPreparedDeletionActive
            hpsi r := by
        simpa [BirthShortDoneTerminalDeletionRank.CurrentPreparedDeletionActive]
          using hdR
      have hlabels :=
        B6LocalRuler.r1_prepared_responder_delete_labels_of_followers
          (kappa := kappa) (tau := tau)
          hpsi (by decide : 0 < 2) h2 l r hl hr hactive
      dsimp only at hlabels
      have hRight :
          B9Host.label ((B9Host.r1Host hpsi h2).row l r).2 =
            B9Host.label r := by
        change
          (BirthCheckPermitRepair.row
            hpsi (by decide : 0 < 2) h2 l r).2.core.core.label =
            r.core.core.label
        exact hlabels.2
      exact B9Host.aligned_of_labels_eq l r _ _ hLeft hRight hA

  | false =>
      cases hdL : deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase) with
      | true =>
          have hRightRaw :=
            r1af_row_right_label_of_initiator_delete
              (kappa := kappa) (tau := tau)
              hpsi (by decide : 0 < 2) h2 l r hOR hdR hdL
          have hRight :
              B9Host.label ((B9Host.r1Host hpsi h2).row l r).2 =
                B9Host.label r := by
            change
              (BirthCheckPermitRepair.row
                hpsi (by decide : 0 < 2) h2 l r).2.core.core.label =
                r.core.core.label
            exact hRightRaw
          exact B9Host.aligned_of_labels_eq l r _ _ hLeft hRight hA

      | false =>
          have hopen :
              BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
                hpsi l r := by
            change
              deletionActive
                  (normalizeDeletion
                    (prepareExpiringDisposal hpsi r).core.erase) = false ∧
                deletionActive
                  (normalizeDeletion
                    (prepareExpiringDisposal hpsi l).core.erase) = false
            exact ⟨hdR, hdL⟩

          have ho := B6LocalRulerE.r1_ordinary_label_or_leader
            (kappa := kappa) (tau := tau)
            hpsi h2 l r hl hr hopen
          dsimp only at ho
          rcases ho with hbad | hbad | hlabels
          · rw [hOL] at hbad
            cases hbad
          · rw [hOR] at hbad
            cases hbad
          · have hnext :
                B6LocalRuler.nextLabel hpsi l.core.core.label =
                  r.core.core.label := by
              apply Fin.ext
              simpa [B6LocalRuler.nextLabel] using hA.symm
            have hRight :
                B9Host.label ((B9Host.r1Host hpsi h2).row l r).2 =
                  B9Host.label r := by
              change
                (BirthCheckPermitRepair.row
                  hpsi (by decide : 0 < 2) h2 l r).2.core.core.label =
                  r.core.core.label
              exact hlabels.2.trans hnext
            exact B9Host.aligned_of_labels_eq l r _ _ hLeft hRight hA


theorem r1Host_spliceLaws
    (hpsi : 0 < psi) (h2 : 2 <= psi) :
    B9Host.SpliceLaws
      (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2) where
  left_follower_label := by
    intro l r hl
    exact r1Host_left_follower_label hpsi h2 l r hl
  right_leader := by
    intro l r hr
    exact r1Host_right_leader hpsi h2 l r hr
  aligned_followers := by
    intro l r hl hr hOL hOR hA
    exact r1Host_aligned_followers
      hpsi h2 l r hl hr hOL hOR hA

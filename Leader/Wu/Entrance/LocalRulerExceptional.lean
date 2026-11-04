import Leader.Wu.Entrance.LocalRuler
import Leader.Wu.Splice.OrdinaryBirthLabelPriority
import Leader.Wu.Birth.ShortDoneTerminalBirthPhysical

/-!
# R1 local-ruler exceptional class E

Closes the remaining ordinary-row label seam in `B6LocalRuler`: the R1-only
`permitFix` is label-neutral even when the CHECK cut is `equal`, and the whole
finite/expiring/normalized/K2 row preserves the CHECK-cut labels whenever the
completed pair contains no leader.

The final `local_ruler_word` recursion is intentionally left only as a PLAN
comment: after this file, its missing content is interval-local deletion-rank
bookkeeping, not the exceptional CHECK row.
-/

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6LocalRulerE

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
open PPLLWallSweepPreCheckResetContracts PPLLWallSweepNormalResetContract
  PPLLCompleteMultiLeaderCleanup PPLLPpsiLeaderCreationSchedule
open BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthShortDoneCuts
  BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
  BirthSigMoveDisposalRepair BirthStationaryWrite
open K2BirthDispatcher K2BirthDispatcherDone K2BirthLeaderNormalize
  ExpiringK2Projection LDSinkKernelC
open B6LocalRuler
open B9SpliceV8BirthCaseAdapterLabelGen

variable {n psi width kappa tau : Nat}

/-! ## 1. Public R1 post-CHECK label transport -/

attribute [local irreducible]
  BirthStationaryWrite.stationaryPersistentAuthorizedRow

private theorem stationary_labels
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

/-- DISAPPEAR, action-one COMPARE, SUPPRESS and stationary WRITE preserve both
labels exactly.  This is the public replacement for the private helper in
`BirthShortDoneTerminalOrdinaryLabelR1`. -/
theorem r1_afterCheck_labels
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    authLabels (afterCheckMetadataWidth hpsi hwidth hle l r) =
      authLabels (l, r) := by
  let b := beforeWriteWidth hpsi hwidth hle l r
  have hb := B9SpliceV8BirthCaseAdapterLabelCheck.beforeWrite_labels
    hpsi hwidth hle l r
  have hw := stationary_labels hpsi b.1 b.2
  have hs :
      afterCheckMetadataWidth hpsi hwidth hle l r =
        stationaryPersistentAuthorizedRow hpsi b.1 b.2 := by
    rfl
  exact (congrArg authLabels hs).trans (hw.trans hb)

private theorem markBirth_labels
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authLabels (markLeaderBirth born q) = authLabels q := by
  have h :=
    PPLLWallSweepPreCheckResetContracts.markLeaderBirth_labels_eq born q
  exact Prod.ext h.1 h.2

/-- The exceptional repair itself changes only `path0Crossed`; this pair form
is convenient at the post-CHECK seam. -/
theorem permitFix_pair_labels
    (c : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authLabels (BirthCheckPermitRepair.permitFix c.1, c.2) =
      authLabels c := by
  exact Prod.ext (B6LocalRuler.permitFix_label c.1) rfl

/-- Authorized R1 ordinary metadata has exactly the two labels present at the
CHECK cut, including class E. -/
theorem r1_ordinary_labels_from_check
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (cap : Nat) (l r : AuthorizedAgentState psi) :
    authLabels
        (BirthCheckPermitRepair.ordinary
          hpsi hwidth hle cap l r) =
      authLabels
        (doneThroughCheckEntryWidth hpsi hwidth hle cap l r) := by
  unfold BirthCheckPermitRepair.ordinary
  dsimp only
  generalize doneThroughCheckEntryWidth hpsi hwidth hle cap l r = c
  let f := BirthCheckPermitRepair.permitFix c.1
  let q := afterCheckMetadataWidth hpsi hwidth hle f c.2
  have hf : authLabels (f, c.2) = authLabels c := by
    simpa only [f] using permitFix_pair_labels c
  have hq := r1_afterCheck_labels hpsi hwidth hle f c.2
  have hm := markBirth_labels (authBirth l r q) q
  change authLabels (markLeaderBirth (authBirth l r q) q) = authLabels c
  exact hm.trans (hq.trans hf)

private theorem permitFix_pair_signal
    (c : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authSignalPair (BirthCheckPermitRepair.permitFix c.1, c.2) =
      authSignalPair c := by
  change signalPair
      ((BirthCheckPermitRepair.permitFix c.1).core, c.2.core) =
    signalPair (c.1.core, c.2.core)
  rw [BirthCheckPermitRepair.permitFix_core]

/-- The same suffix preserves the four-field signal view from the CHECK cut.
This is used only to transport already-created leaders forward. -/
private theorem r1_ordinary_signal_from_check
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
    simpa only [f] using permitFix_pair_signal c
  have hq := afterCheckMetadataWidth_signal hpsi hwidth hle f c.2
  have hm := markBirth_signal (authBirth l r q) q
  change authSignalPair (markLeaderBirth (authBirth l r q) q) =
    authSignalPair c
  exact hm.trans (hq.trans hf)

private theorem leaders_of_signal
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authSignalPair q = authSignalPair p) :
    q.1.core.leader = p.1.core.leader ∧
      q.2.core.leader = p.2.core.leader := by
  exact
    ⟨congrArg
        (fun z : AgentState 1 × AgentState 1 => z.1.leader) h,
      congrArg
        (fun z : AgentState 1 × AgentState 1 => z.2.leader) h⟩

private theorem genStart_signal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genSigSaturatedStart hpsi l r) = signalPair (l, r) := by
  unfold genSigSaturatedStart
  split <;> dsimp only <;> split <;> rfl

private theorem genEmit_signal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genCleanEmit hpsi l r) = signalPair (l, r) := by
  unfold genCleanEmit
  repeat (first | rfl | split)

private theorem genProp_signal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genCleanPropagate hpsi l r) = signalPair (l, r) := by
  unfold genCleanPropagate
  repeat (first | rfl | split)

private theorem genFinish_signal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genSigSaturatedFinish hpsi l r) = signalPair (l, r) := by
  unfold genSigSaturatedFinish
  repeat (first | rfl | split)

/-- Exact P-prime-to-pre-CHECK leader/signal frame, duplicated from the private
ordinary-label proof so no existing file needs editing. -/
private theorem before_signal
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
    rw [genFinish_signal, genProp_signal, genEmit_signal, genStart_signal]
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

private theorem pprime_leaders_reach_r1_ordinary_direct
    (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat)
    (l r : AuthorizedAgentState psi) :
    ((authorizedPPsiLeaderResetProbeWall hpsi l r).1.core.leader = true ->
        (BirthCheckPermitRepair.ordinary
          hpsi hwidth hle cap l r).1.core.leader = true) ∧
      ((authorizedPPsiLeaderResetProbeWall hpsi l r).2.core.leader = true ->
        (BirthCheckPermitRepair.ordinary
          hpsi hwidth hle cap l r).2.core.leader = true) := by
  have hb := leaders_of_signal
    (before_signal hpsi hwidth hle cap l r)
  have ht :=
    B9SpliceV8LeftLeaderOpaqueBridge.doneThrough_eq_stages
      hpsi hwidth hle cap l r
  have ho := leaders_of_signal
    (r1_ordinary_signal_from_check hpsi hwidth hle cap l r)


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


/-- Any leader already produced by P-prime survives through CHECK and the R1
ordinary metadata suffix. -/
private theorem pprime_leaders_reach_r1_ordinary
    (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat)
    (l r : AuthorizedAgentState psi) :
    let p := authorizedPPsiLeaderResetProbeWall hpsi l r
    let o := BirthCheckPermitRepair.ordinary
      hpsi hwidth hle cap l r
    (p.1.core.leader = true -> o.1.core.leader = true) ∧
      (p.2.core.leader = true -> o.2.core.leader = true) := by
  exact pprime_leaders_reach_r1_ordinary_direct
    hpsi hwidth hle cap l r

/-- Exact erasure of the R1 bounded reification. -/
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

/-- R1 bounded reification and both expiry calls preserve the authorized
ordinary output labels. -/
private theorem r1_expiring_labels_authorized
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let a := BirthCheckPermitRepair.authorized
      hpsi hwidth hle kappa pl.core.erase pr.core.erase
    let d := BirthCheckPermitRepair.expiring
      hpsi hwidth hle l r
    d.1.core.core.label = a.1.core.label ∧
      d.2.core.core.label = a.2.core.label := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let b := BirthCheckPermitRepair.bounded
    hpsi hwidth hle pl.core pr.core
  let xL : ExpiringAgentState psi kappa tau := ⟨b.1, pl.stall⟩
  let xR : ExpiringAgentState psi kappa tau := ⟨b.2, pr.stall⟩
  let a := BirthCheckPermitRepair.authorized
    hpsi hwidth hle kappa pl.core.erase pr.core.erase
  have he := r1_bounded_erase hpsi hwidth hle pl.core pr.core
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
  unfold BirthCheckPermitRepair.expiring
  exact ⟨hl.trans hel, hr.trans her⟩

/-- The same finite/expiry shell preserves the two leader bits from the R1
authorized output. -/
private theorem r1_expiring_leaders_authorized
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
  let a := BirthCheckPermitRepair.authorized
    hpsi hwidth hle kappa pl.core.erase pr.core.erase
  have he := r1_bounded_erase hpsi hwidth hle pl.core pr.core
  have hel := congrArg (fun z : AuthorizedAgentState psi => z.core.leader)
    (congrArg Prod.fst he)
  have her := congrArg (fun z : AuthorizedAgentState psi => z.core.leader)
    (congrArg Prod.snd he)
  change xL.core.erase.core.leader = a.1.core.leader at hel
  change xR.core.erase.core.leader = a.2.core.leader at her
  have hl := congrArg (fun z => z.leader)
    (deletionPriorityExpireOne_peaceView_frame pl xL)
  have hr := congrArg (fun z => z.leader)
    (deletionPriorityExpireOne_peaceView_frame pr xR)
  change (deletionPriorityExpireOne tau pl xL).core.erase.core.leader =
    xL.core.erase.core.leader at hl
  change (deletionPriorityExpireOne tau pr xR).core.erase.core.leader =
    xR.core.erase.core.leader at hr
  unfold BirthCheckPermitRepair.expiring
  exact ⟨hl.trans hel, hr.trans her⟩

private theorem r1_authorized_eq_ordinary_of_open
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi l r) :
    let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let l0 := normalizeDeletion pl.core.erase
    let r0 := normalizeDeletion pr.core.erase
    BirthCheckPermitRepair.authorized
        hpsi hwidth hle kappa pl.core.erase pr.core.erase =
      BirthCheckPermitRepair.ordinary
        hpsi hwidth hle kappa l0 r0 := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  change deletionActive r0 = false ∧ deletionActive l0 = false at hopen
  have hr0 :
      deletionActive (normalizeDeletion pr.core.erase) = false := by
    simpa only [r0] using hopen.1
  have hl0 :
      deletionActive (normalizeDeletion pl.core.erase) = false := by
    simpa only [l0] using hopen.2
  change BirthCheckPermitRepair.authorized
      hpsi hwidth hle kappa pl.core.erase pr.core.erase =
    BirthCheckPermitRepair.ordinary hpsi hwidth hle kappa l0 r0
  unfold BirthCheckPermitRepair.authorized
  dsimp only
  simp only [hr0, hl0, Bool.false_eq_true, if_false, l0, r0]

-- END PART 1
/-! ## 2. Follower reconstruction and the full physical suffix -/

private theorem prepared_normalized_followers
    (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false) :
    let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let l0 := normalizeDeletion pl.core.erase
    let r0 := normalizeDeletion pr.core.erase
    l0.core.leader = false ∧ r0.core.leader = false := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  have hpl := congrArg AgentState.leader (prepareExpiring_signal hpsi l)
  have hpr := congrArg AgentState.leader (prepareExpiring_signal hpsi r)
  change pl.core.erase.core.leader = l.core.core.leader at hpl
  change pr.core.erase.core.leader = r.core.core.leader at hpr
  have hn := normalize_pair_signal pl.core.erase pr.core.erase
  exact
    ⟨(congrArg
        (fun z : AgentState 1 × AgentState 1 => z.1.leader) hn).trans
        (hpl.trans hl),
      (congrArg
        (fun z : AgentState 1 × AgentState 1 => z.2.leader) hn).trans
        (hpr.trans hr)⟩

/-- Local copy of the private P′ label theorem used by the old ordinary proof.
It needs only follower inputs and a follower responder at the P′ output. -/
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
    (congrArg
      (fun q : AgentState psi × AgentState psi => q.2.leader) hc).symm.trans
      hout
  by_cases hs : l.core.reset_cmd = true
  · have hz := pPsiLeaderResetProbeWall_source_follower_normalizes
      hpsi l.core r.core (Or.inr hs) hr
    change z.1.leader = l.core.leader ∧ z.2.leader = false ∧
      z.1.label = l.core.label ∧
      z.2.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ∧
      z.2.probe = false at hz
    exact
      ⟨(congrArg
          (fun q : AgentState psi × AgentState psi => q.1.label) hc).trans
          hz.2.2.1,
        (congrArg
          (fun q : AgentState psi × AgentState psi => q.2.label) hc).trans
          hz.2.2.2.1⟩
  · have hz := pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_no_reset
      hpsi l.core r.core (by cases h : l.core.reset_cmd <;> simp_all)
    have hleft := pPsiLeaderProbeWall_initiator_label hpsi l.core r.core
    have hright :=
      pPsiLeaderProbeWall_responder_aligned_of_followers_of_output_follower
        hpsi l.core r.core hl hr (by simpa [z, hz] using hpFollower)
    exact
      ⟨(congrArg
          (fun q : AgentState psi × AgentState psi => q.1.label) hc).trans
          (by simpa [z, hz] using hleft),
        (congrArg
          (fun q : AgentState psi × AgentState psi => q.2.label) hc).trans
          (by simpa [z, hz] using hright)⟩

/-- `finalPhysical` changes only the K2 signal view, hence retains both labels
presented to it. -/
private theorem finalPhysical_labels
    (hpsi : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau) :
    (K2BirthDispatcher.finalPhysical
        hpsi oldL oldR metaL metaR).1.core.core.label =
        metaL.core.core.label ∧
      (K2BirthDispatcher.finalPhysical
        hpsi oldL oldR metaL metaR).2.core.core.label =
        metaR.core.core.label := by
  have h := K2BirthDispatcher.finalPhysical_nonK2
    hpsi oldL oldR metaL metaR
  have hl := congrArg
    (fun q : ExpiringAgentState psi kappa tau => q.core.core.label) h.1
  have hr := congrArg
    (fun q : ExpiringAgentState psi kappa tau => q.core.core.label) h.2
  change (K2BirthDispatcher.finalPhysical
      hpsi oldL oldR metaL metaR).1.core.core.label =
    metaL.core.core.label at hl
  change (K2BirthDispatcher.finalPhysical
      hpsi oldL oldR metaL metaR).2.core.core.label =
    metaR.core.core.label at hr
  exact ⟨hl, hr⟩

/-- Reproof of the private K2 survival leaf used by the terminal birth proof. -/
private theorem k2_left_protected_leader
    (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = true)
    (hs : l.core.core.shield = true)
    (hr : r.core.core.leader = false) :
    (ExpiringK2Projection.row hpsi l r).1.core.core.leader = true := by
  have ho := ExpiringK2Projection.observe_row hpsi l r
  have hl' : (ExpiringK2Projection.observeCell l).leader = true := hl
  have hs' : (ExpiringK2Projection.observeCell l).shield = true := hs
  have hr' : (ExpiringK2Projection.observeCell r).leader = false := hr
  have hk :
      (sinkKernelC (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r)).1.leader = true := by
    cases h :
        (sinkKernelC (by decide : 0 < 1)
          (ExpiringK2Projection.observeCell l)
          (ExpiringK2Projection.observeCell r)).1.leader with
    | true => rfl
    | false =>
        have hd := (K2GlobalGapClosure.kernel_delete_iff
          (by decide : 0 < 1)
          (ExpiringK2Projection.observeCell l)
          (ExpiringK2Projection.observeCell r) hl' hr').mp h
        have hbad : (true : Bool) = false := hs'.symm.trans hd.1
        cases hbad
  have he := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.1.leader) ho
  change (ExpiringK2Projection.row hpsi l r).1.core.core.leader =
    (sinkKernelC (by decide : 0 < 1)
      (ExpiringK2Projection.observeCell l)
      (ExpiringK2Projection.observeCell r)).1.leader at he
  exact he.trans hk

private theorem k2_right_leader
    (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau)
    (hr : r.core.core.leader = true) :
    (ExpiringK2Projection.row hpsi l r).2.core.core.leader = true := by
  have ho := ExpiringK2Projection.observe_row hpsi l r
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_right_leader_eq
    (by decide : 0 < 1)
    (ExpiringK2Projection.observeCell l)
    (ExpiringK2Projection.observeCell r)
  have hr' : (ExpiringK2Projection.observeCell r).leader = true := hr
  have he := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.2.leader) ho
  change (ExpiringK2Projection.row hpsi l r).2.core.core.leader =
    (sinkKernelC (by decide : 0 < 1)
      (ExpiringK2Projection.observeCell l)
      (ExpiringK2Projection.observeCell r)).2.leader at he
  exact he.trans (hk.trans hr')

/-- A newly-computed leader on either old-follower endpoint survives the actual
newborn/collision/K2 physical tail somewhere on the serviced pair. -/
private theorem finalPhysical_birth_has_leader
    (hpsi : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau)
    (hb : K2BirthDispatcher.newborn oldL metaL = true ∨
      K2BirthDispatcher.newborn oldR metaR = true) :
    (K2BirthDispatcher.finalPhysical
        hpsi oldL oldR metaL metaR).1.core.core.leader = true ∨
      (K2BirthDispatcher.finalPhysical
        hpsi oldL oldR metaL metaR).2.core.core.leader = true := by
  let iL := K2BirthDispatcher.initializeNewborn oldL metaL
  let iR := K2BirthDispatcher.initializeNewborn oldR metaR
  change
    (K2BirthDispatcher.collisionRow hpsi iL iR).1.core.core.leader = true ∨
      (K2BirthDispatcher.collisionRow hpsi iL iR).2.core.core.leader = true
  rcases hb with hbL | hbR
  · have hx := K2BirthDispatcher.initializeNewborn_exact oldL metaL hbL
    have hL : iL.core.core.leader = true := hx.2.1
    have hS : iL.core.core.shield = true := hx.2.2.2.1
    by_cases hR : iR.core.core.leader = true
    · exact Or.inr
        (K2BirthDispatcher.collisionRow_of_both hpsi iL iR hL hR).2.1
    · have hRf : iR.core.core.leader = false := by
        cases h : iR.core.core.leader with
        | false => rfl
        | true => exact (hR h).elim
      have hnot :
          ¬ (iL.core.core.leader = true ∧ iR.core.core.leader = true) :=
        fun h => hR h.2
      rw [K2BirthDispatcher.collisionRow_of_not_both hpsi iL iR hnot]
      exact Or.inl (k2_left_protected_leader hpsi iL iR hL hS hRf)
  · have hx := K2BirthDispatcher.initializeNewborn_exact oldR metaR hbR
    have hR : iR.core.core.leader = true := hx.2.1
    by_cases hL : iL.core.core.leader = true
    · exact Or.inr
        (K2BirthDispatcher.collisionRow_of_both hpsi iL iR hL hR).2.1
    · have hnot :
          ¬ (iL.core.core.leader = true ∧ iR.core.core.leader = true) :=
        fun h => hL h.1
      rw [K2BirthDispatcher.collisionRow_of_not_both hpsi iL iR hnot]
      exact Or.inr (k2_right_leader hpsi iL iR hR)

/-- If the old endpoints are followers and the completed R1 row has no leader,
then neither pre-normalization R1 expiring output was a leader. -/
private theorem expiring_followers_of_final_followers
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hqL : (BirthCheckPermitRepair.row
      hpsi hwidth hle l r).1.core.core.leader = false)
    (hqR : (BirthCheckPermitRepair.row
      hpsi hwidth hle l r).2.core.core.leader = false) :
    let d := BirthCheckPermitRepair.expiring hpsi hwidth hle l r
    d.1.core.core.leader = false ∧ d.2.core.core.leader = false := by
  let d := BirthCheckPermitRepair.expiring hpsi hwidth hle l r
  let mL := normalizeLeader hpsi d.1
  let mR := normalizeLeader hpsi d.2
  let q := K2BirthDispatcher.finalPhysical hpsi l r mL mR
  have hrow : BirthCheckPermitRepair.row hpsi hwidth hle l r = q := by
    rfl
  have hqLf : q.1.core.core.leader = false := by
    rw [← hrow]
    exact hqL
  have hqRf : q.2.core.core.leader = false := by
    rw [← hrow]
    exact hqR
  constructor
  · cases hd : d.1.core.core.leader with
    | false => rfl
    | true =>
        have hm : mL.core.core.leader = true :=
          (normalizeLeader_leader hpsi d.1).trans hd
        have hb : K2BirthDispatcher.newborn l mL = true := by
          simp [K2BirthDispatcher.newborn, hl, hm]
        have hsurvive :=
          finalPhysical_birth_has_leader hpsi l r mL mR (Or.inl hb)
        rcases hsurvive with hbad | hbad
        · rw [hqLf] at hbad
          cases hbad
        · rw [hqRf] at hbad
          cases hbad
  · cases hd : d.2.core.core.leader with
    | false => rfl
    | true =>
        have hm : mR.core.core.leader = true :=
          (normalizeLeader_leader hpsi d.2).trans hd
        have hb : K2BirthDispatcher.newborn r mR = true := by
          simp [K2BirthDispatcher.newborn, hr, hm]
        have hsurvive :=
          finalPhysical_birth_has_leader hpsi l r mL mR (Or.inr hb)
        rcases hsurvive with hbad | hbad
        · rw [hqLf] at hbad
          cases hbad
        · rw [hqRf] at hbad
          cases hbad

private theorem authLabels_components_fast
    {x y : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authLabels x = authLabels y) :
    x.1.core.label = y.1.core.label ∧
      x.2.core.label = y.2.core.label := by
  have hL := congrArg (fun z : Fin psi × Fin psi => z.1) h
  have hR := congrArg (fun z : Fin psi × Fin psi => z.2) h
  change x.1.core.label = y.1.core.label at hL
  change x.2.core.label = y.2.core.label at hR
  exact ⟨hL, hR⟩

private theorem normalizeLeader_eq_of_follower_fast
    (hpsi : 0 < psi) (q : ExpiringAgentState psi kappa tau)
    (h : q.core.core.leader = false) :
    normalizeLeader hpsi q = q := by
  unfold K2BirthLeaderNormalize.normalizeLeader
  simp only [h, Bool.false_eq_true, if_false]

private theorem r1_row_eq_finalPhysical_stage
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

private theorem r1_postCheck_labels_of_final_followers
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi l r)
    (hqL : (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader = false)
    (hqR : (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = false) :
    (BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r).1.core.core.label =
      (doneThroughCheckEntryWidth
        hpsi (by decide : 0 < 2) h2 kappa
        (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase)
        (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase)).1.core.label ∧
    (BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r).2.core.core.label =
      (doneThroughCheckEntryWidth
        hpsi (by decide : 0 < 2) h2 kappa
        (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase)
        (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase)).2.core.label := by
  have hdf := expiring_followers_of_final_followers
    hpsi (by decide : 0 < 2) h2 l r hl hr hqL hqR
  dsimp only at hdf

  have ha := r1_authorized_eq_ordinary_of_open
    (kappa := kappa) hpsi (by decide : 0 < 2) h2 l r hopen
  dsimp only at ha

  have hd := r1_expiring_labels_authorized
    hpsi (by decide : 0 < 2) h2 l r
  dsimp only at hd

  have ho := authLabels_components_fast
    (r1_ordinary_labels_from_check
      hpsi (by decide : 0 < 2) h2 kappa
      (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase)
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase))

  have haL := congrArg
    (fun z : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      z.1.core.label) ha
  have haR := congrArg
    (fun z : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      z.2.core.label) ha

  have hmL := congrArg
    (fun z : ExpiringAgentState psi kappa tau => z.core.core.label)
    (normalizeLeader_eq_of_follower_fast hpsi
      (BirthCheckPermitRepair.expiring
        hpsi (by decide : 0 < 2) h2 l r).1 hdf.1)
  have hmR := congrArg
    (fun z : ExpiringAgentState psi kappa tau => z.core.core.label)
    (normalizeLeader_eq_of_follower_fast hpsi
      (BirthCheckPermitRepair.expiring
        hpsi (by decide : 0 < 2) h2 l r).2 hdf.2)

  have hrow := r1_row_eq_finalPhysical_stage
    (kappa := kappa) (tau := tau)
    hpsi (by decide : 0 < 2) h2 l r
  have hf := finalPhysical_labels hpsi l r
    (normalizeLeader hpsi
      (BirthCheckPermitRepair.expiring
        hpsi (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hpsi
      (BirthCheckPermitRepair.expiring
        hpsi (by decide : 0 < 2) h2 l r).2)

  have hqLabelL :
      (BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).1.core.core.label =
        (normalizeLeader hpsi
          (BirthCheckPermitRepair.expiring
            hpsi (by decide : 0 < 2) h2 l r).1).core.core.label :=
    (congrArg
      (fun z : ExpiringAgentState psi kappa tau ×
          ExpiringAgentState psi kappa tau => z.1.core.core.label)
      hrow).trans hf.1
  have hqLabelR :
      (BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).2.core.core.label =
        (normalizeLeader hpsi
          (BirthCheckPermitRepair.expiring
            hpsi (by decide : 0 < 2) h2 l r).2).core.core.label :=
    (congrArg
      (fun z : ExpiringAgentState psi kappa tau ×
          ExpiringAgentState psi kappa tau => z.2.core.core.label)
      hrow).trans hf.2

  exact
    ⟨hqLabelL.trans (hmL.trans (hd.1.trans (haL.trans ho.1))),
      hqLabelR.trans (hmR.trans (hd.2.trans (haR.trans ho.2)))⟩

theorem r1_postCheck_label_or_leader
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi l r) :
    let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let l0 := normalizeDeletion pl.core.erase
    let r0 := normalizeDeletion pr.core.erase
    let c := doneThroughCheckEntryWidth
      hpsi (by decide : 0 < 2) h2 kappa l0 r0
    let q := BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r
    q.1.core.core.leader = true ∨
      q.2.core.core.leader = true ∨
      (q.1.core.core.label = c.1.core.label ∧
        q.2.core.core.label = c.2.core.label) := by
  dsimp only
  cases hqL : (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader with
  | true =>
      exact Or.inl rfl
  | false =>
      cases hqR : (BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader with
      | true =>
          exact Or.inr (Or.inl rfl)
      | false =>
          exact Or.inr (Or.inr
            (r1_postCheck_labels_of_final_followers
              (kappa := kappa) (tau := tau)
              hpsi h2 l r hl hr hopen hqL hqR))

private theorem pprime_responder_follower_of_final_followers
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi l r)
    (hqL : (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader = false)
    (hqR : (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = false) :
    let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let l0 := normalizeDeletion pl.core.erase
    let r0 := normalizeDeletion pr.core.erase
    (authorizedPPsiLeaderResetProbeWall hpsi l0 r0).2.core.leader = false := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  let p := authorizedPPsiLeaderResetProbeWall hpsi l0 r0
  let o := BirthCheckPermitRepair.ordinary
    hpsi (by decide : 0 < 2) h2 kappa l0 r0
  let a := BirthCheckPermitRepair.authorized
    hpsi (by decide : 0 < 2) h2 kappa pl.core.erase pr.core.erase
  let d := BirthCheckPermitRepair.expiring
    hpsi (by decide : 0 < 2) h2 l r
  have hdf := expiring_followers_of_final_followers
    hpsi (by decide : 0 < 2) h2 l r hl hr hqL hqR
  change d.1.core.core.leader = false ∧
    d.2.core.core.leader = false at hdf
  have hda := r1_expiring_leaders_authorized
    hpsi (by decide : 0 < 2) h2 l r
  change d.1.core.core.leader = a.1.core.leader ∧
    d.2.core.core.leader = a.2.core.leader at hda
  have ha := r1_authorized_eq_ordinary_of_open
    (kappa := kappa) hpsi (by decide : 0 < 2) h2 l r hopen
  change a = o at ha
  have hoR : o.2.core.leader = false := by
    rw [← ha]
    rw [← hda.2]
    exact hdf.2
  have hpersist := pprime_leaders_reach_r1_ordinary
    hpsi (by decide : 0 < 2) h2 kappa l0 r0
  cases hp : p.2.core.leader with
  | false =>
      simpa only [pl, pr, l0, r0, p] using hp
  | true =>
      have hbad := hpersist.2 hp
      rw [hoR] at hbad
      cases hbad



private theorem authLabels_components
    {x y : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authLabels x = authLabels y) :
    x.1.core.label = y.1.core.label ∧
      x.2.core.label = y.2.core.label := by
  have hL := congrArg (fun z : Fin psi × Fin psi => z.1) h
  have hR := congrArg (fun z : Fin psi × Fin psi => z.2) h
  change x.1.core.label = y.1.core.label at hL
  change x.2.core.label = y.2.core.label at hR
  exact ⟨hL, hR⟩


private theorem r1_ordinary_label_or_leader_direct
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi l r) :
    (BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader = true ∨
      (BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = true ∨
      ((BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).1.core.core.label =
          l.core.core.label ∧
        (BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).2.core.core.label =
          B6LocalRuler.nextLabel hpsi l.core.core.label) := by
  by_cases hne : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r
  · simpa only using
      (B6LocalRuler.r1_ordinary_label_or_leader_of_no_equal
        hpsi h2 l r hl hr hopen hne)
  · let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let l0 := normalizeDeletion pl.core.erase
    let r0 := normalizeDeletion pr.core.erase


    cases hqL :
        (BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader with
    | true =>
        exact Or.inl rfl
    | false =>
        cases hqR :
            (BirthCheckPermitRepair.row
              hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader with
        | true =>
            exact Or.inr (Or.inl rfl)
        | false =>
            right
            right


            have hnorm :
                l0.core.leader = false ∧ r0.core.leader = false := by
              simpa only [pl, pr, l0, r0] using
                (prepared_normalized_followers hpsi l r hl hr)


            have hpFollower :
                (authorizedPPsiLeaderResetProbeWall
                  hpsi l0 r0).2.core.leader = false := by
              simpa only [pl, pr, l0, r0] using
                (pprime_responder_follower_of_final_followers
                  (kappa := kappa) hpsi h2 l r hl hr hopen hqL hqR)


            have hp :
                (authorizedPPsiLeaderResetProbeWall
                    hpsi l0 r0).1.core.label = l0.core.label ∧
                  (authorizedPPsiLeaderResetProbeWall
                    hpsi l0 r0).2.core.label =
                    ⟨(l0.core.label.val + 1) % psi,
                      Nat.mod_lt _ hpsi⟩ := by
              simpa only using
                (pprime_labels_of_follower_output
                  hpsi l0 r0 hnorm.1 hnorm.2 hpFollower)


            have hc :
                (doneThroughCheckEntryWidth
                    hpsi (by decide : 0 < 2) h2 kappa l0 r0).1.core.label =
                    (authorizedPPsiLeaderResetProbeWall
                      hpsi l0 r0).1.core.label ∧
                  (doneThroughCheckEntryWidth
                    hpsi (by decide : 0 < 2) h2 kappa l0 r0).2.core.label =
                    (authorizedPPsiLeaderResetProbeWall
                      hpsi l0 r0).2.core.label :=
              authLabels_components
                (B9SpliceV8BirthCaseAdapterLabelCheck.throughCheck_labels
                  hpsi (by decide : 0 < 2) h2 kappa l0 r0)


            have hpost :
                (BirthCheckPermitRepair.row
                    hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader = true ∨
                  (BirthCheckPermitRepair.row
                    hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = true ∨
                  ((BirthCheckPermitRepair.row
                      hpsi (by decide : 0 < 2) h2 l r).1.core.core.label =
                      (doneThroughCheckEntryWidth
                        hpsi (by decide : 0 < 2) h2 kappa l0 r0).1.core.label ∧
                    (BirthCheckPermitRepair.row
                      hpsi (by decide : 0 < 2) h2 l r).2.core.core.label =
                      (doneThroughCheckEntryWidth
                        hpsi (by decide : 0 < 2) h2 kappa l0 r0).2.core.label) := by
              simpa only [pl, pr, l0, r0] using
                (r1_postCheck_label_or_leader
                  (kappa := kappa) hpsi h2 l r hl hr hopen)


            rcases hpost with hbad | hbad | hcut
            · rw [hqL] at hbad
              cases hbad
            · rw [hqR] at hbad
              cases hbad
            · have hllabel : l0.core.label = l.core.core.label :=
                (B9SpliceV8BirthCaseAdapterLabelProjection.normalizeDeletion_label_local
                  pl.core.erase).trans
                  (B9SpliceV8BirthCaseAdapterLabelProjection.prepared_label_local
                    hpsi l)
              have hpL :
                  (authorizedPPsiLeaderResetProbeWall
                    hpsi l0 r0).1.core.label = l.core.core.label :=
                hp.1.trans hllabel
              have hpR :
                  (authorizedPPsiLeaderResetProbeWall
                      hpsi l0 r0).2.core.label =
                    B6LocalRuler.nextLabel hpsi l.core.core.label := by
                unfold B6LocalRuler.nextLabel
                rw [← hllabel]
                exact hp.2
              exact
                ⟨hcut.1.trans (hc.1.trans hpL),
                  hcut.2.trans (hc.2.trans hpR)⟩


/-- Exceptional class E is now covered as well: every ordinary-open
follower/follower R1 row either exposes a leader or has the ruler labels. -/
theorem r1_ordinary_label_or_leader
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi l r) :
    let q := BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r
    q.1.core.core.leader = true ∨
      q.2.core.core.leader = true ∨
      (q.1.core.core.label = l.core.core.label ∧
        q.2.core.core.label = B6LocalRuler.nextLabel
          hpsi l.core.core.label) := by
  exact r1_ordinary_label_or_leader_direct
    hpsi h2 l r hl hr hopen

/-!
PLAN -- the protocol seam is now closed; the remaining theorem is the local
rank/search recursion itself.

The desired statement is still exactly the one recorded in
`Leader/Wu/Entrance/LocalRuler.lean`:


What remains after `r1_ordinary_label_or_leader`:

1. Export an interval-local responder-deletion step lemma.  For an interior
   victim `v = cell ring I.first (k+1)` with `k+1 < I.size`, if
   `CurrentPreparedDeletionActive hpsi (C v)`, serve
   `e = cell ring I.first k`.  Use
   `B6LocalRuler.r1_prepared_responder_delete_contract`,
   `BirthCheckPermitRepairLeaf.step1_other`, `right_cell`, and
   `B6LocalReverseFill.interval_cells_injective` to prove that the restriction
   of `interiorPathCount ring I` strictly decreases.  The global consumer
   theorem `localStep_prepared_responder_delete_count_lt` is not this result:
   it counts the whole ring and uses the TerminalHost step.

2. Prove the constructive selection lemma: while some prepared-active victim
   exists at offsets `1,...,W-1`, choose one and apply item 1.  Since each tail
   cell contributes at most one unit, prove
   `interiorPathCount ring I C <= I.size - 1`; therefore at most `W` such
   services are needed before one ruler request.  If activity retreats onto
   offset zero, leave it there: offset zero is the deliberately unused service
   cell and is not a ruler responder.

3. Frame the already-built part of `TailSuccessorChain` across those deletion
   services using
   `B6LocalRuler.r1_prepared_responder_delete_labels_of_followers` and
   `step1_other`.  When no interior prepared-active responder remains, the next
   ruler edge between offsets `k` and `k+1` is `PreparedOrdinaryOpen`; apply the
   theorem proved above.  A leader is immediate `RulerSuccess`; otherwise the
   chain grows by one edge.

4. Induct over at most `W` ruler edges.  Each round spends at most `W`
   deletion letters plus one ordinary ruler letter, with one final drain if
   convenient, yielding the recorded loose budget `(W+1)*W + W`.  `W=2` is
   vacuous for `TailSuccessorChain` and can close directly.

No additional class-E lemma is needed after this file.
-/

end B6LocalRulerE

-- END PART 2

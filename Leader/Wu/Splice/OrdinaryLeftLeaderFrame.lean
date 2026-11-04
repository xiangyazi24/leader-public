import Leader.Wu.Splice.OrdinaryLeftLeaderStages

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV8LeftLeaderFrame

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair
open BirthGenerationControlRepair BirthGenerationDone
  BirthTossCheckPreservationRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneCuts BirthShortDoneTerminalHost
open K2BirthDispatcher
open B6PreWriterFramesA B6PreWriterFramesB B6PreWriterFramesC
open B9SpliceV8LeftLeaderOpaqueBridge

variable {psi width kappa : Nat}

attribute [local irreducible]
  normalizeDeletion authorizedPPsiLeaderResetProbeWall
  authorizedGenCleanEntryWidth authorizedCleanSig authorizedEliminateSig
  generationBeforeMoveEntryWidth authorizedDoneMove preCheckResetWall
  sanitizeAuthorizedPair doneBeforeCheckEntryWidth preserveDoneCheck
  doneThroughCheckEntryWidth beforeWriteWidth afterCheckMetadataWidth
  markLeaderBirth doneOrdinaryMetadataEntryWidth

private theorem frame_left_leader
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : PreWriterFrame q = PreWriterFrame p) :
    q.1.core.leader = p.1.core.leader := by
  have hx :
      (PreWriterFrame q).leftLeader = (PreWriterFrame p).leftLeader := by
    exact congrArg PreWriterFrameView.leftLeader h
  exact hx

private theorem signal_left_leader
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authSignalPair q = authSignalPair p) :
    q.1.core.leader = p.1.core.leader := by
  have hx :
      (authSignalPair q).1.leader = (authSignalPair p).1.leader := by
    exact congrArg
      (fun z : AgentState 1 × AgentState 1 => z.1.leader) h
  exact hx

/-- Opaque stage-by-stage left-leader frame for the ordinary metadata path. -/
theorem ordinary_normalized_left_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    (doneOrdinaryMetadataEntryWidth
      hpsi hwidth hle kappa l0 r0).1.core.leader = l.core.leader := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let p := authorizedPPsiLeaderResetProbeWall hpsi l0 r0
  let g := authorizedGenCleanEntryWidth hpsi hwidth hle kappa p.1 p.2
  let cl := authorizedCleanSig hpsi g.1 g.2
  let el := authorizedEliminateSig hpsi cl.1 cl.2
  let gen := generationBeforeMoveEntryWidth hpsi hwidth hle kappa l0 r0
  let m := authorizedDoneMove hpsi gen.1 gen.2
  let z := sanitizeAuthorizedPair hpsi (preCheckResetWall m.1 m.2)
  let d := doneBeforeCheckEntryWidth hpsi hwidth hle kappa l0 r0
  let chk := preserveDoneCheck hpsi d.1 d.2
  let t := doneThroughCheckEntryWidth hpsi hwidth hle kappa l0 r0
  let b := beforeWriteWidth hpsi hwidth hle t.1 t.2
  let q := afterCheckMetadataWidth hpsi hwidth hle t.1 t.2
  let out := markLeaderBirth (authBirth l0 r0 q) q

  have hnF : authSignalPair (l0, r0) = authSignalPair (l, r) := by
    exact normalize_pair_signal l r
  have hn : l0.core.leader = l.core.leader := signal_left_leader hnF

  have hpF : PreWriterFrame p = PreWriterFrame (l0, r0) := by
    exact B6PreWriterFramesA.pprime_frame hpsi l0 r0
  have hp : p.1.core.leader = l0.core.leader := frame_left_leader hpF

  have hgF : PreWriterFrame g = PreWriterFrame p := by
    exact B6PreWriterFramesA.genEntry_frame hpsi hwidth hle kappa p.1 p.2
  have hg : g.1.core.leader = p.1.core.leader := frame_left_leader hgF

  have hclF : PreWriterFrame cl = PreWriterFrame g := by
    exact B6PreWriterFramesB.clean_frame hpsi g.1 g.2
  have hcl : cl.1.core.leader = g.1.core.leader := frame_left_leader hclF

  have helF : PreWriterFrame el = PreWriterFrame cl := by
    exact B6PreWriterFramesB.eliminate_frame hpsi cl.1 cl.2
  have hel : el.1.core.leader = cl.1.core.leader := frame_left_leader helF

  have hgenEq : gen = el := by
    exact generation_eq_stages hpsi hwidth hle kappa l0 r0
  have hgen : gen.1.core.leader = el.1.core.leader := by
    exact congrArg
      (fun x : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        x.1.core.leader) hgenEq

  have hmF : PreWriterFrame m = PreWriterFrame gen := by
    exact B6PreWriterFramesB.doneMove_frame hpsi gen.1 gen.2
  have hm : m.1.core.leader = gen.1.core.leader := frame_left_leader hmF

  have hzF : PreWriterFrame z = PreWriterFrame m := by
    exact B6PreWriterFramesC.resetSanitize_frame hpsi m
  have hz : z.1.core.leader = m.1.core.leader := frame_left_leader hzF

  have hdEq : d = z := by
    exact doneBefore_eq_stages hpsi hwidth hle kappa l0 r0
  have hd : d.1.core.leader = z.1.core.leader := by
    exact congrArg
      (fun x : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        x.1.core.leader) hdEq

  have hchkF : PreWriterFrame chk = PreWriterFrame d := by
    exact B6PreWriterFramesC.preserveDoneCheck_frame hpsi d.1 d.2
  have hchk : chk.1.core.leader = d.1.core.leader := frame_left_leader hchkF

  have htEq : t = chk := by
    exact doneThrough_eq_stages hpsi hwidth hle kappa l0 r0
  have ht : t.1.core.leader = chk.1.core.leader := by
    exact congrArg
      (fun x : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        x.1.core.leader) htEq

  have hbS : authSignalPair b = authSignalPair (t.1, t.2) := by
    exact beforeWriteWidth_signal hpsi hwidth hle t.1 t.2
  have hb : b.1.core.leader = t.1.core.leader := signal_left_leader hbS

  have hqS : authSignalPair q = authSignalPair (t.1, t.2) := by
    exact afterCheckMetadataWidth_signal hpsi hwidth hle t.1 t.2
  have hq : q.1.core.leader = t.1.core.leader := signal_left_leader hqS
  have hqb : q.1.core.leader = b.1.core.leader := hq.trans hb.symm

  have houtS : authSignalPair out = authSignalPair q := by
    exact markBirth_signal (authBirth l0 r0 q) q
  have hout : out.1.core.leader = q.1.core.leader := signal_left_leader houtS

  have hordinaryEq :
      doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa l0 r0 = out := by
    exact ordinary_eq_stages hpsi hwidth hle kappa l0 r0
  have hordinary :
      (doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa l0 r0).1.core.leader =
        out.1.core.leader := by
    exact congrArg
      (fun x : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        x.1.core.leader) hordinaryEq

  exact hordinary.trans (hout.trans (hqb.trans (hb.trans
    (ht.trans (hchk.trans (hd.trans (hz.trans (hm.trans
      (hgen.trans (hel.trans (hcl.trans (hg.trans (hp.trans hn)))))))))))))

/-- Direct follower form consumed after the V8 ordinary-branch deletion exclusion. -/
theorem ordinary_normalized_left_follower
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) (hl : l.core.leader = false) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    (doneOrdinaryMetadataEntryWidth
      hpsi hwidth hle kappa l0 r0).1.core.leader = false := by
  exact (ordinary_normalized_left_leader
    (kappa := kappa) hpsi hwidth hle l r).trans hl

end B9SpliceV8LeftLeaderFrame

#print axioms B9SpliceV8LeftLeaderFrame.ordinary_normalized_left_leader
#print axioms B9SpliceV8LeftLeaderFrame.ordinary_normalized_left_follower

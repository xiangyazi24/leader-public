import Leader.Wu.Birth.GenerationDonePhase

/-! Current-row phase certificates on the named complete host. Cleanup may
really delete a payload, and the existing timer may expire it. The statements
retain those alternatives; no future phase closure or cohort field is added. -/

set_option autoImplicit false
namespace BirthGenerationDone

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLComparisonHistory PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepNormalResetContract
  PPLLCompleteMultiLeaderCleanup PPLLWriteIncrementGate
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair BirthDisposalRouteInvariant
  BirthMismatchDisposalProducer BirthArrivalCaptureRepair BirthGenerationControlRepair
  BirthTossCheckPreservationRepair BirthSingleUseReleaseRepair

variable {psi kappa tau : Nat}

/-- The actual GEN/CLEAN/ELIMINATE suffix of generationBeforeMove. CLEAN's
possible path deletion is exposed, while done/depart and the new empty control
are derived through the real rows. The source input may be the actual P-prime
output; the definition does not skip that host stage. -/
theorem gen_ack_through_clean_eliminate (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hz : 0 < (genAckInput hpsi kappa l.core r.core).1.label.val)
    (hl : (genAckInput hpsi kappa l.core r.core).1.label.val < psi - 1)
    (hp : (genAckInput hpsi kappa l.core r.core).1.state = .produce)
    (hr : (genAckInput hpsi kappa l.core r.core).2.state = .done) :
    let g := authorizedGenClean hpsi kappa l r
    let c := authorizedCleanSig hpsi g.1 g.2
    let q := authorizedEliminateSig hpsi c.1 c.2
    q.1.core.state = .done ∧ q.2.core.state = .depart ∧ q.1.core.path2 = none ∧
      (q.1.core.path = .bot ∨ q.1.core.path =
        .some (genAckInput hpsi kappa l.core r.core).1.label.val
          (if (genAckInput hpsi kappa l.core r.core).1.bit then 1 else 0)) := by
  let g := authorizedGenClean hpsi kappa l r
  let c := authorizedCleanSig hpsi g.1 g.2
  have hg := genClean_nonzero_ack hpsi kappa l.core r.core hz hl hp hr
  have hf := cleanSig_comparison_frame hpsi g.1.core g.2.core
  have hls : c.1.core.state = .done := hf.2.2.1.trans hg.1
  have hrs : c.2.core.state = .depart := hf.2.2.2.1.trans (congrArg AgentState.state hg.2.2.2)
  have hlp : c.1.core.path2 = none := hf.2.2.2.2.1.trans hg.2.2.1
  have hpath : c.1.core.path = .bot ∨ c.1.core.path =
      .some (genAckInput hpsi kappa l.core r.core).1.label.val
        (if (genAckInput hpsi kappa l.core r.core).1.bit then 1 else 0) :=
    hf.1.imp id (fun h => h.trans hg.2.1)
  have he : (authorizedEliminateSig hpsi c.1 c.2).1.core = c.1.core ∧
      (authorizedEliminateSig hpsi c.1 c.2).2.core = c.2.core := by
    change (eliminateSig hpsi c.1.core c.2.core).1 = c.1.core ∧
      (eliminateSig hpsi c.1.core c.2.core).2 = c.2.core
    simp [eliminateSig, hrs]
  change (authorizedEliminateSig hpsi c.1 c.2).1.core.state = .done ∧
    (authorizedEliminateSig hpsi c.1 c.2).2.core.state = .depart ∧
    (authorizedEliminateSig hpsi c.1 c.2).1.core.path2 = none ∧
    ((authorizedEliminateSig hpsi c.1 c.2).1.core.path = .bot ∨
      (authorizedEliminateSig hpsi c.1 c.2).1.core.path =
        .some (genAckInput hpsi kappa l.core r.core).1.label.val
          (if (genAckInput hpsi kappa l.core r.core).1.bit then 1 else 0))
  rw [he.1, he.2]
  exact ⟨hls, hrs, hlp, hpath⟩

/-- A current, untainted ACK pair passes all movement sub-stages. In particular
Step1 is held, and the retained departure propagation does not consume done.
All unrelated physical registers are framed by the exact core equality. -/
theorem done_move_current_ack (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hs : l.core.state = .done) (hr : r.core.state = .depart)
    (hlp : l.core.path2 = none) (hrp : r.core.path2 = none)
    (hll : l.core.leader = false) (hrl : r.core.leader = false) :
    let q := authorizedDoneMove hpsi l r
    q.1.core = l.core ∧ q.2.core = r.core := by
  have hraw : doneCaptureSigMove hpsi l.core r.core = (l.core, r.core) := by
    simp [doneCaptureSigMove, sigMoveLeaderPreclear, incompleteLeftLeaderBoundary,
      clearIfLeader, hll, hrl, doneTransfers, holdDoneStep1, hs, controlTransfers,
      sigMoveStep2, sigMoveStep3, sigMoveStep4, sigMoveStep5, hlp, hrp,
      comparisonLeaderWall, singleUseControlTail, singleUseApplyControl, hr]
  have h := authorizedDoneMove_core hpsi l r
  rw [hraw] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

private theorem compare_done_core (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hs : l.core.state = .done) (hz : 0 < l.core.label.val)
    (hp : l.core.path ≠ .bot) (hlp : l.core.path2 = none) (hrp : r.core.path2 = none)
    (hr : r.core.state = .none ∨ r.core.state = .depart) :
    (authorizedCompareSigActionOne hpsi l r).1.core = l.core ∧
      (authorizedCompareSigActionOne hpsi l r).2.core = r.core := by
  have hn : l.core.label ≠ ⟨0, hpsi⟩ := by
    intro h; have hv : l.core.label.val = 0 := congrArg Fin.val h; omega
  cases hpath : l.core.path with
  | bot => exact False.elim (hp hpath)
  | some j b =>
    cases j <;> rcases hr with hr | hr
    all_goals cases hrpath : r.core.path
    all_goals simp [authorizedCompareSigActionOne, compareSigInit, hpath, hrpath,
      authorizedCmpUpdate, freshComparisonStart, hn, hs, hr, cmpUpdateReturnPriority,
      cmpUpdateSetPath2, compareSigDispatchActionOne, hlp, hrp]

private theorem suppress_quiet_comparison (hpsi : psi > 0)
    (l r : AgentState psi) (hlleader : l.leader = false)
    (hlreset : l.reset_cmd = false) (hrreset : r.reset_cmd = false) :
    comparisonTrackedPair (suppressSigResetKill hpsi l r) = comparisonTrackedPair (l, r) := by
  unfold suppressSigResetKill suppressSigStart
  simp only [hlleader, Bool.false_eq_true, ↓reduceIte]
  unfold resetKillComparison suppressSigMoveReset
  simp only [hlreset, hrreset, Bool.false_eq_true, ↓reduceIte]
  unfold suppressSigTerminal
  simp only [hrreset, Bool.false_eq_true, and_false, ↓reduceIte]
  unfold suppressSigEcho suppressSigFinish comparisonTrackedPair ComparisonTrackedView.ofState
  repeat (first | rfl | split)

attribute [local irreducible] eliminateLeadersNoCollisionLeaderSink
  writeSeqIncrementGate authorizedPostSuppressLeaderSink

private theorem post_suffix_comparison (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedComparisonTrackedPair (authorizedPostSuppressLeaderSink hpsi l r) =
      authorizedComparisonTrackedPair (l, r) := by
  unfold authorizedPostSuppressLeaderSink
  let q := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
  have hq := eliminateLeadersNoCollisionLeaderSink_comparisonTracked_frame hpsi l.core r.core
  have hw := writeSeqIncrementGate_comparisonTracked_pair hpsi q.1 q.2
  exact hw.trans (Prod.ext hq.1 hq.2)

/-- The full retained suffix preserves a current positive-label done prefix
when there is no incoming return phase, control token, reset or lottery carry.
These are present row fields; no future invariant or writer-frame assumption
is supplied. Gated WRITE and the leader sink are included in the proof. -/
theorem done_afterCheck_suffix_frame (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hs : l.core.state = .done) (hz : 0 < l.core.label.val)
    (hp : l.core.path ≠ .bot) (hlp : l.core.path2 = none) (hrp : r.core.path2 = none)
    (hr : r.core.state = .none ∨ r.core.state = .depart)
    (hcarry : l.core.p_carry = false) (hll : l.core.leader = false)
    (hlreset : l.core.reset_cmd = false) (hrreset : r.core.reset_cmd = false) :
    authorizedComparisonTrackedPair (actionOneAfterCheckSuffix hpsi l r) =
      authorizedComparisonTrackedPair (l, r) := by
  let d := authorizedDisappear hpsi l r
  have hd : d.1.core = l.core ∧ d.2.core = r.core := by
    rcases hr with hr | hr
    all_goals change (disappear hpsi l.core r.core).1 = l.core ∧
      (disappear hpsi l.core r.core).2 = r.core
    all_goals simp [disappear, hs, hr, hcarry]
  let c := authorizedCompareSigActionOne hpsi d.1 d.2
  have hc : c.1.core = l.core ∧ c.2.core = r.core := by
    have hh := compare_done_core hpsi d.1 d.2 (by simpa only [hd.1] using hs)
      (by simpa only [hd.1] using hz) (by simpa only [hd.1] using hp)
      (by simpa only [hd.1] using hlp) (by simpa only [hd.2] using hrp)
      (by simpa only [hd.2] using hr)
    exact ⟨hh.1.trans hd.1, hh.2.trans hd.2⟩
  let s := authorizedReconcile (suppressSigResetKill hpsi) c.1 c.2
  have hsr := suppress_quiet_comparison hpsi c.1.core c.2.core
    (by simpa only [hc.1] using hll) (by simpa only [hc.1] using hlreset)
    (by simpa only [hc.2] using hrreset)
  have ht := post_suffix_comparison hpsi s.1 s.2
  change authorizedComparisonTrackedPair (authorizedPostSuppressLeaderSink hpsi s.1 s.2) = _
  rw [ht]
  change comparisonTrackedPair (suppressSigResetKill hpsi c.1.core c.2.core) = _
  rw [hsr]
  simp only [comparisonTrackedPair, authorizedComparisonTrackedPair, hc.1, hc.2]

/-- Real consecutive CHECK/suffix behavior on a current positive-label ACK
pair. Unlike a bare CHECK guard, this includes COMPARE, reset and WRITE. -/
theorem done_check_and_suffix_frame (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hs : l.core.state = .done) (hz : 0 < l.core.label.val)
    (hp : l.core.path ≠ .bot) (hlp : l.core.path2 = none) (hrp : r.core.path2 = none)
    (hr : r.core.state = .none ∨ r.core.state = .depart)
    (hcarry : l.core.p_carry = false) (hll : l.core.leader = false)
    (hlreset : l.core.reset_cmd = false) (hrreset : r.core.reset_cmd = false) :
    let q := preserveDoneCheck hpsi l r
    authorizedComparisonTrackedPair (actionOneAfterCheckSuffix hpsi q.1 q.2) =
      authorizedComparisonTrackedPair (l, r) := by
  rw [preserveDoneCheck_of_done hpsi l r (Or.inl hs)]
  exact done_afterCheck_suffix_frame hpsi l r hs hz hp hlp hrp hr hcarry hll hlreset hrreset

/-- The actual source ACK cut includes the real P-prime prefix. This is a
read-only expression over this interaction, not a stored event or phase tag. -/
def sourceAckCut (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    AgentState psi × AgentState psi :=
  let p := authorizedPPsiLeaderResetProbeWall hpsi l r
  genAckInput hpsi kappa p.1.core p.2.core

/-- Produce the current phase in the named host's complete prefix through
CLEAN and ELIMINATE. The hypotheses inspect actual pre-propagation fields. -/
theorem source_ack_beforeMove (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hz : 0 < (sourceAckCut hpsi kappa l r).1.label.val)
    (hl : (sourceAckCut hpsi kappa l r).1.label.val < psi - 1)
    (hp : (sourceAckCut hpsi kappa l r).1.state = .produce)
    (hr : (sourceAckCut hpsi kappa l r).2.state = .done) :
    let b := generationBeforeMove hpsi kappa l r
    b.1.core.state = .done ∧ b.2.core.state = .depart ∧ b.1.core.path2 = none ∧
      (b.1.core.path = .bot ∨ b.1.core.path =
        .some (sourceAckCut hpsi kappa l r).1.label.val
          (if (sourceAckCut hpsi kappa l r).1.bit then 1 else 0)) := by
  exact gen_ack_through_clean_eliminate hpsi kappa
    (authorizedPPsiLeaderResetProbeWall hpsi l r).1
    (authorizedPPsiLeaderResetProbeWall hpsi l r).2 hz hl hp hr

attribute [local irreducible] generationBeforeMove doneBeforeCheck authorizedDoneMove

/-- At the actual post-CLEAN cut, current reset/leader/control fields are
enough to frame every physical register through movement and sanitization. -/
theorem doneBeforeCheck_current_ack (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hs : (generationBeforeMove hpsi kappa l r).1.core.state = .done)
    (hr : (generationBeforeMove hpsi kappa l r).2.core.state = .depart)
    (hlp : (generationBeforeMove hpsi kappa l r).1.core.path2 = none)
    (hrp : (generationBeforeMove hpsi kappa l r).2.core.path2 = none)
    (hll : (generationBeforeMove hpsi kappa l r).1.core.leader = false)
    (hrl : (generationBeforeMove hpsi kappa l r).2.core.leader = false)
    (hlreset : (generationBeforeMove hpsi kappa l r).1.core.reset_cmd = false)
    (hrreset : (generationBeforeMove hpsi kappa l r).2.core.reset_cmd = false) :
    let b := generationBeforeMove hpsi kappa l r
    let q := doneBeforeCheck hpsi kappa l r
    q.1.core = b.1.core ∧ q.2.core = b.2.core := by
  let b := generationBeforeMove hpsi kappa l r
  let m := authorizedDoneMove hpsi b.1 b.2
  have hm := done_move_current_ack hpsi b.1 b.2 hs hr hlp hrp hll hrl
  change m.1.core = b.1.core ∧ m.2.core = b.2.core at hm
  have hw := preCheckResetWall_eq_of_inactive m.1 m.2
    (by simpa only [hm.1] using hll) (by simpa only [hm.1] using hlreset)
    (by simpa only [hm.2] using hrreset)
  have hsan : sanitizeAuthorizedPair hpsi (m.1, m.2) = (m.1, m.2) := by
    have hms : m.1.core.state = .done := (congrArg AgentState.state hm.1).trans hs
    have hmr : m.2.core.state = .depart := (congrArg AgentState.state hm.2).trans hr
    simp [sanitizeAuthorizedPair, sanitizeAuthorizedTerminalEqual,
      unsupportedTerminalEqual, hms, hmr]
  unfold doneBeforeCheck
  change (sanitizeAuthorizedPair hpsi (preCheckResetWall m.1 m.2)).1.core = b.1.core ∧
    (sanitizeAuthorizedPair hpsi (preCheckResetWall m.1 m.2)).2.core = b.2.core
  rw [hw, hsan]
  exact hm

/-- The current done at the real CHECK cut is derived from the source row.
Only right control, leader and reset fields at the real post-CLEAN cut remain
as noninterference premises. CLEAN may already have removed the new path. -/
theorem source_ack_doneBeforeCheck (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hz : 0 < (sourceAckCut hpsi kappa l r).1.label.val)
    (hl : (sourceAckCut hpsi kappa l r).1.label.val < psi - 1)
    (hp : (sourceAckCut hpsi kappa l r).1.state = .produce)
    (hr : (sourceAckCut hpsi kappa l r).2.state = .done)
    (hrp : (generationBeforeMove hpsi kappa l r).2.core.path2 = none)
    (hll : (generationBeforeMove hpsi kappa l r).1.core.leader = false)
    (hrl : (generationBeforeMove hpsi kappa l r).2.core.leader = false)
    (hlreset : (generationBeforeMove hpsi kappa l r).1.core.reset_cmd = false)
    (hrreset : (generationBeforeMove hpsi kappa l r).2.core.reset_cmd = false) :
    let q := doneBeforeCheck hpsi kappa l r
    q.1.core.state = .done ∧ q.1.core.path2 = none ∧
      (q.1.core.path = .bot ∨ q.1.core.path =
        .some (sourceAckCut hpsi kappa l r).1.label.val
          (if (sourceAckCut hpsi kappa l r).1.bit then 1 else 0)) := by
  have hg := source_ack_beforeMove hpsi kappa l r hz hl hp hr
  have hm := doneBeforeCheck_current_ack hpsi kappa l r hg.1 hg.2.1 hg.2.2.1
    hrp hll hrl hlreset hrreset
  dsimp only
  rw [hm.1]
  exact ⟨hg.1, hg.2.2.1, hg.2.2.2⟩

end BirthGenerationDone

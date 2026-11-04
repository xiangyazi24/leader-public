import Leader.Wu.Elimination.MultiLeaderCleanupSegmentPlan
import Leader.Wu.Birth.PpsiLeaderCreationRepair

/-!
# Local propagation contracts for the corrected multi-leader repair tail

The repaired producer schedules a full clockwise sweep after the victim kill.
These contracts expose the two physical facts needed to propagate that sweep:
source labels advance by one across a follower edge, and a reset-token edge
between followers cannot create a leader.  The proofs cover the custom
Algorithm-1 suffix rather than importing the older leader-sink transition.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLRepair PPLLWriteIncrementGate
  PPLLComparisonHistory PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLWallSweepPreCheckResetRepair
  PPLLWallSweepPreCheckResetContracts
  PPLLWallSweepNormalResetContract
  PPLLWallSweepRepair
  PPLLWallSweepEchoDrain
  PPLLWallSweepFiniteCleanup
  PPLLWallSweepClockwiseScheduler
  PPLLWallSweepRestartableGeneric
  PPLLPpsiLeaderCreationRepair
  PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoWriteFrames

variable {psi : Nat}

theorem egressSink_labels
    (hpsi : psi > 0) (l r : AgentState psi) :
    (eliminateLeadersNoCollisionEgressSink hpsi l r).1.label = l.label ∧
      (eliminateLeadersNoCollisionEgressSink hpsi l r).2.label = r.label := by
  simp (config := { maxSteps := 50000 })
    [eliminateLeadersNoCollisionEgressSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      dummyBulletSink]

theorem egressSink_followers
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false) :
    (eliminateLeadersNoCollisionEgressSink hpsi l r).1.leader = false ∧
      (eliminateLeadersNoCollisionEgressSink hpsi l r).2.leader = false := by
  simp (config := { maxSteps := 50000 })
    [eliminateLeadersNoCollisionEgressSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      dummyBulletSink, hl, hr]

theorem egressSink_cleanupAuxPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (eliminateLeadersNoCollisionEgressSink hpsi l r) =
      cleanupAuxPair (l, r) := by
  simp (config := { maxSteps := 50000 })
    [eliminateLeadersNoCollisionEgressSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      dummyBulletSink, cleanupAuxPair, CleanupAuxView.ofState]

/-- The custom egress-sink kernel frames the three P-prime control fields. -/
theorem egressSink_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (eliminateLeadersNoCollisionEgressSink hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    simp (config := { maxSteps := 50000 })
      [eliminateLeadersNoCollisionEgressSink,
        eliminateLeadersNoCollisionFire,
        eliminateLeadersNoCollisionZeroLeaderEgressMove,
        eliminateLeadersNoCollisionSignalLeaderSink,
        dummyBulletSink, ppsiControlPair, PpsiControlView.ofState]

theorem authorizedEgressSink_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (authorizedReconcile
          (eliminateLeadersNoCollisionEgressSink hpsi) l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair
    (eliminateLeadersNoCollisionEgressSink hpsi) l r
      (egressSink_ppsiControlPair hpsi l.core r.core)

private theorem egressSink_comparisonTrackedPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    comparisonTrackedPair
        (eliminateLeadersNoCollisionEgressSink hpsi l r) =
      comparisonTrackedPair (l, r) := by
  simp (config := { maxSteps := 50000 })
    [eliminateLeadersNoCollisionEgressSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      dummyBulletSink, comparisonTrackedPair,
      ComparisonTrackedView.ofState]

private theorem neutral_of_tracked_aux_eq
    {old out : AgentState psi}
    (htracked : ComparisonTrackedView.ofState out =
      ComparisonTrackedView.ofState old)
    (haux : CleanupAuxView.ofState out = CleanupAuxView.ofState old)
    (hold : ComparisonNeutral old) : ComparisonNeutral out := by
  have hs := congrArg ComparisonTrackedView.state htracked
  have hpath := congrArg ComparisonTrackedView.path htracked
  have hpath2 := congrArg ComparisonTrackedView.path2 htracked
  have hpCarry := congrArg ComparisonTrackedView.pCarry htracked
  have hpath4 := congrArg CleanupAuxView.path4 haux
  have hpath5 := congrArg CleanupAuxView.path5 haux
  have hp := congrArg CleanupAuxView.p haux
  change out.state = old.state at hs
  change out.path = old.path at hpath
  change out.path2 = old.path2 at hpath2
  change out.p_carry = old.p_carry at hpCarry
  change out.path4 = old.path4 at hpath4
  change out.path5 = old.path5 at hpath5
  change out.p = old.p at hp
  exact ⟨hs.trans hold.1,
    hpath.trans hold.2.1,
    hpath2.trans hold.2.2.1,
    hpath4.trans hold.2.2.2.1,
    hpath5.trans hold.2.2.2.2.1,
    hp.trans hold.2.2.2.2.2.1,
    hpCarry.trans hold.2.2.2.2.2.2⟩

theorem resetEchoPair_eq_of_cleanupAuxPair_eq
    {a b : AgentState psi × AgentState psi}
    (h : cleanupAuxPair a = cleanupAuxPair b) :
    resetEchoPair a = resetEchoPair b := by
  have hL := congrArg Prod.fst h
  have hR := congrArg Prod.snd h
  apply Prod.ext
  · exact Prod.ext (congrArg CleanupAuxView.resetCmd hL)
      (congrArg CleanupAuxView.echo hL)
  · exact Prod.ext (congrArg CleanupAuxView.resetCmd hR)
      (congrArg CleanupAuxView.echo hR)

theorem authorizedReconcile_resetEchoPair_of_cleanupAuxFrame
    (f : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (haux : cleanupAuxPair (f l.core r.core) =
      cleanupAuxPair (l.core, r.core)) :
    authorizedResetEchoPair (authorizedReconcile f l r) =
      authorizedResetEchoPair (l, r) := by
  exact resetEchoPair_eq_of_cleanupAuxPair_eq haux

private theorem cmpUpdateReturnPriority_labels
    (hpsi : psi > 0) (l r : AgentState psi) :
    (cmpUpdateReturnPriority hpsi l r).1.label = l.label ∧
      (cmpUpdateReturnPriority hpsi l r).2.label = r.label := by
  unfold cmpUpdateReturnPriority
  repeat (first | constructor | rfl | split)

private theorem cmpUpdateSetPath2_label
    (hpsi : psi > 0) (u : AgentState psi) :
    (cmpUpdateSetPath2 hpsi u).label = u.label := by
  unfold cmpUpdateSetPath2
  repeat (first | rfl | split)

private theorem authorizedCmpUpdate_labels
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCmpUpdate hpsi l r).1.core.label = l.core.label ∧
      (authorizedCmpUpdate hpsi l r).2.core.label = r.core.label := by
  let allowed := freshComparisonStart hpsi l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := MainState.congest }
  else l.core
  let q := cmpUpdateReturnPriority hpsi lCore r.core
  have hreturn := cmpUpdateReturnPriority_labels hpsi lCore r.core
  exact ⟨(cmpUpdateSetPath2_label hpsi q.1).trans
      (hreturn.1.trans (by unfold lCore; split <;> rfl)),
    hreturn.2⟩

private theorem compareBitActionOne_labels
    (hpsi : psi > 0) (l r : AgentState psi) :
    (compareBitActionOne hpsi l r).1.label = l.label ∧
      (compareBitActionOne hpsi l r).2.label = r.label := by
  constructor
  · change (compareBitUpdateL hpsi l).label = l.label
    unfold compareBitUpdateL
    repeat (first | rfl | split)
  · change (compareBitUpdateRActionOne hpsi r).label = r.label
    unfold compareBitUpdateRActionOne
    dsimp only
    repeat (first | rfl | split)

private theorem compareSigDispatchActionOne_labels
    (hpsi : psi > 0) (l r : AgentState psi) :
    (compareSigDispatchActionOne hpsi l r).1.label = l.label ∧
      (compareSigDispatchActionOne hpsi l r).2.label = r.label := by
  unfold compareSigDispatchActionOne
  split <;>
    first | exact compareBitActionOne_labels hpsi l r | exact ⟨rfl, rfl⟩

private theorem resetEcho_compareBitUpdateRActionOne
    (hpsi : psi > 0) (u : AgentState psi) :
    resetEchoView (compareBitUpdateRActionOne hpsi u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView compareBitUpdateRActionOne
    dsimp only
    repeat (first | rfl | split)

private theorem resetEcho_compareBitUpdateL
    (hpsi : psi > 0) (u : AgentState psi) :
    resetEchoView (compareBitUpdateL hpsi u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView compareBitUpdateL
    dsimp only
    repeat (first | rfl | split)

private theorem compareBitActionOne_resetEchoPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    resetEchoPair (compareBitActionOne hpsi l r) =
      resetEchoPair (l, r) := by
  exact Prod.ext (resetEcho_compareBitUpdateL hpsi l)
    (resetEcho_compareBitUpdateRActionOne hpsi r)

private theorem compareSigDispatchActionOne_resetEchoPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    resetEchoPair (compareSigDispatchActionOne hpsi l r) =
      resetEchoPair (l, r) := by
  unfold compareSigDispatchActionOne
  repeat
    (first | exact compareBitActionOne_resetEchoPair hpsi l r | rfl | split)

private theorem ppsiControl_compareBitUpdateRActionOne
    (hpsi : psi > 0) (u : AgentState psi) :
    PpsiControlView.ofState (compareBitUpdateRActionOne hpsi u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState compareBitUpdateRActionOne
    dsimp only
    repeat (first | rfl | split)

private theorem ppsiControl_compareBitUpdateL
    (hpsi : psi > 0) (u : AgentState psi) :
    PpsiControlView.ofState (compareBitUpdateL hpsi u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState compareBitUpdateL
    dsimp only
    repeat (first | rfl | split)

private theorem compareBitActionOne_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (compareBitActionOne hpsi l r) =
      ppsiControlPair (l, r) := by
  exact Prod.ext (ppsiControl_compareBitUpdateL hpsi l)
    (ppsiControl_compareBitUpdateRActionOne hpsi r)

private theorem compareSigDispatchActionOne_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (compareSigDispatchActionOne hpsi l r) =
      ppsiControlPair (l, r) := by
  unfold compareSigDispatchActionOne
  repeat
    (first | exact compareBitActionOne_ppsiControlPair hpsi l r | rfl | split)

private theorem cmpUpdateReturnPriority_resetEchoPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    resetEchoPair (cmpUpdateReturnPriority hpsi l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView cmpUpdateReturnPriority
    dsimp only
    repeat (first | rfl | split)

private theorem cmpUpdateSetPath2_resetEcho
    (hpsi : psi > 0) (u : AgentState psi) :
    resetEchoView (cmpUpdateSetPath2 hpsi u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView cmpUpdateSetPath2
    dsimp only
    repeat (first | rfl | split)

private theorem authorizedCmpUpdate_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedCmpUpdate hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  let allowed := freshComparisonStart hpsi l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := MainState.congest }
  else l.core
  let q := cmpUpdateReturnPriority hpsi lCore r.core
  have hlCore : resetEchoView lCore = resetEchoView l.core := by
    unfold lCore
    split <;> rfl
  have hq := cmpUpdateReturnPriority_resetEchoPair hpsi lCore r.core
  have hqL := congrArg Prod.fst hq
  have hqR := congrArg Prod.snd hq
  change resetEchoPair (cmpUpdateSetPath2 hpsi q.1, q.2) =
    resetEchoPair (l.core, r.core)
  exact Prod.ext
    ((cmpUpdateSetPath2_resetEcho hpsi q.1).trans (hqL.trans hlCore)) hqR

private theorem compareSigInit_resetEcho
    (u : AgentState psi) :
    resetEchoView (compareSigInit u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView compareSigInit
    split <;> rfl

theorem authorizedCompareSigActionOne_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedCompareSigActionOne hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hinit : resetEchoView lCore = resetEchoView l.core :=
    compareSigInit_resetEcho l.core
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact Prod.ext hinit rfl
  · split
    · exact Prod.ext hinit rfl
    · let q := authorizedCmpUpdate hpsi l0 r
      have hq := authorizedCmpUpdate_resetEchoPair hpsi l0 r
      have hout := compareSigDispatchActionOne_resetEchoPair
        hpsi q.1.core q.2.core
      exact hout.trans (hq.trans (Prod.ext hinit rfl))

theorem authorizedCompareSigActionOne_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedCompareSigActionOne hpsi l r) =
      authorizedPpsiControlPair (l, r) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hinit : PpsiControlView.ofState lCore =
      PpsiControlView.ofState l.core :=
    compareSigInit_ppsiControl l.core
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact Prod.ext hinit rfl
  · split
    · exact Prod.ext hinit rfl
    · let q := authorizedCmpUpdate hpsi l0 r
      have hq := authorizedCmpUpdate_ppsiControlPair hpsi l0 r
      have hout := compareSigDispatchActionOne_ppsiControlPair
        hpsi q.1.core q.2.core
      exact hout.trans (hq.trans (Prod.ext hinit rfl))

private theorem compareBitActionOne_leaders
    (hpsi : psi > 0) (l r : AgentState psi) :
    (compareBitActionOne hpsi l r).1.leader = l.leader ∧
      (compareBitActionOne hpsi l r).2.leader = r.leader := by
  constructor
  · change (compareBitUpdateL hpsi l).leader = l.leader
    unfold compareBitUpdateL
    repeat (first | rfl | split)
  · change (compareBitUpdateRActionOne hpsi r).leader = r.leader
    unfold compareBitUpdateRActionOne
    dsimp only
    repeat (first | rfl | split)

private theorem compareSigDispatchActionOne_leaders
    (hpsi : psi > 0) (l r : AgentState psi) :
    (compareSigDispatchActionOne hpsi l r).1.leader = l.leader ∧
      (compareSigDispatchActionOne hpsi l r).2.leader = r.leader := by
  unfold compareSigDispatchActionOne
  split <;>
    first | exact compareBitActionOne_leaders hpsi l r | exact ⟨rfl, rfl⟩

theorem compareActionOne_leaders
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    (authorizedCompareSigActionOne hpsi l r).1.core.leader = l.core.leader ∧
      (authorizedCompareSigActionOne hpsi l r).2.core.leader = r.core.leader := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hinit : lCore.leader = l.core.leader := by
    unfold lCore compareSigInit
    split <;> rfl
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact ⟨hinit, rfl⟩
  · split
    · exact ⟨hinit, rfl⟩
    · let q := authorizedCmpUpdate hpsi l0 r
      have hq := authorizedCmpUpdate_leaders_eq hpsi l0 r
      have hout := compareSigDispatchActionOne_leaders
        hpsi q.1.core q.2.core
      exact ⟨hout.1.trans (hq.1.trans hinit), hout.2.trans hq.2⟩

theorem compareActionOne_labels
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    (authorizedCompareSigActionOne hpsi l r).1.core.label = l.core.label ∧
      (authorizedCompareSigActionOne hpsi l r).2.core.label = r.core.label := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hl0 : l0.core.label = l.core.label := by
    unfold l0 lCore compareSigInit
    split <;> rfl
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact ⟨hl0, rfl⟩
  · split
    · exact ⟨hl0, rfl⟩
    · let q := authorizedCmpUpdate hpsi l0 r
      have hq := authorizedCmpUpdate_labels hpsi l0 r
      have hout := compareSigDispatchActionOne_labels
        hpsi q.1.core q.2.core
      exact ⟨hout.1.trans (hq.1.trans hl0), hout.2.trans hq.2⟩

private theorem authorizedReconcile_labels
    (f : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).1.core.label = (f l.core r.core).1.label ∧
      (authorizedReconcile f l r).2.core.label =
        (f l.core r.core).2.label := by
  exact ⟨rfl, rfl⟩

private theorem authorizedReconcile_leaders
    (f : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).1.core.leader =
        (f l.core r.core).1.leader ∧
      (authorizedReconcile f l r).2.core.leader =
      (f l.core r.core).2.leader := by
  exact ⟨rfl, rfl⟩

private theorem authorizedReconcile_neutral_of_frames
    (f : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (htracked : comparisonTrackedPair (f l.core r.core) =
      comparisonTrackedPair (l.core, r.core))
    (haux : cleanupAuxPair (f l.core r.core) =
      cleanupAuxPair (l.core, r.core))
    (hL : ComparisonNeutral l.core)
    (hR : ComparisonNeutral r.core) :
    ComparisonNeutral (authorizedReconcile f l r).1.core ∧
      ComparisonNeutral (authorizedReconcile f l r).2.core := by
  exact ⟨neutral_of_tracked_aux_eq
      (congrArg Prod.fst htracked) (congrArg Prod.fst haux) hL,
    neutral_of_tracked_aux_eq
      (congrArg Prod.snd htracked) (congrArg Prod.snd haux) hR⟩

theorem multiLeaderAfterCheckSuffix_labels
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    let q := multiLeaderAfterCheckSuffix hpsi l r
    q.1.core.label = l.core.label ∧ q.2.core.label = r.core.label := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  let q4 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have h0 := PPLLVerify.disappear_labels_eq hpsi l.core r.core
  have h1 := compareActionOne_labels hpsi q0.1 q0.2
  have h2core := authorizedReconcile_labels
    (suppressSigResetKill hpsi) q1.1 q1.2
  have h2 : q2.1.core.label = q1.1.core.label ∧
      q2.2.core.label = q1.2.core.label :=
    ⟨h2core.1.trans
        (suppressSigResetKill_left_label_eq hpsi q1.1.core q1.2.core),
      h2core.2.trans
        (suppressSigResetKill_right_label_eq hpsi q1.1.core q1.2.core)⟩
  have h3core := authorizedReconcile_labels
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  have h3raw := egressSink_labels hpsi q2.1.core q2.2.core
  have h3 : q3.1.core.label = q2.1.core.label ∧
      q3.2.core.label = q2.2.core.label :=
    ⟨h3core.1.trans h3raw.1, h3core.2.trans h3raw.2⟩
  have h4core := authorizedReconcile_labels
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have h4raw := writeSeqIncrementGate_labels hpsi q3.1.core q3.2.core
  have h4 : q4.1.core.label = q3.1.core.label ∧
      q4.2.core.label = q3.2.core.label :=
    ⟨h4core.1.trans h4raw.1, h4core.2.trans h4raw.2⟩
  have hchain : q4.1.core.label = l.core.label ∧
      q4.2.core.label = r.core.label :=
    ⟨h4.1.trans (h3.1.trans (h2.1.trans (h1.1.trans h0.1))),
      h4.2.trans (h3.2.trans (h2.2.trans (h1.2.trans h0.2)))⟩
  simpa only [multiLeaderAfterCheckSuffix, q0, q1, q2, q3, q4]
    using hchain

theorem multiLeaderAfterCheckSuffix_followers
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false) :
    let q := multiLeaderAfterCheckSuffix hpsi l r
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  let q4 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have h0raw := PPLLVerify.disappear_leaders_eq hpsi l.core r.core
  have h0 : q0.1.core.leader = false ∧ q0.2.core.leader = false :=
    ⟨h0raw.1.trans hl, h0raw.2.trans hr⟩
  have h1raw := compareActionOne_leaders hpsi q0.1 q0.2
  have h1 : q1.1.core.leader = false ∧ q1.2.core.leader = false :=
    ⟨h1raw.1.trans h0.1, h1raw.2.trans h0.2⟩
  have h2core := authorizedReconcile_leaders
    (suppressSigResetKill hpsi) q1.1 q1.2
  have h2raw := suppressSigResetKill_leaders_eq
    hpsi q1.1.core q1.2.core
  have h2 : q2.1.core.leader = false ∧ q2.2.core.leader = false :=
    ⟨h2core.1.trans (h2raw.1.trans h1.1),
      h2core.2.trans (h2raw.2.trans h1.2)⟩
  have h3core := authorizedReconcile_leaders
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  have h3raw := egressSink_followers
    hpsi q2.1.core q2.2.core h2.1 h2.2
  have h3 : q3.1.core.leader = false ∧ q3.2.core.leader = false :=
    ⟨h3core.1.trans h3raw.1, h3core.2.trans h3raw.2⟩
  have h3zero : q3.2.core.leader = true →
      q3.2.core.label = ⟨0, hpsi⟩ := by
    intro hbad
    rw [h3.2] at hbad
    contradiction
  have h4core := authorizedReconcile_leaders
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have h4raw := writeSeqIncrementGate_leaders_of_responder_zero
    hpsi q3.1.core q3.2.core h3zero
  have h4 : q4.1.core.leader = false ∧ q4.2.core.leader = false :=
    ⟨h4core.1.trans (h4raw.1.trans h3.1),
      h4core.2.trans (h4raw.2.trans h3.2)⟩
  simpa only [multiLeaderAfterCheckSuffix, q0, q1, q2, q3, q4]
    using h4

/-- Exact reset-token handoff through the custom action-1/egress/gated-WRITE
suffix.  Unlike the older leader-sink theorem, this follows the transition
used by `multiLeaderCleanupTransition`. -/
theorem multiLeaderAfterCheckSuffix_reset_handoff
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true) :
    let q := multiLeaderAfterCheckSuffix hpsi l r
    q.1.core.reset_cmd = false ∧
      q.2.core.reset_cmd = !r.core.echo ∧
      q.2.core.echo = false := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  let q4 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have h0 := authorizedDisappear_resetEchoPair hpsi l r
  have h1 := authorizedCompareSigActionOne_resetEchoPair
    hpsi q0.1 q0.2
  have hpre : authorizedResetEchoPair q1 =
      authorizedResetEchoPair (l, r) := h1.trans h0
  have hpreFields := resetEcho_fields_of_pair_eq hpre
  have hpreReset : q1.1.core.reset_cmd = true :=
    hpreFields.1.trans hlReset
  have hraw := suppressSigResetKill_source_reset_echo_exact
    hpsi q1.1.core q1.2.core (.inr hpreReset)
  change q2.1.core.reset_cmd = false ∧
      q2.2.core.reset_cmd = !q1.2.core.echo ∧
      q2.2.core.echo = false ∧ _ at hraw
  have h3 : authorizedResetEchoPair q3 =
      authorizedResetEchoPair q2 :=
    authorizedReconcile_resetEchoPair_of_cleanupAuxFrame
      (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
        (egressSink_cleanupAuxPair hpsi q2.1.core q2.2.core)
  have h4 : authorizedResetEchoPair q4 =
      authorizedResetEchoPair q3 :=
    authorizedReconcile_resetEchoPair_of_cleanupAuxFrame
      (writeSeqIncrementGate hpsi) q3.1 q3.2
        (writeSeqIncrementGate_cleanupAux_frame
          hpsi q3.1.core q3.2.core)
  have hpostFields := resetEcho_fields_of_pair_eq (h4.trans h3)
  have hout : q4.1.core.reset_cmd = false ∧
      q4.2.core.reset_cmd = !r.core.echo ∧
      q4.2.core.echo = false :=
    ⟨hpostFields.1.trans hraw.1,
      hpostFields.2.2.1.trans
        (hraw.2.1.trans
          (congrArg (fun b : Bool => !b) hpreFields.2.2.2)),
      hpostFields.2.2.2.trans hraw.2.2.1⟩
  simpa only [multiLeaderAfterCheckSuffix, q0, q1, q2, q3, q4]
    using hout

/-- A follower reset source leaves the custom suffix comparison-neutral on
both endpoints.  Consequently birth bookkeeping is inert on repair edges. -/
theorem multiLeaderAfterCheckSuffix_neutral_of_reset_source
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true) :
    let q := multiLeaderAfterCheckSuffix hpsi l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  let q4 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have h0 := authorizedDisappear_resetEchoPair hpsi l r
  have h1 := authorizedCompareSigActionOne_resetEchoPair
    hpsi q0.1 q0.2
  have hpreFields := resetEcho_fields_of_pair_eq (h1.trans h0)
  have hpreReset : q1.1.core.reset_cmd = true :=
    hpreFields.1.trans hlReset
  have hq2 : ComparisonNeutral q2.1.core ∧
      ComparisonNeutral q2.2.core := by
    by_cases he : q1.2.core.echo = true
    · have hc := suppressSigResetKill_source_echo_collision
        hpsi q1.1.core q1.2.core (.inr hpreReset) he
      exact ⟨hc.1, hc.2.1⟩
    · have he0 : q1.2.core.echo = false := by
        cases h : q1.2.core.echo
        · rfl
        · exact (he h).elim
      have hh := suppressSigResetKill_handoff
        hpsi q1.1.core q1.2.core hpreReset he0
      exact ⟨hh.1, hh.2.1⟩
  have hq3 := authorizedReconcile_neutral_of_frames
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
      (egressSink_comparisonTrackedPair hpsi q2.1.core q2.2.core)
      (egressSink_cleanupAuxPair hpsi q2.1.core q2.2.core)
      hq2.1 hq2.2
  have hq4 := authorizedReconcile_neutral_of_frames
    (writeSeqIncrementGate hpsi) q3.1 q3.2
      (writeSeqIncrementGate_comparisonTracked_pair
        hpsi q3.1.core q3.2.core)
      (writeSeqIncrementGate_cleanupAux_frame
        hpsi q3.1.core q3.2.core)
      hq3.1 hq3.2
  simpa only [multiLeaderAfterCheckSuffix, q0, q1, q2, q3, q4]
    using hq4

private theorem normalizeDeletion_label_eq
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl

private theorem normalizeDeletion_leader_eq
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl

private theorem markLeaderBirth_reset_fields
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (markLeaderBirth born q).1.core.reset_cmd = q.1.core.reset_cmd ∧
      (markLeaderBirth born q).2.core.reset_cmd = q.2.core.reset_cmd ∧
      (markLeaderBirth born q).2.core.echo = q.2.core.echo := by
  unfold markLeaderBirth markComparisonForDeletion
  repeat (first | constructor | rfl | split)

private theorem multiLeaderCleanupAuthorizedTransition_eq_marked_suffix
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let before := wallSweepResetProbePreCheckResetBeforeCheck
      hpsi kappa l0 r0
    let after := wallSweepResetProbePreCheckResetAfterCheck
      hpsi kappa l0 r0
    let born := leaderBirthBeforeOrAtCheck l0 r0 before after
    multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
      markLeaderBirth born
        (multiLeaderAfterCheckSuffix hpsi after.1 after.2) := by
  have h := hopen
  change deletionActive (normalizeDeletion l) = false ∧
    deletionActive (normalizeDeletion r) = false at h
  simp [multiLeaderCleanupAuthorizedTransition, h.1, h.2]

/-- On a priority-open reset edge, the custom suffix is neutral, so the
birth-deletion marker is provably inert and the full transition equals the
suffix itself. -/
theorem multiLeaderCleanupAuthorizedTransition_eq_tail_of_reset_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlReset : l.core.reset_cmd = true) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let after := wallSweepResetProbePreCheckResetAfterCheck
      hpsi kappa l0 r0
    multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
      multiLeaderAfterCheckSuffix hpsi after.1 after.2 := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := multiLeaderAfterCheckSuffix hpsi after.1 after.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 before after
  have hnormalizeFields := resetEcho_fields_of_pair_eq
    (normalizeDeletionPair_resetEcho l r)
  have hafterFields := resetEcho_fields_of_pair_eq
    (wallSweepResetProbePreCheckResetAfterCheck_resetEchoPair
      hpsi kappa l0 r0)
  have hafterReset : after.1.core.reset_cmd = true :=
    hafterFields.1.trans (hnormalizeFields.1.trans hlReset)
  have hneutral := multiLeaderAfterCheckSuffix_neutral_of_reset_source
    hpsi after.1 after.2 hafterReset
  change ComparisonNeutral tail.1.core ∧
    ComparisonNeutral tail.2.core at hneutral
  have hmark : markLeaderBirth born tail = tail :=
    markLeaderBirth_eq_of_neutral born tail hneutral.1 hneutral.2
  have hstage := multiLeaderCleanupAuthorizedTransition_eq_marked_suffix
    hpsi kappa l r hopen
  change multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at hstage
  exact hstage.trans hmark

theorem multiLeaderCleanupAuthorizedTransition_neutral_of_reset_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlReset : l.core.reset_cmd = true) :
    let q := multiLeaderCleanupAuthorizedTransition hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := multiLeaderAfterCheckSuffix hpsi after.1 after.2
  have hnormalizeFields := resetEcho_fields_of_pair_eq
    (normalizeDeletionPair_resetEcho l r)
  have hafterFields := resetEcho_fields_of_pair_eq
    (wallSweepResetProbePreCheckResetAfterCheck_resetEchoPair
      hpsi kappa l0 r0)
  have hafterReset : after.1.core.reset_cmd = true :=
    hafterFields.1.trans (hnormalizeFields.1.trans hlReset)
  have htail := multiLeaderAfterCheckSuffix_neutral_of_reset_source
    hpsi after.1 after.2 hafterReset
  change ComparisonNeutral tail.1.core ∧
    ComparisonNeutral tail.2.core at htail
  have heq := multiLeaderCleanupAuthorizedTransition_eq_tail_of_reset_source
    hpsi kappa l r hopen hlReset
  change multiLeaderCleanupAuthorizedTransition hpsi kappa l r = tail at heq
  rw [heq]
  exact htail

theorem multiLeaderCleanupAuthorizedTransition_source_follower_labels
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let q := multiLeaderCleanupAuthorizedTransition hpsi kappa l r
    q.1.core.label = l.core.label ∧
      q.2.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := multiLeaderAfterCheckSuffix hpsi after.1 after.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 before after
  have hnormalize := resetEcho_fields_of_pair_eq
    (normalizeDeletionPair_resetEcho l r)
  have hsource0 : l0.core.leader = true ∨ l0.core.reset_cmd = true := by
    rcases hsource with hleader | hreset
    · exact .inl ((normalizeDeletion_leader_eq l).trans hleader)
    · exact .inr (hnormalize.1.trans hreset)
  have hrFollower0 : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hrFollower
  have hafter :=
    wallSweepResetProbePreCheckResetAfterCheck_source_follower_labels
      hpsi kappa l0 r0 hsource0 hrFollower0
  rw [normalizeDeletion_label_eq l] at hafter
  have htail := multiLeaderAfterCheckSuffix_labels
    hpsi after.1 after.2
  change tail.1.core.label = after.1.core.label ∧
    tail.2.core.label = after.2.core.label at htail
  have hmark := markLeaderBirth_labels_eq born tail
  have hstage :=
    multiLeaderCleanupAuthorizedTransition_eq_marked_suffix
      hpsi kappa l r hopen
  change multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at hstage
  rw [hstage]
  exact ⟨hmark.1.trans (htail.1.trans hafter.1),
    hmark.2.trans (htail.2.trans hafter.2)⟩

theorem multiLeaderCleanupAuthorizedTransition_followers_of_reset_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let q := multiLeaderCleanupAuthorizedTransition hpsi kappa l r
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := multiLeaderAfterCheckSuffix hpsi after.1 after.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 before after
  have hl0Follower : l0.core.leader = false :=
    (normalizeDeletion_leader_eq l).trans hlFollower
  have hr0Follower : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hrFollower
  have hnormalize := normalizeDeletionPair_resetEcho l r
  have hl0Reset : l0.core.reset_cmd = true :=
    (resetEcho_fields_of_pair_eq hnormalize).1.trans hlReset
  have hafter :=
    wallSweepResetProbePreCheckResetAfterCheck_followers_of_reset_source
      hpsi kappa l0 r0 hl0Follower hl0Reset hr0Follower
  have htail := multiLeaderAfterCheckSuffix_followers
    hpsi after.1 after.2 hafter.1 hafter.2
  change tail.1.core.leader = false ∧
    tail.2.core.leader = false at htail
  have hmark := markLeaderBirth_leaders_eq born tail
  have hstage :=
    multiLeaderCleanupAuthorizedTransition_eq_marked_suffix
      hpsi kappa l r hopen
  change multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at hstage
  rw [hstage]
  exact ⟨hmark.1.trans htail.1, hmark.2.trans htail.2⟩

/-- On a priority-open edge, a left reset token is consumed and handed to an
echo-free responder.  This is the state-threading fact used between adjacent
edges of the clockwise repair sweep. -/
theorem multiLeaderCleanupAuthorizedTransition_reset_handoff
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlReset : l.core.reset_cmd = true)
    (hrEcho : r.core.echo = false) :
    let q := multiLeaderCleanupAuthorizedTransition hpsi kappa l r
    q.1.core.reset_cmd = false ∧
      q.2.core.reset_cmd = true ∧
      q.2.core.echo = false := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := multiLeaderAfterCheckSuffix hpsi after.1 after.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 before after
  have hnormalize := normalizeDeletionPair_resetEcho l r
  have hnormalizeFields := resetEcho_fields_of_pair_eq hnormalize
  have hafterPair := wallSweepResetProbePreCheckResetAfterCheck_resetEchoPair
    hpsi kappa l0 r0
  have hafterFields := resetEcho_fields_of_pair_eq hafterPair
  have hafterLeftReset : after.1.core.reset_cmd = true :=
    hafterFields.1.trans (hnormalizeFields.1.trans hlReset)
  have hafterRightEcho : after.2.core.echo = false :=
    hafterFields.2.2.2.trans (hnormalizeFields.2.2.2.trans hrEcho)
  have htail := multiLeaderAfterCheckSuffix_reset_handoff
    hpsi after.1 after.2 hafterLeftReset
  change tail.1.core.reset_cmd = false ∧
      tail.2.core.reset_cmd = !after.2.core.echo ∧
      tail.2.core.echo = false at htail
  have htailRightReset : tail.2.core.reset_cmd = true := by
    rw [htail.2.1, hafterRightEcho]
    decide
  have hmark := markLeaderBirth_reset_fields born tail
  have hstage := multiLeaderCleanupAuthorizedTransition_eq_marked_suffix
    hpsi kappa l r hopen
  change multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at hstage
  rw [hstage]
  exact ⟨hmark.1.trans htail.1,
    hmark.2.1.trans htailRightReset,
    hmark.2.2.trans htail.2.2⟩

/-- Finite reification and timer expiration preserve the successor-label
contract needed by each source-covered edge of the repair sweep. -/
theorem multiLeaderCleanupTransition_source_follower_labels
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hsource : l.core.erase.core.leader = true ∨
      l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false) :
    let q := multiLeaderCleanupTransition hpsi kappa tau l r
    q.1.core.erase.core.label = l.core.erase.core.label ∧
      q.2.core.erase.core.label =
        ⟨(l.core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
  let raw := multiLeaderCleanupAuthorizedTransition
    hpsi kappa l.core.erase r.core.erase
  have ha := multiLeaderCleanupAuthorizedTransition_source_follower_labels
    hpsi kappa l.core.erase r.core.erase hopen hsource hrFollower
  change raw.1.core.label = l.core.erase.core.label ∧
    raw.2.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ at ha
  have hv := multiLeaderCleanupTransition_cleanupPhysicalView
    hpsi kappa tau l r
  change
    CleanupPhysicalView.ofState
        (multiLeaderCleanupTransition hpsi kappa tau l r).1.core.erase.core =
          CleanupPhysicalView.ofState raw.1.core ∧
      CleanupPhysicalView.ofState
        (multiLeaderCleanupTransition hpsi kappa tau l r).2.core.erase.core =
          CleanupPhysicalView.ofState raw.2.core at hv
  exact
    ⟨(congrArg CleanupPhysicalView.label hv.1).trans ha.1,
      (congrArg CleanupPhysicalView.label hv.2).trans ha.2⟩

/-- A reset source propagating through a follower edge cannot create a
physical leader, including through the finite and expiration wrappers. -/
theorem multiLeaderCleanupTransition_followers_of_reset_source
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false) :
    let q := multiLeaderCleanupTransition hpsi kappa tau l r
    q.1.core.erase.core.leader = false ∧
      q.2.core.erase.core.leader = false := by
  let raw := multiLeaderCleanupAuthorizedTransition
    hpsi kappa l.core.erase r.core.erase
  have ha := multiLeaderCleanupAuthorizedTransition_followers_of_reset_source
    hpsi kappa l.core.erase r.core.erase hopen
      hlFollower hlReset hrFollower
  change raw.1.core.leader = false ∧
    raw.2.core.leader = false at ha
  have hv := multiLeaderCleanupTransition_cleanupPhysicalView
    hpsi kappa tau l r
  change
    CleanupPhysicalView.ofState
        (multiLeaderCleanupTransition hpsi kappa tau l r).1.core.erase.core =
          CleanupPhysicalView.ofState raw.1.core ∧
      CleanupPhysicalView.ofState
        (multiLeaderCleanupTransition hpsi kappa tau l r).2.core.erase.core =
          CleanupPhysicalView.ofState raw.2.core at hv
  exact
    ⟨(congrArg CleanupPhysicalView.leader hv.1).trans ha.1,
      (congrArg CleanupPhysicalView.leader hv.2).trans ha.2⟩

/-- The finite carrier and expiration wrapper preserve the reset-token
handoff exactly. -/
theorem multiLeaderCleanupTransition_reset_handoff
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrEcho : r.core.erase.core.echo = false) :
    let q := multiLeaderCleanupTransition hpsi kappa tau l r
    q.1.core.erase.core.reset_cmd = false ∧
      q.2.core.erase.core.reset_cmd = true ∧
      q.2.core.erase.core.echo = false := by
  let bounded := multiLeaderCleanupBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := multiLeaderCleanupAuthorizedTransition_reset_handoff
    hpsi kappa l.core.erase r.core.erase hopen hlReset hrEcho
  have he := erase_multiLeaderCleanupBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (multiLeaderCleanupAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (multiLeaderCleanupAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseL : lBase.core.erase.core.reset_cmd = false := by
    change bounded.1.erase.core.reset_cmd = false
    rw [hL]
    exact ha.1
  have hbaseRReset : rBase.core.erase.core.reset_cmd = true := by
    change bounded.2.erase.core.reset_cmd = true
    rw [hR]
    exact ha.2.1
  have hbaseREcho : rBase.core.erase.core.echo = false := by
    change bounded.2.erase.core.echo = false
    rw [hR]
    exact ha.2.2
  have hLf := deletionPriorityExpireOne_path_frame l lBase
  have hRf := deletionPriorityExpireOne_path_frame r rBase
  change
    (deletionPriorityExpireOne tau l lBase).core.erase.core.reset_cmd = false ∧
      (deletionPriorityExpireOne tau r rBase).core.erase.core.reset_cmd = true ∧
      (deletionPriorityExpireOne tau r rBase).core.erase.core.echo = false
  exact ⟨hLf.2.2.2.1.trans hbaseL,
    hRf.2.2.2.1.trans hbaseRReset,
    hRf.2.2.2.2.1.trans hbaseREcho⟩

theorem multiLeaderCleanupTransition_neutral_of_reset_source
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlReset : l.core.erase.core.reset_cmd = true) :
    let q := multiLeaderCleanupTransition hpsi kappa tau l r
    ComparisonNeutral q.1.core.erase.core ∧
      ComparisonNeutral q.2.core.erase.core := by
  let bounded := multiLeaderCleanupBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := multiLeaderCleanupAuthorizedTransition_neutral_of_reset_source
    hpsi kappa l.core.erase r.core.erase hopen hlReset
  have he := erase_multiLeaderCleanupBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (multiLeaderCleanupAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (multiLeaderCleanupAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseL : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.1
  have hbaseR : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.2
  change
    ComparisonNeutral
        (deletionPriorityExpireOne tau l lBase).core.erase.core ∧
      ComparisonNeutral
        (deletionPriorityExpireOne tau r rBase).core.erase.core
  exact ⟨(deletionPriorityExpireOne_neutral_fields l lBase hbaseL).1,
    (deletionPriorityExpireOne_neutral_fields r rBase hbaseR).1⟩

/-- Complete physical contract for one echo-free follower edge of the repair
sweep: labels advance, both endpoints remain followers, and the reset token
moves to the responder. -/
theorem multiLeaderCleanupTransition_follower_reset_edge
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false)
    (hrEcho : r.core.erase.core.echo = false) :
    let q := multiLeaderCleanupTransition hpsi kappa tau l r
    q.1.core.erase.core.leader = false ∧
      q.2.core.erase.core.leader = false ∧
      q.1.core.erase.core.label = l.core.erase.core.label ∧
      q.2.core.erase.core.label =
        ⟨(l.core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      q.1.core.erase.core.reset_cmd = false ∧
      q.2.core.erase.core.reset_cmd = true ∧
      q.2.core.erase.core.echo = false := by
  have hleaders := multiLeaderCleanupTransition_followers_of_reset_source
    hpsi kappa tau l r hopen hlFollower hlReset hrFollower
  have hlabels := multiLeaderCleanupTransition_source_follower_labels
    hpsi kappa tau l r hopen (.inr hlReset) hrFollower
  have hreset := multiLeaderCleanupTransition_reset_handoff
    hpsi kappa tau l r hopen hlReset hrEcho
  exact ⟨hleaders.1, hleaders.2, hlabels.1, hlabels.2,
    hreset.1, hreset.2.1, hreset.2.2⟩

private theorem deletionActive_false_of_neutral
    {kappa tau : Nat}
    (u : ExpiringAgentState psi kappa tau)
    (h : ComparisonNeutral u.core.erase.core) :
    deletionActive u.core.erase = false := by
  simp [deletionActive, pathPresent, h.1, h.2.1]

private theorem cwPos_ne_of_ne_below_repair
    (ring : DirectedRing n) (start : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cwPos ring start a ≠ cwPos ring start b := by
  intro hpos
  apply hab
  have ha' := cwPos_bounded_unique ring start
    (cwPos ring start a) a ha rfl
  have hb' := cwPos_bounded_unique ring start
    (cwPos ring start a) b hb hpos.symm
  exact ha'.trans hb'.symm

/-- Reconstruct `noFreeBarrier` after repairing one proper clockwise follower
interval.  The reference configuration supplies the unchanged exterior and
the incoming edge at `start`; the exact modular labels discharge every edge
inside the repaired interval, while the first untouched responder is allowed
to be a leader. -/
theorem noFreeBarrier_of_clockwise_repaired_interval
    (hpsi : psi > 0) (ring : DirectedRing n)
    (start : Fin n) (steps : Nat)
    (A D : Fin n → AgentState psi)
    (hsourceAhead : steps + 1 < n)
    (hfreeA : noFreeBarrier hpsi ring A)
    (hstartLabel : (D start).label = (A start).label)
    (hstartLeader : (D start).leader = (A start).leader)
    (hsourceLeader :
      (D (cwPos ring start (steps + 1))).leader = true)
    (hlabels : ∀ k, k ≤ steps →
      (D (cwPos ring start k)).label =
        ⟨((D start).label.val + k) % psi,
          Nat.mod_lt _ hpsi⟩)
    (houtside : ∀ k, steps < k → k < n →
      D (cwPos ring start k) = A (cwPos ring start k)) :
    noFreeBarrier hpsi ring D := by
  intro i
  dsimp only
  intro hbarrier
  let responder := ring.rightNeighbor i
  let k := cwDist ring start responder
  have hklt : k < n := cwDist_lt ring start responder
  have hkpos : cwPos ring start k = responder :=
    cwPos_cwDist ring start responder
  cases hk : k with
  | zero =>
      rw [hk] at hkpos
      have hresponder : responder = start := by
        simpa using hkpos.symm
      have hpred : i = cwPos ring start (n - 1) := by
        apply rightNeighbor_injective ring
        rw [show ring.rightNeighbor i = start by
          simpa [responder] using hresponder]
        rw [← cwPos_succ]
        have hncalc : n - 1 + 1 = n := by omega
        rw [hncalc, cwPos_period]
      have hpredOutside :
          D (cwPos ring start (n - 1)) =
            A (cwPos ring start (n - 1)) :=
        houtside (n - 1) (by omega) (by omega)
      have hwrapNeighbor :
          ring.rightNeighbor (cwPos ring start (n - 1)) = start := by
        rw [← cwPos_succ]
        have hncalc : n - 1 + 1 = n := by omega
        rw [hncalc, cwPos_period]
      have hbarrierA :
          isBarrier hpsi
            (A (cwPos ring start (n - 1))) (A start) := by
        intro hconsecutive
        apply hbarrier
        change (D (ring.rightNeighbor i)).label =
          ⟨((D i).label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩
        rw [show ring.rightNeighbor i = responder by rfl,
          hresponder, hpred, hstartLabel, hpredOutside]
        exact hconsecutive
      have hleaderA := hfreeA (cwPos ring start (n - 1))
        (by rw [hwrapNeighbor]; exact hbarrierA)
      change (A (ring.rightNeighbor
        (cwPos ring start (n - 1)))).leader = true at hleaderA
      rw [hwrapNeighbor] at hleaderA
      change (D (ring.rightNeighbor i)).leader = true
      rw [show ring.rightNeighbor i = responder by rfl,
        hresponder, hstartLeader]
      exact hleaderA
  | succ k0 =>
      rw [hk] at hkpos hklt
      have hi : i = cwPos ring start k0 := by
        apply rightNeighbor_injective ring
        calc
          ring.rightNeighbor i = responder := rfl
          _ = cwPos ring start (k0 + 1) := hkpos.symm
          _ = ring.rightNeighbor (cwPos ring start k0) :=
            cwPos_succ ring start k0
      have hresponder :
          responder = cwPos ring start (k0 + 1) := by
        exact hkpos.symm
      by_cases hvisited : k0 + 1 ≤ steps
      · have hconsecutive :
            (D (cwPos ring start (k0 + 1))).label =
              ⟨((D (cwPos ring start k0)).label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ := by
          rw [hlabels (k0 + 1) hvisited,
            hlabels k0 (by omega)]
          apply Fin.ext
          simpa [Nat.add_assoc] using
            (mod_add_one (D start).label.val k0 psi).symm
        exfalso
        apply hbarrier
        simpa only [hi, cwPos_succ] using hconsecutive
      · by_cases hsource : k0 + 1 = steps + 1
        · change (D (ring.rightNeighbor i)).leader = true
          rw [hi, ← cwPos_succ, hsource]
          exact hsourceLeader
        · have hk0Outside : steps < k0 := by omega
          have hk0lt : k0 < n := by omega
          have hrespOutside :
              D (cwPos ring start (k0 + 1)) =
                A (cwPos ring start (k0 + 1)) :=
            houtside (k0 + 1) (by omega) (by omega)
          have hleftOutside :
              D (cwPos ring start k0) =
                A (cwPos ring start k0) :=
            houtside k0 hk0Outside hk0lt
          have hbarrierA :
              isBarrier hpsi
                (A (cwPos ring start k0))
                (A (cwPos ring start (k0 + 1))) := by
            intro hconsecutive
            apply hbarrier
            change (D (ring.rightNeighbor i)).label =
              ⟨((D i).label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩
            rw [hi, ← cwPos_succ, hleftOutside, hrespOutside]
            exact hconsecutive
          have hleaderA :=
            hfreeA (cwPos ring start k0)
              (by simpa only [cwPos_succ] using hbarrierA)
          change (A (ring.rightNeighbor
            (cwPos ring start k0))).leader = true at hleaderA
          rw [← cwPos_succ] at hleaderA
          change (D (ring.rightNeighbor i)).leader = true
          rw [hi, ← cwPos_succ, hrespOutside]
          exact hleaderA

/-- Global one-step form of the repair-edge contract.  It additionally
preserves deletion inactivity and every off-edge state, so it can be iterated
without an external readiness wrapper. -/
theorem localStep_multiLeaderCleanup_follower_reset_edge
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false)
    (hrEcho : (C (ring.rightNeighbor e)).core.erase.core.echo = false) :
    let D := localStep ring
      (multiLeaderCleanupTransition hpsi kappa tau) C e
    NoActiveDeletion D ∧
      (∀ i, (D i).core.erase.core.leader =
        (C i).core.erase.core.leader) ∧
      (D e).core.erase.core.label = (C e).core.erase.core.label ∧
      (D (ring.rightNeighbor e)).core.erase.core.label =
        ⟨((C e).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (D e).core.erase.core.reset_cmd = false ∧
      (D (ring.rightNeighbor e)).core.erase.core.reset_cmd = true ∧
      (D (ring.rightNeighbor e)).core.erase.core.echo = false ∧
      (∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i) := by
  let j := ring.rightNeighbor e
  let T := multiLeaderCleanupTransition hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hene : e ≠ j :=
    Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn e)
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hedge := multiLeaderCleanupTransition_follower_reset_edge
    hpsi kappa tau (C e) (C j) hopen hlFollower hlReset
      (by simpa [j] using hrFollower) (by simpa [j] using hrEcho)
  change q.1.core.erase.core.leader = false ∧
      q.2.core.erase.core.leader = false ∧
      q.1.core.erase.core.label = (C e).core.erase.core.label ∧
      q.2.core.erase.core.label =
        ⟨((C e).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      q.1.core.erase.core.reset_cmd = false ∧
      q.2.core.erase.core.reset_cmd = true ∧
      q.2.core.erase.core.echo = false at hedge
  have hneutral := multiLeaderCleanupTransition_neutral_of_reset_source
    hpsi kappa tau (C e) (C j) hopen hlReset
  change ComparisonNeutral q.1.core.erase.core ∧
    ComparisonNeutral q.2.core.erase.core at hneutral
  have hleft : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, T, localStep, j, Ne.symm hene]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i hie hij
    simp [D, T, localStep, j, hie, hij]
  have hnoActiveD : NoActiveDeletion D := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact deletionActive_false_of_neutral q.1 hneutral.1
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact deletionActive_false_of_neutral q.2 hneutral.2
      · rw [hoff i hie hij]
        exact hnoActive i
  have hleaderFrame : ∀ i,
      (D i).core.erase.core.leader =
        (C i).core.erase.core.leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft, hedge.1, hlFollower]
    · by_cases hij : i = j
      · subst i
        rw [hright, hedge.2.1]
        simpa [j] using hrFollower
      · rw [hoff i hie hij]
  change NoActiveDeletion D ∧ _
  exact ⟨hnoActiveD, hleaderFrame,
    (congrArg (fun u => u.core.erase.core.label) hleft).trans hedge.2.2.1,
    (congrArg (fun u => u.core.erase.core.label) hright).trans
      hedge.2.2.2.1,
    (congrArg (fun u => u.core.erase.core.reset_cmd) hleft).trans
      hedge.2.2.2.2.1,
    (congrArg (fun u => u.core.erase.core.reset_cmd) hright).trans
      hedge.2.2.2.2.2.1,
    (congrArg (fun u => u.core.erase.core.echo) hright).trans
      hedge.2.2.2.2.2.2,
    by simpa [j] using hoff⟩

/-- A literal clockwise sweep of the actual cleanup transition propagates an
echo-free reset token across a follower arc.  The theorem derives priority
openness from the preserved global deletion drain at every prefix. -/
theorem runLocalSchedule_multiLeaderCleanup_follower_reset_sweep
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (start : Fin n) (C : EConfig n psi kappa tau)
    (steps : Nat) (hsteps : steps < n)
    (hnoActive : NoActiveDeletion C)
    (hsourceFollower : (C start).core.erase.core.leader = false)
    (hsourceReset : (C start).core.erase.core.reset_cmd = true)
    (hsourceEcho : (C start).core.erase.core.echo = false)
    (hfollowers : ∀ k, 0 < k → k ≤ steps →
      (C (cwPos ring start k)).core.erase.core.leader = false)
    (hecho : ∀ k, 0 < k → k ≤ steps →
      (C (cwPos ring start k)).core.erase.core.echo = false) :
    let D := runLocalSchedule ring
      (multiLeaderCleanupTransition hpsi kappa tau) C
      (clockwiseEdgeSchedule ring start steps)
    NoActiveDeletion D ∧
      (∀ i, (D i).core.erase.core.leader =
        (C i).core.erase.core.leader) ∧
      (D (cwPos ring start steps)).core.erase.core.leader = false ∧
      (D (cwPos ring start steps)).core.erase.core.reset_cmd = true ∧
      (D (cwPos ring start steps)).core.erase.core.echo = false ∧
      (D (cwPos ring start steps)).core.erase.core.label =
        ⟨((C start).core.erase.core.label.val + steps) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (∀ k, k ≤ steps →
        (D (cwPos ring start k)).core.erase.core.label =
          ⟨((C start).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩) ∧
      (∀ k, steps < k → k < n →
        D (cwPos ring start k) = C (cwPos ring start k)) := by
  let T := multiLeaderCleanupTransition hpsi kappa tau
  induction steps with
  | zero =>
      simp only [clockwiseEdgeSchedule, runLocalSchedule, cwPos_zero]
      have hbaseLabel : (C start).core.erase.core.label =
          ⟨((C start).core.erase.core.label.val + 0) % psi,
            Nat.mod_lt _ hpsi⟩ := by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt (C start).core.erase.core.label.isLt]
      refine ⟨hnoActive, (fun _ => True.intro), hsourceFollower,
        hsourceReset, hsourceEcho, hbaseLabel, ?_,
        (fun _ _ _ => True.intro)⟩
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa using hbaseLabel
  | succ s ih =>
      have hslt : s < n := by omega
      have hprev := ih hslt
        (fun k hk hks => hfollowers k hk (by omega))
        (fun k hk hks => hecho k hk (by omega))
      let D := runLocalSchedule ring T C
        (clockwiseEdgeSchedule ring start s)
      change NoActiveDeletion D ∧
          (∀ i, (D i).core.erase.core.leader =
            (C i).core.erase.core.leader) ∧
          (D (cwPos ring start s)).core.erase.core.leader = false ∧
          (D (cwPos ring start s)).core.erase.core.reset_cmd = true ∧
          (D (cwPos ring start s)).core.erase.core.echo = false ∧
          (D (cwPos ring start s)).core.erase.core.label =
            ⟨((C start).core.erase.core.label.val + s) % psi,
              Nat.mod_lt _ hpsi⟩ ∧
          (∀ k, k ≤ s →
            (D (cwPos ring start k)).core.erase.core.label =
              ⟨((C start).core.erase.core.label.val + k) % psi,
                Nat.mod_lt _ hpsi⟩) ∧
          (∀ k, s < k → k < n →
            D (cwPos ring start k) = C (cwPos ring start k)) at hprev
      let e := cwPos ring start s
      let j := ring.rightNeighbor e
      have hj : j = cwPos ring start (s + 1) := by
        simpa [j, e] using (cwPos_succ ring start s).symm
      have hDj : D j = C j := by
        rw [hj]
        exact hprev.2.2.2.2.2.2.2 (s + 1) (by omega) hsteps
      have hrightFollower : (D j).core.erase.core.leader = false := by
        rw [hDj, hj]
        exact hfollowers (s + 1) (by omega) (Nat.le_refl _)
      have hrightEcho : (D j).core.erase.core.echo = false := by
        rw [hDj, hj]
        exact hecho (s + 1) (by omega) (Nat.le_refl _)
      let E := localStep ring T D e
      have hstep := localStep_multiLeaderCleanup_follower_reset_edge
        hpsi kappa tau ring hn D e hprev.1
          (by simpa [e] using hprev.2.2.1)
          (by simpa [e] using hprev.2.2.2.1)
          (by simpa [j] using hrightFollower)
          (by simpa [j] using hrightEcho)
      change NoActiveDeletion E ∧
          (∀ i, (E i).core.erase.core.leader =
            (D i).core.erase.core.leader) ∧
          (E e).core.erase.core.label = (D e).core.erase.core.label ∧
          (E j).core.erase.core.label =
            ⟨((D e).core.erase.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ ∧
          (E e).core.erase.core.reset_cmd = false ∧
          (E j).core.erase.core.reset_cmd = true ∧
          (E j).core.erase.core.echo = false ∧
          (∀ i, i ≠ e → i ≠ j → E i = D i) at hstep
      have hleaderFrame : ∀ i,
          (E i).core.erase.core.leader =
            (C i).core.erase.core.leader := fun i =>
        (hstep.2.1 i).trans (hprev.2.1 i)
      have hendLeader :
          (E (cwPos ring start (s + 1))).core.erase.core.leader = false := by
        rw [← hj]
        exact (hstep.2.1 j).trans hrightFollower
      have hendReset :
          (E (cwPos ring start (s + 1))).core.erase.core.reset_cmd = true := by
        simpa [hj] using hstep.2.2.2.2.2.1
      have hendEcho :
          (E (cwPos ring start (s + 1))).core.erase.core.echo = false := by
        simpa [hj] using hstep.2.2.2.2.2.2.1
      have hendLabel :
          (E (cwPos ring start (s + 1))).core.erase.core.label =
            ⟨((C start).core.erase.core.label.val + (s + 1)) % psi,
              Nat.mod_lt _ hpsi⟩ := by
        rw [← hj]
        calc
          (E j).core.erase.core.label =
              ⟨((D e).core.erase.core.label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ := hstep.2.2.2.1
          _ = ⟨((C start).core.erase.core.label.val + (s + 1)) % psi,
                Nat.mod_lt _ hpsi⟩ := by
            apply Fin.ext
            have hval := congrArg Fin.val hprev.2.2.2.2.2.1
            change (D (cwPos ring start s)).core.erase.core.label.val =
              ((C start).core.erase.core.label.val + s) % psi at hval
            change ((D e).core.erase.core.label.val + 1) % psi =
              ((C start).core.erase.core.label.val + (s + 1)) % psi
            rw [show (D e).core.erase.core.label.val =
              ((C start).core.erase.core.label.val + s) % psi by
                simpa [e] using hval]
            simpa [Nat.add_assoc] using
              mod_add_one (C start).core.erase.core.label.val s psi
      have hahead : ∀ k, s + 1 < k → k < n →
          E (cwPos ring start k) = C (cwPos ring start k) := by
        intro k hk hkn
        have hke : cwPos ring start k ≠ e := by
          simpa [e] using cwPos_ne_of_ne_below_repair ring start
            hkn hslt (by omega)
        have hkj : cwPos ring start k ≠ j := by
          rw [hj]
          exact cwPos_ne_of_ne_below_repair ring start
            hkn hsteps (by omega)
        exact (hstep.2.2.2.2.2.2.2
          (cwPos ring start k) hke hkj).trans
            (hprev.2.2.2.2.2.2.2 k (by omega) hkn)
      have hvisited : ∀ k, k ≤ s + 1 →
          (E (cwPos ring start k)).core.erase.core.label =
            ⟨((C start).core.erase.core.label.val + k) % psi,
              Nat.mod_lt _ hpsi⟩ := by
        intro k hk
        by_cases hlast : k = s + 1
        · subst k
          exact hendLabel
        have hkle : k ≤ s := by omega
        by_cases hcurrent : k = s
        · subst k
          calc
            (E (cwPos ring start s)).core.erase.core.label =
                (D e).core.erase.core.label := by
              simpa [e] using hstep.2.2.1
            _ = ⟨((C start).core.erase.core.label.val + s) % psi,
                  Nat.mod_lt _ hpsi⟩ := by
              simpa [e] using hprev.2.2.2.2.2.2.1 s (Nat.le_refl _)
        · have hklt : k < s := by omega
          have hkn : k < n := by omega
          have hke : cwPos ring start k ≠ e := by
            simpa [e] using cwPos_ne_of_ne_below_repair ring start
              hkn hslt (by omega)
          have hkj : cwPos ring start k ≠ j := by
            rw [hj]
            exact cwPos_ne_of_ne_below_repair ring start
              hkn hsteps (by omega)
          calc
            (E (cwPos ring start k)).core.erase.core.label =
                (D (cwPos ring start k)).core.erase.core.label :=
              congrArg (fun u => u.core.erase.core.label)
                (hstep.2.2.2.2.2.2.2
                  (cwPos ring start k) hke hkj)
            _ = ⟨((C start).core.erase.core.label.val + k) % psi,
                  Nat.mod_lt _ hpsi⟩ :=
              hprev.2.2.2.2.2.2.1 k hkle
      have hE : NoActiveDeletion E ∧
          (∀ i, (E i).core.erase.core.leader =
            (C i).core.erase.core.leader) ∧
          (E (cwPos ring start (s + 1))).core.erase.core.leader = false ∧
          (E (cwPos ring start (s + 1))).core.erase.core.reset_cmd = true ∧
          (E (cwPos ring start (s + 1))).core.erase.core.echo = false ∧
          (E (cwPos ring start (s + 1))).core.erase.core.label =
            ⟨((C start).core.erase.core.label.val + (s + 1)) % psi,
              Nat.mod_lt _ hpsi⟩ ∧
          (∀ k, k ≤ s + 1 →
            (E (cwPos ring start k)).core.erase.core.label =
              ⟨((C start).core.erase.core.label.val + k) % psi,
                Nat.mod_lt _ hpsi⟩) ∧
          (∀ k, s + 1 < k → k < n →
            E (cwPos ring start k) = C (cwPos ring start k)) :=
        ⟨hstep.1, hleaderFrame, hendLeader, hendReset,
          hendEcho, hendLabel, hvisited, hahead⟩
      have hrun : runLocalSchedule ring T C
          (clockwiseEdgeSchedule ring start (s + 1)) = E := by
        calc
          runLocalSchedule ring T C
              (clockwiseEdgeSchedule ring start (s + 1)) =
            runLocalSchedule ring T C
              (clockwiseEdgeSchedule ring start s ++ [e]) := rfl
          _ = runLocalSchedule ring T D [e] :=
            runLocalSchedule_append_generic ring T C
              (clockwiseEdgeSchedule ring start s) [e]
          _ = E := rfl
      rw [hrun]
      exact hE

namespace SegmentCleanupPlan

variable {ring : DirectedRing n}

/-- Full physical state after the kill word, before the corrective sweep. -/
def physicalWordOutput
    (hpsi : psi > 0) (kappa tau : Nat)
    (plan : SegmentCleanupPlan ring)
    (C : EConfig n psi kappa tau) : EConfig n psi kappa tau :=
  runLocalSchedule ring
    (multiLeaderCleanupTransition hpsi kappa tau) C plan.word

/-- Full physical execution of the corrected kill-and-repair word. -/
def physicalFullOutput
    (hpsi : psi > 0) (kappa tau : Nat)
    (plan : SegmentCleanupPlan ring)
    (C : EConfig n psi kappa tau) : EConfig n psi kappa tau :=
  runLocalSchedule ring
    (multiLeaderCleanupTransition hpsi kappa tau) C plan.fullWord

/-- Concrete specialization of the generic sweep theorem to the corrected
`repairTail`.  The hypotheses name the exact producer facts still required
from the preceding kill word; the conclusion is the literal `fullWord`
execution, not an abstract readiness certificate. -/
theorem physicalFullOutput_repairTail_of_post_word
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (plan : SegmentCleanupPlan ring)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion
      (plan.physicalWordOutput hpsi kappa tau C))
    (hsourceFollower :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.leader = false)
    (hsourceReset :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.reset_cmd = true)
    (hsourceEcho :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.echo = false)
    (hfollowers : ∀ k, 0 < k → k ≤ plan.dVS →
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming k)).core.erase.core.leader = false)
    (hecho : ∀ k, 0 < k → k ≤ plan.dVS →
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming k)).core.erase.core.echo = false) :
    let B := plan.physicalWordOutput hpsi kappa tau C
    let D := plan.physicalFullOutput hpsi kappa tau C
    NoActiveDeletion D ∧
      (∀ i, (D i).core.erase.core.leader =
        (B i).core.erase.core.leader) ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.leader =
        false ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.reset_cmd =
        true ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.echo =
        false ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.label =
        ⟨((B plan.predIncoming).core.erase.core.label.val + plan.dVS) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (∀ k, k ≤ plan.dVS →
        (D (cwPos ring plan.predIncoming k)).core.erase.core.label =
          ⟨((B plan.predIncoming).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩) := by
  let B := plan.physicalWordOutput hpsi kappa tau C
  let D := plan.physicalFullOutput hpsi kappa tau C
  have hsweep := runLocalSchedule_multiLeaderCleanup_follower_reset_sweep
    hpsi kappa tau ring hn plan.predIncoming B plan.dVS plan.dVS_lt
      hnoActive hsourceFollower hsourceReset hsourceEcho hfollowers hecho
  let tailOut := runLocalSchedule ring
    (multiLeaderCleanupTransition hpsi kappa tau) B plan.repairTail
  change NoActiveDeletion tailOut ∧
      (∀ i, (tailOut i).core.erase.core.leader =
        (B i).core.erase.core.leader) ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.leader =
        false ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.reset_cmd =
        true ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.echo =
        false ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.label =
        ⟨((B plan.predIncoming).core.erase.core.label.val + plan.dVS) % psi,
          Nat.mod_lt _ hpsi⟩ ∧ _ ∧ _ at hsweep
  have hfull : D = tailOut := by
    unfold D tailOut physicalFullOutput fullWord repairTail B
    exact runLocalSchedule_append_generic ring
      (multiLeaderCleanupTransition hpsi kappa tau) C plan.word
        (clockwiseEdgeSchedule ring plan.predIncoming plan.dVS)
  change NoActiveDeletion D ∧
      (∀ i, (D i).core.erase.core.leader =
        (B i).core.erase.core.leader) ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.leader =
        false ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.reset_cmd =
        true ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.echo =
        false ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.label =
        ⟨((B plan.predIncoming).core.erase.core.label.val + plan.dVS) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (∀ k, k ≤ plan.dVS →
        (D (cwPos ring plan.predIncoming k)).core.erase.core.label =
          ⟨((B plan.predIncoming).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩)
  rw [hfull]
  exact ⟨hsweep.1, hsweep.2.1, hsweep.2.2.1,
    hsweep.2.2.2.1, hsweep.2.2.2.2.1,
    hsweep.2.2.2.2.2.1, hsweep.2.2.2.2.2.2.1⟩

/-- Barrier reconstruction for the literal corrected `fullWord`.  Besides the
six post-kill sweep facts, the producer supplies only a reference
`noFreeBarrier` configuration, the unchanged exterior, and the surviving
source leader. -/
theorem physicalFullOutput_noFreeBarrier_of_reference
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (plan : SegmentCleanupPlan ring)
    (C : EConfig n psi kappa tau)
    (A : Fin n → AgentState psi)
    (hsourceAhead : plan.dVS + 1 < n)
    (hfreeA : noFreeBarrier hpsi ring A)
    (hnoActive : NoActiveDeletion
      (plan.physicalWordOutput hpsi kappa tau C))
    (hsourceFollower :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.leader = false)
    (hsourceReset :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.reset_cmd = true)
    (hsourceEcho :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.echo = false)
    (hfollowers : ∀ k, 0 < k → k ≤ plan.dVS →
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming k)).core.erase.core.leader = false)
    (hecho : ∀ k, 0 < k → k ≤ plan.dVS →
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming k)).core.erase.core.echo = false)
    (hstartLabel :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.label =
          (A plan.predIncoming).label)
    (hstartLeader :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.leader =
          (A plan.predIncoming).leader)
    (hsurvivor :
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming (plan.dVS + 1))).core.erase.core.leader =
          true)
    (houtside : ∀ k, plan.dVS < k → k < n →
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming k)).core.erase.core =
          A (cwPos ring plan.predIncoming k)) :
    noFreeBarrier hpsi ring (fun i =>
      ((plan.physicalFullOutput hpsi kappa tau C) i).core.erase.core) := by
  let B := plan.physicalWordOutput hpsi kappa tau C
  let D := plan.physicalFullOutput hpsi kappa tau C
  have hsweep := runLocalSchedule_multiLeaderCleanup_follower_reset_sweep
    hpsi kappa tau ring hn plan.predIncoming B plan.dVS plan.dVS_lt
      hnoActive hsourceFollower hsourceReset hsourceEcho hfollowers hecho
  let tailOut := runLocalSchedule ring
    (multiLeaderCleanupTransition hpsi kappa tau) B plan.repairTail
  change NoActiveDeletion tailOut ∧
      (∀ i, (tailOut i).core.erase.core.leader =
        (B i).core.erase.core.leader) ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.leader =
        false ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.reset_cmd =
        true ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.echo =
        false ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.label =
        ⟨((B plan.predIncoming).core.erase.core.label.val + plan.dVS) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (∀ k, k ≤ plan.dVS →
        (tailOut (cwPos ring plan.predIncoming k)).core.erase.core.label =
          ⟨((B plan.predIncoming).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩) ∧
      (∀ k, plan.dVS < k → k < n →
        tailOut (cwPos ring plan.predIncoming k) =
          B (cwPos ring plan.predIncoming k)) at hsweep
  have hfull : D = tailOut := by
    unfold D tailOut physicalFullOutput fullWord repairTail B
    exact runLocalSchedule_append_generic ring
      (multiLeaderCleanupTransition hpsi kappa tau) C plan.word
        (clockwiseEdgeSchedule ring plan.predIncoming plan.dVS)
  have hstartTail :
      (tailOut plan.predIncoming).core.erase.core.label =
        (B plan.predIncoming).core.erase.core.label := by
    have hzero := hsweep.2.2.2.2.2.2.1 0 (by omega)
    simpa [Nat.mod_eq_of_lt
      (B plan.predIncoming).core.erase.core.label.isLt] using hzero
  have hreconstructed : noFreeBarrier hpsi ring (fun i =>
      (tailOut i).core.erase.core) := by
    apply noFreeBarrier_of_clockwise_repaired_interval
      hpsi ring plan.predIncoming plan.dVS
        (A := A) (D := fun i => (tailOut i).core.erase.core)
        hsourceAhead hfreeA
    · exact hstartTail.trans hstartLabel
    · exact (hsweep.2.1 plan.predIncoming).trans hstartLeader
    · exact (hsweep.2.1
        (cwPos ring plan.predIncoming (plan.dVS + 1))).trans hsurvivor
    · intro k hk
      calc
        (tailOut (cwPos ring plan.predIncoming k)).core.erase.core.label =
            ⟨((B plan.predIncoming).core.erase.core.label.val + k) % psi,
              Nat.mod_lt _ hpsi⟩ :=
          hsweep.2.2.2.2.2.2.1 k hk
        _ = ⟨((tailOut plan.predIncoming).core.erase.core.label.val + k) % psi,
              Nat.mod_lt _ hpsi⟩ := by rw [hstartTail]
    · intro k hk hkn
      calc
        (tailOut (cwPos ring plan.predIncoming k)).core.erase.core =
            (B (cwPos ring plan.predIncoming k)).core.erase.core :=
          congrArg (fun u => u.core.erase.core)
            (hsweep.2.2.2.2.2.2.2 k hk hkn)
        _ = A (cwPos ring plan.predIncoming k) := houtside k hk hkn
  change noFreeBarrier hpsi ring (fun i => (D i).core.erase.core)
  rw [hfull]
  exact hreconstructed

end SegmentCleanupPlan

end PPLLCompleteMultiLeaderCleanup

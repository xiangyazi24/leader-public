import Leader.Wu.Birth.ShortDoneTerminalCapGenStage


namespace BirthShortDoneTerminalCapGeneralR3


open PPLL PPLLRepair PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthGenerationControlRepair BirthGenerationDone
open BirthWaitPassive BirthShortWait BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1
open BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
open K2BirthDispatcher K2BirthDispatcherDone ExpiringK2Projection
  K2BirthLeaderNormalize BirthShortDoneCuts
open PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair
open BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
  BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


private theorem h2 : 0 < 2 := by decide
private theorem hle2 : 2 <= 2 := by decide


/-- Fields that DONE movement, reset deletion, and terminal-equality sanitation
    must frame.  `state` and `path` are intentionally absent. -/
private structure CapMoveView2 where
  label : Fin 2
  count : Nat
  wait : Bool
  leader : Bool
  resetCmd : Bool
  path2 : Option Path2Info


private def capMoveView2 (u : AgentState 2) : CapMoveView2 :=
  ⟨u.label, u.count, u.wait, u.leader, u.reset_cmd, u.path2⟩


/-- CHECK may change leader on the responder and may write path2, so neither
    belongs to the post-CHECK stable view. -/
private structure CheckStableView2 where
  label : Fin 2
  count : Nat
  wait : Bool
  resetCmd : Bool


private def checkStableView2 (u : AgentState 2) : CheckStableView2 :=
  ⟨u.label, u.count, u.wait, u.reset_cmd⟩


/-! ## DONE movement from the actual depart/depart cut -/


private theorem captureStep1_capMoveView2_of_none
    (l r : AgentState 2)
    (hlp : l.path2 = none) (hrp : r.path2 = none) :
    let q := captureStep1 l r
    capMoveView2 q.1 = capMoveView2 l /\
      capMoveView2 q.2 = capMoveView2 r := by
  cases hL : l.path <;> cases hR : r.path
  all_goals simp only [captureStep1, hL, hR]
  all_goals repeat split
  all_goals simp_all [capMoveView2, hlp, hrp]


private theorem controlTransfers_eq_of_path2_none
    (l r : AgentState 2)
    (hlp : l.path2 = none) (hrp : r.path2 = none) :
    controlTransfers l r = (l, r) := by
  simp [controlTransfers, sigMoveStep2, sigMoveStep3,
    sigMoveStep4, sigMoveStep5, hlp, hrp]


private theorem doneTransfers_eq_capture_of_depart_none
    (l r : AgentState 2)
    (hls : l.state = .depart)
    (hlp : l.path2 = none) (hrp : r.path2 = none) :
    doneTransfers l r = captureStep1 l r := by
  let c := captureStep1 l r
  have hc := captureStep1_capMoveView2_of_none l r hlp hrp
  change capMoveView2 c.1 = capMoveView2 l /\
    capMoveView2 c.2 = capMoveView2 r at hc


  have hcpL : c.1.path2 = none := by
    have h := congrArg CapMoveView2.path2 hc.1
    change c.1.path2 = l.path2 at h
    exact h.trans hlp
  have hcpR : c.2.path2 = none := by
    have h := congrArg CapMoveView2.path2 hc.2
    change c.2.path2 = r.path2 at h
    exact h.trans hrp


  unfold doneTransfers
  rw [holdDoneStep1_of_depart l r hls]
  have ht := controlTransfers_eq_of_path2_none c.1 c.2 hcpL hcpR
  have heta : (c.1, c.2) = c := by
    apply Prod.ext <;> rfl
  exact ht.trans heta


private theorem preclear_eq_of_followers
    (l r : AgentState 2)
    (hll : l.leader = false) (hrl : r.leader = false) :
    sigMoveLeaderPreclear h2 l r = (l, r) := by
  have hb : ¬ incompleteLeftLeaderBoundary h2 l r := by
    intro h
    simpa [hrl] using h.1
  simp [sigMoveLeaderPreclear, clearIfLeader, hll, hrl, hb]


private theorem comparisonLeaderWall_eq_of_followers
    (l r : AgentState 2)
    (hll : l.leader = false) (hrl : r.leader = false) :
    comparisonLeaderWall l r = (l, r) := by
  simp [comparisonLeaderWall, hll, hrl]


private theorem singleUseControlTail_capMoveView2_of_none
    (l r : AgentState 2)
    (hlp : l.path2 = none) (hrp : r.path2 = none) :
    let q := singleUseControlTail h2 l r
    capMoveView2 q.1 = capMoveView2 l /\
      capMoveView2 q.2 = capMoveView2 r := by
  unfold singleUseControlTail
  simp only [singleUseApplyControl, hlp, hrp]
  unfold capMoveView2
  repeat (first | exact ⟨rfl, rfl⟩ | constructor | rfl | split)
  all_goals simp_all


private theorem doneCaptureSigMove_capMoveView2_of_depart_followers
    (l r : AgentState 2)
    (hls : l.state = .depart)
    (hll : l.leader = false) (hrl : r.leader = false)
    (hlp : l.path2 = none) (hrp : r.path2 = none) :
    let q := doneCaptureSigMove h2 l r
    capMoveView2 q.1 = capMoveView2 l /\
      capMoveView2 q.2 = capMoveView2 r := by
  have hp := preclear_eq_of_followers l r hll hrl


  let c := captureStep1 l r
  have hc := captureStep1_capMoveView2_of_none l r hlp hrp
  change capMoveView2 c.1 = capMoveView2 l /\
    capMoveView2 c.2 = capMoveView2 r at hc


  have hdone := doneTransfers_eq_capture_of_depart_none l r hls hlp hrp


  have hcLLeader : c.1.leader = false := by
    have h := congrArg CapMoveView2.leader hc.1
    change c.1.leader = l.leader at h
    exact h.trans hll
  have hcRLeader : c.2.leader = false := by
    have h := congrArg CapMoveView2.leader hc.2
    change c.2.leader = r.leader at h
    exact h.trans hrl
  have hcLP2 : c.1.path2 = none := by
    have h := congrArg CapMoveView2.path2 hc.1
    change c.1.path2 = l.path2 at h
    exact h.trans hlp
  have hcRP2 : c.2.path2 = none := by
    have h := congrArg CapMoveView2.path2 hc.2
    change c.2.path2 = r.path2 at h
    exact h.trans hrp


  have hw0 := comparisonLeaderWall_eq_of_followers
    c.1 c.2 hcLLeader hcRLeader
  have hw : comparisonLeaderWall c.1 c.2 = c := by
    have heta : (c.1, c.2) = c := by
      apply Prod.ext <;> rfl
    exact hw0.trans heta


  have ht := singleUseControlTail_capMoveView2_of_none
    c.1 c.2 hcLP2 hcRP2
  change
    capMoveView2 (singleUseControlTail h2 c.1 c.2).1 = capMoveView2 c.1 /\
      capMoveView2 (singleUseControlTail h2 c.1 c.2).2 = capMoveView2 c.2 at ht


  unfold doneCaptureSigMove
  rw [hp]
  dsimp only
  rw [hdone]
  change capMoveView2 (singleUseControlTail h2 (comparisonLeaderWall c.1 c.2).1 (comparisonLeaderWall c.1 c.2).2).1 = capMoveView2 l ∧
    capMoveView2 (singleUseControlTail h2 (comparisonLeaderWall c.1 c.2).1 (comparisonLeaderWall c.1 c.2).2).2 = capMoveView2 r
  rw [hw]
  exact ⟨ht.1.trans hc.1, ht.2.trans hc.2⟩


private theorem authorizedDoneMove_capMoveView2_of_depart_followers
    (l r : AuthorizedAgentState 2)
    (hls : l.core.state = .depart)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path2 = none) (hrp : r.core.path2 = none) :
    let q := authorizedDoneMove h2 l r
    capMoveView2 q.1.core = capMoveView2 l.core /\
      capMoveView2 q.2.core = capMoveView2 r.core := by
  let q := authorizedDoneMove h2 l r
  let raw := doneCaptureSigMove h2 l.core r.core
  have hc := authorizedDoneMove_core h2 l r
  change (q.1.core, q.2.core) = raw at hc
  have hr := doneCaptureSigMove_capMoveView2_of_depart_followers
    l.core r.core hls hll hrl hlp hrp
  change capMoveView2 raw.1 = capMoveView2 l.core /\
    capMoveView2 raw.2 = capMoveView2 r.core at hr
  have hL := congrArg Prod.fst hc
  have hR := congrArg Prod.snd hc
  change q.1.core = raw.1 at hL
  change q.2.core = raw.2 at hR
  change capMoveView2 q.1.core = capMoveView2 l.core ∧ capMoveView2 q.2.core = capMoveView2 r.core
  rw [hL, hR]
  exact hr


/-- Public DONE-move certificate at the actual depart/depart cut.  `path` and
    `state` are deliberately not retained. -/
theorem authorizedDoneMove_depart_depart_cap_fields
    (l r : AuthorizedAgentState 2)
    (hls : l.core.state = .depart) (_hrs : r.core.state = .depart)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path2 = none) (hrp : r.core.path2 = none) :
    let q := authorizedDoneMove h2 l r
    q.1.core.label = l.core.label /\
      q.2.core.label = r.core.label /\
      q.1.core.count = l.core.count /\
      q.2.core.count = r.core.count /\
      q.1.core.wait = l.core.wait /\
      q.2.core.wait = r.core.wait /\
      q.1.core.leader = false /\
      q.2.core.leader = false /\
      q.1.core.reset_cmd = l.core.reset_cmd /\
      q.2.core.reset_cmd = r.core.reset_cmd /\
      q.1.core.path2 = none /\
      q.2.core.path2 = none := by
  let q := authorizedDoneMove h2 l r
  have hv := authorizedDoneMove_capMoveView2_of_depart_followers
    l r hls hll hrl hlp hrp
  change capMoveView2 q.1.core = capMoveView2 l.core /\
    capMoveView2 q.2.core = capMoveView2 r.core at hv


  have hLL := congrArg CapMoveView2.label hv.1
  have hRL := congrArg CapMoveView2.label hv.2
  have hLC := congrArg CapMoveView2.count hv.1
  have hRC := congrArg CapMoveView2.count hv.2
  have hLW := congrArg CapMoveView2.wait hv.1
  have hRW := congrArg CapMoveView2.wait hv.2
  have hLLeader := congrArg CapMoveView2.leader hv.1
  have hRLeader := congrArg CapMoveView2.leader hv.2
  have hLReset := congrArg CapMoveView2.resetCmd hv.1
  have hRReset := congrArg CapMoveView2.resetCmd hv.2
  have hLP2 := congrArg CapMoveView2.path2 hv.1
  have hRP2 := congrArg CapMoveView2.path2 hv.2


  change q.1.core.label = l.core.label at hLL
  change q.2.core.label = r.core.label at hRL
  change q.1.core.count = l.core.count at hLC
  change q.2.core.count = r.core.count at hRC
  change q.1.core.wait = l.core.wait at hLW
  change q.2.core.wait = r.core.wait at hRW
  change q.1.core.leader = l.core.leader at hLLeader
  change q.2.core.leader = r.core.leader at hRLeader
  change q.1.core.reset_cmd = l.core.reset_cmd at hLReset
  change q.2.core.reset_cmd = r.core.reset_cmd at hRReset
  change q.1.core.path2 = l.core.path2 at hLP2
  change q.2.core.path2 = r.core.path2 at hRP2


  exact ⟨hLL, hRL, hLC, hRC, hLW, hRW,
    hLLeader.trans hll, hRLeader.trans hrl,
    hLReset, hRReset, hLP2.trans hlp, hRP2.trans hrp⟩


/-! ## Reset wall and terminal-equality sanitation -/


private theorem sanitizeAuthorizedTerminalEqual_capMoveView2
    (u : AuthorizedAgentState 2) :
    capMoveView2 (sanitizeAuthorizedTerminalEqual h2 u).core =
      capMoveView2 u.core := by
  unfold sanitizeAuthorizedTerminalEqual capMoveView2
  split <;> rfl


private theorem sanitizeAuthorizedPair_capMoveView2
    (q : AuthorizedAgentState 2 × AuthorizedAgentState 2) :
    let s := sanitizeAuthorizedPair h2 q
    capMoveView2 s.1.core = capMoveView2 q.1.core /\
      capMoveView2 s.2.core = capMoveView2 q.2.core := by
  exact ⟨sanitizeAuthorizedTerminalEqual_capMoveView2 q.1,
    sanitizeAuthorizedTerminalEqual_capMoveView2 q.2⟩


/-- Exact proof-only pre-CHECK cut of `postWaitDone2`. -/
def postWaitDone2PreCheckCut
    (d e : Registers 2) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let g := genCleanAfterWait h2 (cell d) (cell e)
  let q1 := authorizedCleanSig h2 ⟨g.1, false⟩ ⟨g.2, false⟩
  let q2 := authorizedEliminateSig h2 q1.1 q1.2
  let q3 := authorizedDoneMove h2 q2.1 q2.2
  sanitizeAuthorizedPair h2 (preCheckResetWall q3.1 q3.2)


set_option maxHeartbeats 1600000 in
set_option maxRecDepth 32768 in
/-- The public R2 depart/depart certificate feeds DONE movement; its framed
    follower/reset/path2 facts make the reset wall inactive.  Sanitation is
    allowed to change state, but not these physical cap fields. -/
theorem postWaitDone2PreCheckCut_cap_frame
    (d e : Registers 2)
    (hd : d.label = 0) (he : e.label = 1)
    (hwd : d.wait = false) (hwe : e.wait = true) :
    let q4 := postWaitDone2PreCheckCut d e
    q4.1.core.label = 0 /\
      q4.2.core.label = 1 /\
      q4.2.core.count = e.count /\
      q4.1.core.wait = true /\
      q4.2.core.wait = true /\
      q4.1.core.leader = false /\
      q4.2.core.leader = false /\
      q4.1.core.reset_cmd = false /\
      q4.2.core.reset_cmd = false /\
      q4.1.core.path2 = none /\
      q4.2.core.path2 = none := by
  let g := genCleanAfterWait h2 (cell d) (cell e)
  let q1 := authorizedCleanSig h2 ⟨g.1, false⟩ ⟨g.2, false⟩
  let q2 := authorizedEliminateSig h2 q1.1 q1.2
  let q3 := authorizedDoneMove h2 q2.1 q2.2
  let qR := preCheckResetWall q3.1 q3.2
  let q4 := sanitizeAuthorizedPair h2 qR


  change q4.1.core.label = 0 /\
    q4.2.core.label = 1 /\
    q4.2.core.count = e.count /\
    q4.1.core.wait = true /\
    q4.2.core.wait = true /\
    q4.1.core.leader = false /\
    q4.2.core.leader = false /\
    q4.1.core.reset_cmd = false /\
    q4.2.core.reset_cmd = false /\
    q4.1.core.path2 = none /\
    q4.2.core.path2 = none


  have h2cut :=
    BirthShortDoneTerminalCapGeneralR2.postWaitDone2_gen_clean_eliminate_frame
      d e hd he hwd hwe
  change q2.1.core.label = 0 /\
    q2.2.core.label = 1 /\
    q2.2.core.count = e.count /\
    q2.1.core.wait = true /\
    q2.2.core.wait = true /\
    q2.1.core.leader = false /\
    q2.2.core.leader = false /\
    q2.1.core.reset_cmd = false /\
    q2.2.core.reset_cmd = false /\
    q2.1.core.state = .depart /\
    q2.2.core.state = .depart /\
    q2.1.core.path2 = none /\
    q2.2.core.path2 = none at h2cut
  rcases h2cut with
    ⟨h2LL, h2RL, h2RC, h2LW, h2RW,
      h2LLeader, h2RLeader, h2LReset, h2RReset,
      h2LS, h2RS, h2LP2, h2RP2⟩


  have h3 := authorizedDoneMove_depart_depart_cap_fields
    q2.1 q2.2 h2LS h2RS h2LLeader h2RLeader h2LP2 h2RP2
  change q3.1.core.label = q2.1.core.label /\
    q3.2.core.label = q2.2.core.label /\
    q3.1.core.count = q2.1.core.count /\
    q3.2.core.count = q2.2.core.count /\
    q3.1.core.wait = q2.1.core.wait /\
    q3.2.core.wait = q2.2.core.wait /\
    q3.1.core.leader = false /\
    q3.2.core.leader = false /\
    q3.1.core.reset_cmd = q2.1.core.reset_cmd /\
    q3.2.core.reset_cmd = q2.2.core.reset_cmd /\
    q3.1.core.path2 = none /\
    q3.2.core.path2 = none at h3
  rcases h3 with
    ⟨h3LL, h3RL, _h3LC, h3RC, h3LW, h3RW,
      h3LLeader, h3RLeader, h3LResetEq, h3RResetEq,
      h3LP2, h3RP2⟩


  have h3LReset : q3.1.core.reset_cmd = false :=
    h3LResetEq.trans h2LReset
  have h3RReset : q3.2.core.reset_cmd = false :=
    h3RResetEq.trans h2RReset


  have hwall : qR = (q3.1, q3.2) := by
    exact preCheckResetWall_eq_of_inactive
      q3.1 q3.2 h3LLeader h3LReset h3RReset


  have hsan := sanitizeAuthorizedPair_capMoveView2 qR
  change capMoveView2 q4.1.core = capMoveView2 qR.1.core /\
    capMoveView2 q4.2.core = capMoveView2 qR.2.core at hsan
  rw [hwall] at hsan


  have h4LL : q4.1.core.label = 0 := by
    have h := congrArg CapMoveView2.label hsan.1
    change q4.1.core.label = q3.1.core.label at h
    exact h.trans (h3LL.trans h2LL)
  have h4RL : q4.2.core.label = 1 := by
    have h := congrArg CapMoveView2.label hsan.2
    change q4.2.core.label = q3.2.core.label at h
    exact h.trans (h3RL.trans h2RL)
  have h4RC : q4.2.core.count = e.count := by
    have h := congrArg CapMoveView2.count hsan.2
    change q4.2.core.count = q3.2.core.count at h
    exact h.trans (h3RC.trans h2RC)
  have h4LW : q4.1.core.wait = true := by
    have h := congrArg CapMoveView2.wait hsan.1
    change q4.1.core.wait = q3.1.core.wait at h
    exact h.trans (h3LW.trans h2LW)
  have h4RW : q4.2.core.wait = true := by
    have h := congrArg CapMoveView2.wait hsan.2
    change q4.2.core.wait = q3.2.core.wait at h
    exact h.trans (h3RW.trans h2RW)
  have h4LLeader : q4.1.core.leader = false := by
    have h := congrArg CapMoveView2.leader hsan.1
    change q4.1.core.leader = q3.1.core.leader at h
    exact h.trans h3LLeader
  have h4RLeader : q4.2.core.leader = false := by
    have h := congrArg CapMoveView2.leader hsan.2
    change q4.2.core.leader = q3.2.core.leader at h
    exact h.trans h3RLeader
  have h4LReset : q4.1.core.reset_cmd = false := by
    have h := congrArg CapMoveView2.resetCmd hsan.1
    change q4.1.core.reset_cmd = q3.1.core.reset_cmd at h
    exact h.trans h3LReset
  have h4RReset : q4.2.core.reset_cmd = false := by
    have h := congrArg CapMoveView2.resetCmd hsan.2
    change q4.2.core.reset_cmd = q3.2.core.reset_cmd at h
    exact h.trans h3RReset
  have h4LP2 : q4.1.core.path2 = none := by
    have h := congrArg CapMoveView2.path2 hsan.1
    change q4.1.core.path2 = q3.1.core.path2 at h
    exact h.trans h3LP2
  have h4RP2 : q4.2.core.path2 = none := by
    have h := congrArg CapMoveView2.path2 hsan.2
    change q4.2.core.path2 = q3.2.core.path2 at h
    exact h.trans h3RP2


  exact ⟨h4LL, h4RL, h4RC, h4LW, h4RW,
    h4LLeader, h4RLeader, h4LReset, h4RReset, h4LP2, h4RP2⟩


/-! ## CHECK-local stable frames -/


private theorem checkSetReady_stable2 (u : AgentState 2) :
    checkStableView2 (checkSigSetReady u) = checkStableView2 u := by
  unfold checkSigSetReady checkStableView2
  repeat (first | rfl | split)


private theorem checkL_stable2 (u : AgentState 2) :
    checkStableView2 (checkSigCheckL h2 u) = checkStableView2 u := by
  unfold checkSigCheckL checkStableView2
  repeat (first | rfl | split)


private theorem checkR_stable2 (l r : AgentState 2) :
    checkStableView2 (checkSigCheckR h2 l r) = checkStableView2 r := by
  unfold checkSigCheckR checkStableView2
  repeat (first | rfl | split)


private theorem checkSetResult_stable2 (u : AgentState 2) :
    checkStableView2 (checkSigSetResult u) = checkStableView2 u := by
  unfold checkSigSetResult checkStableView2
  split <;> dsimp only <;> split <;> rfl


private theorem checkSetLeader_stable2 (u : AgentState 2) :
    checkStableView2 (checkSigSetLeader h2 u) = checkStableView2 u := by
  unfold checkSigSetLeader checkStableView2
  repeat (first | rfl | split)


private theorem checkSig_stable2 (l r : AgentState 2) :
    let q := checkSig h2 l r
    checkStableView2 q.1 = checkStableView2 l /\
      checkStableView2 q.2 = checkStableView2 r := by
  let l0 := checkSigSetReady l
  let r0 := checkSigSetReady r
  let l1 := checkSigCheckL h2 l0
  let r1 := checkSigCheckR h2 l1 r0
  let l2 := checkSigSetResult l1
  let r2 := checkSigSetResult r1
  let r3 := checkSigSetLeader h2 r2


  have hl0 := checkSetReady_stable2 l
  have hr0 := checkSetReady_stable2 r
  have hl1 := checkL_stable2 l0
  have hr1 := checkR_stable2 l1 r0
  have hl2 := checkSetResult_stable2 l1
  have hr2 := checkSetResult_stable2 r1
  have hr3 := checkSetLeader_stable2 r2


  change checkStableView2 l2 = checkStableView2 l /\
    checkStableView2 r3 = checkStableView2 r
  exact ⟨hl2.trans (hl1.trans hl0),
    hr3.trans (hr2.trans (hr1.trans hr0))⟩


private theorem authorizedCheckSig_stable2
    (l r : AuthorizedAgentState 2) :
    let q := authorizedCheckSig h2 l r
    checkStableView2 q.1.core = checkStableView2 l.core /\
      checkStableView2 q.2.core = checkStableView2 r.core := by
  change
    checkStableView2 (checkSig h2 l.core r.core).1 = checkStableView2 l.core /\
      checkStableView2 (checkSig h2 l.core r.core).2 = checkStableView2 r.core
  exact checkSig_stable2 l.core r.core


private theorem congestGuardCheck_stable2
    (l r : AuthorizedAgentState 2) :
    let q := congestGuardCheck h2 l r
    checkStableView2 q.1.core = checkStableView2 l.core /\
      checkStableView2 q.2.core = checkStableView2 r.core := by
  unfold congestGuardCheck
  split
  · exact ⟨rfl, rfl⟩
  · exact authorizedCheckSig_stable2 l r


private theorem preserveTossCheck_stable2
    (l r : AuthorizedAgentState 2) :
    let q := preserveTossCheck h2 l r
    checkStableView2 q.1.core = checkStableView2 l.core /\
      checkStableView2 q.2.core = checkStableView2 r.core := by
  unfold preserveTossCheck
  split
  · exact ⟨rfl, rfl⟩
  · exact congestGuardCheck_stable2 l r


private theorem preserveDoneCheck_stable2
    (l r : AuthorizedAgentState 2) :
    let q := preserveDoneCheck h2 l r
    checkStableView2 q.1.core = checkStableView2 l.core /\
      checkStableView2 q.2.core = checkStableView2 r.core := by
  unfold preserveDoneCheck
  split
  · exact ⟨rfl, rfl⟩
  · exact preserveTossCheck_stable2 l r


private theorem authorizedCheckSig_left_leader_eq
    (l r : AuthorizedAgentState 2) :
    (authorizedCheckSig h2 l r).1.core.leader = l.core.leader := by
  change (checkSig h2 l.core r.core).1.leader = l.core.leader
  exact PPLLVerify.checkSig_initiator_leader_eq h2 l.core r.core


private theorem congestGuardCheck_left_leader_eq
    (l r : AuthorizedAgentState 2) :
    (congestGuardCheck h2 l r).1.core.leader = l.core.leader := by
  unfold congestGuardCheck
  split
  · rfl
  · exact authorizedCheckSig_left_leader_eq l r


private theorem preserveTossCheck_left_leader_eq
    (l r : AuthorizedAgentState 2) :
    (preserveTossCheck h2 l r).1.core.leader = l.core.leader := by
  unfold preserveTossCheck
  split
  · rfl
  · exact congestGuardCheck_left_leader_eq l r


private theorem preserveDoneCheck_left_leader_eq
    (l r : AuthorizedAgentState 2) :
    (preserveDoneCheck h2 l r).1.core.leader = l.core.leader := by
  unfold preserveDoneCheck
  split
  · rfl
  · exact preserveTossCheck_left_leader_eq l r


/-- Exact proof-only cut after the real guarded CHECK and before metadata tail. -/
def postWaitDone2CheckCut
    (d e : Registers 2) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let q4 := postWaitDone2PreCheckCut d e
  preserveDoneCheck h2 q4.1 q4.2


set_option maxHeartbeats 1600000 in
set_option maxRecDepth 32768 in
/-- Post-CHECK cap frame.  Deliberately no claim about responder leader or
    either path2: CHECK is allowed to create both an actual responder leader
    and action-4/action-6 controls. -/
theorem postWaitDone2CheckCut_cap_frame
    (d e : Registers 2)
    (hd : d.label = 0) (he : e.label = 1)
    (hwd : d.wait = false) (hwe : e.wait = true) :
    let q5 := postWaitDone2CheckCut d e
    q5.1.core.label = 0 /\
      q5.2.core.label = 1 /\
      q5.2.core.count = e.count /\
      q5.1.core.wait = true /\
      q5.2.core.wait = true /\
      q5.1.core.leader = false /\
      q5.1.core.reset_cmd = false /\
      q5.2.core.reset_cmd = false := by
  have h4 := postWaitDone2PreCheckCut_cap_frame d e hd he hwd hwe
  unfold postWaitDone2CheckCut
  generalize hq4 : postWaitDone2PreCheckCut d e = q4 at h4 ⊢
  let q5 := preserveDoneCheck h2 q4.1 q4.2
  change q5.1.core.label = 0 /\
    q5.2.core.label = 1 /\
    q5.2.core.count = e.count /\
    q5.1.core.wait = true /\
    q5.2.core.wait = true /\
    q5.1.core.leader = false /\
    q5.1.core.reset_cmd = false /\
    q5.2.core.reset_cmd = false


  change q4.1.core.label = 0 /\
    q4.2.core.label = 1 /\
    q4.2.core.count = e.count /\
    q4.1.core.wait = true /\
    q4.2.core.wait = true /\
    q4.1.core.leader = false /\
    q4.2.core.leader = false /\
    q4.1.core.reset_cmd = false /\
    q4.2.core.reset_cmd = false /\
    q4.1.core.path2 = none /\
    q4.2.core.path2 = none at h4
  rcases h4 with
    ⟨h4LL, h4RL, h4RC, h4LW, h4RW,
      h4LLeader, _h4RLeader, h4LReset, h4RReset, _h4LP2, _h4RP2⟩


  have hs := preserveDoneCheck_stable2 q4.1 q4.2
  change checkStableView2 q5.1.core = checkStableView2 q4.1.core /\
    checkStableView2 q5.2.core = checkStableView2 q4.2.core at hs
  have hLeader := preserveDoneCheck_left_leader_eq q4.1 q4.2
  change q5.1.core.leader = q4.1.core.leader at hLeader


  have h5LL : q5.1.core.label = 0 := by
    have h := congrArg CheckStableView2.label hs.1
    change q5.1.core.label = q4.1.core.label at h
    exact h.trans h4LL
  have h5RL : q5.2.core.label = 1 := by
    have h := congrArg CheckStableView2.label hs.2
    change q5.2.core.label = q4.2.core.label at h
    exact h.trans h4RL
  have h5RC : q5.2.core.count = e.count := by
    have h := congrArg CheckStableView2.count hs.2
    change q5.2.core.count = q4.2.core.count at h
    exact h.trans h4RC
  have h5LW : q5.1.core.wait = true := by
    have h := congrArg CheckStableView2.wait hs.1
    change q5.1.core.wait = q4.1.core.wait at h
    exact h.trans h4LW
  have h5RW : q5.2.core.wait = true := by
    have h := congrArg CheckStableView2.wait hs.2
    change q5.2.core.wait = q4.2.core.wait at h
    exact h.trans h4RW
  have h5LLeader : q5.1.core.leader = false :=
    hLeader.trans h4LLeader
  have h5LReset : q5.1.core.reset_cmd = false := by
    have h := congrArg CheckStableView2.resetCmd hs.1
    change q5.1.core.reset_cmd = q4.1.core.reset_cmd at h
    exact h.trans h4LReset
  have h5RReset : q5.2.core.reset_cmd = false := by
    have h := congrArg CheckStableView2.resetCmd hs.2
    change q5.2.core.reset_cmd = q4.2.core.reset_cmd at h
    exact h.trans h4RReset


  exact ⟨h5LL, h5RL, h5RC, h5LW, h5RW,
    h5LLeader, h5LReset, h5RReset⟩


set_option maxHeartbeats 1600000 in
set_option maxRecDepth 32768 in
/-- Definitional bridge back to the unchanged R2 helper.  This is the point
    for the next module to start the metadata/suppress/stationary-WRITE suffix. -/
theorem postWaitDone2_factor_check_cut
    (a b d e : Registers 2) (pa pb : Bool) :
    BirthShortDoneTerminalCapGeneralR2.postWaitDone2 a b d e pa pb =
      let q5 := postWaitDone2CheckCut d e
      let q6 := afterCheckMetadataWidth h2 h2 hle2 q5.1 q5.2
      PPLLLeaderCreationCleanupRepair.markLeaderBirth
        (authBirth ⟨cell a, pa⟩ ⟨cell b, pb⟩ q6) q6 := by
  rfl


#print axioms BirthShortDoneTerminalCapGeneralR3.authorizedDoneMove_depart_depart_cap_fields
#print axioms BirthShortDoneTerminalCapGeneralR3.postWaitDone2PreCheckCut_cap_frame
#print axioms BirthShortDoneTerminalCapGeneralR3.postWaitDone2CheckCut_cap_frame
#print axioms BirthShortDoneTerminalCapGeneralR3.postWaitDone2_factor_check_cut


end BirthShortDoneTerminalCapGeneralR3

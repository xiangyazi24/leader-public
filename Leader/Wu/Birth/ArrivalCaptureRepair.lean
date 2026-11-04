import Leader.Wu.Birth.FreshEqualArrivalCounterexample

set_option autoImplicit false

namespace BirthArrivalCaptureRepair

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepNormalResetContract
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair
  BirthDisposalRouteInvariant BirthMismatchDisposalProducer

variable {psi kappa tau : Nat}

/-! A successful Algorithm-10 path arrival replaces the receiver's previous
comparison episode.  Its old path2 is cleared at that exact assignment, and
an aligned path is captured in CHECK_ready.  These assignments precede
Steps 2--5, so a sender-owned action four or five is still transported and
interpreted by the original control tail.  All leader walls, authorization,
CHECK, action-one COMPARE, entry disposal, suffix and expiry stages remain
in their established order.  The separately named host has the same finite
carrier; no event tags or future route promises are added to execution. -/

/-- The original successful Step-1 branch with two receiver assignments:
clear old path2 and capture an aligned incoming component.  A misaligned
arrival starts with none so it cannot inherit a receiver lock or decision. -/
def captureStep1 (l r : AgentState psi) : AgentState psi × AgentState psi :=
  match l.path, r.path with
  | .some pathLabel _, .bot =>
    if l.state ≠ .lock ∧ l.state ≠ .compare1 ∧ l.state ≠ .CHECK_ready then
      if r.state ≠ .produce ∨ pathLabel ≠ psi - 1 then
        ({ l with path := .bot, state := .none },
         { r with
           path := l.path
           path2 := none
           state := if r.label.val = pathLabel then .CHECK_ready else .none })
      else (l, r)
    else (l, r)
  | _, _ => (l, r)

/-- Capture keeps the original path movement exactly and never changes the
sender's control token.  No unrelated endpoint register is cleared. -/
theorem captureStep1_path_and_sender_control (l r : AgentState psi) :
    let q := captureStep1 l r
    let old := sigMoveStep1 l r
    q.1.path = old.1.path ∧ q.2.path = old.2.path ∧
      q.1.path2 = l.path2 ∧ q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.leader = l.leader ∧ q.2.leader = r.leader := by
  cases hL : l.path <;> cases hR : r.path
  all_goals simp only [captureStep1, sigMoveStep1, hL, hR]
  all_goals repeat split
  all_goals simp_all

/-- An actual matched transfer has a fresh capture state and no receiver-old
control, for arbitrary previous receiver state and path2 contents. -/
theorem captureStep1_matched (l r : AgentState psi) (label bit : Nat)
    (hlpath : l.path = .some label bit) (hrpath : r.path = .bot)
    (hlfree : l.state ≠ .lock ∧ l.state ≠ .compare1 ∧ l.state ≠ .CHECK_ready)
    (hrfree : r.state ≠ .produce ∨ label ≠ psi - 1)
    (halign : r.label.val = label) :
    let q := captureStep1 l r
    q.1.path = .bot ∧ q.2.path = l.path ∧ q.2.state = .CHECK_ready ∧
      q.2.path2 = none ∧ q.1.path2 = l.path2 := by
  simp [captureStep1, hlpath, hrpath, hlfree, hrfree, halign]

/-- Step 1 has finished after the capture assignment.  This idempotence is
used only to reuse the original transfer-domain theorem. -/
private theorem captureStep1_fixed (l r : AgentState psi) :
    sigMoveStep1 (captureStep1 l r).1 (captureStep1 l r).2 = captureStep1 l r := by
  cases hL : l.path <;> cases hR : r.path
  all_goals simp only [captureStep1, hL, hR]
  all_goals repeat split
  all_goals simp_all [sigMoveStep1]

/-- Capture moves only an already bounded path and clears a bounded token. -/
theorem captureStep1_inProtocolDomain (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := captureStep1 l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  cases hL : l.path <;> cases hR : r.path
  all_goals simp only [captureStep1, hL, hR]
  all_goals repeat split
  all_goals simp_all [AgentState.inProtocolDomain]

/-- Only Step 1 is substituted; all four path2 movement rows are original. -/
def captureTransfers (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let q0 := captureStep1 l r
  let q1 := sigMoveStep2 q0.1 q0.2
  let q2 := sigMoveStep3 q1.1 q1.2
  let q3 := sigMoveStep4 q2.1 q2.2
  sigMoveStep5 q3.1 q3.2

/-- The unchanged admission guards also preserve every occupied receiver,
including an already checked predecessor in a resident comparison pair. -/
theorem captureStep1_of_occupied (l r : AgentState psi) (hr : r.path ≠ .bot) :
    captureStep1 l r = sigMoveStep1 l r := by
  cases hL : l.path <;> cases hR : r.path <;>
    simp_all [captureStep1, sigMoveStep1]

/-- An actual Step-1 transfer initializes both states independently of all
old receiver states and tokens.  This is a current transition event. -/
theorem captureStep1_moved_states (l r : AgentState psi)
    (hm : pathMovedRight l r (sigMoveStep1 l r).1 (sigMoveStep1 l r).2 = true) :
    let q := captureStep1 l r
    q.1.state = .none ∧ (q.2.state = .none ∨ q.2.state = .CHECK_ready) ∧
      q.1.path = .bot ∧ q.2.path = l.path ∧ q.2.path2 = none := by
  cases hL : l.path <;> cases hR : r.path
  all_goals simp only [captureStep1, sigMoveStep1, hL, hR] at hm ⊢
  all_goals repeat split
  all_goals simp_all [pathMovedRight]

/-- The four retained path2 rows do not change either state or main path. -/
private theorem captureTransfers_frame (l r : AgentState psi) :
    let q := captureTransfers l r
    let b := captureStep1 l r
    q.1.state = b.1.state ∧ q.2.state = b.2.state ∧
      q.1.path = b.1.path ∧ q.2.path = b.2.path := by
  unfold captureTransfers
  generalize captureStep1 l r = b
  unfold sigMoveStep2 sigMoveStep3 sigMoveStep4 sigMoveStep5
  dsimp only
  repeat (first | exact ⟨rfl, rfl, rfl, rfl⟩ | split)

/-- A source-owned action four survives receiver cleanup because Step5
runs afterwards.  Arbitrary receiver-old path2 contents cannot override it. -/
theorem captureTransfers_source_action4 (l r : AgentState psi) (label bit : Nat)
    (hlpath : l.path = .some label bit) (hrpath : r.path = .bot)
    (hlfree : l.state ≠ .lock ∧ l.state ≠ .compare1 ∧ l.state ≠ .CHECK_ready)
    (hrfree : r.state ≠ .produce ∨ label ≠ psi - 1)
    (hp : l.path2 = some ⟨0, 0, 0, 4⟩) :
    let q := captureTransfers l r
    q.1.path2 = none ∧ q.2.path2 = some ⟨0, 0, 0, 4⟩ ∧
      q.2.path = l.path := by
  simp [captureTransfers, captureStep1, hlpath, hrpath, hlfree, hrfree, hp,
    sigMoveStep2, sigMoveStep3, sigMoveStep4, sigMoveStep5]

private theorem applyControl_not_equal (hpsi : psi > 0) (u : AgentState psi)
    (hu : u.state ≠ .equal) : (sigMoveApplyControl hpsi u).state ≠ .equal := by
  unfold sigMoveApplyControl
  split
  · repeat split <;> simp_all
  · exact hu

private theorem controlTail_not_equal (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.state ≠ .equal) (hr : r.state ≠ .equal) :
    let q := sigMoveControlTail hpsi l r
    q.1.state ≠ .equal ∧ q.2.state ≠ .equal := by
  have hL := applyControl_not_equal hpsi l hl
  have hR := applyControl_not_equal hpsi r hr
  unfold sigMoveControlTail
  dsimp only
  split
  · split
    · exact ⟨by change MainState.depart ≠ .equal; decide, hR⟩
    · exact ⟨hL, hR⟩
  · exact ⟨hL, hR⟩

private theorem leaderWall_not_equal (l r : AgentState psi)
    (hl : l.state ≠ .equal) (hr : r.state ≠ .equal) :
    let q := comparisonLeaderWall l r
    q.1.state ≠ .equal ∧ q.2.state ≠ .equal := by
  unfold comparisonLeaderWall
  dsimp only
  split <;> split <;> simp_all [clearComparisonSignal]

private theorem domain_of_count_payload_eq_wall
    (u v : AgentState psi) (hu : u.inProtocolDomain kappa)
    (hc : v.count = u.count) (hp : PayloadView.ofState v = PayloadView.ofState u) :
    v.inProtocolDomain kappa := by
  rw [inProtocolDomain_iff] at hu ⊢
  exact ⟨by simpa [hc] using hu.1, by simpa [hp] using hu.2⟩

private theorem sigMoveApplyControl_count_payload_wall (hpsi : psi > 0)
    (u : AgentState psi) :
    (sigMoveApplyControl hpsi u).count = u.count ∧
      PayloadView.ofState (sigMoveApplyControl hpsi u) =
        PayloadView.ofState u := by
  simp only [sigMoveApplyControl]
  repeat (first | constructor | rfl | split)

private theorem sigMoveControlTail_frame (hpsi : psi > 0)
    (l r : AgentState psi) :
    let q := sigMoveControlTail hpsi l r
    (q.1.count = l.count ∧
        PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧
        PayloadView.ofState q.2 = PayloadView.ofState r) := by
  let l0 := sigMoveApplyControl hpsi l
  let r0 := sigMoveApplyControl hpsi r
  let l1 := if r0.state = .depart then
    if l0.label.val < psi - 1 ∧ l0.state = .CHECK_ready then
      { l0 with state := .depart }
    else l0
  else l0
  have hl0 := sigMoveApplyControl_count_payload_wall hpsi l
  have hr0 := sigMoveApplyControl_count_payload_wall hpsi r
  have hl1 : l1.count = l0.count ∧
      PayloadView.ofState l1 = PayloadView.ofState l0 := by
    dsimp only [l1]
    split
    · split
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  change (l1.count = l.count ∧
      PayloadView.ofState l1 = PayloadView.ofState l) ∧
    (r0.count = r.count ∧ PayloadView.ofState r0 = PayloadView.ofState r)
  exact ⟨⟨hl1.1.trans hl0.1, hl1.2.trans hl0.2⟩, hr0⟩

private theorem sigMoveControlTail_inProtocolDomain { psi kappa : Nat }
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := sigMoveControlTail hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let q := sigMoveControlTail hpsi l r
  have hframe := sigMoveControlTail_frame hpsi l r
  exact ⟨domain_of_count_payload_eq_wall l q.1 hl hframe.1.1 hframe.1.2,
    domain_of_count_payload_eq_wall r q.2 hr hframe.2.1 hframe.2.2⟩

private theorem sigMoveTransfers_inProtocolDomain { psi kappa : Nat }
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := sigMoveTransfers l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let moved := sigMoveTransfers l r
  let out := sigMoveControlTail hpsi moved.1 moved.2
  have hout := sigMove_inProtocolDomain hpsi l r hl hr
  change out.1.inProtocolDomain kappa ∧ out.2.inProtocolDomain kappa at hout
  have hframe := sigMoveControlTail_frame hpsi moved.1 moved.2
  exact ⟨domain_of_count_payload_eq_wall out.1 moved.1 hout.1
      hframe.1.1.symm hframe.1.2.symm,
    domain_of_count_payload_eq_wall out.2 moved.2 hout.2
      hframe.2.1.symm hframe.2.2.symm⟩

/-- The extra Step-1 call in this equality is inert by the previous lemma;
the executable definition itself contains only the single capture call. -/
private theorem captureTransfers_eq (l r : AgentState psi) :
    captureTransfers l r =
      sigMoveTransfers (captureStep1 l r).1 (captureStep1 l r).2 := by
  simp only [captureTransfers, sigMoveTransfers, captureStep1_fixed]

/-- Domain closure transfers through the original bounded path2 rows. -/
theorem captureTransfers_inProtocolDomain (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := captureTransfers l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  rw [captureTransfers_eq]
  have h := captureStep1_inProtocolDomain l r hl hr
  exact sigMoveTransfers_inProtocolDomain hpsi _ _ h.1 h.2

/-- The leader preclear and post-transfer wall retain their original order
around the substituted carrier movement. -/
def captureSigMoveLeaderWall (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let q0 := sigMoveLeaderPreclear hpsi l r
  let moved := captureTransfers q0.1 q0.2
  let walled := comparisonLeaderWall moved.1 moved.2
  sigMoveControlTail hpsi walled.1 walled.2

/-- No equality inherited before an actual arrival survives the complete
raw SIGMOVE, including arbitrary incoming path2 actions and leader walls. -/
theorem captureSigMoveLeaderWall_moved_not_equal
    (hpsi : psi > 0) (l r : AgentState psi)
    (hm : let b := sigMoveLeaderPreclear hpsi l r
      pathMovedRight b.1 b.2 (sigMoveStep1 b.1 b.2).1 (sigMoveStep1 b.1 b.2).2 = true) :
    let q := captureSigMoveLeaderWall hpsi l r
    q.1.state ≠ .equal ∧ q.2.state ≠ .equal := by
  let b := sigMoveLeaderPreclear hpsi l r
  have h := captureStep1_moved_states b.1 b.2 hm
  have hf := captureTransfers_frame b.1 b.2
  have hl : (captureTransfers b.1 b.2).1.state ≠ .equal := by
    rw [hf.1, h.1]
    decide
  have hr : (captureTransfers b.1 b.2).2.state ≠ .equal := by
    rw [hf.2.1]
    rcases h.2.1 with hs | hs <;> rw [hs] <;> decide
  have hw := leaderWall_not_equal _ _ hl hr
  exact controlTail_not_equal hpsi _ _ hw.1 hw.2

/-- No numeric register is enlarged by the complete captured SIGMOVE. -/
theorem captureSigMoveLeaderWall_inProtocolDomain
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := captureSigMoveLeaderWall hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let l0 := if l.leader = true ∨ incompleteLeftLeaderBoundary hpsi l r then
    clearComparisonSignal l else l
  let r0 := clearIfLeader r
  have hl0 : l0.inProtocolDomain kappa := by
    unfold l0
    split
    · exact clearComparisonSignal_inProtocolDomain l hl
    · exact hl
  have hr0 : r0.inProtocolDomain kappa := by
    unfold r0 clearIfLeader
    split
    · exact clearComparisonSignal_inProtocolDomain r hr
    · exact hr
  have hm := captureTransfers_inProtocolDomain hpsi l0 r0 hl0 hr0
  let m := captureTransfers l0 r0
  have hw := comparisonLeaderWall_inProtocolDomain m.1 m.2 hm.1 hm.2
  exact sigMoveControlTail_inProtocolDomain hpsi _ _ hw.1 hw.2

/-- The original authorization transport, using the unchanged path-move
predicate on the newly computed raw output. -/
def authorizedCaptureSigMove (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := captureSigMoveLeaderWall hpsi l.core r.core
  if pathMovedRight l.core r.core q.1 q.2 = true then
    let receiverPermit := match l.core.path with
      | .some 0 _ =>
          if stableSuccessor hpsi l.core r.core then
            l.path0Crossed || stableWrap hpsi l.core r.core
          else false
      | _ => false
    (⟨q.1, false⟩, ⟨q.2, normalizePermit q.2 receiverPermit⟩)
  else
    (⟨q.1, reconcilePermit l q.1⟩, ⟨q.2, reconcilePermit r q.2⟩)

/-- The authorization adapter changes only the existing permit bit. -/
theorem authorizedCaptureSigMove_core (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    let q := authorizedCaptureSigMove hpsi l r
    (q.1.core, q.2.core) = captureSigMoveLeaderWall hpsi l.core r.core := by
  unfold authorizedCaptureSigMove
  dsimp only
  split <;> rfl

theorem authorizedCaptureSigMove_inProtocolDomain
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := authorizedCaptureSigMove hpsi l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  have h := captureSigMoveLeaderWall_inProtocolDomain hpsi l.core r.core hl hr
  unfold authorizedCaptureSigMove
  dsimp only
  split <;> exact h

/-- The exact ordinary prefix through GENSIG, CLEAN and ELIMINATE. -/
def arrivalBeforeMove (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  authorizedEliminateSig hpsi q2.1 q2.2

private theorem arrivalBeforeMove_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := arrivalBeforeMove hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  have h0 := authorizedPPsiLeaderResetProbeWall_inProtocolDomain hpsi l r hl hr
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  have h1 := authorizedReconcile_inProtocolDomain (genSigSaturated hpsi kappa) q0.1 q0.2
    (genSigSaturated_inProtocolDomain hpsi q0.1.core q0.2.core h0.1 h0.2)
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain (cleanSig hpsi) q1.1 q1.2
    (cleanSig_inProtocolDomain hpsi q1.1.core q1.2.core h1.1 h1.2)
  exact authorizedReconcile_inProtocolDomain (eliminateSig hpsi) q2.1 q2.2
    (eliminateSig_inProtocolDomain hpsi q2.1.core q2.2.core h2.1 h2.2)

/-- The actual sanitized CHECK boundary of the capture host. -/
def arrivalBeforeCheck (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let b := arrivalBeforeMove hpsi kappa l r
  let q := authorizedCaptureSigMove hpsi b.1 b.2
  sanitizeAuthorizedPair hpsi (preCheckResetWall q.1 q.2)

attribute [local irreducible] arrivalBeforeMove authorizedCaptureSigMove

theorem arrivalBeforeCheck_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := arrivalBeforeCheck hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let b := arrivalBeforeMove hpsi kappa l r
  have hb := arrivalBeforeMove_inProtocolDomain hpsi kappa l r hl hr
  have hm := authorizedCaptureSigMove_inProtocolDomain hpsi b.1 b.2 hb.1 hb.2
  let m := authorizedCaptureSigMove hpsi b.1 b.2
  have hw := preCheckResetWall_inProtocolDomain m.1 m.2 hm.1 hm.2
  exact ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi _ hw.1,
    sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi _ hw.2⟩

private theorem resetWall_not_equal (l r : AuthorizedAgentState psi)
    (hl : l.core.state ≠ .equal) (hr : r.core.state ≠ .equal) :
    let q := preCheckResetWall l r
    q.1.core.state ≠ .equal ∧ q.2.core.state ≠ .equal := by
  unfold preCheckResetWall
  dsimp only
  split <;> split <;> simp_all [clearAuthorizedComparison, clearComparisonSignal]

private theorem sanitize_not_equal (hpsi : psi > 0) (u : AuthorizedAgentState psi)
    (hu : u.core.state ≠ .equal) :
    (sanitizeAuthorizedTerminalEqual hpsi u).core.state ≠ .equal := by
  simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual, hu]

/-- The actual ordinary pre-CHECK boundary excludes pre-arrival equality
on both endpoints, for arbitrary receiver state and path2.  The premise is
computed at the actual Step-1 input after the retained prefix and leader
preclear; it is not a future route or component-origin promise. -/
theorem arrivalBeforeCheck_moved_not_equal
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hm : let b := arrivalBeforeMove hpsi kappa l r
      let p := sigMoveLeaderPreclear hpsi b.1.core b.2.core
      pathMovedRight p.1 p.2 (sigMoveStep1 p.1 p.2).1 (sigMoveStep1 p.1 p.2).2 = true) :
    let q := arrivalBeforeCheck hpsi kappa l r
    q.1.core.state ≠ .equal ∧ q.2.core.state ≠ .equal := by
  let b := arrivalBeforeMove hpsi kappa l r
  have hraw := captureSigMoveLeaderWall_moved_not_equal hpsi b.1.core b.2.core hm
  have hcore := authorizedCaptureSigMove_core hpsi b.1 b.2
  have hl : (authorizedCaptureSigMove hpsi b.1 b.2).1.core.state ≠ .equal := by
    have h := congrArg (fun q : AgentState psi × AgentState psi => q.1.state) hcore
    rw [h]
    exact hraw.1
  have hr : (authorizedCaptureSigMove hpsi b.1 b.2).2.core.state ≠ .equal := by
    have h := congrArg (fun q : AgentState psi × AgentState psi => q.2.state) hcore
    rw [h]
    exact hraw.2
  have hw := resetWall_not_equal _ _ hl hr
  exact ⟨sanitize_not_equal hpsi _ hw.1, sanitize_not_equal hpsi _ hw.2⟩

/-- The action-one host with only the arrival-capture assignment added to its
ordinary prefix.  Existing deletion has the same first-branch priority. -/
def arrivalGuardedAuthorizedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then (l0, r0)
  else
    let beforeCheck := arrivalBeforeCheck hpsi kappa l0 r0
    let afterCheck := congestGuardCheck hpsi beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born (actionOneAfterCheckSuffix hpsi afterCheck.1 afterCheck.2)

attribute [local irreducible] arrivalBeforeCheck actionOneAfterCheckSuffix

theorem arrivalGuardedAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := arrivalGuardedAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold arrivalGuardedAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let b := arrivalBeforeCheck hpsi kappa l0 r0
      have hb := arrivalBeforeCheck_inProtocolDomain hpsi kappa l0 r0 hl0 hr0
      let c := congestGuardCheck hpsi b.1 b.2
      have hc := congestGuardCheck_inProtocolDomain hpsi b.1 b.2 hb.1 hb.2
      exact markLeaderBirth_inProtocolDomain _ _
        (actionOneAfterCheckSuffix_inProtocolDomain hpsi kappa c.1 c.2 hc.1 hc.2)

/-- Reify the exact authorized transition on the unchanged bounded carrier. -/
def arrivalGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa × AuthorizedBoundedAgentState psi kappa :=
  let q := arrivalGuardedAuthorizedTransition hpsi kappa l.erase r.erase
  let hq := arrivalGuardedAuthorizedTransition_inProtocolDomain hpsi kappa
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem erase_arrivalGuardedBoundedTransition
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := arrivalGuardedBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) = arrivalGuardedAuthorizedTransition hpsi kappa l.erase r.erase := by
  unfold arrivalGuardedBoundedTransition
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

/-- Entry disposal, finite expiry and final leader-signal initialization use
exactly their established definitions and prepared inputs. -/
def arrivalFullTransition (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := arrivalGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  initializeFollowerPairBirthSignals l0 r0
    (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)

private theorem arrivalGuarded_eq_of_active (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (ha : deletionActive (normalizeDeletion l) = true ∨
      deletionActive (normalizeDeletion r) = true) :
    arrivalGuardedAuthorizedTransition hpsi kappa l r =
      actionOneGuardedAuthorizedTransition hpsi kappa l r := by
  unfold arrivalGuardedAuthorizedTransition actionOneGuardedAuthorizedTransition
  dsimp only
  by_cases hr : deletionActive (normalizeDeletion r) = true
  · simp only [hr, ↓reduceIte]
  · have hl : deletionActive (normalizeDeletion l) = true := ha.resolve_right hr
    simp only [hr, hl, ↓reduceIte]

attribute [local irreducible] actionOneGuardedBoundedTransition

/-- Existing disposal has exactly the old complete pair transition,
including expiry and leader-signal initialization.  The arrival assignment
therefore preserves the checked incoming deletion and outgoing pinning rows. -/
theorem arrivalFull_eq_actionOneFull_of_due
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (ha : DisposalDue hpsi l.core.erase ∨ DisposalDue hpsi r.core.erase) :
    arrivalFullTransition hpsi kappa tau l r = actionOneFullTransition hpsi kappa tau l r := by
  have hactive : deletionActive (preparedInput hpsi l.core.erase) = true ∨
      deletionActive (preparedInput hpsi r.core.erase) = true :=
    ha.imp (prepared_due_active hpsi l.core.erase) (prepared_due_active hpsi r.core.erase)
  have hr : arrivalGuardedAuthorizedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core).erase
      (prepareBoundedDisposal hpsi r.core).erase =
      actionOneGuardedAuthorizedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core).erase
        (prepareBoundedDisposal hpsi r.core).erase := by
    rw [erase_prepareBoundedDisposal, erase_prepareBoundedDisposal]
    exact arrivalGuarded_eq_of_active hpsi kappa _ _ hactive
  have hb : arrivalGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) =
      actionOneGuardedBoundedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) := by
    unfold arrivalGuardedBoundedTransition actionOneGuardedBoundedTransition
    dsimp only
    simp only [hr]
  unfold arrivalFullTransition actionOneFullTransition
  dsimp only [prepareExpiringDisposal]
  rw [hb]

/-- Source action four is interpreted after capture and receiver cleanup.
On an admitted terminal arrival it still yields a present elimination
carrier, irrespective of the old receiver token or main state. -/
theorem capture_terminal_source_action4
    (hpsi : psi > 0) (l r : AgentState psi) (bit : Nat)
    (hlpath : l.path = .some (psi - 1) bit) (hrpath : r.path = .bot)
    (hlfree : l.state ≠ .lock ∧ l.state ≠ .compare1 ∧ l.state ≠ .CHECK_ready)
    (hrfree : r.state ≠ .produce)
    (hp : l.path2 = some ⟨0, 0, 0, 4⟩)
    (hrlabel : r.label = ⟨psi - 1, by omega⟩)
    (hlleader : l.leader = false) (hrleader : r.leader = false) :
    let q := captureSigMoveLeaderWall hpsi l r
    q.2.path = l.path ∧ q.2.path2 = some ⟨0, 0, 0, 4⟩ ∧
      q.2.state = .eliminate_signal := by
  have hboundary : ¬incompleteLeftLeaderBoundary hpsi l r := by
    intro h
    simpa [hrleader] using h.1
  simp [captureSigMoveLeaderWall, sigMoveLeaderPreclear, hlleader, hrleader,
    hboundary, clearIfLeader, captureTransfers, captureStep1, hlpath, hrpath,
    hlfree, hrfree, hp, hrlabel, sigMoveStep2, sigMoveStep3, sigMoveStep4,
    sigMoveStep5, comparisonLeaderWall, sigMoveControlTail, sigMoveApplyControl]

end BirthArrivalCaptureRepair

#print axioms BirthArrivalCaptureRepair.captureStep1_path_and_sender_control
#print axioms BirthArrivalCaptureRepair.captureStep1_matched
#print axioms BirthArrivalCaptureRepair.captureStep1_inProtocolDomain
#print axioms BirthArrivalCaptureRepair.captureSigMoveLeaderWall_inProtocolDomain
#print axioms BirthArrivalCaptureRepair.arrivalGuardedAuthorizedTransition_inProtocolDomain
#print axioms BirthArrivalCaptureRepair.erase_arrivalGuardedBoundedTransition

#print axioms BirthArrivalCaptureRepair.captureStep1_moved_states
#print axioms BirthArrivalCaptureRepair.captureStep1_of_occupied
#print axioms BirthArrivalCaptureRepair.captureTransfers_source_action4
#print axioms BirthArrivalCaptureRepair.arrivalBeforeCheck_moved_not_equal
#print axioms BirthArrivalCaptureRepair.arrivalFull_eq_actionOneFull_of_due
#print axioms BirthArrivalCaptureRepair.capture_terminal_source_action4

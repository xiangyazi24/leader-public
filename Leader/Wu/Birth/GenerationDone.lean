import Leader.Wu.Birth.SingleUseReleaseRepair

/-!
# Preserve the current backward-generation acknowledgement phase

The comparator is the frozen single-use-release host. Only two current-state
branches change: CHECK preserves `done` alongside its existing toss guard, and
Step1 cannot transport a `done` sender before the predecessor's GEN consumes
that phase. Steps2--5, single-use control, leader walls and cleanup stay live.
No new carrier field or episode identifier is introduced.
-/

set_option autoImplicit false

namespace BirthGenerationDone

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepNormalResetContract
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair
  BirthDisposalRouteInvariant BirthMismatchDisposalProducer BirthArrivalCaptureRepair
  BirthGenerationControlRepair BirthTossCheckPreservationRepair BirthSingleUseReleaseRepair

variable {psi kappa tau : Nat}

/-- Preserve a current GEN acknowledgement before the next source edge can
consume it. The pre-existing toss and congestion guards are retained exactly. -/
def preserveDoneCheck (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  if l.core.state = .done ∨ r.core.state = .done then (l, r)
  else preserveTossCheck hpsi l r

/-- The protected phase is observed now, without a future ACK promise. -/
theorem preserveDoneCheck_of_done (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : l.core.state = .done ∨ r.core.state = .done) :
    preserveDoneCheck hpsi l r = (l, r) := by simp [preserveDoneCheck, h]

/-- Every actual CHECK input with no done executes the frozen comparator. -/
theorem preserveDoneCheck_of_no_done (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.state ≠ .done) (hr : r.core.state ≠ .done) :
    preserveDoneCheck hpsi l r = preserveTossCheck hpsi l r := by
  simp [preserveDoneCheck, hl, hr]

/-- Protecting done cannot preempt the existing toss-to-DISAPPEAR handoff. -/
theorem preserveDoneCheck_of_toss (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : l.core.state = .toss ∨ r.core.state = .toss) :
    preserveDoneCheck hpsi l r = (l, r) := by
  unfold preserveDoneCheck
  split
  · rfl
  · exact preserveTossCheck_of_toss hpsi l r h

theorem preserveDoneCheck_inProtocolDomain (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := preserveDoneCheck hpsi l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  unfold preserveDoneCheck
  split
  · exact ⟨hl, hr⟩
  · exact preserveTossCheck_inProtocolDomain hpsi l r hl hr

/-- Only current done blocks the captured Step1 transfer. An ACK changes the
phase to depart in GEN, so its later Step1 call uses the original transport. -/
def holdDoneStep1 (l r : AgentState psi) : AgentState psi × AgentState psi :=
  if l.state = .done then (l, r) else captureStep1 l r

theorem holdDoneStep1_of_done (l r : AgentState psi) (hl : l.state = .done) :
    holdDoneStep1 l r = (l, r) := by simp [holdDoneStep1, hl]

theorem holdDoneStep1_of_no_done (l r : AgentState psi) (hl : l.state ≠ .done) :
    holdDoneStep1 l r = captureStep1 l r := by simp [holdDoneStep1, hl]

/-- A consumed ACK is immediately eligible for the original Step1 guards. -/
theorem holdDoneStep1_of_depart (l r : AgentState psi) (hl : l.state = .depart) :
    holdDoneStep1 l r = captureStep1 l r := by simp [holdDoneStep1, hl]

/-- The four control-transfer rows are copied by direct function application,
not guarded together with the main payload transfer. -/
def controlTransfers (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let q := sigMoveStep2 l r
  let q := sigMoveStep3 q.1 q.2
  let q := sigMoveStep4 q.1 q.2
  sigMoveStep5 q.1 q.2

/-- Exact source composition: only the first assignment is substituted. -/
def doneTransfers (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let q := holdDoneStep1 l r
  controlTransfers q.1 q.2

/-- Current done suppresses Step1 while every control row still executes. -/
theorem doneTransfers_of_done (l r : AgentState psi) (hl : l.state = .done) :
    doneTransfers l r = controlTransfers l r := by
  simp [doneTransfers, holdDoneStep1_of_done l r hl]

theorem doneTransfers_of_no_done (l r : AgentState psi) (hl : l.state ≠ .done) :
    doneTransfers l r = captureTransfers l r := by
  simp [doneTransfers, holdDoneStep1, hl, controlTransfers, captureTransfers]

private theorem step2_set_state (l r : AgentState psi) (s : MainState) :
    sigMoveStep2 { l with state := s } r =
      ({ (sigMoveStep2 l r).1 with state := s }, (sigMoveStep2 l r).2) := by
  cases hp : l.path2
  · simp [sigMoveStep2, hp]
  · simp only [sigMoveStep2, hp]
    split <;> simp_all

private theorem step3_set_state (l r : AgentState psi) (s : MainState) :
    sigMoveStep3 { l with state := s } r =
      ({ (sigMoveStep3 l r).1 with state := s }, (sigMoveStep3 l r).2) := by
  cases hp : r.path2
  · simp [sigMoveStep3, hp]
  · simp only [sigMoveStep3, hp]
    split <;> simp_all

private theorem step4_set_state (l r : AgentState psi) (s : MainState) :
    sigMoveStep4 { l with state := s } r =
      ({ (sigMoveStep4 l r).1 with state := s }, (sigMoveStep4 l r).2) := by
  cases hp : r.path2
  · simp [sigMoveStep4, hp]
  · simp only [sigMoveStep4, hp]
    split <;> simp_all

private theorem step5_set_state (l r : AgentState psi) (s : MainState) :
    sigMoveStep5 { l with state := s } r =
      ({ (sigMoveStep5 l r).1 with state := s }, (sigMoveStep5 l r).2) := by
  cases hp : l.path2
  · simp [sigMoveStep5, hp]
  · simp only [sigMoveStep5, hp]
    split <;> simp_all

private theorem controlTransfers_set_state (l r : AgentState psi) (s : MainState) :
    controlTransfers { l with state := s } r =
      ({ (controlTransfers l r).1 with state := s }, (controlTransfers l r).2) := by
  simp only [controlTransfers, step2_set_state, step3_set_state, step4_set_state, step5_set_state]

/-- The retained control rows never alter either main payload or phase. -/
theorem controlTransfers_phase_path (l r : AgentState psi) :
    let q := controlTransfers l r
    q.1.state = l.state ∧ q.2.state = r.state ∧
      q.1.path = l.path ∧ q.2.path = r.path := by
  unfold controlTransfers sigMoveStep2 sigMoveStep3 sigMoveStep4 sigMoveStep5
  dsimp only
  repeat (first | exact ⟨rfl, rfl, rfl, rfl⟩ | split)
  all_goals simp_all

private theorem controlTransfers_inProtocolDomain (hpsi : psi > 0)
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := controlTransfers l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hlocked : ({ l with state := .CHECK_ready } : AgentState psi).inProtocolDomain kappa := hl
  have h := captureTransfers_inProtocolDomain hpsi { l with state := .CHECK_ready } r hlocked hr
  have hc : captureStep1 { l with state := .CHECK_ready } r =
      ({ l with state := .CHECK_ready }, r) := by
    cases l.path <;> cases hq : r.path <;> simp [captureStep1, hq]
  change (controlTransfers (captureStep1 { l with state := .CHECK_ready } r).1
    (captureStep1 { l with state := .CHECK_ready } r).2).1.inProtocolDomain kappa ∧
    (controlTransfers (captureStep1 { l with state := .CHECK_ready } r).1
    (captureStep1 { l with state := .CHECK_ready } r).2).2.inProtocolDomain kappa at h
  rw [hc] at h
  rw [controlTransfers_set_state] at h
  exact h

theorem doneTransfers_inProtocolDomain (hpsi : psi > 0)
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := doneTransfers l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  by_cases hs : l.state = .done
  · rw [doneTransfers_of_done l r hs]
    exact controlTransfers_inProtocolDomain hpsi l r hl hr
  · rw [doneTransfers_of_no_done l r hs]
    exact captureTransfers_inProtocolDomain hpsi l r hl hr

/-- Preclear, the leader wall and single-use control retain their precise
positions around the replacement Step1. In particular, done is not immune
to a real leader wall or incoming control action. -/
def doneCaptureSigMove (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let p := sigMoveLeaderPreclear hpsi l r
  let moved := doneTransfers p.1 p.2
  let wall := comparisonLeaderWall moved.1 moved.2
  singleUseControlTail hpsi wall.1 wall.2

/-- Comparison with the actual frozen movement function at its Step1 cut. -/
theorem doneCaptureSigMove_eq_singleUse (hpsi : psi > 0) (l r : AgentState psi)
    (h : (sigMoveLeaderPreclear hpsi l r).1.state ≠ .done) :
    doneCaptureSigMove hpsi l r = singleUseCaptureSigMove hpsi l r := by
  simp only [doneCaptureSigMove, singleUseCaptureSigMove, doneTransfers_of_no_done _ _ h]

private theorem applyControl_domain (hpsi : psi > 0) (u : AgentState psi)
    (hu : u.inProtocolDomain kappa) :
    (singleUseApplyControl hpsi u).inProtocolDomain kappa := by
  have hraw : (sigMoveApplyControl hpsi u).inProtocolDomain kappa := by
    unfold sigMoveApplyControl
    dsimp only
    repeat (first | exact hu | split)
  rw [singleUseApplyControl_eq_clear]
  unfold clearTerminalRelease
  split
  · split
    · exact ⟨hraw.1, hraw.2.1, True.intro, hraw.2.2.2⟩
    · exact hraw
  · exact hraw

private theorem control_domain (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := singleUseControlTail hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hleft := applyControl_domain hpsi l hl
  have hright := applyControl_domain hpsi r hr
  unfold singleUseControlTail
  dsimp only
  split
  · split <;> exact ⟨hleft, hright⟩
  · exact ⟨hleft, hright⟩

theorem doneCaptureSigMove_inProtocolDomain (hpsi : psi > 0)
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := doneCaptureSigMove hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let p := sigMoveLeaderPreclear hpsi l r
  have hp : p.1.inProtocolDomain kappa ∧ p.2.inProtocolDomain kappa := by
    unfold p sigMoveLeaderPreclear clearIfLeader
    dsimp only
    split
    · constructor
      · exact clearComparisonSignal_inProtocolDomain l hl
      · split
        · exact clearComparisonSignal_inProtocolDomain r hr
        · exact hr
    · constructor
      · exact hl
      · split
        · exact clearComparisonSignal_inProtocolDomain r hr
        · exact hr
  have hm := doneTransfers_inProtocolDomain hpsi p.1 p.2 hp.1 hp.2
  have hw := comparisonLeaderWall_inProtocolDomain _ _ hm.1 hm.2
  exact control_domain hpsi _ _ hw.1 hw.2

/-- The same existing movement authorization is computed from the new raw
output. A held payload is not counted as a crossing. -/
def authorizedDoneMove (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := doneCaptureSigMove hpsi l.core r.core
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

theorem authorizedDoneMove_core (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    let q := authorizedDoneMove hpsi l r
    (q.1.core, q.2.core) = doneCaptureSigMove hpsi l.core r.core := by
  unfold authorizedDoneMove
  dsimp only
  split <;> rfl

theorem authorizedDoneMove_inProtocolDomain (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := authorizedDoneMove hpsi l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  have h := doneCaptureSigMove_inProtocolDomain hpsi l.core r.core hl hr
  unfold authorizedDoneMove
  dsimp only
  split <;> exact h

/-- Neither a fresh epoch nor a new release interpretation is introduced. -/
theorem authorizedDoneMove_eq_singleUse (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : (sigMoveLeaderPreclear hpsi l.core r.core).1.state ≠ .done) :
    authorizedDoneMove hpsi l r = authorizedSingleUseReleaseMove hpsi l r := by
  have hm : ∀ a b : AgentState psi,
      pathMovedRight l.core r.core (clearTerminalRelease hpsi a) (clearTerminalRelease hpsi b) =
        pathMovedRight l.core r.core a b := by
    intro a b
    simp only [pathMovedRight, clearTerminalRelease_path]
  have hn : ∀ (u : AgentState psi) (p : Bool),
      normalizePermit (clearTerminalRelease hpsi u) p = normalizePermit u p := by
    intro u p
    simp only [normalizePermit, clearTerminalRelease_path]
  have hr : ∀ (old : AuthorizedAgentState psi) (u : AgentState psi),
      reconcilePermit old (clearTerminalRelease hpsi u) = reconcilePermit old u := by
    intro old u
    simp only [reconcilePermit, clearTerminalRelease_path, hn]
  unfold authorizedDoneMove
  rw [doneCaptureSigMove_eq_singleUse hpsi l.core r.core h, singleUseCaptureSigMove_eq_clear]
  unfold authorizedSingleUseReleaseMove authorizedCaptureSigMove
  dsimp only
  simp only [hm, hn, hr]
  by_cases hmove : pathMovedRight l.core r.core
      (captureSigMoveLeaderWall hpsi l.core r.core).1
      (captureSigMoveLeaderWall hpsi l.core r.core).2 = true
  · simp only [hmove]
    rfl
  · simp only [hmove]
    rfl

end BirthGenerationDone

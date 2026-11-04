import Leader.Wu.Splice.CleanupEndpointDepartGeneration
import Leader.Wu.Splice.NoRouteStageCheck


set_option autoImplicit false
set_option Elab.async false


namespace B9CleanupEndpointDepartSeed


open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair
open BirthGenerationDone BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
open B9NoRouteStagesB


variable {psi : Nat}


attribute [local irreducible] clearComparisonSignal clearIfLeader
  sigMoveLeaderPreclear captureStep1 holdDoneStep1 sigMoveStep2 sigMoveStep3
  sigMoveStep4 sigMoveStep5 controlTransfers doneTransfers comparisonLeaderWall
  singleUseApplyControl singleUseControlTail doneCaptureSigMove authorizedDoneMove


theorem leftZero_of_neutral_opaque
    (u : AgentState psi) (h : ComparisonNeutral u) : LeftZeroDepart u := by
  intro b hb
  have hbad : (PathInfo.bot : PathInfo) = .some 0 b := h.2.1.symm.trans hb
  cases hbad


private theorem clearIfLeader_path2_none_opaque
    (u : AgentState psi) (h : u.path2 = none) :
    (clearIfLeader u).path2 = none := by
  unfold clearIfLeader
  split
  · exact (clearComparisonSignal_neutral u).2.2.1
  · exact h


private theorem preclear_moveSeed_opaque
    (hpsi : 0 < psi) (l r : AgentState psi) (h : MoveSeed l r) :
    let q := sigMoveLeaderPreclear hpsi l r; MoveSeed q.1 q.2 := by
  rcases h with ⟨hz, hl2, hr2⟩
  have hr2' : (clearIfLeader r).path2 = none :=
    clearIfLeader_path2_none_opaque r hr2
  unfold sigMoveLeaderPreclear
  split
  · exact ⟨leftZero_of_neutral_opaque _ (clearComparisonSignal_neutral l),
      (clearComparisonSignal_neutral l).2.2.1, hr2'⟩
  · exact ⟨hz, hl2, hr2'⟩


private theorem capture_moveSeed_opaque
    (l r : AgentState psi) (h : MoveSeed l r) :
    let q := captureStep1 l r; MoveSeed q.1 q.2 := by
  rcases h with ⟨hz, hl2, hr2⟩
  change MoveSeed (captureStep1 l r).1 (captureStep1 l r).2
  cases hlp : l.path with
  | bot =>
      unfold captureStep1
      rw [hlp]
      exact ⟨hz, hl2, hr2⟩
  | some pathLabel pathBit =>
      cases hrp : r.path with
      | some rLabel rBit =>
          unfold captureStep1
          rw [hlp, hrp]
          exact ⟨hz, hl2, hr2⟩
      | bot =>
          by_cases hfree :
              l.state ≠ .lock ∧ l.state ≠ .compare1 ∧ l.state ≠ .CHECK_ready
          · have hcap :
                captureStep1 l r =
                  (if r.state ≠ .produce ∨ pathLabel ≠ psi - 1 then
                    ({ l with path := .bot, state := .none },
                     { r with
                       path := l.path
                       path2 := none
                       state := if r.label.val = pathLabel then
                         .CHECK_ready else .none })
                   else (l, r)) := by
              unfold captureStep1
              rw [hlp, hrp]
              exact if_pos hfree
            rw [hcap]
            by_cases hmove : r.state ≠ .produce ∨ pathLabel ≠ psi - 1
            · rw [if_pos hmove]
              refine ⟨?_, ?_, rfl⟩
              · intro b hb
                cases hb
              · exact hl2
            · rw [if_neg hmove]
              exact ⟨hz, hl2, hr2⟩
          · have hcap : captureStep1 l r = (l, r) := by
              unfold captureStep1
              rw [hlp, hrp]
              exact if_neg hfree
            rw [hcap]
            exact ⟨hz, hl2, hr2⟩


private theorem step2_none_opaque (l r : AgentState psi) (h : l.path2 = none) :
    sigMoveStep2 l r = (l, r) := by unfold sigMoveStep2; rw [h]
private theorem step3_none_opaque (l r : AgentState psi) (h : r.path2 = none) :
    sigMoveStep3 l r = (l, r) := by unfold sigMoveStep3; rw [h]
private theorem step4_none_opaque (l r : AgentState psi) (h : r.path2 = none) :
    sigMoveStep4 l r = (l, r) := by unfold sigMoveStep4; rw [h]
private theorem step5_none_opaque (l r : AgentState psi) (h : l.path2 = none) :
    sigMoveStep5 l r = (l, r) := by unfold sigMoveStep5; rw [h]


private theorem controlTransfers_none_opaque
    (l r : AgentState psi) (hl : l.path2 = none) (hr : r.path2 = none) :
    controlTransfers l r = (l, r) := by
  let q2 := sigMoveStep2 l r
  have h2 : q2 = (l, r) := step2_none_opaque l r hl
  let q3 := sigMoveStep3 q2.1 q2.2
  have h3 : q3 = (l, r) := by
    change sigMoveStep3 q2.1 q2.2 = (l, r)
    rw [h2]
    exact step3_none_opaque l r hr
  let q4 := sigMoveStep4 q3.1 q3.2
  have h4 : q4 = (l, r) := by
    change sigMoveStep4 q3.1 q3.2 = (l, r)
    rw [h3]
    exact step4_none_opaque l r hr
  let q5 := sigMoveStep5 q4.1 q4.2
  have h5 : q5 = (l, r) := by
    change sigMoveStep5 q4.1 q4.2 = (l, r)
    rw [h4]
    exact step5_none_opaque l r hl
  unfold controlTransfers
  change q5 = (l, r)
  exact h5


private theorem hold_moveSeed_opaque
    (l r : AgentState psi) (h : MoveSeed l r) :
    let q := holdDoneStep1 l r; MoveSeed q.1 q.2 := by
  unfold holdDoneStep1
  split
  · exact h
  · exact capture_moveSeed_opaque l r h


private theorem doneTransfers_moveSeed_opaque
    (l r : AgentState psi) (h : MoveSeed l r) :
    let q := doneTransfers l r; MoveSeed q.1 q.2 := by
  let q := holdDoneStep1 l r
  have hq : MoveSeed q.1 q.2 := hold_moveSeed_opaque l r h
  have hc : controlTransfers q.1 q.2 = (q.1, q.2) :=
    controlTransfers_none_opaque q.1 q.2 hq.2.1 hq.2.2
  unfold doneTransfers
  rw [show holdDoneStep1 l r = q from rfl, hc]
  exact hq


private theorem leaderWall_moveSeed_opaque
    (l r : AgentState psi) (h : MoveSeed l r) :
    let q := comparisonLeaderWall l r; MoveSeed q.1 q.2 := by
  rcases h with ⟨hz, hl2, hr2⟩
  unfold comparisonLeaderWall
  split
  · split
    · exact ⟨leftZero_of_neutral_opaque _ (clearComparisonSignal_neutral l),
        (clearComparisonSignal_neutral l).2.2.1,
        (clearComparisonSignal_neutral r).2.2.1⟩
    · exact ⟨leftZero_of_neutral_opaque _ (clearComparisonSignal_neutral l),
        (clearComparisonSignal_neutral l).2.2.1, hr2⟩
  · split
    · exact ⟨hz, hl2, (clearComparisonSignal_neutral r).2.2.1⟩
    · exact ⟨hz, hl2, hr2⟩


private theorem apply_none_opaque (hpsi : 0 < psi) (u : AgentState psi)
    (h : u.path2 = none) : singleUseApplyControl hpsi u = u := by
  unfold singleUseApplyControl
  rw [h]


private theorem controlTail_none_opaque
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : l.path2 = none) (hr : r.path2 = none) :
    singleUseControlTail hpsi l r =
      (let l' := if r.state = .depart then
          if l.label.val < psi - 1 ∧ l.state = .CHECK_ready then
            { l with state := .depart }
          else l
        else l
       (l', r)) := by
  have hl0 : singleUseApplyControl hpsi l = l := apply_none_opaque hpsi l hl
  have hr0 : singleUseApplyControl hpsi r = r := apply_none_opaque hpsi r hr
  unfold singleUseControlTail
  rw [hl0, hr0]


private theorem tail_moveSeed_opaque
    (hpsi : 0 < psi) (l r : AgentState psi) (h : MoveSeed l r) :
    let q := singleUseControlTail hpsi l r; MoveSeed q.1 q.2 := by
  rcases h with ⟨hz, hl2, hr2⟩
  rw [controlTail_none_opaque hpsi l r hl2 hr2]
  change MoveSeed
    (if r.state = .depart then
      if l.label.val < psi - 1 ∧ l.state = .CHECK_ready then
        { l with state := .depart }
      else l
    else l) r
  by_cases hd : r.state = .depart
  · rw [if_pos hd]
    by_cases hp : l.label.val < psi - 1 ∧ l.state = .CHECK_ready
    · rw [if_pos hp]
      refine ⟨?_, hl2, hr2⟩
      intro b hb
      rfl
    · rw [if_neg hp]
      exact ⟨hz, hl2, hr2⟩
  · rw [if_neg hd]
    exact ⟨hz, hl2, hr2⟩


private theorem doneCapture_moveSeed_opaque
    (hpsi : 0 < psi) (l r : AgentState psi) (h : MoveSeed l r) :
    let q := doneCaptureSigMove hpsi l r; MoveSeed q.1 q.2 := by
  let p := sigMoveLeaderPreclear hpsi l r
  have hp : MoveSeed p.1 p.2 := preclear_moveSeed_opaque hpsi l r h
  let m := doneTransfers p.1 p.2
  have hm : MoveSeed m.1 m.2 := doneTransfers_moveSeed_opaque p.1 p.2 hp
  let w := comparisonLeaderWall m.1 m.2
  have hw : MoveSeed w.1 w.2 := leaderWall_moveSeed_opaque m.1 m.2 hm
  have ht : MoveSeed (singleUseControlTail hpsi w.1 w.2).1
      (singleUseControlTail hpsi w.1 w.2).2 :=
    tail_moveSeed_opaque hpsi w.1 w.2 hw
  have heq : doneCaptureSigMove hpsi l r =
      singleUseControlTail hpsi w.1 w.2 := by
    unfold doneCaptureSigMove
    rfl
  rw [heq]
  exact ht


theorem done_leftZero_opaque
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi)
    (h : MoveSeed l.core r.core) :
    LeftZeroDepart (authorizedDoneMove hpsi l r).1.core := by
  let raw := doneCaptureSigMove hpsi l.core r.core
  have hr : MoveSeed raw.1 raw.2 := doneCapture_moveSeed_opaque hpsi l.core r.core h
  have hc : ((authorizedDoneMove hpsi l r).1.core,
      (authorizedDoneMove hpsi l r).2.core) = raw :=
    authorizedDoneMove_core hpsi l r
  have hcL : (authorizedDoneMove hpsi l r).1.core = raw.1 :=
    congrArg (fun z : AgentState psi × AgentState psi => z.1) hc
  rw [hcL]
  exact hr.1


end B9CleanupEndpointDepartSeed


#print axioms B9CleanupEndpointDepartSeed.done_leftZero_opaque

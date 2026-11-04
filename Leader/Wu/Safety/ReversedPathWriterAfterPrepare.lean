import Leader.Wu.Safety.ReversedPathWriterView

set_option autoImplicit false
set_option Elab.async false

namespace ZZSafeN4WriterAfterGPT

open PPLL
open ZZSafeN4WriterViewGPT

private theorem activate_view (u : AgentState 2) :
    WriterProtectedView.ofState (writeActionActivate hpsi2 u) =
      WriterProtectedView.ofState u := by
  apply WriterProtectedView.ext
  all_goals
    unfold WriterProtectedView.ofState writeActionActivate
    try dsimp only
    repeat (first | rfl | split)

private theorem overwrite_view (u : AgentState 2) :
    WriterProtectedView.ofState (writeActionApplyOverwrite u) =
      WriterProtectedView.ofState u := by
  apply WriterProtectedView.ext
  all_goals
    unfold WriterProtectedView.ofState writeActionApplyOverwrite
    try dsimp only
    repeat (first | rfl | split)

private theorem moveFlip_view (u : AgentState 2) :
    WriterProtectedView.ofState (writeActionApplyMoveFlip u) =
      WriterProtectedView.ofState u := by
  apply WriterProtectedView.ext
  all_goals
    unfold WriterProtectedView.ofState writeActionApplyMoveFlip
    try dsimp only
    repeat (first | rfl | split)

private theorem execute_view (l r : AgentState 2) :
    pairView (writeActionExecute hpsi2 l r) = pairView (l, r) := by
  unfold writeActionExecute
  split
  · let r0 := if r.write_state = .overwrite then
      writeActionApplyOverwrite r else r
    let r1 := if r0.write_state = .move_flip then
      writeActionApplyMoveFlip r0 else r0
    let r2 := if r1.write_state = .increment_group then
      if r1.bit = true then { r1 with bit := false }
      else { r1 with bit := true, write_state := .depart }
    else r1
    let l0 := if r2.label ≠ ⟨0, hpsi2⟩ then
      { l with write_state := r2.write_state } else l
    have hr0 : WriterProtectedView.ofState r0 =
        WriterProtectedView.ofState r := by
      unfold r0
      split
      · exact overwrite_view r
      · rfl
    have hr1 : WriterProtectedView.ofState r1 =
        WriterProtectedView.ofState r0 := by
      unfold r1
      split
      · exact moveFlip_view r0
      · rfl
    have hr2 : WriterProtectedView.ofState r2 =
        WriterProtectedView.ofState r1 := by
      apply WriterProtectedView.ext
      all_goals
        unfold r2 WriterProtectedView.ofState
        try dsimp only
        repeat (first | rfl | split)
    have hl0 : WriterProtectedView.ofState l0 =
        WriterProtectedView.ofState l := by
      apply WriterProtectedView.ext
      all_goals
        unfold l0 WriterProtectedView.ofState
        try dsimp only
        repeat (first | rfl | split)
    change pairView (l0, { r2 with write_state := .depart }) =
      pairView (l, r)
    exact Prod.ext hl0 (hr2.trans (hr1.trans hr0))
  · rfl

theorem writeAction_view (l r : AgentState 2) :
    pairView (writeAction hpsi2 l r) = pairView (l, r) := by
  rw [writeAction_eq_staged]
  exact (execute_view (writeActionActivate hpsi2 l)
    (writeActionActivate hpsi2 r)).trans
      (Prod.ext (activate_view l) (activate_view r))

private theorem start_view (l r : AgentState 2) :
    pairView (moveWsigStart l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState moveWsigStart
      moveWsigCheckGenWs
    try dsimp only
    repeat (first | rfl | split)

private theorem checkLast_view (u : AgentState 2) :
    WriterProtectedView.ofState (moveWsigCheckLast u) =
      WriterProtectedView.ofState u := by
  apply WriterProtectedView.ext
  all_goals
    unfold WriterProtectedView.ofState moveWsigCheckLast
    try dsimp only
    repeat (first | rfl | split)

private theorem transfer_view (l r : AgentState 2) :
    pairView (moveWsigTransfer l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState moveWsigTransfer
    try dsimp only
    repeat (first | rfl | split)

private theorem moveWrite_view (l r : AgentState 2) :
    pairView (moveWsigMoveWrite l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState moveWsigMoveWrite
    try dsimp only
    repeat (first | rfl | split)

private theorem leaderSignal_view (l r : AgentState 2) :
    pairView (moveWsigLeaderSignal l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState moveWsigLeaderSignal
    try dsimp only
    repeat (first | rfl | split)

private theorem signalMove_view (l r : AgentState 2) :
    pairView (moveWsigSignalMove l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState moveWsigSignalMove
    try dsimp only
    repeat (first | rfl | split)

private theorem echoMove_view (l r : AgentState 2) :
    pairView (moveWsigEchoMove l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState moveWsigEchoMove
    try dsimp only
    repeat (first | rfl | split)

private theorem finish_view (l r : AgentState 2) :
    pairView (moveWsigFinish l r) = pairView (l, r) := by
  let q0 := moveWsigMoveWrite l r
  let q1 := moveWsigLeaderSignal q0.1 q0.2
  let q2 := moveWsigSignalMove q1.1 q1.2
  exact (echoMove_view q2.1 q2.2).trans
    ((signalMove_view q1.1 q1.2).trans
      ((leaderSignal_view q0.1 q0.2).trans (moveWrite_view l r)))

theorem moveWsig_view (l r : AgentState 2) :
    pairView (moveWsig hpsi2 l r) = pairView (l, r) := by
  let q0 := moveWsigStart l r
  let l0 := moveWsigCheckLast q0.1
  let q1 := moveWsigTransfer l0 q0.2
  rw [moveWsig_eq_staged]
  have hc : pairView (l0, q0.2) = pairView q0 :=
    Prod.ext (checkLast_view q0.1) rfl
  exact (finish_view q1.1 q1.2).trans
    ((transfer_view l0 q0.2).trans (hc.trans (start_view l r)))

theorem writeSeqAfterPrepare_view (l r : AgentState 2) :
    pairView (writeSeqAfterPrepare hpsi2 l r) = pairView (l, r) := by
  let q := writeAction hpsi2 l r
  change pairView (moveWsig hpsi2 q.1 q.2) = pairView (l, r)
  exact (moveWsig_view q.1 q.2).trans (writeAction_view l r)

end ZZSafeN4WriterAfterGPT

#print axioms ZZSafeN4WriterAfterGPT.writeAction_view
#print axioms ZZSafeN4WriterAfterGPT.moveWsig_view
#print axioms ZZSafeN4WriterAfterGPT.writeSeqAfterPrepare_view

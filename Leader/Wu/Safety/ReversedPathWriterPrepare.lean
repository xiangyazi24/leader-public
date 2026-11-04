import Leader.Wu.Safety.ReversedPathWriterView

set_option autoImplicit false
set_option Elab.async false

namespace ZZSafeN4WriterPrepareGPT

open PPLL
open ZZSafeN4WriterViewGPT

private theorem setReady_view (u : AgentState 2) :
    WriterProtectedView.ofState (writeSeqSetWriteReady u) =
      WriterProtectedView.ofState u := by
  apply WriterProtectedView.ext <;>
    unfold WriterProtectedView.ofState writeSeqSetWriteReady <;>
    try dsimp only <;>
    repeat (first | rfl | split)

private theorem checkBit_view (u : AgentState 2) :
    WriterProtectedView.ofState (writeSeqCheckBit u) =
      WriterProtectedView.ofState u := by
  apply WriterProtectedView.ext <;>
    unfold WriterProtectedView.ofState writeSeqCheckBit <;>
    try dsimp only <;>
    repeat (first | rfl | split)

private theorem setAct_view (u : AgentState 2) :
    WriterProtectedView.ofState (writeSeqSetWriteAct u) =
      WriterProtectedView.ofState u := by
  apply WriterProtectedView.ext <;>
    unfold WriterProtectedView.ofState writeSeqSetWriteAct <;>
    try dsimp only <;>
    repeat (first | rfl | split)

private theorem finalR_view (u : AgentState 2) :
    WriterProtectedView.ofState (writeSeqFinalR u) =
      WriterProtectedView.ofState u := by
  apply WriterProtectedView.ext <;>
    unfold WriterProtectedView.ofState writeSeqFinalR <;>
    try dsimp only <;>
    repeat (first | rfl | split)

theorem writeSeqGenerate_view (l r : AgentState 2) :
    pairView (writeSeqGenerate hpsi2 l r) = pairView (l, r) := by
  unfold writeSeqGenerate
  split
  · exact gensigWriteseq_view l r
  · rfl

theorem writeSeqReady_view (l r : AgentState 2) :
    pairView (writeSeqReady l r) = pairView (l, r) := by
  exact Prod.ext (setReady_view l) (setReady_view r)

theorem writeSeqCompare_view (l r : AgentState 2) :
    pairView (writeSeqCompare hpsi2 l r) = pairView (l, r) := by
  let r0 := if r.label = ⟨0, hpsi2⟩ ∧ r.write_state = .ready then
    writeSeqCheckBit r else r
  let r1 := if l.label.val < 2 - 1 ∧ l.write_state = .equal ∧
      r0.write_state = .ready then writeSeqCheckBit r0 else r0
  have hr0 : WriterProtectedView.ofState r0 =
      WriterProtectedView.ofState r := by
    dsimp [r0]
    split
    · exact checkBit_view r
    · rfl
  have hr1 : WriterProtectedView.ofState r1 =
      WriterProtectedView.ofState r0 := by
    dsimp [r1]
    split
    · exact checkBit_view r0
    · rfl
  change pairView (l, r1) = pairView (l, r)
  exact Prod.ext rfl (hr1.trans hr0)

theorem writeSeqCommands_view (l r : AgentState 2) :
    pairView (writeSeqCommands hpsi2 l r) = pairView (l, r) := by
  let l0 := writeSeqSetWriteAct l
  let r0 := writeSeqSetWriteAct r
  let r1 := if r0.label = ⟨2 - 1, by omega⟩ ∧
      r0.write_state = .equal then writeSeqFinalR r0 else r0
  have hl0 : WriterProtectedView.ofState l0 =
      WriterProtectedView.ofState l := by
    exact setAct_view l
  have hr0 : WriterProtectedView.ofState r0 =
      WriterProtectedView.ofState r := by
    exact setAct_view r
  have hr1 : WriterProtectedView.ofState r1 =
      WriterProtectedView.ofState r0 := by
    dsimp [r1]
    split
    · exact finalR_view r0
    · rfl
  change pairView (l0, r1) = pairView (l, r)
  exact Prod.ext hl0 (hr1.trans hr0)

theorem writeSeqPrepare_view (l r : AgentState 2) :
    pairView (writeSeqPrepare hpsi2 l r) = pairView (l, r) := by
  let q0 := writeSeqReady l r
  let q1 := writeSeqCompare hpsi2 q0.1 q0.2
  change pairView (writeSeqCommands hpsi2 q1.1 q1.2) =
    pairView (l, r)
  exact (writeSeqCommands_view q1.1 q1.2).trans
    ((writeSeqCompare_view q0.1 q0.2).trans
      (writeSeqReady_view l r))

theorem writeSeqThroughPrepare_view (l r : AgentState 2) :
    pairView (writeSeqThroughPrepare hpsi2 l r) = pairView (l, r) := by
  let q0 := writeSeqLeaderMove hpsi2 l r
  let q1 := groupInfo hpsi2 q0.1 q0.2
  let q2 := writeSeqGenerate hpsi2 q1.1 q1.2
  change pairView (writeSeqPrepare hpsi2 q2.1 q2.2) =
    pairView (l, r)
  exact (writeSeqPrepare_view q2.1 q2.2).trans
    ((writeSeqGenerate_view q1.1 q1.2).trans
      ((groupInfo_view q0.1 q0.2).trans
        (writeSeqLeaderMove_view l r)))

end ZZSafeN4WriterPrepareGPT

#print axioms ZZSafeN4WriterPrepareGPT.writeSeqGenerate_view
#print axioms ZZSafeN4WriterPrepareGPT.writeSeqPrepare_view
#print axioms ZZSafeN4WriterPrepareGPT.writeSeqThroughPrepare_view

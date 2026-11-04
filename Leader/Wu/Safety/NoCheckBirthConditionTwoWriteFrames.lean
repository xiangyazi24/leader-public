import Leader.Wu.Safety.NoCheckBirthConditionTwoFrames

/-!
# Gated-WRITE frames for corrected condition 2

Algorithms 16--20 may move the leader and write group bits, but they do not
write shield, bullet, `signal_B`, or labels.  The proof is factored at every
named stage to avoid normalizing the complete WRITE sequence monolithically.
-/

namespace PPLLNoCheckBirthConditionTwoWriteFrames

open PPLL PPLLVerify PPLLWriteIncrementGate
  PPLLNoCheckBirthConditionTwoFrames

private theorem framePair_groupInfoStart (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (groupInfoStart hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState groupInfoStart
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_groupInfoSet (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (groupInfoSet hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState groupInfoSet
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_groupInfoUnset (l r : AgentState ψ) :
    bulletFieldPair (groupInfoUnset l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState groupInfoUnset
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_groupInfo (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (groupInfo hψ l r) = bulletFieldPair (l, r) := by
  let q0 := groupInfoStart hψ l r
  let q1 := groupInfoSet hψ q0.1 q0.2
  rw [groupInfo_eq_staged]
  exact (framePair_groupInfoUnset q1.1 q1.2).trans
    ((framePair_groupInfoSet hψ q0.1 q0.2).trans
      (framePair_groupInfoStart hψ l r))

private theorem framePair_gensigStart (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (gensigWriteseqStart hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState gensigWriteseqStart
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_gensigEmit (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (gensigWriteseqEmit hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState gensigWriteseqEmit
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_gensigPropagate (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (gensigWriteseqPropagate hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState gensigWriteseqPropagate
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_gensigFinish (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (gensigWriteseqFinish hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState gensigWriteseqFinish
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_gensigWriteseq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (gensigWriteseq hψ l r) = bulletFieldPair (l, r) := by
  let q0 := gensigWriteseqStart hψ l r
  let q1 := gensigWriteseqEmit hψ q0.1 q0.2
  let q2 := gensigWriteseqPropagate hψ q1.1 q1.2
  rw [gensigWriteseq_eq_staged]
  exact (framePair_gensigFinish hψ q2.1 q2.2).trans
    ((framePair_gensigPropagate hψ q1.1 q1.2).trans
      ((framePair_gensigEmit hψ q0.1 q0.2).trans
        (framePair_gensigStart hψ l r)))

private theorem framePair_writeSeqLeaderMove (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeSeqLeaderMove hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState writeSeqLeaderMove
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_writeSeqGenerate (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeSeqGenerate hψ l r) = bulletFieldPair (l, r) := by
  unfold writeSeqGenerate
  split
  · exact framePair_gensigWriteseq hψ l r
  · rfl

private theorem frameFields_writeSeqSetWriteReady (u : AgentState ψ) :
    BulletFields.ofState (writeSeqSetWriteReady u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState writeSeqSetWriteReady
    try dsimp only []
    repeat (first | rfl | split)

private theorem frameFields_writeSeqCheckBit (u : AgentState ψ) :
    BulletFields.ofState (writeSeqCheckBit u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState writeSeqCheckBit
    try dsimp only []
    repeat (first | rfl | split)

private theorem frameFields_writeSeqSetWriteAct (u : AgentState ψ) :
    BulletFields.ofState (writeSeqSetWriteAct u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState writeSeqSetWriteAct
    try dsimp only []
    repeat (first | rfl | split)

private theorem frameFields_writeSeqFinalR (u : AgentState ψ) :
    BulletFields.ofState (writeSeqFinalR u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState writeSeqFinalR
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_writeSeqReady (l r : AgentState ψ) :
    bulletFieldPair (writeSeqReady l r) = bulletFieldPair (l, r) :=
  Prod.ext (frameFields_writeSeqSetWriteReady l)
    (frameFields_writeSeqSetWriteReady r)

private theorem framePair_writeSeqCompare (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeSeqCompare hψ l r) = bulletFieldPair (l, r) := by
  let r0 := if r.label = ⟨0, hψ⟩ ∧ r.write_state = .ready then
    writeSeqCheckBit r else r
  have hr0 : BulletFields.ofState r0 = BulletFields.ofState r := by
    unfold r0
    split
    · exact frameFields_writeSeqCheckBit r
    · rfl
  change bulletFieldPair
    (l, if l.label.val < ψ - 1 ∧ l.write_state = .equal ∧
      r0.write_state = .ready then writeSeqCheckBit r0 else r0) = _
  apply Prod.ext
  · rfl
  · split
    · exact (frameFields_writeSeqCheckBit r0).trans hr0
    · exact hr0

private theorem framePair_writeSeqCommands (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeSeqCommands hψ l r) = bulletFieldPair (l, r) := by
  let l0 := writeSeqSetWriteAct l
  let r0 := writeSeqSetWriteAct r
  have hl0 := frameFields_writeSeqSetWriteAct l
  have hr0 := frameFields_writeSeqSetWriteAct r
  change bulletFieldPair
    (l0, if r0.label = ⟨ψ - 1, by omega⟩ ∧ r0.write_state = .equal then
      writeSeqFinalR r0 else r0) = _
  apply Prod.ext
  · exact hl0
  · split
    · exact (frameFields_writeSeqFinalR r0).trans hr0
    · exact hr0

private theorem framePair_writeSeqPrepare (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeSeqPrepare hψ l r) = bulletFieldPair (l, r) := by
  let q0 := writeSeqReady l r
  let q1 := writeSeqCompare hψ q0.1 q0.2
  exact (framePair_writeSeqCommands hψ q1.1 q1.2).trans
    ((framePair_writeSeqCompare hψ q0.1 q0.2).trans
      (framePair_writeSeqReady l r))

private theorem framePair_writeSeqThroughPrepare (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeSeqThroughPrepare hψ l r) =
      bulletFieldPair (l, r) := by
  let q0 := writeSeqLeaderMove hψ l r
  let q1 := groupInfo hψ q0.1 q0.2
  let q2 := writeSeqGenerate hψ q1.1 q1.2
  exact (framePair_writeSeqPrepare hψ q2.1 q2.2).trans
    ((framePair_writeSeqGenerate hψ q1.1 q1.2).trans
      ((framePair_groupInfo hψ q0.1 q0.2).trans
        (framePair_writeSeqLeaderMove hψ l r)))

private theorem frameFields_gatePreparedIncrement (u : AgentState ψ) :
    BulletFields.ofState (gatePreparedIncrement u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState gatePreparedIncrement clearIncrementAction
    try dsimp only []
    repeat (first | rfl | split)

private theorem frameFields_writeActionActivate (hψ : ψ > 0)
    (u : AgentState ψ) :
    BulletFields.ofState (writeActionActivate hψ u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState writeActionActivate
    try dsimp only []
    repeat (first | rfl | split)

private theorem frameFields_writeActionApplyOverwrite (u : AgentState ψ) :
    BulletFields.ofState (writeActionApplyOverwrite u) =
      BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState writeActionApplyOverwrite
    try dsimp only []
    repeat (first | rfl | split)

private theorem frameFields_writeActionApplyMoveFlip (u : AgentState ψ) :
    BulletFields.ofState (writeActionApplyMoveFlip u) =
      BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState writeActionApplyMoveFlip
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_writeActionExecute (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeActionExecute hψ l r) = bulletFieldPair (l, r) := by
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
    let l0 := if r2.label ≠ ⟨0, hψ⟩ then
      { l with write_state := r2.write_state } else l
    have hr0 : BulletFields.ofState r0 = BulletFields.ofState r := by
      unfold r0
      split
      · exact frameFields_writeActionApplyOverwrite r
      · rfl
    have hr1 : BulletFields.ofState r1 = BulletFields.ofState r0 := by
      unfold r1
      split
      · exact frameFields_writeActionApplyMoveFlip r0
      · rfl
    have hr2 : BulletFields.ofState r2 = BulletFields.ofState r1 := by
      apply BulletFields.ext
      all_goals
        unfold r2 BulletFields.ofState
        try dsimp only []
        repeat (first | rfl | split)
    have hl0 : BulletFields.ofState l0 = BulletFields.ofState l := by
      apply BulletFields.ext
      all_goals
        unfold l0 BulletFields.ofState
        try dsimp only []
        repeat (first | rfl | split)
    change bulletFieldPair (l0, { r2 with write_state := .depart }) = _
    exact Prod.ext hl0 (hr2.trans (hr1.trans hr0))
  · rfl

private theorem framePair_writeAction (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeAction hψ l r) = bulletFieldPair (l, r) := by
  rw [writeAction_eq_staged]
  exact (framePair_writeActionExecute hψ
    (writeActionActivate hψ l) (writeActionActivate hψ r)).trans
      (Prod.ext (frameFields_writeActionActivate hψ l)
        (frameFields_writeActionActivate hψ r))

private theorem framePair_moveWsigStart (l r : AgentState ψ) :
    bulletFieldPair (moveWsigStart l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState moveWsigStart
      moveWsigCheckGenWs
    try dsimp only []
    repeat (first | rfl | split)

private theorem frameFields_moveWsigCheckLast (u : AgentState ψ) :
    BulletFields.ofState (moveWsigCheckLast u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState moveWsigCheckLast
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_moveWsigTransfer (l r : AgentState ψ) :
    bulletFieldPair (moveWsigTransfer l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState moveWsigTransfer
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_moveWsigMoveWrite (l r : AgentState ψ) :
    bulletFieldPair (moveWsigMoveWrite l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState moveWsigMoveWrite
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_moveWsigLeaderSignal (l r : AgentState ψ) :
    bulletFieldPair (moveWsigLeaderSignal l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState moveWsigLeaderSignal
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_moveWsigSignalMove (l r : AgentState ψ) :
    bulletFieldPair (moveWsigSignalMove l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState moveWsigSignalMove
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_moveWsigEchoMove (l r : AgentState ψ) :
    bulletFieldPair (moveWsigEchoMove l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState moveWsigEchoMove
    try dsimp only []
    repeat (first | rfl | split)

private theorem framePair_moveWsigFinish (l r : AgentState ψ) :
    bulletFieldPair (moveWsigFinish l r) = bulletFieldPair (l, r) := by
  let q0 := moveWsigMoveWrite l r
  let q1 := moveWsigLeaderSignal q0.1 q0.2
  let q2 := moveWsigSignalMove q1.1 q1.2
  exact (framePair_moveWsigEchoMove q2.1 q2.2).trans
    ((framePair_moveWsigSignalMove q1.1 q1.2).trans
      ((framePair_moveWsigLeaderSignal q0.1 q0.2).trans
        (framePair_moveWsigMoveWrite l r)))

private theorem framePair_moveWsig (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (moveWsig hψ l r) = bulletFieldPair (l, r) := by
  let q0 := moveWsigStart l r
  let l0 := moveWsigCheckLast q0.1
  let q1 := moveWsigTransfer l0 q0.2
  rw [moveWsig_eq_staged]
  have hcheck : bulletFieldPair (l0, q0.2) = bulletFieldPair q0 :=
    Prod.ext (frameFields_moveWsigCheckLast q0.1) rfl
  exact (framePair_moveWsigFinish q1.1 q1.2).trans
    ((framePair_moveWsigTransfer l0 q0.2).trans
      (hcheck.trans (framePair_moveWsigStart l r)))

private theorem framePair_writeSeqAfterPrepare (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeSeqAfterPrepare hψ l r) = bulletFieldPair (l, r) := by
  let q := writeAction hψ l r
  exact (framePair_moveWsig hψ q.1 q.2).trans
    (framePair_writeAction hψ l r)

/-- The complete prepared-increment-gated WRITE suffix frames shield, bullet,
and `signal_B` at both endpoints. -/
theorem writeSeqIncrementGate_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (writeSeqIncrementGate hψ l r) = bulletFieldPair (l, r) := by
  let q := writeSeqThroughPrepare hψ l r
  let qg := (gatePreparedIncrement q.1, gatePreparedIncrement q.2)
  change bulletFieldPair (writeSeqAfterPrepare hψ qg.1 qg.2) = _
  exact (framePair_writeSeqAfterPrepare hψ qg.1 qg.2).trans
    ((Prod.ext (frameFields_gatePreparedIncrement q.1)
      (frameFields_gatePreparedIncrement q.2)).trans
        (framePair_writeSeqThroughPrepare hψ l r))

/-- The gated WRITE suffix frames the initiator bullet. -/
theorem writeSeqIncrementGate_initiator_bullet_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (writeSeqIncrementGate hψ l r).1.bullet = l.bullet := by
  have hpair := writeSeqIncrementGate_bulletFieldPair hψ l r
  have hleft := congrArg (fun q => q.1.bullet) hpair
  unfold bulletFieldPair BulletFields.ofState at hleft
  dsimp only at hleft
  exact hleft

/-- The gated WRITE suffix frames the responder bullet. -/
theorem writeSeqIncrementGate_responder_bullet_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (writeSeqIncrementGate hψ l r).2.bullet = r.bullet := by
  have hpair := writeSeqIncrementGate_bulletFieldPair hψ l r
  have hright := congrArg (fun q => q.2.bullet) hpair
  unfold bulletFieldPair BulletFields.ofState at hright
  dsimp only at hright
  exact hright

private theorem writeSeqAfterPrepare_labels (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (writeSeqAfterPrepare hψ l r).1.label = l.label ∧
      (writeSeqAfterPrepare hψ l r).2.label = r.label := by
  let q := writeAction hψ l r
  have hwL := writeAction_l_label hψ l r
  have hwR := writeAction_r_label hψ l r
  have hmL := moveWsig_l_label hψ q.1 q.2
  have hmR := moveWsig_r_label hψ q.1 q.2
  change (moveWsig hψ q.1 q.2).1.label = l.label ∧
    (moveWsig hψ q.1 q.2).2.label = r.label
  exact ⟨hmL.trans hwL, hmR.trans hwR⟩

private theorem gatePreparedIncrement_label (u : AgentState ψ) :
    (gatePreparedIncrement u).label = u.label := by
  unfold gatePreparedIncrement clearIncrementAction
  repeat (first | rfl | split)

/-- The complete gated WRITE suffix frames both labels. -/
theorem writeSeqIncrementGate_labels (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (writeSeqIncrementGate hψ l r).1.label = l.label ∧
      (writeSeqIncrementGate hψ l r).2.label = r.label := by
  let q := writeSeqThroughPrepare hψ l r
  have htotalL := writeSeq_l_label hψ l r
  have htotalR := writeSeq_r_label hψ l r
  have hafterQ := writeSeqAfterPrepare_labels hψ q.1 q.2
  have heq := writeSeq_eq_afterPrepare hψ l r
  have heqL := congrArg (fun p => p.1.label) heq
  have heqR := congrArg (fun p => p.2.label) heq
  have hqEq : q = writeSeqThroughPrepare hψ l r := rfl
  rw [← hqEq] at heqL heqR
  have hqL : q.1.label = l.label :=
    hafterQ.1.symm.trans (heqL.symm.trans htotalL)
  have hqR : q.2.label = r.label :=
    hafterQ.2.symm.trans (heqR.symm.trans htotalR)
  rw [writeSeqIncrementGate_eq_afterPrepare]
  rw [← hqEq]
  have hafterG := writeSeqAfterPrepare_labels hψ
    (gatePreparedIncrement q.1) (gatePreparedIncrement q.2)
  exact ⟨hafterG.1.trans ((gatePreparedIncrement_label q.1).trans hqL),
    hafterG.2.trans ((gatePreparedIncrement_label q.2).trans hqR)⟩

/-- Gated WRITE preserves both leader bits when every responder leader is
already hosted at label zero. -/
theorem writeSeqIncrementGate_leaders_of_responder_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hrZero : r.leader = true → r.label = ⟨0, hψ⟩) :
    (writeSeqIncrementGate hψ l r).1.leader = l.leader ∧
      (writeSeqIncrementGate hψ l r).2.leader = r.leader := by
  constructor
  · cases hl : l.leader
    · cases hout : (writeSeqIncrementGate hψ l r).1.leader
      · rfl
      · have hnew := writeSeqIncrementGate_new_initiator_requires_responder
          hψ l r hout hl
        exact (hnew.2 (hrZero hnew.1)).elim
    · exact writeSeqIncrementGate_initiator_survives hψ l r hl
  · cases hr : r.leader
    · cases hout : (writeSeqIncrementGate hψ l r).2.leader
      · rfl
      · have horigin := writeSeqIncrementGate_responder_origin hψ l r hout
        rw [hr] at horigin
        simp at horigin
    · exact writeSeqIncrementGate_responder_zero_survives
        hψ l r hr (hrZero hr)

end PPLLNoCheckBirthConditionTwoWriteFrames

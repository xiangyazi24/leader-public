import Leader.Wu.Safety.NoCheckBirthConditionTwoWriteFrames
import Leader.Wu.Comparison.HistoryIntegrated

/-!
# Stationary Algorithm-16 WRITE component

The sole removed stage is `writeSeqLeaderMove`. GROUP_INFO, generation,
preparation, prepared increment gating, WRITE_ACTION and MOVE_WSIG execute
in the existing order on their actual new inputs. This is a separately
named local component; it makes no birth or full-host convergence claim.
-/

namespace BirthStationaryWrite

open PPLL PPLLRepair PPLLVerify PPLLDomain PPLLWriteIncrementGate
open PPLLComparisonHistory PPLLNoCheckBirthConditionTwoFrames

set_option autoImplicit false

variable {ψ κ : Nat}

/-- The literal Algorithm-16 preparation prefix with only migration omitted. -/
def swThroughPrepare (hψ : 0 < ψ) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := groupInfo hψ l r
  let q := writeSeqGenerate hψ q.1 q.2
  writeSeqPrepare hψ q.1 q.2

/-- Actual stationary raw WRITE row, retaining both prepared increment gates. -/
def stationaryRaw (hψ : 0 < ψ) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := swThroughPrepare hψ l r
  writeSeqAfterPrepare hψ (gatePreparedIncrement q.1) (gatePreparedIncrement q.2)

/-- Full output equality on the literal old migration guard's complement. -/
theorem stationaryRaw_eq_old (hψ : 0 < ψ) (l r : AgentState ψ)
    (hm : ¬ (r.leader = true ∧ r.label ≠ ⟨0, hψ⟩)) :
    stationaryRaw hψ l r = writeSeqIncrementGate hψ l r := by
  simp only [stationaryRaw, swThroughPrepare, writeSeqIncrementGate,
    writeSeqThroughPrepare, writeSeqLeaderMove, if_neg hm]

/-- Concrete physical observation: leader, label, all three K2 signal fields,
and the existing complete comparison-history projection. No equations are
stored in this observation. -/
def swView (u : AgentState ψ) :
    Bool × Fin ψ × BulletFields ψ × ComparisonTrackedView ψ :=
  (u.leader, u.label, BulletFields.ofState u, ComparisonTrackedView.ofState u)

def swPair (q : AgentState ψ × AgentState ψ) := (swView q.1, swView q.2)

private theorem swGroupStart (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (groupInfoStart hψ l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState groupInfoStart
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swGroupSet (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (groupInfoSet hψ l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState groupInfoSet
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swGroupUnset (l r : AgentState ψ) :
    swPair (groupInfoUnset l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState groupInfoUnset
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swGroupFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (groupInfo hψ l r) = swPair (l, r) := by
  rw [groupInfo_eq_staged]
  let q0 := groupInfoStart hψ l r
  let q1 := groupInfoSet hψ q0.1 q0.2
  exact (swGroupUnset q1.1 q1.2).trans ((swGroupSet hψ q0.1 q0.2).trans (swGroupStart hψ l r))

private theorem swGenStart (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (gensigWriteseqStart hψ l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState gensigWriteseqStart
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swGenEmit (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (gensigWriteseqEmit hψ l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState gensigWriteseqEmit
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swGenPropagate (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (gensigWriteseqPropagate hψ l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState gensigWriteseqPropagate
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swGenFinish (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (gensigWriteseqFinish hψ l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState gensigWriteseqFinish
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swGenerateFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (writeSeqGenerate hψ l r) = swPair (l, r) := by
  unfold writeSeqGenerate
  split
  · rw [gensigWriteseq_eq_staged]
    let q0 := gensigWriteseqStart hψ l r
    let q1 := gensigWriteseqEmit hψ q0.1 q0.2
    let q2 := gensigWriteseqPropagate hψ q1.1 q1.2
    exact (swGenFinish hψ q2.1 q2.2).trans ((swGenPropagate hψ q1.1 q1.2).trans
      ((swGenEmit hψ q0.1 q0.2).trans (swGenStart hψ l r)))
  · rfl

private theorem swReady (l r : AgentState ψ) :
    swPair (writeSeqReady l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState writeSeqReady writeSeqSetWriteReady
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swCompareFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (writeSeqCompare hψ l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState writeSeqCompare writeSeqCheckBit
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

set_option maxHeartbeats 1000000 in
theorem swCommandsFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (writeSeqCommands hψ l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState
    writeSeqCommands writeSeqSetWriteAct writeSeqFinalR
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

set_option maxHeartbeats 1000000 in
theorem swPrepareFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (writeSeqPrepare hψ l r) = swPair (l, r) := by
  let q0 := writeSeqReady l r
  let q1 := writeSeqCompare hψ q0.1 q0.2
  exact (swCommandsFrame hψ q1.1 q1.2).trans ((swCompareFrame hψ q0.1 q0.2).trans (swReady l r))

theorem swThroughPrepareFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (swThroughPrepare hψ l r) = swPair (l, r) := by
  let q0 := groupInfo hψ l r
  let q1 := writeSeqGenerate hψ q0.1 q0.2
  exact (swPrepareFrame hψ q1.1 q1.2).trans ((swGenerateFrame hψ q0.1 q0.2).trans (swGroupFrame hψ l r))

attribute [local irreducible] swThroughPrepare

theorem swGateFrame (u : AgentState ψ) : swView (gatePreparedIncrement u) = swView u := by
  unfold swView BulletFields.ofState ComparisonTrackedView.ofState gatePreparedIncrement clearIncrementAction
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swActivate (hψ : 0 < ψ) (u : AgentState ψ) :
    swView (writeActionActivate hψ u) = swView u := by
  unfold swView BulletFields.ofState ComparisonTrackedView.ofState writeActionActivate
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swViewIte (p : Prop) [Decidable p] (u v : AgentState ψ) :
    swView (if p then u else v) = if p then swView u else swView v := by
  split <;> rfl

theorem swViewBitState (u : AgentState ψ) (b : Bool) (s : WriteState) :
    swView { u with bit := b, write_state := s } = swView u := rfl

theorem swOverwrite (u : AgentState ψ) :
    swView (writeActionApplyOverwrite u) = swView u := by
  unfold writeActionApplyOverwrite
  cases u.path3 <;> rfl

theorem swMoveFlip (u : AgentState ψ) :
    swView (writeActionApplyMoveFlip u) = swView u := by
  unfold writeActionApplyMoveFlip
  cases u.path3 <;> rfl

attribute [local irreducible] writeActionApplyOverwrite writeActionApplyMoveFlip

private theorem swExecute (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (writeActionExecute hψ l r) = swPair (l, r) := by
  unfold writeActionExecute
  split
  · simp only [swPair, swViewIte, swViewBitState, swOverwrite, swMoveFlip, ite_self]
  · rfl

theorem swActionFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (writeAction hψ l r) = swPair (l, r) := by
  rw [writeAction_eq_staged]
  exact (swExecute hψ (writeActionActivate hψ l) (writeActionActivate hψ r)).trans
    (Prod.ext (swActivate hψ l) (swActivate hψ r))

theorem swMoveStart (l r : AgentState ψ) :
    swPair (moveWsigStart l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState moveWsigStart moveWsigCheckGenWs
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swMoveLast (l : AgentState ψ) : swView (moveWsigCheckLast l) = swView l := by
  unfold swView BulletFields.ofState ComparisonTrackedView.ofState moveWsigCheckLast
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swMoveTransfer (l r : AgentState ψ) :
    swPair (moveWsigTransfer l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState moveWsigTransfer
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swMoveWrite (l r : AgentState ψ) :
    swPair (moveWsigMoveWrite l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState moveWsigMoveWrite
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swMoveLeaderSignal (l r : AgentState ψ) :
    swPair (moveWsigLeaderSignal l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState moveWsigLeaderSignal
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swMoveSignal (l r : AgentState ψ) :
    swPair (moveWsigSignalMove l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState moveWsigSignalMove
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swMoveEcho (l r : AgentState ψ) :
    swPair (moveWsigEchoMove l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState moveWsigEchoMove
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swMoveFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (moveWsig hψ l r) = swPair (l, r) := by
  rw [moveWsig_eq_staged]
  let q0 := moveWsigStart l r
  let q1 := (moveWsigCheckLast q0.1, q0.2)
  let q2 := moveWsigTransfer q1.1 q1.2
  let q3 := moveWsigMoveWrite q2.1 q2.2
  let q4 := moveWsigLeaderSignal q3.1 q3.2
  let q5 := moveWsigSignalMove q4.1 q4.2
  have hlast : swPair q1 = swPair q0 := Prod.ext (swMoveLast q0.1) rfl
  exact (swMoveEcho q5.1 q5.2).trans ((swMoveSignal q4.1 q4.2).trans
    ((swMoveLeaderSignal q3.1 q3.2).trans ((swMoveWrite q2.1 q2.2).trans
      ((swMoveTransfer q1.1 q1.2).trans (hlast.trans (swMoveStart l r))))))

/-- Unconditional exact frame for every arbitrary raw input pair. -/
theorem stationaryRaw_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (stationaryRaw hψ l r) = swPair (l, r) := by
  let q := swThroughPrepare hψ l r
  let g := (gatePreparedIncrement q.1, gatePreparedIncrement q.2)
  let w := writeAction hψ g.1 g.2
  have hg : swPair g = swPair q := Prod.ext (swGateFrame q.1) (swGateFrame q.2)
  exact (swMoveFrame hψ w.1 w.2).trans ((swActionFrame hψ g.1 g.2).trans
    (hg.trans (swThroughPrepareFrame hψ l r)))

attribute [local irreducible] stationaryRaw

/-- Both physical leader bits stay at their original endpoints. -/
theorem stationaryRaw_leaders (hψ : 0 < ψ) (l r : AgentState ψ) :
    (stationaryRaw hψ l r).1.leader = l.leader ∧
      (stationaryRaw hψ l r).2.leader = r.leader :=
  ⟨congrArg (fun q => q.1.1) (stationaryRaw_frame hψ l r),
   congrArg (fun q => q.2.1) (stationaryRaw_frame hψ l r)⟩

theorem stationaryRaw_labels (hψ : 0 < ψ) (l r : AgentState ψ) :
    (stationaryRaw hψ l r).1.label = l.label ∧
      (stationaryRaw hψ l r).2.label = r.label :=
  ⟨congrArg (fun q => q.1.2.1) (stationaryRaw_frame hψ l r),
   congrArg (fun q => q.2.2.1) (stationaryRaw_frame hψ l r)⟩

theorem stationaryRaw_bullets (hψ : 0 < ψ) (l r : AgentState ψ) :
    bulletFieldPair (stationaryRaw hψ l r) = bulletFieldPair (l, r) :=
  congrArg (fun q => (q.1.2.2.1, q.2.2.2.1)) (stationaryRaw_frame hψ l r)

/-- The public comparison suffix frame applies to the actual newly prepared
inputs, including the existing two increment gates. -/
theorem stationaryRaw_comparison (hψ : 0 < ψ) (l r : AgentState ψ) :
    comparisonTrackedPair (stationaryRaw hψ l r) = comparisonTrackedPair (l, r) := by
  unfold stationaryRaw
  rw [writeSeqAfterPrepare_comparisonTracked_pair]
  let q := swThroughPrepare hψ l r
  have hg : swPair (gatePreparedIncrement q.1, gatePreparedIncrement q.2) = swPair q :=
    Prod.ext (swGateFrame q.1) (swGateFrame q.2)
  exact congrArg (fun q => (q.1.2.2.2, q.2.2.2.2))
    (hg.trans (swThroughPrepareFrame hψ l r))

end BirthStationaryWrite

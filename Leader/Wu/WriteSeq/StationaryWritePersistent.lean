import Leader.Wu.WriteSeq.StationaryWriteFinite

/-!
# Stationary persistent-comparison writer

The separately repaired persistent lifecycle is retained literally, including
input-increment sanitation and stop-on-alignment transport. Only its leader
migration stage is omitted. This is an actual local component, not a ruler
repair producer for arbitrary dirty intervals.
-/

namespace BirthStationaryWrite

open PPLL PPLLRepair PPLLDomain PPLLWriteIncrementGate
open PPLLWriteSeqPersistenceRepair PPLLAuthorizedComparisonRepair
open PPLLComparisonHistory PPLLNoCheckBirthConditionTwoFrames

set_option autoImplicit false

variable {n ψ κ : Nat}

/-- The persistent lifecycle's literal preparation, omitting only migration. -/
def swPersistentThroughPrepare (hψ : 0 < ψ) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := clearInputIncrementPair l r
  let q := groupInfo hψ q.1 q.2
  let q := writeSeqGenerate hψ q.1 q.2
  writeSeqPrepareTransport hψ q.1 q.2

/-- Actual stationary persistent writer, using the original repaired suffix. -/
def stationaryPersistentRaw (hψ : 0 < ψ) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := swPersistentThroughPrepare hψ l r
  writeSeqAfterPrepareComparisonTransport hψ
    (gatePreparedIncrement q.1) (gatePreparedIncrement q.2)

private theorem swPersistentClearLeader (u : AgentState ψ) :
    (clearIncrementAction u).leader = u.leader := by
  unfold clearIncrementAction
  split <;> rfl

private theorem swPersistentClearLabel (u : AgentState ψ) :
    (clearIncrementAction u).label = u.label := by
  unfold clearIncrementAction
  split <;> rfl

/-- The sanitizer leaves the actual migration guard unchanged. Whole outputs
agree when that guard is false; every downstream stage sees identical inputs. -/
theorem stationaryPersistentRaw_eq_old (hψ : 0 < ψ) (l r : AgentState ψ)
    (hm : ¬ (r.leader = true ∧ r.label ≠ ⟨0, hψ⟩)) :
    stationaryPersistentRaw hψ l r =
      writeSeqPersistentComparisonTransportLifecycle hψ l r := by
  have hm' : ¬ ((clearIncrementAction r).leader = true ∧
      (clearIncrementAction r).label ≠ ⟨0, hψ⟩) := by
    simpa only [swPersistentClearLeader, swPersistentClearLabel] using hm
  have he : writeSeqLeaderMove hψ (clearIncrementAction l) (clearIncrementAction r) =
      (clearIncrementAction l, clearIncrementAction r) := if_neg hm'
  simp only [stationaryPersistentRaw, swPersistentThroughPrepare,
    writeSeqPersistentComparisonTransportLifecycle, clearInputIncrementPair,
    he]

private theorem swPersistentClearFrame (u : AgentState ψ) :
    swView (clearIncrementAction u) = swView u := by
  unfold clearIncrementAction
  split <;> rfl

private theorem swPersistentReadyFrame (u : AgentState ψ) :
    swView (writeSeqSetWriteReadyTransport u) = swView u := by
  unfold swView BulletFields.ofState ComparisonTrackedView.ofState writeSeqSetWriteReadyTransport
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swPersistentPrepareFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (writeSeqPrepareTransport hψ l r) = swPair (l, r) := by
  let q0 := writeSeqReadyTransport l r
  let q1 := writeSeqCompare hψ q0.1 q0.2
  have h0 : swPair q0 = swPair (l, r) :=
    Prod.ext (swPersistentReadyFrame l) (swPersistentReadyFrame r)
  exact (swCommandsFrame hψ q1.1 q1.2).trans ((swCompareFrame hψ q0.1 q0.2).trans h0)

theorem swPersistentThroughPrepareFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (swPersistentThroughPrepare hψ l r) = swPair (l, r) := by
  let q0 := clearInputIncrementPair l r
  let q1 := groupInfo hψ q0.1 q0.2
  let q2 := writeSeqGenerate hψ q1.1 q1.2
  have h0 : swPair q0 = swPair (l, r) :=
    Prod.ext (swPersistentClearFrame l) (swPersistentClearFrame r)
  exact (swPersistentPrepareFrame hψ q2.1 q2.2).trans
    ((swGenerateFrame hψ q1.1 q1.2).trans ((swGroupFrame hψ q0.1 q0.2).trans h0))

attribute [local irreducible] swPersistentThroughPrepare

private theorem swPersistentActivateFrame (hψ : 0 < ψ) (u : AgentState ψ) :
    swView (writeActionActivateNonempty hψ u) = swView u := by
  unfold writeActionActivateNonempty
  split <;> rfl

private theorem swPersistentIncrementFrame (u : AgentState ψ) :
    swView (writeActionApplyIncrementAndFlip u) = swView u := by
  unfold swView BulletFields.ofState ComparisonTrackedView.ofState writeActionApplyIncrementAndFlip
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swPersistentPropagateFrame (u : AgentState ψ) (s : WriteState) :
    swView (writeActionPropagateState u s) = swView u := by
  cases s <;> rfl

private theorem swPersistentStateFrame (u : AgentState ψ) (s : WriteState) :
    swView { u with write_state := s } = swView u := rfl

attribute [local irreducible] writeActionApplyOverwrite writeActionApplyMoveFlip
  writeActionApplyIncrementAndFlip writeActionPropagateState

private theorem swPersistentExecuteFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (writeActionExecutePreservingDepart hψ l r) = swPair (l, r) := by
  unfold writeActionExecutePreservingDepart
  split
  · simp only [swPair, swViewIte, swPersistentStateFrame, swPersistentPropagateFrame,
      swOverwrite, swMoveFlip, swPersistentIncrementFrame, ite_self]
  · rfl

theorem swPersistentActionFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (writeActionPreservingComparison hψ l r) = swPair (l, r) := by
  let l0 := writeActionActivateNonempty hψ l
  let r0 := writeActionActivateNonempty hψ r
  have he : swPair (writeActionExecutePreservingComparison hψ l0 r0) = swPair (l0, r0) := by
    unfold writeActionExecutePreservingComparison
    split
    · rfl
    · exact swPersistentExecuteFrame hψ l0 r0
  exact he.trans (Prod.ext (swPersistentActivateFrame hψ l) (swPersistentActivateFrame hψ r))

private theorem swPersistentTransferFrame (l r : AgentState ψ) :
    swPair (moveWsigTransferStopAligned l r) = swPair (l, r) := by
  unfold swPair swView BulletFields.ofState ComparisonTrackedView.ofState moveWsigTransferStopAligned
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swPersistentMoveWriteFrame (l r : AgentState ψ) :
    swPair (moveWsigMoveWritePreservingNonempty l r) = swPair (l, r) := by
  unfold moveWsigMoveWritePreservingNonempty
  split <;> rfl

theorem swPersistentMoveFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (moveWsigStopAligned hψ l r) = swPair (l, r) := by
  let q0 := moveWsigStart l r
  let q1 := (moveWsigCheckLast q0.1, q0.2)
  let q2 := moveWsigTransferStopAligned q1.1 q1.2
  let q3 := moveWsigMoveWritePreservingNonempty q2.1 q2.2
  let q4 := moveWsigLeaderSignal q3.1 q3.2
  let q5 := moveWsigSignalMove q4.1 q4.2
  have hlast : swPair q1 = swPair q0 := Prod.ext (swMoveLast q0.1) rfl
  exact (swMoveEcho q5.1 q5.2).trans ((swMoveSignal q4.1 q4.2).trans
    ((swMoveLeaderSignal q3.1 q3.2).trans ((swPersistentMoveWriteFrame q2.1 q2.2).trans
      ((swPersistentTransferFrame q1.1 q1.2).trans (hlast.trans (swMoveStart l r))))))

/-- Unconditional physical and comparison-field frame of the actual row. -/
theorem stationaryPersistentRaw_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swPair (stationaryPersistentRaw hψ l r) = swPair (l, r) := by
  let q := swPersistentThroughPrepare hψ l r
  let g := (gatePreparedIncrement q.1, gatePreparedIncrement q.2)
  let w := writeActionPreservingComparison hψ g.1 g.2
  have hg : swPair g = swPair q := Prod.ext (swGateFrame q.1) (swGateFrame q.2)
  exact (swPersistentMoveFrame hψ w.1 w.2).trans ((swPersistentActionFrame hψ g.1 g.2).trans
    (hg.trans (swPersistentThroughPrepareFrame hψ l r)))

attribute [local irreducible] stationaryPersistentRaw

theorem stationaryPersistentRaw_leaders (hψ : 0 < ψ) (l r : AgentState ψ) :
    (stationaryPersistentRaw hψ l r).1.leader = l.leader ∧
      (stationaryPersistentRaw hψ l r).2.leader = r.leader :=
  ⟨congrArg (fun q => q.1.1) (stationaryPersistentRaw_frame hψ l r),
   congrArg (fun q => q.2.1) (stationaryPersistentRaw_frame hψ l r)⟩

theorem stationaryPersistentRaw_labels (hψ : 0 < ψ) (l r : AgentState ψ) :
    (stationaryPersistentRaw hψ l r).1.label = l.label ∧
      (stationaryPersistentRaw hψ l r).2.label = r.label :=
  ⟨congrArg (fun q => q.1.2.1) (stationaryPersistentRaw_frame hψ l r),
   congrArg (fun q => q.2.2.1) (stationaryPersistentRaw_frame hψ l r)⟩

theorem stationaryPersistentRaw_bullets (hψ : 0 < ψ) (l r : AgentState ψ) :
    bulletFieldPair (stationaryPersistentRaw hψ l r) = bulletFieldPair (l, r) :=
  congrArg (fun q => (q.1.2.2.1, q.2.2.2.1)) (stationaryPersistentRaw_frame hψ l r)

theorem stationaryPersistentRaw_comparison (hψ : 0 < ψ) (l r : AgentState ψ) :
    comparisonTrackedPair (stationaryPersistentRaw hψ l r) = comparisonTrackedPair (l, r) :=
  congrArg (fun q => (q.1.2.2.2, q.2.2.2.2)) (stationaryPersistentRaw_frame hψ l r)

end BirthStationaryWrite

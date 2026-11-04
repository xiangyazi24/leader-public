import Leader.Wu.Entrance.PreWriterFramesCheck

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6WriterLanesB

open PPLL PPLLWriteSeqPersistenceRepair

variable {ψ : Nat}

/-- Responder writer lane is completely idle. -/
def RightIdle (u : AgentState ψ) : Prop :=
  u.path3 = none ∧ u.write = .none ∧ u.write_state = .none

/-- Algorithm 19 preserves the responder bit and can only leave an idle
responder idle or mark it departed. -/
theorem action_right_safe
    (hψ : 0 < ψ) (l r : AgentState ψ) (hr : RightIdle r) :
    let q := writeActionPreservingComparison hψ l r
    q.2.bit = r.bit ∧
      (q.2.write_state = .none ∨ q.2.write_state = .depart) := by
  rcases hr with ⟨_, hw, hs⟩
  simp [writeActionPreservingComparison, writeActionActivateNonempty,
    writeActionExecutePreservingComparison,
    writeActionExecutePreservingDepart, hw, hs]
  intro _
  exact (Classical.em _).symm

/-- `moveWsigStart` preserves the responder bit and writer state. -/
theorem moveWsigStart_right_frame (l r : AgentState ψ) :
    let q := moveWsigStart l r
    q.2.bit = r.bit ∧ q.2.write_state = r.write_state := by
  unfold moveWsigStart moveWsigCheckGenWs
  dsimp only
  repeat (first | exact ⟨rfl, rfl⟩ | split)

/-- The transfer preserves the responder bit and either preserves its writer
state or changes it to one of the two safe states. -/
theorem moveWsigTransferStopAligned_right_frame (l r : AgentState ψ) :
    let q := moveWsigTransferStopAligned l r
    q.2.bit = r.bit ∧
      (q.2.write_state = r.write_state ∨
        q.2.write_state = .none ∨ q.2.write_state = .depart) := by
  unfold moveWsigTransferStopAligned
  dsimp only
  repeat (first
    | exact ⟨rfl, Or.inl rfl⟩
    | exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    | exact ⟨rfl, Or.inr (Or.inr rfl)⟩
    | split)

/-- Command movement does not touch the responder bit or writer state. -/
theorem moveWsigMoveWritePreservingNonempty_right_frame
    (l r : AgentState ψ) :
    let q := moveWsigMoveWritePreservingNonempty l r
    q.2.bit = r.bit ∧ q.2.write_state = r.write_state := by
  unfold moveWsigMoveWritePreservingNonempty
  split <;> exact ⟨rfl, rfl⟩

/-- Leader-signal generation does not touch the responder fields of interest. -/
theorem moveWsigLeaderSignal_right_frame (l r : AgentState ψ) :
    let q := moveWsigLeaderSignal l r
    q.2.bit = r.bit ∧ q.2.write_state = r.write_state := by
  unfold moveWsigLeaderSignal
  exact ⟨rfl, rfl⟩

/-- Signal movement preserves the responder bit and writer state. -/
theorem moveWsigSignalMove_right_frame (l r : AgentState ψ) :
    let q := moveWsigSignalMove l r
    q.2.bit = r.bit ∧ q.2.write_state = r.write_state := by
  unfold moveWsigSignalMove
  split <;> exact ⟨rfl, rfl⟩

/-- Echo movement preserves the responder bit and writer state. -/
theorem moveWsigEchoMove_right_frame (l r : AgentState ψ) :
    let q := moveWsigEchoMove l r
    q.2.bit = r.bit ∧ q.2.write_state = r.write_state := by
  unfold moveWsigEchoMove
  repeat (first | exact ⟨rfl, rfl⟩ | split)

/-- The complete command/signal finish chain preserves both responder fields. -/
theorem moveWsigFinishPreservingCommand_right_frame
    (l r : AgentState ψ) :
    let q := moveWsigFinishPreservingCommand l r
    q.2.bit = r.bit ∧ q.2.write_state = r.write_state := by
  let q0 := moveWsigMoveWritePreservingNonempty l r
  let q1 := moveWsigLeaderSignal q0.1 q0.2
  let q2 := moveWsigSignalMove q1.1 q1.2
  let q3 := moveWsigEchoMove q2.1 q2.2
  have h0 : q0.2.bit = r.bit ∧ q0.2.write_state = r.write_state :=
    moveWsigMoveWritePreservingNonempty_right_frame l r
  have h1 : q1.2.bit = q0.2.bit ∧ q1.2.write_state = q0.2.write_state :=
    moveWsigLeaderSignal_right_frame q0.1 q0.2
  have h2 : q2.2.bit = q1.2.bit ∧ q2.2.write_state = q1.2.write_state :=
    moveWsigSignalMove_right_frame q1.1 q1.2
  have h3 : q3.2.bit = q2.2.bit ∧ q3.2.write_state = q2.2.write_state :=
    moveWsigEchoMove_right_frame q2.1 q2.2
  change q3.2.bit = r.bit ∧ q3.2.write_state = r.write_state
  exact ⟨h3.1.trans (h2.1.trans (h1.1.trans h0.1)),
    h3.2.trans (h2.2.trans (h1.2.trans h0.2))⟩

/-- Whole Algorithm-20 responder frame. -/
theorem moveWsigStopAligned_right_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    let q := moveWsigStopAligned hψ l r
    q.2.bit = r.bit ∧
      (q.2.write_state = r.write_state ∨
        q.2.write_state = .none ∨ q.2.write_state = .depart) := by
  let q0 := moveWsigStart l r
  let l1 := moveWsigCheckLast q0.1
  let q1 := moveWsigTransferStopAligned l1 q0.2
  let q2 := moveWsigFinishPreservingCommand q1.1 q1.2
  have h0 : q0.2.bit = r.bit ∧ q0.2.write_state = r.write_state :=
    moveWsigStart_right_frame l r
  have h1 : q1.2.bit = q0.2.bit ∧
      (q1.2.write_state = q0.2.write_state ∨
        q1.2.write_state = .none ∨ q1.2.write_state = .depart) :=
    moveWsigTransferStopAligned_right_frame l1 q0.2
  have h2 : q2.2.bit = q1.2.bit ∧ q2.2.write_state = q1.2.write_state :=
    moveWsigFinishPreservingCommand_right_frame q1.1 q1.2
  change q2.2.bit = r.bit ∧
    (q2.2.write_state = r.write_state ∨
      q2.2.write_state = .none ∨ q2.2.write_state = .depart)
  refine ⟨h2.1.trans (h1.1.trans h0.1), ?_⟩
  rcases h1.2 with hs | hn | hd
  · exact Or.inl (h2.2.trans (hs.trans h0.2))
  · exact Or.inr (Or.inl (h2.2.trans hn))
  · exact Or.inr (Or.inr (h2.2.trans hd))

/-- A safe responder writer state stays safe through Algorithm 20. -/
theorem move_right_safe
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hs : r.write_state = .none ∨ r.write_state = .depart) :
    let q := moveWsigStopAligned hψ l r
    q.2.bit = r.bit ∧
      (q.2.write_state = .none ∨ q.2.write_state = .depart) := by
  have h := moveWsigStopAligned_right_frame hψ l r
  dsimp only at h ⊢
  rcases h with ⟨hb, hw⟩
  refine ⟨hb, ?_⟩
  rcases hw with hsame | hnone | hdepart
  · rw [hsame]
    exact hs
  · exact Or.inl hnone
  · exact Or.inr hdepart

end B6WriterLanesB

#print axioms B6WriterLanesB.action_right_safe
#print axioms B6WriterLanesB.moveWsigStopAligned_right_frame
#print axioms B6WriterLanesB.move_right_safe

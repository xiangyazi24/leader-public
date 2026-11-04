import Leader.Wu.WallSweep.Repair
import Leader.Wu.Comparison.HistoryIntegrated

/-!
# Proof-history deletion at the source-backed walls

`LocalComparisonHistory` is proof-only configuration history, not executable
agent memory.  A wall therefore adds no protocol state: when its physical
projection deletes `state`, `path`, `path2`, and `p_carry`, the refinement sets
the corresponding four source marks to `absent`.
-/

namespace PPLLWallSweepHistory

open PPLL PPLLRepair PPLLComparisonHistory PPLLComparisonLifecycle
  PPLLWallSweepRepair

/-- Delete every proof-history mark whose physical field is deleted by
`clearComparisonSignal`. -/
def clearComparisonHistory (_h : LocalComparisonHistory n) :
    LocalComparisonHistory n :=
  { state := .absent
    path := .absent
    path2 := .absent
    pCarry := .absent }

/-- Proof refinement of one physical comparison-carrier deletion. -/
def markedClearComparisonSignal (u : MarkedAgentState n ψ) :
    MarkedAgentState n ψ :=
  ⟨clearComparisonSignal u.concrete,
    clearComparisonHistory u.history⟩

/-- History deletion cannot alter the physical wall assignment. -/
theorem erase_markedClearComparisonSignal (u : MarkedAgentState n ψ) :
    (markedClearComparisonSignal u).concrete =
      clearComparisonSignal u.concrete := by
  rfl

/-- All four source marks are absent immediately after physical deletion. -/
theorem markedClearComparisonSignal_marks_absent
    (u : MarkedAgentState n ψ) :
    let q := markedClearComparisonSignal u
    q.history.state = .absent ∧ q.history.path = .absent ∧
      q.history.path2 = .absent ∧ q.history.pCarry = .absent := by
  simp [markedClearComparisonSignal, clearComparisonHistory]

/-- A wall converts even arbitrary/tainted input history into the trusted idle
surface, because all four tracked fields and all four marks are absent. -/
theorem markedClearComparisonSignal_fullLocalHistoryTrusted
    (u : MarkedAgentState n ψ) :
    FullLocalHistoryTrusted
      (markedClearComparisonSignal u).concrete
      (markedClearComparisonSignal u).history := by
  simp [markedClearComparisonSignal, clearComparisonSignal,
    clearComparisonHistory, FullLocalHistoryTrusted,
    AuditLocalHistoryTrusted, PCarryHistoryTrusted, MarkMatches]

/-- Physical deletion alone is not a history update: retaining a trusted mark
on any now-absent field violates the existing trust relation. -/
theorem clearComparisonSignal_retaining_trusted_marks_not_fullTrusted
    (u : AgentState ψ) (source : Fin n) :
    let stale : LocalComparisonHistory n :=
      { state := .trusted source
        path := .trusted source
        path2 := .trusted source
        pCarry := .trusted source }
    ¬FullLocalHistoryTrusted (clearComparisonSignal u) stale := by
  simp [clearComparisonSignal, FullLocalHistoryTrusted,
    AuditLocalHistoryTrusted, PCarryHistoryTrusted, MarkMatches]

/-! ## Reset deletion -/

/-- Marked counterpart of the reset-command deletion primitive. -/
def markedResetKillComparison (u : MarkedAgentState n ψ) :
    MarkedAgentState n ψ :=
  if u.concrete.reset_cmd then markedClearComparisonSignal u else u

theorem erase_markedResetKillComparison (u : MarkedAgentState n ψ) :
    (markedResetKillComparison u).concrete =
      resetKillComparison u.concrete := by
  unfold markedResetKillComparison resetKillComparison
  split <;> rfl

/-- Reset deletion preserves trusted history on untouched inputs and replaces
all tracked marks by trusted absence when it fires. -/
theorem markedResetKillComparison_preserves_fullLocalHistoryTrusted
    (u : MarkedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete u.history) :
    FullLocalHistoryTrusted
      (markedResetKillComparison u).concrete
      (markedResetKillComparison u).history := by
  unfold markedResetKillComparison
  split
  · exact markedClearComparisonSignal_fullLocalHistoryTrusted u
  · exact hu

/-- A live reset token rehabilitates arbitrary local comparison history. -/
theorem markedResetKillComparison_of_reset
    (u : MarkedAgentState n ψ) (hreset : u.concrete.reset_cmd = true) :
    FullLocalHistoryTrusted
      (markedResetKillComparison u).concrete
      (markedResetKillComparison u).history := by
  simp [markedResetKillComparison, hreset,
    markedClearComparisonSignal_fullLocalHistoryTrusted]

/-! ## Complete reset-suppression stage -/

private theorem suppressSigStart_history_frame (l r : AgentState ψ) :
    let q := suppressSigStart l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  unfold suppressSigStart ComparisonTrackedView.ofState
  try dsimp only []
  repeat (first | constructor | rfl | split)

private theorem suppressSigMoveReset_history_frame (l r : AgentState ψ) :
    let q := suppressSigMoveReset l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  unfold suppressSigMoveReset ComparisonTrackedView.ofState
  try dsimp only []
  repeat (first | constructor | rfl | split)

private theorem suppressSigTerminal_history_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := suppressSigTerminal hψ l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  unfold suppressSigTerminal ComparisonTrackedView.ofState
  try dsimp only []
  repeat (first | constructor | rfl | split)

private theorem suppressSigEcho_history_frame (l r : AgentState ψ) :
    let q := suppressSigEcho l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  unfold suppressSigEcho ComparisonTrackedView.ofState
  repeat (first | constructor | rfl | split)

private theorem suppressSigFinish_history_frame (l r : AgentState ψ) :
    let q := suppressSigFinish l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  unfold suppressSigFinish ComparisonTrackedView.ofState
  try dsimp only []
  repeat (first | constructor | rfl | split)

/-- Marked Algorithm 14 with the same two reset-kill boundaries as the physical
repair. Non-kill sub-stages retain the four proof marks verbatim. -/
def markedSuppressSigResetKill (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q0 := markedFrame suppressSigStart l r
  let q0k := (markedResetKillComparison q0.1,
    markedResetKillComparison q0.2)
  let q1 := markedFrame suppressSigMoveReset q0k.1 q0k.2
  let q1k := (markedResetKillComparison q1.1,
    markedResetKillComparison q1.2)
  let q2 := markedFrame (suppressSigTerminal hψ) q1k.1 q1k.2
  let q3 := markedFrame suppressSigEcho q2.1 q2.2
  markedFrame suppressSigFinish q3.1 q3.2

/-- The proof-history replay erases exactly to the repaired physical
SUPPRESS_SIG. -/
theorem erase_markedSuppressSigResetKill (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedSuppressSigResetKill hψ l r
    (q.1.concrete, q.2.concrete) =
      suppressSigResetKill hψ l.concrete r.concrete := by
  let q0m := markedFrame suppressSigStart l r
  let q0 := suppressSigStart l.concrete r.concrete
  have h0 : (q0m.1.concrete, q0m.2.concrete) = q0 := by rfl
  have h0l : q0m.1.concrete = q0.1 := by
    simpa using congrArg Prod.fst h0
  have h0r : q0m.2.concrete = q0.2 := by
    simpa using congrArg Prod.snd h0
  let q0km := (markedResetKillComparison q0m.1,
    markedResetKillComparison q0m.2)
  let q0k := (resetKillComparison q0.1, resetKillComparison q0.2)
  have h0k : (q0km.1.concrete, q0km.2.concrete) = q0k := by
    apply Prod.ext
    · change q0km.1.concrete = q0k.1
      dsimp only [q0km, q0k]
      rw [erase_markedResetKillComparison, h0l]
    · change q0km.2.concrete = q0k.2
      dsimp only [q0km, q0k]
      rw [erase_markedResetKillComparison, h0r]
  have h0kl : q0km.1.concrete = q0k.1 := by
    simpa using congrArg Prod.fst h0k
  have h0kr : q0km.2.concrete = q0k.2 := by
    simpa using congrArg Prod.snd h0k
  let q1m := markedFrame suppressSigMoveReset q0km.1 q0km.2
  let q1 := suppressSigMoveReset q0k.1 q0k.2
  have h1 : (q1m.1.concrete, q1m.2.concrete) = q1 := by
    change suppressSigMoveReset q0km.1.concrete q0km.2.concrete =
      suppressSigMoveReset q0k.1 q0k.2
    rw [h0kl, h0kr]
  have h1l : q1m.1.concrete = q1.1 := by
    simpa using congrArg Prod.fst h1
  have h1r : q1m.2.concrete = q1.2 := by
    simpa using congrArg Prod.snd h1
  let q1km := (markedResetKillComparison q1m.1,
    markedResetKillComparison q1m.2)
  let q1k := (resetKillComparison q1.1, resetKillComparison q1.2)
  have h1k : (q1km.1.concrete, q1km.2.concrete) = q1k := by
    apply Prod.ext
    · change q1km.1.concrete = q1k.1
      dsimp only [q1km, q1k]
      rw [erase_markedResetKillComparison, h1l]
    · change q1km.2.concrete = q1k.2
      dsimp only [q1km, q1k]
      rw [erase_markedResetKillComparison, h1r]
  have h1kl : q1km.1.concrete = q1k.1 := by
    simpa using congrArg Prod.fst h1k
  have h1kr : q1km.2.concrete = q1k.2 := by
    simpa using congrArg Prod.snd h1k
  let q2m := markedFrame (suppressSigTerminal hψ) q1km.1 q1km.2
  let q2 := suppressSigTerminal hψ q1k.1 q1k.2
  have h2 : (q2m.1.concrete, q2m.2.concrete) = q2 := by
    change suppressSigTerminal hψ q1km.1.concrete q1km.2.concrete =
      suppressSigTerminal hψ q1k.1 q1k.2
    rw [h1kl, h1kr]
  have h2l : q2m.1.concrete = q2.1 := by
    simpa using congrArg Prod.fst h2
  have h2r : q2m.2.concrete = q2.2 := by
    simpa using congrArg Prod.snd h2
  let q3m := markedFrame suppressSigEcho q2m.1 q2m.2
  let q3 := suppressSigEcho q2.1 q2.2
  have h3 : (q3m.1.concrete, q3m.2.concrete) = q3 := by
    change suppressSigEcho q2m.1.concrete q2m.2.concrete =
      suppressSigEcho q2.1 q2.2
    rw [h2l, h2r]
  have h3l : q3m.1.concrete = q3.1 := by
    simpa using congrArg Prod.fst h3
  have h3r : q3m.2.concrete = q3.2 := by
    simpa using congrArg Prod.snd h3
  let q4m := markedFrame suppressSigFinish q3m.1 q3m.2
  let q4 := suppressSigFinish q3.1 q3.2
  have h4 : (q4m.1.concrete, q4m.2.concrete) = q4 := by
    change suppressSigFinish q3m.1.concrete q3m.2.concrete =
      suppressSigFinish q3.1 q3.2
    rw [h3l, h3r]
  change (q4m.1.concrete, q4m.2.concrete) = q4
  exact h4

theorem markedSuppressSigResetKill_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedSuppressSigResetKill hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  let q0 := markedFrame suppressSigStart l r
  have h0 := markedFrame_preserves_fullLocalHistoryTrusted
    suppressSigStart l r hl hr (suppressSigStart_history_frame l.concrete r.concrete)
  change FullLocalHistoryTrusted q0.1.concrete q0.1.history ∧
    FullLocalHistoryTrusted q0.2.concrete q0.2.history at h0
  let q0k := (markedResetKillComparison q0.1,
    markedResetKillComparison q0.2)
  have h0k : FullLocalHistoryTrusted q0k.1.concrete q0k.1.history ∧
      FullLocalHistoryTrusted q0k.2.concrete q0k.2.history :=
    ⟨markedResetKillComparison_preserves_fullLocalHistoryTrusted q0.1 h0.1,
      markedResetKillComparison_preserves_fullLocalHistoryTrusted q0.2 h0.2⟩
  let q1 := markedFrame suppressSigMoveReset q0k.1 q0k.2
  have h1 := markedFrame_preserves_fullLocalHistoryTrusted
    suppressSigMoveReset q0k.1 q0k.2 h0k.1 h0k.2
      (suppressSigMoveReset_history_frame q0k.1.concrete q0k.2.concrete)
  change FullLocalHistoryTrusted q1.1.concrete q1.1.history ∧
    FullLocalHistoryTrusted q1.2.concrete q1.2.history at h1
  let q1k := (markedResetKillComparison q1.1,
    markedResetKillComparison q1.2)
  have h1k : FullLocalHistoryTrusted q1k.1.concrete q1k.1.history ∧
      FullLocalHistoryTrusted q1k.2.concrete q1k.2.history :=
    ⟨markedResetKillComparison_preserves_fullLocalHistoryTrusted q1.1 h1.1,
      markedResetKillComparison_preserves_fullLocalHistoryTrusted q1.2 h1.2⟩
  let q2 := markedFrame (suppressSigTerminal hψ) q1k.1 q1k.2
  have h2 := markedFrame_preserves_fullLocalHistoryTrusted
    (suppressSigTerminal hψ) q1k.1 q1k.2 h1k.1 h1k.2
      (suppressSigTerminal_history_frame hψ q1k.1.concrete q1k.2.concrete)
  change FullLocalHistoryTrusted q2.1.concrete q2.1.history ∧
    FullLocalHistoryTrusted q2.2.concrete q2.2.history at h2
  let q3 := markedFrame suppressSigEcho q2.1 q2.2
  have h3 := markedFrame_preserves_fullLocalHistoryTrusted
    suppressSigEcho q2.1 q2.2 h2.1 h2.2
      (suppressSigEcho_history_frame q2.1.concrete q2.2.concrete)
  change FullLocalHistoryTrusted q3.1.concrete q3.1.history ∧
    FullLocalHistoryTrusted q3.2.concrete q3.2.history at h3
  exact markedFrame_preserves_fullLocalHistoryTrusted
    suppressSigFinish q3.1 q3.2 h3.1 h3.2
      (suppressSigFinish_history_frame q3.1.concrete q3.2.concrete)

/-- One echo-free reset handoff rehabilitates both endpoints even when their
incoming comparison histories are arbitrary or tainted. -/
theorem markedSuppressSigResetKill_handoff_rehabilitates
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hlreset : l.concrete.reset_cmd = true)
    (hrEcho : r.concrete.echo = false) :
    let q := markedSuppressSigResetKill hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history ∧
      q.1.concrete.reset_cmd = false ∧
      q.2.concrete.reset_cmd = true := by
  cases hrightReset : r.concrete.reset_cmd <;>
    simp [markedSuppressSigResetKill, markedFrame,
    markedResetKillComparison, markedClearComparisonSignal,
    clearComparisonHistory, clearComparisonSignal,
    suppressSigStart, suppressSigMoveReset, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish, hlreset, hrEcho,
    FullLocalHistoryTrusted, AuditLocalHistoryTrusted,
    PCarryHistoryTrusted, MarkMatches, hrightReset]

/-! ## Leader/incomplete boundary deletion -/

/-- Marked counterpart of the post-transfer leader wall. -/
def markedComparisonLeaderWall
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let l := if l.concrete.leader ∨ r.concrete.leader then
    markedClearComparisonSignal l
  else l
  let r := if r.concrete.leader then markedClearComparisonSignal r else r
  (l, r)

/-- The marked wall erases exactly to the factor-one physical wall. -/
theorem erase_markedComparisonLeaderWall
    (l r : MarkedAgentState n ψ) :
    let q := markedComparisonLeaderWall l r
    (q.1.concrete, q.2.concrete) =
      comparisonLeaderWall l.concrete r.concrete := by
  unfold markedComparisonLeaderWall comparisonLeaderWall
  dsimp only
  repeat (first | constructor | rfl | split)

theorem markedComparisonLeaderWall_preserves_fullLocalHistoryTrusted
    (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedComparisonLeaderWall l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedComparisonLeaderWall
  dsimp only
  split
  · constructor
    · exact markedClearComparisonSignal_fullLocalHistoryTrusted l
    · split
      · exact markedClearComparisonSignal_fullLocalHistoryTrusted r
      · exact hr
  · constructor
    · exact hl
    · split
      · exact markedClearComparisonSignal_fullLocalHistoryTrusted r
      · exact hr

/-- When the responder is a leader, both sides of the incoming boundary are
trusted idle even if their incoming physical histories were arbitrary. -/
theorem markedComparisonLeaderWall_right_leader_rehabilitates
    (l r : MarkedAgentState n ψ) (hr : r.concrete.leader = true) :
    let q := markedComparisonLeaderWall l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  simp [markedComparisonLeaderWall, hr,
    markedClearComparisonSignal_fullLocalHistoryTrusted]

end PPLLWallSweepHistory

import Leader.Wu.Comparison.HistoryDoneMove
import Leader.Wu.Birth.SigMoveDisposalRepair
import Leader.Wu.WallSweep.PreCheckResetRepair
import Leader.Wu.WallSweep.History

set_option autoImplicit false

namespace PPLLComparisonHistory

open PPLL PPLLRepair
open PPLLAuthorizedComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
open PPLLWallSweepRepair PPLLWallSweepHistory
open PPLLWallSweepPreCheckResetRepair
open PPLLTerminalEqualSupportRepair

variable {n ψ : Nat}

/-- Proof-side history attached to an authorized physical endpoint. -/
structure MarkedAuthorizedAgentState (n ψ : Nat) where
  concrete : AuthorizedAgentState ψ
  history : LocalComparisonHistory n

/-! ## Small fieldwise helpers -/

/-- Clearing only physical `state` to `.none` is represented by an absent
state mark; the other three trusted fields are framed. -/
private theorem clearState_preserves_fullLocalHistoryTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (hu : FullLocalHistoryTrusted s h) :
    FullLocalHistoryTrusted
      { s with state := .none }
      { h with state := .absent } := by
  constructor
  · unfold AuditLocalHistoryTrusted
    exact ⟨.inl ⟨rfl, rfl⟩, hu.1.2.1, hu.1.2.2⟩
  · change MarkMatches (s.p_carry = false) h.pCarry
    exact hu.2

private theorem eliminateState_from_path_preserves_fullLocalHistoryTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (hu : FullLocalHistoryTrusted s h)
    (hpresent : s.path ≠ .bot) :
    FullLocalHistoryTrusted
      { s with state := .eliminate_signal }
      { h with state := h.path } := by
  obtain ⟨source, hsource⟩ :=
    pathSource_of_present s h hu.1 hpresent
  constructor
  · unfold AuditLocalHistoryTrusted
    constructor
    · right
      exact ⟨by simp, source, hsource⟩
    · exact hu.1.2
  · change MarkMatches (s.p_carry = false) h.pCarry
    exact hu.2

/-- History counterpart of `markComparisonForDeletion`: on a present path the
new `.eliminate_signal` state inherits the path source; on `.bot` the physical
operation and history are both unchanged. -/
private def markComparisonForDeletionHistory
    (u : AuthorizedAgentState ψ) (h : LocalComparisonHistory n) :
    LocalComparisonHistory n :=
  match u.core.path with
  | .bot => h
  | .some _ _ => { h with state := h.path }

private theorem markComparisonForDeletionHistory_preserves_fullLocalHistoryTrusted
    (u : AuthorizedAgentState ψ) (h : LocalComparisonHistory n)
    (hu : FullLocalHistoryTrusted u.core h) :
    FullLocalHistoryTrusted
      (PPLLLeaderCreationCleanupRepair.markComparisonForDeletion u).core
      (markComparisonForDeletionHistory u h) := by
  cases hpath : u.core.path with
  | bot =>
      simpa [markComparisonForDeletionHistory,
        PPLLLeaderCreationCleanupRepair.markComparisonForDeletion,
        hpath] using hu
  | some label bit =>
      have hpresent : u.core.path ≠ .bot := by
        rw [hpath]
        intro hbad
        contradiction
      have htrusted :=
        eliminateState_from_path_preserves_fullLocalHistoryTrusted
          u.core h hu hpresent
      simpa [markComparisonForDeletionHistory,
        PPLLLeaderCreationCleanupRepair.markComparisonForDeletion,
        hpath] using htrusted

/-- Exact proof-history update for the authorized entry disposal primitive. -/
def prepareDisposalHistory (hψ : ψ > 0)
    (u : AuthorizedAgentState ψ) (h : LocalComparisonHistory n) :
    LocalComparisonHistory n :=
  if pendingTerminalDisposal hψ u.core then
    markComparisonForDeletionHistory u h
  else h

/-- Marked authorized entry disposal. -/
def markedPrepareDisposal (hψ : ψ > 0)
    (u : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ :=
  ⟨BirthSigMoveDisposalRepair.prepareDisposal hψ u.concrete,
    prepareDisposalHistory hψ u.concrete u.history⟩

/-- The marked disposal lift erases exactly to the current physical primitive. -/
theorem erase_markedPrepareDisposal (hψ : ψ > 0)
    (u : MarkedAuthorizedAgentState n ψ) :
    (markedPrepareDisposal hψ u).concrete =
      BirthSigMoveDisposalRepair.prepareDisposal hψ u.concrete := by
  rfl

/-- Entry disposal preserves all four tracked history fields.  The only
source-writing branch derives `state` from the present trusted `path`. -/
theorem markedPrepareDisposal_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAuthorizedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete.core u.history) :
    FullLocalHistoryTrusted
      (markedPrepareDisposal hψ u).concrete.core
      (markedPrepareDisposal hψ u).history := by
  unfold markedPrepareDisposal prepareDisposalHistory
  dsimp only
  unfold BirthSigMoveDisposalRepair.prepareDisposal
  split
  · exact markComparisonForDeletionHistory_preserves_fullLocalHistoryTrusted
      u.concrete u.history hu
  · exact hu

/-! ## Orphan deletion normalization -/

/-- History update mirroring the exact orphan-normalization guard. -/
def normalizeDeletionHistory
    (u : AuthorizedAgentState ψ) (h : LocalComparisonHistory n) :
    LocalComparisonHistory n :=
  if u.core.state = .eliminate_signal && !pathPresent u then
    { h with state := .absent }
  else h

/-- Marked current orphan-deletion normalization. -/
def markedNormalizeDeletion
    (u : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ :=
  ⟨PPLLLeaderCreationCleanupRepair.normalizeDeletion u.concrete,
    normalizeDeletionHistory u.concrete u.history⟩

/-- The marked normalization erases exactly. -/
theorem erase_markedNormalizeDeletion
    (u : MarkedAuthorizedAgentState n ψ) :
    (markedNormalizeDeletion u).concrete =
      PPLLLeaderCreationCleanupRepair.normalizeDeletion u.concrete := by
  rfl

/-- Orphan normalization is an unconditional clearing stage: when it fires,
`.eliminate_signal` becomes `.none` and the state mark becomes `.absent`. -/
theorem markedNormalizeDeletion_preserves_fullLocalHistoryTrusted
    (u : MarkedAuthorizedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete.core u.history) :
    FullLocalHistoryTrusted
      (markedNormalizeDeletion u).concrete.core
      (markedNormalizeDeletion u).history := by
  unfold markedNormalizeDeletion normalizeDeletionHistory
  dsimp only
  unfold PPLLLeaderCreationCleanupRepair.normalizeDeletion
  split
  · exact clearState_preserves_fullLocalHistoryTrusted
      u.concrete.core u.history hu
  · exact hu

/-! ## Pre-CHECK reset wall -/

/-- Clearing an authorized endpoint uses the already-proved raw clearing
history: all four tracked marks become absent. -/
private theorem clearAuthorizedComparisonHistory_fullLocalHistoryTrusted
    (u : AuthorizedAgentState ψ) (h : LocalComparisonHistory n) :
    FullLocalHistoryTrusted
      (PPLLWallSweepPreCheckResetRepair.clearAuthorizedComparison u).core
      (PPLLWallSweepHistory.clearComparisonHistory h) := by
  have hclear :=
    PPLLWallSweepHistory.markedClearComparisonSignal_fullLocalHistoryTrusted
      (⟨u.core, h⟩ : MarkedAgentState n ψ)
  simpa [PPLLWallSweepPreCheckResetRepair.clearAuthorizedComparison,
    PPLLWallSweepHistory.markedClearComparisonSignal] using hclear

/-- Exact history-side branch structure of `preCheckResetWall`. -/
def preCheckResetWallHistory
    (l r : AuthorizedAgentState ψ)
    (hl hr : LocalComparisonHistory n) :
    LocalComparisonHistory n × LocalComparisonHistory n :=
  let sendRight : Prop :=
    l.core.leader = true ∨ l.core.reset_cmd = true
  let hl' := if sendRight then clearComparisonHistory hl else hl
  let hr' := if sendRight ∨ r.core.reset_cmd = true then
    clearComparisonHistory hr else hr
  (hl', hr')

/-- Marked pre-CHECK reset wall. -/
def markedPreCheckResetWall
    (l r : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ × MarkedAuthorizedAgentState n ψ :=
  let q := PPLLWallSweepPreCheckResetRepair.preCheckResetWall
    l.concrete r.concrete
  let hq := preCheckResetWallHistory
    l.concrete r.concrete l.history r.history
  (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)

/-- The marked reset wall erases exactly to the current physical wall. -/
theorem erase_markedPreCheckResetWall
    (l r : MarkedAuthorizedAgentState n ψ) :
    let q := markedPreCheckResetWall l r
    (q.1.concrete, q.2.concrete) =
      PPLLWallSweepPreCheckResetRepair.preCheckResetWall
        l.concrete r.concrete := by
  rfl

/-- Every clearing branch is trusted without a compatibility premise; an
untouched endpoint simply retains its trusted history. -/
theorem markedPreCheckResetWall_preserves_fullLocalHistoryTrusted
    (l r : MarkedAuthorizedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete.core l.history)
    (hr : FullLocalHistoryTrusted r.concrete.core r.history) :
    let q := markedPreCheckResetWall l r
    FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete.core q.2.history := by
  by_cases hsend :
      l.concrete.core.leader = true ∨ l.concrete.core.reset_cmd = true
  · have hlc := clearAuthorizedComparisonHistory_fullLocalHistoryTrusted
      l.concrete l.history
    have hrc := clearAuthorizedComparisonHistory_fullLocalHistoryTrusted
      r.concrete r.history
    simpa [markedPreCheckResetWall, preCheckResetWallHistory,
      PPLLWallSweepPreCheckResetRepair.preCheckResetWall, hsend] using
      And.intro hlc hrc
  · by_cases hrReset : r.concrete.core.reset_cmd = true
    · have hrc := clearAuthorizedComparisonHistory_fullLocalHistoryTrusted
        r.concrete r.history
      simpa [markedPreCheckResetWall, preCheckResetWallHistory,
        PPLLWallSweepPreCheckResetRepair.preCheckResetWall,
        hsend, hrReset] using And.intro hl hrc
    · simpa [markedPreCheckResetWall, preCheckResetWallHistory,
        PPLLWallSweepPreCheckResetRepair.preCheckResetWall,
        hsend, hrReset] using And.intro hl hr

/-! ## Terminal-equality sanitation -/

/-- Sanitizing unsupported terminal equality clears only the state source. -/
def sanitizeTerminalEqualHistory (hψ : ψ > 0)
    (u : AuthorizedAgentState ψ) (h : LocalComparisonHistory n) :
    LocalComparisonHistory n :=
  if unsupportedTerminalEqual hψ u.core then
    { h with state := .absent }
  else h

/-- Marked local authorized sanitation primitive. -/
def markedSanitizeAuthorizedTerminalEqual (hψ : ψ > 0)
    (u : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ :=
  ⟨PPLLTerminalEqualSupportRepair.sanitizeAuthorizedTerminalEqual
      hψ u.concrete,
    sanitizeTerminalEqualHistory hψ u.concrete u.history⟩

/-- The marked local sanitizer erases exactly. -/
theorem erase_markedSanitizeAuthorizedTerminalEqual
    (hψ : ψ > 0) (u : MarkedAuthorizedAgentState n ψ) :
    (markedSanitizeAuthorizedTerminalEqual hψ u).concrete =
      PPLLTerminalEqualSupportRepair.sanitizeAuthorizedTerminalEqual
        hψ u.concrete := by
  rfl

/-- Terminal sanitation is an unconditional clearing stage. -/
theorem markedSanitizeAuthorizedTerminalEqual_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAuthorizedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete.core u.history) :
    FullLocalHistoryTrusted
      (markedSanitizeAuthorizedTerminalEqual hψ u).concrete.core
      (markedSanitizeAuthorizedTerminalEqual hψ u).history := by
  unfold markedSanitizeAuthorizedTerminalEqual sanitizeTerminalEqualHistory
  dsimp only
  unfold PPLLTerminalEqualSupportRepair.sanitizeAuthorizedTerminalEqual
  split
  · exact clearState_preserves_fullLocalHistoryTrusted
      u.concrete.core u.history hu
  · exact hu

/-- Pairwise marked version of the actual pre-CHECK sanitizer. -/
def markedSanitizeAuthorizedPair (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ × MarkedAuthorizedAgentState n ψ :=
  (markedSanitizeAuthorizedTerminalEqual hψ l,
    markedSanitizeAuthorizedTerminalEqual hψ r)

/-- Pair sanitation erases exactly to `sanitizeAuthorizedPair`. -/
theorem erase_markedSanitizeAuthorizedPair
    (hψ : ψ > 0) (l r : MarkedAuthorizedAgentState n ψ) :
    let q := markedSanitizeAuthorizedPair hψ l r
    (q.1.concrete, q.2.concrete) =
      PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hψ
        (l.concrete, r.concrete) := by
  rfl

/-- Pair sanitation preserves full fieldwise history with no join premise. -/
theorem markedSanitizeAuthorizedPair_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAuthorizedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete.core l.history)
    (hr : FullLocalHistoryTrusted r.concrete.core r.history) :
    let q := markedSanitizeAuthorizedPair hψ l r
    FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete.core q.2.history := by
  exact ⟨
    markedSanitizeAuthorizedTerminalEqual_preserves_fullLocalHistoryTrusted
      hψ l hl,
    markedSanitizeAuthorizedTerminalEqual_preserves_fullLocalHistoryTrusted
      hψ r hr⟩

end PPLLComparisonHistory

#print axioms PPLLComparisonHistory.erase_markedPrepareDisposal
#print axioms PPLLComparisonHistory.markedPrepareDisposal_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedNormalizeDeletion
#print axioms PPLLComparisonHistory.markedNormalizeDeletion_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedPreCheckResetWall
#print axioms PPLLComparisonHistory.markedPreCheckResetWall_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedSanitizeAuthorizedTerminalEqual
#print axioms PPLLComparisonHistory.markedSanitizeAuthorizedTerminalEqual_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedSanitizeAuthorizedPair
#print axioms PPLLComparisonHistory.markedSanitizeAuthorizedPair_preserves_fullLocalHistoryTrusted

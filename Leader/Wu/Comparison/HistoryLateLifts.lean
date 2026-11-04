import Leader.Wu.Comparison.HistoryEntryResetSanitize
import Leader.Wu.Birth.ShortDoneCuts

set_option autoImplicit false

namespace PPLLComparisonHistory

open PPLL PPLLRepair
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
open PPLLWallSweepRepair PPLLWallSweepHistory
open BirthShortWait BirthShortDoneCuts

variable {n ψ width κ τ : Nat}

/-! ## 1. Current width-limited reset-kill SUPPRESS -/

/-- The suffix after the second reset-kill boundary. -/
private def suppressHistoryTail (hψ : 0 < ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q2 := suppressSigTerminal hψ l r
  let q3 := suppressSigEcho q2.1 q2.2
  suppressSigFinish q3.1 q3.2

private theorem shortCountReset_history_frame
    (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AgentState ψ) :
    let q := shortCountReset hwidth hle l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  unfold shortCountReset ComparisonTrackedView.ofState
  repeat (first | constructor | rfl | split)

private theorem lateSuppressTerminal_history_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    let q := suppressSigTerminal hψ l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  unfold suppressSigTerminal ComparisonTrackedView.ofState
  try dsimp only []
  repeat (first | constructor | rfl | split)

private theorem lateSuppressEcho_history_frame
    (l r : AgentState ψ) :
    let q := suppressSigEcho l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  unfold suppressSigEcho ComparisonTrackedView.ofState
  repeat (first | constructor | rfl | split)

private theorem lateSuppressFinish_history_frame
    (l r : AgentState ψ) :
    let q := suppressSigFinish l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  unfold suppressSigFinish ComparisonTrackedView.ofState
  try dsimp only []
  repeat (first | constructor | rfl | split)

private theorem suppressHistoryTail_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    let q := suppressHistoryTail hψ l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  let q2 := suppressSigTerminal hψ l r
  let q3 := suppressSigEcho q2.1 q2.2
  let q4 := suppressSigFinish q3.1 q3.2
  have h2 := lateSuppressTerminal_history_frame hψ l r
  change ComparisonTrackedView.ofState q2.1 = ComparisonTrackedView.ofState l ∧
    ComparisonTrackedView.ofState q2.2 = ComparisonTrackedView.ofState r at h2
  have h3 := lateSuppressEcho_history_frame q2.1 q2.2
  change ComparisonTrackedView.ofState q3.1 = ComparisonTrackedView.ofState q2.1 ∧
    ComparisonTrackedView.ofState q3.2 = ComparisonTrackedView.ofState q2.2 at h3
  have h4 := lateSuppressFinish_history_frame q3.1 q3.2
  change ComparisonTrackedView.ofState q4.1 = ComparisonTrackedView.ofState q3.1 ∧
    ComparisonTrackedView.ofState q4.2 = ComparisonTrackedView.ofState q3.2 at h4
  change ComparisonTrackedView.ofState q4.1 = ComparisonTrackedView.ofState l ∧
    ComparisonTrackedView.ofState q4.2 = ComparisonTrackedView.ofState r
  exact ⟨h4.1.trans (h3.1.trans h2.1),
    h4.2.trans (h3.2.trans h2.2)⟩

/-- The width insertion changes `count` only.  Therefore the current width row
has exactly the same comparison-tracked output as the already-marked reset-kill
SUPPRESS row. -/
private theorem suppressSigResetKillWidth_tracked_eq
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AgentState ψ) :
    let q := suppressSigResetKillWidth hψ hwidth hle l r
    let old := suppressSigResetKill hψ l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState old.1 ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState old.2 := by
  let p := suppressPrefix l r
  let c := shortCountReset hwidth hle p.1 p.2
  have hc := shortCountReset_history_frame hwidth hle p.1 p.2
  change ComparisonTrackedView.ofState c.1 = ComparisonTrackedView.ofState p.1 ∧
    ComparisonTrackedView.ofState c.2 = ComparisonTrackedView.ofState p.2 at hc
  have hn := suppressHistoryTail_frame hψ c.1 c.2
  have ho := suppressHistoryTail_frame hψ p.1 p.2
  have hnew :
      suppressSigResetKillWidth hψ hwidth hle l r =
        suppressHistoryTail hψ c.1 c.2 := by
    rfl
  have hold :
      suppressSigResetKill hψ l r =
        suppressHistoryTail hψ p.1 p.2 := by
    rfl
  rw [hnew, hold]
  exact ⟨hn.1.trans (hc.1.trans ho.1.symm),
    hn.2.trans (hc.2.trans ho.2.symm)⟩

/-- Current shortened SUPPRESS.  The old marked reset-kill row already performs
the two source-mark clears at the exact reset boundaries; the additional
short-count write is history-neutral. -/
def markedSuppressSigResetKillWidth
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let old := PPLLWallSweepHistory.markedSuppressSigResetKill hψ l r
  let q := suppressSigResetKillWidth hψ hwidth hle l.concrete r.concrete
  (⟨q.1, old.1.history⟩, ⟨q.2, old.2.history⟩)

/-- Exact erasure to the current width-limited physical SUPPRESS. -/
theorem erase_markedSuppressSigResetKillWidth
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : MarkedAgentState n ψ) :
    let q := markedSuppressSigResetKillWidth hψ hwidth hle l r
    (q.1.concrete, q.2.concrete) =
      suppressSigResetKillWidth hψ hwidth hle l.concrete r.concrete := by
  rfl

/-- Reset-kill SUPPRESS preserves full four-field trust.  No compatibility
premise is needed: reset kills clear all four marks, and every other changed
piece is a physical frame. -/
theorem markedSuppressSigResetKillWidth_preserves_fullLocalHistoryTrusted
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedSuppressSigResetKillWidth hψ hwidth hle l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  let oldm := PPLLWallSweepHistory.markedSuppressSigResetKill hψ l r
  let oldp := suppressSigResetKill hψ l.concrete r.concrete
  let newp := suppressSigResetKillWidth hψ hwidth hle l.concrete r.concrete
  have ht :=
    PPLLWallSweepHistory.markedSuppressSigResetKill_preserves_fullLocalHistoryTrusted
      hψ l r hl hr
  change FullLocalHistoryTrusted oldm.1.concrete oldm.1.history ∧
    FullLocalHistoryTrusted oldm.2.concrete oldm.2.history at ht
  have he := PPLLWallSweepHistory.erase_markedSuppressSigResetKill hψ l r
  change (oldm.1.concrete, oldm.2.concrete) = oldp at he
  have heL : oldm.1.concrete = oldp.1 := congrArg Prod.fst he
  have heR : oldm.2.concrete = oldp.2 := congrArg Prod.snd he
  have htL : FullLocalHistoryTrusted oldp.1 oldm.1.history := by
    rw [← heL]
    exact ht.1
  have htR : FullLocalHistoryTrusted oldp.2 oldm.2.history := by
    rw [← heR]
    exact ht.2
  have hv := suppressSigResetKillWidth_tracked_eq
    hψ hwidth hle l.concrete r.concrete
  change ComparisonTrackedView.ofState newp.1 = ComparisonTrackedView.ofState oldp.1 ∧
    ComparisonTrackedView.ofState newp.2 = ComparisonTrackedView.ofState oldp.2 at hv
  have hnewL := fullLocalHistoryTrusted_of_trackedView_eq
    oldp.1 newp.1 oldm.1.history htL hv.1
  have hnewR := fullLocalHistoryTrusted_of_trackedView_eq
    oldp.2 newp.2 oldm.2.history htR hv.2
  change FullLocalHistoryTrusted newp.1 oldm.1.history ∧
    FullLocalHistoryTrusted newp.2 oldm.2.history
  exact ⟨hnewL, hnewR⟩

/-- The exact authorized current-host SUPPRESS cut, with the raw marked histories
carried through `authorizedReconcile`. -/
def markedAuthorizedSuppressWidth
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ × MarkedAuthorizedAgentState n ψ :=
  let lm : MarkedAgentState n ψ := ⟨l.concrete.core, l.history⟩
  let rm : MarkedAgentState n ψ := ⟨r.concrete.core, r.history⟩
  let m := markedSuppressSigResetKillWidth hψ hwidth hle lm rm
  let q := BirthShortDoneCuts.authorizedSuppressWidth
    hψ hwidth hle l.concrete r.concrete
  (⟨q.1, m.1.history⟩, ⟨q.2, m.2.history⟩)

/-- Erasure of the authorized marked lift is exactly `authorizedSuppressWidth`. -/
theorem erase_markedAuthorizedSuppressWidth
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : MarkedAuthorizedAgentState n ψ) :
    let q := markedAuthorizedSuppressWidth hψ hwidth hle l r
    (q.1.concrete, q.2.concrete) =
      BirthShortDoneCuts.authorizedSuppressWidth
        hψ hwidth hle l.concrete r.concrete := by
  rfl

/-- Authorization changes only the wrapper permit; the current raw cores retain
the full trusted histories proved above. -/
theorem markedAuthorizedSuppressWidth_preserves_fullLocalHistoryTrusted
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : MarkedAuthorizedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete.core l.history)
    (hr : FullLocalHistoryTrusted r.concrete.core r.history) :
    let q := markedAuthorizedSuppressWidth hψ hwidth hle l r
    FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete.core q.2.history := by
  let lm : MarkedAgentState n ψ := ⟨l.concrete.core, l.history⟩
  let rm : MarkedAgentState n ψ := ⟨r.concrete.core, r.history⟩
  let m := markedSuppressSigResetKillWidth hψ hwidth hle lm rm
  let q := BirthShortDoneCuts.authorizedSuppressWidth
    hψ hwidth hle l.concrete r.concrete
  have hm := markedSuppressSigResetKillWidth_preserves_fullLocalHistoryTrusted
    hψ hwidth hle lm rm hl hr
  change FullLocalHistoryTrusted m.1.concrete m.1.history ∧
    FullLocalHistoryTrusted m.2.concrete m.2.history at hm
  have he := erase_markedSuppressSigResetKillWidth hψ hwidth hle lm rm
  change (m.1.concrete, m.2.concrete) =
    suppressSigResetKillWidth hψ hwidth hle
      l.concrete.core r.concrete.core at he
  have hcore : (q.1.core, q.2.core) = (m.1.concrete, m.2.concrete) := by
    calc
      (q.1.core, q.2.core) =
          suppressSigResetKillWidth hψ hwidth hle
            l.concrete.core r.concrete.core := by
        rfl
      _ = (m.1.concrete, m.2.concrete) := he.symm
  have hL : q.1.core = m.1.concrete := congrArg Prod.fst hcore
  have hR : q.2.core = m.2.concrete := congrArg Prod.snd hcore
  change FullLocalHistoryTrusted q.1.core m.1.history ∧
    FullLocalHistoryTrusted q.2.core m.2.history
  constructor
  · rw [hL]
    exact hm.1
  · rw [hR]
    exact hm.2

/-! ## 2. Post-WRITE leader-birth deletion marking -/

private theorem eliminateStateFromPath_fullLocalHistoryTrusted
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

/-- History counterpart of the actual deletion marker.  A present path donates
its authenticated source to the new `.eliminate_signal` state; a pathless
endpoint is unchanged. -/
def markComparisonForDeletionHistory
    (u : AuthorizedAgentState ψ) (h : LocalComparisonHistory n) :
    LocalComparisonHistory n :=
  match u.core.path with
  | .bot => h
  | .some _ _ => { h with state := h.path }

/-- Marked one-endpoint deletion marker. -/
def markedMarkComparisonForDeletion
    (u : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ :=
  ⟨PPLLLeaderCreationCleanupRepair.markComparisonForDeletion u.concrete,
    markComparisonForDeletionHistory u.concrete u.history⟩

/-- Exact erasure to `markComparisonForDeletion`. -/
theorem erase_markedMarkComparisonForDeletion
    (u : MarkedAuthorizedAgentState n ψ) :
    (markedMarkComparisonForDeletion u).concrete =
      PPLLLeaderCreationCleanupRepair.markComparisonForDeletion u.concrete := by
  rfl

/-- Deletion marking preserves full local history and never fabricates a
source from a pathless endpoint. -/
theorem markedMarkComparisonForDeletion_preserves_fullLocalHistoryTrusted
    (u : MarkedAuthorizedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete.core u.history) :
    FullLocalHistoryTrusted
      (markedMarkComparisonForDeletion u).concrete.core
      (markedMarkComparisonForDeletion u).history := by
  cases hpath : u.concrete.core.path with
  | bot =>
      simpa [markedMarkComparisonForDeletion,
        markComparisonForDeletionHistory,
        PPLLLeaderCreationCleanupRepair.markComparisonForDeletion,
        hpath] using hu
  | some label bit =>
      have hpresent : u.concrete.core.path ≠ .bot := by
        rw [hpath]
        intro hbad
        contradiction
      have ht := eliminateStateFromPath_fullLocalHistoryTrusted
        u.concrete.core u.history hu hpresent
      simpa [markedMarkComparisonForDeletion,
        markComparisonForDeletionHistory,
        PPLLLeaderCreationCleanupRepair.markComparisonForDeletion,
        hpath] using ht

/-- Pairwise post-WRITE birth marker. -/
def markedMarkLeaderBirth (born : Bool)
    (l r : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ × MarkedAuthorizedAgentState n ψ :=
  if born then
    (markedMarkComparisonForDeletion l, markedMarkComparisonForDeletion r)
  else (l, r)

/-- Exact erasure to the source `PPLLLeaderCreationCleanupRepair.markLeaderBirth`. -/
theorem erase_markedMarkLeaderBirth (born : Bool)
    (l r : MarkedAuthorizedAgentState n ψ) :
    let q := markedMarkLeaderBirth born l r
    (q.1.concrete, q.2.concrete) =
      PPLLLeaderCreationCleanupRepair.markLeaderBirth
        born (l.concrete, r.concrete) := by
  cases born <;> rfl

/-- The observed-birth wrapper preserves full history without a join premise. -/
theorem markedMarkLeaderBirth_preserves_fullLocalHistoryTrusted
    (born : Bool) (l r : MarkedAuthorizedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete.core l.history)
    (hr : FullLocalHistoryTrusted r.concrete.core r.history) :
    let q := markedMarkLeaderBirth born l r
    FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete.core q.2.history := by
  cases born with
  | false =>
      simpa [markedMarkLeaderBirth] using And.intro hl hr
  | true =>
      have hl' :=
        markedMarkComparisonForDeletion_preserves_fullLocalHistoryTrusted l hl
      have hr' :=
        markedMarkComparisonForDeletion_preserves_fullLocalHistoryTrusted r hr
      simpa [markedMarkLeaderBirth] using And.intro hl' hr'

/-! ## 3. Current deletion-priority/path-stall expiry -/

/-- Marked expiring endpoint used only by this proof refinement. -/
structure MarkedExpiringAgentState (n ψ κ τ : Nat) where
  concrete : ExpiringAgentState ψ κ τ
  history : LocalComparisonHistory n

/-- Exact history policy of `deletionPriorityExpireOne`: active deletion,
physical path progress, and positive static stall all retain the output history;
only the zero/static expiry branch clears all four source marks. -/
def deletionPriorityExpireOneHistory (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (h : LocalComparisonHistory n) : LocalComparisonHistory n :=
  if deletionActive out.core.erase then h
  else if PathProgressView.ofState out.core ≠ PathProgressView.ofState old.core then h
  else if old.stall.val = 0 then PPLLWallSweepHistory.clearComparisonHistory h
  else h

/-- Marked current expiry wrapper. -/
def markedDeletionPriorityExpireOne (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (h : LocalComparisonHistory n) : MarkedExpiringAgentState n ψ κ τ :=
  ⟨PPLLLeaderCreationCleanupRepair.deletionPriorityExpireOne τ old out,
    deletionPriorityExpireOneHistory τ old out h⟩

/-- Exact erasure to the current physical expiry. -/
theorem erase_markedDeletionPriorityExpireOne (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (h : LocalComparisonHistory n) :
    (markedDeletionPriorityExpireOne τ old out h).concrete =
      PPLLLeaderCreationCleanupRepair.deletionPriorityExpireOne τ old out := by
  rfl

private theorem clearComparisonCarrier_history_fullLocalHistoryTrusted
    (u : AuthorizedBoundedAgentState ψ κ)
    (h : LocalComparisonHistory n) :
    FullLocalHistoryTrusted
      (PPLLExpiringComparisonRepair.clearComparisonCarrier u).erase.core
      (PPLLWallSweepHistory.clearComparisonHistory h) := by
  simp [PPLLExpiringComparisonRepair.clearComparisonCarrier,
    PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase,
    BoundedAgentState.erase,
    PPLLWallSweepHistory.clearComparisonHistory,
    FullLocalHistoryTrusted, AuditLocalHistoryTrusted,
    PCarryHistoryTrusted, MarkMatches] <;> rfl

/-- Current expiry preserves full local history.  The zero/static branch is
trusted unconditionally because both the physical carrier and all four marks
are cleared; every other branch leaves `out.core` unchanged. -/
theorem markedDeletionPriorityExpireOne_preserves_fullLocalHistoryTrusted
    (τ : Nat) (old out : ExpiringAgentState ψ κ τ)
    (h : LocalComparisonHistory n)
    (hout : FullLocalHistoryTrusted out.core.erase.core h) :
    FullLocalHistoryTrusted
      (markedDeletionPriorityExpireOne τ old out h).concrete.core.erase.core
      (markedDeletionPriorityExpireOne τ old out h).history := by
  cases hactive : deletionActive out.core.erase with
  | true =>
      simpa [markedDeletionPriorityExpireOne,
        deletionPriorityExpireOneHistory,
        PPLLLeaderCreationCleanupRepair.deletionPriorityExpireOne,
        hactive] using hout
  | false =>
      by_cases hprogress :
          PathProgressView.ofState out.core ≠ PathProgressView.ofState old.core
      · simpa [markedDeletionPriorityExpireOne,
          deletionPriorityExpireOneHistory,
          PPLLLeaderCreationCleanupRepair.deletionPriorityExpireOne,
          PPLLPathStallComparisonRepair.pathExpireOne,
          hactive, hprogress] using hout
      · by_cases hzero : old.stall.val = 0
        · have hc := clearComparisonCarrier_history_fullLocalHistoryTrusted
            out.core h
          simpa [markedDeletionPriorityExpireOne,
            deletionPriorityExpireOneHistory,
            PPLLLeaderCreationCleanupRepair.deletionPriorityExpireOne,
            PPLLPathStallComparisonRepair.pathExpireOne,
            hactive, hprogress, hzero] using hc
        · simpa [markedDeletionPriorityExpireOne,
            deletionPriorityExpireOneHistory,
            PPLLLeaderCreationCleanupRepair.deletionPriorityExpireOne,
            PPLLPathStallComparisonRepair.pathExpireOne,
            hactive, hprogress, hzero] using hout

end PPLLComparisonHistory

#print axioms PPLLComparisonHistory.erase_markedSuppressSigResetKillWidth
#print axioms PPLLComparisonHistory.markedSuppressSigResetKillWidth_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedAuthorizedSuppressWidth
#print axioms PPLLComparisonHistory.markedAuthorizedSuppressWidth_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedMarkComparisonForDeletion
#print axioms PPLLComparisonHistory.markedMarkComparisonForDeletion_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedMarkLeaderBirth
#print axioms PPLLComparisonHistory.markedMarkLeaderBirth_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedDeletionPriorityExpireOne
#print axioms PPLLComparisonHistory.markedDeletionPriorityExpireOne_preserves_fullLocalHistoryTrusted

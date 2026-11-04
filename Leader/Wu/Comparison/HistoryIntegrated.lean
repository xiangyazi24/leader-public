import Leader.Wu.Comparison.HistoryCompare

/-!
# Integrated comparison-history replay

The comparison proof ghost must replay the exact repaired Algorithm-1 order
without influencing a physical branch. This module first isolates the four
physical fields whose histories are tracked—comparison state, path, path2, and
the DISAPPEAR carry—and supplies a generic physical-first adapter for stages
that frame all four. Stage-specific frame theorems remain mandatory: the
adapter itself proves erasure, not that a transition is history-neutral.
-/

namespace PPLLComparisonHistory

open PPLL PPLLRepair PPLLComparisonLifecycle

/-- The complete physical projection observed by `LocalComparisonHistory`.
Equality of this view is exactly what permits a stage to retain all four marks. -/
structure ComparisonTrackedView (ψ : Nat) where
  state : MainState
  path : PathInfo
  path2 : Option Path2Info
  pCarry : Bool
  deriving DecidableEq, Repr

namespace ComparisonTrackedView

/-- Extract all physical fields represented by comparison-history marks. -/
def ofState (s : AgentState ψ) : ComparisonTrackedView ψ :=
  ⟨s.state, s.path, s.path2, s.p_carry⟩

end ComparisonTrackedView

/-- Physical-first wrapper for a pair transition proved separately to frame the
comparison projection. The histories are retained verbatim. -/
def markedFrame
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := f l.concrete r.concrete
  (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- A framed marked transition always erases to its supplied physical stage. -/
theorem erase_markedFrame
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : MarkedAgentState n ψ) :
    let q := markedFrame f l r
    (q.1.concrete, q.2.concrete) = f l.concrete r.concrete := by
  rfl

/-- Equality of the four-field view transports full local history trust while
retaining the old marks. -/
theorem fullLocalHistoryTrusted_of_trackedView_eq
    (old out : AgentState ψ) (h : LocalComparisonHistory n)
    (hold : FullLocalHistoryTrusted old h)
    (hview : ComparisonTrackedView.ofState out =
      ComparisonTrackedView.ofState old) :
    FullLocalHistoryTrusted out h := by
  have hstate := congrArg ComparisonTrackedView.state hview
  have hpath := congrArg ComparisonTrackedView.path hview
  have hpath2 := congrArg ComparisonTrackedView.path2 hview
  have hpCarry := congrArg ComparisonTrackedView.pCarry hview
  change out.state = old.state at hstate
  change out.path = old.path at hpath
  change out.path2 = old.path2 at hpath2
  change out.p_carry = old.p_carry at hpCarry
  unfold FullLocalHistoryTrusted AuditLocalHistoryTrusted
    PCarryHistoryTrusted at hold ⊢
  rw [hstate, hpath, hpath2, hpCarry]
  exact hold

/-- A pairwise physical frame lifts the generic wrapper to full history trust. -/
theorem markedFrame_preserves_fullLocalHistoryTrusted
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hframe :
      let q := f l.concrete r.concrete
      ComparisonTrackedView.ofState q.1 =
          ComparisonTrackedView.ofState l.concrete ∧
        ComparisonTrackedView.ofState q.2 =
          ComparisonTrackedView.ofState r.concrete) :
    let q := markedFrame f l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  exact ⟨fullLocalHistoryTrusted_of_trackedView_eq
      l.concrete _ l.history hl hframe.1,
    fullLocalHistoryTrusted_of_trackedView_eq
      r.concrete _ r.history hr hframe.2⟩

/-! ## Algorithm 2 frame -/

/-- The barrier/probe subprotocol changes labels and leadership controls but
frames all four comparison-history fields. -/
theorem pPsi_comparisonTracked_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := pPsi hψ l r
    ComparisonTrackedView.ofState q.1 =
        ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 =
        ComparisonTrackedView.ofState r := by
  unfold pPsi
  dsimp only
  repeat (first | constructor | rfl | split)

/-- Marked Algorithm 2 retains comparison history while executing the exact
physical transition. -/
def markedPPsi (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  markedFrame (pPsi hψ) l r

/-- Marked Algorithm 2 erases exactly. -/
theorem erase_markedPPsi (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedPPsi hψ l r
    (q.1.concrete, q.2.concrete) = pPsi hψ l.concrete r.concrete := by
  rfl

/-- Algorithm 2 preserves full local comparison history. -/
theorem markedPPsi_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedPPsi hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  exact markedFrame_preserves_fullLocalHistoryTrusted
    (pPsi hψ) l r hl hr (pPsi_comparisonTracked_frame hψ l.concrete r.concrete)

/-! ## Post-comparison physical frames -/

/-- Pair projection used to compose small physical frame lemmas without
unfolding an entire multi-stage algorithm. -/
def comparisonTrackedPair (q : AgentState ψ × AgentState ψ) :
    ComparisonTrackedView ψ × ComparisonTrackedView ψ :=
  (ComparisonTrackedView.ofState q.1,
    ComparisonTrackedView.ofState q.2)

/-- Sequential composition of two pair transitions. -/
def pairThen
    (f g : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := f l r
  g q.1 q.2

private theorem pairThen_tracked
    (f g : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ l r, comparisonTrackedPair (f l r) =
      comparisonTrackedPair (l, r))
    (hg : ∀ l r, comparisonTrackedPair (g l r) =
      comparisonTrackedPair (l, r))
    (l r : AgentState ψ) :
    comparisonTrackedPair (pairThen f g l r) =
      comparisonTrackedPair (l, r) := by
  let q := f l r
  have hq := hg q.1 q.2
  change comparisonTrackedPair (g q.1 q.2) = comparisonTrackedPair q at hq
  exact hq.trans (hf l r)

private theorem trackedPair_eq_components
    {q : AgentState ψ × AgentState ψ} {l r : AgentState ψ}
    (h : comparisonTrackedPair q = comparisonTrackedPair (l, r)) :
    ComparisonTrackedView.ofState q.1 =
        ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 =
        ComparisonTrackedView.ofState r := by
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

private theorem suppressSigStart_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (suppressSigStart l r) =
      comparisonTrackedPair (l, r) := by
  unfold suppressSigStart comparisonTrackedPair
  split <;> rfl

private theorem suppressSigMoveReset_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (suppressSigMoveReset l r) =
      comparisonTrackedPair (l, r) := by
  unfold suppressSigMoveReset comparisonTrackedPair
  split <;> rfl

private theorem suppressSigTerminal_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (suppressSigTerminal hψ l r) =
      comparisonTrackedPair (l, r) := by
  unfold suppressSigTerminal comparisonTrackedPair
  split <;> rfl

private theorem suppressSigEcho_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (suppressSigEcho l r) =
      comparisonTrackedPair (l, r) := by
  unfold suppressSigEcho comparisonTrackedPair
  repeat (first | rfl | split)

private theorem suppressSigFinish_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (suppressSigFinish l r) =
      comparisonTrackedPair (l, r) := by
  unfold suppressSigFinish comparisonTrackedPair
  split <;> rfl

/-- SUPPRESS_SIG changes reset/count/echo controls only and frames comparison
state, both path carriers, and the lottery carry. -/
theorem suppressSig_comparisonTracked_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := suppressSig hψ l r
    ComparisonTrackedView.ofState q.1 =
        ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 =
        ComparisonTrackedView.ofState r := by
  rw [suppressSig_eq_staged]
  let q0 := suppressSigStart l r
  let q1 := suppressSigMoveReset q0.1 q0.2
  let q2 := suppressSigTerminal hψ q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  let q4 := suppressSigFinish q3.1 q3.2
  have h0 := suppressSigStart_tracked l r
  have h1 := suppressSigMoveReset_tracked q0.1 q0.2
  have h2 := suppressSigTerminal_tracked hψ q1.1 q1.2
  have h3 := suppressSigEcho_tracked q2.1 q2.2
  have h4 := suppressSigFinish_tracked q3.1 q3.2
  change comparisonTrackedPair q0 = comparisonTrackedPair (l, r) at h0
  change comparisonTrackedPair q1 = comparisonTrackedPair q0 at h1
  change comparisonTrackedPair q2 = comparisonTrackedPair q1 at h2
  change comparisonTrackedPair q3 = comparisonTrackedPair q2 at h3
  change comparisonTrackedPair q4 = comparisonTrackedPair q3 at h4
  exact trackedPair_eq_components (h4.trans (h3.trans (h2.trans (h1.trans h0))))

/-- Marked SUPPRESS_SIG retains all comparison-history marks. -/
def markedSuppressSig (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  markedFrame (suppressSig hψ) l r

/-- Marked SUPPRESS_SIG erases exactly. -/
theorem erase_markedSuppressSig (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedSuppressSig hψ l r
    (q.1.concrete, q.2.concrete) = suppressSig hψ l.concrete r.concrete := by
  rfl

/-- SUPPRESS_SIG preserves full local comparison history. -/
theorem markedSuppressSig_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedSuppressSig hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  exact markedFrame_preserves_fullLocalHistoryTrusted
    (suppressSig hψ) l r hl hr
      (suppressSig_comparisonTracked_frame hψ l.concrete r.concrete)

private theorem eliminateLeadersNoCollisionFire_tracked
    (hψ : ψ > 0) (l r : AgentState ψ) :
    comparisonTrackedPair (eliminateLeadersNoCollisionFire hψ l r) =
      comparisonTrackedPair (l, r) := by
  unfold eliminateLeadersNoCollisionFire comparisonTrackedPair
  repeat (first | rfl | split)

private theorem eliminateLeadersNoCollisionMove_tracked
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    comparisonTrackedPair
        (eliminateLeadersNoCollisionMove nextLabel l r) =
      comparisonTrackedPair (l, r) := by
  unfold eliminateLeadersNoCollisionMove comparisonTrackedPair
  repeat (first | rfl | split)

private theorem eliminateLeadersNoCollisionSignal_tracked
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    comparisonTrackedPair
        (eliminateLeadersNoCollisionSignal nextLabel l r) =
      comparisonTrackedPair (l, r) := by
  unfold eliminateLeadersNoCollisionSignal comparisonTrackedPair
  repeat (first | rfl | split)

/-- The no-collision leader-elimination repair changes only leader/bullet/
signal controls and frames all four comparison-history fields. -/
theorem eliminateLeadersNoCollision_comparisonTracked_frame
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateLeadersNoCollision hψ l r
    ComparisonTrackedView.ofState q.1 =
        ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 =
        ComparisonTrackedView.ofState r := by
  rw [eliminateLeadersNoCollision_eq_staged]
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignal nextLabel q1.1 q1.2
  have h0 := eliminateLeadersNoCollisionFire_tracked hψ l r
  have h1 := eliminateLeadersNoCollisionMove_tracked
    nextLabel q0.1 q0.2
  have h2 := eliminateLeadersNoCollisionSignal_tracked
    nextLabel q1.1 q1.2
  change comparisonTrackedPair q0 = comparisonTrackedPair (l, r) at h0
  change comparisonTrackedPair q1 = comparisonTrackedPair q0 at h1
  change comparisonTrackedPair q2 = comparisonTrackedPair q1 at h2
  exact trackedPair_eq_components (h2.trans (h1.trans h0))

private theorem eliminateLeadersNoCollisionSignalLeaderSink_tracked
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    comparisonTrackedPair
        (eliminateLeadersNoCollisionSignalLeaderSink nextLabel l r) =
      comparisonTrackedPair (l, r) := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink comparisonTrackedPair
  repeat (first | rfl | split)

/-- The rooted leader-sink variant changes the same physical control fields as
the established no-collision repair and therefore retains the complete
comparison-history projection. -/
theorem eliminateLeadersNoCollisionLeaderSink_comparisonTracked_frame
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    ComparisonTrackedView.ofState q.1 =
        ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 =
        ComparisonTrackedView.ofState r := by
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink
    nextLabel q1.1 q1.2
  have h0 := eliminateLeadersNoCollisionFire_tracked hψ l r
  have h1 := eliminateLeadersNoCollisionMove_tracked
    nextLabel q0.1 q0.2
  have h2 := eliminateLeadersNoCollisionSignalLeaderSink_tracked
    nextLabel q1.1 q1.2
  change comparisonTrackedPair q0 = comparisonTrackedPair (l, r) at h0
  change comparisonTrackedPair q1 = comparisonTrackedPair q0 at h1
  change comparisonTrackedPair q2 = comparisonTrackedPair q1 at h2
  exact trackedPair_eq_components (h2.trans (h1.trans h0))

/-- Marked no-collision Algorithm 15 retains comparison history. -/
def markedEliminateLeadersNoCollision (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  markedFrame (eliminateLeadersNoCollision hψ) l r

/-- Marked no-collision Algorithm 15 erases exactly. -/
theorem erase_markedEliminateLeadersNoCollision (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedEliminateLeadersNoCollision hψ l r
    (q.1.concrete, q.2.concrete) =
      eliminateLeadersNoCollision hψ l.concrete r.concrete := by
  rfl

/-- No-collision leader elimination preserves full local comparison history. -/
theorem markedEliminateLeadersNoCollision_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedEliminateLeadersNoCollision hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  exact markedFrame_preserves_fullLocalHistoryTrusted
    (eliminateLeadersNoCollision hψ) l r hl hr
      (eliminateLeadersNoCollision_comparisonTracked_frame
        hψ l.concrete r.concrete)

private theorem writeSeqLeaderMove_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqLeaderMove hψ l r) =
      comparisonTrackedPair (l, r) := by
  unfold writeSeqLeaderMove comparisonTrackedPair
  split <;> rfl

private theorem groupInfoStart_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (groupInfoStart hψ l r) =
      comparisonTrackedPair (l, r) := by
  simp [groupInfoStart, comparisonTrackedPair,
    ComparisonTrackedView.ofState]

private theorem groupInfoSet_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (groupInfoSet hψ l r) =
      comparisonTrackedPair (l, r) := by
  unfold groupInfoSet comparisonTrackedPair
  repeat (first | rfl | split)

private theorem groupInfoUnset_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (groupInfoUnset l r) =
      comparisonTrackedPair (l, r) := by
  unfold groupInfoUnset comparisonTrackedPair
  repeat (first | rfl | split)

private theorem groupInfo_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (groupInfo hψ l r) =
      comparisonTrackedPair (l, r) := by
  rw [groupInfo_eq_staged]
  let q0 := groupInfoStart hψ l r
  let q1 := groupInfoSet hψ q0.1 q0.2
  let q2 := groupInfoUnset q1.1 q1.2
  have h0 := groupInfoStart_tracked hψ l r
  have h1 := groupInfoSet_tracked hψ q0.1 q0.2
  have h2 := groupInfoUnset_tracked q1.1 q1.2
  change comparisonTrackedPair q0 = comparisonTrackedPair (l, r) at h0
  change comparisonTrackedPair q1 = comparisonTrackedPair q0 at h1
  change comparisonTrackedPair q2 = comparisonTrackedPair q1 at h2
  exact h2.trans (h1.trans h0)

private theorem gensigWriteseqStart_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (gensigWriteseqStart hψ l r) =
      comparisonTrackedPair (l, r) := by
  simp [gensigWriteseqStart, comparisonTrackedPair,
    ComparisonTrackedView.ofState]

private theorem gensigWriteseqEmit_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (gensigWriteseqEmit hψ l r) =
      comparisonTrackedPair (l, r) := by
  simp [gensigWriteseqEmit, comparisonTrackedPair,
    ComparisonTrackedView.ofState]

private theorem gensigWriteseqPropagate_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (gensigWriteseqPropagate hψ l r) =
      comparisonTrackedPair (l, r) := by
  simp [gensigWriteseqPropagate, comparisonTrackedPair,
    ComparisonTrackedView.ofState]

private theorem gensigWriteseqFinish_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (gensigWriteseqFinish hψ l r) =
      comparisonTrackedPair (l, r) := by
  unfold gensigWriteseqFinish comparisonTrackedPair
  split <;> rfl

private theorem gensigWriteseq_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (gensigWriteseq hψ l r) =
      comparisonTrackedPair (l, r) := by
  rw [gensigWriteseq_eq_staged]
  let q0 := gensigWriteseqStart hψ l r
  let q1 := gensigWriteseqEmit hψ q0.1 q0.2
  let q2 := gensigWriteseqPropagate hψ q1.1 q1.2
  let q3 := gensigWriteseqFinish hψ q2.1 q2.2
  have h0 := gensigWriteseqStart_tracked hψ l r
  have h1 := gensigWriteseqEmit_tracked hψ q0.1 q0.2
  have h2 := gensigWriteseqPropagate_tracked hψ q1.1 q1.2
  have h3 := gensigWriteseqFinish_tracked hψ q2.1 q2.2
  change comparisonTrackedPair q0 = comparisonTrackedPair (l, r) at h0
  change comparisonTrackedPair q1 = comparisonTrackedPair q0 at h1
  change comparisonTrackedPair q2 = comparisonTrackedPair q1 at h2
  change comparisonTrackedPair q3 = comparisonTrackedPair q2 at h3
  exact h3.trans (h2.trans (h1.trans h0))

private theorem writeSeqGenerate_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqGenerate hψ l r) =
      comparisonTrackedPair (l, r) := by
  unfold writeSeqGenerate
  split
  · exact gensigWriteseq_tracked hψ l r
  · rfl

private theorem writeSeqSetWriteReady_tracked (u : AgentState ψ) :
    ComparisonTrackedView.ofState (writeSeqSetWriteReady u) =
      ComparisonTrackedView.ofState u := by
  unfold writeSeqSetWriteReady
  cases u.path3 <;> repeat (first | rfl | split)

private theorem writeSeqCheckBit_tracked (u : AgentState ψ) :
    ComparisonTrackedView.ofState (writeSeqCheckBit u) =
      ComparisonTrackedView.ofState u := by
  unfold writeSeqCheckBit
  cases u.path3 <;> rfl

private theorem writeSeqSetWriteAct_tracked (u : AgentState ψ) :
    ComparisonTrackedView.ofState (writeSeqSetWriteAct u) =
      ComparisonTrackedView.ofState u := by
  unfold writeSeqSetWriteAct
  dsimp only
  repeat (first | rfl | split)

private theorem writeSeqFinalR_tracked (u : AgentState ψ) :
    ComparisonTrackedView.ofState (writeSeqFinalR u) =
      ComparisonTrackedView.ofState u := by
  unfold writeSeqFinalR
  cases u.path3 <;> repeat (first | rfl | split)

private theorem writeSeqReady_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqReady l r) =
      comparisonTrackedPair (l, r) := by
  unfold writeSeqReady comparisonTrackedPair
  rw [writeSeqSetWriteReady_tracked, writeSeqSetWriteReady_tracked]

private theorem writeSeqCompare_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqCompare hψ l r) =
      comparisonTrackedPair (l, r) := by
  let r0 := if r.label = ⟨0, hψ⟩ ∧ r.write_state = .ready then
    writeSeqCheckBit r else r
  let r1 := if l.label.val < ψ - 1 ∧ l.write_state = .equal ∧
      r0.write_state = .ready then writeSeqCheckBit r0 else r0
  have h0 : ComparisonTrackedView.ofState r0 =
      ComparisonTrackedView.ofState r := by
    dsimp only [r0]
    split
    · exact writeSeqCheckBit_tracked r
    · rfl
  have h1 : ComparisonTrackedView.ofState r1 =
      ComparisonTrackedView.ofState r0 := by
    dsimp only [r1]
    split
    · exact writeSeqCheckBit_tracked r0
    · rfl
  change comparisonTrackedPair (l, r1) = comparisonTrackedPair (l, r)
  unfold comparisonTrackedPair
  rw [h1, h0]

private theorem writeSeqCommands_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqCommands hψ l r) =
      comparisonTrackedPair (l, r) := by
  let l0 := writeSeqSetWriteAct l
  let r0 := writeSeqSetWriteAct r
  let r1 := if r0.label = ⟨ψ - 1, by omega⟩ ∧
      r0.write_state = .equal then writeSeqFinalR r0 else r0
  have hl0 := writeSeqSetWriteAct_tracked l
  have hr0 := writeSeqSetWriteAct_tracked r
  have hr1 : ComparisonTrackedView.ofState r1 =
      ComparisonTrackedView.ofState r0 := by
    dsimp only [r1]
    split
    · exact writeSeqFinalR_tracked r0
    · rfl
  change comparisonTrackedPair (l0, r1) = comparisonTrackedPair (l, r)
  unfold comparisonTrackedPair
  rw [hl0, hr1, hr0]

private theorem writeSeqPrepare_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqPrepare hψ l r) =
      comparisonTrackedPair (l, r) := by
  unfold writeSeqPrepare
  let q0 := writeSeqReady l r
  let q1 := writeSeqCompare hψ q0.1 q0.2
  let q2 := writeSeqCommands hψ q1.1 q1.2
  have h0 := writeSeqReady_tracked l r
  have h1 := writeSeqCompare_tracked hψ q0.1 q0.2
  have h2 := writeSeqCommands_tracked hψ q1.1 q1.2
  change comparisonTrackedPair q0 = comparisonTrackedPair (l, r) at h0
  change comparisonTrackedPair q1 = comparisonTrackedPair q0 at h1
  change comparisonTrackedPair q2 = comparisonTrackedPair q1 at h2
  exact h2.trans (h1.trans h0)

private theorem writeActionActivate_tracked (hψ : ψ > 0)
    (u : AgentState ψ) :
    ComparisonTrackedView.ofState (writeActionActivate hψ u) =
      ComparisonTrackedView.ofState u := by
  unfold writeActionActivate
  split <;> rfl

private theorem writeActionApplyOverwrite_tracked (u : AgentState ψ) :
    ComparisonTrackedView.ofState (writeActionApplyOverwrite u) =
      ComparisonTrackedView.ofState u := by
  unfold writeActionApplyOverwrite
  cases u.path3 <;> rfl

private theorem writeActionApplyMoveFlip_tracked (u : AgentState ψ) :
    ComparisonTrackedView.ofState (writeActionApplyMoveFlip u) =
      ComparisonTrackedView.ofState u := by
  unfold writeActionApplyMoveFlip
  cases u.path3 <;> rfl

private theorem writeActionExecute_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeActionExecute hψ l r) =
      comparisonTrackedPair (l, r) := by
  by_cases hrun : l.label < r.label ∨ r.label = ⟨0, hψ⟩
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
    have hr0 : ComparisonTrackedView.ofState r0 =
        ComparisonTrackedView.ofState r := by
      dsimp only [r0]
      split
      · exact writeActionApplyOverwrite_tracked r
      · rfl
    have hr1 : ComparisonTrackedView.ofState r1 =
        ComparisonTrackedView.ofState r0 := by
      dsimp only [r1]
      split
      · exact writeActionApplyMoveFlip_tracked r0
      · rfl
    have hr2 : ComparisonTrackedView.ofState r2 =
        ComparisonTrackedView.ofState r1 := by
      dsimp only [r2]
      repeat (first | rfl | split)
    have hl0 : ComparisonTrackedView.ofState l0 =
        ComparisonTrackedView.ofState l := by
      dsimp only [l0]
      split <;> rfl
    unfold writeActionExecute
    rw [if_pos hrun]
    change comparisonTrackedPair
      (l0, { r2 with write_state := .depart }) = comparisonTrackedPair (l, r)
    unfold comparisonTrackedPair
    rw [hl0]
    have hright : ComparisonTrackedView.ofState
        { r2 with write_state := .depart } =
        ComparisonTrackedView.ofState r := by
      change ComparisonTrackedView.ofState r2 =
        ComparisonTrackedView.ofState r
      exact hr2.trans (hr1.trans hr0)
    rw [hright]
  · unfold writeActionExecute
    rw [if_neg hrun]

private theorem writeAction_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeAction hψ l r) =
      comparisonTrackedPair (l, r) := by
  rw [writeAction_eq_staged]
  let l0 := writeActionActivate hψ l
  let r0 := writeActionActivate hψ r
  have hl := writeActionActivate_tracked hψ l
  have hr := writeActionActivate_tracked hψ r
  have hq := writeActionExecute_tracked hψ l0 r0
  change comparisonTrackedPair (writeActionExecute hψ l0 r0) =
    comparisonTrackedPair (l0, r0) at hq
  change ComparisonTrackedView.ofState l0 =
    ComparisonTrackedView.ofState l at hl
  change ComparisonTrackedView.ofState r0 =
    ComparisonTrackedView.ofState r at hr
  have hbase : comparisonTrackedPair (l0, r0) =
      comparisonTrackedPair (l, r) := by
    unfold comparisonTrackedPair
    rw [hl, hr]
  exact hq.trans hbase

private theorem moveWsigCheckLast_tracked (u : AgentState ψ) :
    ComparisonTrackedView.ofState (moveWsigCheckLast u) =
      ComparisonTrackedView.ofState u := by
  unfold moveWsigCheckLast
  cases u.path3 <;> repeat (first | rfl | split)

private theorem moveWsigStart_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (moveWsigStart l r) =
      comparisonTrackedPair (l, r) := by
  unfold moveWsigStart moveWsigCheckGenWs comparisonTrackedPair
  repeat (first | rfl | split)

private theorem moveWsigTransfer_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (moveWsigTransfer l r) =
      comparisonTrackedPair (l, r) := by
  cases hlpath : l.path3 with
  | none => simp [moveWsigTransfer, hlpath]
  | some p3 =>
      cases hrpath : r.path3 with
      | some p3r => simp [moveWsigTransfer, hlpath, hrpath]
      | none =>
          by_cases hdepart : l.write_state = .depart
          · by_cases hecho : r.ws_echo = false
            · simp [moveWsigTransfer, hlpath, hrpath, hdepart, hecho,
                comparisonTrackedPair, ComparisonTrackedView.ofState]
            · simp [moveWsigTransfer, hlpath, hrpath, hdepart, hecho,
                comparisonTrackedPair, ComparisonTrackedView.ofState]
          · simp [moveWsigTransfer, hlpath, hrpath, hdepart]

private theorem moveWsigMoveWrite_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (moveWsigMoveWrite l r) =
      comparisonTrackedPair (l, r) := by
  unfold moveWsigMoveWrite comparisonTrackedPair
  split <;> rfl

private theorem moveWsigLeaderSignal_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (moveWsigLeaderSignal l r) =
      comparisonTrackedPair (l, r) := by
  unfold moveWsigLeaderSignal comparisonTrackedPair
  split <;> rfl

private theorem moveWsigSignalMove_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (moveWsigSignalMove l r) =
      comparisonTrackedPair (l, r) := by
  unfold moveWsigSignalMove comparisonTrackedPair
  repeat (first | rfl | split)

private theorem moveWsigEchoMove_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (moveWsigEchoMove l r) =
      comparisonTrackedPair (l, r) := by
  unfold moveWsigEchoMove comparisonTrackedPair
  repeat (first | rfl | split)

private theorem moveWsigFinish_tracked (l r : AgentState ψ) :
    comparisonTrackedPair (moveWsigFinish l r) =
      comparisonTrackedPair (l, r) := by
  unfold moveWsigFinish
  let q0 := moveWsigMoveWrite l r
  let q1 := moveWsigLeaderSignal q0.1 q0.2
  let q2 := moveWsigSignalMove q1.1 q1.2
  let q3 := moveWsigEchoMove q2.1 q2.2
  have h0 := moveWsigMoveWrite_tracked l r
  have h1 := moveWsigLeaderSignal_tracked q0.1 q0.2
  have h2 := moveWsigSignalMove_tracked q1.1 q1.2
  have h3 := moveWsigEchoMove_tracked q2.1 q2.2
  change comparisonTrackedPair q0 = comparisonTrackedPair (l, r) at h0
  change comparisonTrackedPair q1 = comparisonTrackedPair q0 at h1
  change comparisonTrackedPair q2 = comparisonTrackedPair q1 at h2
  change comparisonTrackedPair q3 = comparisonTrackedPair q2 at h3
  exact h3.trans (h2.trans (h1.trans h0))

private theorem moveWsig_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (moveWsig hψ l r) =
      comparisonTrackedPair (l, r) := by
  rw [moveWsig_eq_staged]
  let q0 := moveWsigStart l r
  let l1 := moveWsigCheckLast q0.1
  let q1 := moveWsigTransfer l1 q0.2
  let q2 := moveWsigFinish q1.1 q1.2
  have h0 := moveWsigStart_tracked l r
  have hl := moveWsigCheckLast_tracked q0.1
  have h1 := moveWsigTransfer_tracked l1 q0.2
  have h2 := moveWsigFinish_tracked q1.1 q1.2
  change comparisonTrackedPair q0 = comparisonTrackedPair (l, r) at h0
  change ComparisonTrackedView.ofState l1 =
    ComparisonTrackedView.ofState q0.1 at hl
  change comparisonTrackedPair q1 = comparisonTrackedPair (l1, q0.2) at h1
  change comparisonTrackedPair q2 = comparisonTrackedPair q1 at h2
  have h01 : comparisonTrackedPair (l1, q0.2) =
      comparisonTrackedPair q0 := by
    unfold comparisonTrackedPair
    rw [hl]
  exact h2.trans (h1.trans (h01.trans h0))

private theorem writeSeqThroughPrepare_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqThroughPrepare hψ l r) =
      comparisonTrackedPair (l, r) := by
  unfold writeSeqThroughPrepare
  let q0 := writeSeqLeaderMove hψ l r
  let q1 := groupInfo hψ q0.1 q0.2
  let q2 := writeSeqGenerate hψ q1.1 q1.2
  have h0 := writeSeqLeaderMove_tracked hψ l r
  have h1 := groupInfo_tracked hψ q0.1 q0.2
  have h2 := writeSeqGenerate_tracked hψ q1.1 q1.2
  have h3 := writeSeqPrepare_tracked hψ q2.1 q2.2
  have hchain := h3.trans (h2.trans (h1.trans h0))
  exact hchain

/-- Public factored interface for the four comparison-history fields through
the Algorithm-16 preparation boundary.  Downstream repaired WRITE variants can
reuse this theorem without reopening Algorithms 17--18. -/
theorem writeSeqThroughPrepare_comparisonTracked_pair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqThroughPrepare hψ l r) =
      comparisonTrackedPair (l, r) :=
  writeSeqThroughPrepare_tracked hψ l r

private theorem writeSeqAfterPrepare_tracked (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqAfterPrepare hψ l r) =
      comparisonTrackedPair (l, r) := by
  unfold writeSeqAfterPrepare
  let q0 := writeAction hψ l r
  have h0 := writeAction_tracked hψ l r
  have h1 := moveWsig_tracked hψ q0.1 q0.2
  exact h1.trans h0

/-- Public factored interface for the four comparison-history fields after
command preparation.  It applies to arbitrary prepared inputs, so a local
command gate may be inserted before this suffix without changing the view. -/
theorem writeSeqAfterPrepare_comparisonTracked_pair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    comparisonTrackedPair (writeSeqAfterPrepare hψ l r) =
      comparisonTrackedPair (l, r) :=
  writeSeqAfterPrepare_tracked hψ l r

/-- WRITE_SEQ may mutate group bits and write carriers, but it never writes the
four comparison-history fields. This frame theorem intentionally says nothing
about historical payload immutability. -/
theorem writeSeq_comparisonTracked_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := writeSeq hψ l r
    ComparisonTrackedView.ofState q.1 =
        ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 =
        ComparisonTrackedView.ofState r := by
  have hpair := pairThen_tracked (writeSeqThroughPrepare hψ)
    (writeSeqAfterPrepare hψ) (writeSeqThroughPrepare_tracked hψ)
      (writeSeqAfterPrepare_tracked hψ) l r
  change comparisonTrackedPair (writeSeq hψ l r) =
    comparisonTrackedPair (l, r) at hpair
  exact trackedPair_eq_components hpair

/-- Marked WRITE_SEQ retains comparison-history marks while executing every
physical write subalgorithm. -/
def markedWriteSeq (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  markedFrame (writeSeq hψ) l r

/-- Marked WRITE_SEQ erases exactly. -/
theorem erase_markedWriteSeq (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedWriteSeq hψ l r
    (q.1.concrete, q.2.concrete) = writeSeq hψ l.concrete r.concrete := by
  exact erase_markedFrame (writeSeq hψ) l r

/-- WRITE_SEQ preserves the four-field local history relation. -/
theorem markedWriteSeq_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedWriteSeq hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  exact markedFrame_preserves_fullLocalHistoryTrusted
    (writeSeq hψ) l r hl hr
      (writeSeq_comparisonTracked_frame hψ l.concrete r.concrete)

end PPLLComparisonHistory

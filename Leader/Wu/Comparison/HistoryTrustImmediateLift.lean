import Leader.Wu.Comparison.HistoryIntegrated
import Leader.Wu.WriteSeq.StationaryWritePersistent
import Leader.Wu.WallSweep.Repair
import Leader.Wu.Birth.ShortWaitTerminalEntryRepair
import Leader.Wu.Elimination.BirthDispatcherLeaderNormalize

namespace Q11515ImmediateHistoryLift

open PPLL PPLLComparisonHistory BirthStationaryWrite

set_option autoImplicit false

variable {n ψ : Nat}

/-- Current stationary persistent WRITE, not the older `writeSeq`. -/
def markedStationaryPersistentRaw (hψ : 0 < ψ)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  markedFrame (stationaryPersistentRaw hψ) l r

/-- Erasure is definitionally the current physical writer. -/
theorem erase_markedStationaryPersistentRaw (hψ : 0 < ψ)
    (l r : MarkedAgentState n ψ) :
    let q := markedStationaryPersistentRaw hψ l r
    (q.1.concrete, q.2.concrete) =
      stationaryPersistentRaw hψ l.concrete r.concrete := by
  simpa only [markedStationaryPersistentRaw] using
    (erase_markedFrame (stationaryPersistentRaw hψ) l r)

/-- The current physical comparison-frame theorem closes history trust. -/
theorem markedStationaryPersistentRaw_preserves_fullLocalHistoryTrusted
    (hψ : 0 < ψ) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedStationaryPersistentRaw hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  have hpair := stationaryPersistentRaw_comparison hψ l.concrete r.concrete
  have hL := congrArg
    (fun q : ComparisonTrackedView ψ × ComparisonTrackedView ψ => q.1)
    hpair
  have hR := congrArg
    (fun q : ComparisonTrackedView ψ × ComparisonTrackedView ψ => q.2)
    hpair
  have hframe :
      ComparisonTrackedView.ofState
          (stationaryPersistentRaw hψ l.concrete r.concrete).1 =
        ComparisonTrackedView.ofState l.concrete ∧
      ComparisonTrackedView.ofState
          (stationaryPersistentRaw hψ l.concrete r.concrete).2 =
        ComparisonTrackedView.ofState r.concrete := by
    constructor
    · simpa only [comparisonTrackedPair] using hL
    · simpa only [comparisonTrackedPair] using hR
  simpa only [markedStationaryPersistentRaw] using
    (markedFrame_preserves_fullLocalHistoryTrusted
      (stationaryPersistentRaw hψ) l r hl hr hframe)

end Q11515ImmediateHistoryLift

namespace Q11525CurrentHistoryFrames

open PPLL PPLLRepair PPLLComparisonHistory
open PPLLExpiringComparisonRepair

set_option autoImplicit false

variable {n ψ width κ τ : Nat}

/-! ## (a) Current P-prime/probe wall -/

/-- The current leader/reset probe wall changes no comparison-tracked field. -/
theorem pPsiLeaderResetProbeWall_comparisonTracked_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    let q := PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  let l0 : AgentState ψ :=
    if l.leader = true then { l with probe := false } else l
  let r0 : AgentState ψ :=
    if r.leader = true ∨ l.leader = true ∨ l.reset_cmd = true then
      { r with probe := false }
    else r
  have hl0 :
      ComparisonTrackedView.ofState l0 = ComparisonTrackedView.ofState l := by
    dsimp only [l0]
    split <;> rfl
  have hr0 :
      ComparisonTrackedView.ofState r0 = ComparisonTrackedView.ofState r := by
    dsimp only [r0]
    split <;> rfl
  have hp := pPsi_comparisonTracked_frame hψ l0 r0
  dsimp only at hp
  have h :
      ComparisonTrackedView.ofState (pPsi hψ l0 r0).1 =
          ComparisonTrackedView.ofState l ∧
        ComparisonTrackedView.ofState (pPsi hψ l0 r0).2 =
          ComparisonTrackedView.ofState r :=
    ⟨hp.1.trans hl0, hp.2.trans hr0⟩
  simpa only [PPLLWallSweepRepair.pPsiLeaderResetProbeWall, l0, r0] using h

/-- Marked current P-prime/probe wall: history is retained verbatim. -/
def markedPPsiLeaderResetProbeWall (hψ : 0 < ψ)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  markedFrame (PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ) l r

/-- The marked wall erases exactly to the current physical wall. -/
theorem erase_markedPPsiLeaderResetProbeWall (hψ : 0 < ψ)
    (l r : MarkedAgentState n ψ) :
    let q := markedPPsiLeaderResetProbeWall hψ l r
    (q.1.concrete, q.2.concrete) =
      PPLLWallSweepRepair.pPsiLeaderResetProbeWall
        hψ l.concrete r.concrete := by
  simpa only [markedPPsiLeaderResetProbeWall] using
    (erase_markedFrame
      (PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ) l r)

/-- The current wall preserves the full four-field local-history trust relation. -/
theorem markedPPsiLeaderResetProbeWall_preserves_fullLocalHistoryTrusted
    (hψ : 0 < ψ) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedPPsiLeaderResetProbeWall hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  simpa only [markedPPsiLeaderResetProbeWall] using
    (markedFrame_preserves_fullLocalHistoryTrusted
      (PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ) l r hl hr
      (pPsiLeaderResetProbeWall_comparisonTracked_frame
        hψ l.concrete r.concrete))

/-! ## (b) Current shortened WAIT -/

private theorem waitSaturatedPrepare_comparisonTracked_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    let q := PPLLRepair.waitSaturatedPrepare hψ l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  simp only [PPLLRepair.waitSaturatedPrepare, ComparisonTrackedView.ofState]
  repeat (first | constructor | rfl | split)

private theorem terminalInactiveClear_comparisonTracked_frame
    (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    let q := BirthShortWaitTerminalEntryRepair.terminalInactiveClear
      hwidth hle l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  simp only [BirthShortWaitTerminalEntryRepair.terminalInactiveClear,
    ComparisonTrackedView.ofState]
  repeat (first | constructor | rfl | split)

private theorem waitWidthCarry_comparisonTracked_frame
    (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AgentState ψ) :
    let q := BirthShortWait.waitWidthCarry hwidth hle κ l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  simp only [BirthShortWait.waitWidthCarry, ComparisonTrackedView.ofState]
  repeat (first | constructor | rfl | split)

private theorem waitWidthReset_comparisonTracked_frame
    (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    let q := BirthShortWait.waitWidthReset hwidth hle l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  simp only [BirthShortWait.waitWidthReset, ComparisonTrackedView.ofState]
  repeat (first | constructor | rfl | split)

private theorem waitWidthFinish_comparisonTracked_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AgentState ψ) :
    let q := BirthShortWait.waitWidthFinish hψ hwidth hle κ l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  simp only [BirthShortWait.waitWidthFinish, ComparisonTrackedView.ofState]
  repeat (first | constructor | rfl | split)

/-- The corrected shortened WAIT changes only WAIT/clock/count controls, not
`state`, `path`, `path2`, or `p_carry`. -/
theorem waitWidthEntry_comparisonTracked_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AgentState ψ) :
    let q := BirthShortWaitTerminalEntryRepair.waitWidthEntry
      hψ hwidth hle κ l r
    ComparisonTrackedView.ofState q.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q.2 = ComparisonTrackedView.ofState r := by
  let q0 := PPLLRepair.waitSaturatedPrepare hψ l r
  let q1 := BirthShortWaitTerminalEntryRepair.terminalInactiveClear
    hwidth hle q0.1 q0.2
  let q2 := BirthShortWait.waitWidthCarry hwidth hle κ q1.1 q1.2
  let q3 := BirthShortWait.waitWidthReset hwidth hle q2.1 q2.2
  let q4 := BirthShortWait.waitWidthFinish hψ hwidth hle κ q3.1 q3.2

  have h0 := waitSaturatedPrepare_comparisonTracked_frame hψ l r
  change
    ComparisonTrackedView.ofState q0.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q0.2 = ComparisonTrackedView.ofState r at h0

  have h1 := terminalInactiveClear_comparisonTracked_frame
    hwidth hle q0.1 q0.2
  change
    ComparisonTrackedView.ofState q1.1 = ComparisonTrackedView.ofState q0.1 ∧
      ComparisonTrackedView.ofState q1.2 = ComparisonTrackedView.ofState q0.2 at h1

  have h2 := waitWidthCarry_comparisonTracked_frame
    hwidth hle κ q1.1 q1.2
  change
    ComparisonTrackedView.ofState q2.1 = ComparisonTrackedView.ofState q1.1 ∧
      ComparisonTrackedView.ofState q2.2 = ComparisonTrackedView.ofState q1.2 at h2

  have h3 := waitWidthReset_comparisonTracked_frame
    hwidth hle q2.1 q2.2
  change
    ComparisonTrackedView.ofState q3.1 = ComparisonTrackedView.ofState q2.1 ∧
      ComparisonTrackedView.ofState q3.2 = ComparisonTrackedView.ofState q2.2 at h3

  have h4 := waitWidthFinish_comparisonTracked_frame
    hψ hwidth hle κ q3.1 q3.2
  change
    ComparisonTrackedView.ofState q4.1 = ComparisonTrackedView.ofState q3.1 ∧
      ComparisonTrackedView.ofState q4.2 = ComparisonTrackedView.ofState q3.2 at h4

  change
    ComparisonTrackedView.ofState q4.1 = ComparisonTrackedView.ofState l ∧
      ComparisonTrackedView.ofState q4.2 = ComparisonTrackedView.ofState r
  constructor
  · calc
      ComparisonTrackedView.ofState q4.1 =
          ComparisonTrackedView.ofState q3.1 := h4.1
      _ = ComparisonTrackedView.ofState q2.1 := h3.1
      _ = ComparisonTrackedView.ofState q1.1 := h2.1
      _ = ComparisonTrackedView.ofState q0.1 := h1.1
      _ = ComparisonTrackedView.ofState l := h0.1
  · calc
      ComparisonTrackedView.ofState q4.2 =
          ComparisonTrackedView.ofState q3.2 := h4.2
      _ = ComparisonTrackedView.ofState q2.2 := h3.2
      _ = ComparisonTrackedView.ofState q1.2 := h2.2
      _ = ComparisonTrackedView.ofState q0.2 := h1.2
      _ = ComparisonTrackedView.ofState r := h0.2

/-- Marked current shortened WAIT: history is retained verbatim. -/
def markedWaitWidthEntry
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  markedFrame
    (BirthShortWaitTerminalEntryRepair.waitWidthEntry hψ hwidth hle κ) l r

/-- The marked shortened WAIT erases exactly to the corrected physical row. -/
theorem erase_markedWaitWidthEntry
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : MarkedAgentState n ψ) :
    let q := markedWaitWidthEntry hψ hwidth hle κ l r
    (q.1.concrete, q.2.concrete) =
      BirthShortWaitTerminalEntryRepair.waitWidthEntry
        hψ hwidth hle κ l.concrete r.concrete := by
  simpa only [markedWaitWidthEntry] using
    (erase_markedFrame
      (BirthShortWaitTerminalEntryRepair.waitWidthEntry
        hψ hwidth hle κ) l r)

/-- The current shortened WAIT preserves full local comparison history. -/
theorem markedWaitWidthEntry_preserves_fullLocalHistoryTrusted
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedWaitWidthEntry hψ hwidth hle κ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  simpa only [markedWaitWidthEntry] using
    (markedFrame_preserves_fullLocalHistoryTrusted
      (BirthShortWaitTerminalEntryRepair.waitWidthEntry
        hψ hwidth hle κ) l r hl hr
      (waitWidthEntry_comparisonTracked_frame
        hψ hwidth hle κ l.concrete r.concrete))

/-! ## (c) `normalizeLeader` -/

private theorem putLabel_comparisonTracked_frame
    (q : ExpiringAgentState ψ κ τ) (a : Fin ψ) :
    ComparisonTrackedView.ofState
        (K2BirthLeaderNormalize.putLabel q a).core.erase.core =
      ComparisonTrackedView.ofState q.core.erase.core := by
  rfl

/-- Leader-label normalization is invisible to comparison history.  This is
proved through the exact `normalizeLeader_field_frame`; `normalizeLeader` itself
is not unfolded. -/
theorem normalizeLeader_comparisonTracked_frame
    (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    ComparisonTrackedView.ofState
        (K2BirthLeaderNormalize.normalizeLeader hψ q).core.erase.core =
      ComparisonTrackedView.ofState q.core.erase.core := by
  have hrestore := K2BirthLeaderNormalize.normalizeLeader_field_frame hψ q
  have hv := congrArg
    (fun u : ExpiringAgentState ψ κ τ =>
      ComparisonTrackedView.ofState u.core.erase.core)
    hrestore
  exact
    (putLabel_comparisonTracked_frame
      (K2BirthLeaderNormalize.normalizeLeader hψ q) q.core.core.label).symm.trans hv

/-! ## (d) `finalPhysical` -/

private theorem nonK2_comparisonTracked_frame
    (q : ExpiringAgentState ψ κ τ) :
    ComparisonTrackedView.ofState
        (ExpiringK2Projection.nonK2 q).core.erase.core =
      ComparisonTrackedView.ofState q.core.erase.core := by
  rfl

private theorem nonK2_eq_comparisonTracked_frame
    {a b : ExpiringAgentState ψ κ τ}
    (h : ExpiringK2Projection.nonK2 a = ExpiringK2Projection.nonK2 b) :
    ComparisonTrackedView.ofState a.core.erase.core =
      ComparisonTrackedView.ofState b.core.erase.core := by
  have hv := congrArg
    (fun u : ExpiringAgentState ψ κ τ =>
      ComparisonTrackedView.ofState u.core.erase.core)
    h
  exact
    (nonK2_comparisonTracked_frame a).symm.trans
      (hv.trans (nonK2_comparisonTracked_frame b))

/-- Newborn initialization and the collision/K2 tail preserve the complete
comparison-tracked view of the computed metadata endpoints. -/
theorem finalPhysical_comparisonTracked_frame
    (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    let q := K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR
    ComparisonTrackedView.ofState q.1.core.erase.core =
        ComparisonTrackedView.ofState metaL.core.erase.core ∧
      ComparisonTrackedView.ofState q.2.core.erase.core =
        ComparisonTrackedView.ofState metaR.core.erase.core := by
  dsimp only
  have hf := K2BirthDispatcher.finalPhysical_nonK2
    hψ oldL oldR metaL metaR
  exact
    ⟨nonK2_eq_comparisonTracked_frame hf.1,
      nonK2_eq_comparisonTracked_frame hf.2⟩

end Q11525CurrentHistoryFrames

#print axioms Q11515ImmediateHistoryLift.erase_markedStationaryPersistentRaw
#print axioms Q11515ImmediateHistoryLift.markedStationaryPersistentRaw_preserves_fullLocalHistoryTrusted
#print axioms Q11525CurrentHistoryFrames.pPsiLeaderResetProbeWall_comparisonTracked_frame
#print axioms Q11525CurrentHistoryFrames.erase_markedPPsiLeaderResetProbeWall
#print axioms Q11525CurrentHistoryFrames.markedPPsiLeaderResetProbeWall_preserves_fullLocalHistoryTrusted
#print axioms Q11525CurrentHistoryFrames.waitWidthEntry_comparisonTracked_frame
#print axioms Q11525CurrentHistoryFrames.erase_markedWaitWidthEntry
#print axioms Q11525CurrentHistoryFrames.markedWaitWidthEntry_preserves_fullLocalHistoryTrusted
#print axioms Q11525CurrentHistoryFrames.normalizeLeader_comparisonTracked_frame
#print axioms Q11525CurrentHistoryFrames.finalPhysical_comparisonTracked_frame

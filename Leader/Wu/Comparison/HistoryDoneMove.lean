import Leader.Wu.Comparison.HistoryDoneMoveAssumingCapture
import Leader.Wu.Birth.SingleUseReleaseRepair


set_option autoImplicit false


namespace PPLLComparisonHistory


open PPLL PPLLRepair
open PPLLWallSweepRepair PPLLWallSweepHistory
open BirthGenerationDone BirthSingleUseReleaseRepair


variable {n ψ : Nat}


/-! ## 1. Discharge the temporary capture premise -/


/-- The repaired current capture theorem supplies the exact temporary interface
used by `ComparisonHistoryDoneMove`. -/
theorem captureStep1Preservation_repaired :
    CaptureStep1Preservation n ψ := by
  intro l r hl hr
  exact markedCaptureStep1_preserves_auditLocalHistoryTrusted l r hl hr


/-- Unconditional current held-Step1 preservation. -/
theorem markedHoldDoneStep1_preserves_auditLocalHistoryTrusted_unconditional
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedHoldDoneStep1 l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  exact markedHoldDoneStep1_preserves_auditLocalHistoryTrusted
    (captureStep1Preservation_repaired (n := n) (ψ := ψ)) l r hl hr


/-- Unconditional current transfer-prefix preservation. -/
theorem markedDoneTransfers_preserves_auditLocalHistoryTrusted_unconditional
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedDoneTransfers l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  exact markedDoneTransfers_preserves_auditLocalHistoryTrusted
    (captureStep1Preservation_repaired (n := n) (ψ := ψ)) l r hl hr


/-! ## 2. Single-use control history -/


/-- Proof-side counterpart of the post-control terminal action-five token
projection.  It changes only the tracked path2 mark, exactly where the physical
projection clears path2. -/
private def markedClearTerminalRelease (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  match u.concrete.path2 with
  | some p2 =>
      if _hrelease :
          u.concrete.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧
            p2.action = 5 then
        ⟨clearTerminalRelease hψ u.concrete,
          { u.history with path2 := .absent }⟩
      else u
  | none => u


private theorem erase_markedClearTerminalRelease
    (hψ : ψ > 0) (u : MarkedAgentState n ψ) :
    (markedClearTerminalRelease hψ u).concrete =
      clearTerminalRelease hψ u.concrete := by
  unfold markedClearTerminalRelease
  dsimp only
  split
  next p2 hp2 =>
    split
    next hrelease =>
      rfl
    next hrelease =>
      simp [clearTerminalRelease, hp2, hrelease]
  next hp2 =>
    simp [clearTerminalRelease, hp2]


private theorem
    markedClearTerminalRelease_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history) :
    AuditLocalHistoryTrusted
      (markedClearTerminalRelease hψ u).concrete
      (markedClearTerminalRelease hψ u).history := by
  unfold markedClearTerminalRelease
  dsimp only
  split
  next p2 hp2 =>
    split
    next hrelease =>
      have hout : clearTerminalRelease hψ u.concrete =
          { u.concrete with path2 := none } := by
        simp [clearTerminalRelease, hp2, hrelease]
      rw [hout]
      unfold AuditLocalHistoryTrusted
      exact ⟨hu.1, hu.2.1, .inl ⟨rfl, rfl⟩⟩
    next hrelease =>
      exact hu
  next hp2 =>
    exact hu


/-- Current single-use control.  The old marked control first derives any new
state source from authenticated path2.  The terminal action-five projection is
then applied, so action 5 keeps that derived state source while clearing the
path2 mark to absent. -/
def markedSingleUseApplyControl (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  markedClearTerminalRelease hψ (markedSigMoveApplyControl hψ u)


/-- The marked single-use local control erases exactly. -/
theorem erase_markedSingleUseApplyControl (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) :
    (markedSingleUseApplyControl hψ u).concrete =
      singleUseApplyControl hψ u.concrete := by
  change
    (markedClearTerminalRelease hψ
      (markedSigMoveApplyControl hψ u)).concrete =
      singleUseApplyControl hψ u.concrete
  calc
    (markedClearTerminalRelease hψ
        (markedSigMoveApplyControl hψ u)).concrete =
        clearTerminalRelease hψ
          (markedSigMoveApplyControl hψ u).concrete :=
      erase_markedClearTerminalRelease hψ
        (markedSigMoveApplyControl hψ u)
    _ = clearTerminalRelease hψ
          (sigMoveApplyControl hψ u.concrete) := by
      rw [erase_markedSigMoveApplyControl]
    _ = singleUseApplyControl hψ u.concrete :=
      (singleUseApplyControl_eq_clear hψ u.concrete).symm


/-- Actions 3/4/6 inherit the existing marked control ancestry rule.  Terminal
action 5 also inherits its old path2 source for the new depart state, then the
consumed path2 is marked absent. -/
theorem markedSingleUseApplyControl_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history) :
    AuditLocalHistoryTrusted
      (markedSingleUseApplyControl hψ u).concrete
      (markedSingleUseApplyControl hψ u).history := by
  change AuditLocalHistoryTrusted
    (markedClearTerminalRelease hψ
      (markedSigMoveApplyControl hψ u)).concrete
    (markedClearTerminalRelease hψ
      (markedSigMoveApplyControl hψ u)).history
  exact markedClearTerminalRelease_preserves_auditLocalHistoryTrusted
    hψ (markedSigMoveApplyControl hψ u)
    (markedSigMoveApplyControl_preserves_auditLocalHistoryTrusted
      hψ u hu)


/-- Marked current single-use control tail: two independent local control
applications followed by the unchanged backward departure propagation. -/
def markedSingleUseControlTail (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let l6 := markedSingleUseApplyControl hψ l
  let r6 := markedSingleUseApplyControl hψ r
  markedSigMoveDepart hψ l6 r6


/-- The marked current control tail erases exactly to the physical
single-use tail. -/
theorem erase_markedSingleUseControlTail (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedSingleUseControlTail hψ l r
    (q.1.concrete, q.2.concrete) =
      singleUseControlTail hψ l.concrete r.concrete := by
  let l6 := markedSingleUseApplyControl hψ l
  let r6 := markedSingleUseApplyControl hψ r
  let pl6 := singleUseApplyControl hψ l.concrete
  let pr6 := singleUseApplyControl hψ r.concrete
  have hl6 := erase_markedSingleUseApplyControl hψ l
  have hr6 := erase_markedSingleUseApplyControl hψ r
  change l6.concrete = pl6 at hl6
  change r6.concrete = pr6 at hr6
  let q7 := markedSigMoveDepart hψ l6 r6
  have hq7 := erase_markedSigMoveDepart hψ l6 r6
  change (q7.1.concrete, q7.2.concrete) =
    (let left := if r6.concrete.state = .depart then
      if l6.concrete.label.val < ψ - 1 ∧
          l6.concrete.state = .CHECK_ready then
        { l6.concrete with state := .depart }
      else l6.concrete
    else l6.concrete
    (left, r6.concrete)) at hq7
  rw [hl6, hr6] at hq7
  change (q7.1.concrete, q7.2.concrete) =
    (let left := if pr6.state = .depart then
      if pl6.label.val < ψ - 1 ∧ pl6.state = .CHECK_ready then
        { pl6 with state := .depart }
      else pl6
    else pl6
    (left, pr6)) at hq7
  change (q7.1.concrete, q7.2.concrete) =
    singleUseControlTail hψ l.concrete r.concrete
  exact hq7.trans (by rfl)


/-- The single-use control tail preserves fieldwise trust under exactly the old
backward-departure source join, evaluated after both local control applications. -/
theorem markedSingleUseControlTail_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hcompat :
      let l6 := markedSingleUseApplyControl hψ l
      let r6 := markedSingleUseApplyControl hψ r
      SigMoveDepartCompatible hψ l6 r6) :
    let q := markedSingleUseControlTail hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  let l6 := markedSingleUseApplyControl hψ l
  let r6 := markedSingleUseApplyControl hψ r
  have hl6 :=
    markedSingleUseApplyControl_preserves_auditLocalHistoryTrusted
      hψ l hl
  have hr6 :=
    markedSingleUseApplyControl_preserves_auditLocalHistoryTrusted
      hψ r hr
  change AuditLocalHistoryTrusted l6.concrete l6.history at hl6
  change AuditLocalHistoryTrusted r6.concrete r6.history at hr6
  change SigMoveDepartCompatible hψ l6 r6 at hcompat
  have h7 := markedSigMoveDepart_preserves_auditLocalHistoryTrusted
    hψ l6 r6 hl6 hr6 hcompat
  simpa [markedSingleUseControlTail, l6, r6] using h7


/-! ## 3. Current DONE join point -/


/-- The only cross-lineage premise for the current DONE move.  It is the old
SIGMOVE departure join, evaluated at the actual pair after preclear, current
held/captured transfers, the leader wall, and both single-use local controls. -/
def CurrentDoneMoveCompatible (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) : Prop :=
  let p := markedSigMoveLeaderPreclear hψ l r
  let moved := markedDoneTransfers p.1 p.2
  let wall := PPLLWallSweepHistory.markedComparisonLeaderWall
    moved.1 moved.2
  let l6 := markedSingleUseApplyControl hψ wall.1
  let r6 := markedSingleUseApplyControl hψ wall.2
  SigMoveDepartCompatible hψ l6 r6


/-! ## 4. Whole current DONE movement -/


/-- Full marked current DONE movement in the exact physical order. -/
def markedDoneCaptureSigMove (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let p := markedSigMoveLeaderPreclear hψ l r
  let moved := markedDoneTransfers p.1 p.2
  let wall := PPLLWallSweepHistory.markedComparisonLeaderWall
    moved.1 moved.2
  markedSingleUseControlTail hψ wall.1 wall.2


/-- The marked current DONE move erases exactly to
`BirthGenerationDone.doneCaptureSigMove`. -/
theorem erase_markedDoneCaptureSigMove (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedDoneCaptureSigMove hψ l r
    (q.1.concrete, q.2.concrete) =
      doneCaptureSigMove hψ l.concrete r.concrete := by
  let pm := markedSigMoveLeaderPreclear hψ l r
  let p := sigMoveLeaderPreclear hψ l.concrete r.concrete
  have hp := erase_markedSigMoveLeaderPreclear hψ l r
  change (pm.1.concrete, pm.2.concrete) = p at hp
  have hpl := congrArg Prod.fst hp
  have hpr := congrArg Prod.snd hp
  change pm.1.concrete = p.1 at hpl
  change pm.2.concrete = p.2 at hpr


  let mm := markedDoneTransfers pm.1 pm.2
  let m := doneTransfers p.1 p.2
  have hm := erase_markedDoneTransfers pm.1 pm.2
  change (mm.1.concrete, mm.2.concrete) =
    doneTransfers pm.1.concrete pm.2.concrete at hm
  rw [hpl, hpr] at hm
  change (mm.1.concrete, mm.2.concrete) = m at hm
  have hml := congrArg Prod.fst hm
  have hmr := congrArg Prod.snd hm
  change mm.1.concrete = m.1 at hml
  change mm.2.concrete = m.2 at hmr


  let wm := PPLLWallSweepHistory.markedComparisonLeaderWall mm.1 mm.2
  let w := comparisonLeaderWall m.1 m.2
  have hw := PPLLWallSweepHistory.erase_markedComparisonLeaderWall mm.1 mm.2
  change (wm.1.concrete, wm.2.concrete) =
    comparisonLeaderWall mm.1.concrete mm.2.concrete at hw
  rw [hml, hmr] at hw
  change (wm.1.concrete, wm.2.concrete) = w at hw
  have hwl := congrArg Prod.fst hw
  have hwr := congrArg Prod.snd hw
  change wm.1.concrete = w.1 at hwl
  change wm.2.concrete = w.2 at hwr


  let tm := markedSingleUseControlTail hψ wm.1 wm.2
  let t := singleUseControlTail hψ w.1 w.2
  have ht := erase_markedSingleUseControlTail hψ wm.1 wm.2
  change (tm.1.concrete, tm.2.concrete) =
    singleUseControlTail hψ wm.1.concrete wm.2.concrete at ht
  rw [hwl, hwr] at ht
  change (tm.1.concrete, tm.2.concrete) = t at ht


  change (tm.1.concrete, tm.2.concrete) =
    doneCaptureSigMove hψ l.concrete r.concrete
  exact ht.trans (by rfl)


/-- Whole current DONE preservation.  The two leader clear stages need no
compatibility premise; the sole join is `CurrentDoneMoveCompatible`. -/
theorem markedDoneCaptureSigMove_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hcompat : CurrentDoneMoveCompatible hψ l r) :
    let q := markedDoneCaptureSigMove hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  let p := markedSigMoveLeaderPreclear hψ l r
  have hp :=
    markedSigMoveLeaderPreclear_preserves_auditLocalHistoryTrusted
      hψ l r hl hr
  change AuditLocalHistoryTrusted p.1.concrete p.1.history ∧
    AuditLocalHistoryTrusted p.2.concrete p.2.history at hp


  let moved := markedDoneTransfers p.1 p.2
  have hm :=
    markedDoneTransfers_preserves_auditLocalHistoryTrusted_unconditional
      p.1 p.2 hp.1 hp.2
  change AuditLocalHistoryTrusted moved.1.concrete moved.1.history ∧
    AuditLocalHistoryTrusted moved.2.concrete moved.2.history at hm


  let wall := PPLLWallSweepHistory.markedComparisonLeaderWall
    moved.1 moved.2
  have hw := markedComparisonLeaderWall_preserves_auditLocalHistoryTrusted
    moved.1 moved.2 hm.1 hm.2
  change AuditLocalHistoryTrusted wall.1.concrete wall.1.history ∧
    AuditLocalHistoryTrusted wall.2.concrete wall.2.history at hw


  have hcompat' :
      let l6 := markedSingleUseApplyControl hψ wall.1
      let r6 := markedSingleUseApplyControl hψ wall.2
      SigMoveDepartCompatible hψ l6 r6 := by
    simpa [CurrentDoneMoveCompatible, p, moved, wall] using hcompat


  have ht :=
    markedSingleUseControlTail_preserves_auditLocalHistoryTrusted
      hψ wall.1 wall.2 hw.1 hw.2 hcompat'
  simpa [markedDoneCaptureSigMove, p, moved, wall] using ht


end PPLLComparisonHistory


#print axioms PPLLComparisonHistory.captureStep1Preservation_repaired
#print axioms PPLLComparisonHistory.markedHoldDoneStep1_preserves_auditLocalHistoryTrusted_unconditional
#print axioms PPLLComparisonHistory.markedDoneTransfers_preserves_auditLocalHistoryTrusted_unconditional
#print axioms PPLLComparisonHistory.erase_markedSingleUseApplyControl
#print axioms PPLLComparisonHistory.markedSingleUseApplyControl_preserves_auditLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedSingleUseControlTail
#print axioms PPLLComparisonHistory.markedSingleUseControlTail_preserves_auditLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedDoneCaptureSigMove
#print axioms PPLLComparisonHistory.markedDoneCaptureSigMove_preserves_auditLocalHistoryTrusted

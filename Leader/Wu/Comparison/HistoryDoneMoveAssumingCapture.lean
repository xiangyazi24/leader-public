import Leader.Wu.Comparison.HistoryCaptureStepOne
import Leader.Wu.WallSweep.History


set_option autoImplicit false


namespace PPLLComparisonHistory


open PPLL PPLLRepair
open PPLLWallSweepRepair PPLLWallSweepHistory
open BirthGenerationDone


variable {n ψ : Nat}


/-- Temporary interface to the repaired `markedCaptureStep1` preservation
statement.  Current main still has the one elaboration failure in that theorem,
so the current DONE-prefix lift accepts exactly that statement as a premise
rather than depending on its `sorryAx`-carrying declaration. -/
def CaptureStep1Preservation (n ψ : Nat) : Prop :=
  ∀ (l r : MarkedAgentState n ψ),
    AuditLocalHistoryTrusted l.concrete l.history →
    AuditLocalHistoryTrusted r.concrete r.history →
    AuditLocalHistoryTrusted
        (markedCaptureStep1 l r).1.concrete
        (markedCaptureStep1 l r).1.history ∧
      AuditLocalHistoryTrusted
        (markedCaptureStep1 l r).2.concrete
        (markedCaptureStep1 l r).2.history


/-! ## 1. Current leader preclear -/


/-- Marked counterpart of the exact current `sigMoveLeaderPreclear`.
Every physical `clearComparisonSignal` is mirrored by the existing proof-side
`markedClearComparisonSignal`; untouched endpoints retain their histories. -/
def markedSigMoveLeaderPreclear (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let l0 :=
    if l.concrete.leader = true ∨
        incompleteLeftLeaderBoundary hψ l.concrete r.concrete then
      markedClearComparisonSignal l
    else l
  let r0 :=
    if r.concrete.leader = true then markedClearComparisonSignal r else r
  (l0, r0)


/-- The marked preclear erases exactly to the current physical preclear. -/
theorem erase_markedSigMoveLeaderPreclear (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveLeaderPreclear hψ l r
    (q.1.concrete, q.2.concrete) =
      sigMoveLeaderPreclear hψ l.concrete r.concrete := by
  unfold markedSigMoveLeaderPreclear sigMoveLeaderPreclear clearIfLeader
  dsimp only
  repeat (first | rfl | split)


private theorem markedClearComparisonSignal_auditTrusted
    (u : MarkedAgentState n ψ) :
    AuditLocalHistoryTrusted
      (markedClearComparisonSignal u).concrete
      (markedClearComparisonSignal u).history := by
  exact (markedClearComparisonSignal_fullLocalHistoryTrusted u).1


/-- Leader/incomplete-boundary deletion needs no source join: clearing an
endpoint makes all three comparison fields and their marks absent. -/
theorem markedSigMoveLeaderPreclear_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedSigMoveLeaderPreclear hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedSigMoveLeaderPreclear
  dsimp only
  split
  · split
    · exact ⟨markedClearComparisonSignal_auditTrusted l,
        markedClearComparisonSignal_auditTrusted r⟩
    · exact ⟨markedClearComparisonSignal_auditTrusted l, hr⟩
  · split
    · exact ⟨hl, markedClearComparisonSignal_auditTrusted r⟩
    · exact ⟨hl, hr⟩


/-! ## 2. Current held/captured transfers -/


/-- Mark the current Step-1 dispatch: a `.done` left endpoint holds the pair;
all other states execute the current marked capture seam. -/
def markedHoldDoneStep1 (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  if l.concrete.state = .done then (l, r) else markedCaptureStep1 l r


/-- The marked dispatch erases exactly to `BirthGenerationDone.holdDoneStep1`. -/
theorem erase_markedHoldDoneStep1 (l r : MarkedAgentState n ψ) :
    let q := markedHoldDoneStep1 l r
    (q.1.concrete, q.2.concrete) =
      holdDoneStep1 l.concrete r.concrete := by
  unfold markedHoldDoneStep1 holdDoneStep1
  split
  · rfl
  · exact erase_markedCaptureStep1 l r


/-- The held branch is identity; the active branch uses exactly the external
capture-preservation premise described above. -/
theorem markedHoldDoneStep1_preserves_auditLocalHistoryTrusted
    (hCapture : CaptureStep1Preservation n ψ)
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedHoldDoneStep1 l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold CaptureStep1Preservation at hCapture
  unfold markedHoldDoneStep1
  split
  · exact ⟨hl, hr⟩
  · exact hCapture l r hl hr


/-- Current `doneTransfers`: held/captured Step 1 followed by the unchanged
marked Algorithm-10 path2 rows 2--5. -/
def markedDoneTransfers (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q1 := markedHoldDoneStep1 l r
  let q2 := markedSigMoveStep2 q1.1 q1.2
  let q3 := markedSigMoveStep3 q2.1 q2.2
  let q4 := markedSigMoveStep4 q3.1 q3.2
  markedSigMoveStep5 q4.1 q4.2


/-- Exact erasure of the current transfer prefix. -/
theorem erase_markedDoneTransfers (l r : MarkedAgentState n ψ) :
    let q := markedDoneTransfers l r
    (q.1.concrete, q.2.concrete) =
      doneTransfers l.concrete r.concrete := by
  let q1 := markedHoldDoneStep1 l r
  let p1 := holdDoneStep1 l.concrete r.concrete
  have h1 := erase_markedHoldDoneStep1 l r
  change (q1.1.concrete, q1.2.concrete) = p1 at h1
  have h1l := congrArg Prod.fst h1
  have h1r := congrArg Prod.snd h1
  change q1.1.concrete = p1.1 at h1l
  change q1.2.concrete = p1.2 at h1r


  let q2 := markedSigMoveStep2 q1.1 q1.2
  let p2 := sigMoveStep2 p1.1 p1.2
  have h2 := erase_markedSigMoveStep2 q1.1 q1.2
  change (q2.1.concrete, q2.2.concrete) =
    sigMoveStep2 q1.1.concrete q1.2.concrete at h2
  rw [h1l, h1r] at h2
  change (q2.1.concrete, q2.2.concrete) = p2 at h2
  have h2l := congrArg Prod.fst h2
  have h2r := congrArg Prod.snd h2
  change q2.1.concrete = p2.1 at h2l
  change q2.2.concrete = p2.2 at h2r


  let q3 := markedSigMoveStep3 q2.1 q2.2
  let p3 := sigMoveStep3 p2.1 p2.2
  have h3 := erase_markedSigMoveStep3 q2.1 q2.2
  change (q3.1.concrete, q3.2.concrete) =
    sigMoveStep3 q2.1.concrete q2.2.concrete at h3
  rw [h2l, h2r] at h3
  change (q3.1.concrete, q3.2.concrete) = p3 at h3
  have h3l := congrArg Prod.fst h3
  have h3r := congrArg Prod.snd h3
  change q3.1.concrete = p3.1 at h3l
  change q3.2.concrete = p3.2 at h3r


  let q4 := markedSigMoveStep4 q3.1 q3.2
  let p4 := sigMoveStep4 p3.1 p3.2
  have h4 := erase_markedSigMoveStep4 q3.1 q3.2
  change (q4.1.concrete, q4.2.concrete) =
    sigMoveStep4 q3.1.concrete q3.2.concrete at h4
  rw [h3l, h3r] at h4
  change (q4.1.concrete, q4.2.concrete) = p4 at h4
  have h4l := congrArg Prod.fst h4
  have h4r := congrArg Prod.snd h4
  change q4.1.concrete = p4.1 at h4l
  change q4.2.concrete = p4.2 at h4r


  let q5 := markedSigMoveStep5 q4.1 q4.2
  let p5 := sigMoveStep5 p4.1 p4.2
  have h5 := erase_markedSigMoveStep5 q4.1 q4.2
  change (q5.1.concrete, q5.2.concrete) =
    sigMoveStep5 q4.1.concrete q4.2.concrete at h5
  rw [h4l, h4r] at h5
  change (q5.1.concrete, q5.2.concrete) = p5 at h5


  change (q5.1.concrete, q5.2.concrete) =
    doneTransfers l.concrete r.concrete
  exact h5.trans (by rfl)


/-- The current transfer prefix preserves fieldwise source trust.  The only
non-existing imported proof is the one-line-broken capture theorem, represented
by `hCapture`; Steps 2--5 use their already compiled preservation theorems. -/
theorem markedDoneTransfers_preserves_auditLocalHistoryTrusted
    (hCapture : CaptureStep1Preservation n ψ)
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedDoneTransfers l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  let q1 := markedHoldDoneStep1 l r
  have h1 := markedHoldDoneStep1_preserves_auditLocalHistoryTrusted
    hCapture l r hl hr
  change AuditLocalHistoryTrusted q1.1.concrete q1.1.history ∧
    AuditLocalHistoryTrusted q1.2.concrete q1.2.history at h1


  let q2 := markedSigMoveStep2 q1.1 q1.2
  have h2 := markedSigMoveStep2_preserves_auditLocalHistoryTrusted
    q1.1 q1.2 h1.1 h1.2
  change AuditLocalHistoryTrusted q2.1.concrete q2.1.history ∧
    AuditLocalHistoryTrusted q2.2.concrete q2.2.history at h2


  let q3 := markedSigMoveStep3 q2.1 q2.2
  have h3 := markedSigMoveStep3_preserves_auditLocalHistoryTrusted
    q2.1 q2.2 h2.1 h2.2
  change AuditLocalHistoryTrusted q3.1.concrete q3.1.history ∧
    AuditLocalHistoryTrusted q3.2.concrete q3.2.history at h3


  let q4 := markedSigMoveStep4 q3.1 q3.2
  have h4 := markedSigMoveStep4_preserves_auditLocalHistoryTrusted
    q3.1 q3.2 h3.1 h3.2
  change AuditLocalHistoryTrusted q4.1.concrete q4.1.history ∧
    AuditLocalHistoryTrusted q4.2.concrete q4.2.history at h4


  let q5 := markedSigMoveStep5 q4.1 q4.2
  have h5 := markedSigMoveStep5_preserves_auditLocalHistoryTrusted
    q4.1 q4.2 h4.1 h4.2
  change AuditLocalHistoryTrusted q5.1.concrete q5.1.history ∧
    AuditLocalHistoryTrusted q5.2.concrete q5.2.history at h5


  change AuditLocalHistoryTrusted q5.1.concrete q5.1.history ∧
    AuditLocalHistoryTrusted q5.2.concrete q5.2.history
  exact h5


/-! ## Existing wrapper 3: Audit-only adapter -/


/-- `PPLLWallSweepHistory.markedComparisonLeaderWall` already exists on main.
This is only the weaker Audit-level preservation theorem needed by the DONE
move, avoiding an unnecessary `pCarry` premise. -/
theorem markedComparisonLeaderWall_preserves_auditLocalHistoryTrusted
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := PPLLWallSweepHistory.markedComparisonLeaderWall l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold PPLLWallSweepHistory.markedComparisonLeaderWall
  dsimp only
  split
  · constructor
    · exact markedClearComparisonSignal_auditTrusted l
    · split
      · exact markedClearComparisonSignal_auditTrusted r
      · exact hr
  · constructor
    · exact hl
    · split
      · exact markedClearComparisonSignal_auditTrusted r
      · exact hr


end PPLLComparisonHistory


#print axioms PPLLComparisonHistory.erase_markedSigMoveLeaderPreclear
#print axioms PPLLComparisonHistory.markedSigMoveLeaderPreclear_preserves_auditLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedHoldDoneStep1
#print axioms PPLLComparisonHistory.markedHoldDoneStep1_preserves_auditLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedDoneTransfers
#print axioms PPLLComparisonHistory.markedDoneTransfers_preserves_auditLocalHistoryTrusted
#print axioms PPLLComparisonHistory.markedComparisonLeaderWall_preserves_auditLocalHistoryTrusted

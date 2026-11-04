import Leader.Wu.Comparison.AuthorizedRepair
import Leader.Wu.Elimination.MultiLeaderCleanup
import Leader.Wu.Birth.ShortDoneCuts
import Leader.Wu.WallSweep.Repair

set_option autoImplicit false

namespace R2NewEqualPreimage

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLCompleteMultiLeaderCleanup PPLLWallSweepRepair

variable {ψ psi κ τ : Nat}

/-- Scalar frame used instead of equality of a pair-valued observation.
This avoids normalizing whole record updates. -/
private def StatePathFrame (out input : AgentState ψ) : Prop :=
  out.state = input.state ∧ out.path = input.path

private theorem statePathFrame_trans {a b c : AgentState ψ}
    (hab : StatePathFrame a b) (hbc : StatePathFrame b c) :
    StatePathFrame a c :=
  ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

private theorem disappearStartR_left_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    StatePathFrame (disappearStartR hψ l r).1 l := by
  unfold disappearStartR StatePathFrame
  dsimp only
  exact ⟨rfl, rfl⟩

private theorem disappearStartR_right_equal_frame (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hout : (disappearStartR hψ l r).2.state = .equal) :
    StatePathFrame (disappearStartR hψ l r).2 r := by
  unfold disappearStartR at hout ⊢
  dsimp only at hout ⊢
  unfold StatePathFrame
  by_cases h : r.state = .toss ∧ r.label = ⟨0, hψ⟩
  · rw [if_pos h] at hout
    change MainState.toss_done = MainState.equal at hout
    cases hout
  · rw [if_neg h] at hout ⊢
    exact ⟨rfl, rfl⟩

private theorem disappearStartL_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    StatePathFrame (disappearStartL hψ l r).1 l ∧
      StatePathFrame (disappearStartL hψ l r).2 r := by
  unfold disappearStartL
  dsimp only
  unfold StatePathFrame
  by_cases ht : l.state = .toss ∧ l.label = ⟨0, hψ⟩
  · rw [if_pos ht]
    by_cases hp : l.p = true
    · rw [if_pos hp]
      exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · rw [if_neg hp]
      exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · rw [if_neg ht]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

private theorem disappearCarry_left_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    StatePathFrame (disappearCarry hψ l r).1 l := by
  unfold disappearCarry StatePathFrame
  by_cases hc : l.p_carry = true
  · rw [if_pos hc]
    by_cases hp : r.p = true
    · rw [if_pos hp]
      by_cases ht : r.label = ⟨ψ - 1, by omega⟩
      · rw [if_pos ht]
        exact ⟨rfl, rfl⟩
      · rw [if_neg ht]
        exact ⟨rfl, rfl⟩
    · rw [if_neg hp]
      exact ⟨rfl, rfl⟩
  · rw [if_neg hc]
    exact ⟨rfl, rfl⟩

private theorem disappearCarry_right_equal_frame (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hout : (disappearCarry hψ l r).2.state = .equal) :
    StatePathFrame (disappearCarry hψ l r).2 r := by
  unfold disappearCarry at hout ⊢
  unfold StatePathFrame
  by_cases hc : l.p_carry = true
  · by_cases hp : r.p = true
    · by_cases ht : r.label = ⟨ψ - 1, by omega⟩
      · rw [if_pos hc, if_pos hp, if_pos ht] at hout
        change MainState.eliminate_signal = MainState.equal at hout
        cases hout
      · rw [if_pos hc, if_pos hp, if_neg ht] at hout ⊢
        exact ⟨rfl, rfl⟩
    · rw [if_pos hc, if_neg hp] at hout ⊢
      exact ⟨rfl, rfl⟩
  · rw [if_neg hc] at hout ⊢
    exact ⟨rfl, rfl⟩

private theorem disappear_left_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    StatePathFrame (disappear hψ l r).1 l := by
  rw [disappear_eq_staged]
  let q0 := disappearStartR hψ l r
  let q1 := disappearStartL hψ q0.1 q0.2
  change StatePathFrame (disappearCarry hψ q1.1 q1.2).1 l
  have h0 := disappearStartR_left_frame hψ l r
  have h1 := (disappearStartL_frame hψ q0.1 q0.2).1
  have h2 := disappearCarry_left_frame hψ q1.1 q1.2
  exact statePathFrame_trans h2 (statePathFrame_trans h1 h0)

private theorem disappear_right_equal_frame (hψ : ψ > 0)
    (l r : AgentState ψ) (hout : (disappear hψ l r).2.state = .equal) :
    StatePathFrame (disappear hψ l r).2 r := by
  rw [disappear_eq_staged] at hout ⊢
  let q0 := disappearStartR hψ l r
  let q1 := disappearStartL hψ q0.1 q0.2
  change (disappearCarry hψ q1.1 q1.2).2.state = .equal at hout
  change StatePathFrame (disappearCarry hψ q1.1 q1.2).2 r
  have h2 := disappearCarry_right_equal_frame hψ q1.1 q1.2 hout
  have hq1 : q1.2.state = .equal := h2.1.symm.trans hout
  have h1 := (disappearStartL_frame hψ q0.1 q0.2).2
  have hq0 : q0.2.state = .equal := h1.1.symm.trans hq1
  have h0 := disappearStartR_right_equal_frame hψ l r hq0
  exact statePathFrame_trans h2 (statePathFrame_trans h1 h0)

/-- `authorizedReconcile` keeps the raw cores definitionally
(`Leader/Wu/Comparison/AuthorizedRepair.lean:49-55`).  For the label projection,
do not simplify the record update: use
`PPLLWallSweepPreCheckResetContracts.authorizedDisappear_labels_eq`
(`Leader/Wu/WallSweep/PreCheckResetContractsCore.lean:442-446`). -/
theorem authorizedDisappear_equal_preimage (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    let q := authorizedDisappear hψ l r
    (q.1.core.state = .equal →
      l.core.state = .equal ∧ l.core.path = q.1.core.path ∧
        l.core.label = q.1.core.label) ∧
    (q.2.core.state = .equal →
      r.core.state = .equal ∧ r.core.path = q.2.core.path ∧
        r.core.label = q.2.core.label) := by
  dsimp only
  constructor
  · intro hstate
    change (disappear hψ l.core r.core).1.state = .equal at hstate
    have hf := disappear_left_frame hψ l.core r.core
    have hl :=
      PPLLWallSweepPreCheckResetContracts.authorizedDisappear_labels_eq hψ l r
    exact ⟨hf.1.symm.trans hstate, hf.2.symm, hl.1.symm⟩
  · intro hstate
    change (disappear hψ l.core r.core).2.state = .equal at hstate
    have hf := disappear_right_equal_frame hψ l.core r.core hstate
    have hl :=
      PPLLWallSweepPreCheckResetContracts.authorizedDisappear_labels_eq hψ l r
    exact ⟨hf.1.symm.trans hstate, hf.2.symm, hl.2.symm⟩

/-- Named obligation only.  The public label projection is
`PPLLCompleteMultiLeaderCleanup.compareActionOne_labels`
(`Leader/Wu/Elimination/MultiLeaderCleanupRepairTail.lean:410-432`), but the needed path
projection is still private upstream:
`BirthMismatchDisposalProducer.compareActionOne_anchor`
(`Leader/Wu/Birth/MismatchDisposalProducer.lean:283-302`).  Its responder helper
is `PPLLRepair.compareBitUpdateRActionOne`
(`Leader/Wu/Protocol/Repairs.lean:1085-1102`). -/
def compareActionOne_equal_preimage (hψ : psi > 0)
    (l r : AuthorizedAgentState psi) : Prop :=
  let q := authorizedCompareSigActionOne hψ l r
  (q.1.core.state = .equal →
    l.core.state = .equal ∧ l.core.path = q.1.core.path ∧
      l.core.label = q.1.core.label) ∧
  (q.2.core.state = .equal →
    r.core.state = .equal ∧ r.core.path = q.2.core.path ∧
      r.core.label = q.2.core.label)

/-- `resetKillComparison` is the only SUPPRESS substage that can change
`state` or `path`.  Its destructive branch is exactly `clearComparisonSignal`,
which sets `state := .none` and `path := .bot`
(`Leader/Wu/WallSweep/Repair.lean:25-33,58-59`). -/
private theorem resetKill_equal_frame (u : AgentState psi)
    (hout : (resetKillComparison u).state = .equal) :
    StatePathFrame (resetKillComparison u) u := by
  by_cases hreset : u.reset_cmd = true
  · have hk : resetKillComparison u = clearComparisonSignal u := by
      unfold resetKillComparison
      rw [if_pos hreset]
    rw [hk] at hout
    change MainState.none = MainState.equal at hout
    cases hout
  · have hk : resetKillComparison u = u := by
      unfold resetKillComparison
      rw [if_neg hreset]
    rw [hk]
    exact ⟨rfl, rfl⟩

private theorem suppressStart_frame (l r : AgentState psi) :
    StatePathFrame (suppressSigStart l r).1 l ∧
      StatePathFrame (suppressSigStart l r).2 r := by
  unfold suppressSigStart StatePathFrame
  by_cases h : l.leader = true
  · rw [if_pos h]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · rw [if_neg h]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

private theorem suppressMove_frame (l r : AgentState psi) :
    StatePathFrame (suppressSigMoveReset l r).1 l ∧
      StatePathFrame (suppressSigMoveReset l r).2 r := by
  unfold suppressSigMoveReset StatePathFrame
  by_cases h : l.reset_cmd = true
  · rw [if_pos h]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · rw [if_neg h]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

private theorem suppressTerminal_frame (hψ : psi > 0)
    (l r : AgentState psi) :
    StatePathFrame (suppressSigTerminal hψ l r).1 l ∧
      StatePathFrame (suppressSigTerminal hψ l r).2 r := by
  unfold suppressSigTerminal StatePathFrame
  by_cases h : r.label = ⟨psi - 1, by omega⟩ ∧ r.reset_cmd = true
  · rw [if_pos h]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · rw [if_neg h]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

private theorem suppressEcho_frame (l r : AgentState psi) :
    StatePathFrame (suppressSigEcho l r).1 l ∧
      StatePathFrame (suppressSigEcho l r).2 r := by
  unfold suppressSigEcho StatePathFrame
  by_cases he : r.echo = true
  · rw [if_pos he]
    by_cases hr : r.reset_cmd = true
    · rw [if_pos hr]
      exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · rw [if_neg hr]
      exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · rw [if_neg he]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

private theorem suppressFinish_frame (l r : AgentState psi) :
    StatePathFrame (suppressSigFinish l r).1 l ∧
      StatePathFrame (suppressSigFinish l r).2 r := by
  unfold suppressSigFinish StatePathFrame
  by_cases h : l.leader = true
  · rw [if_pos h]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · rw [if_neg h]
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The repaired SUPPRESS composition is the seven named steps at
`Leader/Wu/WallSweep/Repair.lean:261-269`; the five ordinary Algorithm-14 steps
are `Leader/Wu/Protocol/Algorithm.lean:535-562`. -/
private theorem suppress_left_equal_frame (hψ : psi > 0)
    (l r : AgentState psi)
    (hout : (suppressSigResetKill hψ l r).1.state = .equal) :
    StatePathFrame (suppressSigResetKill hψ l r).1 l := by
  let q0 := suppressSigStart l r
  let q0k := (resetKillComparison q0.1, resetKillComparison q0.2)
  let q1 := suppressSigMoveReset q0k.1 q0k.2
  let q1k := (resetKillComparison q1.1, resetKillComparison q1.2)
  let q2 := suppressSigTerminal hψ q1k.1 q1k.2
  let q3 := suppressSigEcho q2.1 q2.2
  have htail : StatePathFrame (suppressSigResetKill hψ l r).1 q1k.1 := by
    change StatePathFrame (suppressSigFinish q3.1 q3.2).1 q1k.1
    exact statePathFrame_trans (suppressFinish_frame q3.1 q3.2).1
      (statePathFrame_trans (suppressEcho_frame q2.1 q2.2).1
        (suppressTerminal_frame hψ q1k.1 q1k.2).1)
  have hq1k : q1k.1.state = .equal := htail.1.symm.trans hout
  change (resetKillComparison q1.1).state = .equal at hq1k
  have hk1 := resetKill_equal_frame q1.1 hq1k
  have hq1 : q1.1.state = .equal := hk1.1.symm.trans hq1k
  have hm := (suppressMove_frame q0k.1 q0k.2).1
  have hq0k : q0k.1.state = .equal := hm.1.symm.trans hq1
  change (resetKillComparison q0.1).state = .equal at hq0k
  have hk0 := resetKill_equal_frame q0.1 hq0k
  have hs := (suppressStart_frame l r).1
  exact statePathFrame_trans htail
    (statePathFrame_trans hk1
      (statePathFrame_trans hm (statePathFrame_trans hk0 hs)))

private theorem suppress_right_equal_frame (hψ : psi > 0)
    (l r : AgentState psi)
    (hout : (suppressSigResetKill hψ l r).2.state = .equal) :
    StatePathFrame (suppressSigResetKill hψ l r).2 r := by
  let q0 := suppressSigStart l r
  let q0k := (resetKillComparison q0.1, resetKillComparison q0.2)
  let q1 := suppressSigMoveReset q0k.1 q0k.2
  let q1k := (resetKillComparison q1.1, resetKillComparison q1.2)
  let q2 := suppressSigTerminal hψ q1k.1 q1k.2
  let q3 := suppressSigEcho q2.1 q2.2
  have htail : StatePathFrame (suppressSigResetKill hψ l r).2 q1k.2 := by
    change StatePathFrame (suppressSigFinish q3.1 q3.2).2 q1k.2
    exact statePathFrame_trans (suppressFinish_frame q3.1 q3.2).2
      (statePathFrame_trans (suppressEcho_frame q2.1 q2.2).2
        (suppressTerminal_frame hψ q1k.1 q1k.2).2)
  have hq1k : q1k.2.state = .equal := htail.1.symm.trans hout
  change (resetKillComparison q1.2).state = .equal at hq1k
  have hk1 := resetKill_equal_frame q1.2 hq1k
  have hq1 : q1.2.state = .equal := hk1.1.symm.trans hq1k
  have hm := (suppressMove_frame q0k.1 q0k.2).2
  have hq0k : q0k.2.state = .equal := hm.1.symm.trans hq1
  change (resetKillComparison q0.2).state = .equal at hq0k
  have hk0 := resetKill_equal_frame q0.2 hq0k
  have hs := (suppressStart_frame l r).2
  exact statePathFrame_trans htail
    (statePathFrame_trans hk1
      (statePathFrame_trans hm (statePathFrame_trans hk0 hs)))

/-- For the label component, use the public authorized projection rather than
reducing the repaired SUPPRESS tree:
`PPLLWallSweepNormalResetContract.authorizedSuppressSigResetKill_peaceViewPair`
(`Leader/Wu/WallSweep/NormalResetContract.lean:599-604`). -/
theorem suppress_equal_preimage (hψ : psi > 0)
    (l r : AuthorizedAgentState psi) :
    let q := authorizedReconcile (suppressSigResetKill hψ) l r
    (q.1.core.state = .equal →
      l.core.state = .equal ∧
      (q.1.core.path = l.core.path ∨ q.1.core.path = .bot) ∧
      q.1.core.label = l.core.label) ∧
    (q.2.core.state = .equal →
      r.core.state = .equal ∧
      (q.2.core.path = r.core.path ∨ q.2.core.path = .bot) ∧
      q.2.core.label = r.core.label) := by
  dsimp only
  have hpeace :=
    PPLLWallSweepNormalResetContract.authorizedSuppressSigResetKill_peaceViewPair
      hψ l r
  have hlabelL := congrArg
    (fun p : PPLLNoCheckBirthConditionTwoPhysical.PeaceView psi ×
        PPLLNoCheckBirthConditionTwoPhysical.PeaceView psi => p.1.label) hpeace
  have hlabelR := congrArg
    (fun p : PPLLNoCheckBirthConditionTwoPhysical.PeaceView psi ×
        PPLLNoCheckBirthConditionTwoPhysical.PeaceView psi => p.2.label) hpeace
  change (authorizedReconcile (suppressSigResetKill hψ) l r).1.core.label =
    l.core.label at hlabelL
  change (authorizedReconcile (suppressSigResetKill hψ) l r).2.core.label =
    r.core.label at hlabelR
  constructor
  · intro hstate
    change (suppressSigResetKill hψ l.core r.core).1.state = .equal at hstate
    have hf := suppress_left_equal_frame hψ l.core r.core hstate
    exact ⟨hf.1.symm.trans hstate, Or.inl hf.2, hlabelL⟩
  · intro hstate
    change (suppressSigResetKill hψ l.core r.core).2.state = .equal at hstate
    have hf := suppress_right_equal_frame hψ l.core r.core hstate
    exact ⟨hf.1.symm.trans hstate, Or.inl hf.2, hlabelR⟩

end R2NewEqualPreimage

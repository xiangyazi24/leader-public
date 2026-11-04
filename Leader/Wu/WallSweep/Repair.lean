import Leader.Wu.Protocol.CombinedLocalRepair
import Leader.Wu.WriteSeq.PersistenceRepair

/-!
# Source-backed reset, leader, and probe walls

Wu's positive convergence argument uses three deletion rules stated in prose
but absent from Algorithms 2, 10--11, and 14.  This repair-lane module adds the
smallest direct assignments for the unambiguous reset/probe cases and an
explicit comparison-signal wall at a leader boundary, then composes them once
in Algorithm-1 order.  The literal `Leader.Wu.Protocol.Algorithm` source lane is unchanged.
-/

namespace PPLLWallSweepRepair

open PPLL PPLLRepair PPLLDomain PPLLCombinedLocalRepair
  PPLLWriteSeqPersistenceRepair

/-! ## Comparison-signal erasure -/

/-- Delete the physical fields belonging to one comparison carrier, including
its cleanup connectors and lottery carry, while retaining leader, label,
barrier, reset, bullet, and overwriting-signal fields.  This is the raw-state
counterpart of the existing finite `clearComparisonCarrier`. -/
def clearComparisonSignal (u : AgentState ψ) : AgentState ψ :=
  { u with
    state := MainState.none
    path := PathInfo.bot
    path2 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false }

/-- No physical comparison carrier or cleanup residue remains at an agent. -/
def ComparisonNeutral (u : AgentState ψ) : Prop :=
  u.state = .none ∧ u.path = .bot ∧ u.path2 = none ∧
    u.path4 = none ∧ u.path5 = none ∧ u.p = false ∧
    u.p_carry = false

theorem clearComparisonSignal_neutral (u : AgentState ψ) :
    ComparisonNeutral (clearComparisonSignal u) := by
  simp [ComparisonNeutral, clearComparisonSignal]

/-- Comparison erasure only removes constrained payloads and therefore
preserves the declared numeric domain. -/
theorem clearComparisonSignal_inProtocolDomain
    (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (clearComparisonSignal u).inProtocolDomain κ := by
  change u.count ≤ κ ∧ (PayloadView.ofState u).Valid at hu
  change (clearComparisonSignal u).count ≤ κ ∧
    (PayloadView.ofState (clearComparisonSignal u)).Valid
  rcases hu with ⟨hcount, _, _, hpath3, _, _⟩
  refine ⟨hcount, ?_⟩
  simpa [clearComparisonSignal, PayloadView.ofState, PayloadView.Valid,
    PayloadView.PathValid, PayloadView.Path2Valid,
    PayloadView.CleanPathValid] using hpath3

/-- A reset command eliminates the comparison signal at its current host. -/
def resetKillComparison (u : AgentState ψ) : AgentState ψ :=
  if u.reset_cmd then clearComparisonSignal u else u

theorem resetKillComparison_inProtocolDomain
    (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (resetKillComparison u).inProtocolDomain κ := by
  unfold resetKillComparison
  split
  · exact clearComparisonSignal_inProtocolDomain u hu
  · exact hu

/-- A leader is a comparison-signal wall.  A signal resident at a leader is
deleted; when the responder is the leader, the initiator is the endpoint at
the incoming left boundary and is deleted as well. -/
def comparisonLeaderWall (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := if l.leader ∨ r.leader then clearComparisonSignal l else l
  let r := if r.leader then clearComparisonSignal r else r
  (l, r)

theorem comparisonLeaderWall_inProtocolDomain
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := comparisonLeaderWall l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  unfold comparisonLeaderWall
  dsimp only
  split
  · constructor
    · exact clearComparisonSignal_inProtocolDomain l hl
    · split
      · exact clearComparisonSignal_inProtocolDomain r hr
      · exact hr
  · constructor
    · exact hl
    · split
      · exact clearComparisonSignal_inProtocolDomain r hr
      · exact hr

/-! ## Probe wall from the printed P'_psi prose -/

/-- Algorithm 2 with a source-prose probe wall applied before the literal
stage. A leader drops its resident probe, and a probe immediately to its right
is consumed instead of entering that leader. Follower/follower behavior,
including barrier-return birth, is unchanged. -/
def pPsiLeaderProbeWall (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true then
    { r with probe := false }
  else r
  pPsi hψ l0 r0

/-- Separately named reset-aware extension of the probe wall.  A reset source
clears the responder probe before literal P-prime, preventing a remote
barrier/probe birth on a scheduled cleanup edge.  This is a repair-lane
building block; the current complete transition is not silently changed. -/
def pPsiLeaderResetProbeWall (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true ∨
      l.reset_cmd = true then
    { r with probe := false }
  else r
  pPsi hψ l0 r0

/-- Reset-free edges are definitionally the established leader/probe wall. -/
theorem pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_no_reset
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlReset : l.reset_cmd = false) :
    pPsiLeaderResetProbeWall hψ l r =
      pPsiLeaderProbeWall hψ l r := by
  simp [pPsiLeaderResetProbeWall, pPsiLeaderProbeWall, hlReset]

/-- On an edge entering an existing leader, the older probe wall already
clears the responder probe.  The reset-source clause is therefore redundant,
so the reset-aware and rooted raw P-prime stages agree exactly. -/
theorem pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_right_leader
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hrLeader : r.leader = true) :
    pPsiLeaderResetProbeWall hψ l r =
      pPsiLeaderProbeWall hψ l r := by
  simp [pPsiLeaderResetProbeWall, pPsiLeaderProbeWall, hrLeader]

/-- On an edge initiated by an existing leader, the older probe wall already
clears the responder probe.  The reset-source clause is again redundant,
independently of the leader's current reset bit. -/
theorem pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_left_leader
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlLeader : l.leader = true) :
    pPsiLeaderResetProbeWall hψ l r =
      pPsiLeaderProbeWall hψ l r := by
  simp [pPsiLeaderResetProbeWall, pPsiLeaderProbeWall, hlLeader]

/-- A leader or reset source normalizes a follower responder before any
barrier-return birth can occur.  The responder leaves probe-free at the exact
successor label, while the initiator leader and label fields are framed. -/
theorem pPsiLeaderResetProbeWall_source_follower_normalizes
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hsource : l.leader = true ∨ l.reset_cmd = true)
    (hrFollower : r.leader = false) :
    let q := pPsiLeaderResetProbeWall hψ l r
    q.1.leader = l.leader ∧
      q.2.leader = false ∧
      q.1.label = l.label ∧
      q.2.label =
        ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ ∧
      q.2.probe = false := by
  rcases hsource with hlLeader | hlReset
  · simp [pPsiLeaderResetProbeWall, pPsi, hlLeader, hrFollower]
  · by_cases hlLeader : l.leader = true
    · simp [pPsiLeaderResetProbeWall, pPsi, hlLeader, hrFollower]
    · have hlFollower : l.leader = false := by
        cases h : l.leader
        · rfl
        · exact (hlLeader h).elim
      simp [pPsiLeaderResetProbeWall, pPsi, hlFollower, hlReset,
        hrFollower]

/-- With no existing leader, the probe wall is exactly literal Algorithm 2. -/
theorem pPsiLeaderProbeWall_eq_pPsi_of_no_leaders (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.leader = false)
    (hr : r.leader = false) :
    pPsiLeaderProbeWall hψ l r = pPsi hψ l r := by
  simp [pPsiLeaderProbeWall, hl, hr]

/-- On a non-barrier edge, the left leader consumes the incoming probe and is
not turned into a probe carrier. -/
theorem pPsiLeaderProbeWall_consumes_at_leader (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hleader : l.leader = true) :
    let q := pPsiLeaderProbeWall hψ l r
    q.1.probe = false ∧ q.2.probe = false := by
  simp [pPsiLeaderProbeWall, pPsi, hleader]

/-- Without a leader, the repaired non-barrier branch is the literal probe
movement. -/
theorem pPsiLeaderProbeWall_eq_pPsi_of_nonbarrier_follower (hψ : ψ > 0)
    (l r : AgentState ψ)
    (_hnonbarrier : r.label =
      ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hl : l.leader = false) (hr : r.leader = false) :
    pPsiLeaderProbeWall hψ l r = pPsi hψ l r := by
  exact pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hψ l r hl hr

/-- The repair leaves the follower/follower barrier-return birth mechanism
live. -/
theorem pPsiLeaderProbeWall_preserves_barrier_birth (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.leader = false)
    (hr : r.leader = false) (hprobe : r.probe = true)
    (hbarrier : isBarrier hψ l r) :
    (pPsiLeaderProbeWall hψ l r).2.leader = true := by
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hψ l r hl hr]
  unfold isBarrier at hbarrier
  simp [pPsi, hbarrier, hprobe]

theorem pPsiLeaderProbeWall_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlDom : l.inProtocolDomain κ) (hrDom : r.inProtocolDomain κ) :
    let q := pPsiLeaderProbeWall hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true then
    { r with probe := false }
  else r
  have hl0 : l0.inProtocolDomain κ := by
    unfold l0
    split <;> simpa [AgentState.inProtocolDomain] using hlDom
  have hr0 : r0.inProtocolDomain κ := by
    unfold r0
    split <;> simpa [AgentState.inProtocolDomain] using hrDom
  change let q := pPsi hψ l0 r0
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
  exact pPsi_inProtocolDomain hψ l0 r0 hl0 hr0

/-- The reset-aware probe wall uses only existing Boolean assignments and the
literal P-prime label update, so it preserves the same finite domain. -/
theorem pPsiLeaderResetProbeWall_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlDom : l.inProtocolDomain κ) (hrDom : r.inProtocolDomain κ) :
    let q := pPsiLeaderResetProbeWall hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true ∨
      l.reset_cmd = true then
    { r with probe := false }
  else r
  have hl0 : l0.inProtocolDomain κ := by
    unfold l0
    split <;> simpa [AgentState.inProtocolDomain] using hlDom
  have hr0 : r0.inProtocolDomain κ := by
    unfold r0
    split <;> simpa [AgentState.inProtocolDomain] using hrDom
  change let q := pPsi hψ l0 r0
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
  exact pPsi_inProtocolDomain hψ l0 r0 hl0 hr0

/-! ## Reset-command suppression with physical deletion -/

/-- Algorithm 14 with comparison erasure immediately after reset generation
and again after reset movement.  Token/echo/count order is otherwise the
literal staged Algorithm 14 order. -/
def suppressSigResetKill (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q0 := suppressSigStart l r
  let q0 := (resetKillComparison q0.1, resetKillComparison q0.2)
  let q1 := suppressSigMoveReset q0.1 q0.2
  let q1 := (resetKillComparison q1.1, resetKillComparison q1.2)
  let q2 := suppressSigTerminal hψ q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  suppressSigFinish q3.1 q3.2

/-- Any endpoint carrying reset is comparison-neutral after the deletion
primitive, with the reset token itself retained for movement/cancellation. -/
theorem resetKillComparison_exact (u : AgentState ψ)
    (hreset : u.reset_cmd = true) :
    let v := resetKillComparison u
    v.state = .none ∧ v.path = .bot ∧ v.path2 = none ∧
      v.path4 = none ∧ v.path5 = none ∧ v.p = false ∧
      v.p_carry = false ∧ v.reset_cmd = true := by
  simp [resetKillComparison, hreset, clearComparisonSignal]

/-- A moving reset command clears the comparison carrier on the responder in
the same repaired SUPPRESS_SIG call. -/
theorem suppressSigResetKill_moving_command_clears_responder
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlreset : l.reset_cmd = true) (hlleader : l.leader = false) :
    let q := suppressSigResetKill hψ l r
    q.2.state = .none ∧ q.2.path = .bot ∧ q.2.path2 = none ∧
      q.2.path4 = none ∧ q.2.path5 = none ∧
      q.2.p = false ∧ q.2.p_carry = false := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, hlreset, hlleader,
    suppressSigTerminal, suppressSigEcho, suppressSigFinish]

/-- Exact reset-sweep handoff.  With no pre-existing responder echo to cancel
the token, one interaction clears both endpoints and moves reset clockwise. -/
theorem suppressSigResetKill_handoff (hψ : ψ > 0)
    (l r : AgentState ψ) (hlreset : l.reset_cmd = true)
    (hrEcho : r.echo = false) :
    let q := suppressSigResetKill hψ l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 ∧
      q.1.reset_cmd = false ∧ q.2.reset_cmd = true := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, ComparisonNeutral,
    suppressSigTerminal, suppressSigEcho, suppressSigFinish,
    hlreset, hrEcho]

private theorem domain_of_count_payload_eq_wall {ψ κ : Nat}
    (input output : AgentState ψ) (hin : input.inProtocolDomain κ)
    (hcount : output.count = input.count)
    (hpayload : PayloadView.ofState output = PayloadView.ofState input) :
    output.inProtocolDomain κ := by
  change input.count ≤ κ ∧ (PayloadView.ofState input).Valid at hin
  change output.count ≤ κ ∧ (PayloadView.ofState output).Valid
  exact ⟨hcount ▸ hin.1, hpayload ▸ hin.2⟩

private theorem suppressSigStart_wall_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := suppressSigStart l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := suppressSigStart l r
  have hframe :
      (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
    simp only [q, suppressSigStart]
    repeat (first | constructor | rfl | split)
  exact ⟨domain_of_count_payload_eq_wall l q.1 hl hframe.1.1 hframe.1.2,
    domain_of_count_payload_eq_wall r q.2 hr hframe.2.1 hframe.2.2⟩

private theorem suppressSigMoveReset_wall_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := suppressSigMoveReset l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := suppressSigMoveReset l r
  have hframe :
      (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
    simp only [q, suppressSigMoveReset]
    repeat (first | constructor | rfl | split)
  exact ⟨domain_of_count_payload_eq_wall l q.1 hl hframe.1.1 hframe.1.2,
    domain_of_count_payload_eq_wall r q.2 hr hframe.2.1 hframe.2.2⟩

private theorem suppressSigTerminal_wall_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := suppressSigTerminal hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  unfold suppressSigTerminal
  dsimp only
  split
  · constructor
    · simpa [AgentState.inProtocolDomain] using hl
    · change (0 : Nat) ≤ κ ∧ (PayloadView.ofState r).Valid
      change r.count ≤ κ ∧ (PayloadView.ofState r).Valid at hr
      exact ⟨Nat.zero_le _, hr.2⟩
  · exact ⟨hl, hr⟩

private theorem suppressSigEcho_wall_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := suppressSigEcho l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := suppressSigEcho l r
  have hframe :
      (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
    simp only [q, suppressSigEcho]
    repeat (first | constructor | rfl | split)
  exact ⟨domain_of_count_payload_eq_wall l q.1 hl hframe.1.1 hframe.1.2,
    domain_of_count_payload_eq_wall r q.2 hr hframe.2.1 hframe.2.2⟩

private theorem suppressSigFinish_wall_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := suppressSigFinish l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := suppressSigFinish l r
  have hframe :
      (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
    simp only [q, suppressSigFinish]
    repeat (first | constructor | rfl | split)
  exact ⟨domain_of_count_payload_eq_wall l q.1 hl hframe.1.1 hframe.1.2,
    domain_of_count_payload_eq_wall r q.2 hr hframe.2.1 hframe.2.2⟩

theorem suppressSigResetKill_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := suppressSigResetKill hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := suppressSigStart l r
  have h0 := suppressSigStart_wall_inProtocolDomain l r hl hr
  let q0k := (resetKillComparison q0.1, resetKillComparison q0.2)
  have h0k : q0k.1.inProtocolDomain κ ∧ q0k.2.inProtocolDomain κ :=
    ⟨resetKillComparison_inProtocolDomain q0.1 h0.1,
      resetKillComparison_inProtocolDomain q0.2 h0.2⟩
  let q1 := suppressSigMoveReset q0k.1 q0k.2
  have h1 := suppressSigMoveReset_wall_inProtocolDomain q0k.1 q0k.2
    h0k.1 h0k.2
  let q1k := (resetKillComparison q1.1, resetKillComparison q1.2)
  have h1k : q1k.1.inProtocolDomain κ ∧ q1k.2.inProtocolDomain κ :=
    ⟨resetKillComparison_inProtocolDomain q1.1 h1.1,
      resetKillComparison_inProtocolDomain q1.2 h1.2⟩
  let q2 := suppressSigTerminal hψ q1k.1 q1k.2
  have h2 := suppressSigTerminal_wall_inProtocolDomain hψ q1k.1 q1k.2
    h1k.1 h1k.2
  let q3 := suppressSigEcho q2.1 q2.2
  have h3 := suppressSigEcho_wall_inProtocolDomain q2.1 q2.2 h2.1 h2.2
  have h4 := suppressSigFinish_wall_inProtocolDomain q3.1 q3.2 h3.1 h3.2
  simpa [suppressSigResetKill, q0, q0k, q1, q1k, q2, q3] using h4

/-! ## One raw corrected Algorithm-1 composition -/

/-- Pair-local observable boundary of the incomplete stable group immediately
left of a leader: the responder is the leader and the incoming edge is a
barrier. -/
def incompleteLeftLeaderBoundary (hψ : ψ > 0)
    (l r : AgentState ψ) : Prop :=
  r.leader = true ∧ isBarrier hψ l r

instance incompleteLeftLeaderBoundary_decidable (hψ : ψ > 0)
    (l r : AgentState ψ) :
    Decidable (incompleteLeftLeaderBoundary hψ l r) := by
  unfold incompleteLeftLeaderBoundary isBarrier
  infer_instance

/-- Clear comparison material already resident at a leader. -/
def clearIfLeader (u : AgentState ψ) : AgentState ψ :=
  if u.leader = true then clearComparisonSignal u else u

/-- The five physical carrier-transfer sub-stages of Algorithm 10, before an
arriving `path2` control is interpreted. -/
def sigMoveTransfers (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q0 := sigMoveStep1 l r
  let q1 := sigMoveStep2 q0.1 q0.2
  let q2 := sigMoveStep3 q1.1 q1.2
  let q3 := sigMoveStep4 q2.1 q2.2
  sigMoveStep5 q3.1 q3.2

/-- The control and departure tail of literal Algorithm 10. -/
def sigMoveControlTail (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := sigMoveApplyControl hψ l
  let r := sigMoveApplyControl hψ r
  let l := if r.state = .depart then
    if l.label.val < ψ - 1 ∧ l.state = .CHECK_ready then
      { l with state := .depart }
    else l
  else l
  (l, r)

/-- Delete resident leader/incomplete-left comparison material before any
Algorithm-10 carrier transfer. -/
def sigMoveLeaderPreclear (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l0 := if l.leader = true ∨ incompleteLeftLeaderBoundary hψ l r then
    clearComparisonSignal l
  else l
  let r0 := clearIfLeader r
  (l0, r0)

/-- Exact post-transfer boundary: incoming comparison material is walled
before either `path2` control or departure propagation can execute. -/
def sigMoveLeaderBeforeControl (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q0 := sigMoveLeaderPreclear hψ l r
  let moved := sigMoveTransfers q0.1 q0.2
  comparisonLeaderWall moved.1 moved.2

/-- Algorithms 10--11 boundary with the prose leader wall after carrier
movement but before an arriving control is interpreted and before CHECK. -/
def sigMoveLeaderWall (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let walled := sigMoveLeaderBeforeControl hψ l r
  sigMoveControlTail hψ walled.1 walled.2

/-- The incomplete group immediately left of a leader is neutral before
Algorithm-10 transport, so resident material cannot escape the wall. -/
theorem sigMoveLeaderPreclear_incomplete_left (hψ : ψ > 0)
    (l r : AgentState ψ) (hwall : incompleteLeftLeaderBoundary hψ l r) :
    ComparisonNeutral (sigMoveLeaderPreclear hψ l r).1 := by
  simp [sigMoveLeaderPreclear, hwall, clearComparisonSignal_neutral]

/-- A resident carrier at the right leader is neutral before transport. -/
theorem sigMoveLeaderPreclear_right_leader (hψ : ψ > 0)
    (l r : AgentState ψ) (hr : r.leader = true) :
    ComparisonNeutral (sigMoveLeaderPreclear hψ l r).2 := by
  simp [sigMoveLeaderPreclear, clearIfLeader, hr,
    clearComparisonSignal_neutral]

private theorem sigMoveApplyControl_leader_wall (hψ : ψ > 0)
    (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).leader = u.leader := by
  unfold sigMoveApplyControl
  try dsimp only []
  repeat (first | constructor | rfl | split)

private theorem sigMoveControlTail_leaders_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := sigMoveControlTail hψ l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader := by
  let l0 := sigMoveApplyControl hψ l
  let r0 := sigMoveApplyControl hψ r
  let l1 := if r0.state = .depart then
    if l0.label.val < ψ - 1 ∧ l0.state = .CHECK_ready then
      { l0 with state := .depart }
    else l0
  else l0
  have hl0 : l0.leader = l.leader := sigMoveApplyControl_leader_wall hψ l
  have hr0 : r0.leader = r.leader := sigMoveApplyControl_leader_wall hψ r
  have hl1 : l1.leader = l0.leader := by
    dsimp only [l1]
    split
    · split <;> rfl
    · rfl
  change l1.leader = l.leader ∧ r0.leader = r.leader
  exact ⟨hl1.trans hl0, hr0⟩

private theorem sigMoveTransfers_leaders_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := sigMoveTransfers l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader := by
  let moved := sigMoveTransfers l r
  let out := sigMoveControlTail hψ moved.1 moved.2
  have hfull := PPLLVerify.sigMove_leaders_eq (hψ := hψ) l r
  change out.1.leader = l.leader ∧ out.2.leader = r.leader at hfull
  have htail := sigMoveControlTail_leaders_eq hψ moved.1 moved.2
  exact ⟨htail.1.symm.trans hfull.1, htail.2.symm.trans hfull.2⟩

private theorem sigMoveApplyControl_label_wall (hψ : ψ > 0)
    (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).label = u.label :=
  PPLLVerify.sigMoveApplyControl_label_eq hψ u

private theorem sigMoveApplyControl_shield_wall (hψ : ψ > 0)
    (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).shield = u.shield :=
  PPLLVerify.sigMoveApplyControl_shield_eq hψ u

private theorem sigMoveControlTail_labels_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := sigMoveControlTail hψ l r
    q.1.label = l.label ∧ q.2.label = r.label := by
  let l0 := sigMoveApplyControl hψ l
  let r0 := sigMoveApplyControl hψ r
  let l1 := if r0.state = .depart then
    if l0.label.val < ψ - 1 ∧ l0.state = .CHECK_ready then
      { l0 with state := .depart }
    else l0
  else l0
  have hl1 : l1.label = l0.label := by
    unfold l1
    repeat (first | rfl | split)
  exact ⟨hl1.trans (sigMoveApplyControl_label_wall hψ l),
    sigMoveApplyControl_label_wall hψ r⟩

private theorem sigMoveControlTail_left_shield_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sigMoveControlTail hψ l r).1.shield = l.shield := by
  let l0 := sigMoveApplyControl hψ l
  let r0 := sigMoveApplyControl hψ r
  let l1 := if r0.state = .depart then
    if l0.label.val < ψ - 1 ∧ l0.state = .CHECK_ready then
      { l0 with state := .depart }
    else l0
  else l0
  have hl1 : l1.shield = l0.shield := by
    unfold l1
    repeat (first | rfl | split)
  exact hl1.trans (sigMoveApplyControl_shield_wall hψ l)

private theorem sigMoveTransfers_labels_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := sigMoveTransfers l r
    q.1.label = l.label ∧ q.2.label = r.label := by
  let moved := sigMoveTransfers l r
  have hfull := PPLLVerify.sigMove_labels_eq (hψ := hψ) l r
  have htail := sigMoveControlTail_labels_eq hψ moved.1 moved.2
  exact ⟨htail.1.symm.trans hfull.1, htail.2.symm.trans hfull.2⟩

private theorem sigMoveTransfers_left_shield_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sigMoveTransfers l r).1.shield = l.shield := by
  let moved := sigMoveTransfers l r
  have hfull := (PPLLVerify.sigMove_kill_fields_eq
    (hψ := hψ) l r).1
  have htail := sigMoveControlTail_left_shield_eq hψ moved.1 moved.2
  exact htail.symm.trans hfull

/-- The wall-aware SIGMOVE changes comparison carriers only; both leader bits
are framed exactly. -/
theorem sigMoveLeaderWall_leaders_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := sigMoveLeaderWall hψ l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader := by
  let q0 := sigMoveLeaderPreclear hψ l r
  let moved := sigMoveTransfers q0.1 q0.2
  let walled := comparisonLeaderWall moved.1 moved.2
  have h0 : q0.1.leader = l.leader ∧ q0.2.leader = r.leader := by
    simp [q0, sigMoveLeaderPreclear, clearIfLeader,
      clearComparisonSignal]
  have hm := sigMoveTransfers_leaders_eq hψ q0.1 q0.2
  have hw : walled.1.leader = moved.1.leader ∧
      walled.2.leader = moved.2.leader := by
    simp [walled, comparisonLeaderWall, clearComparisonSignal]
  have ht := sigMoveControlTail_leaders_eq hψ walled.1 walled.2
  exact ⟨ht.1.trans (hw.1.trans (hm.1.trans h0.1)),
    ht.2.trans (hw.2.trans (hm.2.trans h0.2))⟩

/-- The wall-aware SIGMOVE frames both labels. -/
theorem sigMoveLeaderWall_labels_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := sigMoveLeaderWall hψ l r
    q.1.label = l.label ∧ q.2.label = r.label := by
  let q0 := sigMoveLeaderPreclear hψ l r
  let moved := sigMoveTransfers q0.1 q0.2
  let walled := comparisonLeaderWall moved.1 moved.2
  have h0 : q0.1.label = l.label ∧ q0.2.label = r.label := by
    simp [q0, sigMoveLeaderPreclear, clearIfLeader,
      clearComparisonSignal]
  have hm := sigMoveTransfers_labels_eq hψ q0.1 q0.2
  have hw : walled.1.label = moved.1.label ∧
      walled.2.label = moved.2.label := by
    simp [walled, comparisonLeaderWall, clearComparisonSignal]
  have ht := sigMoveControlTail_labels_eq hψ walled.1 walled.2
  exact ⟨ht.1.trans (hw.1.trans (hm.1.trans h0.1)),
    ht.2.trans (hw.2.trans (hm.2.trans h0.2))⟩

/-- The initiator shield is framed by the wall-aware SIGMOVE. -/
theorem sigMoveLeaderWall_left_shield_eq (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sigMoveLeaderWall hψ l r).1.shield = l.shield := by
  let q0 := sigMoveLeaderPreclear hψ l r
  let moved := sigMoveTransfers q0.1 q0.2
  let walled := comparisonLeaderWall moved.1 moved.2
  have h0 : q0.1.shield = l.shield := by
    simp [q0, sigMoveLeaderPreclear, clearIfLeader,
      clearComparisonSignal]
  have hm := sigMoveTransfers_left_shield_eq hψ q0.1 q0.2
  have hw : walled.1.shield = moved.1.shield := by
    simp [walled, comparisonLeaderWall, clearComparisonSignal]
  exact (sigMoveControlTail_left_shield_eq hψ walled.1 walled.2).trans
    (hw.trans (hm.trans h0))

private theorem sigMoveControlTail_neutral (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : ComparisonNeutral l)
    (hr : ComparisonNeutral r) :
    let q := sigMoveControlTail hψ l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 := by
  have hlControl : sigMoveApplyControl hψ l = l := by
    simp [sigMoveApplyControl, hl.2.2.1]
  have hrControl : sigMoveApplyControl hψ r = r := by
    simp [sigMoveApplyControl, hr.2.2.1]
  simpa [sigMoveControlTail, hlControl, hrControl, hr.1] using And.intro hl hr

private theorem sigMoveApplyControl_count_payload_wall (hψ : ψ > 0)
    (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).count = u.count ∧
      PayloadView.ofState (sigMoveApplyControl hψ u) =
        PayloadView.ofState u := by
  simp only [sigMoveApplyControl]
  repeat (first | constructor | rfl | split)

private theorem sigMoveControlTail_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := sigMoveControlTail hψ l r
    (q.1.count = l.count ∧
        PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧
        PayloadView.ofState q.2 = PayloadView.ofState r) := by
  let l0 := sigMoveApplyControl hψ l
  let r0 := sigMoveApplyControl hψ r
  let l1 := if r0.state = .depart then
    if l0.label.val < ψ - 1 ∧ l0.state = .CHECK_ready then
      { l0 with state := .depart }
    else l0
  else l0
  have hl0 := sigMoveApplyControl_count_payload_wall hψ l
  have hr0 := sigMoveApplyControl_count_payload_wall hψ r
  have hl1 : l1.count = l0.count ∧
      PayloadView.ofState l1 = PayloadView.ofState l0 := by
    dsimp only [l1]
    split
    · split
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  change (l1.count = l.count ∧
      PayloadView.ofState l1 = PayloadView.ofState l) ∧
    (r0.count = r.count ∧ PayloadView.ofState r0 = PayloadView.ofState r)
  exact ⟨⟨hl1.1.trans hl0.1, hl1.2.trans hl0.2⟩, hr0⟩

private theorem sigMoveControlTail_inProtocolDomain { ψ κ : Nat }
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := sigMoveControlTail hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := sigMoveControlTail hψ l r
  have hframe := sigMoveControlTail_frame hψ l r
  exact ⟨domain_of_count_payload_eq_wall l q.1 hl hframe.1.1 hframe.1.2,
    domain_of_count_payload_eq_wall r q.2 hr hframe.2.1 hframe.2.2⟩

private theorem sigMoveTransfers_inProtocolDomain { ψ κ : Nat }
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := sigMoveTransfers l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let moved := sigMoveTransfers l r
  let out := sigMoveControlTail hψ moved.1 moved.2
  have hout := sigMove_inProtocolDomain hψ l r hl hr
  change out.1.inProtocolDomain κ ∧ out.2.inProtocolDomain κ at hout
  have hframe := sigMoveControlTail_frame hψ moved.1 moved.2
  exact ⟨domain_of_count_payload_eq_wall out.1 moved.1 hout.1
      hframe.1.1.symm hframe.1.2.symm,
    domain_of_count_payload_eq_wall out.2 moved.2 hout.2
      hframe.2.1.symm hframe.2.2.symm⟩

/-- At the exact boundary before `path2` control, a right leader has erased
both its own carrier and the incoming left-boundary carrier. -/
theorem sigMoveLeaderBeforeControl_right_leader_neutral (hψ : ψ > 0)
    (l r : AgentState ψ) (hr : r.leader = true) :
    let q := sigMoveLeaderBeforeControl hψ l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 := by
  let q0 := sigMoveLeaderPreclear hψ l r
  let moved := sigMoveTransfers q0.1 q0.2
  have hr0 : q0.2.leader = true := by
    simp [q0, sigMoveLeaderPreclear, clearIfLeader, hr,
      clearComparisonSignal]
  have hmovedLeader : moved.2.leader = true := by
    exact (sigMoveTransfers_leaders_eq hψ q0.1 q0.2).2.trans hr0
  change ComparisonNeutral (comparisonLeaderWall moved.1 moved.2).1 ∧
    ComparisonNeutral (comparisonLeaderWall moved.1 moved.2).2
  simp [comparisonLeaderWall, hmovedLeader, clearComparisonSignal_neutral]

private theorem sigMoveLeaderBeforeControl_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := sigMoveLeaderBeforeControl hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let l0 := if l.leader = true ∨ incompleteLeftLeaderBoundary hψ l r then
    clearComparisonSignal l
  else l
  let r0 := clearIfLeader r
  have hl0 : l0.inProtocolDomain κ := by
    unfold l0
    split
    · exact clearComparisonSignal_inProtocolDomain l hl
    · exact hl
  have hr0 : r0.inProtocolDomain κ := by
    unfold r0 clearIfLeader
    split
    · exact clearComparisonSignal_inProtocolDomain r hr
    · exact hr
  let moved := sigMoveTransfers l0 r0
  have hmoved := sigMoveTransfers_inProtocolDomain hψ l0 r0 hl0 hr0
  change moved.1.inProtocolDomain κ ∧ moved.2.inProtocolDomain κ at hmoved
  simpa [sigMoveLeaderBeforeControl, sigMoveLeaderPreclear, l0, r0] using
    comparisonLeaderWall_inProtocolDomain moved.1 moved.2 hmoved.1 hmoved.2

theorem sigMoveLeaderWall_eq_sigMove_of_no_leaders (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.leader = false)
    (hr : r.leader = false) :
    sigMoveLeaderWall hψ l r = sigMove hψ l r := by
  have hboundary : ¬incompleteLeftLeaderBoundary hψ l r := by
    intro h
    simpa [hr] using h.1
  let moved := sigMoveTransfers l r
  have hleaders := sigMoveTransfers_leaders_eq hψ l r
  change moved.1.leader = l.leader ∧ moved.2.leader = r.leader at hleaders
  simp [sigMoveLeaderWall, sigMoveLeaderBeforeControl,
    sigMoveLeaderPreclear, hl, hr, hboundary, clearIfLeader]
  change sigMoveControlTail hψ (comparisonLeaderWall moved.1 moved.2).1
      (comparisonLeaderWall moved.1 moved.2).2 = sigMove hψ l r
  have hleft : moved.1.leader = false := hleaders.1.trans hl
  have hright : moved.2.leader = false := hleaders.2.trans hr
  rw [show comparisonLeaderWall moved.1 moved.2 = moved by
    simp [comparisonLeaderWall, hleft, hright]]
  rfl

theorem sigMoveLeaderWall_right_leader_neutral (hψ : ψ > 0)
    (l r : AgentState ψ) (hr : r.leader = true) :
    let q := sigMoveLeaderWall hψ l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 := by
  let before := sigMoveLeaderBeforeControl hψ l r
  have hneutral := sigMoveLeaderBeforeControl_right_leader_neutral hψ l r hr
  change ComparisonNeutral before.1 ∧ ComparisonNeutral before.2 at hneutral
  exact sigMoveControlTail_neutral hψ before.1 before.2
    hneutral.1 hneutral.2

theorem sigMoveLeaderWall_incomplete_boundary_clears_left (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hwall : incompleteLeftLeaderBoundary hψ l r) :
    let q := sigMoveLeaderWall hψ l r
    ComparisonNeutral q.1 := by
  exact (sigMoveLeaderWall_right_leader_neutral hψ l r hwall.1).1

theorem sigMoveLeaderWall_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := sigMoveLeaderWall hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let before := sigMoveLeaderBeforeControl hψ l r
  have hbefore := sigMoveLeaderBeforeControl_inProtocolDomain hψ l r hl hr
  change before.1.inProtocolDomain κ ∧
    before.2.inProtocolDomain κ at hbefore
  exact sigMoveControlTail_inProtocolDomain hψ before.1 before.2
    hbefore.1 hbefore.2

/-- Source-backed boundary immediately before CHECK. -/
def wallSweepBeforeCheck (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsiLeaderProbeWall hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  sigMoveLeaderWall hψ q.1 q.2

/-- Source-backed boundary immediately before SUPPRESS_SIG. -/
def wallSweepBeforeSuppress (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := wallSweepBeforeCheck hψ κ l r
  let q := checkSig hψ q.1 q.2
  let q := disappear hψ q.1 q.2
  compareSigNoSourceRearm hψ q.1 q.2

/-- Source-backed boundary immediately before the repaired WRITE_SEQ. -/
def wallSweepBeforeWrite (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := wallSweepBeforeSuppress hψ κ l r
  let q := suppressSigResetKill hψ q.1 q.2
  eliminateLeadersNoCollision hψ q.1 q.2

/-- One source-backed raw transition combining CHECK birth, the probe/reset/
leader walls, and the already verified numeric, collision, source-rearm, and
writer-lifecycle repairs.  This is a research transition, not a claim about the
literal pseudocode. -/
def wallSweepTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := wallSweepBeforeWrite hψ κ l r
  writeSeqPersistentComparisonTransportLifecycle hψ q.1 q.2

/-- Every stage through the wall-sweep boundary before WRITE_SEQ preserves the
declared numeric domain. -/
theorem wallSweepBeforeWrite_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := wallSweepBeforeWrite hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := pPsiLeaderProbeWall hψ l r
  have h0 := pPsiLeaderProbeWall_inProtocolDomain hψ l r hl hr
  let q1 := genSigSaturated hψ κ q0.1 q0.2
  have h1 := genSigSaturated_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  let q2 := cleanSig hψ q1.1 q1.2
  have h2 := cleanSig_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
  let q3 := eliminateSig hψ q2.1 q2.2
  have h3 := eliminateSig_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2
  let q4 := sigMoveLeaderWall hψ q3.1 q3.2
  have h4 := sigMoveLeaderWall_inProtocolDomain hψ q3.1 q3.2 h3.1 h3.2
  let q5 := checkSig hψ q4.1 q4.2
  have h5 := checkSig_inProtocolDomain hψ q4.1 q4.2 h4.1 h4.2
  let q6 := disappear hψ q5.1 q5.2
  have h6 := disappear_inProtocolDomain hψ q5.1 q5.2 h5.1 h5.2
  let q7 := compareSigNoSourceRearm hψ q6.1 q6.2
  have h7 := compareSigNoSourceRearm_inProtocolDomain hψ q6.1 q6.2
    h6.1 h6.2
  let q8 := suppressSigResetKill hψ q7.1 q7.2
  have h8 := suppressSigResetKill_inProtocolDomain hψ q7.1 q7.2 h7.1 h7.2
  have h9 := eliminateLeadersNoCollision_inProtocolDomain hψ q8.1 q8.2
    h8.1 h8.2
  simpa [wallSweepBeforeWrite, wallSweepBeforeSuppress, wallSweepBeforeCheck,
    q0, q1, q2, q3, q4, q5, q6, q7, q8] using h9

end PPLLWallSweepRepair

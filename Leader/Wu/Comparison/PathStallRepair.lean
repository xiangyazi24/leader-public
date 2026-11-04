import Leader.Wu.Comparison.ExpiringTraceConvergence

/-!
# Path-movement stall expiration

The first timer reset on any state/path2 change. Arbitrary comparison-state
oscillation can therefore look like progress forever. This refinement resets
only when the physical `path` location or its executable movement permission
changes. Static bit-comparison work spends budget, so the budget must cover a
whole local comparison lifecycle; the concrete ψ=2 six-step route needs six
units and is checked below.

The state carrier remains finite (`ExpiringAgentState`). This is a new physical
transition, not an erasing proof refinement of the earlier timer semantics.
-/

namespace PPLLPathStallComparisonRepair

open PPLL PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair

/-- Progress that can refresh stale-path lifetime: physical path movement or a
change in the one-shot movement permission. State/path2 oscillations do not. -/
structure PathProgressView (ψ κ : Nat) where
  path : BoundedPathInfo ψ
  path0Crossed : Bool
  deriving DecidableEq, Repr

/-- Extract path-location progress. -/
def PathProgressView.ofState
    (s : AuthorizedBoundedAgentState ψ κ) : PathProgressView ψ κ :=
  ⟨s.core.path, s.path0Crossed⟩

/-- Path-stall endpoint policy. -/
def pathExpireOne (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ) : ExpiringAgentState ψ κ τ :=
  if PathProgressView.ofState out.core ≠ PathProgressView.ofState old.core then
    ⟨out.core, freshStall τ⟩
  else if hzero : old.stall.val = 0 then
    ⟨clearComparisonCarrier out.core, freshStall τ⟩
  else
    ⟨out.core, decStall old.stall (Nat.pos_of_ne_zero hzero)⟩

/-- Full finite path-stall transition over the authorized comparison repair. -/
def pathStallTransition (hψ : ψ > 0) (κ τ : Nat)
    (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := authorizedBoundedTransition hψ κ l.core r.core
  let lOut : ExpiringAgentState ψ κ τ := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState ψ κ τ := ⟨q.2, r.stall⟩
  (pathExpireOne τ l lOut, pathExpireOne τ r rOut)

/-- Physical path movement preserves the output and resets its lifetime. -/
theorem pathExpireOne_of_progress (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hprogress : PathProgressView.ofState out.core ≠
      PathProgressView.ofState old.core) :
    pathExpireOne τ old out = ⟨out.core, freshStall τ⟩ := by
  simp [pathExpireOne, hprogress]

/-- Static paths spend positive budget even when state/path2 changes. -/
theorem pathExpireOne_decreases_of_static (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hstatic : PathProgressView.ofState out.core =
      PathProgressView.ofState old.core)
    (hpos : old.stall.val > 0) :
    (pathExpireOne τ old out).stall.val < old.stall.val := by
  unfold pathExpireOne
  rw [if_neg (not_not_intro hstatic)]
  split
  · rename_i hzero
    have : False := by omega
    exact this.elim
  · unfold decStall
    dsimp only
    omega

/-- A positive static-path budget decrements by exactly one while preserving
the base physical output. -/
theorem pathExpireOne_succ_of_static (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hstatic : PathProgressView.ofState out.core =
      PathProgressView.ofState old.core)
    (hpos : old.stall.val > 0) :
    pathExpireOne τ old out = ⟨out.core, decStall old.stall hpos⟩ := by
  unfold pathExpireOne
  rw [if_neg (not_not_intro hstatic)]
  split
  · rename_i hzero
    have : False := by omega
    exact this.elim
  · rfl

/-- Zero static-path budget deletes the comparison carrier. -/
theorem pathExpireOne_zero_clears (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hstatic : PathProgressView.ofState out.core =
      PathProgressView.ofState old.core)
    (hzero : old.stall.val = 0) :
    let q := pathExpireOne τ old out
    q.core.core.path = .bot ∧ q.core.core.path2 = none ∧
      q.core.path0Crossed = false := by
  unfold pathExpireOne
  rw [if_neg (not_not_intro hstatic)]
  simp [hzero, clearComparisonCarrier]

/-! ## Abstract local countdown -/

/-- One no-progress opportunity in which the base physical core is unchanged. -/
def pathIdleTick (τ : Nat) (s : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ :=
  pathExpireOne τ s s

/-- Iterate local no-progress opportunities. -/
def pathIdleRun (τ : Nat) : Nat → ExpiringAgentState ψ κ τ →
    ExpiringAgentState ψ κ τ
  | 0, s => s
  | t + 1, s => pathIdleRun τ t (pathIdleTick τ s)

/-- Any arbitrarily initialized finite budget clears a completely static path
after exactly `stall+1` local opportunities. -/
theorem pathIdleRun_clears (τ : Nat) (s : ExpiringAgentState ψ κ τ) :
    (pathIdleRun τ (s.stall.val + 1) s).core.core.path = .bot := by
  generalize hk : s.stall.val = k
  induction k generalizing s with
  | zero =>
      have hstatic : PathProgressView.ofState s.core =
          PathProgressView.ofState s.core := rfl
      have htick := pathExpireOne_zero_clears τ s s hstatic hk
      change (pathIdleTick τ s).core.core.path = .bot
      exact htick.1
  | succ k ih =>
      have hpos : s.stall.val > 0 := by omega
      have hstatic : PathProgressView.ofState s.core =
          PathProgressView.ofState s.core := rfl
      have htick := pathExpireOne_succ_of_static τ s s hstatic hpos
      let s' : ExpiringAgentState ψ κ τ :=
        ⟨s.core, decStall s.stall hpos⟩
      change pathIdleTick τ s = s' at htick
      have hs' : s'.stall.val = k := by
        dsimp only [s', decStall]
        omega
      change (pathIdleRun τ (k + 1) (pathIdleTick τ s)).core.core.path = .bot
      rw [htick]
      exact ih s' hs'

/-- Iterate a unary base evolution whose non-path fields may change before each
expiration check. -/
def pathStaticRun (τ : Nat)
    (base : ExpiringAgentState ψ κ τ → ExpiringAgentState ψ κ τ) :
    Nat → ExpiringAgentState ψ κ τ → ExpiringAgentState ψ κ τ
  | 0, s => s
  | t + 1, s => pathStaticRun τ base t (pathExpireOne τ s (base s))

/-- The countdown proof does not require the whole physical state to stutter:
any base evolution preserving path/permission location is cleaned after
`stall+1` local opportunities. -/
theorem pathStaticRun_clears (τ : Nat)
    (base : ExpiringAgentState ψ κ τ → ExpiringAgentState ψ κ τ)
    (hbase : ∀ s, PathProgressView.ofState (base s).core =
      PathProgressView.ofState s.core)
    (s : ExpiringAgentState ψ κ τ) :
    (pathStaticRun τ base (s.stall.val + 1) s).core.core.path = .bot := by
  generalize hk : s.stall.val = k
  induction k generalizing s with
  | zero =>
      have hclear := pathExpireOne_zero_clears τ s (base s) (hbase s) hk
      change (pathExpireOne τ s (base s)).core.core.path = .bot
      exact hclear.1
  | succ k ih =>
      have hpos : s.stall.val > 0 := by omega
      have hstep := pathExpireOne_succ_of_static τ s (base s) (hbase s) hpos
      let s' : ExpiringAgentState ψ κ τ :=
        ⟨(base s).core, decStall s.stall hpos⟩
      change pathExpireOne τ s (base s) = s' at hstep
      have hs' : s'.stall.val = k := by
        dsimp only [s', decStall]
        omega
      change (pathStaticRun τ base (k + 1)
        (pathExpireOne τ s (base s))).core.core.path = .bot
      rw [hstep]
      exact ih s' hs'

/-- Packaged finite path-stall protocol. -/
def pathStallProtocol (hψ : ψ > 0) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := LeaderOutput
  transition := pathStallTransition hψ κ τ
  output := fun s => if s.core.core.leader then .leader else .follower

/-! ## Return-priority branch API -/

/-- At the terminal boundary, an incoming compare1 wave is converted to
compare2 before any forward-wave branch is considered. -/
theorem returnPriority_converts_at_terminal (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hl : l.label = ⟨ψ - 1, by omega⟩)
    (hr : r.state = .compare1) :
    cmpUpdateReturnPriority hψ l r = ({ l with state := .compare2 }, r) := by
  simp [cmpUpdateReturnPriority, hl, hr]

/-- Away from the conversion boundary, compare1 propagates left. -/
theorem returnPriority_moves_compare1 (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hnot : ¬(l.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .compare1))
    (hr : r.state = .compare1) :
    cmpUpdateReturnPriority hψ l r = ({ l with state := .compare1 }, r) := by
  have hl : l.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro heq
    exact hnot ⟨heq, hr⟩
  simp [cmpUpdateReturnPriority, hl, hr]

/-- A compare2 return wave always propagates left when the conversion branch is
inactive. -/
theorem returnPriority_moves_compare2 (hψ : ψ > 0)
    (l r : AgentState ψ) (hr : r.state = .compare2) :
    cmpUpdateReturnPriority hψ l r = ({ l with state := .compare2 }, r) := by
  simp [cmpUpdateReturnPriority, hr]

/-- A terminal congest forward wave locks the next component when no return
wave is present. -/
theorem returnPriority_creates_lock (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hlLabel : l.label = ⟨ψ - 1, by omega⟩)
    (hlState : l.state = .congest)
    (hr : r.state ≠ .compare1 ∧ r.state ≠ .compare2) :
    cmpUpdateReturnPriority hψ l r = (l, { r with state := .lock }) := by
  simp [cmpUpdateReturnPriority, hlLabel, hlState, hr.1, hr.2]

/-- A lock reaching the predecessor of a terminal responder launches compare1. -/
theorem returnPriority_launches_compare1 (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hrLabel : r.label = ⟨ψ - 1, by omega⟩)
    (hlState : l.state = .lock)
    (hlNotTerminal : l.label ≠ ⟨ψ - 1, by omega⟩)
    (hr : r.state ≠ .compare1 ∧ r.state ≠ .compare2) :
    cmpUpdateReturnPriority hψ l r = (l, { r with state := .compare1 }) := by
  simp [cmpUpdateReturnPriority, hrLabel, hlState, hlNotTerminal,
    hr.1, hr.2]

/-- An interior forward congest/lock wave copies its state right when no return
wave or terminal special case is enabled. -/
theorem returnPriority_moves_forward (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hlNotTerminal : l.label ≠ ⟨ψ - 1, by omega⟩)
    (hrNotTerminal : r.label ≠ ⟨ψ - 1, by omega⟩)
    (hlState : l.state = .congest ∨ l.state = .lock)
    (hr : r.state ≠ .compare1 ∧ r.state ≠ .compare2) :
    cmpUpdateReturnPriority hψ l r = (l, { r with state := l.state }) := by
  simp [cmpUpdateReturnPriority, hlNotTerminal, hrNotTerminal,
    hlState, hr.1, hr.2]

/-! ## Local ψ=2 lifecycle survives budget six -/

private def auditDepart0 (moved : Bool) : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .depart with path := .some 0 0 }, moved⟩
private def auditDepart1 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .depart with path := .some 1 0 }, false⟩

private theorem auditPairDomain :
    (auditDepart0 true).core.inProtocolDomain 0 ∧
      auditDepart1.core.inProtocolDomain 0 := by
  simp [auditDepart0, auditDepart1, AgentState.inProtocolDomain,
    PPLLCounterexample.state2]

/-- Local authorized CMP_UPDATE followed by path-stall accounting. -/
def localPathCmp (l r : ExpiringAgentState 2 0 6) :
    ExpiringAgentState 2 0 6 × ExpiringAgentState 2 0 6 :=
  let q := authorizedCmpUpdate (by omega : 2 > 0) l.core.erase r.core.erase
  let hq := authorizedCmpUpdate_inProtocolDomain (κ := 0)
    (by omega : 2 > 0) l.core.erase r.core.erase
    l.core.core.erase_inProtocolDomain r.core.core.erase_inProtocolDomain
  let lCore : AuthorizedBoundedAgentState 2 0 :=
    ⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩
  let rCore : AuthorizedBoundedAgentState 2 0 :=
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩
  (pathExpireOne 6 l ⟨lCore, l.stall⟩,
    pathExpireOne 6 r ⟨rCore, r.stall⟩)

private def localStart0 : ExpiringAgentState 2 0 6 :=
  ⟨⟨BoundedAgentState.ofDomain (auditDepart0 true).core auditPairDomain.1,
      true⟩, freshStall 6⟩
private def localStart1 : ExpiringAgentState 2 0 6 :=
  ⟨⟨BoundedAgentState.ofDomain auditDepart1.core auditPairDomain.2,
      false⟩, freshStall 6⟩

/-- Six static-path comparison interactions reach path2 before a seventh
no-progress opportunity could expire the carrier. The first authorization
consumption is path-progress and resets the budget, leaving one unit after the
remaining five static-path interactions. -/
theorem pathStall_psi2_budget_six_reaches_path2 :
    let q0 := localPathCmp localStart0 localStart1
    let q1 := localPathCmp q0.2 q0.1
    let q2 := localPathCmp q1.2 q1.1
    let q3 := localPathCmp q2.1 q2.2
    let q4 := localPathCmp q3.2 q3.1
    let q5 := localPathCmp q4.2 q4.1
    q5.1.core.core.path2 ≠ none ∧ q5.1.stall.val = 1 := by
  decide

end PPLLPathStallComparisonRepair

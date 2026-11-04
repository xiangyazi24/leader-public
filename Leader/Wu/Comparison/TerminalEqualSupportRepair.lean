import Leader.Wu.Comparison.LeaderCreationCleanupRepair

/-!
# Physical support for pre-existing terminal equality

Algorithm 11 creates a terminal leader from `.equal` without rechecking that a
path exists.  An arbitrary pathless `.equal` therefore survives the prefix and
creates a leader.  This separately named repair adds no incremental field to
the authorized carrier and sanitizes the actual pre-CHECK endpoints: a pre-existing terminal equality is retained only when its
current path label and bit locally match the endpoint.

This is deliberately local support, not provenance.  T1's forged complete
carrier is locally consistent and remains executable.  The repair neither
observes a remote leader nor satisfies the immediate-protection premise ruled
out by `RemoteLeaderGuardNoGo`.
-/

namespace PPLLTerminalEqualSupportRepair

open PPLL PPLLRepair PPLLDomain PPLLAuthorizedComparisonRepair
  PPLLLeaderCreationCleanupRepair

/-- Current physical path data locally supports this endpoint's equality claim
when label and bit both match. -/
def equalLocallySupported (u : AgentState ψ) : Bool :=
  match u.path with
  | .bot => false
  | .some pathLabel pathBit =>
      decide (pathLabel = u.label.val) &&
        decide (pathBit = if u.bit then 1 else 0)

/-- A terminal `.equal` is unsupported when its current path does not locally
match the endpoint. -/
def unsupportedTerminalEqual (hψ : ψ > 0) (u : AgentState ψ) : Bool :=
  decide (u.label = ⟨ψ - 1, by omega⟩) &&
    decide (u.state = .equal) && !equalLocallySupported u

/-- Demote only unsupported pre-existing terminal equality. -/
def sanitizeTerminalEqual (hψ : ψ > 0)
    (u : AgentState ψ) : AgentState ψ :=
  if unsupportedTerminalEqual hψ u then { u with state := .none } else u

/-- Sanitization frames every field except `state`. -/
theorem sanitizeTerminalEqual_frame (hψ : ψ > 0) (u : AgentState ψ) :
    let q := sanitizeTerminalEqual hψ u
    q.leader = u.leader ∧ q.path = u.path ∧ q.path2 = u.path2 ∧
      q.bit = u.bit ∧ q.label = u.label := by
  unfold sanitizeTerminalEqual
  split <;> simp

/-- State-only sanitization preserves every numeric value range. -/
theorem sanitizeTerminalEqual_inProtocolDomain (hψ : ψ > 0)
    (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (sanitizeTerminalEqual hψ u).inProtocolDomain κ := by
  unfold sanitizeTerminalEqual
  split
  · simpa [AgentState.inProtocolDomain] using hu
  · exact hu

/-- Authorized fail-closed lift: rejecting equality also consumes the existing
one-shot comparison permission. -/
def sanitizeAuthorizedTerminalEqual (hψ : ψ > 0)
    (u : AuthorizedAgentState ψ) : AuthorizedAgentState ψ :=
  if unsupportedTerminalEqual hψ u.core then
    ⟨{ u.core with state := .none }, false⟩
  else u

/-- Sanitize both actual pre-CHECK endpoints. -/
def sanitizeAuthorizedPair (hψ : ψ > 0)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  (sanitizeAuthorizedTerminalEqual hψ q.1,
    sanitizeAuthorizedTerminalEqual hψ q.2)

/-- Authorized sanitization preserves the core numeric domain. -/
theorem sanitizeAuthorizedTerminalEqual_inProtocolDomain (hψ : ψ > 0)
    (u : AuthorizedAgentState ψ) (hu : u.core.inProtocolDomain κ) :
    (sanitizeAuthorizedTerminalEqual hψ u).core.inProtocolDomain κ := by
  unfold sanitizeAuthorizedTerminalEqual
  split
  · simpa [AgentState.inProtocolDomain] using hu
  · exact hu

/-- Full authorized transition with the support check inserted after SIGMOVE
and before CHECK.  All later stages are unchanged. -/
def terminalEqualSupportAuthorizedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let beforeCheck := authorizedBeforeCheck hψ κ l r
  let clean := sanitizeAuthorizedPair hψ beforeCheck
  let afterCheck := authorizedCheckSig hψ clean.1 clean.2
  authorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2

/-- If neither actual pre-CHECK endpoint is changed, the support repair agrees
exactly with the existing authorized transition. -/
theorem terminalEqualSupport_eq_authorized_of_fixed
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hfixed :
      let q := authorizedBeforeCheck hψ κ l r
      sanitizeAuthorizedPair hψ q = q) :
    terminalEqualSupportAuthorizedTransition hψ κ l r =
      ppllAuthorizedRepair hψ κ l r := by
  simp [terminalEqualSupportAuthorizedTransition, hfixed,
    authorizedAfterCheckSuffix, ppllAuthorizedRepair,
    authorizedBeforeSuppress]

private theorem authorizedAfterCheckSuffix_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedAfterCheckSuffix hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let q0 := authorizedDisappear hψ l r
  have h0 := authorizedReconcile_inProtocolDomain (disappear hψ) l r
    (disappear_inProtocolDomain hψ l.core r.core hl hr)
  let q1 := authorizedCompareSig hψ q0.1 q0.2
  have h1 := authorizedCompareSig_inProtocolDomain
    hψ q0.1 q0.2 h0.1 h0.2
  let q2 := authorizedReconcile (suppressSig hψ) q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain (suppressSig hψ) q1.1 q1.2
    (suppressSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
  let q3 := authorizedReconcile (eliminateLeadersNoCollision hψ) q2.1 q2.2
  have h3 := authorizedReconcile_inProtocolDomain
    (eliminateLeadersNoCollision hψ) q2.1 q2.2
    (eliminateLeadersNoCollision_inProtocolDomain
      hψ q2.1.core q2.2.core h2.1 h2.2)
  exact authorizedReconcile_inProtocolDomain (writeSeq hψ) q3.1 q3.2
    (writeSeq_inProtocolDomain hψ q3.1.core q3.2.core h3.1 h3.2)

attribute [local irreducible] authorizedBeforeCheck
  authorizedAfterCheckSuffix terminalEqualSupportAuthorizedTransition

/-- The complete support repair remains inside all declared numeric ranges. -/
theorem terminalEqualSupportAuthorizedTransition_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := terminalEqualSupportAuthorizedTransition hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  unfold terminalEqualSupportAuthorizedTransition
  dsimp only
  let q0 := authorizedBeforeCheck hψ κ l r
  have h0 := authorizedBeforeCheck_inProtocolDomain hψ κ l r hl hr
  let q1 := sanitizeAuthorizedPair hψ q0
  have h1 : q1.1.core.inProtocolDomain κ ∧
      q1.2.core.inProtocolDomain κ :=
    ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ q0.1 h0.1,
      sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ q0.2 h0.2⟩
  let q2 := authorizedCheckSig hψ q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain (checkSig hψ) q1.1 q1.2
    (checkSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
  exact authorizedAfterCheckSuffix_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2

/-! ## Existing finite carrier and exact erasure -/

/-- Total transition on the unchanged finite authorized carrier. -/
def terminalEqualSupportBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := terminalEqualSupportAuthorizedTransition hψ κ l.erase r.erase
  let hq := terminalEqualSupportAuthorizedTransition_inProtocolDomain
    hψ κ l.erase r.erase l.core.erase_inProtocolDomain
    r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

/-- Finite execution erases exactly to the named support-repair transition. -/
theorem erase_terminalEqualSupportBoundedTransition
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q := terminalEqualSupportBoundedTransition hψ κ l r
    (q.1.erase, q.2.erase) =
      terminalEqualSupportAuthorizedTransition hψ κ l.erase r.erase := by
  let q := terminalEqualSupportAuthorizedTransition hψ κ l.erase r.erase
  let hq := terminalEqualSupportAuthorizedTransition_inProtocolDomain
    hψ κ l.erase r.erase l.core.erase_inProtocolDomain
    r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = q
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Packaged finite protocol for the terminal-equality support repair. -/
def terminalEqualSupportBoundedProtocol (hψ : ψ > 0) (κ : Nat) :
    PopulationProtocol where
  Q := AuthorizedBoundedAgentState ψ κ
  Y := LeaderOutput
  transition := terminalEqualSupportBoundedTransition hψ κ
  output := fun s => if s.core.leader then .leader else .follower

/-- No new state is introduced: reuse the exact authorized certificate. -/
def terminalEqualSupportStateCertificate (ψ κ : Nat) :
    ExhaustiveList (AuthorizedBoundedAgentState ψ κ) :=
  authorizedBoundedAgentState ψ κ

/-- Terminal-equality support reuses a duplicate-free authorized certificate. -/
theorem terminalEqualSupportStateCertificate_values_nodup (ψ κ : Nat) :
    (terminalEqualSupportStateCertificate ψ κ).values.Nodup :=
  authorizedBoundedAgentState_values_nodup ψ κ

/-- The repair has exact semantic-cardinality factor one relative to authorization. -/
theorem terminalEqualSupportStateCertificate_values_length (ψ κ : Nat) :
    (terminalEqualSupportStateCertificate ψ κ).values.length =
      (authorizedBoundedAgentState ψ κ).values.length := by
  rfl

end PPLLTerminalEqualSupportRepair

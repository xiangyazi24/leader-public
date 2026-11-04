import Leader.Wu.Comparison.TerminalEqualSupportRepair
import Leader.Wu.WriteSeq.IncrementGate

/-!
# One non-duplicating stack of the verified local repairs

The existing T8, T9, T19, and T20 repairs each own overlapping parts of
Algorithm 1, so their full transitions cannot be nested.  This module instead
executes each algorithmic stage once and substitutes each local repair at its
proved boundary:

* priority source-zero deletion before ordinary execution;
* moved-carrier authorization and return-priority comparison;
* terminal-equality support after SIGMOVE and before CHECK;
* leader-birth observation before WRITE_SEQ;
* prepared increment validation inside Algorithm 16 before Algorithm 19;
* deletion-priority path-stall accounting after birth marking.

The carrier is the existing finite authorization-plus-stall state.  This is a
coherent local repair stack, not yet a global legitimate invariant: T1 remains
the required remote-carrier negative control.
-/

namespace PPLLCombinedLocalRepair

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair PPLLWriteIncrementGate

/-! ## One authorized suffix with the prepared write gate -/

/-- Existing authorized suffix after CHECK, replacing only ordinary WRITE_SEQ
by the prepared increment gate. -/
def combinedAuthorizedAfterCheckSuffix (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q0 := authorizedDisappear hψ l r
  let q1 := authorizedCompareSig hψ q0.1 q0.2
  let q2 := authorizedReconcile (suppressSig hψ) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollision hψ) q2.1 q2.2
  authorizedReconcile (writeSeqIncrementGate hψ) q3.1 q3.2

/-- The gated suffix preserves every numeric domain component by composing the
existing per-stage contracts. -/
theorem combinedAuthorizedAfterCheckSuffix_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := combinedAuthorizedAfterCheckSuffix hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let q0 := authorizedDisappear hψ l r
  have h0 := authorizedReconcile_inProtocolDomain
    (disappear hψ) l r
    (disappear_inProtocolDomain hψ l.core r.core hl hr)
  let q1 := authorizedCompareSig hψ q0.1 q0.2
  have h1 := authorizedCompareSig_inProtocolDomain
    hψ q0.1 q0.2 h0.1 h0.2
  let q2 := authorizedReconcile (suppressSig hψ) q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (suppressSig hψ) q1.1 q1.2
    (suppressSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollision hψ) q2.1 q2.2
  have h3 := authorizedReconcile_inProtocolDomain
    (eliminateLeadersNoCollision hψ) q2.1 q2.2
    (eliminateLeadersNoCollision_inProtocolDomain
      hψ q2.1.core q2.2.core h2.1 h2.2)
  exact authorizedReconcile_inProtocolDomain
    (writeSeqIncrementGate hψ) q3.1 q3.2
    (writeSeqIncrementGate_inProtocolDomain
      hψ q3.1.core q3.2.core h3.1 h3.2)

/-! ## Exact combined audit transition -/

/-- One Algorithm-1 execution containing all four verified local stage repairs.
Deletion branches retain top priority and return before CHECK/COMPARE revival. -/
def combinedLocalAuthorizedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then
    authorizedEliminateSig hψ l0 r0
  else if deletionActive l0 then
    (l0, r0)
  else
    let beforeRaw := authorizedBeforeCheck hψ κ l0 r0
    let beforeCheck := sanitizeAuthorizedPair hψ beforeRaw
    let afterCheck := authorizedCheckSig hψ beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born
      (combinedAuthorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2)

attribute [local irreducible]
  authorizedBeforeCheck combinedAuthorizedAfterCheckSuffix

/-- The combined local transition preserves every declared numeric range. -/
theorem combinedLocalAuthorizedTransition_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := combinedLocalAuthorizedTransition hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain κ at hl0
  change r0.core.inProtocolDomain κ at hr0
  unfold combinedLocalAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain
      (eliminateSig hψ) l0 r0
      (eliminateSig_inProtocolDomain hψ l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let q0 := authorizedBeforeCheck hψ κ l0 r0
      have h0 := authorizedBeforeCheck_inProtocolDomain
        hψ κ l0 r0 hl0 hr0
      let q1 := sanitizeAuthorizedPair hψ q0
      have h1 : q1.1.core.inProtocolDomain κ ∧
          q1.2.core.inProtocolDomain κ :=
        ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ q0.1 h0.1,
          sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ q0.2 h0.2⟩
      let q2 := authorizedCheckSig hψ q1.1 q1.2
      have h2 := authorizedReconcile_inProtocolDomain
        (checkSig hψ) q1.1 q1.2
        (checkSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
      let tail := combinedAuthorizedAfterCheckSuffix hψ q2.1 q2.2
      have ht := combinedAuthorizedAfterCheckSuffix_inProtocolDomain
        hψ q2.1 q2.2 h2.1 h2.2
      let born := leaderBirthBeforeOrAtCheck l0 r0 q1 q2
      exact markLeaderBirth_inProtocolDomain born tail ht

/-! ## Exact finite reification and timer composition -/

/-- Total transition on the unchanged finite authorized carrier. -/
def combinedLocalBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := combinedLocalAuthorizedTransition hψ κ l.erase r.erase
  let hq := combinedLocalAuthorizedTransition_inProtocolDomain hψ κ
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

/-- Finite combined execution erases exactly to the named audit transition. -/
theorem erase_combinedLocalBoundedTransition
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q := combinedLocalBoundedTransition hψ κ l r
    (q.1.erase, q.2.erase) =
      combinedLocalAuthorizedTransition hψ κ l.erase r.erase := by
  let q := combinedLocalAuthorizedTransition hψ κ l.erase r.erase
  let hq := combinedLocalAuthorizedTransition_inProtocolDomain hψ κ
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = q
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Outermost path-stall accounting, preserving active deletion waves even at
zero timer before applying ordinary path-only expiration. -/
def combinedLocalPathStallTransition
    (hψ : ψ > 0) (κ τ : Nat)
    (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := combinedLocalBoundedTransition hψ κ l.core r.core
  let lOut : ExpiringAgentState ψ κ τ := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState ψ κ τ := ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne τ l lOut,
    deletionPriorityExpireOne τ r rOut)

/-- Packaged finite physical protocol for the combined local repair stack. -/
def combinedLocalProtocol (hψ : ψ > 0) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := LeaderOutput
  transition := combinedLocalPathStallTransition hψ κ τ
  output := fun s => if s.core.core.leader then .leader else .follower

/-- The combined stack adds no field beyond authorization and path-stall. -/
def combinedLocalStateCertificate (ψ κ τ : Nat) :
    ExhaustiveList (ExpiringAgentState ψ κ τ) :=
  expiringAgentState ψ κ τ

/-- The reused finite certificate remains duplicate-free. -/
theorem combinedLocalStateCertificate_values_nodup (ψ κ τ : Nat) :
    (combinedLocalStateCertificate ψ κ τ).values.Nodup :=
  expiringAgentState_values_nodup ψ κ τ

/-- Exact semantic cardinality: factor two for authorization and `τ+1` for the
stall budget; terminal support, birth cleanup, and write gating each cost one. -/
theorem combinedLocalStateCertificate_values_length (ψ κ τ : Nat) :
    (combinedLocalStateCertificate ψ κ τ).values.length =
      (2 * (PPLLFinite.boundedAgentState ψ κ).values.length) * (τ + 1) :=
  expiringAgentState_values_length ψ κ τ

end PPLLCombinedLocalRepair

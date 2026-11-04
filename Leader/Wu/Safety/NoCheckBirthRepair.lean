import Leader.Wu.Protocol.CombinedLocalRepair

/-!
# Source-shaped repair: CHECK never creates a leader

T1, T9, T19, and T20 all share one physical output writer: Algorithm 11's
terminal `.equal` branch.  Local support and source retirement clean particular
lifecycles but cannot protect a remote existing leader before that writer fires.
This separately named source-shaped repair therefore removes leader creation
from CHECK itself while leaving its comparison/action updates intact.

Leader creation remains possible through the barrier/probe subprotocol P'_ψ,
so this change does not impose the generic ban on every follower-pair birth.
The combined deletion, authorization, terminal support, write gate, and timer
stack remains unchanged around the new CHECK boundary.
-/

namespace PPLLNoCheckBirthRepair

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair PPLLCombinedLocalRepair

/-! ## CHECK with pointwise leader framing -/

/-- Restore one endpoint's input leader role after executing CHECK, retaining
all non-output CHECK state/action updates and reconciled authorization. -/
def restoreAuthorizedLeader
    (before after : AuthorizedAgentState ψ) : AuthorizedAgentState ψ :=
  ⟨{ after.core with leader := before.core.leader }, after.path0Crossed⟩

/-- Execute the repaired authorized CHECK but frame both leader outputs to their
pre-CHECK values. -/
def authorizedCheckNoBirth (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := authorizedCheckSig hψ l r
  (restoreAuthorizedLeader l q.1, restoreAuthorizedLeader r q.2)

/-- No-CHECK-birth semantics preserves both endpoint leader bits exactly. -/
theorem authorizedCheckNoBirth_leaders (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    let q := authorizedCheckNoBirth hψ l r
    q.1.core.leader = l.core.leader ∧ q.2.core.leader = r.core.leader := by
  exact ⟨rfl, rfl⟩

/-- Restoring a Boolean output field cannot violate any numeric payload range. -/
theorem restoreAuthorizedLeader_inProtocolDomain
    (before after : AuthorizedAgentState ψ)
    (ha : after.core.inProtocolDomain κ) :
    (restoreAuthorizedLeader before after).core.inProtocolDomain κ := by
  simpa [restoreAuthorizedLeader, AgentState.inProtocolDomain] using ha

/-- The no-birth CHECK preserves the complete numeric domain. -/
theorem authorizedCheckNoBirth_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedCheckNoBirth hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  have hq := authorizedReconcile_inProtocolDomain
    (checkSig hψ) l r
    (checkSig_inProtocolDomain hψ l.core r.core hl hr)
  exact ⟨restoreAuthorizedLeader_inProtocolDomain l _ hq.1,
    restoreAuthorizedLeader_inProtocolDomain r _ hq.2⟩

/-! ## Full source-shaped local stack -/

/-- Combined local repair with the sole global change that CHECK cannot write
`leader=true`.  P'_ψ births in the prefix are still observed and retired. -/
def noCheckBirthAuthorizedTransition (hψ : ψ > 0) (κ : Nat)
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
    let afterCheck := authorizedCheckNoBirth hψ beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born
      (combinedAuthorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2)

attribute [local irreducible]
  authorizedBeforeCheck combinedAuthorizedAfterCheckSuffix

/-- The complete no-CHECK-birth stack preserves every numeric domain. -/
theorem noCheckBirthAuthorizedTransition_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := noCheckBirthAuthorizedTransition hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain κ at hl0
  change r0.core.inProtocolDomain κ at hr0
  unfold noCheckBirthAuthorizedTransition
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
      let q2 := authorizedCheckNoBirth hψ q1.1 q1.2
      have h2 := authorizedCheckNoBirth_inProtocolDomain
        hψ q1.1 q1.2 h1.1 h1.2
      let tail := combinedAuthorizedAfterCheckSuffix hψ q2.1 q2.2
      have ht := combinedAuthorizedAfterCheckSuffix_inProtocolDomain
        hψ q2.1 q2.2 h2.1 h2.2
      let born := leaderBirthBeforeOrAtCheck l0 r0 q1 q2
      exact markLeaderBirth_inProtocolDomain born tail ht

/-- Exact finite reification on the unchanged authorized carrier. -/
def noCheckBirthBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := noCheckBirthAuthorizedTransition hψ κ l.erase r.erase
  let hq := noCheckBirthAuthorizedTransition_inProtocolDomain hψ κ
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

/-- Finite execution erases exactly to the no-CHECK-birth audit transition. -/
theorem erase_noCheckBirthBoundedTransition
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q := noCheckBirthBoundedTransition hψ κ l r
    (q.1.erase, q.2.erase) =
      noCheckBirthAuthorizedTransition hψ κ l.erase r.erase := by
  let q := noCheckBirthAuthorizedTransition hψ κ l.erase r.erase
  let hq := noCheckBirthAuthorizedTransition_inProtocolDomain hψ κ
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = q
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Deletion-priority path-stall wrapper for the source-shaped repair. -/
def noCheckBirthPathStallTransition
    (hψ : ψ > 0) (κ τ : Nat)
    (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := noCheckBirthBoundedTransition hψ κ l.core r.core
  let lOut : ExpiringAgentState ψ κ τ := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState ψ κ τ := ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne τ l lOut,
    deletionPriorityExpireOne τ r rOut)

/-- Packaged finite protocol for the no-CHECK-birth repair. -/
def noCheckBirthProtocol (hψ : ψ > 0) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := LeaderOutput
  transition := noCheckBirthPathStallTransition hψ κ τ
  output := fun s => if s.core.core.leader then .leader else .follower

/-- No new state: reuse the exact combined local certificate. -/
def noCheckBirthStateCertificate (ψ κ τ : Nat) :
    ExhaustiveList (ExpiringAgentState ψ κ τ) :=
  combinedLocalStateCertificate ψ κ τ

/-- Exact semantic cardinality is unchanged by removing the CHECK writer. -/
theorem noCheckBirthStateCertificate_values_length (ψ κ τ : Nat) :
    (noCheckBirthStateCertificate ψ κ τ).values.length =
      (2 * (PPLLFinite.boundedAgentState ψ κ).values.length) * (τ + 1) :=
  combinedLocalStateCertificate_values_length ψ κ τ

end PPLLNoCheckBirthRepair

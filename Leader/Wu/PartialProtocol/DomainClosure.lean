import Leader.Wu.PartialProtocol.Interface
import Leader.Wu.Elimination.MultiLeaderCleanupSuppressedTransitionLift

/-!
# Unconditional numeric-domain closure for `P_partial`

This file proves the domain premise of `P_partial` from the actual exported
implementation.  It uses `suppressSigHiddenControlQ5577`,
`multiLeaderAfterCheckSuffixCombinedQ5577`, and
`multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577` directly.  It does
not introduce a second transition, a source-lock `rfl`, or a renamed domain
premise.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepPreCheckResetRepair
  PPLLPpsiLeaderCreationRepair

open PhysicalBridge
open PhysicalBridge.Q5577HiddenControlAudit

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Domain closure of the actual raw suppressor -/

private theorem pPartialDomain_of_count_payload_eq_q5816
    (input output : AgentState psi)
    (hin : input.inProtocolDomain kappa)
    (hcount : output.count = input.count)
    (hpayload : PayloadView.ofState output = PayloadView.ofState input) :
    output.inProtocolDomain kappa := by
  change input.count ≤ kappa ∧ (PayloadView.ofState input).Valid at hin
  change output.count ≤ kappa ∧ (PayloadView.ofState output).Valid
  exact ⟨hcount ▸ hin.1, hpayload ▸ hin.2⟩

private theorem pPartialSuppressSigStart_inProtocolDomain_q5816
    (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigStart l r
    q.1.inProtocolDomain kappa ∧
      q.2.inProtocolDomain kappa := by
  let q := suppressSigStart l r
  have hframe :
      (q.1.count = l.count ∧
          PayloadView.ofState q.1 = PayloadView.ofState l) ∧
        (q.2.count = r.count ∧
          PayloadView.ofState q.2 = PayloadView.ofState r) := by
    simp only [q, suppressSigStart]
    repeat (first | constructor | rfl | split)
  exact
    ⟨pPartialDomain_of_count_payload_eq_q5816
        l q.1 hl hframe.1.1 hframe.1.2,
      pPartialDomain_of_count_payload_eq_q5816
        r q.2 hr hframe.2.1 hframe.2.2⟩

private theorem pPartialSuppressSigMoveReset_inProtocolDomain_q5816
    (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigMoveReset l r
    q.1.inProtocolDomain kappa ∧
      q.2.inProtocolDomain kappa := by
  let q := suppressSigMoveReset l r
  have hframe :
      (q.1.count = l.count ∧
          PayloadView.ofState q.1 = PayloadView.ofState l) ∧
        (q.2.count = r.count ∧
          PayloadView.ofState q.2 = PayloadView.ofState r) := by
    simp only [q, suppressSigMoveReset]
    repeat (first | constructor | rfl | split)
  exact
    ⟨pPartialDomain_of_count_payload_eq_q5816
        l q.1 hl hframe.1.1 hframe.1.2,
      pPartialDomain_of_count_payload_eq_q5816
        r q.2 hr hframe.2.1 hframe.2.2⟩

private theorem pPartialSuppressSigTerminal_inProtocolDomain_q5816
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigTerminal hpsi l r
    q.1.inProtocolDomain kappa ∧
      q.2.inProtocolDomain kappa := by
  unfold suppressSigTerminal
  dsimp only
  split
  · constructor
    · simpa [AgentState.inProtocolDomain] using hl
    · change (0 : Nat) ≤ kappa ∧ (PayloadView.ofState r).Valid
      change r.count ≤ kappa ∧ (PayloadView.ofState r).Valid at hr
      exact ⟨Nat.zero_le _, hr.2⟩
  · exact ⟨hl, hr⟩

private theorem pPartialSuppressSigEcho_inProtocolDomain_q5816
    (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigEcho l r
    q.1.inProtocolDomain kappa ∧
      q.2.inProtocolDomain kappa := by
  let q := suppressSigEcho l r
  have hframe :
      (q.1.count = l.count ∧
          PayloadView.ofState q.1 = PayloadView.ofState l) ∧
        (q.2.count = r.count ∧
          PayloadView.ofState q.2 = PayloadView.ofState r) := by
    simp only [q, suppressSigEcho]
    repeat (first | constructor | rfl | split)
  exact
    ⟨pPartialDomain_of_count_payload_eq_q5816
        l q.1 hl hframe.1.1 hframe.1.2,
      pPartialDomain_of_count_payload_eq_q5816
        r q.2 hr hframe.2.1 hframe.2.2⟩

private theorem pPartialSuppressSigFinish_inProtocolDomain_q5816
    (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigFinish l r
    q.1.inProtocolDomain kappa ∧
      q.2.inProtocolDomain kappa := by
  let q := suppressSigFinish l r
  have hframe :
      (q.1.count = l.count ∧
          PayloadView.ofState q.1 = PayloadView.ofState l) ∧
        (q.2.count = r.count ∧
          PayloadView.ofState q.2 = PayloadView.ofState r) := by
    simp only [q, suppressSigFinish]
    repeat (first | constructor | rfl | split)
  exact
    ⟨pPartialDomain_of_count_payload_eq_q5816
        l q.1 hl hframe.1.1 hframe.1.2,
      pPartialDomain_of_count_payload_eq_q5816
        r q.2 hr hframe.2.1 hframe.2.2⟩

private theorem resetHostSanitizerQ5577_inProtocolDomain_q5816
    (u : AgentState psi)
    (hu : u.inProtocolDomain kappa) :
    (resetHostSanitizerQ5577 u).inProtocolDomain kappa := by
  cases hreset : u.reset_cmd with
  | false =>
      simpa [resetHostSanitizerQ5577, hreset] using hu
  | true =>
      have hc := clearComparisonSignal_inProtocolDomain u hu
      simpa [resetHostSanitizerQ5577, hreset,
        AgentState.inProtocolDomain] using hc

/-- Numeric-domain closure of the actual raw Algorithm-14 candidate exported
by `Q5577HiddenControlAudit`. -/
theorem suppressSigHiddenControlQ5577_inProtocolDomain_q5816
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigHiddenControlQ5577 hpsi l r
    q.1.inProtocolDomain kappa ∧
      q.2.inProtocolDomain kappa := by
  let q0 := suppressSigStart l r
  have h0 := pPartialSuppressSigStart_inProtocolDomain_q5816
    l r hl hr
  change q0.1.inProtocolDomain kappa ∧
    q0.2.inProtocolDomain kappa at h0

  let q0s :=
    (resetHostSanitizerQ5577 q0.1,
      resetHostSanitizerQ5577 q0.2)
  have h0s : q0s.1.inProtocolDomain kappa ∧
      q0s.2.inProtocolDomain kappa :=
    ⟨resetHostSanitizerQ5577_inProtocolDomain_q5816 q0.1 h0.1,
      resetHostSanitizerQ5577_inProtocolDomain_q5816 q0.2 h0.2⟩

  let q1 := suppressSigMoveReset q0s.1 q0s.2
  have h1 := pPartialSuppressSigMoveReset_inProtocolDomain_q5816
    q0s.1 q0s.2 h0s.1 h0s.2
  change q1.1.inProtocolDomain kappa ∧
    q1.2.inProtocolDomain kappa at h1

  let q1s :=
    (resetHostSanitizerQ5577 q1.1,
      resetHostSanitizerQ5577 q1.2)
  have h1s : q1s.1.inProtocolDomain kappa ∧
      q1s.2.inProtocolDomain kappa :=
    ⟨resetHostSanitizerQ5577_inProtocolDomain_q5816 q1.1 h1.1,
      resetHostSanitizerQ5577_inProtocolDomain_q5816 q1.2 h1.2⟩

  let q2 := suppressSigTerminal hpsi q1s.1 q1s.2
  have h2 := pPartialSuppressSigTerminal_inProtocolDomain_q5816
    hpsi q1s.1 q1s.2 h1s.1 h1s.2
  change q2.1.inProtocolDomain kappa ∧
    q2.2.inProtocolDomain kappa at h2

  let q3 := suppressSigEcho q2.1 q2.2
  have h3 := pPartialSuppressSigEcho_inProtocolDomain_q5816
    q2.1 q2.2 h2.1 h2.2
  change q3.1.inProtocolDomain kappa ∧
    q3.2.inProtocolDomain kappa at h3

  let q4 := suppressSigFinish q3.1 q3.2
  have h4 := pPartialSuppressSigFinish_inProtocolDomain_q5816
    q3.1 q3.2 h3.1 h3.2
  change q4.1.inProtocolDomain kappa ∧
    q4.2.inProtocolDomain kappa at h4
  change q4.1.inProtocolDomain kappa ∧
    q4.2.inProtocolDomain kappa
  exact h4

/-! ## Domain closure of the actual combined suffix -/

private theorem clearAuthorizedResponderPCarryQ5577_inProtocolDomain_q5816
    (u : AuthorizedAgentState psi)
    (hu : u.core.inProtocolDomain kappa) :
    (clearAuthorizedResponderPCarryQ5577 u).core.inProtocolDomain kappa := by
  simpa [clearAuthorizedResponderPCarryQ5577,
    AgentState.inProtocolDomain] using hu

/-- The actual post-DISAPPEAR seam is numeric-domain closed. -/
theorem
    authorizedDisappearResponderPCarryOffQ5577_inProtocolDomain_q5776
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := authorizedDisappearResponderPCarryOffQ5577 hpsi l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let q0 := authorizedDisappear hpsi l r
  have h0 := authorizedReconcile_inProtocolDomain
    (disappear hpsi) l r
    (disappear_inProtocolDomain hpsi l.core r.core hl hr)
  change q0.1.core.inProtocolDomain kappa ∧
    q0.2.core.inProtocolDomain kappa at h0
  change q0.1.core.inProtocolDomain kappa ∧
    (clearAuthorizedResponderPCarryQ5577 q0.2).core.inProtocolDomain kappa
  exact
    ⟨h0.1,
      clearAuthorizedResponderPCarryQ5577_inProtocolDomain_q5816
        q0.2 h0.2⟩

/-- Every stage of the actual exported combined post-CHECK suffix
preserves the numeric domain. -/
theorem multiLeaderAfterCheckSuffixCombinedQ5577_inProtocolDomain_q5776
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := multiLeaderAfterCheckSuffixCombinedQ5577 hpsi l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let q0 := authorizedDisappearResponderPCarryOffQ5577 hpsi l r
  have h0 :=
    authorizedDisappearResponderPCarryOffQ5577_inProtocolDomain_q5776
      (kappa := kappa) hpsi l r hl hr
  change q0.1.core.inProtocolDomain kappa ∧
    q0.2.core.inProtocolDomain kappa at h0

  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  have h1 := authorizedCompareSigActionOne_inProtocolDomain
    hpsi q0.1 q0.2 h0.1 h0.2
  change q1.1.core.inProtocolDomain kappa ∧
    q1.2.core.inProtocolDomain kappa at h1

  let q2 := authorizedReconcile
    (suppressSigHiddenControlQ5577 hpsi) q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (suppressSigHiddenControlQ5577 hpsi) q1.1 q1.2
    (suppressSigHiddenControlQ5577_inProtocolDomain_q5816
      (kappa := kappa) hpsi q1.1.core q1.2.core h1.1 h1.2)
  change q2.1.core.inProtocolDomain kappa ∧
    q2.2.core.inProtocolDomain kappa at h2

  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  have h3 := authorizedReconcile_inProtocolDomain
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
    (eliminateLeadersNoCollisionEgressSink_inProtocolDomain
      hpsi q2.1.core q2.2.core h2.1 h2.2)
  change q3.1.core.inProtocolDomain kappa ∧
    q3.2.core.inProtocolDomain kappa at h3

  let q4 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have h4 := authorizedReconcile_inProtocolDomain
    (writeSeqIncrementGate hpsi) q3.1 q3.2
    (writeSeqIncrementGate_inProtocolDomain
      hpsi q3.1.core q3.2.core h3.1 h3.2)
  change q4.1.core.inProtocolDomain kappa ∧
    q4.2.core.inProtocolDomain kappa at h4
  change q4.1.core.inProtocolDomain kappa ∧
    q4.2.core.inProtocolDomain kappa
  exact h4

/-! ## Domain closure through the already compiled generic dispatcher -/

private theorem q5816_dispatcher_eq_generic
    (hpsi : psi > 0) (kappa : Nat)
    (suffix : AuthorizedAgentState psi → AuthorizedAgentState psi →
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (l r : AuthorizedAgentState psi) :
    multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577
        hpsi kappa suffix l r =
      multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
        hpsi kappa suffix l r := by
  rfl

private theorem
    multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577_inProtocolDomain_q5816
    (hpsi : psi > 0) (kappa : Nat)
    (suffix : AuthorizedAgentState psi → AuthorizedAgentState psi →
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hSuffix :
      ∀ a b : AuthorizedAgentState psi,
        a.core.inProtocolDomain kappa →
        b.core.inProtocolDomain kappa →
        let q := suffix a b
        q.1.core.inProtocolDomain kappa ∧
          q.2.core.inProtocolDomain kappa)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577
      hpsi kappa suffix l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  rw [q5816_dispatcher_eq_generic]
  exact multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_inProtocolDomain
    hpsi kappa suffix hSuffix l r hl hr

/-- Unconditional closure of the exact `P_partialAuthorized` selected by the
already compiled interface. -/
theorem P_partialAuthorized_inProtocolDomain_q5776
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := P_partialAuthorized hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  change
    let q := multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577
      hpsi kappa (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi) l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa
  exact
    multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577_inProtocolDomain_q5816
      hpsi kappa (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi)
      (fun a b ha hb =>
        multiLeaderAfterCheckSuffixCombinedQ5577_inProtocolDomain_q5776
          (kappa := kappa) hpsi a b ha hb)
      l r hl hr

/-- The first premise is discharged for every parameter choice. -/
theorem PPartialAuthorizedDomainClosure_q5776
    (hpsi : psi > 0) (kappa : Nat) :
    PPartialAuthorizedDomainClosure hpsi kappa := by
  intro l r hl hr
  exact P_partialAuthorized_inProtocolDomain_q5776
    hpsi kappa l r hl hr

/-! ## Unconditional bounded and expiring interfaces -/

/-- Bounded reification with the proved closure certificate. -/
def P_partialBoundedUnconditional
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa :=
  P_partialBounded hpsi kappa
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa) l r

/-- Exact bounded erasure, with no domain premise in the signature. -/
theorem erase_P_partialBoundedUnconditional
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := P_partialBoundedUnconditional hpsi kappa l r
    (q.1.erase, q.2.erase) =
      P_partialAuthorized hpsi kappa l.erase r.erase := by
  simpa only [P_partialBoundedUnconditional] using
    (erase_P_partialBounded hpsi kappa
      (PPartialAuthorizedDomainClosure_q5776 hpsi kappa) l r)

/-- Bounded outputs remain in the raw numeric domain unconditionally. -/
theorem P_partialBoundedUnconditional_output_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := P_partialBoundedUnconditional hpsi kappa l r
    q.1.core.erase.inProtocolDomain kappa ∧
      q.2.core.erase.inProtocolDomain kappa := by
  simpa only [P_partialBoundedUnconditional] using
    (P_partialBounded_output_inProtocolDomain
      hpsi kappa
      (PPartialAuthorizedDomainClosure_q5776 hpsi kappa) l r)

/-- Pre-expiry lift with no domain premise. -/
def P_partialExpiringBaseUnconditional
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  P_partialExpiringBase hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa) l r

/-- Exact pre-expiry authorized erasure, with no domain premise. -/
theorem erase_P_partialExpiringBaseUnconditional
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let q := P_partialExpiringBaseUnconditional
      hpsi kappa tau l r
    (q.1.core.erase, q.2.core.erase) =
      P_partialAuthorized hpsi kappa
        l.core.erase r.core.erase := by
  simpa only [P_partialExpiringBaseUnconditional] using
    (erase_P_partialExpiringBase
      hpsi kappa tau
      (PPartialAuthorizedDomainClosure_q5776 hpsi kappa) l r)

/-- Exact physical partial transition with closure internalized. -/
def P_partialUnconditional
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  P_partial hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa) l r

/-- The outer deletion/path-stall expiry equation is unchanged. -/
theorem P_partialUnconditional_expiry_exact
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    P_partialUnconditional hpsi kappa tau l r =
      let q := P_partialExpiringBaseUnconditional
        hpsi kappa tau l r
      (deletionPriorityExpireOne tau l q.1,
        deletionPriorityExpireOne tau r q.2) := by
  rfl

/-- Full expiring outputs remain in the numeric domain unconditionally. -/
theorem P_partialUnconditional_output_inProtocolDomain
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let q := P_partialUnconditional hpsi kappa tau l r
    q.1.core.erase.core.inProtocolDomain kappa ∧
      q.2.core.erase.core.inProtocolDomain kappa := by
  simpa only [P_partialUnconditional] using
    (P_partial_output_inProtocolDomain
      hpsi kappa tau
      (PPartialAuthorizedDomainClosure_q5776 hpsi kappa) l r)

/-! ## Unconditional packaged protocol -/

/-- The protocol package with domain closure discharged internally. -/
def P_partialProtocolUnconditional
    (hpsi : psi > 0) (kappa tau : Nat) : PopulationProtocol :=
  P_partialProtocol hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa)

@[simp]
theorem P_partialProtocolUnconditional_transition
    (hpsi : psi > 0) (kappa tau : Nat) :
    (P_partialProtocolUnconditional hpsi kappa tau).transition =
      P_partialUnconditional hpsi kappa tau := by
  rfl

/-- The packaged carrier remains exactly the existing expiring carrier. -/
theorem P_partialProtocolUnconditional_state_type
    (hpsi : psi > 0) (kappa tau : Nat) :
    (P_partialProtocolUnconditional hpsi kappa tau).Q =
      ExpiringAgentState psi kappa tau := by
  rfl

/-- Explicit and packaged schedule execution coincide without a domain
argument. -/
theorem P_partial_runLocalSchedule_eq_runSchedule_unconditional
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau)
    (word : DetSchedule n) :
    PPLLResearchFormulation.runLocalSchedule
        ring (P_partialUnconditional hpsi kappa tau) C word =
      PPLLResearchFormulation.runSchedule
        (P_partialProtocolUnconditional hpsi kappa tau)
        ring C word := by
  change
    PPLLResearchFormulation.runLocalSchedule
        ring
        (P_partial hpsi kappa tau
          (PPartialAuthorizedDomainClosure_q5776 hpsi kappa))
        C word =
      PPLLResearchFormulation.runSchedule
        (P_partialProtocol hpsi kappa tau
          (PPartialAuthorizedDomainClosure_q5776 hpsi kappa))
        ring C word
  exact P_partial_runLocalSchedule_eq_runSchedule
    hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa)
    ring C word

/-! ## Remaining conditional protocol obligations -/

/-- Operational legitimacy with only the proved domain premise removed. -/
abbrev PPartialLegitUnconditional
    (hpsi : psi > 0) (kappa tau : Nat)
    (C : PPartialConfig n psi kappa tau) : Prop :=
  PPartialLegit hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa) C

/-- The independent local closure/output-frame obligation. -/
abbrev PPartialLocalLegitimacyUnconditional
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) : Prop :=
  PPartialLocalLegitimacy hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa) ring

/-- The independent rank-zero/rank-one producer obligation. -/
abbrev PPartialBaseProducerUnconditional
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (baseBound : Nat) : Prop :=
  PPartialBaseProducer hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa)
    ring baseBound

/-- The independent positive strict-descent producer obligation. -/
abbrev PPartialStrictDescentProducerUnconditional
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (roundBound : Nat) : Prop :=
  PPartialStrictDescentProducer hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa)
    ring roundBound

/-- The deterministic interface with `hDomain` discharged and the three
semantic protocol premises left explicit and unchanged. -/
theorem P_partial_deterministic_interface_unconditional_domain
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (baseBound roundBound : Nat)
    (hLocal : PPartialLocalLegitimacyUnconditional
      hpsi kappa tau ring)
    (hBase : PPartialBaseProducerUnconditional
      hpsi kappa tau ring baseBound)
    (hDescent : PPartialStrictDescentProducerUnconditional
      hpsi kappa tau ring roundBound) :
    PopulationProtocol.ClosedPred
        (P_partialProtocolUnconditional hpsi kappa tau)
        ring
        (PPartialLegitUnconditional hpsi kappa tau) ∧
      (∀ C : PPartialConfig n psi kappa tau,
        PPartialLegitUnconditional hpsi kappa tau C →
        PopulationProtocol.IsSafe
          (P_partialProtocolUnconditional hpsi kappa tau)
          ring C isLeaderOutput) ∧
      (∀ C : PPartialConfig n psi kappa tau,
        ∃ word : DetSchedule n,
          word.length ≤ baseBound + n * roundBound ∧
          ReachesSafeWithinSchedule
            (P_partialProtocolUnconditional hpsi kappa tau)
            ring isLeaderOutput C word) ∧
      (P_partialStateCertificate psi kappa tau).values.length =
        (2 * (PPLLFinite.boundedAgentState
          psi kappa).values.length) * (tau + 1) := by
  exact P_partial_deterministic_interface
    hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa)
    ring baseBound roundBound hLocal hBase hDescent

end PPLLCompleteMultiLeaderCleanup

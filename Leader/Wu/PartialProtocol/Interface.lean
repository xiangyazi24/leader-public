import Leader.Wu.Elimination.MultiLeaderCleanupHiddenControl

/-!
# Compile-first partial erratum interface

This file names the compiled authorized combination
`P_partial`.  It adds no protocol state.  The finite lift is parameterized by
the exact numeric-domain closure proposition needed by `BoundedAgentState`;
this file does not assert that proposition, the local legitimacy condition, the
rank-zero/rank-one producer, or the strict-descent producer.
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

/-! ## Exact compiled authorized transition -/

/-- The actual compiled authorized transition. -/
def P_partialAuthorized
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  multiLeaderCleanupAuthorizedTransitionCombinedQ5577
    hpsi kappa l r

/-- The new name is definitionally the compiled combined transition. -/
theorem P_partialAuthorized_eq_compiled
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    P_partialAuthorized hpsi kappa l r =
      multiLeaderCleanupAuthorizedTransitionCombinedQ5577
        hpsi kappa l r := by
  rfl

/-- The imported finite regression proves that the two compiled repairs clear
responder `p_carry` but still permit the independent reset-free WAIT/GENSIG
obstruction.  Thus `P_partial` is not yet a complete mixed-tail repair. -/
theorem P_partial_combined_repairs_clear_carry_but_leave_wait_obstruction :
    remainingCombinedOutput.2.core.p_carry = false ∧
      remainingResetFreeBeforeCheck.1.core.state = .produce ∧
      remainingResetFreeBeforeCheck.1.core.wait = false ∧
      ¬ CleanupLeftTailIdle remainingResetFreeBeforeCheck.1 :=
  combined_repairs_clear_carry_but_leave_wait_obstruction

/-! ## Exact remaining third local protocol condition -/

/-- The literal GENSIG-root guard, negated at the post-WAIT/pre-GENSIG seam. -/
def PPartialPostWaitNoGenSigRoot
    (hpsi : psi > 0) (u : AgentState psi) : Prop :=
  ¬(u.leader = false ∧
    u.label = (⟨0, hpsi⟩ : Fin psi) ∧
    u.wait = false ∧
    u.path = .bot)

/-- The third local protocol obligation is needed only on the reset-free
mixed-tail branch. -/
def PPartialThirdLocalProtocolObligation
    (hpsi : psi > 0) (u : AgentState psi) : Prop :=
  u.reset_cmd = false → PPartialPostWaitNoGenSigRoot hpsi u

/-- Under the existing follower/label-zero/path-free mixed-tail facts, the
third obligation is exactly `wait = true`. -/
theorem PPartialThirdLocalProtocolObligation_iff_wait_true
    (hpsi : psi > 0) (u : AgentState psi)
    (hReset : u.reset_cmd = false)
    (hFollower : u.leader = false)
    (hZero : u.label = (⟨0, hpsi⟩ : Fin psi))
    (hPath : u.path = .bot) :
    PPartialThirdLocalProtocolObligation hpsi u ↔
      u.wait = true := by
  cases hwait : u.wait <;>
    simp [PPartialThirdLocalProtocolObligation,
      PPartialPostWaitNoGenSigRoot, hReset, hFollower,
      hZero, hPath, hwait]

/-! ## Source-valid finite lift -/

/-- The exact closure fact required to reify the compiled authorized output on
`BoundedAgentState`.  It is a transparent semantic proposition, not a claimed
result of this file. -/
def PPartialAuthorizedDomainClosure
    (hpsi : psi > 0) (kappa : Nat) : Prop :=
  ∀ l r : AuthorizedAgentState psi,
    l.core.inProtocolDomain kappa →
    r.core.inProtocolDomain kappa →
    let q := P_partialAuthorized hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa

/-- Direct projection of the explicit domain-closure premise. -/
theorem P_partialAuthorized_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := P_partialAuthorized hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  exact hDomain l r hl hr

/-- Exact bounded lift of the compiled authorized transition. -/
def P_partialBounded
    (hpsi : psi > 0) (kappa : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa :=
  let q := P_partialAuthorized hpsi kappa l.erase r.erase
  let hq := hDomain l.erase r.erase
    l.core.erase_inProtocolDomain
    r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1,
      q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2,
      q.2.path0Crossed⟩)

/-- Bounded execution erases exactly to the compiled authorized transition. -/
theorem erase_P_partialBounded
    (hpsi : psi > 0) (kappa : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := P_partialBounded hpsi kappa hDomain l r
    (q.1.erase, q.2.erase) =
      P_partialAuthorized hpsi kappa l.erase r.erase := by
  let q := P_partialAuthorized hpsi kappa l.erase r.erase
  have hq :
      q.1.core.inProtocolDomain kappa ∧
        q.2.core.inProtocolDomain kappa :=
    hDomain l.erase r.erase
      l.core.erase_inProtocolDomain
      r.core.erase_inProtocolDomain
  change
    (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
        q.1.path0Crossed⟩,
      ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
        q.2.path0Crossed⟩) = q
  rw [BoundedAgentState.erase_ofDomain,
    BoundedAgentState.erase_ofDomain]

/-- Every bounded output carries its domain certificate by construction. -/
theorem P_partialBounded_output_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := P_partialBounded hpsi kappa hDomain l r
    q.1.core.erase.inProtocolDomain kappa ∧
      q.2.core.erase.inProtocolDomain kappa := by
  let q := P_partialBounded hpsi kappa hDomain l r
  change q.1.core.erase.inProtocolDomain kappa ∧
    q.2.core.erase.inProtocolDomain kappa
  exact ⟨q.1.core.erase_inProtocolDomain,
    q.2.core.erase_inProtocolDomain⟩

/-- Expiring carrier before applying the existing endpoint expiry policy. -/
def P_partialExpiringBase
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  let q := P_partialBounded hpsi kappa hDomain l.core r.core
  (⟨q.1, l.stall⟩, ⟨q.2, r.stall⟩)

/-- The pre-expiry expiring lift has exact authorized erasure. -/
theorem erase_P_partialExpiringBase
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : ExpiringAgentState psi kappa tau) :
    let q := P_partialExpiringBase
      hpsi kappa tau hDomain l r
    (q.1.core.erase, q.2.core.erase) =
      P_partialAuthorized hpsi kappa
        l.core.erase r.core.erase := by
  simpa [P_partialExpiringBase] using
    (erase_P_partialBounded
      hpsi kappa hDomain l.core r.core)

/-- The finite physical partial repair, using the existing deletion-priority
and path-stall endpoint policy unchanged. -/
def P_partial
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  let q := P_partialExpiringBase
    hpsi kappa tau hDomain l r
  (deletionPriorityExpireOne tau l q.1,
    deletionPriorityExpireOne tau r q.2)

/-- Exact outer-wrapper equation; no false post-expiry erasure claim is made. -/
theorem P_partial_expiry_exact
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : ExpiringAgentState psi kappa tau) :
    P_partial hpsi kappa tau hDomain l r =
      let q := P_partialExpiringBase
        hpsi kappa tau hDomain l r
      (deletionPriorityExpireOne tau l q.1,
        deletionPriorityExpireOne tau r q.2) := by
  rfl

/-- Expiring outputs remain in the bounded raw domain, independently of which
expiry branch was selected. -/
theorem P_partial_output_inProtocolDomain
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : ExpiringAgentState psi kappa tau) :
    let q := P_partial hpsi kappa tau hDomain l r
    q.1.core.erase.core.inProtocolDomain kappa ∧
      q.2.core.erase.core.inProtocolDomain kappa := by
  let q := P_partial hpsi kappa tau hDomain l r
  change q.1.core.core.erase.inProtocolDomain kappa ∧
    q.2.core.core.erase.inProtocolDomain kappa
  exact ⟨q.1.core.core.erase_inProtocolDomain,
    q.2.core.core.erase_inProtocolDomain⟩

/-! ## Exact unchanged state carrier -/

/-- No field and no field value is added by `P_partial`. -/
def P_partialStateCertificate
    (psi kappa tau : Nat) :
    ExhaustiveList (ExpiringAgentState psi kappa tau) :=
  leaderCleanupStateCertificate psi kappa tau

/-- Exact carrier cardinality, unchanged from the existing expiring authorized
carrier. -/
theorem P_partialStateCertificate_values_length
    (psi kappa tau : Nat) :
    (P_partialStateCertificate psi kappa tau).values.length =
      (2 * (PPLLFinite.boundedAgentState psi kappa).values.length) *
        (tau + 1) := by
  exact leaderCleanupStateCertificate_values_length
    psi kappa tau

/-! ## Packaged execution -/

/-- Population-protocol package whose transition is definitionally
`P_partial`. -/
def P_partialProtocol
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa) :
    PopulationProtocol where
  Q := ExpiringAgentState psi kappa tau
  Y := LeaderOutput
  transition := P_partial hpsi kappa tau hDomain
  output := fun s =>
    if s.core.core.leader then .leader else .follower

abbrev PPartialConfig
    (n psi kappa tau : Nat) :=
  Fin n → ExpiringAgentState psi kappa tau

/-- Explicit execution and packaged protocol execution coincide exactly. -/
theorem P_partial_runLocalSchedule_eq_runSchedule
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau)
    (word : DetSchedule n) :
    PPLLResearchFormulation.runLocalSchedule
        ring (P_partial hpsi kappa tau hDomain) C word =
      PPLLResearchFormulation.runSchedule
        (P_partialProtocol hpsi kappa tau hDomain)
        ring C word := by
  simpa [P_partialProtocol] using
    (PPLLResearchFormulation.runLocalSchedule_eq_runSchedule
      (P_partialProtocol hpsi kappa tau hDomain)
      ring C word)

/-- `runLocalSchedule` is universe-zero because `PopulationProtocol.Q` is
universe-zero in the current repository API. -/
private theorem P_partial_runLocalSchedule_append
    {Q : Type}
    (ring : DirectedRing n)
    (T : Q → Q → Q × Q)
    (C : Fin n → Q)
    (xs ys : DetSchedule n) :
    PPLLResearchFormulation.runLocalSchedule
        ring T C (xs ++ ys) =
      PPLLResearchFormulation.runLocalSchedule
        ring T
        (PPLLResearchFormulation.runLocalSchedule
          ring T C xs) ys := by
  induction xs generalizing C with
  | nil =>
      rfl
  | cons e xs ih =>
      simp only [List.cons_append,
        PPLLResearchFormulation.runLocalSchedule]
      exact ih
        (PPLLResearchFormulation.localStep ring T C e)

/-! ## Concrete cleanup rank and local legitimacy -/

/-- One unit exactly when the physical state is a leader. -/
def P_partialLeaderMass
    (u : ExpiringAgentState psi kappa tau) : Nat :=
  if u.core.core.leader then 1 else 0

/-- Physical leader-count rank, computed over the complete finite ring. -/
def P_partialLeaderCount
    (C : PPartialConfig n psi kappa tau) : Nat :=
  (List.ofFn (fun i : Fin n => P_partialLeaderMass (C i))).sum

/-- One physical endpoint contributes at most one unit to the rank. -/
theorem P_partialLeaderMass_le_one
    (u : ExpiringAgentState psi kappa tau) :
    P_partialLeaderMass u ≤ 1 := by
  unfold P_partialLeaderMass
  split <;> omega

/-- The rank is bounded by the ring size. -/
theorem P_partialLeaderCount_le
    (C : PPartialConfig n psi kappa tau) :
    P_partialLeaderCount C ≤ n := by
  induction n with
  | zero =>
      simp [P_partialLeaderCount]
  | succ n ih =>
      rw [P_partialLeaderCount, List.ofFn_succ, List.sum_cons]
      have hhead := P_partialLeaderMass_le_one (C 0)
      have htail := ih (C := fun i : Fin n => C i.succ)
      unfold P_partialLeaderCount at htail
      have htail' :
          (List.ofFn (fun i : Fin n =>
            P_partialLeaderMass (C i.succ))).sum ≤ n := by
        simpa using htail
      omega

/-- Operational legitimacy is exactly one current leader output.  Future
stability is derived below from local closure and one-step output preservation;
it is not assumed here. -/
def PPartialLegit
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (C : PPartialConfig n psi kappa tau) : Prop :=
  UniqueLeaderOutput
    (P_partialProtocol hpsi kappa tau hDomain)
    n C isLeaderOutput

/-- Explicit local legitimacy obligation. -/
def PPartialLocalLegitimacy
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n) : Prop :=
  ∀ C : PPartialConfig n psi kappa tau,
    PPartialLegit hpsi kappa tau hDomain C →
    ∀ e : Fin n,
      let D :=
        (P_partialProtocol hpsi kappa tau hDomain).step
          ring C e
      PPartialLegit hpsi kappa tau hDomain D ∧
        ∀ i : Fin n,
          (P_partialProtocol hpsi kappa tau hDomain).output
              (D i) =
            (P_partialProtocol hpsi kappa tau hDomain).output
              (C i)

/-- The local obligation yields a closed operational predicate. -/
theorem PPartialLegit_closed
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n)
    (hLocal : PPartialLocalLegitimacy
      hpsi kappa tau hDomain ring) :
    PopulationProtocol.ClosedPred
      (P_partialProtocol hpsi kappa tau hDomain)
      ring
      (PPartialLegit hpsi kappa tau hDomain) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  exact (hLocal C hC e).1

/-- The same obligation supplies the exact one-step output frame. -/
theorem PPartialLegit_stepOutputPreserving
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n)
    (hLocal : PPartialLocalLegitimacy
      hpsi kappa tau hDomain ring) :
    StepOutputPreservingOn
      (P_partialProtocol hpsi kappa tau hDomain)
      ring
      (PPartialLegit hpsi kappa tau hDomain) := by
  intro C hC C' hstep i
  obtain ⟨e, rfl⟩ := hstep
  exact (hLocal C hC e).2 i

/-- Local operational legitimacy implies Definition-1 semantic safety. -/
theorem PPartialLegit_isSafe
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n)
    (hLocal : PPartialLocalLegitimacy
      hpsi kappa tau hDomain ring)
    (C : PPartialConfig n psi kappa tau)
    (hC : PPartialLegit hpsi kappa tau hDomain C) :
    PopulationProtocol.IsSafe
      (P_partialProtocol hpsi kappa tau hDomain)
      ring C isLeaderOutput := by
  exact isSafe_of_operational_legitimacy
    (P_partialProtocol hpsi kappa tau hDomain)
    ring isLeaderOutput
    (PPartialLegit hpsi kappa tau hDomain)
    (PPartialLegit_closed
      hpsi kappa tau hDomain ring hLocal)
    (fun _ h => h)
    (PPartialLegit_stepOutputPreserving
      hpsi kappa tau hDomain ring hLocal)
    hC

/-! ## Noncircular deterministic producer hypotheses -/

/-- Rank-zero/rank-one producer. -/
def PPartialBaseProducer
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n) (baseBound : Nat) : Prop :=
  ∀ C : PPartialConfig n psi kappa tau,
    P_partialLeaderCount C ≤ 1 →
    ∃ word : DetSchedule n,
      word.length ≤ baseBound ∧
      PPartialLegit hpsi kappa tau hDomain
        (PPLLResearchFormulation.runLocalSchedule
          ring (P_partial hpsi kappa tau hDomain)
          C word)

/-- Positive strict leader-count descent producer. -/
def PPartialStrictDescentProducer
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n) (roundBound : Nat) : Prop :=
  ∀ C : PPartialConfig n psi kappa tau,
    1 < P_partialLeaderCount C →
    ∃ word : DetSchedule n,
      word.length ≤ roundBound ∧
      0 < P_partialLeaderCount
        (PPLLResearchFormulation.runLocalSchedule
          ring (P_partial hpsi kappa tau hDomain)
          C word) ∧
      P_partialLeaderCount
        (PPLLResearchFormulation.runLocalSchedule
          ring (P_partial hpsi kappa tau hDomain)
          C word) <
        P_partialLeaderCount C

/-! ## Fuel/rank composition -/

/-- Strong induction on an explicit upper bound for the physical leader rank. -/
theorem P_partial_fuel_compose
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n)
    (baseBound roundBound fuel : Nat)
    (hBase : PPartialBaseProducer
      hpsi kappa tau hDomain ring baseBound)
    (hDescent : PPartialStrictDescentProducer
      hpsi kappa tau hDomain ring roundBound)
    (C : PPartialConfig n psi kappa tau)
    (hCount : P_partialLeaderCount C ≤ fuel) :
    ∃ word : DetSchedule n,
      word.length ≤ baseBound + fuel * roundBound ∧
      PPartialLegit hpsi kappa tau hDomain
        (PPLLResearchFormulation.runLocalSchedule
          ring (P_partial hpsi kappa tau hDomain)
          C word) := by
  induction fuel generalizing C with
  | zero =>
      have hSmall : P_partialLeaderCount C ≤ 1 := by
        omega
      obtain ⟨word, hWord, hLegit⟩ := hBase C hSmall
      refine ⟨word, ?_, hLegit⟩
      simpa using hWord
  | succ fuel ih =>
      by_cases hSmall : P_partialLeaderCount C ≤ 1
      · obtain ⟨word, hWord, hLegit⟩ := hBase C hSmall
        refine ⟨word, ?_, hLegit⟩
        exact Nat.le_trans hWord
          (Nat.le_add_right baseBound
            (Nat.succ fuel * roundBound))
      · have hLarge : 1 < P_partialLeaderCount C := by
          omega
        obtain ⟨head, hHead, _hPositive, hDrop⟩ :=
          hDescent C hLarge
        let D :=
          PPLLResearchFormulation.runLocalSchedule
            ring (P_partial hpsi kappa tau hDomain)
            C head
        have hDropD :
            P_partialLeaderCount D <
              P_partialLeaderCount C := by
          simpa [D] using hDrop
        have hDCount : P_partialLeaderCount D ≤ fuel := by
          omega
        obtain ⟨tail, hTail, hLegit⟩ := ih D hDCount
        refine ⟨head ++ tail, ?_, ?_⟩
        · simp only [List.length_append]
          calc
            head.length + tail.length ≤
                roundBound +
                  (baseBound + fuel * roundBound) :=
              Nat.add_le_add hHead hTail
            _ = baseBound + Nat.succ fuel * roundBound := by
              simp [Nat.succ_mul, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm]
        · rw [P_partial_runLocalSchedule_append]
          simpa [D] using hLegit

/-- The rank bound `P_partialLeaderCount C ≤ n` removes explicit fuel. -/
theorem P_partial_exists_legit_schedule
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n)
    (baseBound roundBound : Nat)
    (hBase : PPartialBaseProducer
      hpsi kappa tau hDomain ring baseBound)
    (hDescent : PPartialStrictDescentProducer
      hpsi kappa tau hDomain ring roundBound)
    (C : PPartialConfig n psi kappa tau) :
    ∃ word : DetSchedule n,
      word.length ≤ baseBound + n * roundBound ∧
      PPartialLegit hpsi kappa tau hDomain
        (PPLLResearchFormulation.runLocalSchedule
          ring (P_partial hpsi kappa tau hDomain)
          C word) := by
  exact P_partial_fuel_compose
    hpsi kappa tau hDomain ring
    baseBound roundBound n
    hBase hDescent C
    (P_partialLeaderCount_le C)

/-- Deterministic partial-erratum interface.  Every protocol-specific premise
is explicit; none is proved by this theorem. -/
theorem P_partial_deterministic_interface
    (hpsi : psi > 0) (kappa tau : Nat)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (ring : DirectedRing n)
    (baseBound roundBound : Nat)
    (hLocal : PPartialLocalLegitimacy
      hpsi kappa tau hDomain ring)
    (hBase : PPartialBaseProducer
      hpsi kappa tau hDomain ring baseBound)
    (hDescent : PPartialStrictDescentProducer
      hpsi kappa tau hDomain ring roundBound) :
    PopulationProtocol.ClosedPred
        (P_partialProtocol hpsi kappa tau hDomain)
        ring
        (PPartialLegit hpsi kappa tau hDomain) ∧
      (∀ C : PPartialConfig n psi kappa tau,
        PPartialLegit hpsi kappa tau hDomain C →
        PopulationProtocol.IsSafe
          (P_partialProtocol hpsi kappa tau hDomain)
          ring C isLeaderOutput) ∧
      (∀ C : PPartialConfig n psi kappa tau,
        ∃ word : DetSchedule n,
          word.length ≤ baseBound + n * roundBound ∧
          ReachesSafeWithinSchedule
            (P_partialProtocol hpsi kappa tau hDomain)
            ring isLeaderOutput C word) ∧
      (P_partialStateCertificate psi kappa tau).values.length =
        (2 * (PPLLFinite.boundedAgentState
          psi kappa).values.length) * (tau + 1) := by
  refine ⟨PPartialLegit_closed
      hpsi kappa tau hDomain ring hLocal, ?_, ?_, ?_⟩
  · intro C hC
    exact PPartialLegit_isSafe
      hpsi kappa tau hDomain ring hLocal C hC
  · intro C
    obtain ⟨word, hWord, hLegit⟩ :=
      P_partial_exists_legit_schedule
        hpsi kappa tau hDomain ring
        baseBound roundBound hBase hDescent C
    have hSafe :
        PopulationProtocol.IsSafe
          (P_partialProtocol hpsi kappa tau hDomain)
          ring
          (PPLLResearchFormulation.runLocalSchedule
            ring (P_partial hpsi kappa tau hDomain)
            C word)
          isLeaderOutput :=
      PPartialLegit_isSafe
        hpsi kappa tau hDomain ring hLocal
        _ hLegit
    refine ⟨word, hWord, ?_⟩
    refine ⟨word.length, Nat.le_refl word.length, ?_⟩
    simp only [List.take_length]
    rw [← P_partial_runLocalSchedule_eq_runSchedule
      hpsi kappa tau hDomain ring C word]
    exact hSafe
  · exact P_partialStateCertificate_values_length
      psi kappa tau

end PPLLCompleteMultiLeaderCleanup

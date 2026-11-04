import Leader.Wu.Safety.SuppressionHistory
import Leader.Wu.Scheduler.Probability

/-!
# Corrected statement layer for finite P_PLL research candidates

Wu's five-field `safe configuration` is not closed under the audited
transition.  The correct mathematical target is Wu's earlier Definition 1
(printed p.8 / PDF p.21): a configuration with one leader output whose entire
reachable future has the same output vector. Operational predicates about signals, bullets,
and writes are proof devices that must imply this semantic target; they are not
allowed to replace it.

This file states that target, gives it exact finite-scheduler semantics, and
separates the finite physical candidate from the finite historical-receipt
refinement used to reason about Algorithm 14.  It deliberately proves no P_PLL
convergence claim.
-/

namespace PPLLResearchFormulation

/-! ## Minimal operational parameter regime -/

/-- Parameters under which the current research transition has an ordinary
non-self ring edge and a nonempty label type.  The `1 < n` premise is forced by
T10's self-edge ambiguity; no asymptotic `ψ = ⌈log log n⌉ + O(1)` claim is hidden
in this finite-instance structure. -/
structure OperationalRegime (n ψ : Nat) where
  ring : DirectedRing n
  hψ : ψ > 0
  nontrivial : 1 < n

/-- Positive knowledge and a nontrivial ring size construct the regime used by
the family statement; its universal regime quantifier is therefore inhabited. -/
theorem operationalRegime_of (hψ : ψ > 0) (hn : 1 < n) :
    OperationalRegime n ψ where
  ring := ⟨by omega⟩
  hψ := hψ
  nontrivial := hn

/-- A concrete witness that the operational regime is satisfiable. -/
theorem regimeFourTwo : OperationalRegime 4 2 where
  ring := ⟨by omega⟩
  hψ := by omega
  nontrivial := by omega

/-! ## Semantic safety for leader election -/

/-- Exactly one agent currently emits the designated leader output, the first
clause of Wu's Definition 1 (printed p.8 / PDF p.21). -/
def UniqueLeaderOutput (P : PopulationProtocol) (n : Nat)
    (C : P.Configuration n) (isLeader : P.Y → Bool) : Prop :=
  ∃ i : Fin n, isLeader (P.output (C i)) = true ∧
    ∀ j : Fin n, isLeader (P.output (C j)) = true → j = i

/-- Every configuration reachable from `C` has the same pointwise output
vector as `C`, the second clause of Wu's Definition 1 (printed p.8 / PDF p.21).
This is stabilization of outputs, not quiescence of auxiliary protocol fields. -/
def OutputStableFrom (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) : Prop :=
  ∀ C', PopulationProtocol.Reachable P ring C C' →
    ∀ i : Fin n, P.output (C' i) = P.output (C i)

/-- The abstract framework's `IsSafe` is exactly unique leader output plus
future output stability. -/
theorem isSafe_iff_unique_and_outputStable
    (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (isLeader : P.Y → Bool) :
    PopulationProtocol.IsSafe P ring C isLeader ↔
      UniqueLeaderOutput P n C isLeader ∧ OutputStableFrom P ring C := by
  rfl

/-- Semantic leader-election safety is closed for every protocol.  The proof
uses transitivity of reachability: a future of a safe successor is already a
future of the original safe configuration.  This theorem does not say that any
particular protocol can reach such a configuration. -/
theorem isSafe_closed (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) :
    PopulationProtocol.ClosedPred P ring
      (fun C => PopulationProtocol.IsSafe P ring C isLeader) := by
  intro C hsafe C' hstep
  rcases hsafe with ⟨⟨leader, hleader, hunique⟩, hstable⟩
  have hreach : PopulationProtocol.Reachable P ring C C' :=
    PopulationProtocol.OneStep.to_reachable hstep
  have hout : ∀ i : Fin n, P.output (C' i) = P.output (C i) :=
    hstable C' hreach
  constructor
  · refine ⟨leader, ?_, ?_⟩
    · rw [hout leader]
      exact hleader
    · intro j hj
      rw [hout j] at hj
      exact hunique j hj
  · intro C'' hfuture i
    have hfromC : PopulationProtocol.Reachable P ring C C'' :=
      hreach.trans hfuture
    exact (hstable C'' hfromC i).trans (hout i).symm

/-! ## Honest operational route to semantic safety -/

/-- Every one-step transition inside an operational legitimate set preserves
all agent outputs.  This is a local transition obligation, strictly weaker
than assuming future output stability as a premise. -/
def StepOutputPreservingOn (P : PopulationProtocol) (ring : DirectedRing n)
    (Legit : P.Configuration n → Prop) : Prop :=
  ∀ C, Legit C → ∀ C', PopulationProtocol.OneStep P ring C C' →
    ∀ i : Fin n, P.output (C' i) = P.output (C i)

private theorem output_eq_of_reachable_from_legit
    (P : PopulationProtocol) (ring : DirectedRing n)
    (Legit : P.Configuration n → Prop)
    (hclosed : PopulationProtocol.ClosedPred P ring Legit)
    (hstep : StepOutputPreservingOn P ring Legit)
    {C C' : P.Configuration n} (hC : Legit C)
    (hreach : PopulationProtocol.Reachable P ring C C') :
    ∀ i : Fin n, P.output (C' i) = P.output (C i) := by
  induction hreach
  · intro i
    rfl
  · rename_i C₂ C₃ _ hone ih
    have hC₂ : Legit C₂ := hclosed.reachable hC ‹_›
    intro i
    exact (hstep C₂ hC₂ C₃ hone i).trans (ih i)

/-- A closed operational predicate with a unique leader output and local
one-step output preservation implies Wu's semantic Definition-1 safety.  This
is the noncircular interface a repaired signal/bullet/write invariant must
instantiate; no such instantiation for integrated P_PLL is claimed here. -/
theorem isSafe_of_operational_legitimacy
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (Legit : P.Configuration n → Prop)
    (hclosed : PopulationProtocol.ClosedPred P ring Legit)
    (hunique : ∀ C, Legit C → UniqueLeaderOutput P n C isLeader)
    (hstep : StepOutputPreservingOn P ring Legit)
    {C : P.Configuration n} (hC : Legit C) :
    PopulationProtocol.IsSafe P ring C isLeader := by
  exact ⟨hunique C hC,
    fun C' hreach => output_eq_of_reachable_from_legit
      P ring Legit hclosed hstep hC hreach⟩

/-! ## Non-vacuity witness for the semantic target -/

/-- A two-output identity protocol used only to show that semantic leader-
election safety is inhabited and not an impossible interface. -/
def identityOutputProtocol : PopulationProtocol where
  Q := LeaderOutput
  Y := LeaderOutput
  transition := fun l r => (l, r)
  output := fun q => q

/-- Canonical output configuration with its index-zero agent as sole leader. -/
def canonicalLeaderOutputConfig (ring : DirectedRing n) :
    identityOutputProtocol.Configuration n :=
  fun i => if i = (⟨0, ring.hn⟩ : Fin n) then .leader else .follower

private theorem identityOutputProtocol_step
    (ring : DirectedRing n)
    (C : identityOutputProtocol.Configuration n) (e : Fin n) :
    identityOutputProtocol.step ring C e = C := by
  funext k
  unfold PopulationProtocol.step identityOutputProtocol
  change (if k = e then C e
    else if k = ring.rightNeighbor e then C (ring.rightNeighbor e) else C k) = C k
  split
  · next h => subst k; rfl
  · split
    · next h => subst k; rfl
    · rfl

private theorem identityOutputProtocol_reachable_eq
    (ring : DirectedRing n)
    {C C' : identityOutputProtocol.Configuration n}
    (h : PopulationProtocol.Reachable identityOutputProtocol ring C C') :
    C' = C := by
  induction h
  · rfl
  · rename_i C₂ C₃ _ hone ih
    obtain ⟨e, rfl⟩ := hone
    rw [identityOutputProtocol_step, ih]

/-- The canonical configuration is genuinely safe.  This witnesses joint
satisfiability of unique-leader output and future output stability independently
of any P_PLL correctness claim. -/
theorem canonicalLeaderOutputConfig_isSafe (ring : DirectedRing n) :
    PopulationProtocol.IsSafe identityOutputProtocol ring
      (canonicalLeaderOutputConfig ring) isLeaderOutput := by
  constructor
  · refine ⟨⟨0, ring.hn⟩, ?_, ?_⟩
    · simp [canonicalLeaderOutputConfig, identityOutputProtocol, isLeaderOutput]
    · intro j hj
      by_cases hzero : j = (⟨0, ring.hn⟩ : Fin n)
      · exact hzero
      · simp [canonicalLeaderOutputConfig, identityOutputProtocol,
          isLeaderOutput, hzero] at hj
  · intro C' hreach i
    rw [identityOutputProtocol_reachable_eq ring hreach]

/-! ## Generic deterministic and finite-uniform schedule semantics -/

/-- Apply one edge using an explicitly supplied local transition.  This
representation is useful for refinement proofs because its state type is not
hidden behind a dependent protocol projection. -/
def localStep {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (e : Fin n) : Fin n → Q :=
  let j := ring.rightNeighbor e
  let q := T (C e) (C j)
  fun k => if k = e then q.1 else if k = j then q.2 else C k

/-- Execute a schedule under an explicitly supplied local transition. -/
def runLocalSchedule {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (C : Fin n → Q) : DetSchedule n → Fin n → Q
  | [] => C
  | e :: rest => runLocalSchedule ring T (localStep ring T C e) rest

/-- The explicit local step is definitionally the abstract protocol step. -/
theorem localStep_eq_protocol_step (P : PopulationProtocol)
    (ring : DirectedRing n) (C : P.Configuration n) (e : Fin n) :
    localStep ring P.transition C e = P.step ring C e := by
  rfl

/-- Execute a list of directed-ring edges for an arbitrary population
protocol. -/
def runSchedule (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) : DetSchedule n → P.Configuration n
  | [] => C
  | e :: rest => runSchedule P ring (P.step ring C e) rest

/-- Explicit-transition schedules and protocol schedules coincide. -/
theorem runLocalSchedule_eq_runSchedule (P : PopulationProtocol)
    (ring : DirectedRing n) (C : P.Configuration n) (s : DetSchedule n) :
    runLocalSchedule ring P.transition C s = runSchedule P ring C s := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
    simp only [runLocalSchedule, runSchedule]
    rw [localStep_eq_protocol_step, ih]

/-- Every deterministic schedule produces a configuration reachable from its
initial configuration. -/
theorem runSchedule_reachable (P : PopulationProtocol)
    (ring : DirectedRing n) (C : P.Configuration n) (s : DetSchedule n) :
    PopulationProtocol.Reachable P ring C (runSchedule P ring C s) := by
  induction s generalizing C with
  | nil => exact .refl C
  | cons e rest ih =>
    exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans
      (ih (P.step ring C e))

/-- A finite schedule succeeds when some prefix reaches genuine semantic
leader-election safety. -/
def ReachesSafeWithinSchedule (P : PopulationProtocol)
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (C : P.Configuration n) (s : DetSchedule n) : Prop :=
  ∃ k : Nat, k ≤ s.length ∧
    PopulationProtocol.IsSafe P ring
      (runSchedule P ring C (s.take k)) isLeader

/-- Exact number of length-`t` uniform scheduler outcomes that reach semantic
safety.  Classical decidability is used only to count the finite list; no
compiler-trusted reduction or probability axiom is involved. -/
noncomputable def stabilizingScheduleCount (P : PopulationProtocol)
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (C : P.Configuration n) (t : Nat) : Nat := by
  classical
  exact (allSchedules n t).countP (fun s =>
    if ReachesSafeWithinSchedule P ring isLeader C s then true else false)

/-- Honest finite-horizon uniform-scheduler formulation.  `allowedFailures`
is a count of scheduler outcomes, so the asserted failure probability is at
most `allowedFailures / n^t`.  Unlike `ReachSpec`, this proposition quantifies
over every initial configuration and asks for genuine semantic safety. -/
def UniformFiniteHorizonSSLE (P : PopulationProtocol)
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (t allowedFailures : Nat) : Prop :=
  ∀ C : P.Configuration n,
    (allSchedules n t).length ≤
      stabilizingScheduleCount P ring isLeader C t + allowedFailures

/-- Pointwise `c/n`-shaped failure bound at a positive horizon.  Since there
are `n^t` outcomes, `c*n^(t-1)` bad outcomes correspond to probability at most
`c/n`; `c<n` prevents the budget from covering every outcome. An asymptotic
theorem must additionally quantify fixed `c` and a
parameter family for all sufficiently large `n`; this finite statement does
not smuggle in that missing layer. -/
def UniformOneOverNFailureAtHorizon (P : PopulationProtocol)
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (c t : Nat) : Prop :=
  c < n ∧ 0 < t ∧
    UniformFiniteHorizonSSLE P ring isLeader t (c * n ^ (t - 1))

/-- Under the explicit side conditions, the `c/n` failure allowance is
strictly smaller than the full schedule space. Thus the specialized statement
cannot be satisfied merely by spending a budget on every outcome. -/
theorem oneOverNFailure_budget_lt_total (ring : DirectedRing n)
    (c t : Nat) (hc : c < n) (ht : 0 < t) :
    c * n ^ (t - 1) < (allSchedules n t).length := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hp : 0 < n ^ k := Nat.pow_pos ring.hn
  have hmul : c * n ^ k < n * n ^ k :=
    (Nat.mul_lt_mul_right hp).2 hc
  simpa [allSchedules_length, Nat.pow_succ, Nat.mul_comm] using hmul

/-! ## Physical candidate versus proof refinement -/

/-- The finite physical protocol for the current integrated research
candidate.  Its local state has no historical reset-receipt bit. -/
abbrev physicalProtocol {n ψ : Nat} (regime : OperationalRegime n ψ)
    (κ : Nat) : PopulationProtocol :=
  PPLLRepair.integratedBoundedProtocol regime.hψ κ

/-- Constructive finite-state certificate for the physical candidate. -/
def physicalStateCertificate {n ψ : Nat}
    (regime : OperationalRegime n ψ) (κ : Nat) :
    ExhaustiveList (physicalProtocol regime κ).Q :=
  PPLLRepair.integratedBoundedProtocolStateCertificate regime.hψ κ

/-- The finite proof refinement carrying historical Algorithm-14 receipt.
Its extra Boolean is ghost history and must not be counted as a field of the
physical P_PLL candidate. -/
abbrev receiptProtocol {n ψ : Nat} (regime : OperationalRegime n ψ)
    (κ : Nat) : PopulationProtocol :=
  PPLLSuppressionHistory.boundedProtocol regime.hψ κ

/-- Constructive finite-state certificate for the receipt refinement. -/
def receiptStateCertificate {n ψ : Nat}
    (_regime : OperationalRegime n ψ) (κ : Nat) :
    ExhaustiveList (PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ) :=
  PPLLSuppressionHistory.boundedReceiptCertificate ψ κ

/-- Canonical lift of an arbitrary physical state at the beginning of a
receipt-tracking phase.  No agent is credited with a pre-phase receipt. -/
def freshReceiptState {ψ κ : Nat} (s : BoundedAgentState ψ κ) :
    PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ where
  concrete := s
  receivedReset := false

/-- Pointwise canonical lift of an arbitrary physical configuration. -/
def freshReceiptConfig {ψ κ n : Nat}
    (C : Fin n → BoundedAgentState ψ κ) :
    Fin n → PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ :=
  fun i => freshReceiptState (C i)

/-- Pointwise erasure from the receipt refinement to physical state. -/
def eraseReceiptConfig {ψ κ n : Nat}
    (C : Fin n → PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ) :
    Fin n → BoundedAgentState ψ κ :=
  fun i => (C i).concrete

/-- The canonical phase-start lift erases to the arbitrary physical input. -/
theorem erase_freshReceiptConfig {ψ κ n : Nat}
    (C : Fin n → BoundedAgentState ψ κ) :
    eraseReceiptConfig (freshReceiptConfig C) = C := by
  rfl

/-- Every agent has received a reset command since the beginning of the
refined phase.  Unlike the old `reset_cmd=true` snapshot, this predicate refers
to a monotone proof-history bit. -/
def AllReceivedReset {ψ κ n : Nat}
    (C : Fin n → PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ) : Prop :=
  ∀ i, (C i).receivedReset = true

/-- The canonical phase-start lift assigns no fictitious historical receipt. -/
theorem freshReceiptConfig_unreceived {ψ κ n : Nat}
    (C : Fin n → BoundedAgentState ψ κ) :
    ∀ i, (freshReceiptConfig C i).receivedReset = false := by
  intro i
  rfl

/-- Historical reset completion is preserved by every refined protocol step. -/
theorem allReceivedReset_preserved_step {n ψ : Nat}
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : Fin n → PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ)
    (hC : AllReceivedReset C) (e : Fin n) :
    AllReceivedReset ((receiptProtocol regime κ).step regime.ring C e) := by
  have hl := PPLLSuppressionHistory.boundedTransition_left_received
    regime.hψ κ (C e) (C (regime.ring.rightNeighbor e)) (hC e)
  have hr := PPLLSuppressionHistory.boundedTransition_right_received
    regime.hψ κ (C e) (C (regime.ring.rightNeighbor e))
      (hC (regime.ring.rightNeighbor e))
  intro k
  by_cases hke : k = e
  · simp only [PopulationProtocol.step, receiptProtocol,
      PPLLSuppressionHistory.boundedProtocol, if_pos hke]
    exact hl
  · by_cases hkj : k = regime.ring.rightNeighbor e
    · simp only [PopulationProtocol.step, receiptProtocol,
        PPLLSuppressionHistory.boundedProtocol, if_neg hke, if_pos hkj]
      exact hr
    · simp only [PopulationProtocol.step, receiptProtocol,
        PPLLSuppressionHistory.boundedProtocol, if_neg hke, if_neg hkj]
      exact hC k

/-- One refined interaction erases exactly to one physical interaction of the
integrated candidate. -/
theorem eraseReceipt_step {n ψ : Nat} (regime : OperationalRegime n ψ)
    (κ : Nat)
    (C : Fin n → PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ)
    (e : Fin n) :
    eraseReceiptConfig
        ((receiptProtocol regime κ).step regime.ring C e) =
      (physicalProtocol regime κ).step regime.ring
        (eraseReceiptConfig C) e := by
  funext k
  unfold PopulationProtocol.step
  simp only [receiptProtocol, physicalProtocol,
    PPLLSuppressionHistory.boundedProtocol,
    PPLLRepair.integratedBoundedProtocol, eraseReceiptConfig]
  have ht := PPLLSuppressionHistory.erase_boundedTransition
    regime.hψ κ (C e) (C (regime.ring.rightNeighbor e))
  split
  · exact congrArg Prod.fst ht
  · split
    · exact congrArg Prod.snd ht
    · rfl

/-- Erasure commutes with one explicit local step of the receipt refinement. -/
theorem eraseReceipt_localStep {n ψ : Nat}
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : Fin n → PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ)
    (e : Fin n) :
    eraseReceiptConfig (localStep regime.ring
        (PPLLSuppressionHistory.boundedTransition regime.hψ κ) C e) =
      localStep regime.ring
        (PPLLRepair.integratedBoundedTransition regime.hψ κ)
        (eraseReceiptConfig C) e := by
  funext k
  unfold localStep
  simp only [eraseReceiptConfig]
  have ht := PPLLSuppressionHistory.erase_boundedTransition
    regime.hψ κ (C e) (C (regime.ring.rightNeighbor e))
  split
  · exact congrArg Prod.fst ht
  · split
    · exact congrArg Prod.snd ht
    · rfl

/-- Erasure commutes with every finite refined schedule, so historical receipt
can be used in a proof without changing physical execution. -/
theorem eraseReceipt_runSchedule {n ψ : Nat}
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : Fin n → PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ)
    (s : DetSchedule n) :
    eraseReceiptConfig
        (runLocalSchedule regime.ring
          (PPLLSuppressionHistory.boundedTransition regime.hψ κ) C s) =
      runLocalSchedule regime.ring
        (PPLLRepair.integratedBoundedTransition regime.hψ κ)
        (eraseReceiptConfig C) s := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
    simp only [runLocalSchedule]
    rw [ih]
    rw [eraseReceipt_localStep regime κ C e]

/-- Whole-schedule erasure also holds for the packaged population protocols,
not only the explicit local-transition presentation. -/
theorem eraseReceipt_protocolSchedule {n ψ : Nat}
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : Fin n → PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ)
    (s : DetSchedule n) :
    eraseReceiptConfig
        (runSchedule (PPLLSuppressionHistory.boundedProtocol regime.hψ κ)
          regime.ring C s) =
      runSchedule (PPLLRepair.integratedBoundedProtocol regime.hψ κ)
        regime.ring (eraseReceiptConfig C) s := by
  have hr := runLocalSchedule_eq_runSchedule
    (PPLLSuppressionHistory.boundedProtocol regime.hψ κ) regime.ring C s
  have hp := runLocalSchedule_eq_runSchedule
    (PPLLRepair.integratedBoundedProtocol regime.hψ κ) regime.ring
    (eraseReceiptConfig C) s
  rw [← hr, ← hp]
  exact eraseReceipt_runSchedule regime κ C s

/-- Outputs of the proof refinement are exactly physical outputs. -/
theorem receipt_output_eq_physical {n ψ : Nat}
    (regime : OperationalRegime n ψ) (κ : Nat)
    (s : PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ) :
    (receiptProtocol regime κ).output s =
      (physicalProtocol regime κ).output s.concrete := by
  rfl

/-! ## The corrected finite candidate statement -/

/-- Exact non-vacuous finite-scheduler bound for one integrated physical
candidate. This is one fixed-size probability statement, not yet an asymptotic
SSLE theorem. Historical receipt may be used through the exact refinement
above, but the target remains output safety of the physical protocol. -/
def IntegratedCandidateFiniteBound {n ψ : Nat}
    (regime : OperationalRegime n ψ) (κ c t : Nat) : Prop :=
  UniformOneOverNFailureAtHorizon (physicalProtocol regime κ)
    regime.ring isLeaderOutput c t

/-- Family-level high-probability formulation with the essential quantifier
order: the protocol parameters are fixed functions, and one constant `c` is
chosen before all sufficiently large ring sizes. Positivity of `ψ n` is an
explicit conjunct, so a zero-label family cannot make the statement vacuous by
leaving `OperationalRegime n (ψ n)` empty.

This still states only the probabilistic stabilization layer. A faithful
analogue of Theorem 4.1.13 must separately bound `horizon`, relate `ψ` to
knowledge of `n`, constrain `κ`, and bound the physical carrier cardinality. -/
def IntegratedCandidateWHPFamily
    (ψ κ horizon : Nat → Nat) : Prop :=
  ∃ c N : Nat, 1 < N ∧ c < N ∧
    ∀ n : Nat, N ≤ n →
      ψ n > 0 ∧
      ∀ regime : OperationalRegime n (ψ n),
        IntegratedCandidateFiniteBound regime (κ n) c (horizon n)

/-- A natural-valued function is eventually bounded by a constant multiple of
another. This generic arithmetic layer makes runtime/state asymptotics explicit
without pretending that the repository already has a faithful `log log n`
encoding. -/
def EventuallyBoundedBy (f g : Nat → Nat) : Prop :=
  ∃ K N : Nat, 0 < K ∧ ∀ n : Nat, N ≤ n → f n ≤ K * g n

end PPLLResearchFormulation

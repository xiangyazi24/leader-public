import Leader.Wu.PartialProtocol.DomainClosure
import Leader.Wu.Safety.NoCheckBirthOutputLegitimacy
import Leader.Wu.Safety.NoCheckBirthRegression
import Leader.Wu.Scheduler.RepeatedBlocks

/-!
# One-bit output lock for `P_partial`

`P_partial` retains the source-level first-leader writers, but the exact
six-agent counterexample shows that it can later migrate the sole leader.
Removing CHECK births avoids that migration only by introducing an unbounded
leaderless trap.  This file instead adds one Boolean dissemination lock and
makes the existing P'_psi barrier/probe birth an atomic lock-seeding branch.
Every other unlocked pair still executes the exact `P_partial` transition.

An endpoint that is already locked, or an endpoint that currently holds a
leader, freezes the physical pair and sets both locks.  On an unlocked
follower/follower barrier/probe pair, the exact P'_psi source writer runs and
both endpoints lock before a later suffix can move the newborn.  Every other
unlocked pair runs exact `P_partial`; if that step creates a leader, both
outputs lock.  Consequently a newborn or pre-existing leader can seed a
clockwise lock flood without moving any physical state.  Once every endpoint
is locked, every interaction is the identity, which is stronger than the
pointwise output frame required by Definition 1.

The added bit can be stale in an arbitrary initial state.  More strongly,
every pre-existing leader is frozen whenever one of its incident interactions
occurs, and every all-locked configuration is physically fixed.  Thus this
transition is not arbitrary-state self-stabilizing: all-locked leaderless and
multi-leader states are closed unsafe traps.  The results below prove only the
conditional post-election layer from a configuration that already has a unique
leader and at least one lock seed; the lock flood from such a seed is proved
inside this file.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialMinimalLockRepairSol

open PPLL PPLLResearchFormulation
  PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthOutputLegitimacy
  PPLLNoCheckBirthConditionTwoGeometry

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Carrier and transition -/

/-- The exact current finite `P_partial` carrier with one dissemination bit.
The Boolean is protocol state, not proof-only history. -/
abbrev MinimalLockState (psi kappa tau : Nat) :=
  ExpiringAgentState psi kappa tau × Bool

/-- Physical leader bit of a lock-augmented state. -/
def minimalLockLeader
    (u : MinimalLockState psi kappa tau) : Bool :=
  u.1.core.core.leader

/-- A local lock is activated by either an existing lock or an existing
leader.  Existing leaders are included so that the first interaction touching
one seeds dissemination without first executing a migrating `P_partial` step. -/
def MinimalLockTrigger
    (l r : MinimalLockState psi kappa tau) : Prop :=
  l.2 = true ∨ r.2 = true ∨
    minimalLockLeader l = true ∨ minimalLockLeader r = true

/-- Whether an unlocked physical `P_partial` result contains a leader. -/
def minimalLockPairHasLeader
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Bool :=
  q.1.core.core.leader || q.2.core.core.leader

/-- The existing P'_psi first-leader writer: a responder probe returns across
a label barrier.  This guard is inspected only after `MinimalLockTrigger` is
false, so both endpoints are unlocked followers at the branch point. -/
def MinimalLockBirthGuard
    (hpsi : psi > 0)
    (l r : MinimalLockState psi kappa tau) : Prop :=
  r.1.core.core.probe = true ∧
    isBarrier hpsi l.1.core.core.erase r.1.core.core.erase

instance minimalLockTriggerDecidable
    (l r : MinimalLockState psi kappa tau) :
    Decidable (MinimalLockTrigger l r) := by
  unfold MinimalLockTrigger
  infer_instance

instance minimalLockBirthGuardDecidable
    (hpsi : psi > 0)
    (l r : MinimalLockState psi kappa tau) :
    Decidable (MinimalLockBirthGuard hpsi l r) := by
  unfold MinimalLockBirthGuard isBarrier
  infer_instance

/-- Finite-by-construction lift of the exact source P'_psi writer.  It keeps
authorization and stall data at their original endpoints and reifies only the
two raw P'_psi outputs. -/
def minimalLockPPsiPhysical
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  let q := pPsi hpsi l.core.core.erase r.core.core.erase
  let hq := pPsi_inProtocolDomain hpsi
    l.core.core.erase r.core.core.erase
    l.core.core.erase_inProtocolDomain
    r.core.core.erase_inProtocolDomain
  (⟨⟨BoundedAgentState.ofDomain q.1 hq.1,
      l.core.path0Crossed⟩, l.stall⟩,
    ⟨⟨BoundedAgentState.ofDomain q.2 hq.2,
      r.core.path0Crossed⟩, r.stall⟩)

/-- Source-shaped one-bit repair.  Triggered pairs freeze physically and
spread the lock.  The source P'_psi birth is intercepted atomically and seeds
the lock.  Every remaining unlocked follower/follower pair delegates to the
exact unconditional `P_partial`; a leader created by that real step also seeds
the lock on both endpoints. -/
def P_partialMinimalLock
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : MinimalLockState psi kappa tau) :
    MinimalLockState psi kappa tau ×
      MinimalLockState psi kappa tau :=
  if MinimalLockTrigger l r then
    ((l.1, true), (r.1, true))
  else if MinimalLockBirthGuard hpsi l r then
    let q := minimalLockPPsiPhysical hpsi kappa tau l.1 r.1
    ((q.1, true), (q.2, true))
  else
    let q := P_partialUnconditional hpsi kappa tau l.1 r.1
    let locked := minimalLockPairHasLeader q
    ((q.1, locked), (q.2, locked))

/-- Packaged protocol.  Output ignores the new bit and remains exactly the
physical leader field. -/
def P_partialMinimalLockProtocol
    (hpsi : psi > 0) (kappa tau : Nat) : PopulationProtocol where
  Q := MinimalLockState psi kappa tau
  Y := LeaderOutput
  transition := P_partialMinimalLock hpsi kappa tau
  output := fun s =>
    if minimalLockLeader s then LeaderOutput.leader
    else LeaderOutput.follower

abbrev MinimalLockConfig
    (n psi kappa tau : Nat) :=
  Fin n → MinimalLockState psi kappa tau

/-! ## A concrete rank-zero first-birth route -/

/-- The finite P'_psi lift preserves its responder birth exactly. -/
theorem minimalLockPPsiPhysical_responder_birth
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.core.erase.leader = false)
    (hr : r.core.core.erase.leader = false)
    (hprobe : r.core.core.erase.probe = true)
    (hbarrier : isBarrier hpsi
      l.core.core.erase r.core.core.erase) :
    (minimalLockPPsiPhysical hpsi kappa tau l r).2.core.core.leader =
      true := by
  have hraw :
      (pPsi hpsi l.core.core.erase r.core.core.erase).2.leader = true := by
    unfold isBarrier at hbarrier
    simp [pPsi, hbarrier, hprobe]
  change (pPsi hpsi l.core.core.erase r.core.core.erase).2.leader = true
  exact hraw

/-- An untriggered source barrier/probe event produces a real responder
leader and atomically locks both endpoints. -/
theorem P_partialMinimalLock_of_birthGuard
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : MinimalLockState psi kappa tau)
    (htrigger : ¬ MinimalLockTrigger l r)
    (hbirth : MinimalLockBirthGuard hpsi l r) :
    let q := P_partialMinimalLock hpsi kappa tau l r
    q.1.2 = true ∧ q.2.2 = true ∧
      minimalLockLeader q.2 = true := by
  have hl : l.1.core.core.erase.leader = false := by
    change minimalLockLeader l = false
    cases h : minimalLockLeader l with
    | false => rfl
    | true =>
        exact (htrigger (Or.inr (Or.inr (Or.inl h)))).elim
  have hr : r.1.core.core.erase.leader = false := by
    change minimalLockLeader r = false
    cases h : minimalLockLeader r with
    | false => rfl
    | true =>
        exact (htrigger (Or.inr (Or.inr (Or.inr h)))).elim
  have hphysical := minimalLockPPsiPhysical_responder_birth
    hpsi kappa tau l.1 r.1 hl hr hbirth.1 hbirth.2
  simp only [P_partialMinimalLock, if_neg htrigger, if_pos hbirth]
  exact ⟨True.intro, True.intro, hphysical⟩

/-- Away from the atomic P'_psi birth case, the unlocked physical branch is
definitionally the exact current `P_partial`. -/
theorem P_partialMinimalLock_of_untriggered_nonbirth
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : MinimalLockState psi kappa tau)
    (htrigger : ¬ MinimalLockTrigger l r)
    (hbirth : ¬ MinimalLockBirthGuard hpsi l r) :
    P_partialMinimalLock hpsi kappa tau l r =
      let q := P_partialUnconditional hpsi kappa tau l.1 r.1
      let locked := minimalLockPairHasLeader q
      ((q.1, locked), (q.2, locked)) := by
  simp [P_partialMinimalLock, htrigger, hbirth]

abbrev MinimalLockBirthPsi : Nat := 2

private theorem minimalLockBirthHPsi : MinimalLockBirthPsi > 0 := by
  decide

private def minimalLockBirthRawLeft : AgentState MinimalLockBirthPsi :=
  PPLLCounterexample.state2 0 false

private def minimalLockBirthRawRight : AgentState MinimalLockBirthPsi :=
  { PPLLCounterexample.state2 0 false with probe := true }

private theorem minimalLockBirthRawLeft_domain (kappa : Nat) :
    minimalLockBirthRawLeft.inProtocolDomain kappa := by
  simp [minimalLockBirthRawLeft, PPLLCounterexample.state2,
    AgentState.inProtocolDomain]

private theorem minimalLockBirthRawRight_domain (kappa : Nat) :
    minimalLockBirthRawRight.inProtocolDomain kappa := by
  simp [minimalLockBirthRawRight, PPLLCounterexample.state2,
    AgentState.inProtocolDomain]

private def minimalLockBirthPhysicalLeft (kappa tau : Nat) :
    ExpiringAgentState MinimalLockBirthPsi kappa tau :=
  ⟨⟨BoundedAgentState.ofDomain minimalLockBirthRawLeft
      (minimalLockBirthRawLeft_domain kappa), false⟩,
    freshStall tau⟩

private def minimalLockBirthPhysicalRight (kappa tau : Nat) :
    ExpiringAgentState MinimalLockBirthPsi kappa tau :=
  ⟨⟨BoundedAgentState.ofDomain minimalLockBirthRawRight
      (minimalLockBirthRawRight_domain kappa), false⟩,
    freshStall tau⟩

/-- Explicit unlocked follower/follower barrier/probe pair. -/
def minimalLockBirthLeft (kappa tau : Nat) :
    MinimalLockState MinimalLockBirthPsi kappa tau :=
  (minimalLockBirthPhysicalLeft kappa tau, false)

def minimalLockBirthRight (kappa tau : Nat) :
    MinimalLockState MinimalLockBirthPsi kappa tau :=
  (minimalLockBirthPhysicalRight kappa tau, false)

private theorem minimalLockBirth_not_trigger (kappa tau : Nat) :
    ¬ MinimalLockTrigger
      (minimalLockBirthLeft kappa tau)
      (minimalLockBirthRight kappa tau) := by
  simp [MinimalLockTrigger, minimalLockLeader,
    minimalLockBirthLeft, minimalLockBirthRight,
    minimalLockBirthPhysicalLeft, minimalLockBirthPhysicalRight,
    minimalLockBirthRawLeft, minimalLockBirthRawRight,
    PPLLCounterexample.state2, BoundedAgentState.ofDomain]

private theorem minimalLockBirth_guard (kappa tau : Nat) :
    MinimalLockBirthGuard minimalLockBirthHPsi
      (minimalLockBirthLeft kappa tau)
      (minimalLockBirthRight kappa tau) := by
  change true = true ∧ (0 : Fin 2) ≠ (1 : Fin 2)
  constructor
  · rfl
  · intro h
    have hv := congrArg Fin.val h
    omega

/-- Concrete, computation-free use of the generic writer theorem: both input
leader bits are false, while one repaired interaction creates and locks the
responder leader.  This witnesses that the local birth branch is inhabited; it
is not a global rank-zero producer theorem. -/
theorem minimalLock_concrete_first_birth (kappa tau : Nat) :
    minimalLockLeader (minimalLockBirthLeft kappa tau) = false ∧
      minimalLockLeader (minimalLockBirthRight kappa tau) = false ∧
      let q := P_partialMinimalLock minimalLockBirthHPsi kappa tau
        (minimalLockBirthLeft kappa tau)
        (minimalLockBirthRight kappa tau)
      q.1.2 = true ∧ q.2.2 = true ∧
        minimalLockLeader q.2 = true := by
  refine ⟨rfl, rfl, ?_⟩
  exact P_partialMinimalLock_of_birthGuard
    minimalLockBirthHPsi kappa tau
    (minimalLockBirthLeft kappa tau)
    (minimalLockBirthRight kappa tau)
    (minimalLockBirth_not_trigger kappa tau)
    (minimalLockBirth_guard kappa tau)

/-- The bounded raw domain is closed by construction in both branches.  The
unlocked branch uses `P_partial`'s proved unconditional domain closure, while
the triggered branch returns old bounded cores. -/
theorem P_partialMinimalLock_output_inProtocolDomain
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : MinimalLockState psi kappa tau) :
    let q := P_partialMinimalLock hpsi kappa tau l r
    q.1.1.core.erase.core.inProtocolDomain kappa ∧
      q.2.1.core.erase.core.inProtocolDomain kappa := by
  let q := P_partialMinimalLock hpsi kappa tau l r
  change q.1.1.core.core.erase.inProtocolDomain kappa ∧
    q.2.1.core.core.erase.inProtocolDomain kappa
  exact ⟨q.1.1.core.core.erase_inProtocolDomain,
    q.2.1.core.core.erase_inProtocolDomain⟩

/-! ## Exact lock and physical frames -/

/-- A triggered interaction changes no physical field and locks both
endpoints. -/
theorem P_partialMinimalLock_of_trigger
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : MinimalLockState psi kappa tau)
    (htrigger : MinimalLockTrigger l r) :
    P_partialMinimalLock hpsi kappa tau l r =
      ((l.1, true), (r.1, true)) := by
  simp [P_partialMinimalLock, htrigger]

/-- Two locked inputs make the complete local transition the identity. -/
theorem P_partialMinimalLock_eq_self_of_locked
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : MinimalLockState psi kappa tau)
    (hl : l.2 = true) (hr : r.2 = true) :
    P_partialMinimalLock hpsi kappa tau l r = (l, r) := by
  rcases l with ⟨l, llock⟩
  rcases r with ⟨r, rlock⟩
  cases llock <;> cases rlock <;>
    simp_all [P_partialMinimalLock, MinimalLockTrigger]

/-- A true left lock is never lost. -/
theorem P_partialMinimalLock_preserves_left_lock
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : MinimalLockState psi kappa tau)
    (hl : l.2 = true) :
    (P_partialMinimalLock hpsi kappa tau l r).1.2 = true := by
  simp [P_partialMinimalLock, MinimalLockTrigger, hl]

/-- A true right lock is never lost. -/
theorem P_partialMinimalLock_preserves_right_lock
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : MinimalLockState psi kappa tau)
    (hr : r.2 = true) :
    (P_partialMinimalLock hpsi kappa tau l r).2.2 = true := by
  simp [P_partialMinimalLock, MinimalLockTrigger, hr]

/-! ## Closed, nonvacuous legitimate set -/

/-- Every endpoint has received the dissemination lock. -/
def MinimalLockAllLocked
    (C : MinimalLockConfig n psi kappa tau) : Prop :=
  ∀ i : Fin n, (C i).2 = true

/-- Operational legitimacy: dissemination is complete and the current output
has exactly one leader.  Future stability is proved rather than included in
this definition. -/
def MinimalLockLegit
    (hpsi : psi > 0) (kappa tau : Nat)
    (C : MinimalLockConfig n psi kappa tau) : Prop :=
  MinimalLockAllLocked C ∧
    UniqueLeaderOutput
      (P_partialMinimalLockProtocol hpsi kappa tau)
      n C isLeaderOutput

/-- On an all-locked configuration, an exact packaged step is the identity
configuration, including every auxiliary field. -/
theorem P_partialMinimalLock_step_eq_of_allLocked
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau)
    (hlocked : MinimalLockAllLocked C) (e : Fin n) :
    (P_partialMinimalLockProtocol hpsi kappa tau).step ring C e = C := by
  let j := ring.rightNeighbor e
  have hpair : P_partialMinimalLock hpsi kappa tau (C e) (C j) =
      (C e, C j) :=
    P_partialMinimalLock_eq_self_of_locked hpsi kappa tau
      (C e) (C j) (hlocked e) (hlocked j)
  funext i
  by_cases hie : i = e
  · subst i
    simp [PopulationProtocol.step, P_partialMinimalLockProtocol, j, hpair]
  · by_cases hij : i = j
    · subst i
      simp [PopulationProtocol.step, P_partialMinimalLockProtocol,
        j, hie, hpair]
    · simp [PopulationProtocol.step, P_partialMinimalLockProtocol,
        j, hie, hij]

/-- The legitimate set is closed under every exact interaction. -/
theorem minimalLockLegit_closed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialMinimalLockProtocol hpsi kappa tau) ring
      (MinimalLockLegit hpsi kappa tau) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  rw [P_partialMinimalLock_step_eq_of_allLocked
    hpsi kappa tau ring C hC.1 e]
  exact hC

/-- Every legitimate step preserves the complete pointwise output vector. -/
theorem minimalLockLegit_stepOutputPreserving
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    StepOutputPreservingOn
      (P_partialMinimalLockProtocol hpsi kappa tau) ring
      (MinimalLockLegit hpsi kappa tau) := by
  intro C hC D hstep i
  obtain ⟨e, rfl⟩ := hstep
  rw [P_partialMinimalLock_step_eq_of_allLocked
    hpsi kappa tau ring C hC.1 e]

/-- Membership in `MinimalLockLegit` implies Definition-1 safety. -/
theorem minimalLockLegit_isSafe
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau)
    (hC : MinimalLockLegit hpsi kappa tau C) :
    PopulationProtocol.IsSafe
      (P_partialMinimalLockProtocol hpsi kappa tau)
      ring C isLeaderOutput := by
  exact isSafe_of_operational_legitimacy
    (P_partialMinimalLockProtocol hpsi kappa tau)
    ring isLeaderOutput
    (MinimalLockLegit hpsi kappa tau)
    (minimalLockLegit_closed hpsi kappa tau ring)
    (fun _ h => h.2)
    (minimalLockLegit_stepOutputPreserving hpsi kappa tau ring)
    hC

/-- Canonical all-locked witness obtained from the already verified finite
one-leader configuration. -/
def minimalLockWitness
    (hpsi : psi > 0) (kappa tau : Nat) :
    MinimalLockConfig n psi kappa tau :=
  fun i => (outputFinite hpsi kappa tau i, true)

/-- The lock bit is output-invisible on the canonical witness. -/
theorem minimalLockWitness_output_eq_noCheck
    (hpsi : psi > 0) (kappa tau : Nat) (i : Fin n) :
    (P_partialMinimalLockProtocol hpsi kappa tau).output
        (minimalLockWitness (n := n) hpsi kappa tau i) =
      (PPLLNoCheckBirthRepair.noCheckBirthProtocol hpsi kappa tau).output
        (outputFinite (n := n) hpsi kappa tau i) := by
  change
    (if (outputFinite (n := n) hpsi kappa tau i).core.core.leader
      then LeaderOutput.leader else LeaderOutput.follower) =
    (if (outputFinite (n := n) hpsi kappa tau i).core.core.leader
      then LeaderOutput.leader else LeaderOutput.follower)
  rfl

/-- The operational legitimate set is inhabited for every nonempty ring and
every finite parameter choice. -/
theorem minimalLockLegit_inhabited
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    MinimalLockLegit hpsi kappa tau
      (minimalLockWitness (n := n) hpsi kappa tau) := by
  constructor
  · intro i
    rfl
  · have hOutput : OutputLegit hpsi ring
        (outputFinite (n := n) hpsi kappa tau) :=
      outputLegit_inhabited hpsi kappa tau ring
    have hUnique := outputLegit_unique_output
      hpsi kappa tau ring
      (outputFinite (n := n) hpsi kappa tau) hOutput
    obtain ⟨leader, hleader, honly⟩ := hUnique
    refine ⟨leader, ?_, ?_⟩
    · have hout := congrArg isLeaderOutput
        (minimalLockWitness_output_eq_noCheck
          (n := n) hpsi kappa tau leader)
      exact hout.trans hleader
    · intro j hj
      apply honly j
      have hout := congrArg isLeaderOutput
        (minimalLockWitness_output_eq_noCheck
          (n := n) hpsi kappa tau j)
      exact hout.symm.trans hj

/-! ## Deterministic dissemination from one seed -/

/-- If the selected pair is triggered, its local step frames every physical
endpoint, including the one-agent self-edge case. -/
theorem minimalLock_localStep_physical_of_trigger
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau) (e : Fin n)
    (htrigger : MinimalLockTrigger
      (C e) (C (ring.rightNeighbor e))) :
    ∀ i : Fin n,
      (localStep ring (P_partialMinimalLock hpsi kappa tau) C e i).1 =
        (C i).1 := by
  let j := ring.rightNeighbor e
  have hpair : P_partialMinimalLock hpsi kappa tau (C e) (C j) =
      (((C e).1, true), ((C j).1, true)) :=
    P_partialMinimalLock_of_trigger hpsi kappa tau
      (C e) (C j) htrigger
  intro i
  by_cases hie : i = e
  · subst i
    simp [localStep, j, hpair]
  · by_cases hij : i = j
    · subst i
      simp [localStep, j, hie, hpair]
    · simp [localStep, j, hie, hij]

/-- A true lock at any site survives every local interaction. -/
theorem minimalLock_localStep_lock_mono
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau) (e i : Fin n)
    (hi : (C i).2 = true) :
    (localStep ring (P_partialMinimalLock hpsi kappa tau) C e i).2 =
      true := by
  let j := ring.rightNeighbor e
  by_cases hie : i = e
  · subst i
    have hpair := P_partialMinimalLock_of_trigger
      hpsi kappa tau (C e) (C j) (Or.inl hi)
    simp [localStep, j, hpair]
  · by_cases hij : i = j
    · subst i
      have hpair := P_partialMinimalLock_of_trigger
        hpsi kappa tau (C e) (C j) (Or.inr (Or.inl hi))
      simp [localStep, j, hie, hpair]
    · simpa [localStep, j, hie, hij] using hi

/-- Selecting an edge whose initiator is locked locks its clockwise
responder.  On a one-agent ring the initiator output supplies the same fact. -/
theorem minimalLock_localStep_locks_responder
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau) (e : Fin n)
    (he : (C e).2 = true) :
    (localStep ring (P_partialMinimalLock hpsi kappa tau) C e
      (ring.rightNeighbor e)).2 = true := by
  let j := ring.rightNeighbor e
  have hpair := P_partialMinimalLock_of_trigger
    hpsi kappa tau (C e) (C j) (Or.inl he)
  simp [localStep, j, hpair]

/-- After the first `steps` clockwise edges from a lock seed, physical state is
unchanged and every visited clockwise position through `steps` is locked. -/
theorem minimalLock_clockwise_flood_prefix
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau) (seed : Fin n)
    (hseed : (C seed).2 = true) (steps : Nat) :
    let D := runLocalSchedule ring
      (P_partialMinimalLock hpsi kappa tau) C
      (clockwiseEdgeSchedule ring seed steps)
    (∀ i : Fin n, (D i).1 = (C i).1) ∧
      ∀ k : Nat, k ≤ steps →
        (D (cwPos ring seed k)).2 = true := by
  induction steps with
  | zero =>
      constructor
      · intro i
        rfl
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        simpa [clockwiseEdgeSchedule, runLocalSchedule] using hseed
  | succ steps ih =>
      let D := runLocalSchedule ring
        (P_partialMinimalLock hpsi kappa tau) C
        (clockwiseEdgeSchedule ring seed steps)
      let e := cwPos ring seed steps
      have hrun :
          runLocalSchedule ring
              (P_partialMinimalLock hpsi kappa tau) C
              (clockwiseEdgeSchedule ring seed (steps + 1)) =
            localStep ring (P_partialMinimalLock hpsi kappa tau) D e := by
        change runLocalSchedule ring
            (P_partialMinimalLock hpsi kappa tau) C
            (clockwiseEdgeSchedule ring seed steps ++
              [cwPos ring seed steps]) = _
        rw [PPLLSchedulerBlocks.runLocalSchedule_append]
        rfl
      have he : (D e).2 = true := ih.2 steps (Nat.le_refl steps)
      rw [hrun]
      constructor
      · intro i
        exact (minimalLock_localStep_physical_of_trigger
          hpsi kappa tau ring D e (Or.inl he) i).trans (ih.1 i)
      · intro k hk
        by_cases hle : k ≤ steps
        · exact minimalLock_localStep_lock_mono
            hpsi kappa tau ring D e (cwPos ring seed k)
            (ih.2 k hle)
        · have hkeq : k = steps + 1 := by omega
          subst k
          rw [cwPos_succ]
          exact minimalLock_localStep_locks_responder
            hpsi kappa tau ring D e he

/-- One seed locks the complete nonempty ring in exactly `n - 1` selected
clockwise edges. -/
theorem minimalLock_clockwise_flood_allLocked
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau) (seed : Fin n)
    (hseed : (C seed).2 = true) :
    MinimalLockAllLocked
      (runLocalSchedule ring
        (P_partialMinimalLock hpsi kappa tau) C
        (clockwiseEdgeSchedule ring seed (n - 1))) := by
  intro i
  let d := cwDist ring seed i
  have hdlt : d < n := cwDist_lt ring seed i
  have hdle : d ≤ n - 1 := by omega
  have hprefix := (minimalLock_clockwise_flood_prefix
    hpsi kappa tau ring C seed hseed (n - 1)).2 d hdle
  rw [cwPos_cwDist] at hprefix
  exact hprefix

/-- Lock dissemination never changes a physical field. -/
theorem minimalLock_clockwise_flood_physical_eq
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau) (seed : Fin n)
    (hseed : (C seed).2 = true) (steps : Nat) (i : Fin n) :
    (runLocalSchedule ring
      (P_partialMinimalLock hpsi kappa tau) C
      (clockwiseEdgeSchedule ring seed steps) i).1 = (C i).1 :=
  (minimalLock_clockwise_flood_prefix
    hpsi kappa tau ring C seed hseed steps).1 i

/-- Hence dissemination preserves the complete pointwise output vector. -/
theorem minimalLock_clockwise_flood_output_eq
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau) (seed : Fin n)
    (hseed : (C seed).2 = true) (steps : Nat) (i : Fin n) :
    (P_partialMinimalLockProtocol hpsi kappa tau).output
        (runLocalSchedule ring
          (P_partialMinimalLock hpsi kappa tau) C
          (clockwiseEdgeSchedule ring seed steps) i) =
      (P_partialMinimalLockProtocol hpsi kappa tau).output (C i) := by
  have hphysical := minimalLock_clockwise_flood_physical_eq
    hpsi kappa tau ring C seed hseed steps i
  change
    (if minimalLockLeader
        (runLocalSchedule ring
          (P_partialMinimalLock hpsi kappa tau) C
          (clockwiseEdgeSchedule ring seed steps) i)
      then LeaderOutput.leader else LeaderOutput.follower) =
      (if minimalLockLeader (C i) then LeaderOutput.leader
        else LeaderOutput.follower)
  have hleader : minimalLockLeader
        (runLocalSchedule ring
          (P_partialMinimalLock hpsi kappa tau) C
          (clockwiseEdgeSchedule ring seed steps) i) =
      minimalLockLeader (C i) := by
    unfold minimalLockLeader
    rw [hphysical]
  rw [hleader]

/-- Every explicit local schedule is a reachable execution of the packaged
minimal-lock protocol. -/
theorem P_partialMinimalLock_runLocalSchedule_reachable
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau)
    (word : DetSchedule n) :
    PopulationProtocol.Reachable
      (P_partialMinimalLockProtocol hpsi kappa tau) ring C
      (runLocalSchedule ring
        (P_partialMinimalLock hpsi kappa tau) C word) := by
  induction word generalizing C with
  | nil =>
      exact @PopulationProtocol.Reachable.refl n
        (P_partialMinimalLockProtocol hpsi kappa tau) ring C
  | cons e rest ih =>
      exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans
        (ih (localStep ring
          (P_partialMinimalLock hpsi kappa tau) C e))

/-- Strictly weaker than legitimacy: one current leader output and one lock
seed.  Unlocked remote edges may still change outputs under another schedule,
so this predicate is not semantic safety in disguise. -/
def MinimalLockSeeded
    (hpsi : psi > 0) (kappa tau : Nat)
    (C : MinimalLockConfig n psi kappa tau) : Prop :=
  UniqueLeaderOutput
      (P_partialMinimalLockProtocol hpsi kappa tau)
      n C isLeaderOutput ∧
    ∃ seed : Fin n, (C seed).2 = true

/-- The explicit clockwise flood maps every seeded unique-output state into
the closed legitimate set without changing any output. -/
theorem minimalLockSeeded_clockwise_flood_legit
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau)
    (hC : MinimalLockSeeded hpsi kappa tau C) :
    ∃ seed : Fin n,
      MinimalLockLegit hpsi kappa tau
        (runLocalSchedule ring
          (P_partialMinimalLock hpsi kappa tau) C
          (clockwiseEdgeSchedule ring seed (n - 1))) := by
  obtain ⟨hunique, seed, hseed⟩ := hC
  refine ⟨seed,
    minimalLock_clockwise_flood_allLocked
      hpsi kappa tau ring C seed hseed, ?_⟩
  obtain ⟨leader, hleader, honly⟩ := hunique
  refine ⟨leader, ?_, ?_⟩
  · have hout := congrArg isLeaderOutput
      (minimalLock_clockwise_flood_output_eq
        hpsi kappa tau ring C seed hseed (n - 1) leader)
    exact hout.trans hleader
  · intro j hj
    apply honly j
    have hout := congrArg isLeaderOutput
      (minimalLock_clockwise_flood_output_eq
        hpsi kappa tau ring C seed hseed (n - 1) j)
    exact hout.symm.trans hj

/-- The same flood endpoint is genuinely reachable in the packaged protocol. -/
theorem minimalLockSeeded_reaches_safe
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau)
    (hC : MinimalLockSeeded hpsi kappa tau C) :
    ∃ D : MinimalLockConfig n psi kappa tau,
      PopulationProtocol.Reachable
          (P_partialMinimalLockProtocol hpsi kappa tau) ring C D ∧
        PopulationProtocol.IsSafe
          (P_partialMinimalLockProtocol hpsi kappa tau)
          ring D isLeaderOutput := by
  obtain ⟨seed, hlegit⟩ :=
    minimalLockSeeded_clockwise_flood_legit
      hpsi kappa tau ring C hC
  let word := clockwiseEdgeSchedule ring seed (n - 1)
  let D := runLocalSchedule ring
    (P_partialMinimalLock hpsi kappa tau) C word
  refine ⟨D, ?_, minimalLockLegit_isSafe
    hpsi kappa tau ring D hlegit⟩
  exact P_partialMinimalLock_runLocalSchedule_reachable
    hpsi kappa tau ring C word

/-! ## Exact factor-two finite carrier -/

/-- Constructive exhaustive certificate for the one-bit product carrier. -/
def minimalLockStateCertificate (psi kappa tau : Nat) :
    ExhaustiveList (MinimalLockState psi kappa tau) :=
  ExhaustiveList.prod
    (P_partialStateCertificate psi kappa tau)
    ExhaustiveList.bool

/-- The one-bit repair has exactly twice as many local states as
`P_partial`. -/
theorem minimalLockStateCertificate_values_length
    (psi kappa tau : Nat) :
    (minimalLockStateCertificate psi kappa tau).values.length =
      ((2 * (PPLLFinite.boundedAgentState psi kappa).values.length) *
        (tau + 1)) * 2 := by
  unfold minimalLockStateCertificate
  rw [ExhaustiveList.values_length_prod,
    P_partialStateCertificate_values_length,
    ExhaustiveList.values_length_bool]

end PPartialMinimalLockRepairSol
end PPLLCompleteMultiLeaderCleanup

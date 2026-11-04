import Leader.Wu.PartialProtocol.CollisionReset

/-!
# Separated leaders: the arbitrary-singleton obstruction

The adjacent-collision repair cannot see two separated leaders in one local
interaction.  A natural next attempt is to move a leader, or to propagate an
output-invisible certificate and later let that certificate move or delete a
leader.  The relevant safety demand must be stated carefully: if *every*
arbitrary assignment of the complete local carrier with one leader output is
already pointwise-output stable, then locality forbids every output change on
a pair containing at most one leader.

The proof embeds an arbitrary local pair beside a remote leader on a four-agent
ring.  Complete local states include every proposed certificate, phase, lease,
timer, and reset tag.  Hence the premise covers arbitrary initialization of all
such fields.  Leader/follower migration is ruled out immediately.  More
strongly, any configuration with no adjacent leader outputs has a permanently
fixed output vector, even while hidden state may continue to evolve.  An
alternating four-agent two-leader configuration is therefore an exact
separated obstruction and can never reach unique-leader output.

This is a scoped no-go, not an impossibility theorem for self-stabilizing
leader election.  A repair can evade the premise by making only a narrower,
coherent singleton certificate kernel safe, or by using a ring-indexed global
epoch.  What it cannot do is combine arbitrary-certificate singleton safety
with certificate-driven cleanup of separated leaders in one fixed local
transition.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSeparatedLeaderRepairSol

open PPLLResearchFormulation
open PPLLStaticDoubleCoverNoGo

set_option autoImplicit false

/-! ## Arbitrary-initialized singleton protection -/

/-- The fixed audit ring.  Four sites leave a disjoint position at which a
leader can witness an arbitrary follower/follower input pair. -/
abbrev separatedAuditRing : DirectedRing 4 := ⟨by omega⟩

/-- Strong singleton requirement under arbitrary initialization of the whole
local carrier: every four-agent configuration that currently has one leader
output is already pointwise-output stable forever. -/
def ArbitrarySingletonOutputStable4
    (P : PopulationProtocol) (isLeader : P.Y → Bool) : Prop :=
  ∀ C : P.Configuration 4,
    UniqueLeaderOutput P 4 C isLeader →
      OutputStableFrom P separatedAuditRing C

/-- Put an arbitrary selected pair at `0 → 1` and use one filler state at
the other two positions. -/
private def edgeZeroShadow
    (P : PopulationProtocol) (l r filler : P.Q) :
    P.Configuration 4
  | ⟨0, _⟩ => l
  | ⟨1, _⟩ => r
  | _ => filler

@[simp] private theorem edgeZeroShadow_zero
    (P : PopulationProtocol) (l r filler : P.Q) :
    edgeZeroShadow P l r filler (0 : Fin 4) = l := by
  rfl

@[simp] private theorem edgeZeroShadow_one
    (P : PopulationProtocol) (l r filler : P.Q) :
    edgeZeroShadow P l r filler (1 : Fin 4) = r := by
  rfl

@[simp] private theorem edgeZeroShadow_two
    (P : PopulationProtocol) (l r filler : P.Q) :
    edgeZeroShadow P l r filler (2 : Fin 4) = filler := by
  rfl

@[simp] private theorem edgeZeroShadow_three
    (P : PopulationProtocol) (l r filler : P.Q) :
    edgeZeroShadow P l r filler (3 : Fin 4) = filler := by
  rfl

/-- Put an arbitrary follower/follower pair at `0 → 1` and a remote leader
at position two. -/
private def remoteLeaderShadow
    (P : PopulationProtocol) (L l r : P.Q) :
    P.Configuration 4
  | ⟨0, _⟩ => l
  | ⟨1, _⟩ => r
  | ⟨2, _⟩ => L
  | _ => l

@[simp] private theorem remoteLeaderShadow_zero
    (P : PopulationProtocol) (L l r : P.Q) :
    remoteLeaderShadow P L l r (0 : Fin 4) = l := by
  rfl

@[simp] private theorem remoteLeaderShadow_one
    (P : PopulationProtocol) (L l r : P.Q) :
    remoteLeaderShadow P L l r (1 : Fin 4) = r := by
  rfl

@[simp] private theorem remoteLeaderShadow_two
    (P : PopulationProtocol) (L l r : P.Q) :
    remoteLeaderShadow P L l r (2 : Fin 4) = L := by
  rfl

@[simp] private theorem remoteLeaderShadow_three
    (P : PopulationProtocol) (L l r : P.Q) :
    remoteLeaderShadow P L l r (3 : Fin 4) = l := by
  rfl

private theorem edgeZeroShadow_unique_left
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (l r : P.Q)
    (hl : isLeader (P.output l) = true)
    (hr : isLeader (P.output r) = false) :
    UniqueLeaderOutput P 4 (edgeZeroShadow P l r r) isLeader := by
  refine ⟨0, ?_, ?_⟩
  · simpa using hl
  · intro i hi
    have hc : i = (0 : Fin 4) ∨ i = (1 : Fin 4) ∨
        i = (2 : Fin 4) ∨ i = (3 : Fin 4) := by
      omega
    rcases hc with rfl | rfl | rfl | rfl
    · rfl
    · simp [hr] at hi
    · simp [hr] at hi
    · simp [hr] at hi

private theorem edgeZeroShadow_unique_right
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (l r : P.Q)
    (hl : isLeader (P.output l) = false)
    (hr : isLeader (P.output r) = true) :
    UniqueLeaderOutput P 4 (edgeZeroShadow P l r l) isLeader := by
  refine ⟨1, ?_, ?_⟩
  · simpa using hr
  · intro i hi
    have hc : i = (0 : Fin 4) ∨ i = (1 : Fin 4) ∨
        i = (2 : Fin 4) ∨ i = (3 : Fin 4) := by
      omega
    rcases hc with rfl | rfl | rfl | rfl
    · simp [hl] at hi
    · rfl
    · simp [hl] at hi
    · simp [hl] at hi

private theorem remoteLeaderShadow_unique
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (L l r : P.Q)
    (hL : isLeader (P.output L) = true)
    (hl : isLeader (P.output l) = false)
    (hr : isLeader (P.output r) = false) :
    UniqueLeaderOutput P 4 (remoteLeaderShadow P L l r) isLeader := by
  refine ⟨2, ?_, ?_⟩
  · simpa using hL
  · intro i hi
    have hc : i = (0 : Fin 4) ∨ i = (1 : Fin 4) ∨
        i = (2 : Fin 4) ∨ i = (3 : Fin 4) := by
      omega
    rcases hc with rfl | rfl | rfl | rfl
    · simp [hl] at hi
    · simp [hr] at hi
    · rfl
    · simp [hl] at hi

/-- If an arbitrary pair appears on edge `0 → 1` of an arbitrary protected
singleton configuration, both endpoint outputs of its local transition must
equal their input outputs. -/
private theorem embeddedSingleton_pair_output_eq
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (hstable : ArbitrarySingletonOutputStable4 P isLeader)
    (C : P.Configuration 4)
    (hunique : UniqueLeaderOutput P 4 C isLeader)
    (l r : P.Q) (hzero : C 0 = l) (hone : C 1 = r) :
    let q := P.transition l r
    P.output q.1 = P.output l ∧
      P.output q.2 = P.output r := by
  let D := P.step separatedAuditRing C 0
  have hreach : PopulationProtocol.Reachable
      P separatedAuditRing C D :=
    PopulationProtocol.OneStep.to_reachable ⟨0, rfl⟩
  have hout := hstable C hunique D hreach
  constructor
  · have hz := hout (0 : Fin 4)
    simpa [D, PopulationProtocol.step, separatedAuditRing,
      DirectedRing.rightNeighbor, hzero, hone] using hz
  · have ho := hout (1 : Fin 4)
    simpa [D, PopulationProtocol.step, separatedAuditRing,
      DirectedRing.rightNeighbor, hzero, hone] using ho

/-! ## Local indistinguishability and migration failure -/

/-- Locality consequence: under arbitrary-singleton protection, the output of
an input pair can change only if both input endpoints are leaders.  `L` merely
witnesses that the leader output class is inhabited; all complete states
`l`,`r` remain arbitrary. -/
theorem transition_output_eq_of_not_twoLeaders
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (hstable : ArbitrarySingletonOutputStable4 P isLeader)
    (L : P.Q) (hL : isLeader (P.output L) = true)
    (l r : P.Q)
    (hnotBoth : ¬(isLeader (P.output l) = true ∧
      isLeader (P.output r) = true)) :
    let q := P.transition l r
    P.output q.1 = P.output l ∧
      P.output q.2 = P.output r := by
  cases hl : isLeader (P.output l) with
  | false =>
      cases hr : isLeader (P.output r) with
      | false =>
          exact embeddedSingleton_pair_output_eq P isLeader hstable
            (remoteLeaderShadow P L l r)
            (remoteLeaderShadow_unique P isLeader L l r hL hl hr)
            l r (by rfl) (by rfl)
      | true =>
          exact embeddedSingleton_pair_output_eq P isLeader hstable
            (edgeZeroShadow P l r l)
            (edgeZeroShadow_unique_right P isLeader l r hl hr)
            l r (by rfl) (by rfl)
  | true =>
      cases hr : isLeader (P.output r) with
      | false =>
          exact embeddedSingleton_pair_output_eq P isLeader hstable
            (edgeZeroShadow P l r r)
            (edgeZeroShadow_unique_left P isLeader l r hl hr)
            l r (by rfl) (by rfl)
      | true => exact (hnotBoth ⟨hl, hr⟩).elim

/-- Exact adversarial audit of a leader-migration rule.  Clearing a leader
initiator on a leader/follower input already contradicts arbitrary-singleton
pointwise stability, independently of what hidden certificate is written or
whether the responder becomes a leader. -/
theorem leaderMigration_violates_arbitrarySingleton
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (L l r : P.Q)
    (hL : isLeader (P.output L) = true)
    (hl : isLeader (P.output l) = true)
    (hr : isLeader (P.output r) = false)
    (hclear : isLeader (P.output (P.transition l r).1) = false) :
    ¬ArbitrarySingletonOutputStable4 P isLeader := by
  intro hstable
  have hp := transition_output_eq_of_not_twoLeaders
    P isLeader hstable L hL l r (by simp [hl, hr])
  have hout := congrArg isLeader hp.1
  rw [hclear, hl] at hout
  contradiction

/-! ## Separated configurations are output-frozen -/

/-- No directed edge currently has two leader-output endpoints.  This property
allows arbitrarily many separated leaders. -/
def NoAdjacentLeaderOutputs
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    {m : Nat} (ring : DirectedRing m) (C : P.Configuration m) : Prop :=
  ∀ e : Fin m,
    ¬(isLeader (P.output (C e)) = true ∧
      isLeader (P.output (C (ring.rightNeighbor e))) = true)

/-- One step from a no-adjacent configuration preserves the complete output at
every position.  Hidden state is intentionally not claimed to be fixed. -/
theorem noAdjacent_step_output_eq
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (hstable : ArbitrarySingletonOutputStable4 P isLeader)
    (L : P.Q) (hL : isLeader (P.output L) = true)
    {m : Nat} (ring : DirectedRing m)
    (C : P.Configuration m)
    (hC : NoAdjacentLeaderOutputs P isLeader ring C)
    (e i : Fin m) :
    P.output (P.step ring C e i) = P.output (C i) := by
  let j := ring.rightNeighbor e
  let q := P.transition (C e) (C j)
  have hp : P.output q.1 = P.output (C e) ∧
      P.output q.2 = P.output (C j) :=
    transition_output_eq_of_not_twoLeaders
      P isLeader hstable L hL (C e) (C j)
        (by simpa [j] using hC e)
  change P.output
      (if i = e then q.1 else if i = j then q.2 else C i) =
    P.output (C i)
  by_cases hie : i = e
  · subst i
    simpa using hp.1
  · by_cases hij : i = j
    · subst i
      simpa [hie] using hp.2
    · simp [hie, hij]

/-- Since each step preserves all output bits, no-adjacency is itself closed. -/
theorem noAdjacentLeaderOutputs_closed
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (hstable : ArbitrarySingletonOutputStable4 P isLeader)
    (L : P.Q) (hL : isLeader (P.output L) = true)
    {m : Nat} (ring : DirectedRing m) :
    PopulationProtocol.ClosedPred P ring
      (NoAdjacentLeaderOutputs P isLeader ring) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  intro k
  rintro ⟨hk, hj⟩
  have houtk := noAdjacent_step_output_eq
    P isLeader hstable L hL ring C hC e k
  have houtj := noAdjacent_step_output_eq
    P isLeader hstable L hL ring C hC e (ring.rightNeighbor k)
  apply hC k
  constructor
  · rw [← houtk]
    exact hk
  · rw [← houtj]
    exact hj

/-- Every reachable future of a no-adjacent configuration has exactly the same
pointwise output vector. -/
theorem noAdjacent_outputStable
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (hstable : ArbitrarySingletonOutputStable4 P isLeader)
    (L : P.Q) (hL : isLeader (P.output L) = true)
    {m : Nat} (ring : DirectedRing m)
    {C : P.Configuration m}
    (hC : NoAdjacentLeaderOutputs P isLeader ring C) :
    OutputStableFrom P ring C := by
  intro C' hreach
  induction hreach
  · intro i
    rfl
  · rename_i C₂ C₃ _ hone ih
    have hC₂ : NoAdjacentLeaderOutputs P isLeader ring C₂ :=
      (noAdjacentLeaderOutputs_closed
        P isLeader hstable L hL ring).reachable hC ‹_›
    obtain ⟨e, rfl⟩ := hone
    intro i
    exact (noAdjacent_step_output_eq
      P isLeader hstable L hL ring C₂ hC₂ e i).trans (ih i)

/-- Two separated leaders therefore survive at their original sites throughout
every execution, so no reachable future has unique-leader output. -/
theorem separatedLeaders_never_unique
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (hstable : ArbitrarySingletonOutputStable4 P isLeader)
    (L : P.Q) (hL : isLeader (P.output L) = true)
    {m : Nat} (ring : DirectedRing m)
    {C : P.Configuration m}
    (hC : NoAdjacentLeaderOutputs P isLeader ring C)
    (htwo : HasTwoLeaderOutputs P isLeader C) :
    ∀ C' : P.Configuration m,
      PopulationProtocol.Reachable P ring C C' →
        ¬UniqueLeaderOutput P m C' isLeader := by
  have hout := noAdjacent_outputStable
    P isLeader hstable L hL ring hC
  obtain ⟨i, j, hij, hi, hj⟩ := htwo
  intro C' hreach
  apply hasTwoLeaders_not_unique P isLeader
  refine ⟨i, j, hij, ?_, ?_⟩
  · rw [hout C' hreach i]
    exact hi
  · rw [hout C' hreach j]
    exact hj

/-! ## A concrete separated four-agent obstruction -/

/-- Alternating leader/follower outputs: two leaders, but no adjacent pair. -/
def alternatingSeparatedConfig
    (P : PopulationProtocol) (L F : P.Q) : P.Configuration 4
  | ⟨0, _⟩ => L
  | ⟨1, _⟩ => F
  | ⟨2, _⟩ => L
  | _ => F

@[simp] theorem alternatingSeparatedConfig_zero
    (P : PopulationProtocol) (L F : P.Q) :
    alternatingSeparatedConfig P L F (0 : Fin 4) = L := by
  rfl

@[simp] theorem alternatingSeparatedConfig_one
    (P : PopulationProtocol) (L F : P.Q) :
    alternatingSeparatedConfig P L F (1 : Fin 4) = F := by
  rfl

@[simp] theorem alternatingSeparatedConfig_two
    (P : PopulationProtocol) (L F : P.Q) :
    alternatingSeparatedConfig P L F (2 : Fin 4) = L := by
  rfl

@[simp] theorem alternatingSeparatedConfig_three
    (P : PopulationProtocol) (L F : P.Q) :
    alternatingSeparatedConfig P L F (3 : Fin 4) = F := by
  rfl

theorem alternatingSeparatedConfig_noAdjacent
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (L F : P.Q)
    (hL : isLeader (P.output L) = true)
    (hF : isLeader (P.output F) = false) :
    NoAdjacentLeaderOutputs P isLeader separatedAuditRing
      (alternatingSeparatedConfig P L F) := by
  intro e
  have hc : e = (0 : Fin 4) ∨ e = (1 : Fin 4) ∨
      e = (2 : Fin 4) ∨ e = (3 : Fin 4) := by
    omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [separatedAuditRing,
      DirectedRing.rightNeighbor, hL, hF]

theorem alternatingSeparatedConfig_hasTwoLeaders
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (L F : P.Q)
    (hL : isLeader (P.output L) = true) :
    HasTwoLeaderOutputs P isLeader
      (alternatingSeparatedConfig P L F) := by
  refine ⟨0, 2, ?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    omega
  · simpa using hL
  · simpa using hL

/-- Capstone: the explicit separated two-leader configuration is output-stable
and cannot reach uniqueness under the arbitrary-singleton safety demand.  This
is the exact obstruction faced by any stale-certificate cleanup rule. -/
theorem arbitrarySingletonProtection_blocks_separated_cleanup
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (hstable : ArbitrarySingletonOutputStable4 P isLeader)
    (L F : P.Q)
    (hL : isLeader (P.output L) = true)
    (hF : isLeader (P.output F) = false) :
    OutputStableFrom P separatedAuditRing
        (alternatingSeparatedConfig P L F) ∧
      ∀ C' : P.Configuration 4,
        PopulationProtocol.Reachable P separatedAuditRing
          (alternatingSeparatedConfig P L F) C' →
        ¬UniqueLeaderOutput P 4 C' isLeader := by
  have hno := alternatingSeparatedConfig_noAdjacent
    P isLeader L F hL hF
  constructor
  · exact noAdjacent_outputStable
      P isLeader hstable L hL separatedAuditRing hno
  · exact separatedLeaders_never_unique
      P isLeader hstable L hL separatedAuditRing hno
        (alternatingSeparatedConfig_hasTwoLeaders
          P isLeader L F hL)

end PPartialSeparatedLeaderRepairSol
end PPLLCompleteMultiLeaderCleanup

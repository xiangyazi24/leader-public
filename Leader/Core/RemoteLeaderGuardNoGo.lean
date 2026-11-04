import Leader.Core.Basic

/-!
# Locality obstruction to immediate remote-leader guards

A pairwise protocol cannot inspect a remote leader.  If every arbitrary
four-agent state with a sole leader at position zero must make the disjoint
follower edge `2 → 3` immediately leader-safe, then every possible
follower–follower local pair is forbidden from creating a leader.  Consequently
the all-follower predicate is closed and no execution can create its first
leader.

The argument covers any physical lease, guard, timer, or epoch because all such
metadata is already part of the arbitrary local state `Q`.  It does not assume
`Q` finite.  Its scope is deliberately narrower than SSLE impossibility: a
protocol may converge through unsafe or multi-leader transient states into a
stronger distributed protected predicate.  What fails is treating the bare
existence of one remote leader as immediate protection for every arbitrary
local carrier.
-/

namespace PPLLRemoteLeaderGuardNoGo

/-- The fixed four-agent ring used to shadow an arbitrary local follower pair
beside a disjoint leader. -/
abbrev fourRing : DirectedRing 4 := ⟨by omega⟩

variable (P : PopulationProtocol) (isLeader : P.Y → Bool)

/-- Every local output in the configuration is follower. -/
def AllFollower {n : Nat} (C : P.Configuration n) : Prop :=
  ∀ i, isLeader (P.output (C i)) = false

/-- Position zero is the sole leader output on the four-agent ring. -/
def UniqueLeaderAtZero4 (C : P.Configuration 4) : Prop :=
  isLeader (P.output (C 0)) = true ∧
    ∀ i : Fin 4, i ≠ 0 → isLeader (P.output (C i)) = false

/-- Immediate protection demanded of the edge disjoint from a remote leader:
from every arbitrary unique-leader state, selecting `2 → 3` must leave both
selected outputs followers. -/
def RemoteEdge2Protected : Prop :=
  ∀ C : P.Configuration 4,
    UniqueLeaderAtZero4 P isLeader C →
      let C' := P.step fourRing C 2
      isLeader (P.output (C' 2)) = false ∧
        isLeader (P.output (C' 3)) = false

/-- Embed any follower pair `(x,y)` on remote edge `2 → 3`, with a leader `L`
at position zero.  Position one is another copy of `x` and is irrelevant to the
selected interaction. -/
private def shadowConfig (L x y : P.Q) : P.Configuration 4
  | ⟨0, _⟩ => L
  | ⟨1, _⟩ => x
  | ⟨2, _⟩ => x
  | ⟨3, _⟩ => y

/-- Pair locality turns remote protection into a universal ban on leader birth
from follower–follower inputs.  The complete local states `x,y` include any
physical authorization, lease, timer, or epoch values. -/
theorem remoteProtection_forbids_follower_pair_birth
    (hprot : RemoteEdge2Protected P isLeader)
    (L x y : P.Q)
    (hL : isLeader (P.output L) = true)
    (hx : isLeader (P.output x) = false)
    (hy : isLeader (P.output y) = false) :
    let q := P.transition x y
    isLeader (P.output q.1) = false ∧
      isLeader (P.output q.2) = false := by
  have hu : UniqueLeaderAtZero4 P isLeader (shadowConfig P L x y) := by
    constructor
    · exact hL
    · intro i hi
      have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · contradiction
      · exact hx
      · exact hx
      · exact hy
  have hp := hprot (shadowConfig P L x y) hu
  simpa [PopulationProtocol.step, shadowConfig,
    DirectedRing.rightNeighbor, fourRing] using hp

/-- If at least one leader-output state exists, immediate remote protection
makes the all-follower predicate closed on every nonempty directed ring. -/
theorem allFollower_closed_of_remoteProtection
    (hprot : RemoteEdge2Protected P isLeader)
    (L : P.Q) (hL : isLeader (P.output L) = true)
    {n : Nat} (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred P ring (AllFollower P isLeader) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  intro i
  let j := ring.rightNeighbor e
  let q := P.transition (C e) (C j)
  have hpair := remoteProtection_forbids_follower_pair_birth
    P isLeader hprot L (C e) (C j) hL (hC e) (hC j)
  change isLeader
    (P.output (if i = e then q.1 else if i = j then q.2 else C i)) = false
  split
  · exact hpair.1
  · split
    · exact hpair.2
    · exact hC i

/-- Every state reachable from an all-follower start remains all-follower under
the immediate remote-protection premise. -/
theorem allFollower_reachable_of_remoteProtection
    (hprot : RemoteEdge2Protected P isLeader)
    (L : P.Q) (hL : isLeader (P.output L) = true)
    {n : Nat} (ring : DirectedRing n)
    (C C' : P.Configuration n)
    (hC : AllFollower P isLeader C)
    (hreach : PopulationProtocol.Reachable P ring C C') :
    AllFollower P isLeader C' := by
  exact (allFollower_closed_of_remoteProtection
    P isLeader hprot L hL ring).reachable hC hreach

/-- Scoped no-go capstone: immediate safety of every arbitrary remote
unique-leader state is incompatible with any reachable first leader from an
all-follower configuration.  This leaves open convergence into a narrower
physically certified protected region. -/
theorem remoteProtection_incompatible_with_first_leader
    (hprot : RemoteEdge2Protected P isLeader)
    (L : P.Q) (hL : isLeader (P.output L) = true)
    {n : Nat} (ring : DirectedRing n)
    (C : P.Configuration n) (hC : AllFollower P isLeader C)
    (hrecover : ∃ C' : P.Configuration n,
      PopulationProtocol.Reachable P ring C C' ∧
        ∃ i, isLeader (P.output (C' i)) = true) : False := by
  obtain ⟨C', hreach, i, hi⟩ := hrecover
  have hall := allFollower_reachable_of_remoteProtection
    P isLeader hprot L hL ring C C' hC hreach
  rw [hall i] at hi
  contradiction

end PPLLRemoteLeaderGuardNoGo

/-!
# Population Protocol on Directed Rings

Abstract framework for population protocols on directed rings of n agents,
following Wu (NTU 2024) §2 and Yokota et al. [32] Definition 2.1.

A directed ring of n agents has vertices {0, ..., n-1} with edges (i, (i+1) mod n).
Each agent carries a state from a finite set Q. The transition function
T : Q × Q → Q × Q updates the states of an initiator-responder pair.
-/

/-! ## Directed Ring -/

/-- A directed ring with `n` agents. Agent `i` has right neighbor `(i+1) mod n`. -/
structure DirectedRing (n : Nat) where
  hn : n > 0

namespace DirectedRing

/-- The right neighbor of agent `i` on the ring. -/
def rightNeighbor (ring : DirectedRing n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ ring.hn⟩

/-- The left neighbor of agent `i` on the ring. -/
def leftNeighbor (ring : DirectedRing n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ ring.hn⟩

end DirectedRing

/-! ## Population Protocol -/

/-- A population protocol consists of a state type, an output type,
a transition function, and an output function.

The transition function takes (initiator_state, responder_state) and
returns the new (initiator_state, responder_state). On a directed ring,
the initiator is the left agent and the responder is the right agent
in each interaction edge (uᵢ, u_{i+1 mod n}). -/
structure PopulationProtocol where
  Q : Type
  Y : Type
  transition : Q → Q → Q × Q
  output : Q → Y

namespace PopulationProtocol

/-- A configuration assigns a state to each agent. -/
def Configuration (P : PopulationProtocol) (n : Nat) := Fin n → P.Q

/-- Apply a single interaction at edge `i` to configuration `C`.
Agent `i` is the initiator, agent `(i+1) mod n` is the responder. -/
def step (P : PopulationProtocol) (ring : DirectedRing n) (C : P.Configuration n)
    (e : Fin n) : P.Configuration n :=
  let i := e
  let j := ring.rightNeighbor i
  let (qi', qj') := P.transition (C i) (C j)
  fun k =>
    if k = i then qi'
    else if k = j then qj'
    else C k

/-- Configuration `C'` is reachable from `C` in one step. -/
def OneStep (P : PopulationProtocol) (ring : DirectedRing n)
    (C C' : P.Configuration n) : Prop :=
  ∃ e : Fin n, C' = P.step ring C e

/-- Configuration `C'` is reachable from `C` in zero or more steps. -/
inductive Reachable (P : PopulationProtocol) (ring : DirectedRing n)
    : P.Configuration n → P.Configuration n → Prop where
  | refl (C : P.Configuration n) : Reachable P ring C C
  | step (C C' C'' : P.Configuration n) :
      Reachable P ring C C' → OneStep P ring C' C'' → Reachable P ring C C''

/-- A predicate on configurations is closed (invariant) under the protocol
if every one-step successor of a configuration satisfying the predicate
also satisfies it. -/
def ClosedPred (P : PopulationProtocol) (ring : DirectedRing n)
    (S : P.Configuration n → Prop) : Prop :=
  ∀ C, S C → ∀ C', OneStep P ring C C' → S C'

/-- If a predicate is closed, then it is preserved by reachability. -/
theorem ClosedPred.reachable {P : PopulationProtocol} {ring : DirectedRing n}
    {S : P.Configuration n → Prop} (hS : ClosedPred P ring S)
    {C C' : P.Configuration n} (hC : S C) (hr : Reachable P ring C C') : S C' := by
  induction hr
  · exact hC
  · rename_i C₂ C₃ _ hstep ih
    exact hS _ ih _ hstep

/-- A single step is reachable. -/
theorem OneStep.to_reachable {P : PopulationProtocol} {ring : DirectedRing n}
    {C C' : P.Configuration n} (h : OneStep P ring C C') :
    Reachable P ring C C' :=
  .step C C C' (.refl C) h

/-- Reachability is transitive. -/
theorem Reachable.trans {P : PopulationProtocol} {ring : DirectedRing n}
    {C C' C'' : P.Configuration n}
    (h1 : Reachable P ring C C') (h2 : Reachable P ring C' C'') :
    Reachable P ring C C'' := by
  induction h2
  · exact h1
  · rename_i _ _ _ hstep ih
    exact .step _ _ _ ih hstep

/-- A configuration is safe for leader election if:
(i) exactly one agent outputs L (leader),
(ii) all reachable configurations preserve the output of every agent. -/
def IsSafe (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (isLeader : P.Y → Bool) : Prop :=
  (∃ i : Fin n, isLeader (P.output (C i)) = true ∧
    ∀ j : Fin n, isLeader (P.output (C j)) = true → j = i) ∧
  ∀ C', Reachable P ring C C' →
    ∀ i : Fin n, P.output (C' i) = P.output (C i)

end PopulationProtocol

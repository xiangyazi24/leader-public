import Leader.Wu.Protocol.State

/-!
# High-Probability Convergence Profiles

This file contains **bound metadata**, not a probabilistic convergence proof.
`ReachSpec` records intended pre/postconditions, a step count, and a failure
bound, but has no field connecting those data to executions or probabilities.
In particular, its `ring` and transition parameters are phantom.

The combinators below only calculate new metadata. Their existence does not
establish that any phase reaches its postcondition. A future soundness layer
must define the random scheduler and a semantic proposition, then prove each
profile and each composition rule against that proposition.
-/

/-! ## Failure probability bounds -/

/-- A failure probability bound: a function from ring size n to a
nonneg rational upper bound on the failure probability. -/
def FailBound := Nat → Rat

namespace FailBound

def zero : FailBound := fun _ => 0

def add (ε₁ ε₂ : FailBound) : FailBound := fun n => ε₁ n + ε₂ n

instance : Add FailBound := ⟨add⟩

end FailBound

/-! ## Step bounds -/

/-- A step bound: a function from ring size n to the number of random
scheduler steps needed. Uses explicit arithmetic, not O()-notation. -/
def StepBound := Nat → Nat

namespace StepBound

def zero : StepBound := fun _ => 0

def add (T₁ T₂ : StepBound) : StepBound := fun n => T₁ n + T₂ n

def max (T₁ T₂ : StepBound) : StepBound := fun n => Nat.max (T₁ n) (T₂ n)

instance : Add StepBound := ⟨add⟩

end StepBound

/-! ## ReachSpec: non-semantic bound metadata -/

/-- An intended convergence profile for a protocol on a directed ring.

This structure does **not** assert reachability: there is no scheduler,
execution event, measure, or proof field. The leading parameters are retained
only so profiles have the same indexing shape as the future semantic theorem. -/
structure ReachSpec {ψ n : Nat} (_ring : DirectedRing n)
    (_T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ) where
  Pre : (Fin n → AgentState ψ) → Prop
  Post : (Fin n → AgentState ψ) → Prop
  steps : StepBound
  failProb : FailBound

/-- Retargeting is possible because a profile contains no fact about its ring
or transition. This operation is useful as an explicit reminder that
`ReachSpec` values must never be reported as convergence proofs. -/
def ReachSpec.retarget {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    (r : ReachSpec ring T) (ring' : DirectedRing n)
    (T' : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ) :
    ReachSpec ring' T' where
  Pre := r.Pre
  Post := r.Post
  steps := r.steps
  failProb := r.failProb

/-! ## Preserved: a predicate that holds forever once achieved -/

/-- A configuration predicate is preserved (closed) under the transition
function: if it holds before any single interaction, it holds after. -/
def Preserved {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (Q : (Fin n → AgentState ψ) → Prop) : Prop :=
  ∀ (C : Fin n → AgentState ψ), Q C →
    ∀ (e : Fin n),
      let i := e
      let j := ring.rightNeighbor i
      let (qi', qj') := T (C i) (C j)
      let C' := fun k => if k = i then qi' else if k = j then qj' else C k
      Q C'

/-- A predicate preserved under an ambient invariant: Q is preserved
as long as invariant I also holds. -/
def PreservedUnder {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (I Q : (Fin n → AgentState ψ) → Prop) : Prop :=
  ∀ (C : Fin n → AgentState ψ), I C → Q C →
    ∀ (e : Fin n),
      let i := e
      let j := ring.rightNeighbor i
      let (qi', qj') := T (C i) (C j)
      let C' := fun k => if k = i then qi' else if k = j then qj' else C k
      Q C'

/-! ## Preserved algebra -/

/-- Conjunction of preserved predicates is preserved. -/
theorem Preserved.and {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {P Q : (Fin n → AgentState ψ) → Prop}
    (hp : Preserved ring T P) (hq : Preserved ring T Q) :
    Preserved ring T (fun C => P C ∧ Q C) :=
  fun C ⟨hpC, hqC⟩ e => ⟨hp C hpC e, hq C hqC e⟩

/-- PreservedUnder promotes to Preserved when the predicate implies its
own ambient invariant. -/
theorem PreservedUnder.toPreserved {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {I Q : (Fin n → AgentState ψ) → Prop}
    (hpu : PreservedUnder ring T I Q) (hIQ : ∀ C, Q C → I C) :
    Preserved ring T Q :=
  fun C hqC e => hpu C (hIQ C hqC) hqC e

/-- Preserved implies PreservedUnder any invariant. -/
theorem Preserved.toUnder {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {I Q : (Fin n → AgentState ψ) → Prop}
    (hp : Preserved ring T Q) :
    PreservedUnder ring T I Q :=
  fun C _ hqC e => hp C hqC e

/-- Conjunction of conditionally preserved predicates under the same
invariant. -/
theorem PreservedUnder.and {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {I P Q : (Fin n → AgentState ψ) → Prop}
    (hp : PreservedUnder ring T I P) (hq : PreservedUnder ring T I Q) :
    PreservedUnder ring T I (fun C => P C ∧ Q C) :=
  fun C hI ⟨hpC, hqC⟩ e => ⟨hp C hI hpC e, hq C hI hqC e⟩

/-- PreservedUnder with a stronger invariant implies PreservedUnder with
a weaker one. -/
theorem PreservedUnder.weaken_invariant {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {I J Q : (Fin n → AgentState ψ) → Prop}
    (hp : PreservedUnder ring T I Q) (hIJ : ∀ C, J C → I C) :
    PreservedUnder ring T J Q :=
  fun C hJ hQ e => hp C (hIJ C hJ) hQ e

/-! ## Profile arithmetic

These constructors combine profile fields in the way a future union-bound
proof is expected to justify. They do not currently carry or preserve any
semantic validity evidence. -/

/-- Sequential composition: if we can reach Q from P, and R from Q,
then we can reach Q ∧ R from P (assuming Q is preserved). Steps add,
failure probabilities add (union bound). -/
def ReachSpec.then {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    (r₁ : ReachSpec ring T) (r₂ : ReachSpec ring T)
    (_hclosed : Preserved ring T r₁.Post) : ReachSpec ring T where
  Pre := r₁.Pre
  Post := fun C => r₁.Post C ∧ r₂.Post C
  steps := r₁.steps + r₂.steps
  failProb := r₁.failProb + r₂.failProb

/-- Parallel composition: if both Q and R are reached from P (independently),
and both are preserved, then Q ∧ R is reached. Steps take the max,
failure probabilities add. -/
def ReachSpec.both {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    (r₁ : ReachSpec ring T) (r₂ : ReachSpec ring T)
    (_hclosed₁ : Preserved ring T r₁.Post)
    (_hclosed₂ : Preserved ring T r₂.Post) : ReachSpec ring T where
  Pre := fun C => r₁.Pre C ∧ r₂.Pre C
  Post := fun C => r₁.Post C ∧ r₂.Post C
  steps := StepBound.max r₁.steps r₂.steps
  failProb := r₁.failProb + r₂.failProb

/-- Weakening: strengthen the precondition or weaken the postcondition.
Preserves step and failure bounds. -/
def ReachSpec.weaken {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    (r : ReachSpec ring T)
    (Pre' Post' : (Fin n → AgentState ψ) → Prop)
    (_hpre : ∀ C, Pre' C → r.Pre C)
    (_hpost : ∀ C, r.Post C → Post' C) : ReachSpec ring T where
  Pre := Pre'
  Post := Post'
  steps := r.steps
  failProb := r.failProb

/-- Metadata for delaying a profile whose postcondition has a separate
deterministic preservation proof. This remains non-semantic profile arithmetic. -/
def ReachSpec.delay {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    (r : ReachSpec ring T) (T' : StepBound)
    (_hclosed : Preserved ring T r.Post) : ReachSpec ring T where
  Pre := r.Pre
  Post := r.Post
  steps := r.steps + T'
  failProb := r.failProb

/-- Metadata-only sequential profile. No preservation proof is retained.
This constructor is **not sound as a convergence theorem** by itself; there is
currently no later semantics layer that checks the missing obligation. -/
def ReachSpec.seq {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    (r₁ : ReachSpec ring T) (r₂ : ReachSpec ring T)
    (_hseq : ∀ C, r₁.Post C → r₂.Pre C) : ReachSpec ring T where
  Pre := r₁.Pre
  Post := r₂.Post
  steps := r₁.steps + r₂.steps
  failProb := r₁.failProb + r₂.failProb

/-- Sequential composition with conditional preservation: Post₁ is
preserved as long as invariant I holds, and I is implied by Post₁.
Combined Post = Post₁ ∧ Post₂. This is the workhorse for phases where
the first postcondition's monotonicity is conditional (PreservedUnder). -/
def ReachSpec.then_under {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    (r₁ : ReachSpec ring T) (r₂ : ReachSpec ring T)
    {I : (Fin n → AgentState ψ) → Prop}
    (_hpres : PreservedUnder ring T I r₁.Post)
    (_hI : ∀ C, r₁.Post C → I C) : ReachSpec ring T where
  Pre := r₁.Pre
  Post := fun C => r₁.Post C ∧ r₂.Post C
  steps := r₁.steps + r₂.steps
  failProb := r₁.failProb + r₂.failProb

/-- Sequential composition with external ambient invariant: Post₁ is
preserved as long as invariant I holds (PreservedUnder I Post₁), and I
is independently Preserved. Pre includes both r₁.Pre and I. The combined
Post retains Post₁, Post₂, and I.
Soundness: I persists throughout (Preserved). Post₁ persists through
phase 2 because PreservedUnder I Post₁ and I holds. Post₂ is established
by r₂. -/
def ReachSpec.then_with_invariant {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    (r₁ : ReachSpec ring T) (r₂ : ReachSpec ring T)
    {I : (Fin n → AgentState ψ) → Prop}
    (_hpres : PreservedUnder ring T I r₁.Post)
    (_hI : Preserved ring T I)
    (_hseq : ∀ C, r₁.Post C → r₂.Pre C) : ReachSpec ring T where
  Pre := fun C => r₁.Pre C ∧ I C
  Post := fun C => r₁.Post C ∧ r₂.Post C ∧ I C
  steps := r₁.steps + r₂.steps
  failProb := r₁.failProb + r₂.failProb

/-- Identity: any predicate is reached from itself in 0 steps with
0 failure probability. -/
def ReachSpec.identity {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (P : (Fin n → AgentState ψ) → Prop) : ReachSpec ring T where
  Pre := P
  Post := P
  steps := StepBound.zero
  failProb := FailBound.zero

import Leader.Wu.Scheduler.WhpProfiles
import Leader.Wu.Scheduler.TraversalMetric
import Leader.Wu.Safety.SafeConfig

/-!
# Profiles for Cited Convergence Bounds

This module records the bound formulas attributed to external results. It is
"axiom-free" only because `ReachSpec` is metadata: these definitions do not
formalize random scheduling and do not prove the cited probabilistic theorems.
`yokota_det_to_whp_profile` consumes a deterministic schedule proof but merely
stores the claimed WHP formula; the probabilistic lifting remains open.

1. **Lemma 2.0.1** [Yokota et al. [32], Lemma 2.3]: Converts a deterministic
   interaction sequence of length l into a w.h.p. random-step bound of
   c·n·(l + log n) steps with probability 1 - n^{-c}.

2. **Yokota leader elimination** [[31]]: In a protocol with leaders and
   barriers, the bullet/shield mechanism reduces the leader count to 1
   within O(n² log n) steps w.h.p.
-/

/-! ## Lemma 2.0.1: Deterministic schedule → WHP step bound -/

/-- Metadata for the claimed Lemma 2.0.1 lifting formula. `hseq` proves
the deterministic premise, but this definition does not prove the random-
scheduler conclusion represented informally by the stored bounds. -/
def yokota_det_to_whp_profile
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (Pre Post : (Fin n → AgentState ψ) → Prop)
    (seqLength : Nat)
    (c : Nat) (_hc : c ≥ 1)
    (_hseq : ∀ C : Fin n → AgentState ψ, Pre C →
      ∃ s : DetSchedule n, s.length ≤ seqLength ∧
        Post (applySchedule ring T C s)) :
    ReachSpec ring T where
  Pre := Pre
  Post := Post
  steps := fun n => c * n * (seqLength + Nat.log2 n)
  failProb := fun n => (1 : Rat) / (n ^ c : Nat)

/-! ## Traversal-to-WHP composition

For the ring-traversal phases (4.1.2, 4.1.3, 4.1.7, 4.1.9), the proof pattern
is: provide a TraversalMetric + list of objects → `traversal_bound_family` gives
a det schedule → `yokota_det_to_whp_profile` lifts to a WHP bound. -/

/-- Compose `traversal_bound_family` with `yokota_det_to_whp_profile`: given a
`TraversalMetric` and a list of at most `k` objects to traverse, produce a
`ReachSpec` with det schedule length `k * n`, lifted to WHP. -/
def reach_profile_from_traversal
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    {α : Type}
    (M : TraversalMetric ψ n ring T α)
    (Pre Post : (Fin n → AgentState ψ) → Prop)
    (objects : (Fin n → AgentState ψ) → List α)
    (k : Nat)
    (hk : ∀ C, Pre C → (objects C).length ≤ k)
    (hgoal : ∀ C s, Pre C →
      (∀ obj, obj ∈ objects C → M.goal (applySchedule ring T C s) obj) →
      Post (applySchedule ring T C s))
    (c : Nat) (hc : c ≥ 1) : ReachSpec ring T :=
  yokota_det_to_whp_profile ring T Pre Post (k * n) c hc
    (fun C hpre =>
      let objs := objects C
      let ⟨s, hs_len, hs_goal⟩ := traversal_bound_family M objs C
      ⟨s, Nat.le_trans hs_len (Nat.mul_le_mul_right n (hk C hpre)),
       hgoal C s hpre hs_goal⟩)

/-! ## Parallel Chernoff lifting

For phases where multiple objects traverse the ring simultaneously (cleaning
with ≤n bullets, barriers safe with ≤n barriers), each edge fires Θ(n) times
in O(n²) random steps (by Chernoff). Since each object needs ≤n advance steps
(one per edge), the Θ(n) firings per edge suffice for ALL objects simultaneously.
This gives O(n²) regardless of object count k, vs O(kn²) from sequential
Yokota lifting. -/

/-- Proposed parallel-Chernoff bound profile. The metric and goal proof are
not semantically consumed by `ReachSpec`; a future probability theorem must
justify this profile before the O(n²) claim can be used. -/
def parallel_chernoff_profile
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    {α : Type}
    (_M : TraversalMetric ψ n ring T α)
    (Pre Post : (Fin n → AgentState ψ) → Prop)
    (objects : (Fin n → AgentState ψ) → List α)
    (_hgoal : ∀ C s, Pre C →
      (∀ obj, obj ∈ objects C → _M.goal (applySchedule ring T C s) obj) →
      Post (applySchedule ring T C s))
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T where
  Pre := Pre
  Post := Post
  steps := fun n => c * n * (n + Nat.log2 n)
  failProb := fun n => (1 : Rat) / (n ^ c : Nat)

/-! ## Yokota leader elimination -/

/-- Proposed profile for Yokota [31] leader elimination. This constructor
has no protocol-dynamics premise and therefore cannot be a theorem: it records
the pre/postconditions and formula to be proved later. -/
def yokota_leader_elimination_profile
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T where
  Pre := fun C => hasLeader n C ∧ noFreeBarrier hψ ring C
  Post := fun C => hasUniqueLeader n C
  steps := fun n => c * n * n * Nat.log2 n
  failProb := fun n => (1 : Rat) / (n ^ c : Nat)

import Leader.Wu.Protocol.State

/-!
# Ring Traversal Template

Four convergence lemmas (4.1.2, 4.1.3, 4.1.7, 4.1.9) share the same proof
pattern: an object (bullet, barrier, reset signal, or OW signal) traverses
the directed ring. When the edge at the object's current position fires, the
object advances one position. Irrelevant edge firings do not decrease progress.

This file defines `TraversalMetric` — a generic framework that captures this
pattern — and proves a reusable traversal bound: if the initial distance to
the target is ≤ d, then a deterministic interaction sequence of length d
suffices to reach the target.

The deterministic sequence length is then lifted to a w.h.p. random-step
bound via Lemma 2.0.1 (axiomatized in ConvergenceAxioms.lean).
-/

/-! ## Configuration step -/

/-- Apply one interaction step at edge e: fire the transition function on
the initiator (agent e) and responder (right neighbor of e), updating both. -/
def stepConfig {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (e : Fin n) : Fin n → AgentState ψ :=
  let i := e
  let j := ring.rightNeighbor i
  let (qi', qj') := T (C i) (C j)
  fun k => if k = i then qi' else if k = j then qj' else C k

/-! ## Deterministic interaction sequences -/

/-- A deterministic interaction sequence: a list of edge indices to fire
in order. Each `Fin n` represents the edge (uᵢ, u_{i+1 mod n}). -/
abbrev DetSchedule (n : Nat) := List (Fin n)

/-- Apply a deterministic schedule to a configuration by firing each edge
in sequence. -/
def applySchedule {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) : DetSchedule n → Fin n → AgentState ψ
  | [] => C
  | e :: rest => applySchedule ring T (stepConfig ring T C e) rest

/-! ## TraversalMetric -/

/-- A traversal metric tracks an object's progress around a directed ring.

The `distance` measures remaining steps to the target. The `advance` law
says that firing the edge at the object's position decreases distance.
The `stable` law says that other edge firings do not increase distance.
The `nonterminal` law says that when distance > 0, a relevant edge exists.

The witness type `α` identifies the object being tracked (e.g., a bullet
at a specific position, a barrier between two agents). -/
structure TraversalMetric (ψ n : Nat) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (α : Type) where
  /-- The relevant edge for the object in the current config: firing this
  edge advances the object. Returns `none` if the object has reached its
  target or no longer exists. -/
  relevantEdge : (Fin n → AgentState ψ) → α → Option (Fin n)
  /-- Distance to target. 0 means the target predicate holds. -/
  distance : (Fin n → AgentState ψ) → α → Nat
  /-- The target predicate: holds when the object has completed traversal. -/
  goal : (Fin n → AgentState ψ) → α → Prop
  /-- Distance 0 implies goal reached. -/
  goal_of_zero :
    ∀ (C : Fin n → AgentState ψ) (obj : α),
      distance C obj = 0 → goal C obj
  /-- Initial distance is bounded by ring size. -/
  distance_bound :
    ∀ (C : Fin n → AgentState ψ) (obj : α),
      distance C obj ≤ n
  /-- If distance > 0, there exists a relevant edge to fire. -/
  nonterminal :
    ∀ (C : Fin n → AgentState ψ) (obj : α),
      distance C obj > 0 → ∃ e, relevantEdge C obj = some e
  /-- Firing the relevant edge decreases distance by at least 1. -/
  advance :
    ∀ (C : Fin n → AgentState ψ) (obj : α) (e : Fin n),
      relevantEdge C obj = some e →
      distance (stepConfig ring T C e) obj < distance C obj
  /-- Firing an irrelevant edge does not increase distance. -/
  stable :
    ∀ (C : Fin n → AgentState ψ) (obj : α) (e : Fin n),
      relevantEdge C obj ≠ some e →
      distance (stepConfig ring T C e) obj ≤ distance C obj

/-! ## Traversal bound theorem

Given a traversal metric, there exists a deterministic schedule of length ≤ n
that brings the distance to 0. This is the core reusable result; each of the
four traversal lemmas (4.1.2, 4.1.3, 4.1.7, 4.1.9) instantiates the metric
and applies this theorem. -/

/-- Auxiliary: a schedule of length ≤ fuel suffices when distance ≤ fuel. -/
private theorem traversal_aux
    {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {α : Type}
    (M : TraversalMetric ψ n ring T α)
    (obj : α)
    (fuel : Nat) :
    ∀ (C : Fin n → AgentState ψ), M.distance C obj ≤ fuel →
      ∃ (s : DetSchedule n), s.length ≤ fuel ∧
        M.goal (applySchedule ring T C s) obj := by
  induction fuel with
  | zero =>
    intro C hd
    refine ⟨[], ?_, M.goal_of_zero C obj (by omega)⟩
    · exact Nat.le.refl
  | succ d ih =>
    intro C hd
    by_cases h0 : M.distance C obj = 0
    · refine ⟨[], ?_, M.goal_of_zero C obj h0⟩
      · exact Nat.zero_le _
    · obtain ⟨e, he⟩ := M.nonterminal C obj (by omega)
      have hdec := M.advance C obj e he
      obtain ⟨s, hs_len, hs_goal⟩ := ih (stepConfig ring T C e) (by omega)
      refine ⟨e :: s, ?_, hs_goal⟩
      · simp only [List.length_cons]
        omega

/-- A single object can be brought to its target by a deterministic schedule
of length ≤ n: repeatedly fire the relevant edge (advance law); each firing
decreases distance by ≥ 1 (nonterminal + advance); initial distance ≤ n
(distance_bound); so ≤ n firings suffice. -/
theorem traversal_bound_single
    {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {α : Type}
    (M : TraversalMetric ψ n ring T α) :
    ∀ (C : Fin n → AgentState ψ) (obj : α),
      ∃ (s : DetSchedule n), s.length ≤ n ∧
        M.goal (applySchedule ring T C s) obj :=
  fun C obj => traversal_aux M obj n C (M.distance_bound C obj)

/-! ## Multi-object traversal helpers -/

/-- If distance = 0, firing any edge keeps distance at 0. Advance would give
distance < 0 (impossible for Nat), so the fired edge must be irrelevant,
and stable gives distance ≤ 0 = 0. -/
private theorem distance_zero_stable
    {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {α : Type}
    (M : TraversalMetric ψ n ring T α)
    (C : Fin n → AgentState ψ) (obj : α) (e : Fin n)
    (h0 : M.distance C obj = 0) :
    M.distance (stepConfig ring T C e) obj = 0 := by
  by_cases he : M.relevantEdge C obj = some e
  · have := M.advance C obj e he; omega
  · have := M.stable C obj e he; omega

/-- Schedule concatenation distributes over applySchedule. -/
private theorem applySchedule_append
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) (s1 s2 : DetSchedule n) :
    applySchedule ring T C (s1 ++ s2) =
    applySchedule ring T (applySchedule ring T C s1) s2 := by
  induction s1 generalizing C with
  | nil => rfl
  | cons e rest ih => exact ih (stepConfig ring T C e)

/-- If distance = 0, it stays 0 through any schedule. -/
private theorem applySchedule_preserves_zero
    {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {α : Type}
    (M : TraversalMetric ψ n ring T α)
    (obj : α) (s : DetSchedule n)
    (C : Fin n → AgentState ψ)
    (h0 : M.distance C obj = 0) :
    M.distance (applySchedule ring T C s) obj = 0 := by
  induction s generalizing C with
  | nil => exact h0
  | cons e rest ih =>
    exact ih (stepConfig ring T C e) (distance_zero_stable M C obj e h0)

/-- Like traversal_aux but concludes with distance = 0 (for composability). -/
private theorem traversal_aux_dist
    {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {α : Type}
    (M : TraversalMetric ψ n ring T α)
    (obj : α) (fuel : Nat) :
    ∀ (C : Fin n → AgentState ψ), M.distance C obj ≤ fuel →
      ∃ (s : DetSchedule n), s.length ≤ fuel ∧
        M.distance (applySchedule ring T C s) obj = 0 := by
  induction fuel with
  | zero =>
    intro C hd
    refine ⟨[], ?_, ?_⟩
    · show (0 : Nat) ≤ 0; omega
    · show M.distance C obj = 0; omega
  | succ d ih =>
    intro C hd
    by_cases h0 : M.distance C obj = 0
    · refine ⟨[], ?_, ?_⟩
      · exact Nat.zero_le _
      · show M.distance C obj = 0; exact h0
    · obtain ⟨e, he⟩ := M.nonterminal C obj (by omega)
      have hdec := M.advance C obj e he
      obtain ⟨s, hs_len, hs_dist⟩ := ih (stepConfig ring T C e) (by omega)
      refine ⟨e :: s, ?_, hs_dist⟩
      · simp only [List.length_cons]; omega

/-! ## Multi-object traversal bound

For lemmas involving multiple objects (e.g., n bullets in Lemma 4.1.2),
the deterministic schedule for all objects is the concatenation of individual
schedules. Goal monotonicity (once distance = 0, it stays 0) is proved from
the advance/stable laws: advance at distance 0 would give a negative Nat
(contradiction), so every edge is "irrelevant" and stable preserves 0. -/

/-- k objects, each with traversal metric distance ≤ n, can all be brought
to their targets by a deterministic schedule of total length ≤ k·n. -/
theorem traversal_bound_family
    {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    {α : Type}
    (M : TraversalMetric ψ n ring T α)
    (objs : List α) :
    ∀ (C : Fin n → AgentState ψ),
      ∃ (s : DetSchedule n), s.length ≤ objs.length * n ∧
        ∀ obj, obj ∈ objs → M.goal (applySchedule ring T C s) obj := by
  intro C
  induction objs generalizing C with
  | nil =>
    refine ⟨[], ?_, ?_⟩
    · show (0 : Nat) ≤ 0 * n; omega
    · intro _ h; nomatch h
  | cons hd tl ih =>
    obtain ⟨s1, hs1_len, hs1_dist⟩ :=
      traversal_aux_dist M hd n C (M.distance_bound C hd)
    obtain ⟨s2, hs2_len, hs2_goal⟩ :=
      ih (applySchedule ring T C s1)
    refine ⟨s1 ++ s2, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]
      have h_add := Nat.add_le_add hs1_len hs2_len
      suffices n + tl.length * n = (tl.length + 1) * n by omega
      rw [Nat.succ_mul, Nat.add_comm]
    · intro obj hmem
      rw [applySchedule_append]
      cases hmem with
      | head =>
        exact M.goal_of_zero _ _
          (applySchedule_preserves_zero M _ s2 _ hs1_dist)
      | tail _ htl => exact hs2_goal _ htl

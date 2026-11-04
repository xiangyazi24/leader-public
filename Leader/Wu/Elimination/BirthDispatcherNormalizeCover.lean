import Leader.Wu.Elimination.BirthDispatcherLeaderNormalize

/-!
# Complete initiator-cover producer for leader-label normalization

A raw scheduler word that contains every vertex as an initiator touches every
physical site at least once. After the first such touch, every leader at that
site has label zero. Later rows either touch the site again and normalize its
actual output again, or leave that site literally unchanged.
-/

namespace K2BirthLeaderNormalizeCover

open PPLLExpiringComparisonRepair

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ τ n : Nat}

/-- The one-site fragment of the global `LeadersZero` predicate. -/
def LeaderZeroAt (hψ : 0 < ψ)
    (C : Fin n → ExpiringAgentState ψ κ τ) (i : Fin n) : Prop :=
  (C i).core.core.leader = true →
    (C i).core.core.label = ⟨0, hψ⟩

/-- Once a site has a zero-labeled leader, every later actual row preserves
that fact. A touched site is certified from the actual row output; an untouched
site is framed by the actual `step_other` theorem. -/
theorem leaderZeroAt_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e i : Fin n)
    (hC : LeaderZeroAt hψ C i) :
    LeaderZeroAt hψ (K2BirthLeaderNormalize.step hψ ring C e) i := by
  intro hi
  by_cases he : i = e
  · subst i
    rw [K2BirthLeaderNormalize.step_left hψ ring C e] at hi ⊢
    exact
      (K2BirthLeaderNormalize.row_leader_labels_zero hψ
        (C e) (C (ring.rightNeighbor e))).1 hi
  · by_cases hr : i = ring.rightNeighbor e
    · subst i
      rw [K2BirthLeaderNormalize.step_right hψ ring C e he] at hi ⊢
      exact
        (K2BirthLeaderNormalize.row_leader_labels_zero hψ
          (C e) (C (ring.rightNeighbor e))).2 hi
    · rw [K2BirthLeaderNormalize.step_other hψ ring C e i he hr] at hi ⊢
      exact hC hi

/-- Scheduling `e` as the actual initiator establishes the local property
without any hypothesis on the old state or old label at `e`. -/
theorem leaderZeroAt_step_initiator (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n) :
    LeaderZeroAt hψ (K2BirthLeaderNormalize.step hψ ring C e) e := by
  intro hi
  rw [K2BirthLeaderNormalize.step_left hψ ring C e] at hi ⊢
  exact
    (K2BirthLeaderNormalize.row_leader_labels_zero hψ
      (C e) (C (ring.rightNeighbor e))).1 hi

/-- A one-site certificate survives the literal suffix of the same raw word. -/
theorem leaderZeroAt_run (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n)) (i : Fin n)
    (hC : LeaderZeroAt hψ C i) :
    LeaderZeroAt hψ
      (LDSinkBoundedKernel.run
        (K2BirthLeaderNormalize.step hψ ring) C es) i := by
  induction es generalizing C with
  | nil =>
      simpa only [LDSinkBoundedKernel.run] using hC
  | cons e es ih =>
      simp only [LDSinkBoundedKernel.run]
      exact ih (K2BirthLeaderNormalize.step hψ ring C e)
        (leaderZeroAt_step hψ ring C e i hC)

/-- If `i` actually occurs as an initiator in the supplied raw word, then the
final physical state at `i` satisfies the zero-label-leader property, from an
arbitrary initial configuration. -/
theorem leaderZeroAt_run_of_mem (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n)) (i : Fin n)
    (hi : i ∈ es) :
    LeaderZeroAt hψ
      (LDSinkBoundedKernel.run
        (K2BirthLeaderNormalize.step hψ ring) C es) i := by
  induction es generalizing C with
  | nil =>
      simp at hi
  | cons e es ih =>
      simp only [LDSinkBoundedKernel.run]
      rcases List.mem_cons.mp hi with he | hi
      · subst i
        exact
          leaderZeroAt_run hψ ring
            (K2BirthLeaderNormalize.step hψ ring C e) es e
            (leaderZeroAt_step_initiator hψ ring C e)
      · exact ih (K2BirthLeaderNormalize.step hψ ring C e) hi

/-- Every physical vertex occurs somewhere as an actual initiator. -/
def InitiatorCover (es : List (Fin n)) : Prop :=
  ∀ i, i ∈ es

/-- Complete-cover physical producer. No initial leader-label hypothesis is
present: every old site is forced through a real normalized row at least once. -/
theorem leadersZero_run_of_initiatorCover (hψ : 0 < ψ)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hcover : InitiatorCover es) :
    K2BirthLeaderNormalize.LeadersZero hψ
      (LDSinkBoundedKernel.run
        (K2BirthLeaderNormalize.step hψ ring) C es) := by
  intro i hi
  exact (leaderZeroAt_run_of_mem hψ ring C es i (hcover i)) hi

/-! ## Concrete n = 2 satisfiability witness -/

/-- Make an existing physical state an old leader with the nonzero label `1`. -/
def forceOldBadLeader (q : ExpiringAgentState 2 κ τ) :
    ExpiringAgentState 2 κ τ :=
  { q with
    core := { q.core with
      core := { q.core.core with
        leader := true
        label := (1 : Fin 2) } } }

/-- Vertex `0` is the deliberately bad old leader. Vertex `1` is otherwise the
supplied arbitrary physical state. -/
def n2BadInitial (q : ExpiringAgentState 2 κ τ) :
    Fin 2 → ExpiringAgentState 2 κ τ :=
  fun i => if i = 0 then forceOldBadLeader q else q

def n2Ring : DirectedRing 2 := ⟨by decide⟩

/-- The literal two-edge raw word schedules both vertices as initiators. -/
def n2CoverWord : List (Fin 2) := [0, 1]

theorem n2CoverWord_cover : InitiatorCover n2CoverWord := by
  intro i
  have hib := i.isLt
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · have h : i = (0 : Fin 2) := Fin.ext hi
    subst i
    simp [n2CoverWord]
  · have h : i = (1 : Fin 2) := Fin.ext hi
    subst i
    simp [n2CoverWord]

theorem n2BadInitial_vertex0 (q : ExpiringAgentState 2 κ τ) :
    (n2BadInitial q 0).core.core.leader = true ∧
      (n2BadInitial q 0).core.core.label = (1 : Fin 2) := by
  simp [n2BadInitial, forceOldBadLeader]

/-- The concrete initial configuration really violates the old global premise;
its old leader at vertex `0` has label `1`, not zero. -/
theorem n2BadInitial_not_leadersZero (q : ExpiringAgentState 2 κ τ) :
    ¬ K2BirthLeaderNormalize.LeadersZero
      (by decide : 0 < 2) (n2BadInitial q) := by
  intro h
  have h0 := n2BadInitial_vertex0 q
  have hz := h (0 : Fin 2) h0.1
  rw [h0.2] at hz
  exact (by decide : (1 : Fin 2) ≠ (0 : Fin 2))
    (Fin.ext (congrArg Fin.val hz))

/-- The actual complete-cover word nevertheless produces `LeadersZero`. -/
theorem n2BadInitial_completeCover_produces_leadersZero
    (q : ExpiringAgentState 2 κ τ) :
    K2BirthLeaderNormalize.LeadersZero
      (by decide : 0 < 2)
      (LDSinkBoundedKernel.run
        (K2BirthLeaderNormalize.step (by decide : 0 < 2) n2Ring)
        (n2BadInitial q) n2CoverWord) := by
  exact leadersZero_run_of_initiatorCover
    (by decide : 0 < 2) n2Ring (n2BadInitial q) n2CoverWord
    n2CoverWord_cover

/-- Explicit satisfiability certificate: the same concrete initial state fails
`LeadersZero`, while its literal `[0,1]` execution satisfies it. -/
theorem n2BadInitial_completeCover_witness
    (q : ExpiringAgentState 2 κ τ) :
    (¬ K2BirthLeaderNormalize.LeadersZero
      (by decide : 0 < 2) (n2BadInitial q)) ∧
    K2BirthLeaderNormalize.LeadersZero
      (by decide : 0 < 2)
      (LDSinkBoundedKernel.run
        (K2BirthLeaderNormalize.step (by decide : 0 < 2) n2Ring)
        (n2BadInitial q) n2CoverWord) :=
  ⟨n2BadInitial_not_leadersZero q,
    n2BadInitial_completeCover_produces_leadersZero q⟩

end K2BirthLeaderNormalizeCover

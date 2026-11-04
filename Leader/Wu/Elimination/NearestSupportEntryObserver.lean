import Leader.Wu.Elimination.NearestSupportEntryRows

/-!
# Proof-only observer of old unsupported live transport

The counter records a clockwise interval of actual current followers. Each
transport adds its new follower site to that interval. A current surviving
leader forbids n such transports, without fixing a future leader identity.
-/

namespace K2NearestSupportEntry

open PPLL StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination
  K2PeacefulGlobal PPLLNoCheckBirthConditionTwoGeometry FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

variable {n ψ κ : Nat}

/-- Only current fields are stored as proof obligations. C remains the exact
physical configuration, including every label and controller field. -/
structure Mark (ring : DirectedRing n) (ψ κ : Nat) where
  C : Fin n → UCell ψ κ
  pos : Fin n
  moves : Nat
  moves_lt : moves < n
  trail : ∀ j, j < moves → (C (cwPos ring pos j)).legacy.leader = false
  bad : Bad ring C pos
  leader : hasLeader n (observe C)

/-- One unit is charged only for actual transport into an old follower. -/
def advance (ring : DirectedRing n) (C : Fin n → UCell ψ κ) (e p : Fin n) : Nat :=
  if p = ring.rightNeighbor e ∧ (C e).legacy.leader = false then 1 else 0

/-- The visited interval is maintained using the actual no-new-leader row. -/
theorem trail_step (hψ : 0 < ψ) (ring : DirectedRing n) (s : Mark ring ψ κ) (e : Fin n) :
    ∀ j, j < s.moves + advance ring s.C e s.pos →
      (AdjacentLeaderElimination.step hψ ring s.C e
        (cwPos ring (nextPos ring s.C e s.pos) j)).legacy.leader = false := by
  intro j hj
  by_cases hm : s.pos = ring.rightNeighbor e ∧ (s.C e).legacy.leader = false
  · simp only [advance, if_pos hm, nextPos] at hj ⊢
    cases j with
    | zero =>
      rw [cwPos_zero]
      exact AdjacentLeaderElimination.step_follower hψ ring s.C e e hm.2
    | succ j =>
      rw [← cwPos_rightNeighbor, ← hm.1]
      exact AdjacentLeaderElimination.step_follower hψ ring s.C e _
        (s.trail j (by omega))
  · simp only [advance, if_neg hm, Nat.add_zero] at hj
    simp only [nextPos, if_neg hm]
    exact AdjacentLeaderElimination.step_follower hψ ring s.C e _ (s.trail j hj)

/-- A full follower interval covers every site, so it cannot coexist with
any current leader. This is the physical bound on the transport counter. -/
theorem moves_step_lt (hψ : 0 < ψ) (ring : DirectedRing n)
    (s : Mark ring ψ κ) (e : Fin n)
    (hL : hasLeader n (observe (AdjacentLeaderElimination.step hψ ring s.C e))) :
    s.moves + advance ring s.C e s.pos < n := by
  apply Classical.byContradiction
  intro hbad
  obtain ⟨i, hi⟩ := hL
  have hd := cwDist_lt ring (nextPos ring s.C e s.pos) i
  have hf := trail_step hψ ring s e (cwDist ring (nextPos ring s.C e s.pos) i) (by omega)
  rw [cwPos_cwDist] at hf
  change (AdjacentLeaderElimination.step hψ ring s.C e i).legacy.leader = true at hi
  rw [hi] at hf
  cases hf

/-- Every successor is constructed from the real same-edge row. A mark
terminates on lost live status, obtained Support, or physical zero leaders. -/
noncomputable def markStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (s : Mark ring ψ κ) (e : Fin n) : StopNode (Mark ring ψ κ) := by
  classical
  let D := AdjacentLeaderElimination.step hψ ring s.C e
  let p := nextPos ring s.C e s.pos
  exact if h : hasLeader n (observe D) ∧ Bad ring D p then
    .active ⟨D, p, s.moves + advance ring s.C e s.pos,
      moves_step_lt hψ ring s e h.1, trail_step hψ ring s e, h.2, h.1⟩
  else .success

/-- Exact same-state erasure on every continuing mark row. -/
theorem markStep_active (hψ : 0 < ψ) (ring : DirectedRing n)
    (s t : Mark ring ψ κ) (e : Fin n) (ht : markStep hψ ring s e = .active t) :
    t.C = AdjacentLeaderElimination.step hψ ring s.C e ∧
    t.pos = nextPos ring s.C e s.pos ∧
    t.moves = s.moves + advance ring s.C e s.pos := by
  unfold markStep at ht
  dsimp only at ht
  split at ht
  · cases ht
    exact ⟨rfl, rfl, rfl⟩
  · cases ht

/-- A bad successor at the computed position produces a continuing mark;
there is no assumed all-word mark closure. -/
theorem markStep_produces (hψ : 0 < ψ) (ring : DirectedRing n)
    (s : Mark ring ψ κ) (e : Fin n)
    (hL : hasLeader n (observe (AdjacentLeaderElimination.step hψ ring s.C e)))
    (hb : Bad ring (AdjacentLeaderElimination.step hψ ring s.C e)
      (nextPos ring s.C e s.pos)) :
    ∃ t, markStep hψ ring s e = .active t := by
  unfold markStep
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · rename_i h
    exact False.elim (h ⟨hL, hb⟩)

/-- Raw residual, before the scheduler's factor n. -/
def markRank (ring : DirectedRing n) : StopNode (Mark ring ψ κ) → Nat
  | .active s => n - s.moves
  | .success => 0
  | .failure => 0

theorem markRank_mono (hψ : 0 < ψ) (ring : DirectedRing n)
    (s : Mark ring ψ κ) (e : Fin n) :
    markRank ring (markStep hψ ring s e) ≤ markRank ring (.active s) := by
  unfold markStep
  dsimp only
  split
  · simp only [markRank]
    omega
  · exact Nat.zero_le _

/-- The canonical incoming edge uses no extra scheduler symbols. -/
theorem right_left (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by have := ring.hn; omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by have := ring.hn; omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq]
    have hh : (n + (i.val - 1)) % n = i.val - 1 := by
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    rw [hh]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

/-- A selected incoming edge either charges one follower transport or
terminates the mark. The actual responder classification proves this. -/
theorem markRank_service (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : Mark ring ψ κ) :
    markRank ring (markStep hψ ring s (ring.leftNeighbor s.pos)) + 1 ≤
      markRank ring (.active s) := by
  have hlt := s.moves_lt
  unfold markStep
  dsimp only
  split
  · rename_i h
    have hm : s.pos = ring.rightNeighbor (ring.leftNeighbor s.pos) ∧
        (s.C (ring.leftNeighbor s.pos)).legacy.leader = false := by
      refine ⟨(right_left ring s.pos).symm, ?_⟩
      cases hl : (s.C (ring.leftNeighbor s.pos)).legacy.leader with
      | false => rfl
      | true =>
        have hp : nextPos ring s.C (ring.leftNeighbor s.pos) s.pos = s.pos := by
          simp [nextPos, hl]
        have hb := h.2
        rw [hp] at hb
        have hnb := responder_not_bad hψ hn ring s.C (ring.leftNeighbor s.pos)
        rw [right_left] at hnb
        exact False.elim (hnb hb)
    simp only [markRank, advance, if_pos hm]
    omega
  · simp only [markRank]
    omega

/-- The exact one-mark Bellman potential is bounded by n². -/
def markPotential (ring : DirectedRing n) (x : StopNode (Mark ring ψ κ)) : Nat :=
  n * markRank ring x

theorem mark_bellman (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n) :
    NatBellmanSuperSolution (markStep (κ := κ) hψ ring) 1 (markPotential ring) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have h := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => markRank ring (markStep hψ ring s e)) (markRank ring (.active s))
    (ring.leftNeighbor s.pos) (markRank_mono hψ ring s) (markRank_service hψ hn ring s)
  have hm := Nat.mul_le_mul_left n h
  simp only [markPotential, ofFn_sum_mul_left, Nat.one_mul]
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using hm

theorem markPotential_bound (ring : DirectedRing n) (x : StopNode (Mark ring ψ κ)) :
    markPotential ring x ≤ n * n := by
  apply Nat.mul_le_mul_left
  cases x <;> simp [markRank]

/-- No finite physical state is excluded when the observer is initialized. -/
noncomputable def initialMark (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (p : Fin n) : StopNode (Mark ring ψ κ) := by
  classical
  exact if h : hasLeader n (observe C) ∧ Bad ring C p then
    .active ⟨C, p, 0, ring.hn, fun _ h => by omega, h.2, h.1⟩
  else .success

/-- The whole observer retains the exact configuration. Marks are indexed
by initial sites solely in the proof and may coalesce at one physical site. -/
structure Observer (ring : DirectedRing n) (ψ κ : Nat) where
  C : Fin n → UCell ψ κ
  marks : Fin n → StopNode (Mark ring ψ κ)
  same : ∀ i s, marks i = .active s → s.C = C
  covers : hasLeader n (observe C) → ∀ p, Bad ring C p →
    ∃ i s, marks i = .active s ∧ s.pos = p

noncomputable def initialObserver (ring : DirectedRing n) (C : Fin n → UCell ψ κ) :
    Observer ring ψ κ where
  C := C
  marks := initialMark ring C
  same := by
    intro i s hs
    unfold initialMark at hs
    split at hs
    · cases hs; rfl
    · cases hs
  covers := by
    intro hL p hb
    refine ⟨p, ?_⟩
    unfold initialMark
    split
    · exact ⟨_, rfl, rfl⟩
    · rename_i h
      exact False.elim (h ⟨hL, hb⟩)

/-- Every observer row runs the same physical row once and each proof mark's
already-produced update. The coverage proof uses the literal bad-origin law. -/
noncomputable def observerStep (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : Observer ring ψ κ) (e : Fin n) : Observer ring ψ κ where
  C := AdjacentLeaderElimination.step hψ ring s.C e
  marks := fun i => stepNode (markStep hψ ring) (s.marks i) e
  same := by
    intro i t ht
    cases hi : s.marks i with
    | success => simp [hi, stepNode] at ht
    | failure => simp [hi, stepNode] at ht
    | active q =>
      have hq := s.same i q hi
      have h := markStep_active hψ ring q t e (by simpa [hi, stepNode] using ht)
      exact h.1.trans (congrArg (fun C => AdjacentLeaderElimination.step hψ ring C e) hq)
  covers := by
    intro hL p hb
    have hLold : hasLeader n (observe s.C) := by
      obtain ⟨i, hi⟩ := hL
      exact ⟨i, AdjacentLeaderElimination.step_leader_source hψ ring s.C e i hi⟩
    obtain ⟨q, hbad, hpos⟩ := bad_origin hψ hn ring s.C e p hb
    obtain ⟨i, a, hi, ha⟩ := s.covers hLold q hbad
    have hC := s.same i a hi
    have hLa : hasLeader n (observe (AdjacentLeaderElimination.step hψ ring a.C e)) := by
      simpa only [hC] using hL
    have hba : Bad ring (AdjacentLeaderElimination.step hψ ring a.C e)
        (nextPos ring a.C e a.pos) := by simpa only [hC, ha, hpos] using hb
    obtain ⟨b, hstep⟩ := markStep_produces hψ ring a e hLa hba
    have hf := markStep_active hψ ring a b e hstep
    refine ⟨i, b, ?_, ?_⟩
    · simpa only [hi, stepNode] using hstep
    · exact hf.2.1.trans (by rw [hC, ha, hpos])

/-- Erasure is equality of complete physical configurations, not equality
of a count or projected four-field trace. -/
theorem observerStep_erases (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : Observer ring ψ κ) (e : Fin n) :
    (observerStep hψ hn ring s e).C = AdjacentLeaderElimination.step hψ ring s.C e := rfl

theorem observerRun_erases (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : Observer ring ψ κ) (es : List (Fin n)) :
    (run (observerStep hψ hn ring) s es).C =
      run (AdjacentLeaderElimination.step hψ ring) s.C es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact ih (observerStep hψ hn ring s e)

/-- The per-initial-site stopping tree is exactly the corresponding mark
projection of the whole observer on every original scheduler word. -/
theorem observerRun_mark (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (s : Observer ring ψ κ) (i : Fin n) (es : List (Fin n)) :
    (run (observerStep hψ hn ring) s es).marks i =
      run (stepNode (markStep hψ ring)) (s.marks i) es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact ih (observerStep hψ hn ring s e)

end K2NearestSupportEntry

#print axioms K2NearestSupportEntry.trail_step
#print axioms K2NearestSupportEntry.moves_step_lt
#print axioms K2NearestSupportEntry.mark_bellman
#print axioms K2NearestSupportEntry.observerStep
#print axioms K2NearestSupportEntry.observerRun_erases
#print axioms K2NearestSupportEntry.observerRun_mark

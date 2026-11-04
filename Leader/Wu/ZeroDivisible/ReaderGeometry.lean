import Leader.Core.ModArith
import Leader.Wu.ZeroDivisible.GroupPreparationWord

/-!
# Canonical-reader geometry on the q*psi physical ring

Pure physical geometry for the R5 canonical readers.  There is no transition,
state-stability, readiness, or convergence statement in this module.
-/

namespace PPLLAstraR5ReaderGeometry

open PPLLAstraR5PrepWord

set_option autoImplicit false

private theorem q_pos {q : Nat} (g : Fin q) : 0 < q := by
  have hg := g.isLt
  omega

/-- The next logical psi-group.  Its nonemptiness is derived from g : Fin q. -/
def successorGroup {q : Nat} (g : Fin q) : Fin q :=
  ⟨(g.val + 1) % q, Nat.mod_lt _ (q_pos g)⟩

@[simp] theorem successorGroup_val {q : Nat} (g : Fin q) :
    (successorGroup g).val = (g.val + 1) % q := rfl

/-- Moving psi offsets in the total PrepWord.cell coordinate moves to the
successor logical group, including the q=1 overlap case. -/
theorem source_target_wrap {q ψ : Nat}
    (ring : DirectedRing (q * ψ)) (g : Fin q) (j : Nat) :
    cell ring g (ψ + j) = cell ring (successorGroup g) j := by
  apply Fin.ext
  change (g.val * ψ + (ψ + j)) % (q * ψ) =
    (((g.val + 1) % q) * ψ + j) % (q * ψ)
  by_cases hnext : g.val + 1 < q
  · rw [Nat.mod_eq_of_lt hnext]
    have harg :
        g.val * ψ + (ψ + j) = (g.val + 1) * ψ + j := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [harg]
  · have hlast : g.val + 1 = q := by
      have hg := g.isLt
      omega
    rw [hlast, Nat.mod_self]
    simp only [Nat.zero_mul, Nat.zero_add]
    have hbase : g.val * ψ + ψ = q * ψ := by
      calc
        g.val * ψ + ψ = (g.val + 1) * ψ := by
          rw [Nat.add_mul, Nat.one_mul]
        _ = q * ψ := by rw [hlast]
    have harg : g.val * ψ + (ψ + j) = q * ψ + j := by
      calc
        g.val * ψ + (ψ + j) = (g.val * ψ + ψ) + j := by omega
        _ = q * ψ + j := by rw [hbase]
    rw [harg, add_self_mod]

/-- The physical role of every total cell offset is the offset modulo psi.
This is deliberately not restricted to j < psi. -/
theorem cell_role {q ψ : Nat}
    (ring : DirectedRing (q * ψ)) (g : Fin q) (j : Nat) :
    (cell ring g j).val % ψ = j % ψ := by
  have hdvd : ψ ∣ q * ψ := by
    refine ⟨q, ?_⟩
    simp [Nat.mul_comm]
  change ((g.val * ψ + j) % (q * ψ)) % ψ = j % ψ
  rw [Nat.mod_mod_of_dvd _ hdvd]
  simp [Nat.add_mod]

/-- One physical right move increments the total PrepWord.cell offset.
No within-group bound is required. -/
theorem rightNeighbor_cell {q ψ : Nat}
    (ring : DirectedRing (q * ψ)) (g : Fin q) (j : Nat) :
    ring.rightNeighbor (cell ring g j) = cell ring g (j + 1) := by
  apply Fin.ext
  change (((g.val * ψ + j) % (q * ψ) + 1) % (q * ψ)) =
    (g.val * ψ + (j + 1)) % (q * ψ)
  rw [mod_succ_eq]
  simp only [Nat.add_assoc]

/-- The concrete modular left neighbor is inverse to the concrete modular
right neighbor on every nonempty DirectedRing. -/
theorem left_rightNeighbor {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  change ((((i.val + 1) % n) + n - 1) % n) = i.val
  by_cases hs : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : i.val + 1 + n - 1 = i.val + n := by omega
    rw [he, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt i.isLt]
  · have ht : i.val + 1 = n := by
      have hi := i.isLt
      omega
    rw [ht, Nat.mod_self]
    have hn := ring.hn
    have hl : n - 1 < n := by omega
    simp only [Nat.zero_add, Nat.mod_eq_of_lt hl]
    omega

/-- A positive total offset has the expected one-step predecessor.  This is
valid across repeated wraps as well as within a single group. -/
theorem leftNeighbor_cell {q ψ : Nat}
    (ring : DirectedRing (q * ψ)) (g : Fin q) {j : Nat} (hj : 0 < j) :
    ring.leftNeighbor (cell ring g j) = cell ring g (j - 1) := by
  have hsub : j - 1 + 1 = j := by omega
  have hnext :
      ring.rightNeighbor (cell ring g (j - 1)) = cell ring g j := by
    simpa [hsub] using rightNeighbor_cell ring g (j - 1)
  calc
    ring.leftNeighbor (cell ring g j) =
        ring.leftNeighbor (ring.rightNeighbor (cell ring g (j - 1))) := by
          rw [hnext]
    _ = cell ring g (j - 1) := left_rightNeighbor ring _

/-- k literal physical right-neighbor moves. -/
def rightSteps {n : Nat} (ring : DirectedRing n) : Nat → Fin n → Fin n
  | 0, i => i
  | k + 1, i => ring.rightNeighbor (rightSteps ring k i)

/-- k literal physical left-neighbor moves. -/
def leftSteps {n : Nat} (ring : DirectedRing n) : Nat → Fin n → Fin n
  | 0, i => i
  | k + 1, i => ring.leftNeighbor (leftSteps ring k i)

/-- Exact total-offset accounting for any number of right moves. -/
theorem rightSteps_cell {q ψ : Nat}
    (ring : DirectedRing (q * ψ)) (g : Fin q) (j k : Nat) :
    rightSteps ring k (cell ring g j) = cell ring g (j + k) := by
  induction k with
  | zero => simp [rightSteps]
  | succ k ih =>
      simp only [rightSteps]
      rw [ih, rightNeighbor_cell]
      rfl

/-- Exact total-offset accounting for left moves while the displayed Nat
offset has not been exhausted. -/
theorem leftSteps_cell {q ψ : Nat}
    (ring : DirectedRing (q * ψ)) (g : Fin q) {j k : Nat} (hk : k ≤ j) :
    leftSteps ring k (cell ring g j) = cell ring g (j - k) := by
  induction k generalizing j with
  | zero => simp [leftSteps]
  | succ k ih =>
      have hk0 : k ≤ j := by omega
      have hpos : 0 < j - k := by omega
      simp only [leftSteps]
      rw [ih hk0, leftNeighbor_cell ring g hpos]
      have he : j - k - 1 = j - (k + 1) := by omega
      rw [he]

/-! ## A1 geometry -/

/-- A1 after k <= psi physical right moves has advanced exactly k physical
cells and exactly k units of its position countdown. -/
theorem a1_after_k {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    {j k : Nat} (hj : j < ψ) (hk : k ≤ ψ) :
    rightSteps ring k (cell ring g j) = cell ring g (j + k) :=
  rightSteps_cell ring g j k

/-- After exactly psi A1 moves, the reader is at the same saved role in the
successor logical group. -/
theorem a1_after_psi {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    {j : Nat} (hj : j < ψ) :
    rightSteps ring ψ (cell ring g j) = cell ring (successorGroup g) j := by
  rw [rightSteps_cell]
  rw [Nat.add_comm j ψ]
  exact source_target_wrap ring g j

/-- The A1 landing has the exact saved physical role. -/
theorem a1_after_psi_role {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    {j : Nat} (hj : j < ψ) :
    (rightSteps ring ψ (cell ring g j)).val % ψ = j := by
  rw [a1_after_psi h4 ring g hj, cell_role, Nat.mod_eq_of_lt hj]

/-! ## A2 geometry -/

/-- A2(saved j), starting at offset j+psi-1, after k <= psi-1 physical left
moves is exactly at offset j+psi-1-k. -/
theorem a2_after_k {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    {j k : Nat} (hj : j < ψ) (hk : k ≤ ψ - 1) :
    leftSteps ring k (cell ring g (j + ψ - 1)) =
      cell ring g (j + ψ - 1 - k) := by
  exact leftSteps_cell ring g (by omega)

/-- After exactly psi-1 left moves A2(saved j) lands at source role j. -/
theorem a2_after_pred {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    {j : Nat} (hj : j < ψ) :
    leftSteps ring (ψ - 1) (cell ring g (j + ψ - 1)) = cell ring g j := by
  have h := a2_after_k (q:=q) (ψ:=ψ) h4 ring g
    (j:=j) (k:=ψ - 1) hj (by omega)
  have he : j + ψ - 1 - (ψ - 1) = j := by omega
  rw [he] at h
  exact h

/-- For saved role zero, the A2 start is the source group's terminal cell. -/
theorem a2_start_zero_terminal {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q) :
    cell ring g (0 + ψ - 1) = cell ring g (ψ - 1) := by
  simp

/-- For positive saved role j, the A2 start is role j-1 in the successor
logical group.  When q=1 this is intentionally the same physical group. -/
theorem a2_start_pos_successor {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    {j : Nat} (hj : j < ψ) (hpos : 0 < j) :
    cell ring g (j + ψ - 1) = cell ring (successorGroup g) (j - 1) := by
  have h := source_target_wrap ring g (j - 1)
  have he : j + ψ - 1 = ψ + (j - 1) := by omega
  rw [he]
  exact h

/-! ## Label guards from global index-mod-psi labels -/

/-- The source landing cell carries the saved label. -/
theorem sourceJ_label {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    (C : Fin (q * ψ) → AgentState ψ)
    (labels : ∀ i, (C i).label.val = i.val % ψ)
    {j : Nat} (hj : j < ψ) :
    (C (cell ring g j)).label.val = j := by
  calc
    (C (cell ring g j)).label.val = (cell ring g j).val % ψ := labels _
    _ = j % ψ := cell_role ring g j
    _ = j := Nat.mod_eq_of_lt hj

/-- The successor-group target landing cell carries the same saved label. -/
theorem targetJ_label {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    (C : Fin (q * ψ) → AgentState ψ)
    (labels : ∀ i, (C i).label.val = i.val % ψ)
    {j : Nat} (hj : j < ψ) :
    (C (cell ring (successorGroup g) j)).label.val = j := by
  calc
    (C (cell ring (successorGroup g) j)).label.val =
        (cell ring (successorGroup g) j).val % ψ := labels _
    _ = j % ψ := cell_role ring (successorGroup g) j
    _ = j := Nat.mod_eq_of_lt hj

/-- A1's actual landing cell satisfies the saved-label guard. -/
theorem a1_landing_label {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    (C : Fin (q * ψ) → AgentState ψ)
    (labels : ∀ i, (C i).label.val = i.val % ψ)
    {j : Nat} (hj : j < ψ) :
    (C (rightSteps ring ψ (cell ring g j))).label.val = j := by
  rw [a1_after_psi h4 ring g hj]
  exact targetJ_label h4 ring g C labels hj

/-- A2's actual landing cell satisfies the saved-label guard. -/
theorem a2_landing_label {q ψ : Nat}
    (h4 : 4 ≤ ψ) (ring : DirectedRing (q * ψ)) (g : Fin q)
    (C : Fin (q * ψ) → AgentState ψ)
    (labels : ∀ i, (C i).label.val = i.val % ψ)
    {j : Nat} (hj : j < ψ) :
    (C (leftSteps ring (ψ - 1) (cell ring g (j + ψ - 1)))).label.val = j := by
  rw [a2_after_pred h4 ring g hj]
  exact sourceJ_label h4 ring g C labels hj

/-! ## Explicit q=1 overlap witnesses -/

def q1Ring4 : DirectedRing (1 * 4) := ⟨by decide⟩
def q1Group : Fin 1 := ⟨0, by decide⟩

theorem q1_successor_self :
    successorGroup (q:=1) q1Group = q1Group := by
  apply Fin.ext
  decide

theorem q1_wrap_witness :
    cell (q:=1) (ψ:=4) q1Ring4 q1Group (4 + 2) =
      cell (q:=1) (ψ:=4) q1Ring4 q1Group 2 := by
  have h := source_target_wrap (q:=1) (ψ:=4) q1Ring4 q1Group 2
  rw [q1_successor_self] at h
  exact h

theorem q1_a1_overlap :
    rightSteps q1Ring4 4
        (cell (q:=1) (ψ:=4) q1Ring4 q1Group 2) =
      cell (q:=1) (ψ:=4) q1Ring4 q1Group 2 := by
  have h := a1_after_psi (q:=1) (ψ:=4) (by decide)
    q1Ring4 q1Group (j:=2) (by decide)
  rw [q1_successor_self] at h
  exact h

theorem q1_a2_overlap :
    leftSteps q1Ring4 3
        (cell (q:=1) (ψ:=4) q1Ring4 q1Group (2 + 4 - 1)) =
      cell (q:=1) (ψ:=4) q1Ring4 q1Group 2 := by
  exact a2_after_pred (q:=1) (ψ:=4) (by decide)
    q1Ring4 q1Group (j:=2) (by decide)

theorem q1_a2_start_overlap :
    cell (q:=1) (ψ:=4) q1Ring4 q1Group (2 + 4 - 1) =
      cell (q:=1) (ψ:=4) q1Ring4 q1Group 1 := by
  have h := a2_start_pos_successor (q:=1) (ψ:=4) (by decide)
    q1Ring4 q1Group (j:=2) (by decide) (by decide)
  rw [q1_successor_self] at h
  exact h

/-- Compatibility spelling for consumers of the preparation-word cell map. -/
theorem cell_wrap {q ψ : Nat} (ring : DirectedRing (q * ψ))
    (g : Fin q) (j : Nat) :
    cell ring g (ψ+j)=cell ring (successorGroup g) j :=
  source_target_wrap ring g j

/-- The boundary edge is also an instance of this unrestricted identity. -/
theorem right_cell {q ψ : Nat} (ring : DirectedRing (q * ψ))
    (g : Fin q) (j : Nat) :
    ring.rightNeighbor (cell ring g j)=cell ring g (j+1) :=
  rightNeighbor_cell ring g j

/-- Any offset in the two-group window lies in the source or its successor.
For q=1 these alternatives may denote the same physical cells. -/
theorem cell_two_groups {q ψ : Nat} (ring : DirectedRing (q * ψ))
    (g : Fin q) {k : Nat} (hk : k < 2*ψ) :
    (∃ j, j<ψ ∧ cell ring g k=cell ring g j) ∨
      (∃ j, j<ψ ∧ cell ring g k=cell ring (successorGroup g) j) := by
  by_cases h : k<ψ
  · exact Or.inl ⟨k,h,rfl⟩
  · let j := k-ψ
    have hj : j<ψ := by dsimp [j]; omega
    have he : k=ψ+j := by dsimp [j]; omega
    right
    refine ⟨j,hj,?_⟩
    rw [he]
    exact source_target_wrap ring g j

#print axioms source_target_wrap
#print axioms cell_role
#print axioms rightNeighbor_cell
#print axioms left_rightNeighbor
#print axioms leftNeighbor_cell
#print axioms rightSteps_cell
#print axioms leftSteps_cell
#print axioms a1_after_k
#print axioms a1_after_psi
#print axioms a1_after_psi_role
#print axioms a2_after_k
#print axioms a2_after_pred
#print axioms a2_start_zero_terminal
#print axioms a2_start_pos_successor
#print axioms sourceJ_label
#print axioms targetJ_label
#print axioms a1_landing_label
#print axioms a2_landing_label
#print axioms q1_successor_self
#print axioms q1_wrap_witness
#print axioms q1_a1_overlap
#print axioms q1_a2_overlap
#print axioms q1_a2_start_overlap
#print axioms cell_wrap
#print axioms right_cell
#print axioms cell_two_groups

end PPLLAstraR5ReaderGeometry

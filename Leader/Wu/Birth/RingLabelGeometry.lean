import Leader.Core.Basic
import Leader.Core.ModArith
import Leader.Wu.Birth.CheckChainRing
import Init.Data.List.Count
import Init.Data.List.Nat.Pairwise

/-!
# Protocol-independent ring label geometry

All statements concern only `Fin n → Fin psi` labels. The R1-ring import
is used for its existing `cell`, `right_cell`, and `cell_ne` geometry;
no transition, leader, or configuration hypothesis is used.

`Barrier` uses natural-number residues, avoiding ambiguity about Fin
addition. `DirectedRing` already supplies `0 < n`. No divisibility or
relative-size assumption is needed for rooted existence or local arcs.

`ArcNoBarrier ... W` checks the W-1 internal edges of a W-cell arc.
For W ≤ n these are distinct cells; for larger W the same theorem
applies to the indicated walk, including every wrap it traverses.

Rooted labels start at zero and increase until the closing edge. That
edge is a barrier exactly when psi does not divide n. This is static
geometry, not a claim of protocol invariance or dynamic reachability.
-/

set_option autoImplicit false

namespace RingLabelGeometry

open BirthCheckChainR1Ring (cell right_cell cell_ne)

variable {n psi : Nat}

/-- An edge is named by its initiator; its responder is the right neighbor. -/
def Barrier (ring : DirectedRing n) (lab : Fin n → Fin psi)
    (e : Fin n) : Prop :=
  (lab (ring.rightNeighbor e)).val ≠ ((lab e).val + 1) % psi

instance instDecidableBarrier (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (e : Fin n) :
    Decidable (Barrier ring lab e) := by
  unfold Barrier
  infer_instance

/-- Every physical edge is counted once, including the n=1 self-edge. -/
def barrierCount (ring : DirectedRing n) (lab : Fin n → Fin psi) : Nat :=
  (List.finRange n).countP (fun e => decide (Barrier ring lab e))

def NoBarrier (ring : DirectedRing n) (lab : Fin n → Fin psi) : Prop :=
  ∀ e, ¬ Barrier ring lab e

@[simp] theorem barrierCount_eq_zero (ring : DirectedRing n)
    (lab : Fin n → Fin psi) :
    barrierCount ring lab = 0 ↔ NoBarrier ring lab := by
  simp [barrierCount, NoBarrier, List.countP_eq_zero]

theorem barrierCount_pos_iff (ring : DirectedRing n)
    (lab : Fin n → Fin psi) :
    0 < barrierCount ring lab ↔ ∃ e, Barrier ring lab e := by
  simp [barrierCount, List.countP_pos_iff]

theorem barrierCount_eq_one_of_iff (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (e0 : Fin n)
    (h : ∀ e, Barrier ring lab e ↔ e = e0) :
    barrierCount ring lab = 1 := by
  calc
    barrierCount ring lab = (List.finRange n).count e0 := by
      unfold barrierCount
      rw [List.count_eq_countP]
      apply List.countP_congr
      intro e _
      simp only [decide_eq_true_eq, beq_iff_eq]
      exact h e
    _ = 1 := by rw [(List.nodup_finRange n).count]; simp

@[simp] theorem cell_zero (ring : DirectedRing n) (s : Fin n) :
    cell ring s 0 = s := by
  apply Fin.ext
  simp [cell, Nat.mod_eq_of_lt s.isLt]

@[simp] theorem cell_full_turn (ring : DirectedRing n) (s : Fin n) :
    cell ring s n = s := by
  apply Fin.ext
  simp [cell, Nat.add_mod, Nat.mod_eq_of_lt s.isLt]

/-- Only edges between consecutive cells of the indicated arc are required. -/
def ArcNoBarrier (ring : DirectedRing n) (lab : Fin n → Fin psi)
    (s : Fin n) (W : Nat) : Prop :=
  ∀ j, j + 1 < W → ¬ Barrier ring lab (cell ring s j)

/-- Local modular telescoping, with no global divisibility assumption. -/
theorem arc_labels (ring : DirectedRing n) (lab : Fin n → Fin psi)
    (s : Fin n) {W : Nat} (h : ArcNoBarrier ring lab s W) :
    ∀ k, k < W →
      (lab (cell ring s k)).val = ((lab s).val + k) % psi := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa only [cell_zero, Nat.add_zero] using
        (Nat.mod_eq_of_lt (lab s).isLt).symm
  | succ k ih =>
      intro hk
      have hk' : k + 1 < W := hk
      have he : (lab (ring.rightNeighbor (cell ring s k))).val =
          ((lab (cell ring s k)).val + 1) % psi :=
        Classical.byContradiction (fun hb => h k hk' hb)
      rw [right_cell] at he
      calc
        (lab (cell ring s (k + 1))).val =
            ((lab (cell ring s k)).val + 1) % psi := he
        _ = (((lab s).val + k) % psi + 1) % psi := by
          rw [ih (by omega)]
        _ = ((lab s).val + (k + 1)) % psi := by
          rw [mod_succ_eq, Nat.add_assoc]

theorem labels_of_no_barrier (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (h : NoBarrier ring lab)
    (s : Fin n) (k : Nat) :
    (lab (cell ring s k)).val = ((lab s).val + k) % psi :=
  arc_labels ring lab s (W := k + 1)
    (fun j _ => h (cell ring s j)) k (by omega)

/-- One complete lap adds n modulo psi and returns to its initial label. -/
theorem dvd_of_no_barrier (hpsi : 0 < psi) (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (h : NoBarrier ring lab) : psi ∣ n := by
  let z : Fin n := ⟨0, ring.hn⟩
  have hv := labels_of_no_barrier ring lab h z n
  rw [cell_full_turn] at hv
  exact dvd_of_lt_mod_add_eq (lab z).val n psi hpsi (lab z).isLt hv

theorem barrier_exists_of_not_dvd (hpsi : 0 < psi)
    (ring : DirectedRing n) (lab : Fin n → Fin psi)
    (hndvd : ¬ psi ∣ n) : ∃ e, Barrier ring lab e := by
  apply Classical.byContradiction
  intro h
  apply hndvd
  apply dvd_of_no_barrier hpsi ring lab
  intro e he
  exact h ⟨e, he⟩

/-- The unrotated residue labeling of the physical indices. -/
def ruler (hpsi : 0 < psi) (i : Fin n) : Fin psi :=
  ⟨i.val % psi, Nat.mod_lt _ hpsi⟩

/-- Spatial rotation: read the base ruler at physical index (s+i) mod n. -/
def RulerRotation (hpsi : 0 < psi) (ring : DirectedRing n)
    (lab : Fin n → Fin psi) : Prop :=
  ∃ s : Fin n, ∀ i : Fin n,
    lab i = ruler hpsi (cell ring s i.val)

theorem no_barrier_iff_ruler_of_dvd (hpsi : 0 < psi)
    (ring : DirectedRing n) (lab : Fin n → Fin psi) (hdiv : psi ∣ n) :
    NoBarrier ring lab ↔ RulerRotation hpsi ring lab := by
  constructor
  · intro h
    let z : Fin n := ⟨0, ring.hn⟩
    let s : Fin n := ⟨(lab z).val,
      Nat.lt_of_lt_of_le (lab z).isLt (Nat.le_of_dvd ring.hn hdiv)⟩
    refine ⟨s, ?_⟩
    intro i
    apply Fin.ext
    change (lab i).val = ((s.val + i.val) % n) % psi
    rw [Nat.mod_mod_of_dvd _ hdiv]
    have hv := labels_of_no_barrier ring lab h z i.val
    have hc : cell ring z i.val = i := by
      apply Fin.ext
      simp [cell, z, Nat.mod_eq_of_lt i.isLt]
    rw [hc] at hv
    exact hv
  · rintro ⟨s, hs⟩
    have hp (i : Fin n) : (lab i).val = (s.val + i.val) % psi := by
      have hv := congrArg Fin.val (hs i)
      change (lab i).val = ((s.val + i.val) % n) % psi at hv
      rw [Nat.mod_mod_of_dvd _ hdiv] at hv
      exact hv
    intro e hb
    apply hb
    calc
      (lab (ring.rightNeighbor e)).val =
          (s.val + (e.val + 1) % n) % psi := hp _
      _ = (s.val + (e.val + 1)) % psi := by
        rw [Nat.add_mod, Nat.mod_mod_of_dvd _ hdiv, ← Nat.add_mod]
      _ = ((s.val + e.val) % psi + 1) % psi := by
        simpa only [Nat.add_assoc] using
          (mod_succ_eq (s.val + e.val) psi).symm
      _ = ((lab e).val + 1) % psi := by rw [hp e]

/-- Clockwise distance, represented in the interval [0,n). -/
def offset (r i : Fin n) : Nat :=
  if r.val ≤ i.val then i.val - r.val else n + i.val - r.val

theorem offset_lt (r i : Fin n) : offset r i < n := by
  have hr := r.isLt
  have hi := i.isLt
  unfold offset
  split <;> omega

theorem cell_offset (ring : DirectedRing n) (r i : Fin n) :
    cell ring r (offset r i) = i := by
  apply Fin.ext
  have hi := i.isLt
  change (r.val + offset r i) % n = i.val
  unfold offset
  split
  · rename_i h
    have ha : r.val + (i.val - r.val) = i.val := by omega
    rw [ha]
    exact Nat.mod_eq_of_lt hi
  · rename_i h
    have hr := r.isLt
    have ha : r.val + (n + i.val - r.val) = n + i.val := by omega
    rw [ha]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hi]

theorem offset_cell (ring : DirectedRing n) (r : Fin n)
    (k : Nat) (hk : k < n) : offset r (cell ring r k) = k := by
  apply Classical.byContradiction
  intro h
  exact cell_ne ring r (offset_lt r _) hk h
    (cell_offset ring r (cell ring r k))

/-- The root has label zero; every possible barrier enters the root. -/
def RootedAt (ring : DirectedRing n) (lab : Fin n → Fin psi)
    (r : Fin n) : Prop :=
  (lab r).val = 0 ∧
    ∀ e, Barrier ring lab e → ring.rightNeighbor e = r

/-- This construction also works when psi exceeds n or does not divide n. -/
def rootedLabel (hpsi : 0 < psi) (r : Fin n) (i : Fin n) : Fin psi :=
  ⟨offset r i % psi, Nat.mod_lt _ hpsi⟩

theorem rootedLabel_cell (hpsi : 0 < psi) (ring : DirectedRing n)
    (r : Fin n) (k : Nat) (hk : k < n) :
    (rootedLabel hpsi r (cell ring r k)).val = k % psi := by
  change offset r (cell ring r k) % psi = k % psi
  rw [offset_cell ring r k hk]

theorem rootedLabel_rooted (hpsi : 0 < psi) (ring : DirectedRing n)
    (r : Fin n) : RootedAt ring (rootedLabel hpsi r) r := by
  refine ⟨by simp [rootedLabel, offset], ?_⟩
  intro e hb
  let k := offset r e
  have hk : k < n := offset_lt r e
  have hc : cell ring r k = e := cell_offset ring r e
  by_cases hs : k + 1 < n
  · have hgood : (rootedLabel hpsi r (ring.rightNeighbor e)).val =
        ((rootedLabel hpsi r e).val + 1) % psi := by
      rw [← hc, right_cell,
        rootedLabel_cell hpsi ring r (k + 1) hs,
        rootedLabel_cell hpsi ring r k hk]
      exact (mod_succ_eq k psi).symm
    exact (hb hgood).elim
  · have hkn : k + 1 = n := by omega
    rw [← hc, right_cell, hkn, cell_full_turn]

theorem rooted_exists (hpsi : 0 < psi) (ring : DirectedRing n)
    (r : Fin n) : ∃ lab : Fin n → Fin psi, RootedAt ring lab r :=
  ⟨rootedLabel hpsi r, rootedLabel_rooted hpsi ring r⟩

/-- Every rooted labeling has the same values at all offsets before wrap. -/
theorem rooted_labels (ring : DirectedRing n) (lab : Fin n → Fin psi)
    (r : Fin n) (h : RootedAt ring lab r) (k : Nat) (hk : k < n) :
    (lab (cell ring r k)).val = k % psi := by
  have ha : ArcNoBarrier ring lab r n := by
    intro j hj hb
    have hx := h.2 (cell ring r j) hb
    rw [right_cell] at hx
    have hne : cell ring r (j + 1) ≠ cell ring r 0 :=
      cell_ne ring r hj ring.hn (by omega)
    exact hne (hx.trans (cell_zero ring r).symm)
  have hv := arc_labels ring lab r ha k hk
  simpa only [h.1, Nat.zero_add] using hv

/-- The field predicate determines the entire labeling, not just its seam. -/
theorem rooted_eq (hpsi : 0 < psi) (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (r : Fin n) (h : RootedAt ring lab r) :
    lab = rootedLabel hpsi r := by
  funext i
  apply Fin.ext
  have hv := rooted_labels ring lab r h (offset r i) (offset_lt r i)
  rw [cell_offset] at hv
  exact hv

/-- The physical initiator of the edge entering the root. -/
def incomingEdge (ring : DirectedRing n) (r : Fin n) : Fin n :=
  cell ring r (n - 1)

theorem incomingEdge_eq_leftNeighbor (ring : DirectedRing n) (r : Fin n) :
    incomingEdge ring r = ring.leftNeighbor r := by
  apply Fin.ext
  change (r.val + (n - 1)) % n = (r.val + n - 1) % n
  have hn := ring.hn
  have ha : r.val + (n - 1) = r.val + n - 1 := by omega
  rw [ha]

theorem right_incoming (ring : DirectedRing n) (r : Fin n) :
    ring.rightNeighbor (incomingEdge ring r) = r := by
  unfold incomingEdge
  rw [right_cell]
  have hn := ring.hn
  have hw : n - 1 + 1 = n := by omega
  rw [hw, cell_full_turn]

theorem enters_root_iff (ring : DirectedRing n) (r e : Fin n) :
    ring.rightNeighbor e = r ↔ e = incomingEdge ring r := by
  constructor
  · intro he
    let k := offset r e
    have hk : k < n := offset_lt r e
    have hc : cell ring r k = e := cell_offset ring r e
    have hx : cell ring r (k + 1) = r := by
      rw [← right_cell, hc]
      exact he
    have hb : ¬ k + 1 < n := by
      intro hk1
      have hne : cell ring r (k + 1) ≠ cell ring r 0 :=
        cell_ne ring r hk1 ring.hn (by omega)
      exact hne (hx.trans (cell_zero ring r).symm)
    have hkn : k = n - 1 := by omega
    calc
      e = cell ring r k := hc.symm
      _ = incomingEdge ring r := congrArg (cell ring r) hkn
  · rintro rfl
    exact right_incoming ring r

/-- At the closing edge, the successor residue is n mod psi. -/
theorem rooted_incoming_barrier_iff (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (r : Fin n) (h : RootedAt ring lab r) :
    Barrier ring lab (incomingEdge ring r) ↔ ¬ psi ∣ n := by
  have hn := ring.hn
  have hk : n - 1 < n := by omega
  have hw : n - 1 + 1 = n := by omega
  unfold Barrier
  rw [right_incoming, h.1]
  change (0 ≠ ((lab (cell ring r (n - 1))).val + 1) % psi) ↔ ¬ psi ∣ n
  rw [rooted_labels ring lab r h (n - 1) hk, mod_succ_eq, hw]
  constructor
  · intro hne hd
    exact hne (Nat.mod_eq_zero_of_dvd hd).symm
  · intro hnd he
    exact hnd (Nat.dvd_of_mod_eq_zero he.symm)

/-- Exact barrier classification for every rooted labeling. -/
theorem rooted_barrier_iff (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (r : Fin n) (h : RootedAt ring lab r)
    (e : Fin n) :
    Barrier ring lab e ↔ e = incomingEdge ring r ∧ ¬ psi ∣ n := by
  constructor
  · intro hb
    have he := (enters_root_iff ring r e).mp (h.2 e hb)
    refine ⟨he, ?_⟩
    rw [he] at hb
    exact (rooted_incoming_barrier_iff ring lab r h).mp hb
  · rintro ⟨he, hd⟩
    rw [he]
    exact (rooted_incoming_barrier_iff ring lab r h).mpr hd

/-- Explicit uniqueness, with the count and the actual left neighbor. -/
theorem rooted_unique_barrier_of_not_dvd (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (r : Fin n) (h : RootedAt ring lab r)
    (hndvd : ¬ psi ∣ n) :
    Barrier ring lab (ring.leftNeighbor r) ∧
      (∀ e, Barrier ring lab e ↔ e = ring.leftNeighbor r) ∧
      barrierCount ring lab = 1 := by
  have hi : ∀ e, Barrier ring lab e ↔ e = incomingEdge ring r := by
    intro e
    rw [rooted_barrier_iff ring lab r h e]
    simp [hndvd]
  have hc := barrierCount_eq_one_of_iff ring lab (incomingEdge ring r) hi
  have hb : Barrier ring lab (incomingEdge ring r) := (hi _).mpr rfl
  rw [incomingEdge_eq_leftNeighbor] at hi hb
  exact ⟨hb, hi, hc⟩

theorem rooted_no_barrier_of_dvd (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (r : Fin n) (h : RootedAt ring lab r)
    (hdiv : psi ∣ n) : NoBarrier ring lab := by
  intro e hb
  exact ((rooted_barrier_iff ring lab r h e).mp hb).2 hdiv

theorem rooted_barrierCount (ring : DirectedRing n)
    (lab : Fin n → Fin psi) (r : Fin n) (h : RootedAt ring lab r) :
    barrierCount ring lab = if psi ∣ n then 0 else 1 := by
  by_cases hd : psi ∣ n
  · rw [if_pos hd]
    exact (barrierCount_eq_zero ring lab).mpr
      (rooted_no_barrier_of_dvd ring lab r h hd)
  · rw [if_neg hd]
    exact (rooted_unique_barrier_of_not_dvd ring lab r h hd).2.2

/-- The explicit witness has zero or one barriers according to divisibility. -/
theorem rootedLabel_barrierCount (hpsi : 0 < psi) (ring : DirectedRing n)
    (r : Fin n) :
    barrierCount ring (rootedLabel hpsi r) = if psi ∣ n then 0 else 1 :=
  rooted_barrierCount ring (rootedLabel hpsi r) r
    (rootedLabel_rooted hpsi ring r)

end RingLabelGeometry

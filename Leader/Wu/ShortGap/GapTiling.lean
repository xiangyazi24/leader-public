import Leader.Wu.ShortGap.DenialTransportPlacement

/-!
# Placement gaps tile the physical ring

`Leader/Wu/ShortGap/DenialTransportPlacement.lean` derived the token-walk rearm
layout from an ordered placement and stated the ring-size bound `2*n*(m+n)`
under the explicit hypothesis `Σ_g gapLen ring P g = n`.  This file proves
that hypothesis, so the bound needs only `RootsOrdered ring P` and `1 < m`.

**Upper bound (`≤ n`).**  Flatten all gap edges into one list
`allGapEdges = flatMap over g of [gapEdge g 0, …, gapEdge g (gapLen g - 1)]`.
Its length is `Σ_g gapLen g`, it has no duplicates by `gapEdge_injective`
(which uses `RootsOrdered`), and it is a list of elements of `Fin n`; the core
lemma `List.Nodup.length_le_of_subset` against `List.finRange n` gives
`Σ_g gapLen g ≤ n`.

**Lower bound (`≥ n`).**  Every vertex `v` is covered by some gap: take a root
`g` whose clockwise distance to `v` is minimal (a finite argmin over
`Fin (m'+1)`, proved by induction without Mathlib).  If `v` were not strictly
inside gap `g`, the successor root `ring.rightNeighbor g` would lie on the
clockwise arc from `P.root g` to `v` and would be strictly closer to `v`
(`cwDist_lt_of_on_arc`), contradicting minimality.  Hence
`List.finRange n ⊆ allGapEdges`, and `List.Nodup.length_le_of_subset` applied
to the duplicate-free `finRange n` gives `n ≤ Σ_g gapLen g`.  This direction
does not use `RootsOrdered`: the gaps of any injective placement with `1 < m`
cover the ring.

**`m = 1` is excluded honestly.**  With a single root, `ring.rightNeighbor g
= g`, so `gapLen ring P g = cwDist a a = 0` and the sum is `0`, not `n`.  The
single-root case is degenerate for the two-endpoint denial protocol anyway
(a root would compare its declaration with itself), so the tiling identity and
the ring-size bound are stated for `1 < m`, exactly the hypothesis already
carried by every capstone in this series.

**Abstraction boundary.**  Unchanged from the two companion files: only the
uniform (all-denial) outcome is modelled; the token is a single carrier with no
forgery, staleness, or interference; the shared endpoint root enters only via
disjoint edge sets (the shared-root two-receipt join is in
`Leader/Wu/ShortGap/TwoDenialRearm.lean`, not imported); `RootsOrdered` remains a
hypothesis on the placement.  Nothing here claims complete leader
stabilization or a final complexity bound.
-/

namespace ShortGapGapTiling

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping
open ShortGapDenialTransport
open ShortGapDenialTransportPlacement

set_option autoImplicit false

/-! ## Additional clockwise-distance arithmetic -/

/-- Walking the clockwise distance from `a` to `b` lands exactly at `b`. -/
theorem stepFrom_cwDist {n : Nat} (a b : Fin n) :
    stepFrom a (cwDist a b) = b := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  show (a.val + cwDist a b) % n = b.val
  rw [cwDist_eq]
  split
  · rw [show a.val + (b.val - a.val) = b.val by omega]
    exact Nat.mod_eq_of_lt hb
  · rw [show a.val + (b.val + n - a.val) = b.val + n by omega,
      Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hb

/-- If `r'` lies on the clockwise arc from `r` to `v` and `r' ≠ r`, then `v`
is strictly closer to `r'` than to `r`. -/
theorem cwDist_lt_of_on_arc {n : Nat} (r r' v : Fin n) (hne : r ≠ r')
    (harc : cwDist r r' ≤ cwDist r v) : cwDist r' v < cwDist r v := by
  have hr := r.isLt
  have hr' := r'.isLt
  have hv := v.isLt
  have hne' : r.val ≠ r'.val := fun h => hne (Fin.ext h)
  simp only [cwDist_eq] at harc ⊢
  split at harc <;> split at harc <;> (try split) <;> (try split) <;> omega

/-- A finite argmin over a nonempty index type, without Mathlib. -/
theorem exists_argmin : ∀ {m : Nat} (f : Fin (m + 1) → Nat),
    ∃ g, ∀ g', f g ≤ f g'
  | 0, f => ⟨0, fun g' => by
      have h0 : g' = 0 := Fin.ext (by have := g'.isLt; omega)
      rw [h0]
      exact Nat.le_refl _⟩
  | m + 1, f => by
      obtain ⟨g, hg⟩ := exists_argmin (fun i : Fin (m + 1) => f i.succ)
      by_cases h : f 0 ≤ f g.succ
      · refine ⟨0, fun g' => ?_⟩
        rcases Fin.eq_zero_or_eq_succ g' with h0 | ⟨j, hj⟩
        · rw [h0]
          exact Nat.le_refl _
        · rw [hj]
          exact Nat.le_trans h (hg j)
      · refine ⟨g.succ, fun g' => ?_⟩
        rcases Fin.eq_zero_or_eq_succ g' with h0 | ⟨j, hj⟩
        · rw [h0]
          omega
        · rw [hj]
          exact hg j

/-! ## Coverage: every vertex lies strictly inside some gap -/

/-- The root closest to `v` (clockwise) owns the gap containing `v`.  This
uses only injectivity of the placement, not `RootsOrdered`. -/
theorem exists_gap_containing {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hm : 1 < m) (v : Fin n) :
    ∃ g, cwDist (P.root g) v < gapLen ring P g := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨g, hg⟩ :=
    exists_argmin (fun g : Fin (m' + 1) => cwDist (P.root g) v)
  refine ⟨g, Nat.lt_of_not_le (fun hcon => ?_)⟩
  have harc : cwDist (P.root g) (P.root (ring.rightNeighbor g)) ≤
      cwDist (P.root g) v := by
    unfold gapLen at hcon
    exact hcon
  have hne : P.root g ≠ P.root (ring.rightNeighbor g) :=
    fun h => rightNeighbor_ne ring hm g (P.root_injective h).symm
  have hlt := cwDist_lt_of_on_arc _ _ v hne harc
  have hmin := hg (ring.rightNeighbor g)
  omega

/-! ## The flattened gap-edge list -/

/-- The edges of gap `g` in clockwise order. -/
def gapEdgeList {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (g : Fin m) : List (Fin n) :=
  List.ofFn (fun k : Fin (gapLen ring P g) => gapEdge P g k.val)

/-- All gap edges, gap by gap. -/
def allGapEdges {n m : Nat} (ring : DirectedRing m) (P : Placement n m) :
    List (Fin n) :=
  (List.finRange m).flatMap (gapEdgeList ring P)

theorem length_allGapEdges {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) :
    (allGapEdges ring P).length = (List.ofFn fun g => gapLen ring P g).sum := by
  unfold allGapEdges
  rw [List.length_flatMap]
  simp only [gapEdgeList, List.length_ofFn]
  unfold List.finRange
  rw [List.map_ofFn]
  rfl

private theorem nodup_ofFn_of_injective {k : Nat} {A : Type}
    (f : Fin k → A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

theorem gapEdgeList_nodup {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hord : RootsOrdered ring P) (g : Fin m) :
    (gapEdgeList ring P g).Nodup := by
  apply nodup_ofFn_of_injective
  intro k k' hkk'
  exact Fin.ext
    (gapEdge_injective ring P hord g g k.val k'.val k.isLt k'.isLt hkk').2

/-- Under ring order the flattened edge list has no duplicates. -/
theorem allGapEdges_nodup {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hord : RootsOrdered ring P) :
    (allGapEdges ring P).Nodup := by
  unfold allGapEdges List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun g _ => gapEdgeList_nodup ring P hord g, ?_⟩
  refine List.Pairwise.imp ?_ (List.nodup_finRange m)
  intro g g' hne x hx y hy
  rw [gapEdgeList, List.mem_ofFn] at hx hy
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨k', rfl⟩ := hy
  intro heq
  exact hne
    (gapEdge_injective ring P hord g g' k.val k'.val k.isLt k'.isLt heq).1

/-! ## The tiling identity -/

/-- Disjoint gaps cannot exceed the ring. -/
theorem gapLen_sum_le {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hord : RootsOrdered ring P) :
    (List.ofFn fun g => gapLen ring P g).sum ≤ n := by
  have hsub : allGapEdges ring P ⊆ List.finRange n := by
    intro x _
    exact List.mem_finRange x
  have h := List.Nodup.length_le_of_subset (allGapEdges_nodup ring P hord) hsub
  rw [length_allGapEdges, List.length_finRange] at h
  exact h

/-- The gaps of any injective placement with at least two roots cover the
ring. -/
theorem le_gapLen_sum {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hm : 1 < m) :
    n ≤ (List.ofFn fun g => gapLen ring P g).sum := by
  have hcover : List.finRange n ⊆ allGapEdges ring P := by
    intro v _
    obtain ⟨g, hg⟩ := exists_gap_containing ring P hm v
    unfold allGapEdges
    rw [List.mem_flatMap]
    refine ⟨g, List.mem_finRange g, ?_⟩
    rw [gapEdgeList, List.mem_ofFn]
    exact ⟨⟨cwDist (P.root g) v, hg⟩, stepFrom_cwDist _ _⟩
  have h := List.Nodup.length_le_of_subset (List.nodup_finRange n) hcover
  rw [length_allGapEdges, List.length_finRange] at h
  exact h

/-- Ordered gaps tile the physical ring: `Σ_g gapLen g = n`. -/
theorem gapLen_sum_eq {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hord : RootsOrdered ring P) (hm : 1 < m) :
    (List.ofFn fun g => gapLen ring P g).sum = n :=
  Nat.le_antisymm (gapLen_sum_le ring P hord) (le_gapLen_sum ring P hm)

theorem placementLayout_totalLength_eq {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hord : RootsOrdered ring P) (hm : 1 < m) :
    (placementLayout ring P hord hm).totalLength = n := by
  rw [placementLayout_totalLength]
  exact gapLen_sum_eq ring P hord hm

/-! ## Ring-size bounds with only the ordering hypothesis -/

/-- Repeated candidate rounds with placement-derived denial transport have
expected work at most `2*n*(m+n)`; only ring order of the roots is assumed. -/
theorem placementCandidateRestart_truncatedCost_le_ring
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (hord : RootsOrdered ring P)
    (T : Nat) :
    truncatedActiveCostNumerator
        (placementCandidateRestartStep ring P hord hm)
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * n * (m + n)) :=
  placementCandidateRestart_truncatedCost_le_of_tiling ring hm P hn hord
    (gapLen_sum_eq ring P hord hm) T

private theorem ring_budget_eq (n m : Nat) :
    2 * (n * m) + 2 * n * n = 2 * n * (m + n) := by
  rw [Nat.mul_add]
  ac_rfl

/-- Reciprocal success tail at the ring-size budget. -/
theorem placementCandidateRestart_success_one_minus_inv_factor_ring
    {n m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (hord : RootsOrdered ring P) :
    (factor - 1) * n ^ (factor * (2 * n * (m + n))) ≤
      factor * successCount
        (placementCandidateRestartStep ring P hord hm)
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (2 * n * (m + n))) := by
  have h := placementCandidateRestart_success_one_minus_inv_factor
    ring hm P hn hord (factor := factor)
  rw [gapLen_sum_eq ring P hord hm, ring_budget_eq] at h
  exact h

#print axioms exists_gap_containing
#print axioms allGapEdges_nodup
#print axioms gapLen_sum_le
#print axioms le_gapLen_sum
#print axioms gapLen_sum_eq
#print axioms placementCandidateRestart_truncatedCost_le_ring
#print axioms placementCandidateRestart_success_one_minus_inv_factor_ring

end ShortGapGapTiling

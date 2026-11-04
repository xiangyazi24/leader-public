import Leader.L3.Headline.Stages
import Leader.L3.Bank.Counter
import Leader.L3.Density

/-!
Geometric lemmas for Appendix C.9--C.10.

No theorem asserting StageGrantSpatialSupportBridge is included:
the global cyclic counting/selection lemma is still missing.
There are no changes to the physical transition or the protocol.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- B.6, expressed in the integer bad-edge convention of Density. -/
theorem headlineGrantGoodEdgeIff {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e : Fin n) :
    badRoleEdge b ring R e = 0 ↔
      goodPair b (R e) (R (ring.rightNeighbor e)) = true := by
  cases hg : goodPair b (R e) (R (ring.rightNeighbor e)) with
  | false =>
      simp [badRoleEdge, roleBadSet, Density.bit, hg]
  | true =>
      simp [badRoleEdge, roleBadSet, Density.bit, hg]

/-- Within a good run, a digit strictly below b forces the next digit. -/
theorem headlineGrantGoodDigitSuccessor {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e : Fin n)
    (hgood : badRoleEdge b ring R e = 0)
    (hsmall : (R e).val < b) :
    (R (ring.rightNeighbor e)).val = (R e).val + 1 := by
  have hp := (goodPair_iff b (R e)
    (R (ring.rightNeighbor e))).1
      ((headlineGrantGoodEdgeIff b ring R e).1 hgood)
  rcases hp with h | h | h
  · exact h.2
  · omega
  · omega

/-- The only good successors of the top digit are zero and spacer. -/
theorem headlineGrantGoodTopSuccessor {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e : Fin n)
    (hgood : badRoleEdge b ring R e = 0)
    (htop : (R e).val = b) :
    (R (ring.rightNeighbor e)).val = 0 ∨
      (R (ring.rightNeighbor e)).val = b + 1 := by
  have hp := (goodPair_iff b (R e)
    (R (ring.rightNeighbor e))).1
      ((headlineGrantGoodEdgeIff b ring R e).1 hgood)
  rcases hp with h | h | h
  · omega
  · exact h.2
  · omega

/-- A good spacer has zero as its unique successor. -/
theorem headlineGrantGoodSpacerSuccessor {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e : Fin n)
    (hgood : badRoleEdge b ring R e = 0)
    (hspacer : (R e).val = b + 1) :
    (R (ring.rightNeighbor e)).val = 0 := by
  have hp := (goodPair_iff b (R e)
    (R (ring.rightNeighbor e))).1
      ((headlineGrantGoodEdgeIff b ring R e).1 hgood)
  rcases hp with h | h | h
  · omega
  · omega
  · exact h.2

/-- If the edge into a zero-role root is good, its source
has top or spacer role, never an interior digit role. -/
theorem headlineGrantGoodIncomingRoot {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (e root : Fin n)
    (hinc : ring.rightNeighbor e = root)
    (hzero : (R root).val = 0)
    (hgood : badRoleEdge b ring R e = 0) :
    (R e).val = b ∨ (R e).val = b + 1 := by
  have hp := (goodPair_iff b (R e)
    (R (ring.rightNeighbor e))).1
      ((headlineGrantGoodEdgeIff b ring R e).1 hgood)
  rw [hinc] at hp
  rcases hp with h | h | h
  · omega
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- A zero-role root followed by b good digit edges is complete.
The induction is on the actual clockwise site function. -/
theorem headlineGrantGoodRootComplete {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n)
    (hzero : (C root).pack.val = 0)
    (hgood : ∀ j : Nat, j < (compileAdvice q).b →
      badRoleEdge (compileAdvice q).b ring
        (fun i : Fin n => (C i).pack)
        (Counter.site ring root j) = 0) :
    Counter.Complete ring C root := by
  unfold Counter.Complete
  intro j
  induction j with
  | zero =>
      intro _
      simpa only [Counter.site] using hzero
  | succ k ih =>
      intro hj
      have hprev : k ≤ (compileAdvice q).b := by omega
      have hsmall : k < (compileAdvice q).b := by omega
      have hpack :
          (C (Counter.site ring root k)).pack.val = k :=
        ih hprev
      have hstep := headlineGrantGoodDigitSuccessor
        (compileAdvice q).b ring
        (fun i : Fin n => (C i).pack)
        (Counter.site ring root k) (hgood k hsmall)
        (by omega : (C (Counter.site ring root k)).pack.val <
          (compileAdvice q).b)
      change (C (ring.rightNeighbor
        (Counter.site ring root k))).pack.val = k + 1
      omega

/-- Full-support goodness implies completion once the root has role zero.
The incoming and outgoing boundary edges are not silently discarded. -/
theorem headlineGrantGoodSupportComplete {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n)
    (hzero : (C root).pack.val = 0)
    (hgood : ∀ e : Fin n, Counter.Support q ring root e →
      badRoleEdge (compileAdvice q).b ring
        (fun i : Fin n => (C i).pack) e = 0) :
    Counter.Complete ring C root := by
  apply headlineGrantGoodRootComplete ring C root hzero
  intro j hj
  have hmem : Counter.Support q ring root
      (Counter.site ring root j) :=
    Or.inr ⟨j, by omega, rfl⟩
  exact hgood _ hmem

/-- No complete root can hide at a proper interior digit. -/
theorem headlineGrantNoInteriorRoot {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n) (hc : Counter.Complete ring C root)
    (j : Nat) (hj : 1 ≤ j) (hb : j ≤ (compileAdvice q).b) :
    (C (Counter.site ring root j)).pack.val ≠ 0 := by
  have hv := hc j hb
  omega

/-- The top outgoing edge of a good complete support starts either
another root immediately or a spacer. -/
theorem headlineGrantTopChoice {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n) (hc : Counter.Complete ring C root)
    (hgood : badRoleEdge (compileAdvice q).b ring
      (fun i : Fin n => (C i).pack)
      (Counter.site ring root (compileAdvice q).b) = 0) :
    (C (Counter.site ring root
      ((compileAdvice q).b + 1))).pack.val = 0 ∨
    (C (Counter.site ring root
      ((compileAdvice q).b + 1))).pack.val =
        (compileAdvice q).b + 1 := by
  exact headlineGrantGoodTopSuccessor
    (compileAdvice q).b ring
    (fun i : Fin n => (C i).pack)
    (Counter.site ring root (compileAdvice q).b)
    hgood (hc (compileAdvice q).b (Nat.le_refl _))

/-- Two additional good boundary edges yield the b+1 or b+2
root-location alternative in C.9. This claims role zero at
the next location, not yet completion of the next support. -/
theorem headlineGrantNextRootRole {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (root : Fin n) (hc : Counter.Complete ring C root)
    (htop : badRoleEdge (compileAdvice q).b ring
      (fun i : Fin n => (C i).pack)
      (Counter.site ring root (compileAdvice q).b) = 0)
    (hspacer : badRoleEdge (compileAdvice q).b ring
      (fun i : Fin n => (C i).pack)
      (Counter.site ring root ((compileAdvice q).b + 1)) = 0) :
    (C (Counter.site ring root
      ((compileAdvice q).b + 1))).pack.val = 0 ∨
    (C (Counter.site ring root
      ((compileAdvice q).b + 2))).pack.val = 0 := by
  rcases headlineGrantTopChoice ring C root hc htop with hz | hs
  · exact Or.inl hz
  · exact Or.inr (headlineGrantGoodSpacerSuccessor
      (compileAdvice q).b ring
      (fun i : Fin n => (C i).pack)
      (Counter.site ring root ((compileAdvice q).b + 1))
      hspacer hs)

/-- A clockwise site has its ordinary linear coordinate
whenever the entire path remains before the modular boundary. -/
theorem headlineGrantSiteValWithin {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ j : Nat, root.val + j < n →
      (Counter.site ring root j).val = root.val + j := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [Counter.site]
  | succ k ih =>
      intro hbound
      have hprev : root.val + k < n := by omega
      have hlast : root.val + k + 1 < n := by omega
      change (ring.rightNeighbor
        (Counter.site ring root k)).val = root.val + (k + 1)
      rw [rightNeighbor_val, ih hprev, Nat.mod_eq_of_lt hlast]
      omega

/-- For a nonzero root, its incoming source is literally
the previous ordinary coordinate (there is no wrap at zero). -/
theorem headlineGrantIncomingValWithin {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hpositive : 0 < root.val)
    (hinc : ring.rightNeighbor e = root) :
    e.val + 1 = root.val := by
  have hmod := congrArg Fin.val hinc
  rw [rightNeighbor_val] at hmod
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    omega
  · have heq : e.val + 1 = n := by
      have he := e.isLt
      omega
    rw [heq, Nat.mod_self] at hmod
    omega

/-- Exact integer-coordinate enclosure of an inclusive counter
support in a non-wrapping arc: root-1 through root+b. -/
theorem headlineGrantStraightSupportBounds {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hpositive : 0 < root.val)
    (htop : root.val + (compileAdvice q).b < n)
    (hs : Counter.Support q ring root e) :
    root.val ≤ e.val + 1 ∧
      e.val ≤ root.val + (compileAdvice q).b := by
  rcases hs with hinc | ⟨j, hj, heq⟩
  · have hv := headlineGrantIncomingValWithin
      ring root e hpositive hinc
    omega
  · have hwithin : root.val + j < n := by omega
    have hv := headlineGrantSiteValWithin ring root j hwithin
    have he := congrArg Fin.val heq
    rw [hv] at he
    omega

/-- Spacing by w=b+2 separates the complete inclusive supports,
provided both supports are inside a single non-wrapping arc. -/
theorem headlineGrantStraightSupportsDisjoint {n q : Nat}
    (ring : DirectedRing n) (first second : Fin n)
    (hfirst : 0 < first.val)
    (hsecond : 0 < second.val)
    (hfirstTop : first.val + (compileAdvice q).b < n)
    (hsecondTop : second.val + (compileAdvice q).b < n)
    (hgap : first.val + (compileAdvice q).b + 2 ≤ second.val)
    (e : Fin n) :
    ¬ (Counter.Support q ring first e ∧
       Counter.Support q ring second e) := by
  intro h
  have hf := headlineGrantStraightSupportBounds
    (q := q) ring first e hfirst hfirstTop h.1
  have hs := headlineGrantStraightSupportBounds
    (q := q) ring second e hsecond hsecondTop h.2
  omega

/-- A list with pairwise w-separated linear coordinates has
pairwise disjoint supports. The cyclic wrap exclusion must be
handled when the list is selected; it is not assumed here. -/
theorem headlineGrantLinearFamilyDisjoint {n q : Nat}
    (ring : DirectedRing n) (roots : List (Fin n))
    (hpositive : ∀ root : Fin n, root ∈ roots → 0 < root.val)
    (htop : ∀ root : Fin n, root ∈ roots →
      root.val + (compileAdvice q).b < n)
    (hgap : ∀ root other : Fin n,
      root ∈ roots → other ∈ roots → root ≠ other →
      root.val + (compileAdvice q).b + 2 ≤ other.val ∨
      other.val + (compileAdvice q).b + 2 ≤ root.val) :
    ∀ root other : Fin n,
      root ∈ roots → other ∈ roots → root ≠ other →
      ∀ e : Fin n,
        ¬ (Counter.Support q ring root e ∧
           Counter.Support q ring other e) := by
  intro root other hr ho hne e hh
  rcases hgap root other hr ho hne with hforward | hreverse
  · exact headlineGrantStraightSupportsDisjoint (q := q)
      ring root other (hpositive root hr) (hpositive other ho)
      (htop root hr) (htop other ho) hforward e hh
  · exact headlineGrantStraightSupportsDisjoint (q := q)
      ring other root (hpositive other ho) (hpositive root hr)
      (htop other ho) (htop root hr) hreverse e ⟨hh.2, hh.1⟩

/-- A defect linearly more than 2R behind a root does
not violate the root's rear-buffer constraint. -/
theorem headlineGrantRearGapWithoutWrap {n : Nat}
    (ring : DirectedRing n) (defect root : Fin n)
    (radius : Nat)
    (hgap : defect.val + 2 * radius < root.val) :
    ∀ d : Nat, 1 ≤ d → d ≤ 2 * radius →
      Counter.site ring defect d ≠ root := by
  intro d _ hd heq
  have hwithin : defect.val + d < n := by
    have hr := root.isLt
    omega
  have hv := headlineGrantSiteValWithin ring defect d hwithin
  have he := congrArg Fin.val heq
  rw [hv] at he
  omega

/-- Build the exact target's per-root conjuncts from a zero-role
root, a good inclusive edge support, and the rear-buffer test. -/
theorem headlineGrantBufferedOfLocalData {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius : Nat) (root : Fin n)
    (hroot : (C root).pack.val = 0)
    (hgood : ∀ e : Fin n,
      Counter.Support (ceilLogTwo n) ring root e →
      badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
        (fun i : Fin n => (C i).pack) e = 0)
    (hbehind : ∀ e : Fin n,
      badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
        (fun i : Fin n => (C i).pack) e = 1 →
      ∀ d : Nat, 1 ≤ d → d ≤ 2 * radius →
        Counter.site ring e d ≠ root) :
    HeadlineGrantBufferedCounter ring C radius root := by
  exact ⟨headlineGrantGoodSupportComplete
      (q := ceilLogTwo n) ring C root hroot hgood,
    hgood, hbehind⟩

/-- The uniform b>=18 width ratio used in (C.10):
w/(b+1) is at most 20/19. -/
theorem headlineGrantWidthRatio (b : Nat) (hb : 18 ≤ b) :
    19 * (b + 2) ≤ 20 * (b + 1) := by
  omega

/-- Cleared-denominator certificate for the final strict
489/1000 inequality in (C.10). This is numerical only;
it does not construct or count a family of roots. -/
theorem headlineGrantThinningConstant :
    489 * (2 * 4096 * 64 * 19) <
      1000 * ((4096 - 20) * 64 * 19 -
        20 * 4096 - 2 * 64 * 19) := by
  omega

end L3

/-!
Fixed-block counting alternative to the maximal-good-run
decomposition in Appendix C.9--C.10.

No declaration below
asserts StageGrantSpatialSupportBridge. In particular, the
physical buffered-root witness for each good fixed block is still
an open Prop, defined at the end of this section.

A fixed candidate block has 2*w edges. Its left endpoint is
2*radius+1+2*w*k. The preceding 2*radius edges and the whole
candidate block are inspected. Hence the defect window of bin k
is the ordinary integer interval
[1+2*w*k, 1+2*w*k+2*radius+2*w).
This eliminates cyclic wraparound at the rear of the selected root.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-! ## A. Finite-list incidence counting without Finset -/

/-- The count of the Boolean union of two predicates is at most the
sum of their counts. All counts retain multiplicities of the list. -/
private theorem headlineGrantCountOrLe {α : Type}
    (xs : List α) (p q : α → Bool) :
    xs.countP (fun x => p x || q x) ≤
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;>
        simp [List.countP_cons, hp, hq] at * <;> omega

/-- Union bound for the sites hit by a list of separate windows.
The orientation is cover edge site, not cover site edge. -/
private theorem headlineGrantCountAnyLe {α β : Type}
    (xs : List α) (ys : List β) (cover : β → α → Bool) :
    xs.countP (fun x => ys.any (fun y => cover y x)) ≤
      (ys.map (fun y => xs.countP (cover y))).sum := by
  induction ys with
  | nil =>
      simp
  | cons y ys ih =>
      simp only [List.any_cons, List.map_cons, List.sum_cons]
      exact Nat.le_trans
        (headlineGrantCountOrLe xs (cover y)
          (fun x => ys.any (fun z => cover z x)))
        (Nat.add_le_add_left ih (xs.countP (cover y)))

/-- Summing a pointwise cardinality cap over a finite defect list. -/
private theorem headlineGrantSumCap {α : Type}
    (xs : List α) (f : α → Nat) (cap : Nat) :
    (∀ x, x ∈ xs → f x ≤ cap) →
      (xs.map f).sum ≤ xs.length * cap := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro h
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul]
      omega

/-- A union of D windows, each hitting at most cap entries of xs,
blocks at most D*cap entries. This is the finite-list form of
the first charging inequality in item (a). -/
theorem headlineGrantWindowUnionBound {α β : Type}
    (xs : List α) (defectEdges : List β)
    (cover : β → α → Bool) (cap : Nat)
    (hcap : ∀ e, e ∈ defectEdges →
      xs.countP (cover e) ≤ cap) :
    xs.countP (fun x => defectEdges.any (fun e => cover e x)) ≤
      defectEdges.length * cap := by
  exact Nat.le_trans
    (headlineGrantCountAnyLe xs defectEdges cover)
    (headlineGrantSumCap defectEdges
      (fun e => xs.countP (cover e)) cap hcap)

/-- Finite complement identity, used to count good fixed blocks. -/
private theorem headlineGrantCountPartition {α : Type}
    (xs : List α) (p : α → Bool) :
    xs.length =
      xs.countP p + xs.countP (fun x => !(p x)) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      cases hp : p x <;>
        simp [List.countP_cons, hp] at * <;> omega

/-- The number of hits in any bounded integer strip
[A,A+width) is at most width, independently of the size of
the ambient List.range. This proof uses no Finset. -/
private theorem headlineGrantCountStrip (p : Nat → Bool)
    (A width : Nat)
    (hstrip : ∀ k : Nat, p k = true →
      A ≤ k ∧ k < A + width) :
    ∀ limit : Nat,
      (List.range limit).countP p ≤ width := by
  have hstrong :
      ∀ limit : Nat,
        (List.range limit).countP p ≤ limit - A ∧
        (List.range limit).countP p ≤ width := by
    intro limit
    induction limit with
    | zero =>
        simp
    | succ limit ih =>
        have hstep :
            (List.range (limit + 1)).countP p =
              (List.range limit).countP p +
                (if p limit then 1 else 0) := by
          cases hp : p limit <;>
            simp [List.range_succ, List.countP_append, hp]
        obtain ⟨hleft, hright⟩ := ih
        rw [hstep]
        cases hp : p limit with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            exact ⟨by omega, by omega⟩
        | true =>
            have hhit := hstrip limit hp
            simp only [↓reduceIte]
            exact ⟨by omega, by omega⟩
  intro limit
  exact (hstrong limit).2

/-! ## A.2 Exact finite integer windows of candidate blocks -/

/-- A defect at integer coordinate edge poisons fixed block k if it
lies in the 2*radius rear buffer or the following 2*w-edge block. -/
def headlineGrantWindowHit (w radius k edge : Nat) : Bool :=
  decide (1 + 2 * w * k ≤ edge ∧
    edge < 1 + 2 * w * k + 2 * radius + 2 * w)

theorem headlineGrantWindowHit_iff (w radius k edge : Nat) :
    headlineGrantWindowHit w radius k edge = true ↔
      1 + 2 * w * k ≤ edge ∧
      edge < 1 + 2 * w * k + 2 * radius + 2 * w := by
  simp [headlineGrantWindowHit]

/-- At one fixed defective coordinate, the uniformly spaced
candidate blocks it can poison number at most floor(radius/w)+3.
The proof traps all matching indices in an integer strip ending
at floor(edge/(2*w)). No square-root or modular API is used. -/
theorem headlineGrantWindowPerDefectCap
    (w radius edge limit : Nat) (hw : 0 < w) :
    (List.range limit).countP
      (fun k => headlineGrantWindowHit w radius k edge) ≤
      radius / w + 3 := by
  apply headlineGrantCountStrip
    (fun k => headlineGrantWindowHit w radius k edge)
    (edge / (2 * w) - (radius / w + 2))
    (radius / w + 3) ?_ limit
  intro k hk
  have hhit := (headlineGrantWindowHit_iff w radius k edge).1 hk
  have hstride : 0 < 2 * w := by omega
  have hindex : k ≤ edge / (2 * w) := by
    apply (Nat.le_div_iff_mul_le hstride).2
    calc
      k * (2 * w) = (2 * w) * k := Nat.mul_comm _ _
      _ ≤ edge := by omega
  have hdecomp : radius % w + w * (radius / w) = radius :=
    Nat.mod_add_div radius w
  have hrem : radius % w < w := Nat.mod_lt _ hw
  have hnear : radius < w * (radius / w + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hdouble :
      2 * radius + 1 ≤ (2 * w) * (radius / w + 1) := by
    have hh : 2 * radius < 2 * (w * (radius / w + 1)) :=
      Nat.mul_lt_mul_of_pos_left hnear (by omega)
    rw [← Nat.mul_assoc] at hh
    omega
  have hproduct :
      (k + radius / w + 2) * (2 * w) =
        (2 * w) * k + (2 * w) * (radius / w + 1) +
          2 * w := by
    have ha :
        k + radius / w + 2 = k + (radius / w + 1) + 1 := by
      omega
    rw [ha]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hlarge : edge < (k + radius / w + 2) * (2 * w) := by
    rw [hproduct]
    omega
  have hquot : edge / (2 * w) < k + radius / w + 2 :=
    (Nat.div_lt_iff_lt_mul hstride).2 hlarge
  constructor <;> omega

/-- Filtering before taking any is equivalent to a conjunction
inside any. This identifies real bad-edge lists with bad-edge
incidence over the full finite ring. -/
private theorem headlineGrantAnyFilter {α : Type}
    (xs : List α) (p q : α → Bool) :
    (xs.filter p).any q =
      xs.any (fun x => p x && q x) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      cases hp : p x <;>
        simp [List.filter_cons, List.any_cons, hp, ih]

/-- countP of a Bool predicate equals the sum of its 0/1
indicators. Needed to connect List.finRange with Density.N. -/
private theorem headlineGrantCountBitSum {α : Type}
    (xs : List α) (p : α → Bool) :
    xs.countP p =
      (xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      cases hp : p x <;>
        simp [List.countP_cons, List.map_cons, List.sum_cons,
          hp, ih] <;> omega

theorem headlineGrantCountAsDensity {n : Nat}
    (o : Fin n → Bool) :
    (List.finRange n).countP o = Density.N o := by
  rw [headlineGrantCountBitSum]
  simp [Density.N, Density.bit, List.finRange, List.map_ofFn]
  rfl

/-- Actual bad-edge count = cardinality of the filtered list,
not an assumed independent particle count. -/
theorem headlineGrantBadEdgesLength {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) :
    ((List.finRange n).filter (badSet ring C)).length =
      defects ring C := by
  have hh := headlineGrantCountAsDensity (badSet ring C)
  rw [List.countP_eq_length_filter] at hh
  rw [← defects_eq_N] at hh
  exact hh

/-- (a), fixed-block version. Every actual defect poisons at most
floor(radius/w)+3 blocks. The List.finRange n is the current
physical role word. There is no assumption on private scratch. -/
theorem headlineGrantBlockedBinsCount {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit : Nat) :
    (List.range limit).countP
      (fun k => (List.finRange n).any (fun e =>
        badSet ring C e &&
        headlineGrantWindowHit
          ((compileAdvice (ceilLogTwo n)).b + 2)
          radius k e.val)) ≤
      defects ring C *
        (radius / ((compileAdvice (ceilLogTwo n)).b + 2) + 3) := by
  have hcap : ∀ e : Fin n,
      e ∈ (List.finRange n).filter (badSet ring C) →
      (List.range limit).countP (fun k =>
        headlineGrantWindowHit
          ((compileAdvice (ceilLogTwo n)).b + 2)
          radius k e.val) ≤
        radius / ((compileAdvice (ceilLogTwo n)).b + 2) + 3 := by
    intro e _
    exact headlineGrantWindowPerDefectCap
      ((compileAdvice (ceilLogTwo n)).b + 2)
      radius e.val limit (by omega)
  have hbound := headlineGrantWindowUnionBound
    (List.range limit)
    ((List.finRange n).filter (badSet ring C))
    (fun e k => headlineGrantWindowHit
      ((compileAdvice (ceilLogTwo n)).b + 2)
      radius k e.val)
    (radius / ((compileAdvice (ceilLogTwo n)).b + 2) + 3)
    hcap
  have hfun :
      (fun k => ((List.finRange n).filter (badSet ring C)).any
        (fun e => headlineGrantWindowHit
          ((compileAdvice (ceilLogTwo n)).b + 2)
          radius k e.val)) =
      (fun k => (List.finRange n).any
        (fun e => badSet ring C e &&
          headlineGrantWindowHit
            ((compileAdvice (ceilLogTwo n)).b + 2)
            radius k e.val)) := by
    funext k
    exact headlineGrantAnyFilter (List.finRange n)
      (badSet ring C) (fun e => headlineGrantWindowHit
        ((compileAdvice (ceilLogTwo n)).b + 2)
        radius k e.val)
  rw [hfun, headlineGrantBadEdgesLength ring C] at hbound
  exact hbound

/-- A direct mass statement for the complement of the blocked
candidate bins, without a maximal-run decomposition. -/
theorem headlineGrantUnblockedBinsMass {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit : Nat) :
    limit ≤
      (List.range limit).countP
        (fun k => !((List.finRange n).any (fun e =>
          badSet ring C e &&
          headlineGrantWindowHit
            ((compileAdvice (ceilLogTwo n)).b + 2)
            radius k e.val))) +
      defects ring C *
        (radius / ((compileAdvice (ceilLogTwo n)).b + 2) + 3) := by
  have hpart := headlineGrantCountPartition
    (List.range limit)
    (fun k => (List.finRange n).any (fun e =>
      badSet ring C e &&
      headlineGrantWindowHit
        ((compileAdvice (ceilLogTwo n)).b + 2)
        radius k e.val))
  have hblocked := headlineGrantBlockedBinsCount
    ring C radius limit
  rw [List.length_range] at hpart
  omega

/-! ## B. Local forced root in a sufficiently long good role walk -/

/-- Distance to the NEXT zero role when the present role is nonzero.
A top digit may choose either zero or a one-step spacer. -/
private def headlineGrantRootDistance (b : Nat)
    (role : Fin (b + 2)) : Nat :=
  if role.val = 0 then 0
  else if role.val = b + 1 then 1
  else b + 2 - role.val

private theorem headlineGrantRootDistancePositive
    (b : Nat) (role : Fin (b + 2))
    (hne : role.val ≠ 0) :
    0 < headlineGrantRootDistance b role ∧
      headlineGrantRootDistance b role ≤ b + 1 := by
  unfold headlineGrantRootDistance
  split
  · contradiction
  · split
    · omega
    · have hlt := role.isLt
      omega

/-- The distance strictly decreases on every good role edge until
a zero role is reached. -/
private theorem headlineGrantRootDistanceDrop
    (b : Nat) (before after : Fin (b + 2))
    (hg : goodPair b before after = true)
    (hne : before.val ≠ 0) :
    headlineGrantRootDistance b after <
      headlineGrantRootDistance b before := by
  have hp := (goodPair_iff b before after).1 hg
  rcases hp with h | h | h
  · obtain ⟨hsmall, hstep⟩ := h
    have hbeforeTop : before.val ≠ b + 1 := by omega
    have hafterZero : after.val ≠ 0 := by omega
    have hafterTop : after.val ≠ b + 1 := by omega
    have hb :
        headlineGrantRootDistance b before =
          b + 2 - before.val := by
      simp [headlineGrantRootDistance, hne, hbeforeTop]
    have ha :
        headlineGrantRootDistance b after =
          b + 2 - after.val := by
      simp [headlineGrantRootDistance, hafterZero, hafterTop]
    rw [hb, ha]
    omega
  · obtain ⟨htop, hchoice⟩ := h
    have hbeforeTop : before.val ≠ b + 1 := by omega
    have hb : headlineGrantRootDistance b before = 2 := by
      simp [headlineGrantRootDistance, hne, hbeforeTop]
      omega
    rcases hchoice with hzero | hspacer
    · have ha : headlineGrantRootDistance b after = 0 := by
        simp [headlineGrantRootDistance, hzero]
      omega
    · have hafterZero : after.val ≠ 0 := by omega
      have ha : headlineGrantRootDistance b after = 1 := by
        simp [headlineGrantRootDistance, hafterZero, hspacer]
      omega
  · obtain ⟨hspacer, hzero⟩ := h
    have hb : headlineGrantRootDistance b before = 1 := by
      simp [headlineGrantRootDistance, hne, hspacer]
    have ha : headlineGrantRootDistance b after = 0 := by
      simp [headlineGrantRootDistance, hzero]
    omega

/-- Among b+2 consecutive sites whose intervening b+1 edges
are good, a zero-role root exists. No run partition is needed.
The witness index is at most b+1. -/
theorem headlineGrantGoodWalkContainsRoot {n : Nat}
    (b : Nat) (ring : DirectedRing n)
    (R : Fin n → Fin (b + 2)) (start : Fin n)
    (hgood : ∀ j : Nat, j < b + 1 →
      goodPair b (R (Counter.site ring start j))
        (R (Counter.site ring start (j + 1))) = true) :
    ∃ j : Nat, j ≤ b + 1 ∧
      (R (Counter.site ring start j)).val = 0 := by
  by_cases hex : ∃ j : Nat, j ≤ b + 1 ∧
      (R (Counter.site ring start j)).val = 0
  · exact hex
  · have hnonzero : ∀ j : Nat, j ≤ b + 1 →
        (R (Counter.site ring start j)).val ≠ 0 := by
      intro j hj hz
      exact hex ⟨j, hj, hz⟩
    have hscore : ∀ j : Nat, j ≤ b + 1 →
        headlineGrantRootDistance b
          (R (Counter.site ring start j)) + j ≤ b + 1 := by
      intro j
      induction j with
      | zero =>
          intro _
          have hb := (headlineGrantRootDistancePositive b
            (R (Counter.site ring start 0))
            (hnonzero 0 (by omega))).2
          simpa using hb
      | succ k ih =>
          intro hj
          have hprev := ih (by omega)
          have hdrop := headlineGrantRootDistanceDrop b
            (R (Counter.site ring start k))
            (R (Counter.site ring start (k + 1)))
            (hgood k (by omega)) (hnonzero k (by omega))
          omega
    have hlast := hscore (b + 1) (by omega)
    have hpos := (headlineGrantRootDistancePositive b
      (R (Counter.site ring start (b + 1)))
      (hnonzero (b + 1) (by omega))).1
    omega

/-! ## First remaining geometric interface: defined, not postulated -/

/-- This is the next concrete unproved Prop. It is the geometric
translation from an unblocked straight integer block to an actual
buffered physical root. Its proof needs the root-distance lemma
above, the straight-support lemmas above, and a no-wrap
backward-edge argument for the rear buffer. Do not use this as
an assumption in a theorem.

The subsequent (still absent) selection theorem must enumerate all
unblocked bins, choose one such root per bin in strictly increasing
block order, show that supports of distinct blocks do not overlap,
and combine the cardinality with the arithmetic inequalities
in StageGrantSpatialSupportBridge. -/
def StageGrantFixedBlockRootWitness {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (C : HeadlineConfiguration n) (radius k : Nat),
    2 * radius + 1 +
      2 * ((compileAdvice (ceilLogTwo n)).b + 2) * (k + 1) ≤ n →
    (∀ e : Fin n,
      1 + 2 * ((compileAdvice (ceilLogTwo n)).b + 2) * k ≤ e.val →
      e.val <
        1 + 2 * ((compileAdvice (ceilLogTwo n)).b + 2) * k +
          2 * radius +
          2 * ((compileAdvice (ceilLogTwo n)).b + 2) →
      badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
        (fun i : Fin n => (C i).pack) e = 0) →
    ∃ root : Fin n,
      2 * radius + 1 +
        2 * ((compileAdvice (ceilLogTwo n)).b + 2) * k <
        root.val ∧
      root.val ≤
        2 * radius + 1 +
          2 * ((compileAdvice (ceilLogTwo n)).b + 2) * k +
          ((compileAdvice (ceilLogTwo n)).b + 2) ∧
      HeadlineGrantBufferedCounter ring C radius root

end L3


/-!
This section proves the fixed-bin local witness, physical
support separation, selected-root list, and uniform bridge
arithmetic using only core Lean 4.33.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Clockwise site coordinates modulo n, with the actual
Counter.site recursion and the actual DirectedRing. -/
theorem headlineGrantSiteValModulo {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ j : Nat,
      (Counter.site ring root j).val = (root.val + j) % n := by
  intro j
  induction j with
  | zero =>
      simp [Counter.site, Nat.mod_eq_of_lt root.isLt]
  | succ k ih =>
      change ((Counter.site ring root k).val + 1) % n =
        (root.val + (k + 1)) % n
      rw [ih, Nat.mod_add_mod]
      congr 1

/-- A short clockwise walk cannot wrap around and land at a
root lying strictly beyond the entire short-walk radius.
This is independent of PACK and the private state. -/
theorem headlineGrantShortReachNoWrap {n : Nat}
    (ring : DirectedRing n) (edge root : Fin n)
    (radius d : Nat)
    (hfar : 2 * radius < root.val)
    (hd : d ≤ 2 * radius)
    (hreach : Counter.site ring edge d = root) :
    edge.val + d = root.val := by
  have hv := headlineGrantSiteValModulo ring edge d
  rw [hreach] at hv
  have hshort : d < n := by
    have hr := root.isLt
    omega
  by_cases hsmall : edge.val + d < n
  · rw [Nat.mod_eq_of_lt hsmall] at hv
    omega
  · have hres : edge.val + d - n < n := by
      have he := edge.isLt
      omega
    have hdecomp :
        edge.val + d = n + (edge.val + d - n) := by
      omega
    rw [hdecomp, Nat.add_mod_left, Nat.mod_eq_of_lt hres] at hv
    have he := edge.isLt
    omega

/-- The physical geometric witness from a straight good block.
The good window begins 2R sites before start; the root is
strictly inside the first half of a 2w block, so the inclusive
incoming and top support edges are inside the window.
The rear buffer excludes both local and wrapped defect paths. -/
theorem headlineGrantStraightBlockRoot {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius start : Nat)
    (hfar : 2 * radius < start)
    (hfit : start +
      2 * ((compileAdvice (ceilLogTwo n)).b + 2) ≤ n)
    (hgood : ∀ e : Fin n,
      start - 2 * radius ≤ e.val →
      e.val < start +
        2 * ((compileAdvice (ceilLogTwo n)).b + 2) →
      badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
        (fun i : Fin n => (C i).pack) e = 0) :
    ∃ root : Fin n,
      start < root.val ∧
      root.val ≤ start + ((compileAdvice (ceilLogTwo n)).b + 2) ∧
      HeadlineGrantBufferedCounter ring C radius root := by
  have hfirst : start + 1 < n := by omega
  have hfirstVal : (⟨start + 1, hfirst⟩ : Fin n).val =
      start + 1 := rfl
  have hwalk : ∀ j : Nat,
      j < (compileAdvice (ceilLogTwo n)).b + 1 →
      goodPair (compileAdvice (ceilLogTwo n)).b
        ((C (Counter.site ring
          (⟨start + 1, hfirst⟩ : Fin n) j)).pack)
        ((C (Counter.site ring
          (⟨start + 1, hfirst⟩ : Fin n) (j + 1))).pack) =
          true := by
    intro j hj
    have hjfit : start + 1 + j < n := by omega
    have hv := headlineGrantSiteValWithin ring
      (⟨start + 1, hfirst⟩ : Fin n) j hjfit
    rw [hfirstVal] at hv
    have he : badRoleEdge
        (compileAdvice (ceilLogTwo n)).b ring
        (fun i : Fin n => (C i).pack)
        (Counter.site ring (⟨start + 1, hfirst⟩ : Fin n) j) = 0 :=
      hgood _ (by omega) (by omega)
    have hp := (headlineGrantGoodEdgeIff
      (compileAdvice (ceilLogTwo n)).b ring
      (fun i : Fin n => (C i).pack)
      (Counter.site ring (⟨start + 1, hfirst⟩ : Fin n) j)).1 he
    change goodPair (compileAdvice (ceilLogTwo n)).b
      ((C (Counter.site ring
        (⟨start + 1, hfirst⟩ : Fin n) j)).pack)
      ((C (Counter.site ring
        (⟨start + 1, hfirst⟩ : Fin n) (j + 1))).pack) = true
    exact hp
  obtain ⟨j, hj, hzero⟩ :=
    headlineGrantGoodWalkContainsRoot
      (compileAdvice (ceilLogTwo n)).b ring
      (fun i : Fin n => (C i).pack)
      (⟨start + 1, hfirst⟩ : Fin n) hwalk
  have hjfit : start + 1 + j < n := by omega
  have hv := headlineGrantSiteValWithin ring
    (⟨start + 1, hfirst⟩ : Fin n) j hjfit
  rw [hfirstVal] at hv
  refine ⟨Counter.site ring (⟨start + 1, hfirst⟩ : Fin n) j,
    ?_, ?_, ?_⟩
  · omega
  · omega
  · apply headlineGrantBufferedOfLocalData ring C radius
      (Counter.site ring (⟨start + 1, hfirst⟩ : Fin n) j)
      hzero
    · intro e hs
      have hpositive :
          0 < (Counter.site ring
            (⟨start + 1, hfirst⟩ : Fin n) j).val := by
        omega
      have htop :
          (Counter.site ring
            (⟨start + 1, hfirst⟩ : Fin n) j).val +
              (compileAdvice (ceilLogTwo n)).b < n := by
        omega
      obtain ⟨hl, hr⟩ := headlineGrantStraightSupportBounds
        (q := ceilLogTwo n) ring
        (Counter.site ring
          (⟨start + 1, hfirst⟩ : Fin n) j) e
        hpositive htop hs
      exact hgood e (by omega) (by omega)
    · intro e hbad d hdlo hdhi hreach
      have hfarRoot :
          2 * radius <
            (Counter.site ring
              (⟨start + 1, hfirst⟩ : Fin n) j).val := by
        omega
      have hcoordinate := headlineGrantShortReachNoWrap ring e
        (Counter.site ring
          (⟨start + 1, hfirst⟩ : Fin n) j)
        radius d hfarRoot hdhi hreach
      have hclean : badRoleEdge
          (compileAdvice (ceilLogTwo n)).b ring
          (fun i : Fin n => (C i).pack) e = 0 :=
        hgood e (by omega) (by omega)
      rw [hbad] at hclean
      cases hclean

/-- The previously defined fixed-block witness is now
closed without any additional global PACK hypothesis. -/
theorem headlineGrantFixedBlockRootWitnessProved {n : Nat}
    (ring : DirectedRing n) :
    StageGrantFixedBlockRootWitness ring := by
  intro C radius k hfit hgood
  have hmul :
      2 * ((compileAdvice (ceilLogTwo n)).b + 2) * (k + 1) =
        2 * ((compileAdvice (ceilLogTwo n)).b + 2) * k +
          2 * ((compileAdvice (ceilLogTwo n)).b + 2) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hmul] at hfit
  apply headlineGrantStraightBlockRoot ring C radius
    (2 * radius + 1 +
      2 * ((compileAdvice (ceilLogTwo n)).b + 2) * k)
    (by omega) (by omega)
  intro e hl hr
  exact hgood e (by omega) (by omega)

/-! ## Fixed-bin choice, without maximal-good-run bookkeeping -/

/-- Width of the inclusive causal edge support. -/
def headlineGrantBinWidth (n : Nat) : Nat :=
  (compileAdvice (ceilLogTwo n)).b + 2

/-- A bin is blocked exactly when an actual defective role edge
lies in its tested integer window. No independence is assumed. -/
def headlineGrantBinBad {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius k : Nat) : Bool :=
  (List.finRange n).any (fun e =>
    badSet ring C e &&
    headlineGrantWindowHit (headlineGrantBinWidth n)
      radius k e.val)

/-- A bin index inside the non-wrapping suffix fits whenever the
end of the last bin fits. -/
theorem headlineGrantBinFits {n : Nat}
    (radius limit k : Nat)
    (hfit : 2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * limit ≤ n)
    (hk : k < limit) :
    2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * (k + 1) ≤ n := by
  have hm := Nat.mul_le_mul_left (2 * headlineGrantBinWidth n)
    (by omega : k + 1 ≤ limit)
  rw [Nat.mul_add, Nat.mul_one] at hm
  calc
    2 * radius + 1 +
        2 * headlineGrantBinWidth n * (k + 1) =
      2 * radius + 1 +
        (2 * headlineGrantBinWidth n * k +
          2 * headlineGrantBinWidth n) := by
        rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n := by omega

/-- Each clean fitted bin has an actual root witness. -/
theorem headlineGrantCleanBinRoot {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius k : Nat)
    (hfit : 2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * (k + 1) ≤ n)
    (hclean : headlineGrantBinBad ring C radius k = false) :
    ∃ root : Fin n,
      2 * radius + 1 +
        2 * (headlineGrantBinWidth n) * k < root.val ∧
      root.val ≤
        2 * radius + 1 +
          2 * (headlineGrantBinWidth n) * k +
            headlineGrantBinWidth n ∧
      HeadlineGrantBufferedCounter ring C radius root := by
  apply headlineGrantFixedBlockRootWitnessProved ring C radius k hfit
  intro e hlo hhi
  have hhit :
      headlineGrantWindowHit (headlineGrantBinWidth n)
        radius k e.val = true :=
    (headlineGrantWindowHit_iff
      (headlineGrantBinWidth n) radius k e.val).2
      ⟨hlo, hhi⟩
  have hset : badSet ring C e = false := by
    cases hs : badSet ring C e with
    | false =>
        rfl
    | true =>
        have hblocked : headlineGrantBinBad ring C radius k = true := by
          unfold headlineGrantBinBad
          apply List.any_eq_true.mpr
          exact ⟨e, List.mem_finRange e, by simp [hs, hhit]⟩
        rw [hblocked] at hclean
        cases hclean
  change Density.bit (badSet ring C e) = 0
  rw [hset]
  rfl

/-- Membership in the filtered integer bin list supplies both
the original bound and the negative defect test. -/
theorem headlineGrantCleanBinMem {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit k : Nat)
    (hk : k ∈
      (List.range limit).filter
        (fun j => !(headlineGrantBinBad ring C radius j))) :
    k < limit ∧ headlineGrantBinBad ring C radius k = false := by
  have hh := List.mem_filter.mp hk
  have hlt : k < limit := List.mem_range.mp hh.1
  have hclean : headlineGrantBinBad ring C radius k = false := by
    cases hb : headlineGrantBinBad ring C radius k with
    | false =>
        rfl
    | true =>
        have hno := hh.2
        simp [hb] at hno
  exact ⟨hlt, hclean⟩

/-- A proof-only deterministic choice from an existing local
physical witness. The fallback is never selected on a clean bin. -/
noncomputable def headlineGrantPickRoot {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius k : Nat) : Fin n := by
  classical
  exact if h : ∃ root : Fin n,
      2 * radius + 1 +
        2 * (headlineGrantBinWidth n) * k < root.val ∧
      root.val ≤ 2 * radius + 1 +
        2 * (headlineGrantBinWidth n) * k +
          headlineGrantBinWidth n ∧
      HeadlineGrantBufferedCounter ring C radius root
    then Classical.choose h
    else ⟨0, ring.hn⟩

theorem headlineGrantPickRootSpec {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius k : Nat)
    (h : ∃ root : Fin n,
      2 * radius + 1 +
        2 * (headlineGrantBinWidth n) * k < root.val ∧
      root.val ≤ 2 * radius + 1 +
        2 * (headlineGrantBinWidth n) * k +
          headlineGrantBinWidth n ∧
      HeadlineGrantBufferedCounter ring C radius root) :
    2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * k <
        (headlineGrantPickRoot ring C radius k).val ∧
    (headlineGrantPickRoot ring C radius k).val ≤
      2 * radius + 1 +
        2 * (headlineGrantBinWidth n) * k +
          headlineGrantBinWidth n ∧
    HeadlineGrantBufferedCounter ring C radius
      (headlineGrantPickRoot ring C radius k) := by
  unfold headlineGrantPickRoot
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem headlineGrantPickCleanRootSpec {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius k : Nat)
    (hfit : 2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * (k + 1) ≤ n)
    (hclean : headlineGrantBinBad ring C radius k = false) :
    2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * k <
        (headlineGrantPickRoot ring C radius k).val ∧
    (headlineGrantPickRoot ring C radius k).val ≤
      2 * radius + 1 +
        2 * (headlineGrantBinWidth n) * k +
          headlineGrantBinWidth n ∧
    HeadlineGrantBufferedCounter ring C radius
      (headlineGrantPickRoot ring C radius k) :=
  headlineGrantPickRootSpec ring C radius k
    (headlineGrantCleanBinRoot ring C radius k hfit hclean)

/-- The roots are selected before future physical scheduler marks.
Every clean fixed bin contributes exactly one list entry. -/
noncomputable def headlineGrantChosenRoots {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit : Nat) : List (Fin n) :=
  ((List.range limit).filter
    (fun k => !(headlineGrantBinBad ring C radius k))).map
      (headlineGrantPickRoot ring C radius)

theorem headlineGrantChosenRootsLength {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit : Nat) :
    (headlineGrantChosenRoots ring C radius limit).length =
      (List.range limit).countP
        (fun k => !(headlineGrantBinBad ring C radius k)) := by
  unfold headlineGrantChosenRoots
  rw [List.length_map]
  exact (List.countP_eq_length_filter).symm

/-- The choice on every filtered index lies in the declared first
half-block and satisfies the literal physical buffered predicate. -/
theorem headlineGrantChosenBinSpec {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit k : Nat)
    (hfit : 2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * limit ≤ n)
    (hk : k ∈ (List.range limit).filter
      (fun j => !(headlineGrantBinBad ring C radius j))) :
    2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * k <
        (headlineGrantPickRoot ring C radius k).val ∧
    (headlineGrantPickRoot ring C radius k).val ≤
      2 * radius + 1 +
        2 * (headlineGrantBinWidth n) * k +
          headlineGrantBinWidth n ∧
    HeadlineGrantBufferedCounter ring C radius
      (headlineGrantPickRoot ring C radius k) := by
  obtain ⟨hlt, hclean⟩ :=
    headlineGrantCleanBinMem ring C radius limit k hk
  exact headlineGrantPickCleanRootSpec ring C radius k
    (headlineGrantBinFits radius limit k hfit hlt) hclean

/-- Distinct retained bins yield roots separated by a whole
inclusive support width, with no cyclic-wrap exception. -/
theorem headlineGrantChosenBinSeparation {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit i j : Nat)
    (hfit : 2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * limit ≤ n)
    (hi : i ∈ (List.range limit).filter
      (fun k => !(headlineGrantBinBad ring C radius k)))
    (hj : j ∈ (List.range limit).filter
      (fun k => !(headlineGrantBinBad ring C radius k)))
    (hij : i ≠ j) :
    (headlineGrantPickRoot ring C radius i).val +
      headlineGrantBinWidth n ≤
        (headlineGrantPickRoot ring C radius j).val ∨
    (headlineGrantPickRoot ring C radius j).val +
      headlineGrantBinWidth n ≤
        (headlineGrantPickRoot ring C radius i).val := by
  have hsi := headlineGrantChosenBinSpec
    ring C radius limit i hfit hi
  have hsj := headlineGrantChosenBinSpec
    ring C radius limit j hfit hj
  by_cases hless : i < j
  · left
    have hm := Nat.mul_le_mul_left (2 * headlineGrantBinWidth n)
      (by omega : i + 1 ≤ j)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  · right
    have hm := Nat.mul_le_mul_left (2 * headlineGrantBinWidth n)
      (by omega : j + 1 ≤ i)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega

/-- Counted root list has no duplicates. The pairwise argument
uses injectivity only on clean bin indices, not on fallback
values of the noncomputable choice function. -/
theorem headlineGrantChosenRootsNodup {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit : Nat)
    (hfit : 2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * limit ≤ n) :
    (headlineGrantChosenRoots ring C radius limit).Nodup := by
  unfold headlineGrantChosenRoots
  have hnd :
      ((List.range limit).filter
        (fun k => !(headlineGrantBinBad ring C radius k))).Nodup :=
    List.Pairwise.filter
      (fun k => !(headlineGrantBinBad ring C radius k))
      (List.nodup_range (n := limit))
  apply (List.pairwise_map).2
  exact List.Pairwise.imp_of_mem
    (fun {i j} hi hj hij heq => by
      have hgap := headlineGrantChosenBinSeparation
        ring C radius limit i j hfit hi hj hij
      have hv := congrArg Fin.val heq
      have hwidth : 0 < headlineGrantBinWidth n := by
        unfold headlineGrantBinWidth
        omega
      rcases hgap with hleft | hright
      · omega
      · omega)
    hnd

/-- All selected roots are literal buffered complete supports. -/
theorem headlineGrantChosenRootsBuffered {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit : Nat)
    (hfit : 2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * limit ≤ n) :
    ∀ root : Fin n,
      root ∈ headlineGrantChosenRoots ring C radius limit →
      HeadlineGrantBufferedCounter ring C radius root := by
  intro root hr
  unfold headlineGrantChosenRoots at hr
  obtain ⟨k, hk, heq⟩ := List.mem_map.mp hr
  have hs := headlineGrantChosenBinSpec
    ring C radius limit k hfit hk
  rw [heq] at hs
  exact hs.2.2

/-- Exact inclusive physical support separation for the selected
root list. The top boundary and incoming-root boundary are both
counted as part of Support. -/
theorem headlineGrantChosenRootsDisjoint {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit : Nat)
    (hfit : 2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * limit ≤ n) :
    ∀ root other : Fin n,
      root ∈ headlineGrantChosenRoots ring C radius limit →
      other ∈ headlineGrantChosenRoots ring C radius limit →
      root ≠ other →
      ∀ e : Fin n,
        ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
           Counter.Support (ceilLogTwo n) ring other e) := by
  intro root other hr ho hne e hp
  unfold headlineGrantChosenRoots at hr ho
  obtain ⟨i, hi, hir⟩ := List.mem_map.mp hr
  obtain ⟨j, hj, hjr⟩ := List.mem_map.mp ho
  have hij : i ≠ j := by
    intro heq
    rw [heq] at hir
    exact hne (hir.symm.trans hjr)
  have hsi := headlineGrantChosenBinSpec
    ring C radius limit i hfit hi
  have hsj := headlineGrantChosenBinSpec
    ring C radius limit j hfit hj
  have hipos : 0 < (headlineGrantPickRoot ring C radius i).val := by
    omega
  have hjpos : 0 < (headlineGrantPickRoot ring C radius j).val := by
    omega
  have hifit := headlineGrantBinFits radius limit i hfit
    (headlineGrantCleanBinMem ring C radius limit i hi).1
  have hjfit := headlineGrantBinFits radius limit j hfit
    (headlineGrantCleanBinMem ring C radius limit j hj).1
  rw [Nat.mul_add, Nat.mul_one] at hifit hjfit
  have hitop :
      (headlineGrantPickRoot ring C radius i).val +
        (compileAdvice (ceilLogTwo n)).b < n := by
    unfold headlineGrantBinWidth at hsi hifit
    omega
  have hjtop :
      (headlineGrantPickRoot ring C radius j).val +
        (compileAdvice (ceilLogTwo n)).b < n := by
    unfold headlineGrantBinWidth at hsj hjfit
    omega
  have hsep := headlineGrantChosenBinSeparation
    ring C radius limit i j hfit hi hj hij
  have hpick :
      Counter.Support (ceilLogTwo n) ring
        (headlineGrantPickRoot ring C radius i) e ∧
      Counter.Support (ceilLogTwo n) ring
        (headlineGrantPickRoot ring C radius j) e := by
    rw [hir, hjr]
    exact hp
  rcases hsep with hf | hr
  · exact headlineGrantStraightSupportsDisjoint
      (q := ceilLogTwo n) ring
      (headlineGrantPickRoot ring C radius i)
      (headlineGrantPickRoot ring C radius j)
      hipos hjpos hitop hjtop hf e hpick
  · exact headlineGrantStraightSupportsDisjoint
      (q := ceilLogTwo n) ring
      (headlineGrantPickRoot ring C radius j)
      (headlineGrantPickRoot ring C radius i)
      hjpos hipos hjtop hitop hr e ⟨hpick.2, hpick.1⟩

/-- The selected family simultaneously has the three structural
requirements and the precise complement-cardinality bound. -/
theorem headlineGrantFixedBlockFamily {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (radius limit : Nat)
    (hfit : 2 * radius + 1 +
      2 * (headlineGrantBinWidth n) * limit ≤ n) :
    ∃ roots : List (Fin n),
      roots.Nodup ∧
      (∀ root : Fin n, root ∈ roots →
        HeadlineGrantBufferedCounter ring C radius root) ∧
      (∀ root other : Fin n,
        root ∈ roots → other ∈ roots → root ≠ other →
        ∀ e : Fin n,
          ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
             Counter.Support (ceilLogTwo n) ring other e)) ∧
      limit ≤ roots.length +
        defects ring C *
          (radius / headlineGrantBinWidth n + 3) := by
  refine ⟨headlineGrantChosenRoots ring C radius limit,
    headlineGrantChosenRootsNodup ring C radius limit hfit,
    headlineGrantChosenRootsBuffered ring C radius limit hfit,
    headlineGrantChosenRootsDisjoint ring C radius limit hfit,
    ?_⟩
  have hmass := headlineGrantUnblockedBinsMass
    ring C radius limit
  change limit ≤
    (List.range limit).countP
      (fun k => !(headlineGrantBinBad ring C radius k)) +
    defects ring C *
      (radius / headlineGrantBinWidth n + 3) at hmass
  rw [← headlineGrantChosenRootsLength ring C radius limit] at hmass
  exact hmass

/-! ## Uniform arithmetic without sqrt, Finset or nonlinear tactics -/

/-- Squared order is faithful for nonnegative natural numbers. -/
theorem headlineGrantSquareOrder (a b : Nat)
    (h : a * a ≤ b * b) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have hba : b < a := by omega
    have hstrict := Nat.mul_self_lt_mul_self hba
    omega

/-- The lower population cutoff and upper radius rounding together
give radius >= 16w. The square bound then excludes a large radius
that would cover the entire finite ring. -/
theorem headlineGrantRadiusBudget
    (n w radius : Nat) (hw : 0 < w)
    (hsize : (4096 * w) ^ 2 ≤ n)
    (hlower : (256 * radius) ^ 2 ≤ n)
    (hupper : n < (256 * (radius + 1)) ^ 2) :
    16 * w ≤ radius ∧ 2 * radius + 1 ≤ n := by
  have hwide : 4096 * w < 256 * (radius + 1) := by
    by_cases ht : 4096 * w < 256 * (radius + 1)
    · exact ht
    · have hrev : 256 * (radius + 1) ≤ 4096 * w := by
        omega
      have hsq := Nat.mul_self_le_mul_self hrev
      have hsq' :
          (256 * (radius + 1)) ^ 2 ≤
            (4096 * w) ^ 2 := by
        simpa only [Nat.pow_two] using hsq
      omega
  have hrad : 16 * w ≤ radius := by omega
  have hpos : 1 ≤ radius := by omega
  have hsquare : (256 * radius) * (256 * radius) ≤ n := by
    simpa only [Nat.pow_two] using hlower
  have hmul := Nat.mul_le_mul_left (256 * radius)
    (by omega : 1 ≤ 256 * radius)
  have hfit : 2 * radius + 1 ≤ n := by
    have hbelow :
        2 * radius + 1 ≤
          (256 * radius) * (256 * radius) := by
      calc
        2 * radius + 1 ≤ (256 * radius) * 1 := by omega
        _ ≤ (256 * radius) * (256 * radius) := hmul
    omega
  exact ⟨hrad, hfit⟩

/-- Cauchy-type square product bound specialized to the two exact
scales needed by C.10. All inequalities remain over Nat. -/
theorem headlineGrantDefectRadiusProduct
    (n radius defects : Nat)
    (hd : defects * defects ≤ 4 * n)
    (hr : (256 * radius) ^ 2 ≤ n) :
    128 * (defects * radius) ≤ n := by
  have hrl : (256 * radius) * (256 * radius) ≤ n := by
    simpa only [Nat.pow_two] using hr
  have hp := Nat.mul_le_mul hd hrl
  have hsquare :
      (256 * (defects * radius)) *
          (256 * (defects * radius)) ≤
        (2 * n) * (2 * n) := by
    calc
      (256 * (defects * radius)) *
          (256 * (defects * radius)) =
        (defects * defects) *
          ((256 * radius) * (256 * radius)) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (4 * n) * n := hp
      _ = (2 * n) * (2 * n) := by
          simp only [Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm, Nat.reduceMul]
  have hcomp := headlineGrantSquareOrder
    (256 * (defects * radius)) (2 * n) hsquare
  have hdouble : 2 * (128 * (defects * radius)) ≤ 2 * n := by
    calc
      2 * (128 * (defects * radius)) =
          256 * (defects * radius) := by omega
      _ ≤ 2 * n := hcomp
  omega

theorem headlineGrantDefectWidthProduct
    (n w defects : Nat)
    (hd : defects * defects ≤ 4 * n)
    (hw : (4096 * w) ^ 2 ≤ n) :
    2048 * (defects * w) ≤ n := by
  have hwl : (4096 * w) * (4096 * w) ≤ n := by
    simpa only [Nat.pow_two] using hw
  have hp := Nat.mul_le_mul hd hwl
  have hsquare :
      (4096 * (defects * w)) *
          (4096 * (defects * w)) ≤
        (2 * n) * (2 * n) := by
    calc
      (4096 * (defects * w)) * (4096 * (defects * w)) =
        (defects * defects) * ((4096 * w) * (4096 * w)) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (4 * n) * n := hp
      _ = (2 * n) * (2 * n) := by
          simp only [Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm, Nat.reduceMul]
  have hcomp := headlineGrantSquareOrder
    (4096 * (defects * w)) (2 * n) hsquare
  have hdouble : 2 * (2048 * (defects * w)) ≤ 2 * n := by
    calc
      2 * (2048 * (defects * w)) =
          4096 * (defects * w) := by omega
      _ ≤ 2 * n := hcomp
  omega

/-- The radius and width origin loss is at most half a population
unit. This is deliberately weaker than the true small loss. -/
theorem headlineGrantOriginBudget
    (n w radius : Nat)
    (hr : 16 * w ≤ radius)
    (hw : (256 * radius) ^ 2 ≤ n) :
    2 * (1000 * (radius + w)) ≤ n := by
  by_cases hz : radius = 0
  · have hwzero : w = 0 := by omega
    subst radius
    subst w
    simp
  have hpos : 16 ≤ 256 * radius := by omega
  have hmul := Nat.mul_le_mul_left (256 * radius) hpos
  have hsq : (256 * radius) * (256 * radius) ≤ n := by
    simpa only [Nat.pow_two] using hw
  calc
    2 * (1000 * (radius + w)) ≤
        (256 * radius) * 16 := by omega
    _ ≤ (256 * radius) * (256 * radius) := hmul
    _ ≤ n := hsq

/-- Scaled floor bound. It is intentionally independent of any
root-list choice or physical role computation. -/
theorem headlineGrantBinCountFits
    (n w radius : Nat) (hw : 0 < w)
    (hstart : 2 * radius + 1 ≤ n) :
    2 * radius + 1 +
      (2 * w) * ((n - (2 * radius + 1)) / (2 * w)) ≤ n := by
  have hm := Nat.div_mul_le_self (n - (2 * radius + 1)) (2 * w)
  have hbound :
      (2 * w) * ((n - (2 * radius + 1)) / (2 * w)) ≤
        n - (2 * radius + 1) := by
    simpa only [Nat.mul_comm] using hm
  omega

/-- The universal 489/1000 certificate: with n,w,R,D symbolic,
there is no need for an integer square-root library or a
case split over advice bands. -/
theorem headlineGrantUniformArithmetic
    (n w radius defects selected : Nat)
    (hw : 0 < w)
    (hsize : (4096 * w) ^ 2 ≤ n)
    (hrlower : (256 * radius) ^ 2 ≤ n)
    (hrupper : n < (256 * (radius + 1)) ^ 2)
    (hdensity : defects * defects ≤ 4 * n)
    (hcount :
      (n - (2 * radius + 1)) / (2 * w) ≤
        selected + defects * (radius / w + 3)) :
    489 * n < 1000 * selected * w := by
  obtain ⟨hrad, hstart⟩ :=
    headlineGrantRadiusBudget n w radius hw
      hsize hrlower hrupper
  have hDR :=
    headlineGrantDefectRadiusProduct n radius defects
      hdensity hrlower
  have hDW :=
    headlineGrantDefectWidthProduct n w defects
      hdensity hsize
  have hOrig :=
    headlineGrantOriginBudget n w radius hrad hrlower
  have hX : 1000 * (defects * radius) ≤ 8 * n := by
    have hm := Nat.mul_le_mul_left 8 hDR
    omega
  have hY : 3000 * (defects * w) ≤ 2 * n := by
    have hm := Nat.mul_le_mul_left 2 hDW
    omega
  have hnpos : 0 < n := by omega
  have hBudget :
      1000 * (defects * radius) +
        3000 * (defects * w) +
          1000 * (radius + w) < 11 * n := by
    omega
  have hdiv : (radius / w) * w ≤ radius :=
    Nat.div_mul_le_self radius w
  have hlost :
      w * (defects * (radius / w + 3)) ≤
        defects * radius + 3 * (defects * w) := by
    have hm := Nat.mul_le_mul_left defects hdiv
    calc
      w * (defects * (radius / w + 3)) =
        defects * ((radius / w) * w) +
          3 * (defects * w) := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm, Nat.reduceMul]
      _ ≤ defects * radius + 3 * (defects * w) := by
          omega
  have hscaledCap :
      (2 * w) * (defects * (radius / w + 3)) ≤
        2 * (defects * radius + 3 * (defects * w)) := by
    have hm := Nat.mul_le_mul_left 2 hlost
    simpa only [Nat.mul_assoc] using hm
  have hscaledCount :
      (2 * w) * ((n - (2 * radius + 1)) / (2 * w)) ≤
        (2 * w) * selected +
          2 * (defects * radius + 3 * (defects * w)) := by
    have hm := Nat.mul_le_mul_left (2 * w) hcount
    rw [Nat.mul_add] at hm
    omega
  have hrem := Nat.mod_lt (n - (2 * radius + 1))
    (by omega : 0 < 2 * w)
  have hdecomp := Nat.mod_add_div
    (n - (2 * radius + 1)) (2 * w)
  have hquot :
      n - (2 * radius + 1) <
        (2 * w) *
          (((n - (2 * radius + 1)) / (2 * w)) + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hceil :
      n ≤ 2 * radius +
        (2 * w) *
          (((n - (2 * radius + 1)) / (2 * w)) + 1) := by
    omega
  rw [Nat.mul_add, Nat.mul_one] at hceil
  have hineq :
      n ≤ 2 * radius + (2 * w) * selected +
        2 * (defects * radius + 3 * (defects * w)) +
          2 * w := by
    omega
  have hscaled := Nat.mul_le_mul_left 500 hineq
  have hfactor :
      2 * w * selected = 2 * (selected * w) := by
    ac_rfl
  rw [hfactor] at hscaled
  have hfinal :
      500 * n ≤
        1000 * radius + 1000 * selected * w +
          1000 * (defects * radius) +
            3000 * (defects * w) + 1000 * w := by
    have hselected :
        1000 * selected * w = 1000 * (selected * w) := by
      ac_rfl
    rw [hselected]
    omega
  omega

/-! ## Complete deterministic spatial bridge -/

/-- The spatial-selection bridge from the literal density-bound
physical cut. No independent ghosts or auxiliary scheduler:
the only list members are physical Fin n roots from actual PACK.
The strict constant is supplied by the universal integer
inequality above. -/
theorem headlineGrantSpatialSupportBridgeProved {n : Nat}
    (ring : DirectedRing n) :
    StageGrantSpatialSupportBridge ring := by
  intro C radius hsize hrlower hrupper hdensity
  have hw : 0 < headlineGrantBinWidth n := by
    unfold headlineGrantBinWidth
    omega
  obtain ⟨hrad, hstart⟩ :=
    headlineGrantRadiusBudget n (headlineGrantBinWidth n)
      radius hw hsize hrlower hrupper
  have hlast :
      2 * radius + 1 +
        2 * (headlineGrantBinWidth n) *
          ((n - (2 * radius + 1)) /
            (2 * headlineGrantBinWidth n)) ≤ n := by
    exact headlineGrantBinCountFits n
      (headlineGrantBinWidth n) radius hw hstart
  obtain ⟨roots, hnodup, hbuffered, hdisjoint, hmass⟩ :=
    headlineGrantFixedBlockFamily ring C radius
      ((n - (2 * radius + 1)) /
        (2 * headlineGrantBinWidth n)) hlast
  refine ⟨roots, hnodup, hbuffered, hdisjoint, ?_⟩
  exact headlineGrantUniformArithmetic n
    (headlineGrantBinWidth n) radius
    (defects ring C) roots.length
    hw hsize hrlower hrupper hdensity hmass

end L3



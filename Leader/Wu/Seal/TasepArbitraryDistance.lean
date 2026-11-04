import Leader.Wu.Seal.TasepDistanceTwoComparison

/-!
# Arbitrary-distance moving-particle comparison on a fixed TASEP slice

This file closes the finite combinatorial comparison left open by
`PPartialSealSweepTasepMovingParticleComparisonSol`.  A transposition between
`x` and `cwPos ring x d` is implemented by the adjacent-swap word

`[x, ..., x+d-1] ++ reverse [x, ..., x+d-2]`.

Every intermediate configuration remains in the same exact front-mass slice.
The proof uses the current symmetric-swap mass theorem and therefore threads
the necessary hypothesis `1 < n` through every slice-preservation and slice-
reindexing statement.  Summing the path inequality over the slice and then
over all ordered pairs gives a conservative `4 * n^3` comparison with cyclic
adjacent energy.  The imported denominator-cleared adjacent comparison first
lands in the weighted common-successor energy; the separate conservative row
inclusion into the full common-successor energy costs one further factor `n`,
which is retained in the final theorem.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepTasepArbitraryDistanceSol

open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepFiniteTimeSol
open PPartialSealSweepTasepMovingParticleComparisonSol

set_option autoImplicit false

/-! ## Elementary finite-list sums -/

private theorem arbitrary_sum_map_congr
    {alpha : Type} (xs : List alpha) (f g : alpha -> Nat)
    (h : forall x, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, h x, ih]

private theorem arbitrary_sum_map_add
    {alpha : Type} (xs : List alpha) (f g : alpha -> Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem arbitrary_sum_map_mul_left
    {alpha : Type} (xs : List alpha) (f : alpha -> Nat) (c : Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

private theorem arbitrary_sum_map_mul_right
    {alpha : Type} (xs : List alpha) (f : alpha -> Nat) (c : Nat) :
    (xs.map (fun x => f x * c)).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

private theorem arbitrary_sum_map_const
    {alpha : Type} (xs : List alpha) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih,
        Nat.succ_eq_add_one, Nat.add_mul]
      omega

private theorem arbitrary_sum_map_mono
    {alpha : Type} (xs : List alpha) (f g : alpha -> Nat)
    (h : forall x, x ∈ xs -> f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · exact h x (by simp)
      · apply ih
        intro y hy
        exact h y (by simp [hy])

private theorem arbitrary_sum_map_le_const
    {alpha : Type} (xs : List alpha) (f : alpha -> Nat) (bound : Nat)
    (h : forall x, x ∈ xs -> f x <= bound) :
    (xs.map f).sum <= xs.length * bound := by
  calc
    (xs.map f).sum <= (xs.map (fun _ => bound)).sum :=
      arbitrary_sum_map_mono xs f (fun _ => bound) h
    _ = xs.length * bound := arbitrary_sum_map_const xs bound

private theorem arbitrary_nodup_map_of_injective
    {alpha beta : Type} {xs : List alpha} (hxs : xs.Nodup)
    (f : alpha -> beta) (hf : Function.Injective f) :
    (xs.map f).Nodup := by
  exact List.Pairwise.map f (fun _ _ hne => hf.ne hne) hxs

private theorem arbitrary_nodup_ofFn_of_injective
    {m : Nat} {alpha : Type} (f : Fin m -> alpha)
    (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
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

private theorem arbitrary_sum_map_le_of_nodup_subset
    {alpha : Type} (xs ys : List alpha) (weight : alpha -> Nat)
    (hxs : xs.Nodup) (hsub : xs ⊆ ys) :
    (xs.map weight).sum <= (ys.map weight).sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hxs
      have ha : a ∈ ys := hsub (by simp)
      rw [List.mem_iff_append] at ha
      obtain ⟨before, after, rfl⟩ := ha
      have htailSub : xs ⊆ before ++ after := by
        intro x hx
        have hxfull := hsub (List.mem_cons_of_mem a hx)
        rw [List.mem_append] at hxfull ⊢
        rcases hxfull with hbefore | hrest
        · exact Or.inl hbefore
        · simp only [List.mem_cons] at hrest
          rcases hrest with hxa | hafter
          · subst x
            exact (hxs.1 hx).elim
          · exact Or.inr hafter
      have htail := ih (before ++ after) hxs.2 htailSub
      calc
        ((a :: xs).map weight).sum =
            weight a + (xs.map weight).sum := by rfl
        _ <= weight a + ((before ++ after).map weight).sum :=
          Nat.add_le_add_left htail _
        _ = ((before ++ a :: after).map weight).sum := by
          simp only [List.map_append, List.sum_append, List.map_cons,
            List.sum_cons]
          omega

/-! ## A duplicate-free list of all ring coordinates -/

/-- The canonical list of all coordinates of `Fin n`. -/
def tasepFinIndexList (n : Nat) : List (Fin n) :=
  List.ofFn (fun i : Fin n => i)

@[simp] theorem tasepFinIndexList_length (n : Nat) :
    (tasepFinIndexList n).length = n := by
  simp [tasepFinIndexList]

@[simp] theorem mem_tasepFinIndexList {n : Nat} (i : Fin n) :
    i ∈ tasepFinIndexList n := by
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem tasepFinIndexList_nodup (n : Nat) :
    (tasepFinIndexList n).Nodup := by
  exact arbitrary_nodup_ofFn_of_injective
    (fun i : Fin n => i) (fun _ _ h => h)

/-! ## Bounded clockwise geometry and endpoint permutations -/

private theorem cwPos_injective_of_lt
    {n : Nat} (ring : DirectedRing n) (x : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n)
    (h : cwPos ring x a = cwPos ring x b) : a = b := by
  have ha' := cwPos_bounded_unique ring x (cwPos ring x b) a ha h
  have hb' := cwPos_bounded_unique ring x (cwPos ring x b) b hb rfl
  exact ha'.trans hb'.symm

private theorem cwPos_ne_of_ne
    {n : Nat} (ring : DirectedRing n) (x : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cwPos ring x a ≠ cwPos ring x b := by
  intro h
  exact hab (cwPos_injective_of_lt ring x ha hb h)

/-- For fixed `x`, the bounded clockwise positions are a permutation of all
ring coordinates.  This is the exact reindexing used below for the destination
coordinate in the ordered-pair energy. -/
theorem tasepFinIndexList_map_cwPos_perm
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    ((tasepFinIndexList n).map
      (fun d : Fin n => cwPos ring x d.val)).Perm
      (tasepFinIndexList n) := by
  have hinj : Function.Injective
      (fun d : Fin n => cwPos ring x d.val) := by
    intro a b hab
    apply Fin.ext
    exact cwPos_injective_of_lt ring x a.isLt b.isLt hab
  have hleftNodup :
      ((tasepFinIndexList n).map
        (fun d : Fin n => cwPos ring x d.val)).Nodup :=
    arbitrary_nodup_map_of_injective
      (tasepFinIndexList_nodup n) _ hinj
  apply (List.perm_ext_iff_of_nodup hleftNodup
    (tasepFinIndexList_nodup n)).2
  intro z
  constructor
  · intro hz
    exact mem_tasepFinIndexList z
  · intro hz
    rw [List.mem_map]
    let d : Fin n := ⟨cwDist ring x z, cwDist_lt ring x z⟩
    refine ⟨d, mem_tasepFinIndexList d, ?_⟩
    simpa [d] using cwPos_cwDist ring x z

/-! ## Coordinate-transposition algebra -/

private theorem swapFrontConfigAt_eq_transpose
    {n : Nat} (ring : DirectedRing n)
    (F : Fin n -> Bool) (edge : Fin n) :
    swapFrontConfigAt ring F edge =
      transposeFrontConfig F edge (ring.rightNeighbor edge) := by
  funext i
  simp [swapFrontConfigAt, transposeFrontConfig]

private theorem transposeFrontConfig_braid
    {n : Nat} (F : Fin n -> Bool) {x y z : Fin n}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    transposeFrontConfig
        (transposeFrontConfig
          (transposeFrontConfig F x y) y z) x y =
      transposeFrontConfig F x z := by
  funext i
  by_cases hix : i = x
  · subst i
    simp [transposeFrontConfig, hxy, hxy.symm,
      hyz, hyz.symm, hxz, hxz.symm]
  · by_cases hiy : i = y
    · subst i
      simp [transposeFrontConfig, hxy, hxy.symm,
        hyz, hyz.symm, hxz, hxz.symm]
    · by_cases hiz : i = z
      · subst i
        simp [transposeFrontConfig, hxy, hxy.symm,
          hyz, hyz.symm, hxz, hxz.symm]
      · simp [transposeFrontConfig, hix, hiy, hiz,
          hxy, hxy.symm, hyz, hyz.symm, hxz, hxz.symm]

/-! ## The forward/backward adjacent-swap word -/

/-- Edge labels at clockwise offsets `0, ..., d-1` from `x`. -/
def clockwiseForwardSwapWord {n : Nat}
    (ring : DirectedRing n) (x : Fin n) : Nat -> List (Fin n)
  | 0 => []
  | d + 1 => x :: clockwiseForwardSwapWord ring (ring.rightNeighbor x) d

@[simp] theorem clockwiseForwardSwapWord_length
    {n : Nat} (ring : DirectedRing n) (x : Fin n) (d : Nat) :
    (clockwiseForwardSwapWord ring x d).length = d := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp [clockwiseForwardSwapWord, ih]

theorem mem_clockwiseForwardSwapWord_iff
    {n : Nat} (ring : DirectedRing n) (x edge : Fin n) (d : Nat) :
    edge ∈ clockwiseForwardSwapWord ring x d ↔
      ∃ j : Nat, j < d ∧ edge = cwPos ring x j := by
  induction d generalizing x with
  | zero => simp [clockwiseForwardSwapWord]
  | succ d ih =>
      simp only [clockwiseForwardSwapWord, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | h
        · exact ⟨0, by omega, by simp⟩
        · rw [ih] at h
          rcases h with ⟨j, hj, rfl⟩
          exact ⟨j + 1, by omega, cwPos_rightNeighbor ring x j⟩
      · rintro ⟨j, hj, rfl⟩
        cases j with
        | zero => exact Or.inl (by simp)
        | succ j =>
            apply Or.inr
            rw [ih]
            exact ⟨j, by omega, (cwPos_rightNeighbor ring x j).symm⟩

theorem clockwiseForwardSwapWord_nodup
    {n : Nat} (ring : DirectedRing n) (x : Fin n) (d : Nat)
    (hd : d <= n) :
    (clockwiseForwardSwapWord ring x d).Nodup := by
  induction d generalizing x with
  | zero => simp [clockwiseForwardSwapWord]
  | succ d ih =>
      rw [clockwiseForwardSwapWord, List.nodup_cons]
      constructor
      · intro hx
        rw [mem_clockwiseForwardSwapWord_iff] at hx
        rcases hx with ⟨j, hj, hx⟩
        have heq : cwPos ring x 0 = cwPos ring x (j + 1) := by
          calc
            cwPos ring x 0 = x := by simp
            _ = cwPos ring (ring.rightNeighbor x) j := hx
            _ = cwPos ring x (j + 1) := cwPos_rightNeighbor ring x j
        have hoff := cwPos_injective_of_lt ring x ring.hn (by omega) heq
        omega
      · exact ih (ring.rightNeighbor x) (by omega)

/-- Move the bit at `x` forward to distance `d`, then restore all interior
coordinates by traversing the first `d-1` edges backwards. -/
def arbitraryDistanceSwapWord {n : Nat}
    (ring : DirectedRing n) (x : Fin n) (d : Nat) : List (Fin n) :=
  clockwiseForwardSwapWord ring x d ++
    (clockwiseForwardSwapWord ring x (d - 1)).reverse

@[simp] theorem arbitraryDistanceSwapWord_zero
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    arbitraryDistanceSwapWord ring x 0 = [] := by
  simp [arbitraryDistanceSwapWord, clockwiseForwardSwapWord]

@[simp] theorem arbitraryDistanceSwapWord_one
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    arbitraryDistanceSwapWord ring x 1 = [x] := by
  simp [arbitraryDistanceSwapWord, clockwiseForwardSwapWord]

@[simp] theorem arbitraryDistanceSwapWord_two
    {n : Nat} (ring : DirectedRing n) (x : Fin n) :
    arbitraryDistanceSwapWord ring x 2 =
      [x, ring.rightNeighbor x, x] := by
  simp [arbitraryDistanceSwapWord, clockwiseForwardSwapWord]

@[simp] theorem arbitraryDistanceSwapWord_length
    {n : Nat} (ring : DirectedRing n) (x : Fin n) (d : Nat) :
    (arbitraryDistanceSwapWord ring x d).length = d + (d - 1) := by
  simp [arbitraryDistanceSwapWord]

private theorem arbitraryDistanceSwapWord_length_le
    {n : Nat} (ring : DirectedRing n) (x : Fin n)
    {d : Nat} (hd : d < n) :
    (arbitraryDistanceSwapWord ring x d).length <= 2 * n := by
  rw [arbitraryDistanceSwapWord_length]
  omega

private theorem arbitraryDistanceSwapWord_succ_succ
    {n : Nat} (ring : DirectedRing n) (x : Fin n) (d : Nat) :
    arbitraryDistanceSwapWord ring x (d + 2) =
      x :: (arbitraryDistanceSwapWord
        ring (ring.rightNeighbor x) (d + 1) ++ [x]) := by
  simp [arbitraryDistanceSwapWord, clockwiseForwardSwapWord,
    List.reverse_cons, List.append_assoc]

/-! ## Executing the word and preserving the fixed slice -/

/-- Execute symmetric adjacent swaps from left to right. -/
def runFrontSwapWord {n : Nat} (ring : DirectedRing n) :
    (Fin n -> Bool) -> List (Fin n) -> Fin n -> Bool
  | F, [] => F
  | F, edge :: rest =>
      runFrontSwapWord ring (swapFrontConfigAt ring F edge) rest

@[simp] theorem runFrontSwapWord_nil
    {n : Nat} (ring : DirectedRing n) (F : Fin n -> Bool) :
    runFrontSwapWord ring F [] = F := rfl

@[simp] theorem runFrontSwapWord_singleton
    {n : Nat} (ring : DirectedRing n)
    (F : Fin n -> Bool) (edge : Fin n) :
    runFrontSwapWord ring F [edge] = swapFrontConfigAt ring F edge := rfl

theorem runFrontSwapWord_append
    {n : Nat} (ring : DirectedRing n) (F : Fin n -> Bool)
    (u v : List (Fin n)) :
    runFrontSwapWord ring F (u ++ v) =
      runFrontSwapWord ring (runFrontSwapWord ring F u) v := by
  induction u generalizing F with
  | nil => rfl
  | cons edge u ih =>
      simpa [runFrontSwapWord] using ih (swapFrontConfigAt ring F edge)

/-- Reversing an adjacent-swap word reverses its action. -/
theorem runFrontSwapWord_then_reverse
    {n : Nat} (ring : DirectedRing n) (F : Fin n -> Bool)
    (w : List (Fin n)) :
    runFrontSwapWord ring (runFrontSwapWord ring F w) w.reverse = F := by
  induction w generalizing F with
  | nil => rfl
  | cons edge w ih =>
      rw [List.reverse_cons, runFrontSwapWord_append]
      change runFrontSwapWord ring
        (runFrontSwapWord ring
          (runFrontSwapWord ring (swapFrontConfigAt ring F edge) w)
          w.reverse) [edge] = F
      rw [ih]
      simpa only [runFrontSwapWord_singleton] using
        swapFrontConfigAt_involutive ring edge F

private theorem runFrontSwapWord_reverse_then
    {n : Nat} (ring : DirectedRing n) (F : Fin n -> Bool)
    (w : List (Fin n)) :
    runFrontSwapWord ring (runFrontSwapWord ring F w.reverse) w = F := by
  simpa using runFrontSwapWord_then_reverse ring F w.reverse

theorem runFrontSwapWord_injective
    {n : Nat} (ring : DirectedRing n) (w : List (Fin n)) :
    Function.Injective
      (fun F : Fin n -> Bool => runFrontSwapWord ring F w) := by
  intro F G hFG
  calc
    F = runFrontSwapWord ring (runFrontSwapWord ring F w) w.reverse :=
      (runFrontSwapWord_then_reverse ring F w).symm
    _ = runFrontSwapWord ring (runFrontSwapWord ring G w) w.reverse :=
      congrArg (fun H => runFrontSwapWord ring H w.reverse) hFG
    _ = G := runFrontSwapWord_then_reverse ring G w

/-- One symmetric adjacent swap remains in the same concrete fixed-mass
slice.  The proof deliberately goes through the current mass-preservation
theorem; no simplification of the slice predicate is used as a substitute. -/
theorem swapFrontConfigAt_mem_tasepFrontConfigSlice
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    {F : Fin n -> Bool} (edge : Fin n)
    (hF : F ∈ tasepFrontConfigSlice n k) :
    swapFrontConfigAt ring F edge ∈ tasepFrontConfigSlice n k := by
  apply (mem_tasepFrontConfigSlice_iff _).mpr
  rw [frontConfigMass_swapFrontConfigAt ring hn]
  exact (mem_tasepFrontConfigSlice_iff F).mp hF

/-- Every finite adjacent-swap word preserves exact fixed-slice membership. -/
theorem runFrontSwapWord_mem_tasepFrontConfigSlice
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n) :
    forall (F : Fin n -> Bool) (w : List (Fin n)),
      F ∈ tasepFrontConfigSlice n k ->
      runFrontSwapWord ring F w ∈ tasepFrontConfigSlice n k := by
  intro F w hF
  induction w generalizing F with
  | nil => simpa using hF
  | cons edge w ih =>
      apply ih
      exact swapFrontConfigAt_mem_tasepFrontConfigSlice ring hn edge hF

/-- Every prefix of the arbitrary-distance word, including a `take` longer
than the word, remains in the original fixed-mass slice. -/
theorem arbitraryDistanceSwapWord_prefix_mem_slice
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (hF : F ∈ tasepFrontConfigSlice n k)
    (x : Fin n) (d t : Nat) :
    runFrontSwapWord ring F
        ((arbitraryDistanceSwapWord ring x d).take t) ∈
      tasepFrontConfigSlice n k :=
  runFrontSwapWord_mem_tasepFrontConfigSlice ring hn F _ hF

/-- Applying a word to every member of a fixed slice produces a duplicate-
free list.  This uses the exact current `tasepFrontConfigSlice_nodup` theorem. -/
theorem tasepFrontConfigSlice_map_runFrontSwapWord_nodup
    {n k : Nat} (ring : DirectedRing n) (w : List (Fin n)) :
    ((tasepFrontConfigSlice n k).map
      (fun F => runFrontSwapWord ring F w)).Nodup := by
  exact arbitrary_nodup_map_of_injective
    (tasepFrontConfigSlice_nodup n k) _
    (runFrontSwapWord_injective ring w)

/-- A word of adjacent swaps permutes every exact fixed-mass slice.  Forward
membership uses mass preservation; reverse membership uses the reversed word. -/
theorem tasepFrontConfigSlice_map_runFrontSwapWord_perm
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (w : List (Fin n)) :
    ((tasepFrontConfigSlice n k).map
      (fun F => runFrontSwapWord ring F w)).Perm
      (tasepFrontConfigSlice n k) := by
  classical
  apply (List.perm_ext_iff_of_nodup
    (tasepFrontConfigSlice_map_runFrontSwapWord_nodup ring w)
    (tasepFrontConfigSlice_nodup n k)).2
  intro G
  rw [List.mem_map]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact runFrontSwapWord_mem_tasepFrontConfigSlice ring hn F w hF
  · intro hG
    refine ⟨runFrontSwapWord ring G w.reverse, ?_, ?_⟩
    · exact runFrontSwapWord_mem_tasepFrontConfigSlice
        ring hn G w.reverse hG
    · exact runFrontSwapWord_reverse_then ring G w

/-! ## Endpoint action of the canonical word -/

theorem run_arbitraryDistanceSwapWord
    {n : Nat} (ring : DirectedRing n) (F : Fin n -> Bool)
    (x : Fin n) (d : Nat) (hd : d < n) :
    runFrontSwapWord ring F (arbitraryDistanceSwapWord ring x d) =
      transposeFrontConfig F x (cwPos ring x d) := by
  induction d generalizing x F with
  | zero =>
      simp only [arbitraryDistanceSwapWord_zero,
        runFrontSwapWord_nil, cwPos_zero]
      funext i
      by_cases hix : i = x
      · subst i
        simp [transposeFrontConfig]
      · simp [transposeFrontConfig, hix]
  | succ d ih =>
      cases d with
      | zero =>
          simp [arbitraryDistanceSwapWord, clockwiseForwardSwapWord,
            runFrontSwapWord, swapFrontConfigAt_eq_transpose]
      | succ d =>
          have hinner : d + 1 < n := by omega
          have hfar :
              cwPos ring (ring.rightNeighbor x) (d + 1) =
                cwPos ring x (d + 2) := by
            simpa [Nat.add_assoc] using
              cwPos_rightNeighbor ring x (d + 1)
          have hxy : x ≠ ring.rightNeighbor x := by
            have h := cwPos_ne_of_ne ring x ring.hn
              (by omega : 1 < n) (by omega : 0 ≠ 1)
            simpa using h
          have hyz :
              ring.rightNeighbor x ≠ cwPos ring x (d + 2) := by
            have h := cwPos_ne_of_ne ring x
              (by omega : 1 < n) hd (by omega : 1 ≠ d + 2)
            simpa using h
          have hxz : x ≠ cwPos ring x (d + 2) := by
            have h := cwPos_ne_of_ne ring x ring.hn hd
              (by omega : 0 ≠ d + 2)
            simpa using h
          rw [arbitraryDistanceSwapWord_succ_succ]
          change runFrontSwapWord ring (swapFrontConfigAt ring F x)
              (arbitraryDistanceSwapWord
                ring (ring.rightNeighbor x) (d + 1) ++ [x]) =
            transposeFrontConfig F x (cwPos ring x (d + 2))
          rw [runFrontSwapWord_append]
          rw [ih (x := ring.rightNeighbor x)
            (F := swapFrontConfigAt ring F x) hinner]
          rw [hfar]
          simp only [runFrontSwapWord_singleton]
          rw [swapFrontConfigAt_eq_transpose]
          rw [swapFrontConfigAt_eq_transpose]
          exact transposeFrontConfig_braid F hxy hyz hxz

theorem run_arbitraryDistanceSwapWord_zero
    {n : Nat} (ring : DirectedRing n)
    (F : Fin n -> Bool) (x : Fin n) :
    runFrontSwapWord ring F (arbitraryDistanceSwapWord ring x 0) = F := by
  simp

theorem run_arbitraryDistanceSwapWord_one
    {n : Nat} (ring : DirectedRing n)
    (F : Fin n -> Bool) (x : Fin n) (hn : 1 < n) :
    runFrontSwapWord ring F (arbitraryDistanceSwapWord ring x 1) =
      transposeFrontConfig F x (cwPos ring x 1) :=
  run_arbitraryDistanceSwapWord ring F x 1 hn

theorem run_arbitraryDistanceSwapWord_two
    {n : Nat} (ring : DirectedRing n)
    (F : Fin n -> Bool) (x : Fin n) (hn : 2 < n) :
    runFrontSwapWord ring F [x, ring.rightNeighbor x, x] =
      transposeFrontConfig F x (cwPos ring x 2) := by
  rw [← arbitraryDistanceSwapWord_two ring x]
  exact run_arbitraryDistanceSwapWord ring F x 2 hn

/-! ## A denominator-free path-square estimate -/

private def arbitraryNatSumSquares (xs : List Nat) : Nat :=
  (xs.map (fun x => x * x)).sum

private def arbitraryNatPairSum
    (xs : List Nat) (f : Nat -> Nat -> Nat) : Nat :=
  (xs.map (fun a => (xs.map (fun b => f a b)).sum)).sum

private theorem two_mul_product_le_squares (a b : Nat) :
    2 * (a * b) <= a * a + b * b := by
  rcases Nat.le_total a b with hab | hba
  · obtain ⟨c, rfl⟩ : ∃ c, b = a + c :=
      ⟨b - a, by omega⟩
    simp only [Nat.mul_add, Nat.add_mul, Nat.two_mul]
    rw [Nat.mul_comm c a]
    omega
  · obtain ⟨c, rfl⟩ : ∃ c, a = b + c :=
      ⟨a - b, by omega⟩
    simp only [Nat.mul_add, Nat.add_mul, Nat.two_mul]
    rw [Nat.mul_comm c b]
    omega

private theorem arbitraryNatPairSum_mul (xs : List Nat) :
    arbitraryNatPairSum xs (fun a b => a * b) = xs.sum * xs.sum := by
  unfold arbitraryNatPairSum
  calc
    (xs.map (fun a => (xs.map (fun b => a * b)).sum)).sum =
        (xs.map (fun a => a * xs.sum)).sum := by
      apply arbitrary_sum_map_congr
      intro a
      simpa using arbitrary_sum_map_mul_left xs (fun b => b) a
    _ = xs.sum * xs.sum := by
      simpa using arbitrary_sum_map_mul_right xs (fun a => a) xs.sum

private theorem arbitraryNatPairSum_scale
    (xs : List Nat) (c : Nat) (f : Nat -> Nat -> Nat) :
    arbitraryNatPairSum xs (fun a b => c * f a b) =
      c * arbitraryNatPairSum xs f := by
  unfold arbitraryNatPairSum
  calc
    (xs.map (fun a =>
        (xs.map (fun b => c * f a b)).sum)).sum =
        (xs.map (fun a =>
          c * (xs.map (fun b => f a b)).sum)).sum := by
      apply arbitrary_sum_map_congr
      intro a
      exact arbitrary_sum_map_mul_left xs (fun b => f a b) c
    _ = c *
        (xs.map (fun a => (xs.map (fun b => f a b)).sum)).sum :=
      arbitrary_sum_map_mul_left _ _ c

private theorem arbitraryNatPairSum_add
    (xs : List Nat) (f g : Nat -> Nat -> Nat) :
    arbitraryNatPairSum xs (fun a b => f a b + g a b) =
      arbitraryNatPairSum xs f + arbitraryNatPairSum xs g := by
  unfold arbitraryNatPairSum
  calc
    (xs.map (fun a =>
        (xs.map (fun b => f a b + g a b)).sum)).sum =
        (xs.map (fun a =>
          (xs.map (fun b => f a b)).sum +
            (xs.map (fun b => g a b)).sum)).sum := by
      apply arbitrary_sum_map_congr
      intro a
      exact arbitrary_sum_map_add xs (fun b => f a b) (fun b => g a b)
    _ =
        (xs.map (fun a => (xs.map (fun b => f a b)).sum)).sum +
          (xs.map (fun a => (xs.map (fun b => g a b)).sum)).sum :=
      arbitrary_sum_map_add xs _ _

private theorem arbitraryNatPairSum_left_square (xs : List Nat) :
    arbitraryNatPairSum xs (fun a _ => a * a) =
      xs.length * arbitraryNatSumSquares xs := by
  unfold arbitraryNatPairSum arbitraryNatSumSquares
  calc
    (xs.map (fun a => (xs.map (fun _ => a * a)).sum)).sum =
        (xs.map (fun a => xs.length * (a * a))).sum := by
      apply arbitrary_sum_map_congr
      intro a
      exact arbitrary_sum_map_const xs (a * a)
    _ = xs.length * (xs.map (fun a => a * a)).sum :=
      arbitrary_sum_map_mul_left _ _ _

private theorem arbitraryNatPairSum_right_square (xs : List Nat) :
    arbitraryNatPairSum xs (fun _ b => b * b) =
      xs.length * arbitraryNatSumSquares xs := by
  unfold arbitraryNatPairSum arbitraryNatSumSquares
  exact arbitrary_sum_map_const xs ((xs.map (fun b => b * b)).sum)

private theorem arbitraryNatPairSum_square_add (xs : List Nat) :
    arbitraryNatPairSum xs (fun a b => a * a + b * b) =
      2 * (xs.length * arbitraryNatSumSquares xs) := by
  rw [arbitraryNatPairSum_add,
    arbitraryNatPairSum_left_square,
    arbitraryNatPairSum_right_square]
  omega

private theorem arbitraryNatPairSum_mono
    (xs : List Nat) (f g : Nat -> Nat -> Nat)
    (h : forall a b, f a b <= g a b) :
    arbitraryNatPairSum xs f <= arbitraryNatPairSum xs g := by
  unfold arbitraryNatPairSum
  apply arbitrary_sum_map_mono
  intro a ha
  apply arbitrary_sum_map_mono
  intro b hb
  exact h a b

/-- Finite Cauchy--Schwarz for a list of natural numbers, proved entirely in
`Nat`; no scalar cast or division is introduced. -/
private theorem nat_sum_sq_le_length_mul_sum_squares (xs : List Nat) :
    xs.sum * xs.sum <= xs.length * arbitraryNatSumSquares xs := by
  have hpair :
      arbitraryNatPairSum xs (fun a b => 2 * (a * b)) <=
        arbitraryNatPairSum xs (fun a b => a * a + b * b) := by
    apply arbitraryNatPairSum_mono
    intro a b
    exact two_mul_product_le_squares a b
  rw [arbitraryNatPairSum_scale, arbitraryNatPairSum_mul,
    arbitraryNatPairSum_square_add] at hpair
  exact Nat.le_of_mul_le_mul_left hpair (by omega)

private theorem frontSquaredGap_eq_mul_natAbs
    {n : Nat} (phi : (Fin n -> Bool) -> Int)
    (F G : Fin n -> Bool) :
    frontSquaredGap phi F G =
      Int.natAbs (phi F - phi G) * Int.natAbs (phi F - phi G) := by
  simp [frontSquaredGap, Nat.pow_succ]

/-- Absolute observable increments along a concrete adjacent-swap word. -/
def frontSwapWordGaps {n : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int) :
    (Fin n -> Bool) -> List (Fin n) -> List Nat
  | F, [] => []
  | F, edge :: rest =>
      Int.natAbs (phi F - phi (swapFrontConfigAt ring F edge)) ::
        frontSwapWordGaps ring phi
          (swapFrontConfigAt ring F edge) rest

@[simp] theorem frontSwapWordGaps_length
    {n : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int)
    (F : Fin n -> Bool) (w : List (Fin n)) :
    (frontSwapWordGaps ring phi F w).length = w.length := by
  induction w generalizing F with
  | nil => rfl
  | cons edge w ih => simp [frontSwapWordGaps, ih]

/-- Sum of the current Nat-valued squared observable gaps along a word. -/
def frontSwapWordSquaredEnergy {n : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int) :
    (Fin n -> Bool) -> List (Fin n) -> Nat
  | F, [] => 0
  | F, edge :: rest =>
      frontSquaredGap phi F (swapFrontConfigAt ring F edge) +
        frontSwapWordSquaredEnergy ring phi
          (swapFrontConfigAt ring F edge) rest

private theorem frontSwapWordGaps_sum_squares
    {n : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int)
    (F : Fin n -> Bool) (w : List (Fin n)) :
    arbitraryNatSumSquares (frontSwapWordGaps ring phi F w) =
      frontSwapWordSquaredEnergy ring phi F w := by
  induction w generalizing F with
  | nil => rfl
  | cons edge w ih =>
      change
        Int.natAbs (phi F - phi (swapFrontConfigAt ring F edge)) *
            Int.natAbs (phi F - phi (swapFrontConfigAt ring F edge)) +
          arbitraryNatSumSquares
            (frontSwapWordGaps ring phi
              (swapFrontConfigAt ring F edge) w) =
        frontSquaredGap phi F (swapFrontConfigAt ring F edge) +
          frontSwapWordSquaredEnergy ring phi
            (swapFrontConfigAt ring F edge) w
      rw [ih (swapFrontConfigAt ring F edge)]
      rw [frontSquaredGap_eq_mul_natAbs]

private theorem endpoint_natAbs_le_frontSwapWordGaps_sum
    {n : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int) :
    forall (F : Fin n -> Bool) (w : List (Fin n)),
      Int.natAbs (phi F - phi (runFrontSwapWord ring F w)) <=
        (frontSwapWordGaps ring phi F w).sum := by
  intro F w
  induction w generalizing F with
  | nil => simp [runFrontSwapWord, frontSwapWordGaps]
  | cons edge w ih =>
      let G := swapFrontConfigAt ring F edge
      change Int.natAbs (phi F - phi (runFrontSwapWord ring G w)) <=
        Int.natAbs (phi F - phi G) +
          (frontSwapWordGaps ring phi G w).sum
      have htel :
          phi F - phi (runFrontSwapWord ring G w) =
            (phi F - phi G) +
              (phi G - phi (runFrontSwapWord ring G w)) := by
        omega
      calc
        Int.natAbs (phi F - phi (runFrontSwapWord ring G w)) =
            Int.natAbs ((phi F - phi G) +
              (phi G - phi (runFrontSwapWord ring G w))) :=
          congrArg Int.natAbs htel
        _ <= Int.natAbs (phi F - phi G) +
            Int.natAbs (phi G - phi (runFrontSwapWord ring G w)) :=
          Int.natAbs_add_le _ _
        _ <= Int.natAbs (phi F - phi G) +
            (frontSwapWordGaps ring phi G w).sum :=
          Nat.add_le_add_left (ih G) _

/-- The squared endpoint gap is at most path length times the sum of squared
leg gaps.  All arithmetic after the unavoidable observable differences is in
`Nat`. -/
theorem frontSquaredGap_runFrontSwapWord_le
    {n : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int)
    (F : Fin n -> Bool) (w : List (Fin n)) :
    frontSquaredGap phi F (runFrontSwapWord ring F w) <=
      w.length * frontSwapWordSquaredEnergy ring phi F w := by
  have hgap := endpoint_natAbs_le_frontSwapWordGaps_sum ring phi F w
  have hsq := Nat.mul_le_mul hgap hgap
  have hcauchy := nat_sum_sq_le_length_mul_sum_squares
    (frontSwapWordGaps ring phi F w)
  calc
    frontSquaredGap phi F (runFrontSwapWord ring F w) =
        Int.natAbs (phi F - phi (runFrontSwapWord ring F w)) *
          Int.natAbs (phi F - phi (runFrontSwapWord ring F w)) :=
      frontSquaredGap_eq_mul_natAbs phi F _
    _ <= (frontSwapWordGaps ring phi F w).sum *
        (frontSwapWordGaps ring phi F w).sum := hsq
    _ <= (frontSwapWordGaps ring phi F w).length *
        arbitraryNatSumSquares (frontSwapWordGaps ring phi F w) :=
      hcauchy
    _ = w.length * frontSwapWordSquaredEnergy ring phi F w := by
      rw [frontSwapWordGaps_length, frontSwapWordGaps_sum_squares]

/-- Endpoint specialization for the explicit arbitrary-distance word. -/
theorem frontSquaredGap_transpose_le_arbitraryDistancePath
    {n : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int)
    (F : Fin n -> Bool) (x : Fin n)
    (d : Nat) (hd : d < n) :
    frontSquaredGap phi F
        (transposeFrontConfig F x (cwPos ring x d)) <=
      (arbitraryDistanceSwapWord ring x d).length *
        frontSwapWordSquaredEnergy ring phi F
          (arbitraryDistanceSwapWord ring x d) := by
  rw [← run_arbitraryDistanceSwapWord ring F x d hd]
  exact frontSquaredGap_runFrontSwapWord_le
    ring phi F (arbitraryDistanceSwapWord ring x d)

/-! ## Exact fixed-slice reindexing of path legs -/

/-- Sum a Nat-valued observable over the concrete fixed-mass slice. -/
def arbitrarySliceSum {n : Nat} (k : Nat)
    (f : (Fin n -> Bool) -> Nat) : Nat :=
  ((tasepFrontConfigSlice n k).map f).sum

private theorem arbitrarySliceSum_add
    {n k : Nat} (f g : (Fin n -> Bool) -> Nat) :
    arbitrarySliceSum k (fun F => f F + g F) =
      arbitrarySliceSum k f + arbitrarySliceSum k g := by
  exact arbitrary_sum_map_add (tasepFrontConfigSlice n k) f g

private theorem arbitrarySliceSum_mul_left
    {n k : Nat} (c : Nat) (f : (Fin n -> Bool) -> Nat) :
    arbitrarySliceSum k (fun F => c * f F) =
      c * arbitrarySliceSum k f := by
  exact arbitrary_sum_map_mul_left (tasepFrontConfigSlice n k) f c

private theorem arbitrarySliceSum_mono
    {n k : Nat} {f g : (Fin n -> Bool) -> Nat}
    (h : forall F, f F <= g F) :
    arbitrarySliceSum k f <= arbitrarySliceSum k g := by
  unfold arbitrarySliceSum
  apply arbitrary_sum_map_mono
  intro F hF
  exact h F

private theorem arbitrarySliceSum_comp_run
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (w : List (Fin n)) (f : (Fin n -> Bool) -> Nat) :
    arbitrarySliceSum k
        (fun F => f (runFrontSwapWord ring F w)) =
      arbitrarySliceSum k f := by
  have hp :=
    (tasepFrontConfigSlice_map_runFrontSwapWord_perm
      (k := k) ring hn w).map f
  have hs := List.Perm.sum_nat hp
  simpa [arbitrarySliceSum, List.map_map, Function.comp_def] using hs

private theorem arbitrarySliceSum_comp_swap
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (edge : Fin n) (f : (Fin n -> Bool) -> Nat) :
    arbitrarySliceSum k
        (fun F => f (swapFrontConfigAt ring F edge)) =
      arbitrarySliceSum k f := by
  simpa [runFrontSwapWord] using
    arbitrarySliceSum_comp_run (k := k) ring hn [edge] f

/-- Sum over the slice of the adjacent-gap summands indexed by an arbitrary
edge word. -/
def swapWordSquaredEnergy
    {n : Nat} (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) (w : List (Fin n)) : Nat :=
  arbitrarySliceSum k (fun F =>
    (w.map (fun edge =>
      frontSquaredGap phi F (swapFrontConfigAt ring F edge))).sum)

private theorem swapWordSquaredEnergy_nil
    {n : Nat} (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    swapWordSquaredEnergy ring k phi [] = 0 := by
  unfold swapWordSquaredEnergy arbitrarySliceSum
  change ((tasepFrontConfigSlice n k).map (fun _ => 0)).sum = 0
  calc
    ((tasepFrontConfigSlice n k).map (fun _ => 0)).sum =
        (tasepFrontConfigSlice n k).length * 0 :=
      arbitrary_sum_map_const (tasepFrontConfigSlice n k) 0
    _ = 0 := Nat.mul_zero _

private theorem swapWordSquaredEnergy_cons
    {n : Nat} (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int)
    (edge : Fin n) (w : List (Fin n)) :
    swapWordSquaredEnergy ring k phi (edge :: w) =
      arbitrarySliceSum k
          (fun F => frontSquaredGap phi F
            (swapFrontConfigAt ring F edge)) +
        swapWordSquaredEnergy ring k phi w := by
  unfold swapWordSquaredEnergy
  simp only [List.map_cons, List.sum_cons]
  exact arbitrarySliceSum_add _ _

private theorem swapWordSquaredEnergy_append
    {n : Nat} (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) (u v : List (Fin n)) :
    swapWordSquaredEnergy ring k phi (u ++ v) =
      swapWordSquaredEnergy ring k phi u +
        swapWordSquaredEnergy ring k phi v := by
  unfold swapWordSquaredEnergy
  have h := arbitrary_sum_map_add
    (tasepFrontConfigSlice n k)
    (fun F => (u.map (fun edge =>
      frontSquaredGap phi F (swapFrontConfigAt ring F edge))).sum)
    (fun F => (v.map (fun edge =>
      frontSquaredGap phi F (swapFrontConfigAt ring F edge))).sum)
  simpa [arbitrarySliceSum, List.map_append, List.sum_append] using h

private theorem swapWordSquaredEnergy_reverse
    {n : Nat} (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) (w : List (Fin n)) :
    swapWordSquaredEnergy ring k phi w.reverse =
      swapWordSquaredEnergy ring k phi w := by
  unfold swapWordSquaredEnergy arbitrarySliceSum
  apply arbitrary_sum_map_congr
  intro F
  have hp := (List.reverse_perm w).map
    (fun edge => frontSquaredGap phi F
      (swapFrontConfigAt ring F edge))
  exact hp.sum_nat

private theorem swapWordSquaredEnergy_all_edges
    {n : Nat} (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    swapWordSquaredEnergy ring k phi (tasepFinIndexList n) =
      adjacentCyclicSquaredEnergy ring k phi := by
  simp [swapWordSquaredEnergy, arbitrarySliceSum,
    tasepFinIndexList, adjacentCyclicSquaredEnergy,
    List.map_ofFn, Function.comp_def]

theorem slice_frontSwapWordSquaredEnergy_eq_swapWordSquaredEnergy
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (phi : (Fin n -> Bool) -> Int) (w : List (Fin n)) :
    arbitrarySliceSum k
        (fun F => frontSwapWordSquaredEnergy ring phi F w) =
      swapWordSquaredEnergy ring k phi w := by
  induction w with
  | nil =>
      rw [swapWordSquaredEnergy_nil]
      unfold arbitrarySliceSum
      change ((tasepFrontConfigSlice n k).map (fun _ => 0)).sum = 0
      calc
        ((tasepFrontConfigSlice n k).map (fun _ => 0)).sum =
            (tasepFrontConfigSlice n k).length * 0 :=
          arbitrary_sum_map_const (tasepFrontConfigSlice n k) 0
        _ = 0 := Nat.mul_zero _
  | cons edge w ih =>
      calc
        arbitrarySliceSum k
            (fun F => frontSwapWordSquaredEnergy ring phi F (edge :: w)) =
          arbitrarySliceSum k
            (fun F =>
              frontSquaredGap phi F (swapFrontConfigAt ring F edge) +
                frontSwapWordSquaredEnergy ring phi
                  (swapFrontConfigAt ring F edge) w) := rfl
        _ = arbitrarySliceSum k
              (fun F => frontSquaredGap phi F
                (swapFrontConfigAt ring F edge)) +
            arbitrarySliceSum k
              (fun F => frontSwapWordSquaredEnergy ring phi
                (swapFrontConfigAt ring F edge) w) :=
          arbitrarySliceSum_add _ _
        _ = arbitrarySliceSum k
              (fun F => frontSquaredGap phi F
                (swapFrontConfigAt ring F edge)) +
            arbitrarySliceSum k
              (fun F => frontSwapWordSquaredEnergy ring phi F w) := by
          rw [arbitrarySliceSum_comp_swap
            (k := k) ring hn edge
            (fun G => frontSwapWordSquaredEnergy ring phi G w)]
        _ = arbitrarySliceSum k
              (fun F => frontSquaredGap phi F
                (swapFrontConfigAt ring F edge)) +
            swapWordSquaredEnergy ring k phi w := by
          rw [ih]
        _ = swapWordSquaredEnergy ring k phi (edge :: w) :=
          (swapWordSquaredEnergy_cons ring k phi edge w).symm

private theorem clockwiseForwardSwapWord_subset_finIndexList
    {n : Nat} (ring : DirectedRing n) (x : Fin n) (d : Nat) :
    clockwiseForwardSwapWord ring x d ⊆ tasepFinIndexList n := by
  intro edge hedge
  exact mem_tasepFinIndexList edge

private theorem forwardWordSquaredEnergy_le_adjacent
    {n k : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int)
    (x : Fin n) (d : Nat) (hd : d <= n) :
    swapWordSquaredEnergy ring k phi
        (clockwiseForwardSwapWord ring x d) <=
      adjacentCyclicSquaredEnergy ring k phi := by
  calc
    swapWordSquaredEnergy ring k phi
        (clockwiseForwardSwapWord ring x d) <=
      swapWordSquaredEnergy ring k phi (tasepFinIndexList n) := by
        unfold swapWordSquaredEnergy arbitrarySliceSum
        apply arbitrary_sum_map_mono
        intro F hF
        exact arbitrary_sum_map_le_of_nodup_subset
          (clockwiseForwardSwapWord ring x d)
          (tasepFinIndexList n)
          (fun edge => frontSquaredGap phi F
            (swapFrontConfigAt ring F edge))
          (clockwiseForwardSwapWord_nodup ring x d hd)
          (clockwiseForwardSwapWord_subset_finIndexList ring x d)
    _ = adjacentCyclicSquaredEnergy ring k phi :=
      swapWordSquaredEnergy_all_edges ring k phi

private theorem arbitraryDistanceWordSquaredEnergy_le_two_adjacent
    {n k : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int)
    (x : Fin n) (d : Nat) (hd : d < n) :
    swapWordSquaredEnergy ring k phi
        (arbitraryDistanceSwapWord ring x d) <=
      2 * adjacentCyclicSquaredEnergy ring k phi := by
  have hf := forwardWordSquaredEnergy_le_adjacent
    (k := k) ring phi x d (Nat.le_of_lt hd)
  have hb := forwardWordSquaredEnergy_le_adjacent
    (k := k) ring phi x (d - 1) (by omega)
  rw [arbitraryDistanceSwapWord, swapWordSquaredEnergy_append,
    swapWordSquaredEnergy_reverse]
  omega

/-! ## One route, all ordered pairs, and cyclic congestion -/

/-- Fixed-slice energy for one source coordinate and one bounded clockwise
distance. -/
def clockwiseDistanceTranspositionEnergy
    {n : Nat} (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int)
    (x : Fin n) (d : Nat) : Nat :=
  arbitrarySliceSum k (fun F =>
    frontSquaredGap phi F
      (transposeFrontConfig F x (cwPos ring x d)))

theorem clockwiseDistanceTranspositionEnergy_le_four_mul_n_adjacent
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (phi : (Fin n -> Bool) -> Int)
    (x : Fin n) (d : Nat) (hd : d < n) :
    clockwiseDistanceTranspositionEnergy ring k phi x d <=
      4 * n * adjacentCyclicSquaredEnergy ring k phi := by
  let w := arbitraryDistanceSwapWord ring x d
  have hpoint : forall F : Fin n -> Bool,
      frontSquaredGap phi F
          (transposeFrontConfig F x (cwPos ring x d)) <=
        w.length * frontSwapWordSquaredEnergy ring phi F w := by
    intro F
    dsimp [w]
    exact frontSquaredGap_transpose_le_arbitraryDistancePath
      ring phi F x d hd
  have hsum :
      clockwiseDistanceTranspositionEnergy ring k phi x d <=
        w.length * swapWordSquaredEnergy ring k phi w := by
    unfold clockwiseDistanceTranspositionEnergy
    calc
      arbitrarySliceSum k
          (fun F => frontSquaredGap phi F
            (transposeFrontConfig F x (cwPos ring x d))) <=
        arbitrarySliceSum k
          (fun F => w.length *
            frontSwapWordSquaredEnergy ring phi F w) :=
        arbitrarySliceSum_mono hpoint
      _ = w.length * arbitrarySliceSum k
          (fun F => frontSwapWordSquaredEnergy ring phi F w) :=
        arbitrarySliceSum_mul_left w.length _
      _ = w.length * swapWordSquaredEnergy ring k phi w := by
        rw [slice_frontSwapWordSquaredEnergy_eq_swapWordSquaredEnergy
          ring hn]
  have hlen : w.length <= 2 * n := by
    dsimp [w]
    exact arbitraryDistanceSwapWord_length_le ring x hd
  have hword :
      swapWordSquaredEnergy ring k phi w <=
        2 * adjacentCyclicSquaredEnergy ring k phi := by
    dsimp [w]
    exact arbitraryDistanceWordSquaredEnergy_le_two_adjacent
      ring phi x d hd
  calc
    clockwiseDistanceTranspositionEnergy ring k phi x d <=
        w.length * swapWordSquaredEnergy ring k phi w := hsum
    _ <= (2 * n) *
        (2 * adjacentCyclicSquaredEnergy ring k phi) :=
      Nat.mul_le_mul hlen hword
    _ = 4 * n * adjacentCyclicSquaredEnergy ring k phi := by
      have hfour : (4 : Nat) = 2 * 2 := by decide
      rw [hfour]
      ac_rfl

/-- Direct fixed-slice energy summed over all ordered coordinate pairs
`(x,z)`.  Diagonal pairs are retained and contribute zero. -/
def arbitraryTranspositionEnergy
    {n : Nat} (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFinIndexList n).map (fun x =>
    ((tasepFinIndexList n).map (fun z =>
      arbitrarySliceSum k (fun F =>
        frontSquaredGap phi F
          (transposeFrontConfig F x z)))).sum)).sum

/-- The same ordered-pair energy indexed by a source and a bounded clockwise
distance. -/
def arbitraryDistanceTranspositionEnergy
    {n : Nat} (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFinIndexList n).map (fun x =>
    ((tasepFinIndexList n).map (fun d =>
      clockwiseDistanceTranspositionEnergy
        ring k phi x d.val)).sum)).sum

/-- For one fixed source, the `cwPos` permutation reindexes the destination
sum by bounded clockwise distance. -/
theorem destination_sum_eq_clockwiseDistance_sum
    {n k : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int) (x : Fin n) :
    ((tasepFinIndexList n).map (fun z =>
      arbitrarySliceSum k (fun F =>
        frontSquaredGap phi F
          (transposeFrontConfig F x z)))).sum =
      ((tasepFinIndexList n).map (fun d =>
        clockwiseDistanceTranspositionEnergy
          ring k phi x d.val)).sum := by
  let cost : Fin n -> Nat := fun z =>
    arbitrarySliceSum k (fun F =>
      frontSquaredGap phi F (transposeFrontConfig F x z))
  have hp := (tasepFinIndexList_map_cwPos_perm ring x).map cost
  have hs := hp.sum_nat
  simpa [cost, clockwiseDistanceTranspositionEnergy,
    List.map_map, Function.comp_def] using hs.symm

/-- Reindex both coordinates of the ordered-pair sum as source and bounded
clockwise distance. -/
theorem arbitraryTranspositionEnergy_eq_distanceEnergy
    {n k : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int) :
    arbitraryTranspositionEnergy ring k phi =
      arbitraryDistanceTranspositionEnergy ring k phi := by
  unfold arbitraryTranspositionEnergy arbitraryDistanceTranspositionEnergy
  apply arbitrary_sum_map_congr
  intro x
  exact destination_sum_eq_clockwiseDistance_sum ring phi x

private theorem arbitraryDistanceTranspositionEnergy_le
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (phi : (Fin n -> Bool) -> Int) :
    arbitraryDistanceTranspositionEnergy ring k phi <=
      n * (n *
        (4 * n * adjacentCyclicSquaredEnergy ring k phi)) := by
  let bound := 4 * n * adjacentCyclicSquaredEnergy ring k phi
  have hinner : forall x : Fin n,
      ((tasepFinIndexList n).map (fun d =>
        clockwiseDistanceTranspositionEnergy
          ring k phi x d.val)).sum <= n * bound := by
    intro x
    have h := arbitrary_sum_map_le_const
      (tasepFinIndexList n)
      (fun d => clockwiseDistanceTranspositionEnergy
        ring k phi x d.val) bound
      (fun d hd =>
        clockwiseDistanceTranspositionEnergy_le_four_mul_n_adjacent
          ring hn phi x d.val d.isLt)
    simpa using h
  unfold arbitraryDistanceTranspositionEnergy
  have h := arbitrary_sum_map_le_const
    (tasepFinIndexList n)
    (fun x =>
      ((tasepFinIndexList n).map (fun d =>
        clockwiseDistanceTranspositionEnergy
          ring k phi x d.val)).sum)
    (n * bound)
    (fun x hx => hinner x)
  simpa [bound] using h

/-- Conservative arbitrary-transposition moving-particle comparison.  The
factor `n^3` consists of `n^2` ordered source/distance pairs and the `4*n`
cost of each canonical route. -/
theorem arbitraryTranspositionEnergy_le_four_mul_cube_adjacent
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (phi : (Fin n -> Bool) -> Int) :
    arbitraryTranspositionEnergy ring k phi <=
      4 * n ^ 3 * adjacentCyclicSquaredEnergy ring k phi := by
  rw [arbitraryTranspositionEnergy_eq_distanceEnergy]
  calc
    arbitraryDistanceTranspositionEnergy ring k phi <=
        n * (n *
          (4 * n * adjacentCyclicSquaredEnergy ring k phi)) :=
      arbitraryDistanceTranspositionEnergy_le ring hn phi
    _ = 4 * n ^ 3 * adjacentCyclicSquaredEnergy ring k phi := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
      ac_rfl

/-! ## Splice to the exact common-successor kernel -/

theorem n_mul_arbitraryTranspositionEnergy_le_eight_mul_cube_weighted
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (phi : (Fin n -> Bool) -> Int) :
    n * arbitraryTranspositionEnergy ring k phi <=
      8 * n ^ 3 *
        commonSuccessorWeightedAdjacentSquaredEnergy ring k phi := by
  have hroute :=
    arbitraryTranspositionEnergy_le_four_mul_cube_adjacent
      (k := k) ring hn phi
  have hrouteScaled := Nat.mul_le_mul_left n hroute
  have hadj :=
    n_mul_adjacentEnergy_le_two_mul_commonSuccessorEnergy
      ring hn k phi
  calc
    n * arbitraryTranspositionEnergy ring k phi <=
        n * (4 * n ^ 3 *
          adjacentCyclicSquaredEnergy ring k phi) := hrouteScaled
    _ = 4 * n ^ 3 *
        (n * adjacentCyclicSquaredEnergy ring k phi) := by ac_rfl
    _ <= 4 * n ^ 3 *
        (2 * commonSuccessorWeightedAdjacentSquaredEnergy ring k phi) :=
      Nat.mul_le_mul_left (4 * n ^ 3) hadj
    _ = 8 * n ^ 3 *
        commonSuccessorWeightedAdjacentSquaredEnergy ring k phi := by
      rw [show (8 : Nat) = 4 * 2 from rfl]; ac_rfl

theorem arbitraryTranspositionEnergy_le_eight_mul_cube_fullCommonSuccessor
    {n k : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (phi : (Fin n -> Bool) -> Int) :
    arbitraryTranspositionEnergy ring k phi <=
      8 * n ^ 3 * fullCommonSuccessorSquaredEnergy ring k phi := by
  have hweighted :=
    n_mul_arbitraryTranspositionEnergy_le_eight_mul_cube_weighted
      (k := k) ring hn phi
  have hfull :=
    commonSuccessorWeightedAdjacentSquaredEnergy_le_n_mul_full
      ring hn k phi
  have hscaled :
      n * arbitraryTranspositionEnergy ring k phi <=
        n * (8 * n ^ 3 *
          fullCommonSuccessorSquaredEnergy ring k phi) := by
    calc
      n * arbitraryTranspositionEnergy ring k phi <=
          8 * n ^ 3 *
            commonSuccessorWeightedAdjacentSquaredEnergy ring k phi :=
        hweighted
      _ <= 8 * n ^ 3 *
          (n * fullCommonSuccessorSquaredEnergy ring k phi) :=
        Nat.mul_le_mul_left (8 * n ^ 3) hfull
      _ = n * (8 * n ^ 3 *
          fullCommonSuccessorSquaredEnergy ring k phi) := by
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled ring.hn

end PPartialSealSweepTasepArbitraryDistanceSol
end PPLLCompleteMultiLeaderCleanup

import Leader.L4.Height.Core

namespace L4.Height.Depth

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Encode -1, 0, +1 by 0, 1, 2. -/
def move {m : Nat} (hm : 0 < m) (i : Fin m) (d : Fin 3) : Fin m :=
  if d.val = 0 then left hm i
  else if d.val = 1 then i
  else right hm i

/-- Sites visited backwards, including the endpoint. -/
def pathSites {m : Nat} (hm : 0 < m) (i : Fin m) :
    List (Fin 3) → List (Fin m)
  | [] => [i]
  | d :: ds => i :: pathSites hm (move hm i d) ds

theorem pathSites_length {m : Nat} (hm : 0 < m)
    (i : Fin m) (ds : List (Fin 3)) :
    (pathSites hm i ds).length = ds.length + 1 := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih =>
      simp only [pathSites, List.length_cons, ih]

/-- The site at level zero at the end of the backward path. -/
def pathStart {m : Nat} (hm : 0 < m) (i : Fin m) :
    List (Fin 3) → Fin m
  | [] => i
  | d :: ds => pathStart hm (move hm i d) ds

/-- The first step is charged at level h-1, the next at h-2, etc. -/
def pathWait {m : Nat} (hm : 0 < m)
    (w : Fin m → Nat → Nat) : Nat → Fin m → List (Fin 3) → Nat
  | _, _, [] => 0
  | 0, _, _ :: _ => 0
  | h + 1, i, d :: ds =>
      w i h + pathWait hm w h (move hm i d) ds

def pathScore {m : Nat} (hm : 0 < m)
    (T w : Fin m → Nat → Nat) (h : Nat)
    (i : Fin m) (ds : List (Fin 3)) : Nat :=
  T (pathStart hm i ds) 0 + pathWait hm w h i ds

theorem pathScore_cons {m : Nat} (hm : 0 < m)
    (T w : Fin m → Nat → Nat) (h : Nat)
    (i : Fin m) (d : Fin 3) (ds : List (Fin 3)) :
    pathScore hm T w (h + 1) i (d :: ds) =
      w i h + pathScore hm T w h (move hm i d) ds := by
  simp only [pathScore, pathStart, pathWait]
  omega

/-- Exactly all the words over the three-element step alphabet. -/
def allSteps : Nat → List (List (Fin 3))
  | 0 => [[]]
  | h + 1 =>
      (allSteps h).map (fun ds => (0 : Fin 3) :: ds) ++
      ((allSteps h).map (fun ds => (1 : Fin 3) :: ds) ++
       (allSteps h).map (fun ds => (2 : Fin 3) :: ds))

theorem allSteps_length (h : Nat) :
    (allSteps h).length = 3 ^ h := by
  induction h with
  | zero => rfl
  | succ h ih =>
      simp only [allSteps, List.length_append, List.length_map, ih]
      rw [Nat.pow_succ]
      omega

theorem allSteps_nonempty (h : Nat) : allSteps h ≠ [] := by
  intro he
  have hl : 3 ^ h = 0 := by
    have hlen := congrArg List.length he
    simpa only [List.length_nil, allSteps_length] using hlen
  have hp : 0 < 3 ^ h := Nat.pow_pos (by decide)
  exact (Nat.ne_of_gt hp) hl

private theorem prefix_left (h : Nat) (ds : List (Fin 3))
    (hs : ds ∈ allSteps h) :
    ((0 : Fin 3) :: ds) ∈ allSteps (h + 1) := by
  simp only [allSteps, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨ds, hs, rfl⟩)

private theorem prefix_mid (h : Nat) (ds : List (Fin 3))
    (hs : ds ∈ allSteps h) :
    ((1 : Fin 3) :: ds) ∈ allSteps (h + 1) := by
  simp only [allSteps, List.mem_append]
  exact Or.inr (Or.inl (List.mem_map.mpr ⟨ds, hs, rfl⟩))

private theorem prefix_right (h : Nat) (ds : List (Fin 3))
    (hs : ds ∈ allSteps h) :
    ((2 : Fin 3) :: ds) ∈ allSteps (h + 1) := by
  simp only [allSteps, List.mem_append]
  exact Or.inr (Or.inr (List.mem_map.mpr ⟨ds, hs, rfl⟩))

/-- Maximum of a finite list, with zero as the empty maximum. -/
def foldMax (xs : List Nat) : Nat := xs.foldr max 0

private theorem le_foldMax_of_mem (xs : List Nat)
    (a : Nat) (ha : a ∈ xs) : a ≤ foldMax xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha
      simp only [foldMax, List.foldr_cons]
      rcases ha with rfl | ht
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

private theorem foldMax_le_of_all (xs : List Nat) (B : Nat)
    (hb : ∀ x, x ∈ xs → x ≤ B) : foldMax xs ≤ B := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
      have hx : x ≤ B := hb x (by simp)
      have ht : foldMax xs ≤ B := ih (by
        intro y hy
        exact hb y (by simp [hy]))
      simp only [foldMax, List.foldr_cons]
      exact (Nat.max_le).mpr ⟨hx, ht⟩

/-- A positive list has a maximum stable under a common additive bound. -/
private theorem add_foldMax_le (xs : List Nat) (c B : Nat)
    (hne : xs ≠ [])
    (hb : ∀ x, x ∈ xs → c + x ≤ B) :
    c + foldMax xs ≤ B := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
      have hx : c + x ≤ B := hb x (by simp)
      by_cases he : xs = []
      · subst xs
        simp only [foldMax, List.foldr_cons, List.foldr_nil,
          Nat.max_zero]
        exact hx
      · have ht : c + foldMax xs ≤ B := ih he (by
          intro y hy
          exact hb y (by simp [hy]))
        unfold foldMax at ht ⊢
        rw [List.foldr_cons]
        by_cases hxm : x ≤ List.foldr max 0 xs
        · rw [Nat.max_eq_right hxm]
          exact ht
        · have hmx : List.foldr max 0 xs ≤ x := Nat.le_of_not_ge hxm
          rw [Nat.max_eq_left hmx]
          exact hx

/-- Explicit fold over all 3^h paths ending at i. -/
def pathMaximum {m : Nat} (hm : 0 < m)
    (T w : Fin m → Nat → Nat) (h : Nat) (i : Fin m) : Nat :=
  foldMax ((allSteps h).map (pathScore hm T w h i))

private theorem score_le_maximum {m : Nat} (hm : 0 < m)
    (T w : Fin m → Nat → Nat) (h : Nat)
    (i : Fin m) (ds : List (Fin 3)) (hs : ds ∈ allSteps h) :
    pathScore hm T w h i ds ≤ pathMaximum hm T w h i := by
  unfold pathMaximum
  apply le_foldMax_of_mem
  exact List.mem_map.mpr ⟨ds, hs, rfl⟩

private theorem branch_le {m : Nat} (hm : 0 < m)
    (T w : Fin m → Nat → Nat) (h : Nat)
    (i j : Fin m) (d : Fin 3)
    (hj : move hm i d = j)
    (hp : ∀ ds, ds ∈ allSteps h →
       (d :: ds) ∈ allSteps (h + 1)) :
    w i h + pathMaximum hm T w h j ≤
      pathMaximum hm T w (h + 1) i := by
  unfold pathMaximum
  apply add_foldMax_le
  · intro he
    have hl : 3 ^ h = 0 := by
      have hlen := congrArg List.length he
      simpa only [List.length_map, List.length_nil,
        allSteps_length] using hlen
    have hp' : 0 < 3 ^ h := Nat.pow_pos (by decide)
    exact (Nat.ne_of_gt hp') hl
  · intro x hx
    obtain ⟨ds, hs, rfl⟩ := List.mem_map.mp hx
    have hbound := score_le_maximum hm T w (h + 1) i
      (d :: ds) (hp ds hs)
    rw [pathScore_cons, hj] at hbound
    exact hbound

/-- The max-plus recursion unrolled as a maximum over exactly 3^h paths. -/
theorem depth_bound {m : Nat} (hm : 0 < m)
    (T w : Fin m → Nat → Nat)
    (hrec : ∀ i ℓ,
      T i (ℓ + 1) ≤
        max (max (T (left hm i) ℓ) (T i ℓ))
          (T (right hm i) ℓ) + w i ℓ) :
    ∀ h i, T i h ≤ pathMaximum hm T w h i := by
  intro h
  induction h with
  | zero =>
      intro i
      unfold pathMaximum foldMax
      simp only [allSteps, List.map_cons, List.map_nil,
        List.foldr_cons, List.foldr_nil, pathScore,
        pathStart, pathWait, Nat.add_zero, Nat.max_zero]
      exact Nat.le_refl _
  | succ h ih =>
      intro i
      have hleft : move hm i (0 : Fin 3) = left hm i := by
        simp [move]
      have hmid : move hm i (1 : Fin 3) = i := by
        simp [move]
      have hright : move hm i (2 : Fin 3) = right hm i := by
        simp [move]
      have hL := branch_le hm T w h i (left hm i) 0 hleft
        (fun ds hs => prefix_left h ds hs)
      have hM := branch_le hm T w h i i 1 hmid
        (fun ds hs => prefix_mid h ds hs)
      have hR := branch_le hm T w h i (right hm i) 2 hright
        (fun ds hs => prefix_right h ds hs)
      have hTl := ih (left hm i)
      have hTm := ih i
      have hTr := ih (right hm i)
      have hstep := hrec i h
      have hl : T (left hm i) h + w i h ≤
          pathMaximum hm T w (h + 1) i :=
        Nat.le_trans (Nat.add_le_add_right hTl _) (by
          simpa [Nat.add_comm] using hL)
      have hc : T i h + w i h ≤
          pathMaximum hm T w (h + 1) i :=
        Nat.le_trans (Nat.add_le_add_right hTm _) (by
          simpa [Nat.add_comm] using hM)
      have hr : T (right hm i) h + w i h ≤
          pathMaximum hm T w (h + 1) i :=
        Nat.le_trans (Nat.add_le_add_right hTr _) (by
          simpa [Nat.add_comm] using hR)
      omega

/-- The path wait, without its level-zero initial-time term. -/
def waitMaximum {m : Nat} (hm : 0 < m)
    (w : Fin m → Nat → Nat) (h : Nat) (i : Fin m) : Nat :=
  foldMax ((allSteps h).map (pathWait hm w h i))

/-- Common initial floor yields an additive maximum of path waits. -/
theorem depth_bound_uniform {m : Nat} (hm : 0 < m)
    (T w : Fin m → Nat → Nat) (T0 : Nat)
    (hrec : ∀ i ℓ,
      T i (ℓ + 1) ≤
        max (max (T (left hm i) ℓ) (T i ℓ))
          (T (right hm i) ℓ) + w i ℓ)
    (hfloor : ∀ j, T j 0 ≤ T0) :
    ∀ h i, T i h ≤ T0 + waitMaximum hm w h i := by
  intro h i
  apply Nat.le_trans (depth_bound hm T w hrec h i)
  unfold pathMaximum waitMaximum
  apply foldMax_le_of_all
  intro x hx
  obtain ⟨ds, hs, rfl⟩ := List.mem_map.mp hx
  have hw := le_foldMax_of_mem
    ((allSteps h).map (pathWait hm w h i))
    (pathWait hm w h i ds)
    (List.mem_map.mpr ⟨ds, hs, rfl⟩)
  unfold pathScore
  have ht := hfloor (pathStart hm i ds)
  omega

/-- A fixed endpoint contributes exactly 3^h path-wait functions. -/
def pathWaits {m : Nat} (hm : 0 < m)
    (w : Fin m → Nat → Nat) (h : Nat) (i : Fin m) : List Nat :=
  (allSteps h).map (pathWait hm w h i)

theorem pathWaits_length {m : Nat} (hm : 0 < m)
    (w : Fin m → Nat → Nat) (h : Nat) (i : Fin m) :
    (pathWaits hm w h i).length = 3 ^ h := by
  simp only [pathWaits, List.length_map, allSteps_length]

/-- All endpoints contribute m * 3^h indexed waits (duplicates retained). -/
def allPathWaits {m : Nat} (hm : 0 < m)
    (w : Fin m → Nat → Nat) (h : Nat) : List Nat :=
  (List.finRange m).flatMap (fun i => pathWaits hm w h i)

private theorem flatMap_length_const {α β : Type}
    (xs : List α) (f : α → List β) (n : Nat)
    (hf : ∀ x, x ∈ xs → (f x).length = n) :
    (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_cons]
      rw [hf x (by simp)]
      rw [ih (by
        intro y hy
        exact hf y (by simp [hy]))]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

theorem allPathWaits_length {m : Nat} (hm : 0 < m)
    (w : Fin m → Nat → Nat) (h : Nat) :
    (allPathWaits hm w h).length = m * 3 ^ h := by
  unfold allPathWaits
  rw [flatMap_length_const _ _ (3 ^ h)
    (by intro i hi; exact pathWaits_length hm w h i)]
  simp only [List.length_finRange]

end L4.Height.Depth

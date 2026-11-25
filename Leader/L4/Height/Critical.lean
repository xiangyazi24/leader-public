import Leader.L4.Height.Depth

namespace L4.Height.Depth

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/--
Apply the service functions from the level-zero start of a backward path
forwards toward its endpoint.  The level-zero start itself contributes the
initial time `t0`; every edge contributes the service query at its arrival
site, so a word of length `h` performs exactly `h` queries and ends at `i`.
-/
def seqTime {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 : Nat) :
    Fin m → List (Fin 3) → Nat
  | _, [] => t0
  | i, d :: ds =>
      S i (seqTime hm S t0 (move hm i d) ds)

theorem seqTime_nil {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 : Nat) (i : Fin m) :
    seqTime hm S t0 i [] = t0 := rfl

theorem seqTime_cons {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 : Nat)
    (i : Fin m) (d : Fin 3) (ds : List (Fin 3)) :
    seqTime hm S t0 i (d :: ds) =
      S i (seqTime hm S t0 (move hm i d) ds) := rfl

theorem seqTime_cons_strict {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 : Nat)
    (hafter : ∀ i t, t < S i t)
    (i : Fin m) (d : Fin 3) (ds : List (Fin 3)) :
    seqTime hm S t0 (move hm i d) ds <
      seqTime hm S t0 i (d :: ds) := by
  simp only [seqTime]
  exact hafter i _

/-- The `3^h` sequential query times for one fixed endpoint. -/
def criticalTimes {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 h : Nat)
    (i : Fin m) : List Nat :=
  (allSteps h).map (seqTime hm S t0 i)

/-- Explicit maximum over the `3^h` paths ending at `i`. -/
def criticalMaximum {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 h : Nat)
    (i : Fin m) : Nat :=
  foldMax (criticalTimes hm S t0 h i)

theorem criticalTimes_length {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 h : Nat)
    (i : Fin m) :
    (criticalTimes hm S t0 h i).length = 3 ^ h := by
  simp only [criticalTimes, List.length_map, allSteps_length]

private theorem critical_prefix_left (h : Nat)
    (ds : List (Fin 3)) (hs : ds ∈ allSteps h) :
    ((0 : Fin 3) :: ds) ∈ allSteps (h + 1) := by
  simp only [allSteps, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨ds, hs, rfl⟩)

private theorem critical_prefix_mid (h : Nat)
    (ds : List (Fin 3)) (hs : ds ∈ allSteps h) :
    ((1 : Fin 3) :: ds) ∈ allSteps (h + 1) := by
  simp only [allSteps, List.mem_append]
  exact Or.inr (Or.inl (List.mem_map.mpr ⟨ds, hs, rfl⟩))

private theorem critical_prefix_right (h : Nat)
    (ds : List (Fin 3)) (hs : ds ∈ allSteps h) :
    ((2 : Fin 3) :: ds) ∈ allSteps (h + 1) := by
  simp only [allSteps, List.mem_append]
  exact Or.inr (Or.inr (List.mem_map.mpr ⟨ds, hs, rfl⟩))

private theorem critical_le_foldMax_of_mem
    (xs : List Nat) (a : Nat) (ha : a ∈ xs) :
    a ≤ foldMax xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha
      simp only [foldMax, List.foldr_cons]
      rcases ha with rfl | ht
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

/-- On a nonempty finite list, its folded maximum is one of its entries. -/
private theorem critical_apply_foldMax_le
    (f : Nat → Nat) (xs : List Nat) (B : Nat)
    (hne : xs ≠ [])
    (hb : ∀ x, x ∈ xs → f x ≤ B) :
    f (foldMax xs) ≤ B := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
      have hx : f x ≤ B := hb x (by simp)
      by_cases he : xs = []
      · subst xs
        simp only [foldMax, List.foldr_cons, List.foldr_nil,
          Nat.max_zero]
        exact hx
      · have ht : f (foldMax xs) ≤ B := ih he (by
          intro y hy
          exact hb y (by simp [hy]))
        unfold foldMax at ht ⊢
        rw [List.foldr_cons]
        by_cases hxm : x ≤ List.foldr max 0 xs
        · rw [Nat.max_eq_right hxm]
          exact ht
        · have hmx : List.foldr max 0 xs ≤ x :=
            Nat.le_of_not_ge hxm
          rw [Nat.max_eq_left hmx]
          exact hx

private theorem critical_apply_max_le
    (f : Nat → Nat) (a b B : Nat)
    (ha : f a ≤ B) (hb : f b ≤ B) :
    f (max a b) ≤ B := by
  by_cases hab : a ≤ b
  · rw [Nat.max_eq_right hab]
    exact hb
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    rw [Nat.max_eq_left hba]
    exact ha

/--
The maximum for one predecessor branch, followed by the service at `i`, is
contained in the maximum over the corresponding prefixed paths at `i`.
-/
private theorem critical_branch_le {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 h : Nat)
    (i j : Fin m) (d : Fin 3)
    (hj : move hm i d = j)
    (hp : ∀ ds, ds ∈ allSteps h →
      (d :: ds) ∈ allSteps (h + 1)) :
    S i (criticalMaximum hm S t0 h j) ≤
      criticalMaximum hm S t0 (h + 1) i := by
  unfold criticalMaximum criticalTimes
  apply critical_apply_foldMax_le
  · intro he
    have hl : 3 ^ h = 0 := by
      have hlen := congrArg List.length he
      simpa only [List.length_map, List.length_nil,
        allSteps_length] using hlen
    have hpos : 0 < 3 ^ h := Nat.pow_pos (by decide)
    exact (Nat.ne_of_gt hpos) hl
  · intro x hx
    obtain ⟨ds, hs, rfl⟩ := List.mem_map.mp hx
    apply critical_le_foldMax_of_mem
    exact List.mem_map.mpr ⟨d :: ds, hp ds hs, by
      simp only [seqTime, hj]⟩

/--
Lifted level times are dominated by sequential service queries along one of
exactly `3^h` backward paths ending at the requested site.
-/
theorem critical_bound {m : Nat} (hm : 0 < m)
    (S T : Fin m → Nat → Nat) (t0 : Nat)
    (hafter : ∀ i t, t < S i t)
    (hmono : ∀ i t t', t ≤ t' → S i t ≤ S i t')
    (hrec : ∀ i ℓ,
      T i (ℓ + 1) ≤
        S i (max (max (T (left hm i) ℓ) (T i ℓ))
          (T (right hm i) ℓ)))
    (hfloor : ∀ j, T j 0 ≤ t0) :
    ∀ h i, T i h ≤ criticalMaximum hm S t0 h i := by
  intro h
  induction h with
  | zero =>
      intro i
      simpa only [criticalMaximum, criticalTimes, allSteps,
        List.map_cons, List.map_nil, foldMax, List.foldr_cons,
        List.foldr_nil, seqTime, Nat.max_zero] using hfloor i
  | succ h ih =>
      intro i
      have hmoveLeft :
          move hm i (0 : Fin 3) = left hm i := by
        simp [move]
      have hmoveMid :
          move hm i (1 : Fin 3) = i := by
        simp [move]
      have hmoveRight :
          move hm i (2 : Fin 3) = right hm i := by
        simp [move]

      have htimeLeft :
          T (left hm i) h ≤
            criticalMaximum hm S t0 h (left hm i) :=
        ih (left hm i)
      have htimeMid :
          T i h ≤ criticalMaximum hm S t0 h i :=
        ih i
      have htimeRight :
          T (right hm i) h ≤
            criticalMaximum hm S t0 h (right hm i) :=
        ih (right hm i)

      have harg :
          max (max (T (left hm i) h) (T i h))
              (T (right hm i) h) ≤
            max
              (max
                (criticalMaximum hm S t0 h (left hm i))
                (criticalMaximum hm S t0 h i))
              (criticalMaximum hm S t0 h (right hm i)) := by
        apply (Nat.max_le).mpr
        constructor
        · apply (Nat.max_le).mpr
          constructor
          · calc
              T (left hm i) h ≤
                  criticalMaximum hm S t0 h (left hm i) :=
                htimeLeft
              _ ≤ max
                  (criticalMaximum hm S t0 h (left hm i))
                  (criticalMaximum hm S t0 h i) :=
                Nat.le_max_left _ _
              _ ≤ max
                  (max
                    (criticalMaximum hm S t0 h (left hm i))
                    (criticalMaximum hm S t0 h i))
                  (criticalMaximum hm S t0 h (right hm i)) :=
                Nat.le_max_left _ _
          · calc
              T i h ≤ criticalMaximum hm S t0 h i :=
                htimeMid
              _ ≤ max
                  (criticalMaximum hm S t0 h (left hm i))
                  (criticalMaximum hm S t0 h i) :=
                Nat.le_max_right _ _
              _ ≤ max
                  (max
                    (criticalMaximum hm S t0 h (left hm i))
                    (criticalMaximum hm S t0 h i))
                  (criticalMaximum hm S t0 h (right hm i)) :=
                Nat.le_max_left _ _
        · calc
            T (right hm i) h ≤
                criticalMaximum hm S t0 h (right hm i) :=
              htimeRight
            _ ≤ max
                (max
                  (criticalMaximum hm S t0 h (left hm i))
                  (criticalMaximum hm S t0 h i))
                (criticalMaximum hm S t0 h (right hm i)) :=
              Nat.le_max_right _ _

      have hservice :
          S i
              (max (max (T (left hm i) h) (T i h))
                (T (right hm i) h)) ≤
            S i
              (max
                (max
                  (criticalMaximum hm S t0 h (left hm i))
                  (criticalMaximum hm S t0 h i))
                (criticalMaximum hm S t0 h (right hm i))) :=
        hmono i _ _ harg

      have hpre :
          T i (h + 1) ≤
            S i
              (max
                (max
                  (criticalMaximum hm S t0 h (left hm i))
                  (criticalMaximum hm S t0 h i))
                (criticalMaximum hm S t0 h (right hm i))) :=
        Nat.le_trans (hrec i h) hservice

      have hbranchLeft :
          S i (criticalMaximum hm S t0 h (left hm i)) ≤
            criticalMaximum hm S t0 (h + 1) i :=
        critical_branch_le hm S t0 h i (left hm i) 0
          hmoveLeft
          (fun ds hs => critical_prefix_left h ds hs)
      have hbranchMid :
          S i (criticalMaximum hm S t0 h i) ≤
            criticalMaximum hm S t0 (h + 1) i :=
        critical_branch_le hm S t0 h i i 1
          hmoveMid
          (fun ds hs => critical_prefix_mid h ds hs)
      have hbranchRight :
          S i (criticalMaximum hm S t0 h (right hm i)) ≤
            criticalMaximum hm S t0 (h + 1) i :=
        critical_branch_le hm S t0 h i (right hm i) 2
          hmoveRight
          (fun ds hs => critical_prefix_right h ds hs)

      have hpair :
          S i
              (max
                (criticalMaximum hm S t0 h (left hm i))
                (criticalMaximum hm S t0 h i)) ≤
            criticalMaximum hm S t0 (h + 1) i :=
        critical_apply_max_le
          (S i)
          (criticalMaximum hm S t0 h (left hm i))
          (criticalMaximum hm S t0 h i)
          (criticalMaximum hm S t0 (h + 1) i)
          hbranchLeft hbranchMid

      have hall :
          S i
              (max
                (max
                  (criticalMaximum hm S t0 h (left hm i))
                  (criticalMaximum hm S t0 h i))
                (criticalMaximum hm S t0 h (right hm i))) ≤
            criticalMaximum hm S t0 (h + 1) i :=
        critical_apply_max_le
          (S i)
          (max
            (criticalMaximum hm S t0 h (left hm i))
            (criticalMaximum hm S t0 h i))
          (criticalMaximum hm S t0 h (right hm i))
          (criticalMaximum hm S t0 (h + 1) i)
          hpair hbranchRight

      exact Nat.le_trans hpre hall

/-- Sequential query times for every ending site, with multiplicity. -/
def allCriticalTimes {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 h : Nat) : List Nat :=
  (List.finRange m).flatMap
    (fun i => criticalTimes hm S t0 h i)

private theorem critical_flatMap_length_const {α β : Type}
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

/-- The family over all endpoints has exactly `m * 3^h` members. -/
theorem critical_count {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 h : Nat) :
    (allCriticalTimes hm S t0 h).length = m * 3 ^ h := by
  unfold allCriticalTimes
  rw [critical_flatMap_length_const _ _ (3 ^ h)
    (by
      intro i hi
      exact criticalTimes_length hm S t0 h i)]
  simp only [List.length_finRange]

end L4.Height.Depth

import Leader.L4.Height.OverrunChain

namespace L4.Height

open L4.Compiler.Native
open Classical

/-- The first prefix attaining a given raw lifted level, capped at the
length of the physical word. Level zero is reached at time zero. -/
noncomputable def rawLevelTime {α : Type} {n m : Nat}
    (next : α → Fin n → α) (height : α → Fin m → Nat)
    (x : α) (base : Nat) (u : List (Fin n)) (i : Fin m)
    (d : Nat) : Nat :=
  if d = 0 then 0 else
    overrunLeastTrue
      (fun k => decide
        (base + d ≤ height (Thru.runWord next x (u.take k)) i))
      u.length

/-- Execute consecutive raw-word segments in order. -/
private theorem raw_runWord_append
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u v : List (Fin n)) :
    Thru.runWord next x (u ++ v) =
      Thru.runWord next (Thru.runWord next x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (next x e)

/-- Split a raw prefix at its requested time. -/
private theorem raw_take_add
    {β : Type} (u : List β) (a b : Nat) :
    u.take (a + b) = u.take a ++ (u.drop a).take b := by
  induction a generalizing u with
  | zero => simp
  | succ a ih =>
      cases u with
      | nil => simp
      | cons e u =>
          simp only [Nat.succ_add, List.take_succ_cons,
            List.drop_succ_cons, List.cons_append]
          exact congrArg (List.cons e) (ih u)

/-- An ordinary wait ending before exhaustion witnesses its target. -/
private theorem raw_wait_hit
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop) :
    ∀ x (u : List (Fin n)),
      Thru.wait next A x u < u.length →
        A (Thru.runWord next x
          (u.take (Thru.wait next A x u))) := by
  intro x u
  induction u generalizing x with
  | nil =>
      intro h
      simp [Thru.wait] at h
  | cons e u ih =>
      intro h
      by_cases hx : A x
      · have hw := Thru.wait_of_hit next A x hx (e :: u)
        simpa [hw, Thru.runWord] using hx
      · rw [Thru.wait_cons_of_not next A x hx e u] at h ⊢
        have ht : Thru.wait next A (next x e) u < u.length := by
          simp only [List.length_cons] at h
          omega
        have htail := ih (next x e) ht
        simpa [Thru.runWord] using htail

/-- A strict service inside the word really occurs at its stopping prefix. -/
private theorem raw_service_hit
    {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop)
    (u : List (Fin n)) (i : Fin m) (t : Nat)
    (h : serviceTime next x served u i t < u.length) :
    served i (Thru.runWord next x
      (u.take (serviceTime next x served u i t))) := by
  rw [serviceTime_eq_requested] at h ⊢
  let a := t + 1
  let y := Thru.runWord next x (u.take a)
  let v := u.drop a
  have hw : Thru.wait next (served i) y v < v.length := by
    change a + Thru.wait next (served i) y v < u.length at h
    change Thru.wait next (served i) y v < (u.drop a).length
    rw [List.length_drop]
    omega
  change served i (Thru.runWord next x
    (u.take (a + Thru.wait next (served i) y v)))
  rw [raw_take_add, raw_runWord_append]
  exact raw_wait_hit next (served i) y v hw

/-- A bounded-search result strictly below the cap is a true hit. -/
private theorem raw_search_hit (p : Nat → Bool) (k : Nat)
    (h : overrunLeastTrue p k < k) :
    p (overrunLeastTrue p k) = true := by
  cases k with
  | zero => omega
  | succ k =>
      simp only [overrunLeastTrue] at h ⊢
      split at h <;> rename_i hp
      · simp [hp]
      · omega

/-- An observed true prefix bounds the earliest bounded-search hit. -/
private theorem raw_search_min (p : Nat → Bool) (k j : Nat)
    (hj : j ≤ k) (hp : p j = true) :
    overrunLeastTrue p k ≤ j ∧
      p (overrunLeastTrue p k) = true := by
  induction k with
  | zero =>
      have hz : j = 0 := by omega
      subst j
      exact ⟨Nat.le_refl _, hp⟩
  | succ k ih =>
      simp only [overrunLeastTrue]
      by_cases hjk : j ≤ k
      · obtain ⟨hle, hhit⟩ := ih hjk
        simp [hhit, hle]
      · have he : j = k + 1 := by omega
        split
        next h => exact ⟨by have := overrunLeastTrue_le p k; omega, h⟩
        next _ => exact ⟨by omega, he ▸ hp⟩

/-- Exactly one letter separates consecutive raw prefixes. -/
private theorem raw_prefix_step
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u : List (Fin n)) (q : Nat) (hq : q < u.length) :
    Thru.runWord next x (u.take (q + 1)) =
      next (Thru.runWord next x (u.take q)) u[q] := by
  rw [List.take_succ_eq_append_getElem hq, raw_runWord_append]
  rfl

/-- All lifted coordinates are monotone along the same raw word. -/
private theorem raw_prefix_mono
    {α : Type} {n m : Nat}
    (next : α → Fin n → α) (height : α → Fin m → Nat)
    (hMono : ∀ y e j, height y j ≤ height (next y e) j)
    (x : α) (u : List (Fin n)) (j : Fin m)
    (a q : Nat) (ha : a ≤ q) (hq : q ≤ u.length) :
    height (Thru.runWord next x (u.take a)) j ≤
      height (Thru.runWord next x (u.take q)) j := by
  induction q with
  | zero =>
      have he : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ q ih =>
      by_cases he : a = q + 1
      · subst a
        exact Nat.le_refl _
      · apply Nat.le_trans (ih (by omega) (by omega))
        rw [raw_prefix_step next x u q (by omega)]
        exact hMono _ u[q] j

/-- The no-hit sentinel is at most the word length. -/
private theorem raw_level_le_length
    {α : Type} {n m : Nat}
    (next : α → Fin n → α) (height : α → Fin m → Nat)
    (x : α) (base : Nat) (u : List (Fin n))
    (i : Fin m) (d : Nat) :
    rawLevelTime next height x base u i d ≤ u.length := by
  unfold rawLevelTime
  by_cases hz : d = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    exact overrunLeastTrue_le _ _

/-- If the capped hitting time precedes a strict prefix, the required
level has already been attained at that prefix. -/
private theorem raw_level_at
    {α : Type} {n m : Nat}
    (next : α → Fin n → α) (height : α → Fin m → Nat)
    (x : α) (base : Nat)
    (hBase : ∀ i, base ≤ height x i)
    (hMono : ∀ y e i, height y i ≤ height (next y e) i)
    (u : List (Fin n)) (j : Fin m) (ell q : Nat)
    (ht : rawLevelTime next height x base u j ell ≤ q)
    (hq : q < u.length) :
    base + ell ≤ height (Thru.runWord next x (u.take q)) j := by
  by_cases hz : ell = 0
  · subst ell
    simpa only [Nat.add_zero] using
      (Nat.le_trans (hBase j)
        (raw_prefix_mono next height hMono x u j 0 q
          (Nat.zero_le _) (Nat.le_of_lt hq)))
  · let p : Nat → Bool :=
      fun k => decide
        (base + ell ≤ height (Thru.runWord next x (u.take k)) j)
    have he : rawLevelTime next height x base u j ell =
        overrunLeastTrue p u.length := by
      simp [rawLevelTime, hz, p]
    rw [he] at ht
    have hh := of_decide_eq_true
      (raw_search_hit p u.length (Nat.lt_of_le_of_lt ht hq))
    exact Nat.le_trans hh
      (raw_prefix_mono next height hMono x u j _ q ht
        (Nat.le_of_lt hq))

/-- Three-predecessor causal recurrence on an arbitrary closed raw-state
type; its strict service clock counts actual scheduler letters. -/
theorem raw_level_recurrence {α : Type} {n m : Nat} (hm : 0 < m)
    (next : α → Fin n → α) (height : α → Fin m → Nat)
    (served : Fin m → α → Prop) (x : α) (base : Nat)
    (hBase : ∀ i, base ≤ height x i)
    (hMono : ∀ y e i, height y i ≤ height (next y e) i)
    (hProgress : ∀ y e i k, served i (next y e) →
      k ≤ height y (left hm i) → k ≤ height y i →
      k ≤ height y (right hm i) →
      k + 1 ≤ height (next y e) i) :
    ∀ (u : List (Fin n)) (i : Fin m) (d : Nat),
      rawLevelTime next height x base u i (d + 1) ≤
        serviceTime next x served u i
          (max (max (rawLevelTime next height x base u (left hm i) d)
                    (rawLevelTime next height x base u i d))
               (rawLevelTime next height x base u (right hm i) d)) := by
  intro u i d
  let t := max
    (max (rawLevelTime next height x base u (left hm i) d)
         (rawLevelTime next height x base u i d))
    (rawLevelTime next height x base u (right hm i) d)
  let k := serviceTime next x served u i t
  change rawLevelTime next height x base u i (d + 1) ≤ k
  by_cases hk : k < u.length
  · have hafter : t < k := serviceTime_after next x served u i t
    obtain ⟨q, he⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
    have hq : q < u.length := by omega
    have hs : served i
        (Thru.runWord next x (u.take (q + 1))) := by
      rw [← he]
      exact raw_service_hit next x served u i t hk
    have hsNext : served i
        (next (Thru.runWord next x (u.take q)) u[q]) := by
      rw [← raw_prefix_step next x u q hq]
      exact hs
    have hlocal := raw_level_at next height x base hBase hMono u
    have hl : base + d ≤
        height (Thru.runWord next x (u.take q)) (left hm i) :=
      hlocal (left hm i) d q
        (by dsimp [t] at hafter; omega) hq
    have hc : base + d ≤
        height (Thru.runWord next x (u.take q)) i :=
      hlocal i d q
        (by dsimp [t] at hafter; omega) hq
    have hr : base + d ≤
        height (Thru.runWord next x (u.take q)) (right hm i) :=
      hlocal (right hm i) d q
        (by dsimp [t] at hafter; omega) hq
    have hh : base + d + 1 ≤
        height (Thru.runWord next x (u.take (q + 1))) i := by
      rw [raw_prefix_step next x u q hq]
      exact hProgress
        (Thru.runWord next x (u.take q)) u[q] i (base + d)
        hsNext hl hc hr
    rw [he]
    simp only [rawLevelTime, Nat.succ_ne_zero, ↓reduceIte]
    apply (raw_search_min _ u.length (q + 1) (by omega) _).1
    exact decide_eq_true (by simpa only [Nat.add_assoc] using hh)
  · exact Nat.le_trans
      (raw_level_le_length next height x base u i (d + 1))
      (by omega)

/-- If the final raw state is below a positive requested level, no earlier
prefix attained the level, and the bounded-search value is the cap. -/
theorem raw_level_miss {α : Type} {n m : Nat}
    (next : α → Fin n → α) (height : α → Fin m → Nat)
    (x : α) (base : Nat) (u : List (Fin n))
    (i : Fin m) (d : Nat)
    (hMono : ∀ y e j, height y j ≤ height (next y e) j)
    (hDepth : 0 < d)
    (hMiss : height (Thru.runWord next x u) i < base + d) :
    rawLevelTime next height x base u i d = u.length := by
  apply Nat.le_antisymm
  · exact raw_level_le_length next height x base u i d
  · apply Nat.le_of_not_lt
    intro hlt
    have hz : d ≠ 0 := by omega
    let p : Nat → Bool :=
      fun k => decide
        (base + d ≤ height (Thru.runWord next x (u.take k)) i)
    have he : rawLevelTime next height x base u i d =
        overrunLeastTrue p u.length := by
      simp [rawLevelTime, hz, p]
    rw [he] at hlt
    have hh : base + d ≤
        height (Thru.runWord next x
          (u.take (overrunLeastTrue p u.length))) i :=
      of_decide_eq_true (raw_search_hit p u.length hlt)
    have hlast : height (Thru.runWord next x
        (u.take (overrunLeastTrue p u.length))) i ≤
        height (Thru.runWord next x (u.take u.length)) i :=
      raw_prefix_mono next height hMono x u i
        (overrunLeastTrue p u.length) u.length
        (overrunLeastTrue_le p u.length) (Nat.le_refl _)
    have hfinal : base + d ≤ height (Thru.runWord next x u) i := by
      have hle := Nat.le_trans hh hlast
      simpa using hle
    exact (Nat.not_le_of_gt hMiss) hfinal

end L4.Height


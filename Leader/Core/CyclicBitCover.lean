import Std

/-!
# Coordinate-wise covers in a cyclic binary word

Formalization of the bit-cover combinatorial argument.

For each coordinate, every bad target charges its preceding R positions.
The binary-alphabet argument in `charge_overlap` proves that distinct
bad targets have disjoint charges. A duplicate-free List of charges gives
`bad_count_le`. A List-based union bound then gives `covered_count_ge`
at radius 2 * psi. `cover_map` selects an actual preceding supplier for
each coordinate. The repeated five-coordinate one-hot word supplies the
closed radius-four counterexample.

This module is independent of protocol states, transitions, provenance,
and scheduling. Counts use List.finRange and List.countP. The decidability
instances reduce the bounded Nat quantifier in Bad to a finite quantifier;
the one-hot counterexample is consequently checked by plain decide.
-/

set_option autoImplicit false
set_option Elab.async false

namespace B6BitCover

universe u v

variable {m ψ R : Nat}

abbrev Word (m ψ : Nat) := Fin m → Fin ψ → Bool

/-- The d-th cyclic predecessor. The presence of j : Fin m supplies m > 0,
so the definition also has a well-typed empty-domain interpretation at m = 0. -/
def pred (d : Nat) (j : Fin m) : Fin m :=
  ⟨(j.val + m - d % m) % m,
    Nat.mod_lt _ (by have hj := j.isLt; omega)⟩

/-- No matching bit occurs among the preceding R positions. -/
def Bad (w : Word m ψ) (R : Nat) (j : Fin m) (k : Fin ψ) : Prop :=
  ∀ d : Nat, 1 ≤ d → d ≤ R → w (pred d j) k ≠ w j k

/-- Every coordinate has some matching bit among the preceding R positions. -/
def Covered (w : Word m ψ) (R : Nat) (j : Fin m) : Prop :=
  ∀ k : Fin ψ, ¬ Bad w R j k

/-- A finite presentation of exactly the same bounded Nat quantifier. -/
theorem bad_iff_fin (w : Word m ψ) (R : Nat) (j : Fin m) (k : Fin ψ) :
    Bad w R j k ↔
      ∀ t : Fin R, w (pred (t.val + 1) j) k ≠ w j k := by
  constructor
  · intro h t
    have ht := t.isLt
    exact h (t.val + 1) (by omega) (by omega)
  · intro h d hd hR
    have ht := h (⟨d - 1, by omega⟩ : Fin R)
    change w (pred (d - 1 + 1) j) k ≠ w j k at ht
    have he : d - 1 + 1 = d := by omega
    simpa only [he] using ht

instance instDecidableBad (w : Word m ψ) (R : Nat)
    (j : Fin m) (k : Fin ψ) : Decidable (Bad w R j k) :=
  decidable_of_iff
    (∀ t : Fin R, w (pred (t.val + 1) j) k ≠ w j k)
    (bad_iff_fin w R j k).symm

instance instDecidableCovered (w : Word m ψ) (R : Nat)
    (j : Fin m) : Decidable (Covered w R j) := by
  unfold Covered
  infer_instance

/-- Number of bad targets at the given coordinate. -/
def badCount (w : Word m ψ) (R : Nat) (k : Fin ψ) : Nat :=
  (List.finRange m).countP (fun j => decide (Bad w R j k))

/-- Number of targets covered at every coordinate. -/
def coveredCount (w : Word m ψ) (R : Nat) : Nat :=
  (List.finRange m).countP (fun j => decide (Covered w R j))

/-! ## Small-distance cyclic arithmetic -/

private theorem mod_below_twice (x m : Nat) (hx : x < 2 * m) :
    x % m = if x < m then x else x - m := by
  by_cases h : x < m
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h, Nat.mod_eq_sub_mod (by omega : m ≤ x)]
    exact Nat.mod_eq_of_lt (by omega)

/-- For a distance below the ring size there is at most one wrap. -/
theorem pred_val_small (d : Nat) (j : Fin m) (hd : d < m) :
    (pred d j).val =
      if d ≤ j.val then j.val - d else j.val + m - d := by
  have hj := j.isLt
  change (j.val + m - d % m) % m =
    if d ≤ j.val then j.val - d else j.val + m - d
  rw [Nat.mod_eq_of_lt hd,
    mod_below_twice (j.val + m - d) m (by omega)]
  split <;> split <;> omega

/-- A subtraction-free version of the same wrap calculation. -/
theorem pred_add_cases (d : Nat) (j : Fin m) (hd : d < m) :
    (pred d j).val + d = j.val ∨
      (pred d j).val + d = j.val + m := by
  rw [pred_val_small d j hd]
  split
  · left
    omega
  · right
    omega

/-- At a fixed small distance, the predecessor determines its target. -/
theorem pred_target_eq_of_eq (d : Nat) (j j' : Fin m) (hd : d < m)
    (h : pred d j = pred d j') : j = j' := by
  have h₁ := pred_add_cases d j hd
  have h₂ := pred_add_cases d j' hd
  have hv := congrArg Fin.val h
  have hj := j.isLt
  have hj' := j'.isLt
  apply Fin.ext
  omega

/-- At a fixed target, small distances have distinct predecessors. -/
theorem pred_offset_eq_of_eq (j : Fin m) {d e : Nat}
    (hd : d < m) (he : e < m)
    (h : pred d j = pred e j) : d = e := by
  have h₁ := pred_add_cases d j hd
  have h₂ := pred_add_cases e j he
  have hv := congrArg Fin.val h
  omega

/-- If the same charged point is d steps behind j and e steps behind j',
and d < e, then j itself is e-d steps behind j'. -/
theorem pred_sub_eq_of_overlap (j j' : Fin m) {d e : Nat}
    (hd : d < m) (he : e < m) (hde : d < e)
    (h : pred d j = pred e j') : pred (e - d) j' = j := by
  have hdiff : e - d < m := by omega
  have h₁ := pred_add_cases d j hd
  have h₂ := pred_add_cases e j' he
  have h₃ := pred_add_cases (e - d) j' hdiff
  have hv := congrArg Fin.val h
  have hj := j.isLt
  have hj' := j'.isLt
  have hz := (pred (e - d) j').isLt
  apply Fin.ext
  omega

/-! ## Binary charging injection -/

/-- This is the only alphabet-specific step: both bits opposite to a fixed
Bool must be equal. It would not hold for an arbitrary larger alphabet. -/
private theorem bool_eq_of_common_ne {a b c : Bool}
    (ha : c ≠ a) (hb : c ≠ b) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Charged positions of bad targets cannot overlap, except at the same
target and the same offset. The endpoints 1 and R are included. -/
theorem charge_overlap (w : Word m ψ) (hm : R < m) (k : Fin ψ)
    (j j' : Fin m) (hj : Bad w R j k) (hj' : Bad w R j' k)
    {d e : Nat} (hd : 1 ≤ d) (hdR : d ≤ R)
    (he : 1 ≤ e) (heR : e ≤ R)
    (h : pred d j = pred e j') : j = j' ∧ d = e := by
  have hdm : d < m := Nat.lt_of_le_of_lt hdR hm
  have hem : e < m := Nat.lt_of_le_of_lt heR hm
  have hbits : w j k = w j' k :=
    bool_eq_of_common_ne (hj d hd hdR) (by
      rw [h]
      exact hj' e he heR)
  by_cases hde : d < e
  · have hpos := pred_sub_eq_of_overlap j j' hdm hem hde h
    have hbad := hj' (e - d) (by omega) (by omega)
    rw [hpos] at hbad
    exact False.elim (hbad hbits)
  · by_cases hed : e < d
    · have hpos := pred_sub_eq_of_overlap j' j hem hdm hed h.symm
      have hbad := hj (d - e) (by omega) (by omega)
      rw [hpos] at hbad
      exact False.elim (hbad hbits.symm)
    · have hdist : d = e := by omega
      subst e
      exact ⟨pred_target_eq_of_eq d j j' hdm h, rfl⟩

/-- The requested charge map on bad-target/offset pairs. -/
def charge (w : Word m ψ) (R : Nat) (k : Fin ψ)
    (a : {j : Fin m // Bad w R j k} × Fin R) : Fin m :=
  pred (a.2.val + 1) a.1.val

/-- Injectivity is stated without requiring any finite-set library. -/
theorem charge_injective (w : Word m ψ) (hm : R < m) (k : Fin ψ)
    (a b : {j : Fin m // Bad w R j k} × Fin R)
    (h : charge w R k a = charge w R k b) : a = b := by
  have ha := a.2.isLt
  have hb := b.2.isLt
  have hc := charge_overlap w hm k a.1.val b.1.val
    a.1.property b.1.property
    (d := a.2.val + 1) (e := b.2.val + 1)
    (by omega) (by omega) (by omega) (by omega) h
  apply Prod.ext
  · exact Subtype.ext hc.1
  · apply Fin.ext
    omega

/-! ## The per-coordinate count -/

/-- The R charged predecessors, each listed once when R < m. -/
def chargeList (R : Nat) (j : Fin m) : List (Fin m) :=
  (List.finRange R).map (fun t => pred (t.val + 1) j)

@[simp] theorem chargeList_length (R : Nat) (j : Fin m) :
    (chargeList R j).length = R := by
  simp [chargeList]

theorem mem_chargeList {j x : Fin m} :
    x ∈ chargeList R j ↔
      ∃ t : Fin R, pred (t.val + 1) j = x := by
  simp [chargeList, List.mem_map]

theorem chargeList_nodup (hm : R < m) (j : Fin m) :
    (chargeList R j).Nodup := by
  change List.Pairwise (fun x y : Fin m => x ≠ y)
    ((List.finRange R).map (fun t => pred (t.val + 1) j))
  apply List.pairwise_map.mpr
  refine List.Pairwise.imp ?_ (List.nodup_finRange R)
  intro a b hab heq
  apply hab
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  have hoff := pred_offset_eq_of_eq j
    (d := a.val + 1) (e := b.val + 1)
    (by omega) (by omega) heq
  omega

/-- Concatenating the charges of a duplicate-free list of bad targets
still gives a duplicate-free list. -/
theorem chargeLists_nodup (w : Word m ψ) (hm : R < m) (k : Fin ψ)
    (js : List (Fin m)) :
    js.Nodup → (∀ j, j ∈ js → Bad w R j k) →
      (js.flatMap (chargeList R)).Nodup := by
  induction js with
  | nil =>
      intro _ _
      simp
  | cons j js ih =>
      intro hnd hbad
      have hn := List.nodup_cons.mp hnd
      have hjBad : Bad w R j k := hbad j (by simp)
      have hrest : ∀ i, i ∈ js → Bad w R i k := by
        intro i hi
        exact hbad i (List.mem_cons_of_mem j hi)
      simp only [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨chargeList_nodup hm j, ih hn.2 hrest, ?_⟩
      intro x hx y hy hxy
      obtain ⟨t, ht⟩ := mem_chargeList.mp hx
      obtain ⟨j', hj', hy'⟩ := List.mem_flatMap.mp hy
      obtain ⟨s, hs⟩ := mem_chargeList.mp hy'
      have htr := t.isLt
      have hsr := s.isLt
      have hc := charge_overlap w hm k j j' hjBad (hrest j' hj')
        (d := t.val + 1) (e := s.val + 1)
        (by omega) (by omega) (by omega) (by omega)
        (ht.trans (hxy.trans hs.symm))
      apply hn.1
      rw [hc.1]
      exact hj'

private theorem chargeLists_length (R : Nat) (js : List (Fin m)) :
    (js.flatMap (chargeList R)).length = R * js.length := by
  induction js with
  | nil => simp
  | cons j js ih =>
      simp only [List.flatMap_cons, List.length_append,
        chargeList_length, List.length_cons, ih]
      simp [Nat.mul_add, Nat.add_comm]

/-- Per-coordinate charging bound. No division or rounding convention is
needed: the count is the concrete List.countP count on Fin m. -/
theorem bad_count_le (w : Word m ψ) (hR : 1 ≤ R)
    (hm : R < m) (k : Fin ψ) : R * badCount w R k ≤ m := by
  let js := (List.finRange m).filter (fun j => decide (Bad w R j k))
  have hnd : js.Nodup := by
    exact List.Pairwise.filter
      (fun j => decide (Bad w R j k)) (List.nodup_finRange m)
  have hbad : ∀ j, j ∈ js → Bad w R j k := by
    intro j hj
    have hj' : j ∈ (List.finRange m).filter
        (fun i => decide (Bad w R i k)) := hj
    exact of_decide_eq_true (List.mem_filter.mp hj').2
  have hc : (js.flatMap (chargeList R)).Nodup :=
    chargeLists_nodup w hm k js hnd hbad
  have hlen : (js.flatMap (chargeList R)).length ≤
      (List.finRange m).length :=
    List.Nodup.length_le_of_subset hc (by
      intro x _
      exact List.mem_finRange x)
  have hbound : R * js.length ≤ m := by
    simpa only [chargeLists_length, List.length_finRange] using hlen
  simpa only [badCount, List.countP_eq_length_filter, js] using hbound

/-! ## List-based union bound -/

private theorem countP_or_le {α : Type u} (xs : List α)
    (p q : α → Bool) :
    xs.countP (fun x => p x || q x) ≤ xs.countP p + xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;>
        simp [List.countP_cons, hp, hq] at * <;> omega

private theorem countP_any_le {α : Type u} {β : Type v}
    (xs : List α) (ys : List β) (p : β → α → Bool) :
    xs.countP (fun x => ys.any (fun y => p y x)) ≤
      (ys.map (fun y => xs.countP (p y))).sum := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      simp only [List.any_cons, List.map_cons, List.sum_cons]
      exact Nat.le_trans
        (countP_or_le xs (p y) (fun x => ys.any (fun z => p z x)))
        (Nat.add_le_add_left ih (xs.countP (p y)))

private theorem countP_partition {α : Type u}
    (xs : List α) (p : α → Bool) :
    xs.length = xs.countP p + xs.countP (fun x => !(p x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x <;>
        simp [List.countP_cons, hp] at * <;> omega

private theorem mul_sum_bound {α : Type u}
    (xs : List α) (f : α → Nat) (r b : Nat) :
    (∀ x, x ∈ xs → r * f x ≤ b) →
      r * (xs.map f).sum ≤ xs.length * b := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro h
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.mul_add, Nat.add_mul, Nat.one_mul]
      omega

private def anyBad (w : Word m ψ) (R : Nat) (j : Fin m) : Bool :=
  (List.finRange ψ).any (fun k => decide (Bad w R j k))

private def uncoveredCount (w : Word m ψ) (R : Nat) : Nat :=
  (List.finRange m).countP (anyBad w R)

private theorem not_anyBad_eq_decide (w : Word m ψ) (R : Nat)
    (j : Fin m) : (!(anyBad w R j)) = decide (Covered w R j) := by
  by_cases h : Covered w R j
  · have hany : anyBad w R j = false := by
      unfold anyBad
      rw [List.any_eq_false]
      intro k _
      simpa using h k
    rw [hany, decide_eq_true h]
    rfl
  · have hex : ∃ k : Fin ψ, Bad w R j k :=
      Classical.byContradiction fun hne => h (fun k hk => hne ⟨k, hk⟩)
    obtain ⟨k, hk⟩ := hex
    have hany : anyBad w R j = true := by
      unfold anyBad
      rw [List.any_eq_true]
      exact ⟨k, List.mem_finRange k, by simpa using hk⟩
    rw [hany, decide_eq_false h]
    rfl

private theorem counts_partition (w : Word m ψ) (R : Nat) :
    m = uncoveredCount w R + coveredCount w R := by
  have h := countP_partition (List.finRange m) (anyBad w R)
  have hf : (fun x => !(anyBad w R x)) = (fun j => decide (Covered w R j)) := by
    funext x
    exact not_anyBad_eq_decide w R x
  rw [List.length_finRange, hf] at h
  simpa only [uncoveredCount, coveredCount] using h

private theorem uncovered_count_le (w : Word m ψ) (R : Nat) :
    uncoveredCount w R ≤
      ((List.finRange ψ).map (fun k => badCount w R k)).sum := by
  exact countP_any_le (List.finRange m) (List.finRange ψ)
    (fun k j => decide (Bad w R j k))

/-- At radius 2 * psi, at least half of all cyclic targets are covered. -/
theorem covered_count_ge (w : Word m ψ) (hψ : 0 < ψ)
    (hm : 2 * ψ < m) : m ≤ 2 * coveredCount w (2 * ψ) := by
  let U := uncoveredCount w (2 * ψ)
  let B := ((List.finRange ψ).map
    (fun k => badCount w (2 * ψ) k)).sum
  have hu : U ≤ B := uncovered_count_le w (2 * ψ)
  have hb : (2 * ψ) * B ≤ ψ * m := by
    have h := mul_sum_bound (List.finRange ψ)
      (fun k => badCount w (2 * ψ) k) (2 * ψ) m
      (fun k _ => bad_count_le w (by omega) hm k)
    simpa only [List.length_finRange] using h
  have hscaled : (2 * ψ) * U ≤ ψ * m :=
    Nat.le_trans (Nat.mul_le_mul_left (2 * ψ) hu) hb
  have hscaled' : ψ * (2 * U) ≤ ψ * m := by
    calc
      ψ * (2 * U) = (2 * ψ) * U := by
        rw [← Nat.mul_assoc, Nat.mul_comm ψ 2]
      _ ≤ ψ * m := hscaled
  have hU : 2 * U ≤ m := Nat.le_of_mul_le_mul_left hscaled' hψ
  have hpart : m = U + coveredCount w (2 * ψ) :=
    counts_partition w (2 * ψ)
  omega

/-! ## Supplier selection -/

/-- Select one bounded predecessor with the right bit at each coordinate.
The chosen predecessor may depend on the coordinate. -/
theorem cover_map {w : Word m ψ} {j : Fin m}
    (hc : Covered w R j) :
    ∃ f : Fin ψ → Nat, ∀ k,
      1 ≤ f k ∧ f k ≤ R ∧ w (pred (f k) j) k = w j k := by
  classical
  have hs : ∀ k : Fin ψ, ∃ d : Nat,
      1 ≤ d ∧ d ≤ R ∧ w (pred d j) k = w j k := by
    intro k
    apply Classical.byContradiction
    intro hnone
    apply hc k
    intro d hd hdR heq
    exact hnone ⟨d, hd, hdR, heq⟩
  refine ⟨fun k => Classical.choose (hs k), ?_⟩
  intro k
  exact Classical.choose_spec (hs k)

/-! ## A fixed radius of four does not cover every binary word -/

/-- Two cyclic repetitions of the five distinct one-hot identifiers. -/
def oneHot : Word 10 5 :=
  fun j k => decide (j.val % 5 = k.val)

/-- The closed finite counterexample. -/
theorem oneHot_no_covered : ∀ j : Fin 10, ¬ Covered oneHot 4 j := by
  decide

/-- The counterexample also has exactly zero covered targets. -/
theorem oneHot_coveredCount_eq_zero : coveredCount oneHot 4 = 0 := by
  decide

end B6BitCover

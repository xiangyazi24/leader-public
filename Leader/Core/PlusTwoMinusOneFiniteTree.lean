import Leader.Core.PredictableTrialFiniteTree

/-!
# Finite scheduler theorem for a predictable plus-two/minus-one trial

This module turns the generic stopped action-tree bounds into the exact
arithmetic used by the centered AAFJ zero-leader trial.  The two distinguished
edges are functions of the current proof state; no independence premise is
present.  All conclusions are finite-horizon, division-free scheduler counts.
-/

namespace PlusTwoMinusOneFiniteTree

open PredictableTrialFiniteTree

set_option autoImplicit false

private theorem sum_map_const {α : Type} [BEq α] (xs : List α) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp only [Nat.succ_mul]
      omega

private theorem nodup_ofFn_of_injective {n : Nat} {α : Type}
    (f : Fin n → α) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
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

private theorem pred_mul (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [Nat.succ_mul, Nat.add_comm]

private theorem sum_ofFn_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n ↦ c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem sum_one_exception
    {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) (f : α → Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hother : ∀ z, z ∈ xs → z ≠ a → f z = c) :
    (xs.map f).sum = f a + (xs.length - 1) * c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hall : xs.map f = xs.map (fun _ => c) := by
          apply List.map_congr_left
          intro z hz
          exact hother z (by simp [hz])
            (by intro q; subst z; exact hnodup.1 hz)
        rw [List.map_cons, List.sum_cons, hall, sum_map_const]
        simp
      · have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | hat
          · exact absurd hax.symm hxa
          · exact hat
        have hot : ∀ z, z ∈ xs → z ≠ a → f z = c := by
          intro z hz
          exact hother z (by simp [hz])
        have hi := ih hnodup.2 hat hot
        have hx : f x = c := hother x (by simp) hxa
        rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
        have hpos : 0 < xs.length :=
          List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
        have hc := pred_mul xs.length c hpos
        have hsub : xs.length + 1 - 1 = xs.length := by omega
        rw [hsub]
        omega

/-- Sum a function that is constant away from two distinct list entries. -/
theorem sum_two_exceptions
    {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (a b : α) (f : α → Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b)
    (hother : ∀ z, z ∈ xs → z ≠ a → z ≠ b → f z = c) :
    (xs.map f).sum = f a + f b + (xs.length - 2) * c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hbt : b ∈ xs := by
          rcases List.mem_cons.mp hb with hbx | hbt
          · exact absurd hbx.symm hab
          · exact hbt
        have hone := sum_one_exception xs b f c hnodup.2 hbt (by
          intro z hz hzb
          exact hother z (by simp [hz])
            (by intro hza; subst z; exact hnodup.1 hz) hzb)
        rw [List.map_cons, List.sum_cons, hone, List.length_cons]
        have hsub : xs.length + 1 - 2 = xs.length - 1 := by omega
        rw [hsub]
        omega
      · by_cases hxb : x = b
        · subst x
          have hat : a ∈ xs := by
            rcases List.mem_cons.mp ha with hax | hat
            · exact absurd hax hab
            · exact hat
          have hone := sum_one_exception xs a f c hnodup.2 hat (by
            intro z hz hza
            exact hother z (by simp [hz]) hza
              (by intro hzb; subst z; exact hnodup.1 hz))
          rw [List.map_cons, List.sum_cons, hone, List.length_cons]
          have hsub : xs.length + 1 - 2 = xs.length - 1 := by omega
          rw [hsub]
          omega
        · have hat : a ∈ xs := by
            rcases List.mem_cons.mp ha with hax | hat
            · exact absurd hax.symm hxa
            · exact hat
          have hbt : b ∈ xs := by
            rcases List.mem_cons.mp hb with hbx | hbt
            · exact absurd hbx.symm hxb
            · exact hbt
          have hot : ∀ z, z ∈ xs → z ≠ a → z ≠ b → f z = c := by
            intro z hz
            exact hother z (by simp [hz])
          have hi := ih hnodup.2 hat hbt hot
          have hx : f x = c := hother x (by simp) hxa hxb
          rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
          have hlen : 2 ≤ xs.length := by
            have h1 : 0 < xs.length :=
              List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
            by_cases hlen1 : xs.length = 1
            · rw [List.length_eq_one_iff] at hlen1
              obtain ⟨z, hz⟩ := hlen1
              subst xs
              simp at hat hbt
              exact absurd (hat.trans hbt.symm) hab
            · omega
          have hLp : 0 < xs.length - 1 := by omega
          have hc := pred_mul (xs.length - 1) c hLp
          have hidx : xs.length + 1 - 2 = xs.length - 1 := by omega
          have hidx2 : xs.length - 1 - 1 = xs.length - 2 := by omega
          rw [hidx2] at hc
          rw [hidx]
          omega

/-- Exact proof-facing interface for an adaptive stopped walk. -/
structure Spec (S : Type) (n B : Nat) where
  active : S → Bool
  next : S → Fin n → S
  coord : S → Nat
  upEdge : S → Fin n
  downEdge : S → Fin n
  edge_count : 2 ≤ n
  coord_le : ∀ s, coord s ≤ B
  active_pos : ∀ s, active s = true → 1 ≤ coord s
  active_up_le : ∀ s, active s = true → coord s + 2 ≤ B
  edges_ne : ∀ s, active s = true → upEdge s ≠ downEdge s
  up_coord : ∀ s, active s = true →
    coord (next s (upEdge s)) = coord s + 2
  down_coord : ∀ s, active s = true →
    coord (next s (downEdge s)) + 1 = coord s
  frame_coord : ∀ s, active s = true → ∀ e,
    e ≠ upEdge s → e ≠ downEdge s → coord (next s e) = coord s

theorem coord_child_sum_eq {S : Type} {n B : Nat}
    (M : Spec S n B) (s : S) (hs : M.active s = true) :
    (List.ofFn (fun e : Fin n ↦ M.coord (M.next s e))).sum =
      n * M.coord s + 1 := by
  let xs := List.ofFn (fun e : Fin n ↦ e)
  have hsum := sum_two_exceptions xs (M.upEdge s) (M.downEdge s)
    (fun e ↦ M.coord (M.next s e)) (M.coord s)
    (nodup_ofFn_of_injective (fun e : Fin n ↦ e) Function.injective_id)
    (List.mem_ofFn.mpr ⟨M.upEdge s, rfl⟩)
    (List.mem_ofFn.mpr ⟨M.downEdge s, rfl⟩)
    (M.edges_ne s hs) (by
      intro z hz hzu hzd
      exact M.frame_coord s hs z hzu hzd)
  have hlen : xs.length = n := by simp [xs]
  have hmap : xs.map (fun e ↦ M.coord (M.next s e)) =
      List.ofFn (fun e : Fin n ↦ M.coord (M.next s e)) := by
    simp [xs, List.map_ofFn, Function.comp_def]
  rw [← hmap, hsum, M.up_coord s hs, hlen]
  have hdown := M.down_coord s hs
  have hn2 : 2 ≤ n := M.edge_count
  have hn : n = (n - 2) + 2 := by omega
  have hmul : n * M.coord s =
      (n - 2) * M.coord s + 2 * M.coord s := by
    calc
      n * M.coord s = ((n - 2) + 2) * M.coord s :=
        congrArg (fun m : Nat ↦ m * M.coord s) hn
      _ = (n - 2) * M.coord s + 2 * M.coord s := Nat.add_mul _ _ _
  omega

/-- The generic stopped-tree duration budget specialized to the exact
plus-two/minus-one/frame arithmetic.  After division by `n^t`, the left weighted term is
`(1/n)` times the truncated raw-interaction duration. -/
theorem duration_budget {S : Type} {n B : Nat}
    (M : Spec S n B) (s : S) (t : Nat) :
    n ^ t * M.coord s +
        weightedLiveTotal M.active M.next s t ≤ n ^ t * B := by
  apply weightedLiveTotal_budget M.active M.next M.coord M.coord_le
  intro x hx
  rw [coord_child_sum_eq M x hx]
  exact Nat.le_refl _

/-- Integer clearing of `(2/3)^q`: `failureWeight B q / 3^B`. -/
def failureWeight (B q : Nat) : Nat := 2 ^ q * 3 ^ (B - q)

theorem failureWeight_pos (B q : Nat) : 0 < failureWeight B q := by
  exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))

/-- The exact two exceptional weights are dominated by two copies of the
current weight. -/
theorem failureWeight_up_down_le (B q : Nat)
    (hq : 1 ≤ q) (hup : q + 2 ≤ B) :
    failureWeight B (q + 2) + failureWeight B (q - 1) ≤
      2 * failureWeight B q := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hup
  rw [hr]
  cases q with
  | zero => omega
  | succ q =>
      have hUp : q + 1 + 2 + r - (q + 1 + 2) = r := by omega
      have hDown : q + 1 + 2 + r - q = r + 3 := by omega
      have hCur : q + 1 + 2 + r - (q + 1) = r + 2 := by omega
      change
        2 ^ (q + 1 + 2) * 3 ^ (q + 1 + 2 + r - (q + 1 + 2)) +
            2 ^ q * 3 ^ (q + 1 + 2 + r - q) ≤
          2 * (2 ^ (q + 1) * 3 ^ (q + 1 + 2 + r - (q + 1)))
      rw [hUp, hDown, hCur]
      let z := 2 ^ q * 3 ^ r
      calc
        2 ^ (q + 1 + 2) * 3 ^ r + 2 ^ q * 3 ^ (r + 3) =
            8 * z + 27 * z := by
              simp [z, Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm]
              rw [show (8 : Nat) = 2 * 4 by decide]
              ac_rfl
        _ = 35 * z := by omega
        _ ≤ 36 * z := Nat.mul_le_mul_right z (by omega)
        _ = 2 * (2 ^ (q + 1) * 3 ^ (r + 2)) := by
              simp [z, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm]
              rw [show (36 : Nat) = 2 * 2 * 9 by decide]
              ac_rfl

theorem failureWeight_child_sum_le {S : Type} {n B : Nat}
    (M : Spec S n B) (s : S) (hs : M.active s = true) :
    (List.ofFn (fun e : Fin n ↦ failureWeight B (M.coord (M.next s e)))).sum ≤
      n * failureWeight B (M.coord s) := by
  let xs := List.ofFn (fun e : Fin n ↦ e)
  have hsum := sum_two_exceptions xs (M.upEdge s) (M.downEdge s)
    (fun e ↦ failureWeight B (M.coord (M.next s e)))
    (failureWeight B (M.coord s))
    (nodup_ofFn_of_injective (fun e : Fin n ↦ e) Function.injective_id)
    (List.mem_ofFn.mpr ⟨M.upEdge s, rfl⟩)
    (List.mem_ofFn.mpr ⟨M.downEdge s, rfl⟩)
    (M.edges_ne s hs) (by
      intro z hz hzu hzd
      rw [M.frame_coord s hs z hzu hzd])
  have hlen : xs.length = n := by simp [xs]
  have hmap : xs.map
      (fun e ↦ failureWeight B (M.coord (M.next s e))) =
      List.ofFn (fun e : Fin n ↦ failureWeight B (M.coord (M.next s e))) := by
    simp [xs, List.map_ofFn, Function.comp_def]
  rw [← hmap, hsum, M.up_coord s hs, hlen]
  have hdown := M.down_coord s hs
  rw [show M.coord (M.next s (M.downEdge s)) = M.coord s - 1 by omega]
  have hpair := failureWeight_up_down_le B (M.coord s)
    (M.active_pos s hs) (M.active_up_le s hs)
  have hn2 : 2 ≤ n := M.edge_count
  have hn : n = (n - 2) + 2 := by omega
  have hmul : n * failureWeight B (M.coord s) =
      (n - 2) * failureWeight B (M.coord s) +
        2 * failureWeight B (M.coord s) := by
    calc
      n * failureWeight B (M.coord s) =
          ((n - 2) + 2) * failureWeight B (M.coord s) :=
        congrArg (fun m : Nat ↦ m * failureWeight B (M.coord s)) hn
      _ = (n - 2) * failureWeight B (M.coord s) +
          2 * failureWeight B (M.coord s) := Nat.add_mul _ _ _
  omega

/-- The stopped exponential weight is a finite-tree supermartingale. -/
theorem failureWeight_supermartingale {S : Type} {n B : Nat}
    (M : Spec S n B) (s : S) (t : Nat) :
    actionTreeTotal M.active M.next (failureWeight B ∘ M.coord) s t ≤
      n ^ t * failureWeight B (M.coord s) := by
  apply actionTreeTotal_supermartingale
  intro x
  cases hx : M.active x
  · simp only [stoppedNext, hx, Function.comp_apply]
    change (List.ofFn (fun _ : Fin n ↦ failureWeight B (M.coord x))).sum ≤
        n * failureWeight B (M.coord x)
    rw [sum_ofFn_const]
    exact Nat.le_refl _
  · simpa [stoppedNext, hx, Function.comp_def] using
      failureWeight_child_sum_le M x hx

/-- If every bad stopped endpoint has coordinate zero, then its exact count
obeys the denominator-cleared bound corresponding to `(2/3)^q`. -/
theorem failure_count_bound {S : Type} {n B : Nat}
    (M : Spec S n B) (bad : S → Bool)
    (hbad : ∀ s, bad s = true → M.coord s = 0)
    (s : S) (t : Nat) :
    3 ^ B * badEndpointCount M.active bad M.next s t ≤
      n ^ t * failureWeight B (M.coord s) := by
  apply badEndpointCount_weight_bound M.active bad M.next
    (failureWeight B ∘ M.coord)
  · intro x
    cases hx : M.active x
    · simp only [stoppedNext, hx, Function.comp_apply]
      change (List.ofFn (fun _ : Fin n ↦ failureWeight B (M.coord x))).sum ≤
          n * failureWeight B (M.coord x)
      rw [sum_ofFn_const]
      exact Nat.le_refl _
    · simpa [stoppedNext, hx, Function.comp_def] using
        failureWeight_child_sum_le M x hx
  · intro x hx
    change 3 ^ B ≤ failureWeight B (M.coord x)
    rw [hbad x hx]
    simp [failureWeight]

end PlusTwoMinusOneFiniteTree

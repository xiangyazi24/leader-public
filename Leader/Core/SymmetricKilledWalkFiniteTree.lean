import Leader.Core.FiniteUniformStoppingTree

/-!
# Symmetric killed walks on finite uniform scheduler trees

This module packages the arithmetic needed by a stopped nearest-neighbor
coordinate with two predictable scheduler edges.  Children may be killed into
either terminal outcome; the specification asks only for the corresponding
coordinate and concave-potential upper bounds.  Consequently a collision can
replace a nominal neighbor without introducing lineage choices.
-/

namespace SymmetricKilledWalkFiniteTree

open FiniteUniformStoppingTree

set_option autoImplicit false

/-- Endpoint extension of an active coordinate.  Success is the lower endpoint
and failure is the upper endpoint. -/
def endpointCoord {S : Type} (coord : S → Nat) (L : Nat) : StopNode S → Nat
  | .active s => coord s
  | .success => 0
  | .failure => L

/-- The standard concave gambler's-ruin potential. -/
def concave (L q : Nat) : Nat := q * (L - q)

/-- Endpoint extension of the concave potential; both killed endpoints have
value zero. -/
def endpointConcave {S : Type} (coord : S → Nat) (L : Nat) :
    StopNode S → Nat
  | .active s => concave L (coord s)
  | .success => 0
  | .failure => 0

private theorem nodup_ofFn_of_injective {n : Nat} {A : Type}
    (f : Fin n → A) (hf : Function.Injective f) :
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

/-- The two neighboring concave potentials lose exactly two in total. -/
theorem concave_neighbors (L q : Nat) (hq : 1 ≤ q) (hqL : q < L) :
    concave L (q - 1) + concave L (q + 1) + 2 =
      2 * concave L q := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hq
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hqL)
  subst q
  subst L
  have hsubOne : 1 + a + 1 + b - a = 2 + b := by omega
  have hsubTwo : 1 + a + 1 + b - (1 + a) = 1 + b := by omega
  have hsubThree : 1 + a + 1 + b - (1 + a + 1) = b := by omega
  simp only [concave, Nat.succ_eq_add_one]
  rw [show 1 + a - 1 = a by omega, hsubOne, hsubTwo, hsubThree]
  simp only [Nat.mul_add, Nat.add_mul]
  omega

/-- Proof-facing interface for a killed symmetric coordinate.  The transition
may terminate early, so the fields state domination by the nominal down/up
children rather than forcing an artificial surviving tag. -/
structure Spec (S : Type) (n L : Nat) where
  step : S → Fin n → StopNode S
  coord : S → Nat
  downEdge : S → Fin n
  upEdge : S → Fin n
  edge_count : 2 ≤ n
  coord_pos : ∀ s, 1 ≤ coord s
  coord_lt : ∀ s, coord s < L
  edges_ne : ∀ s, downEdge s ≠ upEdge s
  down_coord : ∀ s,
    endpointCoord coord L (step s (downEdge s)) ≤ coord s - 1
  up_coord : ∀ s,
    endpointCoord coord L (step s (upEdge s)) ≤ coord s + 1
  frame_coord : ∀ s e, e ≠ downEdge s → e ≠ upEdge s →
    endpointCoord coord L (step s e) ≤ coord s
  down_concave : ∀ s,
    endpointConcave coord L (step s (downEdge s)) ≤
      concave L (coord s - 1)
  up_concave : ∀ s,
    endpointConcave coord L (step s (upEdge s)) ≤
      concave L (coord s + 1)
  frame_concave : ∀ s e, e ≠ downEdge s → e ≠ upEdge s →
    endpointConcave coord L (step s e) ≤ concave L (coord s)

private theorem two_exception_sum_le {n : Nat}
    (a b : Fin n) (f : Fin n → Nat) (c da db : Nat)
    (hab : a ≠ b) (hda : f a ≤ da) (hdb : f b ≤ db)
    (hframe : ∀ e, e ≠ a → e ≠ b → f e ≤ c) :
    (List.ofFn f).sum ≤ da + db + (n - 2) * c := by
  let g : Fin n → Nat := fun e ↦ if e = a then da else if e = b then db else c
  have hfg : ∀ e, f e ≤ g e := by
    intro e
    by_cases hea : e = a
    · subst e
      simp [g, hda]
    · by_cases heb : e = b
      · subst e
        simp [g, hea, hdb]
      · simp [g, hea, heb, hframe e hea heb]
  refine Nat.le_trans (ofFn_sum_le f g hfg) ?_
  let xs := List.ofFn (fun e : Fin n ↦ e)
  have hsum := sum_two_exceptions xs a b g c
    (nodup_ofFn_of_injective (fun e : Fin n ↦ e) Function.injective_id)
    (List.mem_ofFn.mpr ⟨a, rfl⟩) (List.mem_ofFn.mpr ⟨b, rfl⟩) hab (by
      intro e he hea heb
      simp [g, hea, heb])
  have hmap : xs.map g = List.ofFn g := by
    simp [xs, List.map_ofFn, Function.comp_def]
  have hlen : xs.length = n := by simp [xs]
  rw [hmap] at hsum
  rw [hlen] at hsum
  exact Nat.le_of_eq (by simpa [g, hab, Ne.symm hab] using hsum)

/-- The endpoint coordinate is a one-step supermartingale. -/
theorem coord_child_sum_le {S : Type} {n L : Nat}
    (M : Spec S n L) (s : S) :
    (List.ofFn (fun e : Fin n ↦
      endpointCoord M.coord L (M.step s e))).sum ≤ n * M.coord s := by
  have hsum := two_exception_sum_le (M.downEdge s) (M.upEdge s)
    (fun e ↦ endpointCoord M.coord L (M.step s e)) (M.coord s)
    (M.coord s - 1) (M.coord s + 1) (M.edges_ne s)
    (M.down_coord s) (M.up_coord s) (M.frame_coord s)
  have hn2 := M.edge_count
  have hn : n = (n - 2) + 2 := by omega
  have hq := M.coord_pos s
  apply Nat.le_trans hsum
  rw [show M.coord s - 1 + (M.coord s + 1) = 2 * M.coord s by omega]
  calc
    2 * M.coord s + (n - 2) * M.coord s =
        ((n - 2) + 2) * M.coord s := by
          rw [Nat.add_mul]
          omega
    _ = n * M.coord s :=
      (congrArg (fun z ↦ z * M.coord s) hn).symm
    _ ≤ n * M.coord s := Nat.le_refl _

/-- The endpoint coordinate remains a supermartingale over every exact finite
scheduler tree. -/
theorem coord_treeWeight_le {S : Type} {n L : Nat}
    (M : Spec S n L) (s : S) (T : Nat) :
    treeWeight M.step (endpointCoord M.coord L) (.active s) T ≤
      n ^ T * M.coord s := by
  exact treeWeight_le_pow_mul_of_child_sum_le M.step
    (endpointCoord M.coord L) (coord_child_sum_le M) (.active s) T

/-- Every failed leaf contributes the upper endpoint `L`, giving the exact
finite-horizon gambler's-ruin failure-count certificate. -/
theorem failureCount_mul_L_le {S : Type} {n L : Nat}
    (M : Spec S n L) (s : S) (T : Nat) :
    L * failureCount M.step (.active s) T ≤ n ^ T * M.coord s := by
  have hpoint : ∀ x : StopNode S,
      L * FiniteUniformStoppingTree.failureWeight x ≤
        endpointCoord M.coord L x := by
    intro x
    cases x <;> simp [FiniteUniformStoppingTree.failureWeight, endpointCoord]
  have hmono := treeWeight_mono M.step
    (fun x ↦ L * FiniteUniformStoppingTree.failureWeight x)
    (endpointCoord M.coord L) hpoint (.active s) T
  rw [treeWeight_mul_left] at hmono
  exact Nat.le_trans hmono (coord_treeWeight_le M s T)

/-- Starting at the midpoint `L = 2*q`, at most half of all finite scheduler
words have already exited through the failure endpoint. -/
theorem failureCount_twice_le_of_midpoint {S : Type} {n L : Nat}
    (M : Spec S n L) (s : S) (hmid : L = 2 * M.coord s) (T : Nat) :
    2 * failureCount M.step (.active s) T ≤ n ^ T := by
  have hfail := failureCount_mul_L_le M s T
  have hscaled : M.coord s *
        (2 * failureCount M.step (.active s) T) ≤
      M.coord s * n ^ T := by
    calc
      M.coord s * (2 * failureCount M.step (.active s) T) =
          (2 * M.coord s) * failureCount M.step (.active s) T := by
            ac_rfl
      _ = L * failureCount M.step (.active s) T :=
        (congrArg (fun z ↦
          z * failureCount M.step (.active s) T) hmid).symm
      _ ≤ n ^ T * M.coord s := hfail
      _ = M.coord s * n ^ T := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hscaled (M.coord_pos s)

/-- The concave endpoint potential pays two units of one-step drift. -/
theorem concave_child_sum_add_two_le {S : Type} {n L : Nat}
    (M : Spec S n L) (s : S) :
    2 + (List.ofFn (fun e : Fin n ↦
      endpointConcave M.coord L (M.step s e))).sum ≤
        n * concave L (M.coord s) := by
  have hsum := two_exception_sum_le (M.downEdge s) (M.upEdge s)
    (fun e ↦ endpointConcave M.coord L (M.step s e))
    (concave L (M.coord s)) (concave L (M.coord s - 1))
    (concave L (M.coord s + 1)) (M.edges_ne s)
    (M.down_concave s) (M.up_concave s) (M.frame_concave s)
  have hneighbors := concave_neighbors L (M.coord s)
    (M.coord_pos s) (M.coord_lt s)
  have hn2 := M.edge_count
  have hn : n = (n - 2) + 2 := by omega
  apply Nat.le_trans (Nat.add_le_add_left hsum 2)
  calc
    2 + (concave L (M.coord s - 1) + concave L (M.coord s + 1) +
          (n - 2) * concave L (M.coord s)) =
        (concave L (M.coord s - 1) + concave L (M.coord s + 1) + 2) +
          (n - 2) * concave L (M.coord s) := by omega
    _ = 2 * concave L (M.coord s) +
          (n - 2) * concave L (M.coord s) := by rw [hneighbors]
    _ = ((n - 2) + 2) * concave L (M.coord s) := by
      rw [Nat.add_mul]
      omega
    _ = n * concave L (M.coord s) :=
      (congrArg (fun z ↦ z * concave L (M.coord s)) hn).symm
    _ ≤ n * concave L (M.coord s) := Nat.le_refl _

/-- Scheduler-scaled concave potential.  The unscaled coordinate loses two
over the sum of `n` children, so multiplying it by `n` pays two raw steps. -/
def scaledConcave {S : Type} (n : Nat) (coord : S → Nat) (L : Nat) :
    StopNode S → Nat := fun x ↦ n * endpointConcave coord L x

/-- The scheduler-scaled concave potential is a natural Bellman
supersolution at scale two. -/
theorem concave_natSuperSolution {S : Type} {n L : Nat}
    (M : Spec S n L) :
    NatBellmanSuperSolution M.step 2 (scaledConcave n M.coord L) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have h := Nat.mul_le_mul_left n (concave_child_sum_add_two_le M s)
  calc
    2 * n + (List.ofFn (fun e : Fin n ↦
        scaledConcave n M.coord L (M.step s e))).sum =
        n * (2 + (List.ofFn (fun e : Fin n ↦
          endpointConcave M.coord L (M.step s e))).sum) := by
            rw [show (List.ofFn (fun e : Fin n ↦
                scaledConcave n M.coord L (M.step s e))).sum =
              n * (List.ofFn (fun e : Fin n ↦
                endpointConcave M.coord L (M.step s e))).sum by
                  exact ofFn_sum_mul_left n _]
            simp [Nat.mul_add, Nat.mul_comm]
    _ ≤ n * (n * concave L (M.coord s)) := h
    _ = n * scaledConcave n M.coord L (.active s) := by
      rfl

/-- Exact finite-horizon stopped-duration bound with its leaf residual. -/
theorem duration_add_residual_le {S : Type} {n L : Nat}
    (M : Spec S n L) (s : S) (T : Nat) :
    2 * truncatedActiveCostNumerator M.step (.active s) T +
        treeWeight M.step (scaledConcave n M.coord L) (.active s) T ≤
      n ^ T * (n * concave L (M.coord s)) :=
  truncatedActiveCost_add_treeWeight_le_of_natSuperSolution
    M.step 2 (scaledConcave n M.coord L) (concave_natSuperSolution M)
    (.active s) T

/-- Cost-only finite-horizon corollary. -/
theorem duration_mul_two_le {S : Type} {n L : Nat}
    (M : Spec S n L) (s : S) (T : Nat) :
    2 * truncatedActiveCostNumerator M.step (.active s) T ≤
      n ^ T * (n * concave L (M.coord s)) :=
  truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    M.step 2 (scaledConcave n M.coord L) (concave_natSuperSolution M)
    (.active s) T

end SymmetricKilledWalkFiniteTree

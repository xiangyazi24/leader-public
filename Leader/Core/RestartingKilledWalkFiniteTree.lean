import Leader.Core.SymmetricKilledWalkFiniteTree

/-!
# A killed walk with free restart at the upper endpoint

This module packages the geometric-restart argument into one natural-valued
Bellman potential.  A child which would hit the upper endpoint may already be
replaced by a newly selected active trial state, provided its potential is no
larger than the formal upper-endpoint value.  Thus no infinite stopping-time
or supremum argument is needed.
-/

namespace RestartingKilledWalkFiniteTree

open FiniteUniformStoppingTree
open SymmetricKilledWalkFiniteTree

/-- The concave duration potential plus a linear account which pays for a
restart at the upper endpoint. -/
def restartPotential (n L R q : Nat) : Nat :=
  n * L * concave L q + 2 * q * R

/-- Endpoint potential used by the global, already-restarted process.  The
failure constructor is assigned zero because a concrete instantiation should
replace an upper-endpoint exit by its next active trial state. -/
def nodePotential {S : Type} (n L R : Nat) (coord : S → Nat) :
    StopNode S → Nat
  | .active s => restartPotential n L R (coord s)
  | .success => 0
  | .failure => 0

/-- Proof-facing interface for a symmetric coordinate whose upper exit is
immediately restarted.  The three domination fields are deliberately stated
at the potential level: the upper distinguished child may be a fresh state
with a smaller coordinate, where concavity alone is not monotone. -/
structure Spec (S : Type) (n L R : Nat) where
  step : S → Fin n → StopNode S
  coord : S → Nat
  downEdge : S → Fin n
  upEdge : S → Fin n
  edge_count : 2 ≤ n
  coord_pos : ∀ s, 1 ≤ coord s
  coord_lt : ∀ s, coord s < L
  edges_ne : ∀ s, downEdge s ≠ upEdge s
  down_potential : ∀ s,
    nodePotential n L R coord (step s (downEdge s)) ≤
      restartPotential n L R (coord s - 1)
  up_potential : ∀ s,
    nodePotential n L R coord (step s (upEdge s)) ≤
      restartPotential n L R (coord s + 1)
  frame_potential : ∀ s e, e ≠ downEdge s → e ≠ upEdge s →
    nodePotential n L R coord (step s e) ≤
      restartPotential n L R (coord s)

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
  rw [hmap, hlen] at hsum
  exact Nat.le_of_eq (by simpa [g, hab, Ne.symm hab] using hsum)

/-- The two symmetric ideal children decrease `restartPotential` by exactly
`2*n*L`; the linear restart account has zero second difference. -/
theorem restartPotential_neighbors (n L R q : Nat)
    (hq : 1 ≤ q) (hqL : q < L) :
    restartPotential n L R (q - 1) +
        restartPotential n L R (q + 1) + 2 * n * L =
      2 * restartPotential n L R q := by
  have hc := concave_neighbors L q hq hqL
  have hlinear : 2 * (q - 1) * R + 2 * (q + 1) * R =
      2 * (2 * q * R) := by
    calc
      2 * (q - 1) * R + 2 * (q + 1) * R =
          (2 * (q - 1) + 2 * (q + 1)) * R := by rw [Nat.add_mul]
      _ = (2 * (2 * q)) * R := by
        congr 1
        omega
      _ = 2 * (2 * q * R) := by ac_rfl
  simp only [restartPotential]
  calc
    n * L * concave L (q - 1) + 2 * (q - 1) * R +
          (n * L * concave L (q + 1) + 2 * (q + 1) * R) + 2 * n * L =
        n * L * (concave L (q - 1) + concave L (q + 1) + 2) +
          (2 * (q - 1) * R + 2 * (q + 1) * R) := by
            simp only [Nat.mul_add]
            ac_rfl
    _ = n * L * (2 * concave L q) + 2 * (2 * q * R) := by
      rw [hc, hlinear]
    _ = 2 * (n * L * concave L q + 2 * q * R) := by
      simp only [Nat.mul_add]
      ac_rfl

/-- The restart potential is a Bellman supersolution paying `2*L` per
interaction under an `n`-edge uniform scheduler. -/
theorem natSuperSolution {S : Type} {n L R : Nat}
    (M : Spec S n L R) :
    NatBellmanSuperSolution M.step (2 * L)
      (nodePotential n L R M.coord) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have hsum := two_exception_sum_le (M.downEdge s) (M.upEdge s)
    (fun e ↦ nodePotential n L R M.coord (M.step s e))
    (restartPotential n L R (M.coord s))
    (restartPotential n L R (M.coord s - 1))
    (restartPotential n L R (M.coord s + 1))
    (M.edges_ne s) (M.down_potential s) (M.up_potential s)
    (M.frame_potential s)
  have hneighbors := restartPotential_neighbors n L R (M.coord s)
    (M.coord_pos s) (M.coord_lt s)
  have hn2 := M.edge_count
  have hn : n = (n - 2) + 2 := by omega
  have hscale : (2 * L) * n = 2 * n * L := by ac_rfl
  calc
    (2 * L) * n +
        (List.ofFn (fun e ↦
          nodePotential n L R M.coord (M.step s e))).sum ≤
      (2 * L) * n +
        (restartPotential n L R (M.coord s - 1) +
          restartPotential n L R (M.coord s + 1) +
          (n - 2) * restartPotential n L R (M.coord s)) :=
            Nat.add_le_add_left hsum _
    _ =
      (restartPotential n L R (M.coord s - 1) +
          restartPotential n L R (M.coord s + 1) + 2 * n * L) +
        (n - 2) * restartPotential n L R (M.coord s) := by
          rw [hscale]
          omega
    _ = 2 * restartPotential n L R (M.coord s) +
        (n - 2) * restartPotential n L R (M.coord s) := by
          rw [hneighbors]
    _ = ((n - 2) + 2) * restartPotential n L R (M.coord s) := by
          rw [Nat.add_mul]
          omega
    _ = n * restartPotential n L R (M.coord s) := by
          exact congrArg (fun z ↦ z * restartPotential n L R (M.coord s)) hn.symm

/-- Exact finite-horizon cost bound, retaining the nonnegative leaf residual. -/
theorem duration_add_residual_le {S : Type} {n L R : Nat}
    (M : Spec S n L R) (s : S) (T : Nat) :
    (2 * L) * truncatedActiveCostNumerator M.step (.active s) T +
        treeWeight M.step (nodePotential n L R M.coord) (.active s) T ≤
      n ^ T * restartPotential n L R (M.coord s) :=
  truncatedActiveCost_add_treeWeight_le_of_natSuperSolution
    M.step (2 * L) (nodePotential n L R M.coord) (natSuperSolution M)
    (.active s) T

/-- Every coordinate in the lower half of `[0,2Q]` fits below the formal
upper-endpoint restart account with budget `R=n*Q²`. -/
theorem restartPotential_le_midpoint_budget (n Q q : Nat) (hq : q ≤ Q) :
    restartPotential n (2 * Q) (n * Q * Q) q ≤
      (2 * (2 * Q)) * (n * Q * Q) := by
  have hsub : 2 * Q - q = Q + (Q - q) := by omega
  have hqsub : q * (Q - q) ≤ Q * (Q - q) :=
    Nat.mul_le_mul_right (Q - q) hq
  have hconc : q * (2 * Q - q) ≤ Q * Q := by
    rw [hsub, Nat.mul_add]
    calc
      q * Q + q * (Q - q) ≤ q * Q + Q * (Q - q) :=
        Nat.add_le_add_left hqsub _
      _ = Q * Q := by
        have : q + (Q - q) = Q := by omega
        calc
          q * Q + Q * (Q - q) = Q * (q + (Q - q)) := by
            simp only [Nat.mul_add]
            ac_rfl
          _ = Q * Q := by rw [this]
  unfold restartPotential concave
  have hfirst := Nat.mul_le_mul_left (n * (2 * Q)) hconc
  have hsecond := Nat.mul_le_mul_left (2 * (n * Q * Q)) hq
  calc
    n * (2 * Q) * (q * (2 * Q - q)) + 2 * q * (n * Q * Q) ≤
        n * (2 * Q) * (Q * Q) + 2 * Q * (n * Q * Q) := by
          exact Nat.add_le_add hfirst (by
            simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsecond)
    _ = (2 * (2 * Q)) * (n * Q * Q) := by
      simp only [Nat.mul_assoc]
      have hdouble (a : Nat) : a * 2 + a * 2 = a * (2 * 2) := by omega
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        hdouble (n * Q * Q * Q)

/-- Uniform version of `midpoint_duration_le`: every restarted trial may begin
at any coordinate at most `Q`, while the common formal upper endpoint is
`2Q`. -/
theorem lowerHalf_duration_le {S : Type} {n L R : Nat}
    (M : Spec S n L R) (s : S) (T Q : Nat)
    (hQ : 0 < Q) (hcoord : M.coord s ≤ Q)
    (hL : L = 2 * Q) (hR : R = n * Q * Q) :
    truncatedActiveCostNumerator M.step (.active s) T ≤ n ^ T * R := by
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    M.step (2 * L) (nodePotential n L R M.coord) (natSuperSolution M)
    (.active s) T
  simp only [nodePotential] at hcost
  have hpot := restartPotential_le_midpoint_budget n Q (M.coord s) hcoord
  rw [← hL, ← hR] at hpot
  have hscaled : (2 * L) * truncatedActiveCostNumerator M.step (.active s) T ≤
      (2 * L) * (n ^ T * R) := by
    exact Nat.le_trans hcost (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.mul_le_mul_left (n ^ T) hpot)
  have hscale : 0 < 2 * L := by omega
  exact Nat.le_of_mul_le_mul_left hscaled hscale

/-- At a midpoint start, choosing `R=n*q²` makes the root potential exactly
`(2*L)*R`.  Cancelling this positive scale gives the global restarted cost
bound directly, without separately summing a geometric series. -/
theorem midpoint_duration_le {S : Type} {n L R : Nat}
    (M : Spec S n L R) (s : S) (T q : Nat)
    (hq : 0 < q) (hcoord : M.coord s = q)
    (hL : L = 2 * q) (hR : R = n * q * q) :
    truncatedActiveCostNumerator M.step (.active s) T ≤ n ^ T * R := by
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    M.step (2 * L) (nodePotential n L R M.coord) (natSuperSolution M)
    (.active s) T
  simp only [nodePotential] at hcost
  have hpot : restartPotential n L R (M.coord s) = (2 * L) * R := by
    subst L
    subst R
    rw [hcoord]
    have hsub : 2 * q - q = q := by omega
    simp only [restartPotential, concave, hsub]
    have hdouble (a : Nat) : a * 2 + a * 2 = a * (2 * 2) := by omega
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hdouble (n * q * q * q)
  rw [hpot] at hcost
  have hscale : 0 < 2 * L := by omega
  have hscaled : (2 * L) * truncatedActiveCostNumerator M.step (.active s) T ≤
      (2 * L) * (n ^ T * R) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcost
  exact Nat.le_of_mul_le_mul_left hscaled hscale

end RestartingKilledWalkFiniteTree

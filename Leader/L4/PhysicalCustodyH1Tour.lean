import Leader.L4.PhysicalCustodyH1IID
import Leader.L4.AllSizeComposition

namespace L4.PhysicalCustody.H1
open L4.AllSizeS1Geometry

/-- A forward-invariant predicate may be added to the target without
delaying the hit when present initially. -/
theorem iid_cost_invariant {X : Type} {n : Nat} (step : X → Fin n → X)
    (P R : X → Prop) (closed : ∀ x e,P x → P (step x e))
    (x : X) (H : P x) (t : Nat) :
    iidHitCost step (fun y => P y ∧ R y) t x=iidHitCost step R t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases A : R x
    · simp only [iidHitCost,if_pos A,if_pos (show P x ∧ R x from ⟨H,A⟩)]
    · have N : ¬ (P x ∧ R x) := fun B => A B.2
      simp only [iidHitCost,if_neg A,if_neg N]
      congr 1
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      exact ih (step x e) (closed x e H)

private theorem iid_cost_equiv {X : Type} {n : Nat} (step : X → Fin n → X)
    (P R : X → Prop) (eq : ∀ x,P x ↔ R x) (x : X) (t : Nat) :
    iidHitCost step P t x=iidHitCost step R t x := by
  have h : P=R := funext fun x => propext (eq x)
  rw [h]

def independentRank {n : Nat} (j : Nat) (x : State n) : Prop :=
  Authenticated x ∧ ∀ i : Fin n,i.val<j → ¬badBond x i

theorem independentRank_closed {n : Nat} (j : Nat) (x : State n) (e : Fin n)
    (sep : ∀ i : Fin n,i≠rightNeighbor i)
    (sepTwo : ∀ i : Fin n,i≠rightNeighbor (rightNeighbor i))
    (H : independentRank j x) : independentRank j (physicalStep x e) := by
  refine ⟨authenticated_next e sep sepTwo H.1,?_⟩
  intro i hi B
  exact H.2 i hi (bad_bond_no_creation x e i (incoming i) (incoming_spec i) sep H.1 B)

theorem independent_rank_succ {n : Nat} {j : Nat} (hj : j<n) (x : State n) :
    independentRank (j+1) x ↔ independentRank j x ∧ ¬badBond x ⟨j,hj⟩ := by
  constructor
  · intro H
    exact ⟨⟨H.1,fun i hi => H.2 i (by omega)⟩,H.2 ⟨j,hj⟩ (by change j < j+1; omega)⟩
  · intro H
    refine ⟨H.1.1,?_⟩
    intro i hi
    by_cases E : i.val=j
    · have K : i=(⟨j,hj⟩ : Fin n) := Fin.ext E
      rw [K]
      exact H.2
    · exact H.1.2 i (by omega)

/-- A serial tour over actual bonds gives the all-bond independence
mean, with every previously cleared bond retained under each mark. -/
theorem independence_tour_expected {n : Nat} (N : 5≤n) (x : State n)
    (sep : ∀ i : Fin n,i≠rightNeighbor i)
    (sepTwo : ∀ i : Fin n,i≠rightNeighbor (rightNeighbor i))
    (H : Authenticated x) (j : Nat) (J : j≤n) :
    IIDExpectedHittingTimeAtMost physicalStep (independentRank j) x (j*(n*6^9)) := by
  induction j with
  | zero =>
    intro t
    rw [iidHitCost_of_target _ _ x ⟨H,fun _ lt => (Nat.not_lt_zero _ lt).elim⟩]
    exact Nat.zero_le _
  | succ j ih =>
    rw [Nat.succ_mul]
    apply L4.AllSizeComposition.additive_stage physicalStep (independentRank j)
      (independentRank (j+1)) _ _ x (ih (by omega))
    intro y hy t
    have hj : j<n := by omega
    rw [iid_cost_equiv _ _ _ (independent_rank_succ hj)]
    rw [iid_cost_invariant _ _ _ (fun z e hz => independentRank_closed j z e sep sepTwo hz) y hy]
    exact ring_bad_bond_expected N ⟨j,hj⟩ y hy.1 t

#print axioms independence_tour_expected
end L4.PhysicalCustody.H1

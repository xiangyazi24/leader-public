import Init.Omega

namespace L4.ReportRadiusSpacing

universe u

/-- Iterate the next lower-layer header. The recurrence arguments do not
require any cyclic enumeration, bijection, or even finiteness. -/
def advance {X : Type u} (f : X → X) (q : X) : Nat → X
  | 0 => q
  | i+1 => f (advance f q i)

theorem advance_add {X : Type u} (f : X → X) (q : X) (i j : Nat) :
    advance f q (i+j)=advance f (advance f q i) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg f ih

/-- Semantic report equations on a fixed lower layer. Directional values
test the first positive hop, not the centre's own old selection bit. -/
structure Settled {X : Type u} (f : X → X) (k : Nat)
    (selected : X → Bool) (left right : X → Nat) : Prop where
  leftStep : ∀ i, left (f i)=if selected i then 0 else min k (left i+1)
  rightStep : ∀ i, right i=if selected (f i) then 0 else min k (right (f i)+1)
  selectedIff : ∀ i, selected i=true ↔ left i=k ∧ right i=k

variable {X : Type u} {f : X → X} {k : Nat} {sel : X → Bool} {l r : X → Nat}

private theorem left_lo (S : Settled f k sel l r) (q : X) :
    ∀ d, (∀ j<d, sel (advance f q j)=false) → min k d≤l (advance f q d) := by
  intro d
  induction d with
  | zero => intro _; omega
  | succ d ih =>
    intro N
    change min k (d+1)≤l (f (advance f q d))
    rw [S.leftStep, N d (by omega)]
    simp only [Bool.false_eq_true, if_false]
    have P := ih (fun j J => N j (by omega))
    omega

private theorem right_lo (S : Settled f k sel l r) :
    ∀ d (q : X), (∀ j, 0<j → j≤d → sel (advance f q j)=false) → min k d≤r q := by
  intro d
  induction d with
  | zero => intro q _; omega
  | succ d ih =>
    intro q N
    have B : sel (f q)=false := N 1 (by omega) (by omega)
    rw [S.rightStep, B]
    simp only [Bool.false_eq_true, if_false]
    have P := ih (f q) (fun j J H => by
      rw [← show advance f q 1=f q from rfl, ← advance_add]
      exact N (1+j) (by omega) (by omega))
    omega

private theorem left_hi (S : Settled f k sel l r) (q : X) (Q : sel q=true) :
    ∀ d, l (advance f q (d+1))≤d := by
  intro d
  induction d with
  | zero =>
    change l (f q)≤0
    rw [S.leftStep,Q]
    simp
  | succ d ih =>
    change l (f (advance f q (d+1)))≤d+1
    rw [S.leftStep]
    split <;> omega

private theorem positive_bounded_exists (S : Settled f k sel l r) (q : X) :
    ∃ j, 0<j ∧ j≤2*k+1 ∧ sel (advance f q j)=true := by
  classical
  apply Classical.byContradiction
  intro H
  have N (j : Nat) (J : 0<j) (K : j≤2*k+1) : sel (advance f q j)=false :=
    Bool.eq_false_iff.mpr (fun Z => H ⟨j,J,K,Z⟩)
  let c := advance f q (k+1)
  have L0 := left_lo S (advance f q 1) k (fun j J => by
    rw [← advance_add]
    exact N (1+j) (by omega) (by omega))
  rw [← advance_add, show 1+k=k+1 by omega] at L0
  change min k k≤l c at L0
  have R0 := right_lo S k c (fun j J T => by
    rw [show advance f c j=advance f q (k+1+j) from (advance_add f q (k+1) j).symm]
    exact N (k+1+j) (by omega) (by omega))
  have L1 : l c≤k := by
    change l (f (advance f q k))≤k
    rw [S.leftStep]
    split <;> omega
  have R1 : r c≤k := by rw [S.rightStep]; split <;> omega
  exact H ⟨k+1,by omega,by omega,(S.selectedIff c).mpr
    ⟨by simp only [Nat.min_self] at L0; omega, by simp only [Nat.min_self] at R0; omega⟩⟩

theorem selected_nonempty (S : Settled f k sel l r) (q : X) :
    ∃ i, sel i=true := by
  obtain ⟨j,_,_,H⟩ := positive_bounded_exists S q
  exact ⟨advance f q j,H⟩

private theorem least_positive {P : Nat → Prop} (b : Nat)
    (H : ∃ j, 0<j ∧ j≤b ∧ P j) :
    ∃ j, 0<j ∧ j≤b ∧ P j ∧ ∀ i, 0<i → i<j → ¬P i := by
  classical
  induction b with
  | zero => obtain ⟨_,_,_,_⟩ := H; omega
  | succ b ih =>
    by_cases T : ∃ j, 0<j ∧ j≤b ∧ P j
    · obtain ⟨j,J,U,V,W⟩ := ih T
      exact ⟨j,J,by omega,V,W⟩
    · obtain ⟨j,J,U,V⟩ := H
      have E : j=b+1 := by
        apply Classical.byContradiction
        intro O
        exact T ⟨j,J,by omega,V⟩
      subst j
      exact ⟨_,J,U,V,fun i I L R => T ⟨i,I,by omega,R⟩⟩

/-- Every selected root has its first subsequent selection between k+1
and 2k+1 successor hops, inclusive. -/
theorem next_selected_gap (S : Settled f k sel l r) (q : X) (Q : sel q=true) :
    ∃ d, k+1≤d ∧ d≤2*k+1 ∧ sel (advance f q d)=true ∧
      (∀ j, 0<j → j<d → sel (advance f q j)=false) := by
  obtain ⟨d,D,U,V,W⟩ := least_positive (P := fun j => sel (advance f q j)=true)
    _ (positive_bounded_exists S q)
  have H := left_hi S q Q (d-1)
  rw [show d-1+1=d by omega,(S.selectedIff _).mp V |>.1] at H
  exact ⟨d,by omega,U,V,fun j J T => Bool.eq_false_iff.mpr (W j J T)⟩

#print axioms advance_add
#print axioms selected_nonempty
#print axioms next_selected_gap
end L4.ReportRadiusSpacing

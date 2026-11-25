import Leader.L4.ReportClosePulseLoss

namespace L4.ReportClosePulsePositions
open AdviceBandRadiusBudget ReportLossArithmetic FourLossStickyClock ReportClosePulseLoss
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

variable {n : Nat}

def candidates (g B D : Nat) : List (Fin g×Fin g×Fin B×Fin (D+1)) :=
  (List.finRange g).flatMap fun i=>
    (List.finRange g).flatMap fun j=>
      (List.finRange B).flatMap fun p=>
        (List.finRange (D+1)).map fun d=>(i,j,p,d)

private theorem flat_const_len {X Y : Type} (xs : List X) (f : X→List Y) (k : Nat)
    (L : ∀ x,(f x).length=k) : (xs.flatMap f).length=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs IH =>
    simp only [List.flatMap_cons,List.length_append,L,IH,List.length_cons,Nat.add_mul,Nat.one_mul]
    ac_rfl

theorem candidates_length (g B D : Nat) :
    (candidates g B D).length=g*g*B*(D+1) := by
  unfold candidates
  rw [flat_const_len _ _ (g*(B*(D+1)))]
  · simp only [List.length_finRange]
    ac_rfl
  · intro i
    rw [flat_const_len _ _ (B*(D+1))]
    · rw [List.length_finRange]
    · intro j
      rw [flat_const_len _ _ (D+1)]
      · rw [List.length_finRange]
      · intro p
        simp

theorem candidates_complete {g B D : Nat} (i j : Fin g) (p : Fin B) (d : Fin (D+1)) :
    (i,j,p,d)∈candidates g B D := by
  unfold candidates
  apply List.mem_flatMap.mpr
  refine ⟨i,by simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨j,by simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨p,by simp,?_⟩
  apply List.mem_map.mpr
  exact ⟨d,by simp,rfl⟩

/-- Number of ordered gate pairs, first marks, and nonnegative close
offsets. The mark equality itself is excluded from the per-key event. -/
private theorem close_key_numeric (g H U a : Nat) (N : 0<n) (G : g≤9*H) :
    g*g*(n*U)*(3*n*a+1)≤(600*H^2*(U+1)*(a+1))*n^2 := by
  have P : g*g≤(9*H)*(9*H) := Nat.mul_le_mul G G
  have X : 3*n*a+1≤n*(3*(a+1)) := by
    have E : 3*n*a=n*(3*a) := by ac_rfl
    rw [E,Nat.mul_add,Nat.mul_add,Nat.mul_one]
    omega
  have C : 81*(3*(a+1))≤600*(a+1) := by
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by decide)
  calc
    _ ≤ (9*H)*(9*H)*(n*U)*(n*(3*(a+1))) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ P) X
    _ = ((9*9)*(3*(a+1)))*(H^2*U*n^2) := by simp only [Nat.pow_two]; ac_rfl
    _ = (81*(3*(a+1)))*(H^2*U*n^2) := rfl
    _ ≤ (600*(a+1))*(H^2*(U+1)*n^2) :=
      Nat.mul_le_mul C (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    _ = (600*H^2*(U+1)*(a+1))*n^2 := by ac_rfl

theorem close_key_census (rho g : Nat) (N : 0<n)
    (G : g≤9*trialH rho) :
    (candidates g (n*trialU rho) (3*n*hSize rho)).length≤
      (600*(trialH rho)^2*(trialU rho+1)*(hSize rho+1))*n^2 := by
  rw [candidates_length]
  exact close_key_numeric g _ _ _ N G

/-- Union over the actual ordered close-event family. The per-pin
certificate supplies the single-pair count, not a marginal hazard. -/
theorem deployed_close_count (rho g : Nat) (N : 0<n) (G : g≤9*trialH rho)
    (L : 2≤n*trialU rho)
    (fixed : (Fin g×Fin g×Fin (n*trialU rho)×Fin (3*n*hSize rho+1))→
      List (Fin n)→Prop) (loss : List (Fin n)→Prop)
    (implies_key : ∀ w,loss w→∃ key,fixed key w)
    (per : ∀ key,2^(2*trialJ rho)*badCount (fixed key) (n*trialU rho)≤
      n^(n*trialU rho-2)) :
    8*badCount loss (n*trialU rho)≤n^(n*trialU rho) := by
  let keys := candidates g (n*trialU rho) (3*n*hSize rho)
  apply close_from_two_pin_counts rho _ keys.length L (close_key_census rho g N G)
    (fun i=>fixed keys[i.val]) loss
  · intro w W
    obtain ⟨⟨i,j,p,d⟩,E⟩ := implies_key w W
    have H : (i,j,p,d)∈keys := candidates_complete i j p d
    obtain ⟨k,K,Eq⟩ := List.mem_iff_getElem.mp H
    exact ⟨⟨k,K⟩,Eq.symm ▸ E⟩
  · intro _; exact per _

end L4.ReportClosePulsePositions

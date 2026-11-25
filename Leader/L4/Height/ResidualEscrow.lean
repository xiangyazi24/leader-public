import Leader.L4.Height.Window

namespace L4.Height.ResidualEscrow

open Classical

/-- Natural ceiling of a normalized, twice-scaled censored hitting cost. -/
noncomputable def rounded {S : Type} {n : Nat}
    (next : S→Fin n→S) (target : S→Prop) (y : S) (t : Nat) : Nat :=
  (2*iidHitCost next target t y+(n^t-1))/n^t

private theorem rounded_le {S : Type} {n : Nat} (hn : 0<n)
    (next : S→Fin n→S) (target : S→Prop) (y : S) (t v : Nat) :
    rounded next target y t≤v ↔ 2*iidHitCost next target t y≤n^t*v := by
  unfold rounded
  rw [Nat.div_le_iff_le_mul_add_pred (Nat.pow_pos hn)]
  omega

private theorem rounded_cap {S : Type} {n : Nat}
    (next : S→Fin n→S) (target : S→Prop) (y : S) (t : Nat) :
    n^t*rounded next target y t≤2*iidHitCost next target t y+(n^t-1) := by
  unfold rounded
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

private theorem cost_monotone_step {S : Type} {n : Nat}
    (next : S→Fin n→S) (target : S→Prop) :
    ∀ t y, n*iidHitCost next target t y≤iidHitCost next target (t+1) y := by
  intro t
  induction t with
  | zero => intro y; simp [iidHitCost]
  | succ t ih =>
    intro y
    by_cases h : target y
    · rw [iidHitCost_of_target next target y h, iidHitCost_of_target next target y h]
      simp
    · simp only [iidHitCost,if_neg h,Nat.mul_add,←sum_ofFn_mul_left]
      rw [←Nat.pow_succ']
      exact Nat.add_le_add_left (sum_ofFn_le _ _ (fun e=>ih (next y e))) _

private theorem rounded_mono {S : Type} {n : Nat} (hn : 0<n)
    (next : S→Fin n→S) (target : S→Prop) (y : S) {a b : Nat} (h : a≤b) :
    rounded next target y a≤rounded next target y b := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step b _ ind =>
    apply Nat.le_trans ind
    apply (rounded_le hn next target y b _).mpr
    have gain := Nat.mul_le_mul_left 2 (cost_monotone_step next target b y)
    have cap := (rounded_le hn next target y (b+1) _).mp (Nat.le_refl _)
    rw [Nat.pow_succ'] at cap
    have H := Nat.le_trans gain cap
    apply Nat.le_of_mul_le_mul_left (c:=n) _ hn
    calc
      n*(2*iidHitCost next target b y) = 2*(n*iidHitCost next target b y) := by ac_rfl
      _ ≤ (n*n^b)*rounded next target y (b+1) := H
      _ = n*(n^b*rounded next target y (b+1)) := by ac_rfl

private theorem bounded_max (f : Nat→Nat) (B : Nat) (cap : ∀ t,f t≤B) :
    ∃ k,∀ t,f t≤f k := by
  induction B with
  | zero =>
    refine ⟨0,fun t=>?_⟩
    have H := cap t
    omega
  | succ B ih =>
    by_cases E : ∃ t,f t=B+1
    · obtain ⟨t,E⟩ := E
      exact ⟨t,fun u=>E.symm ▸ cap u⟩
    · exact ih (fun t=>Nat.le_of_lt_succ (Nat.lt_of_le_of_ne (cap t) (fun e=>E ⟨t,e⟩)))

/-- A uniform bound on all finite censored costs produces a stationary
natural Bellman escrow. Successors are aligned only on one finite common
horizon for a fixed parent, not by any globally uniform convergence. -/
theorem exists_escrow {S : Type} {n : Nat} (hn : 0<n)
    (next : S→Fin n→S) (Q target : S→Prop) (F : Nat)
    (closed : ∀ y e,Q y→Q (next y e))
    (bound : ∀ y,Q y→IIDExpectedHittingTimeAtMost next target y F) :
    ∃ E : S→Nat,
      (∀ y,E y≤2*F) ∧
      (∀ y,target y→E y=0) ∧
      (∀ y,Q y→¬target y→
        n+(List.ofFn (fun e : Fin n=>E (next y e))).sum≤n*E y) := by
  let u := rounded next target
  have ub (y : S) (h : Q y) (t : Nat) : u y t≤2*F := by
    apply (rounded_le hn next target y t _).mpr
    have H := Nat.mul_le_mul_left 2 (bound y h t)
    exact Nat.le_trans H (Nat.le_of_eq (by ac_rfl))
  let best (y : S) (h : Q y) := Classical.choose (bounded_max (u y) (2*F) (ub y h))
  let E (y : S) := if h : Q y then u y (best y h) else 0
  have upper (y : S) (h : Q y) (t : Nat) : u y t≤E y := by
    unfold E
    rw [dif_pos h]
    exact Classical.choose_spec (bounded_max (u y) (2*F) (ub y h)) t
  have attained (y : S) (h : Q y) {t : Nat} (le : best y h≤t) : E y=u y t := by
    apply Nat.le_antisymm _ (upper y h t)
    unfold E
    rw [dif_pos h]
    exact rounded_mono hn next target y le
  refine ⟨E,?_,?_,?_⟩
  · intro y
    unfold E
    split
    · exact ub _ ‹Q y› _
    · omega
  · intro y hit
    unfold E
    split
    · unfold u rounded
      rw [iidHitCost_of_target next target y hit,Nat.mul_zero,Nat.zero_add]
      exact Nat.div_eq_of_lt (by have := Nat.pow_pos (n:=best y ‹Q y›) hn; omega)
    · rfl
  · intro y q alive
    let times := fun e : Fin n=>best (next y e) (closed y e q)
    let H := (List.ofFn times).max?.getD 0
    let d := n^H
    have dpos : 0<d := Nat.pow_pos hn
    let A : Fin n→Nat := fun e=>iidHitCost next target H (next y e)
    let V : Fin n→Nat := fun e=>E (next y e)
    have link : (List.ofFn (fun e=>d*V e)).sum≤
        (List.ofFn (fun e=>2*A e+(d-1))).sum := by
      apply sum_ofFn_le
      intro e
      have h : times e≤H := List.le_max?_getD_of_mem (by
        rw [List.mem_ofFn]; exact ⟨e,rfl⟩)
      change best (next y e) (closed y e q)≤H at h
      have ee : V e=u (next y e) H := attained _ (closed y e q) h
      rw [ee]
      exact rounded_cap next target (next y e) H
    rw [sum_ofFn_mul_left,sum_ofFn_add,sum_ofFn_mul_left,sum_ofFn_const] at link
    have circ : 2*(n*d+(List.ofFn A).sum)≤n*d*E y := by
      have h := (rounded_le hn next target y (H+1) _).mp (upper y q (H+1))
      simpa only [iidHitCost,if_neg alive,Nat.pow_succ',d,A] using h
    have slack : n*(d-1)≤n*d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have product : d*(n+(List.ofFn V).sum)≤d*(n*E y) := by
      rw [Nat.mul_add,Nat.mul_comm d n,←Nat.mul_assoc]
      rw [Nat.mul_comm d n]
      omega
    exact Nat.le_of_mul_le_mul_left product dpos

end L4.Height.ResidualEscrow

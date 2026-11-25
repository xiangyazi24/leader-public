import Leader.L4.WidthChooseEpoch
import Leader.Core.LeaderCountDyadicTail

namespace L4.WidthCycleEpoch
open FiniteUniformStoppingTree

namespace AbsorbingMax
open LeaderCountDyadicTail

variable {X : Type} {n m : Nat}

noncomputable def miss (Q : X→Prop) (x : X) : Nat := by
  classical
  exact if Q x then 0 else 1

theorem miss_le_one (Q : X→Prop) (x : X) : miss Q x≤1 := by
  classical
  by_cases H : Q x <;> simp [miss,H]

theorem miss_mono (step : X→Fin n→X) (Q : X→Prop)
    (closed : ∀ x e,Q x→Q (step x e)) (x : X) (e : Fin n) :
    miss Q (step x e)≤miss Q x := by
  classical
  by_cases H : Q x
  · simp [miss,H,closed x e H]
  · simpa [miss,H] using miss_le_one Q (step x e)

/-- For an absorbing Q the one-step cost recursion also holds
    inside Q, because all children are then already stopped. -/
theorem cost_rec (step : X→Fin n→X) (Q : X→Prop)
    (closed : ∀ x e,Q x→Q (step x e)) (t : Nat) (x : X) :
    L4.iidHitCost step Q (t+1) x =
      n^(t+1)*miss Q x+
        (List.ofFn (fun e : Fin n=>L4.iidHitCost step Q t (step x e))).sum := by
  classical
  by_cases H : Q x
  · have C (e : Fin n) : L4.iidHitCost step Q t (step x e)=0 :=
      L4.iidHitCost_of_target step Q (step x e) (closed x e H) t
    rw [L4.iidHitCost_of_target step Q x H,
      ofFn_sum_eq _ (fun _=>0) C,ofFn_sum_const]
    simp [miss,H]
  · simp [L4.iidHitCost,H,miss]

theorem markov_cost (step : X→Fin n→X) (Q : X→Prop)
    (closed : ∀ x e,Q x→Q (step x e)) (t : Nat) (x : X) :
    t*wordSum step (miss Q) x t≤L4.iidHitCost step Q t x := by
  induction t generalizing x with
  | zero => simp [L4.iidHitCost]
  | succ t ih =>
    have B := wordSum_le_initial step (miss Q)
      (miss_mono step Q closed) x (t+1)
    have S := ofFn_sum_le
      (fun e : Fin n=>t*wordSum step (miss Q) (step x e) t)
      (fun e=>L4.iidHitCost step Q t (step x e)) (fun e=>ih (step x e))
    rw [ofFn_sum_mul_left] at S
    rw [cost_rec step Q closed, Nat.succ_mul]
    rw [wordSum_succ] at B ⊢
    omega

theorem half_block (step : X→Fin n→X) (Q : X→Prop)
    (closed : ∀ x e,Q x→Q (step x e)) (mu : Nat) (pos : 0<mu)
    (x : X) (H : L4.IIDExpectedHittingTimeAtMost step Q x mu) :
    2*wordSum step (miss Q) x (2*mu)≤n^(2*mu)*miss Q x := by
  classical
  by_cases Qx : Q x
  · have U := wordSum_le_initial step (miss Q)
      (miss_mono step Q closed) x (2*mu)
    simp [miss,Qx] at U ⊢
    omega
  · have B := markov_cost step Q closed (2*mu) x
    have V : mu*(2*wordSum step (miss Q) x (2*mu))≤mu*n^(2*mu) := by
      calc
        _ = (2*mu)*wordSum step (miss Q) x (2*mu) := by ac_rfl
        _ ≤ _ := Nat.le_trans B (H (2*mu))
    -- CHECK: Nat.le_of_mul_le_mul_left (Nat version, positive factor).
    have U := Nat.le_of_mul_le_mul_left V pos
    simpa [miss,Qx] using U

/-- Uniformity over the closed domain is needed for every block,
    not only at the distinguished starting raw configuration. -/
theorem owner_tail (step : X→Fin n→X) (D Q : X→Prop)
    (closeD : ∀ x e,D x→D (step x e))
    (closeQ : ∀ x e,Q x→Q (step x e))
    (mu : Nat) (pos : 0<mu)
    (H : ∀ x,D x→L4.IIDExpectedHittingTimeAtMost step Q x mu)
    (k : Nat) (x : X) (A : D x) :
    2^k*wordSum step (miss Q) x (k*(2*mu))≤n^(k*(2*mu)) := by
  -- CHECK: Leader/Core/LeaderCountDyadicTail.lean:270-299.
  have V := iterate_contraction step D closeD (miss Q) (2*mu) 2 1
    (fun y Y=>by
      simpa only [Nat.one_mul] using half_block step Q closeQ mu pos y (H y Y))
    k x A
  calc
    _ ≤ (1*n^(2*mu))^k*miss Q x := V
    _ ≤ (1*n^(2*mu))^k*1 := Nat.mul_le_mul_left _ (miss_le_one Q x)
    _ = _ := by simp only [Nat.one_mul,Nat.mul_one,←Nat.pow_mul]; rw [Nat.mul_comm (2*mu) k]

private theorem sum_at_le {m : Nat} (f : Fin m→Nat) (i : Fin m) :
    f i≤(List.ofFn f).sum := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ,List.sum_cons]
    refine Fin.cases ?_ (fun j=>?_) i
    · omega
    · have H := ih (fun j=>f j.succ) j
      omega

private theorem sum_swap {m n : Nat} (f : Fin m→Fin n→Nat) :
    (List.ofFn (fun i : Fin m=>(List.ofFn (f i)).sum)).sum =
      (List.ofFn (fun e : Fin n=>(List.ofFn (fun i : Fin m=>f i e)).sum)).sum := by
  induction m with
  | zero => simp [ofFn_sum_const]
  | succ m ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    rw [ofFn_sum_add,ih (fun i=>f i.succ)]

noncomputable def count (G : Fin m→X→Prop) (x : X) : Nat :=
  (List.ofFn (fun i=>miss (G i) x)).sum

def All (G : Fin m→X→Prop) (x : X) : Prop := ∀ i,G i x

theorem all_closed (step : X→Fin n→X) (G : Fin m→X→Prop)
    (C : ∀ i x e,G i x→G i (step x e)) :
    ∀ x e,All G x→All G (step x e) := by
  intro x e H i
  exact C i x e (H i)

theorem miss_all_le (G : Fin m→X→Prop) (x : X) :
    miss (All G) x≤count G x := by
  classical
  by_cases H : All G x
  · simp [miss,H]
  · have N : ¬∀ i,G i x := H
    obtain ⟨i,I⟩ := Classical.not_forall.mp N
    have V := sum_at_le (fun j=>miss (G j) x) i
    change miss (G i) x≤count G x at V
    simpa [miss,H,I] using V

/-- Cost of the simultaneous intersection is at most the sum
    of individual costs, used only for the residual after cutoff. -/
theorem cost_all_le (step : X→Fin n→X) (G : Fin m→X→Prop)
    (C : ∀ i x e,G i x→G i (step x e)) (t : Nat) (x : X) :
    L4.iidHitCost step (All G) t x≤
      (List.ofFn (fun i=>L4.iidHitCost step (G i) t x)).sum := by
  induction t generalizing x with
  | zero => simp [L4.iidHitCost,ofFn_sum_const]
  | succ t ih =>
    rw [cost_rec step (All G) (all_closed step G C)]
    have E :
        (List.ofFn (fun i=>L4.iidHitCost step (G i) (t+1) x)).sum =
          n^(t+1)*count G x+
            (List.ofFn (fun e : Fin n=>
              (List.ofFn (fun i=>L4.iidHitCost step (G i) t (step x e))).sum)).sum := by
      rw [ofFn_sum_eq _ _ (fun i=>cost_rec step (G i) (C i) t x),
        ofFn_sum_add,ofFn_sum_mul_left]
      rw [sum_swap (fun i e=>L4.iidHitCost step (G i) t (step x e))]
      rfl
    rw [E]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (miss_all_le G x))
      (ofFn_sum_le _ _ (fun e=>ih (step x e)))

private theorem wordSum_sum (step : X→Fin n→X) (v : Fin m→X→Nat)
    (x : X) (t : Nat) :
    wordSum step (fun y=>(List.ofFn (fun i=>v i y)).sum) x t =
      (List.ofFn (fun i=>wordSum step (v i) x t)).sum := by
  induction m with
  | zero =>
    simp only [List.ofFn_zero,List.sum_nil]
    rw [wordSum_const]
    simp
  | succ m ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    rw [wordSum_add,ih (fun i=>v i.succ)]

theorem cutoff_count (step : X→Fin n→X) (D : X→Prop)
    (closeD : ∀ x e,D x→D (step x e))
    (G : Fin m→X→Prop) (C : ∀ i x e,G i x→G i (step x e))
    (mu : Nat) (pos : 0<mu)
    (H : ∀ i x,D x→L4.IIDExpectedHittingTimeAtMost step (G i) x mu)
    (k : Nat) (card : m≤2^k) (x : X) (A : D x) :
    wordSum step (count G) x (k*(2*mu))≤n^(k*(2*mu)) := by
  let T := k*(2*mu)
  have E := ofFn_sum_le
    (fun i : Fin m=>2^k*wordSum step (miss (G i)) x T)
    (fun _=>n^T)
    (fun i=>owner_tail step D (G i) closeD (C i) mu pos (H i) k x A)
  rw [ofFn_sum_mul_left,ofFn_sum_const] at E
  have V : wordSum step (count G) x T=
      (List.ofFn (fun i=>wordSum step (miss (G i)) x T)).sum :=
    wordSum_sum step (fun i=>miss (G i)) x T
  rw [←V] at E
  have U := Nat.le_trans E (Nat.mul_le_mul_right (n^T) card)
  exact Nat.le_of_mul_le_mul_left U (Nat.pow_pos (by decide : 0<2))

/-- Split at a deterministic physical prefix, not a compressed
    watched schedule. Already paid histories only reduce cost. -/
theorem cost_cutoff (step : X→Fin n→X) (Q : X→Prop)
    (closed : ∀ x e,Q x→Q (step x e)) (k t : Nat) (x : X) :
    L4.iidHitCost step Q (k+t) x≤
      k*n^(k+t)+wordSum step (fun y=>L4.iidHitCost step Q t y) x k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_add,cost_rec step Q closed,wordSum_succ]
    have E := ofFn_sum_le
      (fun e : Fin n=>L4.iidHitCost step Q (k+t) (step x e))
      (fun e=>k*n^(k+t)+wordSum step (fun y=>L4.iidHitCost step Q t y)
        (step x e) k) (fun e=>ih (step x e))
    rw [ofFn_sum_add,ofFn_sum_const] at E
    have K : n*(k*n^(k+t))=k*n^(k+t+1) := by rw [Nat.pow_succ]; ac_rfl
    rw [K] at E
    have M : n^(k+t+1)*miss Q x≤n^(k+t+1) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n^(k+t+1)) (miss_le_one Q x)
    rw [Nat.succ_mul]
    simp only [Nat.succ_eq_add_one] at *
    omega

theorem horizon (step : X→Fin n→X) (Q : X→Prop)
    (closed : ∀ x e,Q x→Q (step x e)) (t : Nat) (x : X) :
    L4.iidHitCost step Q t x≤t*n^t := by
  have E := cost_cutoff step Q closed t 0 x
  simpa [L4.iidHitCost,wordSum_const] using E

theorem residual_cost (step : X→Fin n→X) (G : Fin m→X→Prop)
    (C : ∀ i x e,G i x→G i (step x e)) (mu t : Nat) (x : X)
    (H : ∀ i,L4.IIDExpectedHittingTimeAtMost step (G i) x mu) :
    L4.iidHitCost step (All G) t x≤(mu*n^t)*count G x := by
  classical
  apply Nat.le_trans (cost_all_le step G C t x)
  have U := ofFn_sum_le
    (fun i=>L4.iidHitCost step (G i) t x)
    (fun i=>(mu*n^t)*miss (G i) x) (fun i=>by
      by_cases I : G i x
      · rw [L4.iidHitCost_of_target step (G i) x I]
        exact Nat.zero_le _
      · simpa [miss,I] using H i t)
  rw [ofFn_sum_mul_left] at U
  exact U

/-- One original-tape maximum. This is conditional on uniform individual
    MEANS and absorption, with no independence between owner events. -/
theorem expected (step : X→Fin n→X) (D : X→Prop)
    (closeD : ∀ x e,D x→D (step x e))
    (G : Fin m→X→Prop) (C : ∀ i x e,G i x→G i (step x e))
    (mu : Nat) (pos : 0<mu)
    (H : ∀ i x,D x→L4.IIDExpectedHittingTimeAtMost step (G i) x mu)
    (k : Nat) (card : m≤2^k) (x : X) (A : D x) :
    L4.IIDExpectedHittingTimeAtMost step (All G) x ((2*mu)*(k+2)) := by
  let T := k*(2*mu)
  have CAll := all_closed step G C
  have U : T+mu≤(2*mu)*(k+2) := by
    dsimp only [T]
    rw [Nat.mul_add,Nat.mul_comm k (2*mu)]
    omega
  intro t
  by_cases E : T≤t
  · obtain ⟨u,R⟩ := Nat.exists_eq_add_of_le E
    subst t
    have M := cutoff_count step D closeD G C mu pos H k card x A
    have B := cost_cutoff step (All G) CAll T u x
    have V := wordSum_mono_on step D closeD
      (fun y=>L4.iidHitCost step (All G) u y)
      (fun y=>(mu*n^u)*count G y)
      (fun y Y=>residual_cost step G C mu u y (fun i=>H i y Y)) T x A
    rw [wordSum_mul] at V
    have W : wordSum step (fun y=>L4.iidHitCost step (All G) u y) x T
        ≤mu*n^(T+u) := by
      calc
        _ ≤ (mu*n^u)*wordSum step (count G) x T := V
        _ ≤ (mu*n^u)*n^T := Nat.mul_le_mul_left _ M
        _ = _ := by rw [Nat.pow_add]; ac_rfl
    calc
      _ ≤ T*n^(T+u)+mu*n^(T+u) := Nat.le_trans B (Nat.add_le_add_left W _)
      _ = (T+mu)*n^(T+u) := (Nat.add_mul _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ U
  · have W : t≤(2*mu)*(k+2) := by omega
    exact Nat.le_trans (horizon step (All G) CAll t x) (Nat.mul_le_mul_right _ W)

end AbsorbingMax

#print axioms AbsorbingMax.markov_cost
#print axioms AbsorbingMax.cutoff_count
#print axioms AbsorbingMax.expected
end L4.WidthCycleEpoch

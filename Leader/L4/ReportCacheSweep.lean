import Leader.L4.ReportCacheAllSites
import Leader.L4.ShortResetChart

namespace L4.ReportCacheSweep
open AllSizeProtocol BStarH6Ordinal Height ReportCacheWindow ReportCacheAllSites
open ShortResetChart PhysicalCustody

variable {X : Type} {n cap : Nat} {h : Fin n → Bool}
  {step : X → Fin n → X} {Q : X → Prop} {off : X → Fin n → Nat} {succ : X → Fin n → Bool}

def CorrectOffset (h : Fin n → Bool) (hh : ∃ i,h i=true) (cap : Nat)
    (off : X → Fin n → Nat) (x : X) (i : Fin n) : Prop :=
  off x i=min cap (ordinal h hh i)

private theorem install (hh : ∃ i,h i=true) (F : Frame step Q h cap off succ)
    (x : X) (e : Fin n) (A : Q x)
    (P : h (rightNeighbor e)=true ∨ CorrectOffset h hh cap off x e) :
    CorrectOffset h hh cap off (step x e) (rightNeighbor e) := by
  unfold CorrectOffset at *
  rw [F.respond x e A,ordinal_right]
  by_cases R : h (rightNeighbor e)=true
  · simp [R]
  · rw [if_neg R,if_neg R]
    obtain P|P := P
    · contradiction
    · rw [P]
      by_cases E : h e=true
      · simp [E,(ordinal_zero h hh e).mpr E]
      · simp only [if_neg E]
        omega

private theorem target_of_fields (hh : ∃ i,h i=true)
    (x : X) (A : Q x) (O : ∀ i, CorrectOffset h hh cap off x i)
    (S : ∀ i, succ x i=h (rightNeighbor i)) :
    AllCorrect Q h hh cap off succ x := by
  have prec (k : Nat) (K : k≤cap) (i : Fin n) : Precision h hh off x k i := by
    induction k generalizing i with
    | zero => trivial
    | succ k ih =>
      refine ⟨?_,ih (by omega) _⟩
      have E := O i
      unfold CorrectOffset at E
      rw [E]
      omega
  exact ⟨A,fun i=>⟨A,prec cap (Nat.le_refl _) i,(O i) ▸ Nat.min_le_left _ _,S i⟩⟩

def Sweep (Q : X → Prop) (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (cap : Nat) (off : X → Fin n → Nat) (succ : X → Fin n → Bool)
    (r : Fin n) (k : Nat) (x : X) : Prop :=
  Q x ∧ (∀ j≤k, CorrectOffset h hh cap off x (nextAt r j)) ∧
    ∀ j<k, succ x (nextAt r j)=h (rightNeighbor (nextAt r j))

private theorem sweep_closed (hh : ∃ i,h i=true) (F : Frame step Q h cap off succ)
    (r : Fin n) (R : h r=true) (k : Nat) (x : X) (e : Fin n)
    (A : Sweep Q h hh cap off succ r k x) :
    Sweep Q h hh cap off succ r k (step x e) := by
  refine ⟨F.closed x e A.1,?_,?_⟩
  · intro j J
    by_cases E : nextAt r j=rightNeighbor e
    · rw [E]
      apply install hh F x e A.1
      cases j with
      | zero =>
        exact Or.inl (E ▸ R)
      | succ j =>
        have I := congrArg RearTrace.predecessor E
        change RearTrace.predecessor (rightNeighbor (nextAt r j)) = RearTrace.predecessor (rightNeighbor e) at I
        rw [RearTrace.predecessor_right,RearTrace.predecessor_right] at I
        exact Or.inr (I ▸ A.2.1 j (by omega))
    · unfold CorrectOffset
      rw [F.hold x e _ A.1 E]
      exact A.2.1 j J
  · intro j J
    by_cases E : nextAt r j=e
    · rw [E]
      exact F.writeSucc x e A.1
    · rw [F.holdSucc x e _ A.1 E]
      exact A.2.2 j J

private theorem sweep_pay (hh : ∃ i,h i=true) (F : Frame step Q h cap off succ)
    (r : Fin n) (R : h r=true) (k : Nat) (x : X)
    (A : Sweep Q h hh cap off succ r k x) :
    Sweep Q h hh cap off succ r (k+1) (step x (nextAt r k)) := by
  have B := sweep_closed hh F r R k x (nextAt r k) A
  refine ⟨B.1,?_,?_⟩
  · intro j J
    by_cases E : j≤k
    · exact B.2.1 j E
    · have S : j=k+1 := by omega
      subst j
      exact install hh F x _ A.1 (Or.inr (A.2.1 k (Nat.le_refl _)))
  · intro j J
    by_cases E : j<k
    · exact B.2.2 j E
    · have S : j=k := by omega
      subst j
      exact F.writeSucc x _ A.1

private theorem seed (hh : ∃ i,h i=true) (F : Frame step Q h cap off succ)
    (r : Fin n) (R : h r=true) (x : X) (A : Q x) :
    Sweep Q h hh cap off succ r 0 (step x (RearTrace.predecessor r)) := by
  refine ⟨F.closed x _ A,?_,fun _ I=>False.elim (Nat.not_lt_zero _ I)⟩
  intro j J
  have J0 : j=0 := by omega
  subst j
  change CorrectOffset h hh cap off (step x (RearTrace.predecessor r)) r
  have E := RearTrace.right_predecessor r
  have R' : h (rightNeighbor (RearTrace.predecessor r))=true := by rwa [E]
  have T := install hh F x (RearTrace.predecessor r) A (Or.inl R')
  rwa [E] at T

private theorem walk_surj (r i : Fin n) : ∃ j, j<n ∧ nextAt r j=i := by
  have R := r.isLt
  have I := i.isLt
  by_cases E : r.val≤i.val
  · refine ⟨i.val-r.val,by omega,Fin.ext ?_⟩
    rw [nextAt_val,show r.val+(i.val-r.val)=i.val by omega,Nat.mod_eq_of_lt I]
  · refine ⟨n+i.val-r.val,by omega,Fin.ext ?_⟩
    rw [nextAt_val,show r.val+(n+i.val-r.val)=i.val+n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt I]

private theorem complete (hh : ∃ i,h i=true) (r : Fin n) (x : X)
    (A : Sweep Q h hh cap off succ r n x) : AllCorrect Q h hh cap off succ x := by
  apply target_of_fields hh x A.1
  · intro i
    obtain ⟨j,J,E⟩ := walk_surj r i
    exact E ▸ A.2.1 j (Nat.le_of_lt J)
  · intro i
    obtain ⟨j,J,E⟩ := walk_surj r i
    exact E ▸ A.2.2 j J

private theorem marked_expected {step : X → Fin n → X} {region target : X → Prop}
    (a : Fin n) (safe : ∀ x e, region x → region (step x e))
    (success : ∀ x, region x → target (step x a)) (x : X) (A : region x) :
    Height.IIDExpectedHittingTimeAtMost step target x n := by
  intro t
  induction t generalizing x with
  | zero => simp [Height.iidHitCost]
  | succ t ih =>
    by_cases H : target x
    · simp [Height.iidHitCost,H]
    simp only [Height.iidHitCost,if_neg H]
    let f := fun e : Fin n=>if e=a then 0 else n*n^t
    have L : (List.ofFn (fun e=>Height.iidHitCost step target t (step x e))).sum ≤ (List.ofFn f).sum := by
      apply FiniteUniformStoppingTree.ofFn_sum_le
      intro e
      by_cases E : e=a
      · subst e
        rw [Height.iidHitCost_of_target _ _ _ (success x A)]
        exact Nat.zero_le _
      · simpa only [f,if_neg E] using ih (step x e) (safe x e A)
    rw [PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const a f (n*n^t)
      (fun e E=>if_neg E)] at L
    simp only [f,if_true,Nat.zero_add] at L
    calc
      _ ≤ n^(t+1) + (n-1)*(n*n^t) := Nat.add_le_add_left L _
      _ = n*n^(t+1) := by
        have N : 1+(n-1)=n := by have := a.isLt; omega
        rw [Nat.pow_succ,Nat.mul_comm (n^t) n]
        calc
          _ = (1+(n-1))*(n*n^t) := by rw [Nat.add_mul,Nat.one_mul]
          _ = _ := by rw [N]

private theorem cost_weaken {step : X → Fin n → X} {P T : X → Prop}
    (sub : ∀ z, P z → T z) (x : X) (t : Nat) :
    Height.iidHitCost step T t x≤Height.iidHitCost step P t x := by
  induction t generalizing x with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    by_cases H : T x
    · simp [Height.iidHitCost,H]
    · have J : ¬P x := fun h=>H (sub x h)
      simp only [Height.iidHitCost,if_neg H,if_neg J]
      exact Nat.add_le_add_left (FiniteUniformStoppingTree.ofFn_sum_le _ _ (fun e=>ih (step x e))) _

theorem all_expected_sweep (hh : ∃ i,h i=true) (F : Frame step Q h cap off succ)
    (x : X) (A : Q x) :
    Height.IIDExpectedHittingTimeAtMost step (AllCorrect Q h hh cap off succ) x ((n+1)*n) := by
  obtain ⟨r,R⟩ := hh
  have N := Nat.zero_lt_of_lt r.isLt
  let P := Sweep Q h ⟨r,R⟩ cap off succ r
  have E (k : Nat) : Height.IIDExpectedHittingTimeAtMost step (P k) x ((k+1)*n) := by
    induction k with
    | zero =>
      simpa using marked_expected (RearTrace.predecessor r) F.closed (seed ⟨r,R⟩ F r R) x A
    | succ k ih =>
      have H : Height.IIDExpectedHittingTimeAtMost step (fun z=>P k z ∨ P (k+1) z) x ((k+1)*n) :=
        fun t=>Nat.le_trans (cost_weaken (step:=step) (fun _=>Or.inl) x t) (ih t)
      have H' (z : X) (Z : P k z) : Height.IIDExpectedHittingTimeAtMost step (P (k+1)) z n :=
        marked_expected (nextAt r k) (sweep_closed ⟨r,R⟩ F r R k) (sweep_pay ⟨r,R⟩ F r R k) z Z
      rw [Nat.succ_mul]
      exact iid_stage_le step N x (P k) (P (k+1)) ((k+1)*n) n H H'
  intro t
  exact Nat.le_trans (cost_weaken (step:=step) (complete ⟨r,R⟩ r) x t) (E n t)

theorem all_expected_quadratic (hh : ∃ i,h i=true) (F : Frame step Q h cap off succ)
    (x : X) (A : Q x) :
    Height.IIDExpectedHittingTimeAtMost step (AllCorrect Q h hh cap off succ) x (2*n^2) := by
  have N : 0<n := by obtain ⟨r,_⟩ := hh; exact Nat.zero_lt_of_lt r.isLt
  have E : (n+1)*n≤2*n^2 := by
    rw [Nat.pow_two,←Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by omega)
  exact fun t=>Nat.le_trans (all_expected_sweep hh F x A t) (Nat.mul_le_mul_right _ E)

end L4.ReportCacheSweep

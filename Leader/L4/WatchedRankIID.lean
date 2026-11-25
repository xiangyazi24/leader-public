import Leader.L4.ShortResetWatch
import Leader.Core.FiniteUniformStoppingTree

namespace L4.WatchedRankIID

def potential (B k : Nat) : Nat := 10^B - 10^(B-k)

theorem potential_mono (B : Nat) {j k : Nat} (E : j≤k) :
    potential B j≤potential B k := by
  apply Nat.sub_le_sub_left
  exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left E B)

theorem potential_credit {B k b : Nat} (K : 0<k) (KB : k≤B) (W : b≤9) :
    9 + potential B (k-1) + b*potential B B ≤ (b+1)*potential B k := by
  let M := 10^B
  let D := 10^(B-k)
  have Dp : 0<D := Nat.pow_pos (by decide)
  have Pow : 10^(B-(k-1)) = 10*D := by
    rw [show B-(k-1)=B-k+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have DM : 10*D≤M := by
    rw [←Pow]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have E1 : (b+1)*(M-D)+(b+1)*D=(b+1)*M := by
    rw [←Nat.mul_add,Nat.sub_add_cancel (by omega)]
  have E2 : b*(M-1)+b=b*M := by
    have p : 1≤M := by omega
    simpa only [Nat.mul_one,Nat.sub_add_cancel p] using (Nat.mul_add b (M-1) 1).symm
  have E3 : (b+1)*D+(9-b)*D=10*D := by
    rw [←Nat.add_mul,show b+1+(9-b)=10 by omega]
  have E4 : (b+1)*M=b*M+M := by rw [Nat.add_mul,Nat.one_mul]
  have E5 : 9-b≤(9-b)*D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (9-b) (show 1≤D by omega)
  unfold potential
  rw [Pow,Nat.sub_self,Nat.pow_zero]
  change 9+(M-10*D)+b*(M-1)≤(b+1)*(M-D)
  omega

private theorem nodup_length_of_subset {A : Type} [BEq A] [LawfulBEq A]
    (xs ys : List A) (H : xs.Nodup) (S : ∀ x∈xs,x∈ys) : xs.length≤ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have E := List.nodup_cons.mp H
    have mem : x∈ys := S x List.mem_cons_self
    have Q := ih (ys.erase x) E.2 (fun a ha =>
      (List.mem_erase_of_ne (fun V => E.1 (by simpa only [V] using ha))).mpr (S a (List.mem_cons_of_mem _ ha)))
    rw [List.length_erase_of_mem mem] at Q
    have P := List.length_pos_iff.mpr (List.ne_nil_of_mem mem)
    simp only [List.length_cons]
    omega

private def wrong {n : Nat} (watch : Fin n → Bool) (a e : Fin n) : Bool :=
  if e=a then false else watch e

private def spectator {n : Nat} (watch : Fin n → Bool) (a e : Fin n) : Bool :=
  if e=a then false else !watch e

private theorem bucket_sum {n : Nat} (watch : Fin n → Bool) (a : Fin n)
    (g b c : Nat) (L : List (Fin n)) :
    (L.map (fun e => if e=a then g else if watch e then b else c)).sum =
      L.count a*g + L.countP (wrong watch a)*b + L.countP (spectator watch a)*c := by
  induction L with
  | nil => simp
  | cons e L ih =>
    by_cases E : e=a
    · subst e
      simp [wrong,spectator,ih,Nat.add_mul,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
    · cases W : watch e <;>
        simp [E,W,List.count_cons_of_ne,wrong,spectator,ih,Nat.add_mul,
          Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

private theorem bucket_card {n : Nat} (watch : Fin n → Bool) (a : Fin n) :
    n = 1 + (List.finRange n).countP (wrong watch a) +
      (List.finRange n).countP (spectator watch a) := by
  have H := bucket_sum watch a 1 1 1 (List.finRange n)
  have O := (List.nodup_finRange n).count (a:=a)
  rw [if_pos (List.mem_finRange a)] at O
  have U : (List.finRange n).map (fun _ => 1) = List.ofFn (fun _ : Fin n => 1) := by
    rw [List.finRange,List.map_ofFn]
    rfl
  have V : (List.finRange n).map (fun e => if e=a then 1 else if watch e then 1 else 1) =
      (List.finRange n).map (fun _ => 1) := by
    apply List.map_congr_left
    intro e _
    simp
  rw [V,U,FiniteUniformStoppingTree.ofFn_sum_const] at H
  simpa [O] using H

private theorem wrong_count_le {n : Nat} (watch : List (Fin n)) (a : Fin n)
    (A : a∈watch) (L : watch.length≤10) :
    (List.finRange n).countP (wrong (fun e => decide (e∈watch)) a)≤9 := by
  rw [List.countP_eq_length_filter]
  have R := nodup_length_of_subset
    ((List.finRange n).filter (wrong (fun e => decide (e∈watch)) a))
    (watch.erase a) (List.Pairwise.filter _ (List.nodup_finRange n))
    (fun e he => by
      have E := (List.mem_filter.mp he).2
      by_cases ea : e=a
      · simp [wrong,ea] at E
      · exact (List.mem_erase_of_ne ea).mpr
          (of_decide_eq_true (by simpa only [wrong,if_neg ea] using E : decide (e∈watch)=true)))
  rw [List.length_erase_of_mem A] at R
  omega

/-- Score on the literal raw state. A wrong watched edge may reset it. -/
structure Spec {X : Type} {n : Nat} (step : X → Fin n → X)
    (region target : X → Prop) (watch : List (Fin n)) (B : Nat) (rank : X → Nat) : Prop where
  close : ∀ x e, region x → region (step x e)
  bounded : ∀ x, region x → rank x≤B
  zero_hits : ∀ x, region x → rank x=0 → target x
  nominate : ∀ x, region x → ¬target x → ∃ e∈watch, rank (step x e)<rank x
  idle : ∀ x e, region x → ¬target x → e∉watch → rank (step x e)≤rank x

private theorem drift {X : Type} {n : Nat} {step : X → Fin n → X}
    {region target : X → Prop} {watch : List (Fin n)} {B : Nat} {rank : X → Nat}
    (S : Spec step region target watch B rank) (W : watch.length≤10) (x : X) (A : region x)
    (H : ¬target x) :
    9*n + (List.ofFn (fun e => n*potential B (rank (step x e)))).sum ≤
      n*(n*potential B (rank x)) := by
  obtain ⟨a,ha,dec⟩ := S.nominate x A H
  let w : Fin n → Bool := fun e=>decide (e∈watch)
  let k := rank x
  let b := (List.finRange n).countP (wrong w a)
  let c := (List.finRange n).countP (spectator w a)
  let f := fun e => if e=a then n*potential B (k-1)
    else if w e then n*potential B B else n*potential B k
  have U := FiniteUniformStoppingTree.ofFn_sum_le
    (fun e => n*potential B (rank (step x e))) f (fun e=>by
      dsimp [f]
      by_cases E : e=a
      · subst e
        rw [if_pos rfl]
        exact Nat.mul_le_mul_left _ (potential_mono B (by change rank (step x a)≤rank x-1; omega))
      · rw [if_neg E]
        by_cases V : e∈watch
        · rw [if_pos (show w e=true from decide_eq_true V)]
          exact Nat.mul_le_mul_left _ (potential_mono B (S.bounded _ (S.close x e A)))
        · rw [if_neg (show w e≠true from fun E=>V (of_decide_eq_true E))]
          exact Nat.mul_le_mul_left _ (potential_mono B (S.idle x e A H V)))
  have F : List.ofFn f=(List.finRange n).map f := by rw [List.finRange,List.map_ofFn]; rfl
  rw [F] at U
  unfold f at U
  rw [bucket_sum] at U
  have O := (List.nodup_finRange n).count (a:=a)
  rw [if_pos (List.mem_finRange a)] at O
  rw [O,Nat.one_mul] at U
  have C : 9+potential B (k-1)+b*potential B B≤(b+1)*potential B k :=
    potential_credit (by change 0<rank x; omega) (S.bounded x A) (wrong_count_le watch a ha W)
  have L : n=1+b+c := bucket_card w a
  calc
    _ ≤ 9*n+(n*potential B (k-1)+b*(n*potential B B)+c*(n*potential B k)) :=
      Nat.add_le_add_left U _
    _ = n*(9+potential B (k-1)+b*potential B B+c*potential B k) := by
      simp only [Nat.mul_add]
      ac_rfl
    _ ≤ n*((b+1)*potential B k+c*potential B k) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right C _)
    _ = n*(n*potential B k) := by rw [←Nat.add_mul,show b+1+c=n by omega]

private theorem cost {X : Type} {n : Nat} {step : X → Fin n → X}
    {region target : X → Prop} {watch : List (Fin n)} {B : Nat} {rank : X → Nat}
    (S : Spec step region target watch B rank) (W : watch.length≤10) (t : Nat)
    (x : X) (A : region x) :
    9 * L4.iidHitCost step target t x ≤ (n*potential B (rank x))*n^t := by
  induction t generalizing x with
  | zero => simp [L4.iidHitCost]
  | succ t ih =>
    by_cases H : target x
    · simp [L4.iidHitCost,H]
    · simp only [L4.iidHitCost,if_neg H]
      have U := FiniteUniformStoppingTree.ofFn_sum_le
        (fun e => 9*L4.iidHitCost step target t (step x e))
        (fun e => (n*potential B (rank (step x e)))*n^t)
        (fun e => ih _ (S.close x e A))
      rw [FiniteUniformStoppingTree.ofFn_sum_mul_left] at U
      have R : (List.ofFn (fun e => (n*potential B (rank (step x e)))*n^t)).sum =
          n^t*(List.ofFn (fun e => n*potential B (rank (step x e)))).sum := by
        rw [←FiniteUniformStoppingTree.ofFn_sum_mul_left]
        apply FiniteUniformStoppingTree.ofFn_sum_eq
        intro e
        exact Nat.mul_comm _ _
      rw [R] at U
      calc
        _ = n^t*(9*n)+9*(List.ofFn (fun e => L4.iidHitCost step target t (step x e))).sum := by
          rw [Nat.mul_add,Nat.pow_succ]; ac_rfl
        _ ≤ n^t*(9*n)+n^t*(List.ofFn (fun e => n*potential B (rank (step x e)))).sum :=
          Nat.add_le_add_left U _
        _ = n^t*(9*n+(List.ofFn (fun e => n*potential B (rank (step x e)))).sum) := by rw [Nat.mul_add]
        _ ≤ n^t*(n*(n*potential B (rank x))) := Nat.mul_le_mul_left _ (drift S W x A H)
        _ = _ := by rw [Nat.pow_succ]; ac_rfl

/-- Full raw IID bound on a closed region, with no replay or resampling. -/
theorem expected {X : Type} {n : Nat} {step : X → Fin n → X}
    {region target : X → Prop} {watch : List (Fin n)} {B : Nat} {rank : X → Nat}
    (S : Spec step region target watch B rank) (W : watch.length≤10)
    (x : X) (A : region x) :
    L4.IIDExpectedHittingTimeAtMost step target x (n*10^B) := by
  intro t
  have C := cost S W t x A
  have L : n*potential B (rank x)≤n*10^B := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have R := Nat.le_trans C (Nat.mul_le_mul_right (n^t) L)
  change L4.iidHitCost step target t x≤_
  omega

/-- An actual fixed H1 fiber. Its rank is a function only of the watched
chart bytes, so spectator invariance is discharged by the row frame. -/
theorem chart_expected {s n B : Nat} {h : Fin n → Bool}
    (C : ShortResetCycle.Chart h) (small : C.L≤9) (N : 5≤n)
    (target : PhysicalCustody.Raw s n → Prop) (f : (Fin C.L → BitVec 96) → Nat)
    (bounded : ∀ x : PhysicalCustody.Raw s n, PhysicalCustody.H2Ready x →
      (∀ i, AllSizeS1Geometry.header (x i)=h i) → f (ShortResetWatch.projection C x)≤B)
    (nominate : ∀ x : PhysicalCustody.Raw s n, PhysicalCustody.H2Ready x →
      (∀ i, AllSizeS1Geometry.header (x i)=h i) → ¬target x →
      ∃ e∈ShortResetWatch.watch C,
        f (ShortResetWatch.projection C (PhysicalCustody.rawNext s x e)) <
          f (ShortResetWatch.projection C x))
    (x : PhysicalCustody.Raw s n) (A : PhysicalCustody.H2Ready x)
    (heads : ∀ i, AllSizeS1Geometry.header (x i)=h i) :
    L4.IIDExpectedHittingTimeAtMost (PhysicalCustody.rawNext s) target x (n*10^B) := by
  let region := fun x : PhysicalCustody.Raw s n =>
    PhysicalCustody.H2Ready x ∧ ∀ i,AllSizeS1Geometry.header (x i)=h i
  let rank := fun x : PhysicalCustody.Raw s n => f (ShortResetWatch.projection C x)
  let D : Spec (PhysicalCustody.rawNext s) region target (ShortResetWatch.watch C) B rank := by
    refine ⟨?_,fun y Y=>bounded y Y.1 Y.2,?_,fun y Y F=>nominate y Y.1 Y.2 F,?_⟩
    · intro y e Y
      exact ⟨PhysicalCustody.h2_ready_closed N y e Y.1,fun i=>
        (PhysicalCustody.H1.raw_h1_selected_frozen N y e i Y.1.1).trans (Y.2 i)⟩
    · intro y Y Z
      by_cases F : target y
      · exact F
      · obtain ⟨e,_,G⟩ := nominate y Y.1 Y.2 F
        change f (ShortResetWatch.projection C y)=0 at Z
        omega
    · intro y e _ _ E
      exact Nat.le_of_eq (congrArg f (ShortResetWatch.outside_projection C y e E))
  exact expected D (ShortResetWatch.watch_bound C small) x ⟨A,heads⟩

#print axioms potential_credit
#print axioms expected
#print axioms chart_expected
end L4.WatchedRankIID

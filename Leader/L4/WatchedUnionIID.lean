import Leader.L4.ShortResetWatch
import Leader.Core.FiniteUniformStoppingTree

namespace L4.WatchedUnionIID

def potential (q B k : Nat) : Nat := q^B - q^(B-k)

theorem potential_mono {q : Nat} (Q : 0<q) (B : Nat) {j k : Nat} (E : j≤k) :
    potential q B j≤potential q B k := by
  apply Nat.sub_le_sub_left
  exact Nat.pow_le_pow_right Q (Nat.sub_le_sub_left E B)

theorem potential_credit {q B k b : Nat} (Q : 0<q) (K : 0<k) (KB : k≤B) (W : b<q) :
    (q-1) + potential q B (k-1) + b*potential q B B ≤ (b+1)*potential q B k := by
  let M := q^B
  let D := q^(B-k)
  have Dp : 0<D := Nat.pow_pos Q
  have Pow : q^(B-(k-1)) = q*D := by
    rw [show B-(k-1)=B-k+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have DM : q*D≤M := by
    rw [←Pow]
    exact Nat.pow_le_pow_right Q (Nat.sub_le _ _)
  have Dm : D ≤ M := Nat.le_trans (Nat.le_mul_of_pos_left D Q) DM
  have E1 : (b+1)*(M-D)+(b+1)*D=(b+1)*M := by
    rw [←Nat.mul_add,Nat.sub_add_cancel (by omega)]
  have E2 : b*(M-1)+b=b*M := by
    have p : 1≤M := by omega
    simpa only [Nat.mul_one,Nat.sub_add_cancel p] using (Nat.mul_add b (M-1) 1).symm
  have E3 : (b+1)*D+(q-1-b)*D=q*D := by
    rw [←Nat.add_mul,show b+1+(q-1-b)=q by omega]
  have E4 : (b+1)*M=b*M+M := by rw [Nat.add_mul,Nat.one_mul]
  have E5 : q-1-b≤(q-1-b)*D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (q-1-b) (show 1≤D by omega)
  unfold potential
  rw [Pow,Nat.sub_self,Nat.pow_zero]
  change q-1+(M-q*D)+b*(M-1)≤(b+1)*(M-D)
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

private theorem wrong_count_le {q n : Nat} (watch : List (Fin n)) (a : Fin n)
    (A : a∈watch) (L : watch.length≤q) :
    (List.finRange n).countP (wrong (fun e => decide (e∈watch)) a)<q := by
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
  have P := List.length_pos_iff.mpr (List.ne_nil_of_mem A)
  omega

/-- Score on the literal raw state. A wrong watched edge may reset it. -/
structure Spec {X : Type} {n : Nat} (step : X → Fin n → X)
    (region target : X → Prop) (watch : List (Fin n)) (B : Nat) (rank : X → Nat) : Prop where
  close : ∀ x e, region x → region (step x e)
  bounded : ∀ x, region x → rank x≤B
  zero_hits : ∀ x, region x → rank x=0 → target x
  nominate : ∀ x, region x → ¬target x → ∃ e∈watch, rank (step x e)<rank x
  idle : ∀ x e, region x → ¬target x → e∉watch → rank (step x e)≤rank x

private theorem drift {X : Type} {q n : Nat} (Q : 0<q) {step : X → Fin n → X}
    {region target : X → Prop} {watch : List (Fin n)} {B : Nat} {rank : X → Nat}
    (S : Spec step region target watch B rank) (W : watch.length≤q) (x : X) (A : region x)
    (H : ¬target x) :
    (q-1)*n + (List.ofFn (fun e => n*potential q B (rank (step x e)))).sum ≤
      n*(n*potential q B (rank x)) := by
  obtain ⟨a,ha,dec⟩ := S.nominate x A H
  let w : Fin n → Bool := fun e=>decide (e∈watch)
  let k := rank x
  let b := (List.finRange n).countP (wrong w a)
  let c := (List.finRange n).countP (spectator w a)
  let f := fun e => if e=a then n*potential q B (k-1)
    else if w e then n*potential q B B else n*potential q B k
  have U := FiniteUniformStoppingTree.ofFn_sum_le
    (fun e => n*potential q B (rank (step x e))) f (fun e=>by
      dsimp [f]
      by_cases E : e=a
      · subst e
        rw [if_pos rfl]
        exact Nat.mul_le_mul_left _ (potential_mono Q B (by change rank (step x a)≤rank x-1; omega))
      · rw [if_neg E]
        by_cases V : e∈watch
        · rw [if_pos (show w e=true from decide_eq_true V)]
          exact Nat.mul_le_mul_left _ (potential_mono Q B (S.bounded _ (S.close x e A)))
        · rw [if_neg (show w e≠true from fun E=>V (of_decide_eq_true E))]
          exact Nat.mul_le_mul_left _ (potential_mono Q B (S.idle x e A H V)))
  have F : List.ofFn f=(List.finRange n).map f := by rw [List.finRange,List.map_ofFn]; rfl
  rw [F] at U
  unfold f at U
  rw [bucket_sum] at U
  have O := (List.nodup_finRange n).count (a:=a)
  rw [if_pos (List.mem_finRange a)] at O
  rw [O,Nat.one_mul] at U
  have C : q-1+potential q B (k-1)+b*potential q B B≤(b+1)*potential q B k :=
    potential_credit Q (by change 0<rank x; omega) (S.bounded x A) (wrong_count_le watch a ha W)
  have L : n=1+b+c := bucket_card w a
  calc
    _ ≤ (q-1)*n+(n*potential q B (k-1)+b*(n*potential q B B)+c*(n*potential q B k)) :=
      Nat.add_le_add_left U _
    _ = n*(q-1+potential q B (k-1)+b*potential q B B+c*potential q B k) := by
      simp only [Nat.mul_add]
      ac_rfl
    _ ≤ n*((b+1)*potential q B k+c*potential q B k) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right C _)
    _ = n*(n*potential q B k) := by rw [←Nat.add_mul,show b+1+c=n by omega]

private theorem cost {X : Type} {q n : Nat} (Q : 0<q) {step : X → Fin n → X}
    {region target : X → Prop} {watch : List (Fin n)} {B : Nat} {rank : X → Nat}
    (S : Spec step region target watch B rank) (W : watch.length≤q) (t : Nat)
    (x : X) (A : region x) :
    (q-1) * L4.iidHitCost step target t x ≤ (n*potential q B (rank x))*n^t := by
  induction t generalizing x with
  | zero => simp [L4.iidHitCost]
  | succ t ih =>
    by_cases H : target x
    · simp [L4.iidHitCost,H]
    · simp only [L4.iidHitCost,if_neg H]
      have U := FiniteUniformStoppingTree.ofFn_sum_le
        (fun e => (q-1)*L4.iidHitCost step target t (step x e))
        (fun e => (n*potential q B (rank (step x e)))*n^t)
        (fun e => ih _ (S.close x e A))
      rw [FiniteUniformStoppingTree.ofFn_sum_mul_left] at U
      have R : (List.ofFn (fun e => (n*potential q B (rank (step x e)))*n^t)).sum =
          n^t*(List.ofFn (fun e => n*potential q B (rank (step x e)))).sum := by
        rw [←FiniteUniformStoppingTree.ofFn_sum_mul_left]
        apply FiniteUniformStoppingTree.ofFn_sum_eq
        intro e
        exact Nat.mul_comm _ _
      rw [R] at U
      calc
        _ = n^t*((q-1)*n)+(q-1)*(List.ofFn (fun e => L4.iidHitCost step target t (step x e))).sum := by
          rw [Nat.mul_add,Nat.pow_succ]; ac_rfl
        _ ≤ n^t*((q-1)*n)+n^t*(List.ofFn (fun e => n*potential q B (rank (step x e)))).sum :=
          Nat.add_le_add_left U _
        _ = n^t*((q-1)*n+(List.ofFn (fun e => n*potential q B (rank (step x e)))).sum) := by rw [Nat.mul_add]
        _ ≤ n^t*(n*(n*potential q B (rank x))) := Nat.mul_le_mul_left _ (drift Q S W x A H)
        _ = _ := by rw [Nat.pow_succ]; ac_rfl

/-- Full raw IID bound on a closed region, with no replay or resampling. -/
theorem expected {X : Type} {q n : Nat} (Q : 1<q) {step : X → Fin n → X}
    {region target : X → Prop} {watch : List (Fin n)} {B : Nat} {rank : X → Nat}
    (S : Spec step region target watch B rank) (W : watch.length≤q)
    (x : X) (A : region x) :
    L4.IIDExpectedHittingTimeAtMost step target x (n*q^B) := by
  intro t
  have C := cost (by omega : 0<q) S W t x A
  have L : n*potential q B (rank x)≤n*q^B := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have R := Nat.le_trans C (Nat.mul_le_mul_right (n^t) L)
  calc
    _ = 1 * L4.iidHitCost step target t x := (Nat.one_mul _).symm
    _ ≤ (q-1) * L4.iidHitCost step target t x :=
      Nat.mul_le_mul_right _ (by omega)
    _ ≤ _ := R


open PhysicalCustody

/-- A watcher for several (possibly overlapping) charts; repeated labels
in the list only increase the bound, not their sampling probability. -/
def chartsWatch {n : Nat} {h : Fin n → Bool}
    (cs : List (ShortResetCycle.Chart h)) : List (Fin n) :=
  cs.flatMap ShortResetWatch.watch

theorem chartsWatch_bound {n : Nat} {h : Fin n → Bool}
    (cs : List (ShortResetCycle.Chart h)) (small : ∀ C ∈ cs, C.L ≤ 9) :
    (chartsWatch cs).length ≤ 10 * cs.length := by
  induction cs with
  | nil => simp [chartsWatch]
  | cons C cs ih =>
    have H := ShortResetWatch.watch_bound C (small C (by simp))
    have I := ih (fun E m => small E (List.mem_cons_of_mem _ m))
    simp only [chartsWatch, List.flatMap_cons, List.length_append, List.length_cons]
    change (ShortResetWatch.watch C).length + (chartsWatch cs).length ≤ _
    omega

/-- A rank on the original raw state can ignore inter-chart spectator
marks without claiming that their deletion commutes with boundary rows. -/
theorem charts_expected {s n B q : Nat} {h : Fin n → Bool} (N : 5 ≤ n)
    (cs : List (ShortResetCycle.Chart h)) (Q : 1 < q)
    (W : (chartsWatch cs).length ≤ q)
    (target : Raw s n → Prop) (rank : Raw s n → Nat)
    (bounded : ∀ x, H2Ready x → (∀ i, AllSizeS1Geometry.header (x i) = h i) → rank x ≤ B)
    (nominate : ∀ x, H2Ready x → (∀ i, AllSizeS1Geometry.header (x i) = h i) →
      ¬ target x → ∃ e ∈ chartsWatch cs, rank (rawNext s x e) < rank x)
    (localRank : ∀ x y, (∀ C ∈ cs, ShortResetWatch.projection C x =
      ShortResetWatch.projection C y) → rank x = rank y)
    (x : Raw s n) (A : H2Ready x)
    (heads : ∀ i, AllSizeS1Geometry.header (x i) = h i) :
    IIDExpectedHittingTimeAtMost (rawNext s) target x (n * q^B) := by
  let region := fun x : Raw s n => H2Ready x ∧ ∀ i, AllSizeS1Geometry.header (x i) = h i
  let S : Spec (rawNext s) region target (chartsWatch cs) B rank := by
    refine ⟨?_, fun y Y => bounded y Y.1 Y.2, ?_,
      fun y Y T => nominate y Y.1 Y.2 T, ?_⟩
    · intro y e Y
      exact ⟨h2_ready_closed N y e Y.1, fun i =>
        (H1.raw_h1_selected_frozen N y e i Y.1.1).trans (Y.2 i)⟩
    · intro y Y R
      by_cases T : target y
      · exact T
      · obtain ⟨e, _, E⟩ := nominate y Y.1 Y.2 T
        omega
    · intro y e _ _ E
      apply Nat.le_of_eq
      apply localRank
      intro C HC
      apply ShortResetWatch.outside_projection
      intro M
      exact E (List.mem_flatMap.mpr ⟨C, HC, M⟩)
  exact expected Q S W x ⟨A, heads⟩

#print axioms chartsWatch_bound
#print axioms charts_expected
#print axioms potential_credit
#print axioms expected
end L4.WatchedUnionIID

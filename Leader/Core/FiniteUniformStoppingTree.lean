import Leader.Core.Basic

/-!
# Finite uniform stopping trees

This module gives a protocol-independent, division-free model of a uniformly
scheduled stopped process.  An active state has exactly `n` raw scheduler
children, while success and failure are distinct absorbing nodes.  All
quantities below are exact natural-number sums over scheduler words; no
probability space or independence premise is used.

The main theorem is a finite-horizon Bellman bound.  A natural-valued
supersolution with scale `c` pays `c` units for every active interaction.  At
every horizon, the scaled truncated active cost plus the nonnegative leaf
residual is bounded by `n ^ T` times the initial potential.
-/

namespace FiniteUniformStoppingTree

set_option autoImplicit false

/-! ## Finite uniform sums -/

/-- Pointwise equality lifts to equality of a finite uniform sum. -/
theorem ofFn_sum_eq {n : Nat} (f g : Fin n → Nat)
    (hfg : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        hfg 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

/-- Pointwise domination lifts to domination of a finite uniform sum. -/
theorem ofFn_sum_le {n : Nat} (f g : Fin n → Nat)
    (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

/-- A finite uniform sum distributes over pointwise addition. -/
theorem ofFn_sum_add {n : Nat} (f g : Fin n → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

/-- A common natural factor pulls out of a finite uniform sum. -/
theorem ofFn_sum_mul_left {n : Nat} (a : Nat) (f : Fin n → Nat) :
    (List.ofFn (fun i => a * f i)).sum =
      a * (List.ofFn f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        ih, Nat.mul_add]

/-- The sum of a constant over `Fin n` is `n` times that constant. -/
theorem ofFn_sum_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem sum_map_const {A : Type} (xs : List A) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp only [Nat.succ_mul]
      omega

private theorem pred_mul (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [Nat.succ_mul, Nat.add_comm]

private theorem sum_one_exception
    {A : Type} [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (f : A → Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hother : ∀ z, z ∈ xs → z ≠ a → f z = c) :
    (xs.map f).sum = f a + (xs.length - 1) * c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hall : xs.map f = xs.map (fun _ => c) := by
          apply List.map_congr_left
          intro z hz
          exact hother z (by simp [hz])
            (by intro q; subst z; exact hnodup.1 hz)
        rw [List.map_cons, List.sum_cons, hall, sum_map_const]
        simp
      · have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | hat
          · exact absurd hax.symm hxa
          · exact hat
        have hi := ih hnodup.2 hat (by
          intro z hz
          exact hother z (by simp [hz]))
        have hx : f x = c := hother x (by simp) hxa
        rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
        have hpos : 0 < xs.length :=
          List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
        have hc := pred_mul xs.length c hpos
        have hsub : xs.length + 1 - 1 = xs.length := by omega
        rw [hsub]
        omega

/-- Sum a natural-valued function that is constant away from two distinct
entries.  This is the reusable arithmetic form for two distinguished raw
scheduler edges. -/
theorem sum_two_exceptions
    {A : Type} [BEq A] [LawfulBEq A]
    (xs : List A) (a b : A) (f : A → Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b)
    (hother : ∀ z, z ∈ xs → z ≠ a → z ≠ b → f z = c) :
    (xs.map f).sum = f a + f b + (xs.length - 2) * c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hbt : b ∈ xs := by
          rcases List.mem_cons.mp hb with hbx | hbt
          · exact absurd hbx.symm hab
          · exact hbt
        have hone := sum_one_exception xs b f c hnodup.2 hbt (by
          intro z hz hzb
          exact hother z (by simp [hz])
            (by intro hza; subst z; exact hnodup.1 hz) hzb)
        rw [List.map_cons, List.sum_cons, hone, List.length_cons]
        have hsub : xs.length + 1 - 2 = xs.length - 1 := by omega
        rw [hsub]
        omega
      · by_cases hxb : x = b
        · subst x
          have hat : a ∈ xs := by
            rcases List.mem_cons.mp ha with hax | hat
            · exact absurd hax hab
            · exact hat
          have hone := sum_one_exception xs a f c hnodup.2 hat (by
            intro z hz hza
            exact hother z (by simp [hz]) hza
              (by intro hzb; subst z; exact hnodup.1 hz))
          rw [List.map_cons, List.sum_cons, hone, List.length_cons]
          have hsub : xs.length + 1 - 2 = xs.length - 1 := by omega
          rw [hsub]
          omega
        · have hat : a ∈ xs := by
            rcases List.mem_cons.mp ha with hax | hat
            · exact absurd hax.symm hxa
            · exact hat
          have hbt : b ∈ xs := by
            rcases List.mem_cons.mp hb with hbx | hbt
            · exact absurd hbx.symm hxb
            · exact hbt
          have hi := ih hnodup.2 hat hbt (by
            intro z hz
            exact hother z (by simp [hz]))
          have hx : f x = c := hother x (by simp) hxa hxb
          rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
          have hlen : 2 ≤ xs.length := by
            have hpos : 0 < xs.length :=
              List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
            by_cases hone : xs.length = 1
            · rw [List.length_eq_one_iff] at hone
              obtain ⟨z, rfl⟩ := hone
              simp at hat hbt
              exact absurd (hat.trans hbt.symm) hab
            · omega
          have hc := pred_mul (xs.length - 1) c (by omega)
          have hidx : xs.length + 1 - 2 = xs.length - 1 := by omega
          have hidx2 : xs.length - 1 - 1 = xs.length - 2 := by omega
          rw [hidx2] at hc
          rw [hidx]
          omega

/-! ## Absorbing stopped trees -/

/-- A node is either an active process state or one of two terminal outcomes. -/
inductive StopNode (S : Type) where
  | active : S → StopNode S
  | success : StopNode S
  | failure : StopNode S

/-- Extend an active-state transition to an absorbing stopped transition. -/
def stepNode {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) : StopNode S → Fin n → StopNode S
  | .active s, e => step s e
  | .success, _ => .success
  | .failure, _ => .failure

/-- Exact sum of a leaf weight over all depth-`T` scheduler words. -/
def treeWeight {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (weight : StopNode S → Nat) :
    StopNode S → Nat → Nat
  | x, 0 => weight x
  | x, T + 1 =>
      (List.ofFn (fun e : Fin n =>
        treeWeight step weight (stepNode step x e) T)).sum

/-- Unit leaf weight. -/
def oneWeight {S : Type} : StopNode S → Nat := fun _ => 1

/-- Indicator that a leaf is still active. -/
def activeWeight {S : Type} : StopNode S → Nat
  | .active _ => 1
  | .success => 0
  | .failure => 0

/-- Indicator that a leaf has stopped in success. -/
def successWeight {S : Type} : StopNode S → Nat
  | .active _ => 0
  | .success => 1
  | .failure => 0

/-- Indicator that a leaf has stopped in failure. -/
def failureWeight {S : Type} : StopNode S → Nat
  | .active _ => 0
  | .success => 0
  | .failure => 1

/-- Number of depth-`T` words ending at an active node. -/
def activeCount {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T : Nat) : Nat :=
  treeWeight step activeWeight x T

/-- Number of depth-`T` words absorbed in success. -/
def successCount {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T : Nat) : Nat :=
  treeWeight step successWeight x T

/-- Number of depth-`T` words absorbed in failure. -/
def failureCount {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T : Nat) : Nat :=
  treeWeight step failureWeight x T

/-- Pointwise equal weights have equal exact scheduler-tree sums. -/
theorem treeWeight_congr {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (w v : StopNode S → Nat)
    (hwv : ∀ x, w x = v x) :
    ∀ x T, treeWeight step w x T = treeWeight step v x T := by
  intro x T
  induction T generalizing x with
  | zero => exact hwv x
  | succ T ih =>
      simp only [treeWeight]
      exact ofFn_sum_eq _ _ (fun e => ih (stepNode step x e))

/-- Exact tree sums distribute over addition of leaf weights. -/
theorem treeWeight_add {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (w v : StopNode S → Nat) :
    ∀ x T,
      treeWeight step (fun y => w y + v y) x T =
        treeWeight step w x T + treeWeight step v x T := by
  intro x T
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      calc
        (List.ofFn (fun e => treeWeight step (fun y => w y + v y)
            (stepNode step x e) T)).sum =
            (List.ofFn (fun e => treeWeight step w (stepNode step x e) T +
              treeWeight step v (stepNode step x e) T)).sum := by
                exact ofFn_sum_eq _ _ (fun e => ih (stepNode step x e))
        _ = _ := ofFn_sum_add _ _

/-- Pointwise domination of leaf weights lifts through every scheduler-tree
horizon. -/
theorem treeWeight_mono {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (w v : StopNode S → Nat)
    (hwv : ∀ x, w x ≤ v x) :
    ∀ x T, treeWeight step w x T ≤ treeWeight step v x T := by
  intro x T
  induction T generalizing x with
  | zero => exact hwv x
  | succ T ih =>
      simp only [treeWeight]
      exact ofFn_sum_le _ _ (fun e ↦ ih (stepNode step x e))

/-- A common natural factor pulls out of every scheduler-tree leaf sum. -/
theorem treeWeight_mul_left {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (a : Nat)
    (w : StopNode S → Nat) :
    ∀ x T,
      treeWeight step (fun y ↦ a * w y) x T =
        a * treeWeight step w x T := by
  intro x T
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      calc
        (List.ofFn (fun e : Fin n ↦
          treeWeight step (fun y ↦ a * w y)
            (stepNode step x e) T)).sum =
            (List.ofFn (fun e : Fin n ↦
              a * treeWeight step w (stepNode step x e) T)).sum := by
                exact ofFn_sum_eq _ _ (fun e ↦ ih (stepNode step x e))
        _ = a * (List.ofFn (fun e : Fin n ↦
              treeWeight step w (stepNode step x e) T)).sum :=
          ofFn_sum_mul_left a _

/-- A nonnegative leaf potential whose active child sum is at most `n` times
its current value is dominated by its initial value at every finite horizon.
Terminal nodes need no side condition because `stepNode` makes them absorbing. -/
theorem treeWeight_le_pow_mul_of_child_sum_le {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (w : StopNode S → Nat)
    (hstep : ∀ s,
      (List.ofFn (fun e : Fin n ↦ w (step s e))).sum ≤
        n * w (.active s)) :
    ∀ x T, treeWeight step w x T ≤ n ^ T * w x := by
  intro x T
  induction T generalizing x with
  | zero => simp [treeWeight]
  | succ T ih =>
      cases x with
      | success =>
          simp only [treeWeight, stepNode]
          calc
            (List.ofFn (fun _ : Fin n ↦ treeWeight step w .success T)).sum ≤
                (List.ofFn (fun _ : Fin n ↦ n ^ T * w .success)).sum :=
              ofFn_sum_le _ _ (fun _ ↦ ih .success)
            _ = n * (n ^ T * w .success) := ofFn_sum_const n _
            _ = n ^ (T + 1) * w .success := by
              rw [Nat.pow_succ]
              ac_rfl
      | failure =>
          simp only [treeWeight, stepNode]
          calc
            (List.ofFn (fun _ : Fin n ↦ treeWeight step w .failure T)).sum ≤
                (List.ofFn (fun _ : Fin n ↦ n ^ T * w .failure)).sum :=
              ofFn_sum_le _ _ (fun _ ↦ ih .failure)
            _ = n * (n ^ T * w .failure) := ofFn_sum_const n _
            _ = n ^ (T + 1) * w .failure := by
              rw [Nat.pow_succ]
              ac_rfl
      | active s =>
          simp only [treeWeight]
          calc
            (List.ofFn (fun e : Fin n ↦
              treeWeight step w (step s e) T)).sum ≤
                (List.ofFn (fun e : Fin n ↦
                  n ^ T * w (step s e))).sum :=
              ofFn_sum_le _ _ (fun e ↦ ih (step s e))
            _ = n ^ T *
                (List.ofFn (fun e : Fin n ↦ w (step s e))).sum :=
              ofFn_sum_mul_left _ _
            _ ≤ n ^ T * (n * w (.active s)) :=
              Nat.mul_le_mul_left _ (hstep s)
            _ = n ^ (T + 1) * w (.active s) := by
              simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
                Nat.mul_left_comm]

/-- A complete depth-`T` uniform scheduler tree has exactly `n ^ T` leaves. -/
theorem treeWeight_one {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) :
    ∀ x T, treeWeight step oneWeight x T = n ^ T := by
  intro x T
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      calc
        (List.ofFn (fun e => treeWeight step oneWeight
            (stepNode step x e) T)).sum =
            (List.ofFn (fun _ : Fin n => n ^ T)).sum := by
              exact ofFn_sum_eq _ _ (fun e => ih (stepNode step x e))
        _ = n * n ^ T := ofFn_sum_const n _
        _ = n ^ (T + 1) := by simp [Nat.pow_succ, Nat.mul_comm]

/-- Every scheduler word ends in exactly one of active, success, or failure. -/
theorem node_count_partition {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T : Nat) :
    activeCount step x T + successCount step x T + failureCount step x T =
      n ^ T := by
  unfold activeCount successCount failureCount
  calc
    treeWeight step activeWeight x T + treeWeight step successWeight x T +
        treeWeight step failureWeight x T =
        treeWeight step (fun y => activeWeight y + successWeight y) x T +
          treeWeight step failureWeight x T := by
            exact Nat.add_right_cancel_iff.mpr
              (treeWeight_add step activeWeight successWeight x T).symm
    _ =
        treeWeight step
          (fun y => (activeWeight y + successWeight y) + failureWeight y)
          x T := (treeWeight_add step
            (fun y => activeWeight y + successWeight y)
            failureWeight x T).symm
    _ = treeWeight step oneWeight x T := by
      apply treeWeight_congr
      intro y
      cases y <;> rfl
    _ = n ^ T := treeWeight_one step x T

/-! ## Truncated active cost and Bellman certificates -/

/-- Exact numerator of active interactions along all depth-`T` scheduler
words.  At an active node with `T+1` steps remaining, all `n^(T+1)` full
words pay for the first interaction; terminal nodes pay nothing. -/
def truncatedActiveCostNumerator {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) : StopNode S → Nat → Nat
  | _, 0 => 0
  | .success, _ + 1 => 0
  | .failure, _ + 1 => 0
  | .active s, T + 1 =>
      n ^ (T + 1) +
        (List.ofFn (fun e : Fin n =>
          truncatedActiveCostNumerator step (step s e) T)).sum

/-- Increasing the raw horizon by one cannot decrease the normalized
truncated active cost.  The factor `n` pads every old scheduler word by one
arbitrary final symbol. -/
theorem mul_truncatedActiveCostNumerator_le_succ
    {S : Type} {n : Nat} (step : S -> Fin n -> StopNode S) :
    forall (x : StopNode S) T,
      n * truncatedActiveCostNumerator step x T <=
        truncatedActiveCostNumerator step x (T + 1) := by
  intro x T
  induction T generalizing x with
  | zero => simp [truncatedActiveCostNumerator]
  | succ T ih =>
      cases x with
      | success => simp [truncatedActiveCostNumerator]
      | failure => simp [truncatedActiveCostNumerator]
      | active state =>
          simp only [truncatedActiveCostNumerator, Nat.mul_add]
          apply Nat.add_le_add
          · simp [Nat.pow_succ, Nat.mul_comm]
          · rw [← ofFn_sum_mul_left]
            exact ofFn_sum_le _ _ (fun edge => ih (step state edge))

/-- Iterated normalized horizon monotonicity. -/
theorem pow_mul_truncatedActiveCostNumerator_le_add
    {S : Type} {n : Nat} (step : S -> Fin n -> StopNode S) :
    forall (x : StopNode S) T K,
      n ^ K * truncatedActiveCostNumerator step x T <=
        truncatedActiveCostNumerator step x (T + K) := by
  intro x T K
  induction K with
  | zero => simp
  | succ K ih =>
      calc
        n ^ (K + 1) * truncatedActiveCostNumerator step x T =
            n * (n ^ K * truncatedActiveCostNumerator step x T) := by
          rw [Nat.pow_succ]
          ac_rfl
        _ <= n * truncatedActiveCostNumerator step x (T + K) :=
          Nat.mul_le_mul_left n ih
        _ <= truncatedActiveCostNumerator step x ((T + K) + 1) :=
          mul_truncatedActiveCostNumerator_le_succ step x (T + K)
        _ = truncatedActiveCostNumerator step x (T + (K + 1)) := by
          rw [Nat.add_assoc]

/-- A division-free Bellman supersolution.  `potential` vanishes at both
terminal outcomes, and its one-step decrease pays `scale` units per active
interaction after multiplying the uniform average by `n`.  Nonnegativity is
automatic because the potential is natural-valued. -/
def NatBellmanSuperSolution {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (scale : Nat)
    (potential : StopNode S → Nat) : Prop :=
  potential .success = 0 ∧
    potential .failure = 0 ∧
    ∀ s, scale * n +
      (List.ofFn (fun e : Fin n => potential (step s e))).sum ≤
        n * potential (.active s)

/-- The exact depth-`T` leaf residual at an absorbing success node. -/
theorem treeWeight_success {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (weight : StopNode S → Nat) :
    ∀ T, treeWeight step weight .success T = n ^ T * weight .success := by
  intro T
  induction T with
  | zero => simp [treeWeight]
  | succ T ih =>
      simp only [treeWeight, stepNode]
      rw [show (List.ofFn (fun _ : Fin n =>
        treeWeight step weight .success T)).sum =
          n * treeWeight step weight .success T from ofFn_sum_const n _]
      rw [ih]
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

/-- The exact depth-`T` leaf residual at an absorbing failure node. -/
theorem treeWeight_failure {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (weight : StopNode S → Nat) :
    ∀ T, treeWeight step weight .failure T = n ^ T * weight .failure := by
  intro T
  induction T with
  | zero => simp [treeWeight]
  | succ T ih =>
      simp only [treeWeight, stepNode]
      rw [show (List.ofFn (fun _ : Fin n =>
        treeWeight step weight .failure T)).sum =
          n * treeWeight step weight .failure T from ofFn_sum_const n _]
      rw [ih]
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

/-! ## Lifting one-step terminal balance through the stopped tree -/

/-- If every active state has at least as many immediate success children as
immediate failure children, then the complete finite stopped tree has at least
as much success mass as failure mass at every horizon.  Active children may
change both their state and their future terminal ports arbitrarily.

The proof pairs the terminal imbalance only after summing a whole scheduler
level; it does not require a pointwise success mate for each failure edge. -/
theorem failureCount_le_successCount_of_local_balance
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S)
    (hlocal : ∀ state,
      (List.ofFn (fun edge : Fin n => failureWeight (step state edge))).sum ≤
        (List.ofFn
          (fun edge : Fin n => successWeight (step state edge))).sum) :
    ∀ state T,
      failureCount step (.active state) T ≤
        successCount step (.active state) T := by
  intro state T
  induction T generalizing state with
  | zero => simp [failureCount, successCount, treeWeight,
      failureWeight, successWeight]
  | succ T ih =>
      have hpoint : ∀ edge : Fin n,
          failureCount step (step state edge) T +
              n ^ T * successWeight (step state edge) ≤
            successCount step (step state edge) T +
              n ^ T * failureWeight (step state edge) := by
        intro edge
        cases hchild : step state edge with
        | active child =>
            simpa [failureCount, successCount,
              failureWeight, successWeight] using ih child
        | success =>
            simp [failureCount, successCount, treeWeight_success,
              failureWeight, successWeight]
        | failure =>
            simp [failureCount, successCount, treeWeight_failure,
              failureWeight, successWeight]
      have hsum := ofFn_sum_le
        (fun edge : Fin n =>
          failureCount step (step state edge) T +
            n ^ T * successWeight (step state edge))
        (fun edge : Fin n =>
          successCount step (step state edge) T +
            n ^ T * failureWeight (step state edge)) hpoint
      rw [ofFn_sum_add, ofFn_sum_add, ofFn_sum_mul_left,
        ofFn_sum_mul_left] at hsum
      have hscaled := Nat.mul_le_mul_left (n ^ T) (hlocal state)
      change
        (List.ofFn (fun edge : Fin n =>
          failureCount step (step state edge) T)).sum ≤
        (List.ofFn (fun edge : Fin n =>
          successCount step (step state edge) T)).sum
      omega

/-- Bellman induction with the nonnegative leaf residual retained.  This is
the strongest reusable finite-horizon form: dropping the residual gives the
truncated active-cost bound. -/
theorem truncatedActiveCost_add_treeWeight_le_of_natSuperSolution
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (scale : Nat)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step scale potential) :
    ∀ x T,
      scale * truncatedActiveCostNumerator step x T +
          treeWeight step potential x T ≤
        n ^ T * potential x := by
  intro x T
  induction T generalizing x with
  | zero => simp [truncatedActiveCostNumerator, treeWeight]
  | succ T ih =>
      rcases hsuper with ⟨hsuccess, hfailure, hstep⟩
      cases x with
      | success => simp [truncatedActiveCostNumerator,
          treeWeight_success, hsuccess]
      | failure => simp [truncatedActiveCostNumerator,
          treeWeight_failure, hfailure]
      | active s =>
          have hchildren := ofFn_sum_le
            (fun e : Fin n =>
              scale * truncatedActiveCostNumerator step (step s e) T +
                treeWeight step potential (step s e) T)
            (fun e : Fin n => n ^ T * potential (step s e))
            (fun e => ih (step s e))
          simp only [truncatedActiveCostNumerator, treeWeight]
          calc
            scale * (n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  truncatedActiveCostNumerator step (step s e) T)).sum) +
                (List.ofFn (fun e : Fin n =>
                  treeWeight step potential (step s e) T)).sum =
              n ^ T * (scale * n) +
                (List.ofFn (fun e : Fin n =>
                  scale * truncatedActiveCostNumerator step (step s e) T +
                    treeWeight step potential (step s e) T)).sum := by
                      rw [Nat.mul_add, ofFn_sum_add,
                        ofFn_sum_mul_left]
                      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
                        Nat.mul_assoc, Nat.add_assoc]
            _ ≤ n ^ T * (scale * n) +
                (List.ofFn (fun e : Fin n =>
                  n ^ T * potential (step s e))).sum :=
              Nat.add_le_add_left hchildren _
            _ = n ^ T * (scale * n +
                (List.ofFn (fun e : Fin n => potential (step s e))).sum) := by
              rw [ofFn_sum_mul_left, Nat.mul_add]
            _ ≤ n ^ T * (n * potential (.active s)) :=
              Nat.mul_le_mul_left _ (hstep s)
            _ = n ^ (T + 1) * potential (.active s) := by
              simp [Nat.pow_succ, Nat.mul_assoc]

/-- Every finite-horizon active-cost numerator is bounded by a natural-scaled
Bellman supersolution. -/
theorem truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (scale : Nat)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step scale potential)
    (x : StopNode S) (T : Nat) :
    scale * truncatedActiveCostNumerator step x T ≤
      n ^ T * potential x := by
  have h := truncatedActiveCost_add_treeWeight_le_of_natSuperSolution
    step scale potential hsuper x T
  omega

/-! ## Finite tail charging -/

/-- At every horizon the active leaves form a subfamily of the complete
uniform scheduler tree. -/
theorem activeCount_le_pow {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T : Nat) :
    activeCount step x T ≤ n ^ T := by
  unfold activeCount
  calc
    treeWeight step activeWeight x T ≤ treeWeight step oneWeight x T := by
      apply treeWeight_mono
      intro y
      cases y <;> simp [activeWeight, oneWeight]
    _ = n ^ T := treeWeight_one step x T

/-- A scheduler word still active after `T` draws has paid for all `T`
preceding interactions.  This is the division-free finite-tree tail charge. -/
theorem horizon_mul_activeCount_le_truncatedActiveCostNumerator
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S) :
    ∀ (x : StopNode S) (T : Nat),
      T * activeCount step x T ≤ truncatedActiveCostNumerator step x T := by
  intro x T
  induction T generalizing x with
  | zero => simp [truncatedActiveCostNumerator]
  | succ T ih =>
      cases x with
      | success =>
          unfold activeCount
          rw [treeWeight_success]
          simp [activeWeight, truncatedActiveCostNumerator]
      | failure =>
          unfold activeCount
          rw [treeWeight_failure]
          simp [activeWeight, truncatedActiveCostNumerator]
      | active s =>
          let A := (List.ofFn (fun e : Fin n ↦
            activeCount step (step s e) T)).sum
          let C := (List.ofFn (fun e : Fin n ↦
            truncatedActiveCostNumerator step (step s e) T)).sum
          have htail : T * A ≤ C := by
            calc
              T * A = (List.ofFn (fun e : Fin n ↦
                  T * activeCount step (step s e) T)).sum := by
                    exact (ofFn_sum_mul_left T _).symm
              _ ≤ C := by
                apply ofFn_sum_le
                intro e
                exact ih (step s e)
          have hpow : A ≤ n ^ (T + 1) := by
            calc
              A ≤ (List.ofFn (fun _ : Fin n ↦ n ^ T)).sum := by
                apply ofFn_sum_le
                intro e
                exact activeCount_le_pow step (step s e) T
              _ = n * n ^ T := ofFn_sum_const n _
              _ = n ^ (T + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
          change (T + 1) * A ≤ n ^ (T + 1) + C
          rw [Nat.add_mul]
          omega

/-- Division-free Markov inequality at probability threshold `1/2`. -/
theorem two_mul_le_of_scaled_delay
    {L miss delay den num total : Nat}
    (hL : 0 < L) (hden : 0 < den)
    (hcharge : L * miss ≤ delay)
    (hdelay : den * delay ≤ num * total)
    (hscale : 2 * num ≤ L * den) :
    2 * miss ≤ total := by
  have hmul : (L * den) * (2 * miss) ≤ (L * den) * total := by
    calc
      (L * den) * (2 * miss) = (2 * den) * (L * miss) := by ac_rfl
      _ ≤ (2 * den) * delay := Nat.mul_le_mul_left _ hcharge
      _ = 2 * (den * delay) := by ac_rfl
      _ ≤ 2 * (num * total) := Nat.mul_le_mul_left 2 hdelay
      _ = (2 * num) * total := by ac_rfl
      _ ≤ (L * den) * total := Nat.mul_le_mul_right total hscale
  exact Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos hL hden)

/-- A scaled finite-horizon active-cost bound gives a one-block half-tail at
the same horizon whenever the chosen horizon pays twice the cost scale. -/
theorem two_mul_activeCount_le_pow_of_scaled_cost
    {S : Type} {n den num L : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S)
    (hL : 0 < L) (hden : 0 < den)
    (hcost : den * truncatedActiveCostNumerator step x L ≤ num * n ^ L)
    (hscale : 2 * num ≤ L * den) :
    2 * activeCount step x L ≤ n ^ L := by
  exact two_mul_le_of_scaled_delay hL hden
    (horizon_mul_activeCount_le_truncatedActiveCostNumerator step x L)
    hcost hscale

end FiniteUniformStoppingTree

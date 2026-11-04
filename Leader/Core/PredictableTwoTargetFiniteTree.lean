import Leader.Core.FiniteUniformStoppingTree

/-!
# Predictable one- and two-target finite scheduler trees

This module supplies division-free scheduler-count bounds for targets chosen
from the complete current history.  A target may change after every irrelevant
edge; the only requirement is that the one or two current targets are fixed
before the next scheduler choice is made.

The single-target tree has truncated expected service cost at most `n`.  For
two distinct targets, the two first-hit types have exactly equal count at every
horizon, while the unresolved count at horizon `2*n` is at most one quarter of
the scheduler space.  Thus either named first-hit type occurs by `2*n` on at
least three eighths of all schedules (and hence on at least one quarter).

The final section gives endpoint union bounds and state-uniform sequential
composition.  These are literal natural-number scheduler-count statements;
they use neither event independence nor a probability-space API.
-/

namespace PredictableTwoTargetFiniteTree

set_option autoImplicit false

open FiniteUniformStoppingTree

/-! ## Finite-sum bookkeeping -/

private theorem sum_map_const {A : Type} (xs : List A) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons _ xs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons]
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

private theorem nodup_ofFn_fin (n : Nat) :
    (List.ofFn (fun i : Fin n => i)).Nodup :=
  nodup_ofFn_of_injective (fun i : Fin n => i) (fun _ _ h => h)

/-- Removing one distinguished zero entry from a constant `Fin n` sum leaves
exactly `n-1` copies of the constant. -/
theorem ofFn_sum_zero_one_else_const {n : Nat} (a : Fin n)
    (f : Fin n → Nat) (c : Nat) (ha : f a = 0)
    (hother : ∀ e, e ≠ a → f e = c) :
    (List.ofFn f).sum = (n - 1) * c := by
  have h := sum_one_exception
    (List.ofFn (fun i : Fin n => i)) a f c (nodup_ofFn_fin n)
    (by rw [List.mem_ofFn]; exact ⟨a, rfl⟩)
    (by
      intro z _ hza
      exact hother z hza)
  simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn, ha,
    Nat.zero_add] using h

/-- Exact sum with one distinguished value and a constant value on every
other scheduler edge. -/
theorem ofFn_sum_one_value_else_const {n : Nat} (a : Fin n)
    (f : Fin n → Nat) (c : Nat)
    (hother : ∀ e, e ≠ a → f e = c) :
    (List.ofFn f).sum = f a + (n - 1) * c := by
  have h := sum_one_exception
    (List.ofFn (fun i : Fin n => i)) a f c (nodup_ofFn_fin n)
    (by rw [List.mem_ofFn]; exact ⟨a, rfl⟩)
    (by intro e _ he; exact hother e he)
  simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using h

/-- Exact sum with two distinguished values and a constant value on every
other scheduler edge. -/
theorem ofFn_sum_two_values_else_const {n : Nat} (a b : Fin n)
    (f : Fin n → Nat) (c : Nat) (hab : a ≠ b)
    (hother : ∀ e, e ≠ a → e ≠ b → f e = c) :
    (List.ofFn f).sum = f a + f b + (n - 2) * c := by
  have h := FiniteUniformStoppingTree.sum_two_exceptions
    (List.ofFn (fun i : Fin n => i)) a b f c (nodup_ofFn_fin n)
    (by rw [List.mem_ofFn]; exact ⟨a, rfl⟩)
    (by rw [List.mem_ofFn]; exact ⟨b, rfl⟩) hab
    (by intro e _ hea heb; exact hother e hea heb)
  simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using h

private theorem sum_map_add_eq_of_one_exception
    {A : Type} [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (f g : A → Nat) (left right : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hatarget : f a + left = g a + right)
    (hother : ∀ z, z ∈ xs → z ≠ a → f z = g z) :
    (xs.map f).sum + left = (xs.map g).sum + right := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hall : xs.map f = xs.map g := by
          apply List.map_congr_left
          intro z hz
          exact hother z (by simp [hz]) (by
            intro hza
            subst z
            exact hnodup.1 hz)
        simp only [List.map_cons, List.sum_cons, hall]
        omega
      · have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with h | h
          · exact False.elim (hxa h.symm)
          · exact h
        have hx : f x = g x := hother x (by simp) hxa
        simp only [List.map_cons, List.sum_cons, hx]
        have ht := ih hnodup.2 hat (by
          intro z hz
          exact hother z (by simp [hz]))
        omega

/-- Two functions have equal complete `Fin n` sums when they agree away from
two entries and exchange their values at those entries. -/
private theorem sum_map_eq_of_swap_two
    {A : Type} [BEq A] [LawfulBEq A]
    (xs : List A) (a b : A) (f g : A → Nat)
    (hnodup : xs.Nodup) (haMem : a ∈ xs) (hbMem : b ∈ xs)
    (hab : a ≠ b) (ha : f a = g b) (hb : f b = g a)
    (hother : ∀ e, e ∈ xs → e ≠ a → e ≠ b → f e = g e) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => simp at haMem
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hbTail : b ∈ xs := by
          rcases List.mem_cons.mp hbMem with h | h
          · exact False.elim (hab h.symm)
          · exact h
        have hcomp := sum_map_add_eq_of_one_exception xs b f g
          (f a) (g a) hnodup.2 hbTail (by rw [hb, ha]; omega) (by
            intro z hz hzb
            exact hother z (by simp [hz]) (by
              intro hza
              subst z
              exact hnodup.1 hz) hzb)
        simp only [List.map_cons, List.sum_cons]
        omega
      · by_cases hxb : x = b
        · subst x
          have haTail : a ∈ xs := by
            rcases List.mem_cons.mp haMem with h | h
            · exact False.elim (hxa h.symm)
            · exact h
          have hcomp := sum_map_add_eq_of_one_exception xs a f g
            (f b) (g b) hnodup.2 haTail (by rw [ha, hb]; omega) (by
              intro z hz hza
              exact hother z (by simp [hz]) hza (by
                intro hzb
                subst z
                exact hnodup.1 hz))
          simp only [List.map_cons, List.sum_cons]
          omega
        · have haTail : a ∈ xs := by
            rcases List.mem_cons.mp haMem with h | h
            · exact False.elim (hxa h.symm)
            · exact h
          have hbTail : b ∈ xs := by
            rcases List.mem_cons.mp hbMem with h | h
            · exact False.elim (hxb h.symm)
            · exact h
          have hi := ih hnodup.2 haTail hbTail (by
            intro e he hea heb
            exact hother e (by simp [he]) hea heb)
          have hx : f x = g x := hother x (by simp) hxa hxb
          simp only [List.map_cons, List.sum_cons, hx, hi]

theorem ofFn_sum_eq_of_swap_two {n : Nat} (a b : Fin n)
    (f g : Fin n → Nat) (hab : a ≠ b)
    (ha : f a = g b) (hb : f b = g a)
    (hother : ∀ e, e ≠ a → e ≠ b → f e = g e) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  simpa only [List.map_ofFn, Function.comp_def] using
    sum_map_eq_of_swap_two (List.ofFn (fun i : Fin n => i)) a b f g
      (nodup_ofFn_fin n)
      (by simp [List.mem_ofFn]) (by simp [List.mem_ofFn]) hab ha hb
      (by intro e _; exact hother e)

/-! ## Generic active-cost tail lemma -/

/-- Every still-active depth-`T` leaf has paid all `T` active interactions.
This is the pathwise half of finite-horizon Markov, stated on exact counts. -/
theorem horizon_mul_activeCount_le_truncatedActiveCost
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S) :
    ∀ x T,
      T * activeCount step x T ≤ truncatedActiveCostNumerator step x T := by
  intro x T
  induction T generalizing x with
  | zero => simp [activeCount, truncatedActiveCostNumerator]
  | succ T ih =>
      cases x with
      | success =>
          simp [activeCount, truncatedActiveCostNumerator,
            treeWeight_success, activeWeight]
      | failure =>
          simp [activeCount, truncatedActiveCostNumerator,
            treeWeight_failure, activeWeight]
      | active s =>
          have hchildren := ofFn_sum_le
            (fun e : Fin n ↦
              T * activeCount step (step s e) T)
            (fun e : Fin n ↦
              truncatedActiveCostNumerator step (step s e) T)
            (fun e ↦ ih (step s e))
          rw [ofFn_sum_mul_left] at hchildren
          have hactive : activeCount step (.active s) (T + 1) ≤
              n ^ (T + 1) := by
            unfold activeCount
            have hm := treeWeight_mono step activeWeight oneWeight
              (by intro y; cases y <;> simp [activeWeight, oneWeight])
              (.active s) (T + 1)
            rw [treeWeight_one] at hm
            exact hm
          simp only [activeCount, treeWeight,
            stepNode, truncatedActiveCostNumerator] at hchildren ⊢
          simp only [activeCount, treeWeight, stepNode] at hactive
          rw [Nat.add_mul, Nat.one_mul]
          omega

/-! ## One predictable current target -/

/-- Stop successfully when the current predictable target is selected;
otherwise update the payload and choose the next target from the new state. -/
def oneTargetStep {S : Type} {n : Nat} (target : S → Fin n)
    (next : S → Fin n → S) (s : S) (e : Fin n) : StopNode S :=
  if e = target s then .success else .active (next s e)

private def oneTargetPotential {S : Type} (n : Nat) : StopNode S → Nat
  | .active _ => n
  | .success => 0
  | .failure => 0

/-- The constant active potential `n` is a Bellman supersolution of scale one
for predictable service of a single current target. -/
theorem oneTarget_natBellmanSuperSolution
    {S : Type} {n : Nat} (target : S → Fin n)
    (next : S → Fin n → S) :
    NatBellmanSuperSolution (oneTargetStep target next) 1
      (oneTargetPotential n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have hsum :
      (List.ofFn (fun e : Fin n ↦
        oneTargetPotential n (oneTargetStep target next s e))).sum =
        (n - 1) * n := by
    apply ofFn_sum_zero_one_else_const (target s)
    · simp [oneTargetStep, oneTargetPotential]
    · intro e he
      simp [oneTargetStep, oneTargetPotential, he]
  simp only [oneTargetPotential]
  change 1 * n +
      (List.ofFn (fun e : Fin n ↦
        oneTargetPotential n (oneTargetStep target next s e))).sum ≤ n * n
  rw [hsum]
  have hn : 0 < n := by
    have := (target s).isLt
    omega
  have hpred := pred_mul n n hn
  exact Nat.le_of_eq (by simpa using hpred.symm)

/-- Division-free truncated expectation bound for one predictable target:
the active-cost numerator is at most `n` times the scheduler-space size. -/
theorem oneTarget_truncatedCost_le
    {S : Type} {n : Nat} (target : S → Fin n)
    (next : S → Fin n → S) (s : S) (T : Nat) :
    truncatedActiveCostNumerator (oneTargetStep target next) (.active s) T ≤
      n ^ T * n := by
  simpa [oneTargetPotential] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (oneTargetStep target next) 1 (oneTargetPotential n)
      (oneTarget_natBellmanSuperSolution target next) (.active s) T

/-- A one-target service tree has no failure leaves. -/
theorem oneTarget_failureCount_eq_zero
    {S : Type} {n : Nat} (target : S → Fin n)
    (next : S → Fin n → S) :
    ∀ s T,
      failureCount (oneTargetStep target next) (.active s) T = 0 := by
  intro s T
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount, treeWeight, stepNode]
      calc
        (List.ofFn (fun e : Fin n => treeWeight
            (oneTargetStep target next) failureWeight
            (oneTargetStep target next s e) T)).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro e
              by_cases he : e = target s
              · simp [oneTargetStep, he, treeWeight_success, failureWeight]
              · simpa [oneTargetStep, he, failureCount] using ih (next s e)
        _ = 0 := by rw [ofFn_sum_const]; simp

/-- Markov at horizon `2*n`: at least half of all scheduler words have already
served the predictable current target. -/
theorem oneTarget_success_half_by_two_mul
    {S : Type} {n : Nat} (target : S → Fin n)
    (next : S → Fin n → S) (s : S) :
    n ^ (2 * n) ≤
      2 * successCount (oneTargetStep target next) (.active s) (2 * n) := by
  let step := oneTargetStep target next
  have hcost := oneTarget_truncatedCost_le target next s (2 * n)
  have hlive := horizon_mul_activeCount_le_truncatedActiveCost
    step (.active s) (2 * n)
  have hscaled : n * (2 * activeCount step (.active s) (2 * n)) ≤
      n * n ^ (2 * n) := by
    calc
      n * (2 * activeCount step (.active s) (2 * n)) =
          (2 * n) * activeCount step (.active s) (2 * n) := by ac_rfl
      _ ≤ truncatedActiveCostNumerator step (.active s) (2 * n) := hlive
      _ ≤ n ^ (2 * n) * n := hcost
      _ = n * n ^ (2 * n) := by ac_rfl
  have hn : 0 < n := by
    have := (target s).isLt
    omega
  have hhalf : 2 * activeCount step (.active s) (2 * n) ≤
      n ^ (2 * n) := Nat.le_of_mul_le_mul_left hscaled hn
  have hpartition := node_count_partition step (.active s) (2 * n)
  have hfailure := oneTarget_failureCount_eq_zero target next s (2 * n)
  dsimp [step] at hhalf hpartition
  rw [hfailure] at hpartition
  omega

/-! ## Two distinct predictable current targets -/

/-- Stop at the first selection of either current target, recording the first
target as success and the second as failure. -/
def twoTargetStep {S : Type} {n : Nat} (first second : S → Fin n)
    (next : S → Fin n → S) (s : S) (e : Fin n) : StopNode S :=
  if e = first s then .success
  else if e = second s then .failure
  else .active (next s e)

private def twoTargetPotential {S : Type} (n : Nat) : StopNode S → Nat
  | .active _ => n
  | .success => 0
  | .failure => 0

/-- With two distinct current targets, the constant active potential `n` pays
two units of active time per raw scheduler interaction. -/
theorem twoTarget_natBellmanSuperSolution
    {S : Type} {n : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) :
    NatBellmanSuperSolution (twoTargetStep first second next) 2
      (twoTargetPotential n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have hsum :
      (List.ofFn (fun e : Fin n ↦
        twoTargetPotential n (twoTargetStep first second next s e))).sum =
        (n - 2) * n := by
    have h := sum_two_exceptions
      (List.ofFn (fun i : Fin n => i)) (first s) (second s)
      (fun e ↦ twoTargetPotential n
        (twoTargetStep first second next s e)) n
      (nodup_ofFn_fin n)
      (by rw [List.mem_ofFn]; exact ⟨first s, rfl⟩)
      (by rw [List.mem_ofFn]; exact ⟨second s, rfl⟩)
      (hdistinct s) (by
        intro e _ hef hes
        simp [twoTargetStep, twoTargetPotential, hef, hes])
    simpa [twoTargetStep, twoTargetPotential, hdistinct s,
      (hdistinct s).symm, List.map_ofFn, Function.comp_def] using h
  simp only [twoTargetPotential]
  change 2 * n +
      (List.ofFn (fun e : Fin n ↦
        twoTargetPotential n (twoTargetStep first second next s e))).sum ≤ n * n
  rw [hsum]
  have hn : 0 < n := by
    have := (first s).isLt
    omega
  have hn1 : n ≠ 1 := by
    intro heq
    apply hdistinct s
    apply Fin.ext
    have hf := (first s).isLt
    have hs := (second s).isLt
    omega
  have hn2 : 2 ≤ n := by omega
  have hpred1 := pred_mul n n hn
  have hpred2 := pred_mul (n - 1) n (by omega)
  have hsub : n - 1 - 1 = n - 2 := by omega
  rw [hsub] at hpred2
  omega

/-- Division-free truncated expectation bound for the first of two predictable
targets: twice the cost numerator is at most `n` times scheduler-space size. -/
theorem twoTarget_two_mul_truncatedCost_le
    {S : Type} {n : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) (s : S) (T : Nat) :
    2 * truncatedActiveCostNumerator (twoTargetStep first second next)
        (.active s) T ≤ n ^ T * n := by
  simpa [twoTargetPotential] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (twoTargetStep first second next) 2 (twoTargetPotential n)
      (twoTarget_natBellmanSuperSolution first second next hdistinct)
      (.active s) T

/-- At every finite horizon, the two possible first-hit types have exactly the
same scheduler count, even though both targets may adapt after irrelevant
draws. -/
theorem twoTarget_successCount_eq_failureCount
    {S : Type} {n : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) :
    ∀ s T,
      successCount (twoTargetStep first second next) (.active s) T =
        failureCount (twoTargetStep first second next) (.active s) T := by
  intro s T
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
      simp only [successCount, failureCount, treeWeight]
      apply ofFn_sum_eq_of_swap_two (first s) (second s)
      · exact hdistinct s
      · simp only [stepNode]
        rw [show twoTargetStep first second next s (first s) = .success by
          simp [twoTargetStep]]
        rw [show twoTargetStep first second next s (second s) = .failure by
          simp [twoTargetStep, (hdistinct s).symm]]
        rw [treeWeight_success, treeWeight_failure]
        rfl
      · simp only [stepNode]
        rw [show twoTargetStep first second next s (second s) = .failure by
          simp [twoTargetStep, (hdistinct s).symm]]
        rw [show twoTargetStep first second next s (first s) = .success by
          simp [twoTargetStep]]
        rw [treeWeight_failure, treeWeight_success]
        rfl
      · intro e hef hes
        simp only [stepNode]
        rw [show twoTargetStep first second next s e = .active (next s e) by
          simp [twoTargetStep, hef, hes]]
        exact ih (next s e)

/-- Markov at horizon `2*n`: at most one quarter of scheduler words have not
yet selected either predictable target. -/
theorem twoTarget_four_mul_activeCount_le_by_two_mul
    {S : Type} {n : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) (s : S) :
    4 * activeCount (twoTargetStep first second next) (.active s) (2 * n) ≤
      n ^ (2 * n) := by
  let step := twoTargetStep first second next
  have hcost := twoTarget_two_mul_truncatedCost_le
    first second next hdistinct s (2 * n)
  have hlive := horizon_mul_activeCount_le_truncatedActiveCost
    step (.active s) (2 * n)
  have hscaledLive := Nat.mul_le_mul_left 2 hlive
  have hcancel : n * (4 * activeCount step (.active s) (2 * n)) ≤
      n * n ^ (2 * n) := by
    calc
      n * (4 * activeCount step (.active s) (2 * n)) =
          2 * ((2 * n) * activeCount step (.active s) (2 * n)) := by
            rw [show 4 = 2 * 2 by decide]
            ac_rfl
      _ ≤ 2 * truncatedActiveCostNumerator step (.active s) (2 * n) :=
        hscaledLive
      _ ≤ n ^ (2 * n) * n := hcost
      _ = n * n ^ (2 * n) := by ac_rfl
  have hn : 0 < n := by
    have := (first s).isLt
    omega
  exact Nat.le_of_mul_le_mul_left hcancel hn

/-- Each named first-hit type occurs within `2*n` on at least three eighths
of all scheduler words.  The centered block only needs the weaker quarter. -/
theorem twoTarget_first_success_three_eighths_by_two_mul
    {S : Type} {n : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) (s : S) :
    3 * n ^ (2 * n) ≤
      8 * successCount (twoTargetStep first second next)
        (.active s) (2 * n) := by
  let step := twoTargetStep first second next
  have hactive := twoTarget_four_mul_activeCount_le_by_two_mul
    first second next hdistinct s
  have heq := twoTarget_successCount_eq_failureCount
    first second next hdistinct s (2 * n)
  have hpartition := node_count_partition step (.active s) (2 * n)
  dsimp [step] at hactive heq hpartition ⊢
  omega

/-- Quarter-strength wrapper used directly by the `1/4` firing stage. -/
theorem twoTarget_first_success_quarter_by_two_mul
    {S : Type} {n : Nat} (first second : S → Fin n)
    (next : S → Fin n → S)
    (hdistinct : ∀ s, first s ≠ second s) (s : S) :
    n ^ (2 * n) ≤
      4 * successCount (twoTargetStep first second next)
        (.active s) (2 * n) := by
  have h := twoTarget_first_success_three_eighths_by_two_mul
    first second next hdistinct s
  omega

/-! ## Plain endpoint counts and finite union bounds -/

/-- A nonabsorbing transition embedded in the stopping-tree API. -/
def plainStep {S : Type} {n : Nat} (next : S → Fin n → S)
    (s : S) (e : Fin n) : StopNode S := .active (next s e)

/-- Lift a state observable to active nodes of a plain tree. -/
def activeStateWeight {S : Type} (value : S → Nat) : StopNode S → Nat
  | .active s => value s
  | .success => 0
  | .failure => 0

/-- Exact sum of a state observable over all depth-`T` scheduler words. -/
def stateTreeTotal {S : Type} {n : Nat} (next : S → Fin n → S)
    (value : S → Nat) (s : S) (T : Nat) : Nat :=
  treeWeight (plainStep next) (activeStateWeight value) (.active s) T

/-- Exact count of depth-`T` endpoints satisfying a Boolean predicate. -/
def endpointCount {S : Type} {n : Nat} (next : S → Fin n → S)
    (good : S → Bool) (s : S) (T : Nat) : Nat :=
  stateTreeTotal next (fun x => if good x then 1 else 0) s T

theorem stateTreeTotal_zero {S : Type} {n : Nat}
    (next : S → Fin n → S) (value : S → Nat) (s : S) :
    stateTreeTotal next value s 0 = value s := rfl

theorem stateTreeTotal_succ {S : Type} {n : Nat}
    (next : S → Fin n → S) (value : S → Nat) (s : S) (T : Nat) :
    stateTreeTotal next value s (T + 1) =
      (List.ofFn (fun e : Fin n =>
        stateTreeTotal next value (next s e) T)).sum := rfl

/-- Running `T+U` raw choices is the depth-`T` tree whose leaf observable is
the complete depth-`U` continuation sum. -/
theorem stateTreeTotal_add_horizon {S : Type} {n : Nat}
    (next : S → Fin n → S) (value : S → Nat) (s : S) (T U : Nat) :
    stateTreeTotal next value s (T + U) =
      stateTreeTotal next (fun x => stateTreeTotal next value x U) s T := by
  induction T generalizing s with
  | zero => simp [stateTreeTotal_zero]
  | succ T ih =>
      simp only [Nat.succ_add, stateTreeTotal_succ]
      apply ofFn_sum_eq
      intro e
      exact ih (next s e)

/-- Pointwise domination lifts to every plain scheduler tree. -/
theorem stateTreeTotal_mono {S : Type} {n : Nat}
    (next : S → Fin n → S) (value upper : S → Nat)
    (hle : ∀ s, value s ≤ upper s) (s : S) (T : Nat) :
    stateTreeTotal next value s T ≤ stateTreeTotal next upper s T := by
  unfold stateTreeTotal
  exact treeWeight_mono (plainStep next) (activeStateWeight value)
    (activeStateWeight upper) (by
      intro x
      cases x with
      | active s => exact hle s
      | success => simp [activeStateWeight]
      | failure => simp [activeStateWeight]) (.active s) T

/-- Scaling an endpoint observable scales its exact tree sum. -/
theorem stateTreeTotal_mul_left {S : Type} {n : Nat}
    (next : S → Fin n → S) (a : Nat) (value : S → Nat)
    (s : S) (T : Nat) :
    stateTreeTotal next (fun x => a * value x) s T =
      a * stateTreeTotal next value s T := by
  unfold stateTreeTotal
  rw [show activeStateWeight (fun x => a * value x) =
      (fun y => a * activeStateWeight value y) by
    funext y
    cases y <;> rfl]
  exact treeWeight_mul_left (plainStep next) a (activeStateWeight value)
    (.active s) T

/-- The exact size of every plain depth-`T` scheduler tree is `n^T`. -/
theorem endpointCount_true {S : Type} {n : Nat}
    (next : S → Fin n → S) (s : S) (T : Nat) :
    endpointCount next (fun _ => true) s T = n ^ T := by
  unfold endpointCount
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
      rw [stateTreeTotal_succ]
      calc
        (List.ofFn (fun e : Fin n => stateTreeTotal next
            (fun _ => 1) (next s e) T)).sum =
            (List.ofFn (fun _ : Fin n => n ^ T)).sum := by
              apply ofFn_sum_eq
              intro e
              exact ih (next s e)
        _ = n * n ^ T := ofFn_sum_const n _
        _ = n ^ (T + 1) := by simp [Nat.pow_succ, Nat.mul_comm]

/-- Denominator-cleared finite union bound for endpoint predicates. -/
theorem endpointCount_union_bound {S : Type} {n : Nat}
    (next : S → Fin n → S) (left right : S → Bool)
    (s : S) (T : Nat) :
    endpointCount next left s T + endpointCount next right s T ≤
      n ^ T + endpointCount next (fun x => left x && right x) s T := by
  let il : S → Nat := fun x => if left x then 1 else 0
  let ir : S → Nat := fun x => if right x then 1 else 0
  let ii : S → Nat := fun x => if left x && right x then 1 else 0
  have hpoint : ∀ x, il x + ir x ≤ 1 + ii x := by
    intro x
    simp only [il, ir, ii]
    cases hleft : left x <;> cases hright : right x <;>
      simp
  have htree := stateTreeTotal_mono next
    (fun x => il x + ir x) (fun x => 1 + ii x) hpoint s T
  rw [show stateTreeTotal next (fun x => il x + ir x) s T =
      stateTreeTotal next il s T + stateTreeTotal next ir s T by
    unfold stateTreeTotal
    rw [show activeStateWeight (fun x => il x + ir x) =
        (fun y => activeStateWeight il y + activeStateWeight ir y) by
      funext y
      cases y <;> rfl]
    exact treeWeight_add _ _ _ _ _] at htree
  rw [show stateTreeTotal next (fun x => 1 + ii x) s T =
      stateTreeTotal next (fun _ => 1) s T + stateTreeTotal next ii s T by
    unfold stateTreeTotal
    rw [show activeStateWeight (fun x => 1 + ii x) =
        (fun y => activeStateWeight (fun _ => 1) y +
          activeStateWeight ii y) by
      funext y
      cases y <;> rfl]
    exact treeWeight_add _ _ _ _ _] at htree
  dsimp [il, ir, ii] at htree
  change endpointCount next left s T + endpointCount next right s T ≤
    stateTreeTotal next (fun _ => 1) s T +
      endpointCount next (fun x => left x && right x) s T at htree
  have hone : stateTreeTotal next (fun _ => 1) s T = n ^ T := by
    simpa [endpointCount] using endpointCount_true next s T
  rwa [hone] at htree

/-- The `1/2 + 3/4 - 1 = 1/4` union-bound arithmetic used for both the firing
and bullet-race stages. -/
theorem endpointCount_intersection_quarter_of_half_three_quarters
    {S : Type} {n : Nat} (next : S → Fin n → S)
    (left right : S → Bool) (s : S) (T : Nat)
    (hhalf : n ^ T ≤ 2 * endpointCount next left s T)
    (hthree : 3 * n ^ T ≤ 4 * endpointCount next right s T) :
    n ^ T ≤
      4 * endpointCount next (fun x => left x && right x) s T := by
  have hu := endpointCount_union_bound next left right s T
  omega

/-! ## State-uniform sequential composition -/

/-- Multiply two state-uniform endpoint-count lower bounds.  The second bound
is assumed at every first-stage favorable endpoint, so conditioning on the
complete first-stage history is built into the theorem. -/
theorem endpointCount_compose
    {S : Type} {n d₁ d₂ : Nat} (next : S → Fin n → S)
    (middle final : S → Bool) (s : S) (T U : Nat)
    (hfirst : n ^ T ≤ d₁ * endpointCount next middle s T)
    (hsecond : ∀ x, middle x = true →
      n ^ U ≤ d₂ * endpointCount next final x U) :
    n ^ (T + U) ≤
      (d₁ * d₂) * endpointCount next final s (T + U) := by
  let middleWeight : S → Nat := fun x => if middle x then 1 else 0
  let finalWeight : S → Nat := fun x => if final x then 1 else 0
  have hpoint : ∀ x,
      n ^ U * middleWeight x ≤
        d₂ * stateTreeTotal next finalWeight x U := by
    intro x
    cases hx : middle x
    · simp [middleWeight, hx]
    · rw [show middleWeight x = 1 by simp [middleWeight, hx]]
      simpa [finalWeight, endpointCount] using hsecond x hx
  have htree := stateTreeTotal_mono next
    (fun x => n ^ U * middleWeight x)
    (fun x => d₂ * stateTreeTotal next finalWeight x U)
    hpoint s T
  rw [stateTreeTotal_mul_left, stateTreeTotal_mul_left] at htree
  have hscaledFirst := Nat.mul_le_mul_left (n ^ U) hfirst
  have hscaledTree := Nat.mul_le_mul_left d₁ htree
  change n ^ T ≤ d₁ * stateTreeTotal next middleWeight s T at hfirst
  change n ^ U * n ^ T ≤
    n ^ U * (d₁ * stateTreeTotal next middleWeight s T) at hscaledFirst
  change d₁ * (n ^ U * stateTreeTotal next middleWeight s T) ≤
    d₁ * (d₂ * stateTreeTotal next
      (fun x => stateTreeTotal next finalWeight x U) s T) at hscaledTree
  unfold endpointCount
  rw [stateTreeTotal_add_horizon]
  change n ^ (T + U) ≤
    (d₁ * d₂) * stateTreeTotal next
      (fun x => stateTreeTotal next finalWeight x U) s T
  calc
    n ^ (T + U) = n ^ U * n ^ T := by
      rw [Nat.pow_add]
      ac_rfl
    _ ≤ n ^ U * (d₁ * stateTreeTotal next middleWeight s T) :=
      hscaledFirst
    _ = d₁ * (n ^ U * stateTreeTotal next middleWeight s T) := by
      ac_rfl
    _ ≤ d₁ * (d₂ * stateTreeTotal next
        (fun x => stateTreeTotal next finalWeight x U) s T) := hscaledTree
    _ = (d₁ * d₂) * stateTreeTotal next
        (fun x => stateTreeTotal next finalWeight x U) s T := by ac_rfl

/-- Direct scheduler-count form of the centered block constants
`(1/2)*(1/4)*(1/4)=1/32`. -/
theorem endpointCount_compose_half_quarter_quarter
    {S : Type} {n : Nat} (next : S → Fin n → S)
    (stage₁ stage₂ final : S → Bool) (s : S) (T₁ T₂ T₃ : Nat)
    (h₁ : n ^ T₁ ≤ 2 * endpointCount next stage₁ s T₁)
    (h₂ : ∀ x, stage₁ x = true →
      n ^ T₂ ≤ 4 * endpointCount next stage₂ x T₂)
    (h₃ : ∀ x, stage₂ x = true →
      n ^ T₃ ≤ 4 * endpointCount next final x T₃) :
    n ^ (T₁ + T₂ + T₃) ≤
      32 * endpointCount next final s (T₁ + T₂ + T₃) := by
  have h₁₂ := endpointCount_compose next stage₁ stage₂ s T₁ T₂ h₁ h₂
  have h123 := endpointCount_compose next stage₂ final s
    (T₁ + T₂) T₃ (d₁ := 2 * 4) (d₂ := 4) h₁₂ h₃
  change n ^ (T₁ + T₂ + T₃) ≤
    32 * endpointCount next final s (T₁ + T₂ + T₃) at h123
  exact h123

#print axioms oneTarget_truncatedCost_le
#print axioms oneTarget_success_half_by_two_mul
#print axioms twoTarget_successCount_eq_failureCount
#print axioms twoTarget_first_success_quarter_by_two_mul
#print axioms endpointCount_intersection_quarter_of_half_three_quarters
#print axioms endpointCount_compose_half_quarter_quarter

end PredictableTwoTargetFiniteTree

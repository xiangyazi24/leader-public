import Leader.Core.ControlledSchedulerMass
import Leader.PPL.Probability.RestartCost
import Leader.Wu.Scheduler.FixedSpanRenewalPayload

/-!
Protocol-independent finite counting for the local-deletion proof.
All numerators count complete scheduler words, including terminal padding.
-/

namespace PPL.Convergence.LDLocal

open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

variable {S : Type} {n : Nat}

/-! ## Adaptive variable-weight change of measure -/

/-- Terminal failures have zero weight; every other endpoint contributes its
integer likelihood weight. -/
def powSuccessOrActive : StopNode S → Nat → Nat
  | .failure, _ => 0
  | .success, k => 2 ^ k
  | .active _, k => 2 ^ k

/-- Sum over complete controlled words. `wordSum` enumerates the same uniform
word space in reverse-generation order so that first-letter recursion is
available; each word still occurs exactly once. -/
def weightedQNonRetryNumerator
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (fun w =>
    powSuccessOrActive
      (ControlledSchedulerMass.runWord
        (ControlledSchedulerMass.controlledStep step r) x w)
      (T - ControlledSchedulerMass.eventCount
        (ControlledSchedulerMass.controlledStep step r) r x w))

/-- The same integer likelihood weight restricted to success leaves. -/
def powSuccessOnly : StopNode S → Nat → Nat
  | .success, k => 2 ^ k
  | _, _ => 0

/-- Controlled success-word sum with the path-dependent likelihood weight. -/
def weightedQSuccessNumerator
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (fun w =>
    powSuccessOnly
      (ControlledSchedulerMass.runWord
        (ControlledSchedulerMass.controlledStep step r) x w)
      (T - ControlledSchedulerMass.eventCount
        (ControlledSchedulerMass.controlledStep step r) r x w))

private theorem eventCost_le_one
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (e : Fin n) :
    ControlledSchedulerMass.eventCost r x e ≤ 1 := by
  cases x with
  | active s => simp [ControlledSchedulerMass.eventCost]; split <;> omega
  | success => simp [ControlledSchedulerMass.eventCost]
  | failure => simp [ControlledSchedulerMass.eventCost]

private theorem eventCount_le_length
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (w : List (Fin n)) :
    ControlledSchedulerMass.eventCount step r x w ≤ w.length := by
  induction w generalizing x with
  | nil => simp [ControlledSchedulerMass.eventCount]
  | cons e es ih =>
      simp only [ControlledSchedulerMass.eventCount, List.length_cons]
      have hc := eventCost_le_one r x e
      have ht := ih (stepNode step x e)
      omega

private theorem sum_map_mul_left {X : Type} (xs : List X)
    (c : Nat) (f : X → Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

private theorem wordSum_weighted_succ
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (weight : StopNode S → Nat → Nat)
    (hdouble : ∀ x k, weight x (k + 1) = 2 * weight x k)
    (x : StopNode S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n (T + 1) (fun w =>
      weight (ControlledSchedulerMass.runWord
        (ControlledSchedulerMass.controlledStep step r) x w)
        (T + 1 - ControlledSchedulerMass.eventCount
          (ControlledSchedulerMass.controlledStep step r) r x w)) =
      (List.ofFn (fun e : Fin n =>
        (if ControlledSchedulerMass.eventCost r x e = 1 then 1 else 2) *
          FixedSpanRenewalPayload.wordSum n T (fun w =>
            weight (ControlledSchedulerMass.runWord
              (ControlledSchedulerMass.controlledStep step r)
              (stepNode (ControlledSchedulerMass.controlledStep step r) x e) w)
              (T - ControlledSchedulerMass.eventCount
                (ControlledSchedulerMass.controlledStep step r) r
                (stepNode (ControlledSchedulerMass.controlledStep step r) x e) w)))).sum := by
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply ofFn_sum_eq
  intro e
  let y := stepNode (ControlledSchedulerMass.controlledStep step r) x e
  let c := if ControlledSchedulerMass.eventCost r x e = 1 then 1 else 2
  change FixedSpanRenewalPayload.wordSum n T (fun w =>
      weight (ControlledSchedulerMass.runWord
        (ControlledSchedulerMass.controlledStep step r) x (e :: w))
        (T + 1 - ControlledSchedulerMass.eventCount
          (ControlledSchedulerMass.controlledStep step r) r x (e :: w))) =
    c * FixedSpanRenewalPayload.wordSum n T (fun w =>
      weight (ControlledSchedulerMass.runWord
        (ControlledSchedulerMass.controlledStep step r) y w)
        (T - ControlledSchedulerMass.eventCount
          (ControlledSchedulerMass.controlledStep step r) r y w))
  unfold FixedSpanRenewalPayload.wordSum
  rw [← sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  have hlen := allSchedules_schedule_length n T u hu
  have hcount :
      ControlledSchedulerMass.eventCount
        (ControlledSchedulerMass.controlledStep step r) r y u.reverse ≤ T := by
    have h := eventCount_le_length
      (ControlledSchedulerMass.controlledStep step r) r y u.reverse
    simpa [hlen] using h
  simp only [ControlledSchedulerMass.runWord,
    ControlledSchedulerMass.eventCount]
  change weight (ControlledSchedulerMass.runWord
      (ControlledSchedulerMass.controlledStep step r) y u.reverse)
      (T + 1 - (ControlledSchedulerMass.eventCost r x e +
        ControlledSchedulerMass.eventCount
          (ControlledSchedulerMass.controlledStep step r) r y u.reverse)) =
    c * weight (ControlledSchedulerMass.runWord
      (ControlledSchedulerMass.controlledStep step r) y u.reverse)
      (T - ControlledSchedulerMass.eventCount
        (ControlledSchedulerMass.controlledStep step r) r y u.reverse)
  by_cases hc : ControlledSchedulerMass.eventCost r x e = 1
  · have hexp :
        T + 1 - (ControlledSchedulerMass.eventCost r x e +
          ControlledSchedulerMass.eventCount
            (ControlledSchedulerMass.controlledStep step r) r y u.reverse) =
          T - ControlledSchedulerMass.eventCount
            (ControlledSchedulerMass.controlledStep step r) r y u.reverse := by
      omega
    rw [hexp]
    simp [c, hc]
  · have hc0 : ControlledSchedulerMass.eventCost r x e = 0 := by
      have hle := eventCost_le_one r x e
      omega
    have hexp :
        T + 1 - (ControlledSchedulerMass.eventCost r x e +
          ControlledSchedulerMass.eventCount
            (ControlledSchedulerMass.controlledStep step r) r y u.reverse) =
          (T - ControlledSchedulerMass.eventCount
            (ControlledSchedulerMass.controlledStep step r) r y u.reverse) + 1 := by
      omega
    rw [hexp, hdouble]
    simp [c, hc]

private theorem nodup_ofFn_injective {k : Nat} {X : Type}
    (f : Fin k → X) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem sum_pair_part (a b : Fin n) (f : Fin n → Nat)
    (hab : a ≠ b) :
    (List.ofFn (fun e => if e = a then f a else if e = b then f b else 0)).sum =
      f a + f b := by
  let g : Fin n → Nat := fun e => if e = a then f a else if e = b then f b else 0
  have h := sum_two_exceptions (List.ofFn (fun e : Fin n => e)) a b g 0
    (nodup_ofFn_injective _ Function.injective_id)
    (List.mem_ofFn.mpr ⟨a, rfl⟩)
    (List.mem_ofFn.mpr ⟨b, rfl⟩) hab (by
      intro e _ hea heb
      simp [g, hea, heb])
  simpa [List.map_ofFn, Function.comp_def, g, hab, Ne.symm hab] using h

private theorem sum_le_of_pair (a b : Fin n) (f g : Fin n → Nat)
    (hab : a ≠ b) (hpair : f a + f b ≤ g a + g b)
    (hother : ∀ e, e ≠ a → e ≠ b → f e ≤ g e) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  let rest := fun (v : Fin n → Nat) e => if e = a ∨ e = b then 0 else v e
  have split_sum (v : Fin n → Nat) :
      (List.ofFn v).sum = v a + v b + (List.ofFn (rest v)).sum := by
    calc
      (List.ofFn v).sum =
          (List.ofFn (fun e =>
            (if e = a then v a else if e = b then v b else 0) + rest v e)).sum := by
        apply ofFn_sum_eq
        intro e
        by_cases hea : e = a
        · simp [rest, hea]
        · by_cases heb : e = b <;> simp [rest, hea, heb, Ne.symm hab]
      _ = _ := by rw [ofFn_sum_add, sum_pair_part a b v hab]
  rw [split_sum f, split_sum g]
  apply Nat.add_le_add hpair
  apply ofFn_sum_le
  intro e
  by_cases hea : e = a
  · simp [rest, hea]
  · by_cases heb : e = b
    · simp [rest, heb]
    · simpa [rest, hea, heb] using hother e hea heb

private theorem redirect_weighted_sum_le
    (r : ControlledSchedulerMass.Redirection S n)
    (s : S) (f : Fin n → Nat) :
    (List.ofFn (fun e : Fin n =>
      (if ControlledSchedulerMass.eventCost r (.active s) e = 1 then 1 else 2) *
        f (r.effective s e))).sum ≤
      2 * (List.ofFn f).sum := by
  by_cases hg : r.gate s = true
  · let a := r.portA s
    let b := r.portB s
    have hab : a ≠ b := r.distinct s hg
    let g : Fin n → Nat := fun e => 2 * f e
    let h : Fin n → Nat := fun e =>
      (if ControlledSchedulerMass.eventCost r (.active s) e = 1 then 1 else 2) *
        f (r.effective s e)
    have ha : h a = f a := by
      simp [h, a, b, ControlledSchedulerMass.eventCost,
        ControlledSchedulerMass.Redirection.Collapses, hg]
    have hb : h b = f a := by
      simp [h, a, b, ControlledSchedulerMass.eventCost,
        ControlledSchedulerMass.Redirection.Collapses, hg,
        ControlledSchedulerMass.Redirection.effective_B r s hg]
    have hp : h a + h b ≤ g a + g b := by
      simp [ha, hb, g]
      omega
    have ho : ∀ e, e ≠ a → e ≠ b → h e ≤ g e := by
      intro e hea heb
      change e ≠ r.portA s at hea
      change e ≠ r.portB s at heb
      have heff : r.effective s e = e := by
        simp [ControlledSchedulerMass.Redirection.effective, heb]
      have hcost : ControlledSchedulerMass.eventCost r (.active s) e = 0 := by
        simp [ControlledSchedulerMass.eventCost,
          ControlledSchedulerMass.Redirection.Collapses, hg, hea, heb]
      simp [h, g, heff, hcost]
    have hsum := sum_le_of_pair a b h g hab hp ho
    simpa [h, g, ofFn_sum_mul_left] using hsum
  · have hgate : r.gate s = false := by
      cases h : r.gate s <;> simp_all
    have heq : ∀ e : Fin n,
        (if ControlledSchedulerMass.eventCost r (.active s) e = 1 then 1 else 2) *
          f (r.effective s e) = 2 * f e := by
      intro e
      simp [ControlledSchedulerMass.eventCost,
        ControlledSchedulerMass.Redirection.Collapses,
        r.effective_of_gate_false s hgate e, hgate]
    rw [ofFn_sum_eq _ _ heq, ofFn_sum_mul_left]
    exact Nat.le_refl _

private theorem wordSum_runWord_eq_treeWeight
    (step : S → Fin n → StopNode S) (weight : StopNode S → Nat)
    (x : StopNode S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T
        (fun w => weight (ControlledSchedulerMass.runWord step x w)) =
      treeWeight step weight x T := by
  induction T generalizing x with
  | zero => simp [FixedSpanRenewalPayload.wordSum, allSchedules,
      ControlledSchedulerMass.runWord, treeWeight]
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ]
      simp only [ControlledSchedulerMass.runWord, treeWeight]
      exact ofFn_sum_eq _ _ (fun e => ih (stepNode step x e))

/-- Generic finite-word likelihood comparison. The adaptive two-port
redirection is paid for by one factor `2` per raw letter, while the actual
number of duplicated preimages is removed from each path's exponent. -/
private theorem weighted_change_generic
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (weight : StopNode S → Nat → Nat)
    (hdouble : ∀ x k, weight x (k + 1) = 2 * weight x k)
    (x : StopNode S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun w =>
      weight (ControlledSchedulerMass.runWord
        (ControlledSchedulerMass.controlledStep step r) x w)
        (T - ControlledSchedulerMass.eventCount
          (ControlledSchedulerMass.controlledStep step r) r x w)) ≤
      2 ^ T * treeWeight step (fun y => weight y 0) x T := by
  induction T generalizing x with
  | zero =>
      simp [FixedSpanRenewalPayload.wordSum, allSchedules,
        ControlledSchedulerMass.runWord,
        ControlledSchedulerMass.eventCount, treeWeight]
  | succ T ih =>
      rw [wordSum_weighted_succ step r weight hdouble x T]
      let f : StopNode S → Nat := fun y => treeWeight step (fun z => weight z 0) y T
      let Q : StopNode S → Nat := fun y =>
        FixedSpanRenewalPayload.wordSum n T (fun w =>
          weight (ControlledSchedulerMass.runWord
            (ControlledSchedulerMass.controlledStep step r) y w)
            (T - ControlledSchedulerMass.eventCount
              (ControlledSchedulerMass.controlledStep step r) r y w))
      have hchildren :
          (List.ofFn (fun e : Fin n =>
            (if ControlledSchedulerMass.eventCost r x e = 1 then 1 else 2) *
              Q (stepNode (ControlledSchedulerMass.controlledStep step r) x e))).sum ≤
          (List.ofFn (fun e : Fin n =>
            (if ControlledSchedulerMass.eventCost r x e = 1 then 1 else 2) *
              (2 ^ T * f
                (stepNode (ControlledSchedulerMass.controlledStep step r) x e)))).sum := by
        apply ofFn_sum_le
        intro e
        exact Nat.mul_le_mul_left _
          (ih (stepNode (ControlledSchedulerMass.controlledStep step r) x e))
      calc
        (List.ofFn (fun e : Fin n =>
          (if ControlledSchedulerMass.eventCost r x e = 1 then 1 else 2) *
            Q (stepNode (ControlledSchedulerMass.controlledStep step r) x e))).sum ≤
            (List.ofFn (fun e : Fin n =>
              (if ControlledSchedulerMass.eventCost r x e = 1 then 1 else 2) *
                (2 ^ T * f
                  (stepNode (ControlledSchedulerMass.controlledStep step r) x e)))).sum :=
          hchildren
        _ = 2 ^ T *
            (List.ofFn (fun e : Fin n =>
              (if ControlledSchedulerMass.eventCost r x e = 1 then 1 else 2) *
                f (stepNode (ControlledSchedulerMass.controlledStep step r) x e))).sum := by
          rw [← ofFn_sum_mul_left]
          apply ofFn_sum_eq
          intro e
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ 2 ^ T *
            (2 * (List.ofFn (fun e : Fin n =>
              f (stepNode step x e))).sum) := by
          apply Nat.mul_le_mul_left
          cases x with
          | active s =>
              simpa [f, ControlledSchedulerMass.controlledStep,
                ControlledSchedulerMass.eventCost, stepNode] using
                redirect_weighted_sum_le r s
                  (fun e => f (step s e))
          | success =>
              simp [ControlledSchedulerMass.eventCost, stepNode,
                ofFn_sum_const, Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm]
          | failure =>
              simp [ControlledSchedulerMass.eventCost, stepNode,
                ofFn_sum_const, Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm]
        _ = 2 ^ (T + 1) * treeWeight step (fun y => weight y 0) x (T + 1) := by
          rw [Nat.pow_succ]
          simp [treeWeight, f, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm]

/-- Variable-weight finite change of measure for nonretry leaves. -/
theorem weighted_changeOfMeasure_nonretry
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (T : Nat) :
    weightedQNonRetryNumerator step r x T ≤
      2 ^ T * (activeCount step x T + successCount step x T) := by
  have hdouble : ∀ y k,
      powSuccessOrActive (S := S) y (k + 1) =
        2 * powSuccessOrActive y k := by
    intro y k
    cases y <;> simp [powSuccessOrActive, Nat.pow_succ, Nat.mul_comm]
  have h := weighted_change_generic step r powSuccessOrActive
    hdouble x T
  change weightedQNonRetryNumerator step r x T ≤
    2 ^ T * (activeCount step x T + successCount step x T)
  calc
    weightedQNonRetryNumerator step r x T ≤
        2 ^ T * treeWeight step
          (fun y => powSuccessOrActive y 0) x T := h
    _ = 2 ^ T * (activeCount step x T + successCount step x T) := by
      have hw : ∀ y : StopNode S,
          powSuccessOrActive y 0 = activeWeight y + successWeight y := by
        intro y
        cases y <;> rfl
      rw [treeWeight_congr step _ _ hw x T,
        treeWeight_add step activeWeight successWeight x T]
      rfl

/-- Success-only specialization of the same adaptive fiber inequality. -/
theorem weighted_changeOfMeasure_success
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (T : Nat) :
    weightedQSuccessNumerator step r x T ≤
      2 ^ T * successCount step x T := by
  have hdouble : ∀ y k,
      powSuccessOnly (S := S) y (k + 1) =
        2 * powSuccessOnly y k := by
    intro y k
    cases y <;> simp [powSuccessOnly, Nat.pow_succ, Nat.mul_comm]
  have h := weighted_change_generic step r powSuccessOnly hdouble x T
  calc
    weightedQSuccessNumerator step r x T ≤
        2 ^ T * treeWeight step (fun y => powSuccessOnly y 0) x T := h
    _ = 2 ^ T * successCount step x T := by
      have hw : ∀ y : StopNode S,
          powSuccessOnly y 0 = successWeight y := by
        intro y
        cases y <;> rfl
      rw [treeWeight_congr step _ _ hw x T]
      rfl

/-! ## Predictable service charges -/

/-- Total charge over all length-`T` words of a stopped process. At a live
prefix each possible next edge receives its own state-dependent charge. -/
def edgeChargeNumerator
    (step : S → Fin n → StopNode S) (charge : S → Fin n → Nat) :
    StopNode S → Nat → Nat
  | _, 0 => 0
  | .success, _ + 1 => 0
  | .failure, _ + 1 => 0
  | .active s, T + 1 =>
      n ^ T * (List.ofFn (fun e => charge s e)).sum +
        (List.ofFn (fun e =>
          edgeChargeNumerator step charge (step s e) T)).sum

/-- Charge one when the chosen edge is the predictable required service. -/
def serviceCharge (active : S → Bool) (required : S → Fin n)
    (s : S) (e : Fin n) : Nat :=
  if active s && e == required s then 1 else 0

/-- Charge one on every edge out of an active monitored state. -/
def activeCharge (active : S → Bool) (s : S) (_ : Fin n) : Nat :=
  if active s then 1 else 0

/-- Charge accumulated along one finite scheduler word, stopped at either
terminal outcome. -/
def wordCharge (step : S → Fin n → StopNode S)
    (charge : S → Fin n → Nat) :
    StopNode S → List (Fin n) → Nat
  | _, [] => 0
  | .success, _ :: _ => 0
  | .failure, _ :: _ => 0
  | .active s, e :: es =>
      charge s e + wordCharge step charge (step s e) es

private theorem sum_map_const {X : Type} (xs : List X) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

private theorem sum_map_add {X : Type} (xs : List X)
    (f g : X → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

private theorem sum_map_le {X : Type} (xs : List X)
    (f g : X → Nat) (hfg : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · exact hfg x (by simp)
      · apply ih
        intro y hy
        exact hfg y (by simp [hy])

private theorem wordSum_const (T c : Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun _ => c) = n ^ T * c := by
  unfold FixedSpanRenewalPayload.wordSum
  rw [sum_map_const, allSchedules_length]

private theorem wordSum_add (T : Nat)
    (f g : List (Fin n) → Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun w => f w + g w) =
      FixedSpanRenewalPayload.wordSum n T f +
        FixedSpanRenewalPayload.wordSum n T g := by
  unfold FixedSpanRenewalPayload.wordSum
  exact sum_map_add _ _ _

/-- Full-word summation equals the recursive prefix-charge numerator;
terminal padding has zero charge on both sides. -/
theorem wordSum_charge_eq_edgeChargeNumerator
    (step : S → Fin n → StopNode S)
    (charge : S → Fin n → Nat) (x : StopNode S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T
        (wordCharge step charge x) =
      edgeChargeNumerator step charge x T := by
  induction T generalizing x with
  | zero =>
      cases x <;> simp [FixedSpanRenewalPayload.wordSum,
        allSchedules, wordCharge, edgeChargeNumerator]
  | succ T ih =>
      cases x with
      | success =>
          rw [FixedSpanRenewalPayload.wordSum_succ]
          simp [wordCharge, edgeChargeNumerator, wordSum_const,
            ofFn_sum_const]
      | failure =>
          rw [FixedSpanRenewalPayload.wordSum_succ]
          simp [wordCharge, edgeChargeNumerator, wordSum_const,
            ofFn_sum_const]
      | active s =>
          rw [FixedSpanRenewalPayload.wordSum_succ]
          change (List.ofFn (fun e : Fin n =>
            FixedSpanRenewalPayload.wordSum n T (fun w =>
              charge s e + wordCharge step charge (step s e) w))).sum =
            n ^ T * (List.ofFn (fun e : Fin n => charge s e)).sum +
              (List.ofFn (fun e : Fin n =>
                edgeChargeNumerator step charge (step s e) T)).sum
          rw [ofFn_sum_eq _ _ (fun e =>
            wordSum_add T (fun _ => charge s e)
              (wordCharge step charge (step s e))),
            ofFn_sum_add]
          rw [ofFn_sum_eq _ _ (fun e =>
            wordSum_const (n := n) T (charge s e)),
            ofFn_sum_mul_left]
          congr 1
          apply ofFn_sum_eq
          intro e
          exact ih (step s e)

/-- Number of controlled collapsed-event occurrences across full words. -/
def collapseCountNumerator
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (fun w =>
    ControlledSchedulerMass.eventCount
      (ControlledSchedulerMass.controlledStep step r) r x w)

/-- Cumulative required-service charge in the controlled process. -/
def targetServiceNumerator
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (active : S → Bool) (required : S → Fin n)
    (x : StopNode S) (T : Nat) : Nat :=
  edgeChargeNumerator (ControlledSchedulerMass.controlledStep step r)
    (serviceCharge active required) x T

private def collapseCharge
    (r : ControlledSchedulerMass.Redirection S n)
    (s : S) (e : Fin n) : Nat :=
  if r.Collapses s e then 1 else 0

private theorem eventCount_eq_wordCharge
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (x : StopNode S) (w : List (Fin n)) :
    ControlledSchedulerMass.eventCount step r x w =
      wordCharge step (collapseCharge r) x w := by
  induction w generalizing x with
  | nil => cases x <;> rfl
  | cons e es ih =>
      cases x with
      | success =>
          simp [ControlledSchedulerMass.eventCount_success, wordCharge]
      | failure =>
          simp [ControlledSchedulerMass.eventCount_failure, wordCharge]
      | active s =>
          simp only [ControlledSchedulerMass.eventCount,
            ControlledSchedulerMass.eventCost, wordCharge, stepNode,
            collapseCharge]
          rw [ih]

/-- A physical pathwise cycle-service inequality, checked on every word of
length `T`, transfers exactly to the two finite numerators. -/
theorem collapseNumerator_le_serviceNumerator
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (active : S → Bool) (required : S → Fin n)
    (m : Nat) (x : StopNode S) (T : Nat)
    (hcycle : ∀ w : List (Fin n), w.length = T →
      m * ControlledSchedulerMass.eventCount
        (ControlledSchedulerMass.controlledStep step r) r x w ≤
      wordCharge (ControlledSchedulerMass.controlledStep step r)
        (serviceCharge active required) x w) :
    m * collapseCountNumerator step r x T ≤
      targetServiceNumerator step r active required x T := by
  unfold collapseCountNumerator targetServiceNumerator
  rw [← wordSum_charge_eq_edgeChargeNumerator]
  unfold FixedSpanRenewalPayload.wordSum
  rw [← sum_map_mul_left]
  apply sum_map_le
  intro w hw
  have hlen := allSchedules_schedule_length n T w hw
  have hrev : w.reverse.length = T := by simpa [hlen]
  exact hcycle w.reverse hrev

private theorem sum_spike (a : Fin n) :
    (List.ofFn (fun e : Fin n => if e = a then 1 else 0)).sum = 1 := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have htail :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then 1 else 0)).sum = 0 := by
          calc
            _ = (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro i
              have hne : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv : i.val + 1 = 0 := by
                  simpa using congrArg Fin.val he
                omega
              exact if_neg hne
            _ = 0 := by simp [ofFn_sum_const]
        simp [htail]
      · intro b
        have hz : (0 : Fin (n + 1)) ≠ b.succ := by
          intro he
          have hv : 0 = b.val + 1 := by
            simpa using congrArg Fin.val he
          omega
        rw [List.ofFn_succ, List.sum_cons]
        simp only [hz, ite_false, Nat.zero_add]
        calc
          (List.ofFn (fun i : Fin n =>
              if i.succ = b.succ then 1 else 0)).sum =
              (List.ofFn (fun i : Fin n => if i = b then 1 else 0)).sum := by
                apply ofFn_sum_eq
                intro i
                simp only [Fin.succ_inj]
          _ = 1 := ih b

private theorem service_charge_sum (active : S → Bool)
    (required : S → Fin n) (s : S) :
    n * (List.ofFn (fun e => serviceCharge active required s e)).sum =
      (List.ofFn (fun e : Fin n => activeCharge active s e)).sum := by
  cases ha : active s with
  | false => simp [serviceCharge, activeCharge, ha, ofFn_sum_const]
  | true =>
      have hsp :
          (List.ofFn (fun e : Fin n => serviceCharge active required s e)).sum = 1 := by
        calc
          _ = (List.ofFn (fun e : Fin n =>
              if e = required s then 1 else 0)).sum := by
                apply ofFn_sum_eq
                intro e
                simp [serviceCharge, ha, beq_iff_eq]
          _ = 1 := sum_spike (required s)
      rw [hsp, Nat.mul_one]
      simp [activeCharge, ha, ofFn_sum_const]

/-- Exact finite-horizon compensator. Every live monitored prefix has exactly
one required edge among its `n` raw children. -/
theorem predictable_service_exact
    (step : S → Fin n → StopNode S)
    (active : S → Bool) (required : S → Fin n)
    (x : StopNode S) (T : Nat) :
    n * edgeChargeNumerator step (serviceCharge active required) x T =
      edgeChargeNumerator step (activeCharge active) x T := by
  induction T generalizing x with
  | zero => cases x <;> simp [edgeChargeNumerator]
  | succ T ih =>
      cases x with
      | success => simp [edgeChargeNumerator]
      | failure => simp [edgeChargeNumerator]
      | active s =>
          change n *
              (n ^ T * (List.ofFn (fun e : Fin n =>
                  serviceCharge active required s e)).sum +
                (List.ofFn (fun e : Fin n =>
                  edgeChargeNumerator step (serviceCharge active required)
                    (step s e) T)).sum) =
              n ^ T * (List.ofFn (fun e : Fin n =>
                activeCharge active s e)).sum +
                (List.ofFn (fun e : Fin n =>
                  edgeChargeNumerator step (activeCharge active)
                    (step s e) T)).sum
          rw [Nat.mul_add, Nat.mul_left_comm n (n ^ T),
            service_charge_sum active required s]
          congr 1
          calc
            n * (List.ofFn (fun e : Fin n =>
                edgeChargeNumerator step (serviceCharge active required)
                  (step s e) T)).sum =
                (List.ofFn (fun e : Fin n =>
                  n * edgeChargeNumerator step
                    (serviceCharge active required) (step s e) T)).sum :=
              (ofFn_sum_mul_left n _).symm
            _ = _ := ofFn_sum_eq _ _ (fun e => ih (step s e))

/-- Monitored active time is at most the full stopped interaction cost. -/
theorem activeCharge_le_cost
    (step : S → Fin n → StopNode S)
    (active : S → Bool) (x : StopNode S) (T : Nat) :
    edgeChargeNumerator step (activeCharge active) x T ≤
      truncatedActiveCostNumerator step x T := by
  induction T generalizing x with
  | zero => cases x <;> simp [edgeChargeNumerator, truncatedActiveCostNumerator]
  | succ T ih =>
      cases x with
      | success => simp [edgeChargeNumerator, truncatedActiveCostNumerator]
      | failure => simp [edgeChargeNumerator, truncatedActiveCostNumerator]
      | active s =>
          simp only [edgeChargeNumerator, truncatedActiveCostNumerator]
          apply Nat.add_le_add
          · cases ha : active s <;>
              simp [activeCharge, ha, ofFn_sum_const, Nat.pow_succ,
                Nat.mul_comm]
          · apply ofFn_sum_le
            intro e
            exact ih (step s e)

/-- A physical cycle-count inequality can be passed to the generic
compensator without assuming independence between successive cycles. The
producer of `hcycle` must establish it for the actual controlled process. -/
theorem compensator_cleared
    (step : S → Fin n → StopNode S)
    (active : S → Bool) (required : S → Fin n)
    (collapseNumerator : StopNode S → Nat → Nat)
    (m : Nat) (x : StopNode S) (T : Nat)
    (hcycle : m * collapseNumerator x T ≤
      edgeChargeNumerator step (serviceCharge active required) x T) :
    n * (m * collapseNumerator x T) ≤
      truncatedActiveCostNumerator step x T := by
  calc
    n * (m * collapseNumerator x T) ≤
        n * edgeChargeNumerator step
          (serviceCharge active required) x T :=
      Nat.mul_le_mul_left n hcycle
    _ = edgeChargeNumerator step (activeCharge active) x T :=
      predictable_service_exact step active required x T
    _ ≤ truncatedActiveCostNumerator step x T :=
      activeCharge_le_cost step active x T

/-- Cancel the positive scheduler alphabet size after a finite Bellman
attempt-cost estimate. -/
theorem collapse_moment_cleared
    (step : S → Fin n → StopNode S)
    (active : S → Bool) (required : S → Fin n)
    (collapseNumerator : StopNode S → Nat → Nat)
    (m A : Nat) (hn : 0 < n) (x : StopNode S) (T : Nat)
    (hcycle : m * collapseNumerator x T ≤
      edgeChargeNumerator step (serviceCharge active required) x T)
    (hcost : truncatedActiveCostNumerator step x T ≤
      n ^ T * (n * A)) :
    m * collapseNumerator x T ≤ n ^ T * A := by
  have hscaled : n * (m * collapseNumerator x T) ≤
      n * (n ^ T * A) := by
    calc
      _ ≤ truncatedActiveCostNumerator step x T :=
        compensator_cleared step active required collapseNumerator
          m x T hcycle
      _ ≤ n ^ T * (n * A) := hcost
      _ = n * (n ^ T * A) := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left hscaled hn

/-- Moderate regime arithmetic after the physical layer provides the
`(2b-1)`-per-collapse moment and the `5a` attacker cost. -/
theorem moderate_collapse_moment
    (b a C P : Nat) (hb : 2 ≤ b) (hab : a ≤ 2 * b)
    (hmoment : (2 * b - 1) * C ≤ P * (5 * a)) :
    3 * C ≤ 20 * P := by
  have hmpos : 0 < 2 * b - 1 := by omega
  have hcoef : 3 * (5 * a) ≤ 20 * (2 * b - 1) := by omega
  have hscaled : (2 * b - 1) * (3 * C) ≤
      (2 * b - 1) * (20 * P) := by
    calc
      (2 * b - 1) * (3 * C) = 3 * ((2 * b - 1) * C) := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ 3 * (P * (5 * a)) := Nat.mul_le_mul_left 3 hmoment
      _ = P * (3 * (5 * a)) := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ P * (20 * (2 * b - 1)) := Nat.mul_le_mul_left P hcoef
      _ = (2 * b - 1) * (20 * P) := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left hscaled hmpos

/-- Retained-bullet arithmetic when its remaining distance is at most `2b`. -/
theorem retained_collapse_moment
    (b r C P : Nat) (hb : 2 ≤ b) (hr : r ≤ 2 * b)
    (hmoment : (2 * b - 1) * C ≤ P * r) :
    C ≤ 2 * P := by
  have hmpos : 0 < 2 * b - 1 := by omega
  have hcoef : r ≤ 2 * (2 * b - 1) := by omega
  have hscaled : (2 * b - 1) * C ≤
      (2 * b - 1) * (2 * P) := by
    calc
      _ ≤ P * r := hmoment
      _ ≤ P * (2 * (2 * b - 1)) := Nat.mul_le_mul_left P hcoef
      _ = (2 * b - 1) * (2 * P) := by
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left hscaled hmpos

/-! ## Integer-cleared weight inequalities -/

/-- W1 with no rational numbers and no subtraction of `8-N`. -/
theorem W1_scaled (N T : Nat) (hNT : N ≤ T) :
    8 * 2 ^ T ≤ 128 * 2 ^ (T - N) + N * 2 ^ T := by
  have hpow : 2 ^ T = 2 ^ N * 2 ^ (T - N) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hbase : 8 * 2 ^ N ≤ 128 + N * 2 ^ N := by
    by_cases h8 : 8 ≤ N
    · have hm := Nat.mul_le_mul_right (2 ^ N) h8
      omega
    · have hc : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨
          N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 := by omega
      rcases hc with h|h|h|h|h|h|h|h <;> subst N <;> decide
  calc
    8 * 2 ^ T = (8 * 2 ^ N) * 2 ^ (T - N) := by simp [hpow, Nat.mul_assoc]
    _ ≤ (128 + N * 2 ^ N) * 2 ^ (T - N) :=
      Nat.mul_le_mul_right _ hbase
    _ = 128 * 2 ^ (T - N) + N * 2 ^ T := by
      simp [Nat.add_mul, hpow, Nat.mul_assoc]

/-- W2 with no rational numbers and no subtraction of `4-N`. -/
theorem W2_scaled (N T : Nat) (hNT : N ≤ T) :
    4 * 2 ^ T ≤ 8 * 2 ^ (T - N) + N * 2 ^ T := by
  have hpow : 2 ^ T = 2 ^ N * 2 ^ (T - N) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hbase : 4 * 2 ^ N ≤ 8 + N * 2 ^ N := by
    by_cases h4 : 4 ≤ N
    · have hm := Nat.mul_le_mul_right (2 ^ N) h4
      omega
    · have hc : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 := by omega
      rcases hc with h|h|h|h <;> subst N <;> decide
  calc
    4 * 2 ^ T = (4 * 2 ^ N) * 2 ^ (T - N) := by simp [hpow, Nat.mul_assoc]
    _ ≤ (8 + N * 2 ^ N) * 2 ^ (T - N) :=
      Nat.mul_le_mul_right _ hbase
    _ = 8 * 2 ^ (T - N) + N * 2 ^ T := by
      simp [Nat.add_mul, hpow, Nat.mul_assoc]

/-! ## Payload-preserving retry -/

/-- A retry carries the actual surviving state into the next attempt. -/
inductive AttemptNode (A S : Type) where
  | active : A → AttemptNode A S
  | success : AttemptNode A S
  | retry : S → AttemptNode A S

/-- One attempt starts from the current survivor and either continues,
succeeds, or returns another valid survivor. -/
structure RetryKernel (A S : Type) (n : Nat) where
  start : S → A
  step : A → Fin n → AttemptNode A S
  valid : S → Prop
  retry_valid : ∀ a e s', step a e = .retry s' → valid s'

variable {A : Type}

/-- Cost of one attempt, stopped at either success or retry. -/
def attemptCostNumerator (K : RetryKernel A S n) :
    AttemptNode A S → Nat → Nat
  | _, 0 => 0
  | .success, _ + 1 => 0
  | .retry _, _ + 1 => 0
  | .active a, T + 1 =>
      n ^ (T + 1) +
        (List.ofFn (fun e => attemptCostNumerator K (K.step a e) T)).sum

/-- Number of full words whose first attempt has completed in retry by the
horizon. Padding after a retry contributes `n^T` at remaining depth `T`. -/
def retryCount (K : RetryKernel A S n) :
    AttemptNode A S → Nat → Nat
  | .retry _, T => n ^ T
  | .success, _ => 0
  | .active _, 0 => 0
  | .active a, T + 1 =>
      (List.ofFn (fun e => retryCount K (K.step a e) T)).sum

/-- Cost of the repeated process while an attempt is active. The retry
survivor is reinitialized without consuming a scheduler letter. -/
def repeatCostActive (K : RetryKernel A S n) (a : A) : Nat → Nat
  | 0 => 0
  | T + 1 =>
      n ^ (T + 1) +
        (List.ofFn (fun e =>
          match K.step a e with
          | .active a' => repeatCostActive K a' T
          | .success => 0
          | .retry s' => repeatCostActive K (K.start s') T)).sum

/-- Exact cost numerator from an actual survivor state. -/
def repeatCostNumerator (K : RetryKernel A S n) (s : S) (T : Nat) : Nat :=
  repeatCostActive K (K.start s) T

private def repeatContinuation (K : RetryKernel A S n)
    (x : AttemptNode A S) (T : Nat) : Nat :=
  match x with
  | .active a => repeatCostActive K a T
  | .success => 0
  | .retry s => repeatCostNumerator K s T

private def attemptNodeValid (K : RetryKernel A S n)
    (x : AttemptNode A S) : Prop :=
  match x with
  | .retry s => K.valid s
  | _ => True

private theorem attempt_child_valid (K : RetryKernel A S n)
    (a : A) (e : Fin n) : attemptNodeValid K (K.step a e) := by
  cases hx : K.step a e with
  | active _ => trivial
  | success => trivial
  | retry s' => exact K.retry_valid a e s' hx

private theorem repeatContinuation_le_attempt_add_retry
    (K : RetryKernel A S n) (q B T : Nat)
    (hbound : ∀ t ≤ T, ∀ s, K.valid s →
      repeatCostNumerator K s t ≤ n ^ t * (q * B)) :
    ∀ x, attemptNodeValid K x →
      repeatContinuation K x T ≤
        attemptCostNumerator K x T + q * B * retryCount K x T := by
  induction T with
  | zero =>
      intro x hx
      cases x with
      | active a => simp [repeatContinuation, repeatCostActive,
          attemptCostNumerator, retryCount]
      | success => simp [repeatContinuation, attemptCostNumerator, retryCount]
      | retry s =>
          have hs := hbound 0 (Nat.le_refl 0) s hx
          simpa [repeatContinuation, attemptCostNumerator, retryCount] using hs
  | succ T ih =>
      intro x hx
      cases x with
      | success => simp [repeatContinuation, attemptCostNumerator, retryCount]
      | retry s =>
          have hs := hbound (T + 1) (Nat.le_refl _) s hx
          simpa [repeatContinuation, attemptCostNumerator, retryCount,
            Nat.mul_comm] using hs
      | active a =>
          have hchild (e : Fin n) :
              repeatContinuation K (K.step a e) T ≤
                attemptCostNumerator K (K.step a e) T +
                  q * B * retryCount K (K.step a e) T := by
            apply ih
            · intro t ht s hs
              exact hbound t (by omega) s hs
            · exact attempt_child_valid K a e
          change n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                repeatContinuation K (K.step a e) T)).sum ≤
              (n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  attemptCostNumerator K (K.step a e) T)).sum) +
              q * B *
                (List.ofFn (fun e : Fin n =>
                  retryCount K (K.step a e) T)).sum
          have hsum := ofFn_sum_le
            (fun e : Fin n => repeatContinuation K (K.step a e) T)
            (fun e : Fin n => attemptCostNumerator K (K.step a e) T +
              q * B * retryCount K (K.step a e) T) hchild
          rw [ofFn_sum_add, ofFn_sum_mul_left] at hsum
          omega

/-- A state-uniform bound on completed retry mass suffices for a geometric
restart cost bound. No attempt-independence premise occurs. -/
theorem retry_cost_of_retry_mass
    (K : RetryKernel A S n) (q B : Nat) (hq : 0 < q)
    (hcost : ∀ s, K.valid s → ∀ T,
      attemptCostNumerator K (.active (K.start s)) T ≤ n ^ T * B)
    (hretry : ∀ s, K.valid s → ∀ T,
      q * retryCount K (.active (K.start s)) T ≤
        (q - 1) * n ^ T) :
    ∀ s, K.valid s → ∀ T,
      repeatCostNumerator K s T ≤ n ^ T * (q * B) := by
  intro s hs T
  induction T using Nat.strongRecOn generalizing s with
  | ind T ih =>
      cases T with
      | zero => simp [repeatCostNumerator, repeatCostActive]
      | succ T =>
          have hbound : ∀ t ≤ T, ∀ s', K.valid s' →
              repeatCostNumerator K s' t ≤ n ^ t * (q * B) := by
            intro t ht s' hs'
            exact ih t (by omega) s' hs'
          have hchildren (e : Fin n) :
              repeatContinuation K (K.step (K.start s) e) T ≤
                attemptCostNumerator K (K.step (K.start s) e) T +
                  q * B * retryCount K (K.step (K.start s) e) T :=
            repeatContinuation_le_attempt_add_retry K q B T hbound
              _ (attempt_child_valid K (K.start s) e)
          have hdecomp :
              repeatCostNumerator K s (T + 1) ≤
                attemptCostNumerator K (.active (K.start s)) (T + 1) +
                  q * B * retryCount K (.active (K.start s)) (T + 1) := by
            change n ^ (T + 1) +
                (List.ofFn (fun e : Fin n =>
                  repeatContinuation K (K.step (K.start s) e) T)).sum ≤
                (n ^ (T + 1) +
                  (List.ofFn (fun e : Fin n =>
                    attemptCostNumerator K (K.step (K.start s) e) T)).sum) +
                q * B *
                  (List.ofFn (fun e : Fin n =>
                    retryCount K (K.step (K.start s) e) T)).sum
            have hsum := ofFn_sum_le
              (fun e : Fin n =>
                repeatContinuation K (K.step (K.start s) e) T)
              (fun e : Fin n =>
                attemptCostNumerator K (K.step (K.start s) e) T +
                  q * B * retryCount K (K.step (K.start s) e) T)
              hchildren
            rw [ofFn_sum_add, ofFn_sum_mul_left] at hsum
            omega
          have hr := hretry s hs (T + 1)
          have hc := hcost s hs (T + 1)
          have hrB := Nat.mul_le_mul_left B hr
          have hq : q - 1 + 1 = q := by omega
          calc
            repeatCostNumerator K s (T + 1) ≤
                attemptCostNumerator K (.active (K.start s)) (T + 1) +
                  q * B * retryCount K (.active (K.start s)) (T + 1) := hdecomp
            _ ≤ n ^ (T + 1) * B +
                  B * ((q - 1) * n ^ (T + 1)) := by
              have hretryB :
                  q * B * retryCount K (.active (K.start s)) (T + 1) ≤
                    B * ((q - 1) * n ^ (T + 1)) := by
                simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hrB
              exact Nat.add_le_add hc hretryB
            _ = n ^ (T + 1) * (q * B) := by
              calc
                _ = n ^ (T + 1) * (B + (q - 1) * B) := by
                  simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm,
                    Nat.mul_comm]
                _ = n ^ (T + 1) * (q * B) := by
                  congr 1
                  calc
                    B + (q - 1) * B = ((q - 1) + 1) * B := by
                      simp [Nat.add_mul, Nat.add_comm]
                    _ = q * B := by rw [hq]

end PPL.Convergence.LDLocal

#check PPL.Convergence.LDLocal.weighted_changeOfMeasure_nonretry
#check PPL.Convergence.LDLocal.collapseNumerator_le_serviceNumerator
#check PPL.Convergence.LDLocal.compensator_cleared
#check PPL.Convergence.LDLocal.retry_cost_of_retry_mass

#print axioms PPL.Convergence.LDLocal.weighted_changeOfMeasure_nonretry
#print axioms PPL.Convergence.LDLocal.weighted_changeOfMeasure_success
#print axioms PPL.Convergence.LDLocal.wordSum_charge_eq_edgeChargeNumerator
#print axioms PPL.Convergence.LDLocal.collapseNumerator_le_serviceNumerator
#print axioms PPL.Convergence.LDLocal.predictable_service_exact
#print axioms PPL.Convergence.LDLocal.activeCharge_le_cost
#print axioms PPL.Convergence.LDLocal.compensator_cleared
#print axioms PPL.Convergence.LDLocal.collapse_moment_cleared
#print axioms PPL.Convergence.LDLocal.moderate_collapse_moment
#print axioms PPL.Convergence.LDLocal.retained_collapse_moment
#print axioms PPL.Convergence.LDLocal.W1_scaled
#print axioms PPL.Convergence.LDLocal.W2_scaled
#print axioms PPL.Convergence.LDLocal.retry_cost_of_retry_mass

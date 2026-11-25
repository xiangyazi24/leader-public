import Leader.L4.Statement

/-!
# Finite-word weighted survival

This is an exact natural-number interface. The denominator of a horizon-t
probability is n^t; the numerator counts all raw length-t scheduler words.
-/

namespace L4.TaggedTail
open Classical

/-- Sum over the next uniform mark. -/
def sumEdge {n : Nat} (f : Fin n → Nat) : Nat := (List.ofFn f).sum

private theorem sumEdge_succ {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun i : Fin n => f i.succ) := by
  simp [sumEdge, List.ofFn_succ, List.sum_cons]

private theorem sumEdge_mono {n : Nat} (f g : Fin n → Nat) (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [sumEdge_succ f, sumEdge_succ g]
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

private theorem sumEdge_add {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumEdge_succ, sumEdge_succ f, sumEdge_succ g, ih]; omega

private theorem sumEdge_scale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a * f e) = a * sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sumEdge_succ, sumEdge_succ f, ih, Nat.mul_add]

/-- Terminal weight summed over words still live at every prefix, including
the endpoint.  A previously stopped trajectory never revives in this sum. -/
noncomputable def weightedSurvival {α : Type} {n : Nat}
    (next : α → Fin n → α) (live : α → Prop) (w : α → Nat) :
    Nat → α → Nat
  | 0, x => if live x then w x else 0
  | t+1, x => if live x then sumEdge (fun e => weightedSurvival next live w t (next x e)) else 0

/-- Exact survival numerator (unit terminal weight). -/
noncomputable def survival {α : Type} {n : Nat}
    (next : α → Fin n → α) (live : α → Prop) (t : Nat) (x : α) : Nat :=
  weightedSurvival next live (fun _ => 1) t x

/-- Predictable one-mark comparison with killed children implies the exact
finite-word contraction. The actual probability contraction is b/(a*n).
A weight is needed only on the predictable live domain. -/
theorem weightedSurvival_le {α : Type} {n : Nat}
    (next : α → Fin n → α) (live : α → Prop) (w : α → Nat)
    (a b : Nat)
    (h : ∀ x, live x →
      a * sumEdge (fun e => if live (next x e) then w (next x e) else 0) ≤ b * w x)
    (t : Nat) (x : α) :
    a^t * weightedSurvival next live w t x ≤ b^t * (if live x then w x else 0) := by
  classical
  induction t generalizing x with
  | zero => simp [weightedSurvival]
  | succ t ih =>
    by_cases hx : live x
    · simp only [weightedSurvival, hx, if_true, Nat.pow_succ]
      calc
        _ = a * sumEdge (fun e => a^t * weightedSurvival next live w t (next x e)) := by
          rw [sumEdge_scale]
          ac_rfl
        _ ≤ a * sumEdge (fun e => b^t * (if live (next x e) then w (next x e) else 0)) :=
          Nat.mul_le_mul_left _ (sumEdge_mono _ _ (fun e => ih (next x e)))
        _ = b^t * (a * sumEdge (fun e => if live (next x e) then w (next x e) else 0)) := by
          rw [sumEdge_scale]
          ac_rfl
        _ ≤ _ := by
          rw [show b^t * b * w x = b^t * (b * w x) from Nat.mul_assoc ..]
          exact Nat.mul_le_mul_left _ (h x hx)
    · simp [weightedSurvival, hx]

/-- Comparison to unweighted survival when every live endpoint contributes
at least a fixed threshold. This supports exponentially large thresholds. -/
theorem threshold_mul_survival_le {α : Type} {n : Nat}
    (next : α → Fin n → α) (live : α → Prop) (w : α → Nat)
    (threshold : Nat) (h : ∀ x, live x → threshold ≤ w x)
    (t : Nat) (x : α) :
    threshold * survival next live t x ≤ weightedSurvival next live w t x := by
  classical
  induction t generalizing x with
  | zero =>
    by_cases hx : live x
    · simpa [survival, weightedSurvival, hx] using h x hx
    · simp [survival, weightedSurvival, hx]
  | succ t ih =>
    by_cases hx : live x
    · simp only [survival, weightedSurvival, hx, if_true]
      rw [← sumEdge_scale]
      exact sumEdge_mono _ _ (fun e => ih (next x e))
    · simp [survival, weightedSurvival, hx]

/-- Contracted rational tail without importing a probability library.
All quantities are numerator-level. -/
theorem survival_contraction {α : Type} {n : Nat}
    (next : α → Fin n → α) (live : α → Prop) (w : α → Nat)
    (a b threshold : Nat)
    (hstep : ∀ x, live x →
      a * sumEdge (fun e => if live (next x e) then w (next x e) else 0) ≤ b * w x)
    (hweight : ∀ x, live x → threshold ≤ w x)
    (t : Nat) (x : α) :
    a^t * (threshold * survival next live t x) ≤ b^t * (if live x then w x else 0) :=
  Nat.le_trans (Nat.mul_le_mul_left _ (threshold_mul_survival_le next live w threshold hweight t x))
    (weightedSurvival_le next live w a b hstep t x)

private theorem sumEdge_congr {n : Nat} (f g : Fin n → Nat) (h : ∀ e, f e = g e) :
    sumEdge f = sumEdge g :=
  congrArg sumEdge (funext h)

private theorem entry_le_sumEdge {n : Nat} (f : Fin n → Nat) (i : Fin n) :
    f i ≤ sumEdge f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [sumEdge_succ]
    refine Fin.cases (Nat.le_add_right ..) (fun j => ?_) i
    exact Nat.le_trans (ih (fun e => f e.succ) j) (Nat.le_add_left ..)

private theorem sumEdge_const (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sumEdge_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem sumEdge_swap {n m : Nat} (f : Fin n → Fin m → Nat) :
    sumEdge (fun i => sumEdge (f i)) = sumEdge (fun j => sumEdge (fun i => f i j)) := by
  induction n with
  | zero =>
    have h : sumEdge (fun j : Fin m => sumEdge (fun i : Fin 0 => f i j)) =
      sumEdge (fun _ : Fin m => 0) := sumEdge_congr _ _ (fun _ => rfl)
    rw [h, sumEdge_const, Nat.mul_zero]
    rfl
  | succ n ih =>
    rw [sumEdge_succ, ih]
    rw [show sumEdge (fun j => sumEdge (fun i => f i j)) =
      sumEdge (fun j => f 0 j + sumEdge (fun i : Fin n => f i.succ j)) from
        sumEdge_congr _ _ (fun j => sumEdge_succ (fun i => f i j)), sumEdge_add]

/-- Union bound on all raw words. Once a tag has died, it must stay dead.
This is a deterministic condition on augmented state, not independence of
tags or a disjointness assumption on their nominated edges. -/
theorem survival_union {α : Type} {n m : Nat} (next : α → Fin n → α)
    (live : Fin m → α → Prop)
    (habsorb : ∀ i x e, live i (next x e) → live i x) (t : Nat) (x : α) :
    survival next (fun y => ∃ i, live i y) t x ≤
      sumEdge (fun i => survival next (live i) t x) := by
  induction t generalizing x with
  | zero =>
    by_cases hx : ∃ i, live i x
    · rcases hx with ⟨i, hi⟩
      have h := entry_le_sumEdge (fun i => if live i x then 1 else 0) i
      simpa [survival, weightedSurvival, hi, show ∃ j, live j x from ⟨i,hi⟩] using h
    · simp [survival, weightedSurvival, hx]
  | succ t ih =>
    by_cases hx : ∃ i, live i x
    · calc
        _ = sumEdge (fun e => survival next (fun y => ∃ i, live i y) t (next x e)) := by
          simp [survival, weightedSurvival, hx]
        _ ≤ sumEdge (fun e => sumEdge (fun i => survival next (live i) t (next x e))) :=
          sumEdge_mono _ _ (fun e => ih (next x e))
        _ = sumEdge (fun i => sumEdge (fun e => survival next (live i) t (next x e))) :=
          sumEdge_swap _
        _ = _ := by
          apply sumEdge_congr
          intro i
          by_cases hix : live i x
          · simp [survival, weightedSurvival, hix]
          · apply Eq.trans (b := 0)
            · rw [show sumEdge (fun e => survival next (live i) t (next x e)) =
                  sumEdge (fun _ : Fin n => 0) from sumEdge_congr _ _ (fun e => by
                    have hi : ¬ live i (next x e) := fun h => hix (habsorb i x e h)
                    cases t <;> simp [survival, weightedSurvival, hi])]
              rw [sumEdge_const, Nat.mul_zero]
            · simp [survival, weightedSurvival, hix]
    · simp [survival, weightedSurvival, hx]

/-- Increasing the truncation by one charges exactly the corresponding
survival probability. This connects the rational tail to the existing
IID expected-hitting-time definition; dead endpoints are not charged. -/
theorem iidHitCost_succ_eq {α : Type} {n : Nat} (next : α → Fin n → α)
    (stop : α → Prop) (t : Nat) (x : α) :
    iidHitCost next stop (t+1) x =
      n * (iidHitCost next stop t x + survival next (fun y => ¬ stop y) t x) := by
  induction t generalizing x with
  | zero =>
    by_cases hx : stop x
    · simp [iidHitCost, survival, weightedSurvival, hx]
    · simp only [iidHitCost, survival, weightedSurvival, hx, if_false, not_false_eq_true,
        if_true, Nat.mul_one, Nat.zero_add, Nat.pow_one]
      change n + sumEdge (fun _ : Fin n => 0) = n
      rw [sumEdge_const, Nat.mul_zero, Nat.add_zero]
  | succ t ih =>
    by_cases hx : stop x
    · simp [iidHitCost, survival, weightedSurvival, hx]
    · have h : sumEdge (fun e => iidHitCost next stop (t+1) (next x e)) =
          n * (sumEdge (fun e => iidHitCost next stop t (next x e)) +
            sumEdge (fun e => survival next (fun y => ¬ stop y) t (next x e))) := by
        calc
          _ = sumEdge (fun e => n * (iidHitCost next stop t (next x e) +
              survival next (fun y => ¬ stop y) t (next x e))) := sumEdge_congr _ _ (fun e => ih _)
          _ = _ := by rw [sumEdge_scale, sumEdge_add]
      have cost (u : Nat) : iidHitCost next stop (u+1) x =
          n^(u+1) + sumEdge (fun e => iidHitCost next stop u (next x e)) := by
        rw [iidHitCost, if_neg hx]
        rfl
      have surv : survival next (fun y => ¬ stop y) (t+1) x =
          sumEdge (fun e => survival next (fun y => ¬ stop y) t (next x e)) := by
        unfold survival
        rw [weightedSurvival, if_pos hx]
      rw [cost (t+1), cost t, surv, h, Nat.pow_succ n (t+1)]
      simp only [Nat.mul_add]
      ac_rfl

/-- The truncated hitting cost never exceeds the deterministic horizon. -/
theorem iidHitCost_le_horizon {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (t : Nat) (x : α) :
    iidHitCost next stop t x ≤ t * n^t := by
  induction t generalizing x with
  | zero => simp [iidHitCost]
  | succ t ih =>
    by_cases hx : stop x
    · simp [iidHitCost, hx]
    · rw [iidHitCost, if_neg hx]
      change n^(t+1) + sumEdge (fun e => iidHitCost next stop t (next x e)) ≤ (t+1)*n^(t+1)
      have h := sumEdge_mono (fun e => iidHitCost next stop t (next x e)) (fun _ => t*n^t)
        (fun e => ih (next x e))
      rw [sumEdge_const] at h
      calc
        _ ≤ n^(t+1) + n * (t*n^t) := Nat.add_le_add_left h _
        _ = _ := by
          simp only [Nat.pow_succ, Nat.add_mul, Nat.one_mul]
          ac_rfl

/-- Integrate a rational geometric tail from a deterministic cutoff. The
survival probability after the cutoff is bounded by c*(b/(a*n))^t.
The post-cut mean allowance k must satisfy a*n*c + k*b <= a*n*k.
Here a single tail can already represent the union of all tags. No limit,
floating logarithms, or independence between tags is needed. -/
theorem expected_of_cutoff_tail {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (x : α)
    (a b c cutoff k : Nat) (ha : 0 < a)
    (hpay : a*n*c + k*b ≤ a*n*k)
    (htail : ∀ t, a^t * survival next (fun y => ¬ stop y) (cutoff+t) x ≤
      c * n^cutoff * b^t) :
    IIDExpectedHittingTimeAtMost next stop x (cutoff+k) := by
  let cost := fun t => iidHitCost next stop t x
  let E := fun t => survival next (fun y => ¬ stop y) t x
  have hrec (t : Nat) : cost (t+1) = n * (cost t + E t) :=
    iidHitCost_succ_eq next stop t x
  have hind (t : Nat) : a^t * cost (cutoff + t) + k * n^cutoff * b^t ≤
      a^t * ((cutoff+k) * n^(cutoff+t)) := by
    induction t with
    | zero =>
      have h := iidHitCost_le_horizon next stop cutoff x
      simpa [cost, Nat.add_mul] using Nat.add_le_add_right h (k*n^cutoff)
    | succ t ih =>
      have he : a^t * E (cutoff+t) ≤ c * n^cutoff * b^t := htail t
      have h1 : a*n * (a^t * cost (cutoff+t) + a^t * E (cutoff+t))
            + k * n^cutoff * (b^t * b) ≤
          a*n * (a^t * cost (cutoff+t) + c * n^cutoff * b^t)
            + k * n^cutoff * (b^t * b) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_left he _)) _
      have h2 : a*n * (a^t * cost (cutoff+t) + c * n^cutoff * b^t)
            + k * n^cutoff * (b^t * b) ≤
          a*n * (a^t * cost (cutoff+t) + k * n^cutoff * b^t) := by
        calc
          _ = a*n * (a^t * cost (cutoff+t)) + (a*n*c + k*b) * (n^cutoff * b^t) := by
            simp only [Nat.mul_add, Nat.add_mul]
            ac_rfl
          _ ≤ a*n * (a^t * cost (cutoff+t)) + (a*n*k) * (n^cutoff * b^t) :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ hpay) _
          _ = _ := by rw [Nat.mul_add]; ac_rfl
      calc
        _ = a*n * (a^t * cost (cutoff+t) + a^t * E (cutoff+t))
              + k * n^cutoff * (b^t * b) := by
          rw [show cutoff+(t+1)=cutoff+t+1 from (Nat.add_assoc ..).symm, hrec, Nat.pow_succ a, Nat.pow_succ b]
          simp only [Nat.mul_add]
          ac_rfl
        _ ≤ _ := h1
        _ ≤ _ := h2
        _ ≤ a*n * (a^t * ((cutoff+k) * n^(cutoff+t))) := Nat.mul_le_mul_left _ ih
        _ = _ := by
          rw [show cutoff+(t+1)=cutoff+t+1 from (Nat.add_assoc ..).symm,
            Nat.pow_succ n (cutoff+t), Nat.pow_succ a t]
          ac_rfl
  intro T
  by_cases hT : T ≤ cutoff
  · exact Nat.le_trans (iidHitCost_le_horizon next stop T x)
          (Nat.mul_le_mul_right _ (by omega))
  · have heq : cutoff + (T-cutoff) = T := by omega
    have h := hind (T-cutoff)
    rw [heq] at h
    exact Nat.le_of_mul_le_mul_left (Nat.le_trans (Nat.le_add_right ..) h) (Nat.pow_pos ha)

/-- Conditional all-tag bound at the numerical cutoff in the elementary
7/8 exponential argument. The premise is the *per-tag tail*, not merely
its mean. The maximum is integrated in one shot. The physical proof must
still supply the premise from predictable debt and gate labels. -/
theorem allTags_expected_of_tail {α : Type} {n m : Nat}
    (next : α → Fin n → α) (live : Fin m → α → Prop) (x : α)
    (hn : 0 < n) (hm : m ≤ n)
    (habsorb : ∀ i y e, live i (next y e) → live i y)
    (htail : ∀ i t, 6^t * survival next (live i) (144*n^2+t) x ≤
      n^(144*n^2) * (6*n-1)^t) :
    IIDExpectedHittingTimeAtMost next (fun y => ¬∃ i, live i y) x (150*n^2) := by
  have hmul : 6*n*m ≤ 6*n^2 := by
    rw [Nat.pow_succ, Nat.pow_one, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hm
  have hpay : 6*n*m + (6*n^2)*(6*n-1) ≤ 6*n*(6*n^2) := by
    calc
      _ ≤ (6*n^2) + (6*n^2)*(6*n-1) := Nat.add_le_add_right hmul _
      _ = _ := by
        have h : 1 + (6*n-1) = 6*n := by omega
        calc
          _ = (6*n^2)*(1+(6*n-1)) := by rw [Nat.mul_add, Nat.mul_one]
          _ = _ := by rw [h, Nat.mul_comm]
  have htotal := expected_of_cutoff_tail next (fun y => ¬∃ i, live i y) x
    6 (6*n-1) m (144*n^2) (6*n^2) (by decide) hpay (fun t => by
      have hsame : (fun y => ¬¬∃ i, live i y) = fun y => ∃ i, live i y :=
        funext (fun _ => propext not_not)
      rw [hsame]
      calc
        _ ≤ 6^t * sumEdge (fun i => survival next (live i) (144*n^2+t) x) :=
          Nat.mul_le_mul_left _ (survival_union next live habsorb _ x)
        _ = sumEdge (fun i => 6^t * survival next (live i) (144*n^2+t) x) :=
          (sumEdge_scale ..).symm
        _ ≤ sumEdge (fun _ : Fin m => n^(144*n^2)*(6*n-1)^t) :=
          sumEdge_mono _ _ (fun i => htail i t)
        _ = _ := by rw [sumEdge_const, Nat.mul_assoc])
  simpa [show 144*n^2+6*n^2 = 150*n^2 by omega] using htotal

end L4.TaggedTail

#print axioms L4.TaggedTail.weightedSurvival_le
#print axioms L4.TaggedTail.threshold_mul_survival_le
#print axioms L4.TaggedTail.survival_contraction
#print axioms L4.TaggedTail.survival_union
#print axioms L4.TaggedTail.iidHitCost_succ_eq
#print axioms L4.TaggedTail.iidHitCost_le_horizon
#print axioms L4.TaggedTail.expected_of_cutoff_tail
#print axioms L4.TaggedTail.allTags_expected_of_tail

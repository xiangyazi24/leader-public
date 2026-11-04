import Leader.Core.FiniteUniformStoppingTree

/-!
# Exact dyadic tails for a nonincreasing leader count

All counts below are `FiniteUniformStoppingTree.treeWeight` sums on the
original raw scheduler. Blocks retain their actual endpoint state. In
particular, neither independent geometric variables nor optional stopping
occur in the argument. Physical deletion mass, invariant closure, and the
final two-leader estimate are inputs, not concentration assumptions.
-/

namespace LeaderCountDyadicTail

open FiniteUniformStoppingTree

set_option autoImplicit false

/-! ## Raw-state sums inside the existing stopping-tree semantics -/

/-- Keep every physical endpoint, including endpoints already below the
current bin. Stopping is expressed by zero leaf weight. -/
def rawStep {S : Type} {n : Nat} (step : S → Fin n → S)
    (x : S) (e : Fin n) : StopNode S := .active (step x e)

/-- Extend a physical-state weight by zero at the two unused terminal nodes. -/
def rawWeight {S : Type} (w : S → Nat) : StopNode S → Nat
  | .active x => w x
  | .success => 0
  | .failure => 0

/-- Exact numerator over the `n^T` literal raw scheduler words. This is only
an abbreviation for the project's stopping-tree sum. -/
def wordSum {S : Type} {n : Nat} (step : S → Fin n → S)
    (w : S → Nat) (x : S) (T : Nat) : Nat :=
  treeWeight (rawStep step) (rawWeight w) (.active x) T

@[simp] theorem wordSum_zero {S : Type} {n : Nat}
    (step : S → Fin n → S) (w : S → Nat) (x : S) :
    wordSum step w x 0 = w x := rfl

@[simp] theorem wordSum_succ {S : Type} {n : Nat}
    (step : S → Fin n → S) (w : S → Nat) (x : S) (T : Nat) :
    wordSum step w x (T + 1) =
      (List.ofFn (fun e : Fin n => wordSum step w (step x e) T)).sum := rfl

/-- A closed predicate restricts comparison to actual reachable states. -/
theorem wordSum_mono_on {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e))
    (w v : S → Nat) (h : ∀ x, P x → w x ≤ v x) :
    ∀ T x, P x → wordSum step w x T ≤ wordSum step v x T := by
  intro T
  induction T with
  | zero => exact h
  | succ T ih =>
      intro x hx
      exact ofFn_sum_le _ _ (fun e => ih (step x e) (hclosed x e hx))

/-- Exact finite sums distribute over a common factor. -/
theorem wordSum_mul {S : Type} {n : Nat}
    (step : S → Fin n → S) (a : Nat) (w : S → Nat) :
    ∀ x T, wordSum step (fun y => a * w y) x T = a * wordSum step w x T := by
  intro x T
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [wordSum_succ]
      exact (ofFn_sum_eq _ _ (fun e => ih (step x e))).trans
        (ofFn_sum_mul_left a _)

/-- Exact finite sums distribute over addition. -/
theorem wordSum_add {S : Type} {n : Nat}
    (step : S → Fin n → S) (w v : S → Nat) :
    ∀ x T, wordSum step (fun y => w y + v y) x T =
      wordSum step w x T + wordSum step v x T := by
  intro x T
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [wordSum_succ]
      exact (ofFn_sum_eq _ _ (fun e => ih (step x e))).trans (ofFn_sum_add _ _)

/-- A constant physical-state weight counts all `n^T` raw words. -/
theorem wordSum_const {S : Type} {n : Nat}
    (step : S → Fin n → S) (c : Nat) :
    ∀ x T, wordSum step (fun _ => c) x T = n ^ T * c := by
  intro x T
  induction T generalizing x with
  | zero => simp
  | succ T ih =>
      simp only [wordSum_succ]
      rw [ofFn_sum_eq _ _ (fun e => ih (step x e)), ofFn_sum_const]
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

/-- Split raw words at a deterministic boundary and retain the actual
prefix endpoint as the suffix's initial state. -/
theorem wordSum_horizon_add {S : Type} {n : Nat}
    (step : S → Fin n → S) (w : S → Nat) :
    ∀ x T U, wordSum step w x (T + U) =
      wordSum step (fun y => wordSum step w y U) x T := by
  intro x T U
  induction T generalizing x with
  | zero => simp
  | succ T ih =>
      rw [Nat.succ_add]
      exact ofFn_sum_eq _ _ (fun e => ih (step x e))

/-- A pathwise nonincreasing weight is bounded by its initial value at
every leaf; the proof is finite induction over scheduler words. -/
theorem wordSum_le_initial {S : Type} {n : Nat}
    (step : S → Fin n → S) (w : S → Nat)
    (hstep : ∀ x e, w (step x e) ≤ w x) :
    ∀ x T, wordSum step w x T ≤ n ^ T * w x := by
  intro x T
  induction T generalizing x with
  | zero => simp
  | succ T ih =>
      calc
        wordSum step w x (T + 1) ≤
            (List.ofFn (fun _ : Fin n => n ^ T * w x)).sum :=
          ofFn_sum_le _ _ (fun e =>
            Nat.le_trans (ih (step x e)) (Nat.mul_le_mul_left _ (hstep x e)))
        _ = n ^ (T + 1) * w x := by
          rw [ofFn_sum_const, Nat.pow_succ]
          ac_rfl

/-! ## An elementary integer half-life inequality -/

/-- Integer Bernoulli inequality in a division-free form. It follows by
induction, retaining only the constant and linear terms. -/
theorem bernoulli_scaled (a j : Nat) :
    (a + j) * a ^ j ≤ a * (a + 1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hcoef : (a + (j + 1)) * a ≤ (a + j) * (a + 1) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
        omega
      calc
        (a + (j + 1)) * a ^ (j + 1) =
            ((a + (j + 1)) * a) * a ^ j := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ ((a + j) * (a + 1)) * a ^ j := Nat.mul_le_mul_right _ hcoef
        _ = ((a + j) * a ^ j) * (a + 1) := by ac_rfl
        _ ≤ (a * (a + 1) ^ j) * (a + 1) := Nat.mul_le_mul_right _ ih
        _ = a * (a + 1) ^ (j + 1) := by simp only [Nat.pow_succ, Nat.mul_assoc]

/-- The contraction `(d-1)/d` loses at least half its mass in `d` steps.
This derives, in particular, `2*(2Q-1)^(2Q) ≤ (2Q)^(2Q)`; it is not an input. -/
theorem integer_half_life (d : Nat) (hd : 1 ≤ d) :
    2 * (d - 1) ^ d ≤ d ^ d := by
  by_cases hone : d = 1
  · subst d; decide
  · have ha : 0 < d - 1 := by omega
    have hb := bernoulli_scaled (d - 1) d
    have he : d - 1 + 1 = d := by omega
    rw [he] at hb
    have hc : (d - 1) * (2 * (d - 1) ^ d) ≤ (d - 1) * d ^ d := by
      calc
        (d - 1) * (2 * (d - 1) ^ d) = (2 * (d - 1)) * (d - 1) ^ d := by ac_rfl
        _ ≤ (d - 1 + d) * (d - 1) ^ d :=
          Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := hb
    exact Nat.le_of_mul_le_mul_left hc ha

/-! ## The dyadic residual for one leader-count bin -/

/-- A bin `(m,2m]` has zero potential after exit, and `2^(k-m)` otherwise.
An actual leader drop halves this residual while the count stays in the bin. -/
def binPotential (m k : Nat) : Nat := if k ≤ m then 0 else 2 ^ (k - m)

/-- Indicator of not having exited the bin. -/
def binMiss (m k : Nat) : Nat := if k ≤ m then 0 else 1

theorem binPotential_mono {m k l : Nat} (hkl : k ≤ l) :
    binPotential m k ≤ binPotential m l := by
  by_cases hk : k ≤ m
  · simp [binPotential, hk]
  · have hl : ¬ l ≤ m := by omega
    simp only [binPotential, if_neg hk, if_neg hl]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hkl m)

/-- Strict decrease of the actual count halves the nonzero residual,
including a jump all the way out of the bin. -/
theorem binPotential_drop {m k l : Nat} (hkl : k < l) :
    2 * binPotential m k ≤ binPotential m l := by
  by_cases hk : k ≤ m
  · simp [binPotential, hk]
  · have hl : ¬ l ≤ m := by omega
    simp only [binPotential, if_neg hk, if_neg hl]
    calc
      2 * 2 ^ (k - m) = 2 ^ (k - m + 1) := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- This pointwise inequality preserves the strict-deletion indicator;
summing it is the entire one-block exponential-moment argument. -/
theorem binPotential_charge {m k l : Nat} (hkl : k ≤ l) :
    2 * binPotential m k +
        binPotential m l * (if k < l then 1 else 0) ≤
      2 * binPotential m l := by
  by_cases h : k < l
  · simp only [if_pos h, Nat.mul_one]
    have hd := binPotential_drop (m := m) h
    omega
  · have he : k = l := by omega
    subst k
    simp

theorem binMiss_le_potential (m k : Nat) : binMiss m k ≤ binPotential m k := by
  by_cases h : k ≤ m
  · simp [binMiss, binPotential, h]
  · simp only [binMiss, binPotential, if_neg h]
    exact Nat.one_le_pow _ _ (by decide)

theorem binPotential_le_of_le_twice {m k : Nat} (h : k ≤ 2 * m) :
    binPotential m k ≤ 2 ^ m := by
  by_cases hm : k ≤ m
  · simp [binPotential, hm]
  · simp only [binPotential, if_neg hm]
    exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Uniform actual deletion mass in a bin gives the exact exponential
residual contraction. The mass premise concerns a strict physical count
drop from this block's actual starting state. -/
theorem bin_one_block_contraction {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (m H Q : Nat)
    (hQ : 1 ≤ Q)
    (hstep : ∀ x e, count (step x e) ≤ count x)
    (hmass : ∀ x, m < count x → count x ≤ 2 * m →
      n ^ H ≤ Q * wordSum step (fun y => if count y < count x then 1 else 0) x H)
    (x : S) (hx : count x ≤ 2 * m) :
    (2 * Q) * wordSum step (fun y => binPotential m (count y)) x H ≤
      (2 * Q - 1) * n ^ H * binPotential m (count x) := by
  let w : S → Nat := fun y => binPotential m (count y)
  by_cases hactive : m < count x
  · let drop : S → Nat := fun y => if count y < count x then 1 else 0
    have hcharge : 2 * wordSum step w x H + w x * wordSum step drop x H ≤
        n ^ H * (2 * w x) := by
      rw [← wordSum_mul, ← wordSum_mul, ← wordSum_add]
      rw [← wordSum_const step (2 * w x) x H]
      exact wordSum_mono_on step (fun y => count y ≤ count x)
        (fun y e hy => Nat.le_trans (hstep y e) hy) _ _
        (fun y hy => binPotential_charge hy) H x (Nat.le_refl _)
    have hm : n ^ H ≤ Q * wordSum step drop x H := hmass x hactive hx
    have hscaled : (2 * Q) * wordSum step w x H +
        w x * (Q * wordSum step drop x H) ≤ (2 * Q) * n ^ H * w x := by
      have h := Nat.mul_le_mul_left Q hcharge
      simpa only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    have hcredit : n ^ H * w x ≤ w x * (Q * wordSum step drop x H) := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (w x) hm
    have heq : (2 * Q) * n ^ H * w x =
        (2 * Q - 1) * n ^ H * w x + n ^ H * w x := by
      have hd : 2 * Q = (2 * Q - 1) + 1 := by omega
      calc
        _ = ((2 * Q - 1) + 1) * n ^ H * w x :=
          congrArg (fun a => a * n ^ H * w x) hd
        _ = _ := by simp [Nat.add_mul]
    change (2 * Q) * wordSum step w x H ≤ (2 * Q - 1) * n ^ H * w x
    omega
  · have hw : w x = 0 := by simp [w, binPotential, Nat.le_of_not_gt hactive]
    have hzero := wordSum_le_initial step w
      (fun y e => binPotential_mono (hstep y e)) x H
    rw [hw, Nat.mul_zero] at hzero
    change (2 * Q) * wordSum step w x H ≤ (2 * Q - 1) * n ^ H * w x
    rw [hw, Nat.mul_zero, Nat.eq_zero_of_le_zero hzero, Nat.mul_zero]
    exact Nat.le_refl _

/-- Iterate any finite-word weighted contraction on a closed state domain.
Every suffix starts at its own physical endpoint; no independence is assumed. -/
theorem iterate_contraction {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e))
    (w : S → Nat) (H d c : Nat)
    (hblock : ∀ x, P x → d * wordSum step w x H ≤ c * n ^ H * w x) :
    ∀ J x, P x → d ^ J * wordSum step w x (J * H) ≤
      (c * n ^ H) ^ J * w x := by
  intro J
  induction J with
  | zero => intro x _; simp
  | succ J ih =>
      intro x hx
      have ht : (J + 1) * H = H + J * H := by simp [Nat.add_mul, Nat.add_comm]
      rw [ht, wordSum_horizon_add, Nat.pow_succ]
      calc
        d ^ J * d * wordSum step (fun y => wordSum step w y (J * H)) x H =
            d * wordSum step (fun y => d ^ J * wordSum step w y (J * H)) x H := by
          rw [wordSum_mul]
          ac_rfl
        _ ≤ d * wordSum step (fun y => (c * n ^ H) ^ J * w y) x H :=
          Nat.mul_le_mul_left d (wordSum_mono_on step P hclosed _ _ (ih ·) H x hx)
        _ = (c * n ^ H) ^ J * (d * wordSum step w x H) := by
          rw [wordSum_mul]
          ac_rfl
        _ ≤ (c * n ^ H) ^ J * (c * n ^ H * w x) :=
          Nat.mul_le_mul_left _ (hblock x hx)
        _ = (c * n ^ H) ^ (J + 1) * w x := by simp only [Nat.pow_succ, Nat.mul_assoc]

/-- A block contraction with multiplier `(d-1)/d` gives a half-mass
contraction after exactly `d` blocks, by the proved integer inequality. -/
theorem half_life_contraction {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e))
    (w : S → Nat) (H d : Nat) (hd : 1 ≤ d)
    (hblock : ∀ x, P x → d * wordSum step w x H ≤ (d - 1) * n ^ H * w x)
    (x : S) (hx : P x) :
    2 * wordSum step w x (d * H) ≤ n ^ (d * H) * w x := by
  have hit := iterate_contraction step P hclosed w H d (d - 1) hblock d x hx
  have hhalf := integer_half_life d hd
  have hlarge : d ^ d * (2 * wordSum step w x (d * H)) ≤
      d ^ d * (n ^ (d * H) * w x) := by
    calc
      d ^ d * (2 * wordSum step w x (d * H)) =
          2 * (d ^ d * wordSum step w x (d * H)) := by ac_rfl
      _ ≤ 2 * (( (d - 1) * n ^ H) ^ d * w x) := Nat.mul_le_mul_left 2 hit
      _ = (2 * (d - 1) ^ d) * (n ^ (d * H) * w x) := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
        simp only [Nat.mul_comm H d]
        ac_rfl
      _ ≤ d ^ d * (n ^ (d * H) * w x) := Nat.mul_le_mul_right _ hhalf
  exact Nat.le_of_mul_le_mul_left hlarge (Nat.pow_pos (by omega))

/-- True finite-count tail for a bin `(m,2m]`: after `2Q*(m+s)` physical
blocks the number of words still above `m` is at most a `2^-s` fraction.
The sole random-progress input is one actual count drop with mass `1/Q`
from every current state in the bin. -/
theorem bin_tail {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (m H Q s : Nat)
    (hQ : 1 ≤ Q)
    (hstep : ∀ x e, count (step x e) ≤ count x)
    (hmass : ∀ x, m < count x → count x ≤ 2 * m →
      n ^ H ≤ Q * wordSum step (fun y => if count y < count x then 1 else 0) x H)
    (x : S) (hx : count x ≤ 2 * m) :
    2 ^ s * wordSum step (fun y => binMiss m (count y)) x
        ((m + s) * (2 * Q * H)) ≤ n ^ ((m + s) * (2 * Q * H)) := by
  let P : S → Prop := fun y => count y ≤ 2 * m
  let w : S → Nat := fun y => binPotential m (count y)
  have hclosed : ∀ y e, P y → P (step y e) :=
    fun y e hy => Nat.le_trans (hstep y e) hy
  have hhalf : ∀ y, P y →
      2 * wordSum step w y (2 * Q * H) ≤ 1 * n ^ (2 * Q * H) * w y := by
    intro y hy
    simpa only [Nat.one_mul] using
      half_life_contraction step P hclosed w H (2 * Q) (by omega)
        (fun z hz => bin_one_block_contraction step count m H Q hQ hstep hmass z hz) y hy
  have hit := iterate_contraction step P hclosed w (2 * Q * H) 2 1 hhalf (m + s) x hx
  simp only [Nat.one_mul, ← Nat.pow_mul, Nat.mul_comm (2 * Q * H) (m + s)] at hit
  have hmiss : wordSum step (fun y => binMiss m (count y)) x
        ((m + s) * (2 * Q * H)) ≤ wordSum step w x ((m + s) * (2 * Q * H)) :=
    wordSum_mono_on step P hclosed _ _ (fun y _ => binMiss_le_potential _ _)
      _ x hx
  have hstart : w x ≤ 2 ^ m := binPotential_le_of_le_twice hx
  have hlarge : 2 ^ m * (2 ^ s * wordSum step (fun y => binMiss m (count y)) x
        ((m + s) * (2 * Q * H))) ≤
      2 ^ m * n ^ ((m + s) * (2 * Q * H)) := by
    calc
      _ = 2 ^ (m + s) * wordSum step (fun y => binMiss m (count y)) x
          ((m + s) * (2 * Q * H)) := by simp only [Nat.pow_add, Nat.mul_assoc]
      _ ≤ 2 ^ (m + s) * wordSum step w x ((m + s) * (2 * Q * H)) :=
        Nat.mul_le_mul_left _ hmiss
      _ ≤ n ^ ((m + s) * (2 * Q * H)) * w x := hit
      _ ≤ n ^ ((m + s) * (2 * Q * H)) * 2 ^ m := Nat.mul_le_mul_left _ hstart
      _ = _ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hlarge (Nat.pow_pos (by decide))

/-! ## Adaptive composition of the descending dyadic bins -/

/-- A bounded leaf weight gives the corresponding total-word bound. -/
theorem wordSum_le_const {S : Type} {n : Nat}
    (step : S → Fin n → S) (w : S → Nat) (c : Nat)
    (hw : ∀ y, w y ≤ c) (x : S) (T : Nat) :
    wordSum step w x T ≤ n ^ T * c := by
  rw [← wordSum_const step c x T]
  exact wordSum_mono_on step (fun _ => True) (fun _ _ _ => True.intro)
    w (fun _ => c) (fun y _ => hw y) T x True.intro

theorem binMiss_le_one (m k : Nat) : binMiss m k ≤ 1 := by
  unfold binMiss
  split <;> omega

theorem binMiss_mono {m k l : Nat} (hkl : k ≤ l) :
    binMiss m k ≤ binMiss m l := by
  unfold binMiss
  split <;> split <;> omega

/-- Rounded physical budget for a single bin. -/
def binTime (H : Nat → Nat) (Q s m : Nat) : Nat := (m + s) * (2 * Q * H m)

/-- Execute bins in descending order: first `(2^(L+1),2^(L+2)]`,
then the `L` smaller bins. The final target is at most two leaders. -/
def dyadicTime (H : Nat → Nat) (Q s : Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => binTime H Q s (2 ^ (L + 1)) + dyadicTime H Q s L

/-- Exact union bound on adaptive physical endpoints. There are `L` bins,
each with failure mass at most `2^-s`; early jumps across several bins need
no artificial restart or extra charge. -/
theorem dyadic_tail {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (H : Nat → Nat) (Q s : Nat)
    (hQ : 1 ≤ Q)
    (hstep : ∀ x e, count (step x e) ≤ count x)
    (hmass : ∀ m, 2 ≤ m → ∀ x, m < count x → count x ≤ 2 * m →
      n ^ H m ≤ Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H m)) :
    ∀ L x, count x ≤ 2 ^ (L + 1) →
      2 ^ s * wordSum step (fun y => binMiss 2 (count y)) x (dyadicTime H Q s L) ≤
        L * n ^ dyadicTime H Q s L := by
  intro L
  induction L with
  | zero =>
      intro x hx
      have hx2 : count x ≤ 2 := by simpa using hx
      simp [dyadicTime, binMiss, hx2]
  | succ L ih =>
      intro x hx
      let m := 2 ^ (L + 1)
      let T := binTime H Q s m
      let U := dyadicTime H Q s L
      let bad : S → Nat := fun y => binMiss 2 (count y)
      have hm : 2 ≤ m := by
        change 2 ^ 1 ≤ 2 ^ (L + 1)
        exact Nat.pow_le_pow_right (by decide) (by omega)
      have hxbin : count x ≤ 2 * m := by
        simpa only [Nat.pow_succ, Nat.mul_comm, m] using hx
      have htop : 2 ^ s * wordSum step (fun y => binMiss m (count y)) x T ≤ n ^ T :=
        bin_tail step count m (H m) Q s hQ hstep (hmass m hm) x hxbin
      have hsuffix : ∀ y, 2 ^ s * wordSum step bad y U ≤
          L * n ^ U + (2 ^ s * n ^ U) * binMiss m (count y) := by
        intro y
        by_cases hy : count y ≤ m
        · simpa only [bad, U, binMiss, if_pos hy, Nat.mul_zero, Nat.add_zero] using ih y hy
        · have hbound : wordSum step bad y U ≤ n ^ U := by
            simpa only [Nat.mul_one] using wordSum_le_const step bad 1
              (fun z => binMiss_le_one _ _) y U
          have h := Nat.mul_le_mul_left (2 ^ s) hbound
          simp only [binMiss, if_neg hy, Nat.mul_one]
          omega
      change 2 ^ s * wordSum step bad x (T + U) ≤ (L + 1) * n ^ (T + U)
      rw [wordSum_horizon_add, ← wordSum_mul]
      calc
        wordSum step (fun y => 2 ^ s * wordSum step bad y U) x T ≤
            wordSum step (fun y => L * n ^ U +
              (2 ^ s * n ^ U) * binMiss m (count y)) x T :=
          wordSum_mono_on step (fun _ => True) (fun _ _ _ => True.intro)
            _ _ (fun y _ => hsuffix y) T x True.intro
        _ = L * n ^ (T + U) +
            n ^ U * (2 ^ s * wordSum step (fun y => binMiss m (count y)) x T) := by
          rw [wordSum_add, wordSum_const, wordSum_mul, Nat.pow_add]
          ac_rfl
        _ ≤ L * n ^ (T + U) + n ^ U * n ^ T :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ htop) _
        _ = (L + 1) * n ^ (T + U) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.pow_add]
          ac_rfl

/-- Attach a separately proved final two-leader tail. The result is still
one exact count on one physical scheduler tree, with `L+1` failure terms. -/
theorem dyadic_tail_with_final {S : Type} {n : Nat}
    (step : S → Fin n → S) (count bad : S → Nat) (H : Nat → Nat) (Q s F L : Nat)
    (hQ : 1 ≤ Q) (hbad : ∀ y, bad y ≤ 1)
    (hstep : ∀ x e, count (step x e) ≤ count x)
    (hmass : ∀ m, 2 ≤ m → ∀ x, m < count x → count x ≤ 2 * m →
      n ^ H m ≤ Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H m))
    (hfinal : ∀ y, count y ≤ 2 → 2 ^ s * wordSum step bad y F ≤ n ^ F)
    (x : S) (hx : count x ≤ 2 ^ (L + 1)) :
    2 ^ s * wordSum step bad x (dyadicTime H Q s L + F) ≤
      (L + 1) * n ^ (dyadicTime H Q s L + F) := by
  let T := dyadicTime H Q s L
  have hprefix := dyadic_tail step count H Q s hQ hstep hmass L x hx
  have hsuffix : ∀ y, 2 ^ s * wordSum step bad y F ≤
      n ^ F + (2 ^ s * n ^ F) * binMiss 2 (count y) := by
    intro y
    by_cases hy : count y ≤ 2
    · simpa only [binMiss, if_pos hy, Nat.mul_zero, Nat.add_zero] using hfinal y hy
    · have hb : wordSum step bad y F ≤ n ^ F := by
        simpa only [Nat.mul_one] using wordSum_le_const step bad 1 hbad y F
      have h := Nat.mul_le_mul_left (2 ^ s) hb
      simp only [binMiss, if_neg hy, Nat.mul_one]
      omega
  change 2 ^ s * wordSum step bad x (T + F) ≤ (L + 1) * n ^ (T + F)
  rw [wordSum_horizon_add, ← wordSum_mul]
  calc
    wordSum step (fun y => 2 ^ s * wordSum step bad y F) x T ≤
        wordSum step (fun y => n ^ F + (2 ^ s * n ^ F) * binMiss 2 (count y)) x T :=
      wordSum_mono_on step (fun _ => True) (fun _ _ _ => True.intro)
        _ _ (fun y _ => hsuffix y) T x True.intro
    _ = n ^ (T + F) + n ^ F *
        (2 ^ s * wordSum step (fun y => binMiss 2 (count y)) x T) := by
      rw [wordSum_add, wordSum_const, wordSum_mul, Nat.pow_add]
      ac_rfl
    _ ≤ n ^ (T + F) + n ^ F * (L * n ^ T) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hprefix) _
    _ = (L + 1) * n ^ (T + F) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.pow_add]
      ac_rfl

/-! ## Rounded dyadic physical-time sum -/

/-- A finite sum over bin lower endpoints `2,4,...,2^L`. -/
def dyadicSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => f (2 ^ (L + 1)) + dyadicSum f L

private theorem dyadicSum_congr (f g : Nat → Nat) (h : ∀ m, f m = g m) :
    ∀ L, dyadicSum f L = dyadicSum g L := by
  intro L
  induction L with
  | zero => rfl
  | succ L ih => simp only [dyadicSum, h, ih]

private theorem dyadicSum_add (f g : Nat → Nat) :
    ∀ L, dyadicSum (fun m => f m + g m) L = dyadicSum f L + dyadicSum g L := by
  intro L
  induction L with
  | zero => rfl
  | succ L ih => simp only [dyadicSum, ih]; ac_rfl

private theorem dyadicSum_mul (a : Nat) (f : Nat → Nat) :
    ∀ L, dyadicSum (fun m => a * f m) L = a * dyadicSum f L := by
  intro L
  induction L with
  | zero => simp [dyadicSum]
  | succ L ih => simp only [dyadicSum, ih, Nat.mul_add]

private theorem dyadicSum_const (c L : Nat) : dyadicSum (fun _ => c) L = L * c := by
  induction L with
  | zero => simp [dyadicSum]
  | succ L ih => simp only [dyadicSum, ih, Nat.add_mul, Nat.one_mul]; ac_rfl

private theorem dyadicSum_le_const (f : Nat → Nat) (C : Nat) :
    ∀ L, (∀ j, j < L → f (2 ^ (j + 1)) ≤ C) → dyadicSum f L ≤ L * C := by
  intro L
  induction L with
  | zero => intro _; simp [dyadicSum]
  | succ L ih =>
      intro h
      have ht := ih (fun j hj => h j (by omega))
      have hh := h L (by omega)
      simp only [dyadicSum, Nat.add_mul, Nat.one_mul]
      omega

private theorem dyadicSum_shift (f : Nat → Nat) :
    ∀ L, dyadicSum f (L + 1) = f 2 + dyadicSum (fun m => f (2 * m)) L := by
  intro L
  induction L with
  | zero => simp [dyadicSum]
  | succ L ih =>
      change f (2 ^ ((L + 1) + 1)) + dyadicSum f (L + 1) =
        f 2 + (f (2 * 2 ^ (L + 1)) + dyadicSum (fun m => f (2 * m)) L)
      rw [ih, Nat.pow_succ]
      simp only [Nat.mul_comm (2 ^ (L + 1)) 2]
      ac_rfl

/-- The sum of the rounded inverse dyadic scales is at most the numerator.
Induction uses `floor(x/2)+floor(x/4)+...`, with no real-number analysis. -/
theorem dyadic_div_sum_le (x L : Nat) : dyadicSum (fun m => x / m) L ≤ x := by
  induction L generalizing x with
  | zero => simp [dyadicSum]
  | succ L ih =>
      rw [dyadicSum_shift]
      have he : dyadicSum (fun m => x / (2 * m)) L =
          dyadicSum (fun m => (x / 2) / m) L :=
        dyadicSum_congr _ _ (fun m => (Nat.div_div_eq_div_mul x 2 m).symm) L
      rw [he]
      have ht := ih (x / 2)
      have hd := Nat.mul_div_le x 2
      omega

/-- One extra interaction safely includes integer rounding of a rational
bound `A*n*n/k+B*n`. No per-bin rounding term is discarded. -/
def levelBlock (n A B m : Nat) : Nat := A * n * n / m + B * n + 1

/-- Separate the deterministic cost of the necessary drops from the tail
slack. This is an algebraic identity, not an expected-time telescope. -/
theorem dyadicTime_eq_sum (H : Nat → Nat) (Q s : Nat) :
    ∀ L, dyadicTime H Q s L =
      (2 * Q) * (dyadicSum (fun m => m * H m) L + s * dyadicSum H L) := by
  intro L
  induction L with
  | zero => simp [dyadicTime, dyadicSum]
  | succ L ih =>
      simp only [dyadicTime, binTime, dyadicSum, ih, Nat.add_mul, Nat.mul_add]
      ac_rfl

private theorem linear_square_bound (n A B : Nat) (hn : 1 ≤ n) :
    A * n * n + n * (B * n + 1) ≤ (A + B + 1) * n * n := by
  have hn2 : n ≤ n * n := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hn
  calc
    _ = (A + B) * n * n + n := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
      ac_rfl
    _ ≤ (A + B) * n * n + n * n := Nat.add_le_add_left hn2 _
    _ = _ := by simp only [Nat.add_mul, Nat.one_mul]

/-- Explicit aggregate bound including every rounded block. Its two terms
are the number of bins and the logarithmic failure slack. -/
theorem dyadicTime_le (n A B Q s L : Nat) (hn : 1 ≤ n)
    (hL : L ≤ n) (hpow : 2 ^ L ≤ n) :
    dyadicTime (levelBlock n A B) Q s L ≤
      (2 * Q) * ((A + B + 1) * n * n) * (L + s) := by
  let C := (A + B + 1) * n * n
  have hw : dyadicSum (fun m => m * levelBlock n A B m) L ≤ L * C := by
    apply dyadicSum_le_const
    intro j hj
    have hm : 2 ^ (j + 1) ≤ n :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hpow
    change 2 ^ (j + 1) * (A * n * n / 2 ^ (j + 1) + (B * n + 1)) ≤ C
    rw [Nat.mul_add]
    have hdiv := Nat.mul_div_le (A * n * n) (2 ^ (j + 1))
    have hlinear := Nat.mul_le_mul_right (B * n + 1) hm
    exact Nat.le_trans (Nat.add_le_add hdiv hlinear) (linear_square_bound n A B hn)
  have hu : dyadicSum (levelBlock n A B) L ≤ C := by
    have he : dyadicSum (levelBlock n A B) L =
        dyadicSum (fun m => A * n * n / m) L + L * (B * n + 1) := by
      have hfun : levelBlock n A B = fun m => A * n * n / m + (B * n + 1) := by
        funext m
        simp only [levelBlock, Nat.add_assoc]
      rw [hfun, dyadicSum_add, dyadicSum_const]
    rw [he]
    exact Nat.le_trans
      (Nat.add_le_add (dyadic_div_sum_le _ L) (Nat.mul_le_mul_right _ hL))
      (linear_square_bound n A B hn)
  rw [dyadicTime_eq_sum]
  calc
    (2 * Q) * (dyadicSum (fun m => m * levelBlock n A B m) L +
        s * dyadicSum (levelBlock n A B) L) ≤ (2 * Q) * (L * C + s * C) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add hw (Nat.mul_le_mul_left _ hu))
    _ = (2 * Q) * ((A + B + 1) * n * n) * (L + s) := by
      simp only [Nat.mul_add, Nat.add_mul, C]
      ac_rfl

/-- Convenient logarithmic slack; `log2 n + 1` is an integer upper bound
for `ceil(log2 n)`, differing by one only at exact powers of two. -/
def logSlack (n : Nat) : Nat := 2 * (Nat.log2 n + 1) + 1

private theorem succ_le_two_pow (L : Nat) : L + 1 ≤ 2 ^ L := by
  induction L with
  | zero => decide
  | succ L ih =>
      rw [Nat.pow_succ]
      have hp := Nat.two_pow_pos L
      omega

/-- Elementary floor-log facts used by both the count and clock bounds. -/
theorem log_parameters (n : Nat) (hn : 2 ≤ n) :
    1 ≤ Nat.log2 n ∧ Nat.log2 n + 1 ≤ n ∧
      2 ^ Nat.log2 n ≤ n ∧ n ≤ 2 ^ (Nat.log2 n + 1) := by
  have hn0 : n ≠ 0 := by omega
  have hlo : 2 ^ Nat.log2 n ≤ n := by
    by_cases h : 2 ^ Nat.log2 n ≤ n
    · exact h
    · have hlt : n < 2 ^ Nat.log2 n := by omega
      have hbad := (Nat.log2_lt hn0).2 hlt
      omega
  have hhi : n < 2 ^ (Nat.log2 n + 1) := (Nat.log2_lt hn0).1 (by omega)
  have hpos : 1 ≤ Nat.log2 n := by
    by_cases h : 1 ≤ Nat.log2 n
    · exact h
    · have hz : Nat.log2 n = 0 := by omega
      rw [hz] at hhi
      simp only [Nat.zero_add] at hhi
      omega
  exact ⟨hpos, Nat.le_trans (succ_le_two_pow _) hlo, hlo, Nat.le_of_lt hhi⟩

/-- The complete dyadic stage costs at most `12Q(A+B+1)n² floor(log₂ n)`
physical interactions. In particular, it does not add a second logarithm. -/
theorem dyadicTime_log_bound (n A B Q : Nat) (hn : 2 ≤ n) :
    dyadicTime (levelBlock n A B) Q (logSlack n) (Nat.log2 n) ≤
      12 * Q * (A + B + 1) * n * n * Nat.log2 n := by
  obtain ⟨hpos, hL, hpow, _⟩ := log_parameters n hn
  have ht := dyadicTime_le n A B Q (logSlack n) (Nat.log2 n) (by omega) (by omega) hpow
  have hs : Nat.log2 n + logSlack n ≤ 6 * Nat.log2 n := by
    unfold logSlack
    omega
  exact Nat.le_trans ht (by
    have h := Nat.mul_le_mul_left ((2 * Q) * ((A + B + 1) * n * n)) hs
    have he : (2 * Q) * ((A + B + 1) * n * n) * (6 * Nat.log2 n) =
        12 * Q * (A + B + 1) * n * n * Nat.log2 n := by
      have h12 : 12 = 2 * 6 := by decide
      rw [h12]
      ac_rfl
    rw [he] at h
    exact h)

/-! ## From level-dependent physical deletion to the final WHP bound -/

/-- A persistent nonnegative leaf weight survives every suffix, with the
exact `n^T` multiplicity. This is the padding rule for an actual deletion. -/
theorem wordSum_ge_initial {S : Type} {n : Nat}
    (step : S → Fin n → S) (w : S → Nat)
    (hstep : ∀ x e, w x ≤ w (step x e)) :
    ∀ x T, n ^ T * w x ≤ wordSum step w x T := by
  intro x T
  induction T generalizing x with
  | zero => simp
  | succ T ih =>
      calc
        n ^ (T + 1) * w x =
            (List.ofFn (fun _ : Fin n => n ^ T * w x)).sum := by
          rw [ofFn_sum_const, Nat.pow_succ]
          ac_rfl
        _ ≤ wordSum step w x (T + 1) :=
          ofFn_sum_le _ _ (fun e =>
            Nat.le_trans (Nat.mul_le_mul_left _ (hstep x e)) (ih (step x e)))

/-- A lower deletion-mass bound remains valid after padding to a larger
physical horizon. The comparison uses the same actual state and raw words. -/
theorem pad_deletion_mass {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat)
    (hstep : ∀ x e, count (step x e) ≤ count x)
    (x : S) (Q H U : Nat) (hHU : H ≤ U)
    (hmass : n ^ H ≤ Q * wordSum step (fun y => if count y < count x then 1 else 0) x H) :
    n ^ U ≤ Q * wordSum step (fun y => if count y < count x then 1 else 0) x U := by
  obtain ⟨K, hU⟩ := Nat.exists_eq_add_of_le hHU
  subst U
  let w : S → Nat := fun y => if count y < count x then 1 else 0
  have hpersist : ∀ y e, w y ≤ w (step y e) := by
    intro y e
    have hle := hstep y e
    unfold w
    split <;> split <;> omega
  have hpad : n ^ K * wordSum step w x H ≤ wordSum step w x (H + K) := by
    rw [wordSum_horizon_add, ← wordSum_mul]
    exact wordSum_mono_on step (fun _ => True) (fun _ _ _ => True.intro)
      _ _ (fun y _ => wordSum_ge_initial step w hpersist y K) H x True.intro
  calc
    n ^ (H + K) = n ^ K * n ^ H := by rw [Nat.pow_add]; ac_rfl
    _ ≤ n ^ K * (Q * wordSum step w x H) := Nat.mul_le_mul_left _ hmass
    _ = Q * (n ^ K * wordSum step w x H) := by ac_rfl
    _ ≤ Q * wordSum step w x (H + K) := Nat.mul_le_mul_left _ hpad

/-- Convert a state-uniform, level-dependent actual deletion bound into the
fixed horizon used by each bin. The only enlargement is integer rounding
and replacing the current count by the lower endpoint of its bin. -/
theorem level_mass_to_bin_mass {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (H : Nat → Nat) (A B Q : Nat)
    (hstep : ∀ x e, count (step x e) ≤ count x)
    (hH : ∀ x, 3 ≤ count x → H (count x) ≤ levelBlock n A B (count x))
    (hmass : ∀ x, 3 ≤ count x → n ^ H (count x) ≤
      Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H (count x))) :
    ∀ m, 2 ≤ m → ∀ x, m < count x → count x ≤ 2 * m →
      n ^ levelBlock n A B m ≤
        Q * wordSum step (fun y => if count y < count x then 1 else 0) x
          (levelBlock n A B m) := by
  intro m hm x hk _
  have hk3 : 3 ≤ count x := by omega
  have hdiv : A * n * n / count x ≤ A * n * n / m :=
    Nat.div_le_div_left (by omega) (by omega)
  have hblock : H (count x) ≤ levelBlock n A B m := by
    have hlocal := hH x hk3
    unfold levelBlock at hlocal ⊢
    omega
  exact pad_deletion_mass step count hstep x Q (H (count x))
    (levelBlock n A B m) hblock (hmass x hk3)

/-- The chosen slack pays for every dyadic bin and one final two-leader
stage, leaving total failure at most `1/n`. -/
theorem logSlack_union_bound (n : Nat) (hn : 2 ≤ n) :
    n * (Nat.log2 n + 1) ≤ 2 ^ logSlack n := by
  obtain ⟨_, hcard, _, hupper⟩ := log_parameters n hn
  calc
    n * (Nat.log2 n + 1) ≤ n * n := Nat.mul_le_mul_left n hcard
    _ ≤ 2 ^ (Nat.log2 n + 1) * 2 ^ (Nat.log2 n + 1) := Nat.mul_le_mul hupper hupper
    _ = 2 ^ ((Nat.log2 n + 1) + (Nat.log2 n + 1)) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ logSlack n := Nat.pow_le_pow_right (by decide) (by unfold logSlack; omega)

/-- Exact finite-word `1/n` failure bound with a concrete `O(n² log n)`
deterministic physical horizon. The inputs are actual leader monotonicity,
uniform physical deletion mass by `H_k`, its level-dependent clock bound,
and the separately supplied two-leader tail and clock. No concentration
conclusion is carried as a field. -/
theorem leader_whp {S : Type} {n : Nat}
    (step : S → Fin n → S) (count bad : S → Nat) (H : Nat → Nat)
    (A B Q D F : Nat) (hn : 2 ≤ n) (hQ : 1 ≤ Q)
    (hstep : ∀ x e, count (step x e) ≤ count x)
    (hbad : ∀ x, bad x ≤ 1)
    (hH : ∀ x, 3 ≤ count x → H (count x) ≤ levelBlock n A B (count x))
    (hmass : ∀ x, 3 ≤ count x → n ^ H (count x) ≤
      Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H (count x)))
    (hfinal : ∀ x, count x ≤ 2 →
      2 ^ logSlack n * wordSum step bad x F ≤ n ^ F)
    (hF : F ≤ D * n * n * Nat.log2 n)
    (x : S) (hx : count x ≤ n) :
    let T := dyadicTime (levelBlock n A B) Q (logSlack n) (Nat.log2 n) + F
    n * wordSum step bad x T ≤ n ^ T ∧
      T ≤ (12 * Q * (A + B + 1) + D) * n * n * Nat.log2 n := by
  dsimp only
  let T := dyadicTime (levelBlock n A B) Q (logSlack n) (Nat.log2 n) + F
  have hstart : count x ≤ 2 ^ (Nat.log2 n + 1) :=
    Nat.le_trans hx (log_parameters n hn).2.2.2
  have htail : 2 ^ logSlack n * wordSum step bad x T ≤
      (Nat.log2 n + 1) * n ^ T :=
    dyadic_tail_with_final step count bad (levelBlock n A B) Q (logSlack n) F
      (Nat.log2 n) hQ hbad hstep
      (level_mass_to_bin_mass step count H A B Q hstep hH hmass) hfinal x hstart
  have hfailure : n * wordSum step bad x T ≤ n ^ T := by
    have hscaled : 2 ^ logSlack n * (n * wordSum step bad x T) ≤
        2 ^ logSlack n * n ^ T := by
      calc
        _ = n * (2 ^ logSlack n * wordSum step bad x T) := by ac_rfl
        _ ≤ n * ((Nat.log2 n + 1) * n ^ T) := Nat.mul_le_mul_left n htail
        _ = (n * (Nat.log2 n + 1)) * n ^ T := by ac_rfl
        _ ≤ _ := Nat.mul_le_mul_right _ (logSlack_union_bound n hn)
    exact Nat.le_of_mul_le_mul_left hscaled (Nat.two_pow_pos _)
  refine ⟨hfailure, ?_⟩
  have ht := Nat.add_le_add (dyadicTime_log_bound n A B Q hn) hF
  simpa only [Nat.add_mul] using ht

/-! ## Closed physical domains without changing the scheduler -/

/-- Restrict the state carrier to a proved closed physical domain. The raw
edge and actual successor configuration are unchanged. -/
def restrictedStep {S : Type} {n : Nat} (step : S → Fin n → S)
    (P : S → Prop) (hclosed : ∀ x e, P x → P (step x e))
    (x : {y // P y}) (e : Fin n) : {y // P y} :=
  ⟨step x.val e, hclosed x.val e x.property⟩

/-- Subtype restriction preserves the exact word sum, not merely its bound.
Thus domain closure handles adaptive restart states on the original process. -/
theorem wordSum_restrict {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (w : S → Nat) :
    ∀ T (x : {y // P y}),
      wordSum (restrictedStep step P hclosed) (fun y => w y.val) x T =
        wordSum step w x.val T := by
  intro T
  induction T with
  | zero => intro x; rfl
  | succ T ih =>
      intro x
      exact ofFn_sum_eq _ _ (fun e => ih (restrictedStep step P hclosed x e))

/-- Consumer form with all physical assumptions restricted to a closed
domain. Unreachable or illegal raw configurations carry no progress premise.
The conclusion still counts words of the original physical transition. -/
theorem leader_whp_on_closed_domain {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e))
    (count bad : S → Nat) (H : Nat → Nat)
    (A B Q D F : Nat) (hn : 2 ≤ n) (hQ : 1 ≤ Q)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x)
    (hbad : ∀ x, P x → bad x ≤ 1)
    (hH : ∀ x, P x → 3 ≤ count x → H (count x) ≤ levelBlock n A B (count x))
    (hmass : ∀ x, P x → 3 ≤ count x → n ^ H (count x) ≤
      Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H (count x)))
    (hfinal : ∀ x, P x → count x ≤ 2 →
      2 ^ logSlack n * wordSum step bad x F ≤ n ^ F)
    (hF : F ≤ D * n * n * Nat.log2 n)
    (x : S) (hPx : P x) (hx : count x ≤ n) :
    let T := dyadicTime (levelBlock n A B) Q (logSlack n) (Nat.log2 n) + F
    n * wordSum step bad x T ≤ n ^ T ∧
      T ≤ (12 * Q * (A + B + 1) + D) * n * n * Nat.log2 n := by
  let stepP := restrictedStep step P hclosed
  have hmassP : ∀ y : {z // P z}, 3 ≤ count y.val → n ^ H (count y.val) ≤
      Q * wordSum stepP (fun z => if count z.val < count y.val then 1 else 0)
        y (H (count y.val)) := by
    intro y hy
    rw [wordSum_restrict step P hclosed
      (fun z => if count z < count y.val then 1 else 0) (H (count y.val)) y]
    exact hmass y.val y.property hy
  have hfinalP : ∀ y : {z // P z}, count y.val ≤ 2 →
      2 ^ logSlack n * wordSum stepP (fun z => bad z.val) y F ≤ n ^ F := by
    intro y hy
    rw [wordSum_restrict]
    exact hfinal y.val y.property hy
  have h := leader_whp stepP (fun y => count y.val) (fun y => bad y.val) H
    A B Q D F hn hQ (fun y e => hstep y.val e y.property)
    (fun y => hbad y.val y.property) (fun y => hH y.val y.property) hmassP hfinalP hF ⟨x, hPx⟩ hx
  simpa only [stepP, wordSum_restrict] using h

/-- Leader-count-specific consumer: the bad words are exactly those whose
physical endpoint still has more than one leader. The final-stage premise
is required only from states already having at most two leaders. If the
physical invariant also guarantees at least one leader, this is the exact
unique-leader failure event. -/
theorem leader_count_whp_on_closed_domain {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e))
    (count : S → Nat) (H : Nat → Nat)
    (A B Q D F : Nat) (hn : 2 ≤ n) (hQ : 1 ≤ Q)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x)
    (hH : ∀ x, P x → 3 ≤ count x → H (count x) ≤ levelBlock n A B (count x))
    (hmass : ∀ x, P x → 3 ≤ count x → n ^ H (count x) ≤
      Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H (count x)))
    (hfinal : ∀ x, P x → count x ≤ 2 →
      2 ^ logSlack n * wordSum step (fun y => binMiss 1 (count y)) x F ≤ n ^ F)
    (hF : F ≤ D * n * n * Nat.log2 n)
    (x : S) (hPx : P x) (hx : count x ≤ n) :
    let T := dyadicTime (levelBlock n A B) Q (logSlack n) (Nat.log2 n) + F
    n * wordSum step (fun y => binMiss 1 (count y)) x T ≤ n ^ T ∧
      T ≤ (12 * Q * (A + B + 1) + D) * n * n * Nat.log2 n := by
  exact leader_whp_on_closed_domain step P hclosed count
    (fun y => binMiss 1 (count y)) H A B Q D F hn hQ hstep
    (fun y _ => binMiss_le_one _ _) hH hmass hfinal hF x hPx hx

/-! ## A nontrivial finite physical process -/

/-- Four possible positive leader counts and one control bit. The bit
changes at every interaction, so the deletion edge depends on the actual
restart state. -/
abbrev ToyState := Fin 4 × Bool

/-- The true edge deletes one leader unless only one remains; all other
edges preserve the count. Every edge flips the control bit. -/
def toyStep (x : ToyState) (e : Fin 4) : ToyState :=
  (⟨if e.val = (if x.2 then 1 else 0) then x.1.val - 1 else x.1.val, by
    have h := x.1.isLt
    split <;> split <;> omega⟩, !x.2)

/-- Physical leader count for the finite example. -/
def toyCount (x : ToyState) : Nat := x.1.val + 1

/-- The finite example never creates a leader. -/
theorem toy_count_nonincreasing (x : ToyState) (e : Fin 4) :
    toyCount (toyStep x e) ≤ toyCount x := by
  unfold toyCount toyStep
  split <;> split <;> simp only <;> omega

/-- Exactly one of the four raw edges strictly deletes a leader whenever
more than one remains. This is a derived finite sum, not an assumed mass. -/
theorem toy_drop_mass (x : ToyState) (hx : 2 ≤ toyCount x) :
    wordSum toyStep (fun y => if toyCount y < toyCount x then 1 else 0) x 1 = 1 := by
  have hd : x.1.val - 1 + 1 < x.1.val + 1 := by unfold toyCount at hx; omega
  rcases x with ⟨k, b⟩
  cases b <;>
    simp [wordSum_succ, List.ofFn_succ, toyStep, toyCount] at hd ⊢ <;> exact hd

/-- The example's supplied two-leader tail is itself proved by the bin
theorem, with `m=1`, `Q=4`, and a 64-interaction horizon. -/
theorem toy_final_tail (x : ToyState) (hx : toyCount x ≤ 2) :
    2 ^ logSlack 4 * wordSum toyStep (fun y => binMiss 1 (toyCount y)) x 64 ≤ 4 ^ 64 := by
  have hm : ∀ y, 1 < toyCount y → toyCount y ≤ 2 * 1 →
      4 ^ 1 ≤ 4 * wordSum toyStep
        (fun z => if toyCount z < toyCount y then 1 else 0) y 1 := by
    intro y hy _
    rw [toy_drop_mass y (by omega)]
    decide
  have h := bin_tail toyStep toyCount 1 1 4 (logSlack 4) (by decide)
    toy_count_nonincreasing hm x hx
  exact h

/-- The example has a surviving bad word at every finite horizon: edge 2
never deletes, whatever the alternating control bit. Thus the tail result
does not reduce to a deterministic finite-time extinction calculation. -/
theorem toy_miss_positive : ∀ T (x : ToyState), 2 ≤ toyCount x →
    1 ≤ wordSum toyStep (fun y => binMiss 1 (toyCount y)) x T := by
  intro T
  induction T with
  | zero =>
      intro x hx
      have h : ¬ toyCount x ≤ 1 := by omega
      simp [binMiss, h]
  | succ T ih =>
      intro x hx
      have hkeep : toyCount (toyStep x (2 : Fin 4)) = toyCount x := by
        rcases x with ⟨k, b⟩
        cases b <;> simp [toyStep, toyCount]
      have hh := ih (toyStep x (2 : Fin 4)) (by omega)
      simp only [wordSum_succ, List.ofFn_succ, List.ofFn_zero,
        List.sum_cons, List.sum_nil]
      simp only [show (0 : Fin 2).succ.succ = (2 : Fin 4) from rfl]
      omega

/-- A fully instantiated finite-process consequence: from four leaders,
the number of bad 224-edge words is at most one quarter of all words.
The starting control bit is concrete, and every progress premise is proved. -/
theorem toy_whp :
    4 * wordSum toyStep (fun y => binMiss 1 (toyCount y)) (⟨3, by decide⟩, false) 224 ≤
      4 ^ 224 := by
  have hm : ∀ x, 3 ≤ toyCount x → 4 ^ (fun _ : Nat => 1) (toyCount x) ≤
      4 * wordSum toyStep (fun y => if toyCount y < toyCount x then 1 else 0) x
        ((fun _ : Nat => 1) (toyCount x)) := by
    intro x hx
    rw [toy_drop_mass x (by omega)]
    change 4 ≤ 4
    decide
  have h := leader_whp toyStep toyCount (fun y => binMiss 1 (toyCount y))
    (fun _ => 1) 0 0 4 2 64 (by decide) (by decide)
    toy_count_nonincreasing (fun x => binMiss_le_one _ _)
    (fun k _ => by simp [levelBlock]) hm toy_final_tail (by decide)
    (⟨3, by decide⟩, false) (by decide)
  have ht : dyadicTime (levelBlock 4 0 0) 4 (logSlack 4) (Nat.log2 4) + 64 = 224 := by
    decide
  simpa only [ht] using h.1

end LeaderCountDyadicTail

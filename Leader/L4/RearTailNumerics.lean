import Leader.L4.TaggedTail
import Leader.L4.TaggedTailKernel
import Leader.L4.RearTrace

/-!
# Exact rear-clock numerical tail constants
No probability library or floating arithmetic is required.
-/

namespace L4.RearTailNumerics
open Classical

/-- Numerators of (7/8)^(-1), (7/8)^0, (7/8)^1 and (7/8)^2
with common denominator 448, in that order. -/
theorem local_kernel_constants :
    12 * (392 : Nat) ≤ 11 * 448 ∧
      12 * (512 + 343 : Nat) ≤ 23 * 448 := by decide

private theorem neighboring_power (d k : Nat) :
    d^(k+1) + (k+1)*d^k ≤ (d+1)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : (k+1)*d^(k+1) = ((k+1)*d^k)*d := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    calc
      _ = (d^(k+1)*d + d^(k+1)) + (k+1)*d^(k+1) := by
        rw [Nat.pow_succ d (k+1), show k.succ + 1 = (k+1)+1 from rfl,
          Nat.add_mul, Nat.one_mul]
        ac_rfl
      _ ≤ (d^(k+1)*d + d^(k+1)) + ((k+1)*d^(k+1)+(k+1)*d^k) :=
        Nat.add_le_add_left (Nat.le_add_right ..) _
      _ = (d^(k+1)+(k+1)*d^k)*(d+1) := by
        rw [he]
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
        ac_rfl
      _ ≤ (d+1)^(k+1)*(d+1) := Nat.mul_le_mul_right _ ih
      _ = _ := (Nat.pow_succ ..).symm

/-- One block of 12n marks halves the rational tail (when normalized). -/
theorem half_block (n : Nat) (hn : 0 < n) :
    2 * (12*n-1)^(12*n) ≤ (12*n)^(12*n) := by
  let d := 12*n-1
  have hd : d+1 = 12*n := by dsimp [d]; omega
  have h := neighboring_power d d
  have hmono : d*d^d ≤ (d+1)*d^d := Nat.mul_le_mul_right _ (by omega)
  have h' : 2*d^(d+1) ≤ d^(d+1)+(d+1)*d^d := by
    rw [Nat.pow_succ, Nat.mul_comm (d^d) d]
    omega
  exact hd ▸ (Nat.le_trans h' h)

private theorem prefactor (n : Nat) (hn : 0 < n) :
    8^(12*n+2) ≤ 7^(12*n+2) * 2^(3*n) := by
  let k := 12*n+2
  let d := 15*n-k
  have he : k+d = 15*n := by dsimp [k,d]; omega
  have h : (8:Nat)^5 ≤ 7^5*2 := by decide
  have h' := Nat.pow_le_pow_left h (3*n)
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
    show 5 * (3*n) = 15*n by omega] at h'
  have hb : 7^d * 8^k ≤ 7^d * (7^k*2^(3*n)) := by
    calc
      _ ≤ 8^d * 8^k := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _)
      _ = 8^(15*n) := by rw [← Nat.pow_add, Nat.add_comm d k, he]
      _ ≤ 7^(15*n)*2^(3*n) := h'
      _ = _ := by rw [← he, Nat.pow_add]; ac_rfl
  exact Nat.le_of_mul_le_mul_left hb (Nat.pow_pos (by decide))

/-- The prefactor (8/7)^((12*n+2)) is paid by 3*n half-blocks. -/
theorem numerical_cutoff (n : Nat) (hn : 0 < n) :
    8^((12*n+2)) * (12*n-1)^(36*n^2) ≤ 7^((12*n+2)) * (12*n)^(36*n^2) := by
  have hh := Nat.pow_le_pow_left (half_block n hn) (3*n)
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hh
  have he : 12*n*(3*n) = 36*n^2 := by
    rw [Nat.pow_succ, Nat.pow_one]
    ac_rfl
  rw [he] at hh
  calc
    _ ≤ (7^((12*n+2)) * 2^(3*n)) * (12*n-1)^(36*n^2) :=
      Nat.mul_le_mul_right _ (prefactor n hn)
    _ = 7^((12*n+2)) * (2^(3*n) * (12*n-1)^(36*n^2)) := Nat.mul_assoc ..
    _ ≤ _ := Nat.mul_le_mul_left _ hh

/-- Cancel horizon-dependent weight normalization and the deterministic
36*n² prefix. T is the auxiliary exponent shift, not a probability
parameter. The result is exactly the post-cutoff survival form. -/
theorem cutoff_of_horizon_weight {n t s T : Nat} (hn : 0 < n)
    (h : 12^(36*n^2+t) * 7^((12*n+2)+T) * s ≤
      (12*n-1)^(36*n^2+t) * 7^(T) * 8^((12*n+2))) :
    12^t*s ≤ n^(36*n^2) * (12*n-1)^t := by
  let L := 36*n^2
  let K := (12*n+2)
  let b := 12*n-1
  have hL : 8^K * b^L ≤ 7^K * (12*n)^L := numerical_cutoff n hn
  have h' : (12^L * 7^K * 7^(T)) * (12^t*s) ≤
      (12^L * 7^K * 7^(T)) * (n^L*b^t) := by
    calc
      _ = 12^(L+t)*7^(K+T)*s := by rw [Nat.pow_add 12 L t, Nat.pow_add 7 K T]; ac_rfl
      _ ≤ b^(L+t)*7^(T)*8^K := h
      _ = (7^(T)*b^t) * (8^K*b^L) := by rw [Nat.pow_add]; ac_rfl
      _ ≤ (7^(T)*b^t) * (7^K*(12*n)^L) := Nat.mul_le_mul_left _ hL
      _ = _ := by rw [Nat.mul_pow]; ac_rfl
  exact Nat.le_of_mul_le_mul_left h' (Nat.mul_pos (Nat.mul_pos
    (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide)))

open TaggedTail

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

private theorem sumEdge_scale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a * f e) = a * sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sumEdge_succ, sumEdge_succ f, ih, Nat.mul_add]

private theorem sumEdge_const (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sumEdge_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem sumEdge_add {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumEdge_succ, sumEdge_succ f, sumEdge_succ g, ih]; omega

private theorem sumEdge_selector {n : Nat} (i : Fin n) (a : Nat) :
    sumEdge (fun e => if e = i then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sumEdge_succ]
      have hz : (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then a else 0) =
          (fun _ : Fin n => 0) := by
        funext e
        simp [Fin.succ_ne_zero]
      rw [hz, sumEdge_const]
      simp
    · rw [sumEdge_succ]
      rw [if_neg (Ne.symm (Fin.succ_ne_zero j))]
      have hc : (fun e : Fin n => if e.succ = j.succ then a else 0) =
          (fun e : Fin n => if e = j then a else 0) := by funext e; simp
      rw [hc, ih, Nat.zero_add]

/-- Numerator of the rational 7/8 multiplier with denominator 448,
in the four cases for overlap of the outgoing and rear nominations. -/
def rearRatio {n : Nat} (out rear e : Fin n) : Nat :=
  if e = out then (if e = rear then 392 else 343)
  else if e = rear then 512 else 448

/-- Exact one-mark contraction over the actual uniform edge alphabet. -/
theorem rearRatio_sum_bound {n : Nat} (hn : 0 < n) (out rear : Fin n) :
    12 * sumEdge (rearRatio out rear) ≤ (12*n-1)*448 := by
  by_cases hs : out = rear
  · subst rear
    have h : sumEdge (rearRatio out out) + 56 = n*448 := by
      rw [← sumEdge_selector out 56, ← sumEdge_add, ← sumEdge_const]
      apply congrArg sumEdge
      funext e
      by_cases he : e = out <;> simp [rearRatio, he]
    omega
  · have h : sumEdge (rearRatio out rear) + 105 = n*448 + 64 := by
      rw [← sumEdge_selector out 105, ← sumEdge_selector rear 64,
        ← sumEdge_const, ← sumEdge_add, ← sumEdge_add]
      apply congrArg sumEdge
      funext e
      by_cases he : e = out
      · subst e
        simp [rearRatio, hs]
      · by_cases hr : e = rear
        · subst e
          simp [rearRatio, Ne.symm hs]
        · simp [rearRatio, he, hr]
    omega

/-- Reuse the old generic weight-ratio kernel with the different rear
mark debt. Its common denominator is 3584 times 448. -/
theorem rear_kernel {n : Nat} (hn : 0 < n) (out rear : Fin n) :
    12 * sumEdge (fun e => TaggedTailKernel.ratioNumerator (RearTrace.markDebt out rear e))
      ≤ (12*n-1)*TaggedTailKernel.scale := by
  have h : (fun e => TaggedTailKernel.ratioNumerator (RearTrace.markDebt out rear e)) =
      fun e => 3584 * rearRatio out rear e := by
    funext e
    by_cases ho : e = out
    · by_cases hr : e = rear
      · simp only [RearTrace.markDebt, rearRatio, if_pos ho, if_pos hr]; decide
      · simp only [RearTrace.markDebt, rearRatio, if_pos ho, if_neg hr]; decide
    · by_cases hr : e = rear
      · simp only [RearTrace.markDebt, rearRatio, if_neg ho, if_pos hr]; decide
      · simp only [RearTrace.markDebt, rearRatio, if_neg ho, if_neg hr]; decide
  rw [h, sumEdge_scale]
  change 12 * (3584 * sumEdge (rearRatio out rear)) ≤ (12*n-1)*(3584*448)
  calc
    _ = 3584 * (12 * sumEdge (rearRatio out rear)) := by ac_rfl
    _ ≤ 3584 * ((12*n-1)*448) := Nat.mul_le_mul_left _ (rearRatio_sum_bound hn out rear)
    _ = _ := by ac_rfl

/-- The generic signed-debt weight is allowed to use +2T instead of +T;
cancel the extra common factor explicitly before applying the cutoff. -/
theorem cancel_extra_shift {n T s : Nat}
    (h : 12^T*7^(12*n+2+2*T)*s ≤ (12*n-1)^T*7^(2*T)*8^(12*n+2)) :
    12^T*7^(12*n+2+T)*s ≤ (12*n-1)^T*7^T*8^(12*n+2) := by
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (7 : Nat)^T from Nat.pow_pos (by decide))
  calc
    _ = 12^T*7^(12*n+2+2*T)*s := by
      rw [Nat.two_mul, ← Nat.add_assoc, Nat.pow_add 7 (12*n+2+T) T]
      ac_rfl
    _ ≤ _ := h
    _ = _ := by rw [Nat.two_mul, Nat.pow_add 7 T T]; ac_rfl

/-- No independence between tags is assumed. The numerator premise is the
post-cutoff tail of each individual tag under the common raw edge word. -/
theorem allTags_expected_of_tail {α : Type} {n m : Nat}
    (next : α → Fin n → α) (live : Fin m → α → Prop) (x : α)
    (hn : 0 < n) (hm : m ≤ n)
    (habsorb : ∀ i y e, live i (next y e) → live i y)
    (htail : ∀ i t, 12^t * TaggedTail.survival next (live i) (36*n^2+t) x ≤
      n^(36*n^2) * (12*n-1)^t) :
    IIDExpectedHittingTimeAtMost next (fun y => ¬∃ i, live i y) x (48*n^2) := by
  classical
  have hmul : 12*n*m ≤ 12*n^2 := by
    rw [Nat.pow_succ, Nat.pow_one, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hm
  have hpay : 12*n*m + (12*n^2)*(12*n-1) ≤ 12*n*(12*n^2) := by
    calc
      _ ≤ (12*n^2) + (12*n^2)*(12*n-1) := Nat.add_le_add_right hmul _
      _ = (12*n^2)*(1+(12*n-1)) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by
        have h : 1 + (12*n-1) = 12*n := by omega
        rw [h, Nat.mul_comm]
  have htotal := TaggedTail.expected_of_cutoff_tail next (fun y => ¬∃ i, live i y) x
    12 (12*n-1) m (36*n^2) (12*n^2) (by decide) hpay (fun t => by
      have hsame : (fun y => ¬¬∃ i, live i y) = fun y => ∃ i, live i y :=
        funext (fun _ => propext not_not)
      rw [hsame]
      calc
        _ ≤ 12^t * TaggedTail.sumEdge (fun i => TaggedTail.survival next (live i) (36*n^2+t) x) :=
          Nat.mul_le_mul_left _ (TaggedTail.survival_union next live habsorb _ x)
        _ = TaggedTail.sumEdge (fun i => 12^t * TaggedTail.survival next (live i) (36*n^2+t) x) :=
          (sumEdge_scale ..).symm
        _ ≤ TaggedTail.sumEdge (fun _ : Fin m => n^(36*n^2)*(12*n-1)^t) :=
          sumEdge_mono _ _ (fun i => htail i t)
        _ = _ := by rw [sumEdge_const, Nat.mul_assoc])
  simpa [show 36*n^2+12*n^2 = 48*n^2 by omega] using htotal

/-- Weighted all-horizon per-tag tails imply the all-tags mean after
deterministic prefactor cancellation. -/
theorem allTags_expected_of_weighted_tail {α : Type} {n m : Nat}
    (next : α → Fin n → α) (live : Fin m → α → Prop) (x : α)
    (hn : 0 < n) (hm : m ≤ n)
    (habsorb : ∀ i y e, live i (next y e) → live i y)
    (htail : ∀ i T, 12^T * 7^(12*n+2+T) * TaggedTail.survival next (live i) T x ≤
      (12*n-1)^T * 7^T * 8^(12*n+2)) :
    IIDExpectedHittingTimeAtMost next (fun y => ¬∃ i, live i y) x (48*n^2) :=
  allTags_expected_of_tail next live x hn hm habsorb
    (fun i t => cutoff_of_horizon_weight hn (htail i (36*n^2+t)))

end L4.RearTailNumerics

#print axioms L4.RearTailNumerics.local_kernel_constants
#print axioms L4.RearTailNumerics.half_block
#print axioms L4.RearTailNumerics.cutoff_of_horizon_weight
#print axioms L4.RearTailNumerics.allTags_expected_of_tail
#print axioms L4.RearTailNumerics.allTags_expected_of_weighted_tail
#print axioms L4.RearTailNumerics.rearRatio_sum_bound
#print axioms L4.RearTailNumerics.rear_kernel
#print axioms L4.RearTailNumerics.cancel_extra_shift

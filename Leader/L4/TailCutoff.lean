import Leader.L4.TaggedAll

/-!
# Exact cutoff for the tagged 7/8 survival argument

All inequalities below are cross-multiplied over natural-number
numerators. No choice of floating approximation is needed.
-/

namespace L4.TailCutoff

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

/-- One block of 6n marks halves the rational tail (when normalized). -/
theorem half_block (n : Nat) (hn : 0 < n) :
    2 * (6*n-1)^(6*n) ≤ (6*n)^(6*n) := by
  let d := 6*n-1
  have hd : d+1 = 6*n := by dsimp [d]; omega
  have h := neighboring_power d d
  have hmono : d*d^d ≤ (d+1)*d^d := Nat.mul_le_mul_right _ (by omega)
  have h' : 2*d^(d+1) ≤ d^(d+1)+(d+1)*d^d := by
    rw [Nat.pow_succ, Nat.mul_comm (d^d) d]
    omega
  exact hd ▸ (Nat.le_trans h' h)

private theorem prefactor (n : Nat) :
    8^(120*n) ≤ 7^(120*n) * 2^(24*n) := by
  have h : (8:Nat)^5 ≤ 7^5*2 := by decide
  have h' := Nat.pow_le_pow_left h (24*n)
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h'
  rwa [show 5 * (24*n) = 120*n by omega] at h'

/-- The prefactor (8/7)^(120*n) is paid by 24*n half-blocks. -/
theorem numerical_cutoff (n : Nat) (hn : 0 < n) :
    8^(120*n) * (6*n-1)^(144*n^2) ≤ 7^(120*n) * (6*n)^(144*n^2) := by
  have hh := Nat.pow_le_pow_left (half_block n hn) (24*n)
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hh
  have he : 6*n*(24*n) = 144*n^2 := by
    rw [Nat.pow_succ, Nat.pow_one]
    ac_rfl
  rw [he] at hh
  calc
    _ ≤ (7^(120*n) * 2^(24*n)) * (6*n-1)^(144*n^2) :=
      Nat.mul_le_mul_right _ (prefactor n)
    _ = 7^(120*n) * (2^(24*n) * (6*n-1)^(144*n^2)) := Nat.mul_assoc ..
    _ ≤ _ := Nat.mul_le_mul_left _ hh

/-- Cancel horizon-dependent weight normalization and the deterministic
144*n² prefix. T is the auxiliary exponent shift, not a probability
parameter. The result is exactly the post-cutoff survival form. -/
theorem cutoff_of_horizon_weight {n t s T : Nat} (hn : 0 < n)
    (h : 6^(144*n^2+t) * 7^(120*n+2*T) * s ≤
      (6*n-1)^(144*n^2+t) * 7^(2*T) * 8^(120*n)) :
    6^t*s ≤ n^(144*n^2) * (6*n-1)^t := by
  let L := 144*n^2
  let K := 120*n
  let b := 6*n-1
  have hL : 8^K * b^L ≤ 7^K * (6*n)^L := numerical_cutoff n hn
  have h' : (6^L * 7^K * 7^(2*T)) * (6^t*s) ≤
      (6^L * 7^K * 7^(2*T)) * (n^L*b^t) := by
    calc
      _ = 6^(L+t)*7^(K+2*T)*s := by rw [Nat.pow_add, Nat.pow_add]; ac_rfl
      _ ≤ b^(L+t)*7^(2*T)*8^K := h
      _ = (7^(2*T)*b^t) * (8^K*b^L) := by rw [Nat.pow_add]; ac_rfl
      _ ≤ (7^(2*T)*b^t) * (7^K*(6*n)^L) := Nat.mul_le_mul_left _ hL
      _ = _ := by rw [Nat.mul_pow]; ac_rfl
  exact Nat.le_of_mul_le_mul_left h' (Nat.mul_pos (Nat.mul_pos
    (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide)))

/-- A horizon-limited proof-side augmentation preserves the exact
unweighted survival numerator at every requested depth that fits inside
its budget. In particular, additional live guards at time T+1 are irrelevant
when observing a prefix of length at most T. -/
theorem survival_projection_through_horizon {α β : Type} {n : Nat}
    (nextA : α → Fin n → α) (nextB : β → Fin n → β)
    (liveA : α → Prop) (liveB : β → Prop)
    (project : α → β) (level : α → Nat) (T : Nat)
    (hproj : ∀ x e, project (nextA x e) = nextB (project x) e)
    (hlevel : ∀ x e, level (nextA x e) = level x + 1)
    (hlive : ∀ x, level x ≤ T → (liveA x ↔ liveB (project x)))
    (t : Nat) (x : α) (hfit : level x + t ≤ T) :
    TaggedTail.survival nextA liveA t x = TaggedTail.survival nextB liveB t (project x) := by
  classical
  unfold TaggedTail.survival
  induction t generalizing x with
  | zero =>
    have h := hlive x (by omega)
    by_cases hx : liveA x
    · simp [TaggedTail.weightedSurvival, hx, h.mp hx]
    · have hb : ¬ liveB (project x) := fun h' => hx (h.mpr h')
      simp [TaggedTail.weightedSurvival, hx, hb]
  | succ t ih =>
    have h := hlive x (by omega)
    by_cases hx : liveA x
    · simp only [TaggedTail.weightedSurvival, hx, h.mp hx, if_true]
      apply congrArg TaggedTail.sumEdge
      funext e
      rw [← hproj x e]
      exact ih (nextA x e) (by rw [hlevel]; omega)
    · have hb : ¬ liveB (project x) := fun h' => hx (h.mpr h')
      simp [TaggedTail.weightedSurvival, hx, hb]

open L4.TaggedTrace

/-- Assemble the concrete tag-tail interface once the physical trace has
supplied the all-horizon weighted inequality. -/
theorem concreteTagTail_of_horizon_weight
    (h : ∀ {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) (t : Nat),
      2 ≤ p → 12 ≤ c1 → 4 ≤ n → (¬ p ∣ n) → MCOV x → COV x →
      6^t * 7^(120*n+2*t) *
        TaggedTail.survival advance (fun y => ¬ ended y) t (init x i) ≤
        (6*n-1)^t * 7^(2*t) * 8^(120*n)) :
    ConcreteTagTail := by
  intro p c1 n x i t hp hc hn hnd hmark hcov
  exact cutoff_of_horizon_weight (by omega) (h x i (144*n^2+t) hp hc hn hnd hmark hcov)

end L4.TailCutoff

#print axioms L4.TailCutoff.half_block
#print axioms L4.TailCutoff.numerical_cutoff
#print axioms L4.TailCutoff.cutoff_of_horizon_weight
#print axioms L4.TailCutoff.concreteTagTail_of_horizon_weight
#print axioms L4.TailCutoff.survival_projection_through_horizon

import Leader.L3.Grant.ShortCounter

/-!
# G17: the one-site survival profile of the finite counter

Scaled by `n^t`, the survival probability of an isolated site started at run
value `j` and driven for `t` steps by an incoming reset and an outgoing tick,
each with probability `1/n` per step, is `shortV n K t j`.  This file proves,
over the natural numbers, its monotonicity in `j` and in `t`, and the hazard
lower bound (the drop `V t 0 - V t 1` is at least `V t 0 * alpha / (2^K n^t)`
with `alpha` the forward chain started with a reset).
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The scaled one-site survival profile: `shortV n K t j = n^t * P_j(alive
after t steps)`; run values `≥ K` are dead. -/
def shortV (n K : Nat) : Nat → Nat → Nat
  | 0, j => if j < K then 1 else 0
  | t + 1, j =>
      if j < K then
        (n - 2) * shortV n K t j + shortV n K t (j + 1) + shortV n K t 0
      else 0

/-- Dead run values have zero survival.

Consumer: `shortVTimeMono`. -/
theorem shortV_dead (n K t j : Nat) (hj : K ≤ j) : shortV n K t j = 0 := by
  cases t with
  | zero => simp [shortV, Nat.not_lt.mpr hj]
  | succ t => simp [shortV, Nat.not_lt.mpr hj]

/-- Survival is nonincreasing in time (scaled): `V (t+1) j ≤ n V t j`.

Consumer: `shortProductStep`. -/
theorem shortVTimeMono (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) :
    ∀ t j, shortV n K (t + 1) j ≤ n * shortV n K t j := by
  intro t
  induction t with
  | zero =>
      intro j
      by_cases hj : j < K
      · by_cases hj1 : j + 1 < K
        · simp [shortV, hj, hj1, hK]
          omega
        · simp [shortV, hj, hj1, hK]
          omega
      · simp [shortV, hj]
  | succ t ih =>
      intro j
      by_cases hj : j < K
      · have e1 : shortV n K (t + 1 + 1) j =
            (n - 2) * shortV n K (t + 1) j + shortV n K (t + 1) (j + 1) +
              shortV n K (t + 1) 0 := by
          simp [shortV, hj]
        have e2 : shortV n K (t + 1) j =
            (n - 2) * shortV n K t j + shortV n K t (j + 1) +
              shortV n K t 0 := by
          simp [shortV, hj]
        have h1 := Nat.mul_le_mul_left (n - 2) (ih j)
        have h2 := ih (j + 1)
        have h3 := ih 0
        have e3 : n * shortV n K (t + 1) j =
            (n - 2) * (n * shortV n K t j) +
            n * shortV n K t (j + 1) + n * shortV n K t 0 := by
          rw [e2]
          simp only [Nat.mul_add, Nat.mul_left_comm]
        omega
      · simp [shortV, hj]


/-- The profile is nonincreasing in the run value.

Consumer: `shortProductStep`. -/
theorem shortVMonoJ (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) :
    ∀ t j, shortV n K t (j + 1) ≤ shortV n K t j := by
  intro t
  induction t with
  | zero =>
      intro j
      by_cases hj : j + 1 < K
      · have hj' : j < K := by omega
        simp [shortV, hj, hj']
      · by_cases hj' : j < K
        · simp [shortV, hj, hj']
        · simp [shortV, hj, hj']
  | succ t ih =>
      intro j
      by_cases hj : j + 1 < K
      · have hj' : j < K := by omega
        have e1 : shortV n K (t + 1) (j + 1) =
            (n - 2) * shortV n K t (j + 1) + shortV n K t (j + 1 + 1) +
              shortV n K t 0 := by
          simp [shortV, hj]
        have e2 : shortV n K (t + 1) j =
            (n - 2) * shortV n K t j + shortV n K t (j + 1) +
              shortV n K t 0 := by
          simp [shortV, hj']
        have h1 := Nat.mul_le_mul_left (n - 2) (ih j)
        have h2 := ih (j + 1)
        omega
      · have : shortV n K (t + 1) (j + 1) = 0 := by
          simp [shortV, hj]
        omega

/-- Every value is at most the value at zero.

Consumer: `shortProductStep`. -/
theorem shortVLeZero (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) (t : Nat) :
    ∀ j, shortV n K t j ≤ shortV n K t 0 := by
  intro j
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih => exact Nat.le_trans (shortVMonoJ n K hn hK t j) ih

/-- The scaled profile is at most `n^t`.

Consumer: `shortSumStep`. -/
theorem shortVLePow (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) :
    ∀ t j, shortV n K t j ≤ n ^ t := by
  intro t
  induction t with
  | zero =>
      intro j
      by_cases hj : j < K <;> simp [shortV, hj]
  | succ t ih =>
      intro j
      have h := shortVTimeMono n K hn hK t j
      have h2 := Nat.mul_le_mul_left n (ih j)
      rw [Nat.pow_succ, Nat.mul_comm (n ^ t) n]
      omega

/-- The drop `V t j - V t (j+1)`.

Consumer: `shortHazard`. -/
def shortD (n K t j : Nat) : Nat := shortV n K t j - shortV n K t (j + 1)

/-- The forward chain `alpha t i = n^t 2^(i+1) a_i(t)` started with a reset:
`a_0 = 1/2` and `a_i(t+1) = (1 - 2/n) a_i(t) + a_(i-1)(t)/n`. -/
def shortAlpha (n : Nat) : Nat → Nat → Nat
  | 0, i => if i = 0 then 1 else 0
  | t + 1, 0 => n ^ (t + 1)
  | t + 1, i + 1 => (n - 2) * shortAlpha n t (i + 1) + 2 * shortAlpha n t i

/-- `alpha_0 (t) = n^t`.

Consumer: `shortAlphaLePow`. -/
theorem shortAlpha_zero (n t : Nat) : shortAlpha n t 0 = n ^ t := by
  cases t <;> simp [shortAlpha]

/-- `alpha_i (t) ≤ n^t`.

Consumer: `shortSumStep`. -/
theorem shortAlphaLePow (n : Nat) (hn : 2 ≤ n) :
    ∀ t i, shortAlpha n t i ≤ n ^ t := by
  intro t
  induction t with
  | zero =>
      intro i
      cases i <;> simp [shortAlpha]
  | succ t ih =>
      intro i
      cases i with
      | zero => simp [shortAlpha]
      | succ i =>
          have h1 := Nat.mul_le_mul_left (n - 2) (ih (i + 1))
          have h2 := Nat.mul_le_mul_left 2 (ih i)
          have e : n ^ (t + 1) = (n - 2) * n ^ t + 2 * n ^ t := by
            have hn2 : n = (n - 2) + 2 := by omega
            calc
              n ^ (t + 1) = n ^ t * n := Nat.pow_succ _ _
              _ = n ^ t * ((n - 2) + 2) := by rw [← hn2]
              _ = (n - 2) * n ^ t + 2 * n ^ t := by
                rw [Nat.mul_add, Nat.mul_comm (n ^ t) (n - 2),
                  Nat.mul_comm (n ^ t) 2]
          simp only [shortAlpha]
          omega


/-- Recursion of the drop at the last live value.

Consumer: `shortHazardClaim`. -/
theorem shortD_last (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) (t j : Nat)
    (hj : j + 1 = K) :
    shortD n K (t + 1) j = (n - 2) * shortD n K t j + shortV n K t 0 := by
  have hjK : j < K := by omega
  have e1 : shortV n K (t + 1) j =
      (n - 2) * shortV n K t j + shortV n K t (j + 1) + shortV n K t 0 := by
    simp [shortV, hjK]
  have e2 : shortV n K (t + 1) (j + 1) = 0 :=
    shortV_dead n K (t + 1) (j + 1) (by omega)
  have e3 : shortV n K t (j + 1) = 0 := shortV_dead n K t (j + 1) (by omega)
  unfold shortD
  rw [e2, e3, e1, Nat.sub_zero, Nat.sub_zero, e3]
  omega

/-- Recursion of the drop at an interior value.

Consumer: `shortHazardClaim`. -/
theorem shortD_mid (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) (t j : Nat)
    (hj : j + 1 < K) :
    shortD n K (t + 1) j = (n - 2) * shortD n K t j + shortD n K t (j + 1) := by
  have hjK : j < K := by omega
  have e1 : shortV n K (t + 1) j =
      (n - 2) * shortV n K t j + shortV n K t (j + 1) + shortV n K t 0 := by
    simp [shortV, hjK]
  have e2 : shortV n K (t + 1) (j + 1) =
      (n - 2) * shortV n K t (j + 1) + shortV n K t (j + 1 + 1) +
        shortV n K t 0 := by
    simp [shortV, hj]
  have m1 := shortVMonoJ n K hn hK t j
  have m2 := shortVMonoJ n K hn hK t (j + 1)
  have e4 : (n - 2) * (shortV n K t j - shortV n K t (j + 1)) =
      (n - 2) * shortV n K t j - (n - 2) * shortV n K t (j + 1) :=
    Nat.mul_sub _ _ _
  have e5 : (n - 2) * shortV n K t (j + 1) ≤ (n - 2) * shortV n K t j :=
    Nat.mul_le_mul_left _ m1
  unfold shortD
  rw [e4]
  omega

/-- **Hazard lower bound.**  For `j + i + 1 = K`,
`V t 0 * alpha t i ≤ 2^(i+1) n^t D t j`: the forward chain started with a
reset lower-bounds the drop of the backward profile.

Consumer: `shortHazard`. -/
theorem shortHazardClaim (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) :
    ∀ t i j, j + i + 1 = K →
      shortV n K t 0 * shortAlpha n t i ≤
        2 ^ (i + 1) * n ^ t * shortD n K t j := by
  intro t
  induction t with
  | zero =>
      intro i j hij
      have hV0 : shortV n K 0 0 = 1 := by simp [shortV, hK]
      rw [hV0]
      cases i with
      | zero =>
          have hjK : j + 1 = K := by omega
          have hd : shortD n K 0 j = 1 := by
            unfold shortD
            have e1 : shortV n K 0 j = 1 := by
              simp [shortV]; omega
            have e2 : shortV n K 0 (j + 1) = 0 := by
              simp [shortV]; omega
            omega
          simp [shortAlpha, hd]
      | succ i =>
          simp [shortAlpha]
  | succ t ih =>
      intro i j hij
      have hpos : 0 < n ^ (t + 1) := Nat.pow_pos (by omega)
      have hposT : 0 < n ^ t := Nat.pow_pos (by omega)
      have hTM := shortVTimeMono n K hn hK t 0
      cases i with
      | zero =>
          have hjK : j + 1 = K := by omega
          have h0 := ih 0 j (by omega)
          rw [shortAlpha_zero] at h0
          have h1 : shortV n K t 0 ≤ 2 * shortD n K t j := by
            have h0' : shortV n K t 0 * n ^ t ≤ (2 * shortD n K t j) * n ^ t := by
              calc
                shortV n K t 0 * n ^ t ≤ 2 ^ (0 + 1) * n ^ t * shortD n K t j := h0
                _ = (2 * shortD n K t j) * n ^ t := by
                  simp only [Nat.zero_add, Nat.pow_one]
                  ac_rfl
            exact Nat.le_of_mul_le_mul_right h0' hposT
          have hdl := shortD_last n K hn hK t j hjK
          have h2 := Nat.mul_le_mul_left (n - 2) h1
          have hn2 : (n - 2) * (2 * shortD n K t j) =
              2 * ((n - 2) * shortD n K t j) := by ac_rfl
          have hmain : shortV n K (t + 1) 0 ≤ 2 * shortD n K (t + 1) j := by
            have e : n * shortV n K t 0 = (n - 2) * shortV n K t 0 +
                2 * shortV n K t 0 := by
              have hn2' : n = (n - 2) + 2 := by omega
              calc
                n * shortV n K t 0 = ((n - 2) + 2) * shortV n K t 0 := by
                  rw [← hn2']
                _ = _ := Nat.add_mul _ _ _
            rw [hdl]
            have h3 := Nat.mul_le_mul_left (n - 2) h1
            omega
          rw [shortAlpha_zero]
          calc
            shortV n K (t + 1) 0 * n ^ (t + 1) ≤
                (2 * shortD n K (t + 1) j) * n ^ (t + 1) :=
              Nat.mul_le_mul_right _ hmain
            _ = 2 ^ (0 + 1) * n ^ (t + 1) * shortD n K (t + 1) j := by
              simp only [Nat.zero_add, Nat.pow_one]
              ac_rfl
      | succ i =>
          have hjK : j + 1 < K := by omega
          have hA := ih (i + 1) j (by omega)
          have hB := ih i (j + 1) (by omega)
          have hdl := shortD_mid n K hn hK t j hjK
          have hal : shortAlpha n (t + 1) (i + 1) =
              (n - 2) * shortAlpha n t (i + 1) + 2 * shortAlpha n t i := by
            simp [shortAlpha]
          rw [hal, hdl]
          have s1 := Nat.mul_le_mul_right
            ((n - 2) * shortAlpha n t (i + 1) + 2 * shortAlpha n t i) hTM
          have s2 := Nat.mul_le_mul_left (n * (n - 2)) hA
          have s3 := Nat.mul_le_mul_left (n * 2) hB
          have e1 : n * shortV n K t 0 *
              ((n - 2) * shortAlpha n t (i + 1) + 2 * shortAlpha n t i) =
              n * (n - 2) * (shortV n K t 0 * shortAlpha n t (i + 1)) +
              n * 2 * (shortV n K t 0 * shortAlpha n t i) := by
            simp only [Nat.mul_add]
            ac_rfl
          have e2 : 2 ^ (i + 1 + 1) * n ^ (t + 1) *
              ((n - 2) * shortD n K t j + shortD n K t (j + 1)) =
              n * (n - 2) * (2 ^ (i + 1 + 1) * n ^ t * shortD n K t j) +
              n * 2 * (2 ^ (i + 1) * n ^ t * shortD n K t (j + 1)) := by
            simp only [Nat.pow_succ (2 : Nat) (i + 1), Nat.pow_succ n t,
              Nat.mul_add]
            ac_rfl
          rw [e2]
          omega


/-- The one-step identity `V (t+1) 0 + D t 0 = n V t 0`.

Consumer: `shortHazard`. -/
theorem shortV_zero_step (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) (t : Nat) :
    shortV n K (t + 1) 0 + shortD n K t 0 = n * shortV n K t 0 := by
  have e1 : shortV n K (t + 1) 0 =
      (n - 2) * shortV n K t 0 + shortV n K t 1 + shortV n K t 0 := by
    simp [shortV, hK]
  have m1 := shortVMonoJ n K hn hK t 0
  have e3 : n * shortV n K t 0 = (n - 2) * shortV n K t 0 +
      2 * shortV n K t 0 := by
    have hn2 : n = (n - 2) + 2 := by omega
    calc
      n * shortV n K t 0 = ((n - 2) + 2) * shortV n K t 0 := by
        rw [← hn2]
      _ = _ := Nat.add_mul _ _ _
  unfold shortD
  simp only [Nat.zero_add] at m1 ⊢
  omega

/-- **The hazard inequality.**  With `w = 2^K n^t`,
`w V(t+1,0) + V(t,0) alpha_t ≤ w n V(t,0)`, `alpha_t = alpha t (K-1)`.

Consumer: `shortPowStep`. -/
theorem shortHazard (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) (t : Nat) :
    2 ^ K * n ^ t * shortV n K (t + 1) 0 +
        shortV n K t 0 * shortAlpha n t (K - 1) ≤
      2 ^ K * n ^ t * n * shortV n K t 0 := by
  have hc := shortHazardClaim n K hn hK t (K - 1) 0 (by omega)
  have hid := shortV_zero_step n K hn hK t
  have hK1 : K - 1 + 1 = K := by omega
  rw [hK1] at hc
  have e : 2 ^ K * n ^ t * (shortV n K (t + 1) 0 + shortD n K t 0) =
      2 ^ K * n ^ t * shortV n K (t + 1) 0 +
        2 ^ K * n ^ t * shortD n K t 0 := Nat.mul_add _ _ _
  have e2 : 2 ^ K * n ^ t * (n * shortV n K t 0) =
      2 ^ K * n ^ t * n * shortV n K t 0 := (Nat.mul_assoc _ _ _).symm
  have e3 : 2 ^ K * n ^ t * (shortV n K (t + 1) 0 + shortD n K t 0) =
      2 ^ K * n ^ t * (n * shortV n K t 0) := by rw [hid]
  omega

/-- Natural-number Bernoulli: `A^(k+1) + (k+1) A^k B ≤ (A+B)^(k+1)`.

Consumer: `shortBernoulliCore`. -/
theorem shortBernoulli (A B : Nat) :
    ∀ k, A ^ (k + 1) + (k + 1) * A ^ k * B ≤ (A + B) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := Nat.mul_le_mul_left (A + B) ih
      have e1 : (A + B) * (A ^ (k + 1) + (k + 1) * A ^ k * B) =
          A ^ (k + 1 + 1) + (k + 1) * A ^ (k + 1) * B + A ^ (k + 1) * B +
            (k + 1) * A ^ k * B * B := by
        simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
        ac_rfl
      have e2 : (A + B) ^ (k + 1 + 1) = (A + B) * (A + B) ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have e3 : (k + 1 + 1) * A ^ (k + 1) * B =
          (k + 1) * A ^ (k + 1) * B + A ^ (k + 1) * B := by
        simp only [Nat.add_mul, Nat.one_mul]
      rw [e2, e3]
      omega


/-- Integer form of `(1 - a/n)^n (1 + a) ≤ 1`:
`(w (k+1) - α)^(k+1) (w + α) ≤ (w (k+1))^(k+1) w` for `α ≤ w`.

Consumer: `shortBernoulliStep`. -/
theorem shortBernoulliCore (w α k : Nat) (hw : 0 < w) (hα : α ≤ w) :
    (w * (k + 1) - α) ^ (k + 1) * (w + α) ≤ (w * (k + 1)) ^ (k + 1) * w := by
  have hWn : α ≤ w * (k + 1) := Nat.le_trans hα (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨a, ha⟩ : ∃ a, a = w * (k + 1) - α := ⟨_, rfl⟩
  have hsum : a + α = w * (k + 1) := by omega
  generalize hW : w * (k + 1) = Wn at hsum ha ⊢
  rw [← ha]
  have hprod : a * (Wn + α) ≤ Wn * Wn := by
    rw [← hsum]
    have hc := Nat.mul_comm a α
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have hpow : a ^ (k + 1) * (Wn + α) ^ (k + 1) ≤ Wn ^ (k + 1) * Wn ^ (k + 1) := by
    rw [← Nat.mul_pow, ← Nat.mul_pow]
    exact Nat.pow_le_pow_left hprod _
  have hb := shortBernoulli Wn α k
  have hWnpos : 0 < Wn := by
    rw [← hW]
    exact Nat.mul_pos hw (by omega)
  have e0 : Wn + (k + 1) * α = (k + 1) * (w + α) := by
    rw [← hW]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    have c1 := Nat.mul_comm k w
    have c2 := Nat.mul_comm k α
    omega
  have e1 : Wn ^ (k + 1) + (k + 1) * Wn ^ k * α = Wn ^ k * ((k + 1) * (w + α)) := by
    calc
      Wn ^ (k + 1) + (k + 1) * Wn ^ k * α =
          Wn ^ k * Wn + Wn ^ k * ((k + 1) * α) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = Wn ^ k * (Wn + (k + 1) * α) := by rw [Nat.mul_add]
      _ = Wn ^ k * ((k + 1) * (w + α)) := by rw [e0]
  have h3 := Nat.mul_le_mul_left (a ^ (k + 1)) hb
  rw [e1] at h3
  have h4 : a ^ (k + 1) * (Wn ^ k * ((k + 1) * (w + α))) ≤
      Wn ^ k * (Wn ^ (k + 1) * (w * (k + 1))) := by
    calc
      _ ≤ a ^ (k + 1) * (Wn + α) ^ (k + 1) := h3
      _ ≤ Wn ^ (k + 1) * Wn ^ (k + 1) := hpow
      _ = Wn ^ k * (Wn ^ (k + 1) * Wn) := by
        simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = Wn ^ k * (Wn ^ (k + 1) * (w * (k + 1))) := by rw [hW]
  have h5 : (a ^ (k + 1) * (w + α)) * (k + 1) ≤
      (Wn ^ (k + 1) * w) * (k + 1) := by
    have hp : 0 < Wn ^ k := Nat.pow_pos hWnpos
    have h6 : Wn ^ k * ((a ^ (k + 1) * (w + α)) * (k + 1)) ≤
        Wn ^ k * ((Wn ^ (k + 1) * w) * (k + 1)) := by
      calc
        _ = a ^ (k + 1) * (Wn ^ k * ((k + 1) * (w + α))) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ _ := h4
        _ = _ := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    exact Nat.le_of_mul_le_mul_left h6 hp
  exact Nat.le_of_mul_le_mul_right h5 (by omega)

/-- **One Bernoulli step.**  From `w σ' + σ α ≤ w n σ` (`n = k+1`,
`α ≤ w`) the `n`-th powers satisfy `σ'^n (w + α) ≤ n^n w σ^n`.

Consumer: `shortPowStep`. -/
theorem shortBernoulliStep (σ σ' w α k : Nat) (hw : 0 < w) (hα : α ≤ w)
    (H : w * σ' + σ * α ≤ w * (k + 1) * σ) :
    σ' ^ (k + 1) * (w + α) ≤ (k + 1) ^ (k + 1) * w * σ ^ (k + 1) := by
  have hWn : α ≤ w * (k + 1) := Nat.le_trans hα (Nat.le_mul_of_pos_right _ (by omega))
  have h1 : w * σ' ≤ σ * (w * (k + 1) - α) := by
    have e : σ * (w * (k + 1) - α) + σ * α = σ * (w * (k + 1)) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hWn]
    have e2 : σ * (w * (k + 1)) = w * (k + 1) * σ := Nat.mul_comm _ _
    omega
  have h2 : (w * σ') ^ (k + 1) ≤ (σ * (w * (k + 1) - α)) ^ (k + 1) :=
    Nat.pow_le_pow_left h1 _
  have h3 := shortBernoulliCore w α k hw hα
  have h4 : (w * σ') ^ (k + 1) * (w + α) ≤
      σ ^ (k + 1) * ((w * (k + 1) - α) ^ (k + 1) * (w + α)) := by
    calc
      (w * σ') ^ (k + 1) * (w + α) ≤
          (σ * (w * (k + 1) - α)) ^ (k + 1) * (w + α) :=
        Nat.mul_le_mul_right _ h2
      _ = σ ^ (k + 1) * ((w * (k + 1) - α) ^ (k + 1) * (w + α)) := by
        rw [Nat.mul_pow, Nat.mul_assoc]
  have h5 : (w * σ') ^ (k + 1) * (w + α) ≤
      σ ^ (k + 1) * ((w * (k + 1)) ^ (k + 1) * w) :=
    Nat.le_trans h4 (Nat.mul_le_mul_left _ h3)
  have hwp : 0 < w ^ (k + 1) := Nat.pow_pos hw
  have h6 : w ^ (k + 1) * (σ' ^ (k + 1) * (w + α)) ≤
      w ^ (k + 1) * ((k + 1) ^ (k + 1) * w * σ ^ (k + 1)) := by
    calc
      w ^ (k + 1) * (σ' ^ (k + 1) * (w + α)) =
          (w * σ') ^ (k + 1) * (w + α) := by
        rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ _ := h5
      _ = _ := by
        rw [Nat.mul_pow]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.le_of_mul_le_mul_left h6 hwp


/-- The scaled `n`-th power of the zero survival.

Consumer: `shortSumInvariant`. -/
def shortX (n K t : Nat) : Nat := shortV n K t 0 ^ n

/-- **The product step.**  With `w = 2^K n^t`,
`X_(t+1) (w + alpha_t) ≤ n^n w X_t`.

Consumer: `shortSumInvariant`. -/
theorem shortPowStep (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) (t : Nat) :
    shortX n K (t + 1) * (2 ^ K * n ^ t + shortAlpha n t (K - 1)) ≤
      n ^ n * (2 ^ K * n ^ t) * shortX n K t := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hw : 0 < 2 ^ K * (k + 1) ^ t :=
    Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by omega))
  have hα : shortAlpha (k + 1) t (K - 1) ≤ 2 ^ K * (k + 1) ^ t := by
    have h1 := shortAlphaLePow (k + 1) hn t (K - 1)
    exact Nat.le_trans h1 (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  have H := shortHazard (k + 1) K hn hK t
  exact shortBernoulliStep (shortV (k + 1) K t 0) (shortV (k + 1) K (t + 1) 0)
    (2 ^ K * (k + 1) ^ t) (shortAlpha (k + 1) t (K - 1)) k hw hα H

/-- The arithmetic of the sum step: from
`X' (Kp m + α) ≤ Dn (Kp m) X`, `X ≤ N`, `α ≤ m`,
`Dn m X + (Kp+1) m X' + N Dn α ≤ N Dn m + (Kp+1) Dn m X`.

Consumer: `shortSumStep`. -/
theorem shortStepArith (Kp m α X X' N Dn : Nat) (hKp : 0 < Kp)
    (hm : 0 < m)
    (H1 : X' * (Kp * m + α) ≤ Dn * (Kp * m) * X) (H2 : X ≤ N)
    (H3 : α ≤ m) :
    Dn * m * X + (Kp + 1) * m * X' + N * Dn * α ≤
      N * Dn * m + (Kp + 1) * Dn * m * X := by
  obtain ⟨γ, rfl⟩ : ∃ γ, m = α + γ := ⟨m - α, by omega⟩
  have hW : 0 < Kp * (α + γ) + α := by
    have : 0 < Kp * (α + γ) := Nat.mul_pos hKp hm
    omega
  have F1 := Nat.mul_le_mul_left ((Kp + 1) * (α + γ)) H1
  have F2 := Nat.mul_le_mul_left (Dn * γ * ((α + γ) * Kp)) H2
  have F3 : Dn * γ * N * (Kp * (α + γ)) ≤
      Dn * γ * N * (Kp * (α + γ) + α) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hid : (Kp * (α + γ) + α) *
      (N * Dn * (α + γ) + (Kp + 1) * Dn * (α + γ) * X) +
      Dn * γ * ((α + γ) * Kp * X) =
      (Kp * (α + γ) + α) * (Dn * (α + γ) * X) +
      (Kp + 1) * (α + γ) * (Dn * (Kp * (α + γ)) * X) +
      (Kp * (α + γ) + α) * (N * Dn * α) +
      Dn * γ * ((Kp * (α + γ) + α) * N) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have key : (Kp * (α + γ) + α) *
      (Dn * (α + γ) * X + (Kp + 1) * (α + γ) * X' + N * Dn * α) ≤
      (Kp * (α + γ) + α) *
      (N * Dn * (α + γ) + (Kp + 1) * Dn * (α + γ) * X) := by
    have g1 : (Kp * (α + γ) + α) *
        (Dn * (α + γ) * X + (Kp + 1) * (α + γ) * X' + N * Dn * α) =
        (Kp * (α + γ) + α) * (Dn * (α + γ) * X) +
        (Kp + 1) * (α + γ) * (X' * (Kp * (α + γ) + α)) +
        (Kp * (α + γ) + α) * (N * Dn * α) := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      omega
    have g2 : Dn * γ * ((α + γ) * Kp * X) ≤
        Dn * γ * ((α + γ) * Kp * N) := Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ H2)
    have g3 : Dn * γ * ((α + γ) * Kp * N) ≤
        Dn * γ * ((Kp * (α + γ) + α) * N) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_right
      have : (α + γ) * Kp = Kp * (α + γ) := Nat.mul_comm _ _
      omega
    have g4 : (Kp + 1) * (α + γ) * (X' * (Kp * (α + γ) + α)) ≤
        (Kp + 1) * (α + γ) * (Dn * (Kp * (α + γ)) * X) :=
      Nat.mul_le_mul_left _ H1
    rw [g1]
    omega
  exact Nat.le_of_mul_le_mul_left key hW


/-- The linear-combination step of the sum invariant.

Consumer: `shortSumInvariant`. -/
theorem shortSumStep (n m N Dn X X' L P P' α c : Nat)
    (IH : 2 * m * (L + c * X) + n * m * N ≤ 2 * c * m * N + N * n * P)
    (STEP : Dn * m * X + c * m * X' + N * Dn * α ≤
      N * Dn * m + c * Dn * m * X)
    (hP : P' + 2 * α = n * P + 2 * m) :
    2 * (n * m) * (Dn * (L + X) + c * X') + n * (n * m) * (N * Dn) ≤
      2 * c * (n * m) * (N * Dn) + N * Dn * n * P' := by
  have g1 := Nat.mul_le_mul_left (n * Dn) IH
  have g2 := Nat.mul_le_mul_left (2 * n) STEP
  have g3 : N * Dn * n * (P' + 2 * α) = N * Dn * n * (n * P + 2 * m) := by
    rw [hP]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at g1 g2 g3 ⊢
  omega

/-- The recursion of the cumulative weighted sum of the powers.

Consumer: `shortSumInvariant`. -/
def shortL (n K : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => n ^ n * (shortL n K t + shortX n K t)

/-- The total of the forward chain.

Consumer: `shortSumInvariant`. -/
def shortPhi (n K t : Nat) : Nat :=
  ((List.range K).map (shortAlpha n t)).sum

/-- The total of the forward chain satisfies
`Phi (t+1) + 2 alpha_t = n Phi t + 2 n^t`.

Consumer: `shortSumInvariant`. -/
theorem shortPhiStep (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) (t : Nat) :
    shortPhi n K (t + 1) + 2 * shortAlpha n t (K - 1) =
      n * shortPhi n K t + 2 * n ^ t := by
  have key : ∀ m, ((List.range (m + 1)).map (shortAlpha n (t + 1))).sum +
      2 * shortAlpha n t m =
      n * ((List.range (m + 1)).map (shortAlpha n t)).sum + 2 * n ^ t := by
    intro m
    induction m with
    | zero =>
        rw [List.range_succ]
        simp only [List.range_zero, List.nil_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [shortAlpha_zero, shortAlpha_zero]
        simp only [Nat.pow_succ]
        rw [Nat.mul_comm]
    | succ m ih =>
        rw [List.range_succ (n := m + 1)]
        simp only [List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have hal : shortAlpha n (t + 1) (m + 1) =
            (n - 2) * shortAlpha n t (m + 1) + 2 * shortAlpha n t m := by
          simp [shortAlpha]
        rw [hal]
        have e : n * shortAlpha n t (m + 1) =
            (n - 2) * shortAlpha n t (m + 1) + 2 * shortAlpha n t (m + 1) := by
          have hn2 : n = (n - 2) + 2 := by omega
          calc
            n * shortAlpha n t (m + 1) =
                ((n - 2) + 2) * shortAlpha n t (m + 1) := by rw [← hn2]
            _ = _ := Nat.add_mul _ _ _
        rw [Nat.mul_add]
        omega
  unfold shortPhi
  have hK1 : K = (K - 1) + 1 := by omega
  rw [hK1]
  simp only [Nat.add_sub_cancel]
  exact key (K - 1)


/-- Initial total of the forward chain.

Consumer: `shortSumInvariant`. -/
theorem shortPhi_zero (n K : Nat) (hK : 0 < K) : shortPhi n K 0 = 1 := by
  have key : ∀ m, ((List.range (m + 1)).map (shortAlpha n 0)).sum = 1 := by
    intro m
    induction m with
    | zero => simp [shortAlpha]
    | succ m ih =>
        rw [List.range_succ, List.map_append, List.sum_append, ih]
        simp [shortAlpha]
  unfold shortPhi
  have hK1 : K = (K - 1) + 1 := by omega
  rw [hK1]
  exact key (K - 1)

/-- The total of the forward chain is at most `K n^t`.

Consumer: `shortSumBound`. -/
theorem shortPhiLe (n K : Nat) (hn : 2 ≤ n) (t : Nat) :
    shortPhi n K t ≤ K * n ^ t := by
  have key : ∀ m, ((List.range m).map (shortAlpha n t)).sum ≤ m * n ^ t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [List.range_succ, List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Nat.add_zero, Nat.succ_mul]
        have := shortAlphaLePow n hn t m
        omega
  exact key K

/-- Consumer: `shortSumInvariant`. -/
theorem shortXLe (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) (t : Nat) :
    shortX n K t ≤ n ^ (n * t) := by
  unfold shortX
  have h := Nat.pow_le_pow_left (shortVLePow n K hn hK t 0) n
  rw [← Nat.pow_mul, Nat.mul_comm t n] at h
  exact h

/-- **The sum invariant.**  With `c = 2^K + 1`,

`2 n^t (L_t + c X_t) + n n^t n^(nt) ≤ 2 c n^t n^(nt) + n^(nt) n Phi_t`.

Consumer: `shortSumBound`. -/
theorem shortSumInvariant (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) :
    ∀ t, 2 * n ^ t * (shortL n K t + (2 ^ K + 1) * shortX n K t) +
        n * n ^ t * n ^ (n * t) ≤
      2 * (2 ^ K + 1) * n ^ t * n ^ (n * t) +
        n ^ (n * t) * n * shortPhi n K t := by
  intro t
  induction t with
  | zero =>
      have hX : shortX n K 0 = 1 := by
        unfold shortX
        simp [shortV, hK]
      rw [hX, shortPhi_zero n K hK]
      simp [shortL]
  | succ t ih =>
      have hXle := shortXLe n K hn hK t
      have hmpos : 0 < n ^ t := Nat.pow_pos (by omega)
      have hα := shortAlphaLePow n hn t (K - 1)
      have hpow := shortPowStep n K hn hK t
      have hstep := shortStepArith (2 ^ K) (n ^ t) (shortAlpha n t (K - 1))
        (shortX n K t) (shortX n K (t + 1)) (n ^ (n * t)) (n ^ n)
        (Nat.two_pow_pos K) hmpos hpow hXle hα
      have hP := shortPhiStep n K hn hK t
      have h := shortSumStep n (n ^ t) (n ^ (n * t)) (n ^ n)
        (shortX n K t) (shortX n K (t + 1)) (shortL n K t)
        (shortPhi n K t) (shortPhi n K (t + 1))
        (shortAlpha n t (K - 1)) (2 ^ K + 1) ih hstep hP
      have e1 : n ^ (t + 1) = n * n ^ t := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have e2 : n ^ (n * (t + 1)) = n ^ (n * t) * n ^ n := by
        rw [Nat.mul_succ, Nat.pow_add]
      rw [e1, e2]
      simp only [shortL]
      exact h

/-- **The sum bound.**  `2 L_t + n n^(nt) ≤ (2 (2^K+1) + n K) n^(nt)`.

Consumer: `shortCostOfSurvival`. -/
theorem shortSumBound (n K : Nat) (hn : 2 ≤ n) (hK : 0 < K) (t : Nat) :
    2 * shortL n K t + n * n ^ (n * t) ≤
      (2 * (2 ^ K + 1) + n * K) * n ^ (n * t) := by
  have hI := shortSumInvariant n K hn hK t
  have hΦ := shortPhiLe n K hn t
  have hmpos : 0 < n ^ t := Nat.pow_pos (by omega)
  have h1 : n ^ (n * t) * n * shortPhi n K t ≤
      n ^ (n * t) * n * (K * n ^ t) := Nat.mul_le_mul_left _ hΦ
  have h2 : n ^ t * (2 * shortL n K t + n * n ^ (n * t)) ≤
      n ^ t * ((2 * (2 ^ K + 1) + n * K) * n ^ (n * t)) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at hI h1 ⊢
    omega
  exact Nat.le_of_mul_le_mul_left h2 hmpos

end L3

#print axioms L3.shortHazardClaim
#print axioms L3.shortHazard
#print axioms L3.shortPowStep
#print axioms L3.shortSumInvariant
#print axioms L3.shortSumBound

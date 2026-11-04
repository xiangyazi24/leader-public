import Leader.Core.FiniteUniformStoppingTree

/-!
# Arithmetic for the local-deletion transfer

This file isolates finite natural-number estimates used by the transfer from
local tagged-triple deletion to a global leader-count bound.  No protocol or
probability definitions occur here.
-/

namespace PPL.Convergence.LDTransferArith

open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## Short cyclic triples -/

/-- The next cyclic index.  At the last index it wraps to zero. -/
def cyclicNext {s : Nat} (r : Fin s) : Fin s := by
  cases s with
  | zero => exact r.elim0
  | succ k => exact Fin.lastCases 0 Fin.succ r

/-- Rotating a finite sum by one cyclic index preserves its value. -/
private theorem ofFn_sum_cyclicNext {s : Nat} (f : Fin s → Nat) :
    (List.ofFn (fun r => f (cyclicNext r))).sum = (List.ofFn f).sum := by
  cases s with
  | zero => simp
  | succ k =>
      rw [List.ofFn_succ_last, List.ofFn_succ]
      simp only [cyclicNext, Fin.lastCases_castSucc, Fin.lastCases_last,
        List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
      exact Nat.add_comm _ _

/-- A large gap exceeds four times the mean gap, without division. -/
def largeGap {s : Nat} (n : Nat) (g : Fin s → Nat) (r : Fin s) : Bool :=
  decide (4 * n < s * g r)

/-- A candidate anchor has two successive gaps at most four times the mean. -/
def shortCandidate {s : Nat} (n : Nat) (g : Fin s → Nat) (r : Fin s) : Bool :=
  decide (s * g r ≤ 4 * n ∧ s * g (cyclicNext r) ≤ 4 * n)

/-- The sum of candidate indicators over all cyclic anchors. -/
def candidateCount {s : Nat} (n : Nat) (g : Fin s → Nat) : Nat :=
  (List.ofFn (fun r => if shortCandidate n g r then 1 else 0)).sum

/-- For positive gaps summing to `n`, more than half of the cyclic anchors
have both following gaps at most `4n/s`.  This is Lemma 1 of
`LDC_TRANSFER.md`, in division-free form. -/
theorem lemma1_candidates_gt_half {s n : Nat} (g : Fin s → Nat)
    (hs : 2 ≤ s) (_hg : ∀ r, 1 ≤ g r)
    (hsum : (List.ofFn g).sum = n) :
    s < 2 * candidateCount n g := by
  let bad : Fin s → Nat := fun r => if largeGap n g r then 1 else 0
  let good : Fin s → Nat := fun r => if shortCandidate n g r then 1 else 0
  let B := (List.ofFn bad).sum
  have hweight : (4 * n + 1) * B ≤ s * n := by
    calc
      (4 * n + 1) * B =
          (List.ofFn (fun r => (4 * n + 1) * bad r)).sum := by
            rw [ofFn_sum_mul_left]
      _ ≤ (List.ofFn (fun r => s * g r)).sum := by
            apply ofFn_sum_le
            intro r
            by_cases h : 4 * n < s * g r
            · simp [bad, largeGap, h]
              omega
            · simp [bad, largeGap, h]
      _ = s * n := by rw [ofFn_sum_mul_left, hsum]
  have hbad : 4 * B < s := by
    by_cases hB : B = 0
    · omega
    · have hBpos : 0 < B := by omega
      by_cases hlt : 4 * B < s
      · exact hlt
      · have hrev : s ≤ 4 * B := by omega
        have hmul : s * n ≤ (4 * n) * B := by
          calc
            s * n = n * s := Nat.mul_comm s n
            _ ≤ n * (4 * B) := Nat.mul_le_mul_left n hrev
            _ = (4 * n) * B := by ac_rfl
        have hplus : (4 * n + 1) * B = (4 * n) * B + B := by
          simp [Nat.add_mul]
        omega
  have hpoint (r : Fin s) : 1 ≤ good r + bad r + bad (cyclicNext r) := by
    by_cases h₁ : 4 * n < s * g r
    · have h₁' : ¬ s * g r ≤ 4 * n := by omega
      simp [good, bad, shortCandidate, largeGap, h₁, h₁']
    · by_cases h₂ : 4 * n < s * g (cyclicNext r)
      · simp [good, bad, shortCandidate, largeGap, h₁, h₂]
      · have h₁' : s * g r ≤ 4 * n := by omega
        have h₂' : s * g (cyclicNext r) ≤ 4 * n := by omega
        simp [good, bad, shortCandidate, largeGap, h₁, h₂, h₁', h₂']
  have hsumPoint := ofFn_sum_le
    (fun _ : Fin s => 1)
    (fun r => good r + bad r + bad (cyclicNext r)) hpoint
  simp only [ofFn_sum_const, Nat.mul_one, ofFn_sum_add,
    ofFn_sum_cyclicNext] at hsumPoint
  have hgood : (List.ofFn good).sum = candidateCount n g := rfl
  rw [hgood] at hsumPoint
  omega

/-- Each candidate triple spans at most `8n/s` in division-free form. -/
theorem lemma1_candidate_span {s n : Nat} (g : Fin s → Nat) (r : Fin s)
    (hr : shortCandidate n g r = true) :
    s * (g r + g (cyclicNext r)) ≤ 8 * n := by
  have h : s * g r ≤ 4 * n ∧ s * g (cyclicNext r) ≤ 4 * n := by
    simpa only [shortCandidate, decide_eq_true_eq] using hr
  rw [Nat.mul_add]
  omega

/-! ## Finite scale costs -/

/-- The exact ceiling of `A * (23/24)^h`, expressed using natural division. -/
def scaleCeil (A h : Nat) : Nat :=
  (A * 23 ^ h + 24 ^ h - 1) / 24 ^ h

/-- The sum of the first `k` scale budgets, indexed by `0, ..., k-1`. -/
def scaleBudgetSum (A : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => scaleBudgetSum A k + 3 * (scaleCeil A k + 1)

/-- The recursive budget is exactly the finite sum over scales `h < k`. -/
theorem scaleBudgetSum_eq_ofFn (A k : Nat) :
    scaleBudgetSum A k =
      (List.ofFn (fun i : Fin k => 3 * (scaleCeil A i.val + 1))).sum := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [scaleBudgetSum, List.ofFn_succ_last]
      simp only [List.sum_append, List.sum_cons, List.sum_nil,
        Nat.add_zero, Fin.val_castSucc, Fin.val_last]
      rw [ih]

private theorem scaleCeil_mul (A h : Nat) :
    scaleCeil A h * 24 ^ h ≤ A * 23 ^ h + 24 ^ h := by
  unfold scaleCeil
  have h := Nat.div_mul_le_self (A * 23 ^ h + 24 ^ h - 1) (24 ^ h)
  exact Nat.le_trans h (Nat.sub_le _ _)

/-- The finite geometric bound retains its unused terminal tail, which pays
for both natural-number rounding terms at each scale. -/
private theorem scaleBudgetSum_weighted (A k : Nat) :
    scaleBudgetSum A k * 24 ^ k + 72 * A * 23 ^ k ≤
      72 * A * 24 ^ k + 6 * k * 24 ^ k := by
  induction k with
  | zero => simp [scaleBudgetSum]
  | succ k ih =>
      have hceil := scaleCeil_mul A k
      have ih' :
          scaleBudgetSum A k * 24 ^ k + 72 * (A * 23 ^ k) ≤
            72 * (A * 24 ^ k) + 6 * (k * 24 ^ k) := by
        simpa only [Nat.mul_assoc] using ih
      have harith :
          24 * (scaleBudgetSum A k * 24 ^ k) +
            72 * (scaleCeil A k * 24 ^ k) + 72 * 24 ^ k +
            1656 * (A * 23 ^ k) ≤
          1728 * (A * 24 ^ k) + 144 * (k * 24 ^ k) + 144 * 24 ^ k := by
        omega
      calc
        scaleBudgetSum A (k + 1) * 24 ^ (k + 1) +
            72 * A * 23 ^ (k + 1) =
          24 * (scaleBudgetSum A k * 24 ^ k) +
            72 * (scaleCeil A k * 24 ^ k) + 72 * 24 ^ k +
            1656 * (A * 23 ^ k) := by
              have hqterm :
                  3 * (24 * (24 ^ k * scaleCeil A k)) =
                    24 ^ k * (72 * scaleCeil A k) := by
                calc
                  _ = (3 * 24) * (24 ^ k * scaleCeil A k) := by ac_rfl
                  _ = 24 ^ k * (72 * scaleCeil A k) := by
                    change 72 * (24 ^ k * scaleCeil A k) =
                      24 ^ k * (72 * scaleCeil A k)
                    ac_rfl
              have hpterm : 3 * (24 * 24 ^ k) = 24 ^ k * 72 := by
                calc
                  _ = (3 * 24) * 24 ^ k := by ac_rfl
                  _ = 24 ^ k * 72 := by
                    change 72 * 24 ^ k = 24 ^ k * 72
                    ac_rfl
              have htterm :
                  A * (23 * (23 ^ k * 72)) = A * (23 ^ k * 1656) := by
                calc
                  _ = A * ((23 * 72) * 23 ^ k) := by ac_rfl
                  _ = A * (23 ^ k * 1656) := by
                    change A * (1656 * 23 ^ k) = A * (23 ^ k * 1656)
                    ac_rfl
              simp [scaleBudgetSum, Nat.pow_succ,
                Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              rw [hqterm, hpterm, htterm]
              omega
        _ ≤ 1728 * (A * 24 ^ k) + 144 * (k * 24 ^ k) +
              144 * 24 ^ k := harith
        _ = 72 * A * 24 ^ (k + 1) +
              6 * (k + 1) * 24 ^ (k + 1) := by
              have hat : A * (24 * (24 ^ k * 72)) =
                  A * (24 ^ k * 1728) := by
                calc
                  _ = A * ((24 * 72) * 24 ^ k) := by ac_rfl
                  _ = A * (24 ^ k * 1728) := by
                    change A * (1728 * 24 ^ k) = A * (24 ^ k * 1728)
                    ac_rfl
              have hkt : k * (6 * (24 * 24 ^ k)) =
                  k * (24 ^ k * 144) := by
                calc
                  _ = k * ((6 * 24) * 24 ^ k) := by ac_rfl
                  _ = k * (24 ^ k * 144) := by
                    change k * (144 * 24 ^ k) = k * (24 ^ k * 144)
                    ac_rfl
              have hpt : 6 * (24 * 24 ^ k) = 24 ^ k * 144 := by
                calc
                  _ = (6 * 24) * 24 ^ k := by ac_rfl
                  _ = 24 ^ k * 144 := by
                    change 144 * 24 ^ k = 24 ^ k * 144
                    ac_rfl
              simp [Nat.pow_succ, Nat.add_mul,
                Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              rw [hat, hkt, hpt]
              omega

/-- Bernoulli's inequality for the integer ratio `24/23`. -/
private theorem scale_pow_lower (m : Nat) :
    (m + 24) * 23 ^ m ≤ 24 ^ (m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      have hc : (m + 1 + 24) * 23 ≤ 24 * (m + 24) := by omega
      calc
        (m + 1 + 24) * (23 ^ m * 23) =
            ((m + 1 + 24) * 23) * 23 ^ m := by ac_rfl
        _ ≤ (24 * (m + 24)) * 23 ^ m := Nat.mul_le_mul_right _ hc
        _ = 24 * ((m + 24) * 23 ^ m) := by ac_rfl
        _ ≤ 24 * 24 ^ (m + 1) := Nat.mul_le_mul_left 24 ih
        _ = 24 ^ (m + 1) * 24 := by ac_rfl

/-- Any least height reaching `n * 23^H ≤ 24^H` is at most `24n+1`. -/
private theorem scale_height_le (n H : Nat) (hn : 2 ≤ n)
    (hLeast : ∀ h < H, 24 ^ h < n * 23 ^ h) :
    H ≤ 24 * n + 1 := by
  have hp := scale_pow_lower (24 * n)
  have hcoeff : n * 23 ≤ 24 * n + 24 := by omega
  have hpow : n * 23 ^ (24 * n + 1) ≤ 24 ^ (24 * n + 1) := by
    rw [Nat.pow_succ]
    calc
      n * (23 ^ (24 * n) * 23) = (n * 23) * 23 ^ (24 * n) := by ac_rfl
      _ ≤ (24 * n + 24) * 23 ^ (24 * n) :=
        Nat.mul_le_mul_right _ hcoeff
      _ ≤ 24 ^ (24 * n + 1) := hp
  by_cases h : H ≤ 24 * n + 1
  · exact h
  · have hlt : 24 * n + 1 < H := by omega
    have := hLeast (24 * n + 1) hlt
    omega

/-- The first scale height exists: the integer ratio `(24/23)^h` eventually
reaches every natural leader count. -/
theorem least_scale_height_exists (n : Nat) (hn : 2 ≤ n) :
    ∃ H, n * 23 ^ H ≤ 24 ^ H ∧
      ∀ h < H, 24 ^ h < n * 23 ^ h := by
  have hp := scale_pow_lower (24 * n)
  have hcoeff : n * 23 ≤ 24 * n + 24 := by omega
  have hbound : n * 23 ^ (24 * n + 1) ≤ 24 ^ (24 * n + 1) := by
    rw [Nat.pow_succ]
    calc
      n * (23 ^ (24 * n) * 23) = (n * 23) * 23 ^ (24 * n) := by ac_rfl
      _ ≤ (24 * n + 24) * 23 ^ (24 * n) :=
        Nat.mul_le_mul_right _ hcoeff
      _ ≤ 24 ^ (24 * n + 1) := hp
  have hleast : ∀ B : Nat, n * 23 ^ B ≤ 24 ^ B →
      ∃ H, n * 23 ^ H ≤ 24 ^ H ∧
        ∀ h < H, 24 ^ h < n * 23 ^ h := by
    intro B
    induction B using Nat.strongRecOn with
    | ind B ih =>
        intro hB
        classical
        by_cases hsmall : ∃ h : Nat, h < B ∧ n * 23 ^ h ≤ 24 ^ h
        · obtain ⟨h, hlt, hh⟩ := hsmall
          exact ih h hlt hh
        · refine ⟨B, hB, ?_⟩
          intro h hlt
          have hnot : ¬ n * 23 ^ h ≤ 24 ^ h := by
            intro hh
            exact hsmall ⟨h, hlt, hh⟩
          omega
  exact hleast (24 * n + 1) hbound

/-- Minimality bounds the last geometric denominator by twice its numerator. -/
private theorem scale_tail_lower (n H : Nat) (hn : 2 ≤ n)
    (hLeast : ∀ h < H, 24 ^ h < n * 23 ^ h) :
    24 ^ (H + 1) ≤ 2 * n * 23 ^ (H + 1) := by
  cases H with
  | zero => simp; omega
  | succ H =>
      have hp := hLeast H (by omega)
      simp only [Nat.pow_succ] at *
      have hh : 24 ^ H * (24 * 24) ≤ n * 23 ^ H * (2 * (23 * 23)) := by
        have hx : 24 ^ H ≤ n * 23 ^ H := by omega
        calc
          24 ^ H * (24 * 24) ≤ (n * 23 ^ H) * (24 * 24) :=
            Nat.mul_le_mul_right _ hx
          _ ≤ (n * 23 ^ H) * (2 * (23 * 23)) :=
            Nat.mul_le_mul_left _ (by decide)
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh

/-- Lemma 5's exact natural-number scale sum.  The premise says that `H` is
the first exponent at which `n*(23/24)^H ≤ 1`.  The stronger bound `1152cn²`
comes from using the finite geometric tail to absorb ceiling costs. -/
theorem scale_budget_sum_le (n c H : Nat) (hn : 2 ≤ n) (hc : 1 ≤ c)
    (_hHit : n * 23 ^ H ≤ 24 ^ H)
    (hLeast : ∀ h < H, 24 ^ h < n * 23 ^ h) :
    scaleBudgetSum (16 * c * n ^ 2) (H + 1) ≤ 1172 * c * n ^ 2 := by
  let A := 16 * c * n ^ 2
  let k := H + 1
  have hk : k ≤ 24 * n + 2 := by
    dsimp [k]
    have := scale_height_le n H hn hLeast
    omega
  have htail : 24 ^ k ≤ 2 * n * 23 ^ k := by
    exact scale_tail_lower n H hn hLeast
  have hround : 6 * k * 24 ^ k ≤ 72 * A * 23 ^ k := by
    have h1 : 6 * k ≤ 6 * (24 * n + 2) := Nat.mul_le_mul_left 6 hk
    have h2 := Nat.mul_le_mul_left (6 * k) htail
    have h3 : (6 * (24 * n + 2)) * (2 * n) ≤ 72 * A := by
      have ha : 6 * (24 * n + 2) ≤ 150 * n := by omega
      have hb := Nat.mul_le_mul_right (2 * n) ha
      have hc' : 300 ≤ 1152 * c := by omega
      have hd := Nat.mul_le_mul_right (n ^ 2) hc'
      dsimp [A]
      calc
        (6 * (24 * n + 2)) * (2 * n) ≤ (150 * n) * (2 * n) := hb
        _ = 300 * n ^ 2 := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ (1152 * c) * n ^ 2 := hd
        _ = 72 * (16 * c * n ^ 2) := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h4 := Nat.mul_le_mul_right (23 ^ k) h3
    calc
      6 * k * 24 ^ k ≤ (6 * k) * (2 * n * 23 ^ k) := h2
      _ = ((6 * k) * (2 * n)) * 23 ^ k := by ac_rfl
      _ ≤ (6 * (24 * n + 2) * (2 * n)) * 23 ^ k := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
      _ ≤ (72 * A) * 23 ^ k := h4
  have hw := scaleBudgetSum_weighted A k
  have hsum : scaleBudgetSum A k * 24 ^ k ≤ 72 * A * 24 ^ k := by
    omega
  have hpos : 0 < 24 ^ k := by exact Nat.pow_pos (by decide)
  have hmain : scaleBudgetSum A k ≤ 72 * A := by
    exact Nat.le_of_mul_le_mul_right hsum hpos
  dsimp [A, k] at hmain ⊢
  have hc' : 1152 ≤ 1172 := by decide
  have hlast := Nat.mul_le_mul_right (c * n ^ 2) hc'
  calc
    scaleBudgetSum (16 * c * n ^ 2) (H + 1) ≤
        72 * (16 * c * n ^ 2) := hmain
    _ = 1152 * (c * n ^ 2) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ 1172 * (c * n ^ 2) := hlast
    _ = 1172 * c * n ^ 2 := by ac_rfl

#print axioms lemma1_candidates_gt_half
#print axioms lemma1_candidate_span
#print axioms scale_budget_sum_le

end PPL.Convergence.LDTransferArith

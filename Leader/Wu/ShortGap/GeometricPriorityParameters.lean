import Std.Tactic

/-!
# Explicit finite parameters for geometric-priority contraction

This file checks the integer envelope used by the candidate asynchronous
priority contraction.  It contains no probability space and no physical
sampler.  The probabilistic argument separately uses iid geometric ranks and
the elementary inequality `(3/4)^5 < 1/4`.
-/

namespace GeometricPriorityParameters

/-- A positive strict binary-length upper bound: `n < 2^scale`. -/
def scale (n : Nat) : Nat := Nat.log2 n + 1

/-- Number of distributed bits plus a fixed safety margin. -/
def width (n : Nat) : Nat := Nat.log2 (scale n) + 8

/-- Peak-label capacity represented by the distributed width. -/
def peakCap (n : Nat) : Nat := 2 ^ width n

/-- Geometric priorities are truncated at this value. -/
def priorityCutoff (n : Nat) : Nat :=
  16 * 2 ^ Nat.log2 (scale n)

theorem width_ge_eight (n : Nat) : 8 <= width n := by
  simp [width]

theorem scale_pos (n : Nat) : 0 < scale n := by
  simp [scale]

theorem n_lt_two_pow_scale (n : Nat) : n < 2 ^ scale n := by
  simpa [scale] using (Nat.lt_log2_self (n := n))

theorem peakCap_eq (n : Nat) :
    peakCap n = 256 * 2 ^ Nat.log2 (scale n) := by
  simp [peakCap, width, Nat.pow_add, Nat.mul_comm]

theorem priorityCutoff_mul_sixteen (n : Nat) :
    16 * priorityCutoff n = peakCap n := by
  rw [peakCap_eq]
  simp only [priorityCutoff]
  omega

/-- The cutoff is computable from the supplied width alone: it is the single
bit four positions below the peak-cap bit.  No local copy of `n` or `scale n`
is part of the protocol state. -/
theorem priorityCutoff_eq_two_pow_width_sub_four (n : Nat) :
    priorityCutoff n = 2 ^ (width n - 4) := by
  have width_sub : width n - 4 = Nat.log2 (scale n) + 4 := by
    simp [width]
  rw [width_sub]
  simp [priorityCutoff, Nat.pow_add, Nat.mul_comm]

theorem priorityCutoff_pos (n : Nat) : 0 < priorityCutoff n := by
  simp only [priorityCutoff]
  exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)

/-- The truncated geometric value fits strictly inside the distributed
priority word.  In fact the peak alphabet is sixteen times larger. -/
theorem priorityCutoff_lt_peakCap (n : Nat) :
    priorityCutoff n < peakCap n := by
  have cutoff_pos := priorityCutoff_pos n
  have scale := priorityCutoff_mul_sixteen n
  omega

/-- The chosen `h`-bit peak alphabet has between 128 and 256 times the binary
scale. -/
theorem peakCap_bounds (n : Nat) :
    128 * scale n < peakCap n ∧ peakCap n <= 256 * scale n := by
  have scale_ne : scale n ≠ 0 := Nat.ne_of_gt (scale_pos n)
  have lower_power : 2 ^ Nat.log2 (scale n) <= scale n :=
    Nat.log2_self_le scale_ne
  have upper_power : scale n < 2 ^ (Nat.log2 (scale n) + 1) :=
    (Nat.log2_lt scale_ne).1 (by omega)
  have upper_rewrite :
      2 ^ (Nat.log2 (scale n) + 1) =
        2 * 2 ^ Nat.log2 (scale n) := by
    rw [show Nat.log2 (scale n) + 1 =
      (Nat.log2 (scale n)).succ by omega, Nat.pow_succ]
    omega
  rw [peakCap_eq]
  rw [upper_rewrite] at upper_power
  constructor <;> omega

/-- The cutoff is between eight and sixteen times the binary scale. -/
theorem priorityCutoff_bounds (n : Nat) :
    8 * scale n < priorityCutoff n ∧
      priorityCutoff n <= 16 * scale n := by
  have scale_ne : scale n ≠ 0 := Nat.ne_of_gt (scale_pos n)
  have lower_power : 2 ^ Nat.log2 (scale n) <= scale n :=
    Nat.log2_self_le scale_ne
  have upper_power : scale n < 2 ^ (Nat.log2 (scale n) + 1) :=
    (Nat.log2_lt scale_ne).1 (by omega)
  have upper_rewrite :
      2 ^ (Nat.log2 (scale n) + 1) =
        2 * 2 ^ Nat.log2 (scale n) := by
    rw [show Nat.log2 (scale n) + 1 =
      (Nat.log2 (scale n)).succ by omega, Nat.pow_succ]
    omega
  rw [upper_rewrite] at upper_power
  simp only [priorityCutoff]
  constructor <;> omega

/-- Two directional weak-record budgets of `60*scale` leave strict room in
the peak alphabet. -/
theorem height_budget_lt_peakCap (n : Nat) :
    120 * scale n < peakCap n := by
  have bounds := peakCap_bounds n
  omega

/-- Integer form of `(3/4)^5 < 1/4`, used in the record-count tail. -/
theorem three_quarters_fifth_lt_quarter : 4 * 3 ^ 5 < 4 ^ 5 := by
  decide

end GeometricPriorityParameters

#print axioms GeometricPriorityParameters.n_lt_two_pow_scale
#print axioms GeometricPriorityParameters.width_ge_eight
#print axioms GeometricPriorityParameters.peakCap_bounds
#print axioms GeometricPriorityParameters.priorityCutoff_bounds
#print axioms GeometricPriorityParameters.priorityCutoff_eq_two_pow_width_sub_four
#print axioms GeometricPriorityParameters.priorityCutoff_lt_peakCap
#print axioms GeometricPriorityParameters.height_budget_lt_peakCap
#print axioms GeometricPriorityParameters.three_quarters_fifth_lt_quarter

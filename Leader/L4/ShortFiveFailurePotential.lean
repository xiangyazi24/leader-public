import Init

namespace L4.ShortFiveFailurePotential

/-- At a live trial with r watched letters remaining, one correct
letter consumes one unit of remaining length. Failure costs D. -/
def V (D q r : Nat) : Nat := D - D / q^r

theorem at_zero (D q : Nat) : V D q 0=0 := by
  simp [V]

theorem start_le (D q m : Nat) (Q : 0<q) (B : q^m≤D) : V D q m≤D-1 := by
  have H := Nat.div_pos B (Nat.pow_pos Q)
  unfold V
  omega

theorem quotient_progress (D q r : Nat) (Q : 0<q) :
    q*(D/q^(r+1))≤D/q^r := by
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos Q)).mpr
  have B := Nat.div_mul_le_self D (q^(r+1))
  calc
    _ = D/q^(r+1)*q^(r+1) := by rw [Nat.pow_succ]; ac_rfl
    _ ≤ D := B

theorem watched_drift (D q r : Nat) (Q : 0<q) :
    (q-1)*D+V D q r≤q*V D q (r+1) := by
  have H := quotient_progress D q r Q
  have L := Nat.div_le_self D (q^r)
  rw [V,V,Nat.mul_sub_left_distrib,Nat.mul_sub_right_distrib,Nat.one_mul]
  have B : D≤q*D := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right D Q
  omega

theorem physical_drift (D q n r : Nat) (Q : 0<q) (N : q≤n) :
    (n-q)*V D q (r+1)+V D q r+(q-1)*D≤n*V D q (r+1) := by
  have H := watched_drift D q r Q
  have E := Nat.sub_add_cancel N
  have M : (n-q)*V D q (r+1)+q*V D q (r+1)=n*V D q (r+1) := by
    rw [←Nat.add_mul,E]
  omega

theorem concrete_start {q m : Nat} (Q : 0<q) (W : q≤50) (M : m≤116) :
    V (50^116) q m≤50^116-1 := by
  apply start_le _ _ _ Q
  calc
    q^m ≤ 50^m := Nat.pow_le_pow_left W m
    _ ≤ 50^116 := Nat.pow_le_pow_right (by decide) M

#print axioms at_zero
#print axioms concrete_start
#print axioms watched_drift
#print axioms physical_drift
end L4.ShortFiveFailurePotential

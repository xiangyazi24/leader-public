import Leader.L4.PhysicalCustody

namespace L4.WidthRatioArithmetic

/-- Consecutive coarser gaps represented as lists of finer gaps. Only the
length bound and per-gap spacing are required. -/
theorem sum_between {l u : Nat} (xs : List Nat)
    (H : ∀ x∈xs, l≤x ∧ x≤u) :
    l*xs.length ≤ xs.sum ∧ xs.sum ≤ u*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨A,B⟩ := H x (by simp)
    obtain ⟨L,U⟩ := ih (fun y Y => H y (by simp [Y]))
    simp only [List.length_cons,List.sum_cons,Nat.mul_succ]
    omega

theorem coarsen_spacing {l u r : Nat} (xs : List Nat)
    (H : ∀ x∈xs, l≤x ∧ x≤u)
    (size : r+1≤xs.length ∧ xs.length≤2*r+1) :
    l*(r+1)≤xs.sum ∧ xs.sum≤u*(2*r+1) := by
  exact ⟨Nat.le_trans (Nat.mul_le_mul_left _ size.1) (sum_between xs H).1,
    Nat.le_trans (sum_between xs H).2 (Nat.mul_le_mul_left _ size.2)⟩

/-- The strict width inequality follows from a strict factor-two bound
at either report level. The lower H4 bound is 2^4, the upper one 3^4. -/
theorem width_ratio {s r a b : Nat}
    (A : a≤81*(2*s+1)*(2*r+1))
    (B : 16*(s+1)*(r+1)≤b) :
    4*a<81*b := by
  have U : (2*s+1)*(2*r+1)<(2*(s+1))*(2*(r+1)) := by
    exact Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right (by omega : 2*s+1<2*(s+1)) (by omega : 0<2*r+1))
      (Nat.mul_le_mul_left _ (by omega))
  have UL := Nat.mul_lt_mul_of_pos_left U (by decide : 0<324)
  have E1 : 4*(81*(2*s+1)*(2*r+1)) = 324*((2*s+1)*(2*r+1)) := by
    simp only [←Nat.mul_assoc]
  have E2 : 324*((2*(s+1))*(2*(r+1))) = 81*(16*(s+1)*(r+1)) := by
    calc
      _ = (324*2*2)*((s+1)*(r+1)) := by ac_rfl
      _ = (81*16)*((s+1)*(r+1)) := by rfl
      _ = _ := by ac_rfl
  rw [←E1,E2] at UL
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ A)
    (Nat.lt_of_lt_of_le UL (Nat.mul_le_mul_left _ B))

/-- Adapter to the exact widthRatio field consumed by CustodyGeometry
and the production pace chart lower bound. -/
theorem physical_width_ratio {s n : Nat} {z : PhysicalCustody.Raw s n}
    (hh : ∃ q, BStarH6WordChart.oldH6 (PhysicalCustody.rows s) z q=true)
    (spacing : ∀ e,
      BStarH6WordChart.oldH6 (PhysicalCustody.rows s) z (rightNeighbor e)=true →
      let r := PhysicalCustody.radiusTwo s
      let w := BStarH6Ordinal.oldOrdinal (PhysicalCustody.rows s) z hh e+1
      16*(s+1)*(r+1)≤w ∧ w≤81*(2*s+1)*(2*r+1)) :
    ∀ e f,
      BStarH6WordChart.oldH6 (PhysicalCustody.rows s) z (rightNeighbor e)=true →
      BStarH6WordChart.oldH6 (PhysicalCustody.rows s) z (rightNeighbor f)=true →
      4*(BStarH6Ordinal.oldOrdinal (PhysicalCustody.rows s) z hh e+1)<
      81*(BStarH6Ordinal.oldOrdinal (PhysicalCustody.rows s) z hh f+1) :=
  fun e f E F => width_ratio (spacing e E).2 (spacing f F).1

private theorem four_mul_le_power (t : Nat) : 4*(t+4)≤2^(t+4) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have E : t+1+4=t+4+1 := by omega
    change 4*(t+1+4)≤2^(t+1+4)
    rw [E,Nat.pow_succ]
    omega

/-- Size arithmetic from lem:space for production s≥6. No header or
protocol assumptions enter this part of the width argument. -/
theorem production_bounds {s : Nat} (S : 6≤s) :
    let k := PhysicalCustody.radiusTwo s
    PhysicalCustody.radWidth s≤16*(s+1)*(k+1) ∧
      81*(2*s+1)*(2*k+1)≤1024*PhysicalCustody.radWidth s := by
  dsimp only
  let P := 2^s
  let k := PhysicalCustody.radiusTwo s
  change P-1≤16*(s+1)*(k+1) ∧ 81*(2*s+1)*(2*k+1)≤1024*(P-1)
  have P64 : 64≤P := Nat.pow_le_pow_right (by decide : 0<2) S
  have T : s-4+4=s := by omega
  have PS : 4*s≤P := by
    unfold P
    rw [←T] at *
    exact four_mul_le_power (s-4)
  have Q := Nat.mod_add_div (P+s-1) s
  have R := Nat.mod_lt (P+s-1) (by omega : 0<s)
  change (P+s-1)%s + s*k = P+s-1 at Q
  have C : P≤s*k ∧ s*k≤P+s-1 := by omega
  have KN : 0<k := by
    by_cases H : k=0
    · rw [H,Nat.mul_zero] at C
      omega
    · omega
  have lower : s*k≤(s+1)*(k+1) := Nat.mul_le_mul (by omega) (by omega)
  have lower' : s*k≤16*((s+1)*(k+1)) := by omega
  have upper := Nat.mul_le_mul (by omega : 2*s+1≤3*s) (by omega : 2*k+1≤3*k)
  have U := Nat.mul_le_mul_left 81 upper
  have E1 : 81*(3*s*(3*k)) = (81*3*3)*(s*k) := by ac_rfl
  rw [E1] at U
  change 81*((2*s+1)*(2*k+1))≤729*(s*k) at U
  simp only [Nat.mul_assoc]
  exact ⟨by omega,by omega⟩

end L4.WidthRatioArithmetic

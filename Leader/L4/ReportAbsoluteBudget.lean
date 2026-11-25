import Leader.L4.ReportStageMeans
import Leader.L4.ReportResetCovers

namespace L4.ReportAbsoluteBudget
open AllSizeProtocol PhysicalCustody ShortHopSpacing
open AdviceBandRadiusBudget ReportResetEventClock ReportServiceMesh
open ReportResetRawHooks ReportRawProjection ReportFastRawEvent ReportStageInputs
open ReportStageMeans

variable {n s : Nat}

theorem reset_polynomial (B t s : Nat) (W : B≤486*(s+1)) (T : t≤s+1) :
    resetCoefficient B t≤4194304*(s+1)^2 := by
  have A : B+4*t+7≤512*(s+1) := by omega
  have M : (B+4*t+7)^2≤(512*(s+1))^2 := Nat.pow_le_pow_left A _
  have E : 2*B+1≤973*(s+1) := by omega
  have Sq : s+1≤(s+1)^2 := by
    rw [Nat.pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have F := Nat.le_trans E (Nat.mul_le_mul_left 973 Sq)
  have P : (512*(s+1))^2=262144*(s+1)^2 := by
    rw [Nat.mul_pow,show (512:Nat)^2=262144 by decide]
  rw [P] at M
  unfold resetCoefficient
  have J := Nat.mul_le_mul_left 10 M
  omega

theorem local_reset_budget (d : Sheet) (s : Nat) (S : 6≤s) {G_B : Nat}
    (Hi : G_B≤maxWidth d s) :
    resetCoefficient (3*G_B) (params d s).digits≤4194304*(s+1)^2 := by
  apply reset_polynomial
  · have W : 3*maxWidth d s≤486*(s+1) := by cases d <;> simp [maxWidth] <;> omega
    exact Nat.le_trans (Nat.mul_le_mul_left 3 Hi) W
  · cases d
    · change 1≤s+1
      omega
    · exact AdviceBandRadiusBudget.t2_le S

theorem flat_two_report_reset {B t : Nat} (S : 6≤s) (advice : s=ell (ell n))
    (C : resetCoefficient B t≤4194304*(s+1)^2) :
    8*n*resetCoefficient B t*(ell n+1)≤67108864*n^2 := by
  obtain ⟨_,L,_,_,_,_,_,_⟩ := advice_interval advice S
  have all : ∀ k : Nat, k+1≤2^k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ]; omega
  have E := all s
  have P : (s+1)^2≤2^(2*s) := by
    have Q := Nat.pow_le_pow_left E 2
    rw [←Nat.pow_mul,Nat.mul_comm s 2] at Q
    exact Q
  have D : 2^(3*s)≤n := by
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide)
      (by have := exp_dominates S; omega)) (Nat.le_of_lt (ProductionH6Count.advice_lower (by omega) advice))
  have Ln : ell n+1≤2*2^s := by omega
  have K := Nat.le_trans C (Nat.mul_le_mul_left 4194304 P)
  calc
    _ ≤ 8*n*(4194304*2^(2*s))*(2*2^s) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ K) Ln
    _ = 67108864*n*2^(3*s) := by
      rw [show 3*s=2*s+s by omega,Nat.pow_add]
      calc
        _ = (8*4194304*2)*(n*(2^(2*s)*2^s)) := by ac_rfl
        _ = _ := by rw [show (8*4194304*2 : Nat)=67108864 by decide,Nat.mul_assoc]
    _ ≤ _ := by rw [Nat.pow_two,Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ D)

/-- The two pulse trial costs together use one fixed advice-band budget. -/
theorem flat_report_service (S : 6≤s) (advice : s=ell (ell n)) :
    serviceCost .first s n+serviceCost .second s n≤K_rad*n^2 := by
  have H := advice_band_radius_budget S advice
  have E : U1 s=trialU (meshRadius .first s) := by unfold U1 meshRadius; rfl
  have F : U2 s=trialU (meshRadius .second s) := by unfold U2 meshRadius; rfl
  unfold serviceCost
  rw [E,F] at H
  let u := trialU (meshRadius .first s)
  let v := trialU (meshRadius .second s)
  let a := ell n+1
  change 4*n*(u+v)*a≤K_rad*n^2 at H
  change 2*n*u*a+2*n*v*a≤K_rad*n^2
  calc
    _ = 2*n*(u+v)*a := by rw [Nat.mul_add (2*n) u v,Nat.add_mul (2*n*u) (2*n*v) a]
    _ ≤ 4*n*(u+v)*a :=
      Nat.mul_le_mul_right a (Nat.mul_le_mul_right (u+v) (Nat.mul_le_mul_right n (by decide)))
    _ ≤ _ := H

#print axioms local_reset_budget
#print axioms flat_two_report_reset
#print axioms flat_report_service
end L4.ReportAbsoluteBudget

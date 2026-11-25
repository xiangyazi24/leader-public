import Leader.L4.AdviceBandRadiusBudget

namespace L4.ReportLossArithmetic
open AllSizeProtocol PhysicalCustody AdviceBandRadiusBudget
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def ceilDiv (a d : Nat) := (a+d-1)/d

theorem ceil_cover (a d : Nat) (D : 0<d) : a≤ceilDiv a d*d := by
  have E := Nat.mod_add_div (a+d-1) d
  change (a+d-1)%d+d*ceilDiv a d=a+d-1 at E
  have R := Nat.mod_lt (a+d-1) D
  rw [Nat.mul_comm]
  omega

def halfCell (n h H : Nat) := ceilDiv (n*h) (40*H)

theorem halfCell_pos {n h H : Nat} (N : 0<n) (I : 0<h) (W : 0<H) :
    0<halfCell n h H := by
  have A := ceil_cover (n*h) (40*H) (by omega)
  have P := Nat.mul_pos N I
  by_cases E : halfCell n h H=0
  · change halfCell n h H * (40*H) ≥ n*h at A
    rw [E,Nat.zero_mul] at A
    omega
  · omega

theorem complete_cells {n h H U : Nat} (N : 0<n) (I : 0<h) (W : 0<H) :
    n*U/(2*halfCell n h H)≤(20*H*U)/h := by
  let b := halfCell n h H
  let c := n*U/(2*b)
  have Cover := ceil_cover (n*h) (40*H) (by omega)
  change n*h≤b*(40*H) at Cover
  have Q : c*(2*b)≤n*U := (Nat.le_div_iff_mul_le (by have := halfCell_pos N I W; omega)).mp (Nat.le_refl _)
  apply (Nat.le_div_iff_mul_le I).mpr
  apply Nat.le_of_mul_le_mul_right (c:=n) _ N
  calc
    _ = c*(n*h) := by show _ = n*U/(2*halfCell n h H)*(n*h); ac_rfl
    _ ≤ c*(b*(40*H)) := Nat.mul_le_mul_left _ Cover
    _ = 20*H*(c*(2*b)) := by calc
      _ = 40*(c*b*H) := by ac_rfl
      _ = (20*2)*(c*b*H) := by rfl
      _ = _ := by ac_rfl
    _ ≤ 20*H*(n*U) := Nat.mul_le_mul_left _ Q
    _ = _ := by ac_rfl

theorem halfcell_attempts {n h H mu : Nat} (N : 0<n) (W : 0<H) (M : 0<mu) :
    h/(80*H*mu)≤halfCell n h H/(2*mu*n) := by
  have P : 0<80*H*mu := Nat.mul_pos (by omega) M
  have Q : 0<2*mu*n := Nat.mul_pos (by omega) N
  let a := h/(80*H*mu)
  have L : a*(80*H*mu)≤h := (Nat.le_div_iff_mul_le P).mp (Nat.le_refl _)
  have C := ceil_cover (n*h) (40*H) (by omega)
  apply (Nat.le_div_iff_mul_le Q).mpr
  apply Nat.le_of_mul_le_mul_right (c:=40*H) _ (by omega)
  change a*(2*mu*n)*(40*H) ≤ _
  calc
    _ = n*(a*(80*H*mu)) := by calc
      _ = (2*40)*(a*mu*n*H) := by ac_rfl
      _ = 80*(a*mu*n*H) := by rfl
      _ = _ := by ac_rfl
    _ ≤ n*h := Nat.mul_le_mul_left _ L
    _ ≤ _ := C

theorem warm_blocks {n h J : Nat} (N : 0<n) :
    (n*h/2)/(3*n*(J+2))=h/(6*(J+2)) := by
  rw [Nat.div_div_eq_div_mul]
  have E : 2*(3*n*(J+2))=n*(6*(J+2)) := by calc
    _ = (2*3)*(n*(J+2)) := by ac_rfl
    _ = _ := by change 6*(n*(J+2))=_; ac_rfl
  rw [E,Nat.mul_div_mul_left _ _ N]

/-- Inward-rounded interval endpoints leave at least a tenth of the
trial. Bounds count completely contained physical marks, not endpoints. -/
theorem middle_windows (B : Nat) (S : 20≤B) :
    B≤10*(2*B/5-ceilDiv B 5) ∧ B≤10*(4*B/5-ceilDiv (3*B) 5) := by
  unfold ceilDiv
  omega

/-- The exact complete-cell union incurs no real-floor relaxation and
therefore has coefficient 320, not 640. -/
theorem complete_cell_union {H U h cells : Nat} (I : 0<h)
    (C : cells≤(20*H*U)/h) :
    8*H*cells*2≤320*H^2*(U/h+1) := by
  have A := (Nat.le_div_iff_mul_le I).mp C
  have B : U < (U/h+1)*h := (Nat.div_lt_iff_lt_mul I).mp (by omega)
  have D : cells≤20*H*(U/h+1) := by
    apply Nat.le_of_mul_le_mul_right (c:=h) _ I
    have E := Nat.mul_le_mul_left (20*H) (Nat.le_of_lt B)
    rw [Nat.mul_assoc] at ⊢
    exact Nat.le_trans A E
  calc
    _ ≤ 8*H*(20*H*(U/h+1))*2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ D)
    _ = _ := by
      rw [Nat.pow_two]
      calc
        _ = (8*20*2)*(H*H*(U/h+1)) := by ac_rfl
        _ = 320*(H*H*(U/h+1)) := by rfl
        _ = _ := by ac_rfl

end L4.ReportLossArithmetic

namespace L4.ReportLossArithmetic
open AllSizeProtocol PhysicalCustody AdviceBandRadiusBudget
set_option maxRecDepth 4096

def E (rho : Nat) := trialJ rho+3*trialL rho+ell (trialJ rho)+27
def hSize (rho : Nat) := 19440*2^sigma*(trialH rho)^3*E rho

private theorem twice_le_pow (t : Nat) : 2*(t+1)≤2^(t+1) := by
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ]; omega

private theorem ell_half (x : Nat) : 2*ell x≤x+1 := by
  by_cases X : x≤1
  · simp [ell,X]
  · let k := (x+1)/2
    have K : 0<k := by dsimp [k]; omega
    have I := twice_le_pow (k-1)
    rw [show k-1+1=k by omega] at I
    have Q : x≤2*k := by dsimp [k]; omega
    have R := (ell_le_iff x k).mpr (Nat.le_trans Q I)
    dsimp [k] at R
    omega

private theorem j_le (rho : Nat) : trialJ rho≤2*trialX rho := by
  have P := ell_half (trialX rho)
  unfold trialJ trialX at *
  omega

private theorem e_le (rho : Nat) : E rho≤4*trialJ rho := by
  have P := ell_half (trialJ rho)
  unfold E trialJ at *
  omega

private theorem pow_h (rho : Nat) (k : Nat) :
    (trialH rho)^k≤2^(k*trialL rho) := by
  rw [Nat.mul_comm k,Nat.pow_mul]
  exact Nat.pow_le_pow_left (power_of_ell _) _

private theorem j_pow_lower (rho : Nat) :
    2^sigma*(trialH rho)^6*2^45*(trialX rho)^2≤2^(trialJ rho) := by
  have P : (trialX rho)^2≤2^(2*ell (trialX rho)) := by
    rw [Nat.mul_comm 2,Nat.pow_mul]
    exact Nat.pow_le_pow_left (power_of_ell _) _
  calc
    _ ≤ 2^sigma*2^(6*trialL rho)*2^45*2^(2*ell (trialX rho)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (pow_h rho 6))) P
    _ = _ := by rw [←Nat.pow_add,←Nat.pow_add,←Nat.pow_add]; rfl

private theorem e_pow_lower (rho : Nat) :
    2^(trialJ rho)*(trialH rho)^3*trialJ rho*2^27≤2^(E rho) := by
  calc
    _ ≤ 2^(trialJ rho)*2^(3*trialL rho)*2^(ell (trialJ rho))*2^27 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (pow_h rho 3)) (power_of_ell _))
    _ = _ := by rw [←Nat.pow_add,←Nat.pow_add,←Nat.pow_add]; rfl

/-- Inequality A, in a form avoiding any evaluation of 2^J. -/
theorem close_power (rho : Nat) :
    19200*4096*19440*2^sigma*(trialH rho)^6*trialJ rho*E rho < 2^(trialJ rho) := by
  have A : trialJ rho*E rho≤16*(trialX rho)^2 := by
    have X := j_le rho
    have T := Nat.mul_le_mul X (show E rho≤8*trialX rho by have := e_le rho; omega)
    calc
      _ ≤ (2*trialX rho)*(8*trialX rho) := T
      _ = 16*(trialX rho)^2 := by rw [Nat.pow_two]; calc
        _ = (2*8)*(trialX rho*trialX rho) := by ac_rfl
        _ = _ := rfl
  have B : 19200*4096*19440*16 < 2^45 := by decide
  have Pos : 0<2^sigma*(trialH rho)^6*(trialX rho)^2 := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by unfold trialH; omega)))
      (Nat.pow_pos (by unfold trialX; omega))
  have L := j_pow_lower rho
  generalize (2:Nat)^sigma = c at Pos L ⊢
  calc
    _ = (19200*4096*19440*c*(trialH rho)^6)*(trialJ rho*E rho) := by ac_rfl
    _ ≤ (19200*4096*19440*c*(trialH rho)^6)*(16*(trialX rho)^2) :=
      Nat.mul_le_mul_left _ A
    _ = (19200*4096*19440*16)*(c*(trialH rho)^6*(trialX rho)^2) := by ac_rfl
    _ < 2^45*(c*(trialH rho)^6*(trialX rho)^2) := Nat.mul_lt_mul_of_pos_right B Pos
    _ = c*(trialH rho)^6*2^45*(trialX rho)^2 := by ac_rfl
    _ ≤ _ := L

/-- Inequality B, retaining the exact absolute constants. -/
theorem mesh_power (rho : Nat) :
    10240*(trialH rho)^2*trialU rho<2^(E rho) := by
  have P : 0<2^(trialJ rho)*(trialH rho)^3*trialJ rho := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by unfold trialH; omega)))
      (by unfold trialJ; omega)
  have C : 10240*4096<2^27 := by decide
  unfold trialU
  calc
    _ = (10240*4096)*(2^(trialJ rho)*(trialH rho)^3*trialJ rho) := by
      rw [show (trialH rho)^3=(trialH rho)^2*trialH rho by rw [Nat.pow_succ]]
      ac_rfl
    _ < 2^27*(2^(trialJ rho)*(trialH rho)^3*trialJ rho) := Nat.mul_lt_mul_of_pos_right C P
    _ = 2^(trialJ rho)*(trialH rho)^3*trialJ rho*2^27 := by ac_rfl
    _ ≤ _ := e_pow_lower rho

theorem service_exponent {rho g : Nat} (G : 0<g) (A : g≤243*(trialH rho)^2) :
    E rho≤hSize rho/(80*trialH rho*(2^sigma*g)) := by
  have P : 0<80*trialH rho*(2^sigma*g) :=
    Nat.mul_pos (by unfold trialH; omega) (Nat.mul_pos (Nat.pow_pos (by decide)) G)
  apply (Nat.le_div_iff_mul_le P).mpr
  unfold hSize
  generalize (2:Nat)^sigma = c
  calc
    _ = (80*trialH rho*c*E rho)*g := by ac_rfl
    _ ≤ (80*trialH rho*c*E rho)*(243*(trialH rho)^2) := Nat.mul_le_mul_left _ A
    _ = _ := by
      rw [show (trialH rho)^3=(trialH rho)^2*trialH rho by rw [Nat.pow_succ]]
      calc
        _ = (80*243)*(c*trialH rho*(trialH rho)^2*E rho) := by ac_rfl
        _ = 19440*(c*trialH rho*(trialH rho)^2*E rho) := by rfl
        _ = _ := by ac_rfl

end L4.ReportLossArithmetic

namespace L4.ReportLossArithmetic
open AllSizeProtocol PhysicalCustody AdviceBandRadiusBudget
set_option maxRecDepth 4096

private theorem hSize_pos (rho : Nat) : 0<hSize rho := by
  unfold hSize
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
    (Nat.pow_pos (by unfold trialH; omega))) (by unfold E; omega)

private theorem j_pos (rho : Nat) : 0<trialJ rho := by unfold trialJ; omega

private theorem trialU_pos (rho : Nat) : 0<trialU rho := by
  unfold trialU
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by unfold trialH; omega))
    (j_pos rho)) (Nat.pow_pos (by decide))

theorem close_cross (rho : Nat) :
    19200*(trialH rho)^2*hSize rho*trialU rho < (2^(trialJ rho))^2 := by
  have C := close_power rho
  have P : 0<2^(trialJ rho) := Nat.pow_pos (by decide)
  have L := Nat.mul_lt_mul_of_pos_right C P
  unfold hSize trialU
  generalize (2:Nat)^sigma=c at L ⊢
  have D : (trialH rho)^2*(trialH rho)^3*trialH rho=(trialH rho)^6 := by
    conv => lhs; arg 2; rw [←Nat.pow_one (trialH rho)]
    rw [←Nat.pow_add,←Nat.pow_add]
  rw [Nat.pow_two (2^(trialJ rho))]
  calc
    _ = (19200*4096*19440*c)*(trialH rho)^6*trialJ rho*E rho*2^(trialJ rho) := by
      rw [←D]
      ac_rfl
    _ < _ := L

theorem warm_gap_large (rho : Nat) : 25*hSize rho<trialU rho := by
  have C := close_cross rho
  have H : 1≤(trialH rho)^2 := Nat.pow_le_pow_left (show 1≤trialH rho by unfold trialH; omega) 2
  have J : 1≤trialJ rho := j_pos rho
  have B : 1≤4096*trialH rho*trialJ rho :=
    Nat.mul_pos (Nat.mul_pos (by decide) (by unfold trialH; omega)) J
  have M : 2^(trialJ rho)≤trialU rho := by
    unfold trialU
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^(trialJ rho)) B
  have L : 25*hSize rho≤19200*(trialH rho)^2*hSize rho :=
    Nat.mul_le_mul_right _ (Nat.le_trans (by decide : 25≤19200)
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 19200 H))
  apply Nat.lt_of_mul_lt_mul_right (a:=trialU rho)
  calc
    _ ≤ _ := Nat.mul_le_mul_right _ L
    _ < _ := C
    _ ≤ _ := by rw [Nat.pow_two]; exact Nat.mul_le_mul M M

private theorem plus_one_le_double {v : Nat} (V : 0<v) : v+1≤2*v := by omega

theorem close_loss_lt (rho : Nat) :
    8*(600*(trialH rho)^2*(trialU rho+1)*(hSize rho+1)) < (2^(trialJ rho))^2 := by
  have A := plus_one_le_double (trialU_pos rho)
  have B := plus_one_le_double (hSize_pos rho)
  have C := close_cross rho
  generalize hSize rho=h at B C ⊢
  calc
    _ ≤ 8*(600*(trialH rho)^2*(2*trialU rho)*(2*h)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ A) B)
    _ = 19200*(trialH rho)^2*h*trialU rho := by calc
      _ = (8*600*2*2)*((trialH rho)^2*h*trialU rho) := by ac_rfl
      _ = 19200*((trialH rho)^2*h*trialU rho) := by rfl
      _ = _ := by ac_rfl
    _ < _ := C

theorem miss_loss_lt (rho : Nat) :
    8*(400*trialH rho*trialJ rho*2^(trialJ rho)) < trialU rho := by
  have P : 0<trialH rho*trialJ rho*2^(trialJ rho) :=
    Nat.mul_pos (Nat.mul_pos (by unfold trialH; omega) (j_pos rho)) (Nat.pow_pos (by decide))
  unfold trialU
  calc
    _ = (8*400)*(trialH rho*trialJ rho*2^(trialJ rho)) := by ac_rfl
    _ < 4096*(trialH rho*trialJ rho*2^(trialJ rho)) := Nat.mul_lt_mul_of_pos_right (by decide) P
    _ = _ := by ac_rfl

theorem mesh_loss_lt (rho : Nat) :
    8*(640*(trialH rho)^2*(trialU rho/hSize rho+1)) < 2^(E rho) := by
  have P : trialU rho/hSize rho+1≤2*trialU rho := by
    have := Nat.div_le_self (trialU rho) (hSize rho)
    have := trialU_pos rho
    omega
  have A := mesh_power rho
  calc
    _ ≤ 8*(640*(trialH rho)^2*(2*trialU rho)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ P)
    _ = 10240*(trialH rho)^2*trialU rho := by calc
      _ = (8*640*2)*((trialH rho)^2*trialU rho) := by ac_rfl
      _ = 10240*((trialH rho)^2*trialU rho) := by rfl
      _ = _ := by ac_rfl
    _ < _ := A

end L4.ReportLossArithmetic

namespace L4.ReportLossArithmetic
open AllSizeProtocol PhysicalCustody AdviceBandRadiusBudget
set_option maxRecDepth 4096

theorem warm_exponent (rho : Nat) :
    trialL rho+7≤hSize rho/(6*(trialJ rho+2)) := by
  have PH : 2≤trialH rho := by unfold trialH; omega
  have A : trialL rho+7≤5*trialH rho := by
    have T := ell_half (trialH rho)
    change 2*trialL rho≤trialH rho+1 at T
    omega
  have B : trialH rho≤(trialH rho)^3 := by
    have T := Nat.pow_le_pow_right (by omega : 0<trialH rho) (by decide : 1≤3)
    simpa only [Nat.pow_one] using T
  have C : trialJ rho+2≤E rho := by unfold E; omega
  have D : 1≤2^sigma := Nat.pow_pos (by decide)
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  unfold hSize
  generalize (2:Nat)^sigma=c at D ⊢
  calc
    _ ≤ (5*(trialH rho)^3)*(6*E rho) :=
      Nat.mul_le_mul (Nat.le_trans A (Nat.mul_le_mul_left _ B)) (Nat.mul_le_mul_left _ C)
    _ = 30*((trialH rho)^3*E rho) := by calc
      _ = (5*6)*((trialH rho)^3*E rho) := by ac_rfl
      _ = _ := rfl
    _ ≤ (19440*c)*((trialH rho)^3*E rho) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ac_rfl

theorem warm_loss_lt (rho : Nat) :
    8*(9*trialH rho) < 2^(hSize rho/(6*(trialJ rho+2))) := by
  calc
    _ < 128*trialH rho := by have : 2≤trialH rho := by unfold trialH; omega
                             omega
    _ ≤ 128*2^(trialL rho) := Nat.mul_le_mul_left _ (power_of_ell _)
    _ = 2^(trialL rho+7) := by rw [Nat.pow_add,Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (warm_exponent rho)

/-- Direct mesh budget at the literal floor, no real-exponent relaxation. -/
theorem mesh_integer_loss_lt {rho g : Nat} (G : 0<g) (A : g≤243*(trialH rho)^2) :
    8*(640*(trialH rho)^2*(trialU rho/hSize rho+1)) <
      2^(hSize rho/(80*trialH rho*(2^sigma*g))) :=
  Nat.lt_of_lt_of_le (mesh_loss_lt rho)
    (Nat.pow_le_pow_right (by decide) (service_exponent G A))

end L4.ReportLossArithmetic

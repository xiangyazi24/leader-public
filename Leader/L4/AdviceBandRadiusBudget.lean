import Leader.L4.ProductionH6Count

namespace L4.AdviceBandRadiusBudget
open AllSizeProtocol PhysicalCustody
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def nMin (s : Nat) := 2^(2^(s-1))+1

theorem ell_interval {m a : Nat} (A : 0<a) (E : ell m=a) :
    2^(a-1)<m ∧ m≤2^a := by
  refine ⟨?_,E ▸ power_of_ell m⟩
  apply Nat.lt_of_not_ge
  intro H
  have T := (ell_le_iff m (a-1)).mpr H
  omega

private theorem pow_split {s : Nat} (H : 0<s) : 2^s=2^(s-1)*2 := by
  conv => lhs; rw [show s=(s-1)+1 by omega,Nat.pow_succ]

theorem advice_interval {n s : Nat} (S : s=ell (ell n)) (H : 6≤s) :
    2^(s-1)<ell n ∧ ell n≤2^s ∧ 2^(ell n-1)<n ∧ n≤2^(ell n) ∧
    nMin s≤n ∧ n≤2^(2^s) ∧ 2^s<2*ell n ∧ ell n+2≤2^(s+1) := by
  have Q := ell_interval (m:=ell n) (a:=s) (by omega) S.symm
  have N : 2^(ell n-1)<n ∧ n≤2^(ell n) := ell_interval (m:=n) (a:=ell n) (Nat.lt_of_le_of_lt (Nat.zero_le _) Q.1) rfl
  have A := ProductionH6Count.advice_lower (by omega) S
  have B := Nat.pow_le_pow_right (by decide : 0<2) Q.2
  have C := pow_split (by omega : 0<s)
  have D : 64≤2^s := Nat.pow_le_pow_right (by decide : 0<2) H
  refine ⟨Q.1,Q.2,N.1,N.2,by unfold nMin; omega,Nat.le_trans N.2 B,by omega,?_⟩
  rw [Nat.pow_succ]
  omega

theorem exp_dominates {s : Nat} (H : 6≤s) : 3*s+14≤2^(s-1) := by
  have M (t : Nat) : 3*(t+6)+14≤2^(t+5) := by
    induction t with
    | zero => decide
    | succ t ih =>
      change 3*(t+1+6)+14≤2^(t+1+5)
      rw [show t+1+5=t+5+1 by omega,Nat.pow_succ]
      omega
  have A := M (s-6)
  rw [show s-6+6=s by omega,show s-6+5=s-1 by omega] at A
  exact A

theorem radius_ceiling_bounds (s : Nat) (H : 0<s) :
    2^s≤s*radiusTwo s ∧ s*radiusTwo s≤2^s+s-1 := by
  have R := Nat.mod_add_div (2^s+s-1) s
  change (2^s+s-1)%s+s*radiusTwo s=2^s+s-1 at R
  have T := Nat.mod_lt (2^s+s-1) H
  omega

theorem radius_six {s : Nat} (H : 6≤s) : 6*radiusTwo s≤2^s+5 := by
  have R := radius_ceiling_bounds s (by omega)
  generalize E : radiusTwo s = k at R ⊢
  have P : 0<2^s := Nat.pow_pos (by decide)
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.mul_succ] at R
    have T := Nat.mul_le_mul_right k H
    omega

theorem radius_le_power {s : Nat} (H : 6≤s) : radiusTwo s≤2^s := by
  have R := radius_six H
  have P : 0<2^s := Nat.pow_pos (by decide)
  omega

theorem t2_le {s : Nat} (H : 6≤s) : ell (radiusTwo s+1)≤s+1 := by
  apply (ell_le_iff _ _).mpr
  rw [Nat.pow_succ]
  have R := radius_le_power H
  have P : 0<2^s := Nat.pow_pos (by decide)
  omega

private theorem squared_log {n s k c : Nat} (S : s=ell (ell n)) (H : 6≤s)
    (A : k≤2^(s+c)) (E : 3*s+2*c+1≤2^(s-1)+2*c) :
    k^2*(ell n+2)<2^(2*c)*n := by
  obtain ⟨_,_,_,_,_,_,_,L⟩ := advice_interval S H
  have T := ProductionH6Count.advice_lower (by omega) S
  calc
    _ ≤ (2^(s+c))^2*2^(s+1) := Nat.mul_le_mul (Nat.pow_le_pow_left A 2) L
    _ = 2^(3*s+2*c+1) := by rw [←Nat.pow_mul,←Nat.pow_add]; congr 1; omega
    _ ≤ 2^(2^(s-1)+2*c) := Nat.pow_le_pow_right (by decide) E
    _ < _ := by rw [Nat.pow_add,Nat.mul_comm]; exact Nat.mul_lt_mul_of_pos_left T (Nat.pow_pos (by decide))

theorem radius_square_log_absorb {n s : Nat} (S : s=ell (ell n)) (H : 6≤s) :
    radiusTwo s^2*(ell n+2)<n := by
  have A := squared_log (c:=0) S H (radius_le_power H) (by have := exp_dominates H; omega)
  simpa using A

theorem radWidth_square_log_absorb {n s : Nat} (S : s=ell (ell n)) (H : 6≤s) :
    radWidth s^2*(ell n+2)<n := by
  have A := squared_log (c:=0) S H (k:=radWidth s)
    (by simp [radWidth]) (by have := exp_dominates H; omega)
  simpa using A

theorem cover_log_absorb {n s : Nat} (S : s=ell (ell n)) (H : 6≤s) :
    2*(radiusTwo s+1)*(ell n+2)<n := by
  obtain ⟨_,_,_,_,_,_,_,L⟩ := advice_interval S H
  have T := ProductionH6Count.advice_lower (by omega) S
  have R : radiusTwo s+1≤2^(s+1) := by
    rw [Nat.pow_succ]
    have := radius_le_power H
    have P : 0<2^s := Nat.pow_pos (by decide)
    omega
  calc
    _ ≤ 2*2^(s+1)*2^(s+1) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 R) L
    _ = 2^(2*s+3) := by
      change 2^1*2^(s+1)*2^(s+1) = _
      rw [←Nat.pow_add,←Nat.pow_add]
      congr 1
      omega
    _ ≤ 2^(2^(s-1)) := Nat.pow_le_pow_right (by decide) (by have := exp_dominates H; omega)
    _ < n := T

def widthMax (s : Nat) := 81*(2*s+1)*(2*radiusTwo s+1)

theorem width_below_486 {s : Nat} (S : 6≤s) : widthMax s<486*2^s := by
  have A := (radius_ceiling_bounds s (by omega)).2
  have B := radius_six S
  have C : 6*s≤2^s := by
    rw [pow_split (by omega)]
    have := exp_dominates S
    omega
  have P : 0<2^s := Nat.pow_pos (by decide)
  have E : 3*((2*s+1)*(2*radiusTwo s+1))=12*(s*radiusTwo s)+6*s+6*radiusTwo s+3 := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul,←Nat.mul_assoc]
    have F : 3*2*s*2*radiusTwo s=12*(s*radiusTwo s) := by
      calc
        _ = (3*2*2)*(s*radiusTwo s) := by ac_rfl
        _ = _ := rfl
    rw [F,Nat.mul_assoc 12 s]
    omega
  unfold widthMax
  rw [Nat.mul_assoc]
  omega

theorem width_below_502 {s : Nat} (S : 6≤s) : widthMax s<502*2^s := by
  have := width_below_486 S
  omega

theorem width_square_log_absorb {n s : Nat} (S : s=ell (ell n)) (H : 6≤s) :
    widthMax s^2*(ell n+2)<32*n := by
  obtain ⟨_,_,_,_,_,_,_,L⟩ := advice_interval S H
  have T := ProductionH6Count.advice_lower (by omega) S
  have B : widthMax s≤2^(s+9) := by rw [Nat.pow_add]; have := width_below_486 H; omega
  calc
    _ ≤ (2^(s+9))^2*2^(s+1) := Nat.mul_le_mul (Nat.pow_le_pow_left B 2) L
    _ = 2^(3*s+19) := by rw [←Nat.pow_mul,←Nat.pow_add]; congr 1; omega
    _ ≤ 2^(2^(s-1)+5) := Nat.pow_le_pow_right (by decide) (by have := exp_dominates H; omega)
    _ < _ := by rw [Nat.pow_add,Nat.mul_comm]; exact Nat.mul_lt_mul_of_pos_left T (by decide)

theorem width_stage_budget {n s : Nat} (S : s=ell (ell n)) (H : 6≤s) :
    40*n*(widthMax s+1)^2*(ell n+2) ≤ 5120*n^2 := by
  have P : 1≤widthMax s := by
    unfold widthMax
    have T := Nat.mul_pos (show 0<81*(2*s+1) by omega) (show 0<2*radiusTwo s+1 by omega)
    omega
  have A := Nat.pow_le_pow_left (show widthMax s+1≤2*widthMax s by omega) 2
  have B := Nat.mul_le_mul_left (40*n) (Nat.mul_le_mul_right (ell n+2) A)
  rw [Nat.mul_pow] at B
  have C := Nat.mul_le_mul_left (40*n*4) (Nat.le_of_lt (width_square_log_absorb S H))
  calc
    _ ≤ 40*n*(2^2*widthMax s^2*(ell n+2)) := by simpa only [Nat.mul_assoc] using B
    _ = 40*n*4*(widthMax s^2*(ell n+2)) := by change 40*n*(4*widthMax s^2*(ell n+2)) = _; ac_rfl
    _ ≤ 40*n*4*(32*n) := C
    _ = _ := by rw [Nat.pow_two]; calc
      _ = (40*4*32)*(n*n) := by ac_rfl
      _ = _ := rfl

#print axioms advice_interval
#print axioms t2_le
#print axioms radius_square_log_absorb
#print axioms radWidth_square_log_absorb
#print axioms cover_log_absorb
#print axioms width_below_486
#print axioms width_stage_budget
end L4.AdviceBandRadiusBudget

namespace L4.AdviceBandRadiusBudget
open AllSizeProtocol PhysicalCustody

def trialH (k : Nat) := k+2
def trialL (k : Nat) := ell (trialH k)
def trialX (k : Nat) := sigma+6*trialL k+100
def trialJ (k : Nat) := sigma+6*trialL k+45+2*ell (trialX k)
def trialU (k : Nat) := 4096*trialH k*trialJ k*2^(trialJ k)
@[irreducible] def U1 (s : Nat) := trialU s
@[irreducible] def U2 (s : Nat) := trialU (radiusTwo s)
def n0 : Nat := 2^32+1
def trialCeiling (u d : Nat) := (520*u+d-1)/d
scoped notation "K_rad" => trialCeiling (U2 6) n0

theorem trialJ_eq_streak (k : Nat) : trialJ k=streak k := rfl

theorem radiusTwo_next_le_double {s : Nat} (S : 0<s) :
    radiusTwo (s+1)≤2*radiusTwo s := by
  apply Nat.le_of_not_gt
  intro A
  have L := (radius_ceiling_bounds s S).1
  have U := (radius_ceiling_bounds (s+1) (by omega)).2
  have K := Nat.mul_le_mul_left (s+1) (show 2*radiusTwo s+1≤radiusTwo (s+1) by omega)
  rw [Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.one_mul] at K
  have E : s*(2*radiusTwo s)=2*(s*radiusTwo s) := by ac_rfl
  rw [Nat.pow_succ] at U
  rw [E] at K
  omega

theorem ell_at_most_double {u v : Nat} (H : u≤2*v) : ell u≤ell v+1 := by
  apply (ell_le_iff _ _).mpr
  calc
    u ≤ 2*v := H
    _ ≤ 2*2^(ell v) := Nat.mul_le_mul_left 2 (power_of_ell _)
    _ = 2^(ell v+1) := by rw [Nat.pow_succ,Nat.mul_comm]

theorem trialU_doubling (k k' : Nat) (D : trialH k'≤2*trialH k) :
    trialU k'≤1024*trialU k := by
  have L : trialL k'≤trialL k+1 := ell_at_most_double D
  have X : trialX k'≤2*trialX k := by unfold trialX; omega
  have E := ell_at_most_double X
  have J : trialJ k'≤trialJ k+8 := by unfold trialJ; omega
  have J8 : 8≤trialJ k := by unfold trialJ sigma; omega
  have J2 : trialJ k'≤2*trialJ k := by omega
  have P : 2^(trialJ k')≤256*2^(trialJ k) := by
    calc
      _ ≤ 2^(trialJ k+8) := Nat.pow_le_pow_right (by decide) J
      _ = _ := by rw [Nat.pow_add,Nat.mul_comm]
  unfold trialU
  calc
    _ ≤ 4096*(2*trialH k)*(2*trialJ k)*(256*2^(trialJ k)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 4096 D) J2) P
    _ = _ := by
      calc
        _ = (4096*2*2*256)*(trialH k*trialJ k*2^(trialJ k)) := by ac_rfl
        _ = (1024*4096)*(trialH k*trialJ k*2^(trialJ k)) := by rfl
        _ = _ := by ac_rfl

theorem U1_growth (s : Nat) : U1 (s+1)≤1024*U1 s := by
  unfold U1
  exact trialU_doubling _ _ (by unfold trialH; omega)

theorem U2_growth {s : Nat} (S : 6≤s) : U2 (s+1)≤1024*U2 s := by
  unfold U2
  exact trialU_doubling _ _ (by unfold trialH; have := radiusTwo_next_le_double (s:=s) (by omega); omega)

theorem nMin_growth {s : Nat} (S : 6≤s) : 2^31*nMin s<nMin (s+1) := by
  let a := 2^(2^(s-1))
  have A : 4294967296≤a :=
    Nat.pow_le_pow_right (by decide : 0<2)
      (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 5≤s-1))
  have E : nMin (s+1)=a*a+1 := by
    change 2^(2^((s+1)-1))+1 = a*a+1
    rw [show s+1-1=s by omega]
    have PE := pow_split (s:=s) (by omega)
    calc
      _ = 2^(2^(s-1)*2)+1 := congrArg (fun k=>2^k+1) PE
      _ = _ := by rw [Nat.pow_mul,Nat.pow_two]
  have M := Nat.mul_le_mul_right a A
  rw [E]
  change 2147483648*(a+1)<a*a+1
  omega

theorem trialU_mono {k l : Nat} (D : k≤l) : trialU k≤trialU l := by
  have H : trialH k≤trialH l := Nat.add_le_add_right D _
  have L : trialL k≤trialL l := ell_mono H
  have X : trialX k≤trialX l := by unfold trialX; omega
  have E := ell_mono X
  have J : trialJ k≤trialJ l := by unfold trialJ; omega
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 4096 H) J)
    (Nat.pow_le_pow_right (by decide) J)

theorem U6_order : U1 6≤U2 6 := by
  unfold U1 U2
  exact trialU_mono (by decide : 6≤radiusTwo 6)

private theorem normalized_trial_band_core (u1 u2 : Nat → Nat)
    (G1 : ∀ s, u1 (s+1) ≤ 1024*u1 s)
    (G2 : ∀ s, 6≤s → u2 (s+1) ≤ 1024*u2 s)
    (G6 : u1 6 ≤ u2 6) {s : Nat} (S : 6≤s) :
    n0*(u1 s+u2 s)*(2^s+1)≤130*u2 6*nMin s := by
  have all (t : Nat) : n0*(u1 (t+6)+u2 (t+6))*(2^(t+6)+1)≤130*u2 6*nMin (t+6) := by
    induction t with
    | zero =>
      change n0*(u1 6+u2 6)*65≤130*u2 6*n0
      calc
        _ ≤ n0*(2*u2 6)*65 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
        _ = _ := by calc
          _ = (2*65)*(n0*u2 6) := by ac_rfl
          _ = 130*(n0*u2 6) := by rfl
          _ = _ := by ac_rfl
    | succ t ih =>
      let q := t+6
      have E : t+1+6=q+1 := by unfold q; omega
      change n0*(u1 (t+1+6)+u2 (t+1+6))*(2^(t+1+6)+1)≤130*u2 6*nMin (t+1+6)
      rw [E]
      have V : u1 (q+1)+u2 (q+1)≤1024*(u1 q+u2 q) := by
        rw [Nat.mul_add]
        exact Nat.add_le_add (G1 q) (G2 q (by dsimp [q]; omega))
      have P : 2^(q+1)+1≤2*(2^q+1) := by rw [Nat.pow_succ]; omega
      have D : 2048*nMin q≤nMin (q+1) := by
        have H := nMin_growth (s:=q) (by dsimp [q]; omega)
        change 2147483648*nMin q<nMin (q+1) at H
        omega
      calc
        _ ≤ n0*(1024*(u1 q+u2 q))*(2*(2^q+1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ V) P
        _ = 2048*(n0*(u1 q+u2 q)*(2^q+1)) := by calc
          _ = (1024*2)*(n0*(u1 q+u2 q)*(2^q+1)) := by ac_rfl
          _ = _ := rfl
        _ ≤ 2048*(130*u2 6*nMin q) := Nat.mul_le_mul_left _ ih
        _ = (130*u2 6)*(2048*nMin q) := by ac_rfl
        _ ≤ _ := Nat.mul_le_mul_left _ D
  have A := all (s-6)
  rwa [show s-6+6=s by omega] at A

theorem normalized_trial_band {s : Nat} (S : 6≤s) :
    n0*(U1 s+U2 s)*(2^s+1)≤130*U2 6*nMin s :=
  normalized_trial_band_core U1 U2 U1_growth (fun _=>U2_growth) U6_order S

private theorem ceiling_le (m d : Nat) (D : 0<d) : m≤((m+d-1)/d)*d := by
  have E := Nat.mod_add_div (m+d-1) d
  have R := Nat.mod_lt (m+d-1) D
  rw [Nat.mul_comm]
  omega

private theorem ceil_trial (u d : Nat) (D : 0<d) : 520*u≤trialCeiling u d*d :=
  ceiling_le (520*u) d D

theorem ceiling_rad_budget : 520*U2 6 ≤ K_rad*n0 :=
  ceil_trial (U2 6) n0 (by decide : 0<n0)

private theorem final_core {n q p d u v m K : Nat}
    (D : 0<d) (Q : q≤p) (M : m≤n)
    (C : 520*v≤K*d) (B : d*u*(p+1)≤130*v*m) :
    4*n*u*(q+1)≤K*n^2 := by
  have G : d*(4*u*(q+1))≤d*(K*n) := by
    calc
      _ ≤ d*(4*u*(p+1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = 4*(d*u*(p+1)) := by ac_rfl
      _ ≤ 4*(130*v*m) := Nat.mul_le_mul_left _ B
      _ = (520*v)*m := by calc
        _ = (4*130)*v*m := by ac_rfl
        _ = _ := rfl
      _ ≤ (K*d)*n := Nat.mul_le_mul C M
      _ = _ := by ac_rfl
  have F := Nat.mul_le_mul_left n (Nat.le_of_mul_le_mul_left G D)
  rw [Nat.pow_two]
  calc
    _ = n*(4*u*(q+1)) := by ac_rfl
    _ ≤ _ := F
    _ = _ := by ac_rfl

/-- Exact absolute trial coefficient, with no probabilistic
premises used or discharged by this arithmetic. -/
theorem advice_band_radius_budget {n s : Nat} (S : 6≤s) (advice : s=ell (ell n)) :
    4*n*(U1 s+U2 s)*(ell n+1)≤K_rad*n^2 := by
  obtain ⟨_,Q,_,_,M,_,_,_⟩ := advice_interval advice S
  exact final_core (by decide : 0<n0) Q M ceiling_rad_budget (normalized_trial_band S)

#print axioms radiusTwo_next_le_double
#print axioms trialU_doubling
#print axioms U1_growth
#print axioms U2_growth
#print axioms nMin_growth
#print axioms U6_order
#print axioms normalized_trial_band
#print axioms ceiling_rad_budget
#print axioms advice_band_radius_budget
end L4.AdviceBandRadiusBudget

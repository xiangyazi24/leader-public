import Leader.L4.ReportPulseProductionClose

namespace L4.ReportPulseQuietCells
open ReportLossArithmetic AdviceBandRadiusBudget ReportServiceMesh
open ReportPulseJointLoss ReportPulseProductionClose
open AllSizeProtocol PhysicalCustody

theorem ceil_le (a d : Nat) : ceilDiv a d*d≤a+d-1 :=
  Nat.div_mul_le_self _ _

theorem production_half_count (rho n : Nat) (N : 0<n) :
    (rho+2)*(2*halfCell n (hSize rho) (trialH rho))≤n*hSize rho := by
  let H := trialH rho
  let T := n*hSize rho
  let b := halfCell n (hSize rho) H
  have Hpos : 0<H := by unfold H trialH; omega
  have Epos : 0<E rho := by
    have P := hSize_positive rho
    by_cases Z : E rho=0
    · simp [hSize,Z] at P
    · omega
  have Bound : 40*H≤hSize rho := by
    have Hp : H≤H^3 := by
      rw [show H^3=H*(H^2) by rw [Nat.pow_succ,Nat.mul_comm]]
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos Hpos)
    have P : 19440≤19440*2^sigma := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
    calc
      40*H ≤ 19440*H := Nat.mul_le_mul_right _ (by decide)
      _ ≤ (19440*2^sigma)*H := Nat.mul_le_mul_right _ P
      _ ≤ (19440*2^sigma)*H^3 := Nat.mul_le_mul_left _ Hp
      _ ≤ hSize rho := Nat.le_mul_of_pos_right _ Epos
  have BT : 40*H≤T := Nat.le_trans Bound (Nat.le_mul_of_pos_left _ N)
  have U : b*(40*H)≤T+40*H-1 := ceil_le T (40*H)
  have V : b*(40*H)=40*(H*b) := by ac_rfl
  rw [V] at U
  change H*(2*b)≤T
  rw [show H*(2*b)=2*(H*b) by ac_rfl]
  omega

/-- Consecutive complete cells contained in any sufficiently long
half-open interval, even when its endpoints are off-grid. -/
theorem aligned_cells (B b lo hi k : Nat) (P : 0<b) (T : hi≤B)
    (Width : lo+(k+1)*(2*b)≤hi) :
    ∃ j, ∀ i<k,
      lo≤2*(j+i)*b ∧ (2*(j+i)+2)*b≤hi ∧ j+i<cells B b := by
  let d := 2*b
  let j := ceilDiv lo d
  have D : 0<d := by unfold d; omega
  have A : lo≤j*d := ceil_cover lo d D
  have U : j*d≤lo+d-1 := ceil_le lo d
  refine ⟨j,?_⟩
  intro i I
  have F : (i+1)*d≤k*d := Nat.mul_le_mul_right _ (by omega)
  have M : lo+(k+1)*d≤hi := Width
  rw [Nat.add_mul,Nat.one_mul] at M
  have Q : (j+i+1)*d≤hi := by
    rw [show j+i+1=j+(i+1) by omega,Nat.add_mul]
    omega
  refine ⟨?_,?_,?_⟩
  · rw [show 2*(j+i)*b=(j+i)*d by unfold d; ac_rfl,Nat.add_mul]
    omega
  · rw [show 2*(j+i)+2=(j+i+1)*2 by omega,Nat.mul_assoc]
    exact Q
  · unfold cells
    change j+i<B/d
    have L := (Nat.le_div_iff_mul_le D).mpr (Nat.le_trans Q T)
    omega

/-- In either inward-rounded middle window all marks have a full
radius-T interval on both sides outside the initial half-H warm-up. -/
theorem envelope_margins (rho n t : Nat) (N : 0<n)
    (Middle : ceilDiv (n*trialU rho) 5≤t ∧ t<4*(n*trialU rho)/5) :
    let T := n*hSize rho
    T/2≤t-T ∧ T≤t ∧ t+1+T≤n*trialU rho := by
  dsimp only
  have Scale := Nat.mul_lt_mul_of_pos_left (warm_gap_large rho) N
  have A : n*(25*hSize rho)=25*(n*hSize rho) := Nat.mul_left_comm _ _ _
  rw [A] at Scale
  generalize n*trialU rho=B at Middle Scale ⊢
  generalize n*hSize rho=T at Scale ⊢
  unfold ceilDiv at Middle
  obtain ⟨L,U⟩ := Middle
  omega

theorem envelope_service_cells (rho n t : Nat) (N : 0<n)
    (Middle : ceilDiv (n*trialU rho) 5≤t ∧ t<4*(n*trialU rho)/5) :
    let T := n*hSize rho
    let B := n*trialU rho
    let b := halfCell n (hSize rho) (trialH rho)
    (∃ j,∀ i<rho+1,T/2≤2*(j+i)*b ∧ t-T≤2*(j+i)*b ∧
      (2*(j+i)+2)*b≤t ∧ j+i<cells B b) ∧
    (∃ j,∀ i<rho+1,t+1≤2*(j+i)*b ∧
      (2*(j+i)+2)*b≤t+1+T ∧ j+i<cells B b) := by
  dsimp only
  let T := n*hSize rho
  let B := n*trialU rho
  let b := halfCell n (hSize rho) (trialH rho)
  obtain ⟨Warm,Past,Future⟩ := envelope_margins rho n t N Middle
  have Small : (rho+2)*(2*b)≤T := production_half_count rho n N
  have Pos : 0<b := halfCell_pos N (hSize_positive rho) (by unfold trialH; omega)
  change T/2≤t-T at Warm
  change T≤t at Past
  change t+1+T≤B at Future
  have S : (rho+1+1)*(2*b)≤T := Small
  have L := aligned_cells B b (t-T) t (rho+1) Pos (by omega) (by omega)
  have R := aligned_cells B b (t+1) (t+1+T) (rho+1) Pos Future (by omega)
  obtain ⟨j,J⟩ := L
  exact ⟨⟨j,fun i I=>⟨Nat.le_trans Warm (J i I).1,J i I⟩⟩,R⟩

open ReportByteRows ReportPulseRaw ReportPulseWarmup

variable {X G : Type} {n m : Nat}

def PaintAt (raw : X→Fin n→X) (put : G×Bool→Fin n) (p : Params)
    (bytes : G→X→BitVec p.w) (x : X) (g : G) (i : Nat) (w : List (Fin n)) : Prop :=
  ∃ pre e post, w=pre++e::post ∧ pre.length=i ∧
    countedPaint (put (g,true)) p (bytes g) (pre.foldl raw x) e=true

def WarmBy (raw : X→Fin n→X) (p : Params) (bytes : X→BitVec p.w) (x : X)
    (k : Nat) (w : List (Fin n)) : Prop :=
  ∃ pre post, w=pre++post ∧ pre.length≤k ∧ cleanAt raw p bytes x pre

theorem warm_prefix_of_hit (raw : X→Fin n→X) (p : Params) (bytes : X→BitVec p.w)
    (x : X) (k : Nat) (w : List (Fin n))
    (H : ((w.take k).foldl (warmNext raw p bytes) (warmInit p bytes x)).2=true) :
    WarmBy raw p bytes x k w := by
  obtain ⟨u,v,E,C⟩ := warm_firstCut_exists raw p bytes x (w.take k) H
  have S : u.length≤k := by
    have L := congrArg List.length E
    rw [List.length_take,List.length_append] at L
    omega
  have T : w=u++(v++w.drop k) := by
    rw [←List.append_assoc,←E,List.take_append_drop]
  exact ⟨u,_,T,S,firstCut_clean C⟩

theorem warm_cut_in_prefix (raw : X→Fin n→X) (p : Params)
    (bytes : X→BitVec p.w) (x : X) (k : Nat) (w a b : List (Fin n))
    (W : WarmBy raw p bytes x k w) (E : w=a++b) (L : k≤a.length) :
    ∃ pre rest,a=pre++rest ∧ cleanAt raw p bytes x pre := by
  obtain ⟨pre,post,J,B,C⟩ := W
  have P : pre <+: w := ⟨post,J.symm⟩
  have O : a <+: w := ⟨b,E.symm⟩
  obtain ⟨r,R⟩ := List.prefix_of_prefix_length_le P O (Nat.le_trans B L)
  exact ⟨pre,r,R.symm,C⟩

theorem paintPair_close (raw : X→Fin n→X) (put : G×Bool→Fin n) (p : Params)
    (bytes : G→X→BitVec p.w) (x : X) (g h : G)
    (k i j : Nat) (w : List (Fin n)) (Order : i<j) (After : k≤i)
    (Wa : WarmBy raw p (bytes g) x k w) (Wb : WarmBy raw p (bytes h) x k w)
    (A : PaintAt raw put p bytes x g i w) (B : PaintAt raw put p bytes x h j w) :
    closeAt raw put p bytes x g h i j w := by
  obtain ⟨u,e,tail,E,L,P⟩ := A
  obtain ⟨v,f,rest,R,M,Q⟩ := B
  have U : u++[e] <+: w := ⟨tail,by rw [List.append_assoc];exact E.symm⟩
  have V : v <+: w := ⟨f::rest,R.symm⟩
  obtain ⟨between,T⟩ := List.prefix_of_prefix_length_le U V (by simp [L,M]; omega)
  change (u++[e])++between=v at T
  have K : u.length+1+between.length=j := by rw [←M,←T]; simp; omega
  refine ⟨u,between,rest,e,f,?_,L,K,P,?_,?_,?_⟩
  · rw [R,←T]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  · rw [T]
    exact Q
  · exact warm_cut_in_prefix raw p _ x k w u (e::tail) Wa E (by omega)
  · intro _
    rw [T]
    exact warm_cut_in_prefix raw p _ x k w v (f::rest) Wb R (by omega)

/-- On a full no-close tape, every tested paint in the middle envelope
has a paint-free radius-T window on either side, among the full relevant
gate census. The two intervals omit the tested mark itself. -/
theorem envelope_quiet (rho : Nat) (gate : Fin m→G) (N : 0<n)
    (raw : X→Fin n→X) (put : G×Bool→Fin n) (p : Params)
    (bytes : G→X→BitVec p.w) (x : X) (w : List (Fin n))
    (Warm : ∀ a,WarmBy raw p (bytes (gate a)) x (n*hSize rho/2) w)
    (NoClose : ¬closeLoss rho gate raw put p bytes x w)
    (a : Fin m) (t : Nat) (Mid : ceilDiv (n*trialU rho) 5≤t ∧ t<4*(n*trialU rho)/5)
    (Hit : PaintAt raw put p bytes x (gate a) t w) :
    let T := n*hSize rho
    (∀ b i,t-T≤i→i<t→¬PaintAt raw put p bytes x (gate b) i w) ∧
    (∀ b i,t+1≤i→i<t+1+T→¬PaintAt raw put p bytes x (gate b) i w) := by
  dsimp only
  obtain ⟨Low,Tall,High⟩ := envelope_margins rho n t N Mid
  have TT : t<n*trialU rho := by omega
  have At : n*hSize rho/2≤t := by omega
  constructor
  · intro b i L R P
    have M : i<n*trialU rho := by omega
    have D : t-i≤3*n*hSize rho := by
      rw [Nat.mul_assoc]
      omega
    exact NoClose ⟨b,a,i,t,M,TT,D,paintPair_close raw put p bytes x _ _ _ i t w R
      (Nat.le_trans Low L) (Warm b) (Warm a) P Hit⟩
  · intro b i L R P
    have M : i<n*trialU rho := by omega
    have D : i-t≤3*n*hSize rho := by
      rw [Nat.mul_assoc]
      omega
    exact NoClose ⟨a,b,t,i,TT,M,D,paintPair_close raw put p bytes x _ _ _ t i w
      (by omega) At (Warm a) (Warm b) Hit P⟩

end L4.ReportPulseQuietCells

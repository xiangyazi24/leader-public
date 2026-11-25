import Leader.L4.ReportFastDispatchActual
import Leader.L4.ReportFourLossBridge
import Leader.L4.ReportWindowCounts

namespace L4.ReportServiceMesh
open Height FourLossStickyClock Classical
open AllSizeProtocol PhysicalCustody
open AdviceBandRadiusBudget ReportLossArithmetic
open ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportLeaseOwner ReportFastFiveGeometry
open ReportIngressOwnership ReportFastSplice ReportFastRawEvent
open ReportFastKernel ReportGoodEightBank ReportFastItem10Assembly
open ReportFastDispatch

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

noncomputable section

section Generic
variable {X J : Type} {n m : Nat}

/-- Complete cells only. The remaining B % (2*b) marks are uncharged
    by the loss predicate, but remain part of every counted word. -/
def cells (B b : Nat) : Nat := B/(2*b)

def halfMiss (step : X→Fin n→X) (classify : X→Fin n→Option J)
    (who : J) (x : X) (b k : Nat) (w : List (Fin n)) : Prop :=
  ReportWindowCounts.windowBad step
    (fun y u => who ∉ ShortNORCover.publications step classify y u)
    x (k*b) b w

def meshLoss (step : X→Fin n→X) (classify : X→Fin n→Option J)
    (writer : Fin m→J) (x : X) (B b : Nat)
    (w : List (Fin n)) : Prop :=
  ∃ i : Fin m, ∃ k : Fin (2*cells B b),
    halfMiss step classify (writer i) x b k.val w

theorem scaled_union (loss : Fin m→List (Fin n)→Prop)
    (B K R : Nat) (cap : ∀ i,K*badCount (loss i) B≤R) :
    K*badCount (fun w=>∃ i,loss i w) B≤m*R := by
  calc
    _ ≤ K*((List.ofFn fun i=>badCount (loss i) B).sum) :=
      Nat.mul_le_mul_left _ (badCount_union loss B)
    _ ≤ _ := by
      rw [←FiniteUniformStoppingTree.ofFn_sum_mul_left]
      have M := FiniteUniformStoppingTree.ofFn_sum_le (fun i=>K*badCount (loss i) B)
        (fun _=>R) cap
      rwa [FiniteUniformStoppingTree.ofFn_sum_const] at M

theorem half_fits (B b : Nat) (bp : 0<b)
    (k : Fin (2*cells B b)) : k.val*b+b≤B := by
  have C : cells B b*(2*b)≤B :=
    (Nat.le_div_iff_mul_le (by omega : 0<2*b)).mp
      (show cells B b≤B/(2*b) from Nat.le_refl _)
  have K : (k.val+1)*b≤(2*cells B b)*b :=
    Nat.mul_le_mul_right b (by have := k.isLt; omega)
  rw [Nat.add_mul,Nat.one_mul] at K
  exact Nat.le_trans K (show (2*cells B b)*b≤B from
    calc
      _ = cells B b*(2*b) := by ac_rfl
      _ ≤ B := C)

theorem full_tape_half_count (step : X→Fin n→X)
    (classify : X→Fin n→Option J) (Good : X→Prop)
    (closed : ∀ x e,Good x→Good (step x e))
    (x : X) (G : Good x) (who : J) (B b K : Nat)
    (bp : 0<b) (k : Fin (2*cells B b))
    (one : ∀ y,Good y→K*badCount
      (fun u=>who∉ShortNORCover.publications step classify y u) b≤n^b) :
    K*badCount (halfMiss step classify who x b k.val) B≤n^B := by
  let a := k.val*b
  have F : a+b≤B := half_fits B b bp k
  let c := B-(a+b)
  have L : a+b+c=B := Nat.add_sub_of_le F
  have W := ReportWindowCounts.window_bad_count step Good
    (fun y u=>who∉ShortNORCover.publications step classify y u)
    closed x G a b c K (n^b) one
  rw [L] at W
  have E : n^(a+c)*n^b=n^B := by
    rw [←Nat.pow_add]
    rw [show a+c+b=B by omega]
  rw [E] at W
  exact W

/-- General finite union. Uniform per-writer half-cell count is the
    only probabilistic input here. Both unions are on the same tape. -/
theorem mesh_count (step : X→Fin n→X)
    (classify : X→Fin n→Option J) (Good : X→Prop)
    (closed : ∀ x e,Good x→Good (step x e))
    (writer : Fin m→J) (x : X) (G : Good x)
    (B b K : Nat) (bp : 0<b)
    (one : ∀ i y,Good y→K*badCount
      (fun u=>writer i∉ShortNORCover.publications step classify y u) b≤n^b) :
    K*badCount (meshLoss step classify writer x B b) B≤
      m*(2*cells B b)*n^B := by
  let miss := fun i : Fin m => fun k : Fin (2*cells B b) =>
    halfMiss step classify (writer i) x b k.val
  have A (i : Fin m) (k : Fin (2*cells B b)) :
      K*badCount (miss i k) B≤n^B :=
    full_tape_half_count step classify Good closed x G
      (writer i) B b K bp k (one i)
  have D (i : Fin m) :
      K*badCount (fun w=>∃ k,miss i k w) B≤(2*cells B b)*n^B :=
    scaled_union (miss i) B K (n^B) (A i)
  have V := scaled_union (fun i=>fun w=>∃ k,miss i k w)
    B K ((2*cells B b)*n^B) D
  change K*badCount (fun w => ∃ i, ∃ k, miss i k w) B ≤ _
  simpa only [Nat.mul_assoc] using V

/-- Exact rounded mesh, using the actual uniform mean mu*n. -/
theorem rounded_mesh_count [DecidableEq J] (step : X→Fin n→X)
    (classify : X→Fin n→Option J) (Good : X→Prop)
    (closed : ∀ x e,Good x→Good (step x e))
    (writer : Fin m→J) (x : X) (G : Good x)
    (h0 H U mu0 : Nat) (N : 0<n) (I : 0<h0) (HH : 0<H)
    (Mu : 0<mu0) (census : m≤8*H)
    (mean : ShortTwoPublicationClock.UniformPublicationMean
      step classify Good (mu0*n)) :
    2^(h0/(80*H*mu0)) *
      badCount (meshLoss step classify writer x (n*U)
        (halfCell n h0 H)) (n*U) ≤
      (320*H^2*(U/h0+1))*n^(n*U) := by
  let b := halfCell n h0 H
  let B := n*U
  let K := 2^(h0/(80*H*mu0))
  have bp : 0<b := halfCell_pos N I HH
  have one (i : Fin m) (y : X) (Y : Good y) :
      K*badCount (fun u=>writer i∉
        ShortNORCover.publications step classify y u) b≤n^b :=
    ReportFourLossBridge.publication_halfcell_tail step classify Good closed
      (h:=h0) (H:=H) (mu:=mu0) N HH Mu mean (writer i) y Y
  have C : cells B b≤(20*H*U)/h0 := complete_cells N I HH
  have T : 8*H*cells B b*2≤320*H^2*(U/h0+1) :=
    complete_cell_union I C
  have W : m*(2*cells B b)≤320*H^2*(U/h0+1) := calc
    _ ≤ (8*H)*(2*cells B b) := Nat.mul_le_mul_right _ census
    _ = 8*H*cells B b*2 := by ac_rfl
    _ ≤ _ := T
  exact Nat.le_trans (mesh_count step classify Good closed writer x G B b K bp one)
    (Nat.mul_le_mul_right _ W)

/-- The deterministic event the trial consumer needs: the same cell's
    two complete, chronological raw segments, with the second starting
    at the actual endpoint of the first. -/
def TwoCellCovers (step : X→Fin n→X) (classify : X→Fin n→Option J)
    (writer : Fin m→J) (x : X) (B b : Nat)
    (w : List (Fin n)) : Prop :=
  ∀ c : Fin (cells B b),
    let a := (2*c.val)*b
    let p := w.take a
    let u := (w.drop a).take b
    let v := ((w.drop a).drop b).take b
    ∀ i, writer i∈ShortNORCover.publications step classify
        (runWord step x p) u ∧
      writer i∈ShortNORCover.publications step classify
        (runWord step (runWord step x p) u) v

-- CHECK: core List.take_succ_cons / drop_succ_cons simp syntax;
-- ReportWindowCounts.lean:35–38 uses the same take/drop API.
private theorem take_add_split {A : Type} (w : List A) (a b : Nat) :
    w.take (a+b)=w.take a++(w.drop a).take b := by
  induction a generalizing w with
  | zero => simp
  | succ a ih =>
    cases w with
    | nil => simp
    | cons e w =>
      simp [Nat.succ_add,ih]

private theorem drop_add_split {A : Type} (w : List A) (a b : Nat) :
    w.drop (a+b)=(w.drop a).drop b := by
  induction a generalizing w with
  | zero => simp
  | succ a ih =>
    cases w with
    | nil => simp
    | cons e w =>
      rw [Nat.succ_add]
      exact ih w

theorem covers_of_no_mesh_loss (step : X→Fin n→X)
    (classify : X→Fin n→Option J) (writer : Fin m→J)
    (x : X) (B b : Nat) (w : List (Fin n))
    (OK : ¬meshLoss step classify writer x B b w) :
    TwoCellCovers step classify writer x B b w := by
  intro c
  dsimp only
  intro i
  let k0 : Fin (2*cells B b) := ⟨2*c.val,by have := c.isLt; omega⟩
  let k1 : Fin (2*cells B b) := ⟨2*c.val+1,by have := c.isLt; omega⟩
  have H (k : Fin (2*cells B b)) :
      writer i∈ShortNORCover.publications step classify
        (runWord step x (w.take (k.val*b))) ((w.drop (k.val*b)).take b) :=
    Classical.byContradiction (fun Z=>OK ⟨i,k,Z⟩)
  have A := H k0
  have D := H k1
  change writer i∈ShortNORCover.publications step classify
    (runWord step x (w.take ((2*c.val+1)*b)))
    ((w.drop ((2*c.val+1)*b)).take b) at D
  rw [Nat.add_mul,Nat.one_mul,take_add_split,drop_add_split,runWord_append] at D
  exact ⟨A,D⟩

/-- Complete-cell split: the two segments each contain exactly b marks
    and are disjoint contiguous pieces of the very same original tape. -/
theorem cell_split (B b : Nat) (bp : 0<b) (w : List (Fin n))
    (W : w.length=B) (c : Fin (cells B b)) :
    let a := (2*c.val)*b
    let p := w.take a
    let u := (w.drop a).take b
    let v := ((w.drop a).drop b).take b
    let q := ((w.drop a).drop b).drop b
    w=p++(u++(v++q)) ∧ p.length=a ∧ u.length=b ∧ v.length=b := by
  dsimp only
  let a := (2*c.val)*b
  let k : Fin (2*cells B b) := ⟨2*c.val+1,by have := c.isLt; omega⟩
  have F := half_fits B b bp k
  change (2*c.val+1)*b+b≤B at F
  rw [Nat.add_mul,Nat.one_mul] at F
  change a+b+b≤B at F
  refine ⟨?_,?_,?_,?_⟩
  · -- CHECK: List.take_append_drop, take/drop API at
    -- ReportWindowCounts.lean:35–38.
    have A := List.take_append_drop b ((w.drop a).drop b)
    have D := List.take_append_drop b (w.drop a)
    have P := List.take_append_drop a w
    rw [A,D,P]
  · rw [List.length_take,W,Nat.min_eq_left (by omega : a≤B)]
  · rw [List.length_take,List.length_drop,W,
      Nat.min_eq_left (by omega : b≤B-a)]
  · rw [List.length_take,List.length_drop,List.length_drop,W,
      Nat.min_eq_left (by omega : b≤B-a-b)]

/-- Extract an actual old-mark receipt, not a position in a filtered
    scheduler. Its prefix includes all intervening physical marks. -/
theorem publication_occurs (step : X→Fin n→X)
    (classify : X→Fin n→Option J) (j : J) (x : X)
    (w : List (Fin n)) (H : j∈ShortNORCover.publications step classify x w) :
    ∃ p e q, w=p++(e::q) ∧ classify (runWord step x p) e=some j := by
  induction w generalizing x with
  | nil => simp [ShortNORCover.publications] at H
  | cons e w ih =>
    cases C : classify x e with
    | none =>
      have T : j∈ShortNORCover.publications step classify (step x e) w := by
        simpa [ShortNORCover.publications,C] using H
      obtain ⟨p,f,q,V,F⟩ := ih (step x e) T
      exact ⟨e::p,f,q,by rw [V]; rfl,F⟩
    | some k =>
      have T : j=k ∨ j∈ShortNORCover.publications step classify (step x e) w := by
        simpa [ShortNORCover.publications,C] using H
      rcases T with E|T
      · exact ⟨[],e,w,rfl,by rw [E]; exact C⟩
      · obtain ⟨p,f,q,V,F⟩ := ih (step x e) T
        exact ⟨e::p,f,q,by rw [V]; rfl,F⟩

/-- Both extracted physical receipts are strictly ordered: the first
    lies in u and the second in v. The split is inside the actual word.
    No statement about a new ACQUIRE is inferred by this combinator. -/
theorem chronological_receipts (step : X→Fin n→X)
    (classify : X→Fin n→Option J) (writer : Fin m→J)
    (x : X) (B b : Nat) (w : List (Fin n))
    (OK : TwoCellCovers step classify writer x B b w)
    (c : Fin (cells B b)) (i : Fin m) :
    let a := (2*c.val)*b
    let p := w.take a
    let u := (w.drop a).take b
    let v := ((w.drop a).drop b).take b
    ∃ p1 e1 q1 p2 e2 q2,
      u=p1++(e1::q1) ∧ v=p2++(e2::q2) ∧
      classify (runWord step (runWord step x p) p1) e1=some (writer i) ∧
      classify (runWord step (runWord step (runWord step x p) u) p2) e2=
        some (writer i) := by
  dsimp only
  obtain ⟨p1,e1,q1,L1,C1⟩ := publication_occurs step classify _
    _ _ (OK c i).1
  obtain ⟨p2,e2,q2,L2,C2⟩ := publication_occurs step classify _
    _ _ (OK c i).2
  exact ⟨p1,e1,q1,p2,e2,q2,L1,L2,C1,C2⟩

end Generic

section Arithmetic

/-- The two production radii, in the report's order. -/
def meshRadius (d : Sheet) (s : Nat) : Nat :=
  match d with
  | .first => s
  | .second => radiusTwo s

/-- A geometry factor bounding the actual FAST coefficient after
    removal of its exponential constant. -/
def meshFactor (d : Sheet) (s : Nat) : Nat :=
  match d with
  | .first => 81
  | .second => (s+1)*(81*(2*s+1))

private theorem square_pow_aux (k : Nat) : (k+4)*(k+4)≤2^(k+4) := by
  induction k with
  | zero => decide
  | succ k ih =>
    let t := k+4
    have T : 4≤t := by dsimp [t]; omega
    have A : t*t≤2^t := ih
    have D : 3*t≤t*t := Nat.mul_le_mul_right t (by omega)
    have L : (t+1)*(t+1)≤2*(t*t) := by
      simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
      omega
    change (t+1)*(t+1)≤2^(t+1)
    rw [Nat.pow_succ]
    calc
      _ ≤ 2*(t*t) := L
      _ = (t*t)*2 := Nat.mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_right _ A

theorem radius_ge_self {s : Nat} (S : 6≤s) : s≤radiusTwo s := by
  have A := square_pow_aux (s-4)
  rw [show s-4+4=s by omega] at A
  have D := (radius_ceiling_bounds s (by omega)).1
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans A D) (by omega)

theorem meshFactor_pos (d : Sheet) (s : Nat) : 0<meshFactor d s := by
  cases d
  · change 0 < 81; decide
  · change 0<(s+1)*(81*(2*s+1))
    exact Nat.mul_pos (by omega) (Nat.mul_pos (by decide) (by omega))

theorem meshFactor_le (d : Sheet) (s : Nat) (S : 6≤s) :
    meshFactor d s≤243*(trialH (meshRadius d s))^2 := by
  cases d
  · change 81≤243*(s+2)^2
    have A : 1≤(s+2)^2 := Nat.pow_pos (by omega)
    exact Nat.le_trans (by decide : 81≤243)
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 243 A)
  · let H := trialH (radiusTwo s)
    have R := radius_ge_self S
    have A : s+1≤H := by dsimp [H,trialH]; omega
    have D : 2*s+1≤3*H := by dsimp [H,trialH]; omega
    have T : 81*(2*s+1)≤243*H := calc
      _ ≤ 81*(3*H) := Nat.mul_le_mul_left _ D
      _ = _ := by rw [←Nat.mul_assoc]
    change (s+1)*(81*(2*s+1))≤243*H^2
    calc
      _ ≤ H*(243*H) := Nat.mul_le_mul A T
      _ = _ := by rw [Nat.pow_two]; ac_rfl

theorem deployed_mu_pos (d : Sheet) (s : Nat) (S : 6≤s) :
    0<mu d s := by
  have D := ReportPrelaunchDoorProducer.digits_positive d (by omega : 0<s)
  have W : 0<maxWidth d s := by cases d <;> simp [maxWidth] <;> omega
  unfold mu coefficient denominator
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) D) W)
    (Nat.pow_pos (by decide))

theorem deployed_mu_le (d : Sheet) (s : Nat) (S : 6≤s) :
    mu d s≤2^sigma*meshFactor d s := by
  cases d
  · rw [mu_first_constant]
    have C := coefficient_le_of_exp 1 81 sigma exponent_le_deployed
    simpa only [meshFactor,Nat.mul_one] using C
  · have C := coefficient_le_of_exp (s+1) (81*(2*s+1)) sigma exponent_le_deployed
    exact Nat.le_trans (mu_second_poly S)
      (by simpa only [meshFactor,Nat.mul_assoc] using C)

theorem hSize_positive (rho : Nat) : 0<hSize rho := by
  unfold hSize
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
      (Nat.pow_pos (by unfold trialH; omega))) (by unfold E; omega)

def meshExponent (d : Sheet) (s : Nat) : Nat :=
  hSize (meshRadius d s)/(80*trialH (meshRadius d s)*mu d s)

theorem deployed_exponent (d : Sheet) (s : Nat) (S : 6≤s) :
    E (meshRadius d s)≤meshExponent d s := by
  let rho := meshRadius d s
  let H := trialH rho
  let g := meshFactor d s
  have gp : 0<g := meshFactor_pos d s
  have hp : 0<H := by dsimp [H,trialH]; omega
  have mp := deployed_mu_pos d s S
  have mp' : 0<2^sigma*g := Nat.mul_pos (Nat.pow_pos (by decide)) gp
  have T : E rho≤hSize rho/(80*H*(2^sigma*g)) :=
    service_exponent (rho:=rho) gp (meshFactor_le d s S)
  have A : E rho*(80*H*(2^sigma*g))≤hSize rho :=
    (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) mp')).mp T
  change E rho≤hSize rho/(80*H*mu d s)
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) mp)).mpr
  exact Nat.le_trans
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (deployed_mu_le d s S))) A

theorem deployed_mesh_integer_budget (d : Sheet) (s : Nat) (S : 6≤s) :
    8*(320*(trialH (meshRadius d s))^2*
      (trialU (meshRadius d s)/hSize (meshRadius d s)+1)) <
      2^(meshExponent d s) := by
  let rho := meshRadius d s
  have A : 320*(trialH rho)^2*(trialU rho/hSize rho+1)≤
      640*(trialH rho)^2*(trialU rho/hSize rho+1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 320≤640))
  calc
    _ ≤ 8*(640*(trialH rho)^2*(trialU rho/hSize rho+1)) :=
      Nat.mul_le_mul_left _ A
    _ < 2^(E rho) := mesh_loss_lt rho
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (deployed_exponent d s S)

end Arithmetic

section Deployed
variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

/-- The signed-predecessor chart census is deliberately explicit.
    'relevant' must be the actual local service cone, with the one-root
    source-to-target shift included. There is no dependence on w. -/
structure WriterCensus (rho : Nat)
    (relevant : Fin n→Raw s n→Target h→Prop) where
  size : Fin n→Raw s n→Nat
  writer : ∀ i x,Fin (size i x)→Target h
  cap : ∀ i x,size i x≤8*trialH rho
  mem_iff : ∀ i x j,relevant i x j ↔ ∃ k,writer i x k=j

def rawMeshLoss (d : Sheet) (writer : Fin m→Target h)
    (x : Raw s n) (w : List (Fin n)) : Prop :=
  meshLoss (rawNext s) (classify d h) writer x
    (n*trialU (meshRadius d s))
    (halfCell n (hSize (meshRadius d s)) (trialH (meshRadius d s))) w

def RawTwoCellCovers (d : Sheet) (writer : Fin m→Target h)
    (x : Raw s n) (w : List (Fin n)) : Prop :=
  TwoCellCovers (rawNext s) (classify d h) writer x
    (n*trialU (meshRadius d s))
    (halfCell n (hSize (meshRadius d s)) (trialH (meshRadius d s))) w

theorem deployed_mesh_count (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (advice : s=ell (ell n)) (S : 6≤s)
    (Lo : ∀ r : Owner h,minWidth d s≤gapLen G r)
    (Hi : G.B≤maxWidth d s)
    (writer : Fin m→Target h) (C : m≤8*trialH (meshRadius d s))
    (x : Raw s n) (X : GoodEightBank d hh P G x) :
    2^(meshExponent d s) *
      badCount (rawMeshLoss d writer x) (n*trialU (meshRadius d s))≤
      (320*(trialH (meshRadius d s))^2*
        (trialU (meshRadius d s)/hSize (meshRadius d s)+1))*
          n^(n*trialU (meshRadius d s)) := by
  let rho := meshRadius d s
  have Digit := ReportPrelaunchDoorProducer.digits_positive d (by omega : 0<s)
  have closed : ∀ y e,GoodEightBank d hh P G y→
      GoodEightBank d hh P G (rawNext s y e) :=
    good_bank_closed d N hh G F Digit
      (ReportWriteRailSupplier.rail_supplier d N hh G F Digit)
  exact rounded_mesh_count (rawNext s) (classify d h)
    (GoodEightBank d hh P G) closed writer x X
    (hSize rho) (trialH rho) (trialU rho) (mu d s)
    (by omega) (hSize_positive rho) (by unfold trialH; omega)
    (deployed_mu_pos d s S) C
    (deployed_publication_mean d N hh G F advice S Lo Hi)

theorem deployed_mesh_cap (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (advice : s=ell (ell n)) (S : 6≤s)
    (Lo : ∀ r : Owner h,minWidth d s≤gapLen G r)
    (Hi : G.B≤maxWidth d s)
    (writer : Fin m→Target h) (C : m≤8*trialH (meshRadius d s))
    (x : Raw s n) (X : GoodEightBank d hh P G x) :
    8*badCount (rawMeshLoss d writer x) (n*trialU (meshRadius d s))≤
      n^(n*trialU (meshRadius d s)) := by
  let rho := meshRadius d s
  let B := n*trialU rho
  let K := 2^(meshExponent d s)
  let R := 320*(trialH rho)^2*(trialU rho/hSize rho+1)
  let L := badCount (rawMeshLoss d writer x) B
  have A : K*L≤R*n^B :=
    deployed_mesh_count d N hh G F advice S Lo Hi writer C x X
  have T : 8*R<K := deployed_mesh_integer_budget d s S
  have V : K*(8*L)≤K*n^B := calc
    _ = 8*(K*L) := by ac_rfl
    _ ≤ 8*(R*n^B) := Nat.mul_le_mul_left _ A
    _ = (8*R)*n^B := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_of_lt T)
  exact Nat.le_of_mul_le_mul_left V (Nat.pow_pos (by decide))

theorem raw_covers_of_no_mesh_loss (d : Sheet)
    (writer : Fin m→Target h) (x : Raw s n) (w : List (Fin n))
    (M : ¬rawMeshLoss d writer x w) :
    RawTwoCellCovers d writer x w :=
  covers_of_no_mesh_loss (rawNext s) (classify d h) writer x _ _ w M

/-- A relevant target is in the census's two covers; repetitions of
    enumeration entries cannot remove this guarantee. -/
theorem relevant_two_cell_covers (d : Sheet)
    {relevant : Fin n→Raw s n→Target h→Prop}
    (C : WriterCensus (meshRadius d s) relevant)
    (i : Fin n) (x : Raw s n) (w : List (Fin n))
    (OK : RawTwoCellCovers d (C.writer i x) x w)
    (j : Target h) (J : relevant i x j) :
    RawTwoCellCovers d (fun _ : Fin 1=>j) x w := by
  obtain ⟨k,K⟩ := (C.mem_iff i x j).mp J
  intro c
  dsimp only
  intro z
  have A := OK c k
  rw [K] at A
  exact A

end Deployed

#print axioms scaled_union
#print axioms full_tape_half_count
#print axioms rounded_mesh_count
#print axioms covers_of_no_mesh_loss
#print axioms cell_split
#print axioms chronological_receipts
#print axioms deployed_exponent
#print axioms deployed_mesh_integer_budget
#print axioms deployed_mesh_count
#print axioms deployed_mesh_cap
#print axioms relevant_two_cell_covers

end
end L4.ReportServiceMesh


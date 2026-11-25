import Leader.L4.ReportByteRows

namespace L4.ReportProtectedInterval
open ReportByteRows

variable {I X : Type}

/-- Fixed directed geometry of a lower-root ring, reused by every mark. -/
def Target (neighbor : Bool→I→I) (Z : I→Bool) (dir : Bool) (i : I) : Nat → Prop
  | 0 => False
  | k+1 => Z (neighbor dir i)=true ∨ Target neighbor Z dir (neighbor dir i) k

def Path (neighbor : Bool→I→I) (ball : I→Prop) (dir : Bool) (i : I) : Nat→Prop
  | 0 => ball i
  | k+1 => ball i ∧ Path neighbor ball dir (neighbor dir i) k

private theorem path_here {neighbor : Bool→I→I} {ball : I→Prop} {dir : Bool} {i : I}
    {k : Nat} (P : Path neighbor ball dir i k) : ball i := by
  cases k
  · exact P
  · exact P.1

theorem target_congr (neighbor : Bool→I→I) (ball : I→Prop)
    (Z Z' : I→Bool) (H : ∀ i, ball i → Z i=Z' i)
    (dir : Bool) (i : I) (k : Nat) (P : Path neighbor ball dir i k) :
    Target neighbor Z dir i k ↔ Target neighbor Z' dir i k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    change _ ∨ _ ↔ _ ∨ _
    rw [H _ (path_here P.2),ih _ P.2]

/-- These are geometry-only premises: the center cannot revisit itself
within the radius, while each other ball site has an in-ball path back
to the center in at most the radius. -/
structure BallGeometry (radius : Nat) (neighbor : Bool→I→I) (ball : I→Prop)
    (center : I) (centerMask : I→Bool) : Prop where
  center_mem : ball center
  center_mask : centerMask center=true
  other_mask : ∀ i, ball i → i≠center → centerMask i=false
  center_paths : ∀ dir, Path neighbor ball dir center radius
  center_no_return : ∀ dir, ¬Target neighbor centerMask dir center radius
  inward : ∀ i, ball i → i≠center → ∃ dir k, 1≤k ∧ k≤radius ∧
    Path neighbor ball dir i k ∧ Target neighbor centerMask dir i k

structure Readout (X I : Type) where
  z : X→I→Bool
  a : X→I→Bool
  u : X→I→Bool→Nat
  b : X→I→Nat

def thresholds (radius l r : Nat) : Nat :=
  2*(decide (l<radius)).toNat+(decide (r<radius)).toNat

def updateDistance (radius : Nat) (a : Bool) (u : Nat) : Nat :=
  if a then 0 else min radius (u+1)

theorem threshold_step (radius j u : Nat) (a : Bool) (J : 1≤j) (R : j≤radius) :
    updateDistance radius a u<j ↔ a=true ∨ (1<j ∧ u<j-1) := by
  cases a with
  | true => simp [updateDistance]; omega
  | false =>
    simp only [updateDistance,Bool.false_eq_true,if_false,false_or]
    constructor
    · intro H
      have U : u+1<j := by
        by_cases T : u+1<j
        · exact T
        · have W : j≤min radius (u+1) := Nat.le_min.mpr ⟨R,by omega⟩
          omega
      omega
    · rintro ⟨J1,H⟩
      exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)

/-- Visible state only; no future safety in the definition. Directions
whose paths leave the ball have no radius-prefix equation. -/
structure Visible (R : Readout X I) (radius : Nat) (neighbor : Bool→I→I)
    (ball : I→Prop) (centerMask : I→Bool) (x : X) : Prop where
  isolated : ∀ i, ball i → R.z x i=centerMask i
  captured : ∀ i, ball i → R.a x i=R.z x i
  interior : ∀ i dir k, k≤radius → Path neighbor ball dir i k →
    (R.u x i dir<k ↔ Target neighbor (R.z x) dir i k)
  pair : ∀ i, ball i → R.b x i=thresholds radius (R.u x i true) (R.u x i false)

private theorem thresholds_zero (radius l r : Nat) :
    thresholds radius l r=0 ↔ ¬l<radius ∧ ¬r<radius := by
  by_cases L : l<radius <;> by_cases R : r<radius <;> simp [thresholds,L,R]

/-- A protected ball's old selected B-zero is its old visible Z. -/
theorem old_paint_identity (R : Readout X I) (radius : Nat) (neighbor : Bool→I→I)
    (ball : I→Prop) (center : I) (centerMask : I→Bool)
    (G : BallGeometry radius neighbor ball center centerMask)
    (x : X) (V : Visible R radius neighbor ball centerMask x) (i : I) (I' : ball i) :
    (R.b x i==0)=R.z x i := by
  classical
  by_cases C : i=center
  · subst i
    have out (d : Bool) : ¬R.u x center d<radius := by
      intro H
      have T := (V.interior center d radius (Nat.le_refl _) (G.center_paths d)).mp H
      exact G.center_no_return d
        ((target_congr _ _ _ _ V.isolated d center radius (G.center_paths d)).mp T)
    rw [V.isolated center I',G.center_mask,V.pair center I']
    exact beq_iff_eq.mpr ((thresholds_zero _ _ _).mpr ⟨out true,out false⟩)
  · obtain ⟨d,k,_,K,P,H⟩ := G.inward i I' C
    have Q := (target_congr _ _ _ _ V.isolated d i k P).mpr H
    have U := Nat.lt_of_lt_of_le ((V.interior i d k K P).mpr Q) K
    rw [V.isolated i I',G.other_mask i I' C,V.pair i I']
    apply beq_false_of_ne
    intro T
    have N := (thresholds_zero _ _ _).mp T
    cases d
    · exact N.2 U
    · exact N.1 U

/-- Exact two-cut one-mark contract, not a claim that the current row
producers already establish it. The publication alternative describes
the actual post-selector fields and OLD leased neighbors. -/
structure MarkSemantics (R : Readout X I) (radius : Nat) (neighbor : Bool→I→I)
    (ball : I→Prop) (paint : I→Bool) (x y : X) : Prop where
  pulse : ∀ i, ball i → R.z y i=(if paint i then R.b x i==0 else R.z x i)
  selected : ∀ i, ball i →
    (R.a y i=R.a x i ∧ R.b y i=R.b x i ∧ ∀ dir, R.u y i dir=R.u x i dir) ∨
    (R.a y i=R.z x i ∧
      (∀ dir, R.u y i dir=updateDistance radius
        (R.a x (neighbor dir i)) (R.u x (neighbor dir i) dir)) ∧
      R.b y i=thresholds radius (R.u y i true) (R.u y i false))

theorem one_mark (R : Readout X I) (radius : Nat) (neighbor : Bool→I→I)
    (ball : I→Prop) (center : I) (centerMask : I→Bool)
    (G : BallGeometry radius neighbor ball center centerMask)
    (x y : X) (paint : I→Bool)
    (V : Visible R radius neighbor ball centerMask x)
    (M : MarkSemantics R radius neighbor ball paint x y) :
    Visible R radius neighbor ball centerMask y ∧ ∀ i, ball i → R.z y i=R.z x i := by
  have S (i : I) (H : ball i) : R.z y i=R.z x i := by
    rw [M.pulse i H,old_paint_identity R radius neighbor ball center centerMask G x V i H]
    split <;> rfl
  refine ⟨⟨fun i H=>(S i H).trans (V.isolated i H),?_,?_,?_⟩,S⟩
  · intro i H
    rcases M.selected i H with A|A
    · exact A.1.trans ((V.captured i H).trans (S i H).symm)
    · exact A.1.trans (S i H).symm
  · intro i dir k K P
    have H : ball i := path_here P
    rw [target_congr neighbor ball (R.z y) (R.z x) S dir i k P]
    rcases M.selected i H with A|A
    · rw [A.2.2 dir]
      exact V.interior i dir k K P
    · cases k with
      | zero => simp [Target]
      | succ k =>
        have N := path_here P.2
        rw [A.2.1 dir,V.captured (neighbor dir i) N,
          threshold_step _ _ _ _ (by omega) K]
        change _ ↔ (R.z x (neighbor dir i)=true ∨ Target neighbor (R.z x) dir (neighbor dir i) k)
        have Q := V.interior (neighbor dir i) dir k (by omega) P.2
        rw [←Q]
        have E : (1<k+1 ∧ R.u x (neighbor dir i) dir<k+1-1) ↔
            R.u x (neighbor dir i) dir<k := by omega
        rw [E]
  · intro i H
    rcases M.selected i H with A|A
    · rw [A.2.1,A.2.2 true,A.2.2 false]
      exact V.pair i H
    · exact A.2.2

/-- Direct literal right-lower-header consequence. With old B-zero
equal to old Z, even a painting mark preserves Z; simultaneous accepted
COMMIT therefore writes the same A as the new visible Z. -/
theorem literal_right_sticky (p : Params) (hu : Bool) (u v : BitVec p.w)
    (B : (publicationPair p v (publicationSelector p v)==0)=Z p v) :
    Z p ((row p (hu,true) (u,v)).2.apply v)=Z p v := by
  rw [row_right_Z,B]
  split <;> rfl

theorem literal_right_sticky_commit (p : Params) (hu : Bool) (u v : BitVec p.w)
    (dsc : Nat) (G : CommitGuard p hu u v dsc)
    (B : (publicationPair p v (publicationSelector p v)==0)=Z p v) :
    let y := (row p (hu,true) (u,v)).2.apply v
    Z p y=Z p v ∧ publicationA p y (publicationSelector p y)=Z p y := by
  have C := same_mark_publication p hu u v dsc G
  have S := literal_right_sticky p hu u v B
  dsimp only at C ⊢
  exact ⟨S,congrArg (publicationA p _) C.1 |>.trans (C.2.1.trans S.symm)⟩

#print axioms threshold_step
#print axioms old_paint_identity
#print axioms one_mark
#print axioms literal_right_sticky_commit

/-- A site is sticky when a single actually protected center covers it.
The all-owner two-cut epoch is carried separately, not existentially
recreated from the selected byte snapshot. -/
def Sticky (R : Readout X I) (radius : Nat) (neighbor : Bool→I→I)
    (balls : I→I→Prop) (masks : I→I→Bool) (i : I) (x : X) : Prop :=
  ∃ center, balls center i ∧ Visible R radius neighbor (balls center) (masks center) x

variable {M : Type}

theorem sticky_step (R : Readout X I) (radius : Nat) (neighbor : Bool→I→I)
    (balls : I→I→Prop) (masks : I→I→Bool)
    (G : ∀ c, BallGeometry radius neighbor (balls c) c (masks c))
    (step : X→M→X) (E : X→Prop) (paint : X→M→I→Bool)
    (epoch_step : ∀ x e, E x → E (step x e))
    (sem : ∀ x e c, E x → MarkSemantics R radius neighbor (balls c) (paint x e) x (step x e))
    (x : X) (e : M) (i : I) (epoch : E x) (S : Sticky R radius neighbor balls masks i x) :
    E (step x e) ∧ Sticky R radius neighbor balls masks i (step x e) ∧
      R.z (step x e) i=R.z x i := by
  obtain ⟨c,H,V⟩ := S
  have N := one_mark R radius neighbor (balls c) c (masks c) (G c) x (step x e) (paint x e)
    V (sem x e c epoch)
  exact ⟨epoch_step x e epoch,⟨c,H,N.1⟩,N.2 i H⟩

/-- Once every lower word is covered, every future original mark
retains the two-cut epoch, the visible cover, and the selected Z mask. -/
theorem covering_run (R : Readout X I) (radius : Nat) (neighbor : Bool→I→I)
    (balls : I→I→Prop) (masks : I→I→Bool)
    (G : ∀ c, BallGeometry radius neighbor (balls c) c (masks c))
    (step : X→M→X) (E : X→Prop) (paint : X→M→I→Bool)
    (epoch_step : ∀ x e, E x → E (step x e))
    (sem : ∀ x e c, E x → MarkSemantics R radius neighbor (balls c) (paint x e) x (step x e))
    (x : X) (w : List M) (epoch : E x) (cover : ∀ i, Sticky R radius neighbor balls masks i x) :
    let y := w.foldl step x
    E y ∧ (∀ i, Sticky R radius neighbor balls masks i y) ∧ ∀ i, R.z y i=R.z x i := by
  induction w generalizing x with
  | nil => exact ⟨epoch,cover,fun _=>rfl⟩
  | cons e w ih =>
    have S (i : I) := sticky_step R radius neighbor balls masks G step E paint epoch_step sem
      x e i epoch (cover i)
    obtain ⟨Y,V,Z⟩ := ih (step x e) (epoch_step x e epoch) (fun i=>(S i).2.1)
    exact ⟨Y,V,fun i=>(Z i).trans (S i).2.2⟩

#print axioms sticky_step
#print axioms covering_run
end L4.ReportProtectedInterval

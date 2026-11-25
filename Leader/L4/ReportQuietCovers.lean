import Leader.L4.ReportProtectedInterval

namespace L4.ReportQuietCovers
open ReportProtectedInterval
variable {I X : Type}

/-- The radius in the stored threshold byte is fixed; the separate depth
counts how many directional threshold comparisons are certified. -/
def CorrectAt (R : Readout X I) (radius : Nat) (neighbor : Bool→I→I) (ball : I→Prop)
    (z : I→Bool) (depth : Nat) (x : X) (i : I) : Prop :=
  R.a x i=z i ∧ R.b x i=thresholds radius (R.u x i true) (R.u x i false) ∧
    ∀ dir k,k≤depth → Path neighbor ball dir i k →
      (R.u x i dir<k ↔ Target neighbor z dir i k)

def Frame (R : Readout X I) (x y : X) (i : I) : Prop :=
  R.a y i=R.a x i ∧ R.b y i=R.b x i ∧ ∀ d,R.u y i d=R.u x i d

def Publish (R : Readout X I) (rho : Nat) (near : Bool→I→I) (x y : X) (i : I) : Prop :=
  R.a y i=R.z x i ∧
    (∀ d,R.u y i d=updateDistance rho (R.a x (near d i)) (R.u x (near d i) d)) ∧
    R.b y i=thresholds rho (R.u y i true) (R.u y i false)

private theorem path_here {neighbor : Bool→I→I} {ball : I→Prop} {dir : Bool} {i : I}
    {k : Nat} (P : Path neighbor ball dir i k) : ball i := by
  cases k
  · exact P
  · exact P.1

theorem correct_frame (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop)
    (z : I→Bool) (d : Nat) (x y : X) (i : I)
    (A : CorrectAt R rho near ball z d x i) (H : Frame R x y i) :
    CorrectAt R rho near ball z d y i := by
  refine ⟨H.1.trans A.1,?_,?_⟩
  · rw [H.2.1,H.2.2 true,H.2.2 false]
    exact A.2.1
  · intro side k K P
    rw [H.2.2 side]
    exact A.2.2 side k K P

theorem correct_zero_of_publication
    (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop) (z : I→Bool)
    (x y : X) (i : I) (Z : R.z x i=z i) (P : Publish R rho near x y i) :
    CorrectAt R rho near ball z 0 y i := by
  refine ⟨P.1.trans Z,P.2.2,?_⟩
  intro side k K _
  have E : k=0 := by omega
  subst k
  simp [Target]

theorem correct_succ_of_publication
    (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop) (z : I→Bool)
    (depth : Nat) (D : depth+1≤rho)
    (x y : X) (i : I) (Z : R.z x i=z i)
    (A : ∀ j,ball j→CorrectAt R rho near ball z depth x j)
    (P : Publish R rho near x y i) :
    CorrectAt R rho near ball z (depth+1) y i := by
  refine ⟨P.1.trans Z,P.2.2,?_⟩
  intro dir k K PathK
  cases k with
  | zero => simp [Target]
  | succ k =>
    have B := A (near dir i) (path_here PathK.2)
    have V := B.2.2 dir k (by omega) PathK.2
    rw [P.2.1 dir,B.1,threshold_step _ _ _ _ (by omega) (by omega)]
    change _ ↔ z (near dir i)=true ∨ Target near z dir (near dir i) k
    rw [←V]
    have E : (1<k+1 ∧ R.u x (near dir i) dir<k+1-1) ↔
        R.u x (near dir i) dir<k := by omega
    rw [E]

theorem correct_weaken (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop)
    (z : I→Bool) (d d' : Nat) (D : d'≤d) (x : X) (i : I)
    (A : CorrectAt R rho near ball z d x i) :
    CorrectAt R rho near ball z d' x i :=
  ⟨A.1,A.2.1,fun dir k K=>A.2.2 dir k (Nat.le_trans K D)⟩

/-- A publication is an actual cut label (rather than an existential
choice of the witness to the MarkSemantics disjunction). -/
structure Quiet (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop)
    (z : I→Bool) (states : Nat→X) (pub : Nat→I→Prop) (a b : Nat) : Prop where
  z_const : ∀ t i,a≤t → t≤b → ball i → R.z (states t) i=z i
  frame : ∀ t i,a≤t → t<b → ball i → ¬pub t i → Frame R (states t) (states (t+1)) i
  publish : ∀ t i,a≤t → t<b → ball i → pub t i → Publish R rho near (states t) (states (t+1)) i

def Covers (ball : I→Prop) (pub : Nat→I→Prop) (a b : Nat) : Prop :=
  ∀ i,ball i→∃ t,a≤t ∧ t<b ∧ pub t i

/-- Seed or advance a quiet service pass. The old-pair recurrence and
the frame allow arbitrary extra publications; no global reset or
generation selection is used in this deterministic kernel. -/
theorem pass (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop)
    (z : I→Bool) (states : Nat→X) (pub : Nat→I→Prop) (a b depth : Nat)
    (AB : a≤b) (D : depth≤rho)
    (S : Quiet R rho near ball z states pub a b)
    (C : Covers ball pub a b)
    (Initial : ∀ i,ball i → 0<depth → CorrectAt R rho near ball z (depth-1) (states a) i) :
    ∀ i,ball i→CorrectAt R rho near ball z depth (states b) i := by
  classical
  have go : ∀ u,a+u≤b →
      (∀ i,ball i → 0<depth → CorrectAt R rho near ball z (depth-1) (states (a+u)) i) ∧
      (∀ i,ball i → (∃ t,a≤t ∧ t<a+u ∧ pub t i) →
        CorrectAt R rho near ball z depth (states (a+u)) i) := by
    intro u
    induction u with
    | zero =>
      intro _
      simp only [Nat.add_zero]
      refine ⟨Initial,?_⟩
      rintro i _ ⟨t,A,B,_⟩
      omega
    | succ u IH =>
      intro Limit
      obtain ⟨Old,Previous⟩ := IH (by omega)
      have T : a+u<b := by omega
      have start : a≤a+u := by omega
      have Pay (i : I) (B : ball i) (H : pub (a+u) i) :
          CorrectAt R rho near ball z depth (states (a+u+1)) i := by
        have P := S.publish (a+u) i start T B H
        have Z := S.z_const (a+u) i start (by omega) B
        cases E : depth with
        | zero => exact correct_zero_of_publication _ _ _ _ _ _ _ _ Z P
        | succ k =>
          apply correct_succ_of_publication R rho near ball z k (by omega) _ _ _ Z _ P
          intro j BJ
          have O := Old j BJ (by omega)
          simpa [E] using O
      constructor
      · intro i B H
        by_cases E : pub (a+u) i
        · exact correct_weaken _ _ _ _ _ _ _ (by omega) _ _ (Pay i B E)
        · exact correct_frame _ _ _ _ _ _ _ _ _ (Old i B H) (S.frame _ _ start T B E)
      · rintro i B ⟨t,A,L,P⟩
        by_cases E : pub (a+u) i
        · exact Pay i B E
        · have L' : t<a+u := by
            by_cases H : t<a+u
            · exact H
            · 
              have F : t=a+u := by omega
              exact False.elim (E (F ▸ P))
          exact correct_frame _ _ _ _ _ _ _ _ _
            (Previous i B ⟨t,A,L',P⟩) (S.frame _ _ start T B E)
  have E : a+(b-a)=b := by omega
  obtain ⟨_,R'⟩ := go (b-a) (by omega)
  rw [E] at R'
  exact fun i B=>R' i B (C i B)

/-- An already-correct layer survives the trailing part of a quiet
segment, including any additional classified publications. -/
theorem quiet_preserves_correct
    (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop)
    (z : I→Bool) (states : Nat→X) (pub : Nat→I→Prop) (a b depth : Nat)
    (AB : a≤b) (D : depth≤rho)
    (S : Quiet R rho near ball z states pub a b)
    (A : ∀ i,ball i→CorrectAt R rho near ball z depth (states a) i) :
    ∀ i,ball i→CorrectAt R rho near ball z depth (states b) i := by
  classical
  have go : ∀ k,a+k≤b →
      ∀ i,ball i→CorrectAt R rho near ball z depth (states (a+k)) i := by
    intro k
    induction k with
    | zero => simpa using fun (_ : a≤b) => A
    | succ k ih =>
      intro Limit i H
      have Old := ih (by omega)
      by_cases P : pub (a+k) i
      · have W := S.publish (a+k) i (by omega) (by omega) H P
        have Z := S.z_const (a+k) i (by omega) (by omega) H
        cases E : depth with
        | zero => exact correct_zero_of_publication _ _ _ _ _ _ _ _ Z W
        | succ d =>
          apply correct_succ_of_publication _ _ _ _ _ d (by omega) _ _ _ Z _ W
          intro j J
          exact correct_weaken _ _ _ _ _ _ _ (by omega) _ _ (Old j J)
      · exact correct_frame _ _ _ _ _ _ _ _ _ (Old i H)
          (S.frame (a+k) i (by omega) (by omega) H P)
  have Out := go (b-a) (by omega)
  rwa [show a+(b-a)=b by omega] at Out

/-- Rebase the frozen Boolean function onto the actual quiet endpoint.
Only values on the local operand cone are used. -/
theorem correct_rebase (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop)
    (z z' : I→Bool) (A : ∀ j,ball j→z j=z' j) (depth : Nat) (x : X) (i : I)
    (B : ball i) (H : CorrectAt R rho near ball z depth x i) :
    CorrectAt R rho near ball z' depth x i := by
  refine ⟨H.1.trans (A i B),H.2.1,?_⟩
  intro dir k K P
  exact (H.2.2 dir k K P).trans (target_congr near ball z z' A dir i k P)

/-- A quiet pass first establishes captured Z and the comparison byte.
Each further pass adds one level of the true radius predicate. -/
theorem passes (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop)
    (z : I→Bool) (states : Nat→X) (pub : Nat→I→Prop) (cut : Nat→Nat)
    (AB : ∀ k,k≤rho→cut k≤cut (k+1))
    (S : ∀ k,k≤rho → Quiet R rho near ball z states pub (cut k) (cut (k+1)))
    (C : ∀ k,k≤rho → Covers ball pub (cut k) (cut (k+1))) :
    ∀ k,k≤rho → ∀ i,ball i→CorrectAt R rho near ball z k (states (cut (k+1))) i := by
  intro k
  induction k with
  | zero =>
    intro H
    exact pass R rho near ball z states pub _ _ 0 (AB _ H) H (S _ H) (C _ H)
      (fun _ _ H=>False.elim (Nat.not_lt_zero _ H))
  | succ k IH =>
    intro H
    apply pass R rho near ball z states pub _ _ (k+1) (AB _ H) H (S _ H) (C _ H)
    intro i B _
    simpa only [Nat.add_sub_cancel] using IH (by omega) i B

/-- The same quiet-pass recurrence gives the visible part of a sticky
certificate when the pulse has selected one isolated centre. -/
theorem visible_of_passes (R : Readout X I) (rho : Nat) (near : Bool→I→I) (ball : I→Prop)
    (z : I→Bool) (states : Nat→X) (pub : Nat→I→Prop) (cut : Nat→Nat)
    (AB : ∀ k,k≤rho→cut k≤cut (k+1))
    (S : ∀ k,k≤rho → Quiet R rho near ball z states pub (cut k) (cut (k+1)))
    (C : ∀ k,k≤rho → Covers ball pub (cut k) (cut (k+1))) :
    Visible R rho near ball z (states (cut (rho+1))) := by
  have F := (S rho (Nat.le_refl _)).z_const (cut (rho+1))
  have Z (i : I) (B : ball i) : R.z (states (cut (rho+1))) i=z i :=
    F i (AB rho (Nat.le_refl _)) (Nat.le_refl _) B
  have P := passes R rho near ball z states pub cut AB S C rho (Nat.le_refl _)
  refine ⟨Z,fun i B=>(P i B).1.trans (Z i B).symm,?_,fun i B=>(P i B).2.1⟩
  intro i dir k K PathK
  rw [target_congr near ball _ _ Z dir i k PathK]
  exact (P i (path_here PathK)).2.2 dir k K PathK

#print axioms pass
#print axioms quiet_preserves_correct
#print axioms correct_rebase
#print axioms passes
#print axioms visible_of_passes
end L4.ReportQuietCovers

import Leader.L4.FourLossStickyClock
import Leader.L4.ReportProtectedInterval
import Leader.L4.ReportResetRawHooks
import Leader.L4.ReportStaticSpacing
import Leader.L4.ReportRawCommitSnapshot

namespace L4.ReportStickyRawCover
open AllSizeProtocol PhysicalCustody ReportByteRows ReportResetRawHooks
open ReportProtectedInterval ReportStaticSpacing BStarH6Ordinal BStarH6WordChart

noncomputable def rootOf {n : Nat} (h : Fin n→Bool)
    (hh : ∃ q,h q=true) (i : Fin n) : Lower h :=
  ⟨back i (ordinal h hh i),(ordinal_spec h hh i).2.1⟩

theorem rootOf_header {n : Nat} (h : Fin n→Bool) (hh : ∃ q,h q=true)
    (i : Lower h) : rootOf h hh i.val = i := by
  apply Subtype.ext
  change back i.val (ordinal h hh i.val)=i.val
  rw [(ordinal_zero h hh i.val).mpr i.property,back_zero]

noncomputable def readout (d : Sheet) {s n : Nat} (h : Fin n → Bool) :
    Readout (Raw s n) (Lower h) where
  z x i := Z (params d s) (selectBytes d (x i.val))
  a x i := publicationA (params d s) (selectBytes d (x i.val))
    (publicationSelector (params d s) (selectBytes d (x i.val)))
  u x i b := min (params d s).radius
    (reportValue (params d s) (fun j => selectBytes d (x j)) i.val b)
  b x i := publicationPair (params d s) (selectBytes d (x i.val))
    (publicationSelector (params d s) (selectBytes d (x i.val)))

theorem clipped_threshold_iff (rho j v : Nat) (J : j≤rho) :
    min rho v < j ↔ v < j := by
  constructor
  · intro h
    by_cases V : v<j
    · exact V
    · exact False.elim ((Nat.not_lt_of_ge (Nat.le_min.mpr ⟨J,Nat.le_of_not_gt V⟩)) h)
  · intro h
    exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) h

def rawPaint (d : Sheet) {s n : Nat} (h : Fin n→Bool)
    (x : Raw s n) (e : Fin n) (i : Lower h) : Bool :=
  if i.val=e then paints (params d s) true 2 (selectBytes d (x i.val))
  else if i.val=rightNeighbor e then paints (params d s) true 1 (selectBytes d (x i.val))
  else false

/-- The two endpoints and every spectator use the literal old selected B.
This is the pulse half of MarkSemantics on raw bytes; it needs no lease. -/
theorem raw_pulse (d : Sheet) {s n : Nat} (h : Fin n→Bool)
    (x : Raw s n) (e : Fin n) (i : Lower h) (N : e≠rightNeighbor e)
    (mask : ∀ j,lower d (oldHeaders (rows s) (x j))=h j) :
    (readout d h).z (rawNext s x e) i =
      if rawPaint d h x e i then (readout d h).b x i==0 else (readout d h).z x i := by
  have H : lower d (oldHeaders (rows s) (x i.val))=true := (mask _).trans i.property
  by_cases L : i.val=e
  · simp only [rawPaint,if_pos L,readout]
    rw [L] at H ⊢
    cases d
    · change (oldHeaders (rows s) (x e)).h4=true at H
      have C := ReportRawCommitSnapshot.report1_side2_Z x e N
      dsimp only at C
      rw [H] at C
      change Z (ReportRawProjection.firstParams s) (rawNext s x e e).report1 =
        (if paints (ReportRawProjection.firstParams s) true 2 (x e).report1
         then publicationPair (ReportRawProjection.firstParams s) (x e).report1
           (publicationSelector (ReportRawProjection.firstParams s) (x e).report1)==0
         else Z (ReportRawProjection.firstParams s) (x e).report1)
      exact C
    · change (oldHeaders (rows s) (x e)).h5=true at H
      have C := ReportRawCommitSnapshot.report2_side2_Z x e N
      dsimp only at C
      rw [H] at C
      change Z (ReportRawProjection.secondParams s) (rawNext s x e e).report2 =
        (if paints (ReportRawProjection.secondParams s) true 2 (x e).report2
         then publicationPair (ReportRawProjection.secondParams s) (x e).report2
           (publicationSelector (ReportRawProjection.secondParams s) (x e).report2)==0
         else Z (ReportRawProjection.secondParams s) (x e).report2)
      exact C
  · by_cases R : i.val=rightNeighbor e
    · simp only [rawPaint,if_neg L,if_pos R,readout]
      rw [R] at H ⊢
      cases d
      · have P := congrArg _root_.Prod.snd (ReportRawProjection.raw_report1_pair x e N)
        dsimp only at P
        change (oldHeaders (rows s) (x (rightNeighbor e))).h4=true at H
        rw [H] at P
        change Z (ReportRawProjection.firstParams s) (rawNext s x e (rightNeighbor e)).report1 = _
        rw [P]
        exact ReportRawCommitSnapshot.join_right_Z _ _ _ _ _
      · have P := congrArg _root_.Prod.snd (ReportRawProjection.raw_report2_pair x e N)
        dsimp only at P
        change (oldHeaders (rows s) (x (rightNeighbor e))).h5=true at H
        rw [H] at P
        change Z (ReportRawProjection.secondParams s) (rawNext s x e (rightNeighbor e)).report2 = _
        rw [P]
        exact ReportRawCommitSnapshot.join_right_Z _ _ _ _ _
    · simp only [rawPaint,if_neg L,if_neg R,Bool.false_eq_true,if_false,readout,
        ReportRawProjection.raw_spectator x e i.val L R]

def physicalSticky {n : Nat} {h : Fin n→Bool} {X : Type}
    (hh : ∃ q,h q=true) (sticky : Lower h→X→Prop) (i : Fin n) (x : X) : Prop :=
  sticky (rootOf h hh i) x

theorem physical_cover_iff {n : Nat} {h : Fin n→Bool} {X : Type}
    (hh : ∃ q,h q=true) (E : X→Prop) (sticky : Lower h→X→Prop) (x : X) :
    FourLossStickyClock.Cover E (physicalSticky hh sticky) x ↔
      E x ∧ ∀ i,sticky i x := by
  constructor
  · intro H
    refine ⟨H.1,?_⟩
    intro i
    have I := H.2 i.val
    rw [physicalSticky,rootOf_header] at I
    exact I
  · exact fun H=>⟨H.1,fun i=>H.2 (rootOf h hh i)⟩

def upper (d : Sheet) {s n : Nat} (x : Raw s n) : Fin n→Bool :=
  match d with
  | .first => h5 x
  | .second => oldH6 (rows s) x

theorem upper_eq (d : Sheet) {s n : Nat} (x : Raw s n) (i : Fin n) :
    upper d x i=(lower d (oldHeaders (rows s) (x i)) &&
      Z (params d s) (selectBytes d (x i))) := by
  cases d
  · exact report1_mask x i
  · exact report2_mask x i

theorem upper_of_same_lower_Z (d : Sheet) {s n : Nat} (h : Fin n→Bool)
    (x y : Raw s n)
    (hx : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (hy : ∀ i,lower d (oldHeaders (rows s) (y i))=h i)
    (z : ∀ i : Lower h,(readout d h).z x i=(readout d h).z y i) :
    upper d x=upper d y := by
  funext i
  rw [upper_eq,upper_eq,hx i,hy i]
  cases B : h i
  · simp
  · have Z0 := z ⟨i,B⟩
    exact congrArg (true && ·) Z0

/-- Specializes the site's cover to actual selected-word owners and
runs the existing protected-interval proof on the original marks.
The selected-bank branch of the joined row is an explicit input. -/
theorem covering_raw_run (d : Sheet) {s n : Nat} (h : Fin n→Bool)
    (hh : ∃ q,h q=true)
    (neighbor : Bool→Lower h→Lower h) (ball : Lower h→Lower h→Prop)
    (centerMask : Lower h→Lower h→Bool)
    (geo : ∀ i,BallGeometry (params d s).radius neighbor (ball i) i (centerMask i))
    (E : Raw s n→Prop) (paint : Raw s n→Fin n→Lower h→Bool)
    (closed : ∀ x e,E x→E (rawNext s x e))
    (mask : ∀ x,E x→∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (sem : ∀ x e i,E x→MarkSemantics (readout d h) (params d s).radius
      neighbor (ball i) (paint x e) x (rawNext s x e))
    (x : Raw s n) (w : List (Fin n))
    (C : FourLossStickyClock.Cover E
      (physicalSticky hh (Sticky (readout d h) (params d s).radius neighbor ball centerMask)) x) :
    let y := w.foldl (rawNext s) x
    FourLossStickyClock.Cover E
      (physicalSticky hh (Sticky (readout d h) (params d s).radius neighbor ball centerMask)) y ∧
      upper d y=upper d x := by
  have I := (physical_cover_iff hh _ _ _).mp C
  have T := covering_run (readout d h) (params d s).radius neighbor ball centerMask
    geo (rawNext s) E paint closed sem x w I.1 I.2
  exact ⟨(physical_cover_iff hh _ _ _).mpr ⟨T.1,T.2.1⟩,
    upper_of_same_lower_Z d h _ _ (mask _ T.1) (mask _ I.1) T.2.2⟩

end L4.ReportStickyRawCover

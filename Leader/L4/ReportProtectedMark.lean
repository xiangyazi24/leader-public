import Leader.L4.ReportRootBall
import Leader.L4.ReportProtectedAB
import Leader.L4.ReportProtectedWords
import Leader.L4.ReportProtectedRebase
import Leader.L4.ReportStickyRawCover
import Leader.L4.ReportFastClassifiedCustody

namespace L4.ReportProtectedMark
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportRawProjection ReportGenerationAncestry ReportLeaseStep
open ReportReaderSelectorLease ReportLeaseGrants ReportGrantTimeline ReportOwnerIssueControl
open ReportCurrentCustodyCut ReportLeaseOwner ReportGoodEightCut ReportGoodEightBank
open ReportPrelaunchClock ReportOwnerAcquireReturn ReportAcquireAllCaptures ReportSnapshotLease
open ReportProtectedAB ReportProtectedWords ReportProtectedRebase ReportStaticSpacing
open ReportItemNineTrace ReportItemNineActualPublication ReportIngressOwnership
open ReportProtectedInterval ReportStickyRawCover
open ReportOwnerAcquireProvenance (BeforeConsume NoConsume)

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem side_lanes (_hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) :
    let C := charter G r
    C.route.port 0=0 ∧ C.a+C.b<C.L ∧ h (out C (C.a+C.b))=true ∧
      C.route.port (C.a+C.b)=2 ∧ out C (C.a+C.b)=nextAt C.root (C.a+C.b) := by
  let a := Classical.choose (G.gaps r.val r.property)
  have A := Classical.choose_spec (G.gaps r.val r.property)
  let b := Classical.choose (G.gaps (nextAt r.val a) A.2.2.atEnd)
  have B := Classical.choose_spec (G.gaps (nextAt r.val a) A.2.2.atEnd)
  let c := Classical.choose (G.gaps (nextAt (nextAt r.val a) b) B.2.2.atEnd)
  have D := Classical.choose_spec (G.gaps (nextAt (nextAt r.val a) b) B.2.2.atEnd)
  have PA : 0<a := A.2.2.positive
  have PC := D.2.2.positive
  refine ⟨?_,?_,?_,?_,rfl⟩
  · change lane a b 0=0
    simp [lane,PA]
  · change a+b<a+b+c
    omega
  · change h (nextAt r.val (a+b))=true
    rw [nextAt_add]
    exact B.2.2.atEnd
  · change lane a b (a+b)=2
    simp [lane,show ¬ a+b<a by omega]

theorem flags_now (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Dgt : 0<(params d s).digits) (r : Owner h)
    (issue : Raw s n) (Cut : FirstCut d hh Q G issue)
    (I : LegalIssue d (charter G r) issue)
    (P : readPC d (charter G r) issue=(1,acqOp (params d s)))
    (w : List (Fin n))
    (T : BeforeConsume d (charter G r) (rawNext s issue (door (charter G r))) w)
    (Tag : (tok d (charter G r) (rawRun (rawNext s issue (door (charter G r))) w) 0).tag=3)
    (ND : (tok d (charter G r) (rawRun (rawNext s issue (door (charter G r))) w) 0).outcome≠1)
    (v : List (Fin n))
    (NR : let C := charter G r
      NoRestartTape d C (rawNext s (rawRun (rawNext s issue (door C)) w) (door C)) v) :
    let C := charter G r
    let b := rawNext s (rawRun (rawNext s issue (door C)) w) (door C)
    let K := snapshotInputs d C b
    K.leftRoot=selectedA d (rawRun b v) C.root ∧
      K.rightRoot=selectedA d (rawRun b v) (nextAt C.root (C.a+C.b)) := by
  dsimp only
  let C := charter G r
  obtain ⟨Port0,Len,Head,Port2,Pos⟩ := side_lanes hh G r
  have Left := captured_A_now d C hh G F N issue Cut.1.1.1 I P Cut.1.2 Dgt w T Tag ND v NR
    0 C.positive C.rootHeader (Or.inl Port0)
  have Right := captured_A_now d C hh G F N issue Cut.1.1.1 I P Cut.1.2 Dgt w T Tag ND v NR
    (C.a+C.b) Len Head (Or.inr Port2)
  rw [Port0] at Left
  rw [Port2,Pos] at Right
  let b := rawNext s (rawRun (rawNext s issue (door C)) w) (door C)
  let K := snapshotInputs d C b
  have HL : K.heads / 4 % 2=(selectedA d (rawRun b v) C.root).toNat := Left
  have HR : K.heads % 2=(selectedA d (rawRun b v) (nextAt C.root (C.a+C.b))).toNat := by
    change K.heads/1%2=_ at Right
    simpa only [Nat.div_one] using Right
  constructor
  · change ((K.heads >>> 2)%2==1)=_
    rw [Nat.shiftRight_eq_div_pow]
    change (K.heads/4%2==1)=_
    rw [HL]
    cases selectedA d (rawRun b v) C.root <;> rfl
  · change ((K.heads >>> 0)%2==1)=_
    change (K.heads%2==1)=_
    rw [HR]
    cases selectedA d (rawRun b v) (nextAt C.root (C.a+C.b)) <;> rfl

theorem held_sides_now (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Dgt : 0<(params d s).digits) (r : Owner h)
    (issue : Raw s n) (Cut : FirstCut d hh Q G issue)
    (I : LegalIssue d (charter G r) issue)
    (P : readPC d (charter G r) issue=(1,acqOp (params d s)))
    (w : List (Fin n))
    (T : BeforeConsume d (charter G r) (rawNext s issue (door (charter G r))) w)
    (Tag : (tok d (charter G r) (rawRun (rawNext s issue (door (charter G r))) w) 0).tag=3)
    (ND : (tok d (charter G r) (rawRun (rawNext s issue (door (charter G r))) w) 0).outcome≠1)
    (v : List (Fin n))
    (NR : let C := charter G r
      NoRestartTape d C (rawNext s (rawRun (rawNext s issue (door C)) w) (door C)) v) :
    let C := charter G r
    let b := rawNext s (rawRun (rawNext s issue (door C)) w) (door C)
    FirstCut d hh Q G b ∧ HeldAlong d C.root 0 b v ∧
      HeldAlong d (nextAt C.root (C.a+C.b)) 2 b v := by
  dsimp only
  let C := charter G r
  obtain ⟨Port0,Len,Head,Port2,Pos⟩ := side_lanes hh G r
  have A := all_captures_after_consume d C hh G F N issue Cut.1.1.1 I P Cut.1.2 Dgt w T Tag ND v NR
  have L := (A.2.2.2 0 C.positive C.rootHeader).2
  have R := (A.2.2.2 (C.a+C.b) Len Head).2
  rw [Port0] at L
  rw [Port2,Pos] at R
  have B0 := first_cut_closed d N hh G F Dgt issue (door C) Cut
  have B1 := first_cut_run d N hh G F Dgt _ B0 w
  have B := first_cut_closed d N hh G F Dgt _ (door C) B1
  exact ⟨B,L,R⟩

theorem publication_now (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (r : Owner h) (x : Raw s n) (A : CurrentCustodyCut d hh Q G x)
    (Left : (params d s).digits≤(charter G r).a)
    (Mid : (params d s).digits≤(charter G r).b)
    (Right : (params d s).digits≤(charter G r).L-((charter G r).a+(charter G r).b))
    (e : Fin n) (atCentre : rightNeighbor e=centre (charter G r))
    (Accept : oldCommitAt d x e) :
    let C := charter G r
    let c := centre C
    let l := C.root
    let r' := nextAt C.root (C.a+C.b)
    let p := params d s
    let y := rawNext s x e
    let src := fun i=>selectBytes d (x i)
    let dst := fun i=>selectBytes d (y i)
    selectedA d y c=Z p (src c) ∧
    reportValue p dst c true=ReportDigitArithmetic.updateDist p.radius (selectedA d x l)
      (reportValue p src l true) ∧
    reportValue p dst c false=ReportDigitArithmetic.updateDist p.radius (selectedA d x r')
      (reportValue p src r' false) ∧
    selectedB d y c=thresholds p.radius (reportValue p dst c true) (reportValue p dst c false) := by
  let C := charter G r
  let p := params d s
  have X : Cached d hh Q x := A.1.1.2.1.1.1.1
  have Mask := (cached_fibre d N hh Q F).mask x X
  have Guard := Accept
  unfold oldCommitAt at Guard
  have HC : h (centre (charter G r))=true := (canonical_centre G r).2.2.1
  rw [Mask e,atCentre,Mask _,HC] at Guard
  obtain ⟨issue,w,v,Cut,I,P,T,Tag,ND,W,NR,_,_,_,VL,VR,Pair,Head⟩ :=
    publication_at_current_cut d N Spos hh G F r x A Left Mid Right e atCentre Guard
  let b := rawNext s (rawRun (rawNext s issue (door C)) w) (door C)
  have Dgt := ReportPrelaunchDoorProducer.digits_positive d Spos
  obtain ⟨B,HL,HR⟩ := held_sides_now d N hh G F Dgt r issue Cut I P w T Tag ND v NR
  obtain ⟨NL,NR'⟩ := snapshot_numbers_now d N hh G F Dgt
    (ReportWriteRailSupplier.rail_supplier d N hh G F Dgt) r b B v Left Right HL HR
  obtain ⟨FL,FR⟩ := flags_now d N hh G F Dgt r issue Cut I P w T Tag ND v NR
  change x=rawRun b v at W
  rw [←W] at NL NR' FL FR
  dsimp only
  refine ⟨Head,?_,?_,Pair⟩
  · change _=ReportDigitArithmetic.updateDist p.radius (selectedA d x C.root)
      (reportValue p (fun i=>selectBytes d (x i)) C.root true)
    rw [NL,←FL]
    exact VL
  · change _=ReportDigitArithmetic.updateDist p.radius
      (selectedA d x (nextAt C.root (C.a+C.b)))
      (reportValue p (fun i=>selectBytes d (x i)) (nextAt C.root (C.a+C.b)) false)
    rw [NR',←FR]
    exact VR

private theorem update_clip (r v : Nat) (a : Bool) :
    ReportDigitArithmetic.updateDist r a v=updateDistance r a (min r v) := by
  cases a with
  | true => rfl
  | false =>
    unfold ReportDigitArithmetic.updateDist updateDistance
    simp only [Bool.false_eq_true,if_false]
    by_cases H : v≤r
    · rw [Nat.min_eq_right H]
    · rw [Nat.min_eq_left (by omega : r≤v), Nat.min_eq_left (by omega : r≤v+1),
        Nat.min_eq_left (by omega : r≤r+1)]

/-- Only static chart geometry: three consecutive lower headers agree
with the left/centre/right order of the lower-ring neighbor function. -/
def NeighborLaw (G : GapInput h) (neighbor : Bool→Lower h→Lower h) : Prop :=
  ∀ (r : Owner h) (i : Lower h), centre (charter G r)=i.val →
    (neighbor true i).val=(charter G r).root ∧
    (neighbor false i).val=nextAt (charter G r).root ((charter G r).a+(charter G r).b)

theorem raw_mark_semantics_of_geometry (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Width : ∀ r : Owner h, let C := charter G r
      (params d s).digits≤C.a ∧ (params d s).digits≤C.b ∧
      (params d s).digits≤C.L-(C.a+C.b))
    (Fits : ∀ i : Lower h, ∃ len, Gap h i.val len ∧ (params d s).digits≤len)
    (neighbor : Bool→Lower h→Lower h) (Geom : NeighborLaw G neighbor)
    (x : Raw s n) (A : CurrentCustodyCut d hh Q G x) (e : Fin n)
    (ball : Lower h→Prop) :
    MarkSemantics (readout d h) (params d s).radius neighbor ball (rawPaint d h x e)
      x (rawNext s x e) := by
  let p := params d s
  have X : Cached d hh Q x := A.1.1.2.1.1.1.1
  have Mask := (cached_fibre d N hh Q F).mask x X
  have Safe := A.1.1.2.2
  refine ⟨fun i _=> raw_pulse d h x e i (edge_sep N e) Mask,?_⟩
  intro i _
  by_cases K : i.val=rightNeighbor e ∧ oldCommitAt d x e
  · right
    obtain ⟨r,Eq⟩ := ReportFastClassifiedCustody.centre_covers_lower_header hh G e (K.1 ▸ i.property)
    obtain ⟨L,M,R⟩ := Width r
    have Centre : centre (charter G r)=i.val := Eq.symm.trans K.1.symm
    obtain ⟨HL,HR⟩ := Geom r i Centre
    have Pub := publication_now d N Spos hh G F r x A L M R e Eq K.2
    dsimp only at Pub
    rw [Centre,←HR,←HL] at Pub
    refine ⟨Pub.1,?_,?_⟩
    · intro dir
      change min p.radius (reportValue p (fun j=>selectBytes d (rawNext s x e j)) i.val dir)=
        updateDistance p.radius (selectedA d x (neighbor dir i).val)
          (min p.radius (reportValue p (fun j=>selectBytes d (x j)) (neighbor dir i).val dir))
      cases dir
      · rw [Pub.2.2.1,update_clip]
        apply Nat.min_eq_right
        unfold updateDistance
        split
        · omega
        · exact Nat.min_le_left _ _
      · rw [Pub.2.1,update_clip]
        apply Nat.min_eq_right
        unfold updateDistance
        split
        · omega
        · exact Nat.min_le_left _ _
    · change selectedB d (rawNext s x e) i.val=thresholds p.radius
        (min p.radius (reportValue p (fun j=>selectBytes d (rawNext s x e j)) i.val true))
        (min p.radius (reportValue p (fun j=>selectBytes d (rawNext s x e j)) i.val false))
      rw [Pub.2.2.2]
      unfold thresholds
      simp only [clipped_threshold_iff _ _ _ (Nat.le_refl _)]
      rfl
  · left
    have AB := raw_ab_without_ingress d N x e i.val K
    obtain ⟨len,Gap,Fits'⟩ := Fits i
    exact ⟨AB.1,AB.2,fun dir=>congrArg (min p.radius)
      (value_frame_without_ingress d N hh G x e i.val Mask i.property Gap Fits' Safe K dir)⟩

open ShortHopSpacing ReportRootBall SelectedRingGeometry BStarH6Ordinal WidthOrdinalSpan

theorem concrete_neighbors {L U : Nat} (Bounds : GapBounds h L U)
    (hh : ∃ i,h i=true) (G : GapInput h) :
    NeighborLaw G (rootNeighbor Bounds hh) := by
  intro r i A
  let a := Classical.choose (G.gaps r.val r.property)
  have LA := Classical.choose_spec (G.gaps r.val r.property)
  let b := Classical.choose (G.gaps (nextAt r.val a) LA.2.2.atEnd)
  have LB := Classical.choose_spec (G.gaps (nextAt r.val a) LA.2.2.atEnd)
  let r0 : Lower h := ⟨r.val,r.property⟩
  have W0 : successorWidth Bounds r.val=a :=
    gap_unique (successorWidth_spec Bounds r.val r.property).2.2 LA.2.2
  have Mid : successor Bounds r0=i := by
    apply Subtype.ext
    change nextAt r.val (successorWidth Bounds r.val)=i.val
    rw [W0]
    exact A
  have L : predecessor hh i=r0 := by
    rw [←Mid,predecessor_successor]
  have I : i.val=nextAt r.val a := A.symm
  have W1 : successorWidth Bounds i.val=b := by
    rw [I]
    exact gap_unique (successorWidth_spec Bounds _ LA.2.2.atEnd).2.2 LB.2.2
  constructor
  · exact congrArg Subtype.val L
  · change nextAt i.val (successorWidth Bounds i.val)=nextAt r.val (a+b)
    rw [W1,I,nextAt_add]

theorem width_supplies_gap (d : Sheet) (G : GapInput h)
    (Width : ∀ r : Owner h, let C := charter G r
      (params d s).digits≤C.a ∧ (params d s).digits≤C.b ∧
      (params d s).digits≤C.L-(C.a+C.b)) :
    ∀ i : Lower h,∃ len, Gap h i.val len ∧ (params d s).digits≤len := by
  intro i
  exact ⟨_,(Classical.choose_spec (G.gaps i.val i.property)).2.2,(Width i).1⟩

theorem raw_mark_semantics (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Width : ∀ r : Owner h, let C := charter G r
      (params d s).digits≤C.a ∧ (params d s).digits≤C.b ∧
      (params d s).digits≤C.L-(C.a+C.b))
    {L U : Nat} (Bounds : GapBounds h L U)
    (x : Raw s n) (A : CurrentCustodyCut d hh Q G x) (e : Fin n)
    (ball : Lower h→Prop) :
    MarkSemantics (readout d h) (params d s).radius (rootNeighbor Bounds hh)
      ball (rawPaint d h x e) x (rawNext s x e) :=
  raw_mark_semantics_of_geometry d N Spos hh G F Width (width_supplies_gap d G Width)
    _ (concrete_neighbors Bounds hh G) x A e ball

/-- After protection is reached, it is closed on the original raw
schedule and the upper-header mask is permanently unchanged. -/
theorem protected_cover_run (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Width : ∀ r : Owner h, let C := charter G r
      (params d s).digits≤C.a ∧ (params d s).digits≤C.b ∧
      (params d s).digits≤C.L-(C.a+C.b))
    {L U : Nat} (Bounds : GapBounds h L U) (Lo : 1≤L)
    (Room : (params d s).radius*U<n)
    (x : Raw s n) (w : List (Fin n))
    (A : FourLossStickyClock.Cover (CurrentCustodyCut d hh Q G)
      (physicalSticky hh (Sticky (readout d h) (params d s).radius
        (rootNeighbor Bounds hh) (ball Bounds hh (params d s).radius) centerMask)) x) :
    let y := w.foldl (rawNext s) x
    FourLossStickyClock.Cover (CurrentCustodyCut d hh Q G)
      (physicalSticky hh (Sticky (readout d h) (params d s).radius
        (rootNeighbor Bounds hh) (ball Bounds hh (params d s).radius) centerMask)) y ∧
      upper d y=upper d x := by
  have Dgt := ReportPrelaunchDoorProducer.digits_positive d Spos
  exact covering_raw_run d h hh (rootNeighbor Bounds hh) (ball Bounds hh (params d s).radius)
    centerMask (physical_ball_geometry Bounds hh Lo Room)
    (CurrentCustodyCut d hh Q G) (rawPaint d h)
    (fun y e H=>current_custody_closed d N hh G F Dgt y e H)
    (fun y H=> (cached_fibre d N hh Q F).mask y H.1.1.2.1.1.1.1)
    (fun y e i H=>raw_mark_semantics d N Spos hh G F Width Bounds y H e
      (ball Bounds hh (params d s).radius i)) x w A

end L4.ReportProtectedMark

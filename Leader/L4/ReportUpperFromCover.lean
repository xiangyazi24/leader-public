import Leader.L4.ReportCoverHandoff
import Leader.L4.ReportProtectedMark

namespace L4.ReportUpperFromCover
open AllSizeProtocol PhysicalCustody ReportByteRows ReportResetRawHooks ReportProtectedInterval
open ReportStickyRawCover ReportStaticSpacing ReportRootBall ReportCoverMask ReportCoverHandoff
open ReportProtectedMark ReportCurrentCustodyCut ReportPrelaunchK1Geometry ReportResetBarrier
open ReportOwnerResetDrain BStarH6Ordinal BStarH6WordChart
open ShortHopSpacing ReportRadiusSpacing ReportLeaseOwner

variable {s n L U : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- Sticky coverage itself already implies the literal upper mask's
nonemptiness and next-selected gap bounds. No global ReportCut or
claim about other directions is imposed. -/
theorem upper_at_cover (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (C : GapInput h) (F : Fibre (h:=h) d Q)
    (bounds : GapBounds h L U) (Lo : 1≤L) (Room : (params d s).radius*U<n)
    (x : Raw s n) (A : CoverAt d bounds hh (CurrentCustodyCut d hh Q C) x) :
    let rho := (params d s).radius
    (∃ i,upper d x i=true) ∧
      HopBounds (successorWidth bounds) (upper d x) (rho+1) (2*rho+1) ∧
      GapBounds (upper d x) (L*(rho+1)) (U*(2*rho+1)) := by
  let r := (params d s).radius
  have Y : CurrentCustodyCut d hh Q C x := A.1
  have X : Cached d hh Q x := Y.1.1.2.1.1.1.1
  have M := (cached_fibre d N hh Q F).mask x X
  have Cover := ((physical_cover_iff hh _ _ _).mp A).2
  obtain ⟨Sep,Dom⟩ := sep_dom_of_cover bounds hh Lo Room (readout d h) x Cover
  have Eq (i : Fin n) : upper d x i = (h i && Z (params d s) (selectBytes d (x i))) :=
    (upper_eq d x i).trans (by rw [M i])
  exact hop_bounds_of_selection bounds hh _ Sep Dom Eq (fun _=>rfl)

/-- Every exact raw continuation preserves the same upper mask and
the physical/hop spacing certified at the original cover. -/
theorem upper_spacing_after_cover (d : Sheet) (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (C : GapInput h) (F : Fibre (h:=h) d Q)
    (Width : ∀ r : Owner h, let K := charter C r
      (params d s).digits≤K.a ∧ (params d s).digits≤K.b ∧
      (params d s).digits≤K.L-(K.a+K.b))
    (bounds : GapBounds h L U) (Lo : 1≤L) (Room : (params d s).radius*U<n)
    (x : Raw s n) (A : CoverAt d bounds hh (CurrentCustodyCut d hh Q C) x)
    (w : List (Fin n)) :
    let rho := (params d s).radius
    let y := w.foldl (rawNext s) x
    CoverAt d bounds hh (CurrentCustodyCut d hh Q C) y ∧
      upper d y=upper d x ∧ (∃ i,upper d y i=true) ∧
      HopBounds (successorWidth bounds) (upper d y) (rho+1) (2*rho+1) ∧
      GapBounds (upper d y) (L*(rho+1)) (U*(2*rho+1)) := by
  have ⟨R,E⟩ := protected_cover_run d N Spos hh C F Width bounds Lo Room x w A
  exact ⟨R,E,upper_at_cover d N hh C F bounds Lo Room _ R⟩


theorem h5_at_report1_cover (N : 1<n) (hh : ∃ i,h i=true)
    (C : GapInput h) (F : Fibre (h:=h) .first Q)
    (bounds : GapBounds h L U) (Lo : 1≤L) (Room : s*U<n)
    (x : Raw s n) (A : CoverAt .first bounds hh (CurrentCustodyCut .first hh Q C) x) :
    (∃ i,h5 x i=true) ∧ HopBounds (successorWidth bounds) (h5 x) (s+1) (2*s+1) ∧
      GapBounds (h5 x) (L*(s+1)) (U*(2*s+1)) :=
  upper_at_cover .first N hh C F bounds Lo Room x A

theorem h6_at_report2_cover (N : 1<n) (hh : ∃ i,h i=true)
    (C : GapInput h) (F : Fibre (h:=h) .second Q)
    (bounds : GapBounds h L U) (Lo : 1≤L) (Room : radiusTwo s*U<n)
    (x : Raw s n) (A : CoverAt .second bounds hh (CurrentCustodyCut .second hh Q C) x) :
    let rho := radiusTwo s
    (∃ i,oldH6 (rows s) x i=true) ∧
      HopBounds (successorWidth bounds) (oldH6 (rows s) x) (rho+1) (2*rho+1) ∧
      GapBounds (oldH6 (rows s) x) (L*(rho+1)) (U*(2*rho+1)) :=
  upper_at_cover .second N hh C F bounds Lo Room x A

#print axioms h5_at_report1_cover
#print axioms h6_at_report2_cover
#print axioms upper_at_cover
#print axioms upper_spacing_after_cover
end L4.ReportUpperFromCover

import Leader.L4.ReportUpperFromCover
import Leader.L4.WidthProductionEntrance

namespace L4.ReportWidthHandoff
open AllSizeProtocol PhysicalCustody ShortResetChart BStarH6WordChart
open ShortHopSpacing ReportStaticSpacing ReportByteRows ReportResetRawHooks
open ReportOwnerResetDrain ReportResetBarrier ReportPrelaunchK1Geometry ReportLeaseOwner
open ReportCoverHandoff ReportUpperFromCover ReportCurrentCustodyCut ReportStickyRawCover
open WidthPackedBridge WidthFreshForward WidthProductionEntrance

variable {s n : Nat} {h h4fixed : Fin n→Bool} {Q Q₄ : Raw s n→Prop}

theorem certified_spacing_of_report2_cover (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) .second Q)
    (Bounds : GapBounds h (16*(s+1)) (81*(2*s+1)))
    (Room : radiusTwo s*(81*(2*s+1))<n)
    (x : Raw s n) (A : CoverAt .second Bounds hh (CurrentCustodyCut .second hh Q G) x) :
    (∃ i,oldH6 (rows s) x i=true) ∧ CertifiedSpacing x := by
  have H := h6_at_report2_cover N hh G F Bounds (by omega) Room x A
  exact ⟨H.1,H.2.2⟩

/-- WIDTH starts cold. Only report2 coverage and its exact old H6 mask
are frozen; WIDTH private clients, flags and tokens are unconditioned. -/
def widthLower_at_report2_cover (N : 1<n) (Spos : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) .second Q)
    (Width : ∀ r : Owner h, let K := charter G r
      (params .second s).digits≤K.a ∧ (params .second s).digits≤K.b ∧
      (params .second s).digits≤K.L-(K.a+K.b))
    (Bounds : GapBounds h (16*(s+1)) (81*(2*s+1)))
    (Room : radiusTwo s*(81*(2*s+1))<n)
    (x : Raw s n) (A : CoverAt .second Bounds hh (CurrentCustodyCut .second hh Q G) x) :
    WidthLower s n where
  Q y := CoverAt .second Bounds hh (CurrentCustodyCut .second hh Q G) y ∧
    oldH6 (rows s) y=oldH6 (rows s) x
  closed y e B := by
    have C := upper_spacing_after_cover .second N Spos hh G F Width Bounds
      (by omega) Room y B.1 [e]
    exact ⟨C.1,C.2.1.trans B.2⟩
  h := oldH6 (rows s) x
  frozen _ B i := congrFun B.2 i
  hh := (certified_spacing_of_report2_cover N hh G F Bounds Room x A).1
  spacing y B := (certified_spacing_of_report2_cover N hh G F Bounds Room y B.1).2

theorem packed_after_report2_cover (N : 1<n) (hs : 6≤s) (advice : s=ell (ell n))
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) .second Q)
    (Width : ∀ r : Owner h, let K := charter G r
      (params .second s).digits≤K.a ∧ (params .second s).digits≤K.b ∧
      (params .second s).digits≤K.L-(K.a+K.b))
    (Bounds : GapBounds h (16*(s+1)) (81*(2*s+1)))
    (x : Raw s n) (A : CoverAt .second Bounds hh (CurrentCustodyCut .second hh Q G) x) :
    IIDExpectedHittingTimeAtMost (rawNext s) (fun z=>Nonempty (PackedFiber z))
      x ((s+5132)*n^2) := by
  have Room : radiusTwo s*(81*(2*s+1))<n := (production_room hs advice .second).1
  let P := widthLower_at_report2_cover N (by omega) hh G F Width Bounds Room x A
  exact packed_from_certified_h6 P hs advice N x ⟨A,rfl⟩

/-- Recover the report2 lower physical bounds from report1's actual
Sticky cut on the same run. The fixed report2 header mask is identified
through its current cached fibre, not presumed equal to a proof-level list. -/
theorem report2_bounds_after_report1_cover (N : 1<n) (Spos : 0<s)
    (hh4 : ∃ i,h4fixed i=true) (G4 : GapInput h4fixed)
    (F4 : Fibre (h:=h4fixed) .first Q₄)
    (Width4 : ∀ r : Owner h4fixed, let K := charter G4 r
      (params .first s).digits≤K.a ∧ (params .first s).digits≤K.b ∧
      (params .first s).digits≤K.L-(K.a+K.b))
    (Bounds4 : GapBounds h4fixed 16 81) (Room4 : s*81<n)
    (x : Raw s n) (A : CoverAt .first Bounds4 hh4 (CurrentCustodyCut .first hh4 Q₄ G4) x)
    (w : List (Fin n))
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) .second Q)
    (Cached2 : Cached .second hh Q (w.foldl (rawNext s) x)) :
    GapBounds h (16*(s+1)) (81*(2*s+1)) := by
  let y := w.foldl (rawNext s) x
  have B := upper_spacing_after_cover .first N Spos hh4 G4 F4 Width4 Bounds4
    (by decide) Room4 x A w
  have Id : h5 y=h := funext ((cached_fibre .second N hh Q F).mask y Cached2)
  have H : GapBounds (h5 y) (16*(s+1)) (81*(2*s+1)) := B.2.2.2.2
  rwa [Id] at H

/-- Both observed report covers lie on one raw continuation. The two
radii and the immutable H5-to-H6 mask chain supply the exact certified
spacing consumed by the unmodified WIDTH entrance. -/
theorem packed_after_both_report_covers (N : 1<n) (hs : 6≤s) (advice : s=ell (ell n))
    (hh4 : ∃ i,h4fixed i=true) (G4 : GapInput h4fixed)
    (F4 : Fibre (h:=h4fixed) .first Q₄)
    (Width4 : ∀ r : Owner h4fixed, let K := charter G4 r
      (params .first s).digits≤K.a ∧ (params .first s).digits≤K.b ∧
      (params .first s).digits≤K.L-(K.a+K.b))
    (Bounds4 : GapBounds h4fixed 16 81)
    (x : Raw s n) (A : CoverAt .first Bounds4 hh4 (CurrentCustodyCut .first hh4 Q₄ G4) x)
    (w : List (Fin n))
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) .second Q)
    (Width : ∀ r : Owner h, let K := charter G r
      (params .second s).digits≤K.a ∧ (params .second s).digits≤K.b ∧
      (params .second s).digits≤K.L-(K.a+K.b))
    (B : ∃ bounds : GapBounds h (16*(s+1)) (81*(2*s+1)),
      CoverAt .second bounds hh (CurrentCustodyCut .second hh Q G)
        (w.foldl (rawNext s) x)) :
    IIDExpectedHittingTimeAtMost (rawNext s) (fun z=>Nonempty (PackedFiber z))
      (w.foldl (rawNext s) x) ((s+5132)*n^2) := by
  let y := w.foldl (rawNext s) x
  obtain ⟨B0,C0⟩ := B
  have X : Cached .second hh Q y := C0.1.1.1.2.1.1.1.1
  have Room : s*81<n := (production_room hs advice .first).1
  have B1 := report2_bounds_after_report1_cover N (by omega) hh4 G4 F4 Width4 Bounds4
    Room x A w hh F X
  have Eq : B0=B1 := Subsingleton.elim _ _
  rw [Eq] at C0
  exact packed_after_report2_cover N hs advice hh G F Width B1 y C0

end L4.ReportWidthHandoff

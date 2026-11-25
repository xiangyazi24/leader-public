import Leader.L4.ReportServiceMesh
import Leader.L4.ReportFirstRawEntrance
import Leader.L4.ReportUpperFromCover
import Leader.L4.ReportFastDispatchActual
import Leader.L4.ReportFastProductionRoom

namespace L4.ReportStageInputs
open AllSizeProtocol PhysicalCustody ShortMIS3Entrance
open ReportFirstRawEntrance ReportOwnerResetDrain ShortHopSpacing
open ReportPrelaunchK1Geometry ReportLeaseOwner ReportFastFiveGeometry
open ReportResetRawHooks ReportStaticSpacing ReportFastDispatch ReportFastRawEvent
open ReportFastProductionRoom ReportCoverHandoff ReportCurrentCustodyCut
variable {s n : Nat}

structure Inputs (d : Sheet) (h : Fin n→Bool) (Q : Raw s n→Prop) where
  N : 1<n
  hh : ∃ i,h i=true
  G : GapInput h
  F : Fibre (h:=h) d Q
  Lo : ∀ r : Owner h,minWidth d s≤gapLen G r
  Hi : G.B≤maxWidth d s
  Bounds : GapBounds h (minWidth d s) (maxWidth d s)

def inputs (d : Sheet) (advice : s=ell (ell n)) (S : 6≤s)
    (h : Fin n→Bool) (Q : Raw s n→Prop) (hh : ∃ i,h i=true)
    (F : Fibre (h:=h) d Q) (Bounds : GapBounds h (minWidth d s) (maxWidth d s)) :
    Inputs d h Q := by
  have W : 4*maxWidth d s<n := production_five_room d advice S (Nat.le_refl _)
  have W0 : 3≤maxWidth d s := by cases d <;> simp [maxWidth] <;> omega
  have WL : 2<minWidth d s := by cases d <;> simp [minWidth] <;> omega
  let G : GapInput h := ⟨maxWidth d s,by omega,fun r R=>by
    obtain ⟨k,L,U,E⟩ := Bounds r R
    exact ⟨k,by omega,U,E⟩⟩
  refine ⟨by omega,hh,G,F,?_,Nat.le_refl _,Bounds⟩
  intro r
  obtain ⟨k,L,_,E⟩ := Bounds r.val r.property
  rw [WidthOrdinalSpan.gap_unique (gapLen_spec G r).2.2 E]
  exact L

def firstInputs (advice : s=ell (ell n)) (S : 6≤s)
    (N : 189<n) (x : Raw s n) (H : PermanentH4 N x) :
    Inputs .first (h4 x) (H4Fibre N x) :=
  inputs .first advice S _ _ (permanent_h4_nonempty N x H)
    (report1Fibre N x) (permanent_h4_gaps N x H)

def frozenH5 (R : Raw s n→Prop) (x : Raw s n) (y : Raw s n) : Prop :=
  R y ∧ h5 y=h5 x

theorem frozen_h5_fibre (R : Raw s n→Prop) (x : Raw s n)
    (stay : ∀ y e,R y→R (rawNext s y e))
    (freeze : ∀ y e,R y→h5 (rawNext s y e)=h5 y) :
    Fibre (h:=h5 x) .second (frozenH5 R x) :=
  ⟨fun y e H=>⟨stay y e H.1,(freeze y e H.1).trans H.2⟩,
    fun _ H i=>congrFun H.2 i⟩

def secondInputs (advice : s=ell (ell n)) (S : 6≤s)
    (R : Raw s n→Prop) (x : Raw s n)
    (stay : ∀ y e,R y→R (rawNext s y e))
    (freeze : ∀ y e,R y→h5 (rawNext s y e)=h5 y)
    (hh : ∃ i,h5 x i=true)
    (Bounds : GapBounds (h5 x) (16*(s+1)) (81*(2*s+1))) :
    Inputs .second (h5 x) (frozenH5 R x) :=
  inputs .second advice S _ _ hh (frozen_h5_fibre R x stay freeze) Bounds

theorem cache_entrance (d : Sheet) {h : Fin n→Bool} {Q : Raw s n→Prop}
    (I : Inputs d h Q) (x : Raw s n) (H : Q x) :
    (∀ y e,Cached d I.hh Q y→Cached d I.hh Q (rawNext s y e)) ∧
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Cached d I.hh Q) x
      ((max 3 (params d s).digits+1)*n^2) := by
  refine ⟨(cached_fibre d I.N I.hh Q I.F).closed,?_⟩
  cases d
  · exact (MonitorRawBridge.height_iff_row _ _ _ _).mp
      (ReportCacheAllSites.report1_raw I.N h I.hh Q I.F.closed I.F.mask x H).2
  · exact (MonitorRawBridge.height_iff_row _ _ _ _).mp
      (ReportCacheAllSites.report2_raw I.N h I.hh Q I.F.closed I.F.mask x H).2

theorem production_radius_room (d : Sheet) (advice : s=ell (ell n)) (S : 6≤s) :
    (params d s).radius * maxWidth d s<n := by
  have r : radiusTwo s≤2^s := AdviceBandRadiusBudget.radius_le_power S
  have rs : s≤radiusTwo s := ReportServiceMesh.radius_ge_self S
  have a : (params d s).radius≤2^s := by cases d <;> first | exact r | exact Nat.le_trans rs r
  have w : maxWidth d s≤AdviceBandRadiusBudget.widthMax s := by
    have B : 81*(2*s+1)≤AdviceBandRadiusBudget.widthMax s := by
      unfold AdviceBandRadiusBudget.widthMax
      exact Nat.le_mul_of_pos_right _ (by omega)
    cases d
    · change 81≤AdviceBandRadiusBudget.widthMax s
      exact Nat.le_trans (by omega) B
    · exact B
  have b := Nat.le_trans w (Nat.le_of_lt (AdviceBandRadiusBudget.width_below_486 S))
  have e : 2*s+9≤2^(s-1) := by have := AdviceBandRadiusBudget.exp_dominates S; omega
  calc
    _ ≤ (2^s)*(486*2^s) := Nat.mul_le_mul a b
    _ ≤ (2^s)*(512*2^s) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by decide))
    _ = 2^(2*s+9) := by rw [show 512=2^9 by decide,show 2*s+9=s+(9+s) by omega,Nat.pow_add,Nat.pow_add]
    _ ≤ 2^(2^(s-1)) := Nat.pow_le_pow_right (by decide) e
    _ < n := ProductionH6Count.advice_lower (by omega) advice

open ShortResetChart
variable {h : Fin n→Bool} {Q : Raw s n→Prop}

def FirstCover (I : Inputs .first h Q) (x : Raw s n) : Prop :=
  CoverAt .first I.Bounds I.hh (CurrentCustodyCut .first I.hh Q I.G) x

private theorem first_chart_width (I : Inputs .first h Q) (r : Owner h) :
    let C := charter I.G r
    (params .first s).digits≤C.a ∧ (params .first s).digits≤C.b ∧
    (params .first s).digits≤C.L-(C.a+C.b) :=
  (ReportFastSplice.charter_width_rooms I.G r (params .first s).digits
    (minWidth .first s) (maxWidth .first s) I.Lo I.Hi (by change 1≤16; decide)).2

theorem first_cover_step (I : Inputs .first h Q) (advice : s=ell (ell n)) (S : 6≤s)
    (x : Raw s n) (e : Fin n) (A : FirstCover I x) :
    FirstCover I (rawNext s x e) ∧ h5 (rawNext s x e)=h5 x := by
  exact ReportProtectedMark.protected_cover_run .first I.N (by omega) I.hh I.G I.F
    (first_chart_width I) I.Bounds (by change 1≤16; decide) (production_radius_room .first advice S) x [e] A

def secondOfFirstCover (I : Inputs .first h Q) (advice : s=ell (ell n)) (S : 6≤s)
    (x : Raw s n) (A : FirstCover I x) :
    Inputs .second (h5 x) (frozenH5 (FirstCover I) x) := by
  have K := ReportUpperFromCover.h5_at_report1_cover I.N I.hh I.G I.F I.Bounds
    (by change 1≤16; decide) (production_radius_room .first advice S) x A
  exact secondInputs advice S _ x
    (fun y e Y=>(first_cover_step I advice S y e Y).1)
    (fun y e Y=>(first_cover_step I advice S y e Y).2) K.1 K.2.2

theorem second_cache_from_first_cover (I : Inputs .first h Q)
    (advice : s=ell (ell n)) (S : 6≤s) (x : Raw s n) (A : FirstCover I x) :
    let K := secondOfFirstCover I advice S x A
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (Cached .second K.hh (frozenH5 (FirstCover I) x)) x
      ((max 3 (params .second s).digits+1)*n^2) :=
  (cache_entrance .second (secondOfFirstCover I advice S x A) x ⟨A,rfl⟩).2

end L4.ReportStageInputs

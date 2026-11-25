import Leader.L4.ReportDeployedTrialSound
import Leader.L4.ReportTrialCensus
import Leader.L4.ReportServiceMeshTrial
import Leader.L4.ReportUpperFromCover

namespace L4.ReportProductionSticky
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportLeaseOwner ReportByteRows
open ReportCurrentCustodyCut ReportSourceBankCut ReportProtectedMark
open ReportStickyRawCover ReportStaticSpacing ShortHopSpacing ReportRootBall
open ReportServiceMesh ReportLossArithmetic AdviceBandRadiusBudget ReportFourLossBridge
open ReportRawTrialSticky ReportTrialCensus ReportActualTrialMesh ReportDeployedTrialSound
open ReportPulseProductionClose ReportPulseLossCounts ReportGoodEightBank ReportFastRawEvent ReportFastDispatch ReportFastFiveGeometry

variable {s n L U : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def StickyAt (d : Sheet) (Bounds : GapBounds h L U) (hh : ∃ i,h i=true) (i : Fin n)
    (x : Raw s n) : Prop :=
  physicalSticky hh (ReportProtectedInterval.Sticky (readout d h) (params d s).radius
    (rootNeighbor Bounds hh) (ReportRootBall.ball Bounds hh (params d s).radius) centerMask) i x

theorem cut_of_bank (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (A : GoodEightBank d hh Q G x) : CurrentCustodyCut d hh Q G x :=
  let D := ReportPrelaunchDoorProducer.digits_positive d S
  current_custody_of_source_bank d N hh G F D x
    (source_bank_cut_of_second d N hh G F D x A.1)

theorem sticky_closed (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (W : WidthOK d G s) (Bounds : GapBounds h L U) (Lo : 1≤L)
    (Room : (params d s).radius*U<n) (i : Fin n) (x : Raw s n) (e : Fin n)
    (Good : GoodEightBank d hh Q G x) (A : StickyAt d Bounds hh i x) :
    StickyAt d Bounds hh i (rawNext s x e) := by
  obtain ⟨c,B,X⟩ := A
  have Sem := raw_mark_semantics d N S hh G F W Bounds x (cut_of_bank d N S hh G F x Good) e
    (ReportRootBall.ball Bounds hh (params d s).radius c)
  have E := ReportProtectedInterval.one_mark _ _ _ _ c _
    (physical_ball_geometry Bounds hh Lo Room c) _ _ _ X Sem
  exact ⟨c,B,E.1⟩

/-- Deployed two-sheet pulse trial. Both middle witnesses, the warm
prefix, the absence of close paints and every service mark concern
one original word. No global ReportCut is used. -/
noncomputable def deployedTrial (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (advice : s=ell (ell n)) (S : 6≤s)
    (GapLo : ∀ r : Owner h,minWidth d s≤gapLen G r)
    (GapHi : G.B≤maxWidth d s) (W : WidthOK d G s)
    (Bounds : GapBounds h L U) (Lo : 1≤L) (Room : (params d s).radius*U<n) :
    Trial (meshRadius d s) (GoodEightBank d hh Q G) (StickyAt (s:=s) d Bounds hh) := by
  let rho := meshRadius d s
  let bank := GoodEightBank d hh Q G
  let root := rootOf h hh
  let censusFn := fun i=>census Bounds hh rho (root i)
  let testFn := fun i=>tests Bounds hh rho (root i)
  let warm := fun i (x : Raw s n) w=>ReportTrialCensus.W d (censusFn i) x w
  let close := fun i (x : Raw s n) w=>sheetCloseLoss d (censusFn i) x w
  let miss := fun i (x : Raw s n) w=>ReportTrialCensus.M d (testFn i) (lateTest rho) x w
  have PosS : 0<s := by omega
  have PosN : 0<n := by omega
  have D := ReportPrelaunchDoorProducer.digits_positive d PosS
  let Rail := ReportWriteRailSupplier.rail_supplier d N hh G F D
  have BankFibre : Fibre (h:=h) d bank := bank_fibre d N hh G Q F D Rail
  let cap := fun i x (A : bank x)=>loss_counts d PosN hh G Bounds (root i) bank BankFibre x A
  apply trialWithMesh d N hh G F advice S GapLo GapHi (writerCensus d Bounds hh)
    (StickyAt d Bounds hh) warm close miss
    (sticky_closed d N PosS hh G F W Bounds Lo Room)
  · intro i x H _
    exact (cap i x H).1
  · intro i x H _
    exact (cap i x H).2.1
  · intro i x H _
    exact (cap i x H).2.2
  · intro i x Good _ ys Len NoWarm NoClose NoMiss Mesh
    have Warm := no_warm d (censusFn i) x ys NoWarm
    obtain ⟨t,LoT,HiT,P⟩ := no_miss_late d PosN Bounds hh (root i) x ys Len NoMiss
    have MiddleLo : ceilDiv (n*trialU rho) 5≤t := by
      rw [Len] at LoT
      change ceilDiv (3*(n*trialU rho)) 5≤t at LoT
      unfold ceilDiv at *
      omega
    have MiddleHi : t<4*(n*trialU rho)/5 := by
      rw [Len] at HiT
      exact HiT
    apply endpoint_from_warm_no_close_and_continued_mesh d N PosS hh G F W Bounds Lo Room
      x (cut_of_bank d N PosS hh G F x Good) ys Len i Mesh Warm NoClose t ⟨MiddleLo,MiddleHi⟩ P
    intro j B _
    obtain ⟨a,Low,High,A⟩ := no_miss_early d PosN Bounds hh (root i) j x ys Len B NoMiss
    refine ⟨a,?_,?_,A⟩
    · rw [Len] at Low
      exact Low
    · change a<2*ys.length/5 at High
      change ceilDiv (3*ys.length) 5≤t at LoT
      unfold ceilDiv at LoT
      omega

theorem sticky_cover_expected (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (advice : s=ell (ell n)) (S : 6≤s)
    (GapLo : ∀ r : Owner h,minWidth d s≤gapLen G r) (GapHi : G.B≤maxWidth d s)
    (W : WidthOK d G s) (Bounds : GapBounds h L U) (Lo : 1≤L)
    (Room : (params d s).radius*U<n) (x : Raw s n) (A : GoodEightBank d hh Q G x) :
    IIDExpectedHittingTimeAtMost (rawNext s)
      (FourLossStickyClock.Cover (GoodEightBank d hh Q G) (StickyAt d Bounds hh))
      x (2*n*trialU (meshRadius d s)*(ell n+1)) :=
  raw_report_mean (by omega) _ _ (deployedTrial d N hh G F advice S GapLo GapHi W Bounds Lo Room) x A

end L4.ReportProductionSticky

import Leader.L4.ShortMISLift
import Leader.L4.ReportCacheAllSites

namespace L4.ShortMIS3Entrance

open AllSizeProtocol PhysicalCustody PhysicalShortSheet ShortMISEngine ShortMISLift
open ShortH2RawEntrance ReportStaticSpacing ShortHopSpacing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {s n : Nat}

/-- Fix the reached H3 mask for every subsequent MIS3 step. -/
def H3Fibre (N : 63<n) (cut y : Raw s n) : Prop :=
  PermanentH3 N y ∧ SelectedMISLayers.h3 y=SelectedMISLayers.h3 cut

theorem h3_fibre_closed (N : 63<n) (x y : Raw s n) (e : Fin n)
    (Y : H3Fibre N x y) : H3Fibre N x (rawNext s y e) :=
  ⟨permanent_h3_step N y e Y.1,(permanent_h3_mask_step N y e Y.1).trans Y.2⟩

def mis3Geometry (N : 189<n) (x : Raw s n)
    (H : PermanentH3 (by omega : 63<n) x) : Geometry s n where
  P := Params.ofGapBounds .mis3 (H3Fibre (by omega) x)
    (h3_fibre_closed (by omega) x)
    (SelectedMISLayers.h3 x) (fun y Y=>Y.2)
    (permanent_h3_nonempty (by omega) x H) 8 27 (permanent_h3_gaps (by omega) x H) (by omega)
  A := 8
  gaps := permanent_h3_gaps (by omega) x H
  seven := by change 7*27<n; omega

theorem mis3_actual_cache (N : 189<n) (x : Raw s n)
    (H : PermanentH3 (by omega : 63<n) x) :
    let p := (mis3Geometry N x H).P
    CacheFacts p ∧ L4.IIDExpectedHittingTimeAtMost (rawNext s) (Cached p) x (3*n^2) :=
  ⟨(mis3Geometry N x H).P.cacheFacts,(mis3Geometry N x H).P.cached_expected x ⟨H,rfl⟩⟩

theorem upper_mis3 (P : Params s n) (S : P.sheet=.mis3)
    (x : Raw s n) (X : P.Lower x) : upper P x=ReportStaticSpacing.h4 x := by
  have E := ShortNORPhysicalAdapter.embed_eq_mask (h:=P.h)
    (fun i=>ShortByteReadouts.misSelected (P.byte x i))
  change upper P x=_ at E
  rw [E]
  funext i
  rw [SelectedMISLayers.h4_mask]
  have M := congrFun (P.maskEq x X) i
  rw [S] at M
  change SelectedMISLayers.h3 x i=P.h i at M
  simp only [Params.byte,S,bytes,M]

/-- Keep the exact lower cut, its row supplier, and the frozen MIS3 cut
    together. There is no state-dependent reselection after publication. -/
def PermanentH4 (N : 189<n) (y : Raw s n) : Prop :=
  ∃ x : Raw s n, ∃ H : PermanentH3 (by omega : 63<n) x,
    ∃ _L : LocalRows (mis3Geometry N x H), Cut (mis3Geometry N x H) y

theorem permanent_h4_from_h3 (N : 189<n) (x : Raw s n)
    (H : PermanentH3 (by omega : 63<n) x)
    (L : LocalRows (mis3Geometry N x H)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH4 N) x (K_H4*n^2) := by
  let G := mis3Geometry N x H
  have T := stage_expected G L x (show G.P.Lower x from ⟨H,rfl⟩)
  intro t
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s) (Cut G) (PermanentH4 N)
    (fun y Y=>⟨x,H,L,Y⟩) t x) (T t)

theorem permanent_h4_step (N : 189<n) (x : Raw s n) (e : Fin n)
    (X : PermanentH4 N x) : PermanentH4 N (rawNext s x e) := by
  obtain ⟨z,H,L,C⟩ := X
  exact ⟨z,H,L,cut_closed _ L x e C⟩

theorem permanent_h4_mask_step (N : 189<n) (x : Raw s n) (e : Fin n)
    (X : PermanentH4 N x) : ReportStaticSpacing.h4 (rawNext s x e)=ReportStaticSpacing.h4 x := by
  obtain ⟨z,H,L,C⟩ := X
  let G := mis3Geometry N z H
  have R := cut_frozen G L x e C
  have C' := cut_closed G L x e C
  rw [upper_mis3 G.P rfl _ C'.1.1.1,upper_mis3 G.P rfl _ C.1.1.1] at R
  exact R

theorem permanent_h4_gaps (N : 189<n) (x : Raw s n) (X : PermanentH4 N x) :
    GapBounds (ReportStaticSpacing.h4 x) 16 81 := by
  obtain ⟨z,H,L,C⟩ := X
  let G := mis3Geometry N z H
  have R := cut_gaps G x C
  rw [upper_mis3 G.P rfl _ C.1.1.1] at R
  exact R

theorem permanent_h4_nonempty (N : 189<n) (x : Raw s n) (X : PermanentH4 N x) :
    ∃ i,ReportStaticSpacing.h4 x i=true := by
  obtain ⟨z,H,L,C⟩ := X
  let G := mis3Geometry N z H
  have R := cut_nonempty G x C
  rwa [upper_mis3 G.P rfl _ C.1.1.1] at R

theorem permanent_h4_from_h2 (N : 189<n) (x : Raw s n)
    (H : PermanentH2 (by omega : 21<n) x)
    (L2 : LocalRows (mis2Geometry (by omega : 63<n) x H))
    (L3 : ∀ (y : Raw s n) (Y : PermanentH3 (by omega : 63<n) y), LocalRows (mis3Geometry N y Y)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH4 N) x
      ((K_H3+K_H4)*n^2) := by
  rw [Nat.add_mul]
  exact AllSizeComposition.additive_stage _ _ _ _ _ x
    (permanent_h3_from_h2 (by omega) x H L2)
    (fun y Y=>permanent_h4_from_h3 N y Y (L3 y Y))

/-- Item 8 starts at a fixed, reached H4 mask and earns report1 caches.
    The cache event by itself is not a report owner epoch. -/
def H4Fibre (N : 189<n) (x y : Raw s n) : Prop :=
  PermanentH4 N y ∧ ReportStaticSpacing.h4 y=ReportStaticSpacing.h4 x

theorem h4_fibre_closed (N : 189<n) (x y : Raw s n) (e : Fin n)
    (Y : H4Fibre N x y) : H4Fibre N x (rawNext s y e) :=
  ⟨permanent_h4_step N y e Y.1,(permanent_h4_mask_step N y e Y.1).trans Y.2⟩

theorem report1_cache_from_h4 (N : 189<n) (x : Raw s n)
    (Y : PermanentH4 N x) :
    let Good := ReportCacheAllSites.Report1Correct (ReportStaticSpacing.h4 x)
      (permanent_h4_nonempty N x Y) (H4Fibre N x)
    (∀ y e, Good y → Good (rawNext s y e)) ∧
      L4.IIDExpectedHittingTimeAtMost (rawNext s) Good x (4*n^2) := by
  have V := ReportCacheAllSites.report1_raw (by omega : 1<n)
    (ReportStaticSpacing.h4 x) (permanent_h4_nonempty N x Y) (H4Fibre N x)
    (h4_fibre_closed N x) (fun _ H i=>congrFun H.2 i) x ⟨Y,rfl⟩
  exact ⟨V.1,(MonitorRawBridge.height_iff_row _ _ _ _).mp V.2⟩

end L4.ShortMIS3Entrance

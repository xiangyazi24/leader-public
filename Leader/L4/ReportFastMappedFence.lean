import Leader.L4.ReportFastPrepMapping

namespace L4.ReportFastMappedFence
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchAllOwners ReportFastOwnerSupport ReportGateGeometry
open ReportFastRefractory ReportFastSteeringMap ReportDenyAncestry ReportFastFiveGeometry
open ReportFastDenySteering ReportFastTargetFence ReportOwnerCommandRail
open ReportJoinedGrants ReportLeaseGrants ReportByteRows BStarShort ReportPrelaunchClock
open ShortChartOwnership ReportLeaseOwner

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- Locate an arbitrary old header of the target's chart among its three
actual header occurrences. The lane tag is taken from the same cell. -/
theorem charter_header_index (G : GapInput h) (r : Owner h) (k : Nat)
    (K : k < (charter G r).L) (H : h (out (charter G r) k)=true) :
    ∃ j : Fin 3, k=start G r j ∧ (charter G r).route.port k=j := by
  obtain ⟨_,AB,A⟩ := gapLen_spec G r
  obtain ⟨_,BB,B⟩ := gapLen_spec G (succOwner G r)
  obtain ⟨_,CC,C⟩ := gapLen_spec G (succOwner G (succOwner G r))
  let a := gapLen G r
  let b := gapLen G (succOwner G r)
  let c := gapLen G (succOwner G (succOwner G r))
  have Room : a+b+c<n := by have := G.room; dsimp only [a,b,c]; omega
  let D := chart_of_three r.property A B C Room
  have Root : (charter G r).root=r.val := owner_chart_root G r.val r.property
  have U := ShortReadCaptureGeometry.chart_unique (charter G r) D Root
  have Len : (charter G r).L=a+b+c := U.1
  have K' : k<a+b+c := Len ▸ K
  change h (nextAt (charter G r).root k)=true at H
  rw [Root] at H
  have V (j : Fin 3) (J : k=start G r j) :
      (charter G r).route.port k=j := by
    rw [J]
    exact congrArg Prod.snd (charter_header_cell G r j).2
  by_cases Z : k=0
  · exact ⟨0,Z,V 0 Z⟩
  have Pos := (three_gap_exact A B C k (Nat.pos_of_ne_zero Z)
    (Nat.le_of_lt K')).mp H
  rcases Pos with E|E|E
  · exact ⟨1,E,V 1 E⟩
  · exact ⟨2,E,V 2 E⟩
  · change k=a+b+c at E
    omega

/-- At a mapped-tape endpoint, a denied owner's incidences have neither an
old ACQ ASK nor a grant. No unsteered reachability claim is made. -/
theorem denied_lane_at_endpoint (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (B : Fin 5→Chart h) (inj : Function.Injective (fun j=>center (B j)))
    (policy : Nat → Raw s n → Fin 5 → Bool) (j : Fin 5)
    (P : ∀ t x,policy t x j=false)
    (x : Raw s n) (X : Cached d hh Q x) (v : List (Fin n))
    (receipt : ReceiptSuffix d B policy x v j)
    (k : Nat) (K : k<(B j).L) (H : h (out (B j) k)=true) :
    let y := rawRun x v
    grantAsk (params d s) true (selectBytes d (y (out (B j) k)))
      (acqOp (params d s)) ((B j).route.port k)=false ∧
    rawGrant d y (out (B j) k) ((B j).route.port k)=false := by
  obtain ⟨pre,reset,w,t,R,E⟩ := receipt
  rw [E,ShortOwnerEpochJS.raw_append,ShortOwnerEpochJS.raw_append]
  let X0 := rawRun x pre
  let a := rawRun X0 reset
  let m := mappedWord d B policy t a w
  let y := rawRun a m
  have Xpre := ReportGoodEightCut.cached_run d N hh F x X pre
  have Map := actual_mapped_deny d hh G B inj policy j P t a w
  have D := deny_after_receipt d (B j) N hh G F X0 Xpre digit reset m R Map
  have S := seed_receipt d (B j) N hh F X0 Xpre reset R
  have A := (cached_genuine_full_parked d (B j) N hh F X0 Xpre reset R).1
  have Y := strong_run d (B j) N hh G F digit a A S m
  have Mask := (cached_fibre d N hh Q F).mask y Y.1 (out (B j) k)
  have No := no_ask_of_non_acq_pc d (B j) y k K Y.2.1 Mask D.1
  rw [Mask,H] at No
  constructor
  · rw [plain_departure_ask _ _ _ _ (by unfold acqOp admitOp; omega)]
    exact No
  · exact D.2 k K H

/-- The six physical rival occurrences, for every actual target-header
offset. This is definitionally the RivalFence needed by ACQWINS1. -/
theorem target_rival_fence_of_receipts (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Fin 5→Owner h) (R : Consecutive G r)
    (policy : Nat → Raw s n → Fin 5 → Bool)
    (P : ∀ t y j,j≠2 → policy t y j=false)
    (x : Raw s n) (X : Cached d hh Q x) (v : List (Fin n))
    (Hist : ∀ j,j≠2 → ReceiptSuffix d (fun i=>charter G (r i)) policy x v j)
    (k : Nat) (K : k<(charter G (r 2)).L)
    (H : h (out (charter G (r 2)) k)=true)
    (j : Fin 3) (J : j≠(charter G (r 2)).route.port k) :
    let a := out (charter G (r 2)) k
    grantAsk (params d s) true (selectBytes d (rawRun x v a)) (acqOp (params d s)) j=false ∧
      rawGrant d (rawRun x v) a j=false := by
  let cs := fun i=>charter G (r i)
  have Geo := target_five_incidence G r R
  have I := centers_injective_of_roots G cs Geo.2.1
  obtain ⟨t,T,P0⟩ := charter_header_index G (r 2) k K H
  rw [P0] at J
  have Y := (Geo.2.2 t).2.1
  rw [←T] at Y
  obtain ⟨i,l,A,B,Cell,_⟩ := (Geo.2.2 t).2.2 j
  have Riv : i≠2 := fun E=>J (A.mp E)
  have E : out (cs i) l=out (cs 2) k :=
    (congrArg Prod.fst Cell).trans (congrArg Prod.fst Y).symm
  have Lane : (cs i).route.port l=j := congrArg Prod.snd Cell
  have V : h (out (cs i) l)=true := E.symm ▸ H
  have L := denied_lane_at_endpoint d N hh G F digit cs I policy i
    (fun t y=>P t y i Riv) x X v (Hist i Riv) l B V
  rw [E,Lane] at L
  exact L

end L4.ReportFastMappedFence

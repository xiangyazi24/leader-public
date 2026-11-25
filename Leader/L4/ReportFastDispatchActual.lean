import Leader.L4.ReportFastDispatch
import Leader.L4.ReportFastUniformDependent
import Leader.L4.ReportFastDispatchGeometry
import Leader.L4.ReportLatePostACQSeed

namespace L4.ReportFastDispatch
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportLeaseOwner ReportFastFiveGeometry ReportIngressOwnership
open ReportFastSplice ReportFastRawEvent ReportFastKernel ReportGoodEightBank
open ReportFastItem10Assembly

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

noncomputable def setup_actual
    (d : Sheet) (N : 1<n) (S : 0<s) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P)
    (rs : Fin 5→Owner h) (R : Consecutive G rs) (j : Target h)
    (J : publicationTarget G (rs 2)=j)
    (w W : Nat) (W3 : 3≤W)
    (T : (params d s).digits≤w)
    (Lo : ∀ r : Owner h,w≤gapLen G r) (Hi : G.B≤W) :
    let C := charter G (rs 2)
    Setup d hh P G rs j w W (C.a+2*C.L+3) := by
  have H (i : Fin 5) := charter_width_rooms G (rs i) (params d s).digits w W Lo Hi T
  have K := canonical_centre G (rs 2)
  have Digit := ReportPrelaunchDoorProducer.digits_positive d S
  refine {
    N := N
    Spos := S
    F := F
    consecutive := R
    W3 := W3
    width := fun i=>(H i).1.2
    wide := fun i=>(H i).1.1
    left := (H 2).2.1
    mid := (H 2).2.2.1
    right := (H 2).2.2.2
    cap := late_dispatch_cap _ _ _ _ Digit W3 (H 2).1.2 K.2.1
    late := J ▸ lateSealCommit_actual d hh P G (rs 2) }

/-- No dispatcher, PACE, or late-clock premises remain. The lower
frozen gap bounds and production advice are the explicit geometry. -/
theorem report_publication_mean
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P)
    (advice : s=ell (ell n)) (S : 6≤s)
    (Bmax : G.B≤maxWidth d s)
    (w W : Nat) (W3 : 3≤W) (Ratio : W≤11*w)
    (T : (params d s).digits≤w)
    (Lo : ∀ r : Owner h,w≤gapLen G r) (Hi : G.B≤W) :
    ShortTwoPublicationClock.UniformPublicationMean
      (rawNext s) (classify d h) (GoodEightBank d hh P G)
      (coefficient (params d s).digits W*n) := by
  classical
  have Spos : 0<s := by omega
  have Digit := ReportPrelaunchDoorProducer.digits_positive d Spos
  let picked (j : Target h) := production_consecutive_for_publication d G j advice S Bmax
  let rs (j : Target h) := Classical.choose (picked j)
  let E (j : Target h) := setup_actual d N Spos hh G F (rs j)
    (Classical.choose_spec (picked j)).1 j (Classical.choose_spec (picked j)).2
    w W W3 T Lo Hi
  have BC : ∀ x e,GoodEightBank d hh P G x→GoodEightBank d hh P G (rawNext s x e) :=
    good_bank_closed d N hh G F Digit
      (ReportWriteRailSupplier.rail_supplier d N hh G F Digit)
  exact uniform_from_dependent_dispatchers d N hh G F Digit BC
    (fun j=>(E j).B) (fun j=>(E j).mem) (fun j=>(E j).inj)
    (fun j=>caps (E j).t W ((charter G (rs j 2)).a+2*(charter G (rs j 2)).L+3)) (fun j=>(E j).State) (fun j=>(E j).localRows)
    w W (Nat.lt_of_lt_of_le Digit T) (by omega) Ratio
    (fun j=>(E j).wide) (fun j=>cap_total _ _ _ (E j).cap)

def minWidth (d : Sheet) (s : Nat) : Nat :=
  match d with
  | .first => 16
  | .second => 16*(s+1)

theorem deployed_publication_mean
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P)
    (advice : s=ell (ell n)) (S : 6≤s)
    (Lo : ∀ r : Owner h,minWidth d s≤gapLen G r) (Hi : G.B≤maxWidth d s) :
    ShortTwoPublicationClock.UniformPublicationMean
      (rawNext s) (classify d h) (GoodEightBank d hh P G) (mu d s*n) := by
  have W3 : 3≤maxWidth d s := by cases d <;> simp [maxWidth] <;> omega
  have Wratio : maxWidth d s≤11*minWidth d s := by
    cases d <;> simp [maxWidth,minWidth] <;> omega
  have digits : (params d s).digits≤minWidth d s := by
    cases d
    · change 1≤16
      decide
    · have H := AdviceBandRadiusBudget.t2_le S
      change (params .second s).digits≤s+1 at H
      change (params .second s).digits≤16*(s+1)
      omega
  exact report_publication_mean d N hh G F advice S Hi
    (minWidth d s) (maxWidth d s) W3 Wratio digits Lo Hi

def publicationSites (h : Fin n→Bool) : List (Target h) :=
  (List.finRange n).filterMap fun i=>if H : h i=true then some ⟨i,H⟩ else none

theorem publicationSites_complete (j : Target h) : j∈publicationSites h := by
  apply List.mem_filterMap.mpr
  exact ⟨j.val,by simp,dif_pos j.property⟩

theorem deployed_two_covers_expected
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P)
    (advice : s=ell (ell n)) (S : 6≤s)
    (Lo : ∀ r : Owner h,minWidth d s≤gapLen G r) (Hi : G.B≤maxWidth d s)
    (x : Raw s n) (B : GoodEightBank d hh P G x) :
    Height.IIDExpectedHittingTimeAtMost
      (ShortTwoPublicationClock.monitoredNext (rawNext s) (classify d h))
      SequentialMarkClock.finished
      (SequentialMarkClock.start false (publicationSites h++publicationSites h) x)
      (2*mu d s*n^2) := by
  have Site : (publicationSites h).length≤n :=
    Nat.le_trans (List.length_filterMap_le _ _) (by simp)
  have D := ReportPrelaunchDoorProducer.digits_positive d (by omega : 0<s)
  apply ShortTwoPublicationClock.two_covers_quadratic (rawNext s) (classify d h)
    (GoodEightBank d hh P G)
    (good_bank_closed d N hh G F D (ReportWriteRailSupplier.rail_supplier d N hh G F D))
    (mu d s) (deployed_publication_mean d N hh G F advice S Lo Hi)  (publicationSites h) Site x B

end L4.ReportFastDispatch

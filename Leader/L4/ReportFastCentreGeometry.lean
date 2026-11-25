import Leader.L4.ReportFastLateWitness
import Leader.L4.ReportFastFiveGeometry
import Leader.L4.ReportOwnerAcquireProvenance
import Leader.L4.ReportFastProductionRoom

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportLeaseOwner ReportFastFiveGeometry ReportGenerationAncestry ReportIngressOwnership
open ReportFastOwnerSupport ReportFastProductionRoom ShortChartOwnership

variable {n : Nat} {h : Fin n→Bool}

theorem publicationTarget_eq_successor (G : GapInput h) (r : Owner h) :
    publicationTarget G r=succOwner G r := by
  let C := charter G r
  let k := start G r 1
  obtain ⟨K,E⟩ := charter_header_cell G r 1
  have Left : out C k=(succOwner G r).val := by
    have P0 := congrArg Prod.fst E
    change out C k=(if (1 : Fin 3)=0 then r else if (1 : Fin 3)=1 then
      succOwner G r else succOwner G (succOwner G r)).val at P0
    simpa using P0
  have Right : C.route.port k=1 := congrArg Prod.snd E
  have H : h (out C k)=true := by rw [Left]; exact (succOwner G r).property
  have J : k=C.a := ((ReportOwnerAcquireProvenance.centre_geometry C G).2 k K).mp ⟨H,Right⟩
  apply Subtype.ext
  change out C C.a=(succOwner G r).val
  rwa [←J]

/-- Select the five charts by taking the predecessor of the published
centre as the middle *root*, not the centre itself. -/
theorem consecutive_for_publication (G : GapInput h) (j : Owner h)
    (room : 4*G.B<n) :
    ∃ r : Fin 5→Owner h, Consecutive G r ∧ publicationTarget G (r 2)=j := by
  let hh : ∃ i,h i=true := ⟨j.val,j.property⟩
  obtain ⟨r,C,E⟩ := exists_consecutive_center G (predOwner hh j) room
  refine ⟨r,C,?_⟩
  rw [E,publicationTarget_eq_successor,succ_pred G hh j]

theorem production_consecutive_for_publication (d : Sheet) (G : GapInput h)
    (j : Owner h) {s : Nat}
    (advice : s=ell (ell n)) (S : 6≤s) (Bound : G.B≤ReportFastRawEvent.maxWidth d s) :
    ∃ r : Fin 5→Owner h, Consecutive G r ∧ publicationTarget G (r 2)=j :=
  consecutive_for_publication G j (production_five_room d advice S Bound)

end L4.ReportFastSplice

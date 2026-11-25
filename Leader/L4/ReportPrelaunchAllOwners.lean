import Leader.L4.ReportPrelaunchTwoCovers

namespace L4.ReportPrelaunchAllOwners
open PhysicalCustody ReportResetRawHooks ShortResetCycle ShortResetChart
open ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportPrelaunchTwoCovers

variable {s n : Nat} {h : Fin n → Bool}

noncomputable def ownerChart (G : GapInput h) (i : Fin n) (H : h i=true) : Chart h := by
  let a := Classical.choose (G.gaps i H)
  have A := Classical.choose_spec (G.gaps i H)
  let b := Classical.choose (G.gaps (nextAt i a) A.2.2.atEnd)
  have B := Classical.choose_spec (G.gaps (nextAt i a) A.2.2.atEnd)
  let c := Classical.choose (G.gaps (nextAt (nextAt i a) b) B.2.2.atEnd)
  have C := Classical.choose_spec (G.gaps (nextAt (nextAt i a) b) B.2.2.atEnd)
  have R : a+b+c<n := by
    have aB : a≤G.B := A.2.1
    have bB : b≤G.B := B.2.1
    have cB : c≤G.B := C.2.1
    have G0 := G.room
    omega
  exact ShortLayerGeometry.chart_of_three H A.2.2 B.2.2 C.2.2 R

theorem owner_chart_root (G : GapInput h) (i : Fin n) (H : h i=true) :
    (ownerChart G i H).root=i := rfl

noncomputable def ownerCharts (G : GapInput h) : List (Chart h) :=
  (List.finRange n).filterMap fun i=>if H : h i=true then some (ownerChart G i H) else none

theorem owner_charts_length (G : GapInput h) : (ownerCharts G).length≤n := by
  unfold ownerCharts
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem owner_charts_cover (G : GapInput h) (i : Fin n) (H : h i=true) :
    ∃ C ∈ ownerCharts G, C.root=i := by
  refine ⟨ownerChart G i H,?_ ,owner_chart_root G i H⟩
  apply List.mem_filterMap.mpr
  exact ⟨i,by simp,dif_pos H⟩

/-- Every frozen header appears in both copies of this chart list;
    the mean covers first receipts and does not assume Good8. -/
theorem expected
    (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (Q : Raw s n→Prop) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    Height.IIDExpectedHittingTimeAtMost
      (SequentialMarkClock.step (advance d hh F N)
        (fun C=>ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F))
        (fun _=>ReportOwnerReceiptClock.done) none)
      SequentialMarkClock.finished
      (SequentialMarkClock.start none (ownerCharts G++ownerCharts G) x)
      (2*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) :=
  monitor_expected d N S hh G F _ (owner_charts_length G) x

end L4.ReportPrelaunchAllOwners

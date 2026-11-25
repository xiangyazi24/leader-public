import Leader.L4.ReportFastCentreGeometry

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportLeaseOwner ReportFastFiveGeometry

variable {n : Nat} {h : Fin n→Bool}

theorem charter_dimensions (G : GapInput h) (r : Owner h) :
    let a := gapLen G r
    let b := gapLen G (succOwner G r)
    let c := gapLen G (succOwner G (succOwner G r))
    (charter G r).a=a ∧ (charter G r).b=b ∧ (charter G r).L=a+b+c := by
  exact ⟨rfl,rfl,rfl⟩

/-- Every actual charter derives both width bounds and all three digit
rooms from the lower physical gap bounds. -/
theorem charter_width_rooms (G : GapInput h) (r : Owner h) (t w W : Nat)
    (GapLo : ∀ y : Owner h,w≤gapLen G y) (GapHi : G.B≤W) (T : t≤w) :
    let C := charter G r
    (3*w≤C.L ∧ C.L≤3*W) ∧ t≤C.a ∧ t≤C.b ∧ t≤C.L-(C.a+C.b) := by
  dsimp only
  obtain ⟨A,B,C⟩ := charter_dimensions G r
  have LA := GapLo r
  have LB := GapLo (succOwner G r)
  have LC := GapLo (succOwner G (succOwner G r))
  have UA := (gapLen_spec G r).2.1
  have UB := (gapLen_spec G (succOwner G r)).2.1
  have UC := (gapLen_spec G (succOwner G (succOwner G r))).2.1
  rw [A,B,C]
  omega

theorem late_dispatch_cap (t L a W : Nat) (T : 0<t) (W3 : 3≤W)
    (D : L≤3*W) (R : a<L) :
    29*t*W+(12*W+1)+21*t*W+(a+2*L+3)≤112*t*W := by
  have M : W≤t*W := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right W T
  have E : 29*t*W=29*(t*W) := Nat.mul_assoc ..
  have F : 21*t*W=21*(t*W) := Nat.mul_assoc ..
  have G : 112*t*W=112*(t*W) := Nat.mul_assoc ..
  rw [E,F,G]
  omega

end L4.ReportFastSplice

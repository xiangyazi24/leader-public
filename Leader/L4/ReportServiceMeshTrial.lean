import Leader.L4.ReportServiceMesh

namespace L4.ReportServiceMesh
open Height FourLossStickyClock AllSizeProtocol PhysicalCustody
open AdviceBandRadiusBudget ReportLossArithmetic
open ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportLeaseOwner ReportFastFiveGeometry
open ReportIngressOwnership ReportFastSplice ReportFastRawEvent
open ReportFastKernel ReportGoodEightBank ReportFastItem10Assembly
open ReportFastDispatch

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

noncomputable section

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

def fourLosses (warm close miss mesh :
    Fin n→Raw s n→List (Fin n)→Prop)
    (i : Fin n) (x : Raw s n) (j : Fin 4) (w : List (Fin n)) : Prop :=
  if j.val=0 then warm i x w
  else if j.val=1 then close i x w
  else if j.val=2 then miss i x w
  else mesh i x w

/-- The exact four-loss consumer with the service mesh discharged.
    The deterministic implication uses RawTwoCellCovers, rather than
    making the stronger unsupported claim that all publications are
    fresh at a pulse cut. -/
def trialWithMesh (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P)
    (advice : s=ell (ell n)) (S : 6≤s)
    (Lo : ∀ r : Owner h,minWidth d s≤gapLen G r)
    (Hi : G.B≤maxWidth d s)
    {relevant : Fin n→Raw s n→Target h→Prop}
    (C : WriterCensus (meshRadius d s) relevant)
    (Sticky : Fin n→Raw s n→Prop)
    (warm close miss : Fin n→Raw s n→List (Fin n)→Prop)
    (sticky_closed : ∀ i x e,GoodEightBank d hh P G x→
      Sticky i x→Sticky i (rawNext s x e))
    (WARM_COUNT : ∀ i x,GoodEightBank d hh P G x→¬Sticky i x→
      8*badCount (warm i x) (n*trialU (meshRadius d s))≤
        n^(n*trialU (meshRadius d s)))
    (JOINT_COUNT : ∀ i x,GoodEightBank d hh P G x→¬Sticky i x→
      8*badCount (close i x) (n*trialU (meshRadius d s))≤
        n^(n*trialU (meshRadius d s)))
    (MISS_COUNT : ∀ i x,GoodEightBank d hh P G x→¬Sticky i x→
      8*badCount (miss i x) (n*trialU (meshRadius d s))≤
        n^(n*trialU (meshRadius d s)))
    (TRIAL_TO_STICKY : ∀ i x,GoodEightBank d hh P G x→¬Sticky i x→
      ∀ w,w.length=n*trialU (meshRadius d s)→
        ¬warm i x w→¬close i x w→¬miss i x w→
        RawTwoCellCovers d (C.writer i x) x w→
        Sticky i (runWord (rawNext s) x w)) :
    ReportFourLossBridge.Trial (meshRadius d s)
      (GoodEightBank d hh P G) Sticky := by
  classical
  let mesh := fun i x w=>rawMeshLoss d (C.writer i x) x w
  have Digit := ReportPrelaunchDoorProducer.digits_positive d (by omega : 0<s)
  refine {
    loss := fourLosses warm close miss mesh
    closed := good_bank_closed d N hh G F Digit
      (ReportWriteRailSupplier.rail_supplier d N hh G F Digit)
    sticky := sticky_closed
    sound := ?_
    cap := ?_ }
  · intro i x X NS w L BAD
    by_cases A : warm i x w
    · exact ⟨0,by simpa [fourLosses] using A⟩
    by_cases B : close i x w
    · exact ⟨1,by simpa [fourLosses] using B⟩
    by_cases D : miss i x w
    · exact ⟨2,by simpa [fourLosses] using D⟩
    by_cases M : mesh i x w
    · refine ⟨3,?_⟩
      change mesh i x w
      exact M
    exact False.elim (BAD (TRIAL_TO_STICKY i x X NS w L A B D
      (raw_covers_of_no_mesh_loss d (C.writer i x) x w M)))
  · intro i x X NS j
    have J : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 := by
      have := j.isLt
      omega
    rcases J with A|A|A|A
    · have Eq : fourLosses warm close miss mesh i x j = warm i x := by
        funext w
        simp [fourLosses,A]
      rw [Eq]
      exact WARM_COUNT i x X NS
    · have Eq : fourLosses warm close miss mesh i x j = close i x := by
        funext w
        simp [fourLosses,A]
      rw [Eq]
      exact JOINT_COUNT i x X NS
    · have Eq : fourLosses warm close miss mesh i x j = miss i x := by
        funext w
        simp [fourLosses,A]
      rw [Eq]
      exact MISS_COUNT i x X NS
    · have Eq : fourLosses warm close miss mesh i x j = mesh i x := by
        funext w
        simp [fourLosses,A]
      rw [Eq]
      exact deployed_mesh_cap d N hh G F advice S Lo Hi
        (C.writer i x) (C.cap i x) x X

end
end L4.ReportServiceMesh


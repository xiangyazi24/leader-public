import Leader.L4.ReportFastSplicePace

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners ReportGoodEightBank
open ReportFastOwnerSupport ReportFastRawEvent ReportFastKernel

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop} {X : Type}

/-- The target-wise literal dispatcher is the only observer input.
Projection, publication latch, PACE and the scheduler-dependent mean
are provided by the checked splice, not extra dispatcher premises. -/
theorem uniform_from_dispatchers
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d P) (digit : 0<(params d s).digits)
    (BC : ∀ x e,GoodEightBank d hh P G x→GoodEightBank d hh P G (rawNext s x e))
    (Charts : ReportFastItem10Assembly.Target h→Fin 5→Chart h) (M : ∀ j k,Charts j k∈ownerCharts G)
    (Inj : ∀ j,Function.Injective (fun k=>center (Charts j k)))
    (b : ReportFastItem10Assembly.Target h→Caps) (L : ∀ j,LocalRows d hh P G (Charts j) j (b j) X)
    (w W : Nat) (wp : 0<w) (Wp : 0<W) (Ratio : W≤11*w)
    (Width : ∀ j k,3*w≤(Charts j k).L)
    (Bound : ∀ j,(b j).total≤2*(518*(params d s).digits*W)+1) :
    ShortTwoPublicationClock.UniformPublicationMean
      (rawNext s) (classify d h) (GoodEightBank d hh P G)
      (coefficient (params d s).digits W*n) := by
  apply ReportFastItem10Assembly.item10_uniform_of_phase_rows
    d N hh G F digit (GoodEightBank d hh P G) BC Charts M Inj
    (fun j=>next (L j)) (fun j=>good (L j)) (fun _=>finish)
    (fun j=>project (L j)) (fun j=>init (L j))
    (fun j=>obsBan (L j)) (fun j=>active (L j)) (fun j=>desired (L j))
    (fun j=>obsDebt (L j)) (fun j=>obsCredit (L j)) w W wp Wp Ratio
  · intro j
    exact concrete_phaseRows_of_local (L j) N F digit (M j) (Inj j) BC w W (Width j) (Bound j)
  · intro j y e H
    exact sticky (L j) y e H
  · intro j x B
    exact init_good (L j) x B
  · intro j x B
    exact init_project (L j) x B
  · intro j y e H
    exact (next_spec (L j) BC y e H).2
  · intro j y _ H
    exact H

#print axioms uniform_from_dispatchers
end L4.ReportFastSplice

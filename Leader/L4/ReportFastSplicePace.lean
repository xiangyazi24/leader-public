import Leader.L4.ReportFastSplice
import Leader.L4.ReportFastRefractoryAdapter

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners ReportGoodEightBank ReportFastOwnerSupport
open ReportFastNominationBridge ReportAdaptiveFibre ReportFastKernel
open ReportFastItem10Assembly ReportFastRawEvent ReportGateGeometry

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop} {X : Type}
variable {d : Sheet} {hh : ∃ i,h i=true} {G : GapInput h}
variable {C : Fin 5→Chart h} {j : Target h} {b : Caps}
variable (L : LocalRows d hh P G C j b X)

theorem pace_of_local
    (N : 1<n) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (M : ∀ k,C k∈ownerCharts G)
    (inj : Function.Injective (fun k=>center (C k)))
    (BC : ∀ x e,GoodEightBank d hh P G x→GoodEightBank d hh P G (rawNext s x e))
    (w W : Nat) (Width : ∀ k,3*w≤(C k).L) :
    Pace L (params d s).digits w W := by
  apply ReportFastItem10Assembly.service_program_refractory_raw
    d N hh G F digit C M inj w W Width (next L) (good L) (project L)
    (fun y e H=>(next_spec L BC y e H).1)
    (fun y H=>L.bank y.core H)
    (fun y e H=>congrArg Prod.fst (next_spec L BC y e H).2)
    (obsBan L) (active L) (desired L)
  · intro y _ e a
    exact makeBan_spec hh G C inj (active L y) (desired L y) e a
  · intro y H k A
    by_cases B : y.latch=true
    · simp [active,B] at A
    · exact L.race y.core H k (by simpa [active,B] using A)

theorem concrete_phaseRows_of_local
    (N : 1<n) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (M : ∀ k,C k∈ownerCharts G)
    (inj : Function.Injective (fun k=>center (C k)))
    (BC : ∀ x e,GoodEightBank d hh P G x→GoodEightBank d hh P G (rawNext s x e))
    (w W : Nat) (Width : ∀ k,3*w≤(C k).L)
    (Cap : b.total≤2*(518*(params d s).digits*W)+1) :
    PhaseRows (P:=P) d hh G C (next L) (good L) finish (project L)
      (obsBan L) (active L) (desired L) (obsDebt L) (obsCredit L) (params d s).digits w W :=
  phaseRows_of_local L inj BC _ w W Cap (pace_of_local L N F digit M inj BC w W Width)

end L4.ReportFastSplice

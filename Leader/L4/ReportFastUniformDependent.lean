import Leader.L4.ReportFastUniformFromDispatcher

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners ReportGoodEightBank
open ReportFastOwnerSupport ReportFastRawEvent ReportFastKernel ReportAdaptiveFibre
open ReportFastItem10Assembly

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

private def oneClassifier {A J : Type} [DecidableEq J]
    (c : A→Fin n→Option J) (j : J) (x : A) (e : Fin n) : Option Unit :=
  if c x e=some j then some () else none

private theorem one_phase {A J : Type} [DecidableEq J]
    (step : A→Fin n→A) (c : A→Fin n→Option J) (j : J) :
    ShortTwoPublicationClock.phase step (oneClassifier c j) ()=
      ShortTwoPublicationClock.phase step c j := by
  funext x e
  by_cases E : c x.1 e=some j <;> simp [oneClassifier,ShortTwoPublicationClock.phase,E]

/-- Observer state may contain a target-indexed chart and history. Apply
the same finite-word kernel to each target without casting or forgetting
its chronological witnesses. -/
theorem uniform_from_dependent_dispatchers
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d P) (digit : 0<(params d s).digits)
    (BC : ∀ x e,GoodEightBank d hh P G x→GoodEightBank d hh P G (rawNext s x e))
    (Charts : Target h→Fin 5→Chart h) (M : ∀ j k,Charts j k∈ownerCharts G)
    (Inj : ∀ j,Function.Injective (fun k=>center (Charts j k)))
    (b : Target h→Caps) (X : Target h→Type)
    (L : ∀ j,LocalRows d hh P G (Charts j) j (b j) (X j))
    (w W : Nat) (wp : 0<w) (Wp : 0<W) (Ratio : W≤11*w)
    (Width : ∀ j k,3*w≤(Charts j k).L)
    (Bound : ∀ j,(b j).total≤2*(518*(params d s).digits*W)+1) :
    ShortTwoPublicationClock.UniformPublicationMean
      (rawNext s) (classify d h) (GoodEightBank d hh P G)
      (coefficient (params d s).digits W*n) := by
  classical
  intro j x H
  let c := oneClassifier (classify d (s:=s) h) j
  let R := L j
  have F' := concrete_phaseRows_of_local R N F digit (M j) (Inj j) BC w W (Width j) (Bound j)
  have K := paper_kernel_of_rows d N hh G F digit (Charts j) (M j) (Inj j)
    (next R) (good R) finish (project R) (obsBan R) (active R) (desired R)
    (obsDebt R) (obsCredit R) (params d s).digits w W digit Wp F'
  have C : ShortTwoPublicationClock.phase (rawNext s) c ()=
      ShortTwoPublicationClock.phase (rawNext s) (classify d h) j :=
    one_phase (rawNext s) (classify d h) j
  have A := paper_uniform_publication (rawNext s) c (GoodEightBank d hh P G) BC
    digit Wp wp (by omega) Ratio
    (fun _=>next R) (fun _ y=>mergeSide (obsBan R y)) (fun _=>good R)
    (fun _=>finish) (fun _ y=>eventRank (obsDebt R y) (obsCredit R y))
    (fun _ y e=>mark5 d (Charts j) (project R y).1 e)
    (fun _=>project R) (fun _=>init R) (fun _=>K)
    (fun _ y e H=>sticky R y e H) (fun _ y H=>init_good R y H)
    (fun _ y H=>init_project R y H)
    (fun _ y e H=>by rw [C]; exact (next_spec R BC y e H).2)
    (fun _ y _ H=>H)
  have E := A () x H
  rw [C] at E
  exact E

#print axioms uniform_from_dependent_dispatchers
end L4.ReportFastSplice

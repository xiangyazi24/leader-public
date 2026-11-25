import Leader.L4.ReportFastSixPrep

namespace L4.ReportFastSixPrepPlateau
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportFastSixPrep

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- A step retaining the preparation index is exactly the local
RESET monitor step, not a launch of a new monitor. -/
theorem retained_stage_of_same_index (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : ReportFastSixPrep.State d hh Q) (j : Fin 6) (st : Option Stage)
    (E : z.2=some (j,st)) (e : Fin n)
    (H : (ReportFastSixPrep.step d C N hh F z e).2.map Prod.fst=some j) :
    let m := ReportFastFreshReset.step d (C j) N hh F (z.1,st) e
    (ReportFastSixPrep.step d C N hh F z e).2=some (j,m.2) ∧
      (ReportFastSixPrep.step d C N hh F z e).1=m.1 ∧ m.2≠some .done := by
  dsimp only
  let m := ReportFastFreshReset.step d (C j) N hh F (z.1,st) e
  have P : (ReportFastSixPrep.step d C N hh F z e).1=m.1 := rfl
  by_cases D : m.2=some .done
  · by_cases J : j.val+1<6
    · have K : (ReportFastSixPrep.step d C N hh F z e).2=some ((⟨j.val+1,J⟩:Fin 6),none) := by
        simp [ReportFastSixPrep.step,E,m,D,J]
      rw [K] at H
      have V := congrArg Fin.val (Option.some.inj H)
      change j.val+1=j.val at V
      omega
    · have K : (ReportFastSixPrep.step d C N hh F z e).2=none := by simp [ReportFastSixPrep.step,E,m,D,J]
      rw [K] at H
      contradiction
  · exact ⟨by simp [ReportFastSixPrep.step,E,m,D],P,D⟩

theorem same_phase_debt_iff (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (W : Nat)
    (z : ReportFastSixPrep.State d hh Q) (j : Fin 6) (st : Option Stage)
    (E : z.2=some (j,st)) (e : Fin n)
    (H : (ReportFastSixPrep.step d C N hh F z e).2.map Prod.fst=some j) :
    ReportFastSixPrep.debt d C hh W (ReportFastSixPrep.step d C N hh F z e)=ReportFastSixPrep.debt d C hh W z ↔
      ReportFastFreshReset.freshDebt d (C j) hh
        (ReportFastFreshReset.step d (C j) N hh F (z.1,st) e)=
      ReportFastFreshReset.freshDebt d (C j) hh (z.1,st) := by
  let m := ReportFastFreshReset.step d (C j) N hh F (z.1,st) e
  obtain ⟨V,Raw,_⟩ := retained_stage_of_same_index d C N hh F z j st E e H
  change (ReportFastSixPrep.step d C N hh F z e).2=some (j,m.2) at V
  change (ReportFastSixPrep.step d C N hh F z e).1=m.1 at Raw
  simp only [ReportFastSixPrep.debt,V,E,Raw,ReportFastFreshReset.prepDebt]
  have Eta : (m.1,m.2)=m := by cases m; rfl
  rw [Eta]
  simp only [Nat.add_right_cancel_iff]
  rfl

#print axioms retained_stage_of_same_index
#print axioms same_phase_debt_iff
end L4.ReportFastSixPrepPlateau

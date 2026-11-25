import Leader.L4.ReportFastPrepMapping

namespace L4.ReportFastPreparedMean
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportFastOwnerSupport ReportFastNominationBridge
open ReportAdaptiveFibre ReportFastKernel

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def prepCharts (B : Fin 5→Chart h) (i : Fin 6) : Chart h :=
  if I : i.val<5 then B ⟨i.val,I⟩ else B 2

theorem prepCharts_target (B : Fin 5→Chart h) : prepCharts B ReportFastSixPrep.target=B 2 := rfl

theorem prepCharts_includes (B : Fin 5→Chart h) (j : Fin 5) :
    prepCharts B j.castSucc=B j := by
  simp [prepCharts,j.isLt]

theorem prepCharts_width (B : Fin 5→Chart h) (W : Nat)
    (L : ∀ j,(B j).L≤3*W) :
    ∀ i,(prepCharts B i).L≤3*W := by
  intro i
  unfold prepCharts
  split <;> exact L _

/-- Preparation has linear mean on the mapped driver draws. This is not
an unsteered mean or a success claim for the publication phase. -/
theorem six_prep_driver_mean
    (d : Sheet) (C : Fin 6→Chart h) (B : Fin 5→Chart h)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q)
    (inc : ∀ j,∃ i,C i=B j)
    (inj : Function.Injective (fun j=>center (B j)))
    (digit : 0<(params d s).digits)
    (W : Nat) (W3 : 3≤W) (Width : ∀ i,(C i).L≤3*W)
    (z : ReportFastSixPrepTrack.Prepared d hh Q)
    (I : ReportFastSixPrepTrack.good d C B hh z) :
    let next := ReportFastSixPrepTrack.step d C B N hh F W
    let steer := fun z=>mergeSide (ReportFastSixPrepTrack.prepBan d B z.base)
    let done := fun z : ReportFastSixPrepTrack.Prepared d hh Q=>ReportFastSixPrepTrack.hit z.base
    Height.IIDExpectedHittingTimeAtMost (driverStep next steer) done z
      (n*(2048*(params d s).digits*W)) := by
  dsimp only
  let next := ReportFastSixPrepTrack.step d C B N hh F W
  let steer := fun z : ReportFastSixPrepTrack.Prepared d hh Q=>
    mergeSide (ReportFastSixPrepTrack.prepBan d B z.base)
  let done := fun z : ReportFastSixPrepTrack.Prepared d hh Q=>ReportFastSixPrepTrack.hit z.base
  let rank := fun z : ReportFastSixPrepTrack.Prepared d hh Q=>
    eventRank (ReportFastSixPrep.debt d C hh W z.base) z.unspent
  have M := driver_nominated_mean next steer (ReportFastSixPrepTrack.good d C B hh) done rank
    (ReportFastSixPrepTrack.all_mark d C B N hh F W inc inj G digit W3 Width)
    (fun y e Y H=>by
      have R := ReportFastSixPrepTrack.service_debt d C B N hh F W inc inj G digit W3 Width
        y e Y ((live_iff ReportFastSixPrepTrack.hit y).mpr H)
      have T := ReportFastSixPrepTrack.service_credit d C B N hh F W y e Y
        ((live_iff ReportFastSixPrepTrack.hit y).mpr H)
      exact eventRank_idle R T)
    (fun y Y H=>by
      obtain ⟨a,e,E,P⟩ := ReportFastSixPrepTrack.service_nominate d C B N hh F W
        inc inj G digit W3 Width y Y ((live_iff ReportFastSixPrepTrack.hit y).mpr H)
      exact ⟨a,e,E,eventRank_progress P⟩) z I
  have R := ReportFastSixPrep.debt_bound d C hh W W3 Width digit z.base I.1
  have EB : rank z≤2048*(params d s).digits*W :=
    eventRank_paper_bound R digit (by omega)
  intro v
  exact Nat.le_trans (M v) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ EB))


theorem tracked_driver_run_base
    (d : Sheet) (C : Fin 6→Chart h) (B : Fin 5→Chart h)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (W : Nat) (z : ReportFastSixPrepTrack.Prepared d hh Q)
    (w : List (Fin n)) :
    let next := ReportFastSixPrepTrack.step d C B N hh F W
    let steer := fun z=>mergeSide (ReportFastSixPrepTrack.prepBan d B z.base)
    (Height.runWord (driverStep next steer) z w).base =
      SequentialMarkClock.run
        (fun a e=>ReportFastSixPrep.step d C N hh F a
          (mergeSide (ReportFastSixPrepTrack.prepBan d B a) e)) z.base w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w IH =>
    let m := mergeSide (ReportFastSixPrepTrack.prepBan d B z.base) e
    let y := ReportFastSixPrepTrack.step d C B N hh F W z m
    change (Height.runWord _ y w).base =
      SequentialMarkClock.run _ (ReportFastSixPrep.step d C N hh F z.base m) w
    have E : y.base=ReportFastSixPrep.step d C N hh F z.base m := by
      unfold y ReportFastSixPrepTrack.step
      exact next_base _ _ _ _ _ _
    rw [IH y,E]

/-- The actual last mapped mark, rather than the time or the ghost phase
number, carries the certified owner RESET consume into the next stage. -/
theorem tracked_driver_finish
    (d : Sheet) (B : Fin 5→Chart h) (N : 1<n) (hh : ∃ i,h i=true)
    (F : Fibre (h:=h) d Q) (W : Nat)
    (z : ReportFastSixPrepTrack.Prepared d hh Q)
    (I : ReportFastSixPrepTrack.good d (prepCharts B) B hh z)
    (e : Fin n) (L : ¬ReportFastSixPrepTrack.hit z.base)
    (H : ReportFastSixPrepTrack.hit
      (ReportFastSixPrepTrack.step d (prepCharts B) B N hh F W z
        (mergeSide (ReportFastSixPrepTrack.prepBan d B z.base) e)).base) :
    let m := mergeSide (ReportFastSixPrepTrack.prepBan d B z.base) e
    let y := rawNext s z.base.1.val m
    (∃ st,ReportFastSixPrep.CurrentConsume d (prepCharts B) hh
      z.base ReportFastSixPrep.target st m) ∧
    ReportPrelaunchClock.readPC d (B 2) y=(1,1) ∧ FullParked d (B 2) y := by
  dsimp only
  let m := mergeSide (ReportFastSixPrepTrack.prepBan d B z.base) e
  obtain ⟨st,Consume,PC,Parked⟩ :=
    ReportFastSixPrepTrack.exact_final_cut d (prepCharts B) B N hh F W z m I L H
  rw [ReportFastSixPrepTrack.step_raw,prepCharts_target] at PC Parked
  exact ⟨⟨st,Consume⟩,PC,Parked⟩

#print axioms prepCharts_target
#print axioms prepCharts_includes
#print axioms prepCharts_width
#print axioms six_prep_driver_mean
#print axioms tracked_driver_run_base
#print axioms tracked_driver_finish

end L4.ReportFastPreparedMean

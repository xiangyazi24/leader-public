import Leader.L4.ReportFastPreparedMean
import Leader.L4.ReportFastMappedFence

namespace L4.ReportFastReceiptSwitch
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportFastOwnerSupport ReportFastNominationBridge ReportAdaptiveFibre
open ReportFastPreparedMean ReportFastPrepMapping ReportFastDenySteering
open ReportPrelaunchClock ReportOwnerCommandRail ReportFastFiveGeometry
open ReportFastSteeringMap

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def winAfter (cut : Nat) (time : Nat) (_ : Raw s n) (j : Fin 5) : Bool :=
  decide (cut≤time ∧ j=2)

theorem winAfter_before (cut a : Nat) (x : Raw s n) (L : a<cut) :
    winAfter cut a x=denySides := by
  funext j
  simp [winAfter,denySides,show ¬cut≤a by omega]

theorem winAfter_after (cut a : Nat) (x : Raw s n) (L : cut≤a) :
    winAfter cut a x=fun j=>decide (j=2) := by
  funext j
  simp [winAfter,L]

theorem winAfter_rival (cut a : Nat) (x : Raw s n) (j : Fin 5) (R : j≠2) :
    winAfter cut a x j=false := by simp [winAfter,R]

noncomputable def prepDriver (d : Sheet) (B : Fin 5→Chart h)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (W : Nat) :
    ReportFastSixPrepTrack.Prepared d hh Q → Fin n → ReportFastSixPrepTrack.Prepared d hh Q :=
  driverStep (ReportFastSixPrepTrack.step d (prepCharts B) B N hh F W)
    (fun z=>mergeSide (ReportFastSixPrepTrack.prepBan d B z.base))

noncomputable def prepStart (d : Sheet) (B : Fin 5→Chart h) (hh : ∃ i,h i=true)
    (x : {y : Raw s n // Cached d hh Q y}) (fallback : Fin n) :
    ReportFastSixPrepTrack.Prepared d hh Q :=
  start (ReportFastSixPrepTrack.nom d (prepCharts B) hh)
    (ReportFastSixPrep.init d hh x) fallback

theorem exit_switch
    (d : Sheet) (B : Fin 5→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (inj : Function.Injective (fun j=>center (B j)))
    (digit : 0<(params d s).digits)
    (W : Nat) (W3 : 3≤W) (Width : ∀ j,(B j).L≤3*W)
    (x : {y : Raw s n // Cached d hh Q y}) (S : ∀ j,StrongSerial d (B j) x.val)
    (fallback : Fin n) (v : List (Fin n)) (e : Fin n) (t : Nat) :
    let next := prepDriver d B N hh F W
    let z₀ := prepStart d B hh x fallback
    let prev := Height.runWord next z₀ v
    let z := next prev e
    ¬ReportFastSixPrepTrack.hit prev.base →
    ReportFastSixPrepTrack.hit z.base →
    let lead := v++[e]
    let P := winAfter (t+lead.length) (s:=s) (n:=n)
    z.base.1.val=rawRun x.val (mappedWord d B P t x.val lead) ∧
    readPC d (B 2) z.base.1.val=(1,1) ∧ FullParked d (B 2) z.base.1.val ∧
    (∀ j,StrongSerial d (B j) z.base.1.val) ∧
    ∀ suffix j,j≠2 →
      ReceiptSuffix d B P x.val (mappedWord d B P t x.val (lead++suffix)) j := by
  dsimp only
  let C := prepCharts B
  let next := prepDriver d B N hh F W
  let z₀ := prepStart d B hh x fallback
  let old := Height.runWord next z₀ v
  let z := next old e
  let u := v++[e]
  let P := winAfter (t+u.length) (s:=s) (n:=n)
  have inc : ∀ j,∃ i,C i=B j := fun j=>⟨j.castSucc,prepCharts_includes B j⟩
  have WW := prepCharts_width B W Width
  have S0 : ∀ i,StrongSerial d (C i) x.val := by
    intro i
    simp only [C,prepCharts]
    split <;> exact S _
  have I0 : ReportFastSixPrepTrack.good d C B hh z₀ :=
    ReportFastSixPrepTrack.start_good d C B N hh F W inc inj G digit W3 WW x S0 fallback
  have closed : ∀ a m, ReportFastSixPrepTrack.good d C B hh a →
      ReportFastSixPrepTrack.good d C B hh (next a m) := by
    intro a m K
    exact ReportFastSixPrepTrack.all_mark d C B N hh F W inc inj G digit W3 WW a _ K
  have I := Height.runWord_of_closed next (ReportFastSixPrepTrack.good d C B hh)
    closed z₀ v I0
  have Z := closed old e I
  intro L H
  change ¬ReportFastSixPrepTrack.hit old.base at L
  change ReportFastSixPrepTrack.hit z.base at H
  obtain ⟨_,PC,Parked⟩ := tracked_driver_finish d B N hh F W old I e L H
  have Base := tracked_driver_run_base d C B N hh F W z₀ u
  have U : Height.runWord next z₀ u=z := by
    simp [u,z,old,Height.runWord,List.foldl_append]
  change (Height.runWord next z₀ u).base=_ at Base
  rw [U] at Base
  change z.base=SequentialMarkClock.run
    (fun a e=>ReportFastSixPrep.step d C N hh F a
      (mergeSide (ReportFastSixPrepTrack.prepBan d B a) e))
    (ReportFastSixPrep.init d hh x) u at Base
  have P0 : ∀ a y,t≤a → a<t+u.length → P a y=denySides :=
    fun a y _ E=>winAfter_before _ a y E
  have Map := prep_run_mapped d C B N hh G F inj (ReportFastSixPrep.init d hh x) u t
  have Profile := mappedWord_policy_prefix d B P (fun _ _=>denySides) t x.val u P0
  have Proj : z.base.1.val=rawRun x.val (mappedWord d B P t x.val u) := by
    rw [Base,Map,ReportFastSixPrepHistory.run_raw]
    change rawRun x.val (mappedWord d B (fun _ _=>denySides) t x.val u)=_
    rw [←Profile]
  have HR := ReportFastSixPrepTrack.step_raw d C B N hh F W old
    (mergeSide (ReportFastSixPrepTrack.prepBan d B old.base) e)
  change z.base.1.val=_ at HR
  rw [←HR] at PC Parked
  refine ⟨Proj,PC,Parked,?_,?_⟩
  · intro j
    exact (prepCharts_includes B j) ▸ (Z.1.1 j.castSucc)
  · intro suffix j _
    apply prepared_mapped_receiptSuffix d C B N hh G F inj inc x u suffix t P P0 _ j
    rw [←Base]
    exact H

/-- The post-cut segment uses the target-win profile at every one
of its physical draws, not just at the ADMIT decision. -/
theorem word_switch
    (d : Sheet) (B : Fin 5→Chart h) (t : Nat) (x : Raw s n)
    (u w : List (Fin n)) :
    let P := winAfter (t+u.length) (s:=s) (n:=n)
    let prep := mappedWord d B (fun _ _=>denySides) t x u
    mappedWord d B P t x (u++w)=
      prep ++ mappedWord d B (fun _ _ j=>decide (j=2)) (t+u.length)
        (rawRun x prep) w := by
  dsimp only
  rw [mappedWord_append]
  rw [mappedWord_policy_prefix d B _ (fun _ _=>denySides) t x u
    (fun a y _ E=>winAfter_before _ a y E)]
  rw [mappedWord_policy_prefix d B _ (fun _ _ j=>decide (j=2))
    (t+u.length) _ w (fun a y E _=>winAfter_after _ a y E)]

end L4.ReportFastReceiptSwitch

import Leader.L4.ReportFastReceiptSwitch
import Leader.L4.ReportFastPreACQTrack
import Leader.L4.ReportFastAcqWins

namespace L4.ReportFastPreACQHandoff
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportFastOwnerSupport ReportFastNominationBridge ReportAdaptiveFibre
open ReportFastFreshReset ReportFastPreACQTrack ReportFastSteeringMap
open ReportFastPrepMapping ReportFastDenySteering ReportFastReceiptSwitch ReportFastFiveGeometry
open ReportFastAcqWins
open ReportLeaseOwner ReportOwnerCommandRail

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

noncomputable def preDriver (d : Sheet) (B : Fin 5→Chart h)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) :
    PreTrack d hh Q → Fin n → PreTrack d hh Q :=
  driverStep (preTrackStep d B 2 N hh F) (fun z=>mergeSide (preBan d B 2 hh z.base))

theorem ban_eq (d : Sheet) (B : Fin 5→Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (inj : Function.Injective (fun j=>center (B j)))
    (z : PreACQBase d hh Q) (e : Fin n) :
    mergeSide (preBan d B 2 hh z) e=steerRaw d B (targetDesired 2) z.raw.val e := by
  let active := fun j=>ReportFastRefractory.armed d (B j) z.raw.val
  let P := targetDesired 2
  have A : activeRaw d B z.raw.val=active :=
    funext (active_eq_armed d B z.raw.val)
  unfold preBan steerRaw
  rw [A]
  change mergeSide (makeBan B active P) e=mergeSide (gateBan B active P) e
  cases H : makeBan B active P e with
  | none =>
    cases K : gateBan B active P e with
    | none => simp [mergeSide,H,K]
    | some a =>
      have J := (gate_ban_spec hh G B inj active P e a).mp K
      have D := (makeBan_spec hh G B inj active P e a).mpr J
      rw [H] at D
      contradiction
  | some a =>
    have J := (makeBan_spec hh G B inj active P e a).mp H
    have K := (gate_ban_spec hh G B inj active P e a).mpr J
    simp [mergeSide,H,K]

theorem run_pre_driver_raw (d : Sheet) (B : Fin 5→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (inj : Function.Injective (fun j=>center (B j)))
    (z : PreTrack d hh Q) (w : List (Fin n)) (t : Nat) :
    (Height.runWord (preDriver d B N hh F) z w).base.raw.val=
      rawRun z.base.raw.val
        (mappedWord d B (fun _ _=>targetDesired 2) t z.base.raw.val w) := by
  induction w generalizing z t with
  | nil => rfl
  | cons e w IH =>
    let m := mergeSide (preBan d B 2 hh z.base) e
    let y := preTrackStep d B 2 N hh F z m
    have Raw := preTrack_raw d B 2 N hh F z m
    have M := ban_eq d B hh G inj z.base e
    change m=_ at M
    change (Height.runWord (preDriver d B N hh F) y w).base.raw.val=
      rawRun (rawNext s z.base.raw.val (steerRaw d B (targetDesired 2) z.base.raw.val e)) _
    rw [IH y (t+1)]
    change y.base.raw.val=_ at Raw
    rw [Raw,M]

theorem from_sixth_reset
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (W : Nat) (W3 : 3≤W) (r : Fin 5→Owner h) (R : Consecutive G r)
    (Width : ∀ j,(charter G (r j)).L≤3*W)
    (x : {y : Raw s n // Cached d hh Q y})
    (S : ∀ j,StrongSerial d (charter G (r j)) x.val)
    (fallback : Fin n) (v : List (Fin n)) (e : Fin n) (t : Nat) :
    let B := fun j=>charter G (r j)
    let next := prepDriver d B N hh F W
    let old := Height.runWord next (prepStart d B hh x fallback) v
    let z := next old e
    ¬ReportFastSixPrepTrack.hit old.base →
    ReportFastSixPrepTrack.hit z.base →
    let pre : PreTrack d hh Q := start (PreACQNom d (B 2) hh) ⟨z.base.1,.live⟩ fallback
    preTrackGood d B 2 hh pre ∧ OwnClear d (B 2) pre.base.raw.val ∧
    ∀ w, let y := Height.runWord (preDriver d B N hh F) pre w
      RivalFence d (B 2) y.base.raw.val := by
  dsimp only
  let B := fun j=>charter G (r j)
  let next := prepDriver d B N hh F W
  let old := Height.runWord next (prepStart d B hh x fallback) v
  let z := next old e
  let pre : PreTrack d hh Q := start (PreACQNom d (B 2) hh) ⟨z.base.1,.live⟩ fallback
  let u := v++[e]
  let P := winAfter (t+u.length) (s:=s) (n:=n)
  have inj := centers_injective_of_roots G B (target_five_incidence G r R).2.1
  intro L H
  obtain ⟨Proj,PC,Parked,Serial,Rec⟩ :=
    exit_switch d B N hh G F inj digit W W3 Width x S fallback v e t L H
  change preTrackGood d B 2 hh pre ∧ OwnClear d (B 2) z.base.1.val ∧ _
  refine ⟨preTrack_init d B 2 N hh G F digit inj z.base.1 PC Serial fallback,
    fun k _ K J=>Parked.1.2.2 k K J,?_⟩
  intro w
  have Init : pre.base.raw.val=z.base.1.val := rfl
  rw [run_pre_driver_raw d B N hh G F inj pre w (t+u.length),Init,Proj]
  have Map := mappedWord_append d B P t x.val u w
  rw [mappedWord_policy_prefix d B P (fun _ _=>targetDesired 2)
    (t+u.length) _ w (fun a y E _=>winAfter_after _ a y E)] at Map
  rw [←ShortOwnerEpochJS.raw_append,←Map]
  exact ReportFastMappedFence.target_rival_fence_of_receipts d N hh G F digit r R P
    (winAfter_rival _) x.val x.property _ (Rec w)

#print axioms run_pre_driver_raw
#print axioms from_sixth_reset
end L4.ReportFastPreACQHandoff

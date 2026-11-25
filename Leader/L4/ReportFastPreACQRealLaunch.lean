import Leader.L4.ReportFastPreACQLaunch
import Leader.L4.ReportFastPreACQHandoff
import Leader.L4.ReportFastAcqTrack

namespace L4.ReportFastPreACQRealLaunch
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportFastFreshReset ReportFastPreACQTrack ReportFastPreACQHandoff
open ReportFastNominationBridge ReportFastAcqWins ReportOwnerAcquireProvenance
open ReportOwnerCommandRail ReportOwnerIssueControl ReportAdaptiveFibre
open ReportByteRows ReportPrelaunchClock
open ReportFastOwnerSupport

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem live_clear_phys (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (z : PreACQBase d hh Q) (e : Fin n)
    (I : preACQGood d C hh z) (L : z.status=.live)
    (O : OwnClear d C z.raw.val) :
    OwnClear d C (preACQStep d C N hh F z e).raw.val := by
  rw [preACQStep_raw]
  rcases (I.2 L).2 with P|P
  · exact own_clear_pre_run d C N hh G F digit z.raw.val z.raw.property
      I.1 O [e] ⟨Nat.ne_of_lt P,trivial⟩
  · exact preacq_empty_clear_step d C N hh F z.raw.val z.raw.property
      (preACQ_legal_issue d C _ I.1 P) O e

theorem first_launch_phys (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (z : PreACQBase d hh Q) (e : Fin n)
    (I : preACQGood d C hh z) (L : z.status=.live)
    (O : OwnClear d C z.raw.val)
    (H : preACQSuccess d hh (preACQStep d C N hh F z e)) :
    e=door C ∧ AtACQIssue d C z.raw.val ∧ LegalIssue d C z.raw.val ∧
      FState d C (preACQStep d C N hh F z e).raw.val 0 64 ∧
      OwnClear d C (preACQStep d C N hh F z e).raw.val := by
  classical
  have P : AtACQIssue d C z.raw.val ∧ e=door C := by
    apply Classical.byContradiction
    intro E
    unfold preACQSuccess at H
    rw [show (preACQStep d C N hh F z e).status=
      if PreACQPose d C (rawNext s z.raw.val e) then .live else .retry by
        simp [preACQStep,L,E]] at H
    split at H <;> contradiction
  have Legal := preACQ_legal_issue d C z.raw.val I.1 P.1
  refine ⟨P.2,P.1,Legal,?_,live_clear_phys d C N hh G F digit z e I L O⟩
  rw [preACQStep_raw,P.2]
  exact (ReportOwnerAcquireProvenance.launch d C hh G F N z.raw.val z.raw.property Legal P.1).2

/-- A live endpoint implies that no earlier mark was past the stop. Thus
own clearance holds on its entire actual earlier live prefix. -/
theorem live_endpoint_clear (d : Sheet) (B : Fin 5→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (B j)))
    (z : PreTrack d hh Q) (H : preTrackGood d B 2 hh z)
    (O : OwnClear d (B 2) z.base.raw.val) (w : List (Fin n))
    (L : (Height.runWord (preDriver d B N hh F) z w).base.status=.live) :
    OwnClear d (B 2) (Height.runWord (preDriver d B N hh F) z w).base.raw.val := by
  induction w generalizing z with
  | nil => exact O
  | cons e w IH =>
    let m := mergeSide (preBan d B 2 hh z.base) e
    let y := preTrackStep d B 2 N hh F z m
    have HY := preTrack_closed d B 2 N hh G F digit inj z m H
    have B0 : y.base=preACQStep d (B 2) N hh F z.base m := by
      unfold y preTrackStep
      exact next_base _ _ _ _ _ _
    have z_live : z.base.status=.live := by
      apply Classical.byContradiction
      intro K
      have St : ∀ q a, q.base.status=z.base.status →
          (preDriver d B N hh F q a).base.status=z.base.status := by
        intro q a E
        unfold preDriver driverStep preTrackStep
        rw [next_base]
        exact (preACQ_sticky d (B 2) N hh F q.base _
          (fun J=>K (E.symm.trans J))).trans E
      have T := Height.runWord_of_closed (preDriver d B N hh F)
        (fun q=>q.base.status=z.base.status) St z (e::w) rfl
      rw [L] at T
      exact K T.symm
    have OY : OwnClear d (B 2) y.base.raw.val := by
      rw [B0]
      exact live_clear_phys d (B 2) N hh G F digit z.base m H.1.1 z_live O
    exact IH y HY OY L

theorem driver_launch_boundary (d : Sheet) (B : Fin 5→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (B j)))
    (z : PreTrack d hh Q) (H : preTrackGood d B 2 hh z)
    (O : OwnClear d (B 2) z.base.raw.val) (w : List (Fin n)) (e : Fin n) :
    let nxt := preDriver d B N hh F
    let old := Height.runWord nxt z w
    let now := nxt old e
    old.base.status=.live →
    preACQSuccess d hh now.base →
    mergeSide (preBan d B 2 hh old.base) e=door (B 2) ∧
    AtACQIssue d (B 2) old.base.raw.val ∧ LegalIssue d (B 2) old.base.raw.val ∧
    FState d (B 2) now.base.raw.val 0 64 ∧ OwnClear d (B 2) now.base.raw.val := by
  dsimp only
  let nxt := preDriver d B N hh F
  let old := Height.runWord nxt z w
  let m := mergeSide (preBan d B 2 hh old.base) e
  let now := nxt old e
  have Old := Height.runWord_of_closed nxt (preTrackGood d B 2 hh)
    (fun a q A=>preTrack_closed d B 2 N hh G F digit inj a _ A) z w H
  intro L E
  have V := live_endpoint_clear d B N hh G F digit inj z H O w L
  have P : now.base=preACQStep d (B 2) N hh F old.base m := by
    unfold now nxt preDriver driverStep preTrackStep
    exact next_base _ _ _ _ _ _
  change preACQSuccess d hh now.base at E
  rw [P] at E
  change m=door (B 2) ∧ AtACQIssue d (B 2) old.base.raw.val ∧
    LegalIssue d (B 2) old.base.raw.val ∧
    FState d (B 2) now.base.raw.val 0 64 ∧ OwnClear d (B 2) now.base.raw.val
  rw [P]
  exact first_launch_phys d (B 2) N hh G F digit old.base m Old.1.1 L V E

open ReportFastReceiptSwitch ReportFastDenySteering ReportFastFiveGeometry ReportLeaseOwner

/-- At the first genuine launch cut after the sixth RESET, the ACQ
tracker has its exact F(64), its own lanes still clear, and the actual
mapped-prefix fence. No new seed word or grant credit is introduced. -/
theorem sixth_reset_launch_seed
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (W : Nat) (W3 : 3≤W) (r : Fin 5→Owner h) (R : Consecutive G r)
    (Width : ∀ j,(charter G (r j)).L≤3*W)
    (x : {y : Raw s n // Cached d hh Q y})
    (S : ∀ j,StrongSerial d (charter G (r j)) x.val)
    (fallback : Fin n) (v : List (Fin n)) (e : Fin n) (t : Nat)
    (w : List (Fin n)) (f : Fin n) :
    let B := fun j=>charter G (r j)
    let next := prepDriver d B N hh F W
    let old := Height.runWord next (prepStart d B hh x fallback) v
    let z := next old e
    ¬ReportFastSixPrepTrack.hit old.base →
    ReportFastSixPrepTrack.hit z.base →
    let pre : PreTrack d hh Q := start (PreACQNom d (B 2) hh) ⟨z.base.1,.live⟩ fallback
    let preOld := Height.runWord (preDriver d B N hh F) pre w
    let preNew := preDriver d B N hh F preOld f
    preOld.base.status=.live →
    preACQSuccess d hh preNew.base →
    ReportFastAcqTrack.On d (B 2) preNew.base.raw.val (.fwd 0) ∧
    RivalFence d (B 2) preNew.base.raw.val := by
  dsimp only
  let B := fun j=>charter G (r j)
  let next := prepDriver d B N hh F W
  let old := Height.runWord next (prepStart d B hh x fallback) v
  let z := next old e
  let pre : PreTrack d hh Q := start (PreACQNom d (B 2) hh) ⟨z.base.1,.live⟩ fallback
  let nxt := preDriver d B N hh F
  let preNew := nxt (Height.runWord nxt pre w) f
  have inj := centers_injective_of_roots G B (target_five_incidence G r R).2.1
  intro L H
  obtain ⟨Good,Own,Every⟩ :=
    from_sixth_reset d N hh G F digit W W3 r R Width x S fallback v e t L H
  intro Live Hit
  obtain ⟨_,_,_,Front,Clear⟩ :=
    driver_launch_boundary d B N hh G F digit inj pre Good Own w f Live Hit
  have New : Height.runWord nxt pre (w++[f])=preNew := by
    simp [preNew,Height.runWord,List.foldl_append]
  have Fr := Every (w++[f])
  dsimp only at Fr
  change RivalFence d (B 2) (Height.runWord nxt pre (w++[f])).base.raw.val at Fr
  rw [New] at Fr
  exact ⟨⟨64,Front,by decide,Clear⟩,Fr⟩

#print axioms sixth_reset_launch_seed
#print axioms driver_launch_boundary
#print axioms live_clear_phys
#print axioms first_launch_phys
#print axioms live_endpoint_clear
end L4.ReportFastPreACQRealLaunch

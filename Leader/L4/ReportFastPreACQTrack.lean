import Leader.L4.ReportFastNominationBridge

namespace L4.ReportFastPreACQTrack
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock
open ReportOwnerCommandRail ReportByteRows ReportRawProjection
open ReportFastFreshReset ReportFastOwnerSupport ReportGateGeometry
open ReportFastNominationBridge ReportAdaptiveFibre ReportFastKernel

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def targetDesired (target : Fin 5) (j : Fin 5) : Bool := decide (j=target)

noncomputable def preBan (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (hh : ∃ i,h i=true) (z : PreACQBase d hh Q) : Fin n→Option (Fin n) :=
  makeBan C (activeRaw d C z.raw.val) (targetDesired target)

def preFiveGood (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (hh : ∃ i,h i=true) (z : PreACQBase d hh Q) : Prop :=
  preACQGood d (C target) hh z ∧ ∀ j,StrongSerial d (C j) z.raw.val

theorem pre_rows (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j))) :
    Rows (preACQStep d (C target) N hh F) (preFiveGood d C target hh)
      (preACQHit d hh) (preACQDebt d (C target) hh) (preBan d C target hh)
      (PreACQNom d (C target) hh) (fun z q=>Spent d C z.raw.val q) := by
  constructor
  · intro z e H
    exact ⟨preACQStep_closed d (C target) N hh G F digit z e H.1,
      fun j=>strong_step d (C j) N hh G F z.raw.val z.raw.property
        (H.2 j) digit e⟩
  · intro z e H L
    change (preACQStep d (C target) N hh F z e).status≠.live
    rw [preACQ_sticky d (C target) N hh F z e L]
    exact L
  · intro z e H L
    have L0 : z.status=.live := by
      change ¬(z.status≠.live) at L
      exact Classical.byContradiction L
    exact (preACQ_all_mark d (C target) N hh G F digit z e H.1 L0).1
  · intro z H _
    exact preACQ_nom_exists d (C target) hh z H.1
  · intro z q H L M
    have L0 : z.status=.live := by
      change ¬(z.status≠.live) at L
      exact Classical.byContradiction L
    exact preACQ_nom_pays d (C target) N hh G F digit z q H.1 L0 M
  · intro z q e H L M E
    have L0 : z.status=.live := by
      change ¬(z.status≠.live) at L
      exact Classical.byContradiction L
    exact preACQ_nom_plateau d (C target) N hh G F digit z q e H.1 L0 M E
  · intro z q a H _ E
    exact ban_mate_spends d N hh G F C z.raw.val z.raw.property H.2
      (activeRaw d C z.raw.val) (targetDesired target) (preBan d C target hh z)
      (makeBan_spec hh G C inj _ _) (activeRaw_sound d C z.raw.val) q a E
  · intro z q e H _ E K
    exact spent_step d N hh G F C z.raw.val z.raw.property H.2 q e K E
  · intro z q _ _ E
    exact spent_unblocked d hh G C inj z.raw.val q (activeRaw d C z.raw.val)
      (targetDesired target) (preBan d C target hh z) (makeBan_spec hh G C inj _ _)
      (activeRaw_sound d C z.raw.val) E

abbrev PreTrack (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n→Prop) :=
  Track (PreACQBase d hh Q) n

def preTrackGood (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (hh : ∃ i,h i=true) (z : PreTrack d hh Q) : Prop :=
  GoodTrack (preFiveGood d C target hh) (preACQHit d hh)
    (PreACQNom d (C target) hh) (fun x q=>Spent d C x.raw.val q) z

noncomputable def preTrackStep (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreTrack d hh Q) (e : Fin n) : PreTrack d hh Q :=
  next (preACQStep d (C target) N hh F) (preACQDebt d (C target) hh)
    (preBan d C target hh) (PreACQNom d (C target) hh) z e

noncomputable def preTrackRank (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (hh : ∃ i,h i=true) (z : PreTrack d hh Q) : Nat :=
  eventRank (preACQDebt d (C target) hh z.base) z.unspent

theorem preTrack_raw (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreTrack d hh Q) (e : Fin n) :
    (preTrackStep d C target N hh F z e).base.raw.val=
      rawNext s z.base.raw.val e := by
  unfold preTrackStep
  rw [next_base]
  rfl

theorem preTrack_closed (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (z : PreTrack d hh Q) (e : Fin n) (H : preTrackGood d C target hh z) :
    preTrackGood d C target hh (preTrackStep d C target N hh F z e) :=
  track_closed _ _ _ _ _ _ _ (pre_rows d C target N hh G F digit inj) z e H

theorem preTrack_idle (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (z : PreTrack d hh Q) (e : Fin n) (H : preTrackGood d C target hh z)
    (L : ¬preACQHit d hh z.base) :
    preTrackRank d C target hh (preTrackStep d C target N hh F z e)≤
      preTrackRank d C target hh z :=
  original_rank_idle _ _ _ _ _ _ _ (pre_rows d C target N hh G F digit inj) z e H L

theorem preTrack_nominate (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (z : PreTrack d hh Q) (H : preTrackGood d C target hh z)
    (L : ¬preACQHit d hh z.base) :
    ∃ a e,mergeSide (preBan d C target hh z.base) e=a ∧
      preTrackRank d C target hh (preTrackStep d C target N hh F z a)<
        preTrackRank d C target hh z := by
  have R := service_phase_nominate _ _ _ _ _ _ _
    (pre_rows d C target N hh G F digit inj)
  obtain ⟨a,e,E,P⟩ := R z H ((live_iff (preACQHit d hh) z).mpr L)
  exact ⟨a,e,E,eventRank_progress P⟩

theorem preTrack_init (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (C j)))
    (x : {x : Raw s n // Cached d hh Q x})
    (PC : readPC d (C target) x.val=(1,1))
    (S : ∀ j,StrongSerial d (C j) x.val) (q : Fin n) :
    preTrackGood d C target hh
      (start (PreACQNom d (C target) hh) (⟨x,.live⟩ : PreACQBase d hh Q) q) := by
  apply start_good _ _ _ _ _ _ _ (pre_rows d C target N hh G F digit inj)
  refine ⟨⟨S target,fun _=>?_⟩,S⟩
  unfold PreACQPose
  rw [PC]
  exact ⟨by decide,.inl (by unfold acqOp; omega)⟩

theorem preTrack_budget (d : Sheet) (C : Fin 5→Chart h) (target : Fin 5)
    (hh : ∃ i,h i=true) (z : PreTrack d hh Q)
    (H : preTrackGood d C target hh z) :
    preTrackRank d C target hh z≤
      2*(((params d s).digits+1)*commandCap (C target).L+1)+1 := by
  have D := preACQ_debt_bound d (C target) hh z.base H.1.1
  unfold preTrackRank eventRank
  cases z.unspent <;> simp <;> omega

-- No mapped mark can land on an actually forbidden physical label.
theorem pre_image_allowed (ban : Fin n→Option (Fin n))
    (D : DisjointPairs ban) (e : Fin n) : ban (mergeSide ban e)=none := by
  cases H : ban e with
  | none => simp [mergeSide,H]
  | some a => simpa [mergeSide,H] using D.allowed_target e a H

-- The actual target race-1 incoming label is forbidden, not merely
-- discouraged. This uses the same map for the other four owners.
theorem target_first_incoming_forbidden (d : Sheet)
    (C : Fin 5→Chart h) (target : Fin 5) (hh : ∃ i,h i=true)
    (G : GapInput h) (inj : Function.Injective (fun j=>center (C j)))
    (z : PreACQBase d hh Q)
    (H : healthyAdmit (params d s) (tok d (C target) z.raw.val ((C target).a+2)))
    (R : (tok d (C target) z.raw.val ((C target).a+2)).race=1) :
    preBan d C target hh z (out (C target) ((C target).a+1))=
      some (out (C target) ((C target).a+2)) := by
  classical
  have A : activeRaw d C z.raw.val target=true := by
    simp [activeRaw,H,R]
  unfold preBan
  apply (makeBan_spec hh G C inj _ _ _ _).mpr
  refine ⟨target,A,?_,?_⟩
  · simpa [targetDesired] using (physical_labels (C target)).1
  · simpa [targetDesired] using (physical_labels (C target)).2

theorem target_first_not_incoming (d : Sheet)
    (C : Fin 5→Chart h) (target : Fin 5) (hh : ∃ i,h i=true)
    (G : GapInput h) (inj : Function.Injective (fun j=>center (C j)))
    (z : PreACQBase d hh Q)
    (H : healthyAdmit (params d s) (tok d (C target) z.raw.val ((C target).a+2)))
    (R : (tok d (C target) z.raw.val ((C target).a+2)).race=1)
    (e : Fin n) :
    mergeSide (preBan d C target hh z) e≠out (C target) ((C target).a+1) := by
  let b := preBan d C target hh z
  have D : DisjointPairs b :=
    pairs_from_centers hh G C inj _ _ _ (makeBan_spec hh G C inj _ _)
  have F := target_first_incoming_forbidden d C target hh G inj z H R
  intro E
  have K := pre_image_allowed b D e
  change mergeSide b e=out (C target) ((C target).a+1) at E
  rw [E] at K
  change b (out (C target) ((C target).a+1))=some _ at F
  rw [F] at K
  contradiction

#print axioms preTrack_init
#print axioms preTrack_closed
#print axioms preTrack_nominate
#print axioms preTrack_idle
#print axioms preTrack_budget
end L4.ReportFastPreACQTrack

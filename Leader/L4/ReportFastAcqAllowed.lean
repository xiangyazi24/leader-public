import Leader.L4.ReportFastAcqTrack
import Leader.L4.ReportFastAllowedCredit
import Leader.L4.ReportAdaptiveRank

namespace L4.ReportFastAcqAllowed
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportOwnerReverseControl
open ReportOwnerCommandRail ReportFastOwnerSupport
open ReportFastNominationBridge ReportAdaptiveFibre ReportFastKernel
open ReportFastAcqTrack

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop} {Z : Type}
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

noncomputable def bans (d : Sheet) (B : Fin 5→Chart h) (desired : Fin 5→Bool)
    (raw : Z→Raw s n) (x : Z) : Fin n→Option (Fin n) :=
  makeBan B (activeRaw d B (raw x)) desired

/-- The pre-existing environment may contain a chronology of mapped
driver draws. Neither closure nor the ACQ fence is required on a banned
label. Physical projection is required only on those same marks. -/
structure Relift (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (B : Fin 5→Chart h) (desired : Fin 5→Bool)
    (Env : Z→Prop) (raw : Z→Raw s n) (cur : Z→Cursor)
    (step : Z→Fin n→Z) (Q : Raw s n→Prop) : Prop where
  stable : ∀ z e, Env z→bans d B desired raw z e=none→Env (step z e)
  raw_step : ∀ z e, Env z→bans d B desired raw z e=none→raw (step z e)=rawNext s (raw z) e
  cursor_step : ∀ z e, Env z→bans d B desired raw z e=none→cur (step z e)=ReportFastAcqTrack.next C e (cur z)
  cached : ∀ z,Env z→Cached d hh Q (raw z)
  serial : ∀ z,Env z→∀ j,StrongSerial d (B j) (raw z)
  fence : ∀ z e,Env z→bans d B desired raw z e=none→ReportFastAcqWins.DepartureFence d C (raw z) e

theorem allowed_rows (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (B : Fin 5→Chart h) (desired : Fin 5→Bool)
    (inj : Function.Injective (fun j=>center (B j)))
    (Env : Z→Prop) (raw : Z→Raw s n) (cur : Z→Cursor)
    (step : Z→Fin n→Z) (R : Relift d C hh B desired Env raw cur step Q) :
    ReportFastAllowedCredit.Rows step (fun z=>Env z ∧ On d C (raw z) (cur z))
      (fun z=>cur z=.done) (fun z=>ReportFastAcqTrack.debt C (cur z))
      (bans d B desired raw) (fun z q=>ReportFastAcqTrack.label C (cur z)=some q)
      (fun z q=>Spent d B (raw z) q) := by
  constructor
  · intro z _
    exact pairs_from_centers hh G B inj _ _ _ (makeBan_spec hh G B inj _ _)
  · intro z e H A
    refine ⟨R.stable z e H.1 A,?_⟩
    rw [R.raw_step z e H.1 A,R.cursor_step z e H.1 A]
    exact raw_on_step d C N hh G F digit _ (R.cached z H.1) _ H.2 e (R.fence z e H.1 A)
  · intro z e H A Hit
    rw [R.cursor_step z e H.1 A,Hit]
    rfl
  · intro z e H A _
    rw [R.cursor_step z e H.1 A]
    exact debt_idle C _ (on_fit d C _ _ H.2) _
  · intro z _ L
    cases E : cur z with
    | done => exact (L E).elim
    | fwd k => exact ⟨out C k,rfl⟩
    | rev k => exact ⟨inEdge C k,rfl⟩
  · intro z q H A _ P
    rw [R.cursor_step z q H.1 A]
    exact physical_pays C _ (on_fit d C _ _ H.2) q P
  · intro z q e H A _ P E
    rw [R.cursor_step z e H.1 A] at E ⊢
    exact (plateau_label C _ (on_fit d C _ _ H.2) e E).trans P
  · intro z q a H _ A
    have Dr := pairs_from_centers hh G B inj (activeRaw d B (raw z))
      desired (bans d B desired raw z) (makeBan_spec hh G B inj _ _)
    rw [R.raw_step z a H.1 (Dr.allowed_target q a A)]
    exact ban_mate_spends d N hh G F B _ (R.cached z H.1) (R.serial z H.1)
      (activeRaw d B (raw z)) desired (bans d B desired raw z)
      (makeBan_spec hh G B inj _ _) (activeRaw_sound d B _) q a A
  · intro z q e H A _ P E
    rw [R.raw_step z e H.1 A]
    exact spent_step d N hh G F B _ (R.cached z H.1) (R.serial z H.1) q e E P
  · intro z q _ _ P
    exact spent_unblocked d hh G B inj (raw z) q (activeRaw d B (raw z)) desired
      (bans d B desired raw z) (makeBan_spec hh G B inj _ _) (activeRaw_sound d B _) P


noncomputable def driver (C : Chart h) (step : Z→Fin n→Z)
    (bar : Z→Fin n→Option (Fin n)) (cur : Z→Cursor)
    (z : Track Z n) (e : Fin n) : Track Z n :=
  ReportFastNominationBridge.next step (fun x=>ReportFastAcqTrack.debt C (cur x)) bar
    (fun x q=>ReportFastAcqTrack.label C (cur x)=some q) z (mergeSide (bar z.base) e)

theorem driver_mean (C : Chart h) (step : Z→Fin n→Z)
    (Env : Z→Prop) (raw : Z→Raw s n) (cur : Z→Cursor)
    (d : Sheet) (B : Fin 5→Chart h) (desired : Fin 5→Bool)
    (R : ReportFastAllowedCredit.Rows step (fun z=>Env z ∧ On d C (raw z) (cur z))
      (fun z=>cur z=.done) (fun z=>ReportFastAcqTrack.debt C (cur z))
      (bans d B desired raw) (fun z q=>ReportFastAcqTrack.label C (cur z)=some q)
      (fun z q=>Spent d B (raw z) q))
    (z : Track Z n)
    (H : GoodTrack (fun z=>Env z ∧ On d C (raw z) (cur z)) (fun z=>cur z=.done)
      (fun z q=>ReportFastAcqTrack.label C (cur z)=some q) (fun z q=>Spent d B (raw z) q) z) :
    Height.IIDExpectedHittingTimeAtMost (driver C step (bans d B desired raw) cur)
      (fun y=>cur y.base=.done) z
      (n*eventRank (ReportFastAcqTrack.debt C (cur z.base)) z.unspent) := by
  apply ReportAdaptiveFibre.nominated_mean (driver C step (bans d B desired raw) cur)
    (GoodTrack (fun z=>Env z ∧ On d C (raw z) (cur z)) (fun z=>cur z=.done)
      (fun z q=>ReportFastAcqTrack.label C (cur z)=some q) (fun z q=>Spent d B (raw z) q))
    (fun y=>cur y.base=.done) (fun y=>eventRank (ReportFastAcqTrack.debt C (cur y.base)) y.unspent) _ z H
  constructor
  · intro x e X
    exact ReportFastAllowedCredit.track_step _ _ _ _ _ _ _ R x _
      X (ReportFastRawRelift.allowed_after_merge _ (R.pairs _ X.1) e)
  · intro x e X L
    exact ReportFastAllowedCredit.driver_rank_idle _ _ _ _ _ _ _ R x e X L
  · intro x X L
    obtain ⟨a,e,E,P⟩ := ReportFastAllowedCredit.driver_rank_nominate _ _ _ _ _ _ _ R x X L
    refine ⟨e,?_⟩
    unfold driver
    rw [E]
    exact P

theorem launch_mean (C : Chart h) (step : Z→Fin n→Z)
    (Env : Z→Prop) (raw : Z→Raw s n) (cur : Z→Cursor)
    (d : Sheet) (B : Fin 5→Chart h) (desired : Fin 5→Bool)
    (R : ReportFastAllowedCredit.Rows step (fun z=>Env z ∧ On d C (raw z) (cur z))
      (fun z=>cur z=.done) (fun z=>ReportFastAcqTrack.debt C (cur z))
      (bans d B desired raw) (fun z q=>ReportFastAcqTrack.label C (cur z)=some q)
      (fun z q=>Spent d B (raw z) q))
    (z : Z) (q : Fin n) (A : Env z) (K : cur z=.fwd 0)
    (F : ReportOwnerAcquireProvenance.FState d C (raw z) 0 64)
    (O : ReportFastAcqWins.OwnClear d C (raw z)) :
    Height.IIDExpectedHittingTimeAtMost (driver C step (bans d B desired raw) cur)
      (fun y=>cur y.base=.done)
      (start (fun z q=>ReportFastAcqTrack.label C (cur z)=some q) z q)
      (n*(4*C.L+1)) := by
  have I : On d C (raw z) (cur z) := by rw [K]; exact ⟨64,F,by decide,O⟩
  have T := ReportFastAllowedCredit.start_good _ _ _ _ _ _ _ R z q ⟨A,I⟩
  have M := driver_mean C step Env raw cur d B desired R _ T
  simpa only [start,K,eventRank,ReportFastAcqTrack.debt,ReportFastAcqWins.fDebt,
    Nat.sub_zero,Bool.toNat_true,←Nat.mul_assoc] using M

#print axioms allowed_rows
#print axioms driver_mean
#print axioms launch_mean
end L4.ReportFastAcqAllowed

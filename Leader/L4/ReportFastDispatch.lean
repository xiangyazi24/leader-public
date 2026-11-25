import Leader.L4.ReportFastSplice
import Leader.L4.ReportFastRefractoryAdapter
import Leader.L4.ReportFastAcqPrefix
import Leader.L4.ReportFastPreACQRealLaunch
import Leader.L4.ReportFastPostACQContext
import Leader.L4.ReportWriteRailSupplier

namespace L4.ReportFastDispatch
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportPrelaunchAllOwners
open ReportOwnerCommandRail ReportOwnerIssueControl ReportOwnerAcquireProvenance
open ReportFastOwnerSupport ReportFastFiveGeometry ReportLeaseOwner
open ReportGoodEightBank ReportGoodEightCut ReportByteRows
open ReportFastFreshReset ReportFastPreACQTrack ReportFastAcqWins
open ReportFastEarlyPacket ReportFastPreparedMean ReportFastReceiptSwitch
open ReportFastNominationBridge ReportFastDenySteering ReportFastSteeringMap
open ReportAdaptiveFibre ReportFastKernel ReportFastItem10Assembly
open ReportFastRawEvent ReportGateGeometry
open ReportGenerationAncestry (centre)
open ReportFastSplice

set_option maxRecDepth 16000
set_option maxHeartbeats 16000000
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {s n : Nat} {h : Fin n→Bool}


/-- The ordinary ambient geometry, not an extra service supplier.
    K may be as large as the exact residual cap permits. -/
structure Setup (d : Sheet) (hh : ∃ i,h i=true) (P : Raw s n→Prop)
    (G : GapInput h) (rs : Fin 5→Owner h)
    (j : ReportFastItem10Assembly.Target h) (w W K : Nat) where
  N : 1<n
  Spos : 0<s
  F : Fibre (h:=h) d P
  consecutive : Consecutive G rs
  W3 : 3≤W
  width : ∀ i,(charter G (rs i)).L≤3*W
  wide : ∀ i,3*w≤(charter G (rs i)).L
  left : (params d s).digits≤(charter G (rs 2)).a
  mid : (params d s).digits≤(charter G (rs 2)).b
  right : (params d s).digits≤(charter G (rs 2)).L-
    ((charter G (rs 2)).a+(charter G (rs 2)).b)
  cap : 29*(params d s).digits*W+(12*W+1)+
    21*(params d s).digits*W+K≤112*(params d s).digits*W
  late : ReportFastSplice.LateSealCommit d hh P G (rs 2) j K

variable {d : Sheet} {hh : ∃ i,h i=true} {P : Raw s n→Prop}
variable {G : GapInput h} {rs : Fin 5→Owner h}
variable {j : ReportFastItem10Assembly.Target h} {w W K : Nat}
variable (E : Setup d hh P G rs j w W K)

abbrev Setup.B (_E : Setup d hh P G rs j w W K) : Fin 5→Chart h :=
  fun i=>charter G (rs i)
abbrev Setup.C (E : Setup d hh P G rs j w W K) := prepCharts E.B
abbrev Setup.t (_E : Setup d hh P G rs j w W K) := (params d s).digits

theorem Setup.digit : 0<E.t :=
  ReportPrelaunchDoorProducer.digits_positive d E.Spos

theorem Setup.mem : ∀ i,E.B i∈ownerCharts G :=
  (target_five_incidence G rs E.consecutive).1

theorem Setup.inj : Function.Injective (fun i=>center (E.B i)) :=
  centers_injective_of_roots G E.B
    (target_five_incidence G rs E.consecutive).2.1

theorem Setup.inc : ∀ i,∃ k,E.C k=E.B i :=
  fun i=>⟨i.castSucc,prepCharts_includes E.B i⟩

theorem Setup.cwidth : ∀ i,(E.C i).L≤3*W :=
  prepCharts_width E.B W E.width

include E in
theorem Setup.bankStep (x : Raw s n) (e : Fin n)
    (H : GoodEightBank d hh P G x) :
    GoodEightBank d hh P G (rawNext s x e) :=
  good_bank_closed d E.N hh G E.F E.digit
    (ReportWriteRailSupplier.rail_supplier d E.N hh G E.F E.digit) x e H

theorem Setup.serial (x : Raw s n) (H : GoodEightBank d hh P G x)
    (i : Fin 5) : StrongSerial d (E.B i) x :=
  serial_from_bank d E.N hh G E.F E.digit x H (E.B i) (E.mem i)

theorem Setup.cserial (x : Raw s n) (H : GoodEightBank d hh P G x)
    (i : Fin 6) : StrongSerial d (E.C i) x := by
  unfold Setup.C prepCharts
  split <;> exact E.serial x H _

def cachedOfBank (x : Raw s n) (H : GoodEightBank d hh P G x) :
    {y : Raw s n // Cached d hh P y} :=
  ⟨x,H.2.1.1.1.1⟩

-- The fixed fallback is a physical label; no scheduling assumption.
abbrev Setup.fallback (_E : Setup d hh P G rs j w W K) : Fin n := j.val

abbrev Setup.rStep (E : Setup d hh P G rs j w W K) :=
  ReportFastSixPrepTrack.step d E.C E.B E.N hh E.F W
abbrev Setup.rDrive (E : Setup d hh P G rs j w W K) :=
  prepDriver d E.B E.N hh E.F W
abbrev Setup.rStart (E : Setup d hh P G rs j w W K)
    (x : {y : Raw s n // Cached d hh P y}) := prepStart d E.B hh x E.fallback
abbrev Setup.pStep (E : Setup d hh P G rs j w W K) :=
  preTrackStep d E.B 2 E.N hh E.F
abbrev Setup.pStart (E : Setup d hh P G rs j w W K)
    (x : {y : Raw s n // Cached d hh P y}) : PreTrack d hh P :=
  start (PreACQNom d (E.B 2) hh) ⟨x,.live⟩ E.fallback

abbrev Setup.aBar (E : Setup d hh P G rs j w W K) :
    ReportFastAcqDriver.Trace s n→Fin n→Option (Fin n) :=
  ReportFastAcqAllowed.bans d E.B (targetDesired 2) ReportFastAcqDriver.Trace.raw
abbrev Setup.aNom (E : Setup d hh P G rs j w W K) :=
  fun (z : ReportFastAcqDriver.Trace s n) q=>
    ReportFastAcqTrack.label (E.B 2) z.cur=some q
abbrev Setup.aDebt (E : Setup d hh P G rs j w W K) :=
  fun (z : ReportFastAcqDriver.Trace s n)=>ReportFastAcqTrack.debt (E.B 2) z.cur
abbrev Setup.aHit (_E : Setup d hh P G rs j w W K) :=
  fun (z : ReportFastAcqDriver.Trace s n)=>z.cur=.done
abbrev Setup.aStep (E : Setup d hh P G rs j w W K) :=
  ReportFastNominationBridge.next (ReportFastAcqDriver.step (E.B 2))
    E.aDebt E.aBar E.aNom
abbrev Setup.aStart (E : Setup d hh P G rs j w W K) (x : Raw s n) :
    ReportFastAcqPrefix.Z s n :=
  start E.aNom (⟨x,.fwd 0,[]⟩ : ReportFastAcqDriver.Trace s n) E.fallback

def Setup.aEnv (E : Setup d hh P G rs j w W K)
    (z : ReportFastAcqDriver.Trace s n) : Prop :=
  GoodEightBank d hh P G z.raw ∧ RivalFuture d E.B z.raw

def Setup.aGood (E : Setup d hh P G rs j w W K)
    (z : ReportFastAcqPrefix.Z s n) : Prop :=
  GoodTrack (fun x=>E.aEnv x ∧ ReportFastAcqTrack.On d (E.B 2) x.raw x.cur)
    E.aHit E.aNom (fun x q=>Spent d E.B x.raw q) z

/-- Same constant target-win profile as PREACQ. A permitted physical
    mark is its own driver preimage. -/
theorem Setup.steerFixed (x : Raw s n) (H : GoodEightBank d hh P G x)
    (e : Fin n) (A : makeBan E.B (activeRaw d E.B x) (targetDesired 2) e=none) :
    steerRaw d E.B (targetDesired 2) x e=e := by
  let z : PreACQBase d hh P := ⟨cachedOfBank x H,.live⟩
  have M := ReportFastPreACQHandoff.ban_eq d E.B hh G E.inj z e
  change mergeSide (makeBan E.B (activeRaw d E.B x) (targetDesired 2)) e=
    steerRaw d E.B (targetDesired 2) x e at M
  exact M.symm.trans (easy_allowed _ e A)

/-- This uses the checked allowed-credit adapter, not observed_rows
    with a false ordinary-closed departure fence. -/
theorem Setup.aRelift :
    ReportFastAcqAllowed.Relift d (E.B 2) hh E.B (targetDesired 2)
      E.aEnv ReportFastAcqDriver.Trace.raw ReportFastAcqDriver.Trace.cur
      (ReportFastAcqDriver.step (E.B 2)) P := by
  constructor
  · intro z e H A
    exact ⟨E.bankStep z.raw e H.1,
      future_step d E.B z.raw H.2 e (E.steerFixed z.raw H.1 e A)⟩
  · intros; rfl
  · intros; rfl
  · intro z H
    exact H.1.2.1.1.1.1
  · intro z H i
    exact E.serial z.raw H.1 i
  · intro z e H _ k q F0 eq he
    exact future_now d E.B z.raw H.2

theorem Setup.aRows :
    ReportFastAllowedCredit.Rows (ReportFastAcqDriver.step (E.B 2))
      (fun x=>E.aEnv x ∧ ReportFastAcqTrack.On d (E.B 2) x.raw x.cur)
      E.aHit E.aDebt E.aBar E.aNom (fun x q=>Spent d E.B x.raw q) :=
  ReportFastAcqAllowed.allowed_rows d (E.B 2) E.N hh G E.F E.digit E.B
    (targetDesired 2) E.inj E.aEnv _ _ _ E.aRelift

theorem Setup.aStepBase (z : ReportFastAcqPrefix.Z s n) (e : Fin n) :
    (E.aStep z e).base=ReportFastAcqDriver.step (E.B 2) z.base e :=
  next_base _ _ _ _ _ _

theorem Setup.aStartGood (x : Raw s n) (B : GoodEightBank d hh P G x)
    (R : RivalFuture d E.B x)
    (A : ReportFastAcqTrack.On d (E.B 2) x (.fwd 0)) :
    E.aGood (E.aStart x) :=
  ReportFastAllowedCredit.start_good _ _ _ _ _ _ _ E.aRows _ E.fallback
    ⟨⟨B,R⟩,A⟩

theorem Setup.aStepGood (z : ReportFastAcqPrefix.Z s n) (e : Fin n)
    (H : E.aGood z) (A : E.aBar z.base e=none) :
    E.aGood (E.aStep z e) :=
  ReportFastAllowedCredit.track_step _ _ _ _ _ _ _ E.aRows z e H A

abbrev Setup.rDebt (E : Setup d hh P G rs j w W K)
    (z : ReportFastSixPrepTrack.Prepared d hh P) :=
  ReportFastSixPrep.debt d E.C hh W z.base

def Setup.rRank (E : Setup d hh P G rs j w W K)
    (z : ReportFastSixPrepTrack.Prepared d hh P) :=
  eventRank (E.rDebt z-pubReserve E.t W) z.unspent

abbrev Setup.pRank (E : Setup d hh P G rs j w W K) : PreTrack d hh P→Nat := preTrackRank d E.B 2 hh
abbrev Setup.aRank (E : Setup d hh P G rs j w W K)
    (z : ReportFastAcqPrefix.Z s n) := eventRank (E.aDebt z.base) z.unspent

theorem Setup.rFloor (z : ReportFastSixPrepTrack.Prepared d hh P) :
    pubReserve E.t W≤E.rDebt z := by
  cases H : z.base.2 with
  | none => simp [Setup.rDebt,ReportFastSixPrep.debt,H]
  | some p =>
    rcases p with ⟨i,st⟩
    simp only [Setup.rDebt,ReportFastSixPrep.debt,H,prepDebt]
    exact Nat.le_add_left _ _

theorem Setup.rRankEq (z : ReportFastSixPrepTrack.Prepared d hh P) :
    E.rRank z+2*pubReserve E.t W=eventRank (E.rDebt z) z.unspent := by
  have H := E.rFloor z
  unfold Setup.rRank eventRank
  omega

theorem Setup.rRows :
    ReportFastNominationBridge.Rows (ReportFastSixPrep.step d E.C E.N hh E.F)
      (ReportFastSixPrep.Inv d E.C hh) ReportFastSixPrepTrack.hit
      (ReportFastSixPrep.debt d E.C hh W) (ReportFastSixPrepTrack.prepBan d E.B)
      (ReportFastSixPrepTrack.nom d E.C hh) (fun z q=>Spent d E.B z.1.val q) :=
  ReportFastSixPrepTrack.prep_rows d E.C E.B E.inc E.inj E.N hh G E.F
    E.digit W E.W3 E.cwidth

theorem Setup.rIdle (z : ReportFastSixPrepTrack.Prepared d hh P) (e : Fin n)
    (H : ReportFastSixPrepTrack.good d E.C E.B hh z)
    (L : ¬ReportFastSixPrepTrack.hit z.base) :
    E.rRank (E.rStep z e)≤E.rRank z := by
  have B := original_rank_idle _ _ _ _ _ _ _ E.rRows z e H L
  have X := E.rRankEq z
  have Y := E.rRankEq (E.rStep z e)
  change eventRank (E.rDebt (E.rStep z e)) (E.rStep z e).unspent≤
    eventRank (E.rDebt z) z.unspent at B
  omega

theorem Setup.rNominate (z : ReportFastSixPrepTrack.Prepared d hh P)
    (H : ReportFastSixPrepTrack.good d E.C E.B hh z)
    (L : ¬ReportFastSixPrepTrack.hit z.base) :
    ∃ a e,mergeSide (ReportFastSixPrepTrack.prepBan d E.B z.base) e=a ∧
      E.rRank (E.rStep z a)<E.rRank z := by
  obtain ⟨a,e,A,B⟩ := service_phase_nominate _ _ _ _ _ _ _ E.rRows z H
    ((live_iff ReportFastSixPrepTrack.hit z).mpr L)
  have Q := eventRank_progress B
  have X := E.rRankEq z
  have Y := E.rRankEq (E.rStep z a)
  change eventRank (E.rDebt (E.rStep z a)) (E.rStep z a).unspent<
    eventRank (E.rDebt z) z.unspent at Q
  exact ⟨a,e,A,by omega⟩

theorem Setup.rCap (z : ReportFastSixPrepTrack.Prepared d hh P)
    (H : ReportFastSixPrepTrack.good d E.C E.B hh z) :
    E.rRank z≤924*E.t*W+1 := by
  have D := ReportFastSixPrep.debt_bound d E.C hh W E.W3 E.cwidth E.digit z.base H.1
  have R := E.rRankEq z
  change E.rDebt z≤518*E.t*W at D
  unfold eventRank pubReserve at R
  cases U : z.unspent <;> simp [U,Nat.mul_assoc] at R D ⊢ <;> omega

theorem Setup.pCap (z : PreTrack d hh P) (H : preTrackGood d E.B 2 hh z) :
    E.pRank z≤29*E.t*W :=
  Nat.le_trans (preTrack_budget d E.B 2 hh z H)
    (pre_budget E.t W (E.B 2).L E.digit E.W3 (E.width 2))

theorem Setup.pPos (z : PreTrack d hh P) (L : z.base.status=.live) :
    0<E.pRank z := by
  unfold Setup.pRank preTrackRank eventRank
  rw [preACQ_debt_live d (E.B 2) hh z.base L]
  omega

theorem Setup.aCap (z : ReportFastAcqPrefix.Z s n) (H : E.aGood z) :
    E.aRank z≤12*W+1 := by
  have F := ReportFastAcqTrack.on_fit d (E.B 2) z.base.raw z.base.cur H.1.2
  have D : E.aDebt z.base≤2*(E.B 2).L := by
    cases C : z.base.cur with
    | done => simp [Setup.aDebt,C,ReportFastAcqTrack.debt]
    | fwd k => simp [Setup.aDebt,C,ReportFastAcqTrack.debt,fDebt]
    | rev k =>
      rw [C] at F
      change k<(E.B 2).L at F
      simp only [Setup.aDebt,C,ReportFastAcqTrack.debt,dDebt]
      omega
  have W0 : (E.B 2).L≤3*W := E.width 2
  unfold Setup.aRank eventRank
  cases U : z.unspent <;> simp <;> omega

theorem Setup.aPos (z : ReportFastAcqPrefix.Z s n) (H : E.aGood z)
    (L : z.base.cur≠.done) : 0<E.aRank z := by
  obtain ⟨a,e,A,B⟩ := ReportFastAllowedCredit.driver_rank_nominate _ _ _ _ _ _ _
    E.aRows z H L
  change E.aRank (E.aStep z a)<E.aRank z at B
  omega

/-- One sum of ghost phases. No tag is added to the raw protocol.
    Invalid is used only to totalize functions outside Good. -/
inductive Core (d : Sheet) (hh : ∃ i,h i=true)
    (P : Raw s n→Prop) (G : GapInput h) (rs : Fin 5→Owner h) where
  | reset (z : ReportFastSixPrepTrack.Prepared d hh P)
  | preacq (z : PreTrack d hh P)
  | acq (issue : Raw s n) (z : ReportFastAcqPrefix.Z s n)
  | postacq (A : ReportFastPostACQ.Context d hh P G (rs 2)) (u : List (Fin n))
  | late (A : ReportFastPostACQ.Context d hh P G (rs 2)) (u : List (Fin n)) (x : Raw s n)
  | invalid (x : Raw s n)

abbrev Setup.State (_E : Setup d hh P G rs j w W K) := Core d hh P G rs

def Core.raw : Core d hh P G rs→Raw s n
  | .reset z => z.base.1.val
  | .preacq z => z.base.raw.val
  | .acq _ z => z.base.raw
  | .postacq A u => rawRun A.base u
  | .late _ _ x | .invalid x => x

def Core.phase : Core d hh P G rs→Nat
  | .reset _ => 0
  | .preacq _ => 1
  | .acq _ _ => 2
  | .postacq _ _ => 3
  | .late _ _ _ => 4
  | .invalid _ => 5

def Core.resetIndex : Core d hh P G rs→Option (Fin 6)
  | .reset z => z.base.2.map Prod.fst
  | _ => none

def Setup.cost (E : Setup d hh P G rs j w W K) : E.State→Nat
  | .reset z => E.rRank z
  | .preacq z => E.pRank z
  | .acq _ z => E.aRank z
  | .postacq A u => ReportFastPostACQ.loopDebt A (rawRun A.base u)
  | .late A u x => E.late.rank A u x
  | .invalid _ => 0

def Setup.active (E : Setup d hh P G rs j w W K) : E.State→Fin 5→Bool
  | .reset z => activeRaw d E.B z.base.1.val
  | .preacq z => activeRaw d E.B z.base.raw.val
  | .acq _ z => activeRaw d E.B z.base.raw
  | _ => fun _=>false

def Core.desired : Core d hh P G rs→Fin 5→Bool
  | .reset _ => denySides
  | .preacq _ | .acq _ _ => targetDesired 2
  | _ => fun _=>false

def Setup.bar (E : Setup d hh P G rs j w W K) (x : E.State) :=
  makeBan E.B (E.active x) x.desired

/-- All flight marks are actual, including all holds.
    The old issue is retained, never reconstructed at WAIT. -/
def Setup.anchor (E : Setup d hh P G rs j w W K)
    (issue : Raw s n) (z : ReportFastAcqPrefix.Z s n) : Prop :=
  FirstCut d hh P G issue ∧ LegalIssue d (E.B 2) issue ∧
  AtACQIssue d (E.B 2) issue ∧
  FencedBefore d (E.B 2) (rawNext s issue (door (E.B 2))) z.base.draws ∧
  z.base.raw=rawRun (rawNext s issue (door (E.B 2))) z.base.draws

def Setup.Good (E : Setup d hh P G rs j w W K) (x : E.State) : Prop :=
  GoodEightBank d hh P G x.raw ∧
  match x with
  | .reset z =>
    ReportFastSixPrepTrack.good d E.C E.B hh z ∧
    ¬ReportFastSixPrepTrack.hit z.base ∧
    ∃ x0 : {y : Raw s n // Cached d hh P y},
      (∀ i,StrongSerial d (E.B i) x0.val) ∧
      ∃ v,z=Height.runWord E.rDrive (E.rStart x0) v
  | .preacq z => WinTrackGood d E.B 2 hh z ∧ z.base.status=.live ∧
      OwnClear d (E.B 2) z.base.raw.val ∧ RivalFuture d E.B z.base.raw.val
  | .acq issue z => E.aGood z ∧ z.base.cur≠.done ∧ E.anchor issue z
  | .postacq A u => ReportFastPostACQ.UntilSeal A u ∧
      ReportFastPostACQ.Active A (rawRun A.base u) ∧
      ReportFastPostACQ.loopDebt A (rawRun A.base u)≤21*E.t*W
  | .late A u x => ReportFastPostACQ.UntilSeal A u ∧
      ReportFastPostACQ.Stop A (rawRun A.base u) ∧ E.late.good A u x
  | .invalid _ => False

def Setup.restore (E : Setup d hh P G rs j w W K) (x : Raw s n) : E.State :=
  if H : GoodEightBank d hh P G x then .reset (E.rStart (cachedOfBank x H))
  else .invalid x

theorem Setup.restoreRaw (x : Raw s n) (H : GoodEightBank d hh P G x) :
    (E.restore x).raw=x := by
  simp [Setup.restore,H,Core.raw,Setup.rStart,prepStart,ReportFastNominationBridge.start,ReportFastSixPrep.init,cachedOfBank]

theorem Setup.restoreGood (x : Raw s n) (H : GoodEightBank d hh P G x) :
    E.Good (E.restore x) := by
  unfold Setup.restore
  rw [dif_pos H]
  change GoodEightBank d hh P G x ∧ _ 
  refine ⟨H,?_,?_,cachedOfBank x H,E.serial x H,[],rfl⟩
  · exact ReportFastSixPrepTrack.start_good d E.C E.B E.N hh E.F W
      E.inc E.inj G E.digit E.W3 E.cwidth (cachedOfBank x H)
      (E.cserial x H) E.fallback
  · simp [ReportFastSixPrepTrack.hit,Setup.rStart,prepStart,ReportFastNominationBridge.start,ReportFastSixPrep.init]

theorem Setup.phaseBound (x : E.State) (H : E.Good x) : x.phase<5 := by
  cases x with
  | reset z => change 0<5; decide
  | preacq z => change 1<5; decide
  | acq i z => change 2<5; decide
  | postacq A u => change 3<5; decide
  | late A u y => change 4<5; decide
  | invalid y => exact False.elim H.2

theorem Setup.race (x : E.State) :
    LiveRaces d E.B x.raw (E.active x) := by
  cases x with
  | reset z => exact activeRaw_sound d E.B _
  | preacq z => exact activeRaw_sound d E.B _
  | acq i z => exact activeRaw_sound d E.B _
  | postacq A u => intro k H; cases H
  | late A u y => intro k H; cases H
  | invalid y => intro k H; cases H

theorem Setup.costBound (x : E.State) (H : E.Good x) :
    E.cost x≤(caps E.t W K).at x.phase := by
  cases x with
  | reset z => exact E.rCap z H.2.1
  | preacq z => exact E.pCap z H.2.1.1
  | acq i z => exact E.aCap z H.2.1
  | postacq A u => exact H.2.2.2
  | late A u y => exact E.late.bound A u y H.2.2.2
  | invalid y => exact False.elim H.2

theorem Setup.costPositive (x : E.State) (H : E.Good x) : 0<E.cost x := by
  cases x with
  | reset z =>
    obtain ⟨a,e,Eq,L⟩ := E.rNominate z H.2.1 H.2.2.1
    change 0<E.rRank z
    omega
  | preacq z => exact E.pPos z H.2.2.1
  | acq i z => exact E.aPos z H.2.1 H.2.2.1
  | postacq A u =>
    exact ReportFastPostACQ.rank_live A _
      (ReportFastPostACQ.until_invariant A u H.2.1).serial H.2.2.1
  | late A u y => exact E.late.positive A u y H.2.2.2
  | invalid y => exact False.elim H.2

theorem Setup.barPairs (x : E.State) : DisjointPairs (E.bar x) :=
  pairs_from_centers hh G E.B E.inj (E.active x) x.desired (E.bar x)
    (makeBan_spec hh G E.B E.inj _ _)

theorem Setup.noActive (a : Fin n→Option (Fin n)) (D : Fin 5→Bool)
    (H : BanSpec E.B (fun _=>false) D a) (e : Fin n) : a e=none := by
  cases B : a e with
  | none => rfl
  | some v =>
    obtain ⟨k,F,_,_⟩ := (H e v).mp B
    cases F

/-- The preimages of both POSTACQ and LATE are literally the same
    physical mark. -/
theorem Setup.unsteered (x : E.State) (H : 3≤x.phase) (e : Fin n) :
    E.bar x e=none := by
  cases x with
  | reset z => exact False.elim (by change 3≤0 at H; omega)
  | preacq z => exact False.elim (by change 3≤1 at H; omega)
  | acq i z => exact False.elim (by change 3≤2 at H; omega)
  | postacq A u => exact E.noActive _ _ (makeBan_spec hh G E.B E.inj _ _) e
  | late A u y => exact E.noActive _ _ (makeBan_spec hh G E.B E.inj _ _) e
  | invalid y => exact E.noActive _ _ (makeBan_spec hh G E.B E.inj _ _) e

/-- The local paying test uses the actual successor of that phase,
    including its terminal value. It is NOT a new scheduler rule. -/
def Setup.wantsPay (E : Setup d hh P G rs j w W K) (x : E.State) (e : Fin n) : Prop :=
  match x with
  | .reset z => E.rRank (E.rStep z e)<E.rRank z
  | .preacq z => E.pRank (E.pStep z e)<E.pRank z
  | .acq _ z => E.aRank (E.aStep z e)<E.aRank z
  | .postacq A u =>
    let y := rawNext s (rawRun A.base u) e
    ReportFastPostACQ.Stop A y ∨
      ReportFastPostACQ.loopDebt A y<ReportFastPostACQ.loopDebt A (rawRun A.base u)
  | .late A u y => E.late.rank A u (rawNext s y e)<E.late.rank A u y
  | .invalid _ => False

/-- The exact cut test (old payload, actual physical e). At the
    sixth RESET consume, real ACQ launch, first successful consume,
    and clean ISSUE(SEAL), switch on that same mark, not one later. -/
def Setup.cutPhase (E : Setup d hh P G rs j w W K) (x : E.State) (e : Fin n) : Nat :=
  match x with
  | .reset z => if ReportFastSixPrepTrack.hit (E.rStep z e).base then 1 else 0
  | .preacq z => if (E.pStep z e).base.status=.live then 1 else 2
  | .acq _ z => if (E.aStep z e).base.cur=.done then 3 else 2
  | .postacq A u =>
    if ReportFastPostACQ.Stop A (rawNext s (rawRun A.base u) e) then 4 else 3
  | .late _ _ _ => 4
  | .invalid _ => 5

/-- This stronger relation records exact agreement of each local
    observer, not only equality of the raw endpoints. -/
def Setup.Cut (E : Setup d hh P G rs j w W K) (x : E.State) (e : Fin n) (y : E.State) : Prop :=
  match x with
  | .reset z =>
    let v := E.rStep z e
    if ReportFastSixPrepTrack.hit v.base then y=.preacq (E.pStart v.base.1)
    else y=.reset v
  | .preacq z =>
    let v := E.pStep z e
    if v.base.status=.live then y=.preacq v
    else y=.acq z.base.raw.val (E.aStart v.base.raw.val)
  | .acq issue z =>
    let v := E.aStep z e
    if v.base.cur=.done then
      ∃ A : ReportFastPostACQ.Context d hh P G (rs 2),
        A.issue=issue ∧ A.flight=z.base.draws ∧ A.base=v.base.raw ∧ y=.postacq A []
    else y=.acq issue v
  | .postacq A u =>
    let v := rawNext s (rawRun A.base u) e
    if ReportFastPostACQ.Stop A v then y=.late A (u++[e]) v
    else y=.postacq A (u++[e])
  | .late A u v => y=.late A u (rawNext s v e)
  | .invalid _ => False

structure StepSpec (x : E.State) (e : Fin n) (y : E.State) : Prop where
  good : E.Good y
  raw : y.raw=rawNext s x.raw e
  cut : E.Cut x e y
  phase : y.phase=E.cutPhase x e
  hop : Hop Core.phase E.cost x y
  pay : E.wantsPay x e→Pay Core.phase E.cost x y

theorem Setup.initialPostActive (A : ReportFastPostACQ.Context d hh P G (rs 2)) :
    ReportFastPostACQ.Active A A.base := by
  unfold ReportFastPostACQ.Active
  rw [(ReportFastPostACQ.seed_info A).pc]
  exact ⟨Nat.le_refl _,by
    have := A.digit
    unfold cmpOp sealOp
    omega⟩

/-- One complete allowed transition. The witness choice made below
    is only for a proof-carrying Context, not a choice of raw label. -/
theorem Setup.dispatchExists (x : E.State) (e : Fin n) (H : E.Good x)
    (Allow : E.bar x e=none) (NC : classify d h x.raw e≠some j) :
    ∃ y,StepSpec E x e y := by
  classical
  have Bank := E.bankStep x.raw e H.1
  cases x with
  | invalid v => exact False.elim H.2
  | reset z =>
    obtain ⟨I,L,x0,S,v,Hist⟩ := H.2
    let y := E.rStep z e
    have Raw : y.base.1.val=rawNext s z.base.1.val e :=
      ReportFastSixPrepTrack.step_raw d E.C E.B E.N hh E.F W z e
    have BankY : GoodEightBank d hh P G y.base.1.val := by
      rw [Raw]
      exact Bank
    have Gy := ReportFastSixPrepTrack.all_mark d E.C E.B E.N hh E.F W
      E.inc E.inj G E.digit E.W3 E.cwidth z e I
    have Fix : E.rDrive z e=y := by
      change E.rStep z (mergeSide (ReportFastSixPrepTrack.prepBan d E.B z.base) e)=y
      have F : ReportFastSixPrepTrack.prepBan d E.B z.base e=none := Allow
      rw [easy_allowed _ e F]
    have HistY : y=Height.runWord E.rDrive (E.rStart x0) (v++[e]) := by
      rw [Height.runWord,List.foldl_append]
      change y=E.rDrive (Height.runWord E.rDrive (E.rStart x0) v) e
      rw [←Hist,Fix]
    by_cases T : ReportFastSixPrepTrack.hit y.base
    · have OldLive : ¬ReportFastSixPrepTrack.hit
          (Height.runWord E.rDrive (E.rStart x0) v).base := by rwa [←Hist]
      have End : ReportFastSixPrepTrack.hit
          (E.rDrive (Height.runWord E.rDrive (E.rStart x0) v) e).base := by
        rwa [←Hist,Fix]
      have Entry := reset_pre_entry d E.N hh G E.F E.digit W E.W3 rs
        E.consecutive E.width x0 S E.fallback v e 0 OldLive End
      dsimp only at Entry
      let zz := E.rDrive (Height.runWord E.rDrive (E.rStart x0) v) e
      change WinTrackGood d E.B 2 hh (E.pStart zz.base.1) ∧
        (E.pStart zz.base.1).base.status=.live ∧
        OwnClear d (E.B 2) (E.pStart zz.base.1).base.raw.val ∧
        RivalFuture d E.B (E.pStart zz.base.1).base.raw.val at Entry
      have Z : zz=y := by dsimp [zz]; rw [←Hist,Fix]
      rw [Z] at Entry
      refine ⟨.preacq (E.pStart y.base.1),⟨?_,Raw,?_,?_,.inr rfl,fun _=>.inr rfl⟩⟩
      · exact ⟨BankY,Entry⟩
      · simp [Setup.Cut,y,T]
      · simp [Setup.cutPhase,y,T,Core.phase]
    · refine ⟨.reset y,⟨?_,Raw,?_,?_,.inl ⟨rfl,E.rIdle z e I L⟩,
          fun A=>.inl ⟨rfl,A⟩⟩⟩
      · exact ⟨BankY,Gy,T,x0,S,v++[e],HistY⟩
      · simp [Setup.Cut,y,T]
      · simp [Setup.cutPhase,y,T,Core.phase]
  | preacq z =>
    obtain ⟨I,L,Own,Rival⟩ := H.2
    let y := E.pStep z e
    have Fix : mergeSide (preBan d E.B 2 hh z.base) e=e :=
      easy_allowed _ e Allow
    have Wy := win_driver_step d E.B 2 E.N hh G E.F E.digit E.inj z e I
    unfold preWinDriver at Wy
    rw [Fix] at Wy
    have Raw : y.base.raw.val=rawNext s z.base.raw.val e :=
      preTrack_raw d E.B 2 E.N hh E.F z e
    have BankY : GoodEightBank d hh P G y.base.raw.val := by
      rw [Raw]
      exact Bank
    have Base := preTrack_base_early d E.B 2 E.N hh E.F z e
    have LiveClear := ReportFastPreACQRealLaunch.live_clear_phys d (E.B 2) E.N hh G E.F
      E.digit z.base e I.1.1.1 L Own
    rw [←Base] at LiveClear
    have RivalY : RivalFuture d E.B y.base.raw.val := by
      rw [Raw]
      exact future_step d E.B z.base.raw.val Rival e (E.steerFixed _ H.1 e Allow)
    by_cases T : y.base.status=.live
    · refine ⟨.preacq y,⟨?_,Raw,?_,?_,.inl ⟨rfl,?_⟩,fun A=>.inl ⟨rfl,A⟩⟩⟩
      · exact ⟨BankY,Wy,T,LiveClear,RivalY⟩
      · simp [Setup.Cut,y,T]
      · simp [Setup.cutPhase,y,T,Core.phase]
      · exact preTrack_idle d E.B 2 E.N hh G E.F E.digit E.inj z e I.1
          (fun A=>A L)
    · have Success : preACQSuccess d hh y.base :=
        (win_hit_is_launch d E.B 2 hh y Wy).mp T
      have Actual := ReportFastPreACQRealLaunch.first_launch_phys d (E.B 2) E.N hh G E.F
        E.digit z.base e I.1.1.1 L Own (by rwa [←Base])
      rw [←Base] at Actual
      obtain ⟨Door,PC,Legal,Front,Clear⟩ := Actual
      have YBank : GoodEightBank d hh P G y.base.raw.val := BankY
      have A : ReportFastAcqTrack.On d (E.B 2) y.base.raw.val (.fwd 0) :=
        ⟨64,Front,by decide,Clear⟩
      refine ⟨.acq z.base.raw.val (E.aStart y.base.raw.val),⟨?_,Raw,?_,?_,
        .inr rfl,fun _=>.inr rfl⟩⟩
      · refine ⟨YBank,E.aStartGood _ YBank RivalY A,by change ReportFastAcqTrack.Cursor.fwd 0≠.done; decide,H.1.2.1,Legal,PC,.nil,?_⟩
        change y.base.raw.val=rawNext s z.base.raw.val (door (E.B 2))
        rw [Raw,Door]
      · simp [Setup.Cut,y,T]
      · simp [Setup.cutPhase,y,T,Core.phase]
  | acq issue z =>
    obtain ⟨I,L,First,Legal,PC,Flight,Endpoint⟩ := H.2
    let y := E.aStep z e
    have Base := E.aStepBase z e
    have Raw : y.base.raw=rawNext s z.base.raw e := by rw [Base]; rfl
    have Cur : y.base.cur=ReportFastAcqTrack.next (E.B 2) e z.base.cur := by rw [Base]; rfl
    have Draws : y.base.draws=z.base.draws++[e] := by rw [Base]; rfl
    have Gy := E.aStepGood z e I Allow
    have YBank : GoodEightBank d hh P G y.base.raw := by
      simpa only [Core.raw,Raw] using Bank
    by_cases T : y.base.cur=.done
    · have T0 : ReportFastAcqTrack.next (E.B 2) e z.base.cur=.done := Cur.symm.trans T
      obtain ⟨Door,Tag,Win,_,_,_⟩ :=
        ReportFastAcqTrack.finish_is_successful_consume d (E.B 2) E.N hh G E.F E.digit
          z.base.raw H.1.2.1.1.1.1 z.base.cur I.1.2 e L T0
      let A : ReportFastPostACQ.Context d hh P G (rs 2) :=
        ⟨E.N,E.Spos,E.F,issue,First,Legal,PC,z.base.draws,
          fenced_before_consume d (E.B 2) _ _ Flight,
          by rwa [←Endpoint],by rwa [←Endpoint],E.left,E.mid,E.right⟩
      have AB : A.base=y.base.raw := by
        change rawNext s (rawRun (rawNext s issue (door (E.B 2))) z.base.draws)
          (door (E.B 2))=y.base.raw
        rw [←Endpoint,Raw,Door]
      have Bound : ReportFastPostACQ.loopDebt A A.base≤21*E.t*W := by
        rw [ReportFastPostACQ.rank_initial]
        exact ReportFastPostACQ.arithmetic_budget E.W3 (E.width 2)
      refine ⟨.postacq A [],⟨?_,?_,?_,?_,.inr rfl,fun _=>.inr rfl⟩⟩
      · exact ⟨by change GoodEightBank d hh P G A.base; rwa [AB],
          .nil,Setup.initialPostActive A,Bound⟩
      · change A.base=rawNext s z.base.raw e
        exact AB.trans Raw
      · have Witness : ∃ B : ReportFastPostACQ.Context d hh P G (rs 2),
            B.issue=issue ∧ B.flight=z.base.draws ∧ B.base=y.base.raw ∧
              (Core.postacq A [] : E.State)=Core.postacq B [] := ⟨A,rfl,rfl,AB,rfl⟩
        simpa [Setup.Cut,y,T] using Witness
      · simp [Setup.cutPhase,y,T,Core.phase]
    · have T0 : ReportFastAcqTrack.next (E.B 2) e z.base.cur≠.done :=
        fun U=>T (Cur.trans U)
      have Before := ReportFastAcqPrefix.on_not_done_no_consume d (E.B 2) z.base.raw
        z.base.cur e I.1.2 T0
      have RF : DepartureFence d (E.B 2) z.base.raw e :=
        fun _ _ _ _ _=>future_now d E.B z.base.raw I.1.1.2
      have FlightY : FencedBefore d (E.B 2) (rawNext s issue (door (E.B 2))) y.base.draws := by
        rw [Draws]
        exact .snoc e Flight (by rwa [←Endpoint]) (by rwa [←Endpoint])
      have EndpointY : y.base.raw=rawRun (rawNext s issue (door (E.B 2))) y.base.draws := by
        rw [Raw,Draws,ShortOwnerEpochJS.raw_snoc,←Endpoint]
      have Idle := ReportFastAllowedCredit.driver_rank_idle _ _ _ _ _ _ _ E.aRows z e I L
      dsimp only at Idle
      have Unbar : E.aBar z.base e=none := Allow
      rw [easy_allowed _ e Unbar] at Idle
      change E.aRank y≤E.aRank z at Idle
      refine ⟨.acq issue y,⟨⟨YBank,Gy,T,First,Legal,PC,FlightY,EndpointY⟩,
          Raw,?_,?_,.inl ⟨rfl,Idle⟩,fun A=>.inl ⟨rfl,A⟩⟩⟩
      · simp [Setup.Cut,y,T]
      · simp [Setup.cutPhase,y,T,Core.phase]
  | postacq A u =>
    obtain ⟨Tape,Live,Bound⟩ := H.2
    let v := rawNext s (rawRun A.base u) e
    let u' := u++[e]
    have End : rawRun A.base u'=v := ShortOwnerEpochJS.raw_snoc _ _ _
    have TapeY : ReportFastPostACQ.UntilSeal A u' := .snoc e Tape Live
    have I := ReportFastPostACQ.until_invariant A u Tape
    obtain ⟨q,Clock⟩ := ReportFastPostACQ.clock_step A _ _
      ⟨I,Live,rfl⟩
    by_cases T : ReportFastPostACQ.Stop A v
    · have StopY : ReportFastPostACQ.Stop A (rawRun A.base u') := by rwa [End]
      have B : GoodEightBank d hh P G (rawRun A.base u') := by rwa [End]
      have Late := E.late.enter A u' TapeY StopY B
      rw [End] at Late
      refine ⟨.late A u' v,⟨⟨Bank,TapeY,StopY,Late⟩,rfl,?_,?_,.inr rfl,fun _=>.inr rfl⟩⟩
      · simp [Setup.Cut,v,u',T]
      · simp [Setup.cutPhase,v,T,Core.phase]
    · obtain ⟨b,LiveY,Idle,_⟩ := (Clock e).resolve_left T
      have ActiveY : ReportFastPostACQ.Active A (rawRun A.base u') := by
        rw [End]; exact LiveY.2.1
      have IdleY : ReportFastPostACQ.loopDebt A (rawRun A.base u')≤
          ReportFastPostACQ.loopDebt A (rawRun A.base u) := by
        rw [End,←LiveY.2.2]; exact Idle
      refine ⟨.postacq A u',⟨?_,End,?_,?_,.inl ⟨rfl,IdleY⟩,?_⟩⟩
      · exact ⟨by change GoodEightBank d hh P G (rawRun A.base u'); rwa [End],
          TapeY,ActiveY,Nat.le_trans IdleY Bound⟩
      · simp [Setup.Cut,v,u',T]
      · simp [Setup.cutPhase,v,T,Core.phase]
      · intro Pay0
        change ReportFastPostACQ.Stop A v ∨
          ReportFastPostACQ.loopDebt A v<ReportFastPostACQ.loopDebt A (rawRun A.base u) at Pay0
        apply Or.inl
        refine ⟨rfl,?_⟩
        change ReportFastPostACQ.loopDebt A (rawRun A.base u')<_
        rw [End]
        exact Pay0.resolve_left T
  | late A u v =>
    obtain ⟨Tape,Stop,Good⟩ := H.2
    have Y := E.late.advance A u v e Good NC
    exact ⟨.late A u (rawNext s v e),
      ⟨⟨Bank,Tape,Stop,Y.1⟩,rfl,rfl,rfl,.inl ⟨rfl,Y.2⟩,fun P0=>.inl ⟨rfl,P0⟩⟩⟩

/-- The only totalization outside the allowed nonpublication domain.
    Inside it, dispatchExists proves the exact branch and endpoint. -/
def Setup.advance (E : Setup d hh P G rs j w W K) (x : E.State) (e : Fin n) : E.State :=
  if H : E.Good x ∧ E.bar x e=none ∧ classify d h x.raw e≠some j then
    Classical.choose (E.dispatchExists x e H.1 H.2.1 H.2.2)
  else .invalid (rawNext s x.raw e)

theorem Setup.advanceSpec (x : E.State) (e : Fin n) (H : E.Good x)
    (A : E.bar x e=none) (N0 : classify d h x.raw e≠some j) :
    StepSpec E x e (E.advance x e) := by
  unfold Setup.advance
  rw [dif_pos ⟨H,A,N0⟩]
  exact Classical.choose_spec (E.dispatchExists x e H A N0)

theorem Setup.cut_unique (x : E.State) (e : Fin n) (H : E.Good x)
    (A : E.bar x e=none) (N0 : classify d h x.raw e≠some j)
    (y : E.State) (Y : StepSpec E x e y) :
    (E.advance x e).phase=y.phase :=
  (E.advanceSpec x e H A N0).phase.trans Y.phase.symm

theorem Setup.driver_cut (x : E.State) (e : Fin n) (H : E.Good x)
    (N0 : classify d h x.raw (mergeSide (E.bar x) e)≠some j) :
    E.Cut x (mergeSide (E.bar x) e) (E.advance x (mergeSide (E.bar x) e)) :=
  (E.advanceSpec x _ H
    (ReportFastRawRelift.allowed_after_merge _ (E.barPairs x) e) N0).cut

/-- Choose the phase's paying driver label using its own exact
    checked nomination. In POSTACQ and LATE the label is unsteered. -/
theorem Setup.localNomination (x : E.State) (H : E.Good x) :
    ∃ e,let a := mergeSide (E.bar x) e
      classify d h x.raw a=some j ∨ E.wantsPay x a := by
  classical
  cases x with
  | invalid y => exact False.elim H.2
  | reset z =>
    obtain ⟨a,e,A,B⟩ := E.rNominate z H.2.1 H.2.2.1
    exact ⟨e,.inr (by change E.rRank (E.rStep z
                        (mergeSide (ReportFastSixPrepTrack.prepBan d E.B z.base) e))<_
                      rw [A]; exact B)⟩
  | preacq z =>
    obtain ⟨a,e,A,B⟩ := preTrack_nominate d E.B 2 E.N hh G E.F E.digit E.inj z
      H.2.1.1 (fun L=>L H.2.2.1)
    exact ⟨e,.inr (by change E.pRank (E.pStep z (mergeSide (preBan d E.B 2 hh z.base) e))<_
                      rw [A]; exact B)⟩
  | acq issue z =>
    obtain ⟨a,e,A,B⟩ := ReportFastAllowedCredit.driver_rank_nominate _ _ _ _ _ _ _
      E.aRows z H.2.1 H.2.2.1
    exact ⟨e,.inr (by change E.aRank (E.aStep z (mergeSide (E.aBar z.base) e))<_
                      rw [A]; exact B)⟩
  | postacq A u =>
    obtain ⟨Tape,Live,_⟩ := H.2
    have I := ReportFastPostACQ.until_invariant A u Tape
    obtain ⟨q,C⟩ := ReportFastPostACQ.clock_step A _ _ ⟨I,Live,rfl⟩
    refine ⟨q,.inr ?_⟩
    have F := easy_allowed _ q (E.unsteered (.postacq A u) (by change 3≤3; exact Nat.le_refl 3) q)
    change E.wantsPay (.postacq A u) (mergeSide (E.bar (.postacq A u)) q)
    rw [F]
    rcases C q with Stop|⟨b,B,_,Lt⟩
    · exact .inl Stop
    · exact .inr (by rw [←B.2.2]; exact Lt rfl)
  | late A u y =>
    obtain ⟨q,Q0⟩ := E.late.nominate A u y H.2.2.2
    refine ⟨q,?_⟩
    have F := easy_allowed _ q (E.unsteered (.late A u y) (by change 3≤4; decide) q)
    change classify d h y (mergeSide (E.bar (.late A u y)) q)=some j ∨
      E.wantsPay (.late A u y) (mergeSide (E.bar (.late A u y)) q)
    rw [F]
    exact Q0

/-- The requested concrete supplier of SPLICE1's previously open
    LocalRows. No remaining phase-service parameter. -/
def Setup.localRows (E : Setup d hh P G rs j w W K) :
    LocalRows d hh P G E.B j (caps E.t W K) E.State where
  raw := Core.raw
  good := E.Good
  phase := Core.phase
  cost := E.cost
  active := E.active
  desired := Core.desired
  advance := E.advance
  restore := E.restore
  bank := fun _ H=>H.1
  restore_good := E.restoreGood
  restore_raw := E.restoreRaw
  phase_bound := E.phaseBound
  cost_bound := E.costBound
  positive := E.costPositive
  race := fun x _=>E.race x
  allowed := fun x e H A NC=>
    let S := E.advanceSpec x e H A NC
    ⟨S.good,S.raw,S.hop⟩
  paying := by
    intro x H
    obtain ⟨e,B⟩ := E.localNomination x H
    let a := mergeSide (E.bar x) e
    refine ⟨e,?_⟩
    change classify d h x.raw a=some j ∨ Pay Core.phase E.cost x (E.advance x a)
    by_cases Pub : classify d h x.raw a=some j
    · exact .inl Pub
    · have A := ReportFastRawRelift.allowed_after_merge _ (E.barPairs x) e
      exact .inr ((E.advanceSpec x a H A Pub).pay (B.resolve_left Pub))

/-- Exact all-mark commutation, including a publication on an excluded
    label. The old raw pair and old mark are evaluated before restore. -/
theorem Setup.allMark (y : Obs E.State) (e : Fin n) (H : ReportFastSplice.good E.localRows y) :
    ReportFastSplice.good E.localRows (ReportFastSplice.next E.localRows y e) ∧
      project E.localRows (ReportFastSplice.next E.localRows y e)=
        ShortTwoPublicationClock.phase (rawNext s) (classify d h) j
          (project E.localRows y) e :=
  next_spec E.localRows E.bankStep y e H

theorem Setup.excluded (y : Obs E.State) (e : Fin n)
    (H : ReportFastSplice.good E.localRows y) (A : coreBan E.localRows y.core e≠none) :
    (ReportFastSplice.next E.localRows y e).latch=
        (y.latch || decide (classify d h y.core.raw e=some j)) ∧
      (ReportFastSplice.next E.localRows y e).core=E.restore (rawNext s y.core.raw e) := by
  have C := congrArg Prod.snd (E.allMark y e H).2
  refine ⟨C,?_⟩
  unfold ReportFastSplice.next
  dsimp only
  split
  · rfl
  · simp [project,ShortTwoPublicationClock.phase,Setup.localRows]

theorem Setup.ordinaryBank (y : Obs E.State) (H : ReportFastSplice.good E.localRows y) :
    GoodEightBank d hh P G (project E.localRows y).1 := H.1

theorem Setup.ordinaryRaw (y : Obs E.State) (e : Fin n) (H : ReportFastSplice.good E.localRows y) :
    (project E.localRows (ReportFastSplice.next E.localRows y e)).1=rawNext s (project E.localRows y).1 e :=
  congrArg Prod.fst (E.allMark y e H).2

/-- The checked PACE theorem is reused, on the very same observer,
    with the exact raw projection and bank closure just proved. -/
theorem Setup.pace : Pace E.localRows E.t w W := by
  apply ReportFastItem10Assembly.service_program_refractory_raw d E.N hh G E.F E.digit
    E.B E.mem E.inj w W E.wide (ReportFastSplice.next E.localRows) (ReportFastSplice.good E.localRows)
    (project E.localRows)
    (fun y e H=>(E.allMark y e H).1) E.ordinaryBank E.ordinaryRaw
    (obsBan E.localRows) (ReportFastSplice.active E.localRows) (ReportFastSplice.desired E.localRows)
  · intro y H e a
    exact makeBan_spec hh G E.B E.inj _ _ e a
  · intro y H k B
    by_cases F : y.latch=true
    · simp [ReportFastSplice.active,F] at B
    · have A : E.localRows.active y.core k=true := by
        simpa only [ReportFastSplice.active,if_neg F] using B
      exact E.race y.core k A

/-- Complete PhaseRows modulo the one explicit LateSealCommit, and
    the stated geometric/numeric inputs. -/
theorem Setup.phaseRows :
    PhaseRows (P:=P) d hh G E.B (ReportFastSplice.next E.localRows) (ReportFastSplice.good E.localRows)
      (ReportFastSplice.finish) (project E.localRows) (obsBan E.localRows)
      (ReportFastSplice.active E.localRows) (ReportFastSplice.desired E.localRows) (obsDebt E.localRows)
      (obsCredit E.localRows) E.t w W :=
  phaseRows_of_local E.localRows E.inj E.bankStep E.t w W
    (cap_total E.t W K E.cap) E.pace

theorem Setup.initialGood (x : Raw s n) (H : GoodEightBank d hh P G x) :
    ReportFastSplice.good E.localRows (ReportFastSplice.init E.localRows x) :=
  init_good E.localRows x H

theorem Setup.initialProject (x : Raw s n) (H : GoodEightBank d hh P G x) :
    project E.localRows (init E.localRows x)=(x,false) :=
  init_project E.localRows x H

theorem Setup.finishSticky (y : Obs E.State) (e : Fin n)
    (H : ReportFastSplice.finish y=true) : ReportFastSplice.finish (ReportFastSplice.next E.localRows y e)=true :=
  sticky E.localRows y e H

theorem Setup.finishSound (y : Obs E.State) (H : ReportFastSplice.finish y=true) :
    (project E.localRows y).2=true := H

-- CHECK: ReportFastSixPrepTrack.lean:132–143, exact argument order
-- of start_good/all_mark. ReportFastNominationBridge.lean:170–243
-- next/start/Rows; use qualified ReportFastNominationBridge.next in
-- aStep and ReportFastSplice.next in the assembly if "next" is ambiguous.
-- CHECK: ReportFastPreACQRealLaunch.lean:16–55 for the explicit
-- preTrack_base_early rewrite at LiveClear and Actual.
-- CHECK: ReportFastPostACQ.lean:33–65, 500–511, 639–660, 678–711:
-- Context constructor, UntilSeal, rank_initial, and clock_step.
-- CHECK: ReportFastAcqPrefix.lean:15–39 and ReportFastAcqWins.lean:359–372
-- for actual pre-consume tape and no-consume snoc.
-- CHECK: ReportFastItem10Assembly.lean:13–50, PhaseRows field order;
-- ReportFastRefractoryAdapter.lean: the final theorem is in namespace
-- ReportFastItem10Assembly, not namespace ReportFastRefractoryAdapter.

#print axioms Setup.dispatchExists
#print axioms Setup.advanceSpec
#print axioms Setup.cut_unique
#print axioms Setup.driver_cut
#print axioms Setup.allMark
#print axioms Setup.excluded
#print axioms Setup.pace
#print axioms Setup.phaseRows

end
end L4.ReportFastDispatch


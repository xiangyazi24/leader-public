import Leader.L4.ReportFastAcqAllowed
import Leader.L4.ReportFastAcqMapped

namespace L4.ReportFastAcqDriver
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportOwnerCommandRail
open ReportFastOwnerSupport ReportFastNominationBridge ReportAdaptiveFibre
open ReportFastAcqAllowed ReportFastDenySteering ReportFastSteeringMap
open ReportFastPrepMapping ReportFastMappedFence ReportFastFiveGeometry
open ReportFastAcqWins ReportFastAcqTrack ReportLeaseOwner

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

structure Trace (s n : Nat) where
  raw : Raw s n
  cur : Cursor
  draws : List (Fin n)

def step (C : Chart h) (z : Trace s n) (e : Fin n) : Trace s n :=
  ⟨rawNext s z.raw e,ReportFastAcqTrack.next C e z.cur,z.draws++[e]⟩

def env (d : Sheet) (hh : ∃ i,h i=true) (B : Fin 5→Chart h)
    (P : Nat → Raw s n → Fin 5 → Bool) (t : Nat) (x : Raw s n)
    (front : List (Fin n)) (z : Trace s n) : Prop :=
  z.raw=rawRun x (mappedWord d B P t x (front++z.draws)) ∧
    Cached d hh Q z.raw ∧ ∀ j,StrongSerial d (B j) z.raw

private theorem steer_of_unbarred (d : Sheet) (B : Fin 5→Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (inj : Function.Injective (fun j=>center (B j)))
    (desired : Fin 5→Bool) (z : Trace s n) (e : Fin n)
    (H : bans d B desired Trace.raw z e=none) :
    steerRaw d B desired z.raw e=e := by
  have E : activeRaw d B z.raw=fun j=>ReportFastRefractory.armed d (B j) z.raw :=
    funext (active_eq_armed d B z.raw)
  unfold bans at H
  rw [E] at H
  let act := fun j=>ReportFastRefractory.armed d (B j) z.raw
  have Gate : gateBan B act desired e=none := by
    cases E0 : gateBan B act desired e with
    | none => rfl
    | some a =>
      have A := (gate_ban_spec hh G B inj act desired e a).mp E0
      have C := (makeBan_spec hh G B inj act desired e a).mpr A
      change makeBan B act desired e=none at H
      rw [H] at C
      contradiction
  unfold steerRaw
  change mergeSide (gateBan B act desired) e=e
  exact easy_allowed _ e Gate

theorem same_prefix_insertion (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (B : Fin 5→Chart h)
    (inj : Function.Injective (fun j=>center (B j)))
    (P : Nat → Raw s n → Fin 5 → Bool) (t : Nat) (x : Raw s n)
    (front : List (Fin n)) (D : Fin 5→Bool)
    (late : ∀ a y,t+front.length≤a→P a y=D)
    (z : Trace s n) (e : Fin n) (H : env (Q:=Q) d hh B P t x front z)
    (A : bans d B D Trace.raw z e=none) :
    env (Q:=Q) d hh B P t x front (step (B 2) z e) := by
  refine ⟨?_, (cached_fibre d N hh Q F).closed _ e H.2.1,?_⟩
  · change rawNext s z.raw e=rawRun x (mappedWord d B P t x (front++(z.draws++[e])))
    rw [←List.append_assoc,mappedWord_append,ShortOwnerEpochJS.raw_append,←H.1]
    have D0 : P (t+(front++z.draws).length) z.raw=D := late _ _ (by simp)
    change rawNext s z.raw e=rawNext s z.raw (steerRaw d B (P _ z.raw) z.raw e)
    rw [D0,steer_of_unbarred d B hh G inj D z e A]
  · intro j
    exact strong_step d (B j) N hh G F z.raw H.2.1 (H.2.2 j) digit e

theorem actual_relift (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Fin 5→Owner h) (R : Consecutive G r)
    (incl : ∀ j,∃ i,C i=charter G (r j))
    (x : {y : Raw s n // Cached d hh Q y}) (prep preacq : List (Fin n))
    (t : Nat) (P : Nat → Raw s n → Fin 5 → Bool)
    (D : Fin 5→Bool)
    (prior : ∀ a y,t≤a→a<t+prep.length→P a y=denySides)
    (deny : ∀ a y j,j≠2→P a y j=false)
    (late : ∀ a y,t+(prep++preacq).length≤a→P a y=D)
    (done : (SequentialMarkClock.run
      (fun z e=>ReportFastSixPrep.step d C N hh F z
        (mergeSide (ReportFastSixPrepTrack.prepBan d (fun j=>charter G (r j)) z) e))
      (ReportFastSixPrep.init d hh x) prep).2=none) :
    let B := fun j=>charter G (r j)
    Relift d (B 2) hh B D (env (Q:=Q) d hh B P t x.val (prep++preacq))
      Trace.raw Trace.cur (step (B 2)) Q := by
  dsimp only
  let B := fun j=>charter G (r j)
  have Inj := centers_injective_of_roots G B (target_five_incidence G r R).2.1
  constructor
  · intro z e H A
    exact same_prefix_insertion d N hh G F digit B Inj P t x.val _ D late z e H A
  · intros; rfl
  · intros; rfl
  · intro z H
    exact H.2.1
  · intro z H
    exact H.2.2
  · intro z e H _ _ _ _ _ _
    have Hist := prepared_mapped_receiptSuffix d C B N hh G F Inj incl x prep
      (preacq++z.draws) t P prior done
    have RF := target_rival_fence_of_receipts d N hh G F digit r R P deny
      x.val x.property _ (fun j _=>Hist j)
    rw [H.1, List.append_assoc]
    exact RF

/-- Seed at the real F(64) launch of the mapped preparation/prelude
tape, and run the fixed late profile. Each witness extension uses a
physical image label as its own legal driver preimage. The witness is
the same physical tape, not necessarily the original driver labels. -/
theorem actual_launch_mean (d : Sheet) (C : Fin 6→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Fin 5→Owner h) (R : Consecutive G r)
    (incl : ∀ j,∃ i,C i=charter G (r j))
    (x : {y : Raw s n // Cached d hh Q y}) (prep preacq : List (Fin n))
    (t : Nat) (P : Nat→Raw s n→Fin 5→Bool) (D : Fin 5→Bool)
    (prior : ∀ a y,t≤a→a<t+prep.length→P a y=denySides)
    (deny : ∀ a y j,j≠2→P a y j=false)
    (late : ∀ a y,t+(prep++preacq).length≤a→P a y=D)
    (done : (SequentialMarkClock.run
      (fun z e=>ReportFastSixPrep.step d C N hh F z
        (mergeSide (ReportFastSixPrepTrack.prepBan d (fun j=>charter G (r j)) z) e))
      (ReportFastSixPrep.init d hh x) prep).2=none)
    (q : Fin n) :
    let B := fun j=>charter G (r j)
    let a := rawRun x.val (mappedWord d B P t x.val (prep++preacq))
    Cached d hh Q a →
    (∀ j,StrongSerial d (B j) a) →
    ReportOwnerAcquireProvenance.FState d (B 2) a 0 64 →
    OwnClear d (B 2) a →
    Height.IIDExpectedHittingTimeAtMost
      (driver (B 2) (step (B 2)) (bans d B D Trace.raw) Trace.cur)
      (fun y=>y.base.cur=.done)
      (start (fun z q=>ReportFastAcqTrack.label (B 2) z.cur=some q)
        (⟨a,.fwd 0,[]⟩:Trace s n) q)
      (n*(4*(B 2).L+1)) := by
  dsimp only
  intro X S A O
  let B := fun j=>charter G (r j)
  let a := rawRun x.val (mappedWord d B P t x.val (prep++preacq))
  let z : Trace s n := ⟨a,.fwd 0,[]⟩
  have E : env (Q:=Q) d hh B P t x.val (prep++preacq) z := by
    refine ⟨?_,X,S⟩
    simp [z,a]
  have I := actual_relift d C N hh G F digit r R incl x prep preacq t P D prior deny late done
  have Inj := centers_injective_of_roots G B (target_five_incidence G r R).2.1
  have Rows := allowed_rows d (B 2) N hh G F digit B D Inj _ _ _ _ I
  exact launch_mean (B 2) (step (B 2)) _ Trace.raw Trace.cur d B D Rows z q E rfl A O

theorem actual_driver_finish (d : Sheet) (B : Fin 5→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (D : Fin 5→Bool)
    (z : Track (Trace s n) n) (e : Fin n)
    (X : Cached d hh Q z.base.raw) (A : On d (B 2) z.base.raw z.base.cur)
    (L : z.base.cur≠.done)
    (H : (driver (B 2) (step (B 2)) (bans d B D Trace.raw) Trace.cur z e).base.cur=.done) :
    let m := mergeSide (bans d B D Trace.raw z.base) e
    let y := (driver (B 2) (step (B 2)) (bans d B D Trace.raw) Trace.cur z e).base.raw
    m=ReportResetBarrier.door (B 2) ∧
    (tok d (B 2) z.base.raw 0).tag=3 ∧
    (tok d (B 2) z.base.raw 0).outcome≠1 ∧
    ReportOwnerReverseControl.EmptyIssueShape d (B 2) y ∧
    ReportPrelaunchClock.readPC d (B 2) y=(1,ReportByteRows.cmpOp (params d s)) ∧
    ReportOwnerAcquireReturn.ownerCaptureSix d (B 2) y=(tok d (B 2) z.base.raw 0).payload%64 := by
  unfold driver at H ⊢
  rw [next_base] at H ⊢
  exact finish_is_successful_consume d (B 2) N hh G F digit z.base.raw X
    z.base.cur A _ L H

end L4.ReportFastAcqDriver

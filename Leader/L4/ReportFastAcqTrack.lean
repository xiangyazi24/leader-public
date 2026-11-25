import Leader.L4.ReportFastAcqWins
import Leader.L4.ReportFastNominationBridge

namespace L4.ReportFastAcqTrack
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchClock ReportPrelaunchK1Geometry
open ReportOwnerAcquireProvenance ReportOwnerAcquireReturn
open ReportFastAcqWins ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerReverseControl ReportByteRows

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000

inductive Cursor
  | fwd (k : Nat)
  | rev (k : Nat)
  | done
  deriving DecidableEq

def label (C : Chart h) : Cursor→Option (Fin n)
  | .fwd k => some (out C k)
  | .rev k => some (inEdge C k)
  | .done => none

def debt (C : Chart h) : Cursor→Nat
  | .fwd k => fDebt C k
  | .rev k => dDebt k
  | .done => 0

def next (C : Chart h) (e : Fin n) : Cursor→Cursor
  | .fwd k => if e=out C k then if k+1<C.L then .fwd (k+1) else .rev k else .fwd k
  | .rev 0 => if e=door C then .done else .rev 0
  | .rev (k+1) => if e=out C k then .rev k else .rev (k+1)
  | .done => .done

def On (d : Sheet) (C : Chart h) (x : Raw s n) : Cursor→Prop
  | .fwd k => ∃ q, FState d C x k q ∧ q/64=1 ∧ ClearFrom d C x k
  | .rev k => ∃ q, DState d C x k q ∧ q/64=1
  | .done => True

def fit (C : Chart h) : Cursor→Prop
  | .fwd k | .rev k => k<C.L
  | .done => True

theorem on_fit (d : Sheet) (C : Chart h) (x : Raw s n) (c : Cursor)
    (H : On d C x c) : fit C c := by
  cases c with
  | fwd k => exact H.choose_spec.1.shape.2.1
  | rev k => exact H.choose_spec.1.shape.2.1
  | done => trivial

theorem physical_pays (C : Chart h) (c : Cursor) (H : fit C c) (q : Fin n)
    (L : label C c=some q) : debt C (next C q c)<debt C c := by
  cases c with
  | done => contradiction
  | fwd k =>
    have Q0 := Option.some.inj L
    subst q
    change k<C.L at H
    by_cases J : k+1<C.L <;> simp [next,debt,J,fDebt,dDebt] <;> omega
  | rev k =>
    have Q0 := Option.some.inj L
    subst q
    cases k with
    | zero => simp [next,debt,dDebt,inEdge]
    | succ k => simp [next,debt,dDebt,inEdge]

theorem physical_hold (C : Chart h) (c : Cursor) (e : Fin n)
    (H : label C c≠some e) : next C e c=c := by
  cases c with
  | done => rfl
  | fwd k =>
    have E : e≠out C k := fun X=>H (congrArg some X.symm)
    simp [next,E]
  | rev k =>
    cases k with
    | zero =>
      have E : e≠door C := fun X=>H (by simp [label,inEdge,X])
      simp [next,E]
    | succ k =>
      have E : e≠out C k := fun X=>H (by simp [label,inEdge,X])
      simp [next,E]

theorem debt_idle (C : Chart h) (c : Cursor) (H : fit C c) (e : Fin n) :
    debt C (next C e c)≤debt C c :=
  if A : label C c=some e then Nat.le_of_lt (physical_pays C c H e A)
  else by rw [physical_hold C c e A]; exact Nat.le_refl _

theorem plateau_label (C : Chart h) (c : Cursor) (H : fit C c) (e : Fin n)
    (E : debt C (next C e c)=debt C c) : label C (next C e c)=label C c := by
  by_cases A : label C c=some e
  · exact False.elim ((Nat.ne_of_lt (physical_pays C c H e A)) E)
  · rw [physical_hold C c e A]

theorem finish_iff (C : Chart h) (c : Cursor) (e : Fin n) (L : c≠.done) :
    next C e c=.done ↔ c=.rev 0 ∧ e=door C := by
  cases c with
  | done => exact False.elim (L rfl)
  | fwd k => by_cases E : e=out C k <;> by_cases J : k+1<C.L <;> simp [next,E,J]
  | rev k => cases k with
    | zero => by_cases E : e=door C <;> simp [next,E]
    | succ k => by_cases E : e=out C k <;> simp [next,E]

theorem raw_on_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (c : Cursor) (A : On d C x c)
    (e : Fin n) (RF : DepartureFence d C x e) :
    On d C (rawNext s x e) (next C e c) := by
  let mask := (cached_fibre d N hh Q F).mask x X
  cases c with
  | done => trivial
  | fwd k =>
    obtain ⟨q,R,S,O⟩ := A
    by_cases E : e=out C k
    · subst e
      have S' : stepPayload d C x k q/64=1 := by
        by_cases H : h (out C k)=true
        · exact (actual_header_capture d C N x mask k q R S H
            (RF k q R rfl H) (O k (Nat.le_refl _) R.shape.2.1 H)).1
        · have H' : h (out C k)=false := Bool.eq_false_iff.mpr H
          simpa only [stepPayload,acqFlightNext,H',Bool.false_eq_true,if_false] using S
      rcases forward_depart d C N hh G F x X k q R with ⟨J,B⟩|⟨J,B⟩
      · simp only [next,if_pos J]
        refine ⟨_,B,S',?_⟩
        intro i K I H
        exact clear_unvisited d C N x mask k q R O (out C k) i
          (by omega) I H (by intro E; have := E.2; omega)
      · simp only [next,if_neg (show ¬k+1<C.L by omega)]
        exact ⟨_,B,S'⟩
    · simp only [next,if_neg E]
      refine ⟨q,forward_other d C N hh G F x X k q R e E,S,?_⟩
      intro i K I H
      exact clear_unvisited d C N x mask k q R O e i K I H (fun J=>E J.1)
  | rev k =>
    obtain ⟨q,R,S⟩ := A
    cases k with
    | zero =>
      by_cases E : e=door C
      · simp [next,E,On]
      · simp only [next,if_neg E]
        rcases D_step d C hh G F N x X 0 q R digit e (.inl E) with B|⟨j,J,_,_⟩
        · exact ⟨q,B,S⟩
        · omega
    | succ k =>
      by_cases E : e=out C k
      · subst e
        simp only [next]
        exact ⟨q,(reverse_pays d C N hh G F digit x X k q R).1,S⟩
      · simp only [next,if_neg E]
        have NC : NoConsume d C x e := by
          right
          rw [R.shape.2.2 0 C.positive]
          simp [backTag]
        rcases D_step d C hh G F N x X (k+1) q R digit e NC with B|⟨j,J,L,_⟩
        · exact ⟨q,B,S⟩
        · have E0 : j=k := by omega
          exact False.elim (E (E0 ▸ L))

theorem finish_is_successful_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (c : Cursor) (A : On d C x c) (e : Fin n) (L : c≠.done)
    (E : next C e c=.done) :
    e=door C ∧ (tok d C x 0).tag=3 ∧ (tok d C x 0).outcome≠1 ∧
    EmptyIssueShape d C (rawNext s x e) ∧
    readPC d C (rawNext s x e)=(1,cmpOp (params d s)) ∧
    ownerCaptureSix d C (rawNext s x e)=(tok d C x 0).payload%64 := by
  obtain ⟨E0,E1⟩ := (finish_iff C c e L).mp E
  subst c e
  obtain ⟨q,R,S⟩ := A
  have Op : (readPC d C x).2=acqOp (params d s) := congrArg Prod.snd R.pc
  have K : (tok d C x 0).opcode=acqOp (params d s) := by
    rw [R.packet]
    exact acqFlightD_op _ _
  have F0 : (tok d C x 0).fault=false := by
    rw [R.packet]
    exact acqFlightD_live _ _
  have ND : (tok d C x 0).outcome≠1 := by rw [R.packet]; simp [acqFlightD,S]
  have Tag : (tok d C x 0).tag=3 := by rw [R.packet]; simp [acqFlightD,S]
  have U := raw_acq_consume_six d C hh G F N x X R.shape Op K F0 ND digit
  exact ⟨rfl,Tag,ND,U.2.1,U.2.2.1,U.2.2.2⟩

-- The fixed policy applies to the rival ADMIT gates while the target
-- cursor is in ACQ. Env is the caller's chronology/fence re-lift;
-- this module does not infer it from local PhaseOK.
open ReportFastNominationBridge ReportFastOwnerSupport
open ReportOwnerCommandRail

abbrev State (s n : Nat) := Raw s n × Cursor

def observe {s n : Nat} {h : Fin n→Bool}
    (C : Chart h) (z : State s n) (e : Fin n) : State s n :=
  (rawNext s z.1 e,next C e z.2)

def observedHit (z : State s n) : Prop := z.2=.done

def observedNom (C : Chart h) (z : State s n) (q : Fin n) : Prop :=
  label C z.2=some q

def observerGood (d : Sheet) (C : Chart h) (Env : State s n→Prop)
    (z : State s n) : Prop := Env z ∧ On d C z.1 z.2

noncomputable def observerBan (d : Sheet) (B : Fin 5→Chart h)
    (desired : Fin 5→Bool) (z : State s n) : Fin n→Option (Fin n) :=
  makeBan B (activeRaw d B z.1) desired

theorem observed_rows (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (B : Fin 5→Chart h) (desired : Fin 5→Bool)
    (inj : Function.Injective (fun j=>center (B j)))
    (Env : State s n→Prop)
    (closed : ∀ z e,Env z→Env (observe C z e))
    (cache : ∀ z,Env z→Cached d hh Q z.1)
    (serial : ∀ z,Env z→∀ j,StrongSerial d (B j) z.1)
    (fence : ∀ z e,Env z→DepartureFence d C z.1 e) :
    ReportFastNominationBridge.Rows (observe C) (observerGood d C Env) observedHit
      (fun z=>debt C z.2) (observerBan d B desired) (observedNom C)
      (fun z q=>Spent d B z.1 q) := by
  constructor
  · intro z e H
    exact ⟨closed z e H.1,raw_on_step d C N hh G F digit z.1
      (cache z H.1) z.2 H.2 e (fence z e H.1)⟩
  · intro z e _ H
    change z.2=.done at H
    simp [observedHit,observe,H,next]
  · intro z e H _
    exact debt_idle C _ (on_fit d C _ _ H.2) _
  · intro z _ H
    change z.2≠.done at H
    cases z with
    | mk x c =>
      cases c with
      | done => exact (H rfl).elim
      | fwd k => exact ⟨out C k,rfl⟩
      | rev k => exact ⟨inEdge C k,rfl⟩
  · intro z q H _ A
    exact physical_pays C _ (on_fit d C _ _ H.2) _ A
  · intro z q e H _ A E
    exact (plateau_label C _ (on_fit d C _ _ H.2) e E).trans A
  · intro z q a H _ E
    exact ban_mate_spends d N hh G F B z.1 (cache z H.1) (serial z H.1)
      (activeRaw d B z.1) desired (observerBan d B desired z)
      (makeBan_spec hh G B inj _ _) (activeRaw_sound d B z.1) q a E
  · intro z q e H _ A E
    exact spent_step d N hh G F B z.1 (cache z H.1) (serial z H.1) q e E A
  · intro z q _ _ A
    exact spent_unblocked d hh G B inj z.1 q (activeRaw d B z.1) desired
      (observerBan d B desired z) (makeBan_spec hh G B inj _ _)
      (activeRaw_sound d B z.1) A

end L4.ReportFastAcqTrack

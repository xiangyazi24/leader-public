import Leader.L4.ReportFastNoRearm
import Leader.L4.ReportFastGateRaw
import Leader.L4.ReportFastOwnerSupport
import Leader.L4.ReportPrelaunchDoorReady
import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportGoodEightBank
import Leader.L4.ReportWriteRailSupplier
import Leader.L4.ReportGatePairs

namespace L4.ReportFastFreshReset
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerForwardControl ReportOwnerReverseControl ReportOwnerIssueControl
open ReportOwnerSerial ReportOwnerCommandRail ReportOwnerDoorProjection
open ReportByteRows ReportRawProjection

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

abbrev State (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n→Prop) :=
  ReportOwnerReceiptClock.State (Cached d hh Q)

def step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) :
    State d hh Q→Fin n→State d hh Q :=
  ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F)

def Inv (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : State d hh Q) : Prop :=
  StrongSerial d C z.1.val ∧
  ∀ st,z.2=some st→st≠.done→FullActive d C z.1.val st

theorem step_raw (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (e : Fin n) :
    (step d C N hh F z e).1.val=rawNext s z.1.val e := rfl

theorem initial_inv (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (x : {x : Raw s n // Cached d hh Q x})
    (S : StrongSerial d C x.val) :
    Inv d C hh (x,none) := by
  refine ⟨S,?_⟩
  intro st E
  cases E

theorem inv_closed (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (z : State d hh Q) (e : Fin n) (I : Inv d C hh z) :
    Inv d C hh (step d C N hh F z e) := by
  let CF := cached_fibre d N hh Q F
  refine ⟨strong_step d C N hh G F z.1.val z.1.property I.1 digit e,?_⟩
  intro st H ND
  change (ReportOwnerReceiptClock.next d C CF z e).2=some st at H
  cases E : z.2 with
  | none =>
    by_cases L : ownerPC d C z.1.val=.issue0 ∧ e=door C
    · have J : Stage.fwd 0=st := by
        simpa [ReportOwnerReceiptClock.next,E,L] using H
      subst st
      rw [step_raw, L.2]
      exact full_launch d C z.1.val N (CF.mask _ z.1.property) L.1
    · simp [ReportOwnerReceiptClock.next,E,L] at H
  | some old =>
    have J : nextStage C e old=st := by
      simpa [ReportOwnerReceiptClock.next,E] using H
    have OLD : old≠.done := by
      intro K
      subst old
      exact ND J.symm
    rw [←J,step_raw]
    exact full_active_step d C CF z.1.val z.1.property N e old OLD (I.2 old E OLD)

private theorem door_iff (C : Chart h) (e : Fin n) :
    rightNeighbor e=C.root ↔ e=door C := by
  constructor
  · intro H
    simpa only [door,RearTrace.predecessor_right] using
      congrArg RearTrace.predecessor H
  · rintro rfl
    exact RearTrace.right_predecessor _

-- The observer stage equation is independently exposed, rather
-- than taking "done" as evidence of a raw event.
private theorem stage_done_iff (C : Chart h) (st : Stage) (e : Fin n)
    (N : st≠.done) :
    nextStage C e st=.done ↔ st=.rev 0 ∧ e=door C := by
  cases st with
  | done => exact False.elim (N rfl)
  | fwd i =>
    by_cases E : e=out C i
    · by_cases J : i+1<C.L <;> simp [nextStage,E,J]
    · simp [nextStage,E]
  | rev i =>
    cases i with
    | zero =>
      by_cases E : rightNeighbor e=C.root
      · have D := (door_iff C e).mp E
        have H : rightNeighbor (door C)=C.root := D ▸ E
        simp [nextStage,D,H]
      · have D : e≠door C := fun K=>E ((door_iff C e).mpr K)
        simp [nextStage,E,D]
    | succ i =>
      by_cases E : e=out C i <;> simp [nextStage,E]

theorem done_rise_stage_iff (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (e : Fin n) :
    (¬ReportOwnerReceiptClock.done z ∧
      ReportOwnerReceiptClock.done (step d C N hh F z e)) ↔
      z.2=some (.rev 0) ∧ e=door C := by
  let CF := cached_fibre d N hh Q F
  change (_ ∧ (ReportOwnerReceiptClock.next d C CF z e).2=some .done) ↔ _
  cases E : z.2 with
  | none =>
    by_cases L : ownerPC d C z.1.val=.issue0 ∧ e=door C <;>
      simp [ReportOwnerReceiptClock.done,ReportOwnerReceiptClock.next,E,L]
  | some st =>
    by_cases D : st=.done
    · subst st
      simp [ReportOwnerReceiptClock.done,ReportOwnerReceiptClock.next,E]
    · simp only [ReportOwnerReceiptClock.done,E,Option.some.injEq,D,not_false_eq_true,
        true_and,ReportOwnerReceiptClock.next]
      exact stage_done_iff C st e D

-- The real event (including actual old wire and postmark custody).
-- This is history-qualified by the fresh active cursor, not merely D0
-- bytes at a state which might predate monitor initialization.
def FreshConsume (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : State d hh Q) (e : Fin n) : Prop :=
  z.2=some (.rev 0) ∧ e=door C ∧
    controlWork (params d s) (selectBytes d (z.1.val C.root))=(2,0) ∧
    resetTokenRead (params d s) (selectBytes d (z.1.val C.root)) 0=
      resetTokenWire (params d s) reset0Reply ∧
    FullParked d C (rawNext s z.1.val e)

theorem consume_crossing (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (I : Inv d C hh z) (e : Fin n) :
    (¬ReportOwnerReceiptClock.done z ∧
      ReportOwnerReceiptClock.done (step d C N hh F z e)) ↔
      FreshConsume d C hh z e := by
  rw [done_rise_stage_iff d C N hh F z e]
  constructor
  · rintro ⟨E,rfl⟩
    let CF := cached_fibre d N hh Q F
    have A := I.2 (.rev 0) E (by decide)
    obtain ⟨P,W,_⟩ := consume_step d C CF z.1.val z.1.property N A.1
    have V := full_active_step d C CF z.1.val z.1.property N
      (door C) (.rev 0) (by decide) A
    have J : nextStage C (door C) (.rev 0)=.done :=
      (stage_done_iff C (.rev 0) (door C) (by decide)).mpr ⟨rfl,rfl⟩
    rw [J] at V
    exact ⟨E,rfl,P,W,parked_of_done d C _ V.1,V.2.1,
      fun k K H L=>V.2.2 k K H L trivial⟩
  · intro E
    exact ⟨E.1,E.2.1⟩

-- In a tracked live flight, the old D0 at the root already
-- identifies the reverse-root phase; it cannot be a second F
-- or a stale reply ahead of the current forward front.
theorem active_root_reply_iff (d : Sheet) (C : Chart h)
    (x : Raw s n) (st : Stage) (ND : st≠.done)
    (A : FullActive d C x st) :
    slot d C x 0=.reply0 ↔ st=.rev 0 := by
  cases st with
  | done => exact False.elim (ND rfl)
  | fwd k =>
    have R := A.1.1
    change k<C.L ∧ ownerPC d C x=.wait0 ∧
      slot d C x k=.forward0 ∧ ∀ j,j<k→slot d C x j=.trail at R
    by_cases Z : k=0
    · subst k
      rw [R.2.2.1]
      simp
    · rw [R.2.2.2 0 (Nat.pos_of_ne_zero Z)]
      simp
  | rev k =>
    have R := A.1.1
    change k<C.L ∧ ownerPC d C x=.wait0 ∧
      (∀ j,j<C.L→slot d C x j=
        if j<k then .trail else if j=k then .reply0 else .empty) at R
    rw [R.2.2 0 C.positive]
    cases k <;> simp

theorem consume_at_old_reply (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (I : Inv d C hh z) (e : Fin n) :
    (¬ReportOwnerReceiptClock.done z ∧
      ReportOwnerReceiptClock.done (step d C N hh F z e)) ↔
    ∃ st,z.2=some st ∧ st≠.done ∧ e=door C ∧
      ownerPC d C z.1.val=.wait0 ∧ slot d C z.1.val 0=.reply0 := by
  rw [done_rise_stage_iff d C N hh F z e]
  constructor
  · rintro ⟨E,rfl⟩
    have A := I.2 (.rev 0) E (by decide)
    exact ⟨.rev 0,E,by decide,rfl,A.1.1.2.1,
      (active_root_reply_iff d C _ _ (by decide) A).mpr rfl⟩
  · rintro ⟨st,E,ND,D,_,R⟩
    have J := (active_root_reply_iff d C z.1.val st ND (I.2 st E ND)).mp R
    exact ⟨E.trans (congrArg some J),D⟩

-- Exact old source controller and all new parked fields at the cut.
theorem crossing_parked (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (I : Inv d C hh z) (e : Fin n)
    (H : ¬ReportOwnerReceiptClock.done z ∧
      ReportOwnerReceiptClock.done (step d C N hh F z e)) :
    let y := (step d C N hh F z e).1.val
    readPC d C y=(1,1) ∧ FullParked d C y ∧ Cached d hh Q y := by
  have A := (consume_crossing d C N hh F z I e).mp H
  have P := A.2.2.2.2
  refine ⟨?_,P,(step d C N hh F z e).1.property⟩
  exact pc_fields d C _ .issue1 (by decide) P.1.1

-- The exact checked chronological history is retained, even if the
-- raw observer is subsequently run for further marks after completion.
theorem receipt_history (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) (w : List (Fin n))
    (H : ReportOwnerReceiptClock.done
      (SequentialMarkClock.run (step d C N hh F) (x,none) w)) :
    ∃ pre u post : List (Fin n), w=pre++u++post ∧
      Generated d C (rawRun x.val pre) u .done ∧
      FullParked d C (rawRun x.val (pre++u)) :=
  ReportOwnerReceiptClock.done_has_genuine_cut d C (cached_fibre d N hh Q F) N x w H

theorem fresh_reset_mean_general (d : Sheet) (C : Chart h) (N : 1<n)
    (S : 0<s) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (x : {x : Raw s n // Cached d hh Q x}) :
    Height.IIDExpectedHittingTimeAtMost (step d C N hh F)
      ReportOwnerReceiptClock.done (x,none)
      (n*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits) :=
  ReportPrelaunchDoorReady.receipt_mean d C N S hh G Q F x

inductive Cursor where
  | issue
  | fwd (k : Nat)
  | rev (k : Nat)
  deriving DecidableEq

def On (d : Sheet) (C : Chart h) (x : Raw s n) : Cursor→Prop
  | .issue => LegalIssue d C x
  | .fwd k => ForwardWait d C x k
  | .rev k => ReverseWait d C x k

private theorem cursor_exists (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : Serial d C x) : ∃ m,On d C x m := by
  rcases A with I|⟨k,I⟩|⟨k,I⟩
  · exact ⟨.issue,I⟩
  · exact ⟨.fwd k,I⟩
  · exact ⟨.rev k,I⟩

private theorem front_self (d : Sheet) (C : Chart h) (x : Raw s n)
    (k : Nat) (A : ForwardWait d C x k) : (tok d C x k).tag=2 := by
  simpa [frontTag] using A.2.2 k A.2.1

private theorem back_self (d : Sheet) (C : Chart h) (x : Raw s n)
    (k : Nat) (A : ReverseWait d C x k) : (tok d C x k).tag=3 := by
  simpa [backTag] using A.2.2 k A.2.1

private theorem front_unique_tag (k i : Nat) : frontTag k i=2 ↔ i=k := by
  unfold frontTag
  by_cases E : i=k
  · subst i; simp
  · by_cases L : i<k <;> simp [E,L]

private theorem back_unique_tag (k i : Nat) : backTag k i=3 ↔ i=k := by
  unfold backTag
  by_cases E : i=k
  · subst i; simp
  · by_cases L : i<k <;> simp [E,L]

private theorem back_not_front (k i : Nat) : backTag k i≠2 := by
  unfold backTag
  split <;> try decide
  split <;> decide

private theorem issue_fwd_absurd (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : LegalIssue d C x) (k : Nat) (B : ForwardWait d C x k) : False := by
  have P := A.2.1
  have R := B.1.1
  omega

private theorem issue_rev_absurd (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : LegalIssue d C x) (k : Nat) (B : ReverseWait d C x k) : False := by
  have P := A.2.1
  have R := B.1.1
  omega

private theorem fwd_rev_absurd (d : Sheet) (C : Chart h) (x : Raw s n)
    (k j : Nat) (A : ForwardWait d C x k) (B : ReverseWait d C x j) : False :=
  back_not_front j k ((B.2.2 k A.2.1).symm.trans (front_self d C x k A))

private theorem cursor_unique (d : Sheet) (C : Chart h) (x : Raw s n)
    (m m' : Cursor) (A : On d C x m) (B : On d C x m') : m=m' := by
  cases m with
  | issue =>
    cases m' with
    | issue => rfl
    | fwd k => exact False.elim (issue_fwd_absurd d C x A k B)
    | rev k => exact False.elim (issue_rev_absurd d C x A k B)
  | fwd k =>
    cases m' with
    | issue => exact False.elim (issue_fwd_absurd d C x B k A)
    | fwd j =>
      have E := (front_unique_tag j k).mp
        ((B.2.2 k A.2.1).symm.trans (front_self d C x k A))
      rw [E]
    | rev j => exact False.elim (fwd_rev_absurd d C x k j A B)
  | rev k =>
    cases m' with
    | issue => exact False.elim (issue_rev_absurd d C x B k A)
    | fwd j => exact False.elim (fwd_rev_absurd d C x j k B A)
    | rev j =>
      have E := (back_unique_tag j k).mp
        ((B.2.2 k A.2.1).symm.trans (back_self d C x k A))
      rw [E]

def commandCap (L : Nat) : Nat := 2*L+3
def resetCost (L : Nat) : Nat := 2*L+1

def extraAt (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Nat :=
  extra (C.a+2) k (tok d C x k).race (tok d C x k).fault

def remain (d : Sheet) (C : Chart h) (x : Raw s n) : Cursor→Nat
  | .issue => commandCap C.L
  | .fwd k => 2*C.L-k+extraAt d C x k
  | .rev k => k+1

private theorem remain_bound (d : Sheet) (C : Chart h) (x : Raw s n)
    (m : Cursor) (A : On d C x m) : remain d C x m≤commandCap C.L := by
  cases m with
  | issue => exact Nat.le_refl _
  | fwd k =>
    have B := extra_cap (C.a+2) k (tok d C x k).race (tok d C x k).fault
    simp only [remain,commandCap,extraAt]
    omega
  | rev k =>
    have B := A.2.1
    simp only [remain,commandCap]
    omega

def ordinary (t L a r : Nat) : Nat :=
  (4*t+4-logical t a)*commandCap L+resetCost L+r

def preDebt (d : Sheet) (C : Chart h) (x : Raw s n) (m : Cursor) : Nat :=
  if (readPC d C x).2=0 ∧ m=.issue then resetCost C.L
  else ordinary (params d s).digits C.L (readPC d C x).2 (remain d C x m)

noncomputable def serialDebt (d : Sheet) (C : Chart h) (x : Raw s n) : Nat := by
  classical
  exact if H : ∃ m,On d C x m then preDebt d C x (Classical.choose H) else 0

theorem serialDebt_on (d : Sheet) (C : Chart h) (x : Raw s n)
    (m : Cursor) (A : On d C x m) : serialDebt d C x=preDebt d C x m := by
  classical
  unfold serialDebt
  rw [dif_pos (show ∃ m,On d C x m from ⟨m,A⟩)]
  rw [cursor_unique d C x _ m (Classical.choose_spec (show ∃ m,On d C x m from ⟨m,A⟩)) A]

private theorem preDebt_bound (d : Sheet) (C : Chart h) (x : Raw s n)
    (m : Cursor) (A : On d C x m) :
    preDebt d C x m≤(4*(params d s).digits+7)*commandCap C.L := by
  let t := (params d s).digits
  let B := commandCap C.L
  have H : remain d C x m≤B := remain_bound d C x m A
  have R : resetCost C.L≤B := by unfold resetCost B commandCap; omega
  have Tail : (4*t+4-logical t (readPC d C x).2)*B≤(4*t+4)*B :=
    Nat.mul_le_mul_right B (Nat.sub_le _ _)
  have U : (4*t+7)*B=(4*t+4)*B+3*B := by
    rw [show 4*t+7=(4*t+4)+3 by omega,Nat.add_mul]
  change preDebt d C x m≤(4*t+7)*B
  rw [U]
  unfold preDebt
  split
  · omega
  · change ordinary t C.L (readPC d C x).2 (remain d C x m)≤_
    unfold ordinary
    change _*B+resetCost C.L+remain d C x m≤_
    omega

-- ownerPC's lossy view is used ONLY for the literal launch.
theorem issue0_iff (d : Sheet) (C : Chart h) (x : Raw s n) :
    ownerPC d C x=.issue0 ↔ readPC d C x=(1,0) := by
  constructor
  · exact fun H=>pc_fields d C x .issue0 (by decide) H
  · intro H
    change pcView (readPC d C x)=.issue0
    rw [H]
    rfl

private theorem fresh_issue_pose (d : Sheet) (C : Chart h) (x : Raw s n)
    (m : Cursor) (A : On d C x m) (P : ownerPC d C x=.issue0) : m=.issue := by
  have E := congrArg Prod.fst ((issue0_iff d C x).mp P)
  cases m with
  | issue => rfl
  | fwd k => have B := A.1.1; omega
  | rev k => have B := A.1.1; omega

theorem serialDebt_issue0 (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : Serial d C x) (P : ownerPC d C x=.issue0) :
    serialDebt d C x=resetCost C.L := by
  obtain ⟨m,A⟩ := cursor_exists d C x S
  have J := fresh_issue_pose d C x m A P
  subst m
  rw [serialDebt_on d C x .issue A]
  simp [preDebt,congrArg Prod.snd ((issue0_iff d C x).mp P)]

private theorem rows_at (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) :
    RowCases d C (Cached d hh Q) :=
  ReportPrelaunchK1.rowCases d C hh G Q F N
    (ReportPrelaunchDoorLift.doorCases d C hh G F N
      (ReportPrelaunchDoorProducer.rootRows d C (Cached d hh Q) N digit
        (cached_fibre d N hh Q F).mask))

-- Stronger source-consume cut: the all-mark hold disjunction cannot
-- be used at a root D consume. This is the same literal old-source
-- calculation as the last reverse branch of pc_step_with_phase.
private theorem consume_opcode (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (R : ReverseWait d C x 0) :
    let y := rawNext s x (door C)
    (readPC d C y).2=0 ∨
      PreviewNextOp (params d s).digits (readPC d C x).2 (readPC d C y).2 := by
  dsimp only
  let p := params d s
  let v := selectBytes d (x C.root)
  let z := publicationToken p true v 0
  have TE : tok d C x 0=z := by
    rw [ReportPrelaunchDoorLift.root_tok]; rfl
  have T : z.tag=3 := by rw [←TE]; exact back_self d C x 0 R
  have W := (raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)).1
  rcases prelaunch_wait_controls p v z R.1.1 R.1.2
      (by rw [T]; decide) (by rw [T]; decide) digit with B|⟨a,B,J⟩
  · exact .inl (congrArg Prod.snd (W.trans B))
  · right
    have E : (readPC d C (rawNext s x (door C))).2=a :=
      congrArg Prod.snd (W.trans J)
    rw [E]
    exact B

private theorem wait_pc (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x) (e : Fin n)
    (A : LegalWait d C x) (B : LegalWait d C (rawNext s x e)) :
    readPC d C (rawNext s x e)=readPC d C x := by
  apply Prod.ext (B.1.trans A.1.symm)
  rcases pc_step_with_phase d C N hh G F digit x X S e with R|R|⟨P,_⟩
  · have E := R.2.1
    have W := B.1
    omega
  · exact R
  · have W := B.1
    omega

private theorem nonfront_weight (d : Sheet) (C : Chart h)
    (x y : Raw s n) (i : Fin C.L)
    (T : (tok d C y i.val).tag=(tok d C x i.val).tag)
    (NF : (tok d C x i.val).tag≠2) :
    weight d C y i=weight d C x i := by
  unfold weight label
  rw [T]
  simp only [if_neg NF]

private theorem all_tag_frame (d : Sheet) (C : Chart h) (x y : Raw s n)
    (m : Cursor) (A : On d C x m) (B : On d C y m)
    (i : Fin C.L) :
    (tok d C y i.val).tag=(tok d C x i.val).tag := by
  cases m with
  | issue => exact (B.2.2 i.val i.isLt).trans (A.2.2 i.val i.isLt).symm
  | fwd k => exact (B.2.2 i.val i.isLt).trans (A.2.2 i.val i.isLt).symm
  | rev k => exact (B.2.2 i.val i.isLt).trans (A.2.2 i.val i.isLt).symm

private theorem front_weight (d : Sheet) (C : Chart h) (x : Raw s n)
    (k : Nat) (A : ForwardWait d C x k) :
    weight d C x ⟨k,A.2.1⟩=3*C.L-2*k+extraAt d C x k := by
  simp [weight,label,front_self d C x k A,ReportPrelaunchRank.rank,extraAt]

-- For an unchanged cursor, all weights except the unique F's
-- are literally equal. A pot comparison therefore gives exactly
-- the comparison of local remaining costs.
private theorem same_cursor_remain (d : Sheet) (C : Chart h)
    (x y : Raw s n) (m : Cursor) (A : On d C x m) (B : On d C y m)
    (PC : readPC d C y=readPC d C x)
    (P : pot d C y≤pot d C x) :
    remain d C y m≤remain d C x m ∧
      (pot d C y<pot d C x→remain d C y m<remain d C x m) := by
  have D : debtOf d C y=debtOf d C x := by unfold debtOf; rw [PC]
  have equal_pot (W : ∀ i,weight d C y i=weight d C x i) :
      pot d C y=pot d C x := by
    unfold pot
    rw [D,show weight d C y=weight d C x from funext W]
  cases m with
  | issue =>
    have E := equal_pot (fun i=>nonfront_weight d C x y i
      (all_tag_frame d C x y .issue A B i)
      (by rw [A.2.2 i.val i.isLt]; decide))
    exact ⟨Nat.le_refl _,fun H=>False.elim ((Nat.ne_of_lt H) E)⟩
  | rev k =>
    have E := equal_pot (fun i=>nonfront_weight d C x y i
      (all_tag_frame d C x y (.rev k) A B i)
      (by rw [A.2.2 i.val i.isLt]; exact back_not_front k i.val))
    exact ⟨Nat.le_refl _,fun H=>False.elim ((Nat.ne_of_lt H) E)⟩
  | fwd k =>
    let i : Fin C.L := ⟨k,A.2.1⟩
    have Frame (j : Fin C.L) (J : j≠i) :
        weight d C y j=weight d C x j := by
      have U : j.val≠k := fun V=>J (Fin.ext V)
      apply nonfront_weight d C x y j (all_tag_frame d C x y (.fwd k) A B j)
      rw [A.2.2 j.val j.isLt]
      exact fun T=>U ((front_unique_tag k j.val).mp T)
    have WX : weight d C x i=3*C.L-2*k+extraAt d C x k :=
      front_weight d C x k A
    have WY : weight d C y i=3*C.L-2*k+extraAt d C y k :=
      front_weight d C y k B
    have L : weight d C y i≤weight d C x i := by
      apply Classical.byContradiction
      intro H
      have T := single_total_strict (weight d C y) (weight d C x) i
        (fun j J=>(Frame j J).symm) (by omega)
      unfold pot at P
      rw [D] at P
      omega
    have R : extraAt d C y k≤extraAt d C x k := by rw [WX,WY] at L; omega
    refine ⟨?_,?_⟩
    · simp only [remain]; omega
    · intro S
      have Strict : weight d C y i<weight d C x i := by
        apply Classical.byContradiction
        intro H
        have E : weight d C y i=weight d C x i := by omega
        have P0 := equal_pot (fun j=>by
          by_cases J : j=i
          · subst j; exact E
          · exact Frame j J)
        omega
      rw [WX,WY] at Strict
      simp only [remain]
      omega

private theorem same_cursor_debt (d : Sheet) (C : Chart h)
    (x y : Raw s n) (m : Cursor) (A : On d C x m) (B : On d C y m)
    (PC : readPC d C y=readPC d C x)
    (P : pot d C y≤pot d C x) :
    preDebt d C y m≤preDebt d C x m ∧
      (pot d C y<pot d C x→preDebt d C y m<preDebt d C x m) := by
  obtain ⟨L,R⟩ := same_cursor_remain d C x y m A B PC P
  unfold preDebt
  rw [PC]
  by_cases E : (readPC d C x).2=0 ∧ m=.issue
  · simp only [if_pos E]
    refine ⟨Nat.le_refl _,fun H=>?_⟩
    have H' := R H
    rw [E.2] at H'
    simp [remain] at H'
  · simp only [if_neg E]
    unfold ordinary
    exact ⟨Nat.add_le_add_left L _,fun H=>Nat.add_lt_add_left (R H) _⟩

private theorem ordinary_move (d : Sheet) (C : Chart h) (x y : Raw s n)
    (m m' : Cursor)
    (P : (readPC d C y).2=(readPC d C x).2)
    (A : ¬((readPC d C x).2=0 ∧ m=.issue))
    (B : ¬((readPC d C y).2=0 ∧ m'=.issue))
    (L : remain d C y m'<remain d C x m) :
    preDebt d C y m'<preDebt d C x m := by
  unfold preDebt
  rw [if_neg A,if_neg B]
  unfold ordinary
  rw [P]
  exact Nat.add_lt_add_left L _

private theorem retry_debt (d : Sheet) (C : Chart h) (x y : Raw s n)
    (m : Cursor)
    (A : ¬((readPC d C x).2=0 ∧ m=.issue))
    (P : (readPC d C y).2=0) (R : 0<remain d C x m) :
    preDebt d C y .issue<preDebt d C x m := by
  unfold preDebt
  rw [if_neg A,if_pos ⟨P,rfl⟩]
  unfold ordinary
  omega

private theorem next_consume_debt (d : Sheet) (C : Chart h) (x y : Raw s n)
    (P : PreviewNextOp (params d s).digits (readPC d C x).2 (readPC d C y).2) :
    preDebt d C y .issue<preDebt d C x (.rev 0) := by
  let t := (params d s).digits
  let a := (readPC d C x).2
  let b := (readPC d C y).2
  have B : b≠0 := preview_target_positive P
  have J : logical t b=logical t a+1 := preview_logical P
  have U : logical t b<4*t+5 := logical_le (previewNextOp_bounds P).2
  have E : 4*t+4-logical t a=(4*t+4-logical t b)+1 := by omega
  change (if b=0 ∧ Cursor.issue=Cursor.issue then _ else _) <
    (if a=0 ∧ Cursor.rev 0=Cursor.issue then _ else _)
  rw [if_neg (fun H=>B H.1),if_neg (fun H=>by cases H.2)]
  change ordinary t C.L b (commandCap C.L)<ordinary t C.L a 1
  unfold ordinary
  rw [E,Nat.add_mul,Nat.one_mul]
  omega

theorem pre_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x)
    (m : Cursor) (A : On d C x m) (e : Fin n)
    (NL : ¬Launch d C x e) :
    let y := rawNext s x e
    ∃ m',On d C y m' ∧ preDebt d C y m'≤preDebt d C x m ∧
      (Paid d C x y→preDebt d C y m'<preDebt d C x m) := by
  dsimp only
  let y := rawNext s x e
  have PL : pot d C y≤pot d C x := by
    rcases (rows_at d C N hh G F digit).casesAt x e X NL with W|P
    · exact weak_le d C x y W
    · exact Nat.le_of_lt (paid_lt d C x y P)
  have same (V : On d C y m) (P : readPC d C y=readPC d C x) :
      ∃ m',On d C y m' ∧ preDebt d C y m'≤preDebt d C x m ∧
        (Paid d C x y→preDebt d C y m'<preDebt d C x m) := by
    obtain ⟨L,R⟩ := same_cursor_debt d C x y m A V P PL
    exact ⟨m,V,L,fun H=>R (paid_lt d C x y H)⟩
  have strict (m' : Cursor) (V : On d C y m') (L : preDebt d C y m'<preDebt d C x m) :
      ∃ m',On d C y m' ∧ preDebt d C y m'≤preDebt d C x m ∧
        (Paid d C x y→preDebt d C y m'<preDebt d C x m) :=
    ⟨m',V,Nat.le_of_lt L,fun _=>L⟩
  cases m with
  | issue =>
    change LegalIssue d C x at A
    by_cases E : e=door C
    · have P0 : (readPC d C x).2≠0 := by
        intro Z
        apply NL
        exact ⟨(issue0_iff d C x).mpr (Prod.ext A.2.1 Z),E⟩
      subst e
      rcases door_step d C hh G F N x X A with R|⟨V,P⟩
      · have J : LegalIssue d C y := ⟨by rw [R.1]; exact Nat.zero_le _,R.2⟩
        exact strict .issue J (retry_debt d C x y .issue
          (fun U=>P0 U.1) R.1 (by simp [remain,commandCap]))
      · apply strict (.fwd 0) V
        apply ordinary_move d C x y .issue (.fwd 0) P
          (fun U=>P0 U.1) (fun U=>by cases U.2)
        have L := extra_cap (C.a+2) 0 (tok d C y 0).race (tok d C y 0).fault
        simp only [remain,commandCap,extraAt,Nat.sub_zero]
        omega
    · obtain ⟨V,P⟩ := nondoor_preserves d C hh G F N x X A e E
      exact same V P
  | fwd k =>
    change ForwardWait d C x k at A
    rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k A e with
      V|⟨E,V|⟨J,V⟩⟩
    · exact same V (wait_pc d C N hh G F digit x X S e A.1 V.1)
    · apply strict (.fwd (k+1)) V
      apply ordinary_move d C x y (.fwd k) (.fwd (k+1))
        (congrArg Prod.snd (wait_pc d C N hh G F digit x X S e A.1 V.1))
        (fun U=>by cases U.2) (fun U=>by cases U.2)
      have L := extra_forward (C.a+2) k (tok d C x k).race
        (tok d C y (k+1)).race (tok d C x k).fault (tok d C y (k+1)).fault
      have K := A.2.1
      simp only [remain,extraAt]
      omega
    · apply strict (.rev k) V
      apply ordinary_move d C x y (.fwd k) (.rev k)
        (congrArg Prod.snd (wait_pc d C N hh G F digit x X S e A.1 V.1))
        (fun U=>by cases U.2) (fun U=>by cases U.2)
      simp only [remain]
      omega
  | rev k =>
    change ReverseWait d C x k at A
    rcases ReportOwnerReverseControl.all_mark d C hh G F N x X k A digit e with
      V|⟨j,J,E,V⟩|⟨K,E,V⟩
    · exact same V (wait_pc d C N hh G F digit x X S e A.1 V.1)
    · apply strict (.rev j) V
      apply ordinary_move d C x y (.rev k) (.rev j)
        (congrArg Prod.snd (wait_pc d C N hh G F digit x X S e A.1 V.1))
        (fun U=>by cases U.2) (fun U=>by cases U.2)
      simp only [remain]
      omega
    · subst k e
      rcases consume_opcode d C N hh F digit x X A with R|R
      · have J : LegalIssue d C y := ⟨by rw [R]; exact Nat.zero_le _,V⟩
        exact strict .issue J (retry_debt d C x y (.rev 0)
          (fun U=>by cases U.2) R (by simp [remain]))
      · have B := (previewNextOp_bounds R).2
        have J : LegalIssue d C y := ⟨by have E : y=rawNext s x (door C) := rfl; rw [E]; unfold commitOp; omega,V⟩
        exact strict .issue J (next_consume_debt d C x y R)

theorem serial_step_nonlaunch (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x) (e : Fin n)
    (NL : ¬Launch d C x e) :
    let y := rawNext s x e
    serialDebt d C y≤serialDebt d C x ∧
      (Paid d C x y→serialDebt d C y<serialDebt d C x) := by
  dsimp only
  obtain ⟨m,A⟩ := cursor_exists d C x S.1
  obtain ⟨m',B,L,R⟩ := pre_step d C N hh G F digit x X S m A e NL
  rw [serialDebt_on d C x m A,serialDebt_on d C (rawNext s x e) m' B]
  exact ⟨L,R⟩

noncomputable def freshDebt (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (z : State d hh Q) : Nat :=
  match z.2 with
  | none => serialDebt d C z.1.val
  | some st => ShortResetCycle.debt C.L st

private theorem stage_live (d : Sheet) (C : Chart h) (x : Raw s n)
    (st : Stage) (H : st≠.done) (A : FullActive d C x st) :
    (match st with | .fwd k | .rev k => k<C.L | .done => False) := by
  cases st with
  | fwd k => exact A.1.1.1
  | rev k => exact A.1.1.1
  | done => exact H rfl

theorem freshDebt_bound (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (z : State d hh Q) (I : Inv d C hh z) :
    freshDebt d C hh z≤(4*(params d s).digits+7)*commandCap C.L := by
  let t := (params d s).digits
  have K : 2*C.L≤(4*t+7)*commandCap C.L := by
    have B : 1≤4*t+7 := by omega
    have H := Nat.mul_le_mul_right (commandCap C.L) B
    rw [Nat.one_mul] at H
    exact Nat.le_trans (by unfold commandCap; omega) H
  cases E : z.2 with
  | none =>
    obtain ⟨m,A⟩ := cursor_exists d C z.1.val I.1.1
    simpa only [freshDebt,E,serialDebt_on d C z.1.val m A] using preDebt_bound d C z.1.val m A
  | some st =>
    by_cases H : st=.done
    · subst st
      simp [freshDebt,E,ShortResetCycle.debt]
    · have V := stage_live d C z.1.val st H (I.2 st E H)
      cases st with
      | done => exact False.elim (H rfl)
      | fwd k =>
        simp only [freshDebt,E,ShortResetCycle.debt]
        exact Nat.le_trans (Nat.sub_le _ _) K
      | rev k =>
        simp only [freshDebt,E,ShortResetCycle.debt]
        change k<C.L at V
        exact Nat.le_trans (show k+1≤2*C.L by omega) K

theorem freshDebt_idle (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (z : State d hh Q)
    (I : Inv d C hh z) (e : Fin n) :
    freshDebt d C hh (step d C N hh F z e)≤freshDebt d C hh z := by
  let CF := cached_fibre d N hh Q F
  cases E : z.2 with
  | none =>
    by_cases L : Launch d C z.1.val e
    · have P := serialDebt_issue0 d C z.1.val I.1.1 L.1
      have S : (step d C N hh F z e).2=some (.fwd 0) := by
        change (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F) z e).2=_
        simp [ReportOwnerReceiptClock.next,E,L.1,L.2]
      rw [show freshDebt d C hh (step d C N hh F z e)=2*C.L by
        simp [freshDebt,S,ShortResetCycle.debt]]
      simp only [freshDebt,E,P,resetCost]
      omega
    · have S : (step d C N hh F z e).2=none := by
        change (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F) z e).2=_
        simp [ReportOwnerReceiptClock.next,E,show ¬(ownerPC d C z.1.val=.issue0 ∧ e=door C) from L]
      have R := (serial_step_nonlaunch d C N hh G F digit
        z.1.val z.1.property I.1 e L).1
      simpa only [freshDebt,E,S,step_raw] using R
  | some st =>
    have S : (step d C N hh F z e).2=some (nextStage C e st) := by
      simp [step,ReportOwnerReceiptClock.next,E]
    simp only [freshDebt,E,S]
    by_cases H : st=.done
    · subst st; exact Nat.le_refl _
    · exact (ShortResetCycle.debt_step C st
        (by cases st <;> exact stage_live d C z.1.val _ H (I.2 _ E H))).1 e

theorem freshDebt_nominate (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (z : State d hh Q)
    (I : Inv d C hh z) (H : ¬ReportOwnerReceiptClock.done z) :
    ∃ e,freshDebt d C hh (step d C N hh F z e)<freshDebt d C hh z := by
  cases E : z.2 with
  | none =>
    obtain ⟨e,P⟩ := ReportPrelaunchClock.nominate d C (Cached d hh Q)
      (rows_at d C N hh G F digit) z.1.val z.1.property
    refine ⟨e,?_⟩
    by_cases L : Launch d C z.1.val e
    · have S : (step d C N hh F z e).2=some (.fwd 0) := by
        change (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F) z e).2=_
        simp [ReportOwnerReceiptClock.next,E,L.1,L.2]
      have R := serialDebt_issue0 d C z.1.val I.1.1 L.1
      simp only [freshDebt,E,S,ShortResetCycle.debt,Nat.sub_zero,R,resetCost]
      omega
    · have S : (step d C N hh F z e).2=none := by
        change (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F) z e).2=_
        simp [ReportOwnerReceiptClock.next,E,show ¬(ownerPC d C z.1.val=.issue0 ∧ e=door C) from L]
      have R := (serial_step_nonlaunch d C N hh G F digit
        z.1.val z.1.property I.1 e L).2 (P.resolve_left L)
      simpa only [freshDebt,E,S,step_raw] using R
  | some st =>
    have ND : st≠.done := by
      intro J
      subst st
      exact H E
    obtain ⟨e,P⟩ := (ShortResetCycle.debt_step C st
      (by cases st <;> exact stage_live d C z.1.val _ ND (I.2 _ E ND))).2
    have S : (step d C N hh F z e).2=some (nextStage C e st) := by
      simp [step,ReportOwnerReceiptClock.next,E]
    refine ⟨e,?_⟩
    simp only [freshDebt,E,S]
    omega

theorem fresh_nomination (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) :
    ReportAdaptiveFibre.Nomination (step d C N hh F) (Inv d C hh)
      ReportOwnerReceiptClock.done (freshDebt d C hh) where
  closed := fun z e I=>inv_closed d C N hh G F digit z e I
  idle := fun z e I _=>freshDebt_idle d C N hh G F digit z I e
  progress := fun z I H=>freshDebt_nominate d C N hh G F digit z I H

theorem fresh_reset_mean_serial (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : {x : Raw s n // Cached d hh Q x})
    (S : StrongSerial d C x.val) :
    Height.IIDExpectedHittingTimeAtMost (step d C N hh F)
      ReportOwnerReceiptClock.done (x,none)
      (n*((4*(params d s).digits+7)*commandCap C.L)) := by
  have I := initial_inv d C hh x S
  have R := ReportAdaptiveFibre.nominated_mean (step d C N hh F) (Inv d C hh)
    ReportOwnerReceiptClock.done (freshDebt d C hh)
    (fresh_nomination d C N hh G F digit) (x,none) I
  intro k
  exact Nat.le_trans (R k) (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left n (freshDebt_bound d C hh (x,none) I)))

-- Per-chart budget, in the deployed width convention.
theorem reset_budget {t L W : Nat} (T : 0<t) (W3 : 3≤W) (L3 : L≤3*W) :
    (4*t+7)*commandCap L≤77*t*W := by
  have A : 4*t+7≤11*t := by omega
  have B : commandCap L≤7*W := by unfold commandCap; omega
  calc
    _ ≤ (11*t)*(7*W) := Nat.mul_le_mul A B
    _ = 77*t*W := by
      rw [show 77=11*7 by decide]
      ac_rfl

theorem fresh_reset_mean_fast (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (W : Nat) (W3 : 3≤W) (L3 : C.L≤3*W)
    (x : {x : Raw s n // Cached d hh Q x}) (S : StrongSerial d C x.val) :
    Height.IIDExpectedHittingTimeAtMost (step d C N hh F)
      ReportOwnerReceiptClock.done (x,none) (77*(params d s).digits*W*n) := by
  intro k
  have R := fresh_reset_mean_serial d C N hh G F digit x S k
  have L := Nat.mul_le_mul_left n (reset_budget digit W3 L3)
  rw [Nat.mul_comm n (77*(params d s).digits*W)] at L
  exact Nat.le_trans R (Nat.mul_le_mul_right _ L)

-- The bank history supplies StrongSerial on any owner chart;
-- no additional arithmetic-success hypothesis is necessary.
theorem strong_from_bank (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (B : ReportGoodEightBank.GoodEightBank d hh Q G x)
    (M : C∈ReportPrelaunchAllOwners.ownerCharts G) :
    StrongSerial d C x := by
  obtain ⟨a,u,v,A,R,_,E⟩ := ReportGoodEightCut.second_owner_seed
    d N hh G F digit x B.1 C M
  have X : Cached d hh Q a := A.1.1.1
  have Y := ReportGoodEightCut.cached_run d N hh F a X u
  have S := seed_receipt d C N hh F a X u R
  rw [E]
  exact (strong_run d C N hh G F digit _ Y S v).2.1

theorem crossing_debt (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (e : Fin n)
    (H : ¬ReportOwnerReceiptClock.done z ∧
      ReportOwnerReceiptClock.done (step d C N hh F z e)) :
    freshDebt d C hh z=1 ∧ freshDebt d C hh (step d C N hh F z e)=0 := by
  have E := ((done_rise_stage_iff d C N hh F z e).mp H).1
  have D : (step d C N hh F z e).2=some .done := H.2
  simp [freshDebt,E,D,ShortResetCycle.debt]

theorem publication_reserve {t L W : Nat} (T : 0<t) (W3 : 3≤W) (L3 : L≤3*W) :
    (4*t+4)*commandCap L≤56*t*W := by
  have A : 4*t+4≤8*t := by omega
  have B : commandCap L≤7*W := by unfold commandCap; omega
  calc
    _ ≤ (8*t)*(7*W) := Nat.mul_le_mul A B
    _ = 56*t*W := by rw [show 56=8*7 by decide]; ac_rfl

def resetReserve (t W : Nat) : Nat := 77*t*W
def pubReserve (t W : Nat) : Nat := 56*t*W

-- k = number of future RESET phases AFTER the current one.
-- At most five such phases remain at initialization of the six.
def prepDebt (t W k localDebt : Nat) : Nat :=
  localDebt+k*resetReserve t W+pubReserve t W

theorem prep_budget {t W k localDebt : Nat}
    (K : k≤5) (R : localDebt≤resetReserve t W) :
    prepDebt t W k localDebt≤518*t*W := by
  have A := Nat.mul_le_mul_right (resetReserve t W) K
  have B : 6*resetReserve t W+pubReserve t W=518*t*W := by
    unfold resetReserve pubReserve
    rw [show 6*(77*t*W)=(6*77)*t*W by ac_rfl,←Nat.add_mul,←Nat.add_mul]
  unfold prepDebt
  omega

-- The actual target receipt consumes the last RESET event.  The
-- positive-program reserve was already included in the old debt.
theorem final_handoff_rank {t W newDebt : Nat} {a b : Bool}
    (R : newDebt≤pubReserve t W) :
    ReportFastKernel.eventRank newDebt b <
      ReportFastKernel.eventRank (prepDebt t W 0 1) a := by
  apply ReportFastKernel.eventRank_progress
  left
  unfold prepDebt
  simp only [Nat.zero_mul,Nat.add_zero]
  omega

-- Between preparation phases: a consume of the current tracked
-- receipt pays one, the next monitor starts at its actual endpoint.
-- Even a new unspent blocking bit is paid by the strict debt decrease.
theorem next_reset_handoff_rank {t W k newDebt : Nat} {a b : Bool}
    (R : newDebt≤resetReserve t W) :
    ReportFastKernel.eventRank (prepDebt t W k newDebt) b <
      ReportFastKernel.eventRank (prepDebt t W (k+1) 1) a := by
  apply ReportFastKernel.eventRank_progress
  left
  unfold prepDebt
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem prep_idle {t W k m m' : Nat} (H : m'≤m) :
    prepDebt t W k m'≤prepDebt t W k m :=
  Nat.add_le_add_right (Nat.add_le_add_right H _) _

theorem prep_progress {t W k m m' : Nat} (H : m'<m) :
    prepDebt t W k m'<prepDebt t W k m :=
  Nat.add_lt_add_right (Nat.add_lt_add_right H _) _

-- Exact interface to the PhaseRows bound, for an arbitrary observer
-- whose debt is this reserve during preparation and bounded by the
-- publication reserve afterwards. There is no PaperKernel hypothesis.
theorem service_fresh_reset_bound {Y : Type} (Q0 : Y→Prop)
    (debt : Y→Nat) (t W : Nat)
    (Budget : ∀ y,Q0 y→
      (∃ k localDebt,k≤5 ∧ localDebt≤resetReserve t W ∧
        debt y=prepDebt t W k localDebt) ∨ debt y≤pubReserve t W) :
    ∀ y,Q0 y→debt y≤518*t*W := by
  intro y H
  rcases Budget y H with ⟨k,r,K,R,E⟩|P
  · rw [E]
    exact prep_budget K R
  · have B : pubReserve t W≤518*t*W := by
      unfold pubReserve
      exact Nat.mul_le_mul_right W (Nat.mul_le_mul_right t (by decide))
    exact Nat.le_trans P B

-- Each current reset monitor discharges the concrete local
-- antecedent of the preceding bound using its actual Inv.
theorem local_reserve (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (digit : 0<(params d s).digits) (W : Nat) (W3 : 3≤W) (L3 : C.L≤3*W)
    (z : State d hh Q) (I : Inv d C hh z) :
    freshDebt d C hh z≤resetReserve (params d s).digits W :=
  Nat.le_trans (freshDebt_bound d C hh z I) (reset_budget digit W3 L3)

-- For the LAST target receipt, the exact raw cut and both rank
-- components are supplied together, not just numerical inequalities.
theorem target_cut_handoff (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (W : Nat) (W3 : 3≤W) (L3 : C.L≤3*W)
    (z : State d hh Q) (I : Inv d C hh z) (e : Fin n)
    (H : ¬ReportOwnerReceiptClock.done z ∧
      ReportOwnerReceiptClock.done (step d C N hh F z e))
    (a b : Bool) :
    let y := (step d C N hh F z e).1.val
    readPC d C y=(1,1) ∧ FullParked d C y ∧
    freshDebt d C hh z=1 ∧ freshDebt d C hh (step d C N hh F z e)=0 ∧
    (4*(params d s).digits+4)*commandCap C.L≤pubReserve (params d s).digits W ∧
    ReportFastKernel.eventRank ((4*(params d s).digits+4)*commandCap C.L) b <
      ReportFastKernel.eventRank
        (prepDebt (params d s).digits W 0 (freshDebt d C hh z)) a := by
  dsimp only
  obtain ⟨P,V,_⟩ := crossing_parked d C N hh F z I e H
  obtain ⟨A,B⟩ := crossing_debt d C N hh F z e H
  have R := publication_reserve digit W3 L3
  refine ⟨P,V,A,B,R,?_⟩
  rw [A]
  exact final_handoff_rank R

end L4.ReportFastFreshReset

namespace L4.ReportFastFreshReset
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerForwardControl ReportOwnerReverseControl ReportOwnerIssueControl
open ReportOwnerSerial ReportOwnerCommandRail ReportOwnerProvenanceTransport
open ReportByteRows ReportRawProjection ReportFastGateRaw ReportFastOwnerSupport
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem pre_plateau_cursor (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x)
    (m : Cursor) (A : On d C x m) (e : Fin n)
    (NL : ¬Launch d C x e)
    (Eq : serialDebt d C (rawNext s x e)=serialDebt d C x) :
    On d C (rawNext s x e) m ∧ readPC d C (rawNext s x e)=readPC d C x := by
  let y := rawNext s x e
  have impossible (m' : Cursor) (V : On d C y m')
      (H : preDebt d C y m'<preDebt d C x m) : False := by
    have R := Eq
    change serialDebt d C y=serialDebt d C x at R
    rw [serialDebt_on d C y m' V,serialDebt_on d C x m A] at R
    omega
  cases m with
  | issue =>
    change LegalIssue d C x at A
    by_cases D : e=door C
    · have P0 : (readPC d C x).2≠0 := by
        intro Z
        exact NL ⟨(issue0_iff d C x).mpr (Prod.ext A.2.1 Z),D⟩
      subst e
      rcases door_step d C hh G F N x X A with R|⟨V,P⟩
      · have J : LegalIssue d C y := ⟨by rw [R.1]; exact Nat.zero_le _,R.2⟩
        exact False.elim (impossible .issue J (retry_debt d C x y .issue
          (fun U=>P0 U.1) R.1 (by simp [remain,commandCap])))
      · have L : preDebt d C y (.fwd 0)<preDebt d C x .issue := by
          apply ordinary_move d C x y .issue (.fwd 0) P
            (fun U=>P0 U.1) (fun U=>by cases U.2)
          have B := extra_cap (C.a+2) 0 (tok d C y 0).race (tok d C y 0).fault
          simp only [remain,commandCap,extraAt,Nat.sub_zero]
          omega
        exact False.elim (impossible (.fwd 0) V L)
    · exact nondoor_preserves d C hh G F N x X A e D
  | fwd k =>
    change ForwardWait d C x k at A
    rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k A e with
      V|⟨_,V|⟨J,V⟩⟩
    · exact ⟨V,wait_pc d C N hh G F digit x X S e A.1 V.1⟩
    · have L : preDebt d C y (.fwd (k+1))<preDebt d C x (.fwd k) := by
        apply ordinary_move d C x y (.fwd k) (.fwd (k+1))
          (congrArg Prod.snd (wait_pc d C N hh G F digit x X S e A.1 V.1))
          (fun U=>by cases U.2) (fun U=>by cases U.2)
        have B := extra_forward (C.a+2) k (tok d C x k).race
          (tok d C y (k+1)).race (tok d C x k).fault (tok d C y (k+1)).fault
        have K := A.2.1
        simp only [remain,extraAt]
        omega
      exact False.elim (impossible (.fwd (k+1)) V L)
    · have L : preDebt d C y (.rev k)<preDebt d C x (.fwd k) := by
        apply ordinary_move d C x y (.fwd k) (.rev k)
          (congrArg Prod.snd (wait_pc d C N hh G F digit x X S e A.1 V.1))
          (fun U=>by cases U.2) (fun U=>by cases U.2)
        simp only [remain]
        omega
      exact False.elim (impossible (.rev k) V L)
  | rev k =>
    change ReverseWait d C x k at A
    rcases ReportOwnerReverseControl.all_mark d C hh G F N x X k A digit e with
      V|⟨j,J,_,V⟩|⟨K,E,V⟩
    · exact ⟨V,wait_pc d C N hh G F digit x X S e A.1 V.1⟩
    · have L : preDebt d C y (.rev j)<preDebt d C x (.rev k) := by
        apply ordinary_move d C x y (.rev k) (.rev j)
          (congrArg Prod.snd (wait_pc d C N hh G F digit x X S e A.1 V.1))
          (fun U=>by cases U.2) (fun U=>by cases U.2)
        simp only [remain]
        omega
      exact False.elim (impossible (.rev j) V L)
    · subst k e
      rcases consume_opcode d C N hh F digit x X A with R|R
      · have J : LegalIssue d C y := ⟨by rw [R]; exact Nat.zero_le _,V⟩
        exact False.elim (impossible .issue J (retry_debt d C x y (.rev 0)
          (fun U=>by cases U.2) R (by simp [remain])))
      · have B := (previewNextOp_bounds R).2
        have J : LegalIssue d C y := ⟨by have E : y=rawNext s x (door C) := rfl; rw [E]; unfold commitOp; omega,V⟩
        exact False.elim (impossible .issue J (next_consume_debt d C x y R))

-- At a same-position F and the same complete PC, equality of the
-- compact debt is exactly equality of its remaining gate extra.
private theorem plateau_extra (d : Sheet) (C : Chart h) (x y : Raw s n)
    (k : Nat) (A : ForwardWait d C x k) (B : ForwardWait d C y k)
    (PC : readPC d C y=readPC d C x)
    (E : serialDebt d C y=serialDebt d C x) :
    extraAt d C y k=extraAt d C x k := by
  rw [serialDebt_on d C y (.fwd k) B,serialDebt_on d C x (.fwd k) A] at E
  unfold preDebt at E
  rw [if_neg (fun H=>by cases H.2),if_neg (fun H=>by cases H.2)] at E
  unfold ordinary at E
  rw [PC] at E
  simp only [remain] at E
  omega

private theorem incoming_front_norm_all (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x)
    (i : Nat) (I : i+1<C.L)
    (A : chartGate d C x (i+1)=true) (S : ForwardWait d C x (i+1)) :
    tok d C (rawNext s x (out C i)) (i+1)=
      decode (params d s) true
        (rankNormWire (params d s) 2 true (wire d C x (i+1))) := by
  let e := out C i
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have W := raw_pair_wire d C x N (CF.mask x X) i
  have PT : (tok d C x i).tag=1 := by
    simpa [frontTag,show i<i+1 by omega] using S.2.2 i (by omega)
  have NR : readyAt d C x i=false :=
    Bool.eq_false_iff.mpr (fun R=>by
      have H := ((ready_iff d C x i).mp R).1
      omega)
  have DT : (tok d C x (i+1)).tag=2 := front_self d C x (i+1) S
  have D : (publicationToken (params d s) (h (rightNeighbor e))
       (bytesR d x e) (C.route.port (i+1))).tag≠3 := by
    rw [←successor_projection d C x i,DT]
    decide
  have E := rank_idle_right (params d s) (h e) (h (rightNeighbor e))
    (bytesL d x e) (bytesR d x e) _ _ (internal_dest C i I) NR (.inr D)
  rw [tok_wire,gate_frame d C hh G x y X Y (i+1) I,W.2,workR,E]
  -- CHECK: ReportOwnerProvenanceTransport:25,165–167 uses these
  -- same old successor definitional rewrites.
  change decode (params d s) (chartGate d C x (i+1))
    (rankNormWire (params d s) 2 (chartGate d C x (i+1))
      (wire d C x (i+1)))=_
  rw [A]

private theorem norm_plateau_gate (d : Sheet) (C : Chart h) (x y : Raw s n)
    (A : chartGate d C x (C.a+2)=true)
    (side : Nat) (S : side=2 ∨ side=3)
    (E : tok d C y (C.a+2)=
      decode (params d s) true
        (rankNormWire (params d s) side true (wire d C x (C.a+2))))
    (P : extraAt d C y (C.a+2)=extraAt d C x (C.a+2)) :
    tok d C y (C.a+2)=tok d C x (C.a+2) := by
  have TX : tok d C x (C.a+2)=decode (params d s) true (wire d C x (C.a+2)) := by
    rw [tok_wire,A]
  have V := rank_norm_cases (params d s) true (wire d C x (C.a+2)) side S
  dsimp only at V
  rcases V with V|⟨_,_,F0,_,F1,R⟩
  · exact E.trans (V.trans TX.symm)
  · simp only [←TX,←E] at F0 F1 R
    have H := gate_race_strict C.L (C.a+2)
      (tok d C x (C.a+2)).race (tok d C y (C.a+2)).race R
    unfold extraAt at P
    rw [F0,F1] at P
    simp only [ReportPrelaunchRank.rank] at H
    omega

-- CHECK: if rw [←TX,←E] at F0 F1 R fails because one equation
-- has no occurrence in one hypothesis, use simp only [←TX,←E]
-- at F0 F1 R. rank_norm_cases has the exact RaceAdvance disjunction.

theorem gate_plateau_token (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (e : Fin n)
    (S : ForwardWait d C x (C.a+2))
    (T : ForwardWait d C (rawNext s x e) (C.a+2))
    (P : extraAt d C (rawNext s x e) (C.a+2)=extraAt d C x (C.a+2)) :
    tok d C (rawNext s x e) (C.a+2)=tok d C x (C.a+2) := by
  let g := C.a+2
  let i := C.a+1
  let y := rawNext s x e
  have I : i+1<C.L := S.2.1
  have J : g+1<C.L := (gate_room C G).1
  have A : chartGate d C x g=true :=
    ((gate_geometry d C hh G (Q:=Q)).2.2 x X g S.2.1).mpr rfl
  by_cases L : e=out C i
  · subst e
    exact norm_plateau_gate d C x _ A 2 (.inl rfl)
      (incoming_front_norm_all d C N hh G F x X i I A S) P
  by_cases R : e=out C g
  · subst e
    by_cases RD : readyAt d C x g=true
    · have OldT := (ready_locations d C x N ((cached_fibre d N hh Q F).mask x X)
        g J RD).1
      have NewF := front_self d C _ g T
      rw [OldT] at NewF
      simp [MISByteCodec.T] at NewF
    · have Tag := front_self d C x g S
      have Park : healthyAdmit (params d s) (tok d C x g) ∧
          chartGate d C x g=true ∧ (tok d C x g).race<4 := by
        classical
        exact Classical.byContradiction (fun K=>RD ((ready_iff d C x g).mpr ⟨Tag,K⟩))
      exact norm_plateau_gate d C x _ A 3 (.inr rfl)
        (raw_out_norm d C N hh G F x X g S.2.1 A Park.1 Park.2.2) P
  · exact ReportFastNoRearm.raw_gate_spectator d C N hh G F x X i I e L R

theorem frontLabel_plateau (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (e : Fin n) (k : Nat)
    (A : ForwardWait d C x k) (B : ForwardWait d C (rawNext s x e) k)
    (PC : readPC d C (rawNext s x e)=readPC d C x)
    (E : serialDebt d C (rawNext s x e)=serialDebt d C x) :
    ReportPrelaunchK1.frontLabel d C (rawNext s x e) k=
      ReportPrelaunchK1.frontLabel d C x k := by
  classical
  let y := rawNext s x e
  have Y := (cached_fibre d N hh Q F).closed x e X
  have GF := gate_frame d C hh G x y X Y k A.2.1
  by_cases K : k=C.a+2
  · subst k
    exact ReportPrelaunchK1.frontLabel_frame d C x y _
      (gate_plateau_token d C N hh G F x X e A B
        (plateau_extra d C x y _ A B PC E)) GF
  · have H : chartGate d C x k=false := Bool.eq_false_iff.mpr
      (fun T=>K (((gate_geometry d C hh G (Q:=Q)).2.2 x X k A.2.1).mp T))
    have H' := GF.trans H
    change ReportPrelaunchK1.frontLabel d C y k=ReportPrelaunchK1.frontLabel d C x k
    simp [ReportPrelaunchK1.frontLabel,H,H']

noncomputable def cursorLabel (d : Sheet) (C : Chart h) (x : Raw s n) : Cursor→Fin n
  | .issue => door C
  | .fwd k => ReportPrelaunchK1.frontLabel d C x k
  | .rev k => inEdge C k

def NomAt (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : State d hh Q) (q : Fin n) : Prop :=
  match z.2 with
  | none => ∃ m,On d C z.1.val m ∧ q=cursorLabel d C z.1.val m
  | some st => ShortResetCycle.debt C.L (nextStage C q st)<ShortResetCycle.debt C.L st

theorem nom_exists (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : State d hh Q) (I : Inv d C hh z) (H : ¬ReportOwnerReceiptClock.done z) :
    ∃ q,NomAt d C hh z q := by
  cases E : z.2 with
  | none =>
    obtain ⟨m,A⟩ := cursor_exists d C z.1.val I.1.1
    exact ⟨cursorLabel d C z.1.val m,by simpa only [NomAt,E] using
      (show ∃ m',On d C z.1.val m' ∧
        cursorLabel d C z.1.val m=cursorLabel d C z.1.val m' from ⟨m,A,rfl⟩)⟩
  | some st =>
    have ND : st≠.done := fun J=>H (E.trans (congrArg some J))
    obtain ⟨q,L⟩ := (ShortResetCycle.debt_step C st
      (by cases st <;> exact stage_live d C z.1.val _ ND (I.2 _ E ND))).2
    exact ⟨q,by simp only [NomAt,E]; omega⟩

private theorem cursor_paid (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (m : Cursor) (A : On d C x m) : PaidMark d C x (cursorLabel d C x m) := by
  let R := rows_at d C N hh G F digit
  cases m with
  | issue =>
    change PaidMark d C x (door C)
    apply R.empty x X
    all_goals intro i I; rw [A.2.2 i I]; decide
  | fwd k =>
    exact ReportPrelaunchK1.frontLabel_paid d C hh G F N x X k A.2.1
      (front_self d C x k A)
  | rev k =>
    change PaidMark d C x (inEdge C k)
    exact R.reply x X (fun i I=>by rw [A.2.2 i I]; exact back_not_front k i)
      k A.2.1 (back_self d C x k A)

private theorem launch_stage (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (e : Fin n) (E : z.2=none)
    (L : Launch d C z.1.val e) :
    (step d C N hh F z e).2=some (.fwd 0) := by
  change (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F) z e).2=_
  simp [ReportOwnerReceiptClock.next,E,L.1,L.2]

private theorem nonlaunch_stage (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (e : Fin n) (E : z.2=none)
    (L : ¬Launch d C z.1.val e) :
    (step d C N hh F z e).2=none := by
  change (ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F) z e).2=_
  simp [ReportOwnerReceiptClock.next,E,show ¬(ownerPC d C z.1.val=.issue0 ∧ e=door C) from L]

private theorem launched_pays (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (I : Inv d C hh z) (e : Fin n)
    (E : z.2=none) (L : Launch d C z.1.val e) :
    freshDebt d C hh (step d C N hh F z e)<freshDebt d C hh z := by
  have S := launch_stage d C N hh F z e E L
  have R := serialDebt_issue0 d C z.1.val I.1.1 L.1
  simp only [freshDebt,E,S,ShortResetCycle.debt,Nat.sub_zero,R,resetCost]
  omega

private theorem active_stage (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (e : Fin n) (st : Stage) (E : z.2=some st) :
    (step d C N hh F z e).2=some (nextStage C e st) := by
  simp [step,ReportOwnerReceiptClock.next,E]

theorem nom_pays (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (z : State d hh Q)
    (I : Inv d C hh z) (q : Fin n) (A : NomAt d C hh z q) :
    freshDebt d C hh (step d C N hh F z q)<freshDebt d C hh z := by
  cases E : z.2 with
  | none =>
    simp only [NomAt,E] at A
    obtain ⟨m,V,J⟩ := A
    have P : PaidMark d C z.1.val q := by
      rw [J]
      exact cursor_paid d C N hh G F digit z.1.val z.1.property m V
    by_cases L : Launch d C z.1.val q
    · exact launched_pays d C N hh F z I q E L
    · have S := nonlaunch_stage d C N hh F z q E L
      have B := (serial_step_nonlaunch d C N hh G F digit z.1.val z.1.property I.1 q L).2
        (P.resolve_left L)
      simpa only [freshDebt,E,S,step_raw] using B
  | some st =>
    have S := active_stage d C N hh F z q st E
    simpa only [NomAt,E,freshDebt,S] using A

theorem nom_plateau (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (z : State d hh Q)
    (I : Inv d C hh z) (q e : Fin n) (A : NomAt d C hh z q)
    (E0 : freshDebt d C hh (step d C N hh F z e)=freshDebt d C hh z) :
    NomAt d C hh (step d C N hh F z e) q := by
  cases E : z.2 with
  | none =>
    have NL : ¬Launch d C z.1.val e := by
      intro L
      have T := launched_pays d C N hh F z I e E L
      omega
    have S := nonlaunch_stage d C N hh F z e E NL
    simp only [NomAt,E] at A
    obtain ⟨m,V,J⟩ := A
    have D : serialDebt d C (rawNext s z.1.val e)=serialDebt d C z.1.val := by
      simpa only [freshDebt,E,S,step_raw] using E0
    obtain ⟨W,PC⟩ := pre_plateau_cursor d C N hh G F digit z.1.val z.1.property
      I.1 m V e NL D
    have L : cursorLabel d C (rawNext s z.1.val e) m=cursorLabel d C z.1.val m := by
      cases m with
      | issue => rfl
      | rev k => rfl
      | fwd k =>
        exact frontLabel_plateau d C N hh G F z.1.val z.1.property e k V W PC D
    simp only [NomAt,S,step_raw]
    exact ⟨m,W,J.trans L.symm⟩
  | some st =>
    have ND : st≠.done := by
      intro H
      subst st
      simp [NomAt,E,nextStage] at A
    have R := stage_live d C z.1.val st ND (I.2 st E ND)
    have Range : InRange C st := by
      cases st with
      | fwd k => exact R
      | rev k => exact R
      | done => exact False.elim (ND rfl)
    have S := active_stage d C N hh F z e st E
    have D : ShortResetCycle.debt C.L (nextStage C e st)=ShortResetCycle.debt C.L st := by
      simpa only [freshDebt,E,S] using E0
    have P := progress_debt C st e Range
    have Z : nextStage C e st=st := by
      apply Classical.byContradiction
      intro K
      have V : progress C st e=1 := by simp [progress,K]
      omega
    simp only [NomAt,E] at A
    simpa only [NomAt,S,Z] using A

theorem done_sticky (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : State d hh Q) (e : Fin n) (H : ReportOwnerReceiptClock.done z) :
    ReportOwnerReceiptClock.done (step d C N hh F z e) := by
  change z.2=some .done at H
  exact active_stage d C N hh F z e .done H

end L4.ReportFastFreshReset

namespace L4.ReportFastFreshReset
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerForwardControl ReportOwnerReverseControl ReportOwnerIssueControl
open ReportOwnerSerial ReportOwnerCommandRail ReportByteRows ReportRawProjection

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

def AtACQIssue (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  readPC d C x=(1,acqOp (params d s))

def PreACQPose (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  0<(readPC d C x).2 ∧
    ((readPC d C x).2<acqOp (params d s) ∨ AtACQIssue d C x)

theorem preACQ_pose_opcode (d : Sheet) (C : Chart h) (x : Raw s n)
    (P : PreACQPose d C x) : (readPC d C x).2≤acqOp (params d s) := by
  rcases P.2 with H|H
  · exact Nat.le_of_lt H
  · exact Nat.le_of_eq (congrArg Prod.snd H)

theorem preACQ_not_reset_launch (d : Sheet) (C : Chart h) (x : Raw s n)
    (P : PreACQPose d C x) (e : Fin n) : ¬Launch d C x e := by
  intro H
  have E := congrArg Prod.snd ((issue0_iff d C x).mp H.1)
  exact (Nat.ne_of_gt P.1) E

theorem preACQ_legal_issue (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : StrongSerial d C x) (P : AtACQIssue d C x) :
    LegalIssue d C x := by
  rcases S.1 with A|⟨k,A⟩|⟨k,A⟩
  · exact A
  · have E := A.1.1
    rw [P] at E
    exact False.elim ((by decide : (1:Nat)≠2) E)
  · have E := A.1.1
    rw [P] at E
    exact False.elim ((by decide : (1:Nat)≠2) E)

def preACQFloor (d : Sheet) (C : Chart h) : Nat :=
  (3*(params d s).digits+3)*commandCap C.L+resetCost C.L

theorem preACQ_serial_bounds (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : StrongSerial d C x) (P : PreACQPose d C x) :
    preACQFloor (s:=s) d C≤serialDebt d C x ∧
    serialDebt d C x≤preACQFloor (s:=s) d C+
      ((params d s).digits+1)*commandCap C.L := by
  let t := (params d s).digits
  let B := commandCap C.L
  let a := (readPC d C x).2
  obtain ⟨m,M⟩ := cursor_exists d C x S.1
  have H : a≤t+2 := by
    simpa [a,t,acqOp] using preACQ_pose_opcode d C x P
  have Pos : 0<a := P.1
  have Log : logical t a=a := by
    unfold logical
    rw [if_pos (show a<2*t+3 by omega)]
  have E : ¬((readPC d C x).2=0 ∧ m=.issue) := by
    intro J
    exact (Nat.ne_of_gt Pos) J.1
  have RB : remain d C x m≤B := remain_bound d C x m M
  have U : (4*t+4-a)*B≤(4*t+3)*B :=
    Nat.mul_le_mul_right B (by omega)
  have Sum : (4*t+3)*B+B=(3*t+3)*B+(t+1)*B := by
    calc
      _ = (4*t+3+1)*B := (Nat.succ_mul _ _).symm
      _ = (3*t+3+(t+1))*B := congrArg (· * B) (by omega)
      _ = _ := by rw [Nat.add_mul]
  rw [serialDebt_on d C x m M]
  unfold preDebt
  rw [if_neg E]
  change (3*t+3)*B+resetCost C.L≤
      (4*t+4-logical t a)*B+resetCost C.L+remain d C x m ∧
    (4*t+4-logical t a)*B+resetCost C.L+remain d C x m≤
      (3*t+3)*B+resetCost C.L+(t+1)*B
  rw [Log]
  constructor
  · rcases P.2 with J|J
    · have J' : a<t+2 := by simpa [a,t,acqOp] using J
      have V : (3*t+3)*B≤(4*t+4-a)*B :=
        Nat.mul_le_mul_right B (by omega)
      omega
    · have I : LegalIssue d C x := preACQ_legal_issue d C x S J
      have M0 : m=.issue := cursor_unique d C x m .issue M I
      subst m
      have aE : a=t+2 := by
        simpa [a,t,acqOp] using congrArg Prod.snd J
      have F : 4*t+4-a=3*t+2 := by omega
      rw [F]
      have B0 : (3*t+2)*B+B=(3*t+3)*B := by
        calc
          _ = (3*t+2+1)*B := (Nat.succ_mul _ _).symm
          _ = _ := congrArg (· * B) (by omega)
      change (3*t+3)*B+resetCost C.L≤
        (3*t+2)*B+resetCost C.L+B
      omega
  · omega

theorem preACQ_serial_at_issue (d : Sheet) (C : Chart h) (x : Raw s n)
    (S : StrongSerial d C x) (P : AtACQIssue d C x) :
    serialDebt d C x=preACQFloor (s:=s) d C := by
  let t := (params d s).digits
  let B := commandCap C.L
  rw [serialDebt_on d C x .issue (preACQ_legal_issue d C x S P)]
  unfold preDebt
  have A : (readPC d C x).2=t+2 := by
    simpa [t,acqOp] using congrArg Prod.snd P
  rw [A,if_neg (by omega : ¬(t+2=0 ∧ Cursor.issue=Cursor.issue))]
  change (4*t+4-logical t (t+2))*B+resetCost C.L+B=
    (3*t+3)*B+resetCost C.L
  have K : logical t (t+2)=t+2 := by
    unfold logical
    rw [if_pos (show t+2<2*t+3 by omega)]
  rw [K,show 4*t+4-(t+2)=3*t+2 by omega]
  have H : (3*t+2)*B+B=(3*t+3)*B := by
    calc
      _ = (3*t+2+1)*B := (Nat.succ_mul _ _).symm
      _ = _ := congrArg (· * B) (by omega)
  omega

inductive PreACQStatus where
  | live
  | launched
  | retry
  deriving DecidableEq

structure PreACQBase (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) where
  raw : {x : Raw s n // Cached d hh Q x}
  status : PreACQStatus

def preACQHit (d : Sheet) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) : Prop :=
  z.status≠.live

def preACQSuccess (d : Sheet) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) : Prop :=
  z.status=.launched

def preACQGood (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) : Prop :=
  StrongSerial d C z.raw.val ∧
    (z.status=.live → PreACQPose d C z.raw.val)

noncomputable def preACQStep (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreACQBase d hh Q) (e : Fin n) : PreACQBase d hh Q := by
  classical
  let y := rawNext s z.raw.val e
  exact ⟨⟨y,(cached_fibre d N hh Q F).closed _ e z.raw.property⟩,
    if z.status=.live then
      if AtACQIssue d C z.raw.val ∧ e=door C then .launched
      else if PreACQPose d C y then .live else .retry
    else z.status⟩

theorem preACQStep_raw (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreACQBase d hh Q) (e : Fin n) :
    (preACQStep d C N hh F z e).raw.val=rawNext s z.raw.val e := rfl

theorem preACQStep_closed (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (z : PreACQBase d hh Q) (e : Fin n) (H : preACQGood d C hh z) :
    preACQGood d C hh (preACQStep d C N hh F z e) := by
  classical
  refine ⟨strong_step d C N hh G F z.raw.val z.raw.property H.1 digit e,?_⟩
  intro L
  change PreACQPose d C (rawNext s z.raw.val e)
  unfold preACQStep at L
  dsimp only at L
  split at L
  · split at L
    · cases L
    · split at L
      · assumption
      · cases L
  · rename_i K
    exact False.elim (K L)

theorem preACQ_sticky (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreACQBase d hh Q) (e : Fin n) (H : preACQHit d hh z) :
    (preACQStep d C N hh F z e).status=z.status := by
  classical
  change z.status≠.live at H
  simp [preACQStep,H]

noncomputable def preACQDebt (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) : Nat := by
  classical
  exact if z.status=.live then
    serialDebt d C z.raw.val-preACQFloor (s:=s) d C+1 else 0

theorem preACQ_debt_live (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) (H : z.status=.live) :
    preACQDebt d C hh z=serialDebt d C z.raw.val-preACQFloor (s:=s) d C+1 := by
  classical
  simp [preACQDebt,H]

theorem preACQ_debt_stop (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) (H : z.status≠.live) :
    preACQDebt d C hh z=0 := by
  classical
  simp [preACQDebt,H]

theorem preACQ_debt_bound (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) (H : preACQGood d C hh z) :
    preACQDebt d C hh z≤((params d s).digits+1)*commandCap C.L+1 := by
  by_cases L : z.status=.live
  · rw [preACQ_debt_live d C hh z L]
    have B := (preACQ_serial_bounds d C z.raw.val H.1 (H.2 L)).2
    omega
  · rw [preACQ_debt_stop d C hh z L]
    exact Nat.zero_le _

theorem preACQ_all_mark (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (z : PreACQBase d hh Q) (e : Fin n) (H : preACQGood d C hh z)
    (L : z.status=.live) :
    let y := preACQStep d C N hh F z e
    preACQDebt d C hh y≤preACQDebt d C hh z ∧
    (PaidMark d C z.raw.val e →
      preACQDebt d C hh y<preACQDebt d C hh z) := by
  dsimp only
  let y := preACQStep d C N hh F z e
  have NL := preACQ_not_reset_launch d C z.raw.val (H.2 L) e
  have B := serial_step_nonlaunch d C N hh G F digit z.raw.val
    z.raw.property H.1 e NL
  have Y := preACQStep_closed d C N hh G F digit z e H
  rw [preACQ_debt_live d C hh z L]
  by_cases L' : y.status=.live
  · rw [preACQ_debt_live d C hh y L']
    have F0 := (preACQ_serial_bounds d C z.raw.val H.1 (H.2 L)).1
    have F1 := (preACQ_serial_bounds d C y.raw.val Y.1 (Y.2 L')).1
    change preACQFloor (s:=s) d C≤serialDebt d C
      (rawNext s z.raw.val e) at F1
    constructor
    · change serialDebt d C (rawNext s z.raw.val e)-
        preACQFloor (s:=s) d C+1≤_
      omega
    · intro M
      have K := B.2 (M.resolve_left NL)
      change serialDebt d C (rawNext s z.raw.val e)-
        preACQFloor (s:=s) d C+1<_
      omega
  · rw [preACQ_debt_stop d C hh y L']
    constructor
    · exact Nat.zero_le _
    · intro _
      omega

def PreACQNom (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) (q : Fin n) : Prop :=
  ∃ m,On d C z.raw.val m ∧ q=cursorLabel d C z.raw.val m

theorem preACQ_nom_exists (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (z : PreACQBase d hh Q) (H : preACQGood d C hh z) :
    ∃ q,PreACQNom d C hh z q := by
  obtain ⟨m,M⟩ := cursor_exists d C z.raw.val H.1.1
  exact ⟨cursorLabel d C z.raw.val m,m,M,rfl⟩

theorem preACQ_nom_pays (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (z : PreACQBase d hh Q) (q : Fin n) (H : preACQGood d C hh z)
    (L : z.status=.live) (M : PreACQNom d C hh z q) :
    preACQDebt d C hh (preACQStep d C N hh F z q)<preACQDebt d C hh z := by
  obtain ⟨m,A,rfl⟩ := M
  exact (preACQ_all_mark d C N hh G F digit z _ H L).2
    (cursor_paid d C N hh G F digit z.raw.val z.raw.property m A)

theorem preACQ_nom_plateau (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (z : PreACQBase d hh Q) (q e : Fin n) (H : preACQGood d C hh z)
    (L : z.status=.live) (M : PreACQNom d C hh z q)
    (E : preACQDebt d C hh (preACQStep d C N hh F z e)=preACQDebt d C hh z) :
    PreACQNom d C hh (preACQStep d C N hh F z e) q := by
  let y := preACQStep d C N hh F z e
  have Y := preACQStep_closed d C N hh G F digit z e H
  have L' : y.status=.live := by
    apply Classical.byContradiction
    intro K
    have E0 := E
    rw [preACQ_debt_stop d C hh y K,preACQ_debt_live d C hh z L] at E0
    omega
  rw [preACQ_debt_live d C hh y L',preACQ_debt_live d C hh z L] at E
  have F0 := (preACQ_serial_bounds d C z.raw.val H.1 (H.2 L)).1
  have F1 := (preACQ_serial_bounds d C y.raw.val Y.1 (Y.2 L')).1
  have Eq : serialDebt d C (rawNext s z.raw.val e)=serialDebt d C z.raw.val := by
    change serialDebt d C y.raw.val=serialDebt d C z.raw.val
    omega
  obtain ⟨m,A,J⟩ := M
  have NL := preACQ_not_reset_launch d C z.raw.val (H.2 L) e
  obtain ⟨A',PC⟩ := pre_plateau_cursor d C N hh G F digit z.raw.val
    z.raw.property H.1 m A e NL Eq
  refine ⟨m,A',J.trans ?_⟩
  cases m with
  | issue => rfl
  | rev k => rfl
  | fwd k =>
    exact (frontLabel_plateau d C N hh G F z.raw.val z.raw.property
      e k A A' PC Eq).symm

theorem preACQ_crossing (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (z : PreACQBase d hh Q) (H : preACQGood d C hh z)
    (L : z.status=.live) (P : AtACQIssue d C z.raw.val) :
    preACQDebt d C hh z=1 ∧
    preACQSuccess d hh (preACQStep d C N hh F z (door C)) ∧
    preACQDebt d C hh (preACQStep d C N hh F z (door C))=0 := by
  classical
  have J : (preACQStep d C N hh F z (door C)).status=.launched := by
    simp [preACQStep,L,P]
  refine ⟨?_,J,preACQ_debt_stop d C hh _ (by rw [J]; decide)⟩
  rw [preACQ_debt_live d C hh z L,preACQ_serial_at_issue d C z.raw.val H.1 P]
  omega

-- Correct first-issue tape: no claim about opcode on the subsequent
-- all-empty, off-door waiting suffix.
def FirstACQIssueTape (d : Sheet) (C : Chart h) :
    Raw s n→List (Fin n)→Prop
  | x,[] => AtACQIssue d C x
  | x,e::w => PreACQPose d C x ∧ ¬AtACQIssue d C x ∧
    FirstACQIssueTape d C (rawNext s x e) w

theorem first_issue_tape_end (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (H : FirstACQIssueTape d C x w) :
    AtACQIssue d C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact H
  | cons e w IH => exact IH _ H.2.2

-- Fresh receipt is the old issue-1 cut, not any later decoded WAIT.
theorem preACQ_pose_at_receipt (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (w : List (Fin n))
    (R : Generated d C x w .done) :
    PreACQPose d C (rawRun x w) := by
  obtain ⟨_,P⟩ := cached_genuine_full_parked d C N hh F x X w R
  have PC := pc_fields d C (rawRun x w) .issue1 (by decide) P.1.1
  change readPC d C (rawRun x w)=(1,1) at PC
  unfold PreACQPose
  rw [PC]
  exact ⟨by decide,.inl (by unfold acqOp; omega)⟩

end L4.ReportFastFreshReset

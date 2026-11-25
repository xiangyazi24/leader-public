import Leader.L4.ReportFastPreACQHandoff
import Leader.L4.ReportFastPreACQLaunch
import Leader.L4.ReportFastAcqTrack
import Leader.L4.ReportFastAcqMapped
import Leader.L4.ReportFastEarlyPacket
import Leader.L4.ReportFastPostACQ
import Leader.L4.ReportFastItem10Assembly
import Leader.L4.ReportFastRawRelift

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportPrelaunchAllOwners
open ReportOwnerCommandRail ReportOwnerIssueControl ReportOwnerForwardLocations
open ReportOwnerReverseShape ReportOwnerAcquireProvenance
open ReportFastOwnerSupport ReportFastFiveGeometry ReportLeaseOwner
open ReportGoodEightBank ReportGoodEightCut ReportByteRows
open ReportFastFreshReset ReportFastPreACQTrack ReportFastAcqWins
open ReportFastEarlyPacket ReportFastPreparedMean ReportFastReceiptSwitch
open ReportFastNominationBridge ReportFastDenySteering ReportFastSteeringMap
open ReportAdaptiveFibre ReportFastKernel ReportFastItem10Assembly

set_option maxRecDepth 16000
set_option maxHeartbeats 16000000

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

/-- The future property is on actual target-win mapped words. It is a
    proof predicate on the current raw state; no future tape is stored. -/
def RivalFuture (d : Sheet) (B : Fin 5→Chart h) (x : Raw s n) : Prop :=
  ∀ t (v : List (Fin n)), RivalFence d (B 2)
    (rawRun x (mappedWord d B (fun _ _=>targetDesired 2) t x v))

theorem future_now (d : Sheet) (B : Fin 5→Chart h) (x : Raw s n)
    (H : RivalFuture d B x) : RivalFence d (B 2) x :=
  H 0 []

theorem const_time (d : Sheet) (B : Fin 5→Chart h) (u v : Nat)
    (x : Raw s n) (w : List (Fin n)) :
    mappedWord d B (fun _ _=>targetDesired 2) u x w =
      mappedWord d B (fun _ _=>targetDesired 2) v x w := by
  induction w generalizing u v x with
  | nil => rfl
  | cons e w IH =>
    let a := steerRaw d B (targetDesired 2) x e
    change a::mappedWord d B (fun _ _=>targetDesired 2)
        (u+1) (rawNext s x a) w =
      a::mappedWord d B (fun _ _=>targetDesired 2)
        (v+1) (rawNext s x a) w
    rw [IH (u+1) (v+1) (rawNext s x a)]

theorem future_step (d : Sheet) (B : Fin 5→Chart h) (x : Raw s n)
    (H : RivalFuture d B x) (e : Fin n)
    (E : steerRaw d B (targetDesired 2) x e=e) :
    RivalFuture d B (rawNext s x e) := by
  intro t w
  have F := H 0 (e::w)
  change RivalFence d (B 2) (rawRun (rawNext s x
      (steerRaw d B (targetDesired 2) x e))
    (mappedWord d B (fun _ _=>targetDesired 2) (0+1)
      (rawNext s x (steerRaw d B (targetDesired 2) x e)) w)) at F
  rw [E] at F
  rw [←const_time d B (0+1) t (rawNext s x e) w]
  exact F

/-- The actual sixth RESET mark supplies all three PREACQ entry
    predicates, including the current-state suffix fence. -/
theorem reset_pre_entry
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d P) (digit : 0<(params d s).digits)
    (W : Nat) (W3 : 3≤W) (r : Fin 5→Owner h) (R : Consecutive G r)
    (Width : ∀ j,(charter G (r j)).L≤3*W)
    (x : {y : Raw s n // Cached d hh P y})
    (S : ∀ j,StrongSerial d (charter G (r j)) x.val)
    (fallback : Fin n) (v : List (Fin n)) (e : Fin n) (t₀ : Nat) :
    let B := fun j=>charter G (r j)
    let nxt := prepDriver d B N hh F W
    let old := Height.runWord nxt (prepStart d B hh x fallback) v
    let z := nxt old e
    ¬ReportFastSixPrepTrack.hit old.base →
    ReportFastSixPrepTrack.hit z.base →
    let pre : PreTrack d hh P :=
      start (PreACQNom d (B 2) hh) ⟨z.base.1,.live⟩ fallback
    WinTrackGood d B 2 hh pre ∧ pre.base.status=.live ∧
      OwnClear d (B 2) pre.base.raw.val ∧
      RivalFuture d B pre.base.raw.val := by
  dsimp only
  let B := fun j=>charter G (r j)
  let nxt := prepDriver d B N hh F W
  let old := Height.runWord nxt (prepStart d B hh x fallback) v
  let z := nxt old e
  let pre : PreTrack d hh P :=
    start (PreACQNom d (B 2) hh) ⟨z.base.1,.live⟩ fallback
  intro L H
  have inj := centers_injective_of_roots G B (target_five_incidence G r R).2.1
  obtain ⟨PG,O,Rivals⟩ := ReportFastPreACQHandoff.from_sixth_reset
    d N hh G F digit W W3 r R Width x S fallback v e t₀ L H
  obtain ⟨_,PC,_,Serial,_⟩ :=
    exit_switch d B N hh G F inj digit W W3 Width x S fallback v e t₀ L H
  change WinTrackGood d B 2 hh pre ∧ pre.base.status=.live ∧
    OwnClear d (B 2) pre.base.raw.val ∧ RivalFuture d B pre.base.raw.val
  refine ⟨⟨PG,base_packet_init d (B 2) hh z.base.1 PC (Serial 2)⟩,rfl,O,?_⟩
  intro t w
  rw [←ReportFastPreACQHandoff.run_pre_driver_raw d B N hh G F inj pre w t]
  exact Rivals w

/-- Maintain absent target grants on each actual mark before launch.
    The old ACQ ISSUE waiting branch is separate: it need not satisfy
    the old PreACQPrefix. -/
theorem pre_own_clear_step
    (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh P x) (S : StrongSerial d C x)
    (E : EarlyPacket d C x) (O : OwnClear d C x) (e : Fin n) :
    OwnClear d C (rawNext s x e) := by
  by_cases A : AtACQIssue d C x
  · exact preacq_empty_clear_step d C N hh F x X
      (preACQ_legal_issue d C x S A) O e
  · have K := early_nonacq d C x E A
    exact own_clear_pre_run d C N hh G F digit x X S O [e]
      (show PreACQPrefix d C x [e] from ⟨K,trivial⟩)

/-- Exact entry to ACQ at the actual door, not at the first clean ISSUE. -/
theorem pre_acq_entry
    (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (x : Raw s n) (X : Cached d hh P x)
    (S : StrongSerial d C x) (PC : AtACQIssue d C x)
    (O : OwnClear d C x) :
    LegalIssue d C x ∧
    Cached d hh P (rawNext s x (door C)) ∧
    ReportFastAcqTrack.On d C (rawNext s x (door C)) (.fwd 0) := by
  have I := preACQ_legal_issue d C x S PC
  obtain ⟨Y,L⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N x X I PC
  have O' := issue_clear d C N hh F x X I O
  exact ⟨I,Y,64,L,by decide,O'⟩

/-- At any ACQ nonconsume cursor, a nonterminal cursor step is genuinely
    before the actual source consume. -/
theorem acq_before_mark (d : Sheet) (C : Chart h) (x : Raw s n)
    (c : ReportFastAcqTrack.Cursor) (O : ReportFastAcqTrack.On d C x c)
    (e : Fin n) (L : c≠.done)
    (H : ReportFastAcqTrack.next C e c≠.done) :
    NoConsume d C x e := by
  cases c with
  | done => exact False.elim (L rfl)
  | fwd k =>
    obtain ⟨q,A,_,_⟩ := O
    right
    rw [A.shape.2.2 0 C.positive]
    by_cases E : k=0
    · subst k; simp [frontTag]
    · have K : 0<k := Nat.pos_of_ne_zero E
      simp [frontTag,K]
  | rev k =>
    obtain ⟨q,A,_⟩ := O
    cases k with
    | zero =>
      left
      intro E
      exact H ((ReportFastAcqTrack.finish_iff C (.rev 0) e L).mpr ⟨rfl,E⟩)
    | succ k =>
      right
      rw [A.shape.2.2 0 C.positive]
      simp [backTag]

theorem acq_fenced_snoc
    (d : Sheet) (C : Chart h) (x₀ : Raw s n)
    (u : List (Fin n)) (T : FencedBefore d C x₀ u)
    (c : ReportFastAcqTrack.Cursor)
    (A : ReportFastAcqTrack.On d C (rawRun x₀ u) c)
    (e : Fin n) (L : c≠.done) (H : ReportFastAcqTrack.next C e c≠.done)
    (R : RivalFence d C (rawRun x₀ u)) :
    FencedBefore d C x₀ (u++[e]) :=
  .snoc e T (acq_before_mark d C _ c A e L H) (fun _ _ _ _ _=>R)

/-- Preserve the original actual ACQ launch and flight as the context
    of the arithmetic observer. The stored prefix ends BEFORE consume. -/
noncomputable def post_context_of_consume
    (d : Sheet) (N : 1<n) (Spos : 0<s) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d P) (r : Owner h)
    (digit : 0<(params d s).digits)
    (issue : Raw s n) (First : FirstCut d hh P G issue)
    (I : LegalIssue d (charter G r) issue)
    (PC : AtACQIssue d (charter G r) issue)
    (flight : List (Fin n))
    (T : FencedBefore d (charter G r)
      (rawNext s issue (door (charter G r))) flight)
    (c : ReportFastAcqTrack.Cursor)
    (X : Cached d hh P
      (rawRun (rawNext s issue (door (charter G r))) flight))
    (O : ReportFastAcqTrack.On d (charter G r)
      (rawRun (rawNext s issue (door (charter G r))) flight) c)
    (e : Fin n) (L : c≠.done) (H : ReportFastAcqTrack.next (charter G r) e c=.done)
    (left : (params d s).digits≤(charter G r).a)
    (mid : (params d s).digits≤(charter G r).b)
    (right : (params d s).digits≤(charter G r).L-
      ((charter G r).a+(charter G r).b)) :
    ReportFastPostACQ.Context d hh P G r := by
  let old := rawRun (rawNext s issue (door (charter G r))) flight
  have K := ReportFastAcqTrack.finish_is_successful_consume
    d (charter G r) N hh G F digit old X c O e L H
  exact ⟨N,Spos,F,issue,First,I,PC,flight,
    fenced_before_consume d (charter G r) _ flight T,
    K.2.1,K.2.2.1,left,mid,right⟩

-- CHECK: ReportOwnerForwardLocations/ReportOwnerAcquireProvenance.lean:
-- 345–350 gives the same frontTag root calculation as acq_before_mark.
-- The ReportFastPostACQ.Context constructor fields are listed in its definition.
end L4.ReportFastSplice

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportOwnerCommandRail
open ReportFastNominationBridge ReportFastOwnerSupport
open ReportFastPreACQTrack ReportFastAcqWins
open ReportAdaptiveFibre ReportFastKernel

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

abbrev ACQTrack (s n : Nat) :=
  Track (ReportFastAcqTrack.State s n) n

def acqD (C : Chart h) (z : ReportFastAcqTrack.State s n) : Nat :=
  ReportFastAcqTrack.debt C z.2

def acqNom (C : Chart h) (z : ReportFastAcqTrack.State s n) (q : Fin n) : Prop :=
  ReportFastAcqTrack.label C z.2=some q

noncomputable def acqBan (d : Sheet) (B : Fin 5→Chart h)
    (z : ReportFastAcqTrack.State s n) : Fin n→Option (Fin n) :=
  ReportFastAcqTrack.observerBan d B (targetDesired 2) z

noncomputable def acqNext (d : Sheet) (B : Fin 5→Chart h)
    (z : ACQTrack s n) (e : Fin n) : ACQTrack s n :=
  ReportFastNominationBridge.next (ReportFastAcqTrack.observe (B 2))
    (acqD (B 2)) (acqBan d B) (acqNom (B 2)) z e

def acqGood (d : Sheet) (B : Fin 5→Chart h) (z : ACQTrack s n) : Prop :=
  ReportFastAcqTrack.On d (B 2) z.base.1 z.base.2 ∧
  (z.base.2≠.done →
    acqNom (B 2) z.base z.pending ∧
    (z.unspent=false→Spent d B z.base.1 z.pending))

theorem acqNext_base (d : Sheet) (B : Fin 5→Chart h)
    (z : ACQTrack s n) (e : Fin n) :
    (acqNext d B z e).base=ReportFastAcqTrack.observe (B 2) z.base e :=
  next_base _ _ _ _ _ _

theorem acq_nom_exists (C : Chart h) (z : ReportFastAcqTrack.State s n)
    (H : z.2≠.done) : ∃ q,acqNom C z q := by
  rcases z with ⟨x,c⟩
  cases c with
  | done => exact False.elim (H rfl)
  | fwd k => exact ⟨out C k,rfl⟩
  | rev k => exact ⟨ReportPrelaunchClock.inEdge C k,rfl⟩

theorem acq_start_good (d : Sheet) (B : Fin 5→Chart h) (x : Raw s n)
    (A : ReportFastAcqTrack.On d (B 2) x (.fwd 0)) (q : Fin n) :
    acqGood d B (start (acqNom (B 2)) (x,.fwd 0) q) := by
  have V : ReportFastAcqTrack.Cursor.fwd 0≠.done := by decide
  refine ⟨A,fun _=>⟨chooseNom_spec _ _ _ (acq_nom_exists (B 2) (x,.fwd 0) V),?_⟩⟩
  intro H
  cases H

theorem acq_local_closed
    (d : Sheet) (B : Fin 5→Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d P)
    (digit : 0<(params d s).digits)
    (inj : Function.Injective (fun j=>center (B j)))
    (z : ACQTrack s n) (e : Fin n)
    (H : acqGood d B z) (L : z.base.2≠.done)
    (X : Cached d hh P z.base.1)
    (S : ∀ j,StrongSerial d (B j) z.base.1)
    (RF : DepartureFence d (B 2) z.base.1 e) :
    acqGood d B (acqNext d B z e) := by
  classical
  let C := B 2
  let y := ReportFastAcqTrack.observe C z.base e
  let D : ReportFastAcqTrack.State s n→Nat := acqD C
  let Nom : ReportFastAcqTrack.State s n→Fin n→Prop := acqNom C
  let b : ReportFastAcqTrack.State s n→Fin n→Option (Fin n) := acqBan d B
  have Fit := ReportFastAcqTrack.on_fit d C z.base.1 z.base.2 H.1
  have I : D y≤D z.base :=
    ReportFastAcqTrack.debt_idle C z.base.2 Fit e
  have Y : ReportFastAcqTrack.On d C y.1 y.2 :=
    ReportFastAcqTrack.raw_on_step d C N hh G F digit z.base.1 X z.base.2 H.1 e RF
  obtain ⟨OldNom,OldSpent⟩ := H.2 L
  change acqGood d B (if D y<D z.base then
      ⟨y,chooseNom Nom y z.pending,true⟩
    else ⟨y,z.pending,if b z.base z.pending=some e then false else z.unspent⟩)
  by_cases E : D y<D z.base
  · rw [if_pos E]
    refine ⟨Y,fun K=>⟨chooseNom_spec Nom y z.pending (acq_nom_exists C y K),?_⟩⟩
    intro K
    cases K
  · rw [if_neg E]
    have Eq : D y=D z.base := by omega
    have PN : Nom y z.pending := by
      change ReportFastAcqTrack.label C (ReportFastAcqTrack.next C e z.base.2)=some z.pending
      rw [ReportFastAcqTrack.plateau_label C z.base.2 Fit e Eq]
      exact OldNom
    refine ⟨Y,fun _=>⟨PN,?_⟩⟩
    by_cases A : b z.base z.pending=some e
    · intro _
      exact ban_mate_spends d N hh G F B z.base.1 X S
        (activeRaw d B z.base.1) (targetDesired 2) (b z.base)
        (makeBan_spec hh G B inj _ _) (activeRaw_sound d B z.base.1)
        z.pending e A
    · intro B0
      have U : z.unspent=false := by simpa [A] using B0
      have NE : e≠z.pending := by
        intro K
        subst e
        exact E (ReportFastAcqTrack.physical_pays C z.base.2 Fit z.pending OldNom)
      exact spent_step d N hh G F B z.base.1 X S z.pending e NE (OldSpent U)

theorem acq_idle (d : Sheet) (B : Fin 5→Chart h)
    (z : ACQTrack s n) (e : Fin n) (H : acqGood d B z) :
    eventRank (acqD (B 2) (acqNext d B z e).base) (acqNext d B z e).unspent≤
      eventRank (acqD (B 2) z.base) z.unspent := by
  have I := ReportFastAcqTrack.on_fit d (B 2) z.base.1 z.base.2 H.1
  apply eventRank_idle
  · rw [acqNext_base]
    exact ReportFastAcqTrack.debt_idle (B 2) z.base.2 I e
  · intro E
    have Eq : acqD (B 2) (ReportFastAcqTrack.observe (B 2) z.base e)=
        acqD (B 2) z.base := by simpa only [acqNext_base] using E
    unfold acqNext
    rw [credit_plateau _ _ _ _ z e Eq]
    split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

theorem acq_nominate (d : Sheet) (B : Fin 5→Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h)
    (inj : Function.Injective (fun j=>center (B j)))
    (z : ACQTrack s n) (H : acqGood d B z) (L : z.base.2≠.done) :
    ∃ a e,mergeSide (acqBan d B z.base) e=a ∧
      eventRank (acqD (B 2) (acqNext d B z a).base) (acqNext d B z a).unspent<
        eventRank (acqD (B 2) z.base) z.unspent := by
  classical
  let C := B 2
  let b := acqBan d B z.base
  let q := z.pending
  have Fit := ReportFastAcqTrack.on_fit d C z.base.1 z.base.2 H.1
  obtain ⟨Nom,Sp⟩ := H.2 L
  cases E : b q with
  | none =>
    refine ⟨q,q,easy_allowed b q E,eventRank_progress (.inl ?_)⟩
    rw [acqNext_base]
    exact ReportFastAcqTrack.physical_pays C z.base.2 Fit q Nom
  | some a =>
    refine ⟨a,q,desired_hit b q a E,?_⟩
    have Credit : z.unspent=true := by
      cases U : z.unspent
      · have W := spent_unblocked d hh G B inj z.base.1 q
          (activeRaw d B z.base.1) (targetDesired 2) b
          (makeBan_spec hh G B inj _ _) (activeRaw_sound d B z.base.1) (Sp U)
        rw [W] at E
        cases E
      · rfl
    have Idle := ReportFastAcqTrack.debt_idle C z.base.2 Fit a
    by_cases K : acqD C (ReportFastAcqTrack.observe C z.base a)<acqD C z.base
    · apply eventRank_progress
      left
      rw [acqNext_base]
      exact K
    · have Eq : acqD C (ReportFastAcqTrack.observe C z.base a)=acqD C z.base := by
        change acqD C (ReportFastAcqTrack.observe C z.base a)≤acqD C z.base at Idle
        omega
      apply eventRank_progress
      right
      refine ⟨by rw [acqNext_base]; exact Eq,Credit,?_⟩
      unfold acqNext
      rw [credit_plateau _ _ _ _ z a Eq]
      exact if_pos E

theorem acq_budget (d : Sheet) (B : Fin 5→Chart h) (z : ACQTrack s n)
    (H : acqGood d B z) :
    eventRank (acqD (B 2) z.base) z.unspent≤4*(B 2).L+1 := by
  have F := ReportFastAcqTrack.on_fit d (B 2) z.base.1 z.base.2 H.1
  have D : acqD (B 2) z.base≤2*(B 2).L := by
    change ReportFastAcqTrack.debt (B 2) z.base.2≤_
    cases E : z.base.2 with
    | done => simp [ReportFastAcqTrack.debt]
    | fwd k =>
      simp [ReportFastAcqTrack.debt,ReportFastAcqWins.fDebt]
    | rev k =>
      rw [E] at F
      change k<(B 2).L at F
      simp only [ReportFastAcqTrack.debt,ReportFastAcqWins.dDebt]
      omega
  cases K : z.unspent <;> simp [eventRank] <;> omega

-- CHECK: ReportFastAcqTrack.lean:193–223 for definitional reductions
-- of observerBan and observe; ReportFastNominationBridge.lean:186–232
-- for the exact next conditional and chooseNom_spec argument order.
end L4.ReportFastSplice

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportLeaseOwner ReportGoodEightBank
open ReportFastRawEvent
variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

structure LateSealCommit (d : Sheet) (hh : ∃ i,h i=true)
    (P : Raw s n→Prop) (G : GapInput h) (r j : Owner h) (K : Nat) where
  centre_eq : j.val=ReportGenerationAncestry.centre (charter G r)
  good : ReportFastPostACQ.Context d hh P G r →
    List (Fin n) → Raw s n → Prop
  rank : ReportFastPostACQ.Context d hh P G r →
    List (Fin n) → Raw s n → Nat
  enter : ∀ (A : ReportFastPostACQ.Context d hh P G r) u,
    ReportFastPostACQ.UntilSeal A u →
    ReportFastPostACQ.Stop A (rawRun A.base u) →
    GoodEightBank d hh P G (rawRun A.base u) →
    good A u (rawRun A.base u)
  bound : ∀ A u x,good A u x→rank A u x≤K
  positive : ∀ A u x,good A u x→0<rank A u x
  -- All physical marks, with the same original A,u, and no steering.
  advance : ∀ A u x e,good A u x→
    classify d h x e≠some j →
    good A u (rawNext s x e) ∧ rank A u (rawNext s x e)≤rank A u x
  nominate : ∀ A u x,good A u x→
    ∃ e, classify d h x e=some j ∨
      rank A u (rawNext s x e)<rank A u x

-- A chart root and its classified centre share the subtype but
-- not the site. Context tracks r; the published label is j.
end L4.ReportFastSplice

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportGoodEightBank ReportFastOwnerSupport
open ReportFastNominationBridge ReportAdaptiveFibre ReportFastKernel
open ReportFastItem10Assembly ReportFastRawEvent ReportGateGeometry

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

structure Caps where
  reset : Nat
  pre : Nat
  acq : Nat
  post : Nat
  late : Nat

def Caps.total (b : Caps) : Nat :=
  b.reset+b.pre+b.acq+b.post+b.late

def Caps.at (b : Caps) : Nat→Nat
  | 0 => b.reset
  | 1 => b.pre
  | 2 => b.acq
  | 3 => b.post
  | _ => b.late

def Caps.tail (b : Caps) : Nat→Nat
  | 0 => b.pre+b.acq+b.post+b.late
  | 1 => b.acq+b.post+b.late
  | 2 => b.post+b.late
  | 3 => b.late
  | _ => 0

theorem tail_step (b : Caps) (i : Nat) (I : i<4) :
    b.tail i=b.at (i+1)+b.tail (i+1) := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with rfl|rfl|rfl|rfl <;>
    simp [Caps.tail,Caps.at,Nat.add_assoc]

theorem cap_tail_le (b : Caps) (i : Nat) (I : i<5) :
    b.at i+b.tail i≤b.total := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 by omega)
    with rfl|rfl|rfl|rfl|rfl <;>
    simp only [Caps.tail,Caps.at,Caps.total] <;> omega

def caps (t W K : Nat) : Caps :=
  ⟨924*t*W+1,29*t*W,12*W+1,21*t*W,K⟩

theorem cap_total (t W K : Nat)
    (H : 29*t*W+(12*W+1)+21*t*W+K≤112*t*W) :
    (caps t W K).total≤2*(518*t*W)+1 := by
  change (924*t*W+1)+29*t*W+(12*W+1)+21*t*W+K≤_
  have E : 924*t*W+112*t*W=2*(518*t*W) := by
    rw [←Nat.add_mul,←Nat.add_mul]
    ac_rfl
  omega

theorem pre_budget (t W L : Nat) (T : 0<t) (W3 : 3≤W) (B : L≤3*W) :
    2*((t+1)*ReportFastFreshReset.commandCap L+1)+1≤29*t*W := by
  have U : ReportFastFreshReset.commandCap L≤7*W := by
    unfold ReportFastFreshReset.commandCap
    omega
  have V : t+1≤2*t := by omega
  have M := Nat.mul_le_mul V U
  have M' : (t+1)*ReportFastFreshReset.commandCap L≤14*t*W := by
    calc
      _ ≤ (2*t)*(7*W) := M
      _ = 14*t*W := by rw [show 14=2*7 by decide]; ac_rfl
  have TW : 3≤t*W := by
    have W0 := Nat.mul_le_mul_right W (show 1≤t by omega)
    rw [Nat.one_mul] at W0
    omega
  rw [Nat.mul_assoc] at M' ⊢
  omega

-- Exact eventRank representation of an arbitrary natural clock.
def packedDebt (r : Nat) : Nat := r/2
def packedCredit (r : Nat) : Bool := decide (r%2=1)

theorem pack_rank (r : Nat) :
    eventRank (packedDebt r) (packedCredit r)=r := by
  unfold eventRank packedDebt packedCredit
  by_cases H : r%2=1 <;> simp [H] <;> omega

theorem pack_debt_idle {a b : Nat} (L : a≤b) :
    packedDebt a≤packedDebt b := by
  unfold packedDebt
  omega

theorem pack_credit_idle {a b : Nat} (L : a≤b)
    (E : packedDebt a=packedDebt b) :
    (packedCredit a).toNat≤(packedCredit b).toNat := by
  have A := pack_rank a
  have B := pack_rank b
  unfold eventRank at A B
  omega

theorem pack_progress {a b : Nat} (L : a<b) :
    packedDebt a<packedDebt b ∨
    (packedDebt a=packedDebt b ∧ packedCredit b=true ∧ packedCredit a=false) := by
  by_cases H : packedDebt a<packedDebt b
  · exact .inl H
  · have D := pack_debt_idle (Nat.le_of_lt L)
    have Eq : packedDebt a=packedDebt b := by omega
    have A := pack_rank a
    have B := pack_rank b
    unfold eventRank at A B
    right
    refine ⟨Eq,?_⟩
    cases X : packedCredit a <;> cases Y : packedCredit b <;>
      simp [X,Y] at A B ⊢ <;> omega

section Glue
variable {X : Type}

-- A local continuation stays in its phase or crosses the immediate
-- boundary. The paying disjunction is strict only in the same phase;
-- a proper phase crossing will pay via the reserved-tail algebra.
def Hop (phase cost : X→Nat) (x y : X) : Prop :=
  (phase y=phase x ∧ cost y≤cost x) ∨ phase y=phase x+1
def Pay (phase cost : X→Nat) (x y : X) : Prop :=
  (phase y=phase x ∧ cost y<cost x) ∨ phase y=phase x+1

def fullRank (b : Caps) (phase cost : X→Nat) (x : X) : Nat :=
  cost x+b.tail (phase x)

theorem hop_rank (b : Caps) (phase cost : X→Nat) (x y : X)
    (I : phase y<5) (B : cost y≤b.at (phase y))
    (H : Hop phase cost x y) :
    fullRank b phase cost y≤fullRank b phase cost x := by
  rcases H with ⟨E,K⟩|E
  · unfold fullRank
    rw [E]
    omega
  · have J : phase x<4 := by omega
    have T := tail_step b (phase x) J
    unfold fullRank
    rw [E] at B ⊢
    omega

theorem pay_rank (b : Caps) (phase cost : X→Nat) (x y : X)
    (I : phase y<5) (B : cost y≤b.at (phase y))
    (Positive : 0<cost x) (H : Pay phase cost x y) :
    fullRank b phase cost y<fullRank b phase cost x := by
  rcases H with ⟨E,K⟩|E
  · unfold fullRank
    rw [E]
    omega
  · have J : phase x<4 := by omega
    have T := tail_step b (phase x) J
    unfold fullRank
    rw [E] at B ⊢
    omega

/-- Local deterministic adapter. In this structure there is no mean,
    no PhaseRows hypothesis and no global rank inequality. The Hop/Pay
    fields are the per-phase obligations on the actual dispatcher.
    Concrete instantiation is explicitly not yet supplied here. -/
structure LocalRows (d : Sheet) (hh : ∃ i,h i=true)
    (P : Raw s n→Prop) (G : GapInput h) (C : Fin 5→Chart h)
    (j : Target h) (b : Caps) (X : Type) where
  raw : X→Raw s n
  good : X→Prop
  phase : X→Nat
  cost : X→Nat
  active : X→Fin 5→Bool
  desired : X→Fin 5→Bool
  advance : X→Fin n→X
  restore : Raw s n→X
  bank : ∀ x,good x→GoodEightBank d hh P G (raw x)
  restore_good : ∀ x,GoodEightBank d hh P G x→good (restore x)
  restore_raw : ∀ x,GoodEightBank d hh P G x→raw (restore x)=x
  phase_bound : ∀ x,good x→phase x<5
  cost_bound : ∀ x,good x→cost x≤b.at (phase x)
  positive : ∀ x,good x→0<cost x
  race : ∀ x,good x→LiveRaces d C (raw x) (active x)
  allowed : ∀ x e,good x→makeBan C (active x) (desired x) e=none→
    classify d h (raw x) e≠some j →
    good (advance x e) ∧ raw (advance x e)=rawNext s (raw x) e ∧
      Hop phase cost x (advance x e)
  paying : ∀ x,good x→∃ e,
    let a := mergeSide (makeBan C (active x) (desired x)) e
    classify d h (raw x) a=some j ∨ Pay phase cost x (advance x a)

structure Obs (X : Type) where
  core : X
  latch : Bool

variable {d : Sheet} {hh : ∃ i,h i=true} {G : GapInput h}
variable {C : Fin 5→Chart h} {j : Target h} {b : Caps}
variable (L : LocalRows d hh P G C j b X)

def project (y : Obs X) : Raw s n×Bool := (L.raw y.core,y.latch)
def good (y : Obs X) : Prop := L.good y.core
def finish (y : Obs X) : Bool := y.latch
def active (y : Obs X) : Fin 5→Bool :=
  if y.latch=true then fun _=>false else L.active y.core
def desired (y : Obs X) : Fin 5→Bool := L.desired y.core
noncomputable def coreBan (x : X) : Fin n→Option (Fin n) :=
  makeBan C (L.active x) (L.desired x)
noncomputable def obsBan (y : Obs X) : Fin n→Option (Fin n) :=
  makeBan C (active L y) (desired L y)

def rank (y : Obs X) : Nat :=
  if y.latch=true then 0 else fullRank b L.phase L.cost y.core

def obsDebt (y : Obs X) : Nat := packedDebt (rank L y)
def obsCredit (y : Obs X) : Bool := packedCredit (rank L y)

noncomputable def init (x : Raw s n) : Obs X := ⟨L.restore x,false⟩

/-- No physical mark is replaced by mergeSide here! In all branches the
    old classifier is evaluated on (raw x,e), including excluded marks. -/
noncomputable def next (y : Obs X) (e : Fin n) : Obs X :=
  let p := ShortTwoPublicationClock.phase (rawNext s) (classify d h) j
      (project L y) e
  if p.2=true then ⟨L.restore p.1,true⟩
  else if coreBan L y.core e=none then ⟨L.advance y.core e,false⟩
  else ⟨L.restore p.1,false⟩

theorem init_good (x : Raw s n) (B : GoodEightBank d hh P G x) :
    good L (init L x) := L.restore_good x B

theorem init_project (x : Raw s n) (B : GoodEightBank d hh P G x) :
    project L (init L x)=(x,false) := by
  change (L.raw (L.restore x),false)=(x,false)
  rw [L.restore_raw x B]

theorem next_spec
    (BC : ∀ x e,GoodEightBank d hh P G x→GoodEightBank d hh P G (rawNext s x e))
    (y : Obs X) (e : Fin n) (H : good L y) :
    good L (next L y e) ∧ project L (next L y e)=
      ShortTwoPublicationClock.phase (rawNext s) (classify d h) j (project L y) e := by
  classical
  let p := ShortTwoPublicationClock.phase (rawNext s) (classify d h) j (project L y) e
  have B : GoodEightBank d hh P G p.1 := BC _ e (L.bank y.core H)
  by_cases F : p.2=true
  · change good L (if p.2=true then ⟨L.restore p.1,true⟩ else
          if coreBan L y.core e=none then ⟨L.advance y.core e,false⟩
          else ⟨L.restore p.1,false⟩) ∧
        project L (if p.2=true then ⟨L.restore p.1,true⟩ else
          if coreBan L y.core e=none then ⟨L.advance y.core e,false⟩
          else ⟨L.restore p.1,false⟩)=p
    rw [if_pos F]
    exact ⟨L.restore_good _ B,Prod.ext (L.restore_raw _ B) F.symm⟩
  · have F0 : p.2=false := by cases E : p.2 <;> simp_all
    have NC : classify d h (L.raw y.core) e≠some j := by
      intro E
      simp [p,ShortTwoPublicationClock.phase,project,E] at F
    unfold next
    change good L (if p.2=true then ⟨L.restore p.1,true⟩ else
          if coreBan L y.core e=none then ⟨L.advance y.core e,false⟩
          else ⟨L.restore p.1,false⟩) ∧
        project L (if p.2=true then ⟨L.restore p.1,true⟩ else
          if coreBan L y.core e=none then ⟨L.advance y.core e,false⟩
          else ⟨L.restore p.1,false⟩)=p
    rw [if_neg F]
    by_cases A : coreBan L y.core e=none
    · rw [if_pos A]
      obtain ⟨Y,R,_⟩ := L.allowed y.core e H A NC
      exact ⟨Y,Prod.ext R F0.symm⟩
    · rw [if_neg A]
      exact ⟨L.restore_good _ B,Prod.ext (L.restore_raw _ B) F0.symm⟩

theorem sticky (y : Obs X) (e : Fin n) (H : finish y=true) :
    finish (next L y e)=true := by
  change y.latch=true at H
  simp [next,finish,ShortTwoPublicationClock.phase,project,H]

theorem rank_bound (y : Obs X) (H : good L y) :
    rank L y≤b.total := by
  unfold rank
  split
  · exact Nat.zero_le _
  · unfold fullRank
    have U := L.cost_bound y.core H
    have B := cap_tail_le b (L.phase y.core) (L.phase_bound y.core H)
    omega

theorem live_ban (y : Obs X) (H : y.latch=false) :
    obsBan L y=coreBan L y.core := by
  simp [obsBan,coreBan,active,desired,H]

theorem allowed_rank (y : Obs X) (e : Fin n) (H : good L y)
    (Live : y.latch=false) (A : coreBan L y.core e=none) :
    rank L (next L y e)≤rank L y ∧
    ((classify d h (L.raw y.core) e=some j ∨
      Pay L.phase L.cost y.core (L.advance y.core e)) →
      rank L (next L y e)<rank L y) := by
  classical
  by_cases Pub : classify d h (L.raw y.core) e=some j
  · have Positive := L.positive y.core H
    simp [next,ShortTwoPublicationClock.phase,project,rank,Live,Pub,fullRank]
    omega
  · obtain ⟨Y,_,Hop0⟩ := L.allowed y.core e H A Pub
    have I := L.phase_bound _ Y
    have B := L.cost_bound _ Y
    have Idle := hop_rank b L.phase L.cost y.core (L.advance y.core e) I B Hop0
    have Pay0 : Pay L.phase L.cost y.core (L.advance y.core e) →
        fullRank b L.phase L.cost (L.advance y.core e)<fullRank b L.phase L.cost y.core :=
      pay_rank b L.phase L.cost y.core (L.advance y.core e) I B (L.positive y.core H)
    simpa [next,ShortTwoPublicationClock.phase,project,rank,Live,Pub,A] using
      (show fullRank b L.phase L.cost (L.advance y.core e)≤
          fullRank b L.phase L.cost y.core ∧
        (Pay L.phase L.cost y.core (L.advance y.core e) →
          fullRank b L.phase L.cost (L.advance y.core e)<fullRank b L.phase L.cost y.core)
        from ⟨Idle,Pay0⟩)

theorem allowed_image (inj : Function.Injective (fun k=>center (C k)))
    (y : Obs X) (_H : good L y) (Live : y.latch=false) (e : Fin n) :
    coreBan L y.core (mergeSide (obsBan L y) e)=none := by
  rw [live_ban L y Live]
  exact ReportFastRawRelift.allowed_after_merge (coreBan L y.core)
    (pairs_from_centers hh G C inj (L.active y.core) (L.desired y.core)
      (coreBan L y.core) (makeBan_spec hh G C inj _ _)) e

theorem driver_idle (inj : Function.Injective (fun k=>center (C k)))
    (y : Obs X) (e : Fin n) (H : good L y) (Live : finish y≠true) :
    rank L (next L y (mergeSide (obsBan L y) e))≤rank L y := by
  have B : y.latch=false := by
    cases E : y.latch <;> simp_all [finish]
  exact (allowed_rank L y _ H B (allowed_image L inj y H B e)).1

theorem driver_pay (inj : Function.Injective (fun k=>center (C k)))
    (y : Obs X) (H : good L y) (Live : finish y≠true) :
    ∃ a e,mergeSide (obsBan L y) e=a ∧ rank L (next L y a)<rank L y := by
  have B : y.latch=false := by
    cases E : y.latch <;> simp_all [finish]
  obtain ⟨e,Pay0⟩ := L.paying y.core H
  let a := mergeSide (obsBan L y) e
  refine ⟨a,e,rfl,?_⟩
  have A := allowed_image L inj y H B e
  apply (allowed_rank L y a H B A).2
  simpa only [a,live_ban L y B,coreBan] using Pay0

theorem service_no_rearm_credit
    (inj : Function.Injective (fun k=>center (C k))) :
    ∀ y e,good L y→finish y≠true→
    obsDebt L (next L y (mergeSide (obsBan L y) e))=obsDebt L y→
    (obsCredit L (next L y (mergeSide (obsBan L y) e))).toNat≤(obsCredit L y).toNat := by
  intro y e H B E
  exact pack_credit_idle (driver_idle L inj y e H B) E

theorem service_phase_nominate
    (inj : Function.Injective (fun k=>center (C k))) :
    ∀ y,good L y→finish y≠true→∃ a e,mergeSide (obsBan L y) e=a ∧
      (obsDebt L (next L y a)<obsDebt L y ∨
       (obsDebt L (next L y a)=obsDebt L y ∧ obsCredit L y=true ∧
         obsCredit L (next L y a)=false)) := by
  intro y H B
  obtain ⟨a,e,E,R⟩ := driver_pay L inj y H B
  exact ⟨a,e,E,pack_progress R⟩

-- PACE is separate item 10(d). State it in the identical type, not as
-- a mean-time conclusion and not as something proved by the splice.
def Pace (t w W : Nat) : Prop :=
  ∀ y,good L y→∀ v,
    v.length=block t W n→
    let u := mapWord (next L) (fun z=>mergeSide (obsBan L z)) y v
    3*t*w*choices (next L) (fun z=>mergeSide (obsBan L z)) y u≤
      3*t*w*5+reward (next L) (fun z e=>mark5 d C (project L z).1 e) y u

theorem phaseRows_of_local
    (inj : Function.Injective (fun k=>center (C k)))
    (BC : ∀ x e,GoodEightBank d hh P G x→GoodEightBank d hh P G (rawNext s x e))
    (t w W : Nat) (Cap : b.total≤2*(518*t*W)+1)
    (PACE : Pace L t w W) :
    PhaseRows (P:=P) d hh G C (next L) (good L) finish (project L)
      (obsBan L) (active L) (desired L) (obsDebt L) (obsCredit L) t w W := by
  constructor
  · intro y e H
    exact (next_spec L BC y e H).1
  · intro y H
    exact L.bank y.core H
  · intro y e H
    exact congrArg Prod.fst (next_spec L BC y e H).2
  · intro y _ e a
    exact makeBan_spec hh G C inj (active L y) (desired L y) e a
  · intro y H k A
    by_cases B : y.latch=true
    · simp [active,B] at A
    · exact L.race y.core H k (by simpa [active,B] using A)
  · intro y H
    have E := rank_bound L y H
    unfold obsDebt packedDebt
    omega
  · intro y e H B
    exact pack_debt_idle (driver_idle L inj y e H B)
  · exact service_no_rearm_credit L inj
  · exact service_phase_nominate L inj
  · exact PACE

theorem splice_mean
    (inj : Function.Injective (fun k=>center (C k)))
    (BC : ∀ x e,GoodEightBank d hh P G x→GoodEightBank d hh P G (rawNext s x e))
    (y : Obs X) (H : good L y) :
    Height.IIDExpectedHittingTimeAtMost
      (driverStep (next L) (fun z=>mergeSide (obsBan L z)))
      (fun z=>finish z=true) y (n*b.total) := by
  have M := driver_nominated_mean (next L) (fun z=>mergeSide (obsBan L z))
    (good L) (fun z=>finish z=true) (rank L)
    (fun z e Z=>(next_spec L BC z e Z).1)
    (fun z e Z B=>driver_idle L inj z e Z B)
    (fun z Z B=>driver_pay L inj z Z B) y H
  intro k
  have B := Nat.mul_le_mul_left n (rank_bound L y H)
  exact Nat.le_trans (M k) (Nat.mul_le_mul_right _ B)

-- CHECK: ReportFastItem10Assembly.lean:13–50 is the exact field order.
-- pairs_from_centers is exported in the same imports as paper_kernel_of_rows.
-- ReportGatePairs.lean eventRank and ReportAdaptiveRank.lean:44–55
-- give the packing and driver_nominated_mean signatures.
-- At the two simp calls on Bool in allowed_rank, if simp closes the
-- goal use "simp [...] <;> omega", not a following standalone omega.
end Glue
end L4.ReportFastSplice


#print axioms L4.ReportFastSplice.reset_pre_entry
#print axioms L4.ReportFastSplice.pre_own_clear_step
#print axioms L4.ReportFastSplice.pre_acq_entry
#print axioms L4.ReportFastSplice.acq_before_mark
#print axioms L4.ReportFastSplice.acq_fenced_snoc
#print axioms L4.ReportFastSplice.post_context_of_consume
#print axioms L4.ReportFastSplice.acq_local_closed
#print axioms L4.ReportFastSplice.acq_nominate
#print axioms L4.ReportFastSplice.acq_budget
#print axioms L4.ReportFastSplice.cap_total
#print axioms L4.ReportFastSplice.phaseRows_of_local
#print axioms L4.ReportFastSplice.splice_mean

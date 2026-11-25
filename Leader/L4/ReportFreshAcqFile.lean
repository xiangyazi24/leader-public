import Leader.L4.ReportAcquireAllCaptures
import Leader.L4.ReportGoodEightBank
import Leader.L4.ReportOwnerCommandRail

namespace L4.ReportFreshAcqFile
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerDoorProjection
open ReportOwnerIssueControl ReportOwnerReverseControl ReportOwnerForwardControl
open ReportOwnerReverseShape ReportOwnerForwardLocations ReportPrelaunchDoorLift
open ReportOwnerAcquireReturn ReportOwnerAcquireProvenance ReportAcquireAllCaptures
open ReportOwnerCommandRail ReportGoodEightCut ReportGoodEightBank
open ReportLeaseGrants ReportGrantTimeline

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def Cold (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  (readPC d C x).2<acqOp (params d s) ∨
    readPC d C x=(1,acqOp (params d s))

def LaunchedAt (d : Sheet) (C : Chart h) (b : Raw s n)
    (lead : List (Fin n)) : Prop :=
  let a := rawRun b lead
  LegalIssue d C a ∧ readPC d C a=(1,acqOp (params d s))

/-- Every witness is a subword split of the ONE raw suffix from b.
    We do not existentially choose a different history at each use. -/
def AcqPhase (d : Sheet) (C : Chart h) (b : Raw s n)
    (w : List (Fin n)) : Prop :=
  Cold d C (rawRun b w) ∨
    (∃ lead flight : List (Fin n),
      w=lead++(door C::flight) ∧ LaunchedAt d C b lead ∧
      BeforeConsume d C (rawNext s (rawRun b lead) (door C)) flight) ∨
    (∃ lead flight post : List (Fin n),
      w=lead++(door C::(flight++(door C::post))) ∧
      LaunchedAt d C b lead ∧
      let x0 := rawNext s (rawRun b lead) (door C)
      let old := rawRun x0 flight
      BeforeConsume d C x0 flight ∧ (tok d C old 0).tag=3 ∧
      (tok d C old 0).outcome≠1 ∧
      NoRestartTape d C (rawNext s old (door C)) post)

private theorem nr_snoc (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) (A : NoRestartTape d C x w)
    (NZ : (readPC d C (rawNext s (rawRun x w) e)).2≠0) :
    NoRestartTape d C x (w++[e]) := by
  induction w generalizing x with
  | nil => exact ⟨NZ,trivial⟩
  | cons a w IH => exact ⟨A.1,IH (rawNext s x a) A.2 NZ⟩

private theorem legal_of_issue_phase (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : StrongSerial d C x) (P : (readPC d C x).1=1) :
    LegalIssue d C x := by
  rcases A.1 with I|⟨k,I⟩|⟨k,I⟩
  · exact I
  · have H := I.1.1
    omega
  · have H := I.1.1
    omega

private theorem preview_below_acq (p : Params) {a b : Nat}
    (P : PreviewNextOp p.digits a b) (H : a<acqOp p) :
    b≤acqOp p := by
  unfold acqOp at H ⊢
  cases P <;> omega

private theorem flight_pc (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (A : FlightAt d C x0 w) :
    readPC d C (rawRun x0 w)=(2,acqOp (params d s)) := by
  rcases A with ⟨k,q,R,_⟩|⟨k,q,R,_⟩
  · exact R.pc
  · exact R.pc

/-- All-mark history update on the actual tape. StrongSerial is the
    checked receipt-anchored rail, not an assumed payload history. -/
theorem phase_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (digit : 0<(params d s).digits)
    (b : Raw s n) (B : Cached d hh Q b) (w : List (Fin n))
    (A : StrongSerial d C (rawRun b w)) (P : AcqPhase d C b w)
    (e : Fin n) : AcqPhase d C b (w++[e]) := by
  let p := params d s
  let x := rawRun b w
  let CF := cached_fibre d N hh Q F
  have X : Cached d hh Q x := cached_run d N hh F b B w
  have ColdAfter (L : Cold d C (rawNext s x e)) :
      AcqPhase d C b (w++[e]) := by
    left
    rw [ShortOwnerEpochJS.raw_snoc]
    exact L
  rcases P with P|⟨lead,flight,W,J,T⟩|⟨lead,flight,post,W,J,T,Tag,ND,NR⟩
  · rcases P with Below|Issue
    · apply ColdAfter
      rcases pc_step_with_phase d C N hh G F digit x X A e with R|H|⟨F0,H⟩
      · left
        rw [R.1]
        unfold acqOp
        omega
      · left
        rw [H]
        exact Below
      · have K := preview_below_acq p H Below
        by_cases L : (readPC d C (rawNext s x e)).2<acqOp p
        · exact .inl L
        · right
          apply Prod.ext F0
          change (readPC d C (rawNext s x e)).2=acqOp p
          change (readPC d C (rawNext s x e)).2≤acqOp p at K
          omega
    · by_cases E : e=door C
      · subst e
        have I := legal_of_issue_phase d C x A (congrArg Prod.fst Issue)
        exact .inr (.inl ⟨w,[],rfl,⟨I,Issue⟩,.nil⟩)
      · apply ColdAfter
        right
        rw [raw_nondoor_control d C x e N (CF.mask x X) E]
        exact Issue
  · let a := rawRun b lead
    let x0 := rawNext s a (door C)
    let old := rawRun x0 flight
    have Ex : x=old := by
      dsimp only [x,old,x0,a]
      rw [W,ShortOwnerEpochJS.raw_append]
      rfl
    have Xa : Cached d hh Q a := cached_run d N hh F b B lead
    by_cases NC : NoConsume d C old e
    · exact .inr (.inl ⟨lead,flight++[e],by simp only [W,List.append_assoc,List.cons_append],
        J,.snoc e T NC⟩)
    · have Door : e=door C := by
        by_cases H : e=door C
        · exact H
        · exact (NC (.inl H)).elim
      have Tag : (tok d C old 0).tag=3 := by
        by_cases H : (tok d C old 0).tag=3
        · exact H
        · exact (NC (.inr H)).elim
      subst e
      by_cases Denied : (tok d C old 0).outcome=1
      · obtain ⟨X0,L⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N a Xa J.1 J.2
        obtain ⟨Y,H⟩ := flight_run d C hh G F N x0 X0 L digit flight T
        have PC := flight_pc d C x0 flight H
        let v := selectBytes d (old C.root)
        let t := publicationToken p true v 0
        have Q0 : tok d C old 0=t := by
          rw [root_tok]
          exact (prelaunch_root_decode p v).symm
        have Z := acq_source_denied_pc p v t (congrArg Prod.fst PC)
          (congrArg Prod.snd PC) (by rwa [←Q0]) (by rwa [←Q0])
        have YPC : readPC d C (rawNext s old (door C))=acqSourcePC p v t :=
          (raw_door_final d C old N (CF.mask old Y)).1
        apply ColdAfter
        left
        rw [Ex,YPC,Z]
        unfold acqOp
        omega
      · exact .inr (.inr ⟨lead,flight,[],
          by simp only [W,List.append_assoc,List.cons_append],
          J,T,Tag,Denied,trivial⟩)
  · let a := rawRun b lead
    let old := rawRun (rawNext s a (door C)) flight
    let after := rawNext s old (door C)
    have Ex : x=rawRun after post := by
      dsimp only [x,after,old,a]
      rw [W,ShortOwnerEpochJS.raw_append]
      change rawRun (rawNext s (rawRun b lead) (door C))
        (flight++(door C::post))=_
      rw [ShortOwnerEpochJS.raw_append]
      rfl
    by_cases Z : (readPC d C (rawNext s x e)).2=0
    · apply ColdAfter
      left
      rw [Z]
      unfold acqOp
      omega
    · exact .inr (.inr ⟨lead,flight,post++[e],
        by simp only [W,List.append_assoc,List.cons_append],
        J,T,Tag,ND,nr_snoc d C after post e NR (by rwa [←Ex])⟩)

/-- Same current-state owner predicate which the checked CUT2
    FreshFileRows consumer expects. The origin is an actual own
    RESET from the post-first-cut domain. The tape witness extends
    across *every* mark; it does not freeze the owner at FullParked. -/
def FreshAcqEpoch (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) (C : Chart h) (x : Raw s n) : Prop :=
  ∃ a : Raw s n, ∃ reset w : List (Fin n),
    FirstCut d hh Q G a ∧ Generated d C a reset .done ∧
    x=rawRun (rawRun a reset) w ∧ AcqPhase d C (rawRun a reset) w

/-- ACQ file provenance closure needs no inactive-bank premise.
It tracks the true successful old captures, not the later digit computation. -/
theorem fresh_acq_epoch_step (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (C : Chart h)
    (x : Raw s n) (e : Fin n) (A : FreshAcqEpoch d hh Q G C x) :
    FreshAcqEpoch d hh Q G C (rawNext s x e) := by
  obtain ⟨a,reset,w,B,R,E,P⟩ := A
  let b := rawRun a reset
  have X := B.1.1.1
  have Y := cached_run d N hh F a X reset
  have S := seed_receipt d C N hh F a X reset R
  have U := strong_run d C N hh G F digit b Y S w
  refine ⟨a,reset,w++[e],B,R,?_,phase_step d C hh G F N digit b Y w U.2.1 P e⟩
  rw [ShortOwnerEpochJS.raw_snoc,E]

theorem fresh_acq_rows (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) :
    FreshFileRows d hh Q G (FreshAcqEpoch d hh Q G) := by
  constructor
  · intro C a w A R P
    refine ⟨a,w,[],A,R,rfl,.inl (.inl ?_)⟩
    have B := pc_fields d C (rawRun a w) .issue1 (by decide) P.1.1
    change (readPC d C (rawRun a w)).2<acqOp (params d s)
    unfold readPC
    rw [B]
    change 1 < acqOp (params d s)
    unfold acqOp
    omega
  · intro C x e _ _ A
    exact fresh_acq_epoch_step d N hh G F digit C x e A

/-- Exact current-file consequence. A positive post-ACQ controller
    has a genuine post-first-cut successful ACQ origin, the literal
    captured fields, and their own grants through the present suffix.
    This is not vacuous history-only reachability. -/
theorem fresh_current_captures (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (C : Chart h) (x : Raw s n)
    (A : FreshAcqEpoch d hh Q G C x)
    (Live : cmpOp (params d s)≤(readPC d C x).2) :
    ∃ a : Raw s n, ∃ reset lead flight post : List (Fin n),
      FirstCut d hh Q G a ∧ Generated d C a reset .done ∧
      let issue := rawRun (rawRun a reset) lead
      let x0 := rawNext s issue (door C)
      let old := rawRun x0 flight
      let after := rawNext s old (door C)
      x=rawRun after post ∧
      LegalIssue d C issue ∧ readPC d C issue=(1,acqOp (params d s)) ∧
      BeforeConsume d C x0 flight ∧ (tok d C old 0).tag=3 ∧
      (tok d C old 0).outcome≠1 ∧ NoRestartTape d C after post ∧
      ownerCaptureSix d C x=(tok d C old 0).payload%64 ∧
      ∀ i,i<C.L→h (out C i)=true→
        CapturedAt d C x0 flight i (ownerCaptureSix d C x) ∧
        HeldAlong d (out C i) (C.route.port i) after post := by
  obtain ⟨a,reset,w,B,R,E,P⟩ := A
  let b := rawRun a reset
  have B0 := first_cut_run d N hh G F digit a B reset
  rcases P with P|⟨lead,flight,W,J,T⟩|⟨lead,flight,post,W,J,T,Tag,ND,NR⟩
  · rw [E] at Live
    rcases P with K|K
    · unfold cmpOp at Live
      unfold acqOp at K
      omega
    · rw [K] at Live
      unfold cmpOp acqOp at Live
      omega
  · let issue := rawRun b lead
    have A0 := first_cut_run d N hh G F digit b B0 lead
    obtain ⟨X0,F0⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N issue A0.1.1.1 J.1 J.2
    obtain ⟨_,H⟩ := flight_run d C hh G F N _ X0 F0 digit flight T
    have PC := flight_pc d C _ flight H
    have Eq : x=rawRun (rawNext s issue (door C)) flight := by
      rw [E,W,ShortOwnerEpochJS.raw_append]
      rfl
    rw [Eq,PC] at Live
    unfold cmpOp acqOp at Live
    omega
  · let issue := rawRun b lead
    let old := rawRun (rawNext s issue (door C)) flight
    let after := rawNext s old (door C)
    have A0 := first_cut_run d N hh G F digit b B0 lead
    have Eq : x=rawRun after post := by
      rw [E,W,ShortOwnerEpochJS.raw_append]
      change rawRun (rawNext s issue (door C)) (flight++(door C::post))=_
      rw [ShortOwnerEpochJS.raw_append]
      rfl
    have U := all_captures_after_consume d C hh G F N issue A0.1.1.1
      J.1 J.2 A0.1.2 digit flight T Tag ND post NR
    refine ⟨a,reset,lead,flight,post,B,R,Eq,J.1,J.2,T,Tag,ND,NR,?_,?_⟩
    · rw [Eq]
      exact U.2.2.1
    · rw [Eq]
      exact U.2.2.2

/-- The concrete item-1 ACQ file history itself is present at the
same second cut without RailSupplier or a BankSafe hypothesis. -/
theorem fresh_acq_at_second (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (A : SecondCutHistory d hh Q G x) :
    ∀ C∈ReportPrelaunchAllOwners.ownerCharts G,FreshAcqEpoch d hh Q G C x := by
  intro C M
  obtain ⟨a,flight,post,B,R,P,E⟩ := second_owner_seed d N hh G F digit x A C M
  have init := (fresh_acq_rows d N hh G F digit).seed C a flight B R P
  have go (z : Raw s n) (Y : FreshAcqEpoch d hh Q G C z) (w : List (Fin n)) :
      FreshAcqEpoch d hh Q G C (rawRun z w) := by
    induction w generalizing z with
    | nil => exact Y
    | cons e w IH =>
      exact IH _ (fresh_acq_epoch_step d N hh G F digit C z e Y)
  rw [E]
  exact go _ init post

end L4.ReportFreshAcqFile

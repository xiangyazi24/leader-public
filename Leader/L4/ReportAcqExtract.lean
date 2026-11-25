import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportGoodEightCut

namespace L4.ReportAcqExtract
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerDoorProjection
open ReportPrelaunchDoorLift ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerIssueControl ReportOwnerForwardControl ReportOwnerReverseControl
open ReportOwnerSerial ReportByteRows ReportRawProjection ReportOwnerCommandRail
open ReportOwnerAcquireProvenance ReportOwnerAcquireReturn ReportPrelaunchRank

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- Splitting before the first real consume, on exactly the sampled marks. -/
theorem split_first_consume (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) :
    BeforeConsume d C x w ∨
    ∃ u v : List (Fin n), w=u++door C::v ∧ BeforeConsume d C x u ∧
      (tok d C (rawRun x u) 0).tag=3 := by
  rw [←List.reverse_reverse w]
  induction w.reverse with
  | nil => exact .inl .nil
  | cons e rev IH =>
    rw [List.reverse_cons]
    let w := rev.reverse
    rcases IH with H | ⟨u,v,W,T,K⟩
    · by_cases E : e=door C
      · subst e
        by_cases T : (tok d C (rawRun x w) 0).tag=3
        · exact .inr ⟨w,[],rfl,H,T⟩
        · exact .inl (.snoc (door C) H (.inr T))
      · exact .inl (.snoc e H (.inl E))
    · exact .inr ⟨u,v++[e],by rw [W,List.append_assoc]; rfl,T,K⟩

theorem live_acq_pc (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (P : readPC d C x=(1,acqOp (params d s)))
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s x (door C)) w) :
    readPC d C (rawRun (rawNext s x (door C)) w)=(2,acqOp (params d s)) := by
  obtain ⟨Y,A⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N x X I P
  rcases (flight_run d C hh G F N _ Y A digit w T).2 with ⟨_,_,R,_⟩ | ⟨_,_,R,_⟩
  · exact R.pc
  · exact R.pc

theorem denied_consume_retry (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (R : ReverseWait d C x 0) (Bad : (tok d C x 0).outcome=1) :
    Retry0 d C (rawNext s x (door C)) := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have root : tok d C x 0=t := by rw [root_tok]; rfl
  have H : t.tag=3 := by rw [←root,R.2.2 0 C.positive]; rfl
  have B : t.outcome=1 := root.symm ▸ Bad
  have E := prelaunch_wait_bad_reply p v t R.1.1 R.1.2
    (by rw [H]; decide) (by rw [H]; decide) (.inr (.inr (.inr B)))
  have W := (raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)).1
  change source p v (publicationToken p true v 0)= _ at E
  rw [E] at W
  exact ⟨congrArg Prod.snd (W.trans (prelaunch_restart_controls p v)),
    door_consumes_root d C hh G F N x X R digit⟩

/-- On the original launched tape, the first consume is either a clean
retry or the healthy consume of this flight and installation of CMP. -/
theorem first_consume_outcome (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (P : readPC d C x=(1,acqOp (params d s)))
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s x (door C)) w)
    (Tag : (tok d C (rawRun (rawNext s x (door C)) w) 0).tag=3) :
    let y := rawRun (rawNext s x (door C)) w
    Retry0 d C (rawNext s y (door C)) ∨
    ((tok d C y 0).outcome≠1 ∧
      readPC d C (rawNext s y (door C))=(1,cmpOp (params d s))) := by
  dsimp only
  let y := rawRun (rawNext s x (door C)) w
  by_cases Bad : (tok d C y 0).outcome=1
  · obtain ⟨Y,A⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N x X I P
    obtain ⟨Z,S⟩ := flight_run d C hh G F N _ Y A digit w T
    have R : ReverseWait d C y 0 := by
      rcases S with ⟨k,q,H,_⟩|⟨k,q,H,_⟩
      · have E := H.shape.2.2 0 C.positive
        change (tok d C y 0).tag=frontTag k 0 at E
        rw [Tag] at E
        by_cases J : k=0
        · subst k; contradiction
        · simp [frontTag,show 0<k by omega] at E
      · by_cases J : k=0
        · simpa only [J] using H.shape
        · have E := H.shape.2.2 0 C.positive
          change (tok d C y 0).tag=backTag k 0 at E
          rw [Tag] at E
          simp [backTag,show 0<k by omega] at E
    exact .inl (denied_consume_retry d C N hh G F digit y Z R Bad)
  · obtain ⟨Y,R,O,K,Live,_⟩ :=
      from_genuine_issue d C hh G F N x X I P digit w T Tag Bad
    obtain ⟨_,_,PC,_,_⟩ :=
      raw_acq_consume d C hh G F N y Y R O K Live Bad _ rfl digit
    exact .inr ⟨Bad,PC⟩

private theorem root_pub (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true (selectBytes d (x C.root)) 0 := by
  rw [root_tok]; rfl

private theorem pc_step_shape (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (A : StrongSerial d C x)
    (e : Fin n) :
    let y := rawNext s x e
    Retry0 d C y ∨
      (readPC d C y).2=(readPC d C x).2 ∨
      (EmptyIssueShape d C y ∧
       PreviewNextOp (params d s).digits (readPC d C x).2 (readPC d C y).2) := by
  dsimp only
  have M := (cached_fibre d N hh Q F).mask x X
  by_cases D : e=door C
  · subst e
    let p := params d s
    let v := selectBytes d (x C.root)
    let t := publicationToken p true v 0
    let y := rawNext s x (door C)
    have W := (raw_door_final d C x N M).1
    have Hold (P : LegalWait d C x)
        (T : (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2) :
        (readPC d C y).2=(readPC d C x).2 := by
      rw [root_pub] at T
      exact congrArg Prod.snd (W.trans (prelaunch_hold_controls p v t P.1 P.2 T))
    rcases A.1 with I|⟨k,I⟩|⟨k,I⟩
    · rcases door_step d C hh G F N x X I with R|⟨_,PC⟩
      · exact .inl R
      · exact .inr (.inl PC)
    · apply Or.inr; apply Or.inl; apply Hold I.1
      rw [I.2.2 0 C.positive]
      by_cases K : k=0
      · subst k; exact .inr rfl
      · exact .inl (by simp [frontTag,show 0<k by omega])
    · by_cases K : k=0
      · subst k
        have RT : t.tag=3 := by
          change (publicationToken (params d s) true (selectBytes d (x C.root)) 0).tag=3
          rw [←root_pub d C x,I.2.2 0 C.positive]
          rfl
        rcases prelaunch_wait_controls p v t I.1.1 I.1.2
            (by rw [RT]; decide) (by rw [RT]; decide) digit with R|⟨b,B,R⟩
        · exact .inl ⟨congrArg Prod.snd (W.trans R),
            door_consumes_root d C hh G F N x X I digit⟩
        · apply Or.inr; apply Or.inr
          have E : (readPC d C y).2=b := congrArg Prod.snd (W.trans R)
          refine ⟨door_consumes_root d C hh G F N x X I digit,?_⟩
          rw [E]
          exact B
      · apply Or.inr; apply Or.inl; apply Hold I.1
        rw [I.2.2 0 C.positive]
        exact .inl (by simp [backTag,show 0<k by omega])
  · exact .inr (.inl (congrArg Prod.snd (raw_nondoor_control d C x e N M D)))

private theorem logical_acq (m : Nat) : logical m (m+2)=m+2 := by
  simp [logical,show m+2<2*m+3 by omega]

private theorem logical_ACQ_inv (m a : Nat) (A : logical m a=m+2) : a=m+2 := by
  unfold logical at A
  split at A
  · exact A
  · split at A
    · omega
    · split at A <;> omega

private theorem logical_zero (m : Nat) : logical m 0=0 := by
  simp [logical,show 0<2*m+3 by omega]

private theorem no_restart_snoc (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) (R : NoRestartTape d C x w)
    (E : (readPC d C (rawNext s (rawRun x w) e)).2≠0) :
    NoRestartTape d C x (w++[e]) := by
  induction w generalizing x with
  | nil => exact ⟨E,trivial⟩
  | cons a w IH => exact ⟨R.1,IH _ R.2 E⟩

def AcqHistory (d : Sheet) (C : Chart h) (x : Raw s n) (w : List (Fin n)) : Prop :=
  ∃ pre fly post : List (Fin n),
    w=pre++door C::(fly++door C::post) ∧
    let a := rawRun x pre
    let start := rawNext s a (door C)
    let r := rawRun start fly
    LegalIssue d C a ∧ readPC d C a=(1,acqOp (params d s)) ∧
    BeforeConsume d C start fly ∧ (tok d C r 0).tag=3 ∧
    (tok d C r 0).outcome≠1 ∧
    NoRestartTape d C (rawNext s r (door C)) post

def AcqProgress (d : Sheet) (C : Chart h) (x : Raw s n) (w : List (Fin n)) : Prop :=
  let z := rawRun x w
  logical (params d s).digits (readPC d C z).2 < acqOp (params d s) ∨
  (LegalIssue d C z ∧ readPC d C z=(1,acqOp (params d s))) ∨
  (∃ pre fly : List (Fin n), w=pre++door C::fly ∧
    let a := rawRun x pre
    LegalIssue d C a ∧ readPC d C a=(1,acqOp (params d s)) ∧
    BeforeConsume d C (rawNext s a (door C)) fly) ∨
  AcqHistory d C x w

private theorem issue_of_phase (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : StrongSerial d C x) (P : (readPC d C x).1=1) : LegalIssue d C x := by
  rcases A.1 with I|⟨j,I⟩|⟨j,I⟩
  · exact I
  · have := I.1.1
    omega
  · have := I.1.1
    omega

theorem acq_progress_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (A : StrongSerial d C x) (w : List (Fin n))
    (H : AcqProgress d C x w) (e : Fin n) :
    AcqProgress d C x (w++[e]) := by
  let m := (params d s).digits
  let z := rawRun x w
  let y := rawNext s z e
  have ZS := strong_run d C N hh G F digit x X A w
  have YS := strong_step d C N hh G F z ZS.1 ZS.2.1 digit e
  change _ at H
  unfold AcqProgress
  rw [ShortOwnerEpochJS.raw_snoc]
  change logical m (readPC d C y).2 < acqOp (params d s) ∨ _ ∨ _ ∨ _
  by_cases L : logical m (readPC d C y).2 < acqOp (params d s)
  · exact .inl L
  have NZ : (readPC d C y).2≠0 := by
    intro E
    apply L
    rw [E,logical_zero]
    unfold acqOp
    omega
  rcases H with Lo|⟨I,P⟩|Fly|Good
  · rcases pc_step_shape d C N hh G F digit z ZS.1 ZS.2.1 e with R| E|⟨J,V⟩
    · exact (NZ R.1).elim
    · exact (L (E ▸ Lo)).elim
    · have E := preview_logical V
      have B : logical m (readPC d C y).2=m+2 := by
        change logical m (readPC d C z).2 < m+2 at Lo
        change ¬logical m (readPC d C y).2 < m+2 at L
        change logical m (readPC d C y).2=logical m (readPC d C z).2+1 at E
        omega
      have Op := logical_ACQ_inv m _ B
      exact .inr (.inl ⟨issue_of_phase d C y YS J.1,Prod.ext J.1 Op⟩)
  · by_cases D : e=door C
    · subst e
      exact .inr (.inr (.inl ⟨w,[],rfl,I,P,.nil⟩))
    · have E := raw_nondoor_control d C z e N ((cached_fibre d N hh Q F).mask z ZS.1) D
      have PC := E.trans P
      exact .inr (.inl ⟨issue_of_phase d C y YS (congrArg Prod.fst PC),PC⟩)
  · obtain ⟨pre,fly,W,I,P,T⟩ := Fly
    let a := rawRun x pre
    let start := rawNext s a (door C)
    have Z : z=rawRun start fly := by
      dsimp only [z]
      rw [W,ShortOwnerEpochJS.raw_append]
      rfl
    by_cases D : e=door C
    · subst e
      by_cases Tag : (tok d C z 0).tag=3
      · have XA := (strong_run d C N hh G F digit x X A pre).1
        have Outcome := first_consume_outcome d C N hh G F digit a XA I P fly T (Z ▸ Tag)
        dsimp only at Outcome
        rw [←Z] at Outcome
        rcases Outcome with R|⟨ND,_⟩
        · exact (NZ R.1).elim
        · exact .inr (.inr (.inr ⟨pre,fly,[],by rw [W,List.append_assoc]; rfl,
              I,P,T,Z ▸ Tag,Z ▸ ND,trivial⟩))
      · exact .inr (.inr (.inl ⟨pre,fly++[door C],by rw [W,List.append_assoc]; rfl,
          I,P,.snoc (door C) T (.inr (Z ▸ Tag))⟩))
    · exact .inr (.inr (.inl ⟨pre,fly++[e],by rw [W,List.append_assoc]; rfl,
          I,P,.snoc e T (.inl D)⟩))
  · obtain ⟨pre,fly,post,W,I,P,T,Tag,ND,NR⟩ := Good
    let a := rawRun x pre
    let r := rawRun (rawNext s a (door C)) fly
    let b := rawNext s r (door C)
    have Z : z=rawRun b post := by
      dsimp only [z]
      rw [W,ShortOwnerEpochJS.raw_append]
      change rawRun (rawNext s a (door C)) (fly++door C::post)=_
      rw [ShortOwnerEpochJS.raw_append]
      rfl
    exact .inr (.inr (.inr ⟨pre,fly,post++[e],by simp only [W,List.append_assoc,List.cons_append],
      I,P,T,Tag,ND,no_restart_snoc d C b post e NR (Z ▸ NZ)⟩))

theorem acq_progress_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (A : StrongSerial d C x)
    (Initial : logical (params d s).digits (readPC d C x).2 < acqOp (params d s))
    (w : List (Fin n)) : AcqProgress d C x w := by
  rw [←List.reverse_reverse w]
  induction w.reverse with
  | nil => exact .inl Initial
  | cons e rev IH =>
    rw [List.reverse_cons]
    exact acq_progress_step d C N hh G F digit x X A rev.reverse IH e

/-- Extract the successful ACQ in the current (not a prior aborted)
generation on the same post-receipt tape. Any retry has discarded its
earlier witness; the selected reply is the first consume of its issue. -/
theorem acq_history_after_receipt (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (reset w : List (Fin n)) (R : Generated d C x reset .done)
    (End : acqOp (params d s) <
      logical (params d s).digits (readPC d C (rawRun (rawRun x reset) w)).2) :
    AcqHistory d C (rawRun x reset) w := by
  obtain ⟨Y,Park⟩ := cached_genuine_full_parked d C N hh F x X reset R
  have A := seed_receipt d C N hh F x X reset R
  have PC := pc_fields d C (rawRun x reset) .issue1 (by decide) Park.1.1
  have Init : logical (params d s).digits (readPC d C (rawRun x reset)).2 <
      acqOp (params d s) := by
    change readPC d C (rawRun x reset)=(1,1) at PC
    rw [PC]
    unfold acqOp
    simp [logical,show 1<2*(params d s).digits+3 by omega]
  rcases acq_progress_run d C N hh G F digit (rawRun x reset) Y A Init w with L|⟨_,P⟩|Fly|H
  · omega
  · rw [P] at End
    change (params d s).digits+2 < logical (params d s).digits ((params d s).digits+2) at End
    rw [logical_acq] at End
    omega
  · obtain ⟨pre,fly,W,I,P,T⟩ := Fly
    have Y' := (strong_run d C N hh G F digit _ Y A pre).1
    have E := live_acq_pc d C N hh G F digit _ Y' I P fly T
    rw [W,ShortOwnerEpochJS.raw_append] at End
    change acqOp (params d s) <
      logical (params d s).digits (readPC d C (rawRun
        (rawNext s (rawRun (rawRun x reset) pre) (door C)) fly)).2 at End
    rw [E] at End
    change (params d s).digits+2 < logical (params d s).digits ((params d s).digits+2) at End
    rw [logical_acq] at End
    omega
  · exact H

theorem logical_after_acq_of_preseal (p : Params) (a : Nat)
    (Lo : cmpOp p≤a) (Hi : a<sealOp p) :
    acqOp p<logical p.digits a := by
  unfold cmpOp at Lo
  unfold sealOp at Hi
  unfold acqOp logical
  split
  · omega
  · split
    · omega
    · omega

theorem no_restart_prefix (d : Sheet) (C : Chart h) (x : Raw s n)
    (u v : List (Fin n)) (R : NoRestartTape d C x (u++v)) :
    NoRestartTape d C x u := by
  induction u generalizing x with
  | nil => trivial
  | cons a w IH => exact ⟨R.1,IH _ R.2⟩

/-- Non-restart tape ranks compare by logical order, not their numeric
READ/WRITE codes. The prefix and suffix are both on the original tape. -/
theorem logical_monotone_on_generation (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (A : StrongSerial d C x) (w : List (Fin n))
    (R : NoRestartTape d C x w) :
    logical (params d s).digits (readPC d C x).2≤
      logical (params d s).digits (readPC d C (rawRun x w)).2 := by
  induction w generalizing x with
  | nil => exact Nat.le_refl _
  | cons e w IH =>
    have Y := (cached_fibre d N hh Q F).closed x e X
    have B := strong_step d C N hh G F x X A digit e
    apply Nat.le_trans _ (IH _ Y B R.2)
    rcases pc_step_shape d C N hh G F digit x X A e with Z|E|⟨_,V⟩
    · exact (R.1 Z.1).elim
    · exact Nat.le_of_eq (congrArg (logical (params d s).digits) E.symm)
    · rw [preview_logical V]
      omega

/-- Once the sampled ACQ history identifies its actual consume, the
positive command-rail tape follows from the literal source poststate.
Both the full suffix and any actual prefix are available to write-bank
consumers; no assumption about grants (hence no circular lease proof). -/
theorem rail_after_history_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (P : readPC d C x=(1,acqOp (params d s)))
    (fly : List (Fin n)) (T : BeforeConsume d C (rawNext s x (door C)) fly)
    (Tag : (tok d C (rawRun (rawNext s x (door C)) fly) 0).tag=3)
    (ND : (tok d C (rawRun (rawNext s x (door C)) fly) 0).outcome≠1)
    (post : List (Fin n)) :
    let b := rawNext s (rawRun (rawNext s x (door C)) fly) (door C)
    ReportACQToWriteNoCommit.OwnerRailTape d C b post := by
  obtain ⟨Y,R,O,K,Live,_⟩ :=
    from_genuine_issue d C hh G F N x X I P digit fly T Tag ND
  let y := rawRun (rawNext s x (door C)) fly
  obtain ⟨Z,E,PC,_,_⟩ := raw_acq_consume d C hh G F N y Y R O K Live ND _ rfl digit
  exact (strong_run d C N hh G F digit _ Z (seed_after_acq d C _ E PC) post).2.2

#print axioms no_restart_prefix
#print axioms logical_monotone_on_generation
#print axioms rail_after_history_consume
#print axioms acq_history_after_receipt
#print axioms logical_after_acq_of_preseal
#print axioms acq_progress_run
#print axioms first_consume_outcome
#print axioms split_first_consume
#print axioms live_acq_pc
#print axioms denied_consume_retry
end L4.ReportAcqExtract

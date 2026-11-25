import Leader.L4.ReportACQSelectedCapture
import Leader.L4.ReportFirstCutGrant
import Leader.L4.ReportOwnerSerial

namespace L4.ReportOwnerCommandRail
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerDoorProjection
open ReportPrelaunchDoorLift ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerIssueControl ReportOwnerForwardControl ReportOwnerReverseControl
open ReportOwnerSerial ReportByteRows ReportRawProjection
open ReportGenerationAncestry ReportReaderRailNoRelease
open ReportLeaseGrants ReportLeaseOwner ReportPreCommitSelector
open ReportOwnerAcquireReturn ReportACQToWriteNoCommit

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def Aligned (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  ∀ i,i<C.L→RailAligned (readPC d C x).2 (tok d C x i)

def StrongSerial (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  Serial d C x ∧ Aligned d C x

private theorem tag0_aligned (a : Nat) (t : Tok) (T0 : t.tag=0) :
    RailAligned a t := by
  intro T _
  rcases T with T|T <;> omega

private theorem empty_aligned (d : Sheet) (C : Chart h) (x : Raw s n)
    (R : EmptyIssueShape d C x) : Aligned d C x :=
  fun i I=>tag0_aligned _ _ (R.2 i I)

private theorem root_pub (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true
      (selectBytes d (x C.root)) 0 := by
  rw [root_tok,prelaunch_root_decode]

private theorem incoming_zero (C : Chart h) (e : Fin n)
    (E : rightNeighbor e=out C 0) : e=door C := by
  unfold door
  have R : out C 0=C.root := rfl
  rw [←R,←E,RearTrace.predecessor_right]

private theorem incoming_succ (C : Chart h) (e : Fin n) (i : Nat)
    (E : rightNeighbor e=out C (i+1)) : e=out C i :=
  ShortChartOwnership.right_injective (E.trans (chart_succ C i).symm)

-- CHECK: ReportPrelaunchK1Geometry.lean:21–31,101–105;
-- rankGate is the same old cached gate (ReportByteRows:4538–4548).
private theorem chart_rank_gate (d : Sheet) (C : Chart h)
    (x : Raw s n) (i : Nat) :
    chartGate d C x i=rankGate (params d s) (h (out C i))
      (bytesL d x (out C i)) (C.route.port i) := by
  rfl

theorem nondoor_aligned (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (A : Aligned d C x)
    (e : Fin n) (D : e≠door C) :
    Aligned d C (rawNext s x e) := by
  let CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have M := CF.mask x X
  intro i I
  rw [raw_nondoor_control d C x e N M D]
  by_cases L : e=out C i
  · subst e
    rw [tok_wire,gate_frame d C hh G x _ X Y i I,
      chart_rank_gate,(raw_pair_wire d C x N M i).1,workL]
    apply rail_row_left_aligned
    · rw [←predecessor_projection]
      exact A i I
    · intro k K
      by_cases J : i+1<C.L
      · have E := Option.some.inj ((internal_dest C i J).symm.trans K)
        subst k
        rw [←successor_projection]
        exact A (i+1) J
      · rw [end_dest C i (by omega)] at K
        contradiction
  · by_cases R : rightNeighbor e=out C i
    · cases i with
      | zero => exact (D (incoming_zero C e R)).elim
      | succ j =>
        have E := incoming_succ C e j R
        subst e
        have Gate : chartGate d C x (j+1)=rankGate (params d s)
            (h (rightNeighbor (out C j))) (bytesR d x (out C j))
            (C.route.port (j+1)) := by
          rw [chart_rank_gate]
          simp only [bytesL,bytesR,chart_succ]
        rw [tok_wire,gate_frame d C hh G x _ X Y (j+1) I,
          Gate,(raw_pair_wire d C x N M j).2,workR]
        exact rail_row_right_aligned _ _ _ _ _ _ _
          (internal_dest C j I) _
          (by rw [←predecessor_projection]; exact A j (by omega))
          (by rw [←successor_projection]; exact A (j+1) I)
    · have W : wire d C (rawNext s x e) i=wire d C x i := by
        unfold wire
        rw [raw_spectator x e _ (Ne.symm L) (Ne.symm R)]
      rw [decoded_frame d C hh G x _ X Y i I W]
      exact A i I

private theorem door_wait_aligned (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (A : Aligned d C x)
    (P : LegalWait d C x) (T0 : (tok d C x 0).tag=1 ∨ (tok d C x 0).tag=2) :
    Aligned d C (rawNext s x (door C)) := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  let y := rawNext s x (door C)
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x (door C) X
  have T1 : t.tag=1 ∨ t.tag=2 := by
    rw [root_pub d C x] at T0
    exact T0
  have W := raw_door_final d C x N (CF.mask x X)
  have PC : readPC d C y=readPC d C x :=
    W.1.trans (prelaunch_hold_controls p v t P.1 P.2 T1)
  have WR := W.2
  rw [prelaunch_wait_hold p v t P.1 P.2 T1] at WR
  intro i I
  rw [PC]
  by_cases Z : i=0
  · subst i
    rw [root_tok d C y,WR]
    exact rail_door_norm_aligned p v _
      (by rw [←root_pub d C x]; exact A 0 I)
  · rw [decoded_frame d C hh G x y X Y i I
      (raw_door_frame d C x i (by omega) I)]
    exact A i I

theorem door_aligned (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (A : StrongSerial d C x)
    (digit : 0<(params d s).digits) :
    Aligned d C (rawNext s x (door C)) := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  let y := rawNext s x (door C)
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x (door C) X
  rcases A.1 with I|⟨k,I⟩|⟨k,I⟩
  · have W := raw_door_final d C x N (CF.mask x X)
    have PC : readPC d C y=
        (sourcePhase p ((liftSourcePatch p (source p v t).1).apply v),
        sourceOpcode p ((liftSourcePatch p (source p v t).1).apply v)) := W.1
    intro i J
    by_cases Z : i=0
    · subst i
      rw [root_tok d C y,W.2,PC]
      exact rail_door_issue_aligned p v t I.2.1 I.1
    · apply tag0_aligned
      rw [decoded_frame d C hh G x y X Y i J
        (raw_door_frame d C x i (by omega) J)]
      exact I.2.2 i J
  · apply door_wait_aligned d C N hh G F x X A.2 I.1
    rw [I.2.2 0 C.positive]
    by_cases K : k=0
    · subst k
      exact .inr rfl
    · exact .inl (by simp [frontTag,show 0<k by omega])
  · by_cases K : k=0
    · subst k
      exact empty_aligned d C y (door_consumes_root d C hh G F N x X I digit)
    · apply door_wait_aligned d C N hh G F x X A.2 I.1
      rw [I.2.2 0 C.positive]
      exact .inl (by simp [backTag,show 0<k by omega])

theorem strong_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (A : StrongSerial d C x)
    (digit : 0<(params d s).digits) (e : Fin n) :
    StrongSerial d C (rawNext s x e) := by
  refine ⟨ReportOwnerSerial.all_mark d C N hh G F x X A.1 digit e,?_⟩
  by_cases D : e=door C
  · subst e
    exact door_aligned d C N hh G F x X A digit
  · exact nondoor_aligned d C N hh G F x X A.2 e D

theorem seed_receipt (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (w : List (Fin n))
    (R : Generated d C x w .done) :
    StrongSerial d C (rawRun x w) := by
  have S := seed_at_genuine_receipt d C N hh F x X w R
  obtain ⟨_,A⟩ := cached_genuine_full_parked d C N hh F x X w R
  refine ⟨S,?_⟩
  intro i I
  apply tag0_aligned
  rw [tok_wire,A.1.2.1 i I]
  rw [show canon (params d s) .empty=resetTokenWire (params d s) MISByteCodec.E
    from rfl,drain_decode_E]
  rfl

theorem seed_after_acq (d : Sheet) (C : Chart h) (x : Raw s n)
    (E : EmptyIssueShape d C x)
    (PC : readPC d C x=(1,cmpOp (params d s))) :
    StrongSerial d C x := by
  have B : (readPC d C x).2≤commitOp (params d s) := by
    rw [PC]
    unfold cmpOp commitOp
    omega
  exact ⟨.inl ⟨B,E⟩,empty_aligned d C x E⟩

-- These are the exact same decoded E/T facts used in
-- ReportACQSelectedCapture.lean:14–28, repeated because private.
private theorem tok_empty (d : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (A : (tok d C x i).tag=0) : tok d C x i=MISByteCodec.E := by
  rw [tok_wire] at A ⊢
  rw [rank_decode_tag] at A
  conv => lhs; unfold decode
  dsimp only
  simp only [A,beq_self_eq_true,if_true]

private theorem tok_trail (d : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (A : (tok d C x i).tag=1) : tok d C x i=MISByteCodec.T := by
  rw [tok_wire] at A ⊢
  rw [rank_decode_tag] at A
  conv => lhs; unfold decode
  dsimp only
  simp only [A,show ((1:Nat)==0)=false by decide,
    Bool.false_eq_true,if_false,beq_self_eq_true,if_true]

/-- This is the exact railState, not a new look-alike consumer.
The unused ghost fields are arbitrary: railState reads none of them.
The original generation's actual grants are treated separately. -/
theorem rail_of_strong (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : StrongSerial d C x) :
    ∃ g,railState d C x g ∧ g.op=(readPC d C x).2 := by
  let a := (readPC d C x).2
  rcases A.1 with I|⟨k,I⟩|⟨k,I⟩
  · let g : GenerationTag := ⟨0,0,a,.issue,false,false,fun _=>false,none⟩
    refine ⟨g,?_,rfl⟩
    change readPC d C x=(1,a) ∧ ∀ i,i<C.L→tok d C x i=MISByteCodec.E
    exact ⟨Prod.ext I.2.1 rfl,fun i J=>tok_empty d C x i (I.2.2 i J)⟩
  · let t := tok d C x k
    let g : GenerationTag := ⟨0,0,a,.forward k t,false,false,fun _=>false,none⟩
    refine ⟨g,?_,rfl⟩
    have Tag : t.tag=2 := by
      simpa only [frontTag,Nat.lt_irrefl,if_false,if_true] using I.2.2 k I.2.1
    change readPC d C x=(2,a) ∧ k<C.L ∧ t.tag=2 ∧
      (t.fault=false→t.opcode=a) ∧
      ∀ i,i<C.L→tok d C x i=
        if i<k then MISByteCodec.T else if i=k then t else MISByteCodec.E
    refine ⟨Prod.ext I.1.1 rfl,I.2.1,Tag,A.2 k I.2.1 (.inl Tag),?_⟩
    intro i J
    have V := I.2.2 i J
    by_cases K : i<k
    · rw [if_pos K]
      exact tok_trail d C x i (by simpa only [frontTag,K,if_true] using V)
    · rw [if_neg K]
      by_cases E : i=k
      · subst i; rw [if_pos rfl]
      · rw [if_neg E]
        exact tok_empty d C x i (by simpa only [frontTag,K,E,if_false] using V)
  · let t := tok d C x k
    let g : GenerationTag := ⟨0,0,a,.reverse k t,false,false,fun _=>false,none⟩
    refine ⟨g,?_,rfl⟩
    have Tag : t.tag=3 := by
      simpa only [backTag,Nat.lt_irrefl,if_false,if_true] using I.2.2 k I.2.1
    change readPC d C x=(2,a) ∧ k<C.L ∧ t.tag=3 ∧
      (t.fault=false→t.opcode=a) ∧
      ∀ i,i<C.L→tok d C x i=
        if i<k then MISByteCodec.T else if i=k then t else MISByteCodec.E
    refine ⟨Prod.ext I.1.1 rfl,I.2.1,Tag,A.2 k I.2.1 (.inr Tag),?_⟩
    intro i J
    have V := I.2.2 i J
    by_cases K : i<k
    · rw [if_pos K]
      exact tok_trail d C x i (by simpa only [backTag,K,if_true] using V)
    · rw [if_neg K]
      by_cases E : i=k
      · subst i; rw [if_pos rfl]
      · rw [if_neg E]
        exact tok_empty d C x i (by simpa only [backTag,K,E,if_false] using V)

theorem strong_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (A : StrongSerial d C x) (w : List (Fin n)) :
    Cached d hh Q (rawRun x w) ∧ StrongSerial d C (rawRun x w) ∧
      OwnerRailTape d C x w := by
  induction w generalizing x with
  | nil => exact ⟨X,A,trivial⟩
  | cons e w IH =>
    have Y := (cached_fibre d N hh Q F).closed x e X
    have B := strong_step d C N hh G F x X A digit e
    obtain ⟨Y',B',R⟩ := IH (rawNext s x e) Y B
    obtain ⟨g,R0,_⟩ := rail_of_strong d C x A
    exact ⟨Y',B',⟨⟨g,R0⟩,R⟩⟩

theorem held_incidence_step (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (e : Fin n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (A : StrongSerial d C x) (P : (readPC d C x).2≠0)
    (k : Nat) (K : k<C.L) (H : h (out C k)=true)
    (Compat : Compatible (rawGrant d x (out C k)))
    (Held : rawGrant d x (out C k) (C.route.port k)=true) :
    rawGrant d (rawNext s x e) (out C k) (C.route.port k)=true := by
  obtain ⟨g,R,_⟩ := rail_of_strong d C x A
  have NR := positive_rail_no_release d C x g R P k K H
  have Canon : (oldIncidence d x (out C k)).canonical (C.route.port k)=true :=
    (canonical_eq (oldIncidence d x (out C k)) Compat _).trans Held
  apply (held_grant_survives_iff d x e (out C k) (C.route.port k)
    N ((mask _).trans H) Held).mpr
  unfold grantSurvives
  split
  · exact ⟨Canon,NR⟩
  · split
    · exact Canon
    · trivial

-- At the first actual switch this command is COMMIT. All other
-- owners' operations, including both orientations of neighbours,
-- cannot change the centre selector of this chart.
theorem switch_implies_commit (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (x : Raw s n) (e : Fin n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (A : StrongSerial d (charter G r) x)
    (S : rawSelector d (rawNext s x e) (centre (charter G r))≠
      rawSelector d x (centre (charter G r))) :
    (readPC d (charter G r) x).2=commitOp (params d s) := by
  obtain ⟨g,R,O⟩ := rail_of_strong d (charter G r) x A
  by_cases H : (readPC d (charter G r) x).2=commitOp (params d s)
  · exact H
  · exact (S (selector_frame_noncommit d G r x g R
      (fun E=>H (O.symm.trans E)) e N mask)).elim

-- The PreviewNextOp constructors are the same indexed six cases
-- as NextOp. CHECK: ReportByteRows:5750–5757, ReportPrelaunchClock:53–78.
theorem preview_next {m a b : Nat} (P : PreviewNextOp m a b) :
    NextOp m a b := by
  cases P with
  | linear H => exact .linear H
  | cmpLast H => exact .cmpLast H
  | readWrite H => exact .readWrite H
  | writeRead H => exact .writeRead H
  | writeSeal H => exact .writeSeal H
  | sealCommit => exact .sealCommit

theorem preview_target_positive {m a b : Nat}
    (P : PreviewNextOp m a b) : b≠0 := by
  cases P <;> omega

theorem preview_logical {m a b : Nat} (P : PreviewNextOp m a b) :
    ReportPrelaunchRank.logical m b=ReportPrelaunchRank.logical m a+1 :=
  nextOp_logical (preview_next P)

/-- All source marks on a positive rail: retry at the clean zero
door, hold the opcode, or advance its true logical instruction.
The retry is a distinct transition, not a permitted rewind of
the positive command rail. -/
theorem positive_pc_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (A : StrongSerial d C x)
    (e : Fin n) (_Pos : (readPC d C x).2≠0) :
    let y := rawNext s x e
    Retry0 d C y ∨
      (readPC d C y).2=(readPC d C x).2 ∨
      PreviewNextOp (params d s).digits (readPC d C x).2 (readPC d C y).2 := by
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
          rw [E]
          exact B
      · apply Or.inr; apply Or.inl; apply Hold I.1
        rw [I.2.2 0 C.positive]
        exact .inl (by simp [backTag,show 0<k by omega])
  · exact .inr (.inl (congrArg Prod.snd (raw_nondoor_control d C x e N M D)))

/-- The first zero-PC successor is necessarily a genuine clean
source retry, not a foreign command, partial overwrite, or rewind. -/
theorem zero_is_retry (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (A : StrongSerial d C x) (e : Fin n)
    (Pos : (readPC d C x).2≠0)
    (Z : (readPC d C (rawNext s x e)).2=0) :
    e=door C ∧ Retry0 d C (rawNext s x e) := by
  have M := (cached_fibre d N hh Q F).mask x X
  have D : e=door C := by
    by_cases D : e=door C
    · exact D
    · exact (Pos ((congrArg Prod.snd (raw_nondoor_control d C x e N M D)).symm.trans Z)).elim
  refine ⟨D,?_⟩
  rcases positive_pc_step d C N hh G F digit x X A e Pos with R|E|E
  · exact R
  · exact (Pos (E.symm.trans Z)).elim
  · exact (preview_target_positive E Z).elim

/-- For this stopped lease, a root RESET departure is the first
possible actual release. It is harmless to allow inherited bytes
in FullActive; the separate StrongSerial invariant is already
closed from the clean retry. -/
def AbortPending (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  Retry0 d C x ∨ FullActive d C x (.fwd 0)

private theorem pending_pc_zero (d : Sheet) (C : Chart h)
    (x : Raw s n) (A : AbortPending d C x) :
    (readPC d C x).2=0 := by
  rcases A with I|R
  · exact I.1
  · have PC := pc_fields d C x .wait0 (by decide) R.1.1.2.1
    exact congrArg Prod.snd PC

private theorem issue0_view (d : Sheet) (C : Chart h)
    (x : Raw s n) (I : Retry0 d C x) :
    ownerPC d C x=.issue0 := by
  have PC : readPC d C x=(1,0) := Prod.ext I.2.1 I.1
  change pcView (readPC d C x)=.issue0
  rw [PC]
  decide

-- CHECK: ReportOwnerResetDrain.lean:529–536,1102–1128.
-- The old .fwd 0 rail contains an actual canonical F0 in root K0.
theorem abort_root_departure (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (M : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (R : FullActive d C x (.fwd 0)) :
    grantBit d (rawNext s x (out C 0)) (out C 0) (C.route.port 0)=false := by
  have T := tok_of_slot d C x 0 .forward0 (by decide) R.1.1.2.2.1
  have H : h (out C 0)=true := C.rootHeader
  have U : publicationToken (params d s) true
      (selectBytes d (x (out C 0))) (C.route.port 0)=reset0Forward := by
    rw [←H]
    exact (predecessor_projection d C x 0).symm.trans T
  exact ReportLeaseStep.departing_reset_drops_grant d x (out C 0) N
    (C.route.port 0) M H U

theorem pending_step_while_held (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (A : AbortPending d C x)
    (e : Fin n)
    (Held : grantBit d (rawNext s x e) (out C 0) (C.route.port 0)=true) :
    AbortPending d C (rawNext s x e) := by
  let CF := cached_fibre d N hh Q F
  rcases A with I|R
  · by_cases D : e=door C
    · subst e
      exact .inr (full_launch d C x N (CF.mask x X) (issue0_view d C x I))
    · have L : LegalIssue d C x := ⟨by rw [I.1]; exact Nat.zero_le _,I.2⟩
      obtain ⟨B,PC⟩ := nondoor_preserves d C hh G F N x X L e D
      exact .inl ⟨(congrArg Prod.snd PC).trans I.1,B.2⟩
  · by_cases E : e=out C 0
    · subst e
      have Drop := abort_root_departure d C N x (CF.mask x X) R
      rw [Drop] at Held
      contradiction
    · have V := full_active_step d C CF x X N e (.fwd 0) (by decide) R
      have S : nextStage C e (.fwd 0)=.fwd 0 := by
        -- CHECK: ShortResetCycle.lean:147–152. out C i is nextAt C.root i.
        change (if e=out C 0 then
          (if 0+1<C.L then Stage.fwd (0+1) else Stage.rev 0)
          else Stage.fwd 0)=Stage.fwd 0
        rw [if_neg E]
      rw [S] at V
      exact .inr V

/-- A chronological assertion on a real raw tape, not just matching
endpoint bytes. Includes both endpoints and every intervening state.
The root incidence is the one of the same chart and same generation. -/
def RootHeldThrough (d : Sheet) (C : Chart h) :
    Raw s n→List (Fin n)→Prop
  | x,[]=>grantBit d x (out C 0) (C.route.port 0)=true
  | x,e::w=>grantBit d x (out C 0) (C.route.port 0)=true ∧
      RootHeldThrough d C (rawNext s x e) w

private theorem root_held_head (d : Sheet) (C : Chart h)
    (x : Raw s n) (w : List (Fin n)) (H : RootHeldThrough d C x w) :
    grantBit d x (out C 0) (C.route.port 0)=true := by
  cases w with
  | nil => exact H
  | cons e w => exact H.1

theorem pending_run_while_held (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (A : AbortPending d C x)
    (w : List (Fin n)) (H : RootHeldThrough d C x w) :
    (readPC d C (rawRun x w)).2=0 := by
  induction w generalizing x with
  | nil => exact pending_pc_zero d C x A
  | cons e w IH =>
    have Y := (cached_fibre d N hh Q F).closed x e X
    have B := pending_step_while_held d C N hh G F x X A e
      (root_held_head d C _ w H.2)
    exact IH (rawNext s x e) Y B H.2

/-- The exact missing no-restart hypothesis for a later positive
endpoint of the same unreleased generation. The proof does not
assume any intermediate opcode is positive. A first zero would
enter AbortPending, forcing the final opcode to be zero, or a
root RESET departure which contradicts the real grant history. -/
theorem no_restart_of_held_endpoint (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (A : StrongSerial d C x)
    (Pos : (readPC d C x).2≠0) (w : List (Fin n))
    (H : RootHeldThrough d C x w)
    (End : (readPC d C (rawRun x w)).2≠0) :
    NoRestartTape d C x w := by
  induction w generalizing x with
  | nil => trivial
  | cons e w IH =>
    let y := rawNext s x e
    have Y := (cached_fibre d N hh Q F).closed x e X
    have B := strong_step d C N hh G F x X A digit e
    have NZ : (readPC d C y).2≠0 := by
      intro Z
      have R := (zero_is_retry d C N hh G F digit x X A e Pos Z).2
      exact End (pending_run_while_held d C N hh G F y Y (.inl R) w H.2)
    exact ⟨NZ,IH y Y B NZ H.2 End⟩

/-- Combined supplier in the exact two predicates consumed by
ReportACQSelectedCapture.authentic_capture_is_current. -/
theorem postacq_suffix (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (E : EmptyIssueShape d C x)
    (PC : readPC d C x=(1,cmpOp (params d s)))
    (w : List (Fin n)) (H : RootHeldThrough d C x w)
    (End : (readPC d C (rawRun x w)).2≠0) :
    NoRestartTape d C x w ∧ OwnerRailTape d C x w := by
  have A := seed_after_acq d C x E PC
  have Pos : (readPC d C x).2≠0 := by
    rw [PC]
    unfold cmpOp
    omega
  exact ⟨no_restart_of_held_endpoint d C N hh G F digit x X A Pos w H End,
    (strong_run d C N hh G F digit x X A w).2.2⟩

/-- Actual ACQ consume, not an externally populated source file. -/
theorem postacq_suffix_from_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (R : ReverseWait d C x 0)
    (O : (readPC d C x).2=acqOp (params d s))
    (K : (tok d C x 0).opcode=acqOp (params d s))
    (Live : (tok d C x 0).fault=false)
    (ND : (tok d C x 0).outcome≠1)
    (b : Nat) (B : acqReplyCentre (tok d C x 0)=b)
    (w : List (Fin n))
    (H : RootHeldThrough d C (rawNext s x (door C)) w)
    (End : (readPC d C (rawRun (rawNext s x (door C)) w)).2≠0) :
    NoRestartTape d C (rawNext s x (door C)) w ∧
      OwnerRailTape d C (rawNext s x (door C)) w := by
  obtain ⟨Y,E,PC,_,_⟩ :=
    raw_acq_consume d C hh G F N x X R O K Live ND b B digit
  exact postacq_suffix d C N hh G F digit _ Y E PC w H End

/-- Authenticate the actual captured bit at the current pre-SEAL
endpoint without assuming either NoRestartTape or OwnerRailTape.
The root grant must have been continuously held on this one suffix;
the command rail makes a real RESET release unavoidable after abort. -/
theorem authentic_capture_current_while_held (d : Sheet) (G : GapInput h) (r : Owner h)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d (charter G r) x)
    (P : readPC d (charter G r) x=(1,acqOp (params d s))) (digit : 0<(params d s).digits)
    (w : List (Fin n))
    (T : ReportOwnerAcquireProvenance.BeforeConsume d (charter G r)
      (rawNext s x (door (charter G r))) w)
    (Tag : (tok d (charter G r) (rawRun (rawNext s x (door (charter G r))) w) 0).tag=3)
    (ND : (tok d (charter G r) (rawRun (rawNext s x (door (charter G r))) w) 0).outcome≠1)
    (v : List (Fin n))
    (Held : RootHeldThrough d (charter G r)
      (rawNext s (rawRun (rawNext s x (door (charter G r))) w) (door (charter G r))) v)
    (Lo : cmpOp (params d s)≤(readPC d (charter G r)
      (rawRun (rawNext s (rawRun (rawNext s x (door (charter G r))) w)
        (door (charter G r))) v)).2)
    (Hi : (readPC d (charter G r)
      (rawRun (rawNext s (rawRun (rawNext s x (door (charter G r))) w)
        (door (charter G r))) v)).2<sealOp (params d s)) :
    let C := charter G r
    let z := rawRun (rawNext s (rawRun (rawNext s x (door C)) w) (door C)) v
    ReportWriterPayload.capturedSelector (params d s) (selectBytes d (z C.root))=
      rawSelector d z (centre C) := by
  dsimp only
  let C := charter G r
  let y := rawRun (rawNext s x (door C)) w
  obtain ⟨Y,R,O,K,Live,u,_,_,_,_,_,_,B⟩ :=
    ReportOwnerAcquireProvenance.from_genuine_issue d C hh G F N x X I P digit w T Tag ND
  have End : (readPC d C (rawRun (rawNext s y (door C)) v)).2≠0 := by
    intro E
    rw [E] at Lo
    unfold cmpOp at Lo
    omega
  obtain ⟨NR,Rail⟩ := postacq_suffix_from_consume d C N hh G F digit y Y R O K Live ND
    (ReportOwnerAcquireProvenance.CentreSample d C (rawRun (rawNext s x (door C)) u))
    B v Held End
  exact ReportACQSelectedCapture.authentic_capture_is_current d G r hh F N x X I P
    digit w T Tag ND v NR Rail Hi

end L4.ReportOwnerCommandRail
namespace L4.ReportOwnerCommandRail
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerDoorProjection
open ReportPrelaunchDoorLift ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerIssueControl ReportOwnerForwardControl ReportOwnerReverseControl
open ReportOwnerSerial ReportByteRows ReportRawProjection
open ReportGenerationAncestry ReportReaderRailNoRelease
open ReportLeaseGrants ReportLeaseOwner ReportPreCommitSelector
open ReportOwnerAcquireReturn ReportACQToWriteNoCommit

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem pc_step_with_phase (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (A : StrongSerial d C x)
    (e : Fin n) :
    let y := rawNext s x e
    Retry0 d C y ∨
      (readPC d C y).2=(readPC d C x).2 ∨
      ((readPC d C y).1=1 ∧
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
          refine ⟨congrArg Prod.fst (W.trans R),?_⟩
          rw [E]
          exact B
      · apply Or.inr; apply Or.inl; apply Hold I.1
        rw [I.2.2 0 C.positive]
        exact .inl (by simp [backTag,show 0<k by omega])
  · exact .inr (.inl (congrArg Prod.snd (raw_nondoor_control d C x e N M D)))

end L4.ReportOwnerCommandRail

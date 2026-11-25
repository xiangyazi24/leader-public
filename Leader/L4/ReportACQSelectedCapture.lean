import Leader.L4.ReportOwnerAcquireProvenance
import Leader.L4.ReportACQToWriteNoCommit

namespace L4.ReportACQSelectedCapture
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportByteRows ReportRawProjection
open ReportOwnerAcquireProvenance ReportOwnerAcquireReturn
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportGenerationAncestry ReportLeaseOwner ReportPreCommitSelector

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

private theorem tok_empty (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat)
    (A : (tok d C x k).tag=0) : tok d C x k=MISByteCodec.E := by
  rw [tok_wire] at A ⊢
  rw [rank_decode_tag] at A
  conv => lhs; unfold decode
  dsimp only
  simp only [A,beq_self_eq_true,if_true]

private theorem tok_trail (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat)
    (A : (tok d C x k).tag=1) : tok d C x k=MISByteCodec.T := by
  rw [tok_wire] at A ⊢
  rw [rank_decode_tag] at A
  conv => lhs; unfold decode
  dsimp only
  simp only [A,show ((1:Nat)==0)=false by decide,Bool.false_eq_true,if_false,beq_self_eq_true,if_true]

theorem forward_rail (d : Sheet) (C : Chart h) (x : Raw s n)
    (k q : Nat) (R : FState d C x k q) :
    ∃ g,railState d C x g ∧ g.op=acqOp (params d s) := by
  let t := acqFlightF (params d s) q
  let g : GenerationTag := ⟨0,0,acqOp (params d s),.forward k t,
    false,false,fun _=>false,none⟩
  refine ⟨g,?_,rfl⟩
  change readPC d C x=(2,acqOp (params d s)) ∧ k<C.L ∧ t.tag=2 ∧
    (t.fault=false→t.opcode=acqOp (params d s)) ∧
    ∀ i,i<C.L→tok d C x i=
      if i<k then MISByteCodec.T else if i=k then t else MISByteCodec.E
  refine ⟨R.pc,R.shape.2.1,rfl,fun _=>rfl,?_⟩
  intro i I
  have L := R.shape.2.2 i I
  by_cases J : i<k
  · rw [if_pos J]
    apply tok_trail
    simpa only [frontTag,J,if_true] using L
  · rw [if_neg J]
    by_cases E : i=k
    · subst i
      rw [if_pos rfl]
      exact R.packet
    · rw [if_neg E]
      apply tok_empty
      simpa only [frontTag,J,E,if_false] using L

theorem reverse_rail (d : Sheet) (C : Chart h) (x : Raw s n)
    (k q : Nat) (R : DState d C x k q) :
    ∃ g,railState d C x g ∧ g.op=acqOp (params d s) := by
  let t := acqFlightD (params d s) q
  let g : GenerationTag := ⟨0,0,acqOp (params d s),.reverse k t,
    false,false,fun _=>false,none⟩
  refine ⟨g,?_,rfl⟩
  change readPC d C x=(2,acqOp (params d s)) ∧ k<C.L ∧ t.tag=3 ∧
    (t.fault=false→t.opcode=acqOp (params d s)) ∧
    ∀ i,i<C.L→tok d C x i=
      if i<k then MISByteCodec.T else if i=k then t else MISByteCodec.E
  refine ⟨R.pc,R.shape.2.1,acqFlightD_tag _ _,fun _=>acqFlightD_op _ _,?_⟩
  intro i I
  have L := R.shape.2.2 i I
  by_cases J : i<k
  · rw [if_pos J]
    apply tok_trail
    simpa only [backTag,J,if_true] using L
  · rw [if_neg J]
    by_cases E : i=k
    · subst i
      rw [if_pos rfl]
      exact R.packet
    · rw [if_neg E]
      apply tok_empty
      simpa only [backTag,J,E,if_false] using L

theorem flight_rail (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (A : FlightAt d C x0 w) :
    ∃ g,railState d C (rawRun x0 w) g ∧ g.op=acqOp (params d s) := by
  rcases A with ⟨k,q,R,_⟩|⟨k,q,R,_⟩
  · exact forward_rail d C _ k q R
  · exact reverse_rail d C _ k q R

/-- While the real ACQ packet is in flight the centre selector cannot
change, even on its actual winning departure or the later door
consume. The only possible changer belongs to this same owner. -/
theorem acq_mark_frames_centre (d : Sheet) (G : GapInput h)
    (r : Owner h) (x0 : Raw s n) (w : List (Fin n))
    (A : FlightAt d (charter G r) x0 w) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (rawRun x0 w i))=h i) :
    CentreSample d (charter G r) (rawNext s (rawRun x0 w) e)=
      CentreSample d (charter G r) (rawRun x0 w) := by
  obtain ⟨g,R,O⟩ := flight_rail d (charter G r) x0 w A
  have NC : g.op≠commitOp (params d s) := by
    rw [O]
    unfold acqOp commitOp
    omega
  exact selector_frame_noncommit d G r (rawRun x0 w) g R NC e N mask

theorem acq_prefix_centres_stable (d : Sheet) (G : GapInput h) (r : Owner h)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0) (A : FState d (charter G r) x0 0 64)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d (charter G r) x0 w) :
    CentreSample d (charter G r) (rawRun x0 w)=CentreSample d (charter G r) x0 := by
  induction T with
  | nil => rfl
  | @snoc ws e prev nc IH =>
    obtain ⟨Y,B⟩ := flight_run d (charter G r) hh G F N x0 X A digit ws prev
    rw [ShortOwnerEpochJS.raw_snoc]
    exact (acq_mark_frames_centre d G r x0 ws B e N
      ((cached_fibre d N hh Q F).mask _ Y)).trans IH

theorem before_consume_prefix (d : Sheet) (C : Chart h) (x0 : Raw s n)
    {u w : List (Fin n)} (T : BeforeConsume d C x0 w) (P : u <+: w) :
    BeforeConsume d C x0 u := by
  induction T generalizing u with
  | nil =>
    have E := P.eq_of_length_le (Nat.zero_le _)
    subst u
    exact .nil
  | @snoc w e prev nc IH =>
    by_cases L : u.length≤w.length
    · exact IH (List.prefix_of_prefix_length_le P (List.prefix_append w [e]) L)
    · have E := P.eq_of_length_le (by simp; omega)
      subst u
      exact .snoc e prev nc

/-- The authenticated bit in the actual source file is still the
live centre selector at a later pre-SEAL endpoint on the same
generation. The suffix rail and no-restart inputs are observed on
each original state, not inferred merely from the terminal PC. -/
theorem authentic_capture_is_current (d : Sheet) (G : GapInput h) (r : Owner h)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (I : ReportOwnerIssueControl.LegalIssue d (charter G r) x)
    (P : readPC d (charter G r) x=(1,acqOp (params d s))) (digit : 0<(params d s).digits)
    (w : List (Fin n))
    (T : BeforeConsume d (charter G r) (rawNext s x (door (charter G r))) w)
    (Tag : (tok d (charter G r) (rawRun (rawNext s x (door (charter G r))) w) 0).tag=3)
    (ND : (tok d (charter G r) (rawRun (rawNext s x (door (charter G r))) w) 0).outcome≠1)
    (v : List (Fin n))
    (NR : NoRestartTape d (charter G r)
      (rawNext s (rawRun (rawNext s x (door (charter G r))) w) (door (charter G r))) v)
    (Rail : ReportACQToWriteNoCommit.OwnerRailTape d (charter G r)
      (rawNext s (rawRun (rawNext s x (door (charter G r))) w) (door (charter G r))) v)
    (End : (readPC d (charter G r)
      (rawRun (rawNext s (rawRun (rawNext s x (door (charter G r))) w)
        (door (charter G r))) v)).2<sealOp (params d s)) :
    let C := charter G r
    let z := rawRun (rawNext s (rawRun (rawNext s x (door C)) w) (door C)) v
    ReportWriterPayload.capturedSelector (params d s) (selectBytes d (z C.root))=
      rawSelector d z (centre C) := by
  dsimp only
  let C := charter G r
  let x0 := rawNext s x (door C)
  let y := rawRun x0 w
  let after := rawNext s y (door C)
  let z := rawRun after v
  obtain ⟨X0,A⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N x X I P
  obtain ⟨Y,B⟩ := flight_run d C hh G F N x0 X0 A digit w T
  obtain ⟨_,R,O,K,Live,u,v',q,Split,_,_,_,Sample⟩ :=
    successful_root d C hh G F N x0 X0 A digit w T Tag ND
  have Before : BeforeConsume d C x0 u :=
    before_consume_prefix d C x0 T (by rw [Split]; exact List.prefix_append _ _)
  have AtWin := acq_prefix_centres_stable d G r hh F N x0 X0 A digit u Before
  have AtReturn := acq_prefix_centres_stable d G r hh F N x0 X0 A digit w T
  have AtConsume := acq_mark_frames_centre d G r x0 w B (door C) N
    ((cached_fibre d N hh Q F).mask y Y)
  have Consume := raw_acq_consume d C hh G F N y Y R O K Live ND
    (CentreSample d C (rawRun x0 u)) Sample digit
  have After : PostAcqPC (params d s) (readPC d C after) := by
    rw [Consume.2.2.1]
    exact ⟨.inl rfl,Nat.le_refl _,by unfold cmpOp commitOp; omega⟩
  have Retain := ReportACQToWriteNoCommit.selector_before_write d G r hh F N digit after v
    Consume.1 After NR Rail End
  have Installed := acq_consume_then_run d C hh G F N y Y R O K Live ND
    (CentreSample d C (rawRun x0 u)) Sample digit v NR
  change ReportWriterPayload.capturedSelector (params d s) (selectBytes d (z C.root))=
    CentreSample d C z
  exact Installed.2.2.2.trans <|
    AtWin.trans (AtReturn.symm.trans (AtConsume.symm.trans Retain.symm))

end L4.ReportACQSelectedCapture

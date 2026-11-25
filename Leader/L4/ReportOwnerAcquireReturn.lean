import Leader.L4.ReportLeaseStep
import Leader.L4.ReportOwnerReverseControl
import Leader.L4.ReportWriterPayload

namespace L4.ReportOwnerAcquireReturn
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportOwnerProvenanceTransport ReportOwnerReverseShape
open ReportOwnerReverseControl ReportPrelaunchClock ReportPrelaunchDoorLift
open ReportOwnerDoorProjection ReportByteRows ReportRawProjection

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

variable {s n : Nat} {h : Fin n→Bool}

def ownerCaptureIndex (d : Sheet) (C : Chart h) (x : Raw s n) : Nat :=
  acqCaptureIndex (params d s) (selectBytes d (x C.root))

theorem captured_selector_index (p : Params) (x : BitVec p.w) :
    ReportWriterPayload.capturedSelector p x=acqCaptureIndex p x/2%2 := rfl

/-- Both projections are the actual joined writes. No synthetic tape. -/
theorem raw_capture_pair (d : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i) :
    let p := params d s
    let u := selectBytes d (x e)
    let v := selectBytes d (x (rightNeighbor e))
    let q := row p (h e,h (rightNeighbor e)) (u,v)
    acqCaptureIndex p (selectBytes d (rawNext s x e e))=
      acqCaptureIndex p (q.1.apply u) ∧
    acqCaptureIndex p (selectBytes d (rawNext s x e (rightNeighbor e)))=
      acqCaptureIndex p (q.2.apply v) := by
  dsimp only
  exact ⟨acq_index_low_congr _ _ _ (fun i I =>
      (ReportLeaseStep.raw_low_pair d x e N mask i I).1),
    acq_index_low_congr _ _ _ (fun i I =>
      (ReportLeaseStep.raw_low_pair d x e N mask i I).2)⟩

/-- The initiator/remote orientation of a mark. Includes the last
    reverse link into K0: there is still no source consume. -/
theorem raw_nondoor_capture (d : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (D : e≠door C) :
    ownerCaptureIndex d C (rawNext s x e)=ownerCaptureIndex d C x := by
  by_cases E : e=C.root
  · subst e
    have H := (raw_capture_pair d x C.root N mask).1
    try dsimp only at H
    rw [C.rootHeader] at H
    exact H.trans (acq_row_left_index (params d s)
      (h (rightNeighbor C.root)) _ _)
  · have R : C.root≠rightNeighbor e := by
      intro K
      apply D
      unfold door
      rw [K,RearTrace.predecessor_right]
    unfold ownerCaptureIndex
    rw [raw_spectator x e C.root (Ne.symm E) R]

/-- Use the checked source-file frame, not a decoded tag frame. -/
theorem raw_capture_before_ack (d : Sheet) (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (P : sourcePhase (params d s) (selectBytes d (x C.root))=2)
    (O : sourceOpcode (params d s) (selectBytes d (x C.root))≤
      commitOp (params d s))
    (T : (publicationToken (params d s) true (selectBytes d (x C.root)) 0).tag=1 ∨
         (publicationToken (params d s) true (selectBytes d (x C.root)) 0).tag=2) :
    ownerCaptureIndex d C (rawNext s x e)=ownerCaptureIndex d C x :=
  acq_index_of_file _ _ _ (ReportLeaseStep.file_before_ack d C x e N mask P O T)

private theorem acq_root_tok (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true
      (selectBytes d (x C.root)) 0 := by
  rw [root_tok,prelaunch_root_decode]

/-- Last reverse hop if a caller supplies the actual successful D
    at chart occurrence 1. Its canonical payload q is not derived
    here. This is separate from the next source-door consume. -/
theorem raw_acq_last_relay (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (R : ReverseWait d C x 1)
    (q : Nat) (B : q<64)
    (D : tok d C x 1=({tag:=3,opcode:=acqOp (params d s),payload:=q}:Tok)) :
    let y := rawNext s x (out C 0)
    Cached d hh Q y ∧ ReverseWait d C y 0 ∧
    tok d C y 0=({tag:=3,opcode:=acqOp (params d s),payload:=q}:Tok) ∧
    ownerCaptureIndex d C y=ownerCaptureIndex d C x := by
  dsimp only
  let p := params d s
  let e := out C 0
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y : Cached d hh Q y := CF.closed x e X
  have I : 1<C.L := R.2.1
  have ND : e≠door C := by
    exact Ne.symm (ReportChartPartition.door_not_outgoing C 0 C.positive)
  have LT : (tok d C x 0).tag≠2 := by
    rw [R.2.2 0 C.positive]
    decide
  have DT : (tok d C x 1).tag=3 := by rw [D]
  have W := (reverse_joined d C x N (CF.mask x X) 0 I LT DT).1
  have Fit : RankFits p (tok d C x 1) := by
    rw [tok_wire]
    exact rank_decoded_fits p _ _
  rw [D] at Fit
  have DR : tok d C y 0=
      ({tag:=3,opcode:=acqOp p,payload:=q}:Tok) := by
    rw [tok_wire]
    change decode p (chartGate d C y 0) (wire d C y 0)=_
    rw [W,D]
    exact acq_reply_roundtrip p _ q B Fit
  have PC : LegalWait d C y := by
    unfold LegalWait
    rw [raw_nondoor_control d C x e N (CF.mask x X) ND]
    exact R.1
  have Rev : Reverse d C y 0 := by
    rcases ReportOwnerReverseShape.non_door_step d C hh G F N x X 1 R.2 e ND
      with S|⟨j,J,_,S⟩
    · have A := S.2 0 C.positive
      rw [DR] at A
      simp [backTag] at A
    · have J0 : j=0 := by omega
      simpa only [J0] using S
  exact ⟨Y,⟨PC,Rev⟩,DR,raw_nondoor_capture d C x e N (CF.mask x X) ND⟩

/-- The actual successful consume, not an old D elsewhere on the
    chart and not merely a tag-3 row. The old D's payload bit is an
    explicit hypothesis. The result simultaneously gives the exact
    three-bit capture, the existing WRITE accessor, the correct next
    source instruction, the cleared rail, and post-mark cached geometry. -/
theorem raw_acq_consume (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (R : ReverseWait d C x 0)
    (O : (readPC d C x).2=acqOp (params d s))
    (K : (tok d C x 0).opcode=acqOp (params d s))
    (Live : (tok d C x 0).fault=false)
    (ND : (tok d C x 0).outcome≠1)
    (b : Nat) (B : acqReplyCentre (tok d C x 0)=b)
    (digit : 0<(params d s).digits) :
    let y := rawNext s x (door C)
    Cached d hh Q y ∧ EmptyIssueShape d C y ∧
    readPC d C y=(1,cmpOp (params d s)) ∧
    ownerCaptureIndex d C y=(tok d C x 0).payload/8%8 ∧
    ReportWriterPayload.capturedSelector (params d s)
      (selectBytes d (y C.root))=b := by
  dsimp only
  let p := params d s
  let e := door C
  let u := selectBytes d (x e)
  let v := selectBytes d (x C.root)
  let y := rawNext s x e
  let t := publicationToken p true v 0
  have CF := cached_fibre d N hh Q F
  have Y : Cached d hh Q y := CF.closed x e X
  have P : sourcePhase p v=2 := R.1.1
  have O' : sourceOpcode p v=acqOp p := O
  have T : tok d C x 0=t := acq_root_tok d C x
  have D : t.tag=3 := by
    rw [←T,R.2.2 0 C.positive]
    rfl
  have K' : t.opcode=acqOp p := by rw [←T]; exact K
  have L : t.fault=false := by rw [←T]; exact Live
  have U : t.outcome≠1 := by rw [←T]; exact ND
  have Rdoor : rightNeighbor e=C.root := RearTrace.right_predecessor C.root
  have J := (raw_capture_pair d x e N (CF.mask x X)).2
  try dsimp only at J
  rw [Rdoor,C.rootHeader] at J
  have A : ownerCaptureIndex d C y=t.payload/8%8 :=
    J.trans (acq_row_success_index p (h e) u v P O' D K' L U)
  have W := raw_door_final d C x N (CF.mask x X)
  have PC : readPC d C y=(1,cmpOp p) :=
    W.1.trans (acq_source_success_pc p v t P O' D K' L U)
  refine ⟨Y,door_consumes_root d C hh G F N x X R digit,PC,?_,?_⟩
  · exact A.trans (by rw [T])
  · rw [captured_selector_index]
    change ownerCaptureIndex d C y/2%2=b
    rw [A]
    rw [T] at B
    unfold acqReplyCentre at B
    omega

/-- Exact all-mark post-ACQ frame with the weakest chronological
    restriction used here: no actual return to source opcode zero.
    Old valid phase/opcode are transported, not presumed at each step. -/
theorem raw_postacq_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (e : Fin n)
    (H : PostAcqPC (params d s) (readPC d C x))
    (digit : 0<(params d s).digits)
    (NZ : (readPC d C (rawNext s x e)).2≠0) :
    let y := rawNext s x e
    Cached d hh Q y ∧ PostAcqPC (params d s) (readPC d C y) ∧
      ownerCaptureIndex d C y=ownerCaptureIndex d C x := by
  dsimp only
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  refine ⟨Y,?_⟩
  by_cases D : e=door C
  · subst e
    let p := params d s
    let u := selectBytes d (x (door C))
    let v := selectBytes d (x C.root)
    let t := publicationToken p true v 0
    let y := rawNext s x (door C)
    have W := raw_door_final d C x N (CF.mask x X)
    have WP : readPC d C y=acqSourcePC p v t := W.1
    have Z : (acqSourcePC p v t).2≠0 := by rw [←WP]; exact NZ
    refine ⟨?_,?_⟩
    · rw [WP]
      exact acq_source_post_pc p v t H digit Z
    · by_cases T : sourcePhase p v=2 ∧ (t.tag=1 ∨ t.tag=2)
      · exact raw_capture_before_ack d C x (door C) N (CF.mask x X)
          T.1 H.2.2 T.2
      · have J := (raw_capture_pair d x (door C) N (CF.mask x X)).2
        try dsimp only at J
        rw [show rightNeighbor (door C) = C.root from RearTrace.right_predecessor C.root,C.rootHeader] at J
        exact J.trans (acq_row_post_index p (h (door C)) u v H Z)
  · refine ⟨?_,raw_nondoor_capture d C x e N (CF.mask x X) D⟩
    rw [raw_nondoor_control d C x e N (CF.mask x X) D]
    exact H

/-- Actual consecutive marks in the same post-ACQ generation.
    This excludes precisely the observable restart-to-ISSUE0 on a
    traversed mark, not any particular intervening opcode or payload.
    In particular it does NOT assume the capture invariant. -/
def NoRestartTape (d : Sheet) (C : Chart h) :
    Raw s n → List (Fin n) → Prop
  | _,[] => True
  | x,e::w =>
      (readPC d C (rawNext s x e)).2≠0 ∧
      NoRestartTape d C (rawNext s x e) w

theorem raw_postacq_run (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (w : List (Fin n)) (X : Cached d hh Q x)
    (H : PostAcqPC (params d s) (readPC d C x))
    (NR : NoRestartTape d C x w) :
    Cached d hh Q (rawRun x w) ∧
      PostAcqPC (params d s) (readPC d C (rawRun x w)) ∧
      ownerCaptureIndex d C (rawRun x w)=ownerCaptureIndex d C x := by
  induction w generalizing x with
  | nil => exact ⟨X,H,rfl⟩
  | cons e w ih =>
    change (readPC d C (rawNext s x e)).2≠0 ∧
      NoRestartTape d C (rawNext s x e) w at NR
    have A := raw_postacq_step d C hh F N x X e H digit NR.1
    have B := ih (rawNext s x e) A.1 A.2.1 NR.2
    change Cached d hh Q (rawRun (rawNext s x e) w) ∧
      PostAcqPC (params d s) (readPC d C (rawRun (rawNext s x e) w)) ∧
      ownerCaptureIndex d C (rawRun (rawNext s x e) w)=ownerCaptureIndex d C x
    exact ⟨B.1,B.2.1,B.2.2.trans A.2.2⟩

/-- Bind the payload hypothesis of the actual consume to every
    subsequent no-restart prefix (in particular the prefix ending
    just before a WRITE issue). -/
theorem acq_consume_then_run (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (R : ReverseWait d C x 0)
    (O : (readPC d C x).2=acqOp (params d s))
    (K : (tok d C x 0).opcode=acqOp (params d s))
    (L : (tok d C x 0).fault=false) (U : (tok d C x 0).outcome≠1)
    (b : Nat) (B : acqReplyCentre (tok d C x 0)=b)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (NR : NoRestartTape d C (rawNext s x (door C)) w) :
    let z := rawRun (rawNext s x (door C)) w
    Cached d hh Q z ∧ PostAcqPC (params d s) (readPC d C z) ∧
    ownerCaptureIndex d C z=(tok d C x 0).payload/8%8 ∧
    ReportWriterPayload.capturedSelector (params d s)
      (selectBytes d (z C.root))=b := by
  dsimp only
  let p := params d s
  let y := rawNext s x (door C)
  let z := rawRun y w
  have A := raw_acq_consume d C hh G F N x X R O K L U b B digit
  have H : PostAcqPC p (readPC d C y) := by
    rw [A.2.2.1]
    exact ⟨.inl rfl,Nat.le_refl _,by change (params d s).digits + 3 ≤ 4*(params d s).digits + 4; omega⟩
  have J := raw_postacq_run d C hh F N digit y w A.1 H NR
  have I : ownerCaptureIndex d C z=(tok d C x 0).payload/8%8 :=
    J.2.2.trans A.2.2.2.1
  refine ⟨J.1,J.2.1,I,?_⟩
  rw [captured_selector_index]
  change ownerCaptureIndex d C z/2%2=b
  rw [I]
  unfold acqReplyCentre at B
  omega

/-- Consumer at the real WRITE-launch mark. The prefix lemma supplies
    Captured; no live centre selector assumption is inserted here.
    The output wire is the actual root K0 after the full joined row.
    The capture field itself survives even this issue mark. -/
theorem raw_write_launch_from_capture (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) {Q : Raw s n→Prop}
    (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok) (b : Nat)
    (P : sourcePhase (params d s) (selectBytes d (x C.root))=1)
    (W : writeOp (params d s)≤sourceOpcode (params d s) (selectBytes d (x C.root)))
    (L : sourceOpcode (params d s) (selectBytes d (x C.root))<sealOp (params d s))
    (T : (source (params d s) (selectBytes d (x C.root))
       (publicationToken (params d s) true (selectBytes d (x C.root)) 0)).2=some t)
    (Forward : t.tag=2)
    (Captured : ReportWriterPayload.capturedSelector (params d s)
      (selectBytes d (x C.root))=b) :
    let p := params d s
    let y := rawNext s x (door C)
    Cached d hh Q y ∧
    resetTokenRead p (selectBytes d (y C.root)) 0=resetTokenWire p t ∧
    ownerCaptureIndex d C y=ownerCaptureIndex d C x ∧
    t.tag=2 ∧ t.opcode=sourceOpcode p (selectBytes d (x C.root)) ∧
    t.fault=false ∧ ReportWriterPayload.priorBank p t=b ∧
      ReportWriterPayload.targetBank p t=1-b := by
  dsimp only
  let p := params d s
  let v := selectBytes d (x C.root)
  let y := rawNext s x (door C)
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x (door C) X
  have A := ReportWriterPayload.issue_write_banks p v
    (publicationToken p true v 0) t P W L T Forward
  have R := (raw_door_final d C x N (CF.mask x X)).2
  change resetTokenRead p (selectBytes d (y C.root)) 0=
    (match (source p v (publicationToken p true v 0)).2 with
     | none => prelaunchDoorNormWire p v
     | some q => resetTokenWire p q) at R
  rw [T] at R
  have J := (raw_capture_pair d x (door C) N (CF.mask x X)).2
  try dsimp only at J
  rw [show rightNeighbor (door C) = C.root from RearTrace.right_predecessor C.root,C.rootHeader] at J
  have O : sourceOpcode p v≤commitOp p := by change sourceOpcode p v < sealOp p at L; unfold sealOp at L; unfold commitOp; omega
  have pos : 0<sourceOpcode p v := by change writeOp p ≤ sourceOpcode p v at W; unfold writeOp at W; omega
  have I : ownerCaptureIndex d C y=ownerCaptureIndex d C x :=
    J.trans (acq_row_issue_index p (h (door C)) _ v t P O pos T Forward)
  exact ⟨Y,R,I,A.1,A.2.1,A.2.2.1,A.2.2.2.1.trans Captured,
    A.2.2.2.2.trans (congrArg (fun c : Nat=>1-c) Captured)⟩

#print axioms raw_capture_pair
#print axioms raw_nondoor_capture
#print axioms raw_capture_before_ack
#print axioms raw_acq_last_relay
#print axioms raw_acq_consume
#print axioms raw_postacq_step
#print axioms raw_postacq_run
#print axioms acq_consume_then_run
#print axioms raw_write_launch_from_capture

/-- General reverse movement preserves the entire canonical successful ACQ reply. -/
theorem raw_acq_reverse_hop (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (R : ReverseWait d C x (i+1))
    (q : Nat) (B : q<64)
    (D : tok d C x (i+1)=({tag:=3,opcode:=acqOp (params d s),payload:=q}:Tok)) :
    let y := rawNext s x (out C i)
    Cached d hh Q y ∧ ReverseWait d C y i ∧
    tok d C y i=({tag:=3,opcode:=acqOp (params d s),payload:=q}:Tok) := by
  dsimp only
  let p := params d s
  let e := out C i
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y : Cached d hh Q y := CF.closed x e X
  have I : i+1<C.L := R.2.1
  have IL : i<C.L := by omega
  have ND : e≠door C := Ne.symm (ReportChartPartition.door_not_outgoing C i IL)
  have LT : (tok d C x i).tag≠2 := by
    rw [R.2.2 i IL]
    simp [backTag]
  have DT : (tok d C x (i+1)).tag=3 := by rw [D]
  have W := (reverse_joined d C x N (CF.mask x X) i I LT DT).1
  have Fit : RankFits p (tok d C x (i+1)) := by
    rw [tok_wire]
    exact rank_decoded_fits p _ _
  rw [D] at Fit
  have DR : tok d C y i=({tag:=3,opcode:=acqOp p,payload:=q}:Tok) := by
    rw [tok_wire]
    change decode p (chartGate d C y i) (wire d C y i)=_
    rw [W,D]
    exact acq_reply_roundtrip p _ q B Fit
  have PC : LegalWait d C y := by
    unfold LegalWait
    rw [raw_nondoor_control d C x e N (CF.mask x X) ND]
    exact R.1
  have Rev : Reverse d C y i := by
    rcases ReportOwnerReverseShape.non_door_step d C hh G F N x X (i+1) R.2 e ND
      with S|⟨j,J,_,S⟩
    · have A := S.2 i IL
      rw [DR] at A
      simp [backTag] at A
    · have K : j=i := by omega
      simpa only [K] using S
  exact ⟨Y,⟨PC,Rev⟩,DR⟩

#print axioms raw_acq_reverse_hop
end L4.ReportOwnerAcquireReturn
namespace L4.ReportOwnerAcquireReturn
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportOwnerProvenanceTransport ReportOwnerReverseShape
open ReportOwnerReverseControl ReportPrelaunchClock ReportPrelaunchDoorLift
open ReportOwnerDoorProjection ReportByteRows ReportRawProjection

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
variable {s n : Nat} {h : Fin n→Bool}

def ownerCaptureSix (d : Sheet) (C : Chart h) (x : Raw s n) : Nat :=
  acqCaptureSix (params d s) (selectBytes d (x C.root))

theorem raw_six_pair (d : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i) :
    let p := params d s
    let u := selectBytes d (x e)
    let v := selectBytes d (x (rightNeighbor e))
    let q := row p (h e,h (rightNeighbor e)) (u,v)
    acqCaptureSix p (selectBytes d (rawNext s x e e))=
      acqCaptureSix p (q.1.apply u) ∧
    acqCaptureSix p (selectBytes d (rawNext s x e (rightNeighbor e)))=
      acqCaptureSix p (q.2.apply v) := by
  dsimp only
  exact ⟨acq_six_low_congr _ _ _ (fun i I =>
      (ReportLeaseStep.raw_low_pair d x e N mask i I).1),
    acq_six_low_congr _ _ _ (fun i I =>
      (ReportLeaseStep.raw_low_pair d x e N mask i I).2)⟩

theorem raw_nondoor_six (d : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (D : e≠door C) :
    ownerCaptureSix d C (rawNext s x e)=ownerCaptureSix d C x := by
  by_cases E : e=C.root
  · subst e
    have H := (raw_six_pair d x C.root N mask).1
    try dsimp only at H
    rw [C.rootHeader] at H
    exact H.trans (acq_row_left_six (params d s)
      (h (rightNeighbor C.root)) _ _)
  · have R : C.root≠rightNeighbor e := by
      intro K
      apply D
      unfold door
      rw [K,RearTrace.predecessor_right]
    unfold ownerCaptureSix
    rw [raw_spectator x e C.root (Ne.symm E) R]

theorem raw_six_before_ack (d : Sheet) (C : Chart h)
    (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (P : sourcePhase (params d s) (selectBytes d (x C.root))=2)
    (O : sourceOpcode (params d s) (selectBytes d (x C.root))≤
      commitOp (params d s))
    (T : (publicationToken (params d s) true (selectBytes d (x C.root)) 0).tag=1 ∨
         (publicationToken (params d s) true (selectBytes d (x C.root)) 0).tag=2) :
    ownerCaptureSix d C (rawNext s x e)=ownerCaptureSix d C x :=
  acq_six_of_file _ _ _ (ReportLeaseStep.file_before_ack d C x e N mask P O T)

/-- Actual successful source consume, with the exact six-bit writeback. -/
theorem raw_acq_consume_six (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (R : ReverseWait d C x 0)
    (O : (readPC d C x).2=acqOp (params d s))
    (K : (tok d C x 0).opcode=acqOp (params d s))
    (Live : (tok d C x 0).fault=false)
    (ND : (tok d C x 0).outcome≠1)
    (digit : 0<(params d s).digits) :
    let y := rawNext s x (door C)
    Cached d hh Q y ∧ EmptyIssueShape d C y ∧
      readPC d C y=(1,cmpOp (params d s)) ∧
      ownerCaptureSix d C y=(tok d C x 0).payload%64 := by
  dsimp only
  let p := params d s
  let e := door C
  let u := selectBytes d (x e)
  let v := selectBytes d (x C.root)
  let y := rawNext s x e
  let t := publicationToken p true v 0
  let CF := cached_fibre d N hh Q F
  have P : sourcePhase p v=2 := R.1.1
  have O' : sourceOpcode p v=acqOp p := O
  have T : tok d C x 0=t := acq_root_tok d C x
  have D : t.tag=3 := by
    rw [←T,R.2.2 0 C.positive]
    rfl
  have K' : t.opcode=acqOp p := by rw [←T]; exact K
  have L : t.fault=false := by rw [←T]; exact Live
  have U : t.outcome≠1 := by rw [←T]; exact ND
  have A := raw_acq_consume d C hh G F N x X R O K Live ND
    (acqReplyCentre (tok d C x 0)) rfl digit
  have J := (raw_six_pair d x e N (CF.mask x X)).2
  try dsimp only at J
  rw [show rightNeighbor e=C.root from RearTrace.right_predecessor C.root,C.rootHeader] at J
  refine ⟨A.1,A.2.1,A.2.2.1,?_⟩
  exact (J.trans (acq_row_success_six p (h e) u v P O' D K' L U)).trans
    (by rw [T])

theorem raw_postacq_six_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (e : Fin n)
    (H : PostAcqPC (params d s) (readPC d C x))
    (digit : 0<(params d s).digits)
    (NZ : (readPC d C (rawNext s x e)).2≠0) :
    let y := rawNext s x e
    Cached d hh Q y ∧ PostAcqPC (params d s) (readPC d C y) ∧
      ownerCaptureSix d C y=ownerCaptureSix d C x := by
  dsimp only
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  refine ⟨Y,?_⟩
  by_cases D : e=door C
  · subst e
    let p := params d s
    let u := selectBytes d (x (door C))
    let v := selectBytes d (x C.root)
    let t := publicationToken p true v 0
    let y := rawNext s x (door C)
    have W := raw_door_final d C x N (CF.mask x X)
    have WP : readPC d C y=acqSourcePC p v t := W.1
    have Z : (acqSourcePC p v t).2≠0 := by rw [←WP]; exact NZ
    refine ⟨?_,?_⟩
    · rw [WP]
      exact acq_source_post_pc p v t H digit Z
    · by_cases T : sourcePhase p v=2 ∧ (t.tag=1 ∨ t.tag=2)
      · exact raw_six_before_ack d C x (door C) N (CF.mask x X)
          T.1 H.2.2 T.2
      · have J := (raw_six_pair d x (door C) N (CF.mask x X)).2
        try dsimp only at J
        rw [show rightNeighbor (door C) = C.root from RearTrace.right_predecessor C.root,C.rootHeader] at J
        exact J.trans (acq_row_post_six p (h (door C)) u v H Z)
  · refine ⟨?_,raw_nondoor_six d C x e N (CF.mask x X) D⟩
    rw [raw_nondoor_control d C x e N (CF.mask x X) D]
    exact H

theorem raw_postacq_six_run (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (w : List (Fin n)) (X : Cached d hh Q x)
    (H : PostAcqPC (params d s) (readPC d C x))
    (NR : NoRestartTape d C x w) :
    Cached d hh Q (rawRun x w) ∧
      PostAcqPC (params d s) (readPC d C (rawRun x w)) ∧
      ownerCaptureSix d C (rawRun x w)=ownerCaptureSix d C x := by
  induction w generalizing x with
  | nil => exact ⟨X,H,rfl⟩
  | cons e w ih =>
    change (readPC d C (rawNext s x e)).2≠0 ∧
      NoRestartTape d C (rawNext s x e) w at NR
    have A := raw_postacq_six_step d C hh F N x X e H digit NR.1
    have B := ih (rawNext s x e) A.1 A.2.1 NR.2
    change Cached d hh Q (rawRun (rawNext s x e) w) ∧
      PostAcqPC (params d s) (readPC d C (rawRun (rawNext s x e) w)) ∧
      ownerCaptureSix d C (rawRun (rawNext s x e) w)=ownerCaptureSix d C x
    exact ⟨B.1,B.2.1,B.2.2.trans A.2.2⟩

theorem acq_consume_then_run_six (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (R : ReverseWait d C x 0)
    (O : (readPC d C x).2=acqOp (params d s))
    (K : (tok d C x 0).opcode=acqOp (params d s))
    (Live : (tok d C x 0).fault=false)
    (ND : (tok d C x 0).outcome≠1)
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (NR : NoRestartTape d C (rawNext s x (door C)) w) :
    let z := rawRun (rawNext s x (door C)) w
    Cached d hh Q z ∧ PostAcqPC (params d s) (readPC d C z) ∧
      ownerCaptureSix d C z=(tok d C x 0).payload%64 := by
  dsimp only
  let p := params d s
  let y := rawNext s x (door C)
  have A := raw_acq_consume_six d C hh G F N x X R O K Live ND digit
  have H : PostAcqPC p (readPC d C y) := by
    rw [A.2.2.1]
    exact ⟨.inl rfl,Nat.le_refl _,by change (params d s).digits + 3 ≤ 4*(params d s).digits + 4; omega⟩
  have J := raw_postacq_six_run d C hh F N digit y w A.1 H NR
  exact ⟨J.1,J.2.1,J.2.2.trans A.2.2.2⟩

#print axioms raw_acq_consume_six
#print axioms raw_postacq_six_step
#print axioms acq_consume_then_run_six
end L4.ReportOwnerAcquireReturn

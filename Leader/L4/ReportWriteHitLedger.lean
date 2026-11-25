import Leader.L4.ReportJoinedWriteValue
import Leader.L4.ReportOwnerIndexedFlight
import Leader.L4.ReportIndexedFlightContract

namespace L4.ReportWriteHitLedger
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows ReportOwnerProvenanceTransport ReportPrelaunchK1Geometry
open ReportGenerationAncestry ReportLeaseOwner ReportGoodEightCut
open ReportOwnerForwardLocations ReportOwnerForwardControl
open ReportOwnerReverseShape ReportOwnerReverseControl
open ReportOwnerIssueControl ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerAcquireReturn ReportOwnerCommandRail
open ReportJoinedWriteValue ReportOwnerIndexedFlight
open ReportIndexedSourcePrefix ReportIndexedFlightContract

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def stagedValue (d : Sheet) (f : Tok) : BitVec (2*ReportByteRows.d (params d s)) :=
  BitVec.ofNat _ (f.payload%2^(2*ReportByteRows.d (params d s)))

/-- Pending physical installation. No credit is granted by this
    predicate. The current endpoint belongs to the very same flight
    and retains the actually installed value. -/
def WriteHitLedger (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (j : Fin (params d s).digits) (f : Tok) : Prop :=
  let p := params d s
  let k := C.a+j.val
  ∃ pre post : List (Fin n), w=pre++(out C k::post) ∧
    let x := rawRun x0 pre
    let u := selectBytes d (x (out C k))
    tok d C x k=f ∧ readyAt d C x k=true ∧
    reportOldOffset p (h (out C k)) u=j.val ∧
    (h (out C k)=false ∨
      (reportOldGrant p u 1=true ∧ publicationSelector p u=ancestryWriteOld p f)) ∧
    reportDigitPair p (selectBytes d (rawNext s x (out C k) (out C k)))
      (ancestryWriteTarget p f)=stagedValue d f ∧
    reportDigitPair p (selectBytes d (rawRun x0 w (out C k)))
      (ancestryWriteTarget p f)=stagedValue d f

private theorem write_range (p : Params) (j : Fin p.digits) :
    IndexedOp p (writeOp p+j.val) := by
  have := j.isLt
  unfold IndexedOp cmpOp writeOp sealOp
  omega

/-- The literal old hit on the actual emitted mark, including the
    exact old permission and the joined physical installation. -/
theorem hit_now (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (r : Owner h) (j : Fin (params d s).digits) (J : j.val<(charter G r).b)
    (x0 : Raw s n) (w : List (Fin n)) (X0 : Cached d hh Q x0)
    (a : IndexedData)
    (R : FState d (charter G r) (writeOp (params d s)+j.val) (rawRun x0 w)
      ((charter G r).a+j.val) (some a))
    (Next : stepPayload d (charter G r) (writeOp (params d s)+j.val)
      (rawRun x0 w) ((charter G r).a+j.val) (some a)=some a) :
    WriteHitLedger d (charter G r) x0
      (w++[out (charter G r) ((charter G r).a+j.val)]) j
      (indexedF (params d s) (writeOp (params d s)+j.val) (some a)) := by
  let C := charter G r
  let p := params d s
  let op := writeOp p+j.val
  let k := C.a+j.val
  let x := rawRun x0 w
  let u := selectBytes d (x (out C k))
  let f := indexedF p op (some a)
  have X := cached_run d N hh F x0 X0 w
  obtain ⟨_,Lane,_⟩ := middle_position G r j.val J
  have Off := middle_offset d hh G r j J x X
  have Tok : publicationToken p (h (out C k)) u 1=f := by
    have P := R.packet
    rw [predecessor_projection,Lane] at P
    exact P
  have Rd := rankIndexed_ready p op (write_range p j) (h (out C k)) u 1 (some a) Tok
  have Next' : indexedNext p op (h (out C k)) u 1 (some a)=some a := by
    change indexedNext p op (h (out C k)) u (C.route.port k) (some a)=some a at Next
    rwa [Lane] at Next
  have Permit := indexed_write_next_permit p op (Nat.le_add_right _ _) (h (out C k)) u
    a R.bound (by change reportOldOffset p (h (out C k)) u=op-writeOp p; rw [Off]; omega) Next'
  have Value := raw_write_hit d x (out C k) N ((cached_fibre d N hh Q F).mask x X)
    j Rd (by rw [Tok]; rfl) (by rw [Tok]; rfl) Off
    (by rw [Tok]; exact Permit)
  have V : reportDigitPair p (selectBytes d (rawNext s x (out C k) (out C k)))
      (ancestryWriteTarget p f)=stagedValue d f := by
    have H := Value.1
    rw [Tok] at H
    exact H
  refine ⟨w,[],rfl,R.packet,?_,Off,Permit,V,?_⟩
  · unfold readyAt
    rw [Lane]
    exact Rd
  · rw [ShortOwnerEpochJS.raw_snoc]
    exact V

/-- No matter which physical mark is selected, the recorded digit
    stays installed if the old owner's hit slot is no longer F. -/
theorem hit_extend (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (r : Owner h) (j : Fin (params d s).digits) (J : j.val<(charter G r).b)
    (x0 : Raw s n) (w : List (Fin n)) (X0 : Cached d hh Q x0)
    (e : Fin n) (f : Tok)
    (Tag : (tok d (charter G r) (rawRun x0 w) ((charter G r).a+j.val)).tag≠2)
    (H : WriteHitLedger d (charter G r) x0 w j f) :
    WriteHitLedger d (charter G r) x0 (w++[e]) j f := by
  obtain ⟨pre,post,E,T,R,O,P,V,Now⟩ := H
  let C := charter G r
  let k := C.a+j.val
  have Lane := (middle_position G r j.val J).2.1
  have X := cached_run d N hh F x0 X0 w
  refine ⟨pre,post++[e],?_,T,R,O,P,V,?_⟩
  · rw [E,List.append_assoc]
    rfl
  · rw [ShortOwnerEpochJS.raw_snoc]
    exact (raw_chart_not_forward_frame d C (rawRun x0 w) e N
      ((cached_fibre d N hh Q F).mask _ X) k Lane Tag _).trans Now

private theorem f_passed_tag (d : Sheet) (C : Chart h) (op : Nat)
    (x : Raw s n) (k i : Nat) (q : Option IndexedData)
    (R : FState d C op x k q) (I : i<C.L) (Past : i<k) :
    (tok d C x i).tag≠2 := by
  rw [R.shape.2.2 i I]
  simp [frontTag,Past]

private theorem d_passed_tag (d : Sheet) (C : Chart h) (op : Nat)
    (x : Raw s n) (k i : Nat) (q : Option IndexedData)
    (R : DState d C op x k q) (I : i<C.L) :
    (tok d C x i).tag≠2 := by
  rw [R.shape.2.2 i I]
  unfold backTag
  split <;> try decide
  split <;> decide

/-- The all-mark invariant: a successful WRITE is the original
    issued data, and the physical installation is required exactly
    after passing the hit. The none branch grants no certificate. -/
def WriteProgress (d : Sheet) (C : Chart h) (x0 : Raw s n)
    (w : List (Fin n)) (j : Fin (params d s).digits) (a : IndexedData) :
    Cursor→Prop
  | .forward k q =>
    ∀ b,q=some b→ b=a ∧ (C.a+j.val<k →
      WriteHitLedger d C x0 w j (indexedF (params d s)
        (writeOp (params d s)+j.val) (some a)))
  | .backward _ q =>
    ∀ b,q=some b→ b=a ∧
      WriteHitLedger d C x0 w j (indexedF (params d s)
        (writeOp (params d s)+j.val) (some a))

/-- The new cursor passed the target: either this is the unique
    actual hit now or a frame of an earlier hit. Covers terminal
    turn as well as ordinary forward hops. -/
private theorem forward_credit (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (r : Owner h) (j : Fin (params d s).digits) (J : j.val<(charter G r).b)
    (x0 : Raw s n) (X0 : Cached d hh Q x0) (w : List (Fin n))
    (a : IndexedData) (k : Nat) (q : Option IndexedData)
    (R : FState d (charter G r) (writeOp (params d s)+j.val) (rawRun x0 w) k q)
    (P : WriteProgress d (charter G r) x0 w j a (.forward k q))
    (b : IndexedData)
    (E : stepPayload d (charter G r) (writeOp (params d s)+j.val)
      (rawRun x0 w) k q=some b) :
    b=a ∧ ((charter G r).a+j.val<k+1 →
      WriteHitLedger d (charter G r) x0 (w++[out (charter G r) k]) j
        (indexedF (params d s) (writeOp (params d s)+j.val) (some a))) := by
  let C := charter G r
  let p := params d s
  let op := writeOp p+j.val
  have Q := indexed_write_next_some p op (Nat.le_add_right _ _) (h (out C k))
    (bytesL d (rawRun x0 w) (out C k)) (C.route.port k) q b E
  obtain ⟨Eq,Old⟩ := P b Q
  subst b
  refine ⟨rfl,?_⟩
  intro Past
  by_cases K : k=C.a+j.val
  · subst k
    rw [Q] at R E
    exact hit_now d N hh G F r j J x0 w X0 a R E
  · change k≠(charter G r).a+j.val at K
    have L : C.a+j.val<k := by change (charter G r).a+j.val<k; omega
    have I := (middle_position G r j.val J).1
    exact hit_extend d N hh G F r j J x0 w X0 (out C k) _
      (f_passed_tag d C op (rawRun x0 w) k (C.a+j.val) q R I L) (Old L)

/-- Full all-mark ledger on exactly the historical Walk.
    A faulted flight cannot be made healthy by a later hold/hop. -/
theorem write_hit_progress (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (r : Owner h) (j : Fin (params d s).digits) (J : j.val<(charter G r).b)
    (x0 : Raw s n) (X0 : Cached d hh Q x0) (a : IndexedData)
    (w : List (Fin n)) (c : Cursor)
    (W : Walk d (charter G r) (writeOp (params d s)+j.val) x0 (some a) w c) :
    WriteProgress d (charter G r) x0 w j a c := by
  let C := charter G r
  let p := params d s
  let op := writeOp p+j.val
  have I := (middle_position G r j.val J).1
  induction W with
  | seed R =>
    intro b E
    exact ⟨(Option.some.inj E).symm,fun H=>(by omega : False).elim⟩
  | @fhold w k q e W R IH =>
    intro b E
    obtain ⟨Eq,H⟩ := IH b E
    refine ⟨Eq,?_⟩
    intro Past
    have A : FState d C op (rawRun x0 w) k q :=
      walk_at d C op x0 (some a) w (.forward k q) W
    exact hit_extend d N hh G F r j J x0 w X0 e _
      (f_passed_tag d C op (rawRun x0 w) k (C.a+j.val) q A I Past) (H Past)
  | @hop w k q W R S IH =>
    intro b E
    exact forward_credit d N hh G F r j J x0 X0 w a k q R IH b E
  | @turn w k q W R K S IH =>
    intro b E
    obtain ⟨Eq,H⟩ := forward_credit d N hh G F r j J x0 X0 w a k q R IH b E
    exact ⟨Eq,H (by omega)⟩
  | @dhold w k q e W R IH =>
    intro b E
    obtain ⟨Eq,H⟩ := IH b E
    have A : DState d C op (rawRun x0 w) k q :=
      walk_at d C op x0 (some a) w (.backward k q) W
    exact ⟨Eq,hit_extend d N hh G F r j J x0 w X0 e _
      (d_passed_tag d C op (rawRun x0 w) k (C.a+j.val) q A I) H⟩
  | @back w k q W R IH =>
    intro b E
    obtain ⟨Eq,H⟩ := IH b E
    have A : DState d C op (rawRun x0 w) (k+1) q :=
      walk_at d C op x0 (some a) w (.backward (k+1) q) W
    exact ⟨Eq,hit_extend d N hh G F r j J x0 w X0 (out C k) _
      (d_passed_tag d C op (rawRun x0 w) (k+1) (C.a+j.val) q A I) H⟩

/-- Exact WRITE component of IndexedFlightIdentity.
    The certificate is earned only on the actual CreditAt consume,
    not on the terminal turn or the physical hit. -/
theorem write_flight_result (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Owner h) (issue : Raw s n) (flight : List (Fin n))
    (j : Fin (params d s).digits) (f : Tok)
    (X : Cached d hh Q issue) (J : j.val<(charter G r).b)
    (H : IssuedSegment d (charter G r) issue flight (writeOp (params d s)+j.val) f) :
    WriteFlightResult d (charter G r) issue flight j
      (acqCaptureIndex (params d s) (selectBytes d (issue (charter G r).root))/2%2) f := by
  let C := charter G r
  let p := params d s
  let op := writeOp p+j.val
  let prior := acqCaptureIndex p (selectBytes d (issue C.root))/2%2
  let x0 := rawNext s issue (door C)
  let old := rawRun x0 flight
  obtain ⟨I,PC,Source,Tag,_Live,_Op,Start,Before,_End,Credit⟩ := H
  have P : sourcePhase p (selectBytes d (issue C.root))=1 := congrArg Prod.fst PC
  have O : sourceOpcode p (selectBytes d (issue C.root))=op := congrArg Prod.snd PC
  obtain ⟨a,Valid,Packet,OldBank,Target,Send⟩ := indexed_write_issue_data p
    (selectBytes d (issue C.root)) (publicationToken p true (selectBytes d (issue C.root)) 0)
    f P (by rw [O]; exact Nat.le_add_right _ _)
    (by rw [O]; have B : j.val<p.digits := j.isLt; unfold op writeOp sealOp; omega) Source Tag
  rw [O] at Valid Packet
  have X0 : Cached d hh Q x0 := (cached_fibre d N hh Q F).closed issue (door C) X
  have Seed := launch_from_token d C op (write_range p j) hh G F N issue X I PC a Valid
    (Start.trans Packet)
  have RootTag : (tok d C old 0).tag=3 := Credit.2.2.1
  have RootLive : (tok d C old 0).fault=false := Credit.2.2.2.2.1
  obtain ⟨b,W,D⟩ := walk_successful_root d C op (write_range p j) hh G F N x0 X0
    (some a) Seed digit flight Before RootTag RootLive
  obtain ⟨BA,L⟩ := (write_hit_progress d N hh G F r j J x0 X0 a flight
    (.backward 0 (some b)) W) b rfl
  subst b
  -- The old reply of this flight is the canonical WRITE D, payload 0.
  have _Reply : tok d C old 0=({tag:=3,opcode:=op}:Tok) := by
    rw [D.packet]
    change indexedD p op (some a)=({tag:=3,opcode:=op}:Tok)
    simp [indexedD,op,show ¬writeOp p+j.val<writeOp p by omega]
  rw [←Packet] at L
  obtain ⟨pre,post,W,T,R,Off,Permit,New,Now⟩ := L
  let k := C.a+j.val
  obtain ⟨K,Lane,Site⟩ := middle_position G r j.val J
  have Y := cached_run d N hh F x0 X0 flight
  have Frame := raw_chart_not_forward_frame d C old (door C) N
    ((cached_fibre d N hh Q F).mask old Y) k Lane
    (d_passed_tag d C op old 0 k (some a) D K) (ancestryWriteTarget p f)
  have AtAck := Frame.trans Now
  change ancestryWriteOld p f=prior at OldBank
  change ancestryWriteTarget p f=1-prior at Target
  rw [OldBank] at Permit
  rw [Target] at New AtAck
  refine ⟨pre,post,k,W,K,Site,Lane,T,R,Off,Permit,OldBank,Target,Send,New,AtAck,Credit⟩

#print axioms hit_now
#print axioms write_hit_progress
#print axioms write_flight_result
end L4.ReportWriteHitLedger

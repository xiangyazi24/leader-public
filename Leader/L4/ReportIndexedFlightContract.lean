import Leader.L4.ReportIndexedSourcePrefix
import Leader.L4.ReportReaderWordOwner
import Leader.L4.ReportOwnerWriteTransport

namespace L4.ReportIndexedFlightContract
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportByteRows ReportPrelaunchClock
open ReportOwnerIssueControl ReportOwnerAcquireReturn ReportOwnerCommandRail
open ReportOwnerProvenanceTransport ReportGenerationAncestry
open ReportLeaseOwner ReportLeaseGrants ReportGoodEightCut ReportGoodEightBank
open ReportIndexedSourcePrefix ReportGrantTimeline ReportPrelaunchRank

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- An actual old source issue and subsequent same-command flight up
    to the old root D. Its ending mark is NOT in flight. -/
def IssuedSegment (d : Sheet) (C : Chart h) (issue : Raw s n)
    (flight : List (Fin n)) (op : Nat) (f : Tok) : Prop :=
  LegalIssue d C issue ∧ readPC d C issue=(1,op) ∧
  (source (params d s) (selectBytes d (issue C.root))
    (publicationToken (params d s) true (selectBytes d (issue C.root)) 0)).2=some f ∧
  f.tag=2 ∧ f.fault=false ∧ f.opcode=op ∧
  let start := rawNext s issue (door C)
  let old := rawRun start flight
  tok d C start 0=f ∧
  ReportOwnerAcquireProvenance.BeforeConsume d C start flight ∧
  readPC d C old=(2,op) ∧ CreditAt d C old (door C)

/-- The exact half sampled by reader_digit_old. This definition,
    not a whole-pair clipping, is used in the actual certificate. -/
def sampleHalf (p : Params) (u : BitVec p.w) (bank : Nat) (port : Fin 3) : Nat :=
  let M := 2^ReportByteRows.d p
  min (p.beta-1)
    (if port=0 then (reportDigitPair p u bank).toNat/M
      else (reportDigitPair p u bank).toNat%M)

/-- Correct stronger ReaderHit; unlike ReaderEntry alone it ties
    both index and value to one real occurrence on this flight. -/
def ReadSample (d : Sheet) (C : Chart h) (start : Raw s n)
    (flight : List (Fin n)) (op j : Nat) (port : Fin 3)
    (bank value : Nat) : Prop :=
  let p := params d s
  ∃ pre post : List (Fin n), ∃ k : Nat,
    flight=pre++(out C k::post) ∧ k<C.L ∧ C.route.port k=port ∧
    let x := rawRun start pre
    let u := selectBytes d (x (out C k))
    let t := tok d C x k
    t.tag=2 ∧ t.fault=false ∧ t.opcode=op ∧ readyAt d C x k=true ∧
    reportOldOffset p (h (out C k)) u=j ∧
    (if port=0 then t.payload/2^(2*ReportByteRows.d p+1)%2
      else t.payload/2^(2*ReportByteRows.d p)%2)=bank ∧
    value=sampleHalf p u bank port

/-- The full returned pair of digit samples, not just a fact
    about the two ready marks or about their bank indices. -/
def ReaderFlightResult (d : Sheet) (C : Chart h) (issue : Raw s n)
    (flight : List (Fin n)) (op j : Nat) (left right : Nat) : Prop :=
  let p := params d s
  let start := rawNext s issue (door C)
  let old := rawRun start flight
  ∃ a b : Nat,
    ReadSample d C start flight op j 0 left a ∧
    ReadSample d C start flight op j 2 right b ∧
    (tok d C old 0).payload=a*2^ReportByteRows.d p+b

/-- An actual WRITE effect on the same original command segment,
    followed by its own healthy matching D consume. In the
    pre-ACK state physical installation is not yet logical credit. -/
def WriteFlightResult (d : Sheet) (C : Chart h) (issue : Raw s n)
    (flight : List (Fin n)) (j : Fin (params d s).digits) (prior : Nat)
    (f : Tok) : Prop :=
  let p := params d s
  let start := rawNext s issue (door C)
  let old := rawRun start flight
  let after := rawNext s old (door C)
  ∃ pre post : List (Fin n), ∃ k : Nat,
    flight=pre++(out C k::post) ∧ k<C.L ∧
    out C k=nextAt (centre C) j.val ∧ C.route.port k=1 ∧
    let x := rawRun start pre
    let new := rawNext s x (out C k)
    let u := selectBytes d (x (out C k))
    tok d C x k=f ∧ readyAt d C x k=true ∧
    reportOldOffset p (h (out C k)) u=j.val ∧
    (h (out C k)=false ∨
      (reportOldGrant p u 1=true ∧ publicationSelector p u=prior)) ∧
    ancestryWriteOld p f=prior ∧ ancestryWriteTarget p f=1-prior ∧
    f.payload%2^(2*ReportByteRows.d p)=ancestrySendDigits p (selectBytes d (issue C.root)) ∧
    reportDigitPair p (selectBytes d (new (out C k))) (1-prior)=
      BitVec.ofNat (2*ReportByteRows.d p) (f.payload%2^(2*ReportByteRows.d p)) ∧
    reportDigitPair p (selectBytes d (after (out C k))) (1-prior)=
      BitVec.ofNat (2*ReportByteRows.d p) (f.payload%2^(2*ReportByteRows.d p)) ∧
    CreditAt d C old (door C)

/-- Supply exact per-command completion; the seed has the original
    successful ACQ history and the cached chart width. Only the
    single flight's payload identity and physical row are at issue. -/
def IndexedFlightIdentity (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) : Prop :=
  ∀ (r : Owner h) (issue : Raw s n) (flight : List (Fin n))
    (j : Fin (params d s).digits) (f : Tok),
    let C := charter G r
    let p := params d s
    let cap := acqCaptureIndex p (selectBytes d (issue C.root))
    FirstCut d hh Q G issue →
    (∀ i,i<C.L→h (out C i)=true→rawGrant d issue (out C i) (C.route.port i)=true) →
    (∀ e, e< (params d s).digits →
      e<C.a ∧ e<C.b ∧ e<C.L-C.a-C.b) →
    ((∀ op, (op=cmpOp p+j.val ∨ op=readOp p+j.val) →
      IssuedSegment d C issue flight op f →
      ReaderFlightResult d C issue flight op j.val (cap/4) (cap%2)) ∧
    (IssuedSegment d C issue flight (writeOp p+j.val) f →
      WriteFlightResult d C issue flight j (cap/2%2) f))

/-- One-mark frame for an already credited digit, while no new
    generation is started. The proof uses actual alignment and
    unique K1 ownership; it must not use BankSafe alone (which
    protects the *other*, currently selected bank). -/
def StagedPrefixFrame (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) : Prop :=
  ∀ (r : Owner h) (x : Raw s n) (e : Fin n)
    (j : Fin (params d s).digits) (prior : Nat),
    let C := charter G r
    let p := params d s
    FirstCut d hh Q G x → StrongSerial d C x →
    (logical p.digits (writeOp p+j.val)<logical p.digits (readPC d C x).2) →
    (readPC d C x).2≤commitOp p →
    j.val<C.b →
    reportDigitPair p (selectBytes d (rawNext s x e (nextAt (centre C) j.val))) (1-prior)=
      reportDigitPair p (selectBytes d (x (nextAt (centre C) j.val))) (1-prior)

end L4.ReportIndexedFlightContract

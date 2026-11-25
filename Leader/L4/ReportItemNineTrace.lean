import Leader.L4.ReportByteRows
import Leader.L4.ReportIndexedSourcePrefix
import Leader.L4.ReportFreshIndexedSource
import Leader.L4.ReportCommitValue

namespace L4.ReportItemNineTrace
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows ReportPrelaunchK1Geometry ReportPrelaunchClock
open ReportOwnerAcquireReturn ReportOwnerReverseControl
open ReportIndexedSourcePrefix ReportOwnerCommandRail
open ReportDigitArithmetic ReportDigitWord ReportStaticSpacing
open ReportGoodEightCut ReportLeaseOwner

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def rootBytes (d : Sheet) (C : Chart h) (x : Raw s n) :=
  selectBytes d (x C.root)

def ReadReceipts (p : Params) (I : ItemNineInputs) (l : List Receipt) : Prop :=
  ∀ r∈l,ItemNineReply p I r.1 r.2

theorem math_credit (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n)
    (I : ItemNineInputs) (B : 2≤(params d s).beta)
    (XL : I.left<(params d s).beta^(params d s).digits)
    (XR : I.right<(params d s).beta^(params d s).digits)
    (R : (params d s).radius<(params d s).beta^(params d s).digits)
    (A : ItemNineAt (params d s) I (readPC d C x).2
      (item9Read (params d s) (rootBytes d C x)))
    (K : CreditAt d C x e)
    (D : ItemNineReply (params d s) I (readPC d C x).2 (tok d C x 0)) :
    ItemNineAt (params d s) I (readPC d C (rawNext s x e)).2
      (item9Read (params d s) (rootBytes d C (rawNext s x e))) := by
  let p := params d s
  let v := rootBytes d C x
  let u := rootBytes d C (rawNext s x e)
  let t := tok d C x 0
  obtain ⟨_,Shape,Tag,Match,Live,ND,_,Next,File⟩ := K
  have P : sourcePhase p v=2 := Shape.1.1
  have O : sourceOpcode p v≤commitOp p := Shape.1.2
  have H := item9_advance p I v t _ _ B XL XR R P rfl Tag Match Live ND Next A D
  have F : drainFile p u=fileAfterSource p v t :=
    File.trans (source_file_is_replay p v t P O).symm
  have Eq := item9_read_congr p u ((liftSourcePatch p (source p v t).1).apply v) F
  rw [Eq]
  exact H

/-- Every prefix of a real AckTape runs the exact mathematical
    recurrence. Holds do not touch the file, and there is no credit
    at physical WRITE, only at the actual root consume. -/
theorem math_run (d : Sheet) (C : Chart h) (I : ItemNineInputs)
    (B : 2≤(params d s).beta)
    (XL : I.left<(params d s).beta^(params d s).digits)
    (XR : I.right<(params d s).beta^(params d s).digits)
    (R : (params d s).radius<(params d s).beta^(params d s).digits)
    (x : Raw s n) (w : List (Fin n)) (l : List Receipt)
    (T : AckTape d C x w l)
    (A : ItemNineAt (params d s) I (readPC d C x).2
      (item9Read (params d s) (rootBytes d C x)))
    (D : ReadReceipts (params d s) I l) :
    ItemNineAt (params d s) I (readPC d C (rawRun x w)).2
      (item9Read (params d s) (rootBytes d C (rawRun x w))) := by
  induction T with
  | nil => exact A
  | @hold x e w l H T IH =>
    apply IH
    · change ItemNineAt (params d s) I (readPC d C (rawNext s x e)).2
        (item9Read (params d s) (selectBytes d (rawNext s x e C.root)))
      rw [H.1,item9_read_congr (params d s) _ _ H.2]
      exact A
    · exact D
  | @credit x e w l H T IH =>
    apply IH
    · exact math_credit d C x e I B XL XR R A H
        (D ((readPC d C x).2,tok d C x 0) (by simp))
    · intro r M
      exact D r (List.mem_cons_of_mem _ M)

/-- Splitting the actual mark tape also splits its actual log.
    This is useful to identify the old file at the issued WRITE
    and again at its matching ACK. -/
theorem split_ack (d : Sheet) (C : Chart h) (x : Raw s n)
    (u v : List (Fin n)) (l : List Receipt)
    (T : AckTape d C x (u++v) l) :
    ∃ a b,l=a++b ∧ AckTape d C x u a ∧ AckTape d C (rawRun x u) v b := by
  induction u generalizing x l with
  | nil => exact ⟨[],l,rfl,.nil x,T⟩
  | cons e u IH =>
    cases T with
    | hold H T =>
      obtain ⟨a,b,E,A,B⟩ := IH (rawNext s x e) _ T
      exact ⟨a,b,E,.hold H A,B⟩
    | credit H T =>
      obtain ⟨a,b,E,A,B⟩ := IH (rawNext s x e) _ T
      exact ⟨_,b,by rw [E]; rfl,.credit H A,B⟩

theorem ack_same_opcode_file (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l)
    (H : (readPC d C (rawRun x w)).2=(readPC d C x).2) :
    l=[] ∧ file d C (rawRun x w)=file d C x := by
  have Count := tape_count d C x w l T
  unfold logicalPC at Count
  rw [H] at Count
  have Z : l.length=0 := by omega
  have E := List.length_eq_zero_iff.mp Z
  subst l
  exact ⟨rfl,tape_replay d C x w [] T⟩

/-- If an actual mark is a credit, the tape cannot classify it as
    a hold: its logical instruction really increases. -/
theorem ack_credit_head (d : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) (w : List (Fin n)) (l : List Receipt)
    (T : AckTape d C x (e::w) l) (A : CreditAt d C x e) :
    ∃ tail,l=((readPC d C x).2,tok d C x 0)::tail ∧
      AckTape d C (rawNext s x e) w tail := by
  cases T with
  | hold H T =>
    have N := preview_logical A.2.2.2.2.2.2.2.1
    rw [H.1] at N
    omega
  | credit H T => exact ⟨_,rfl,T⟩

/-- Exact source initialization from the actual successful ACQ
    consume. Old payload provenance is supplied by FRESH1. -/
theorem math_seed_from_acq (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (I : ItemNineInputs)
    (Shape : ReverseWait d C x 0)
    (O : (readPC d C x).2=acqOp (params d s))
    (Tag : (tok d C x 0).tag=3)
    (Match : (tok d C x 0).opcode=acqOp (params d s))
    (Live : (tok d C x 0).fault=false) (ND : (tok d C x 0).outcome≠1)
    (M : 0<(params d s).digits)
    (PC : readPC d C (rawNext s x (door C))=(1,cmpOp (params d s)))
    (H : item9Read (params d s) (rootBytes d C (rawNext s x (door C))) .heads=I.heads)
    (K : item9Read (params d s) (rootBytes d C (rawNext s x (door C))) .indices=I.indices) :
    ItemNineAt (params d s) I (readPC d C (rawNext s x (door C))).2
      (item9Read (params d s) (rootBytes d C (rawNext s x (door C)))) := by
  let p := params d s
  let v := rootBytes d C x
  let u := rootBytes d C (rawNext s x (door C))
  let t := tok d C x 0
  have E := door_file d C x N ((cached_fibre d N hh Q F).mask x X)
  have Z := item9_acq_zero_cmp p v t Shape.1.1 O Tag Match Live ND
  have B := congrFun (item9_read_congr p u
    ((liftSourcePatch p (source p v t).1).apply v) E) .input
  rw [PC]
  exact item9_seed p I u M H K (B.trans Z)

/-- At the *actual* SEAL source issue, the descriptor is semantic.
    In particular both low bits are the strict comparisons of the
    UPDATED output distances, not the input comparison trits. -/
theorem semantic_seal_descriptor (p : Params) (I : ItemNineInputs)
    (v : BitVec p.w) (B : 2≤p.beta) (R : p.radius<p.beta^p.digits)
    (A : ItemNineAt p I (sealOp p) (item9Read p v)) :
    ReportSealDescriptor.descriptor p v=
      ReportCommitValue.descriptor I.prior p.radius
        (updateDist p.radius I.leftRoot I.left)
        (updateDist p.radius I.rightRoot I.right) := by
  obtain ⟨IX,OUT⟩ := item9_at_seal p I v A
  have C0 := emitted_complete p.beta p.digits p.radius I.left I.leftRoot B R
  have C2 := emitted_complete p.beta p.digits p.radius I.right I.rightRoot B R
  have S : ReportWriterPayload.capturedSelector p v=I.prior := by
    change item9Read p v .indices/2%2=I.indices/2%2
    rw [IX]
  have C : ReportSealDescriptor.comparisonFile p v=item9Out p I p.digits := OUT
  -- CHECK: item9_out_bounds is private in ReportByteRows; the public
  -- export immediately below this code block exposes its projections.
  have F := item9_out_components p I p.digits B
  unfold ReportSealDescriptor.descriptor ReportCommitValue.descriptor
  dsimp only
  rw [S,C,F.1,F.2]
  change 4*(2*I.prior+(1-I.prior))+
    2*((item9Left p I p.digits).outCmp==1).toNat+
    ((item9Right p I p.digits).outCmp==1).toNat=_
  have L : ((item9Left p I p.digits).outCmp==1)=
      decide (updateDist p.radius I.leftRoot I.left<p.radius) := by
    by_cases H : updateDist p.radius I.leftRoot I.left<p.radius
    · have E : (item9Left p I p.digits).outCmp=1 := C0.2.mpr H
      simp [E,H]
    · have E : (item9Left p I p.digits).outCmp≠1 := fun E=>H (C0.2.mp E)
      simp [E,H]
  have U : ((item9Right p I p.digits).outCmp==1)=
      decide (updateDist p.radius I.rightRoot I.right<p.radius) := by
    by_cases H : updateDist p.radius I.rightRoot I.right<p.radius
    · have E : (item9Right p I p.digits).outCmp=1 := C2.2.mpr H
      simp [E,H]
    · have E : (item9Right p I p.digits).outCmp≠1 := fun E=>H (C2.2.mp E)
      simp [E,H]
  rw [L,U]

end L4.ReportItemNineTrace

namespace L4.ReportItemNineTrace
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows ReportDigitArithmetic ReportDigitWord ReportStaticSpacing
open ReportIndexedSourcePrefix

variable {s n : Nat} {h : Fin n→Bool}

def snapshotInputs (d : Sheet) (C : Chart h) (b : Raw s n) : ItemNineInputs :=
  let p := params d s
  let bytes := fun i=>selectBytes d (b i)
  ⟨reportValue p bytes C.root true,
    reportValue p bytes (nextAt C.root (C.a+C.b)) false,
    item9Read p (bytes C.root) .heads,item9Read p (bytes C.root) .indices⟩

/-- The exact consumer projection of the reported checked two-half
    ledger, after applying the actual held reader word frames.
    It says ONLY what each old healthy D contains. No arithmetic
    output or final bank equality is a premise. -/
def SnapshotReceipts (d : Sheet) (C : Chart h) (b : Raw s n)
    (l : List Receipt) : Prop :=
  let p := params d s
  let bytes := fun i=>selectBytes d (b i)
  ∀ r∈l,∀ j,j<p.digits→
    (r.1=cmpOp p+j ∨ r.1=readOp p+j) →
      r.2.payload/2^ReportByteRows.d p=selectedFile p bytes C.root true j ∧
      r.2.payload%2^ReportByteRows.d p=selectedFile p bytes (nextAt C.root (C.a+C.b)) false j

theorem snapshot_receipts_to_math (d : Sheet) (C : Chart h) (b : Raw s n)
    (l : List Receipt) (B : 2≤(params d s).beta)
    (A : SnapshotReceipts d C b l) :
    ReadReceipts (params d s) (snapshotInputs d C b) l := by
  intro r M j J Op
  obtain ⟨L,R⟩ := A r M j J Op
  exact ⟨L.trans (radixDigit_reportValue _ _ _ true j B J).symm,
    R.trans (radixDigit_reportValue _ _ _ false j B J).symm⟩

theorem snapshot_bounds (d : Sheet) (C : Chart h) (b : Raw s n)
    (B : 2≤(params d s).beta) :
    let p := params d s
    let I := snapshotInputs d C b
    I.left<p.beta^p.digits ∧ I.right<p.beta^p.digits := by
  let p := params d s
  let bytes := fun i=>selectBytes d (b i)
  change reportValue p bytes C.root true<p.beta^p.digits ∧
    reportValue p bytes (nextAt C.root (C.a+C.b)) false<p.beta^p.digits
  exact ⟨reportValue_lt p bytes C.root true B,
    reportValue_lt p bytes (nextAt C.root (C.a+C.b)) false B⟩

end L4.ReportItemNineTrace

namespace L4.ReportItemNineTrace
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportOwnerAcquireReturn ReportIndexedSourcePrefix

variable {s n : Nat} {h : Fin n→Bool}

theorem no_restart_append (d : Sheet) (C : Chart h) (x : Raw s n)
    (u v : List (Fin n)) (A : NoRestartTape d C x u)
    (B : NoRestartTape d C (rawRun x u) v) :
    NoRestartTape d C x (u++v) := by
  induction u generalizing x with
  | nil => exact B
  | cons e u IH =>
    exact ⟨A.1,IH (rawNext s x e) A.2 B⟩

theorem ack_append (d : Sheet) (C : Chart h) (x : Raw s n)
    (u v : List (Fin n)) (a b : List Receipt)
    (A : AckTape d C x u a) (B : AckTape d C (rawRun x u) v b) :
    AckTape d C x (u++v) (a++b) := by
  induction A with
  | nil => exact B
  | hold H T IH => exact .hold H (IH B)
  | credit H T IH => exact .credit H (IH B)

end L4.ReportItemNineTrace

import Leader.L4.ReportFastFreshReset
import Leader.L4.ReportFastAcqWins
import Leader.L4.ReportArithmeticLaunch
import Leader.L4.ReportArithmeticRootCredit
import Leader.L4.ReportIndexedCurrentWait
import Leader.L4.ReportIndexedNonfault
import Leader.L4.ReportItemNineActualPublication
import Leader.L4.ReportSealStagedBank

namespace L4.ReportFastPostACQ
noncomputable section
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportPrelaunchRank
open ReportByteRows ReportRawProjection ReportOwnerIssueControl
open ReportOwnerForwardControl ReportOwnerReverseControl
open ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerCommandRail ReportOwnerAcquireReturn
open ReportOwnerIndexedFlight ReportIndexedCurrentWait
open ReportIndexedNonfault ReportIndexedSourcePrefix
open ReportArithmeticLaunch ReportArithmeticRootCredit
open ReportGoodEightCut ReportLeaseOwner ReportLeaseGrants
open ReportItemNineTrace ReportItemNineStaging ReportItemNineAdapters
open ReportItemNineCmpSeed ReportItemNinePublication
open ReportAcqExtract
open ReportGenerationAncestry (centre)
open ReportOwnerAcquireProvenance (BeforeConsume NoConsume)

set_option maxRecDepth 16000
set_option maxHeartbeats 16000000
variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n→Prop}

structure Context (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) (r : Owner h) where
  N : 1<n
  Spos : 0<s
  fibre : Fibre (h:=h) d Q
  issue : Raw s n
  first : FirstCut d hh Q G issue
  legal : LegalIssue d (charter G r) issue
  pc : readPC d (charter G r) issue=(1,acqOp (params d s))
  flight : List (Fin n)
  before : BeforeConsume d (charter G r)
    (rawNext s issue (door (charter G r))) flight
  tag : (tok d (charter G r)
    (rawRun (rawNext s issue (door (charter G r))) flight) 0).tag=3
  good : (tok d (charter G r)
    (rawRun (rawNext s issue (door (charter G r))) flight) 0).outcome≠1
  left : (params d s).digits≤(charter G r).a
  mid : (params d s).digits≤(charter G r).b
  right : (params d s).digits≤(charter G r).L-
    ((charter G r).a+(charter G r).b)

variable {d : Sheet} {hh : ∃ i,h i=true} {G : GapInput h} {r : Owner h}

abbrev Context.chart (_A : Context (s:=s) d hh Q G r) := charter G r
abbrev Context.p (_A : Context (s:=s) d hh Q G r) := params d s

def Context.old (A : Context d hh Q G r) : Raw s n :=
  rawRun (rawNext s A.issue (door A.chart)) A.flight

def Context.base (A : Context d hh Q G r) : Raw s n :=
  rawNext s A.old (door A.chart)

def Context.inputs (A : Context d hh Q G r) : ItemNineInputs :=
  snapshotInputs d A.chart A.base

theorem Context.digit (A : Context d hh Q G r) : 0<A.p.digits :=
  ReportPrelaunchDoorProducer.digits_positive d A.Spos

theorem Context.beta (A : Context d hh Q G r) : 2≤A.p.beta :=
  (actual_params_fit d A.Spos).1

theorem Context.radius (A : Context d hh Q G r) :
    A.p.radius<A.p.beta^A.p.digits :=
  (actual_params_fit d A.Spos).2

theorem Context.bounds (A : Context d hh Q G r) :
    A.inputs.left<A.p.beta^A.p.digits ∧ A.inputs.right<A.p.beta^A.p.digits :=
  snapshot_bounds d A.chart A.base A.beta

structure SeedInfo (A : Context d hh Q G r) : Prop where
  first : FirstCut d hh Q G A.base
  serial : StrongSerial d A.chart A.base
  legal : LegalIssue d A.chart A.base
  pc : readPC d A.chart A.base=(1,cmpOp A.p)
  post : PostAcqPC A.p (readPC d A.chart A.base)
  zero : item9Read A.p (rootBytes d A.chart A.base) .input=0
  math : ItemNineAt A.p A.inputs (readPC d A.chart A.base).2
    (item9Read A.p (rootBytes d A.chart A.base))

theorem seed_info (A : Context d hh Q G r) : SeedInfo A := by
  let C := A.chart
  let p := A.p
  obtain ⟨X,R,O,Match,Live,_⟩ :=
    ReportOwnerAcquireProvenance.from_genuine_issue d C hh G A.fibre A.N
      A.issue A.first.1.1.1 A.legal A.pc A.digit A.flight A.before A.tag A.good
  have ACK := raw_acq_consume_six d C hh G A.fibre A.N A.old X R O Match Live A.good A.digit
  have PC : readPC d C A.base=(1,cmpOp p) := ACK.2.2.1
  have Legal : LegalIssue d C A.base := by
    refine ⟨?_,ACK.2.1⟩
    rw [PC]
    change cmpOp p≤commitOp p
    unfold cmpOp commitOp
    omega
  have Post : PostAcqPC p (readPC d C A.base) := by
    rw [PC]
    refine ⟨.inl rfl,Nat.le_refl _,?_⟩
    unfold cmpOp commitOp
    omega
  have F1 := first_cut_closed d A.N hh G A.fibre A.digit
    A.issue (door C) A.first
  have F2 := first_cut_run d A.N hh G A.fibre A.digit
    (rawNext s A.issue (door C)) F1 A.flight
  have F3 := first_cut_closed d A.N hh G A.fibre A.digit
    A.old (door C) F2
  have Zero := raw_acq_consume_zero_cmp d C A.N hh A.fibre
    A.old X R O A.tag Match Live A.good
  refine ⟨F3,seed_after_acq d C A.base ACK.2.1 PC,Legal,PC,Post,Zero,?_⟩
  rw [PC]
  exact item9_seed p A.inputs _ A.digit rfl rfl Zero

def Stop (A : Context d hh Q G r) (x : Raw s n) : Prop :=
  readPC d A.chart x=(1,sealOp A.p)

def Active (A : Context d hh Q G r) (x : Raw s n) : Prop :=
  IndexedOp A.p (readPC d A.chart x).2

/-- Count the logical credits, not raw opcode differences. -/
def commandIndex (A : Context d hh Q G r) (x : Raw s n) : Nat :=
  logicalPC d A.chart x-cmpOp A.p

/-- The source arithmetic state is ItemNineAt; the physical staged
    prefix consists ONLY of WRITE ordinals strictly below current PC.
    No claim about not-yet-credited offsets. -/
def StagedPrefix (A : Context d hh Q G r) (x : Raw s n) : Prop :=
  ∀ j : Fin A.p.digits,
    logical A.p.digits (writeOp A.p+j.val)<logicalPC d A.chart x →
    reportDigitPair A.p
      (selectBytes d (x (nextAt (centre A.chart) j.val))) (1-A.inputs.prior)=
      BitVec.ofNat (2*ReportByteRows.d A.p) (item9Send A.p A.inputs j.val)

/-- All live packets are some, never the absorbing poisoned none.
    At ISSUE there is no packet. At WAIT the actual packet carries
    the full current accumulator, not just the matching opcode. -/
def Pose (A : Context d hh Q G r) (x : Raw s n) : Prop :=
  LegalIssue d A.chart x ∨
    (∃ k a, ReportOwnerIndexedFlight.FState d A.chart (readPC d A.chart x).2 x k (some a)) ∨
    (∃ k a, ReportOwnerIndexedFlight.DState d A.chart (readPC d A.chart x).2 x k (some a))

structure Inv (A : Context d hh Q G r) (x : Raw s n) : Prop where
  trace : ∃ w : List (Fin n), ∃ l : List Receipt,
    x=rawRun A.base w ∧ NoRestartTape d A.chart A.base w ∧ AckTape d A.chart A.base w l
  first : FirstCut d hh Q G x
  serial : StrongSerial d A.chart x
  post : PostAcqPC A.p (readPC d A.chart x)
  region : Stop A x ∨ Active A x
  math : ItemNineAt A.p A.inputs (readPC d A.chart x).2
    (item9Read A.p (rootBytes d A.chart x))
  stage : StagedPrefix A x
  pose : Pose A x

theorem issue_of_phase_one (A : Context d hh Q G r) (x : Raw s n)
    (S : StrongSerial d A.chart x) (P : (readPC d A.chart x).1=1) :
    LegalIssue d A.chart x := by
  rcases S.1 with I|⟨k,I⟩|⟨k,I⟩
  · exact I
  · have E := I.1.1
    omega
  · have E := I.1.1
    omega

theorem snapshots (A : Context d hh Q G r) (w : List (Fin n))
    (l : List Receipt) (NR : NoRestartTape d A.chart A.base w)
    (T : AckTape d A.chart A.base w l) :
    SnapshotReceipts d A.chart A.base l := by
  have S := seed_info A
  exact snapshots_for_charter d A.N hh G A.fibre A.digit
    (ReportWriteRailSupplier.rail_supplier d A.N hh G A.fibre A.digit)
    r A.issue A.first.1.1.1 A.flight w l A.left A.right A.legal A.pc
    A.first.1.2 A.before A.tag A.good S.first S.legal NR T

theorem math_at (A : Context d hh Q G r) (w : List (Fin n))
    (l : List Receipt) (NR : NoRestartTape d A.chart A.base w)
    (T : AckTape d A.chart A.base w l) :
    ItemNineAt A.p A.inputs (readPC d A.chart (rawRun A.base w)).2
      (item9Read A.p (rootBytes d A.chart (rawRun A.base w))) := by
  exact math_run d A.chart A.inputs A.beta A.bounds.1 A.bounds.2 A.radius
    A.base w l T (seed_info A).math
    (snapshot_receipts_to_math d A.chart A.base l A.beta (snapshots A w l NR T))

theorem index_count (A : Context d hh Q G r) (w : List (Fin n))
    (l : List Receipt) (T : AckTape d A.chart A.base w l) :
    commandIndex A (rawRun A.base w)=l.length := by
  have E := tape_count d A.chart A.base w l T
  have P : logicalPC d A.chart A.base=cmpOp A.p := by
    unfold logicalPC
    rw [(seed_info A).pc]
    exact logical_cmp A.p
  rw [P] at E
  unfold commandIndex
  omega

/-- Arbitrary prefix version of ReportItemNineStaging.staged_at_seal.
    Use the existing physical WRITE at current-cut theorem; it has
    already done the suffix frame argument. -/
theorem staged_prefix (A : Context d hh Q G r) (w : List (Fin n))
    (l : List Receipt) (NR : NoRestartTape d A.chart A.base w)
    (T : AckTape d A.chart A.base w l) :
    StagedPrefix A (rawRun A.base w) := by
  let C := A.chart
  let p := A.p
  have S := seed_info A
  intro j Past
  have Start : logicalPC d C A.base=cmpOp p := by
    unfold logicalPC
    rw [S.pc]
    exact logical_cmp p
  have Count := tape_count d C A.base w l T
  rw [Start] at Count
  have Order := tape_order d C A.base w l T
  rw [Start] at Order
  have WO := ReportSealStagedBank.write_ordinal p j
  have J : p.digits+1+2*j.val<l.length := by
    change logical p.digits (writeOp p+j.val)<logicalPC d C (rawRun A.base w) at Past
    omega
  obtain ⟨q,M,Log⟩ := ordered_complete p (cmpOp p) l Order _ J
  have Op : q.1=writeOp p+j.val :=
    ReportSealStagedBank.logical_injective p.digits _ _ (Log.trans WO.symm)
  obtain ⟨pre,fly,post,f,W,Seg,Hit,Value⟩ :=
    ReportWriteACK.receipt_write_at_current_cut d A.N hh G A.fibre A.digit
      r j (Nat.lt_of_lt_of_le j.isLt A.mid) A.base S.first.1.1.1
      S.legal S.serial S.post w NR l T q M Op
  have W' : w=pre++((door C::fly)++door C::post) := by
    rw [W,List.append_assoc]
  have NP := no_restart_prefix d C A.base pre _ (W' ▸ NR)
  obtain ⟨la,lb,_,TA,_⟩ := split_ack d C A.base pre _ l (W' ▸ T)
  have Math := math_at A pre la NP TA
  -- CHECK: ReportIndexedFlightContract.lean:19–31, IssuedSegment's second projection is the full issue PC.
  rw [Seg.2.1] at Math
  have Send := item9_at_write p A.inputs (rootBytes d C (rawRun A.base pre))
    j.val j.isLt Math
  have Cap := (raw_postacq_run d C hh A.fibre A.N A.digit
    A.base pre S.first.1.1.1 S.post NP).2.2
  have Prior : acqCaptureIndex p (selectBytes d (rawRun A.base pre C.root))/2%2=
      A.inputs.prior := congrArg (fun z : Nat=>z/2%2) Cap
  -- CHECK: ReportItemNineTrace.snapshotInputs and ReportByteRows.ItemNineInputs.prior are definitionally the captured index /2%2.
  rw [Prior] at Value
  exact Value.trans (congrArg (BitVec.ofNat (2*ReportByteRows.d p)) Send)

/-- Current packet provenance from the same literal tape. For WRITE,
    instantiate the permit at every actual old departure from the
    original successful ACQ, not from a hypothesis about its future ACK. -/
theorem live_pose (A : Context d hh Q G r) (w : List (Fin n))
    (NR : NoRestartTape d A.chart A.base w)
    (S : StrongSerial d A.chart (rawRun A.base w))
    (PC : PostAcqPC A.p (readPC d A.chart (rawRun A.base w)))
    (Region : Stop A (rawRun A.base w) ∨ Active A (rawRun A.base w)) :
    Pose A (rawRun A.base w) := by
  let C := A.chart
  let p := A.p
  let x := rawRun A.base w
  by_cases P : (readPC d C x).1=1
  · exact .inl (issue_of_phase_one A x S P)
  have Phase : (readPC d C x).1=2 := PC.1.resolve_left P
  have Range : IndexedOp p (readPC d C x).2 := by
    rcases Region with End|R
    · exact (P (congrArg Prod.fst End)).elim
    · exact R
  let op := (readPC d C x).2
  have AtPC : readPC d C x=(2,op) := Prod.ext Phase rfl
  have B := seed_info A
  obtain ⟨pre,fly,c,Eq,Legal,LaunchPC,Seed,No,Walk,At⟩ :=
    current_walk_from_issue d C A.N hh G A.fibre A.digit A.base
      B.first.1.1.1 B.legal w op Range AtPC
  have NRpre := no_restart_prefix d C A.base pre (door C::fly) (Eq ▸ NR)
  let launch := rawRun A.base pre
  let start := rawNext s launch (door C)
  let sent := ReportIndexedLaunchData.concreteSeed p (selectBytes d (launch C.root)) op
  have Healthy : CursorLive c := by
    by_cases R : op<writeOp p
    · exact reader_walk_live d C op R start sent fly c Walk
    · exact walk_live d C op start sent fly c Walk
        (write_permit_after_acq d hh G A.fibre A.N r A.issue A.first.1.1.1
          A.legal A.pc A.first.1.2 A.digit A.flight A.before A.tag A.good
          pre NRpre op (Nat.le_of_not_gt R) Range.2)
  cases c with
  | forward k q =>
    obtain ⟨a,E⟩ := Healthy
    subst q
    exact .inr (.inl ⟨k,a,At⟩)
  | backward k q =>
    obtain ⟨a,E⟩ := Healthy
    subst q
    exact .inr (.inr ⟨k,a,At⟩)

theorem of_tape (A : Context d hh Q G r) (w : List (Fin n))
    (l : List Receipt) (NR : NoRestartTape d A.chart A.base w)
    (T : AckTape d A.chart A.base w l)
    (R : Stop A (rawRun A.base w) ∨ Active A (rawRun A.base w)) :
    Inv A (rawRun A.base w) := by
  have B := seed_info A
  have C := first_cut_run d A.N hh G A.fibre A.digit A.base B.first w
  have S := (strong_run d A.chart A.N hh G A.fibre A.digit
    A.base B.first.1.1.1 B.serial w).2.1
  have P := (raw_postacq_run d A.chart hh A.fibre A.N A.digit A.base w
    B.first.1.1.1 B.post NR).2.1
  exact ⟨⟨w,l,rfl,NR,T⟩,C,S,P,R,math_at A w l NR T,
    staged_prefix A w l NR T,live_pose A w NR S P R⟩

theorem initial (A : Context d hh Q G r) : Inv A A.base := by
  have B := seed_info A
  apply of_tape A [] [] trivial (.nil _)
  right
  unfold Active
  change IndexedOp A.p (readPC d A.chart A.base).2
  rw [B.pc]
  exact ⟨Nat.le_refl _,by
    have := A.digit
    unfold cmpOp sealOp
    omega⟩

theorem active_pos (A : Context d hh Q G r) (x : Raw s n)
    (R : Active A x) : (readPC d A.chart x).2≠0 := by
  have L := R.1
  unfold cmpOp at L
  omega

theorem active_not_stop (A : Context d hh Q G r) (x : Raw s n)
    (R : Active A x) : ¬Stop A x := by
  intro E
  have U := R.2
  rw [E] at U
  exact (Nat.lt_irrefl _ U)

theorem root_credit (A : Context d hh Q G r) (x : Raw s n)
    (H : Inv A x) (R : Active A x) (a : IndexedData)
    (D : ReportOwnerIndexedFlight.DState d A.chart (readPC d A.chart x).2 x 0 (some a)) :
    CreditAt d A.chart x (door A.chart) ∧
      (readPC d A.chart (rawNext s x (door A.chart))).2≠0 := by
  have Match : (tok d A.chart x 0).opcode=(readPC d A.chart x).2 := by
    rw [D.packet]
    rfl
  have Live : (tok d A.chart x 0).fault=false := by rw [D.packet]; rfl
  have Good : (tok d A.chart x 0).outcome≠1 := by
    rw [D.packet]
    change (0 : Nat)≠1
    decide
  have U : (readPC d A.chart x).2<commitOp A.p := by
    have E := R.2
    unfold sealOp commitOp at *
    omega
  exact healthy_root_credit d A.chart A.N hh G A.fibre A.digit x
    H.first.1.1.1 H.serial H.post A.inputs A.beta H.math D.shape Match Live Good U

theorem reverse_at_root (A : Context d hh Q G r) (x : Raw s n)
    (k : Nat) (a : IndexedData)
    (D : ReportOwnerIndexedFlight.DState d A.chart (readPC d A.chart x).2 x k (some a))
    (T : (tok d A.chart x 0).tag=3) : k=0 := by
  by_cases E : k=0
  · exact E
  · rw [D.shape.2.2 0 A.chart.positive] at T
    simp [backTag,show 0<k by omega] at T

/-- Crucial noncircular lemma. NoRestartTape has NOT yet been
    extended. Source arithmetic and healthy old packet imply the
    next positive opcode before calling any tape theorem on it. -/
theorem nonrestart (A : Context d hh Q G r) (x : Raw s n)
    (H : Inv A x) (R : Active A x) (e : Fin n) :
    (readPC d A.chart (rawNext s x e)).2≠0 := by
  let C := A.chart
  let op := (readPC d C x).2
  have Pos : op≠0 := active_pos A x R
  have X := H.first.1.1.1
  rcases H.pose with I|⟨k,a,F⟩|⟨k,a,D⟩
  · by_cases E : e=door C
    · subst e
      have PC : readPC d C x=(1,op) := Prod.ext I.2.1 rfl
      have Z := (actual_seed d C op R hh G A.fibre A.N x X I PC
        A.inputs A.beta H.math).2
      rw [Z.pc]
      exact Pos
    · have P := (ReportOwnerIssueControl.nondoor_preserves d C hh G A.fibre A.N x X I e E).2
      rw [P]
      exact Pos
  · rcases ReportOwnerIndexedFlight.F_step d C op R hh G A.fibre A.N x X k (some a) F e with
      U|⟨_,U⟩|⟨_,_,U⟩
    all_goals rw [U.pc]; exact Pos
  · by_cases NC : NoConsume d C x e
    · rcases ReportOwnerIndexedFlight.D_step d C op R hh G A.fibre A.N x X k (some a)
        D A.digit e NC with U|⟨j,_,_,U⟩
      all_goals rw [U.pc]; exact Pos
    · have E : e=door C := by
        by_cases J : e=door C
        · exact J
        · exact (NC (.inl J)).elim
      have T : (tok d C x 0).tag=3 := by
        by_cases J : (tok d C x 0).tag=3
        · exact J
        · exact (NC (.inr J)).elim
      have K := reverse_at_root A x k a D T
      subst e k
      exact (root_credit A x H R a D).2

/-- Every real root consume in this active region is a credit,
    including the last WRITE. No claim about SEAL or COMMIT. -/
theorem real_root_ack (A : Context d hh Q G r) (x : Raw s n)
    (H : Inv A x) (R : Active A x) (T : (tok d A.chart x 0).tag=3) :
    CreditAt d A.chart x (door A.chart) := by
  rcases H.pose with I|⟨k,a,F⟩|⟨k,a,D⟩
  · rw [I.2.2 0 A.chart.positive] at T
    contradiction
  · rw [F.shape.2.2 0 A.chart.positive] at T
    unfold frontTag at T
    split at T <;> try contradiction
    split at T <;> contradiction
  · have K := reverse_at_root A x k a D T
    subst k
    exact (root_credit A x H R a D).1

theorem preview_within (p : Params) {a b : Nat}
    (R : IndexedOp p a) (H : PreviewNextOp p.digits a b) :
    cmpOp p≤b ∧ b≤sealOp p := by
  have L := R.1
  have U := R.2
  unfold cmpOp sealOp at *
  cases H <;> omega

theorem hold_index (A : Context d hh Q G r) (x : Raw s n) (e : Fin n)
    (H : HoldAt d A.chart x e) :
    commandIndex A (rawNext s x e)=commandIndex A x := by
  unfold commandIndex logicalPC
  rw [H.1]

theorem credit_index (A : Context d hh Q G r) (x : Raw s n) (e : Fin n)
    (H : Inv A x) (K : CreditAt d A.chart x e) :
    commandIndex A (rawNext s x e)=commandIndex A x+1 := by
  obtain ⟨w,l,E,_,T⟩ := H.trace
  have C := tape_count d A.chart A.base w l T
  have S : logicalPC d A.chart A.base=cmpOp A.p := by
    unfold logicalPC
    rw [(seed_info A).pc]
    exact logical_cmp A.p
  rw [S,←E] at C
  have P := preview_logical K.2.2.2.2.2.2.2.1
  change logicalPC d A.chart (rawNext s x e)=logicalPC d A.chart x+1 at P
  unfold commandIndex
  omega

/-- Same-tape induction step, stopped on entering the clean SEAL issue.
    Credit and hold are mutually exclusive (preview_logical).
    At credit the new phase is 1; hence the target is an empty issue
    by StrongSerial, even at the last index. -/
theorem step (A : Context d hh Q G r) (x : Raw s n) (H : Inv A x)
    (R : Active A x) (e : Fin n) :
    Inv A (rawNext s x e) ∧
      (HoldAt d A.chart x e ∨ CreditAt d A.chart x e) := by
  let C := A.chart
  let y := rawNext s x e
  have NZ := nonrestart A x H R e
  have Class := mark_credit_or_hold d C A.N hh G A.fibre A.digit x
    H.first.1.1.1 H.serial H.post e NZ
  have Region : Stop A y ∨ Active A y := by
    rcases Class with Hold|Credit
    · right
      unfold Active
      rw [Hold.1]
      exact R
    · have Next := Credit.2.2.2.2.2.2.2.1
      have Phase := Credit.2.2.2.2.2.2.1
      have B := preview_within A.p R Next
      by_cases E : (readPC d C y).2=sealOp A.p
      · exact .inl (Prod.ext Phase E)
      · right
        change IndexedOp A.p (readPC d C y).2
        change cmpOp A.p≤(readPC d C y).2 ∧ (readPC d C y).2≤sealOp A.p at B
        exact ⟨B.1,by omega⟩
  obtain ⟨w,l,Eq,NR,T⟩ := H.trace
  have RW : rawRun A.base (w++[e])=y := by
    rw [ShortOwnerEpochJS.raw_snoc,←Eq]
  have NRT : NoRestartTape d C A.base (w++[e]) :=
    no_restart_append d C A.base w [e] NR
      (show NoRestartTape d C (rawRun A.base w) [e] from Eq ▸ ⟨NZ,trivial⟩)
  refine ⟨?_,Class⟩
  rcases Class with Hold|Credit
  · have J : AckTape d C x [e] [] := .hold Hold (.nil _)
    have T' := ack_append d C A.base w [e] l [] T (Eq ▸ J)
    change Inv A y
    rw [←RW]
    exact of_tape A _ _ NRT T' (RW.symm ▸ Region)
  · have J : AckTape d C x [e] [((readPC d C x).2,tok d C x 0)] :=
      .credit Credit (.nil _)
    have T' := ack_append d C A.base w [e] l _ T (Eq ▸ J)
    change Inv A y
    rw [←RW]
    exact of_tape A _ _ NRT T' (RW.symm ▸ Region)

/-- Explicit tape theorem: a first-hit prefix is not required to
    remain in the arithmetic region after its endpoint. -/
inductive UntilSeal (A : Context d hh Q G r) : List (Fin n) → Prop where
  | nil : UntilSeal A []
  | snoc {w : List (Fin n)} (e : Fin n) :
    UntilSeal A w → Active A (rawRun A.base w) → UntilSeal A (w++[e])

theorem until_invariant (A : Context d hh Q G r) (w : List (Fin n))
    (T : UntilSeal A w) : Inv A (rawRun A.base w) := by
  induction T with
  | nil => exact initial A
  | snoc e T R IH =>
    rw [ShortOwnerEpochJS.raw_snoc]
    exact (step A _ IH R e).1

theorem at_last_credit (A : Context d hh Q G r) (x : Raw s n) (e : Fin n)
    (H : Inv A x) (R : Active A x) (K : CreditAt d A.chart x e)
    (Last : commandIndex A x+1=3*A.p.digits) :
    Stop A (rawNext s x e) := by
  have L := credit_index A x e H K
  have Next := K.2.2.2.2.2.2.2.1
  have B := preview_within A.p R Next
  obtain ⟨w,l,E,_,T⟩ := H.trace
  have Count := tape_count d A.chart A.base w l T
  have Start : logicalPC d A.chart A.base=cmpOp A.p := by
    unfold logicalPC
    rw [(seed_info A).pc]
    exact logical_cmp A.p
  rw [Start,←E] at Count
  have P := preview_logical Next
  change logicalPC d A.chart (rawNext s x e)=logicalPC d A.chart x+1 at P
  have J : logicalPC d A.chart (rawNext s x e)=sealOp A.p := by
    unfold commandIndex at Last
    simp only [cmpOp, sealOp] at Count Last ⊢
    omega
  have Op : (readPC d A.chart (rawNext s x e)).2=sealOp A.p :=
    ReportSealStagedBank.logical_injective A.p.digits _ _
      (J.trans (logical_seal A.p).symm)
  exact Prod.ext K.2.2.2.2.2.2.1 Op

def floor (A : Context d hh Q G r) : Nat :=
  2*ReportFastFreshReset.commandCap A.chart.L+
    ReportFastFreshReset.resetCost A.chart.L

noncomputable def loopDebt (A : Context d hh Q G r) (x : Raw s n) : Nat :=
  ReportFastFreshReset.serialDebt d A.chart x-floor A

theorem active_logical_lt (A : Context d hh Q G r) (x : Raw s n)
    (R : Active A x) :
    logical A.p.digits (readPC d A.chart x).2<sealOp A.p := by
  have U := R.2
  unfold sealOp at U ⊢
  unfold logical
  split
  · omega
  · split
    · omega
    · omega

theorem serial_cursor (A : Context d hh Q G r) (x : Raw s n)
    (S : StrongSerial d A.chart x) :
    ∃ m : ReportFastFreshReset.Cursor, ReportFastFreshReset.On d A.chart x m := by
  rcases S.1 with I|⟨k,I⟩|⟨k,I⟩
  · exact ⟨.issue,I⟩
  · exact ⟨.fwd k,I⟩
  · exact ⟨.rev k,I⟩

theorem remain_pos (A : Context d hh Q G r) (x : Raw s n)
    (m : ReportFastFreshReset.Cursor) (M : ReportFastFreshReset.On d A.chart x m) :
    0<ReportFastFreshReset.remain d A.chart x m := by
  cases m with
  | issue => simp [ReportFastFreshReset.remain,ReportFastFreshReset.commandCap]
  | fwd k =>
    have K := M.2.1
    simp only [ReportFastFreshReset.remain]
    omega
  | rev k =>
    simp [ReportFastFreshReset.remain]

theorem debt_live (A : Context d hh Q G r) (x : Raw s n)
    (S : StrongSerial d A.chart x) (R : Active A x) :
    floor A<ReportFastFreshReset.serialDebt d A.chart x := by
  let C := A.chart
  let t := A.p.digits
  let B := ReportFastFreshReset.commandCap C.L
  obtain ⟨m,M⟩ := serial_cursor A x S
  have N0 := active_pos A x R
  have Log := active_logical_lt A x R
  unfold sealOp at Log
  have T : 2≤4*t+4-logical t (readPC d C x).2 := by
    change logical t (readPC d C x).2<4*t+3 at Log
    omega
  have Tail := Nat.mul_le_mul_right B T
  have Rem : 0<ReportFastFreshReset.remain d C x m := remain_pos A x m M
  rw [ReportFastFreshReset.serialDebt_on d C x m M]
  unfold ReportFastFreshReset.preDebt
  rw [if_neg (fun H=>N0 H.1)]
  change 2*B+ReportFastFreshReset.resetCost C.L<
    (4*t+4-logical t (readPC d C x).2)*B+
      ReportFastFreshReset.resetCost C.L+ReportFastFreshReset.remain d C x m
  omega

theorem rank_live (A : Context d hh Q G r) (x : Raw s n)
    (S : StrongSerial d A.chart x) (R : Active A x) :
    0<loopDebt A x := by
  have L := debt_live A x S R
  unfold loopDebt
  omega

theorem rank_stop (A : Context d hh Q G r) (x : Raw s n)
    (S : StrongSerial d A.chart x) (R : Stop A x) :
    loopDebt A x=0 := by
  let C := A.chart
  let p := A.p
  have I := issue_of_phase_one A x S (congrArg Prod.fst R)
  have Op : (readPC d C x).2=sealOp p := congrArg Prod.snd R
  unfold loopDebt
  rw [ReportFastFreshReset.serialDebt_on d C x .issue I]
  unfold ReportFastFreshReset.preDebt
  have N : sealOp p≠0 := by unfold sealOp; omega
  rw [Op,if_neg (fun H=>N H.1)]
  change ((4*p.digits+4-logical p.digits (sealOp p))*
      ReportFastFreshReset.commandCap C.L+ReportFastFreshReset.resetCost C.L+
      ReportFastFreshReset.commandCap C.L)-floor A=0
  rw [logical_seal]
  unfold sealOp floor
  rw [show 4*p.digits+4-(4*p.digits+3)=1 by omega,Nat.one_mul]
  change ReportFastFreshReset.commandCap C.L+ReportFastFreshReset.resetCost C.L+
    ReportFastFreshReset.commandCap C.L-
      (2*ReportFastFreshReset.commandCap C.L+ReportFastFreshReset.resetCost C.L)=0
  omega

theorem rank_initial (A : Context d hh Q G r) :
    loopDebt A A.base=3*A.p.digits*ReportFastFreshReset.commandCap A.chart.L := by
  let p := A.p
  let C := A.chart
  let B := ReportFastFreshReset.commandCap C.L
  have S := seed_info A
  have Op : (readPC d C A.base).2=cmpOp p := congrArg Prod.snd S.pc
  have N : cmpOp p≠0 := by unfold cmpOp; omega
  unfold loopDebt
  rw [ReportFastFreshReset.serialDebt_on d C A.base .issue S.legal]
  unfold ReportFastFreshReset.preDebt
  rw [Op,if_neg (fun H=>N H.1)]
  change ((4*p.digits+4-logical p.digits (cmpOp p))*B+
    ReportFastFreshReset.resetCost C.L+B)-floor A=3*p.digits*B
  rw [logical_cmp]
  unfold cmpOp floor
  have E : 4*p.digits+4-(p.digits+3)=3*p.digits+1 := by omega
  rw [E,Nat.add_mul,Nat.one_mul]
  change 3*p.digits*B+B+ReportFastFreshReset.resetCost C.L+B-
    (2*B+ReportFastFreshReset.resetCost C.L)=3*p.digits*B
  omega

theorem not_launch (A : Context d hh Q G r) (x : Raw s n)
    (R : Active A x) (e : Fin n) : ¬Launch d A.chart x e := by
  intro H
  exact active_pos A x R
    (congrArg Prod.snd ((ReportFastFreshReset.issue0_iff d A.chart x).mp H.1))

/-- Exactly the stopped arithmetic observer, on unsteered physical
    rawNext. Nomination is only a mathematical paying label, not
    a scheduler restriction or a change to the raw transition. -/
def Live (A : Context d hh Q G r) (x : Raw s n) (b : Nat) : Prop :=
  Inv A x ∧ Active A x ∧ b=loopDebt A x

theorem live_pos (A : Context d hh Q G r) (x : Raw s n) (b : Nat)
    (H : Live A x b) : 0<b := by
  rw [H.2.2]
  exact rank_live A x H.1.serial H.2.1

theorem clock_step (A : Context d hh Q G r) (x : Raw s n) (b : Nat)
    (H : Live A x b) :
    ∃ q : Fin n, ∀ e : Fin n,
      Stop A (rawNext s x e) ∨
        ∃ b', Live A (rawNext s x e) b' ∧ b'≤b ∧ (e=q → b'<b) := by
  let C := A.chart
  have Rows := ReportPrelaunchDoorProducer.rowCases_cached d C hh G Q A.fibre A.N A.Spos
  obtain ⟨q,Paid⟩ := nominate d C (Cached d hh Q) Rows x H.1.first.1.1.1
  refine ⟨q,fun e=>?_⟩
  have NL := not_launch A x H.2.1 e
  have D := ReportFastFreshReset.serial_step_nonlaunch d C A.N hh G A.fibre
    A.digit x H.1.first.1.1.1 H.1.serial e NL
  have Y := (step A x H.1 H.2.1 e).1
  rcases Y.region with End|R
  · exact .inl End
  · have P0 := debt_live A x H.1.serial H.2.1
    have P1 := debt_live A (rawNext s x e) Y.serial R
    refine .inr ⟨loopDebt A (rawNext s x e),⟨Y,R,rfl⟩,?_,?_⟩
    · rw [H.2.2]
      unfold loopDebt
      change ReportFastFreshReset.serialDebt d C (rawNext s x e) - floor A ≤
        ReportFastFreshReset.serialDebt d C x - floor A
      exact Nat.sub_le_sub_right D.1 _
    · intro E
      have Pay : ReportPrelaunchClock.Paid d C x (rawNext s x e) := by
        subst e
        exact Paid.resolve_left NL
      have Strict : ReportFastFreshReset.serialDebt d A.chart (rawNext s x e) <
          ReportFastFreshReset.serialDebt d A.chart x := D.2 Pay
      rw [H.2.2]
      unfold loopDebt
      omega

theorem arithmetic_mean (A : Context d hh Q G r) :
    Height.IIDExpectedHittingTimeAtMost (rawNext s) (Stop A) A.base
      (n*(3*A.p.digits*ReportFastFreshReset.commandCap A.chart.L)) := by
  have I := initial A
  have B := seed_info A
  have R : Active A A.base := by
    unfold Active
    rw [B.pc]
    exact ⟨Nat.le_refl _,by have := A.digit; unfold cmpOp sealOp; omega⟩
  have L : Live A A.base (loopDebt A A.base) := ⟨I,R,rfl⟩
  have Mean := ResetReturnIID.iid_of_relational_rank (rawNext s) (Stop A)
    (Live A) (live_pos A) (clock_step A) A.base (loopDebt A A.base) (.inr L)
  rw [rank_initial A] at Mean
  exact Mean

theorem arithmetic_budget {t L W : Nat} (W3 : 3≤W) (L3 : L≤3*W) :
    3*t*ReportFastFreshReset.commandCap L≤21*t*W := by
  have B : ReportFastFreshReset.commandCap L≤7*W := by
    unfold ReportFastFreshReset.commandCap
    omega
  calc
    _ ≤ (3*t)*(7*W) := Nat.mul_le_mul_left _ B
    _ = 21*t*W := by rw [show 21=3*7 by decide]; ac_rfl

theorem arithmetic_mean_width (A : Context d hh Q G r)
    (W : Nat) (W3 : 3≤W) (L3 : A.chart.L≤3*W) :
    Height.IIDExpectedHittingTimeAtMost (rawNext s) (Stop A) A.base
      (21*A.p.digits*W*n) := by
  intro k
  have M := arithmetic_mean A k
  have B := Nat.mul_le_mul_left n (arithmetic_budget (t:=A.p.digits) W3 L3)
  rw [Nat.mul_comm n (21*A.p.digits*W)] at B
  exact Nat.le_trans M (Nat.mul_le_mul_right _ B)

theorem literal_tape (A : Context d hh Q G r) (w : List (Fin n))
    (T : UntilSeal A w) :
    NoRestartTape d A.chart A.base w ∧ ∃ l,AckTape d A.chart A.base w l := by
  induction T with
  | nil => exact ⟨trivial,[],.nil _⟩
  | @snoc w e T R IH =>
    let x := rawRun A.base w
    have H := until_invariant A w T
    have NZ := nonrestart A x H R e
    obtain ⟨NR,l,L⟩ := IH
    have NR' := no_restart_append d A.chart A.base w [e] NR
      (show NoRestartTape d A.chart x [e] from ⟨NZ,trivial⟩)
    refine ⟨NR',?_⟩
    rcases (step A x H R e).2 with Hold|Credit
    · exact ⟨l++[],ack_append d A.chart A.base w [e] l [] L (.hold Hold (.nil _))⟩
    · exact ⟨_,ack_append d A.chart A.base w [e] l _ L (.credit Credit (.nil _))⟩

/-- All the committed arithmetic-prefix inputs to the existing
    SEAL/COMMIT continuation.  The quantifier on l is inside the
    fixed original prefix w. -/
theorem seal_handoff (A : Context d hh Q G r) (w : List (Fin n))
    (T : UntilSeal A w) (End : Stop A (rawRun A.base w)) :
    let C := A.chart
    let p := A.p
    let x := rawRun A.base w
    FirstCut d hh Q G A.base ∧ StrongSerial d C A.base ∧
    readPC d C A.base=(1,cmpOp p) ∧
    item9Read p (rootBytes d C A.base) .input=0 ∧
    FirstCut d hh Q G x ∧ StrongSerial d C x ∧ LegalIssue d C x ∧
    readPC d C x=(1,sealOp p) ∧
    ItemNineAt p A.inputs (sealOp p) (item9Read p (rootBytes d C x)) ∧
    (∀ j,j<p.digits→
      reportDigitPair p (selectBytes d (x (nextAt (centre C) j))) (1-A.inputs.prior)=
        BitVec.ofNat (2*ReportByteRows.d p) (item9Send p A.inputs j)) ∧
    ReportSealDescriptor.descriptor p (rootBytes d C x)=
      ReportCommitValue.descriptor A.inputs.prior p.radius
        (ReportDigitArithmetic.updateDist p.radius A.inputs.leftRoot A.inputs.left)
        (ReportDigitArithmetic.updateDist p.radius A.inputs.rightRoot A.inputs.right) ∧
    ∃ l : List Receipt, NoRestartTape d C A.base w ∧ AckTape d C A.base w l ∧
      l.length=3*p.digits ∧ OrderedFrom p (cmpOp p) l ∧
      SnapshotReceipts d C A.base l ∧ WriteCredits d C A.base w l A.inputs.prior := by
  dsimp only
  let C := A.chart
  let p := A.p
  let x := rawRun A.base w
  have B := seed_info A
  have H := until_invariant A w T
  obtain ⟨NR,l,L⟩ := literal_tape A w T
  have Math := H.math
  rw [End] at Math
  have Order := tape_order d C A.base w l L
  unfold logicalPC at Order
  rw [B.pc,logical_cmp] at Order
  refine ⟨B.first,B.serial,B.pc,B.zero,H.first,H.serial,
    issue_of_phase_one A x H.serial (congrArg Prod.fst End),End,Math,?_,?_,?_⟩
  · intro j J
    have W := ReportSealStagedBank.write_ordinal p ⟨j,J⟩
    apply H.stage ⟨j,J⟩
    unfold logicalPC
    rw [End,logical_seal,W]
    change (cmpOp A.p+(A.p.digits+1+2*j))+1 ≤ sealOp A.p
    unfold cmpOp sealOp
    omega
  · exact semantic_seal_descriptor p A.inputs _ A.beta A.radius Math
  · exact ⟨l,NR,L,at_seal_count d C A.base w l (congrArg Prod.snd B.pc)
      (congrArg Prod.snd End) L,Order,snapshots A w l NR L,
      item_nine_write_credits d A.N hh G A.fibre A.digit r A.mid A.base
        B.first.1.1.1 B.legal B.post w NR l L⟩

end
end L4.ReportFastPostACQ


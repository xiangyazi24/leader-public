import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportGoodEightBank
import Leader.L4.ReportSealDescriptor

namespace L4.ReportIndexedSourcePrefix
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerIssueControl ReportOwnerForwardControl ReportOwnerReverseControl
open ReportOwnerForwardLocations ReportOwnerReverseShape ReportOwnerProvenanceTransport
open ReportOwnerDoorProjection ReportPrelaunchDoorLift ReportRawProjection
open ReportOwnerAcquireReturn ReportOwnerCommandRail ReportLeaseStep
open ReportGoodEightCut

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def file (d : Sheet) (C : Chart h) (x : Raw s n) : Nat :=
  drainFile (params d s) (selectBytes d (x C.root))

abbrev Receipt := Nat × Tok

def replay (p : Params) (f : Nat) (l : List Receipt) : Nat :=
  l.foldl (fun v r=>replayAck p v r.1 r.2) f

theorem replay_bound (p : Params) (f : Nat) (l : List Receipt)
    (F : f<2^(19+2*ReportByteRows.d p)) :
    replay p f l<2^(19+2*ReportByteRows.d p) := by
  induction l generalizing f with
  | nil => exact F
  | cons a l IH =>
    exact IH (replayAck p f a.1 a.2) (replayAck_bound p f a.1 a.2)

private theorem file_eq_low (p : Params) (u v : BitVec p.w)
    (H : ∀ i,i<grantBase p→u.getLsbD i=v.getLsbD i) :
    drainFile p u=drainFile p v := by
  change (u.extractLsb' (sourceBase p) (19+2*ReportByteRows.d p)).toNat=
    (v.extractLsb' (sourceBase p) (19+2*ReportByteRows.d p)).toNat
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  apply H
  unfold grantBase sealBase sourceW
  omega

theorem nondoor_file (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (D : e≠door C) :
    file d C (rawNext s x e)=file d C x := by
  by_cases E : e=C.root
  · subst e
    let p := params d s
    let u := selectBytes d (x C.root)
    let v := selectBytes d (x (rightNeighbor C.root))
    apply Eq.trans _ (drain_row_file_left p (h (rightNeighbor C.root)) u v)
    apply file_eq_low
    intro i I
    have W := (raw_low_pair d x C.root N mask i I).1
    rw [C.rootHeader] at W
    exact W
  · have R : C.root≠rightNeighbor e := by
      intro K
      apply D
      unfold door
      rw [K,RearTrace.predecessor_right]
    unfold file
    rw [raw_spectator x e C.root (Ne.symm E) R]

private theorem root_pub (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true
      (selectBytes d (x C.root)) 0 := by
  rw [root_tok,prelaunch_root_decode]

theorem door_file (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i) :
    file d C (rawNext s x (door C))=
      fileAfterSource (params d s) (selectBytes d (x C.root)) (tok d C x 0) := by
  let p := params d s
  let e := door C
  let u := selectBytes d (x e)
  let v := selectBytes d (x C.root)
  rw [root_pub]
  apply Eq.trans _ (indexed_row_source_file p (h e) u v)
  apply file_eq_low
  intro i I
  have R := (raw_low_pair d x e N mask i I).2
  rw [show rightNeighbor e=C.root from RearTrace.right_predecessor C.root,C.rootHeader] at R
  exact R

/-- The actual ACK condition contains the unique old root return
    and the precise logical successor. It is not a service intention. -/
def CreditAt (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  let y := rawNext s x e
  let p := params d s
  e=door C ∧ ReverseWait d C x 0 ∧
    (tok d C x 0).tag=3 ∧
    (tok d C x 0).opcode=(readPC d C x).2 ∧
    (tok d C x 0).fault=false ∧ (tok d C x 0).outcome≠1 ∧
    (readPC d C y).1=1 ∧
    PreviewNextOp p.digits (readPC d C x).2 (readPC d C y).2 ∧
    file d C y=replayAck p (file d C x) (readPC d C x).2 (tok d C x 0)

def HoldAt (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  (readPC d C (rawNext s x e)).2=(readPC d C x).2 ∧
    file d C (rawNext s x e)=file d C x

/-- Exhaustive one-mark classifier in the actual post-ACQ positive
    region, stopped before any restart. This includes the mark
    immediately after a final WRITE; no ACK credit on launch,
    forward hop, terminal turn, reverse hop or foreign mark. -/
theorem mark_credit_or_hold (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (_G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (A : StrongSerial d C x)
    (PC : PostAcqPC (params d s) (readPC d C x)) (e : Fin n)
    (NZ : (readPC d C (rawNext s x e)).2≠0) :
    HoldAt d C x e ∨ CreditAt d C x e := by
  let p := params d s
  let mask := (cached_fibre d N hh Q F).mask x X
  by_cases E : e=door C
  · subst e
    let v := selectBytes d (x C.root)
    let t := publicationToken p true v 0
    let y := rawNext s x (door C)
    have W : readPC d C y=acqSourcePC p v t := (raw_door_final d C x N mask).1
    have J : file d C y=fileAfterSource p v t := by
      rw [door_file d C x N mask,root_pub]
    have N0 : (acqSourcePC p v t).2≠0 := by rwa [←W]
    have hold (P : LegalWait d C x) (T : (tok d C x 0).tag=1 ∨
        (tok d C x 0).tag=2) : HoldAt d C x (door C) := by
      rw [root_pub] at T
      have R := indexed_wait_file p v t P.1 P.2 T
      exact ⟨congrArg Prod.snd (W.trans R.1),J.trans R.2⟩
    rcases A.1 with I|⟨k,I⟩|⟨k,I⟩
    · have Pos : 0<sourceOpcode p v := by
        have L := PC.2.1
        change cmpOp p≤sourceOpcode p v at L
        unfold cmpOp at L
        omega
      have R := indexed_issue_file p v t I.2.1 I.1 Pos N0
      have E := congrArg Prod.snd (W.trans R.1)
      exact .inl ⟨E,J.trans R.2⟩
    · left
      apply hold I.1
      rw [I.2.2 0 C.positive]
      by_cases K : k=0
      · subst k; exact .inr rfl
      · exact .inl (by simp [frontTag,show 0<k by omega])
    · by_cases K : k=0
      · subst k
        have Tag : (tok d C x 0).tag=3 := by rw [I.2.2 0 C.positive]; rfl
        have T : t.tag=3 := by simpa only [root_pub] using Tag
        obtain ⟨Op,Live,Ok,b,B,R⟩ :=
          indexed_credit p v t I.1.1 I.1.2 T N0 digit
        have Z := W.trans R
        right
        refine ⟨rfl,I,Tag,?_,?_,?_,congrArg Prod.fst Z,?_,?_⟩
        · rw [root_pub]; exact Op
        · rw [root_pub]; exact Live
        · rw [root_pub]; exact Ok
        · rw [congrArg Prod.snd Z]; exact B
        · rw [root_pub]
          exact J.trans (source_file_is_replay p v t I.1.1 I.1.2)
      · left
        apply hold I.1
        rw [I.2.2 0 C.positive]
        exact .inl (by simp [backTag,show 0<k by omega])
  · exact .inl ⟨congrArg Prod.snd (raw_nondoor_control d C x e N mask E),
      nondoor_file d C x e N mask E⟩

/-- The log is attached to the actual word, not merely a list of
    opcodes with the right length. Each credit records the complete
    old D at its literal consume mark. -/
inductive AckTape (d : Sheet) (C : Chart h) :
    Raw s n → List (Fin n) → List Receipt → Prop where
  | nil (x) : AckTape d C x [] []
  | hold {x e w l} :
      HoldAt d C x e → AckTape d C (rawNext s x e) w l →
      AckTape d C x (e::w) l
  | credit {x e w l} :
      CreditAt d C x e → AckTape d C (rawNext s x e) w l →
      AckTape d C x (e::w) (((readPC d C x).2,tok d C x 0)::l)

theorem ack_tape_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (A : StrongSerial d C x)
    (PC : PostAcqPC (params d s) (readPC d C x))
    (w : List (Fin n)) (NR : NoRestartTape d C x w) :
    ∃ l, AckTape d C x w l := by
  induction w generalizing x with
  | nil => exact ⟨[],.nil x⟩
  | cons e w IH =>
    obtain ⟨Y,PC',_⟩ := raw_postacq_step d C hh F N x X e PC digit NR.1
    have A' := strong_step d C N hh G F x X A digit e
    obtain ⟨l,T⟩ := IH (rawNext s x e) Y A' PC' NR.2
    rcases mark_credit_or_hold d C N hh G F digit x X A PC e NR.1 with H|H
    · exact ⟨l,.hold H T⟩
    · exact ⟨_,.credit H T⟩

def logicalPC (d : Sheet) (C : Chart h) (x : Raw s n) : Nat :=
  logical (params d s).digits (readPC d C x).2

def OrderedFrom (p : Params) (k : Nat) : List Receipt → Prop
  | [] => True
  | r::l => logical p.digits r.1=k ∧ OrderedFrom p (k+1) l

theorem tape_count (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l) :
    logicalPC d C (rawRun x w)=logicalPC d C x+l.length := by
  induction T with
  | nil => exact (Nat.add_zero _).symm
  | @hold x e w l H T IH =>
    exact IH.trans (by unfold logicalPC; rw [H.1])
  | @credit x e w l H T IH =>
    have E := preview_logical H.2.2.2.2.2.2.2.1
    change logicalPC d C (rawNext s x e)=logicalPC d C x+1 at E
    rw [show rawRun x (e::w)=rawRun (rawNext s x e) w from rfl,
      IH,E,List.length_cons]
    omega

theorem tape_order (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l) :
    OrderedFrom (params d s) (logicalPC d C x) l := by
  induction T with
  | nil => trivial
  | @hold x e w l H T IH =>
    change OrderedFrom (params d s) (logicalPC d C (rawNext s x e)) l at IH
    unfold logicalPC at IH ⊢
    rwa [H.1] at IH
  | @credit x e w l H T IH =>
    have E := preview_logical H.2.2.2.2.2.2.2.1
    change logicalPC d C (rawNext s x e)=logicalPC d C x+1 at E
    refine ⟨rfl,?_⟩
    rw [←E]
    exact IH

theorem tape_replay (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l) :
    file d C (rawRun x w)=replay (params d s) (file d C x) l := by
  induction T with
  | nil => rfl
  | @hold x e w l H T IH =>
    exact IH.trans (by rw [H.2])
  | @credit x e w l H T IH =>
    exact IH.trans (by
      change replay (params d s) (file d C (rawNext s x e)) l=
        replay (params d s)
          (replayAck (params d s) (file d C x) (readPC d C x).2 (tok d C x 0)) l
      rw [H.2.2.2.2.2.2.2.2])

/-- Every log entry has its own actual old prefix and consume.
    The theorem returns the whole CreditAt certificate, not just a
    numerical order or a healthy tag. -/
theorem tape_receipt_origin (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l)
    (r : Receipt) (M : r∈l) :
    ∃ pre post : List (Fin n), w=pre++(door C::post) ∧
      let old := rawRun x pre
      r=((readPC d C old).2,tok d C old 0) ∧ CreditAt d C old (door C) := by
  induction T with
  | nil => simp at M
  | @hold x e w l H T IH =>
    obtain ⟨pre,post,W,R,A⟩ := IH M
    exact ⟨e::pre,post,by rw [W]; rfl,R,A⟩
  | @credit x e w l H T IH =>
    rcases List.mem_cons.mp M with E|M
    · have D := H.1
      subst e
      exact ⟨[],w,rfl,E,H⟩
    · obtain ⟨pre,post,W,R,A⟩ := IH M
      exact ⟨e::pre,post,by rw [W]; rfl,R,A⟩

theorem ordered_range (p : Params) (k : Nat) (l : List Receipt)
    (A : OrderedFrom p k l) (r : Receipt) (M : r∈l) :
    k≤logical p.digits r.1 ∧ logical p.digits r.1<k+l.length := by
  induction l generalizing k with
  | nil => simp at M
  | cons a l IH =>
    rcases List.mem_cons.mp M with E|M
    · subst r
      rw [A.1,List.length_cons]
      omega
    · obtain ⟨L,U⟩ := IH (k+1) A.2 M
      simp only [List.length_cons]
      omega

theorem ordered_complete (p : Params) (k : Nat) (l : List Receipt)
    (A : OrderedFrom p k l) (i : Nat) (I : i<l.length) :
    ∃ r∈l, logical p.digits r.1=k+i := by
  induction l generalizing k i with
  | nil => simp at I
  | cons a l IH =>
    cases i with
    | zero => exact ⟨a,List.mem_cons_self,by simpa using A.1⟩
    | succ i =>
      have L : i<l.length := by simpa using I
      obtain ⟨r,M,E⟩ := IH (k+1) A.2 i L
      exact ⟨r,List.mem_cons_of_mem _ M,by omega⟩

/-- No later receipt duplicates an earlier logical instruction.
    A recursive proof of strict order; no list API from Mathlib. -/
theorem ordered_distinct_head (p : Params) (k : Nat) (a : Receipt)
    (l : List Receipt) (A : OrderedFrom p k (a::l)) (r : Receipt) (M : r∈l) :
    logical p.digits a.1<logical p.digits r.1 := by
  have B := ordered_range p (k+1) l A.2 r M
  rw [A.1]
  omega

/-- Logical opcode is injective in the legal region. In particular
    the alternating READ/WRITE opcodes do not have the same ordinal. -/
theorem logical_injective (m a b : Nat) (A : a<4*m+5)
    (B : b<4*m+5) (E : logical m a=logical m b) : a=b := by
  unfold logical at E
  repeat' first | omega | split at E

theorem logical_cmp (p : Params) :
    logical p.digits (cmpOp p)=cmpOp p := by
  unfold cmpOp logical
  by_cases Z : p.digits=0
  · simp [Z]
  · simp [show p.digits+3<2*p.digits+3 by omega]

theorem logical_seal (p : Params) :
    logical p.digits (sealOp p)=sealOp p := by
  unfold logical sealOp
  simp [show ¬4*p.digits+3<2*p.digits+3 by omega,
    show ¬4*p.digits+3<3*p.digits+3 by omega]

/-- Exact arithmetic prefix count at ISSUE(SEAL) (or WAIT(SEAL)).
    No SEAL or COMMIT has been credited yet. -/
theorem at_seal_count (d : Sheet) (C : Chart h)
    (after : Raw s n) (w : List (Fin n)) (l : List Receipt)
    (A : (readPC d C after).2=cmpOp (params d s))
    (B : (readPC d C (rawRun after w)).2=sealOp (params d s))
    (T : AckTape d C after w l) :
    l.length=3*(params d s).digits := by
  have K := tape_count d C after w l T
  unfold logicalPC at K
  rw [A,B,logical_cmp,logical_seal] at K
  unfold cmpOp sealOp at K
  omega

theorem at_seal_descriptor (d : Sheet) (C : Chart h)
    (after : Raw s n) (w : List (Fin n)) (l : List Receipt)
    (A : (readPC d C after).2=cmpOp (params d s))
    (B : (readPC d C (rawRun after w)).2=sealOp (params d s))
    (T : AckTape d C after w l) :
    let p := params d s
    let f := replay p (file d C after) l
    l.length=3*p.digits ∧
      OrderedFrom p (cmpOp p) l ∧
      ReportSealDescriptor.descriptor p (selectBytes d (rawRun after w C.root))=
        ReportSealDescriptor.descriptor p (indexedImage p f (sealOp p)) := by
  dsimp only
  let p := params d s
  let f := replay p (file d C after) l
  have I := tape_order d C after w l T
  unfold logicalPC at I
  rw [A,logical_cmp] at I
  have L : f<2^(19+2*ReportByteRows.d p) :=
    replay_bound p _ l (indexed_file_bound p _)
  have M := indexed_image_fields p f (sealOp p) L (by unfold sealOp commitOp; omega)
  have Eq := tape_replay d C after w l T
  exact ⟨at_seal_count d C after w l A B T,I,
    ReportSealDescriptor.descriptor_of_file_eq p _ _ (Eq.trans M.1.symm)⟩

end L4.ReportIndexedSourcePrefix

import Leader.L4.ReportReaderACK
import Leader.L4.ReportGoodEightBank
import Leader.L4.ReportReaderDigitsLease
import Leader.L4.ReportDigitWord
import Leader.L4.ReportIndexedSideLease

namespace L4.ReportSnapshotLease
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportOwnerSerial ReportIndexedReadLedger ReportReaderACK
open ReportGrantTimeline ReportReaderDigitsLease ReportReaderSelectorLease
open ReportGoodEightBank ReportGoodEightCut ReportReaderWordLease ReportGenerationAncestry
open ReportDigitWord ReportStaticSpacing ReportLeaseGrants
open ReportOwnerIssueControl ReportIndexedSourcePrefix ReportPrelaunchClock
open ReportOwnerAcquireReturn ReportAcquireAllCaptures ReportIndexedSideLease
open ReportOwnerAcquireProvenance (BeforeConsume)

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

private theorem held_prefix (sheet : Sheet) (a : Fin n) (j : Fin 3)
    (x : Raw s n) (pre post : List (Fin n))
    (H : HeldAlong sheet a j x (pre++post)) : HeldAlong sheet a j x pre := by
  induction pre generalizing x with
  | nil => exact held_start sheet a j _ _ H
  | cons e w IH => exact ⟨H.1,IH _ H.2⟩

private theorem held_header_digits (sheet : Sheet) (N : 1<n)
    (hdr : Fin n) (j : Fin 3) (Side : j=0 ∨ j=2) (sel : Nat)
    (x : Raw s n) (w : List (Fin n)) (Held : HeldAlong sheet hdr j x w)
    (Comp : Compatible (rawGrant sheet x hdr))
    (IsHdr : ∀ pre post, w=pre++post →
      lower sheet (oldHeaders (rows s) (rawRun x pre hdr))=true) :
    rawSelector sheet (rawRun x w) hdr=rawSelector sheet x hdr ∧
    reportDigitPair (params sheet s) (selectBytes sheet (rawRun x w hdr)) sel =
      reportDigitPair (params sheet s) (selectBytes sheet (x hdr)) sel := by
  induction w generalizing x with
  | nil => exact ⟨rfl,rfl⟩
  | cons e w IH =>
    have Head := IsHdr [] (e::w) rfl
    have Dig := reader_grant_protects_digit_pair sheet x e hdr N j Side Head Comp Held.1 sel
    have Sel := reader_grant_protects_selector sheet x e hdr N j Side Comp Held.1
    have Comp' := raw_compatible_step sheet x e hdr (edge_sep N e) Comp
    obtain ⟨L,R⟩ := IH _ Held.2 Comp' (fun pre post E =>
      IsHdr (e::pre) post (congrArg (List.cons e) E))
    exact ⟨L.trans Sel,R.trans Dig⟩

private theorem sample_selected (p : Params) (u : BitVec p.w) (bank : Nat) :
    indexedSample p u bank 0=selectedDigit p bank true u ∧
    indexedSample p u bank 2=selectedDigit p bank false u :=
  ⟨rfl,rfl⟩

private theorem same_sample (p : Params) (u v : BitVec p.w) (bank : Nat) (j : Fin 3)
    (S : j=0 ∨ j=2) (E : reportDigitPair p u bank=reportDigitPair p v bank) :
    indexedSample p u bank j=indexedSample p v bank j := by
  rcases S with rfl|rfl
  · rw [sample_hi,sample_hi,E]
  · rw [sample_lo,sample_lo,E]

theorem observed_word_digit (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Dgt : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (x : Raw s n) (First : FirstCut d hh Q G x)
    (hdr : Fin n) (Hdr : h hdr=true) {len j : Nat} (Gap : Gap h hdr len) (J : j<len)
    (side : Fin 3) (Side : side=0 ∨ side=2) (w : List (Fin n))
    (Held : HeldAlong d hdr side x w) (bank : Nat) (Bank : bank=rawSelector d x hdr) :
    indexedSample (params d s) (selectBytes d (rawRun x w (nextAt hdr j))) bank side =
      selectedFile (params d s) (fun i => selectBytes d (x i)) hdr (side=0) j := by
  have P :
      reportDigitPair (params d s) (selectBytes d (rawRun x w (nextAt hdr j))) bank =
        reportDigitPair (params d s) (selectBytes d (x (nextAt hdr j))) bank := by
    by_cases Z : j=0
    · subst j
      exact (held_header_digits d N hdr side Side bank x w Held (First.1.2 hdr Hdr)
        (fun pre _ _ => ((cached_fibre d N hh Q F).mask _ (cached_run d N hh F x First.1.1.1 pre) hdr).trans Hdr)).2
    · have NotHdr := Gap.interior j (Nat.pos_of_ne_zero Z) J
      obtain ⟨_,_,S,E⟩ := reader_word_protected d N hh G F Dgt Rail hdr Hdr Gap J NotHdr side Side x First w Held
      unfold selectedDigits at E
      rw [S] at E
      simpa only [Bank] using E
  rw [same_sample _ _ _ bank side Side P]
  subst bank
  rcases Side with rfl|rfl
  · exact (sample_selected _ _ _).1
  · exact (sample_selected _ _ _).2

/-- This premise identifies the capture retained in the *actual old source
ISSUE* with the after-ACQ base selectors. Grants alone do not describe
the source's capture bytes. -/
def CaptureAtIssues (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) : Prop :=
  ∀ pre post, w=pre++door C::post →
    let z := rawRun x pre
    let p := params d s
    let cap := acqCaptureIndex p (selectBytes d (z C.root))
    cap/4=rawSelector d x C.root ∧ cap%2=rawSelector d x (nextAt C.root (C.a+C.b))

private theorem current_sample_on_prefix
    (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Dgt : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (C : Chart h) (x : Raw s n) (First : FirstCut d hh Q G x)
    (w pre fly post : List (Fin n))
    (Tape : w=(pre++door C::fly)++door C::post)
    (k : Nat) (op : Nat) (hdr : Fin n) (Hdr : h hdr=true) {len j : Nat}
    (Gap : Gap h hdr len) (J : j<len)
    (Where : out C k=nextAt hdr j) (side : Fin 3) (Side : side=0 ∨ side=2)
    (Held : HeldAlong d hdr side x w)
    (bank value : Nat) (Bank : bank=rawSelector d x hdr)
    (S : Sample d C op (rawNext s (rawRun x pre) (door C)) fly k side bank value) :
    value=selectedFile (params d s) (fun i => selectBytes d (x i)) hdr (side=0) j := by
  obtain ⟨lead,tail,Fly,_,_,Value,_⟩ := S.witness
  let pfx := pre++door C::lead
  have Whole : w=pfx++(out C k::tail++door C::post) := by
    rw [Tape,Fly]
    simp [pfx,List.append_assoc]
  have H := held_prefix d hdr side x pfx _ (Whole ▸ Held)
  have X : rawRun x pfx=rawRun (rawNext s (rawRun x pre) (door C)) lead := by
    dsimp only [pfx]
    rw [ShortOwnerEpochJS.raw_append]
    rfl
  have T := observed_word_digit d N hh G F Dgt Rail x First hdr Hdr Gap J side Side pfx H bank Bank
  rw [X] at T
  exact Value.trans (Where.symm ▸ T)

theorem snapshot_receipts (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    {r0 : Fin n} {a b c : Nat} (Root : h r0=true)
    (GA : Gap h r0 a) (GB : Gap h (nextAt r0 a) b)
    (GC : Gap h (nextAt (nextAt r0 a) b) c) (Room : a+b+c<n)
    (HA : (params d s).digits≤a) (HC : (params d s).digits≤c)
    (x : Raw s n) (First : FirstCut d hh Q G x) (w : List (Fin n)) (l : List Receipt) :
    let C := chart_of_three Root GA GB GC Room
    let p := params d s
    LegalIssue d C x → AckTape d C x w l →
    HeldAlong d C.root 0 x w → HeldAlong d (nextAt C.root (C.a+C.b)) 2 x w →
    CaptureAtIssues d C x w →
    ∀ r∈l,∀ j,j<p.digits→ (r.1=cmpOp p+j ∨ r.1=readOp p+j) →
      r.2.payload/2^ReportByteRows.d p=selectedFile p (fun i=>selectBytes d (x i)) C.root true j ∧
      r.2.payload%2^ReportByteRows.d p=
        selectedFile p (fun i=>selectBytes d (x i)) (nextAt C.root (C.a+C.b)) false j := by
  dsimp only
  let C := chart_of_three Root GA GB GC Room
  let p := params d s
  intro I T Held0 Held2 Capt r Mem j J Op
  change j < p.digits at J
  change r.1=cmpOp p+j ∨ r.1=readOp p+j at Op
  have Args : IndexedOp p r.1 ∧ r.1<writeOp p ∧ indexedReadOffset p r.1=j := by
    rcases Op with E|E
    · have R : cmpOp p+j<readOp p := by unfold cmpOp readOp; omega
      rw [E]
      unfold IndexedOp indexedReadOffset
      rw [if_pos R]
      simp only [cmpOp,writeOp,sealOp]
      omega
    · have R : ¬readOp p+j<readOp p := by omega
      rw [E]
      unfold IndexedOp indexedReadOffset
      rw [if_neg R]
      simp only [cmpOp,readOp,writeOp,sealOp]
      omega
  obtain ⟨pre,fly,post,hi,lo,Tape,S0,S2,_,Payload⟩ :=
    receipt_read_samples d N hh G F digit Root GA GB GC Room HA HC x First.1.1.1 I w l T
      r Mem Args.1 Args.2.1 j Args.2.2 J
  have W : w=pre++door C::(fly++door C::post) := by
    rw [Tape]
    simp only [List.append_assoc,List.cons_append]
    rfl
  have Cap := Capt pre _ W
  obtain ⟨B0,B2⟩ := Cap
  have R2 : nextAt C.root (C.a+C.b)=nextAt (nextAt r0 a) b := by
    change nextAt r0 (a+b)=_
    exact nextAt_add r0 a b
  have L := current_sample_on_prefix d N hh G F digit Rail C x First w pre fly post Tape j r.1
    C.root Root GA (Nat.lt_of_lt_of_le J HA) rfl 0 (.inl rfl) Held0 _ hi B0 S0
  have R := current_sample_on_prefix d N hh G F digit Rail C x First w pre fly post Tape (a+b+j) r.1
    (nextAt C.root (C.a+C.b)) (R2.symm ▸ GB.atEnd) (R2.symm ▸ GC) (Nat.lt_of_lt_of_le J HC)
    (nextAt_add _ _ _) 2 (.inr rfl) Held2 _ lo B2 S2
  have Bound : lo<2^ReportByteRows.d p := by
    obtain ⟨_,_,_,_,_,V,_⟩ := S2.witness
    rw [V]
    unfold indexedSample
    exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) ((BitVec.extractLsb' _ _ _).isLt)
  rw [Payload,Nat.mul_comm hi _,Nat.mul_add_div (Nat.pow_pos (by decide : 0<2)),Nat.div_eq_of_lt Bound,
    Nat.add_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt Bound]
  exact ⟨L,R⟩

private theorem acq_selector_from_prefix (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0)
    (A : ReportOwnerAcquireProvenance.FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (i : Nat) (I : i<C.L) (H : h (out C i)=true)
    (Side : C.route.port i=0 ∨ C.route.port i=2)
    (Compat : Compatible (rawGrant d x0 (out C i)))
    (w : List (Fin n)) (T : BeforeConsume d C x0 w)
    (u : List (Fin n)) (P : u <+: w)
    (Held : rawGrant d (rawRun x0 u) (out C i) (C.route.port i)=true) :
    rawSelector d (rawRun x0 w) (out C i)=rawSelector d (rawRun x0 u) (out C i) := by
  induction T generalizing u with
  | nil =>
    rw [P.eq_of_length_le (Nat.zero_le _)]
  | @snoc ws e prev nc IH =>
    by_cases L : u.length≤ws.length
    · have Prefix := List.prefix_of_prefix_length_le P (List.prefix_append ws [e]) L
      have Held0 := ReportAcquireWinHold.acq_grant_from_prefix d C hh G F N x0 X A digit i I H Compat
        ws prev u Prefix Held
      rw [ShortOwnerEpochJS.raw_snoc]
      exact (reader_grant_protects_selector d _ e _ N _ Side
        (ReportAcquireWinHold.compatible_run d N x0 (out C i) Compat ws) Held0).trans (IH u Prefix Held)
    · rw [P.eq_of_length_le (by simp; omega)]

private theorem winner_selector_at_consume
    (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true) (G : GapInput h)
    (F : Fibre (h:=h) d Q) (N : 1<n)
    (x0 : Raw s n) (X : Cached d hh Q x0)
    (A : ReportOwnerAcquireProvenance.FState d C x0 0 64)
    (digit : 0<(params d s).digits)
    (i : Nat) (I : i<C.L) (H : h (out C i)=true)
    (Side : C.route.port i=0 ∨ C.route.port i=2)
    (Compat : Compatible (rawGrant d x0 (out C i)))
    (w u v : List (Fin n)) (T : BeforeConsume d C x0 w)
    (S : w=u++out C i::v)
    (Held : rawGrant d (rawNext s (rawRun x0 u) (out C i)) (out C i) (C.route.port i)=true) :
    rawSelector d (rawNext s (rawRun x0 w) (door C)) (out C i)=
      rawSelector d (rawRun x0 u) (out C i) := by
  have Prefix : (u++[out C i]) <+: w := by
    rw [S]
    simp
  have B : rawGrant d (rawRun x0 (u++[out C i])) (out C i) (C.route.port i)=true := by
    rw [ShortOwnerEpochJS.raw_snoc]
    exact Held
  have Old := ReportAcquireWinHold.acq_grant_from_prefix d C hh G F N x0 X A digit i I H Compat w T _ Prefix B
  have Sel := acq_selector_from_prefix d C hh G F N x0 X A digit i I H Side Compat w T _ Prefix B
  rw [ShortOwnerEpochJS.raw_snoc] at Sel
  have Own : rawSelector d (rawNext s (rawRun x0 u) (out C i)) (out C i)=
      rawSelector d (rawRun x0 u) (out C i) := by
    apply raw_selector_frame d _ _ _ N
    rintro ⟨E,_⟩
    exact edge_sep N _ E
  exact (reader_grant_protects_selector d _ _ _ N _ Side
    (ReportAcquireWinHold.compatible_run d N x0 _ Compat w) Old).trans (Sel.trans Own)

/-- A real successful ACQ ties both capture bits to the after-ACQ
base selectors, and supplies the held side leases through the actual
no-restart suffix. Neither equality is taken as a premise. -/
theorem actual_acq_snapshot_front (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (issue : Raw s n) (X : Cached d hh Q issue)
    (I : LegalIssue d C issue) (P : readPC d C issue=(1,acqOp (params d s)))
    (Compat : ∀ i,h i=true→Compatible (rawGrant d issue i))
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s issue (door C)) w)
    (Tag : (tok d C (rawRun (rawNext s issue (door C)) w) 0).tag=3)
    (ND : (tok d C (rawRun (rawNext s issue (door C)) w) 0).outcome≠1)
    (v : List (Fin n))
    (NR : NoRestartTape d C (rawNext s (rawRun (rawNext s issue (door C)) w) (door C)) v)
    (i₂ : Nat) (J₂ : i₂<C.L) (H₂ : h (out C i₂)=true) (L₂ : C.route.port i₂=2)
    (L₀ : C.route.port 0=0) (R₂ : out C i₂=nextAt C.root (C.a+C.b)) :
    let after := rawNext s (rawRun (rawNext s issue (door C)) w) (door C)
    HeldAlong d C.root 0 after v ∧ HeldAlong d (nextAt C.root (C.a+C.b)) 2 after v ∧
      CaptureAtIssues d C after v := by
  dsimp only
  let x0 := rawNext s issue (door C)
  let after := rawNext s (rawRun x0 w) (door C)
  have A := all_captures_after_consume d C hh G F N issue X I P Compat digit w T Tag ND v NR
  have A0 := all_captures_after_consume d C hh G F N issue X I P Compat digit w T Tag ND [] trivial
  obtain ⟨X0,F0⟩ := ReportOwnerAcquireProvenance.launch d C hh G F N issue X I P
  have B (i : Nat) (J : i<C.L) (H : h (out C i)=true) (Side : C.route.port i=0 ∨ C.route.port i=2) :
      ownerCaptureIndex d C after/2^(2-(C.route.port i).val)%2=
        rawSelector d after (out C i) := by
    obtain ⟨u,z,r,S,_,_,Held,Eq,_⟩ :=
      captured_file_fields d C x0 after w i (A0.2.2.2 i J H).1
    have Xc := raw_compatible_step d issue (door C) (out C i)
      (edge_sep N _) (Compat _ H)
    have Sel := winner_selector_at_consume d C hh G F N x0 X0 F0 digit i J H Side Xc w u z T S Held
    exact Eq.trans Sel.symm
  have B0 := B 0 C.positive C.rootHeader (.inl L₀)
  have B2 := B i₂ J₂ H₂ (.inr L₂)
  rw [L₀] at B0
  rw [L₂,R₂] at B2
  have D0 : ownerCaptureIndex d C after<8 :=
    ((selectBytes d (after C.root)).extractLsb' (sourceBase (params d s)+(16+2*ReportByteRows.d (params d s))) 3).isLt
  change ownerCaptureIndex d C after/4%2=rawSelector d after C.root at B0
  rw [Nat.mod_eq_of_lt (show ownerCaptureIndex d C after/4<2 by omega)] at B0
  rw [show 2^(2-(2 : Fin 3).val)=1 from rfl,Nat.div_one] at B2
  change ownerCaptureIndex d C after%2=rawSelector d after (nextAt C.root (C.a+C.b)) at B2
  have Hold0 := (A.2.2.2 0 C.positive C.rootHeader).2
  have Hold2 := (A.2.2.2 i₂ J₂ H₂).2
  rw [L₀] at Hold0
  rw [L₂,R₂] at Hold2
  refine ⟨Hold0,Hold2,?_⟩
  intro pre post W
  have NR' := no_restart_left d C after pre (door C::post) (W ▸ NR)
  have Frame := (raw_postacq_run d C hh F N digit after pre A0.1 A0.2.1 NR').2.2
  change ownerCaptureIndex d C (rawRun after pre)/4=rawSelector d after C.root ∧
    ownerCaptureIndex d C (rawRun after pre)%2=rawSelector d after (nextAt C.root (C.a+C.b))
  rw [Frame]
  exact ⟨B0,B2⟩

theorem snapshot_receipts_of_acq (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    {r0 : Fin n} {a b c : Nat} (Root : h r0=true)
    (GA : Gap h r0 a) (GB : Gap h (nextAt r0 a) b)
    (GC : Gap h (nextAt (nextAt r0 a) b) c) (Room : a+b+c<n)
    (HA : (params d s).digits≤a) (HC : (params d s).digits≤c)
    (issue : Raw s n) (X : Cached d hh Q issue)
    (w v : List (Fin n)) (l : List Receipt) :
    let C := chart_of_three Root GA GB GC Room
    let p := params d s
    let acq := rawNext s issue (door C)
    let old := rawRun acq w
    let b := rawNext s old (door C)
    LegalIssue d C issue → readPC d C issue=(1,acqOp p) →
    (∀ i,h i=true→Compatible (rawGrant d issue i)) →
    BeforeConsume d C acq w → (tok d C old 0).tag=3 → (tok d C old 0).outcome≠1 →
    FirstCut d hh Q G b → LegalIssue d C b → NoRestartTape d C b v → AckTape d C b v l →
    ∀ r∈l,∀ j,j<p.digits→ (r.1=cmpOp p+j ∨ r.1=readOp p+j) →
      r.2.payload/2^ReportByteRows.d p=selectedFile p (fun i=>selectBytes d (b i)) C.root true j ∧
      r.2.payload%2^ReportByteRows.d p=
        selectedFile p (fun i=>selectBytes d (b i)) (nextAt C.root (C.a+C.b)) false j := by
  dsimp only
  let C := chart_of_three Root GA GB GC Room
  intro I P Compat T Tag ND First After NR Ack
  have L0 : C.route.port 0=0 := by
    change lane a b 0=0
    simp [lane,GA.positive]
  have L2 : C.route.port (a+b)=2 := by
    change lane a b (a+b)=2
    simp [lane,show ¬ a+b<a by omega]
  have H2 : h (out C (a+b))=true := by
    change h (nextAt r0 (a+b))=true
    rw [nextAt_add]
    exact GB.atEnd
  have J2 : a+b<C.L := by
    change a+b<a+b+c
    have := GC.positive
    omega
  obtain ⟨Hold0,Hold2,Cap⟩ :=
    actual_acq_snapshot_front d C hh G F N issue X I P Compat digit w T Tag ND v NR
      (a+b) J2 H2 L2 L0 rfl
  exact snapshot_receipts d N hh G F digit Rail Root GA GB GC Room HA HC _ First v l After Ack Hold0 Hold2 Cap

end L4.ReportSnapshotLease

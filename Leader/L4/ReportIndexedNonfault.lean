import Leader.L4.ReportOwnerIndexedFlight
import Leader.L4.ReportAcquireAllCaptures
import Leader.L4.ReportIndexedLaunchData
import Leader.L4.ReportIndexedSideLease
import Leader.L4.ReportAcqExtract

namespace L4.ReportIndexedNonfault
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportRawProjection ReportOwnerIndexedFlight ReportOwnerAcquireReturn
open ReportOwnerProvenanceTransport ReportGenerationAncestry ReportAcquireAllCaptures
open ReportOwnerCommandRail ReportACQToWriteNoCommit ReportLeaseOwner ReportLeaseGrants
open ReportPrelaunchClock ReportGrantTimeline
open ReportIndexedLaunchData ReportACQSelectedCapture ReportOwnerIssueControl
open ReportOwnerAcquireProvenance (NoConsume BeforeConsume)

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- The only live indexed flight transition that can set an absorbing fault.
At the centre bit it consults the two actual old guards, not the new grant. -/
def Permit (p : Params) (op : Nat) (hu : Bool) (u : BitVec p.w)
    (port : Fin 3) (a : IndexedData) : Prop :=
  writeOp p≤op → port=1 → reportOldOffset p hu u=op-writeOp p → hu=true →
    reportOldGrant p u 1=true ∧ publicationSelector p u=a.banks/2

theorem next_healthy_iff (p : Params) (op : Nat) (hu : Bool) (u : BitVec p.w)
    (port : Fin 3) (a : IndexedData) :
    (∃ q, indexedNext p op hu u port (some a)=some q) ↔ Permit p op hu u port a := by
  by_cases Reader : op<writeOp p
  · constructor
    · intro _ W
      exact (Nat.not_le_of_gt Reader W).elim
    · intro _
      simp only [indexedNext,if_pos Reader]
      split
      · split
        · exact ⟨_,rfl⟩
        · split <;> exact ⟨_,rfl⟩
      · exact ⟨_,rfl⟩
  · have W : writeOp p≤op := Nat.le_of_not_gt Reader
    constructor
    · rintro ⟨q,E⟩ _ Port Off H
      by_cases Yes : reportOldGrant p u 1=true ∧ publicationSelector p u=a.banks/2
      · exact Yes
      · have A : port=1 ∧ reportOldOffset p hu u=op-writeOp p ∧ hu=true ∧
            ¬(reportOldGrant p u 1=true ∧ publicationSelector p u=a.banks/2) := ⟨Port,Off,H,Yes⟩
        simp only [indexedNext,if_neg Reader,if_pos A] at E
        contradiction
    · intro H
      have E : ¬ (port=1 ∧ reportOldOffset p hu u=op-writeOp p ∧ hu=true ∧
          ¬(reportOldGrant p u 1=true ∧ publicationSelector p u=a.banks/2)) := by
        rintro ⟨Port,Off,Hdr,X⟩
        exact X (H W Port Off Hdr)
      exact ⟨a,by simp only [indexedNext,if_neg Reader,if_neg E]⟩

theorem next_reader_healthy (p : Params) (op : Nat) (R : op<writeOp p)
    (hu : Bool) (u : BitVec p.w) (port : Fin 3) (a : IndexedData) :
    ∃ q, indexedNext p op hu u port (some a)=some q :=
  (next_healthy_iff p op hu u port a).mpr (fun W => (Nat.not_le_of_gt R W).elim)

theorem next_write_same (p : Params) (op : Nat) (W : writeOp p≤op)
    (hu : Bool) (u : BitVec p.w) (port : Fin 3) (a : IndexedData)
    (P : Permit p op hu u port a) :
    indexedNext p op hu u port (some a)=some a := by
  have E : ¬ (port=1 ∧ reportOldOffset p hu u=op-writeOp p ∧ hu=true ∧
      ¬(reportOldGrant p u 1=true ∧ publicationSelector p u=a.banks/2)) :=
    fun ⟨Port,Off,Hdr,Denied⟩=>Denied (P W Port Off Hdr)
  simp only [indexedNext,if_neg (Nat.not_lt_of_ge W),if_neg E]

def CursorLive : Cursor → Prop
  | .forward _ q | .backward _ q => ∃ a,q=some a

def PermitAt (d : Sheet) (C : Chart h) (op : Nat)
    (x : Raw s n) (k : Nat) (a : IndexedData) : Prop :=
  Permit (params d s) op (h (out C k)) (bytesL d x (out C k)) (C.route.port k) a

/-- A per-old-prefix permit rule excludes every absorbing fault on the
actual forward and reverse walk. No success claim is fed into the proof. -/
theorem walk_live (d : Sheet) (C : Chart h) (op : Nat) (x : Raw s n)
    (initial : IndexedData) (w : List (Fin n)) (cur : Cursor)
    (T : Walk d C op x (some initial) w cur)
    (P : ∀ pre k a, Walk d C op x (some initial) pre (.forward k (some a)) →
      PermitAt d C op (rawRun x pre) k a) :
    CursorLive cur := by
  induction T with
  | seed _ => exact ⟨initial,rfl⟩
  | fhold _ _ _ IH => exact IH
  | @hop pre k q Walk _ _ IH =>
    obtain ⟨a,A⟩ := IH
    subst q
    exact (next_healthy_iff _ _ _ _ _ _).mpr (P pre k a Walk)
  | @turn pre k q Walk _ _ _ IH =>
    obtain ⟨a,A⟩ := IH
    subst q
    exact (next_healthy_iff _ _ _ _ _ _).mpr (P pre k a Walk)
  | dhold _ _ _ IH => exact IH
  | back _ _ IH => exact IH

theorem reader_walk_live (d : Sheet) (C : Chart h) (op : Nat)
    (R : op<writeOp (params d s)) (x : Raw s n) (initial : IndexedData)
    (w : List (Fin n)) (cur : Cursor) (T : Walk d C op x (some initial) w cur) :
    CursorLive cur :=
  walk_live d C op x initial w cur T (fun _ _ _ _ W => (Nat.not_le_of_gt R W).elim)

private def packetOption : Cursor → Option IndexedData
  | .forward _ q | .backward _ q => q

theorem write_walk_payload (d : Sheet) (C : Chart h) (op : Nat)
    (W : writeOp (params d s)≤op) (x : Raw s n) (a : IndexedData)
    (w : List (Fin n)) (cur : Cursor) (T : Walk d C op x (some a) w cur) :
    packetOption cur=some a ∨ packetOption cur=none := by
  have Adv (z : Raw s n) (k : Nat) (q : Option IndexedData) (H : q=some a ∨ q=none) :
      stepPayload d C op z k q=some a ∨ stepPayload d C op z k q=none := by
    rcases H with rfl|rfl
    · unfold stepPayload
      simp only [indexedNext,if_neg (Nat.not_lt_of_ge W)]
      split
      · exact .inr rfl
      · exact .inl rfl
    · exact .inr rfl
  induction T with
  | seed _ => exact .inl rfl
  | fhold _ _ _ IH => exact IH
  | hop _ _ _ IH => exact Adv _ _ _ IH
  | turn _ _ _ _ IH => exact Adv _ _ _ IH
  | dhold _ _ _ IH => exact IH
  | back _ _ IH => exact IH

private theorem nr_snoc (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) (A : NoRestartTape d C x w)
    (B : (readPC d C (rawRun x (w++[e]))).2≠0) :
    NoRestartTape d C x (w++[e]) := by
  induction w generalizing x with
  | nil => exact ⟨B,trivial⟩
  | cons a w IH => exact ⟨A.1, IH _ A.2 B⟩

private theorem nr_append (d : Sheet) (C : Chart h) (x : Raw s n)
    (u v : List (Fin n)) (A : NoRestartTape d C x u)
    (B : NoRestartTape d C (rawRun x u) v) :
    NoRestartTape d C x (u++v) := by
  induction u generalizing x with
  | nil => exact B
  | cons a w IH => exact ⟨A.1, IH _ A.2 B⟩

theorem walk_no_restart (d : Sheet) (C : Chart h) (op : Nat) (O : op≠0)
    (x : Raw s n) (q : Option IndexedData) (w : List (Fin n)) (cur : Cursor)
    (T : Walk d C op x q w cur) : NoRestartTape d C x w := by
  induction T with
  | seed _ => trivial
  | fhold _ _ S IH | hop _ _ S IH | turn _ _ _ S IH | dhold _ _ S IH | back _ S IH =>
    exact nr_snoc d C x _ _ IH (fun E => O ((congrArg Prod.snd S.pc).symm.trans E))

theorem write_seed_prior (p : Params) (u : BitVec p.w) (op : Nat) (W : writeOp p≤op) :
    (concreteSeed p u op).banks/2=acqCaptureIndex p u/2%2 := by
  simp only [concreteSeed,if_neg (Nat.not_lt_of_ge W),writeSeed]
  have B := ancestry_source_centre_lt p u
  change (2 * ancestrySourceCentre p u + (1 - ancestrySourceCentre p u)) / 2=ancestrySourceCentre p u
  omega

/-- No guard is assumed at the chosen WRITE mark. The source capture
is authenticated on the prefix ending at that mark's old state. -/
theorem write_permit_after_acq (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (r : Owner h) (issue : Raw s n) (X : Cached d hh Q issue)
    (I : LegalIssue d (charter G r) issue) (P : readPC d (charter G r) issue=(1,acqOp (params d s)))
    (Compat : ∀ i,h i=true→Compatible (rawGrant d issue i))
    (digit : 0<(params d s).digits)
    (w : List (Fin n))
    (T : BeforeConsume d (charter G r) (rawNext s issue (door (charter G r))) w)
    (Tag : (tok d (charter G r) (rawRun (rawNext s issue (door (charter G r))) w) 0).tag=3)
    (ND : (tok d (charter G r) (rawRun (rawNext s issue (door (charter G r))) w) 0).outcome≠1)
    (lead : List (Fin n))
    (NR : NoRestartTape d (charter G r) (rawNext s
      (rawRun (rawNext s issue (door (charter G r))) w) (door (charter G r))) lead)
    (op : Nat) (W : writeOp (params d s)≤op) (U : op<sealOp (params d s)) :
    let C := charter G r
    let after := rawNext s (rawRun (rawNext s issue (door C)) w) (door C)
    let launch := rawRun after lead
    let start := rawNext s launch (door C)
    let sent := concreteSeed (params d s) (selectBytes d (launch C.root)) op
    (∀ pre k a, Walk d C op start (some sent) pre (.forward k (some a)) →
      PermitAt d C op (rawRun start pre) k a) := by
  dsimp only
  let C := charter G r
  let p := params d s
  let after := rawNext s (rawRun (rawNext s issue (door C)) w) (door C)
  let launch := rawRun after lead
  let start := rawNext s launch (door C)
  let sent := concreteSeed p (selectBytes d (launch C.root)) op
  intro pre k a Walk
  let atMark := rawRun start pre
  have Old := walk_at d C op start (some sent) pre _ Walk
  have K : k<C.L := Old.shape.2.1
  intro _ Port _ Header
  have E := ((ReportOwnerAcquireProvenance.centre_geometry C G).2 k K).mp ⟨Header,Port⟩
  have I0 := ((ReportOwnerAcquireProvenance.centre_geometry C G).2 C.a
    (by have := (ReportOwnerAcquireProvenance.centre_geometry C G).1; omega)).mpr rfl
  have Indexed : a=sent := by
    rcases write_walk_payload d C op W start sent pre _ Walk with A|A
    · exact Option.some.inj A
    · contradiction
  have Pos : op≠0 := by
    unfold writeOp at W
    omega
  have PW : NoRestartTape d C start pre := walk_no_restart d C op Pos start (some sent) pre _ Walk
  have startPC {t : List (Fin n)} {cur : Cursor} (Path : ReportOwnerIndexedFlight.Walk d C op start (some sent) t cur) :
      readPC d C start=(2,op) := by
    induction Path with
    | seed A => exact A.pc
    | fhold _ _ _ IH | hop _ _ _ IH | turn _ _ _ _ IH | dhold _ _ _ IH | back _ _ IH => exact IH
  have StartPC := startPC Walk
  have Whole : NoRestartTape d C after (lead++door C::pre) :=
    nr_append _ _ _ _ _ NR ⟨fun E => Pos ((congrArg Prod.snd StartPC).symm.trans E),PW⟩
  have Equiv : rawRun after (lead++door C::pre)=atMark := by
    rw [ShortOwnerEpochJS.raw_append]
    rfl
  have A0 := all_captures_after_consume d C hh G F N issue X I P Compat digit w T Tag ND [] trivial
  have Alead := raw_postacq_run d C hh F N digit after lead A0.1 A0.2.1 NR
  have Aend := raw_postacq_run d C hh F N digit after (lead++door C::pre) A0.1 A0.2.1 Whole
  have CurrentCapture := Aend.2.2.trans Alead.2.2.symm
  rw [Equiv] at CurrentCapture
  have AC := all_captures_after_consume d C hh G F N issue X I P Compat digit w T Tag ND
    (lead++door C::pre) Whole
  have Held := (AC.2.2.2 C.a (by have := (ReportOwnerAcquireProvenance.centre_geometry C G).1; omega) I0.1).2
  have Grant := ReportIndexedSideLease.held_end d (out C C.a) (C.route.port C.a) after _ Held
  rw [Equiv,I0.2] at Grant
  have Gen := ReportAcqExtract.rail_after_history_consume d C N hh G F digit issue X I P w T Tag ND
    (lead++door C::pre)
  have End : (readPC d C (rawRun after (lead++door C::pre))).2<sealOp p := by
    rw [Equiv,show readPC d C atMark=(2,op) from Old.pc]
    exact U
  have Sel := authentic_capture_is_current d G r hh F N issue X I P digit w T Tag ND
    (lead++door C::pre) Whole Gen End
  change ReportWriterPayload.capturedSelector p (selectBytes d (rawRun after (lead++door C::pre) C.root))=
    rawSelector d (rawRun after (lead++door C::pre)) (centre C) at Sel
  rw [Equiv,captured_selector_index] at Sel
  change ownerCaptureIndex d C atMark/2%2=rawSelector d atMark (centre C) at Sel
  have Seed := write_seed_prior p (selectBytes d (launch C.root)) op W
  change sent.banks/2=ownerCaptureIndex d C launch/2%2 at Seed
  subst k a
  exact ⟨Grant,Sel.symm.trans ((congrArg (fun z : Nat=>z/2%2) CurrentCapture).trans Seed.symm)⟩

end L4.ReportIndexedNonfault

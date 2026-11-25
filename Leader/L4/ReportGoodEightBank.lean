import Leader.L4.ReportGoodEightCut

namespace L4.ReportGoodEightBank
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchAllOwners
open ReportOwnerSerial ReportFirstCutGrant ReportLeaseGrants
open ReportLeaseOwner ReportGenerationAncestry ReportByteRows
open ReportOwnerIssueControl ReportOwnerDoorProjection ReportPrelaunchClock
open ReportOwnerAcquireProvenance ReportOwnerAcquireReturn
open ReportACQToWriteNoCommit ReportReaderWordLease ReportGrantTimeline
open ReportGoodEightCut

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- Exact same-word extraction of a live WRITE. The suffix w begins
    at a genuine RESET consume. All cuts are rawRun/actual door marks.
    The duplicate prefix tapes are intentional: they are the exact
    arguments consumed by authentic_capture_is_current at both cuts.
    A rail proof can obtain them by truncation of the full tapes. -/
def WriteOrigin (d : Sheet) (G : GapInput h) (r : Owner h)
    (b : Raw s n) (w : List (Fin n)) (k : Nat) : Prop :=
  let C := charter G r
  ∃ lead flight pre post : List (Fin n), ∃ t : Tok,
    let a := rawRun b lead
    let old := rawRun (rawNext s a (door C)) flight
    let after := rawNext s old (door C)
    let v := pre++(door C::post)
    let launch := rawRun after pre
    w=lead++(door C::(flight++(door C::v))) ∧
    LegalIssue d C a ∧ readPC d C a=(1,acqOp (params d s)) ∧
    BeforeConsume d C (rawNext s a (door C)) flight ∧
    (tok d C old 0).tag=3 ∧ (tok d C old 0).outcome≠1 ∧
    NoRestartTape d C after pre ∧ OwnerRailTape d C after pre ∧
    NoRestartTape d C after v ∧ OwnerRailTape d C after v ∧
    sourcePhase (params d s) (selectBytes d (launch C.root))=1 ∧
    writeOp (params d s)≤sourceOpcode (params d s) (selectBytes d (launch C.root)) ∧
    sourceOpcode (params d s) (selectBytes d (launch C.root))<sealOp (params d s) ∧
    (source (params d s) (selectBytes d (launch C.root))
      (publicationToken (params d s) true (selectBytes d (launch C.root)) 0)).2=some t ∧
    t.tag=2 ∧ tok d C (rawRun b w) k=t ∧
    (readPC d C (rawRun b w)).2<sealOp (params d s)

/-- Explicit rail supplier for the parallel round. No existential
    raw state unrelated to the receipt is allowed as an origin. -/
def RailSupplier (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) : Prop :=
  ∀ (r : Owner h) (a : Raw s n) (reset w : List (Fin n)),
    Cached d hh Q a → Generated d (charter G r) a reset .done →
    ∀ k,k<(charter G r).L →
      WriteCommand (params d s)
        (tok d (charter G r) (rawRun (rawRun a reset) w) k) →
      WriteOrigin d G r (rawRun a reset) w k

/-- The actual inactive-bank result, not an assumed field of Good8. -/
def BankSafe (d : Sheet) (G : GapInput h) (x : Raw s n) : Prop :=
  ∀ (r : Owner h) k,k<(charter G r).L →
    WriteCommand (params d s) (tok d (charter G r) x k) →
    ancestryWriteOld (params d s) (tok d (charter G r) x k)=
        rawSelector d x (centre (charter G r)) ∧
    ancestryWriteTarget (params d s) (tok d (charter G r) x k)≠
        rawSelector d x (centre (charter G r))

-- CHECK: ReportACQSelectedCapture.lean:145–193;
-- ReportOwnerAcquireProvenance.lean:602–626;
-- ReportOwnerAcquireReturn.lean:260–344. The two calls to
-- acq_consume_then_run use the SAME old root D and sampled b.
theorem write_origin_inactive (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (r : Owner h)
    (b : Raw s n) (B : Cached d hh Q b) (w : List (Fin n)) (k : Nat)
    (O : WriteOrigin d G r b w k) :
    ancestryWriteOld (params d s) (tok d (charter G r) (rawRun b w) k)=
        rawSelector d (rawRun b w) (centre (charter G r)) ∧
    ancestryWriteTarget (params d s) (tok d (charter G r) (rawRun b w) k)≠
        rawSelector d (rawRun b w) (centre (charter G r)) := by
  dsimp only [WriteOrigin] at O
  obtain ⟨lead,flight,pre,post,t,W,I,PC,Before,Tag,ND,NRp,Rp,NR,R,
    Phase,Lower,Upper,Launch,Forward,Token,End⟩ := O
  let C := charter G r
  let p := params d s
  let a := rawRun b lead
  let old := rawRun (rawNext s a (door C)) flight
  let after := rawNext s old (door C)
  let v := pre++(door C::post)
  let launch := rawRun after pre
  let final := rawRun after v
  have E : rawRun b w=final := by
    rw [W,ShortOwnerEpochJS.raw_append]
    change rawRun (rawNext s a (door C)) (flight++(door C::v))=final
    rw [ShortOwnerEpochJS.raw_append]
    rfl
  have A := cached_run d N hh F b B lead
  obtain ⟨Y,Rev,Op,Reply,Live,_⟩ :=
    from_genuine_issue d C hh G F N a A I PC digit flight Before Tag ND
  let cap := acqReplyCentre (tok d C old 0)
  have L := acq_consume_then_run d C hh G F N old Y Rev Op Reply Live ND
    cap rfl digit pre NRp
  have U := acq_consume_then_run d C hh G F N old Y Rev Op Reply Live ND
    cap rfl digit v NR
  have End' : (readPC d C final).2<sealOp p := by rwa [←E]
  have Current := ReportACQSelectedCapture.authentic_capture_is_current
    d G r hh F N a A I PC digit flight Before Tag ND v NR R End'
  have CapLive : cap=rawSelector d final (centre C) :=
    U.2.2.2.symm.trans Current
  have LaunchBytes := raw_write_launch_from_capture d C hh F N launch L.1 t cap
    Phase Lower Upper Launch Forward L.2.2.2
  have Old : ReportWriterPayload.priorBank p t=cap := LaunchBytes.2.2.2.2.2.2.1
  have Target : ReportWriterPayload.targetBank p t=1-cap :=
    LaunchBytes.2.2.2.2.2.2.2
  have Lt : rawSelector d final (centre C)<2 := ancestry_selector_lt _ _
  rw [Token,E]
  change ReportWriterPayload.priorBank p t=rawSelector d final (centre C) ∧
    ReportWriterPayload.targetBank p t≠rawSelector d final (centre C)
  refine ⟨Old.trans CapLive,?_⟩
  rw [Target,CapLive]
  omega

theorem first_bank_safe (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (x : Raw s n) (A : FirstCut d hh Q G x) : BankSafe d G x := by
  intro r k K W
  obtain ⟨a,reset,w,X,R,E⟩ := A.2 (charter G r) (charter_mem G r)
  rw [E] at W ⊢
  exact write_origin_inactive d N hh G F digit r (rawRun a reset)
    (cached_run d N hh F a X reset) w k (Rail r a reset w X R k K W)

-- CHECK: ReportReaderWordOwner.lean:59–90.
-- Its original proof used GenerationInv.writes; replace only
-- that final invocation by the just-derived BankSafe.
theorem nonheader_safe (sheet : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (x : Raw s n) (e hdr : Fin n)
    (Hdr : h hdr=true) {len off : Nat}
    (Gap : ShortLayerGeometry.Gap h hdr len) (Off : off<len)
    (H : h (nextAt hdr off)=false) (B : BankSafe sheet G x) :
    NonheaderWriterSafe sheet x hdr (nextAt hdr off) e := by
  intro E
  subst e
  let i := nextAt hdr off
  let p := params sheet s
  let u := selectBytes sheet (x i)
  let t := publicationToken p false u 1
  change rankReady p false u 1=true → t.fault=false →
    writeOp p≤t.opcode → t.opcode<sealOp p →
    reportOldOffset p false u=t.opcode-writeOp p →
    ancestryWriteTarget p t≠rawSelector sheet x hdr
  intro Ready Live Lower Upper _
  obtain ⟨r,k,K,F,_⟩ := unique_cell hh G i 1
  have Pos : out (charter G r) k=i := congrArg Prod.fst F
  have Lane : (charter G r).route.port k=1 := congrArg Prod.snd F
  have Same := ReportReaderWordOwner.lane1_owner_centre hh G r k Lane Hdr Gap Off Pos
  have T : tok sheet (charter G r) x k=t := by
    rw [ReportOwnerProvenanceTransport.predecessor_projection,Pos,Lane,H]
    rfl
  have W : WriteCommand p (tok sheet (charter G r) x k) := by
    rw [T]
    exact ⟨((rankReady_iff p false u 1).mp Ready).1,Live,Lower,Upper⟩
  have D := (B r k K W).2
  rw [T,Same] at D
  exact D

/-- An uninterrupted reader hold on the actual tape rules out a
    literal release, not just a source restart. All prefixes inherit
    FirstCut and thus global inactive-WRITE safety. -/
theorem reader_safe_tape (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (hdr : Fin n) (Hdr : h hdr=true)
    {len off : Nat} (Gap : ShortLayerGeometry.Gap h hdr len) (Off : off<len)
    (H : h (nextAt hdr off)=false) (j : Fin 3)
    (x : Raw s n) (A : FirstCut d hh Q G x)
    (w : List (Fin n))
    (Held : HeldAlong d hdr j x w) :
    SafeReadTape d hdr (nextAt hdr off) j x w := by
  induction w generalizing x with
  | nil => trivial
  | cons e w IH =>
    have X := A.1.1.1
    have mask := (cached_fibre d N hh Q F).mask x X
    have C := A.1.2 hdr Hdr
    have Next := first_cut_closed d N hh G F digit x e A
    refine ⟨(mask hdr).trans Hdr,(mask _).trans H,?_,
      nonheader_safe d hh G x e hdr Hdr Gap Off H
        (first_bank_safe d N hh G F digit Rail x A),IH _ Next Held.2⟩
    intro E
    subst e
    have D := raw_outgoing_retains_iff d x hdr (edge_sep N hdr)
      ((mask hdr).trans Hdr) C j Held.1
    have Keep := held_start d hdr j _ w Held.2
    rw [Keep] at D
    change true=!(oldIncidence d x hdr).release j at D
    cases R : (oldIncidence d x hdr).release j <;> simp [R] at D ⊢

theorem reader_word_protected (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (hdr : Fin n) (Hdr : h hdr=true)
    {len off : Nat} (Gap : ShortLayerGeometry.Gap h hdr len) (Off : off<len)
    (H : h (nextAt hdr off)=false) (j : Fin 3) (Side : j=0 ∨ j=2)
    (x : Raw s n) (A : FirstCut d hh Q G x)
    (w : List (Fin n)) (Held : HeldAlong d hdr j x w) :
    let y := rawRun x w
    Compatible (rawGrant d y hdr) ∧ rawGrant d y hdr j=true ∧
      rawSelector d y hdr=rawSelector d x hdr ∧
      selectedDigits d y hdr (nextAt hdr off)=selectedDigits d x hdr (nextAt hdr off) :=
  reader_word_run d x hdr (nextAt hdr off) N j Side (A.1.2 hdr Hdr)
    (held_start d hdr j x w Held) w
    (reader_safe_tape d N hh G F digit Rail hdr Hdr Gap Off H j x A w Held)

/-- A concrete forward-closed region for chronology and bank safety.
    This is intentionally NOT named full semantic Good8. -/
def GoodEightBank (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) (x : Raw s n) : Prop :=
  SecondCutHistory d hh Q G x ∧ FirstCut d hh Q G x ∧ BankSafe d G x

theorem history_to_bank (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (x : Raw s n) (A : SecondCutHistory d hh Q G x) :
    GoodEightBank d hh Q G x := by
  have B := second_has_first d N hh G F digit x A
  exact ⟨A,B,first_bank_safe d N hh G F digit Rail x B⟩

theorem good_bank_closed (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (x : Raw s n) (e : Fin n) (A : GoodEightBank d hh Q G x) :
    GoodEightBank d hh Q G (rawNext s x e) :=
  history_to_bank d N hh G F digit Rail _
    (second_history_closed d hh G x e A.1)

theorem bank_expected (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Rail : RailSupplier d hh Q G)
    (x : {x : Raw s n // Cached d hh Q x}) :
    IIDExpectedHittingTimeAtMost (rawNext s) (GoodEightBank d hh Q G) x.val
      (2*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) := by
  have E := expected_second_history d N S hh G F x
  intro t
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s)
    (SecondCutHistory d hh Q G) (GoodEightBank d hh Q G)
    (fun y Y=>history_to_bank d N hh G F
      (ReportPrelaunchDoorProducer.digits_positive d S) Rail y Y) t x.val) (E t)

#print axioms write_origin_inactive
#print axioms first_bank_safe
#print axioms nonheader_safe
#print axioms reader_word_protected
#print axioms good_bank_closed
#print axioms bank_expected
structure FreshFileRows (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h)
    (I : Chart h→Raw s n→Prop) : Prop where
  seed : ∀ C a w,FirstCut d hh Q G a →
    Generated d C a w .done → FullParked d C (rawRun a w) →
    I C (rawRun a w)
  keep : ∀ C x e,FirstCut d hh Q G x → BankSafe d G x →
    I C x → I C (rawNext s x e)

theorem fresh_file_at_second (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (I : Chart h→Raw s n→Prop) (L : FreshFileRows d hh Q G I)
    (x : Raw s n) (A : SecondCutHistory d hh Q G x) :
    ∀ C∈ownerCharts G,I C x := by
  intro C M
  obtain ⟨a,flight,post,B,R,P,E⟩ :=
    second_owner_seed d N hh G F digit x A C M
  have init := L.seed C a flight B R P
  have B' := first_cut_run d N hh G F digit a B flight
  have go (z : Raw s n) (Z : FirstCut d hh Q G z)
      (Y : I C z) (w : List (Fin n)) : I C (rawRun z w) := by
    induction w generalizing z with
    | nil => exact Y
    | cons e w IH =>
      exact IH _ (first_cut_closed d N hh G F digit z e Z)
        (L.keep C z e Z (first_bank_safe d N hh G F digit Rail z Z) Y)
  rw [E]
  exact go _ B' init post

def GoodEightWith (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) (I : Chart h→Raw s n→Prop)
    (x : Raw s n) : Prop :=
  GoodEightBank d hh Q G x ∧ ∀ C∈ownerCharts G,I C x

theorem full_cut_of_history (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (I : Chart h→Raw s n→Prop) (L : FreshFileRows d hh Q G I)
    (x : Raw s n) (A : SecondCutHistory d hh Q G x) :
    GoodEightWith d hh Q G I x :=
  ⟨history_to_bank d N hh G F digit Rail x A,
    fresh_file_at_second d N hh G F digit Rail I L x A⟩

theorem full_cut_closed (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (Rail : RailSupplier d hh Q G)
    (I : Chart h→Raw s n→Prop) (L : FreshFileRows d hh Q G I)
    (x : Raw s n) (e : Fin n) (A : GoodEightWith d hh Q G I x) :
    GoodEightWith d hh Q G I (rawNext s x e) :=
  ⟨good_bank_closed d N hh G F digit Rail x e A.1,
    fun C M=>L.keep C x e A.1.2.1 A.1.2.2 (A.2 C M)⟩

theorem full_cut_expected (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Rail : RailSupplier d hh Q G)
    (I : Chart h→Raw s n→Prop) (L : FreshFileRows d hh Q G I)
    (x : {x : Raw s n // Cached d hh Q x}) :
    IIDExpectedHittingTimeAtMost (rawNext s) (GoodEightWith d hh Q G I) x.val
      (2*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) := by
  have E := expected_second_history d N S hh G F x
  intro t
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s)
    (SecondCutHistory d hh Q G) (GoodEightWith d hh Q G I)
    (fun y Y=>full_cut_of_history d N hh G F
      (ReportPrelaunchDoorProducer.digits_positive d S) Rail I L y Y)
    t x.val) (E t)

#print axioms fresh_file_at_second
#print axioms full_cut_closed
#print axioms full_cut_expected

end L4.ReportGoodEightBank

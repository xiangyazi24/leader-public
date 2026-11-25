import Leader.L4.ShortAdmitSameGeneration
import Leader.L4.ShortMIS1ReadLease
import Leader.L4.ShortReadReturnPC
import Leader.L4.ShortChartOwnership
import Leader.L4.ShortCommitGenerationEvent

namespace L4.ShortOwnerEpochJS
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetFlow ShortResetChart ShortResetCycle
open ShortResetForwardH2 ShortClearLaunch ShortReadResult
open ShortWriteCentreWitness ShortControllerEntrance

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

variable {s n : Nat} {h : Fin n → Bool}

def door (C : Chart h) : Fin n := RearTrace.predecessor C.root

def Geom (_C : Chart h) (x : Raw s n) : Prop :=
  H2Ready x ∧ ∀ q, header x q=h q

theorem geom_step (C : Chart h) (x : Raw s n) (N : 5≤n)
    (G : Geom C x) (e : Fin n) : Geom C (rawNext s x e) :=
  ⟨h2_ready_closed N x e G.1,
    fun q => (H1.raw_h1_selected_frozen N x e q G.1.1).trans (G.2 q)⟩

theorem raw_append (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e)

theorem raw_snoc (x : Raw s n) (w : List (Fin n)) (e : Fin n) :
    rawRun x (w++[e])=rawNext s (rawRun x w) e :=
  raw_append x w [e]

theorem geom_run (C : Chart h) (x : Raw s n) (N : 5≤n)
    (G : Geom C x) (w : List (Fin n)) : Geom C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact G
  | cons e w ih => exact ih _ (geom_step C x N G e)

theorem not_door_right (C : Chart h) (e : Fin n)
    (D : e≠door C) : rightNeighbor e≠C.root := by
  intro E
  apply D
  have K := congrArg RearTrace.predecessor E
  simpa only [door,RearTrace.predecessor_right] using K

/-! J: precise field-level framing. The unchanged rail is a consequence
of the phase-specific raw induction, not an assumed spectator frame. -/

def Rail (C : Chart h) (x : Raw s n) (i : Nat) (t : Token) : Prop :=
  ∀ j, j<C.L → bits C.route x j =
    if j<i then encode T else if j=i then encode t else encode E

theorem rail_of_parts (C : Chart h) (x : Raw s n) (i : Nat) (t : Token)
    (P : TrailPrefix C.route x i) (F : bits C.route x i=encode t)
    (S : ShortHelloForward.ClearSuffix C.route x i) : Rail C x i t := by
  intro j J
  by_cases A : j<i
  · simpa only [if_pos A] using P j A
  by_cases B : j=i
  · subst j
    simpa using F
  · simpa only [if_neg A,if_neg B] using S j (by omega) J

theorem foreign_port_disjoint (C D : Chart h) (k j : Nat)
    (K : k<C.L) (J : j<D.L) (different : C.root≠D.root) :
    ShortChartOwnership.cell C k≠ShortChartOwnership.cell D j :=
  ShortChartOwnership.distinct_owners_disjoint C D different k j K J

theorem source_nondoor_frame (C : Chart h) (x : Raw s n)
    (N : 5≤n) (G : Geom C x) (e : Fin n) (D : e≠door C) :
    let y := rawNext s x e
    get (y C.root).mis1 81 2 (by decide)=get (x C.root).mis1 81 2 (by decide) ∧
    get (y C.root).mis1 78 3 (by decide)=get (x C.root).mis1 78 3 (by decide) ∧
    fileField.read (y C.root).mis1=fileField.read (x C.root).mis1 := by
  dsimp only
  have hd := (G.2 C.root).trans C.rootHeader
  have F := ShortWriteFileSplice.raw_file_step x C.root e (by omega)
    hd (fun E => False.elim (not_door_right C e D E))
  by_cases Q : e=C.root
  · subst e
    exact ⟨(reset_controller_outgoing_raw x C.root hd).1,
      (reset_controller_outgoing_raw x C.root hd).2,F⟩
  · have K := reset_remote_frame_raw x e C.root (Ne.symm Q)
      (Ne.symm (not_door_right C e D))
    rw [K]
    exact ⟨rfl,rfl,rfl⟩

/-- Apply with the identical old/new rail obtained on the nonadvancing
    branch of the checked flight step. It deliberately does not frame
    grants, selector, seal or banks of the whole physical site. -/
theorem owner_unmatched_raw_frame (C : Chart h) (x : Raw s n)
    (N : 5≤n) (G : Geom C x) (e : Fin n) (D : e≠door C)
    (i : Nat) (t : Token) (A : Rail C x i t)
    (B : Rail C (rawNext s x e) i t) :
    (∀ j, j<C.L → bits C.route (rawNext s x e) j=bits C.route x j) ∧
      (get (rawNext s x e C.root).mis1 81 2 (by decide)=
        get (x C.root).mis1 81 2 (by decide)) ∧
      (get (rawNext s x e C.root).mis1 78 3 (by decide)=
        get (x C.root).mis1 78 3 (by decide)) ∧
      fileField.read (rawNext s x e C.root).mis1=fileField.read (x C.root).mis1 :=
  ⟨fun j J => (B j J).trans (A j J).symm,
    source_nondoor_frame C x N G e D⟩

/-- Canonical clean pre-READ issue stays grant-free on nondoor marks.
    The same proof as ShortAdmitSameGeneration.clear_wait, specialized
    to one mark, without referencing that private theorem. -/
theorem clear_nondoor_no_grants (C : Chart h) (x : Raw s n)
    (heads : ∀ q,header x q=h q) (op : Nat)
    (I : ClearIssue C x op) (G : ShortHelloForward.NoGrants C.route x)
    (e : Fin n) (D : e≠door C) :
    ClearIssue C (rawNext s x e) op ∧
      ShortHelloForward.NoGrants C.route (rawNext s x e) := by
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  have S : ShortPreReadGrants.NoAsk C.route x := by
    intro j J H
    have V := slot_of_bits C.route x j E empty_decode (I.2.1 j J)
    change oldK (header x (nextAt C.root j))
      (x (nextAt C.root j)).mis1 (C.route.port j)=E at V
    have hh : header x (nextAt C.root j)=true := (heads _).trans H
    rw [hh] at V
    exact ShortPreReadGrants.pre_read_no_ask _ _ (.inl V)
  exact ⟨clear_issue_nondoor C x heads op I e D,
    ShortPreReadGrants.no_ask_keeps_grants_absent C.route x e
      (edge_sep N e) heads G S⟩

/-- RESET from a *drained* source: strengthen the checked dirty-drain
    invariant by the empty suffix, which is available at this launch. -/
def ResetFull (C : Chart h) (x : Raw s n) (st : Stage) : Prop :=
  ShortResetCycle.Active C x st ∧ ShortResetReleased.Released C x st ∧
    match st with
    | .fwd i => ShortHelloForward.ClearSuffix C.route x i
    | _ => True

theorem reset_launch (C : Chart h) (x : Raw s n)
    (heads : ∀ q,header x q=h q) (I : ClearIssue C x 0) :
    ResetFull C (rawNext s x (door C)) (.fwd 0) := by
  have F := clean_launch C x heads 0 I
  -- CHECK: ShortClearLaunch.lean:33–46, ShortResetCycle.lean:158–162.
  -- launchToken 0 is definitionally resetForward.
  exact ⟨⟨C.positive,⟨F.1,F.2.1⟩,
      fun j J => False.elim (by omega),F.2.2.1⟩,
    ShortResetReleased.released_at_issue C _,F.2.2.2⟩

theorem reset_step (C : Chart h) (x : Raw s n) (N : 5≤n)
    (heads : ∀ q,header x q=h q) (e : Fin n) (st : Stage)
    (L : st≠.done) (A : ResetFull C x st) :
    ResetFull C (rawNext s x e) (nextStage C e st) := by
  have R := ShortResetCycle.active_step C x e (by omega) heads st L A.1
  have Q := ShortResetReleased.step_released C x e (by omega) heads st L A.1 A.2.1
  refine ⟨R,Q,?_⟩
  cases st with
  | done => exact False.elim (L rfl)
  | fwd i =>
    have S := ShortHelloForward.clear_suffix_step C.route x e
      (edge_sep (by omega) e) heads i A.2.2
    change ShortHelloForward.ClearSuffix C.route (rawNext s x e)
      (if e=nextAt C.root i then i+1 else i) at S
    by_cases M : e=nextAt C.root i
    · by_cases J : i+1<C.L
      · simpa only [nextStage,if_pos M,if_pos J,
          ShortHelloForward.ahead] using S
      · simp only [nextStage,if_pos M,if_neg J]
    · simpa only [nextStage,if_neg M,ShortHelloForward.ahead] using S
  | rev i =>
    cases i with
    | zero =>
      by_cases K : rightNeighbor e=C.root <;>
        simp [nextStage,K]
    | succ i =>
      by_cases K : e=nextAt C.root i <;>
        simp [nextStage,K]

/-! READ history. In particular the output PC is recovered from the
old actual D3 at consume, because ReadReverseChart.Consumed alone
does not specify that PC. -/

def readEnd (C : Chart h) (a : Raw s n) (w : List (Fin n)) : Raw s n :=
  rawRun a (door C::w)

def ReadHist (C : Chart h) (a : Raw s n) (w : List (Fin n))
    (f : ShortReadFlight.Flight) : Prop :=
  Geom C a ∧ ClearIssue C a 3 ∧
    ShortReadFlight.beforeConsume C (rawNext s a (door C)) (.forward 0 64) w ∧
    ShortReadFlight.trace C (rawNext s a (door C)) (.forward 0 64) w=f

theorem read_trace_snoc (C : Chart h) (x : Raw s n)
    (f : ShortReadFlight.Flight) (w : List (Fin n)) (e : Fin n) :
    ShortReadFlight.trace C x f (w++[e]) =
      ShortReadFlight.next C (rawRun x w) e (ShortReadFlight.trace C x f w) := by
  induction w generalizing x f with
  | nil => rfl
  | cons m w ih => exact ih (rawNext s x m) (ShortReadFlight.next C x m f)

theorem read_before_snoc (C : Chart h) (x : Raw s n)
    (f : ShortReadFlight.Flight) (w : List (Fin n)) (e : Fin n)
    (B : ShortReadFlight.beforeConsume C x f w)
    (L : ShortReadFlight.live (ShortReadFlight.trace C x f w)) :
    ShortReadFlight.beforeConsume C x f (w++[e]) := by
  induction w generalizing x f with
  | nil => exact ⟨L,trivial⟩
  | cons m w ih =>
    exact ⟨B.1,ih (rawNext s x m) (ShortReadFlight.next C x m f) B.2 L⟩

theorem readHist_launch (C : Chart h) (a : Raw s n)
    (G : Geom C a) (I : ClearIssue C a 3) :
    ReadHist C a [] (.forward 0 64) :=
  ⟨G,I,trivial,rfl⟩

theorem readHist_snoc (C : Chart h) (a : Raw s n) (w : List (Fin n))
    (f : ShortReadFlight.Flight) (R : ReadHist C a w f)
    (L : ShortReadFlight.live f) (e : Fin n) :
    ReadHist C a (w++[e]) (ShortReadFlight.next C (readEnd C a w) e f) := by
  refine ⟨R.1,R.2.1,?_,?_⟩
  · apply read_before_snoc C _ _ w e R.2.2.1
    rw [R.2.2.2]
    exact L
  · rw [read_trace_snoc,R.2.2.2]
    rfl

theorem readHist_active (C : Chart h) (a : Raw s n)
    (N : 5≤n) (w : List (Fin n)) (f : ShortReadFlight.Flight)
    (R : ReadHist C a w f) :
    ShortReadFlight.Active C (readEnd C a w) f := by
  have V := ShortReadFlight.active_from_clean_issue3 C N w a
    R.1.1 R.1.2 R.2.1 R.2.2.1
  change ShortReadFlight.Active C (readEnd C a w)
    (ShortReadFlight.trace C (rawNext s a (door C)) (.forward 0 64) w) at V
  rw [R.2.2.2] at V
  exact V

theorem readEnd_snoc (C : Chart h) (a : Raw s n) (w : List (Fin n)) (e : Fin n) :
    readEnd C a (w++[e])=rawNext s (readEnd C a w) e :=
  raw_snoc (rawNext s a (door C)) w e

theorem read_consume_issue (C : Chart h) (x : Raw s n)
    (N : 5≤n) (heads : ∀ q,header x q=h q)
    (e : Fin n) (f : ShortReadFlight.Flight)
    (L : ShortReadFlight.live f) (A : ShortReadFlight.Active C x f)
    (ok : Bool) (out : Fin 64)
    (D : ShortReadFlight.next C x e f=.consumed ok out) :
    ClearIssue C (rawNext s x e) (if ok then 4 else 0) := by
  have B := ShortReadFlight.read_flight_active_step C x e (by omega) heads f L A
  rw [D] at B
  have P : pc (rawNext s x e C.root).mis1=(if ok then 12 else 8) := by
    cases f with
    | consumed b d => exact False.elim L
    | forward i d =>
      by_cases M : e=nextAt C.root i
      · by_cases J : i+1<C.L <;> simp [ShortReadFlight.next,M,J] at D
      · simp [ShortReadFlight.next,M] at D
    | returning i b d =>
      cases i with
      | succ i =>
        by_cases M : e=nextAt C.root i <;>
          simp [ShortReadFlight.next,nextStage,M] at D
      | zero =>
        by_cases M : rightNeighbor e=C.root
        · have Q : ShortReadFlight.Flight.consumed b d=.consumed ok out := by
            simpa only [ShortReadFlight.next,nextStage,if_pos M] using D
          cases Q
          have hd : header x (rightNeighbor e)=true := by
            rw [M]; exact (heads _).trans C.rootHeader
          have W : ShortReadReverseChart.Wait3 x (rightNeighbor e) := by
            rw [M]
            exact A.2.1
          have K := A.2.2 0 C.positive
          -- CHECK: ShortReadReverseChart.lean:11–16,307–309;
          -- Rev is the full raw wire on lane C.a C.b.
          change (kField (lane C.a C.b 0)).read (x C.root).mis1 =
            encode (ShortReadReverseChart.trailAt ok out 0 0) at K
          have K' : (kField 0).read (x (rightNeighbor e)).mis1 =
              encode (ShortReadReturnHop.readReply ok out) := by
            rw [M]
            simpa [C.rootPort,ShortReadReverseChart.trailAt] using K
          have V := ShortReadReturnPC.consume_pc x e (edge_sep (by omega) e)
            hd W ok out K'
          rw [M] at V
          exact V
        · simp [ShortReadFlight.next,nextStage,M] at D
  apply ShortPreReadGrants.clear_issue_of_pc C _ _ (by cases ok <;> decide) B.1
  cases ok <;> exact P

/-- Actual successful READ consumption, not just a matching D3 byte. -/
def ReadReceipt (C : Chart h) (saved : Raw s n) : Prop :=
  ∃ a w out, ReadHist C a w (.consumed true out) ∧
    saved=readEnd C a w

/-! S: attach actual gaps and generated rolls, with exact endpoint
equalities. The descriptor always comes from saved, the actual
successful READ consume cut. -/

def savedDesc (C : Chart h) (saved : Raw s n) : Fin 8 :=
  ⟨issuedDescriptor (saved C.root).mis1,
    (ShortWritePacketCodec.issued_descriptor_valid (saved C.root).mis1).1⟩

theorem savedDesc_valid (C : Chart h) (saved : Raw s n) :
    descValid (savedDesc C saved).val=true :=
  (ShortWritePacketCodec.issued_descriptor_valid (saved C.root).mis1).2

def FileEq (C : Chart h) (a b : Raw s n) : Prop :=
  fileField.read (b C.root).mis1=fileField.read (a C.root).mis1

theorem fileEq_trans (C : Chart h) (a b z : Raw s n)
    (A : FileEq C a b) (B : FileEq C b z) : FileEq C a z :=
  B.trans A

def GapAt (C : Chart h) (a : Raw s n) (op : Nat) (x : Raw s n) : Prop :=
  ∃ w : List (Fin n), Geom C a ∧ ClearIssue C a op ∧
    (∀ e∈w,e≠door C) ∧ x=rawRun a w

theorem gap_nil (C : Chart h) (x : Raw s n) (G : Geom C x)
    (op : Nat) (I : ClearIssue C x op) : GapAt C x op x :=
  ⟨[],G,I,by simp,rfl⟩

theorem gap_snoc (C : Chart h) (a x : Raw s n) (op : Nat)
    (A : GapAt C a op x) (e : Fin n) (D : e≠door C) :
    GapAt C a op (rawNext s x e) := by
  obtain ⟨w,G,I,M,E⟩ := A
  refine ⟨w++[e],G,I,?_,?_⟩
  · intro m H
    rcases List.mem_append.mp H with H|H
    · exact M m H
    · have K : m=e := by simpa using H
      simpa only [K] using D
  · rw [raw_snoc,E]

theorem gap_current (C : Chart h) (a x : Raw s n) (N : 5≤n)
    (op : Nat) (A : GapAt C a op x) :
    ClearIssue C x op ∧ FileEq C a x := by
  obtain ⟨w,G,I,M,E⟩ := A
  rw [E]
  exact ShortWriteFileSplice.clear_issue_file_nondoors C a G.1 G.2 N
    op I w M

/-- A cast of the chart, not a fresh choice of a root/route. -/
def WriteRun (C : Chart h) (a : Raw s n) (cmd : Cmd)
    (d : Fin 8) (w : List (Fin n)) (f : ShortWriteFlight.Flight) : Prop :=
  H2Ready a ∧ ∃ eq : h=header a,
    ShortWriteFlight.Generated a (eq ▸ C) cmd d w f

theorem writeRun_launch (C : Chart h) (a : Raw s n) (G : Geom C a)
    (cmd : Cmd) (d : Fin 8) (I : ClearIssue C a cmd.op)
    (D : d.val=issuedDescriptor (a C.root).mis1) :
    WriteRun C a cmd d [door C] (.front 0 false) := by
  have eq : h=header a := funext (fun q => (G.2 q).symm)
  -- CHECK: ShortWriteFlight.lean:158–165, ShortMIS1ReadLease.lean:377–391.
  -- Eliminate the mask equality before applying Generated.launch.
  subst h
  exact ⟨G.1,rfl,ShortWriteFlight.Generated.launch I D⟩

theorem writeRun_snoc (C : Chart h) (a : Raw s n) (cmd : Cmd)
    (d : Fin 8) (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (A : WriteRun C a cmd d w f) (L : ShortWriteFlight.live f)
    (e : Fin n) :
    WriteRun C a cmd d (w++[e]) (ShortWriteFlight.next C cmd d (rawRun a w) e f) := by
  obtain ⟨X,eq,G⟩ := A
  subst h
  exact ⟨X,rfl,ShortWriteFlight.Generated.snoc e G L⟩

theorem writeRun_active (C : Chart h) (a : Raw s n) (N : 9<n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (A : WriteRun C a cmd d w f) :
    ShortWriteFlight.Active C cmd d (rawRun a w) f ∧
      (ShortWriteFlight.NeedsReceipt C f →
        SampledEffect cmd d a (nextAt C.root C.a) w) := by
  obtain ⟨X,eq,G⟩ := A
  subst h
  exact ShortWriteFlight.generated_receipt a C X N cmd d D w f G

theorem writeRun_file (C : Chart h) (a : Raw s n) (N : 9<n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : ShortWriteFlight.Flight)
    (A : WriteRun C a cmd d w f) (B : ShortWriteFileSplice.healthy f) :
    FileEq C a (rawRun a w) := by
  obtain ⟨X,eq,G⟩ := A
  subst h
  exact ShortWriteFileSplice.generated_retains_actual_file a C X N cmd d D w f G B

def WriteAt (C : Chart h) (base : Raw s n) (cmd : Cmd)
    (d : Fin 8) (x : Raw s n) (f : ShortWriteFlight.Flight) : Prop :=
  ∃ a w, GapAt C base cmd.op a ∧ WriteRun C a cmd d w f ∧ x=rawRun a w

theorem writeAt_launch (C : Chart h) (base x : Raw s n) (N : 9<n)
    (G : Geom C x) (cmd : Cmd) (d : Fin 8)
    (A : GapAt C base cmd.op x)
    (D : d.val=issuedDescriptor (x C.root).mis1) :
    WriteAt C base cmd d (rawNext s x (door C)) (.front 0 false) :=
  ⟨x,[door C],A,writeRun_launch C x G cmd d
    (gap_current C base x (by omega) cmd.op A).1 D,rfl⟩

theorem writeAt_snoc (C : Chart h) (base x : Raw s n) (cmd : Cmd)
    (d : Fin 8) (f : ShortWriteFlight.Flight) (A : WriteAt C base cmd d x f)
    (L : ShortWriteFlight.live f) (e : Fin n) :
    WriteAt C base cmd d (rawNext s x e) (ShortWriteFlight.next C cmd d x e f) := by
  obtain ⟨a,w,G,W,E⟩ := A
  refine ⟨a,w++[e],G,?_,?_⟩
  · rw [E]
    exact writeRun_snoc C a cmd d w f W L e
  · rw [raw_snoc,E]

theorem writeAt_active (C : Chart h) (base x : Raw s n) (N : 9<n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (f : ShortWriteFlight.Flight) (A : WriteAt C base cmd d x f) :
    ShortWriteFlight.Active C cmd d x f := by
  obtain ⟨a,w,G,W,E⟩ := A
  rw [E]
  exact (writeRun_active C a N cmd d D w f W).1

theorem writeAt_done (C : Chart h) (base x : Raw s n) (N : 9<n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (bad : Bool) (A : WriteAt C base cmd d x (.done bad)) :
    ClearIssue C x (if bad then 0 else cmd.op+1) := by
  have B := writeAt_active C base x N cmd d D (.done bad) A
  apply ShortPreReadGrants.clear_issue_of_pc C x _
    (by cases cmd <;> cases bad <;> decide) B.1
  cases cmd <;> cases bad <;> exact B.2

theorem writeAt_good_file (C : Chart h) (base x : Raw s n) (N : 9<n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (A : WriteAt C base cmd d x (.done false)) : FileEq C base x := by
  obtain ⟨a,w,G,W,E⟩ := A
  have F := (gap_current C base a (by omega) cmd.op G).2
  rw [E]
  exact fileEq_trans C base a _ F
    (writeRun_file C a N cmd d D w (.done false) W rfl)

theorem writeAt_effect (C : Chart h) (base x : Raw s n) (N : 9<n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (A : WriteAt C base cmd d x (.done false)) :
    ∃ a w, GapAt C base cmd.op a ∧ x=rawRun a w ∧
      SampledEffect cmd d a (nextAt C.root C.a) w := by
  obtain ⟨a,w,G,W,E⟩ := A
  exact ⟨a,w,G,E,(writeRun_active C a N cmd d D w (.done false) W).2 rfl⟩

def CommitRun (C : Chart h) (a : Raw s n) (d : Fin 8)
    (w : List (Fin n)) (f : ShortCommitFlight.Flight) : Prop :=
  H2Ready a ∧ ∃ eq : h=header a,
    ShortCommitFlight.Generated a (eq ▸ C) d w f

theorem commitRun_launch (C : Chart h) (a : Raw s n) (G : Geom C a)
    (d : Fin 8) (I : ClearIssue C a 6)
    (D : d.val=issuedDescriptor (a C.root).mis1) :
    CommitRun C a d [door C] (.front 0 .pending) := by
  have eq : h=header a := funext (fun q => (G.2 q).symm)
  subst h
  exact ⟨G.1,rfl,ShortCommitFlight.Generated.launch I D⟩

theorem commitRun_snoc (C : Chart h) (a : Raw s n) (d : Fin 8)
    (w : List (Fin n)) (f : ShortCommitFlight.Flight)
    (A : CommitRun C a d w f) (L : ShortCommitFlight.live f) (e : Fin n) :
    CommitRun C a d (w++[e]) (ShortCommitFlight.next C d (rawRun a w) e f) := by
  obtain ⟨X,eq,G⟩ := A
  subst h
  exact ⟨X,rfl,ShortCommitFlight.Generated.snoc e G L⟩

def CommitAt (C : Chart h) (base : Raw s n) (d : Fin 8)
    (x : Raw s n) (f : ShortCommitFlight.Flight) : Prop :=
  ∃ a w, GapAt C base 6 a ∧ CommitRun C a d w f ∧ x=rawRun a w

theorem commitAt_launch (C : Chart h) (base x : Raw s n) (N : 9<n)
    (G : Geom C x) (d : Fin 8) (A : GapAt C base 6 x)
    (D : d.val=issuedDescriptor (x C.root).mis1) :
    CommitAt C base d (rawNext s x (door C)) (.front 0 .pending) :=
  ⟨x,[door C],A,commitRun_launch C x G d
    (gap_current C base x (by omega) 6 A).1 D,rfl⟩

theorem commitAt_snoc (C : Chart h) (base x : Raw s n) (d : Fin 8)
    (f : ShortCommitFlight.Flight) (A : CommitAt C base d x f)
    (L : ShortCommitFlight.live f) (e : Fin n) :
    CommitAt C base d (rawNext s x e) (ShortCommitFlight.next C d x e f) := by
  obtain ⟨a,w,G,W,E⟩ := A
  refine ⟨a,w++[e],G,?_,?_⟩
  · rw [E]
    exact commitRun_snoc C a d w f W L e
  · rw [raw_snoc,E]

theorem commitAt_active (C : Chart h) (base x : Raw s n) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (f : ShortCommitFlight.Flight) (A : CommitAt C base d x f) :
    ShortCommitFlight.Active C d x f ∧ ShortCommitFlight.OneCentre C f := by
  obtain ⟨a,w,Gap,W,E⟩ := A
  obtain ⟨X,eq,G⟩ := W
  rw [E]
  subst h
  exact ⟨(ShortCommitFlight.generated_receipt a C X N d D w f G).1,
    ShortCommitFlight.generated_oneCentre a C X N d w f G⟩

theorem commitAt_done (C : Chart h) (base x : Raw s n) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (p : ShortCommitChartHop.Status) (A : CommitAt C base d x (.done p)) :
    ClearIssue C x 0 := by
  have B := (commitAt_active C base x N d D (.done p) A).1
  exact ShortPreReadGrants.clear_issue_of_pc C x 0 (by decide) B.1 B.2

/-! The fenced continuation is assembled from actual chronological
segments, not a generic assumption on all other owners. -/

def FencedReach (C : Chart h) (a x : Raw s n) : Prop :=
  ∃ w, x=rawRun a w ∧ ShortMIS1ReadLease.FencedTape C a w

theorem fenced_trans (C : Chart h) (a b x : Raw s n)
    (A : FencedReach C a b) (B : FencedReach C b x) :
    FencedReach C a x := by
  obtain ⟨u,U,F⟩ := A
  obtain ⟨v,V,G⟩ := B
  refine ⟨u++v,?_,?_⟩
  · rw [raw_append,←U,V]
  · apply (ShortMIS1ReadLease.fence_append C a u v).mpr
    exact ⟨F,U ▸ G⟩

theorem gap_fenced (C : Chart h) (a x : Raw s n) (N : 5≤n)
    (op : Nat) (A : GapAt C a op x) : FencedReach C a x := by
  obtain ⟨w,G,I,M,E⟩ := A
  exact ⟨w,E,ShortMIS1ReadLease.clear_issue_prefix_fenced C a G.1 N G.2
    op I w M⟩

theorem writeAt_fenced (C : Chart h) (base x : Raw s n) (N : 9<n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (f : ShortWriteFlight.Flight) (A : WriteAt C base cmd d x f) :
    FencedReach C base x := by
  obtain ⟨a,w,Gap,W,E⟩ := A
  apply fenced_trans C base a x (gap_fenced C base a (by omega) cmd.op Gap)
  obtain ⟨X,eq,G⟩ := W
  subst h
  exact ⟨w,E,ShortMIS1ReadLease.write_prefix_fenced a C X N cmd d D w f G⟩

theorem commitAt_fenced (C : Chart h) (base x : Raw s n) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (f : ShortCommitFlight.Flight) (A : CommitAt C base d x f) :
    FencedReach C base x := by
  obtain ⟨a,w,Gap,W,E⟩ := A
  apply fenced_trans C base a x (gap_fenced C base a (by omega) 6 Gap)
  obtain ⟨X,eq,G⟩ := W
  subst h
  exact ⟨w,E,ShortMIS1ReadLease.commit_prefix_fenced a C X N d D w f G⟩

/-- This is the post-READ serial controller. The saved READ cut is
    fixed across every constructor. a4/a5 are the actual successful
    consume cuts, and each successive tape starts at the previous cut. -/
inductive Post (C : Chart h) (saved x : Raw s n) : Prop where
  | gap4 : GapAt C saved 4 x → Post C saved x
  | stage (f : ShortWriteFlight.Flight) :
      WriteAt C saved .stage (savedDesc C saved) x f →
      ShortWriteFlight.live f → Post C saved x
  | gap5 (a4 : Raw s n) :
      WriteAt C saved .stage (savedDesc C saved) a4 (.done false) →
      GapAt C a4 5 x → Post C saved x
  | seal (a4 : Raw s n) (f : ShortWriteFlight.Flight) :
      WriteAt C saved .stage (savedDesc C saved) a4 (.done false) →
      WriteAt C a4 .seal (savedDesc C saved) x f →
      ShortWriteFlight.live f → Post C saved x
  | gap6 (a4 a5 : Raw s n) :
      WriteAt C saved .stage (savedDesc C saved) a4 (.done false) →
      WriteAt C a4 .seal (savedDesc C saved) a5 (.done false) →
      GapAt C a5 6 x → Post C saved x
  | commit (a4 a5 : Raw s n) (f : ShortCommitFlight.Flight) :
      WriteAt C saved .stage (savedDesc C saved) a4 (.done false) →
      WriteAt C a4 .seal (savedDesc C saved) a5 (.done false) →
      CommitAt C a5 (savedDesc C saved) x f →
      ShortCommitFlight.live f → Post C saved x

theorem post_fenced (C : Chart h) (saved x : Raw s n) (N : 9<n)
    (P : Post C saved x) : FencedReach C saved x := by
  let d := savedDesc C saved
  have D : descValid d.val=true := savedDesc_valid C saved
  cases P with
  | gap4 A => exact gap_fenced C saved x (by omega) 4 A
  | stage f A _ => exact writeAt_fenced C saved x N .stage d D f A
  | gap5 a4 A B =>
    exact fenced_trans C saved a4 x
      (writeAt_fenced C saved a4 N .stage d D (.done false) A)
      (gap_fenced C a4 x (by omega) 5 B)
  | «seal» a4 f A B _ =>
    exact fenced_trans C saved a4 x
      (writeAt_fenced C saved a4 N .stage d D (.done false) A)
      (writeAt_fenced C a4 x N .seal d D f B)
  | gap6 a4 a5 A B G =>
    exact fenced_trans C saved a5 x
      (fenced_trans C saved a4 a5
        (writeAt_fenced C saved a4 N .stage d D (.done false) A)
        (writeAt_fenced C a4 a5 N .seal d D (.done false) B))
      (gap_fenced C a5 x (by omega) 6 G)
  | commit a4 a5 f A B K _ =>
    exact fenced_trans C saved a5 x
      (fenced_trans C saved a4 a5
        (writeAt_fenced C saved a4 N .stage d D (.done false) A)
        (writeAt_fenced C a4 a5 N .seal d D (.done false) B))
      (commitAt_fenced C a5 x N d D f K)

theorem descriptor_eq_of_file (C : Chart h) (saved x : Raw s n)
    (F : FileEq C saved x) :
    (savedDesc C saved).val=issuedDescriptor (x C.root).mis1 :=
  (ShortWriteFileSplice.descriptor_of_same_file _ _ F).symm

/-- Continue the exact segmented history on every actual mark.
    The only exit is a fully drained ISSUE0. -/
theorem post_step (C : Chart h) (saved x : Raw s n) (N : 9<n)
    (G : Geom C x) (e : Fin n) (P : Post C saved x) :
    Post C saved (rawNext s x e) ∨ ClearIssue C (rawNext s x e) 0 := by
  let d := savedDesc C saved
  let y := rawNext s x e
  have D : descValid d.val=true := savedDesc_valid C saved
  have Y : Geom C y := geom_step C x (by omega) G e
  cases P with
  | gap4 A =>
    by_cases E : e=door C
    · subst e
      have F := (gap_current C saved x (by omega) 4 A).2
      exact .inl (.stage _ (writeAt_launch C saved x N G .stage d A
        (descriptor_eq_of_file C saved x F)) (by trivial))
    · exact .inl (.gap4 (gap_snoc C saved x 4 A e E))
  | stage f A L =>
    have B := writeAt_snoc C saved x .stage d f A L e
    generalize Q : ShortWriteFlight.next C .stage d x e f=f' at B
    cases f' with
    | front i bad => exact .inl (.stage _ B (by trivial))
    | back i bad => exact .inl (.stage _ B (by trivial))
    | done bad =>
      cases bad with
      | false =>
        have I : ClearIssue C y 5 :=
          writeAt_done C saved y N .stage d D false B
        exact .inl (.gap5 y B (gap_nil C y Y 5 I))
      | true => exact .inr (writeAt_done C saved y N .stage d D true B)
  | gap5 a4 A B =>
    by_cases E : e=door C
    · subst e
      have F := fileEq_trans C saved a4 x
        (writeAt_good_file C saved a4 N .stage d D A)
        (gap_current C a4 x (by omega) 5 B).2
      exact .inl (.seal a4 _ A (writeAt_launch C a4 x N G .seal d B
        (descriptor_eq_of_file C saved x F)) (by trivial))
    · exact .inl (.gap5 a4 A (gap_snoc C a4 x 5 B e E))
  | «seal» a4 f A B L =>
    have K := writeAt_snoc C a4 x .seal d f B L e
    generalize Q : ShortWriteFlight.next C .seal d x e f=f' at K
    cases f' with
    | front i bad => exact .inl (.seal a4 _ A K (by trivial))
    | back i bad => exact .inl (.seal a4 _ A K (by trivial))
    | done bad =>
      cases bad with
      | false =>
        have I : ClearIssue C y 6 :=
          writeAt_done C a4 y N .seal d D false K
        exact .inl (.gap6 a4 y A K (gap_nil C y Y 6 I))
      | true => exact .inr (writeAt_done C a4 y N .seal d D true K)
  | gap6 a4 a5 A B K =>
    by_cases E : e=door C
    · subst e
      have F := fileEq_trans C saved a5 x
        (fileEq_trans C saved a4 a5
          (writeAt_good_file C saved a4 N .stage d D A)
          (writeAt_good_file C a4 a5 N .seal d D B))
        (gap_current C a5 x (by omega) 6 K).2
      exact .inl (.commit a4 a5 _ A B
        (commitAt_launch C a5 x N G d K (descriptor_eq_of_file C saved x F))
        (by trivial))
    · exact .inl (.gap6 a4 a5 A B (gap_snoc C a5 x 6 K e E))
  | commit a4 a5 f A B K L =>
    have V := commitAt_snoc C a5 x d f K L e
    generalize Q : ShortCommitFlight.next C d x e f=f' at V
    cases f' with
    | front i p => exact .inl (.commit a4 a5 _ A B V (by trivial))
    | back i p => exact .inl (.commit a4 a5 _ A B V (by trivial))
    | done p => exact .inr (commitAt_done C a5 y N d D p V)

/-! The owner automaton, including every fault and denied reply. -/

inductive Busy (C : Chart h) (x : Raw s n) (g : Nat) : Prop where
  | reset (st : Stage) : st≠.done → ResetFull C x st → Busy C x g
  | hello (st : Stage) : ShortHelloFlight.Flight C x st → Busy C x g
  | admit (f : ShortAdmitFlight.State) :
      ShortAdmitFlight.Live f → ShortAdmitFlight.Flight C x g f → Busy C x g
  | ready3 : ClearIssue C x 3 → ShortHelloForward.NoGrants C.route x → Busy C x g
  | read (a : Raw s n) (w : List (Fin n)) (f : ShortReadFlight.Flight) :
      ReadHist C a w f → x=readEnd C a w → ShortReadFlight.live f → Busy C x g
  | post (saved : Raw s n) : ReadReceipt C saved → Post C saved x → Busy C x g

/-- These are actual source/rail alternatives. Parked denotes a
    completed RESET endpoint or the waiting ISSUE1 interval. -/
def Local (C : Chart h) (x : Raw s n) (g : Nat) : Prop :=
  ClearIssue C x 0 ∨ ShortResetHelloSplice.Parked C x ∨ Busy C x g

def OwnerInv (C : Chart h) (x : Raw s n) (g : Nat) : Prop :=
  Geom C x ∧ Local C x g

theorem local_step (C : Chart h) (x : Raw s n) (N : 9<n)
    (G : Geom C x) (g : Nat) (gp : 0<g) (gL : g+1<C.L)
    (gates : ShortAdmitFlight.FixedGate (s:=s) C g)
    (e : Fin n) (P : Local C x g) : Local C (rawNext s x e) g := by
  let y := rawNext s x e
  have Y : Geom C y := geom_step C x (by omega) G e
  rcases P with I|P|B
  · by_cases D : e=door C
    · subst e
      exact .inr (.inr (.reset (.fwd 0) (by decide) (reset_launch C x G.2 I)))
    · exact .inl (clear_issue_nondoor C x G.2 0 I e D)
  · by_cases D : e=door C
    · subst e
      exact .inr (.inr (.hello (.fwd 0) (ShortHelloFlight.actual_launch C x G.2 P)))
    · exact .inr (.inl (ShortResetHelloSplice.parked_nondoor C x G.2 P e D))
  · cases B with
    | reset st L A =>
      have R := reset_step C x (by omega) G.2 e st L A
      by_cases D : nextStage C e st=.done
      · rw [D] at R
        exact .inr (.inl (ShortResetHelloSplice.parked_after_consume C y R.1 R.2.1))
      · exact .inr (.inr (.reset _ D R))
    | hello st A =>
      cases st with
      | done =>
        change ShortHelloForward.NoGrants C.route x ∧ ClearIssue C x 2 at A
        by_cases D : e=door C
        · subst e
          exact .inr (.inr (.admit (.forward 0 false 0) (by trivial)
            (ShortAdmitFlight.launch C x G.2 g gp A.2 A.1)))
        · have R := clear_nondoor_no_grants C x G.2 2 A.2 A.1 e D
          exact .inr (.inr (.hello .done ⟨R.2,R.1⟩))
      | fwd i =>
        exact .inr (.inr (.hello _ (ShortHelloFlight.active_step C x G.2 e
          (.fwd i) (by trivial) A)))
      | rev i =>
        exact .inr (.inr (.hello _ (ShortHelloFlight.active_step C x G.2 e
          (.rev i) (by trivial) A)))
    | admit f L A =>
      have R := ShortAdmitFlight.active_step
        (ShortAdmitSameGeneration.wire_frames (s:=s) (n:=n))
        C x G.2 e g gp gL (gates x G.1 G.2) f L A
      generalize Q : ShortAdmitFlight.next C g e f=f' at R
      cases f' with
      | forward i w r => exact .inr (.inr (.admit _ (by trivial) R))
      | reverse i w => exact .inr (.inr (.admit _ (by trivial) R))
      | done won =>
        cases won with
        | false => exact .inl R.2
        | true => exact .inr (.inr (.ready3 R.2 R.1))
    | ready3 I A =>
      by_cases D : e=door C
      · subst e
        exact .inr (.inr (.read x [] (.forward 0 64)
          (readHist_launch C x G I) rfl (by trivial)))
      · have R := clear_nondoor_no_grants C x G.2 3 I A e D
        exact .inr (.inr (.ready3 R.1 R.2))
    | read a w f R E L =>
      have B := readHist_snoc C a w f R L e
      have End : y=readEnd C a (w++[e]) := by
        dsimp [y]
        rw [readEnd_snoc,E]
      have Act : ShortReadFlight.Active C x f := by
        rw [E]
        exact readHist_active C a (by omega) w f R
      have B' : ReadHist C a (w++[e]) (ShortReadFlight.next C x e f) := by
        rw [E]
        exact B
      generalize Q : ShortReadFlight.next C x e f=f' at B'
      cases f' with
      | forward i d =>
        exact .inr (.inr (.read a (w++[e]) _ B' End (by trivial)))
      | returning i ok d =>
        exact .inr (.inr (.read a (w++[e]) _ B' End (by trivial)))
      | consumed ok out =>
        have I := read_consume_issue C x (by omega) G.2 e f L Act ok out Q
        cases ok with
        | false => exact .inl I
        | true =>
          have Receipt : ReadReceipt C y := ⟨a,w++[e],out,B',End⟩
          exact .inr (.inr (.post y Receipt (.gap4 (gap_nil C y Y 4 I))))
    | post saved R P =>
      rcases post_step C saved x N G e P with B|B
      · exact .inr (.inr (.post saved R B))
      · exact .inl B

/-- One actual raw mark, all phases; post-state exits are explicitly
    drained ISSUE0, Parked, or a typed busy owner. -/
theorem owner_raw_step (C : Chart h) (x : Raw s n) (N : 9<n)
    (g : Nat) (gp : 0<g) (gL : g+1<C.L)
    (gates : ShortAdmitFlight.FixedGate (s:=s) C g)
    (e : Fin n) (A : OwnerInv C x g) :
    OwnerInv C (rawNext s x e) g :=
  ⟨geom_step C x (by omega) A.1 e,
    local_step C x N A.1 g gp gL gates e A.2⟩

def OwnerEpoch (C : Chart h) (seed : Raw s n) (w : List (Fin n))
    (g : Nat) : Prop :=
  OwnerInv C (rawRun seed w) g

theorem mis1_epoch_owner_raw_step (C : Chart h)
    (seed : Raw s n) (w : List (Fin n)) (N : 9<n)
    (g : Nat) (gp : 0<g) (gL : g+1<C.L)
    (gates : ShortAdmitFlight.FixedGate (s:=s) C g)
    (e : Fin n) (A : OwnerEpoch C seed w g) :
    OwnerEpoch C seed (w++[e]) g ∧
      (ClearIssue C (rawRun seed (w++[e])) 0 ∨
        ShortResetHelloSplice.Parked C (rawRun seed (w++[e])) ∨
        Busy C (rawRun seed (w++[e])) g) := by
  have B := owner_raw_step C (rawRun seed w) N g gp gL gates e A
  rw [←raw_snoc] at B
  exact ⟨B,B.2⟩

theorem epoch_from_parked (C : Chart h) (x : Raw s n) (N : 9<n)
    (G : Geom C x) (P : ShortResetHelloSplice.Parked C x)
    (g : Nat) (gp : 0<g) (gL : g+1<C.L)
    (gates : ShortAdmitFlight.FixedGate (s:=s) C g)
    (w : List (Fin n)) : OwnerEpoch C x w g := by
  have go (z : Raw s n) (A : OwnerInv C z g) (u : List (Fin n)) :
      OwnerInv C (rawRun z u) g := by
    induction u generalizing z with
    | nil => exact A
    | cons e u ih =>
      exact ih _ (owner_raw_step C z N g gp gL gates e A)
  exact go x ⟨G,.inr (.inl P)⟩ w

/-! Authenticated READ file at the pending COMMIT. All fences in
this theorem are produced by the serialized histories above. -/

theorem current_read_bits (C : Chart h) (saved x : Raw s n)
    (N : 9<n) (R : ReadReceipt C saved) (F : FencedReach C saved x) :
    (saved C.root).mis1.getLsbD 74=ShortReaderMIS1.selectedValue (x C.root).mis1 ∧
    (saved C.root).mis1.getLsbD 72=
      ShortReaderMIS1.selectedValue (x (nextAt C.root (C.a+C.b))).mis1 := by
  obtain ⟨a,w,out,R,E⟩ := R
  obtain ⟨v,V,F⟩ := F
  have eq : h=header a := funext (fun q => (R.1.2 q).symm)
  subst h
  rw [E] at F V ⊢
  rw [V]
  -- CHECK: ShortMIS1ReadLease.lean:332–343; readEnd is
  -- definitionally the real door :: w, with no other tape.
  have K := ShortMIS1ReadLease.read_file_matches_outer_pair a R.1.1 C N
    R.2.1 w v out R.2.2.1 R.2.2.2 F
  exact ⟨(file_bit (readEnd C a w C.root).mis1 2 (by decide)).trans K.1,
    (file_bit (readEnd C a w C.root).mis1 0 (by decide)).trans K.2⟩

theorem commit_port (C : Chart h) (x : Raw s n) (N : 9<n)
    (G : Geom C x) : C.route.port (C.a-1)=0 := by
  have eq : h=header x := funext (fun q => (G.2 q).symm)
  subst h
  exact (ShortPublishChart.commit_centre_pair x x G.1 C N (fun _=>rfl)).2.2.1

/-- This is the concrete old guard payload authentication, before
    the incoming centre mark. The two sites are H1-neighbours, not
    adjacent physical agents. -/
theorem pending_commit_auth (C : Chart h) (saved x a4 a5 : Raw s n)
    (N : 9<n) (G : Geom C x) (R : ReadReceipt C saved)
    (A : WriteAt C saved .stage (savedDesc C saved) a4 (.done false))
    (B : WriteAt C a4 .seal (savedDesc C saved) a5 (.done false))
    (K : CommitAt C a5 (savedDesc C saved) x (.front (C.a-1) .pending)) :
    let e := nextAt C.root (C.a-1)
    ShortPublicationClassifier.FromProtectedBits
      (ShortReaderMIS1.selectedValue (x C.root).mis1)
      (ShortReaderMIS1.selectedValue (x (nextAt C.root (C.a+C.b))).mis1)
      (oldK (header x e) (x e).mis1 0).payload := by
  dsimp only
  let d := savedDesc C saved
  let e := nextAt C.root (C.a-1)
  have P : Post C saved x := .commit a4 a5 _ A B K (by trivial)
  have F := current_read_bits C saved x N R (post_fenced C saved x N P)
  have W := (commitAt_active C a5 x N d (savedDesc_valid C saved)
    (.front (C.a-1) .pending) K).1.2.2.2.1
  have W' : (kField 0).read (x e).mis1=
      encode (ShortWritePacketCodec.writeFwd 6 d false) := by
    change (kField (C.route.port (C.a-1))).read (x e).mis1=
      encode (ShortCommitChartHop.packet d .pending) at W
    rw [commit_port C x N G] at W
    exact W
  have O := ShortCommitGenerationEvent.old_commit_token x e d
    (savedDesc_valid C saved) false W'
  refine ⟨(saved C.root).mis1,F.1,F.2,?_⟩
  rw [O]
  rfl

#print axioms owner_unmatched_raw_frame
#print axioms reset_step
#print axioms read_consume_issue
#print axioms writeRun_active
#print axioms writeAt_effect
#print axioms commitAt_done
#print axioms post_fenced
#print axioms post_step
#print axioms mis1_epoch_owner_raw_step
#print axioms epoch_from_parked
#print axioms pending_commit_auth

end L4.ShortOwnerEpochJS

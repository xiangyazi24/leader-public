import Leader.L4.ShortMISPublicationSuppliers
import Leader.L4.ShortReadCaptureTrace
import Leader.L4.ShortMIS1ReadLease
import Leader.L4.ShortFiveRivalFence

namespace L4.ShortMISPublicationHistoryLocal
open AllSizeProtocol PhysicalCustody MISByteCodec
open ShortResetChart ShortResetCycle ShortResetMIS1Ring
open ShortResetForwardH2 ShortResetRow ShortResetFlow
open ShortMISEngine ShortMISSheetParked ShortMISPublicationLift
open ReportStaticSpacing (Lower)

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
variable {s n : Nat}

-- ShortMISLift.lean: Receipt, Epoch, Good; ShortMISPublicationLift:
-- cached_run_on. The invariant is on actual states and one chart.
theorem epoch_induction (P : Params s n) (C : Chart P.h)
    (I : Raw s n → Prop)
    (seed : ∀ x, Cached P x → ShortMISLift.Parked P C x → I x)
    (stepI : ∀ x e, Cached P x → I x → I (rawNext s x e))
    (y : Raw s n) (Y : ShortMISLift.Epoch P C y) : I y := by
  obtain ⟨x,w,v,X,R,E⟩ := Y
  have runI (a : Raw s n) (A : Cached P a) (B : I a)
      (t : List (Fin n)) : I (rawRun a t) := by
    induction t generalizing a with
    | nil => exact B
    | cons e t ih =>
      exact ih (rawNext s a e) (P.cached_closed a e A) (stepI a e A B)
  rw [←E]
  have B := cached_run_on P x X w
  exact runI (rawRun x w) B (seed (rawRun x w) B R.2.1) v

def ReaderLease (P : Params s n) (i : Fin n) (j : Fin 3)
    (v : Bool) (x : Raw s n) : Prop :=
  ShortGrantRaw.Coherent (P.byte x i) ∧
    (P.byte x i).getLsbD (91-j.val)=true ∧
    ShortReaderMIS1.selectedValue (P.byte x i)=v

def NoRelease (P : Params s n) (i : Fin n) (j : Fin 3)
    (x : Raw s n) (e : Fin n) : Prop :=
  e=i → (headerGrantView (P.byte x i)).release j=false

def NoReleaseTape (P : Params s n) (i : Fin n) (j : Fin 3) :
    Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w => NoRelease P i j x e ∧
      NoReleaseTape P i j (rawNext s x e) w

theorem reader_step (P : Params s n) (x : Raw s n) (X : Cached P x)
    (i e : Fin n) (j : Fin 3) (J : j=0 ∨ j=2)
    (H : P.h i=true) (v : Bool) (L : ReaderLease P i j v x)
    (R : NoRelease P i j x e) :
    ReaderLease P i j v (rawNext s x e) := by
  let z := view P x
  have hd : header z i=true := (view_header P x i).trans H
  have held : (P.byte x i).getLsbD 91=true ∨
      (P.byte x i).getLsbD 89=true := by
    rcases J with rfl|rfl
    · exact .inl L.2.1
    · exact .inr L.2.1
  have no : (P.byte x i).getLsbD 90=false := by
    apply Bool.eq_false_iff.mpr
    intro W
    have C := L.1 W
    rcases held with A|A
    · exact Bool.noConfusion (C.1.symm.trans A)
    · exact Bool.noConfusion (C.2.symm.trans A)
  have C := ShortGrantRaw.coherent_next_at z e i (P.sep e) hd L.1
  have K := ShortGrantPersistence.held_until_release z e i j
    (P.sep e) hd L.1 L.2.1 R
  have B := ShortReaderMIS1.held_reader_value_raw z e i hd no held
  rw [show (rawNext s z e i).mis1=P.byte (rawNext s x e) i
      from view_next P x X e i] at C K B
  exact ⟨C,K,B.trans L.2.2⟩

theorem reader_run (P : Params s n) (x : Raw s n) (X : Cached P x)
    (i : Fin n) (j : Fin 3) (J : j=0 ∨ j=2)
    (H : P.h i=true) (v : Bool) (L : ReaderLease P i j v x)
    (w : List (Fin n)) (R : NoReleaseTape P i j x w) :
    ReaderLease P i j v (rawRun x w) := by
  induction w generalizing x with
  | nil => exact L
  | cons e w ih =>
    exact ih (rawNext s x e) (P.cached_closed x e X)
      (reader_step P x X i e j J H v L R.1) R.2

-- CHECK: ShortReaderMIS1.lean:60 ReaderWindow; exactly the two windows
-- used in ShortMIS1ReadLease.local_winner_current (lines 213–232).
theorem reader_capture (P : Params s n) (x : Raw s n) (X : Cached P x)
    (e : Fin n) (j : Fin 3) (J : j=0 ∨ j=2)
    (H : P.h e=true)
    (W : readWins true (P.h (rightNeighbor e))
      (P.byte x e) (P.byte x (rightNeighbor e)) j=true) :
    ReaderLease P e j (ShortReaderMIS1.selectedValue (P.byte x e))
      (rawNext s x e) := by
  let z := view P x
  have hd : header z e=true := (view_header P x e).trans H
  have win : readWins true (header z (rightNeighbor e))
      (z e).mis1 (z (rightNeighbor e)).mis1 j=true := by
    simpa only [z,view_header,view_byte] using W
  have grant := ShortReadGrantCapture.capture_winner_has_grant z e j hd win
  have coh := ShortGrantRaw.outgoing_coherent_at z e hd
  have no := ShortWinningReaderRelay.winning_reader_no_old_writer
    (header z (rightNeighbor e)) (z e).mis1 (z (rightNeighbor e)).mis1 j J win
  have S := ShortReaderMIS1.no_writer_frame_raw z e e
    (MISByteCodec.lane 92 1 (by decide)) (.inr ⟨by decide,by decide⟩) hd no
  have B := ShortReaderMIS1.no_writer_frame_raw z e e
    (MISByteCodec.lane 87 2 (by decide)) (.inl ⟨by decide,by decide⟩) hd no
  have keep : ShortReaderMIS1.selectedValue (rawNext s z e e).mis1 =
      ShortReaderMIS1.selectedValue (z e).mis1 := by
    unfold ShortReaderMIS1.selectedValue
    rw [S,B]
  rw [show (rawNext s z e e).mis1=P.byte (rawNext s x e) e
      from view_next P x X e e] at grant coh keep
  exact ⟨coh,grant,keep⟩

-- CHECK: ShortReadFlight.lean:15; ShortReadForward.lean:197,259;
-- ShortReadReverseChart.lean:14,235,307,313. All predicates here
-- depend only on the indicated MIS1 bytes, not on the physical mask.
theorem read_active_congr {h : Fin n → Bool} (C : Chart h)
    (u v : Raw s n) (H : ∀ i,(u i).mis1=(v i).mis1)
    (f : ShortReadFlight.Flight) :
    ShortReadFlight.Active C u f ↔ ShortReadFlight.Active C v f := by
  cases f <;> simp only [ShortReadFlight.Active, ShortReadForward.Forward,
    ShortReadForward.Wait3, ShortReadReverseChart.Returning,
    ShortReadReverseChart.Wait3, ShortReadReverseChart.Rev,
    ShortReadReverseChart.Consumed, ShortResetForwardH2.TrailPrefix,
    ShortResetForwardH2.bits, ShortHelloForward.ClearSuffix,H]

def ReadActive (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (f : ShortReadFlight.Flight) : Prop :=
  ShortReadFlight.Active C (view P x) f

def readNext (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (e : Fin n) (f : ShortReadFlight.Flight) : ShortReadFlight.Flight :=
  ShortReadFlight.next C (view P x) e f

theorem read_step (P : Params s n) (C : Chart P.h) (x : Raw s n)
    (X : Cached P x) (e : Fin n) (f : ShortReadFlight.Flight)
    (L : ShortReadFlight.live f) (A : ReadActive P C x f) :
    ReadActive P C (rawNext s x e) (readNext P C x e f) := by
  have U := ShortReadFlight.read_flight_active_step C (view P x) e
    P.nonself (view_header P x) f L A
  exact (read_active_congr C _ _ (view_next P x X e) _).mp U

def readTrace (P : Params s n) (C : Chart P.h) :
    Raw s n → ShortReadFlight.Flight → List (Fin n) → ShortReadFlight.Flight
  | _, f, [] => f
  | x, f, e::w => readTrace P C (rawNext s x e) (readNext P C x e f) w

def beforeRead (P : Params s n) (C : Chart P.h) :
    Raw s n → ShortReadFlight.Flight → List (Fin n) → Prop
  | _, _, [] => True
  | x, f, e::w => ShortReadFlight.live f ∧
      beforeRead P C (rawNext s x e) (readNext P C x e f) w

-- The ledger records a view of each ACTUAL old capture prefix, and
-- nothing in this recursion runs rawNext on the representative.
def captureTrace (P : Params s n) (C : Chart P.h) :
    Raw s n → ShortReadFlight.Flight →
      ShortReadCaptureTrace.Ledger s n → List (Fin n) →
        ShortReadCaptureTrace.Ledger s n
  | _, _, a, [] => a
  | x, f, a, e::w =>
    captureTrace P C (rawNext s x e) (readNext P C x e f)
      (ShortReadCaptureTrace.advanceLedger C (view P x) e f a) w

theorem read_capture_run (P : Params s n) (C : Chart P.h)
    (w : List (Fin n)) (x : Raw s n) (X : Cached P x)
    (f : ShortReadFlight.Flight) (a : ShortReadCaptureTrace.Ledger s n)
    (A : ReadActive P C x f) (G : ShortReadCaptureTrace.Good C a f)
    (B : beforeRead P C x f w) :
    ReadActive P C (rawRun x w) (readTrace P C x f w) ∧
    ShortReadCaptureTrace.Good C (captureTrace P C x f a w)
      (readTrace P C x f w) := by
  induction w generalizing x f a with
  | nil => exact ⟨A,G⟩
  | cons e w ih =>
    exact ih (rawNext s x e) (P.cached_closed x e X)
      (readNext P C x e f)
      (ShortReadCaptureTrace.advanceLedger C (view P x) e f a)
      (read_step P C x X e f B.1 A)
      (ShortReadCaptureTrace.good_step C (view P x) e (view_header P x) f A a G)
      B.2

def FencedOn (P : Params s n) (C : Chart P.h) (x : Raw s n) : Prop :=
  ShortMIS1ReadLease.Fenced C (view P x)

def FencedTapeOn (P : Params s n) (C : Chart P.h) :
    Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w => FencedOn P C x ∧ FencedTapeOn P C (rawNext s x e) w

theorem read_fenced_tape (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x) (f : ShortReadFlight.Flight)
    (A : ReadActive P C x f) (w : List (Fin n)) (B : beforeRead P C x f w) :
    FencedTapeOn P C x w := by
  induction w generalizing x f with
  | nil => trivial
  | cons e w ih =>
    exact ⟨ShortMIS1ReadLease.read_fenced C (view P x) f A,
      ih (rawNext s x e) (P.cached_closed x e X)
        (readNext P C x e f) (read_step P C x X e f B.1 A) B.2⟩

theorem no_release_of_fenced (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (k : Nat) (K : k<C.L)
    (H : P.h (nextAt C.root k)=true)
    (w : List (Fin n)) (F : FencedTapeOn P C x w) :
    NoReleaseTape P (nextAt C.root k) (C.route.port k) x w := by
  induction w generalizing x with
  | nil => trivial
  | cons e w ih =>
    exact ⟨fun _ => F.1 k K ((view_header P x _).trans H),
      ih (rawNext s x e) F.2⟩

-- Explicit history of one sample through the present cut. The last
-- conjunct must be established by READ/post-READ phase induction,
-- never by a snapshot check of the current grant alone.
def RetainedCapture (P : Params s n) (i : Fin n) (j : Fin 3)
    (v : Bool) (y : Raw s n) : Prop :=
  ∃ x : Raw s n, ∃ w : List (Fin n),
    Cached P x ∧ P.h i=true ∧
    readWins true (P.h (rightNeighbor i))
      (P.byte x i) (P.byte x (rightNeighbor i)) j=true ∧
    v=ShortReaderMIS1.selectedValue (P.byte x i) ∧
    NoReleaseTape P i j (rawNext s x i) w ∧
    y=rawRun (rawNext s x i) w

theorem retained_value (P : Params s n) (i : Fin n) (j : Fin 3)
    (J : j=0 ∨ j=2) (v : Bool) (y : Raw s n)
    (R : RetainedCapture P i j v y) :
    ReaderLease P i j v y := by
  obtain ⟨x,w,X,H,W,V,F,E⟩ := R
  rw [E,V]
  exact reader_run P (rawNext s x i) (P.cached_closed x i X) i j J H _
    (reader_capture P x X i j J H W) w F

-- This is the final value relay, with descriptor identity and both
-- actual samples explicit. It does not assume the desired NOR equality.
theorem protected_of_captures (G : ShortMISLift.Geometry s n)
    (x : Raw s n) (e : Fin n) (i : Lower G.P.h) (b : BitVec 96)
    (L : RetainedCapture G.P (G.ring.left i).val 0 (b.getLsbD 74) x)
    (R : RetainedCapture G.P (G.ring.right i).val 2 (b.getLsbD 72) x)
    (D : issuedDescriptor b=(oldK (G.P.h e) (G.P.byte x e) 0).payload) :
    ProtectedAt G x e i := by
  have A := retained_value G.P _ 0 (.inl rfl) _ x L
  have B := retained_value G.P _ 2 (.inr rfl) _ x R
  refine ⟨b,?_,?_,D⟩
  · change b.getLsbD 74=ShortByteReadouts.misSelected
      (G.P.byte x (G.ring.left i).val)
    rw [←ShortH2Final.selected_readout]
    exact A.2.2.symm
  · change b.getLsbD 72=ShortByteReadouts.misSelected
      (G.P.byte x (G.ring.right i).val)
    rw [←ShortH2Final.selected_readout]
    exact B.2.2.symm

open ShortReadCaptureTrace in
theorem advance_sample_local (C : Chart h) (x : Raw s n) (e : Fin n)
    (f : ShortReadFlight.Flight) (a : Ledger s n) (j : Fin 3) (p : Sample s n)
    (H : advanceLedger C x e f a j=some p) :
    a j=some p ∨ ∃ i d, f=.forward i d ∧ e=nextAt C.root i ∧
      C.route.port i=j ∧ ShortReadCaptureBits.wins x e j=true ∧ p=⟨x,e⟩ := by
  cases f with
  | returning => exact .inl H
  | consumed => exact .inl H
  | forward i d =>
    by_cases E : e=nextAt C.root i
    · rw [show advanceLedger C x e (.forward i d) a=push a x e (C.route.port i)
        by simp [advanceLedger,E]] at H
      unfold push at H
      split at H
      · rename_i K
        obtain ⟨J,W⟩ := K
        exact .inr ⟨i,d,rfl,E,J.symm,by rwa [J],(Option.some.inj H).symm⟩
      · exact .inl H
    · exact .inl (by simpa [advanceLedger,E] using H)

open ShortReadCaptureTrace in
theorem actual_sample_origin (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (f : ShortReadFlight.Flight) (a : Ledger s n)
    (w : List (Fin n)) (j : Fin 3) (p : Sample s n)
    (S : captureTrace P C x f a w j=some p) :
    a j=some p ∨ ∃ (lead tail : List (Fin n)) (k d : Nat),
      w=lead++p.edge::tail ∧ p.old=view P (rawRun x lead) ∧
      readTrace P C x f lead=.forward k d ∧
      p.edge=nextAt C.root k ∧ C.route.port k=j ∧
      ShortReadCaptureBits.wins p.old p.edge j=true := by
  induction w generalizing x f a with
  | nil => exact .inl S
  | cons e w ih =>
    have Q : captureTrace P C (rawNext s x e) (readNext P C x e f)
      (advanceLedger C (view P x) e f a) w j=some p := S
    rcases ih _ _ _ Q with T|⟨lead,tail,k,d,E,X,F,M,J,W⟩
    · rcases advance_sample_local C (view P x) e f a j p T with K|⟨k,d,F,M,J,W,E⟩
      · exact .inl K
      · subst p
        exact .inr ⟨[],w,k,d,rfl,rfl,F,M,J,W⟩
    · refine .inr ⟨e::lead,tail,k,d,?_,X,F,M,J,W⟩
      rw [E]
      rfl
end L4.ShortMISPublicationHistoryLocal
open L4 AllSizeProtocol PhysicalCustody MISByteCodec
open L4 ShortResetChart ShortResetCycle ShortResetMIS1Ring
open L4 ShortResetForwardH2 ShortResetRow ShortResetFlow
open L4 ShortMISEngine ShortMISSheetParked ShortMISPublicationLift
open L4.ReportStaticSpacing (Lower)

namespace L4.ShortMISPublicationHistoryLocal
variable {s n : Nat}

theorem parked_view_iff (P : Params s n) (C : Chart P.h) (x : Raw s n) :
    ShortMISLift.Parked P C x ↔ ShortResetHelloSplice.Parked C (view P x) := by
  constructor
  · intro A
    exact ⟨⟨by decide,A.1.1,A.1.2.1,A.1.2.2⟩,A.2⟩
  · intro A
    exact ⟨⟨A.1.2.1,A.1.2.2.1,A.1.2.2.2⟩,A.2⟩

-- CHECK: ShortFiveRivalFence.lean:42 NoTerminal;
-- ShortHelloForward.lean:198ff BeforeTurn, ClearSuffix, NoGrants;
-- ShortEmptyOwnership.lean:57 Clear.
theorem no_terminal_congr {h : Fin n → Bool} (C : Chart h)
    (u v : Raw s n) (H : ∀ i,(u i).mis1=(v i).mis1) :
    ShortFiveRivalFence.NoTerminal C u ↔ ShortFiveRivalFence.NoTerminal C v := by
  simp only [ShortFiveRivalFence.NoTerminal,ShortResetHelloSplice.Parked,
    ShortClearLaunch.ClearIssue,ShortEmptyOwnership.Clear,
    ShortHelloForward.BeforeTurn,ShortHelloForward.Wait1,
    ShortHelloForward.ClearSuffix,ShortHelloForward.NoGrants,
    ShortResetForwardH2.TrailPrefix,ShortResetForwardH2.bits,H]

theorem right_rival_step (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x) (e : Fin n)
    (A : ShortFiveRivalFence.NoTerminal C (view P x))
    (E : e≠ShortHelloForward.terminalMark C.route) :
    ShortFiveRivalFence.NoTerminal C (view P (rawNext s x e)) := by
  let z := view P x
  rcases A with Park|⟨k,F,S,G⟩
  · by_cases D : e=RearTrace.predecessor C.root
    · subst e
      have U := ShortHelloFlight.actual_launch C z (view_header P x) Park
      apply (no_terminal_congr C _ _ (view_next P x X _) ).mp
      exact .inr ⟨0,U.2.1,U.2.2,U.1⟩
    · exact .inl ((parked_view_iff P C _).mp
        (ShortMISSheetParked.parked_nondoor P C x X
          ((parked_view_iff P C x).mpr Park) e D))
  · apply (no_terminal_congr C _ _ (view_next P x X e)).mp
    exact .inr ⟨ShortHelloForward.ahead C.route k e,
      ShortHelloForward.before_turn_step C.route z e (P.sep e)
        (view_header P x) k F E,
      ShortHelloForward.clear_suffix_step C.route z e (P.sep e)
        (view_header P x) k S,
      ShortHelloForward.no_grants_step C.route z e (P.sep e)
        (view_header P x) k F S G⟩

theorem right_rival_run (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x)
    (A : ShortFiveRivalFence.NoTerminal C (view P x))
    (w : List (Fin n)) (E : ShortHelloForward.terminalMark C.route ∉ w) :
    ShortFiveRivalFence.NoTerminal C (view P (rawRun x w)) := by
  induction w generalizing x with
  | nil => exact A
  | cons e w ih =>
    exact ih (rawNext s x e) (P.cached_closed x e X)
      (right_rival_step P C x X e A (fun K => E (by simp [K])))
      (fun K => E (List.mem_cons_of_mem _ K))

theorem left_rival_run (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x) (A : ShortMISLift.Parked P C x)
    (w : List (Fin n)) (E : RearTrace.predecessor C.root ∉ w) :
    ShortMISLift.Parked P C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact A
  | cons e w ih =>
    exact ih (rawNext s x e) (P.cached_closed x e X)
      (ShortMISSheetParked.parked_nondoor P C x X A e
        (fun K => E (by simp [K])))
      (fun K => E (List.mem_cons_of_mem _ K))

-- CHECK: ShortMISLift.lean: family, rival_fences; ShortResetWatch.watch.
theorem actual_rivals_fenced (G : ShortMISLift.Geometry s n)
    (i : Lower G.P.h) (x : Raw s n) (X : Cached G.P x)
    (A : ShortMISLift.FiveParked G.P (G.family i) x)
    (w : List (Fin n))
    (W : ∀ e∈w,e∈ShortResetWatch.watch (G.family i 2))
    (j : Fin 5) (J : j≠2) :
    ShortPreReadGrants.NoAsk (G.family i j).route (view G.P (rawRun x w)) ∧
    ShortHelloForward.NoGrants (G.family i j).route (view G.P (rawRun x w)) := by
  let C := G.family i j
  have F := G.rival_fences i
  have ne : j.val≠2 := fun E => J (Fin.ext E)
  have B : ShortFiveRivalFence.NoTerminal C (view G.P (rawRun x w)) := by
    by_cases L : j.val<2
    · have K := left_rival_run G.P C x X (A j) w
        (fun E => F.1 j L (W _ E))
      exact .inl ((parked_view_iff G.P C _).mp K)
    · have K : ShortHelloForward.terminalMark C.route ∉ w := by
        intro E
        exact F.2 j (by omega) (W _ E)
      exact right_rival_run G.P C x X
        (.inl ((parked_view_iff G.P C x).mp (A j))) w K
  refine ⟨ShortFiveRivalFence.no_terminal_no_ask C _
    (view_header G.P (rawRun x w)) B,?_⟩
  rcases B with K|⟨_,_,_,K⟩
  · exact K.2
  · exact K

end L4.ShortMISPublicationHistoryLocal


namespace L4.ShortMISPublicationHistoryLocal
variable {s n : Nat}

theorem actual_successful_read_file (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x)
    (I : ShortClearLaunch.ClearIssue C (view P x) 3)
    (w : List (Fin n)) (d : Fin 64)
    (B : beforeRead P C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w)
    (D : readTrace P C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w
        = .consumed true d) :
    let z := rawNext s x (RearTrace.predecessor C.root)
    let a := captureTrace P C z (.forward 0 64) (fun _ => none) w
    let file := ShortReadResult.fileField.read (P.byte (rawRun z w) C.root)
    ShortReadCaptureTrace.Covers C a C.L ∧
      (∀ j : Fin 3, file.getLsbD (5-j.val) = ShortReadCaptureTrace.select (a j) ∧
        file.getLsbD (2-j.val) = ShortReadCaptureTrace.value (a j)) ∧
      (∀ j p, a j = some p → ∃ (lead tail : List (Fin n)) (k b : Nat),
        w = lead ++ p.edge :: tail ∧ p.old = view P (rawRun z lead) ∧
        readTrace P C z (.forward 0 64) lead = .forward k b ∧
        p.edge = nextAt C.root k ∧ C.route.port k = j ∧
        ShortReadCaptureBits.wins p.old p.edge j = true) := by
  let e := RearTrace.predecessor C.root
  let z := rawNext s x e
  have init : ReadActive P C z (.forward 0 64) :=
    (read_active_congr C _ _ (view_next P x X e) _).mp
      (ShortReadForward.forward_from_actual_issue3 C (view P x) (view_header P x) I)
  have R := read_capture_run P C w z (P.cached_closed x e X) _
    (fun _ => none) init (ShortReadCaptureTrace.initial C) B
  rw [D] at R
  have G := R.2 rfl
  have H := R.1.2 rfl
  change ShortReadResult.fileField.read (P.byte (rawRun z w) C.root) =
    BitVec.ofNat 6 d.val at H
  dsimp only
  refine ⟨G.2, ?_, ?_⟩
  · intro j
    rw [H]
    have Q := G.1 j
    exact ⟨(ShortReadCaptureBits.low_wire d ⟨5-j.val, by omega⟩).trans Q.1,
      (ShortReadCaptureBits.low_wire d ⟨2-j.val, by omega⟩).trans Q.2⟩
  · intro j p S
    rcases actual_sample_origin P C z (.forward 0 64) (fun _ => none) w j p S with K | K
    · cases K
    · exact K

#print axioms epoch_induction
#print axioms actual_successful_read_file
#print axioms protected_of_captures
#print axioms actual_rivals_fenced
end L4.ShortMISPublicationHistoryLocal

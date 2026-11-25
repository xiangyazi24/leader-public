import Leader.L4.ShortMISPublicationFlight
import Leader.L4.ShortClassifiedOwnerAuth

namespace L4.ShortMISPublicationOwner

open AllSizeProtocol PhysicalCustody MISByteCodec
open ShortResetChart ShortResetCycle ShortResetMIS1Ring
open ShortResetForwardH2 ShortResetFlow ShortResetRow
open ShortClearLaunch ShortReadResult ShortWriteCentreWitness
open ShortMISEngine ShortMISSheetParked ShortMISPublicationLift
open ShortMISPublicationHistoryLocal ShortMISPublicationFlight
open ReportStaticSpacing (Lower)
open ShortMISLift (Geometry)
open ShortOwnerEpochJS (door raw_snoc ResetFull)
open ShortReadCaptureTrace (Ledger Sample)
open ShortClassifiedOwnerAuth (Fresh)

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

variable {s n : Nat} {h : Fin n → Bool}

/-! A. All these congruences concern only the full MIS1 byte.
The actual step always uses the representative of the OLD real state.
No proposition about its H2 geometry is used. -/

theorem issue_congr (C : Chart h) (u v : Raw s n)
    (B : ∀ q, (u q).mis1=(v q).mis1) (op : Nat) :
    ClearIssue C u op ↔ ClearIssue C v op := by
  simp only [ClearIssue, ShortEmptyOwnership.Clear, bits, B]

theorem grants_congr (C : Chart h) (u v : Raw s n)
    (B : ∀ q, (u q).mis1=(v q).mis1) :
    ShortHelloForward.NoGrants C.route u ↔
      ShortHelloForward.NoGrants C.route v := by
  simp only [ShortHelloForward.NoGrants,B]

theorem parked_congr (C : Chart h) (u v : Raw s n)
    (B : ∀ q, (u q).mis1=(v q).mis1) :
    ShortResetHelloSplice.Parked C u ↔
      ShortResetHelloSplice.Parked C v := by
  unfold ShortResetHelloSplice.Parked
  rw [issue_congr C u v B 1, grants_congr C u v B]

-- CHECK: ShortResetCycle.lean: Active/Complete/Wait0;
-- ShortResetReleased.lean: Released; ShortOwnerEpochJS.lean:133.
theorem reset_full_congr (C : Chart h) (u v : Raw s n)
    (B : ∀ q, (u q).mis1=(v q).mis1) (st : Stage) :
    ResetFull C u st ↔ ResetFull C v st := by
  cases st <;>
    simp only [ResetFull, ShortResetCycle.Active, ShortResetCycle.Complete,
      ShortResetCycle.Wait0, ShortResetReleased.Released,
      ShortResetReverseChart.Rev, ShortHelloForward.ClearSuffix,
      TrailPrefix,bits,B]

-- CHECK: ShortHelloFlight.lean:15; ShortHelloForward.lean:
-- BeforeTurn, Wait1, ClearSuffix; ShortHelloReverseChart:Returning.
theorem hello_congr (C : Chart h) (u v : Raw s n)
    (B : ∀ q, (u q).mis1=(v q).mis1) (st : Stage) :
    ShortHelloFlight.Flight C u st ↔
      ShortHelloFlight.Flight C v st := by
  cases st <;>
    simp only [ShortHelloFlight.Flight, ShortHelloForward.NoGrants,
      ShortHelloForward.BeforeTurn, ShortHelloForward.Wait1,
      ShortHelloForward.ClearSuffix, ShortHelloReverseChart.Returning,
      ShortHelloReverseChart.Wait1, ShortHelloReverseChart.Rev,
      ClearIssue, ShortEmptyOwnership.Clear, TrailPrefix,bits,B]

-- CHECK: ShortAdmitFlight.lean:29; ShortAdmitFlightSync.lean:
-- Fwd/Rev/Wait2. Valid is independent of the raw word.
theorem admit_congr (C : Chart h) (u v : Raw s n)
    (B : ∀ q, (u q).mis1=(v q).mis1) (g : Nat)
    (f : ShortAdmitFlight.State) :
    ShortAdmitFlight.Flight C u g f ↔
      ShortAdmitFlight.Flight C v g f := by
  cases f <;>
    simp only [ShortAdmitFlight.Flight, ShortHelloForward.NoGrants,
      ShortAdmitFlightSync.Fwd, ShortAdmitFlightSync.Rev,
      ShortAdmitFlightSync.Wait2, ClearIssue, ShortEmptyOwnership.Clear,
      bits,B]

theorem next_issue (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x) (e : Fin n) (op : Nat)
    (I : ClearIssue C (rawNext s (view P x) e) op) :
    ClearIssue C (view P (rawNext s x e)) op :=
  (issue_congr C _ _ (view_next P x X e) op).mp I

theorem next_grants (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x) (e : Fin n)
    (I : ShortHelloForward.NoGrants C.route (rawNext s (view P x) e)) :
    ShortHelloForward.NoGrants C.route (view P (rawNext s x e)) :=
  (grants_congr C _ _ (view_next P x X e)).mp I

/-! B. Geometry of arbitrary charts of the frozen mask. Use the three
actual lower gaps; no H1 two-or-three bound enters this module. -/

private theorem lane0 (a b k : Nat) : ShortResetChart.lane a b k=0 ↔ k<a := by
  by_cases A : k<a
  · simp [ShortResetChart.lane,A]
  · by_cases B : k<a+b <;> simp [ShortResetChart.lane,A,B]

private theorem lane1 (a b k : Nat) :
    ShortResetChart.lane a b k=1 ↔ a≤k ∧ k<a+b := by
  by_cases A : k<a
  · simp [ShortResetChart.lane,A,show ¬ a≤k by omega]
  · by_cases B : k<a+b <;> simp [ShortResetChart.lane,A,B,show a≤k by omega]

private theorem lane2 (a b k : Nat) :
    ShortResetChart.lane a b k=2 ↔ a+b≤k := by
  by_cases A : k<a
  · simp [ShortResetChart.lane,A,show ¬ a+b≤k by omega]
  · by_cases B : k<a+b
    · simp [ShortResetChart.lane,A,B,show ¬ a+b≤k by omega]
    · simp [ShortResetChart.lane,A,B,show a+b≤k by omega]

structure Shape (C : Chart h) : Prop where
  ap : 0<C.a
  bp : 0<C.b
  tail : C.a+C.b<C.L
  heads : ∀ k, k<C.L →
    (h (nextAt C.root k)=true ↔ k=0 ∨ k=C.a ∨ k=C.a+C.b)

-- CHECK: ShortMISLift.lean:118–138. The chart's second gap is
-- definitionally the successor's width (like chart_a).
theorem canonical_b (G : Geometry s n) (i : Lower G.P.h) :
    (G.chart i).b=G.width (G.ring.right i) := rfl

theorem canonical_shape (G : Geometry s n) (i : Lower G.P.h) :
    Shape (G.chart i) := by
  let j := G.ring.right i
  let k := G.ring.right j
  let a := G.width i
  let b := G.width j
  let c := G.width k
  let C := G.chart i
  have F := (G.width_spec i).2.2
  have H : ShortLayerGeometry.Gap G.P.h (nextAt i.val a) b :=
    (G.width_spec j).2.2
  have I : ShortLayerGeometry.Gap G.P.h
      (nextAt (nextAt i.val a) b) c := (G.width_spec k).2.2
  have ap : 0<a := F.positive
  have bp : 0<b := H.positive
  have cp : 0<c := I.positive
  have ca : C.a=a := rfl
  have cb : C.b=b := rfl
  have cl : C.L=a+b+c := G.chart_length i
  have cr : C.root=i.val := rfl
  change Shape C
  refine ⟨by omega,by omega,by omega,?_⟩
  intro t T
  by_cases Z : t=0
  · subst t
    have HH : G.P.h (nextAt C.root 0)=true := C.rootHeader
    exact ⟨fun _ => .inl rfl, fun _ => HH⟩
  · rw [cr,ca,cb]
    have J := ShortLayerGeometry.three_gap_exact F H I t
      (by omega : 0<t) (by omega : t≤a+b+c)
    rw [J]
    omega

-- The port sequence determines both breakpoints when the comparison
-- chart actually has all three nonempty portions. This avoids the
-- H2Ready-dependent chart_eq_of_root in ShortClassifiedOwnerAuth.
theorem chart_eq_shape (C D : Chart h) (R : C.root=D.root)
    (S : Shape D) : C=D := by
  obtain ⟨L,U⟩ := ShortReadCaptureGeometry.chart_unique C D R
  have A0 : ShortResetChart.lane C.a C.b (D.a-1)=0 :=
    (U _ (by have := S.ap; have := S.tail; omega)).trans
      ((lane0 _ _ _).mpr (by have := S.ap; omega))
  have A1 : ShortResetChart.lane C.a C.b D.a=1 :=
    (U _ (by have := S.tail; omega)).trans
      ((lane1 _ _ _).mpr ⟨by omega,by have := S.bp; omega⟩)
  have B1 : ShortResetChart.lane C.a C.b (D.a+D.b-1)=1 :=
    (U _ (by have := S.tail; omega)).trans
      ((lane1 _ _ _).mpr ⟨by have := S.bp; omega,by have := S.bp; omega⟩)
  have B2 : ShortResetChart.lane C.a C.b (D.a+D.b)=2 :=
    (U _ (by have := S.tail; omega)).trans
      ((lane2 _ _ _).mpr (by omega))
  have p := (lane0 _ _ _).mp A0
  have q := (lane1 _ _ _).mp A1
  have r := (lane1 _ _ _).mp B1
  have t := (lane2 _ _ _).mp B2
  have ca : C.a=D.a := by have := S.ap; omega
  have cb : C.b=D.b := by have := S.bp; omega
  -- CHECK: ShortResetCycle.lean:44–55 (four data fields).
  cases C with
  | mk cr ca' cb' cl cp ctl rp rh dst =>
    cases D with
    | mk dr da db dl dp dtl rp' rh' dst' =>
      dsimp only at R ca cb L
      subst dr
      subst da
      subst db
      subst dl
      rfl

theorem chart_shape (G : Geometry s n) (C : Chart G.P.h) :
    Shape C := by
  let i : Lower G.P.h := ⟨C.root,C.rootHeader⟩
  have Q := canonical_shape G i
  have E : C=G.chart i := chart_eq_shape C _ rfl Q
  rw [E]
  exact Q

theorem centre_write {C : Chart h} (S : Shape C) :
    C.a+1<C.L ∧ ∀ k, k<C.L →
      (h (nextAt C.root k)=true ∧ C.route.port k=1 ↔ k=C.a) := by
  have ap := S.ap
  have bp := S.bp
  have L := S.tail
  refine ⟨by omega,?_⟩
  intro k K
  change (h (nextAt C.root k)=true ∧ ShortResetChart.lane C.a C.b k=1 ↔ k=C.a)
  rw [S.heads k K,lane1]
  omega

theorem centre_commit {C : Chart h} (S : Shape C) :
    C.a-1+1<C.L ∧ ∀ k, k+1<C.L →
      (h (rightNeighbor (nextAt C.root k))=true ∧
        C.route.port k=0 ∧ C.route.port (k+1)=1 ↔ k=C.a-1) := by
  have ap := S.ap
  have bp := S.bp
  have L := S.tail
  refine ⟨by omega,?_⟩
  intro k K
  change (h (nextAt C.root (k+1))=true ∧ ShortResetChart.lane C.a C.b k=0 ∧
      ShortResetChart.lane C.a C.b (k+1)=1 ↔ k=C.a-1)
  rw [S.heads (k+1) K,lane0,lane1]
  omega

/-! C. The actual capture ledger. Each entry stores its ACTUAL old
view and a physical tape after its capture, not an arbitrary raw word
with the same file bits. The captured ledger is threaded on every
READ step and remains fixed through the write/commit phases. -/

def SampleHeld (P : Params s n) (C : Chart P.h) (j : Fin 3)
    (p : Sample s n) (x : Raw s n) : Prop :=
  ∃ k : Nat, k<C.L ∧ p.edge=nextAt C.root k ∧
    C.route.port k=j ∧ P.h p.edge=true ∧
    ∃ z : Raw s n, ∃ w : List (Fin n),
      Cached P z ∧ p.old=view P z ∧
      readWins true (P.h (rightNeighbor p.edge))
        (P.byte z p.edge) (P.byte z (rightNeighbor p.edge)) j=true ∧
      NoReleaseTape P p.edge j (rawNext s z p.edge) w ∧
      x=rawRun (rawNext s z p.edge) w

def LedgerHeld (P : Params s n) (C : Chart P.h) (a : Ledger s n)
    (x : Raw s n) : Prop :=
  ∀ j p, a j=some p → SampleHeld P C j p x

theorem no_release_snoc (P : Params s n) (i : Fin n) (j : Fin 3)
    (x : Raw s n) (w : List (Fin n)) (e : Fin n)
    (A : NoReleaseTape P i j x w)
    (B : NoRelease P i j (rawRun x w) e) :
    NoReleaseTape P i j x (w++[e]) := by
  induction w generalizing x with
  | nil => exact ⟨B,trivial⟩
  | cons m w ih =>
    exact ⟨A.1,ih (rawNext s x m) A.2 B⟩

theorem sample_keep (P : Params s n) (C : Chart P.h)
    (j : Fin 3) (p : Sample s n) (x : Raw s n) (e : Fin n)
    (A : SampleHeld P C j p x) (F : FencedOn P C x) :
    SampleHeld P C j p (rawNext s x e) := by
  obtain ⟨k,K,E,J,H,z,w,X,O,W,U,Y⟩ := A
  have HH : P.h (nextAt C.root k)=true := by rw [←E]; exact H
  have R : NoRelease P p.edge j x e := by
    intro _
    rw [E,←J]
    exact F k K ((view_header P x _).trans HH)
  refine ⟨k,K,E,J,H,z,w++[e],X,O,W,?_,?_⟩
  · apply no_release_snoc P p.edge j _ w e U
    rw [←Y]
    exact R
  · rw [raw_snoc,←Y]

theorem ledger_keep (P : Params s n) (C : Chart P.h)
    (a : Ledger s n) (x : Raw s n) (e : Fin n)
    (A : LedgerHeld P C a x) (F : FencedOn P C x) :
    LedgerHeld P C a (rawNext s x e) := by
  intro j p H
  exact sample_keep P C j p x e (A j p H) F

theorem ledger_empty (P : Params s n) (C : Chart P.h) (x : Raw s n) :
    LedgerHeld P C (fun _=>none) x := by
  intro j p H
  cases H

theorem sample_retained (P : Params s n) (C : Chart P.h)
    (j : Fin 3) (p : Sample s n) (x : Raw s n)
    (A : SampleHeld P C j p x) :
    RetainedCapture P p.edge j (ShortReadCaptureBits.seenValue p.old p.edge) x := by
  obtain ⟨k,K,E,J,H,z,w,X,O,W,U,Y⟩ := A
  refine ⟨z,w,X,H,W,?_,U,Y⟩
  rw [O]
  exact (ShortReaderMIS1.selectedValue_eq (P.byte z p.edge)).symm

-- This is the one-mark version of actual_sample_origin. Crucially
-- we retain the OLD sample even if the new READ is faulted.
theorem ledger_read_step (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (X : Cached P x) (e : Fin n)
    (f : ShortReadFlight.Flight) (A : ReadActive P C x f)
    (a : Ledger s n) (L : LedgerHeld P C a x) :
    LedgerHeld P C (ShortReadCaptureTrace.advanceLedger C (view P x) e f a)
      (rawNext s x e) := by
  intro j p J
  rcases advance_sample_local C (view P x) e f a j p J with U|U
  · exact sample_keep P C j p x e (L j p U)
      (ShortMIS1ReadLease.read_fenced C (view P x) f A)
  · obtain ⟨k,d,Q,E,V,W,O⟩ := U
    have K : k<C.L := by
      rw [Q] at A
      exact A.1
    -- CHECK: ShortReadCaptureBits.lean:15; this is the exact
    -- old-pair allocator predicate, not a successful reply.
    change (header (view P x) e &&
      readWins (header (view P x) e) (header (view P x) (rightNeighbor e))
        ((view P x e).mis1) ((view P x (rightNeighbor e)).mis1) j)=true at W
    rw [view_header,view_header,view_byte,view_byte] at W
    obtain ⟨H,B⟩ := Bool.and_eq_true_iff.mp W
    rw [H] at B
    subst p
    exact ⟨k,K,E,V,H,x,[],X,rfl,B,trivial,rfl⟩

/-- The successful READ cut stores the actual six bits; both the
selector and data portions are recorded, even though ProtectedAt
only needs the data at the two outer reader sites. -/
def Saved (C : Chart h) (b : BitVec 96) (a : Ledger s n) : Prop :=
  ShortReadCaptureTrace.Covers C a C.L ∧
  ∀ j : Fin 3,
    (fileField.read b).getLsbD (5-j.val)=ShortReadCaptureTrace.select (a j) ∧
    (fileField.read b).getLsbD (2-j.val)=ShortReadCaptureTrace.value (a j)

theorem save_at_consume (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (a : Ledger s n) (d : Fin 64)
    (A : ReadActive P C x (.consumed true d))
    (L : ShortReadCaptureTrace.Good C a (.consumed true d)) :
    Saved C (P.byte x C.root) a := by
  have G := L rfl
  have F : fileField.read (P.byte x C.root)=BitVec.ofNat 6 d.val := A.2 rfl
  refine ⟨G.2,?_⟩
  intro j
  rw [F]
  have Q := G.1 j
  exact ⟨(ShortReadCaptureBits.low_wire d ⟨5-j.val,by omega⟩).trans Q.1,
    (ShortReadCaptureBits.low_wire d ⟨2-j.val,by omega⟩).trans Q.2⟩

/-! D. Fixed saved descriptor and post-READ phases. Write failures may
clear the file; we require retention only along healthy flights. -/

def desc (b : BitVec 96) : Fin 8 :=
  ⟨issuedDescriptor b,(ShortWritePacketCodec.issued_descriptor_valid b).1⟩

theorem desc_valid (b : BitVec 96) : descValid (desc b).val=true :=
  (ShortWritePacketCodec.issued_descriptor_valid b).2

def FileAt (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) : Prop :=
  fileField.read (P.byte x C.root)=fileField.read b

theorem desc_eq (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) (F : FileAt P C b x) :
    issuedDescriptor (P.byte x C.root)=(desc b).val :=
  ShortWriteFileSplice.descriptor_of_same_file b _ F

theorem file_step (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) (X : Cached P x) (e : Fin n)
    (F : FileAt P C b x)
    (S : rightNeighbor e=C.root →
      ShortReadFileHold.FileSafe (P.byte x C.root)
        (oldK true (P.byte x C.root) 0)) :
    FileAt P C b (rawNext s x e) := by
  have R := ShortWriteFileSplice.raw_file_step (view P x) C.root e
    P.nonself ((view_header P x C.root).trans C.rootHeader) S
  rw [view_next P x X e] at R
  exact R.trans F

theorem gap_file_step (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) (X : Cached P x) (e : Fin n)
    (op : Nat) (O : 0<op)
    (I : ClearIssue C (view P x) op) (F : FileAt P C b x) :
    FileAt P C b (rawNext s x e) := by
  apply file_step P C b x X e F
  intro _
  refine .inl ⟨I.2.2.1,?_,?_⟩
  · change 0<get (view P x C.root).mis1 78 3 (by decide)
    rw [I.2.2.2]
    exact O
  · change get (view P x C.root).mis1 78 3 (by decide)<7
    rw [I.2.2.2]
    exact I.1

theorem write_launch_fixed (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) (X : Cached P x) (cmd : Cmd)
    (I : ClearIssue C (view P x) cmd.op) (F : FileAt P C b x) :
    ShortWriteFlight.Active C cmd (desc b)
      (view P (rawNext s x (door C))) (.front 0 false) := by
  obtain ⟨d,D,E,A⟩ := ShortWriteFlight.launch C cmd (view P x) (view_header P x) I
  have Q : d=desc b := Fin.ext (E.trans (desc_eq P C b x F))
  subst d
  exact (write_active_congr C cmd _ _ _
    (view_next P x X (door C)) _).mp A

theorem commit_launch_fixed (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) (X : Cached P x)
    (I : ClearIssue C (view P x) 6) (F : FileAt P C b x) :
    ShortCommitFlight.Active C (desc b)
      (view P (rawNext s x (door C))) (.front 0 .pending) := by
  obtain ⟨d,D,E,A⟩ := ShortCommitFlight.launch C (view P x) (view_header P x) I
  have Q : d=desc b := Fin.ext (E.trans (desc_eq P C b x F))
  subst d
  exact (commit_active_congr C _ _ _ (view_next P x X (door C)) _).mp A

theorem write_file_step (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) (X : Cached P x)
    (cmd : Cmd) (e : Fin n) (f : ShortWriteFlight.Flight)
    (L : ShortWriteFlight.live f)
    (A : ShortWriteFlight.Active C cmd (desc b) (view P x) f)
    (F : ShortWriteFileSplice.healthy f → FileAt P C b x)
    (H : ShortWriteFileSplice.healthy
      (ShortWriteFlight.next C cmd (desc b) (view P x) e f)) :
    FileAt P C b (rawNext s x e) := by
  have B := ShortWriteFileSplice.healthy_before C cmd (desc b) (view P x) e f H
  apply file_step P C b x X e (F B)
  intro _
  exact ShortWriteFileSplice.safe_wait_door C (view P x)
    ((view_header P x C.root).trans C.rootHeader)
    cmd (desc b) (desc_valid b) f L B A

inductive PostPhase (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) : Prop where
  | gap4 : ClearIssue C (view P x) 4 → FileAt P C b x → PostPhase P C b x
  | gap5 : ClearIssue C (view P x) 5 → FileAt P C b x → PostPhase P C b x
  | gap6 : ClearIssue C (view P x) 6 → FileAt P C b x → PostPhase P C b x
  | write (cmd : Cmd) (f : ShortWriteFlight.Flight) :
      ShortWriteFlight.Active C cmd (desc b) (view P x) f →
      ShortWriteFlight.live f →
      (ShortWriteFileSplice.healthy f → FileAt P C b x) →
      PostPhase P C b x
  | commit (f : ShortCommitFlight.Flight) :
      ShortCommitFlight.Active C (desc b) (view P x) f →
      ShortCommitFlight.live f → PostPhase P C b x

theorem post_fenced (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) (A : PostPhase P C b x) :
    FencedOn P C x := by
  cases A with
  | gap4 I _ | gap5 I _ | gap6 I _ =>
    exact ShortMIS1ReadLease.clear_fenced C (view P x) I.2.1
  | write cmd f I _ _ =>
    exact ShortMIS1ReadLease.write_fenced C (view P x) cmd (desc b)
      (desc_valid b) f I
  | commit f I _ =>
    exact ShortMIS1ReadLease.commit_fenced C (view P x) (desc b)
      (desc_valid b) f I

theorem post_step (G : Geometry s n) (N : 9<n) (C : Chart G.P.h)
    (b : BitVec 96) (x : Raw s n) (X : Cached G.P x) (e : Fin n)
    (A : PostPhase G.P C b x) :
    PostPhase G.P C b (rawNext s x e) ∨
      ClearIssue C (view G.P (rawNext s x e)) 0 := by
  let P := G.P
  let z := view P x
  let y := rawNext s x e
  let d := desc b
  have D := desc_valid b
  have S := chart_shape G C
  cases A with
  | gap4 I F =>
    by_cases E : e=door C
    · subst e
      exact .inl (.write .stage (.front 0 false)
        (write_launch_fixed P C b x X .stage I F) (by trivial)
        (fun _=>gap_file_step P C b x X _ 4 (by decide) I F))
    · exact .inl (.gap4
        (next_issue P C x X e 4
          (clear_issue_nondoor C z (view_header P x) 4 I e E))
        (gap_file_step P C b x X e 4 (by decide) I F))
  | gap5 I F =>
    by_cases E : e=door C
    · subst e
      exact .inl (.write .seal (.front 0 false)
        (write_launch_fixed P C b x X .seal I F) (by trivial)
        (fun _=>gap_file_step P C b x X _ 5 (by decide) I F))
    · exact .inl (.gap5
        (next_issue P C x X e 5
          (clear_issue_nondoor C z (view_header P x) 5 I e E))
        (gap_file_step P C b x X e 5 (by decide) I F))
  | gap6 I F =>
    by_cases E : e=door C
    · subst e
      exact .inl (.commit (.front 0 .pending)
        (commit_launch_fixed P C b x X I F) (by trivial))
    · exact .inl (.gap6
        (next_issue P C x X e 6
          (clear_issue_nondoor C z (view_header P x) 6 I e E))
        (gap_file_step P C b x X e 6 (by decide) I F))
  | write cmd f I L F =>
    have U := (write_actual_step P C N x X (centre_write S) cmd d D e f L I).1
    have V : ShortWriteFileSplice.healthy (ShortWriteFlight.next C cmd d z e f) →
        FileAt P C b y :=
      write_file_step P C b x X cmd e f L I F
    -- CHECK: ShortMISPublicationFlight.lean:28–42; z,d,y
    -- are definitional aliases of its old-view arguments.
    change ShortWriteFlight.Active C cmd d (view P y)
      (ShortWriteFlight.next C cmd d z e f) at U
    generalize Q : ShortWriteFlight.next C cmd d z e f=f' at U V
    cases f' with
    | front i bad => exact .inl (.write cmd _ U (by trivial) V)
    | back i bad => exact .inl (.write cmd _ U (by trivial) V)
    | done bad =>
      cases bad with
      | true =>
        have R : ClearIssue C (view P y) 0 :=
          ShortPreReadGrants.clear_issue_of_pc C _ 0 (by decide) U.1 U.2
        exact .inr R
      | false =>
        cases cmd with
        | stage =>
          have R : ClearIssue C (view P y) 5 :=
            ShortPreReadGrants.clear_issue_of_pc C _ 5 (by decide) U.1 U.2
          exact .inl (.gap5 R (V rfl))
        | «seal» =>
          have R : ClearIssue C (view P y) 6 :=
            ShortPreReadGrants.clear_issue_of_pc C _ 6 (by decide) U.1 U.2
          exact .inl (.gap6 R (V rfl))
  | commit f I L =>
    have U := (commit_actual_step P C N x X (centre_commit S) d D e f L I).1
    change ShortCommitFlight.Active C d (view P y)
      (ShortCommitFlight.next C d z e f) at U
    generalize Q : ShortCommitFlight.next C d z e f=f' at U
    cases f' with
    | front i p => exact .inl (.commit _ U (by trivial))
    | back i p => exact .inl (.commit _ U (by trivial))
    | done p =>
      exact .inr (ShortPreReadGrants.clear_issue_of_pc C _ 0
        (by decide) U.1 U.2)

/-! E. The actual all-mark owner automaton. The read constructor
carries the cursor and real capture ledger; the post constructor
carries its fixed successful file. An exit to idle drops the proof
ledger, not a physical grant. The following real RESET releases
those grants and reestablishes the parked seed. -/

inductive Owner (P : Params s n) (C : Chart P.h) (x : Raw s n) : Prop where
  | idle : ClearIssue C (view P x) 0 → Owner P C x
  | parked : ShortResetHelloSplice.Parked C (view P x) → Owner P C x
  | reset (st : Stage) :
      st≠.done → ResetFull C (view P x) st → Owner P C x
  | hello (st : Stage) :
      ShortHelloFlight.Flight C (view P x) st → Owner P C x
  | admit (f : ShortAdmitFlight.State) :
      ShortAdmitFlight.Live f →
      ShortAdmitFlight.Flight C (view P x) C.a f → Owner P C x
  | ready3 : ClearIssue C (view P x) 3 →
      ShortHelloForward.NoGrants C.route (view P x) → Owner P C x
  | reading (f : ShortReadFlight.Flight) (a : Ledger s n) :
      ShortReadFlight.live f → ReadActive P C x f →
      ShortReadCaptureTrace.Good C a f → LedgerHeld P C a x →
      Owner P C x
  | post (b : BitVec 96) (a : Ledger s n) :
      Saved C b a → LedgerHeld P C a x → PostPhase P C b x →
      Owner P C x

def OwnerInv (P : Params s n) (C : Chart P.h) (x : Raw s n) : Prop :=
  Cached P x ∧ Owner P C x

theorem owner_step (G : Geometry s n) (N : 9<n) (C : Chart G.P.h)
    (x : Raw s n) (X : Cached G.P x) (e : Fin n)
    (A : Owner G.P C x) : Owner G.P C (rawNext s x e) := by
  let P := G.P
  let z := view P x
  let y := rawNext s x e
  have H : ∀ i,header z i=P.h i := view_header P x
  have B : ∀ i,(rawNext s z e i).mis1=(view P y i).mis1 :=
    view_next P x X e
  obtain ⟨gp,gL,_,gates⟩ := P.chart_gate C
  cases A with
  | idle I =>
    by_cases E : e=door C
    · subst e
      exact .reset (.fwd 0) (by decide)
        ((reset_full_congr C _ _ (view_next P x X (door C)) _).mp
          (ShortOwnerEpochJS.reset_launch C z H I))
    · exact .idle (next_issue P C x X e 0
        (clear_issue_nondoor C z H 0 I e E))
  | parked I =>
    by_cases E : e=door C
    · subst e
      exact .hello (.fwd 0)
        ((hello_congr C _ _ (view_next P x X (door C)) _).mp
          (ShortHelloFlight.actual_launch C z H I))
    · exact .parked ((parked_congr C _ _ B).mp
        (ShortResetHelloSplice.parked_nondoor C z H I e E))
  | reset st L I =>
    have U := (reset_full_congr C _ _ B _).mp
      (ShortOwnerEpochJS.reset_step C z (by omega) H e st L I)
    by_cases E : nextStage C e st=.done
    · rw [E] at U
      exact .parked (ShortResetHelloSplice.parked_after_consume C _
        U.1 U.2.1)
    · exact .reset _ E U
  | hello st I =>
    cases st with
    | done =>
      change ShortHelloForward.NoGrants C.route z ∧ ClearIssue C z 2 at I
      by_cases E : e=door C
      · subst e
        exact .admit (.forward 0 false 0) (by trivial)
          ((admit_congr C _ _ (view_next P x X (door C)) C.a _).mp
            (ShortAdmitFlight.launch C z H C.a gp I.2 I.1))
      · have U := ShortOwnerEpochJS.clear_nondoor_no_grants C z H 2 I.2 I.1 e E
        exact .hello .done ⟨next_grants P C x X e U.2,
          next_issue P C x X e 2 U.1⟩
    | fwd i =>
      exact .hello _ ((hello_congr C _ _ B _).mp
        (ShortHelloFlight.active_step C z H e (.fwd i) (by trivial) I))
    | rev i =>
      exact .hello _ ((hello_congr C _ _ B _).mp
        (ShortHelloFlight.active_step C z H e (.rev i) (by trivial) I))
  | admit f L I =>
    have Gt : ∀ k,k<C.L →
        (ShortAdmitForward.gated C z k=true ↔ k=C.a) := by
      intro k K
      change (ShortAdmitForward.gated C (view P x) k=true ↔ k=C.a)
      simpa only [ShortAdmitForward.gated,view_header,view_byte]
        using gates x X k K
    have U := (admit_congr C _ _ B C.a _).mp
      (ShortAdmitFlight.active_step
        (ShortAdmitSameGeneration.wire_frames (s:=s) (n:=n))
        C z H e C.a gp gL Gt f L I)
    generalize Q : ShortAdmitFlight.next C C.a e f=f' at U
    cases f' with
    | forward i w r => exact .admit _ (by trivial) U
    | reverse i w => exact .admit _ (by trivial) U
    | done won =>
      cases won with
      | false => exact .idle U.2
      | true => exact .ready3 U.2 U.1
  | ready3 I L =>
    by_cases E : e=door C
    · subst e
      have U : ReadActive P C (rawNext s x (door C)) (.forward 0 64) :=
        (read_active_congr C _ _ (view_next P x X (door C)) _).mp
          (ShortReadForward.forward_from_actual_issue3 C z H I)
      exact .reading (.forward 0 64) (fun _=>none) (by trivial) U
        (ShortReadCaptureTrace.initial C) (ledger_empty P C _)
    · have U := ShortOwnerEpochJS.clear_nondoor_no_grants C z H 3 I L e E
      exact .ready3 (next_issue P C x X e 3 U.1) (next_grants P C x X e U.2)
  | reading f a L I A K =>
    let a' := ShortReadCaptureTrace.advanceLedger C z e f a
    have U : ReadActive P C y (readNext P C x e f) :=
      read_step P C x X e f L I
    have V : ShortReadCaptureTrace.Good C a' (readNext P C x e f) :=
      ShortReadCaptureTrace.good_step C z e H f I a A
    have W : LedgerHeld P C a' y := ledger_read_step P C x X e f I a K
    generalize Q : readNext P C x e f=f' at U V
    cases f' with
    | forward i d => exact .reading _ a' (by trivial) U V W
    | returning i ok d => exact .reading _ a' (by trivial) U V W
    | consumed ok out =>
      -- CHECK: ShortOwnerEpochJS.lean:250–287. read_consume_issue
      -- has only frozen heads and 5≤n, not H2Ready.
      have I' := next_issue P C x X e (if ok then 4 else 0)
        (ShortOwnerEpochJS.read_consume_issue C z (by omega) H e f L I ok out Q)
      cases ok with
      | false => exact .idle I'
      | true =>
        let b := P.byte y C.root
        exact .post b a' (save_at_consume P C y a' out U V) W
          (.gap4 I' rfl)
  | post b a R K A =>
    rcases post_step G N C b x X e A with U|U
    · exact .post b a R (ledger_keep P C a x e K (post_fenced P C b x A)) U
    · exact .idle U

theorem owner_inv_step (G : Geometry s n) (N : 9<n)
    (C : Chart G.P.h) (x : Raw s n) (e : Fin n)
    (A : OwnerInv G.P C x) : OwnerInv G.P C (rawNext s x e) :=
  ⟨G.P.cached_closed x e A.1,owner_step G N C x A.1 e A.2⟩

/-- Seed at this chart's actual completed RESET receipt, not at
the lower permanence time and not at some common five-owner cut. -/
theorem epoch_owner (G : Geometry s n) (N : 9<n)
    (C : Chart G.P.h) (x : Raw s n) (E : ShortMISLift.Epoch G.P C x) :
    Owner G.P C x := by
  apply epoch_induction G.P C (Owner G.P C) ?_ ?_ x E
  · intro y Y A
    exact .parked ((parked_view_iff G.P C y).mp A)
  · intro y e Y A
    exact owner_step G N C y Y e A

/-! F. The exact classified pending extraction. This part consumes
the genuine invariant; it does NOT assume ProtectedAt as a field. -/

def PendingAt (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (k : Nat) : Prop :=
  ∃ b : BitVec 96, ∃ a : Ledger s n,
    Saved C b a ∧ LedgerHeld P C a x ∧
    ShortCommitFlight.Active C (desc b) (view P x) (.front k .pending)

theorem post_pending (P : Params s n) (C : Chart P.h)
    (b : BitVec 96) (x : Raw s n) (a : Ledger s n)
    (R : Saved C b a) (H : LedgerHeld P C a x)
    (A : PostPhase P C b x) (k : Nat) (K : k<C.L)
    (F : Fresh (slot C.route (view P x) k)) :
    PendingAt P C x k := by
  cases A with
  | gap4 I _ | gap5 I _ | gap6 I _ =>
    exact False.elim (ShortClassifiedOwnerAuth.clear_no_fresh C _ I.2.1 k K F)
  | write cmd f I L _ =>
    exact False.elim (ShortClassifiedOwnerAuth.write_no_fresh C _ cmd
      (desc b) (desc_valid b) f I k K F)
  | commit f I L =>
    have J := ShortClassifiedOwnerAuth.commit_fresh_front C _ (desc b)
      (desc_valid b) f I k K F
    rw [J] at I
    exact ⟨b,a,R,H,I⟩

theorem owner_pending (P : Params s n) (C : Chart P.h)
    (x : Raw s n) (A : Owner P C x) (k : Nat) (K : k<C.L)
    (F : Fresh (slot C.route (view P x) k)) : PendingAt P C x k := by
  cases A with
  | idle I =>
    exact False.elim (ShortClassifiedOwnerAuth.clear_no_fresh C _ I.2.1 k K F)
  | parked I =>
    exact False.elim (ShortClassifiedOwnerAuth.clear_no_fresh C _ I.1.2.1 k K F)
  | reset st L I =>
    exact False.elim (ShortClassifiedOwnerAuth.reset_no_fresh C _ st I k K F)
  | hello st I =>
    exact False.elim (ShortClassifiedOwnerAuth.hello_no_fresh C _ st I k K F)
  | admit f L I =>
    exact False.elim (ShortClassifiedOwnerAuth.admit_no_fresh C _ C.a f I k K F)
  | ready3 I _ =>
    exact False.elim (ShortClassifiedOwnerAuth.clear_no_fresh C _ I.2.1 k K F)
  | reading f a L I _ _ =>
    exact False.elim (ShortClassifiedOwnerAuth.read_no_fresh C _ f I k K F)
  | post b a R H I =>
    exact post_pending P C b x a R H I k K F

theorem sample_some (a : Ledger s n) (j : Fin 3)
    (H : (a j).isSome=true) : ∃ p, a j=some p := by
  cases E : a j with
  | none => simp [E] at H
  | some p => exact ⟨p,rfl⟩

theorem left_sample (P : Params s n) (C : Chart P.h)
    (S : Shape C) (x : Raw s n) (b : BitVec 96) (a : Ledger s n)
    (R : Saved C b a) (H : LedgerHeld P C a x) :
    RetainedCapture P C.root 0 (b.getLsbD 74) x := by
  have hd : P.h (nextAt C.root 0)=true := C.rootHeader
  have K := R.1 0 C.positive hd
  rw [C.route.rootPort] at K
  obtain ⟨p,E⟩ := sample_some a 0 K
  have A := H 0 p E
  have W := sample_retained P C 0 p x A
  obtain ⟨k,L,F,J,U,_⟩ := A
  have h' : P.h (nextAt C.root k)=true := by rw [←F]; exact U
  have Z := (S.heads k L).mp h'
  have Q := (lane0 C.a C.b k).mp J
  have O : k=0 := by omega
  have edge : p.edge=C.root := by rw [F,O]; rfl
  have bit := (R.2 (0 : Fin 3)).2
  rw [E] at bit
  -- CHECK: ShortReadResult.lean: file_bit; the value reduction
  -- reads the capture view from the ledger, not the current word.
  have B : b.getLsbD 74=ShortReadCaptureBits.seenValue p.old p.edge :=
    (file_bit b 2 (by decide)).trans bit
  rw [←B,edge] at W
  exact W

theorem right_sample (P : Params s n) (C : Chart P.h)
    (S : Shape C) (x : Raw s n) (b : BitVec 96) (a : Ledger s n)
    (R : Saved C b a) (H : LedgerHeld P C a x) :
    RetainedCapture P (nextAt C.root (C.a+C.b)) 2 (b.getLsbD 72) x := by
  have hd := (S.heads (C.a+C.b) S.tail).mpr (.inr (.inr rfl))
  have J : C.route.port (C.a+C.b)=2 :=
    (lane2 _ _ _).mpr (by omega)
  have K := R.1 (C.a+C.b) S.tail hd
  rw [J] at K
  obtain ⟨p,E⟩ := sample_some a 2 K
  have A := H 2 p E
  have W := sample_retained P C 2 p x A
  obtain ⟨k,L,F,J',U,_⟩ := A
  have h' : P.h (nextAt C.root k)=true := by rw [←F]; exact U
  have Z := (S.heads k L).mp h'
  have Q := (lane2 C.a C.b k).mp J'
  have O : k=C.a+C.b := by have := S.ap; have := S.bp; omega
  have edge : p.edge=nextAt C.root (C.a+C.b) := by rw [F,O]
  have bit := (R.2 (2 : Fin 3)).2
  rw [E] at bit
  have B : b.getLsbD 72=ShortReadCaptureBits.seenValue p.old p.edge :=
    (file_bit b 0 (by decide)).trans bit
  rw [←B,edge] at W
  exact W

/-- Select the actual owner chart using the fixed ring. No H2
selector_change_owner theorem is invoked on the representative.
The classifier supplies the exact old guard and responder site;
the canonical chart supplies the ingress of that responder. -/
theorem classified_pending (G : Geometry s n) (N : 9<n)
    (x : Raw s n) (X : ShortMISLift.Good G.P x) (e : Fin n)
    (i : Lower G.P.h) (E : ShortMISLift.classify G.P x e=some i) :
    let C := G.chart (G.ring.left i)
    nextAt C.root (C.a-1)=e ∧ PendingAt G.P C x (C.a-1) := by
  dsimp only
  let j := G.ring.left i
  let C := G.chart j
  have S := canonical_shape G j
  have ap : 0<C.a := S.ap
  have L : C.a+C.b<C.L := S.tail
  obtain ⟨R,_,guard⟩ := recorded_guard_on G.P x X.1 e i E
  have centre : nextAt C.root C.a=i.val := by
    -- CHECK: ShortMISLift.lean: root_coord successor reduction;
    -- SelectedRingGeometry.lean:126–133 (right is successor).
    change (G.ring.right j).val=i.val
    exact congrArg Subtype.val (G.ring.rl i)
  have next : rightNeighbor (nextAt C.root (C.a-1))=i.val := by
    change nextAt C.root (C.a-1+1)=i.val
    rw [show C.a-1+1=C.a by omega]
    exact centre
  have edge := ShortChartOwnership.right_injective (next.trans R)
  have port : C.route.port (C.a-1)=0 := (lane0 _ _ _).mpr (by omega)
  have K : C.a-1<C.L := by omega
  obtain ⟨D,root,EP⟩ := X.2 C.root C.rootHeader
  have Q := chart_eq_shape D C root S
  rw [Q] at EP
  have A := epoch_owner G N C x EP
  have F : Fresh (slot C.route (view G.P x) (C.a-1)) := by
    change Fresh (oldK (header (view G.P x) (nextAt C.root (C.a-1)))
      ((view G.P x (nextAt C.root (C.a-1))).mis1) (C.route.port (C.a-1)))
    rw [edge,port,view_header,view_byte]
    exact ⟨guard.1,guard.2.1,guard.2.2.1,guard.2.2.2.1⟩
  exact ⟨edge,owner_pending G.P C x A _ K F⟩

theorem classified_protected (G : Geometry s n) (N : 9<n)
    (x : Raw s n) (X : ShortMISLift.Good G.P x) (e : Fin n)
    (i : Lower G.P.h) (E : ShortMISLift.classify G.P x e=some i) :
    ProtectedAt G x e i := by
  let j := G.ring.left i
  let C := G.chart j
  have S := canonical_shape G j
  have ap := S.ap
  obtain ⟨edge,b,a,R,H,A⟩ := classified_pending G N x X e i E
  have LL := left_sample G.P C S x b a R H
  have RR := right_sample G.P C S x b a R H
  have L : C.root=(G.ring.left i).val := rfl
  have R' : nextAt C.root (C.a+C.b)=(G.ring.right i).val := by
    rw [nextAt_add]
    change (G.ring.right (G.ring.right j)).val=(G.ring.right i).val
    rw [show G.ring.right j=i from G.ring.rl i]
  rw [L] at LL
  rw [R'] at RR
  have port : C.route.port (C.a-1)=0 :=
    (lane0 _ _ _).mpr (by have h : 0<C.a := S.ap; omega)
  have W := A.2.2.2.1
  -- CHECK: ShortCommitFlight.lean:33–39; the pending packet is
  -- exactly writeFwd 6 (desc b) false.
  change (kField (C.route.port (C.a-1))).read
    (G.P.byte x (nextAt C.root (C.a-1)))=
      encode (ShortWritePacketCodec.writeFwd 6 (desc b) false) at W
  rw [port,edge] at W
  have O := ShortCommitGenerationEvent.old_commit_token
    (view G.P x) e (desc b) (desc_valid b) false W
  have D : issuedDescriptor b=(oldK (G.P.h e) (G.P.byte x e) 0).payload := by
    rw [←view_header G.P x e,←view_byte G.P x e,O]
    rfl
  exact protected_of_captures G x e i b LL RR D

/-- Exact type consumed by ShortMISPublicationSuppliers.assemble. -/
theorem protected_rows (G : Geometry s n) (N : 9<n) :
    ShortMISPublicationSuppliers.ProtectedRows G := by
  intro x e X i E
  exact classified_protected G N x X e i E

/-- Actual MIS2: D=27, frozen permanent H2 fibre. -/
theorem mis2_protected (N : 63<n) (x : Raw s n)
    (H : ShortH2RawEntrance.PermanentH2 (by omega : 21<n) x) :
    ShortMISPublicationSuppliers.ProtectedRows
      (ShortMISLift.mis2Geometry N x H) :=
  protected_rows _ (by omega)

/-- Actual MIS3: D=81, frozen permanent MIS2 (=PermanentH3) fibre. -/
theorem mis3_protected (N : 189<n) (x : Raw s n)
    (H : ShortMISLift.PermanentH3 (by omega : 63<n) x) :
    ShortMISPublicationSuppliers.ProtectedRows
      (ShortMIS3Entrance.mis3Geometry N x H) :=
  protected_rows _ (by omega)

/-- Precisely the old mixed consumer, now leaving only the two
designated-word suppliers explicit. This is the intended integration
test, not a weakened ProtectedRows premise. -/
theorem mis23_from_h2_only_word (N : 189<n) (x : Raw s n)
    (H : ShortH2RawEntrance.PermanentH2 (by omega : 21<n) x)
    (W2 : ShortMISPublicationSuppliers.FencedWordRows
      (ShortMISLift.mis2Geometry (by omega : 63<n) x H))
    (W3 : ∀ (y : Raw s n)
      (Y : ShortMISLift.PermanentH3 (by omega : 63<n) y),
      ShortMISPublicationSuppliers.FencedWordRows
        (ShortMIS3Entrance.mis3Geometry N y Y)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (ShortMIS3Entrance.PermanentH4 N) x
      ((ShortMISLift.K_H3+ShortMISLift.K_H4)*n^2) :=
  ShortMISPublicationSuppliers.mis23_from_h2 N x H
    (mis2_protected (by omega) x H) W2 (fun y Y=>mis3_protected N y Y) W3

#print axioms owner_inv_step
#print axioms epoch_owner
#print axioms classified_pending
#print axioms protected_rows
#print axioms mis2_protected
#print axioms mis3_protected
#print axioms mis23_from_h2_only_word

end
end L4.ShortMISPublicationOwner


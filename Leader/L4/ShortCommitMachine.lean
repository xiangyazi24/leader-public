import Leader.L4.ShortCommitFlight
import Leader.L4.ShortCommitGenerationEvent
import Leader.L4.ShortWriteFileSplice
import Leader.L4.ShortMIS1ReadLease

namespace L4.ShortCommitMachine

open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2 ShortResetFlow
open ShortResetRow ShortWritePacketCodec
open ShortControllerEntrance ShortReadResult

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev Flight := ShortCommitFlight.Flight
abbrev Status := ShortCommitChartHop.Status

/-- No post-consume step of the old generation is allowed.  The
    .done alternative is the exit to the next owner mode. -/
def CommitActive {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (d : Fin 8) (x : Raw s n) (f : Flight) : Prop :=
  ShortCommitFlight.Active C d x f ∧ ShortCommitFlight.OneCentre C f

def status : Flight → Status
  | .front _ p => p
  | .back _ p => p
  | .done p => p

def centreEdge {n : Nat} {h : Fin n → Bool} (C : Chart h) : Fin n :=
  nextAt C.root (C.a-1)

def publicationCentre {s n : Nat} {x0 : Raw s n}
    (X0 : H2Ready x0) (C : Chart (header x0)) (N : 9<n) :
    ShortGuardedNOR.Sites (header x0) :=
  ⟨rightNeighbor (centreEdge C),
    (ShortPublishChart.commit_centre_pair x0 x0 X0 C N
      (fun _=>rfl)).2.2.2.2.2⟩

def IsFreshCentreCrossing {n : Nat} {h : Fin n → Bool}
    (C : Chart h) (e : Fin n) (f : Flight) : Prop :=
  f=.front (C.a-1) .pending ∧ e=centreEdge C

def CommitGuardOld {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (d : Fin 8) (x : Raw s n) : Prop :=
  commitAccept (x (rightNeighbor (centreEdge C))).mis1
    (writeFwd 6 d false)=true

/-- The event is read at the old pair and the result at this single
    mark's actual new bytes; no later ACK stands in for this event. -/
def CentreOutcome {s n : Nat} {x0 : Raw s n}
    (X0 : H2Ready x0) (C : Chart (header x0)) (N : 9<n)
    (d : Fin 8) (x : Raw s n) (p : Status) : Prop :=
  let e := centreEdge C
  let v := rightNeighbor e
  let y := rawNext s x e
  (kField 0).read (y e).mis1=encode T ∧
    ((p=.applied ∧ CommitGuardOld C d x ∧
        ShortGuardedNOR.classifyFixed (header x0) x e =
          some (publicationCentre X0 C N) ∧
        (kField 1).read (y v).mis1=encode (writeFwd 6 d true) ∧
        (y v).mis1.getLsbD 92=(d.val/2%2==1)) ∨
     (p=.failed ∧ ¬ CommitGuardOld C d x ∧
        ShortGuardedNOR.classifyFixed (header x0) x e ≠
          some (publicationCentre X0 C N) ∧
        (kField 1).read (y v).mis1=encode (faultToken 2) ∧
        (y v).mis1.getLsbD 92=(x v).mis1.getLsbD 92))

/-- Exact actual old source descriptor at the genuine launch. -/
theorem launch {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (x : Raw s n) (heads : ∀ q,header x q=h q)
    (I : ShortClearLaunch.ClearIssue C x 6) :
    ∃ d : Fin 8, descValid d.val=true ∧
      d.val=issuedDescriptor (x C.root).mis1 ∧
      CommitActive C d (rawNext s x (RearTrace.predecessor C.root))
        (.front 0 .pending) := by
  obtain ⟨d,D,E,A⟩ := ShortCommitFlight.launch C x heads I
  exact ⟨d,D,E,A,by simp [ShortCommitFlight.OneCentre]⟩

theorem generated_state {s n : Nat}
    (x0 : Raw s n) (C : Chart (header x0))
    (X0 : H2Ready x0) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : Flight)
    (G : ShortCommitFlight.Generated x0 C d w f) :
    CommitActive C d (rawRun x0 w) f :=
  ⟨(ShortCommitFlight.generated_receipt x0 C X0 N d D w f G).1,
   ShortCommitFlight.generated_oneCentre x0 C X0 N d w f G⟩

theorem generated_descriptor {s n : Nat} {x0 : Raw s n}
    {C : Chart (header x0)} {d : Fin 8} {w : List (Fin n)}
    {f : Flight} (G : ShortCommitFlight.Generated x0 C d w f) :
    d.val=issuedDescriptor (x0 C.root).mis1 := by
  induction G with
  | launch _ E => exact E
  | snoc _ _ _ ih => exact ih

/-- The actual fresh front at the old centre is on port zero. -/
private theorem fresh_wire {s n : Nat} {x0 : Raw s n}
    (X0 : H2Ready x0) (C : Chart (header x0)) (N : 9<n)
    (x : Raw s n) (heads : ∀ q,header x q=header x0 q)
    (d : Fin 8)
    (A : CommitActive C d x (.front (C.a-1) .pending)) :
    (kField 0).read (x (centreEdge C)).mis1 =
      encode (writeFwd 6 d false) := by
  have geo := ShortPublishChart.commit_centre_pair x0 x X0 C N heads
  have W := A.1.2.2.2.1
  -- CHECK: definitional route/root/port reduction, ShortResetForwardH2.lean:26-27,
  -- ShortResetCycle.lean:57-69 and ShortCommitFlight.lean:35-36.
  change (kField (C.route.port (C.a-1))).read
    (x (centreEdge C)).mis1=encode (writeFwd 6 d false) at W
  rw [geo.2.2.1] at W
  exact W

/-- Forward mode at a fresh centre has one enabled ordinary old-pair
    crossing.  It either applies once or raises a canonical fault. -/
theorem fresh_centre_outcome {s n : Nat} {x0 : Raw s n}
    (X0 : H2Ready x0) (C : Chart (header x0)) (N : 9<n)
    (x : Raw s n) (heads : ∀ q,header x q=header x0 q)
    (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : Flight) (A : CommitActive C d x f)
    (F : IsFreshCentreCrossing C e f) :
    CentreOutcome X0 C N d x
      (status (ShortCommitFlight.next C d x e f)) := by
  obtain ⟨hf,he⟩ := F
  subst f
  subst e
  have room := (ShortPublishChart.commit_centre x0 x X0 C N heads).1
  have head := (ShortPublishChart.commit_centre_pair x0 x X0 C N
    heads).2.2.2.2.2
  have sep := edge_sep (by omega : 1<n) (centreEdge C)
  have W := fresh_wire X0 C N x heads d A
  have CF := ShortCommitGenerationEvent.classify_center x (centreEdge C)
    (publicationCentre X0 C N) rfl sep head d D false W
  by_cases G : CommitGuardOld C d x
  · have good := ShortCommitFlightRaw.canonical_centre_publication_raw
      x (centreEdge C) sep head d D W G
    have adv : ShortCommitChartHop.advance d C x (C.a-1) .pending =
        .applied := by
      unfold ShortCommitChartHop.advance
      rw [if_pos rfl,if_pos ⟨rfl,G⟩]
    have nextEq : ShortCommitFlight.next C d x (centreEdge C)
        (.front (C.a-1) .pending) =
          .front (C.a-1+1) .applied := by
      simp only [ShortCommitFlight.next,centreEdge,if_true,
        if_pos room,adv]
    rw [nextEq]
    exact ⟨good.1,.inl ⟨rfl,G,CF.mpr G,good.2.1,good.2.2.2⟩⟩
  · have badGuard : commitAccept
        (x (rightNeighbor (centreEdge C))).mis1
        (writeFwd 6 d false)=false :=
      Bool.eq_false_iff.mpr G
    have bad := ShortCommitFlightRaw.canonical_centre_rejected_raw
      x (centreEdge C) sep head d false D W badGuard
    have adv : ShortCommitChartHop.advance d C x (C.a-1) .pending =
        .failed := by
      unfold ShortCommitChartHop.advance
      rw [if_pos rfl,if_neg (fun H=>G H.2)]
    have nextEq : ShortCommitFlight.next C d x (centreEdge C)
        (.front (C.a-1) .pending) =
          .front (C.a-1+1) .failed := by
      simp only [ShortCommitFlight.next,centreEdge,if_true,
        if_pos room,adv]
    rw [nextEq]
    exact ⟨bad.1,.inr ⟨rfl,G,fun H=>G (CF.mp H),bad.2.1,bad.2.2.2⟩⟩

/-- E1 component C, all actual raw marks while the generation is live.
    The generic flight step already proves every joined pair frame.
    No restriction on any other owner or any non-nominated mark. -/
theorem commit_active_step {s n : Nat} {x0 : Raw s n}
    (X0 : H2Ready x0) (C : Chart (header x0)) (N : 9<n)
    (x : Raw s n) (heads : ∀ q,header x q=header x0 q)
    (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : Flight) (L : ShortCommitFlight.live f)
    (A : CommitActive C d x f) :
    CommitActive C d (rawNext s x e)
      (ShortCommitFlight.next C d x e f) ∧
    (IsFreshCentreCrossing C e f →
      CentreOutcome X0 C N d x
        (status (ShortCommitFlight.next C d x e f))) := by
  have F := ShortCommitFlight.step x0 x X0 C N heads d D e f L A.1
  have room := (ShortPublishChart.commit_centre x0 x X0 C N heads).1
  refine ⟨⟨F.1,ShortCommitFlight.oneCentre_step C room x d e f A.2⟩,?_⟩
  exact fresh_centre_outcome X0 C N x heads d D e f A

/-- No new outcome can be manufactured by a relay, terminal, reverse,
    or source mark.  This is status, not raw-state stuttering. -/
theorem status_stutters_off_centre {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (x : Raw s n) (d : Fin 8) (e : Fin n)
    (f : Flight) (A : ShortCommitFlight.OneCentre C f)
    (F : ¬IsFreshCentreCrossing C e f) :
    status (ShortCommitFlight.next C d x e f)=status f := by
  cases f with
  | done p => rfl
  | back i p =>
    cases R : nextStage C e (.rev i) <;>
      simp only [ShortCommitFlight.next,R,status]
  | front i p =>
    by_cases M : e=nextAt C.root i
    · by_cases J : i+1<C.L
      · by_cases K : i=C.a-1
        · subst i
          have pp : p=.pending := A.mpr (Nat.le_refl _)
          subst p
          exact False.elim (F ⟨rfl,M⟩)
        · simp only [ShortCommitFlight.next,if_pos M,if_pos J,status,
            ShortCommitChartHop.advance,if_neg K]
      · simp only [ShortCommitFlight.next,if_pos M,if_neg J,status]
    · simp only [ShortCommitFlight.next,if_neg M,status]

theorem decided_status_stays {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (x : Raw s n) (d : Fin 8) (e : Fin n)
    (f : Flight) (A : ShortCommitFlight.OneCentre C f)
    (H : status f≠.pending) :
    status (ShortCommitFlight.next C d x e f)=status f := by
  apply status_stutters_off_centre C x d e f A
  intro F
  apply H
  rw [F.1]
  rfl

/-- A tag-2 supplier in the owner's ingress cell can only be that
    owner's unique current, still-pending front.  In the other cases
    the *encoded* wire decodes to E, T, or a canonical D. -/
private theorem centre_front_of_tag {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (x : Raw s n) (d : Fin 8)
    (f : Flight) (K : C.a-1<C.L)
    (A : CommitActive C d x f)
    (tag : (slot C.route x (C.a-1)).tag=2) :
    f=.front (C.a-1) .pending := by
  cases f with
  | done p =>
    rw [ShortCommitFlight.no_orphan_of_clear C x A.1.1 _ K] at tag
    simp [MISByteCodec.E] at tag
  | back i p =>
    -- CHECK: Returning := k<L ∧ Wait ∧ Rev; Rev is definitionally
    -- bits/route, ShortCanonicalReverseChart.lean:25-27,323-325.
    have W : bits C.route x (C.a-1) =
        encode (ShortCanonicalReverseChart.trailAt
          (ShortCommitChartHop.reply p) i (C.a-1)) :=
      A.1.2.2 _ K
    by_cases H : C.a-1<i
    · simp only [ShortCanonicalReverseChart.trailAt,if_pos H] at W
      rw [slot_of_bits C.route x _ T trail_decode W] at tag
      simp [MISByteCodec.T] at tag
    · by_cases J : C.a-1=i
      · simp only [ShortCanonicalReverseChart.trailAt,if_neg H,if_pos J] at W
        let r := ShortCommitChartHop.reply p
        rw [slot_of_bits C.route x _ r.token r.decode_encode W,
          r.tag] at tag
        omega
      · simp only [ShortCanonicalReverseChart.trailAt,if_neg H,if_neg J] at W
        rw [slot_of_bits C.route x _ E empty_decode W] at tag
        simp [MISByteCodec.E] at tag
  | front i p =>
    rcases Nat.lt_trichotomy (C.a-1) i with H|H|H
    · have W := A.1.2.2.1 _ H
      rw [slot_of_bits C.route x _ T trail_decode W] at tag
      simp [MISByteCodec.T] at tag
    · subst i
      have pp : p=.pending := A.2.mpr (Nat.le_refl _)
      rw [pp]
    · have W := A.1.2.2.2.2 _ H K
      rw [slot_of_bits C.route x _ E empty_decode W] at tag
      simp [MISByteCodec.E] at tag

/-- Exact converse on the target centre, not just "success implies
    some classifier event".  Other owners can publish on other centres.
    Every event at THIS centre is this current generation's crossing. -/
theorem classify_iff_fresh_centre {s n : Nat} {x0 : Raw s n}
    (X0 : H2Ready x0) (C : Chart (header x0)) (N : 9<n)
    (x : Raw s n) (heads : ∀ q,header x q=header x0 q)
    (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : Flight) (A : CommitActive C d x f) :
    ShortGuardedNOR.classifyFixed (header x0) x e =
        some (publicationCentre X0 C N) ↔
      IsFreshCentreCrossing C e f ∧ CommitGuardOld C d x := by
  have geo := ShortPublishChart.commit_centre_pair x0 x X0 C N heads
  have room := (ShortPublishChart.commit_centre x0 x X0 C N heads).1
  constructor
  · intro H
    have R := ShortPublicationClassifier.recorded_guard x e
      (publicationCentre X0 C N).val
      ((ShortGuardedNOR.fixed_some x e (publicationCentre X0 C N)).mp H)
    have rr : rightNeighbor e=rightNeighbor (centreEdge C) := R.1
    have he := congrArg RearTrace.predecessor rr
    simp only [RearTrace.predecessor_right] at he
    subst e
    have K := (selectorGuard_iff_commitAccept _ _ _).mp R.2.2
    have tag : (slot C.route x (C.a-1)).tag=2 := by
      -- CHECK: port projection as in ShortCommitChartForward.lean:67-70.
      change (oldK (header x (centreEdge C)) (x (centreEdge C)).mis1
        (C.route.port (C.a-1))).tag=2
      rw [geo.2.2.1]
      exact K.1
    have hf := centre_front_of_tag C x d f (by omega) A tag
    subst f
    have W := fresh_wire X0 C N x heads d A
    have CF := ShortCommitGenerationEvent.classify_center x (centreEdge C)
      (publicationCentre X0 C N) rfl (edge_sep (by omega) _) geo.2.2.2.2.2
      d D false W
    exact ⟨⟨rfl,rfl⟩,CF.mp H⟩
  · rintro ⟨⟨hf,he⟩,G⟩
    subst f
    subst e
    have W := fresh_wire X0 C N x heads d A
    exact (ShortCommitGenerationEvent.classify_center x (centreEdge C)
      (publicationCentre X0 C N) rfl (edge_sep (by omega) _) geo.2.2.2.2.2
      d D false W).mpr G

/-- Owned incidence release flags are absent even during the failed
    flight: a canonical fault F has fault=true, not a healthy F0. -/
theorem commit_fenced {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (x : Raw s n) (d : Fin 8)
    (D : descValid d.val=true) (f : Flight)
    (A : CommitActive C d x f) :
    ShortMIS1ReadLease.Fenced C x :=
  ShortMIS1ReadLease.commit_fenced C x d D f A.1

/-- Read the root from the actual canonical K0 field of the chart. -/
private theorem decode_root {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (x : Raw s n) (head : header x C.root=true)
    (t : Token) (W : bits C.route x 0=encode t)
    (D : ∀ g,decode g (encode t)=t) :
    oldK true (x C.root).mis1 0=t := by
  have Q := slot_of_bits C.route x 0 t D W
  -- CHECK: same reduction as ShortWriteFileSplice.lean:35-40.
  change oldK (header x C.root) (x C.root).mis1
    (lane C.a C.b 0)=t at Q
  rwa [head,C.rootPort] at Q

/-- An actual live→live mark cannot consume the D at K0. At an
    incoming root mark in this domain the old K0 is F or T. -/
theorem live_file_step {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (x : Raw s n) (N : 1<n)
    (head : header x C.root=true)
    (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (f : Flight) (L : ShortCommitFlight.live f)
    (A : CommitActive C d x f)
    (L' : ShortCommitFlight.live (ShortCommitFlight.next C d x e f)) :
    fileField.read (rawNext s x e C.root).mis1 =
      fileField.read (x C.root).mis1 := by
  apply ShortWriteFileSplice.raw_file_step x C.root e N head
  intro door
  cases f with
  | done _ => exact False.elim L
  | front i p =>
    obtain ⟨_,W,Tp,P,_⟩ := A.1
    refine .inr ⟨W.1,?_,.inl ?_⟩
    · change get (x C.root).mis1 78 3 (by decide)<7
      rw [W.2]
      decide
    · cases i with
      | zero =>
        right
        rw [decode_root C x head _ P
          (ShortCommitChartHop.packet_decode d D p)]
        exact ShortCommitChartHop.packet_tag d p
      | succ i =>
        left
        rw [decode_root C x head T (Tp 0 (by omega)) trail_decode]
        rfl
  | back i p =>
    obtain ⟨_,W,Q⟩ := A.1
    cases i with
    | zero =>
      -- This is the actual consume mark, which the live→live
      -- assumption excludes; see ShortResetCycle.lean:150.
      have Z : ShortCommitFlight.next C d x e (.back 0 p)=.done p := by
        simp only [ShortCommitFlight.next,nextStage,if_pos door]
      rw [Z] at L'
      exact False.elim L'
    | succ i =>
      refine .inr ⟨W.1,?_,.inl (.inl ?_)⟩
      · change get (x C.root).mis1 78 3 (by decide)<7
        rw [W.2]
        decide
      · have V : bits C.route x 0=encode T := by
          have K : bits C.route x 0 =
              encode (ShortCanonicalReverseChart.trailAt
                (ShortCommitChartHop.reply p) (i+1) 0) := Q 0 C.positive
          simpa [ShortCanonicalReverseChart.trailAt] using K
        rw [decode_root C x head T V trail_decode]
        rfl

/-- The same six-bit READ file is retained from the actual ISSUE6
    launch until (but not including) the final consume. -/
theorem generated_live_file {s n : Nat} (x0 : Raw s n)
    (C : Chart (header x0)) (X0 : H2Ready x0) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : Flight)
    (G : ShortCommitFlight.Generated x0 C d w f) :
    ShortCommitFlight.live f →
      fileField.read (rawRun x0 w C.root).mis1 =
        fileField.read (x0 C.root).mis1 := by
  induction G with
  | launch I _ =>
    intro _
    change fileField.read
      (rawNext s x0 (RearTrace.predecessor C.root) C.root).mis1=_
    apply ShortWriteFileSplice.raw_file_step x0 _ _ (by omega) C.rootHeader
    intro _
    refine .inl ⟨I.2.2.1,?_,?_⟩
    · change 0<get (x0 C.root).mis1 78 3 (by decide)
      rw [I.2.2.2]
      decide
    · change get (x0 C.root).mis1 78 3 (by decide)<7
      rw [I.2.2.2]
      decide
  | @snoc w f e G L ih =>
    intro L'
    let x := rawRun x0 w
    have A := generated_state x0 C X0 N d D w f G
    have hd := ((header_run (by omega) x0 X0.1 w).2 C.root).trans
      C.rootHeader
    have app : rawRun x0 (w++[e])=rawNext s x e :=
      BStarResetSchedule.run_append _ _ _ _
    rw [app]
    exact (live_file_step C x (by omega) hd d D e f L A L').trans (ih L)

theorem generated_live_descriptor {s n : Nat} (x0 : Raw s n)
    (C : Chart (header x0)) (X0 : H2Ready x0) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : Flight)
    (G : ShortCommitFlight.Generated x0 C d w f)
    (L : ShortCommitFlight.live f) :
    issuedDescriptor (rawRun x0 w C.root).mis1=d.val := by
  exact (ShortWriteFileSplice.descriptor_of_same_file _ _
    (generated_live_file x0 C X0 N d D w f G L)).trans
      (generated_descriptor G).symm

/-- Actual prefix at the genuine first centre crossing; the prefix
    itself is generated by the actual ISSUE6 of THIS owner.  A
    planted D6 or a later selector snapshot cannot prove this. -/
def HistoricalOutcome {s n : Nat} (x0 : Raw s n)
    (C : Chart (header x0)) (X0 : H2Ready x0) (N : 9<n)
    (d : Fin 8) (w : List (Fin n)) (p : Status) : Prop :=
  ∃ lead tail : List (Fin n),
    w=lead++centreEdge C::tail ∧
    ShortCommitFlight.Generated x0 C d lead (.front (C.a-1) .pending) ∧
    CentreOutcome X0 C N d (rawRun x0 lead) p

/-- Recover the actual accepted OR rejected centre old pair on the
    same tape.  All later relay/return marks preserve the outcome. -/
theorem generated_outcome {s n : Nat} (x0 : Raw s n)
    (C : Chart (header x0)) (X0 : H2Ready x0) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : Flight)
    (G : ShortCommitFlight.Generated x0 C d w f) :
    status f≠.pending → HistoricalOutcome x0 C X0 N d w (status f) := by
  induction G with
  | launch _ _ =>
    intro H
    exact False.elim (H rfl)
  | @snoc w f e G L ih =>
    intro H
    let x := rawRun x0 w
    have A := generated_state x0 C X0 N d D w f G
    have heads : ∀ q,header x q=header x0 q :=
      (header_run (by omega) x0 X0.1 w).2
    by_cases F : IsFreshCentreCrossing C e f
    · have O := fresh_centre_outcome X0 C N x heads d D e f A F
      obtain ⟨hf,he⟩ := F
      refine ⟨w,[],?_,?_,O⟩
      · rw [he]
      · rw [←hf]
        exact G
    · have st := status_stutters_off_centre C x d e f A.2 F
      have H0 : status f≠.pending := by
        rw [←st]
        exact H
      obtain ⟨lead,tail,W,B,O⟩ := ih H0
      refine ⟨lead,tail++[e],?_,B,?_⟩
      · rw [W,List.append_assoc]
        rfl
      · -- CHECK: snoc endpoint unfolds to next C d (rawRun x0 w) e f,
        -- ShortCommitFlight.lean:179-181.
        change CentreOutcome X0 C N d (rawRun x0 lead)
          (status (ShortCommitFlight.next C d x e f))
        rw [st]
        exact O

/-- A stopped .done has the genuine combined PC 8; extract the
    actual phase=1, opcode=0 fields rather than confuse it with WAIT0. -/
theorem clear_issue_of_done {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (d : Fin 8) (x : Raw s n) (p : Status)
    (A : CommitActive C d x (.done p)) :
    ShortClearLaunch.ClearIssue C x 0 := by
  have W := ShortPhaseRank.pc_fields (x C.root).mis1
  have P : pc (x C.root).mis1=8 := A.1.2
  rw [P] at W
  have B : get (x C.root).mis1 78 3 (by decide)<8 :=
    (MISByteCodec.lane 78 3 (by decide) |>.read (x C.root).mis1).isLt
  exact ⟨by decide,A.1.1,by omega,by omega⟩

/-- Stronger than absence of a healthy F6/D6: every decoded
    owned lane is E.  Does not quantify over foreign owners. -/
def NoOrphanHealthyCOMMIT {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (x : Raw s n) : Prop :=
  ∀ i, i<C.L → slot C.route x i=E

/-- Actual first consume at the root; the return snapshot is the
    physical canonical T/D/E word with the current owner's WAIT6.
    This is the corrected C exit, not Wait0. -/
theorem commit_return0_no_orphan {s n : Nat} {x0 : Raw s n}
    (X0 : H2Ready x0) (C : Chart (header x0)) (N : 9<n)
    (x : Raw s n) (heads : ∀ q,header x q=header x0 q)
    (d : Fin 8) (D : descValid d.val=true)
    (e : Fin n) (p : Status) (door : rightNeighbor e=C.root)
    (A : CommitActive C d x (.back 0 p)) :
    let y := rawNext s x e
    ShortClearLaunch.ClearIssue C y 0 ∧
      NoOrphanHealthyCOMMIT C y ∧ (p=.applied ∨ p=.failed) := by
  have B := (commit_active_step X0 C N x heads d D e (.back 0 p)
    (by trivial) A).1
  have Z : ShortCommitFlight.next C d x e (.back 0 p)=.done p := by
    simp only [ShortCommitFlight.next,nextStage,if_pos door]
  rw [Z] at B
  have I := clear_issue_of_done C d _ p B
  have hp : p≠.pending := A.2
  refine ⟨I,ShortCommitFlight.no_orphan_of_clear C _ I.2.1,?_⟩
  cases p with
  | pending => exact False.elim (hp rfl)
  | applied => exact .inl rfl
  | failed => exact .inr rfl

/-- The E3 export, from the ACTUAL fresh launch to its FIRST consume.
    A Generated word stops at .done; there is no obligation to keep
    the old ISSUE0 snapshot unchanged through the next RESET launch.

    The applied branch has a same-mark publication receipt; the
    failed branch has an actual rejected historical centre pair in
    HistoricalOutcome. The literal six-bit file at issue determines d.
    Both exits drain all owner K wires and leave ISSUE0. -/
theorem mis1_commit6_flight_no_orphan {s n : Nat} (x0 : Raw s n)
    (C : Chart (header x0)) (X0 : H2Ready x0) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (p : Status)
    (G : ShortCommitFlight.Generated x0 C d w (.done p)) :
    let y := rawRun x0 w
    ShortClearLaunch.ClearIssue C y 0 ∧
      NoOrphanHealthyCOMMIT C y ∧
      d.val=issuedDescriptor (x0 C.root).mis1 ∧
      HistoricalOutcome x0 C X0 N d w p ∧
      ((p=.applied ∧
          ShortCommitFlight.SampledPublication d x0 (centreEdge C) w) ∨
        p=.failed) := by
  have A := generated_state x0 C X0 N d D w (.done p) G
  have I := clear_issue_of_done C d _ p A
  have hp : p≠.pending := A.2
  have O := generated_outcome x0 C X0 N d D w (.done p) G hp
  have R := (ShortCommitFlight.consume_clears x0 C X0 N d D w p G).2.2
  refine ⟨I,ShortCommitFlight.no_orphan_of_clear C _ I.2.1,
    generated_descriptor G,O,?_⟩
  cases p with
  | pending => exact False.elim (hp rfl)
  | applied => exact .inl ⟨rfl,R rfl⟩
  | failed => exact .inr rfl

end L4.ShortCommitMachine


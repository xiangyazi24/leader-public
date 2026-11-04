import Leader.Wu.ShortGap.StrictRoundService
import Leader.Wu.ShortGap.CandidatePersistenceRing
import Leader.Wu.ShortGap.CaptureLifecycle

/-!
# Clean selection-to-capture entry

The selection invariant supplies an empty selected gap and immutable candidate
ports. The literal selection Agent has no capture actor, lease, or inbox.
These finite fields are therefore an explicit extension, with a clean-actor
premise. FREE/home below concerns the capture actor; it does not assert that
the shared root's opposite selection port or its next gap is idle.

The launch is a new local pair row on a tagged union. No imported selection
row is changed. The length-one case is a direct root/root proposal delivery.
This module covers entry and the proposal phase, not deletion or merged-gap
repair, and does not acquire a grant from an arbitrary forged configuration.
-/

namespace ShortGapCaptureEntry
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapLineage ShortGapLineageRetained ShortGapTwoEpoch
open ShortGapLineage2Closure ShortGapLineage2ClosureB ShortGapTwoEpochLaws
open ShortGapGhostComposition2 FiniteUniformStoppingTree
set_option autoImplicit false

/-- A held owner candidate rules out idle and live current epochs; the
current epoch is delivered, regardless of its retained previous epoch. -/
theorem owner_candidate_delivered (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m)
    (hc : (s.cfg (rootV R g)).cwPort = some .heldCandidate) :
    ∃ q c d, (s.epoch g).cur = .delivered q c d := by
  cases he : (s.epoch g).cur with
  | idle =>
    have h := hs.idleSend g he
    rw [hc] at h
    cases h
  | outbound q c =>
    have h := (hs.waiting g).mpr (by simp [he,Live])
    rw [hc] at h
    cases h
  | returning q c d =>
    have h := (hs.waiting g).mpr (by simp [he,Live])
    rw [hc] at h
    cases h
  | delivered q c d => exact ⟨q,c,d,rfl⟩

/-- The selected reply is consumed: every interior slot is empty. -/
theorem bothCandidate_empty (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m) (hc : BothCandidate R s g) :
    EmptyGap R (curView R s) g := by
  obtain ⟨q,c,d,he⟩ := owner_candidate_delivered R s hs g hc.1
  simpa only [he] using current_token_shape R s hs g

/-- The owner port alone identifies a historical out1/in0 lock under
Lineage2; a port pattern in a forged state would not suffice. -/
theorem owner_candidate_lock (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m)
    (hc : (s.cfg (rootV R g)).cwPort = some .heldCandidate) :
    Locked10 R s (s.k g) g := by
  have hd := (hs.coherent.outgoing g).mp (by
    change CwHeld (s.cfg (rootV R g)).cwPort
    rw [hc]
    trivial)
  obtain ⟨c,d,hl,hr,hport⟩ := hs.coherent.outgoingValue g hd
  change s.hist g (s.k g) = some c at hl
  change s.hist (next R g) (s.k g) = some d at hr
  change (s.cfg (rootV R g)).cwPort = some (resCw c d) at hport
  rw [hc] at hport
  have hv : c = .out1 ∧ d = .in0 := by
    cases c <;> cases d <;> simp_all [resCw,res,Verdict.cw]
  rcases hv with ⟨rfl,rfl⟩
  exact ⟨hs,hl,hr⟩

theorem bothCandidate_of_owner_candidate (R : RFrame) (s : GhostRing2 R)
    (hs : Lineage2 R s) (g : Fin R.m)
    (hc : (s.cfg (rootV R g)).cwPort = some .heldCandidate) : BothCandidate R s g := by
  apply (owner_candidate_lock R s hs g hc).delivered_latches
  apply (hs.coherent.outgoing g).mp
  change CwHeld (s.cfg (rootV R g)).cwPort
  rw [hc]
  trivial

/-- Identify the imported persistence kernel with the actual ghost erasure. -/
theorem ghost_cfg_eq_persistence (R : RFrame) (s : GhostRing2 R) (e : Vtx R) :
    (ghostStep2 R s e).cfg = ShortGapLiteralRingRows.ringStepU R s.cfg e := by
  funext v
  change ShortGapOwnerRoundSlice.ringStepU R s.cfg e v = _
  by_cases hv : v = e <;> by_cases hr : v = rn R e <;>
    simp [ShortGapOwnerRoundSlice.ringStepU,ShortGapLiteralRingRows.ringStepU,
      incident,rawAt,joinTick,hv,hr,rn_ne_self]

/-- Every literal selection interaction, including both endpoint JOINs,
preserves the two candidate ports. Opposite ports are allowed to change. -/
theorem bothCandidate_stable (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hc : BothCandidate R s g) (e : Vtx R) :
    BothCandidate R (ghostStep2 R s e) g := by
  have hl := owner_candidate_lock R s hs g hc.1
  obtain ⟨cw,ccw,ha⟩ := hl.root_choices.1
  have hp := hc.1
  rw [ha] at hp
  have he : cw = .heldCandidate := Option.some.inj hp
  subst cw
  obtain ⟨dw,dd,hb⟩ := hl.root_choices.2
  have hp := hc.2
  rw [hb] at hp
  have he : dd = .heldCandidate := Option.some.inj hp
  subst dd
  obtain ⟨ccw',ha'⟩ := ringStepU_preserves_heldCandidate_cw R s.cfg _ .out1 ccw
    (by intro h; cases h) ha e
  obtain ⟨dw',hb'⟩ := ringStepU_preserves_heldCandidate_ccw R s.cfg _ .in0 dw
    (by intro h; cases h) hb e
  unfold BothCandidate
  rw [ghost_cfg_eq_persistence,ha',hb']
  exact ⟨rfl,rfl⟩

/-- Finite capture control. freeHome includes an empty capture inbox and
no capture lease; it makes no assertion about opposite selection traffic. -/
inductive Actor where
  | freeHome
  | sourceLeased
  | targetHeld
  deriving DecidableEq

/-- The exact extra runtime data absent from the imported selection state. -/
structure CaptureFrame (R : RFrame) where
  selection : GhostRing2 R
  actor : Fin R.m → Actor

/-- Before any capture, all capture actors are FREE/home. Selection never
changes these added fields. This is an explicit clean-lane hypothesis. -/
def CleanActors (R : RFrame) (s : CaptureFrame R) : Prop := ∀ i, s.actor i = .freeHome

/-- Canonical clean actor extension; it leaves all selection data unchanged. -/
def cleanFrame (R : RFrame) (s : GhostRing2 R) : CaptureFrame R := ⟨s,fun _ => .freeHome⟩

theorem cleanFrame_actors (R : RFrame) (s : GhostRing2 R) : CleanActors R (cleanFrame R s) :=
  fun _ => rfl

/-- Capture entry resources on the selected gap, with independent actor
availability and the actual empty literal interior. -/
structure CaptureReady (R : RFrame) (g : Fin R.m) (s : CaptureFrame R) : Prop where
  candidate : BothCandidate R s.selection g
  sourceFree : s.actor g = .freeHome
  targetFree : s.actor (next R g) = .freeHome
  empty : EmptyGap R (curView R s.selection) g

theorem captureReady_of_bothCandidate (R : RFrame) (s : CaptureFrame R)
    (hs : Lineage2 R s.selection) (ha : CleanActors R s)
    (g : Fin R.m) (hc : BothCandidate R s.selection g) : CaptureReady R g s :=
  ⟨hc,ha g,ha (next R g),bothCandidate_empty R s.selection hs g hc⟩

/-- Lift the existing selection transition by framing all capture actors. -/
def selectionStep (R : RFrame) (s : CaptureFrame R) (e : Vtx R) : CaptureFrame R :=
  ⟨ghostStep2 R s.selection e,s.actor⟩

theorem captureReady_stable (R : RFrame) (s : CaptureFrame R)
    (hs : Lineage2 R s.selection) (g : Fin R.m) (h : CaptureReady R g s) (e : Vtx R) :
    CaptureReady R g (selectionStep R s e) := by
  have hc := bothCandidate_stable R s.selection hs g h.candidate e
  exact ⟨hc,h.sourceFree,h.targetFree,bothCandidate_empty R _ (lineage2_step R _ hs e) g hc⟩

/-! ## A finite tagged pair-row extension -/

/-- Finite metadata only: direction and the out1/in0 pair are fixed by this
constructor. Authority comes from the clean connected candidate, not an ID. -/
inductive EntryGrant where
  | normal10
  deriving DecidableEq

inductive CaptureMessage where
  | proposal (grant : EntryGrant)
  deriving DecidableEq

/-- Selection and capture messages cannot inhabit the same slot. -/
inductive WireSlot where
  | selection (slot : Slot)
  | capture (message : CaptureMessage)
  deriving DecidableEq

/-- The imported Agent vocabulary, extended with finite actor and slot tags. -/
inductive TaggedAgent where
  | root (ch : Choice) (cw : CwPort) (ccw : CcwPort) (actor : Actor)
  | interior (slot : WireSlot)
  deriving DecidableEq

def embedAgent (a : Agent) (actor : Actor) : TaggedAgent :=
  match a with
  | .root c cw ccw => .root c cw ccw actor
  | .interior t => .interior (.selection t)

def taggedCfg (R : RFrame) (s : CaptureFrame R) (v : Vtx R) : TaggedAgent :=
  embedAgent (s.selection.cfg v) (s.actor v.1)

def TaggedAgent.cwPort : TaggedAgent → Option CwPort
  | .root _ cw _ _ => some cw
  | .interior _ => none

theorem taggedCfg_cw (R : RFrame) (s : CaptureFrame R) (v : Vtx R) :
    (taggedCfg R s v).cwPort = (s.selection.cfg v).cwPort := by
  cases h : s.selection.cfg v <;> simp [taggedCfg,h,embedAgent,TaggedAgent.cwPort,Agent.cwPort]

/-- New local pair row. Positive interiors receive the proposal while the
source acquires its lease atomically. With h=1 the same pair interaction
delivers directly and holds the target actor. -/
def captureLaunch : TaggedAgent → TaggedAgent → Option (TaggedAgent × TaggedAgent)
  | .root .out1 .heldCandidate ccw .freeHome, .interior (.selection .empty) =>
      some (.root .out1 .heldCandidate ccw .sourceLeased,
        .interior (.capture (.proposal .normal10)))
  | .root .out1 .heldCandidate ccw .freeHome, .root .in0 cw .heldCandidate .freeHome =>
      some (.root .out1 .heldCandidate ccw .sourceLeased,
        .root .in0 cw .heldCandidate .targetHeld)
  | _, _ => none

theorem captureLaunch_owner (a b x y : TaggedAgent) (h : captureLaunch a b = some (x,y)) :
    ∃ ccw, a = .root .out1 .heldCandidate ccw .freeHome := by
  unfold captureLaunch at h
  split at h
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · cases h

/-- Local firing has a derived global entry certificate on the clean lane;
CaptureReady itself is not included as an executable launch guard. -/
theorem captureLaunch_only_ready (R : RFrame) (s : CaptureFrame R)
    (hs : Lineage2 R s.selection) (ha : CleanActors R s) (g : Fin R.m)
    (x y : TaggedAgent)
    (h : captureLaunch (taggedCfg R s (rootV R g))
      (taggedCfg R s (rn R (rootV R g))) = some (x,y)) : CaptureReady R g s := by
  obtain ⟨ccw,hleft⟩ := captureLaunch_owner _ _ x y h
  have hc : (s.selection.cfg (rootV R g)).cwPort = some .heldCandidate := by
    rw [← taggedCfg_cw,hleft]
    rfl
  exact captureReady_of_bothCandidate R s hs ha g (bothCandidate_of_owner_candidate R _ hs g hc)

/-- Every ready gap has an enabled local launch, including adjacent roots. -/
theorem captureLaunch_enabled (R : RFrame) (s : CaptureFrame R)
    (hs : Lineage2 R s.selection) (g : Fin R.m) (h : CaptureReady R g s) :
    ∃ x y, captureLaunch (taggedCfg R s (rootV R g))
      (taggedCfg R s (rn R (rootV R g))) = some (x,y) := by
  have hl := owner_candidate_lock R s.selection hs g h.candidate.1
  obtain ⟨cw,ccw,hr⟩ := hl.root_choices.1
  have hp := h.candidate.1
  rw [hr] at hp
  have hc : cw = .heldCandidate := Option.some.inj hp
  subst cw
  have hleft : taggedCfg R s (rootV R g) = .root .out1 .heldCandidate ccw .freeHome := by
    simp [taggedCfg,hr,embedAgent,rootV,h.sourceFree]
  rw [hleft]
  by_cases hh : 1 < R.h
  · have hn : rn R (rootV R g) = (g,⟨1,hh⟩) := rn_of_lt R _ hh
    have he := h.empty ⟨1,hh⟩ (by change 0 < 1; decide)
    change s.selection.cfg (g,⟨1,hh⟩) = .interior .empty at he
    rw [hn]
    simp [taggedCfg,he,embedAgent,captureLaunch]
  · have h1 : R.h = 1 := by have := R.hh; omega
    have hn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬ 0+1 < R.h; omega)
    obtain ⟨dw,dd,ht⟩ := hl.root_choices.2
    have hp := h.candidate.2
    rw [ht] at hp
    have hc : dd = .heldCandidate := Option.some.inj hp
    subst dd
    rw [hn]
    simp [taggedCfg,ht,embedAgent,rootV,h.targetFree,captureLaunch]

theorem captureLaunch_leases_source (a b x y : TaggedAgent) (h : captureLaunch a b = some (x,y)) :
    ∃ ccw, x = .root .out1 .heldCandidate ccw .sourceLeased := by
  unfold captureLaunch at h
  split at h
  · cases h; exact ⟨_,rfl⟩
  · cases h; exact ⟨_,rfl⟩
  · cases h

/-- The local capability is consumed: a leased source cannot launch twice. -/
theorem captureLaunch_no_relaunch (a b x y : TaggedAgent) (h : captureLaunch a b = some (x,y))
    (z : TaggedAgent) : captureLaunch x z = none := by
  obtain ⟨ccw,rfl⟩ := captureLaunch_leases_source a b x y h
  rfl

/-- Only unleased selection-tagged states are offered to the old table.
Capture messages are never erased to empty selection slots for dispatch. -/
def selectionInput : TaggedAgent → Option Agent
  | .root c cw ccw .freeHome => some (.root c cw ccw)
  | .interior (.selection t) => some (.interior t)
  | _ => none

/-- The tagged selection dispatcher applies the unchanged pair table and
JOIN when both inputs belong to selection; otherwise it frames the pair. -/
def selectionRow (a b : TaggedAgent) : TaggedAgent × TaggedAgent :=
  match selectionInput a, selectionInput b with
  | some x, some y =>
      let p := row x y
      (embedAgent (ShortGapLiteralRingRows.joinA p.1) .freeHome,
        embedAgent (ShortGapLiteralRingRows.joinA p.2) .freeHome)
  | _, _ => (a,b)

/-- On the clean actor lane the extension is exactly the imported selection
row followed by its original JOIN, with no additional guard or rewrite. -/
theorem selectionRow_embedding (a b : Agent) :
    selectionRow (embedAgent a .freeHome) (embedAgent b .freeHome) =
      (embedAgent (ShortGapLiteralRingRows.joinA (row a b).1) .freeHome,
        embedAgent (ShortGapLiteralRingRows.joinA (row a b).2) .freeHome) := by
  cases a <;> cases b <;> rfl

theorem leased_source_selection_stutters (ccw : CcwPort) (b : TaggedAgent) :
    selectionRow (.root .out1 .heldCandidate ccw .sourceLeased) b =
      (.root .out1 .heldCandidate ccw .sourceLeased,b) := rfl

theorem capture_tag_selection_stutters (a b : TaggedAgent) (msg : CaptureMessage) :
    selectionRow (.interior (.capture msg)) b = (.interior (.capture msg),b) ∧
      selectionRow a (.interior (.capture msg)) = (a,.interior (.capture msg)) := by
  constructor
  · rfl
  · unfold selectionRow
    cases selectionInput a <;> rfl

/-- Slot shapes throughout the proposal phase: empty selection storage or
one capture-tagged proposal, never a selection declaration or reply. -/
def ProposalSlot (a : TaggedAgent) : Prop :=
  a = .interior (.selection .empty) ∨ ∃ grant, a = .interior (.capture (.proposal grant))

theorem proposal_slots_selection_stutter (a b : TaggedAgent) (ha : ProposalSlot a) (hb : ProposalSlot b) :
    selectionRow a b = (a,b) := by
  rcases ha with rfl | ⟨grant,rfl⟩
  · rcases hb with rfl | ⟨grant,rfl⟩ <;> rfl
  · rfl

theorem proposal_target_selection_stutter (a : TaggedAgent) (ha : ProposalSlot a)
    (cw : CwPort) (actor : Actor) :
    selectionRow a (.root .in0 cw .heldCandidate actor) = (a,.root .in0 cw .heldCandidate actor) := by
  rcases ha with rfl | ⟨grant,rfl⟩
  · cases actor <;> cases cw <;> rfl
  · rfl

/-- Clean ownership shape needed by the literal selection exclusion proof.
Opposite endpoint ports remain arbitrary. -/
structure CaptureOwned (R : RFrame) (g : Fin R.m) (cfg : Vtx R → TaggedAgent) : Prop where
  source : ∃ ccw, cfg (rootV R g) = .root .out1 .heldCandidate ccw .sourceLeased
  target : ∃ cw actor, cfg (rootV R (next R g)) = .root .in0 cw .heldCandidate actor
  slots : ∀ p : Fin R.h, 0 < p.val → ProposalSlot (cfg (g,p))

/-- No selected-gap selection row changes state during this capture shape:
L1/L2 are excluded by the leased candidate owner, K1 by the candidate target,
and transport by the disjoint slot tag. This includes post-row JOIN. -/
theorem selection_disabled_during_capture (R : RFrame) (g : Fin R.m)
    (cfg : Vtx R → TaggedAgent) (h : CaptureOwned R g cfg) (p : Fin R.h) :
    selectionRow (cfg (g,p)) (cfg (rn R (g,p))) = (cfg (g,p),cfg (rn R (g,p))) := by
  by_cases hp : p.val = 0
  · have he : (g,p) = rootV R g := Prod.ext rfl (Fin.ext hp)
    rw [he]
    obtain ⟨ccw,hc⟩ := h.source
    rw [hc]
    exact leased_source_selection_stutters _ _
  · have ha := h.slots p (by omega)
    by_cases hn : p.val+1 < R.h
    · rw [rn_of_lt R _ hn]
      exact proposal_slots_selection_stutter _ _ ha (h.slots ⟨p.val+1,hn⟩ (by simp))
    · rw [rn_of_last R _ hn]
      obtain ⟨cw,actor,hc⟩ := h.target
      rw [hc]
      exact proposal_target_selection_stutter _ ha cw actor

/-- The radius-one write primitive used by the new pair rows. -/
def pairWrite (R : RFrame) (cfg : Vtx R → TaggedAgent) (e : Vtx R)
    (a b : TaggedAgent) (v : Vtx R) : TaggedAgent :=
  if v = e then a else if v = rn R e then b else cfg v

theorem pairWrite_left (R : RFrame) (cfg : Vtx R → TaggedAgent) (e : Vtx R) (a b : TaggedAgent) :
    pairWrite R cfg e a b e = a := by simp [pairWrite]

theorem pairWrite_right (R : RFrame) (cfg : Vtx R → TaggedAgent) (e : Vtx R) (a b : TaggedAgent) :
    pairWrite R cfg e a b (rn R e) = b := by simp [pairWrite,rn_ne_self]

theorem pairWrite_frame (R : RFrame) (cfg : Vtx R → TaggedAgent) (e v : Vtx R) (a b : TaggedAgent)
    (he : v ≠ e) (hr : v ≠ rn R e) : pairWrite R cfg e a b v = cfg v := by
  simp [pairWrite,he,hr]

/-- Launch updates exactly the owner edge; a disabled launch is a no-op. -/
def launchCfg (R : RFrame) (s : CaptureFrame R) (g : Fin R.m) : Vtx R → TaggedAgent :=
  match captureLaunch (taggedCfg R s (rootV R g)) (taggedCfg R s (rn R (rootV R g))) with
  | some (a,b) => pairWrite R (taggedCfg R s) (rootV R g) a b
  | none => taggedCfg R s

private theorem ready_tagged_shape (R : RFrame) (s : CaptureFrame R)
    (hs : Lineage2 R s.selection) (g : Fin R.m) (h : CaptureReady R g s) :
    ∃ ccw cw,
      taggedCfg R s (rootV R g) = .root .out1 .heldCandidate ccw .freeHome ∧
      taggedCfg R s (rootV R (next R g)) = .root .in0 cw .heldCandidate .freeHome ∧
      ∀ p : Fin R.h, 0 < p.val → taggedCfg R s (g,p) = .interior (.selection .empty) := by
  have hl := owner_candidate_lock R s.selection hs g h.candidate.1
  obtain ⟨cw,ccw,ha⟩ := hl.root_choices.1
  obtain ⟨dw,dd,hb⟩ := hl.root_choices.2
  have hp := h.candidate.1
  have hq := h.candidate.2
  rw [ha] at hp
  rw [hb] at hq
  have hp' : cw = .heldCandidate := Option.some.inj hp
  have hq' : dd = .heldCandidate := Option.some.inj hq
  subst cw; subst dd
  refine ⟨ccw,dw,?_,?_,?_⟩
  · simp [taggedCfg,ha,embedAgent,rootV,h.sourceFree]
  · simp [taggedCfg,hb,embedAgent,rootV,h.targetFree]
  · intro p hp
    have he := h.empty p hp
    change s.selection.cfg (g,p) = .interior .empty at he
    simp [taggedCfg,he,embedAgent]

/-- The actual local launch produces the complete clean capture shape.
For h=1 there is no fictitious interior slot or extra interaction. -/
theorem captureLaunch_owned (R : RFrame) (s : CaptureFrame R)
    (hs : Lineage2 R s.selection) (g : Fin R.m) (h : CaptureReady R g s) :
    CaptureOwned R g (launchCfg R s g) := by
  obtain ⟨ccw,cw,hl,hr,hi⟩ := ready_tagged_shape R s hs g h
  have hne : rootV R (next R g) ≠ rootV R g := by
    intro he
    exact next_ne_self R g (congrArg Prod.fst he)
  by_cases hh : 1 < R.h
  · have hn : rn R (rootV R g) = (g,⟨1,hh⟩) := rn_of_lt R _ hh
    have hfirst := hi ⟨1,hh⟩ (by change 0 < 1; decide)
    have hc : launchCfg R s g = pairWrite R (taggedCfg R s) (rootV R g)
        (.root .out1 .heldCandidate ccw .sourceLeased) (.interior (.capture (.proposal .normal10))) := by
      simp [launchCfg,hl,hn,hfirst,captureLaunch]
    rw [hc]
    refine ⟨⟨ccw,pairWrite_left R _ _ _ _⟩,⟨cw,.freeHome,?_⟩,?_⟩
    · rw [pairWrite_frame R _ _ _ _ _ hne (by
        rw [hn]
        intro he
        exact next_ne_self R g (congrArg Prod.fst he))]
      exact hr
    · intro p hp
      have hp0 : (g,p) ≠ rootV R g := by
        intro he
        have hv := congrArg (fun v : Vtx R => v.2.val) he
        change p.val = 0 at hv
        omega
      by_cases hp1 : (g,p) = rn R (rootV R g)
      · rw [hp1,pairWrite_right]
        exact Or.inr ⟨.normal10,rfl⟩
      · rw [pairWrite_frame R _ _ _ _ _ hp0 hp1,hi p hp]
        exact Or.inl rfl
  · have h1 : R.h = 1 := by have := R.hh; omega
    have hn : rn R (rootV R g) = rootV R (next R g) := rn_of_last R _ (by change ¬ 0+1 < R.h; omega)
    have hc : launchCfg R s g = pairWrite R (taggedCfg R s) (rootV R g)
        (.root .out1 .heldCandidate ccw .sourceLeased) (.root .in0 cw .heldCandidate .targetHeld) := by
      simp [launchCfg,hl,hn,hr,captureLaunch]
    rw [hc]
    refine ⟨⟨ccw,pairWrite_left R _ _ _ _⟩,⟨cw,.targetHeld,?_⟩,?_⟩
    · rw [← hn,pairWrite_right]
    · intro p hp
      have := p.isLt
      omega

/-- The exclusion theorem is supplied by an actual launch, not merely a
carried post-state ownership premise. -/
theorem selection_disabled_after_launch (R : RFrame) (s : CaptureFrame R)
    (hs : Lineage2 R s.selection) (g : Fin R.m) (h : CaptureReady R g s) (p : Fin R.h) :
    selectionRow (launchCfg R s g (g,p)) (launchCfg R s g (rn R (g,p))) =
      (launchCfg R s g (g,p),launchCfg R s g (rn R (g,p))) :=
  selection_disabled_during_capture R g _ (captureLaunch_owned R s hs g h) p

/-! ## The opposite owned mover is a separate obligation

This clean trace refutes the stronger interpretation of FREE/home that also
requires the target's own clockwise selection mover to be home. A reservation
that blocks that target-owned launch is additional protocol content, not a
consequence of the two candidate ports.
-/

def exampleFrame : RFrame := ⟨3,2,by decide,by decide,.out1,Or.inl rfl⟩
def exampleGap : Fin exampleFrame.m := ⟨0,by decide⟩
def exampleOwnerEdge : Vtx exampleFrame := (exampleGap,⟨0,by decide⟩)
def exampleCompareEdge : Vtx exampleFrame := (exampleGap,⟨1,by decide⟩)
def exampleOtherEdge : Vtx exampleFrame := (⟨1,by decide⟩,⟨0,by decide⟩)

/-- Launch, compare, and return on gap 0, from the checked all-Race base. -/
def latchedExample : GhostRing2 exampleFrame :=
  ghostStep2 exampleFrame
    (ghostStep2 exampleFrame (ghostStep2 exampleFrame (strictStart exampleFrame)
      exampleOwnerEdge) exampleCompareEdge) exampleOwnerEdge

def busyTargetExample : GhostRing2 exampleFrame :=
  ghostStep2 exampleFrame latchedExample exampleOtherEdge

theorem latchedExample_lineage : Lineage2 exampleFrame latchedExample :=
  lineage2_step _ _ (lineage2_step _ _ (lineage2_step _ _ (strictStart_lineage _) _) _) _

theorem latchedExample_candidate : BothCandidate exampleFrame latchedExample exampleGap :=
  ⟨rfl,rfl⟩

theorem latchedExample_target_idle :
    (latchedExample.epoch (next exampleFrame exampleGap)).cur = .idle := rfl

theorem busyTargetExample_lineage : Lineage2 exampleFrame busyTargetExample :=
  lineage2_step _ _ latchedExample_lineage _

theorem busyTargetExample_candidate : BothCandidate exampleFrame busyTargetExample exampleGap :=
  bothCandidate_stable _ _ latchedExample_lineage _ latchedExample_candidate _

/-- The adjacent selection launch is a real new declaration, not a forged
slot or a broken lineage invariant. -/
theorem busyTargetExample_obligation :
    (busyTargetExample.cfg (rootV exampleFrame (next exampleFrame exampleGap))).cwPort = some .waiting ∧
      (busyTargetExample.epoch (next exampleFrame exampleGap)).cur = .outbound 1 .in0 ∧
      busyTargetExample.cfg (⟨1,by decide⟩,⟨1,by decide⟩) = .interior (.decl .in0) :=
  ⟨rfl,rfl,rfl⟩

/-- This stronger requirement is the target-owned-mover clause of the full
grant design. It is deliberately distinguished from capture-actor freedom. -/
def OwnedMoverReady (R : RFrame) (g : Fin R.m) (s : CaptureFrame R) : Prop :=
  CaptureReady R g s ∧ ¬ Live (s.selection.epoch (next R g)).cur

theorem stronger_readiness_counterexample :
    Lineage2 exampleFrame busyTargetExample ∧
      BothCandidate exampleFrame busyTargetExample exampleGap ∧
      ¬ OwnedMoverReady exampleFrame exampleGap (cleanFrame exampleFrame busyTargetExample) := by
  refine ⟨busyTargetExample_lineage,busyTargetExample_candidate,?_⟩
  intro h
  apply h.2
  change Live (busyTargetExample.epoch (next exampleFrame exampleGap)).cur
  rw [busyTargetExample_obligation.2.1]
  trivial

/-- Even the stronger ready state loses that extra clause under a raw row
of the other gap. Full grant stability needs a target-side reservation. -/
theorem stronger_readiness_not_stable :
    exampleOtherEdge.1 ≠ exampleGap ∧
      OwnedMoverReady exampleFrame exampleGap (cleanFrame exampleFrame latchedExample) ∧
      ¬ OwnedMoverReady exampleFrame exampleGap
        (selectionStep exampleFrame (cleanFrame exampleFrame latchedExample) exampleOtherEdge) := by
  refine ⟨by decide,⟨captureReady_of_bothCandidate _ _ latchedExample_lineage
    (cleanFrame_actors _ _) _ latchedExample_candidate,?_⟩,?_⟩
  · change ¬ Live (latchedExample.epoch (next exampleFrame exampleGap)).cur
    rw [latchedExample_target_idle]
    exact id
  · exact stronger_readiness_counterexample.2.2

/-! ## Explicit proposal-walk handoff specification

The semantic constructors are `Step.launchProposal` and
`Step.proposalAtCleanTarget`; the imported file has no `Step.proposal`.
The following actual pair submachine and finite-uniform kernel specify the
remaining walk theorem. Its Bellman bound is not claimed in this file.
-/

/-- Tagged proposal forwarding and clean-target arrival. Capture input is
consumed exactly once; all other pairs stutter in this proposal submachine. -/
def proposalRow : TaggedAgent → TaggedAgent → TaggedAgent × TaggedAgent
  | .interior (.capture (.proposal grant)), .interior (.selection .empty) =>
      (.interior (.selection .empty),.interior (.capture (.proposal grant)))
  | .interior (.capture (.proposal _)), .root .in0 cw .heldCandidate .freeHome =>
      (.interior (.selection .empty),.root .in0 cw .heldCandidate .targetHeld)
  | a,b => (a,b)

/-- Launch is the first pair action of the same proposal walk, so the open
bound n*h includes the scheduler wait for launch. Other gaps are framed by
this selected-gap submachine; full-dispatcher nonmasking is not asserted. -/
def proposalTick (R : RFrame) (g : Fin R.m) (cfg : Vtx R → TaggedAgent) (e : Vtx R) :
    Vtx R → TaggedAgent :=
  if e.1 = g then
    let a := cfg e
    let b := cfg (rn R e)
    let p := (captureLaunch a b).getD (proposalRow a b)
    pairWrite R cfg e p.1 p.2
  else cfg

def targetAcquired (R : RFrame) (g : Fin R.m) (cfg : Vtx R → TaggedAgent) : Bool :=
  match cfg (rootV R (next R g)) with
  | .root .in0 _ .heldCandidate .targetHeld => true
  | _ => false

/-- Reachability restricts the proposed certificate to an actual clean seed;
it does not assume a progress, debt, or carrier-shape theorem. -/
inductive ProposalReachable (R : RFrame) (s : CaptureFrame R) (g : Fin R.m) :
    (Vtx R → TaggedAgent) → Prop where
  | start : ProposalReachable R s g (taggedCfg R s)
  | step {cfg} : ProposalReachable R s g cfg → (e : Vtx R) →
      ProposalReachable R s g (proposalTick R g cfg e)

abbrev ProposalActive (R : RFrame) (s : CaptureFrame R) (g : Fin R.m) :=
  {cfg : Vtx R → TaggedAgent // ProposalReachable R s g cfg ∧ targetAcquired R g cfg = false}

def proposalWalkStep (R : RFrame) (s : CaptureFrame R) (g : Fin R.m)
    (x : ProposalActive R s g) (e : Fin R.n) : StopNode (ProposalActive R s g) :=
  let cfg := proposalTick R g x.val (edgeVtx R e)
  if h : targetAcquired R g cfg = true then .success
  else .active ⟨cfg,.step x.property.1 _,by cases he : targetAcquired R g cfg <;> simp_all⟩

def proposalWalkStart (R : RFrame) (s : CaptureFrame R) (g : Fin R.m)
    (hs : Lineage2 R s.selection) (hr : CaptureReady R g s) : ProposalActive R s g :=
  ⟨taggedCfg R s,.start,by
    obtain ⟨ccw,cw,_,ht,_⟩ := ready_tagged_shape R s hs g hr
    simp [targetAcquired,ht]⟩

theorem proposalWalk_success_sound (R : RFrame) (s : CaptureFrame R) (g : Fin R.m)
    (x : ProposalActive R s g) (e : Fin R.n) (h : proposalWalkStep R s g x e = .success) :
    targetAcquired R g (proposalTick R g x.val (edgeVtx R e)) = true := by
  unfold proposalWalkStep at h
  dsimp only at h
  split at h
  · assumption
  · cases h

/-- The requested future theorem, stated as a proposition rather than an
unproved theorem declaration. Its certificate would imply the finite-horizon
cost bound from CaptureReady, including launch, with potential at most n*h. -/
def ProposalWalkHandoff (R : RFrame) (s : CaptureFrame R) (g : Fin R.m)
    (hs : Lineage2 R s.selection) (hr : CaptureReady R g s) : Prop :=
  ∃ potential : StopNode (ProposalActive R s g) → Nat,
    NatBellmanSuperSolution (proposalWalkStep R s g) 1 potential ∧
      potential (.active (proposalWalkStart R s g hs hr)) ≤ R.n*R.h

/-- Actual names of the semantic proposal transitions being refined. -/
theorem semantic_proposal_handoff :
    ShortGapCaptureLifecycle.Step .candidate .launchProposal .proposalOutbound ∧
      ShortGapCaptureLifecycle.Step .proposalOutbound .proposalAtCleanTarget .finalReturning :=
  ⟨.launchProposal,.proposalAtCleanTarget⟩

/-- The actual end-to-end selection process supplies the lineage premise
used by entry. Actor freedom remains the explicit clean-capture-lane input. -/
theorem physicalCandidate_success_entry (R : RFrame) (s : CandidateRunState R) (e : Fin R.n)
    (actors : Fin R.m → Actor) (ha : ∀ i, actors i = .freeHome)
    (h : physicalCandidateStep R s e = .success) :
    ∃ g, CaptureReady R g ⟨ghostStep2 R (candidateGhost R s) (edgeVtx R e),actors⟩ := by
  have hs : Lineage2 R (candidateGhost R s) := by
    cases s with
    | account s => exact account_lineage R s
    | realize s => exact s.property.1.lineage
  obtain ⟨g,hg⟩ := physicalCandidate_success_sound R s e h
  exact ⟨g,captureReady_of_bothCandidate R
    ⟨ghostStep2 R (candidateGhost R s) (edgeVtx R e),actors⟩
    (lineage2_step R _ hs _) ha g hg⟩

/-- The proposed local launch guard cannot itself enforce target-owned
selection-mover quiescence. A full reservation design must address this case. -/
theorem local_launch_with_busy_target_mover :
    (∃ x y, captureLaunch
      (taggedCfg exampleFrame (cleanFrame exampleFrame busyTargetExample) (rootV exampleFrame exampleGap))
      (taggedCfg exampleFrame (cleanFrame exampleFrame busyTargetExample) (rn exampleFrame (rootV exampleFrame exampleGap))) =
        some (x,y)) ∧
      ¬ OwnedMoverReady exampleFrame exampleGap (cleanFrame exampleFrame busyTargetExample) := by
  exact ⟨captureLaunch_enabled _ _ busyTargetExample_lineage _
    (captureReady_of_bothCandidate _ _ busyTargetExample_lineage (cleanFrame_actors _ _) _ busyTargetExample_candidate),
    stronger_readiness_counterexample.2.2⟩

#print axioms owner_candidate_delivered
#print axioms bothCandidate_empty
#print axioms owner_candidate_lock
#print axioms ghost_cfg_eq_persistence
#print axioms bothCandidate_stable
#print axioms captureReady_of_bothCandidate
#print axioms captureReady_stable
#print axioms captureLaunch_only_ready
#print axioms captureLaunch_enabled
#print axioms captureLaunch_no_relaunch
#print axioms capture_tag_selection_stutters
#print axioms selectionRow_embedding
#print axioms selection_disabled_during_capture
#print axioms captureLaunch_owned
#print axioms selection_disabled_after_launch
#print axioms latchedExample_lineage
#print axioms busyTargetExample_obligation
#print axioms stronger_readiness_counterexample
#print axioms stronger_readiness_not_stable
#print axioms local_launch_with_busy_target_mover
#print axioms physicalCandidate_success_entry
#print axioms proposalWalk_success_sound
#print axioms semantic_proposal_handoff

end ShortGapCaptureEntry

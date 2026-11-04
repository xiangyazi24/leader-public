import Leader.Wu.ShortGap.CaptureEntry

/-!
# Target-side reservation, the candidate-owned freeze, and the proposal walk

The runtime root has independent outgoing capture control and incoming
reservation.  The incoming reservation is installed in the same comparison
interaction (`K1`/`P1`) that writes `heldCandidate`, and `TGT` consumes it
while writing `FINAL` into the same slot.

Two design decisions are implemented here.

* There is one physical root mover shared by the actor side and the gap-owner
  side, so `CaptureReady` does **not** require mover-idle.  Instead the latch
  is a *candidate-owned freeze*: when a root's `ccw` becomes `heldCandidate`
  its gap-owner producer closes (no new `L1`, and no fused `P1`, on the gap it
  owns).  An owner trip that is already out returns once and then retires,
  because a latched root's own choice is `in0` and `res in0 _` is always a
  denial.  No denial is fabricated for the right endpoint of the next gap: its
  incoming port is a literal frame of every pre-commit step.

* No exception to the neighbour-skew clause is needed.  The global clause is
  re-derived at a latched gap and across every selection step.

The proposal/FINAL carrier is related by an explicit local row encoding to the
checked literal one-gap carrier.  Its scale-one budget is `n*(2*h-1)`,
including launch and FINAL deposit.  No root deletion or merged-gap cleanup is
part of this service.
-/

namespace ShortGapCaptureReservation
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapOwnerRoundSlice
open ShortGapLineage ShortGapLineageRetained ShortGapTwoEpoch
open ShortGapLineage2Closure ShortGapLineage2ClosureB ShortGapTwoEpochLaws
open ShortGapGhostComposition2 FiniteUniformStoppingTree
set_option autoImplicit false

/-- Outgoing capture state, separate from the selection cw port. -/
inductive OutControl where
  | home | proposal | finalReady
  deriving DecidableEq

/-- The reserved constructor is the incoming lease bit; accepted records
its consumption and cannot authorize a second proposal. -/
inductive InControl where
  | open | reserved | accepted
  deriving DecidableEq

inductive CaptureMessage where
  | proposal | finalBack
  deriving DecidableEq

inductive Wire where
  | selection (slot : Slot)
  | capture (message : CaptureMessage)
  deriving DecidableEq

/-- A constant-state extension of Agent. No shared mover, root ID, nonce,
or runtime generation occurs in the two capture controls. -/
inductive Node where
  | root (ch : Choice) (cw : CwPort) (ccw : CcwPort) (outgoing : OutControl) (incoming : InControl)
  | interior (wire : Wire)
  deriving DecidableEq

/-- The incoming selection port of a runtime node. -/
def Node.ccwPort : Node → Option CcwPort
  | .root _ _ ccw _ _ => some ccw
  | .interior _ => none

/-- The outgoing selection port of a runtime node. -/
def Node.cwPort : Node → Option CwPort
  | .root _ cw _ _ _ => some cw
  | .interior _ => none

/-- Install the incoming reservation exactly on a newly written candidate
port. Unchanged candidate ports do not regenerate consumed authority. -/
def reserveUpdate (old new : Option CcwPort) (lease : InControl) : InControl :=
  if old ≠ some .heldCandidate ∧ new = some .heldCandidate then .reserved else lease

theorem reserveUpdate_new_candidate (old : Option CcwPort) (lease : InControl)
    (h : old ≠ some .heldCandidate) : reserveUpdate old (some .heldCandidate) lease = .reserved := by
  simp [reserveUpdate,h]

theorem reserveUpdate_same (port : Option CcwPort) (lease : InControl) :
    reserveUpdate port port lease = lease := by simp [reserveUpdate]

/-- The reservation annotation follows actual selection states and is
updated in that same physical interaction, before any proposal service. -/
structure ReservationState (R : RFrame) where
  selection : GhostRing2 R
  incoming : Fin R.m → InControl

def reservationStep (R : RFrame) (s : ReservationState R) (e : Vtx R) : ReservationState R :=
  let t := ghostStep2 R s.selection e
  ⟨t,fun i => reserveUpdate (s.selection.cfg (rootV R i)).ccwPort
    (t.cfg (rootV R i)).ccwPort (s.incoming i)⟩

def reservationStart (R : RFrame) : ReservationState R :=
  ⟨ghostStart2 R,fun _ => .open⟩

/-- A clean selection-lane invariant, before reservation consumption. -/
def ReservedInvariant (R : RFrame) (s : ReservationState R) : Prop :=
  ∀ i, (s.selection.cfg (rootV R i)).ccwPort = some .heldCandidate → s.incoming i = .reserved

theorem reservedInvariant_start (R : RFrame) : ReservedInvariant R (reservationStart R) := by
  intro i h
  cases h

theorem reservedInvariant_step (R : RFrame) (s : ReservationState R)
    (h : ReservedInvariant R s) (e : Vtx R) : ReservedInvariant R (reservationStep R s e) := by
  intro i hi
  change reserveUpdate (s.selection.cfg (rootV R i)).ccwPort
    ((ghostStep2 R s.selection e).cfg (rootV R i)).ccwPort (s.incoming i) = .reserved
  by_cases ho : (s.selection.cfg (rootV R i)).ccwPort = some .heldCandidate
  · simp [reserveUpdate,ho,h i ho]
  · change ((ghostStep2 R s.selection e).cfg (rootV R i)).ccwPort = some .heldCandidate at hi
    simp [reserveUpdate,ho,hi]

inductive SelectionReachable (R : RFrame) : ReservationState R → Prop where
  | start : SelectionReachable R (reservationStart R)
  | step {s} : SelectionReachable R s → (e : Vtx R) → SelectionReachable R (reservationStep R s e)

theorem reachable_reserved (R : RFrame) (s : ReservationState R) (h : SelectionReachable R s) :
    ReservedInvariant R s := by
  induction h with
  | start => exact reservedInvariant_start R
  | step h e ih => exact reservedInvariant_step R _ ih e

/-- The flag follows from the clean producer, not from an assumption added
to BothCandidate and not from a forged heldCandidate pattern. -/
theorem target_reserved_of_bothCandidate (R : RFrame) (s : ReservationState R)
    (h : SelectionReachable R s) (g : Fin R.m) (hc : BothCandidate R s.selection g) :
    s.incoming (next R g) = .reserved := reachable_reserved R s h _ hc.2

/-- K1 installs the reservation with its new candidate receipt. -/
theorem K1_reserves (cw : CwPort) (lease : InControl) :
    reserveUpdate (some .free)
      ((row (.interior (.decl .out1)) (.root .in0 cw .free)).2).ccwPort lease = .reserved := rfl

/-- P1 installs the same reservation when no interior slot exists. -/
theorem P1_reserves (ccw : CcwPort) (cw : CwPort) (lease : InControl) :
    reserveUpdate (some .free)
      ((row (.root .out1 .toSend ccw) (.root .in0 cw .free)).2).ccwPort lease = .reserved := rfl

/-- Target acceptance frames its opposite cw selection port and outgoing
capture control. This is the independent resource the old shared actor lacked. -/
def acceptTarget : Node → Node
  | .root .in0 cw .heldCandidate out .reserved => .root .in0 cw .heldCandidate out .accepted
  | a => a

theorem target_acceptance_frames_outgoing (cw : CwPort) (out : OutControl) :
    acceptTarget (.root .in0 cw .heldCandidate out .reserved) =
      .root .in0 cw .heldCandidate out .accepted := rfl

theorem other_gap_slots_framed (R : RFrame) (s : GhostRing2 R) (g : Fin R.m)
    (e : Vtx R) (he : g ≠ e.1) (a : Fin R.h) (ha : 0 < a.val) :
    (ghostStep2 R s e).cfg (g,a) = s.cfg (g,a) := other_gap_interior R s e g he a ha

/-! ## Literal proposal/FINAL row as a finite carrier encoding

The checked single-gap table already implements launch, outward transport,
comparison-in-place, return transport, and deposit in 2h-1 firings. Here its
control ports are encoded as capture controls while physical candidate ports
remain fixed. The codec and row simulation below establish this reuse.
-/

/-- Only opposite-side capture controls are parameters of the codec. -/
structure Environment where
  sourceIncoming : InControl
  targetOutgoing : OutControl

def outgoingOf : CwPort → OutControl
  | .toSend => .home
  | .waiting => .proposal
  | .heldDenial | .heldCandidate => .finalReady

def virtualCw : OutControl → CwPort
  | .home => .toSend
  | .proposal => .waiting
  | .finalReady => .heldCandidate

def incomingOf : CcwPort → InControl
  | .free => .reserved
  | .heldDenial | .heldCandidate => .accepted

def encodeSlot : Slot → Wire
  | .empty => .selection .empty
  | .decl _ => .capture .proposal
  | .reply _ => .capture .finalBack

def encodeAgent (env : Environment) : Agent → Node
  | .root .out1 cw ccw => .root .out1 .heldCandidate ccw (outgoingOf cw) env.sourceIncoming
  | .root .in0 cw ccw => .root .in0 cw .heldCandidate env.targetOutgoing (incomingOf ccw)
  | .root .race cw ccw => .root .race cw ccw .home .open
  | .interior slot => .interior (encodeSlot slot)

/-- Capture never decodes a live selection message as its own token. -/
def decodeWire : Wire → Option Slot
  | .selection .empty => some .empty
  | .capture .proposal => some (.decl .out1)
  | .capture .finalBack => some (.reply .in0)
  | _ => none

def decodeLeft : Node → Option Agent
  | .root .out1 .heldCandidate ccw out _ => some (.root .out1 (virtualCw out) ccw)
  | .interior wire => (decodeWire wire).map Agent.interior
  | _ => none

/-- The incoming lease is authoritative: open does not decode. -/
def decodeRight : Node → Option Agent
  | .root .in0 cw .heldCandidate _ .reserved => some (.root .in0 cw .free)
  | .root .in0 cw .heldCandidate _ .accepted => some (.root .in0 cw .heldCandidate)
  | .interior wire => (decodeWire wire).map Agent.interior
  | _ => none

def environmentOf (a b : Node) : Environment where
  sourceIncoming := match a with | .root _ _ _ _ incoming => incoming | _ => .open
  targetOutgoing := match b with | .root _ _ _ out _ => out | _ => .home

/-- A finite radius-one row. The role-specific decoders exclude a target
acting as a capture source on its opposite side. Encoding frames both
opposite controls. No runtime coordinate or ghost generation is inspected. -/
def captureRow (a b : Node) : Node × Node :=
  match decodeLeft a, decodeRight b with
  | some x, some y =>
      let p := row x y
      (encodeAgent (environmentOf a b) p.1,encodeAgent (environmentOf a b) p.2)
  | _, _ => (a,b)

theorem captureRow_of_left_none (a b : Node) (h : decodeLeft a = none) :
    captureRow a b = (a,b) := by
  unfold captureRow
  rw [h]

theorem captureRow_of_right_none (a b : Node) (h : decodeRight b = none) :
    captureRow a b = (a,b) := by
  unfold captureRow
  rw [h]
  cases decodeLeft a <;> rfl

theorem launch_row (ccw : CcwPort) (inc : InControl) :
    captureRow (.root .out1 .heldCandidate ccw .home inc) (.interior (.selection .empty)) =
      (.root .out1 .heldCandidate ccw .proposal inc,.interior (.capture .proposal)) := rfl

theorem proposal_forward_row :
    captureRow (.interior (.capture .proposal)) (.interior (.selection .empty)) =
      (.interior (.selection .empty),.interior (.capture .proposal)) := rfl

/-- TGT consumes reserved and creates FINAL at the same physical slot.
Neither cw nor the target's outgoing control is tested or overwritten. -/
theorem TGT_row (cw : CwPort) (out : OutControl) :
    captureRow (.interior (.capture .proposal)) (.root .in0 cw .heldCandidate out .reserved) =
      (.interior (.capture .finalBack),.root .in0 cw .heldCandidate out .accepted) := rfl

theorem unreserved_target_rejects (cw : CwPort) (out : OutControl) :
    captureRow (.interior (.capture .proposal)) (.root .in0 cw .heldCandidate out .open) =
      (.interior (.capture .proposal),.root .in0 cw .heldCandidate out .open) := rfl

theorem consumed_target_rejects (cw : CwPort) (out : OutControl) :
    captureRow (.interior (.capture .proposal)) (.root .in0 cw .heldCandidate out .accepted) =
      (.interior (.capture .proposal),.root .in0 cw .heldCandidate out .accepted) := rfl

theorem FINAL_backward_row :
    captureRow (.interior (.selection .empty)) (.interior (.capture .finalBack)) =
      (.interior (.capture .finalBack),.interior (.selection .empty)) := rfl

theorem FINAL_deposit_row (ccw : CcwPort) (inc : InControl) :
    captureRow (.root .out1 .heldCandidate ccw .proposal inc) (.interior (.capture .finalBack)) =
      (.root .out1 .heldCandidate ccw .finalReady inc,.interior (.selection .empty)) := rfl

/-- With h=1, launch, acceptance and FINAL deposit share one pair firing. -/
theorem direct_row (ccw : CcwPort) (cw : CwPort) (inc : InControl) (out : OutControl) :
    captureRow (.root .out1 .heldCandidate ccw .home inc) (.root .in0 cw .heldCandidate out .reserved) =
      (.root .out1 .heldCandidate ccw .finalReady inc,.root .in0 cw .heldCandidate out .accepted) := rfl

/-- The virtual left endpoint has the source role or a correctly typed slot. -/
def LeftValid (a : Agent) : Prop :=
  (∃ cw ccw, cw ≠ .heldDenial ∧ a = .root .out1 cw ccw) ∨
    a = .interior .empty ∨ a = .interior (.decl .out1) ∨ a = .interior (.reply .in0)

def RightValid (a : Agent) : Prop :=
  (∃ cw ccw, ccw ≠ .heldDenial ∧ a = .root .in0 cw ccw) ∨
    a = .interior .empty ∨ a = .interior (.decl .out1) ∨ a = .interior (.reply .in0)

/-- Local simulation is established for explicit source/target/slot roles;
it is not an assumed carrier law. -/
theorem captureRow_encodes_row (env : Environment) (a b : Agent)
    (ha : LeftValid a) (hb : RightValid b) :
    captureRow (encodeAgent env a) (encodeAgent env b) =
      (encodeAgent env (row a b).1,encodeAgent env (row a b).2) := by
  rcases ha with ⟨cw,ccw,hcw,rfl⟩ | rfl | rfl | rfl <;>
    rcases hb with ⟨dw,dd,hdd,rfl⟩ | rfl | rfl | rfl
  all_goals try cases cw
  all_goals try cases dd
  all_goals simp_all [captureRow,encodeAgent,decodeLeft,decodeRight,decodeWire,encodeSlot,
    outgoingOf,incomingOf,virtualCw,environmentOf,row,resolveInit,resolveResp,resCw,resCcw,res,
    Verdict.cw,Verdict.ccw]

/-- Virtual transport geometry, with the two fixed candidate choices.
Opposite selection ports are arbitrary parameters, including waiting. -/
def walkFrame (R : RFrame) (sourceCcw : CcwPort) (targetCw : CwPort) : Frame where
  h := R.h
  hpos := R.hh
  c := .out1
  d := .in0
  hc := Or.inl rfl
  hd := Or.inr rfl
  ccw0 := sourceCcw
  cw0 := targetCw

theorem left_valid_site (R : RFrame) (ccw : CcwPort) (cw : CwPort)
    (p : Phase) (k : Nat) (hk : k < R.h) : LeftValid (siteOf (walkFrame R ccw cw) p k) := by
  have hne : k ≠ R.h := by omega
  cases p <;> by_cases h0 : k = 0 <;>
    simp [siteOf,walkFrame,h0,hne,LeftValid,resCw,res,Verdict.cw]
  all_goals split <;> simp_all

theorem right_valid_site (R : RFrame) (ccw : CcwPort) (cw : CwPort)
    (p : Phase) (k : Nat) (hk : 0 < k) : RightValid (siteOf (walkFrame R ccw cw) p k) := by
  have hne : k ≠ 0 := by omega
  cases p <;> by_cases hh : k = R.h <;>
    simp [siteOf,walkFrame,hne,hh,RightValid,resCcw,res,Verdict.ccw]
  all_goals split <;> simp_all <;> omega

abbrev CaptureConfig (F : Frame) := Fin (F.h+1) → Node

def encodeConfig (env : Environment) {F : Frame} (cfg : Config F) : CaptureConfig F :=
  fun k => encodeAgent env (cfg k)

/-- Actual pair updates on the selected gap, including its two roots. -/
def captureGapStep (F : Frame) (cfg : CaptureConfig F) (a : Fin F.h) : CaptureConfig F :=
  fun k =>
    if k.val = a.val then (captureRow (cfg (leftEnd F a)) (cfg (rightEnd F a))).1
    else if k.val = a.val+1 then (captureRow (cfg (leftEnd F a)) (cfg (rightEnd F a))).2
    else cfg k

theorem captureGapStep_encodes (R : RFrame) (ccw : CcwPort) (cw : CwPort) (env : Environment)
    (p : Phase) (a : Fin R.h) :
    captureGapStep (walkFrame R ccw cw) (encodeConfig env (configOf (walkFrame R ccw cw) p)) a =
      encodeConfig env (gapStep (walkFrame R ccw cw) (configOf (walkFrame R ccw cw) p) a) := by
  have hp := captureRow_encodes_row env
    (siteOf (walkFrame R ccw cw) p a.val) (siteOf (walkFrame R ccw cw) p (a.val+1))
    (left_valid_site R ccw cw p a.val a.isLt) (right_valid_site R ccw cw p (a.val+1) (by omega))
  funext k
  unfold captureGapStep encodeConfig gapStep
  change (if k.val = a.val then _ else if k.val = a.val+1 then _ else _) = _
  have hrow : captureRow
      (encodeAgent env (configOf (walkFrame R ccw cw) p (leftEnd (walkFrame R ccw cw) a)))
      (encodeAgent env (configOf (walkFrame R ccw cw) p (rightEnd (walkFrame R ccw cw) a))) = _ := hp
  rw [hrow]
  by_cases h0 : k.val = a.val <;> by_cases h1 : k.val = a.val+1 <;> simp [h0,h1,configOf,leftEnd,rightEnd]

/-- Exact phase closure of the new literal pair row, including direct h=1. -/
theorem captureGapStep_phase (R : RFrame) (ccw : CcwPort) (cw : CwPort) (env : Environment)
    (p : Phase) (hp : PhaseOk (walkFrame R ccw cw) p) (a : Fin R.h) :
    captureGapStep (walkFrame R ccw cw) (encodeConfig env (configOf (walkFrame R ccw cw) p)) a =
      encodeConfig env (configOf (walkFrame R ccw cw) (nextPhase (walkFrame R ccw cw) p a)) := by
  exact (captureGapStep_encodes R ccw cw env p a).trans
    (congrArg (encodeConfig env) (gapStep_configOf (walkFrame R ccw cw) p hp a))

/-- Encode the gap's real scheduler edges in the ambient Fin n clock. -/
def walkEmbedding (R : RFrame) (g : Fin R.m) (ccw : CcwPort) (cw : CwPort) :
    GapEmbedding (walkFrame R ccw cw) R.n where
  edgeAt a := encE R g a
  inj a b h := by
    have he := congrArg (edgeVtx R) h
    have he' : (g,(a : Fin R.h)) = (g,(b : Fin R.h)) :=
      (edgeVtx_encE R g a).symm.trans (he.trans (edgeVtx_encE R g b))
    exact congrArg Prod.snd he'

noncomputable def captureSchedStep {n : Nat} (F : Frame) (E : GapEmbedding F n)
    (cfg : CaptureConfig F) (e : Fin n) : CaptureConfig F :=
  if hx : ∃ a : Fin F.h, E.edgeAt a = e then captureGapStep F cfg hx.choose else cfg

/-- The clock and physical pair row commute with the complete carrier
encoding. The clean shape is produced by the imported closure theorem. -/
theorem captureSchedStep_encodes (R : RFrame) (g : Fin R.m) (ccw : CcwPort) (cw : CwPort)
    (env : Environment) (cfg : Config (walkFrame R ccw cw))
    (hc : Clean (walkFrame R ccw cw) cfg) (e : Fin R.n) :
    captureSchedStep (walkFrame R ccw cw) (walkEmbedding R g ccw cw) (encodeConfig env cfg) e =
      encodeConfig env (schedStep (walkFrame R ccw cw) (walkEmbedding R g ccw cw) cfg e) := by
  classical
  obtain ⟨p,_,rfl⟩ := hc.exists_phase
  unfold captureSchedStep schedStep
  split
  · exact captureGapStep_encodes R ccw cw env p _
  · rfl

abbrev WalkState (R : RFrame) (ccw : CcwPort) (cw : CwPort) :=
  ActiveCleanConfig (walkFrame R ccw cw)

/-- The checked state is a finite carrier encoding. Physical execution of
this kernel is captureSchedStep, as proved above; controls are not new guards. -/
noncomputable def proposalWalkStep (R : RFrame) (g : Fin R.m) (ccw : CcwPort) (cw : CwPort) :=
  gapNode (walkFrame R ccw cw) (walkEmbedding R g ccw cw)

def proposalWalkPotential (R : RFrame) (ccw : CcwPort) (cw : CwPort) :=
  gapPotential (n := R.n) (walkFrame R ccw cw)

/-- Scale one on the physical n-edge scheduler: the exact literal
proposal/FINAL debt is charged n times, with one useful edge per live token. -/
theorem proposalWalk_bellman (R : RFrame) (g : Fin R.m) (ccw : CcwPort) (cw : CwPort) :
    NatBellmanSuperSolution (proposalWalkStep R g ccw cw) 1 (proposalWalkPotential R ccw cw) :=
  gap_natBellmanSuperSolution (walkFrame R ccw cw) (walkEmbedding R g ccw cw)

def proposalWalkStart (R : RFrame) (ccw : CcwPort) (cw : CwPort) : WalkState R ccw cw :=
  ShortGapLiteralGapRows.startState (walkFrame R ccw cw)

theorem proposalWalk_start_potential (R : RFrame) (ccw : CcwPort) (cw : CwPort) :
    proposalWalkPotential R ccw cw (.active (proposalWalkStart R ccw cw)) = R.n*(2*R.h-1) :=
  gapPotential_startState (walkFrame R ccw cw)

/-- The potential is `n` times the number of remaining useful firings. -/
theorem proposalWalk_potential_eq (R : RFrame) (ccw : CcwPort) (cw : CwPort)
    (s : WalkState R ccw cw) :
    proposalWalkPotential R ccw cw (.active s) = R.n*deltaOf (walkFrame R ccw cw) s.1.1 := rfl

theorem proposalWalk_truncatedCost_le (R : RFrame) (g : Fin R.m) (ccw : CcwPort) (cw : CwPort) (T : Nat) :
    truncatedActiveCostNumerator (proposalWalkStep R g ccw cw) (.active (proposalWalkStart R ccw cw)) T ≤
      R.n^T*(R.n*(2*R.h-1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (proposalWalkStep R g ccw cw) 1 (proposalWalkPotential R ccw cw) (proposalWalk_bellman R g ccw cw)
    (.active (proposalWalkStart R ccw cw)) T
  simpa only [Nat.one_mul,proposalWalk_start_potential] using h

/-- Success is actual FINAL deposit, not just a zero assigned to an
unrelated terminal label. The whole encoded post-configuration is delivered. -/
theorem proposalWalk_success_sound (R : RFrame) (g : Fin R.m) (ccw : CcwPort) (cw : CwPort)
    (env : Environment) (s : WalkState R ccw cw) (e : Fin R.n)
    (hs : proposalWalkStep R g ccw cw s e = .success) :
    captureSchedStep (walkFrame R ccw cw) (walkEmbedding R g ccw cw)
        (encodeConfig env s.1.1) e =
      encodeConfig env (configOf (walkFrame R ccw cw) .delivered) := by
  have hz : deltaOf (walkFrame R ccw cw)
      (schedStep (walkFrame R ccw cw) (walkEmbedding R g ccw cw) s.1.1 e) = 0 := by
    unfold proposalWalkStep gapNode at hs
    split at hs
    · cases hs
    · omega
  exact (captureSchedStep_encodes R g ccw cw env s.1.1 s.1.2 e).trans
    (congrArg (encodeConfig env) (clean_delta_zero_delivered _ _ (clean_step _ _ _ s.1.2 e) hz))

theorem proposalWalk_no_failure (R : RFrame) (g : Fin R.m) (ccw : CcwPort) (cw : CwPort)
    (s : WalkState R ccw cw) (e : Fin R.n) : proposalWalkStep R g ccw cw s e ≠ .failure :=
  gapNode_ne_failure _ _ s e

theorem delivered_source (R : RFrame) (ccw : CcwPort) (cw : CwPort) (env : Environment) :
    encodeConfig env (configOf (walkFrame R ccw cw) .delivered) (leftPos (walkFrame R ccw cw)) =
      .root .out1 .heldCandidate ccw .finalReady env.sourceIncoming := rfl

theorem delivered_target (R : RFrame) (ccw : CcwPort) (cw : CwPort) (env : Environment) :
    encodeConfig env (configOf (walkFrame R ccw cw) .delivered) (rightPos (walkFrame R ccw cw)) =
      .root .in0 cw .heldCandidate env.targetOutgoing .accepted := by
  have hh : R.h ≠ 0 := by have := R.hh; omega
  simp [encodeConfig,configOf,siteOf,rightPos,walkFrame,hh,encodeAgent,incomingOf,resCcw,res,Verdict.ccw]

/-- The semantic control class of the source's runtime outgoing capture state. -/
def sourceControl : OutControl → ShortGapCaptureLifecycle.Control
  | .home => .candidate
  | .proposal => .proposalOutbound
  | .finalReady => .finalReady

/-- The lifecycle's actual constructor names are launchProposal,
proposalAtCleanTarget and returnFinal. The runtime terminal already includes
the FINAL deposit back at the source; acceptFinal (protection) and
commitAtTarget (deletion) remain separate actions. -/
theorem semantic_proposal_handoff (R : RFrame) (g : Fin R.m) (ccw : CcwPort) (cw : CwPort)
    (env : Environment) (s : WalkState R ccw cw) (e : Fin R.n)
    (hs : proposalWalkStep R g ccw cw s e = .success) :
    captureSchedStep (walkFrame R ccw cw) (walkEmbedding R g ccw cw)
        (encodeConfig env s.1.1) e (leftPos (walkFrame R ccw cw)) =
        .root .out1 .heldCandidate ccw .finalReady env.sourceIncoming ∧
    captureSchedStep (walkFrame R ccw cw) (walkEmbedding R g ccw cw)
        (encodeConfig env s.1.1) e (rightPos (walkFrame R ccw cw)) =
        .root .in0 cw .heldCandidate env.targetOutgoing .accepted ∧
    sourceControl .finalReady = ShortGapCaptureLifecycle.Control.finalReady ∧
    ShortGapCaptureLifecycle.Step .candidate .launchProposal .proposalOutbound ∧
    ShortGapCaptureLifecycle.Step .proposalOutbound .proposalAtCleanTarget .finalReturning ∧
    ShortGapCaptureLifecycle.Step .finalReturning .returnFinal .finalReady ∧
    ShortGapCaptureLifecycle.Trace .candidate
      [.launchProposal,.proposalAtCleanTarget,.returnFinal] .finalReady := by
  rw [proposalWalk_success_sound R g ccw cw env s e hs]
  refine ⟨delivered_source R ccw cw env,delivered_target R ccw cw env,rfl,
    .launchProposal,.proposalAtCleanTarget,.returnFinal,?_⟩
  exact .cons .launchProposal (.cons .proposalAtCleanTarget (.cons .returnFinal (.refl _)))

/-- The FINAL deposit at the source is the last useful firing of this walk;
the two semantic actions that follow it are separate. -/
theorem semantic_final_deposit_extends :
    ShortGapCaptureLifecycle.Step .finalReady .acceptFinal .protectedCommitOutbound ∧
      ShortGapCaptureLifecycle.Step .protectedCommitOutbound .commitAtTarget
        (.committed .full) ∧
      ShortGapCaptureLifecycle.Trace .candidate
        [.launchProposal,.proposalAtCleanTarget,.returnFinal,.acceptFinal,.commitAtTarget]
        (.committed .full) :=
  ⟨.acceptFinal,.commitAtTarget,
    .cons .launchProposal (.cons .proposalAtCleanTarget (.cons .returnFinal
      (.cons .acceptFinal (.cons .commitAtTarget (.refl _)))))⟩

/-! ## Selection, JOIN, and the candidate-owned freeze -/

/-- Selection reads only its own messages; live capture messages disable
selection on that pair. Root capture controls are not shared selection state. -/
def selectionView : Node → Option Agent
  | .root c cw ccw _ _ => some (.root c cw ccw)
  | .interior (.selection s) => some (.interior s)
  | _ => none

theorem selectionView_root (c : Choice) (cw : CwPort) (ccw : CcwPort)
    (out : OutControl) (inc : InControl) :
    selectionView (.root c cw ccw out inc) = some (.root c cw ccw) := rfl

def restoreSelection (old : Node) (new : Agent) : Node :=
  match old,new with
  | .root _ _ ccw out inc,.root c dw dd =>
      .root c dw dd out (reserveUpdate (some ccw) (some dd) inc)
  | .interior _,.interior s => .interior (.selection s)
  | _,_ => old

def joinNode : Node → Node
  | .root _ .heldDenial .heldDenial out inc => .root .race .toSend .free out inc
  | a => a

/-- Freeze predicate: this root's incoming side carries a latched
candidate, so it is the target of a live capture on the gap it does not own. -/
def OwnerLatched : Node → Bool
  | .root _ _ .heldCandidate _ _ => true
  | _ => false

/-- The producing rows of the owned clockwise gap: `L1`/`L2` into the first
empty interior slot, and the fused `P1` launch when the gap has length one.
`V1` return, `L3`, the `K` rows and JOIN are deliberately not listed: an
owner trip that is already out is allowed exactly one completion. -/
def ProducerRow : Node → Node → Bool
  | .root _ .toSend _ _ _, .interior (.selection .empty) => true
  | .root _ .toSend _ _ _, .root _ _ .free _ _ => true
  | _, _ => false

/-- The frozen selection dispatcher.  The only change to the imported
selection lane is the closed gap-owner producer of a latched root. -/
def selectionPair (a b : Node) : Node × Node :=
  match OwnerLatched a && ProducerRow a b with
  | true => (a,b)
  | false =>
    match selectionView a,selectionView b with
    | some x,some y =>
        let p := row x y
        (joinNode (restoreSelection a p.1),joinNode (restoreSelection b p.2))
    | _,_ => (a,b)

theorem selectionPair_frozen (a b : Node) (h : (OwnerLatched a && ProducerRow a b) = true) :
    selectionPair a b = (a,b) := by
  unfold selectionPair
  rw [h]

theorem selectionPair_open (a b : Node) (h : (OwnerLatched a && ProducerRow a b) = false)
    (x y : Agent) (ha : selectionView a = some x) (hb : selectionView b = some y) :
    selectionPair a b =
      (joinNode (restoreSelection a (row x y).1),joinNode (restoreSelection b (row x y).2)) := by
  unfold selectionPair
  rw [h,ha,hb]

theorem selectionPair_none_left (a b : Node) (h : (OwnerLatched a && ProducerRow a b) = false)
    (ha : selectionView a = none) : selectionPair a b = (a,b) := by
  unfold selectionPair
  rw [h,ha]

theorem selectionPair_none_right (a b : Node) (h : (OwnerLatched a && ProducerRow a b) = false)
    (hb : selectionView b = none) : selectionPair a b = (a,b) := by
  unfold selectionPair
  rw [h,hb]
  cases selectionView a <;> rfl

/-- A deterministic radius-one dispatcher. Selection has no enabled update
on a capture edge; on the two adjacent gaps capture is disabled by root role. -/
def runtimeRow (a b : Node) : Node × Node :=
  let p := selectionPair a b
  captureRow p.1 p.2

theorem runtimeRow_def (a b : Node) :
    runtimeRow a b = captureRow (selectionPair a b).1 (selectionPair a b).2 := rfl

/-! ### The freeze law -/

/-- Closing the latched root's own producer loses no candidate: a latched
root's choice is `in0`, and `res in0 _` is always a denial. -/
theorem latched_owner_cannot_win (d : Choice) :
    res .in0 d = .denial ∧ resCw .in0 d = .heldDenial ∧ resCcw .in0 d = .heldDenial := by
  cases d <;> exact ⟨rfl,rfl,rfl⟩

/-- The ghost-level fact behind it: the right endpoint of a latched gap has
choice `in0`. -/
theorem latched_target_choice (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hc : BothCandidate R s g) :
    ∃ cw ccw, s.cfg (rootV R (next R g)) = .root .in0 cw ccw :=
  (ShortGapCaptureEntry.owner_candidate_lock R s hs g hc.1).root_choices.2

/-- No new `L1` on the gap owned by a latched root, at any gap length. -/
theorem latched_no_L1 (c : Choice) (out : OutControl) (inc : InControl) :
    selectionPair (.root c .toSend .heldCandidate out inc) (.interior (.selection .empty)) =
      (.root c .toSend .heldCandidate out inc,.interior (.selection .empty)) := rfl

/-- No fused `P1` either: the length-one specialization is closed too, so no
denial is fabricated for the right endpoint of the next gap. -/
theorem latched_no_P1 (c c' : Choice) (cw' : CwPort) (out out' : OutControl)
    (inc inc' : InControl) :
    selectionPair (.root c .toSend .heldCandidate out inc) (.root c' cw' .free out' inc') =
      (.root c .toSend .heldCandidate out inc,.root c' cw' .free out' inc') := rfl

theorem latched_owner_producer_closed (c : Choice) (cw : CwPort) (out : OutControl)
    (inc : InControl) (b : Node)
    (hb : ProducerRow (.root c cw .heldCandidate out inc) b = true) :
    selectionPair (.root c cw .heldCandidate out inc) b =
      (.root c cw .heldCandidate out inc,b) :=
  selectionPair_frozen _ _ (by rw [hb]; rfl)

/-- The candidate latch is installed by `K1` in the same interaction, and the
resulting root is already frozen. -/
theorem latch_step_closes_owner (cw : CwPort) (out : OutControl) (inc : InControl) :
    selectionPair (.interior (.selection (.decl .out1))) (.root .in0 cw .free out inc) =
      (.interior (.selection (.reply .in0)),.root .in0 cw .heldCandidate out .reserved) ∧
    OwnerLatched (.root .in0 cw .heldCandidate out .reserved) = true := by
  refine ⟨?_,rfl⟩
  rw [selectionPair_open _ _ rfl (.interior (.decl .out1)) (.root .in0 cw .free) rfl
    (selectionView_root ..)]
  cases cw <;> rfl

/-- A latched root does not JOIN: JOIN needs two held denials. -/
theorem latched_blocks_join (c : Choice) (cw : CwPort) (out : OutControl) (inc : InControl) :
    joinNode (.root c cw .heldCandidate out inc) = .root c cw .heldCandidate out inc := by
  cases cw <;> rfl

theorem join_source_fixed (ccw : CcwPort) (out : OutControl) (inc : InControl) :
    joinNode (.root .out1 .heldCandidate ccw out inc) =
      .root .out1 .heldCandidate ccw out inc := rfl

theorem join_target_fixed (cw : CwPort) (out : OutControl) (inc : InControl) :
    joinNode (.root .in0 cw .heldCandidate out inc) =
      .root .in0 cw .heldCandidate out inc := latched_blocks_join _ _ _ _

/-- An owner trip that was already out returns exactly once and then retires:
the returned verdict is a denial, so the clockwise port can never be `toSend`
again and the closed producer needs no further guard. -/
theorem latched_return_retires (c : Choice) (d : Choice) (out : OutControl) (inc : InControl) :
    selectionPair (.root .in0 .waiting .heldCandidate out inc)
        (.interior (.selection (.reply d))) =
      (.root .in0 .heldDenial .heldCandidate out inc,.interior (.selection .empty)) ∧
    ProducerRow (.root .in0 .heldDenial .heldCandidate out inc) (.interior (.selection .empty))
      = false ∧
    ProducerRow (.root .in0 .heldDenial .heldCandidate out inc)
      (.root c .toSend .free out inc) = false := by
  refine ⟨?_,rfl,rfl⟩
  rw [selectionPair_open _ _ rfl (.root .in0 .waiting .heldCandidate) (.interior (.reply d))
    (selectionView_root ..) rfl]
  cases d <;> rfl

/-! ### Frame lemmas for the runtime dispatcher -/

theorem decodeLeft_root (c : Choice) (cw : CwPort) (ccw : CcwPort) (out : OutControl)
    (inc : InControl) (x : Agent) (h : decodeLeft (.root c cw ccw out inc) = some x) :
    c = .out1 ∧ cw = .heldCandidate ∧ x = .root .out1 (virtualCw out) ccw := by
  cases c <;> cases cw <;> simp_all [decodeLeft]

theorem decodeRight_root (c : Choice) (cw : CwPort) (ccw : CcwPort) (out : OutControl)
    (inc : InControl) (y : Agent) (h : decodeRight (.root c cw ccw out inc) = some y) :
    c = .in0 ∧ ccw = .heldCandidate ∧ ∃ d, y = .root .in0 cw d := by
  cases c <;> cases ccw <;> cases inc <;> simp_all [decodeRight] <;> exact ⟨_,h.symm⟩

theorem decodeLeft_in0 (cw : CwPort) (ccw : CcwPort) (out : OutControl) (inc : InControl) :
    decodeLeft (.root .in0 cw ccw out inc) = none := by
  cases cw <;> cases ccw <;> rfl

theorem decodeLeft_race (cw : CwPort) (ccw : CcwPort) (out : OutControl) (inc : InControl) :
    decodeLeft (.root .race cw ccw out inc) = none := by
  cases cw <;> cases ccw <;> rfl

theorem decodeRight_free (c : Choice) (cw : CwPort) (out : OutControl) (inc : InControl) :
    decodeRight (.root c cw .free out inc) = none := by
  cases c <;> cases inc <;> rfl

/-- The capture row frames the initiator's counterclockwise selection port. -/
theorem captureRow_initiator_keeps_ccw (c : Choice) (cw : CwPort) (ccw : CcwPort)
    (out : OutControl) (inc : InControl) (b : Node) :
    ∃ c' cw' out' inc', (captureRow (.root c cw ccw out inc) b).1 = .root c' cw' ccw out' inc' := by
  cases hl : decodeLeft (Node.root c cw ccw out inc) with
  | none => exact ⟨c,cw,out,inc,by rw [captureRow_of_left_none _ _ hl]⟩
  | some x =>
    cases hr : decodeRight b with
    | none => exact ⟨c,cw,out,inc,by rw [captureRow_of_right_none _ _ hr]⟩
    | some y =>
      obtain ⟨rfl,rfl,rfl⟩ := decodeLeft_root c cw ccw out inc x hl
      obtain ⟨cw2,hrow⟩ := row_initiator_keeps_ccw_of_ne_race .out1 (virtualCw out) ccw y
        (by intro hh; cases hh)
      refine ⟨.out1,.heldCandidate,outgoingOf cw2,inc,?_⟩
      unfold captureRow
      rw [hl,hr]
      show encodeAgent _ (row (.root .out1 (virtualCw out) ccw) y).1 = _
      rw [hrow]
      rfl

/-- The capture row never writes a free incoming port of a responder: the
capture target decoder demands a latched candidate lease. -/
theorem captureRow_responder_free_ccw (a : Node) (c : Choice) (cw : CwPort)
    (out : OutControl) (inc : InControl) :
    (captureRow a (.root c cw .free out inc)).2 = .root c cw .free out inc := by
  rw [captureRow_of_right_none _ _ (decodeRight_free c cw out inc)]

/-- The whole dispatcher frames an initiator's counterclockwise port whenever
that port is not itself a held denial (the only JOIN trigger). -/
theorem runtimeRow_initiator_keeps_ccw (c : Choice) (cw : CwPort) (ccw : CcwPort)
    (out : OutControl) (inc : InControl) (b : Node) (hj : ccw ≠ .heldDenial) :
    ∃ c' cw' out' inc', (runtimeRow (.root c cw ccw out inc) b).1 = .root c' cw' ccw out' inc' := by
  have hsel : ∃ c' cw' out' inc',
      (selectionPair (.root c cw ccw out inc) b).1 = .root c' cw' ccw out' inc' := by
    cases hgate : OwnerLatched (Node.root c cw ccw out inc) && ProducerRow (.root c cw ccw out inc) b with
    | true => exact ⟨c,cw,out,inc,by rw [selectionPair_frozen _ _ hgate]⟩
    | false =>
      cases hb : selectionView b with
      | none => exact ⟨c,cw,out,inc,by rw [selectionPair_none_right _ _ hgate hb]⟩
      | some y =>
        obtain ⟨c2,cw2,hrow⟩ := row_initiator_keeps_ccw c cw ccw y
        refine ⟨c2,cw2,out,reserveUpdate (some ccw) (some ccw) inc,?_⟩
        rw [selectionPair_open _ _ hgate _ _ (selectionView_root ..) hb,hrow]
        show joinNode (.root c2 cw2 ccw out (reserveUpdate (some ccw) (some ccw) inc)) = _
        cases ccw with
        | free => cases cw2 <;> rfl
        | heldDenial => exact absurd rfl hj
        | heldCandidate => cases cw2 <;> rfl
  obtain ⟨c2,cw2,out2,inc2,hsel⟩ := hsel
  rw [runtimeRow_def,hsel]
  exact captureRow_initiator_keeps_ccw c2 cw2 ccw out2 inc2 _

/-- No row of the frozen dispatcher writes a free incoming port whose gap
owner is either quiet or latched: `K1`, `K2` and `P1` are all excluded.  This
is the exact "do not fabricate a denial" clause. -/
theorem runtimeRow_keeps_free_responder (a : Node) (c : Choice) (cw : CwPort)
    (out : OutControl) (inc : InControl)
    (ha : a = .interior (.selection .empty) ∨
      ∃ cw0 out0 inc0, a = .root .in0 cw0 .heldCandidate out0 inc0) :
    ∃ c' cw' out' inc',
      (runtimeRow a (.root c cw .free out inc)).2 = .root c' cw' .free out' inc' := by
  have hsel : ∃ c' cw' out' inc',
      (selectionPair a (.root c cw .free out inc)).2 = .root c' cw' .free out' inc' := by
    rcases ha with rfl | ⟨cw0,out0,inc0,rfl⟩
    · refine ⟨resolveResp c,cw,out,reserveUpdate (some .free) (some .free) inc,?_⟩
      rw [selectionPair_open _ _ rfl (.interior .empty) (.root c cw .free) rfl
        (selectionView_root ..)]
      show joinNode (restoreSelection (.root c cw .free out inc)
        (row (.interior .empty) (.root c cw .free)).2) = _
      cases cw <;> rfl
    · cases hgate : OwnerLatched (Node.root .in0 cw0 .heldCandidate out0 inc0) &&
        ProducerRow (.root .in0 cw0 .heldCandidate out0 inc0) (.root c cw .free out inc) with
      | true => exact ⟨c,cw,out,inc,by rw [selectionPair_frozen _ _ hgate]⟩
      | false =>
        have hcw0 : cw0 ≠ .toSend := by
          intro hh
          subst hh
          exact Bool.noConfusion hgate
        have hrow : (row (.root .in0 cw0 .heldCandidate) (.root c cw .free)).2
            = .root (resolveResp c) cw .free := by
          simp [row,hcw0]
        refine ⟨resolveResp c,cw,out,reserveUpdate (some .free) (some .free) inc,?_⟩
        rw [selectionPair_open _ _ hgate _ _ (selectionView_root ..) (selectionView_root ..),hrow]
        show joinNode (.root (resolveResp c) cw .free out
          (reserveUpdate (some .free) (some .free) inc)) = _
        cases cw <;> rfl
  obtain ⟨c2,cw2,out2,inc2,hsel⟩ := hsel
  refine ⟨c2,cw2,out2,inc2,?_⟩
  rw [runtimeRow_def,hsel]
  exact captureRow_responder_free_ccw _ c2 cw2 out2 inc2

/-- Even before launch, the physical candidate ports prohibit selection.
JOIN is included in this statement; typed capture messages cannot be used
as selection declarations or replies. -/
theorem selectionPair_encoded_stutter (env : Environment) (a b : Agent)
    (ha : LeftValid a) (hb : RightValid b) :
    selectionPair (encodeAgent env a) (encodeAgent env b) =
      (encodeAgent env a,encodeAgent env b) := by
  rcases ha with ⟨cw,ccw,hcw,rfl⟩ | rfl | rfl | rfl <;>
    rcases hb with ⟨dw,dd,hdd,rfl⟩ | rfl | rfl | rfl
  all_goals try cases dw
  all_goals simp_all [selectionPair,selectionView,encodeAgent,encodeSlot,row,OwnerLatched,
    ProducerRow,restoreSelection,joinNode,reserveUpdate,resolveInit,resolveResp]

theorem selection_disabled_during_capture (R : RFrame) (ccw : CcwPort) (cw : CwPort)
    (env : Environment) (p : Phase) (a : Fin R.h) :
    selectionPair (encodeAgent env (siteOf (walkFrame R ccw cw) p a.val))
      (encodeAgent env (siteOf (walkFrame R ccw cw) p (a.val+1))) =
    (encodeAgent env (siteOf (walkFrame R ccw cw) p a.val),
      encodeAgent env (siteOf (walkFrame R ccw cw) p (a.val+1))) :=
  selectionPair_encoded_stutter env _ _ (left_valid_site R ccw cw p _ a.isLt)
    (right_valid_site R ccw cw p _ (by omega))

theorem runtimeRow_encodes_row (env : Environment) (a b : Agent)
    (ha : LeftValid a) (hb : RightValid b) :
    runtimeRow (encodeAgent env a) (encodeAgent env b) =
      (encodeAgent env (row a b).1,encodeAgent env (row a b).2) := by
  unfold runtimeRow
  rw [selectionPair_encoded_stutter env a b ha hb]
  exact captureRow_encodes_row env a b ha hb

/-- The full dispatcher preserves the incoming reservation when this root
works as owner of its other gap. This includes the post-row JOIN. -/
theorem runtime_target_side (cw : CwPort) (out : OutControl) (inc : InControl) (b : Node) :
    ∃ cw', (runtimeRow (.root .in0 cw .heldCandidate out inc) b).1 =
      .root .in0 cw' .heldCandidate out inc := by
  have hsel : ∃ cw', (selectionPair (.root .in0 cw .heldCandidate out inc) b).1 =
      .root .in0 cw' .heldCandidate out inc := by
    cases hgate : OwnerLatched (Node.root .in0 cw .heldCandidate out inc) &&
        ProducerRow (.root .in0 cw .heldCandidate out inc) b with
    | true => exact ⟨cw,by rw [selectionPair_frozen _ _ hgate]⟩
    | false =>
      cases hb : selectionView b with
      | none => exact ⟨cw,by rw [selectionPair_none_right _ _ hgate hb]⟩
      | some y =>
        obtain ⟨cw2,hrow⟩ := row_initiator_keeps_ccw_of_ne_race .in0 cw .heldCandidate y
          (by intro hh; cases hh)
        refine ⟨cw2,?_⟩
        rw [selectionPair_open _ _ hgate _ _ (selectionView_root ..) hb,hrow]
        show joinNode (.root .in0 cw2 .heldCandidate out
          (reserveUpdate (some .heldCandidate) (some .heldCandidate) inc)) = _
        rw [reserveUpdate_same]
        exact join_target_fixed _ _ _
  obtain ⟨cw2,hsel⟩ := hsel
  refine ⟨cw2,?_⟩
  have hnone : decodeLeft (selectionPair (.root .in0 cw .heldCandidate out inc) b).1 = none := by
    rw [hsel]
    rfl
  rw [runtimeRow_def,captureRow_of_left_none _ _ hnone]
  exact hsel

/-- As responder on the preceding gap, the source preserves its outgoing
capture control and candidate latch. Its unrelated incoming side may change. -/
theorem runtime_source_side (ccw : CcwPort) (out : OutControl) (inc : InControl) (a : Node) :
    ∃ dd di, (runtimeRow a (.root .out1 .heldCandidate ccw out inc)).2 =
      .root .out1 .heldCandidate dd out di := by
  have hsel : ∃ dd di, (selectionPair a (.root .out1 .heldCandidate ccw out inc)).2 =
      .root .out1 .heldCandidate dd out di := by
    cases hgate : OwnerLatched a && ProducerRow a (.root .out1 .heldCandidate ccw out inc) with
    | true => exact ⟨ccw,inc,by rw [selectionPair_frozen _ _ hgate]⟩
    | false =>
      cases ha : selectionView a with
      | none => exact ⟨ccw,inc,by rw [selectionPair_none_left _ _ hgate ha]⟩
      | some x =>
        obtain ⟨dd,hrow⟩ := row_responder_keeps_cw_of_ne_race x .out1 .heldCandidate ccw
          (by intro hh; cases hh)
        refine ⟨dd,reserveUpdate (some ccw) (some dd) inc,?_⟩
        rw [selectionPair_open _ _ hgate _ _ ha (selectionView_root ..),hrow]
        rfl
  obtain ⟨dd,di,hsel⟩ := hsel
  refine ⟨dd,di,?_⟩
  have hnone : decodeRight (selectionPair a (.root .out1 .heldCandidate ccw out inc)).2 = none := by
    rw [hsel]
    rfl
  rw [runtimeRow_def,captureRow_of_right_none _ _ hnone]
  exact hsel

/-- A latched responder keeps its choice and its candidate incoming port.
The lease itself may advance from `reserved` to `accepted`: that is the `TGT`
row consuming the reservation, which is the only intended writer. -/
theorem runtimeRow_latched_responder (a : Node) (cw : CwPort) (out : OutControl)
    (inc : InControl) :
    ∃ cw' out' inc', (runtimeRow a (.root .in0 cw .heldCandidate out inc)).2 =
      .root .in0 cw' .heldCandidate out' inc' := by
  have hsel : (selectionPair a (.root .in0 cw .heldCandidate out inc)).2 =
      .root .in0 cw .heldCandidate out inc := by
    cases hgate : OwnerLatched a && ProducerRow a (.root .in0 cw .heldCandidate out inc) with
    | true => rw [selectionPair_frozen _ _ hgate]
    | false =>
      cases ha : selectionView a with
      | none => rw [selectionPair_none_left _ _ hgate ha]
      | some x =>
        have hrow : (row x (.root .in0 cw .heldCandidate)).2 = .root .in0 cw .heldCandidate := by
          cases x with
          | root ch cw0 ccw0 =>
            by_cases hs : cw0 = CwPort.toSend <;> simp [row,hs]
          | interior sl => cases sl <;> simp [row,resolveResp]
        rw [selectionPair_open _ _ hgate _ _ ha (selectionView_root ..),hrow]
        show joinNode (.root .in0 cw .heldCandidate out
          (reserveUpdate (some .heldCandidate) (some .heldCandidate) inc)) = _
        rw [reserveUpdate_same]
        exact join_target_fixed _ _ _
  rw [runtimeRow_def,hsel]
  cases hl : decodeLeft (selectionPair a (.root .in0 cw .heldCandidate out inc)).1 with
  | none => exact ⟨cw,out,inc,by rw [captureRow_of_left_none _ _ hl]⟩
  | some x =>
    cases hr : decodeRight (Node.root Choice.in0 cw CcwPort.heldCandidate out inc) with
    | none => exact ⟨cw,out,inc,by rw [captureRow_of_right_none _ _ hr]⟩
    | some y =>
      obtain ⟨-,-,d,rfl⟩ := decodeRight_root .in0 cw .heldCandidate out inc y hr
      obtain ⟨d',hrow⟩ := row_responder_keeps_cw_of_ne_race x .in0 cw d (by intro hh; cases hh)
      refine ⟨cw,out,incomingOf d',?_⟩
      unfold captureRow
      rw [hl,hr]
      show encodeAgent _ (row x (.root .in0 cw d)).2 = _
      rw [hrow]
      rfl

/-- A latched root is never a capture source: its choice is `in0`, so the
whole dispatcher reduces to the frozen selection lane on that side. -/
theorem selectionPair_in0_left_no_capture (cw : CwPort) (ccw : CcwPort) (out : OutControl)
    (inc : InControl) (b : Node) :
    decodeLeft (selectionPair (.root .in0 cw ccw out inc) b).1 = none := by
  cases hgate : OwnerLatched (Node.root .in0 cw ccw out inc) &&
      ProducerRow (.root .in0 cw ccw out inc) b with
  | true =>
    rw [selectionPair_frozen _ _ hgate]
    exact decodeLeft_in0 cw ccw out inc
  | false =>
    cases hb : selectionView b with
    | none =>
      rw [selectionPair_none_right _ _ hgate hb]
      exact decodeLeft_in0 cw ccw out inc
    | some y =>
      obtain ⟨cw2,hrow⟩ := row_initiator_keeps_ccw_of_ne_race .in0 cw ccw y
        (by intro hh; cases hh)
      rw [selectionPair_open _ _ hgate _ _ (selectionView_root ..) hb,hrow]
      show decodeLeft (joinNode (.root .in0 cw2 ccw out
        (reserveUpdate (some ccw) (some ccw) inc))) = none
      cases ccw <;> cases cw2 <;> rfl

theorem runtimeRow_of_in0_left (cw : CwPort) (ccw : CcwPort) (out : OutControl)
    (inc : InControl) (b : Node) :
    runtimeRow (.root .in0 cw ccw out inc) b = selectionPair (.root .in0 cw ccw out inc) b := by
  rw [runtimeRow_def,captureRow_of_left_none _ _ (selectionPair_in0_left_no_capture cw ccw out inc b)]

/-- Two empty selection slots are a stutter for the whole dispatcher. -/
theorem runtimeRow_empty_empty :
    runtimeRow (.interior (.selection .empty)) (.interior (.selection .empty)) =
      (.interior (.selection .empty),.interior (.selection .empty)) := rfl

theorem selectionPair_empty_free_root (c : Choice) (cw : CwPort) (out : OutControl)
    (inc : InControl) :
    selectionPair (.interior (.selection .empty)) (.root c cw .free out inc) =
      (.interior (.selection .empty),
        .root (resolveResp c) cw .free out (reserveUpdate (some .free) (some .free) inc)) := by
  rw [selectionPair_open _ _ rfl (.interior .empty) (.root c cw .free) rfl
    (selectionView_root ..)]
  show (joinNode (.interior (.selection .empty)),
    joinNode (.root (resolveResp c) cw .free out
      (reserveUpdate (some .free) (some .free) inc))) = _
  cases cw <;> rfl

/-- An empty slot in front of a free incoming port is a stutter on the left:
the `K4` incidence row writes only the root. -/
theorem runtimeRow_empty_free_root (c : Choice) (cw : CwPort) (out : OutControl)
    (inc : InControl) :
    (runtimeRow (.interior (.selection .empty)) (.root c cw .free out inc)).1 =
      .interior (.selection .empty) := by
  rw [runtimeRow_def,selectionPair_empty_free_root]
  show (captureRow (.interior (.selection .empty))
    (.root (resolveResp c) cw .free out (reserveUpdate (some .free) (some .free) inc))).1 = _
  rw [captureRow_of_right_none _ _ (decodeRight_free _ _ _ _)]

/-- The closed producer of a latched root leaves the first slot of the gap it
owns empty: no new declaration is created there. -/
theorem runtimeRow_latched_left_empty (cw : CwPort) (out : OutControl) (inc : InControl) :
    (runtimeRow (.root .in0 cw .heldCandidate out inc) (.interior (.selection .empty))).2 =
      .interior (.selection .empty) := by
  rw [runtimeRow_of_in0_left]
  cases hgate : OwnerLatched (Node.root .in0 cw .heldCandidate out inc) &&
      ProducerRow (.root .in0 cw .heldCandidate out inc) (.interior (.selection .empty)) with
  | true => rw [selectionPair_frozen _ _ hgate]
  | false =>
    have hcw : cw ≠ .toSend := by
      intro hh
      subst hh
      exact Bool.noConfusion hgate
    have hrow : (row (.root .in0 cw .heldCandidate) (.interior .empty)).2 = .interior .empty := by
      simp [row,hcw]
    rw [selectionPair_open _ _ hgate _ _ (selectionView_root ..) rfl,hrow]
    rfl

/-! ## Geometry: side separation and off-gap framing -/

/-- Geometric frame valid for any local pair row, including capture tags. -/
def pairStep (R : RFrame) (pair : Node → Node → Node × Node)
    (cfg : Vtx R → Node) (e : Vtx R) : Vtx R → Node :=
  fun v => if v = e then (pair (cfg e) (cfg (rn R e))).1
    else if v = rn R e then (pair (cfg e) (cfg (rn R e))).2 else cfg v

theorem pairStep_initiator (R : RFrame) (pair : Node → Node → Node × Node)
    (cfg : Vtx R → Node) (e : Vtx R) :
    pairStep R pair cfg e e = (pair (cfg e) (cfg (rn R e))).1 := by
  simp [pairStep]

theorem pairStep_initiator' (R : RFrame) (pair : Node → Node → Node × Node)
    (cfg : Vtx R → Node) (e v : Vtx R) (h : v = e) :
    pairStep R pair cfg e v = (pair (cfg e) (cfg (rn R e))).1 := by
  simp only [pairStep,if_pos h]

theorem pairStep_responder (R : RFrame) (pair : Node → Node → Node × Node)
    (cfg : Vtx R → Node) (e v : Vtx R) (h1 : v ≠ e) (h2 : v = rn R e) :
    pairStep R pair cfg e v = (pair (cfg e) (cfg (rn R e))).2 := by
  simp only [pairStep,if_neg h1,if_pos h2]

theorem pairStep_frame (R : RFrame) (pair : Node → Node → Node × Node)
    (cfg : Vtx R → Node) (e v : Vtx R) (h1 : v ≠ e) (h2 : v ≠ rn R e) :
    pairStep R pair cfg e v = cfg v := by
  simp only [pairStep,if_neg h1,if_neg h2]

theorem other_gap_node_slots_framed (R : RFrame) (pair : Node → Node → Node × Node)
    (cfg : Vtx R → Node) (g : Fin R.m) (e : Vtx R) (hg : g ≠ e.1)
    (a : Fin R.h) (ha : 0 < a.val) : pairStep R pair cfg e (g,a) = cfg (g,a) := by
  have he : (g,a) ≠ e := fun h => hg (congrArg Prod.fst h)
  have hn : (g,a) ≠ rn R e := by
    intro h
    by_cases hp : e.2.val+1 < R.h
    · rw [rn_of_lt R e hp] at h
      exact hg (congrArg Prod.fst h)
    · rw [rn_of_last R e hp] at h
      have hz := congrArg (fun v : Vtx R => v.2.val) h
      change a.val = 0 at hz
      omega
  exact pairStep_frame R pair cfg e _ he hn

/-- The two sides of a shared root are disjoint fields: as the owner of its
clockwise gap the latched target never writes its own incoming candidate port,
its lease, or its capture outgoing control; and no edge outside gap `g` writes
any interior slot of gap `g`.  This is the exact refutation of the
busy-target-mover obstacle of `ShortGapCaptureEntry`. -/
theorem target_side_separation (R : RFrame) (cw : CwPort) (out : OutControl) (inc : InControl)
    (b : Node) (pair : Node → Node → Node × Node) (cfg : Vtx R → Node) (g : Fin R.m)
    (e : Vtx R) (hg : g ≠ e.1) :
    (∃ cw', (runtimeRow (.root .in0 cw .heldCandidate out inc) b).1 =
        .root .in0 cw' .heldCandidate out inc) ∧
      (∀ a : Fin R.h, 0 < a.val → pairStep R pair cfg e (g,a) = cfg (g,a)) :=
  ⟨runtime_target_side cw out inc b,
    fun a ha => other_gap_node_slots_framed R pair cfg g e hg a ha⟩

/-- The walk reads only the source's outgoing side. -/
def observeSource : Node → Node
  | .root c cw _ out _ => .root c cw .free out .open
  | a => a

/-- The walk reads only the target's incoming side. -/
def observeTarget : Node → Node
  | .root c _ ccw _ inc => .root c .toSend ccw .home inc
  | a => a

/-- Pull back a physical gap, including both endpoint roots. -/
def gapVertex (R : RFrame) (g : Fin R.m) (k : Fin (R.h+1)) : Vtx R :=
  if hk : k.val < R.h then (g,⟨k.val,hk⟩) else rootV R (next R g)

def observeGap (R : RFrame) (g : Fin R.m) (cfg : Vtx R → Node) : Fin (R.h+1) → Node :=
  fun k => if k.val = 0 then observeSource (cfg (rootV R g))
    else if k.val = R.h then observeTarget (cfg (rootV R (next R g)))
    else cfg (gapVertex R g k)

theorem observeGap_apply (R : RFrame) (g : Fin R.m) (cfg : Vtx R → Node) (k : Fin (R.h+1)) :
    observeGap R g cfg k =
      if k.val = 0 then observeSource (cfg (rootV R g))
      else if k.val = R.h then observeTarget (cfg (rootV R (next R g)))
      else cfg (gapVertex R g k) := rfl

/-- JOIN at either protected endpoint cannot rearm it; at an interior
site it is the identity. This also covers any parallel collection of JOINs. -/
theorem joins_observed_stutter (R : RFrame) (g : Fin R.m) (cfg : Vtx R → Node)
    (ccw : CcwPort) (cw : CwPort) (out so : OutControl) (si ti : InControl)
    (hs : cfg (rootV R g) = .root .out1 .heldCandidate ccw so si)
    (ht : cfg (rootV R (next R g)) = .root .in0 cw .heldCandidate out ti)
    (hi : ∀ a : Fin R.h, 0 < a.val → ∃ w, cfg (g,a) = .interior w) :
    observeGap R g (fun v => joinNode (cfg v)) = observeGap R g cfg := by
  funext k
  rw [observeGap_apply,observeGap_apply]
  by_cases h0 : k.val = 0
  · rw [if_pos h0,if_pos h0]
    show observeSource (joinNode (cfg (rootV R g))) = _
    rw [hs,join_source_fixed]
  · rw [if_neg h0,if_neg h0]
    by_cases hh : k.val = R.h
    · rw [if_pos hh,if_pos hh]
      show observeTarget (joinNode (cfg (rootV R (next R g)))) = _
      rw [ht,join_target_fixed]
    · rw [if_neg hh,if_neg hh]
      have hk : k.val < R.h := by have := k.isLt; omega
      obtain ⟨w,hw⟩ := hi ⟨k.val,hk⟩ (Nat.pos_of_ne_zero h0)
      have hv : gapVertex R g k = (g,(⟨k.val,hk⟩ : Fin R.h)) := dif_pos hk
      show joinNode (cfg (gapVertex R g k)) = cfg (gapVertex R g k)
      rw [hv,hw]
      rfl

/-- An edge outside g cannot have g's target as its responder. -/
theorem other_gap_not_target_responder (R : RFrame) (g : Fin R.m) (e : Vtx R)
    (hg : g ≠ e.1) : rootV R (next R g) ≠ rn R e := by
  intro h
  by_cases hp : e.2.val+1 < R.h
  · rw [rn_of_lt R e hp] at h
    have hz := congrArg (fun v : Vtx R => v.2.val) h
    change 0 = e.2.val+1 at hz
    omega
  · rw [rn_of_last R e hp] at h
    exact hg (next_inj R g e.1 (congrArg Prod.fst h))

/-- Every actual other-gap row, including raw selection, JOIN and capture,
is a stutter for the fields and slots read by this walk. No idle premise is
made on the target's outgoing selection port or on the other gap's slots. -/
theorem other_gap_walk_stutter (R : RFrame) (g : Fin R.m) (cfg : Vtx R → Node)
    (ccw : CcwPort) (cw : CwPort) (out so : OutControl) (si ti : InControl)
    (hs : cfg (rootV R g) = .root .out1 .heldCandidate ccw so si)
    (ht : cfg (rootV R (next R g)) = .root .in0 cw .heldCandidate out ti)
    (e : Vtx R) (hg : g ≠ e.1) :
    observeGap R g (pairStep R runtimeRow cfg e) = observeGap R g cfg := by
  have hsource : observeSource (pairStep R runtimeRow cfg e (rootV R g)) =
      observeSource (cfg (rootV R g)) := by
    have he : rootV R g ≠ e := fun h => hg (congrArg Prod.fst h)
    by_cases hr : rootV R g = rn R e
    · have hh : cfg (rn R e) = .root .out1 .heldCandidate ccw so si := by
        rw [← hr]; exact hs
      obtain ⟨dd,di,hd⟩ := runtime_source_side ccw so si (cfg e)
      rw [pairStep_responder R runtimeRow cfg e _ he hr,hh,hd,hs]
      rfl
    · rw [pairStep_frame R runtimeRow cfg e _ he hr]
  have htarget : observeTarget (pairStep R runtimeRow cfg e (rootV R (next R g))) =
      observeTarget (cfg (rootV R (next R g))) := by
    have hr := other_gap_not_target_responder R g e hg
    by_cases he : rootV R (next R g) = e
    · have hh : cfg e = .root .in0 cw .heldCandidate out ti := by rw [← he]; exact ht
      obtain ⟨dw,hd⟩ := runtime_target_side cw out ti (cfg (rn R e))
      rw [pairStep_initiator' R runtimeRow cfg e _ he,hh,hd,ht]
      rfl
    · rw [pairStep_frame R runtimeRow cfg e _ he hr]
  funext k
  rw [observeGap_apply,observeGap_apply]
  by_cases h0 : k.val = 0
  · rw [if_pos h0,if_pos h0]
    exact hsource
  · rw [if_neg h0,if_neg h0]
    by_cases hh : k.val = R.h
    · rw [if_pos hh,if_pos hh]
      exact htarget
    · rw [if_neg hh,if_neg hh]
      have hk : k.val < R.h := by have := k.isLt; omega
      have hv : gapVertex R g k = (g,(⟨k.val,hk⟩ : Fin R.h)) := dif_pos hk
      rw [hv]
      exact other_gap_node_slots_framed R runtimeRow cfg g e hg _ (Nat.pos_of_ne_zero h0)

/-- The ambient-clock carrier implements that same off-gap stutter. -/
theorem captureSchedStep_other_gap (R : RFrame) (g : Fin R.m) (ccw : CcwPort) (cw : CwPort)
    (cfg : CaptureConfig (walkFrame R ccw cw)) (e : Fin R.n) (hg : g ≠ (edgeVtx R e).1) :
    captureSchedStep (walkFrame R ccw cw) (walkEmbedding R g ccw cw) cfg e = cfg := by
  classical
  have hn : ¬ ∃ a : Fin (walkFrame R ccw cw).h, (walkEmbedding R g ccw cw).edgeAt a = e := by
    rintro ⟨a,ha⟩
    have hv : edgeVtx R e = (g,(a : Fin R.h)) :=
      (congrArg (edgeVtx R) ha).symm.trans (edgeVtx_encE R g a)
    exact hg (congrArg Prod.fst hv).symm
  exact dif_neg hn

/-! ## The stranded K3 endpoint is a literal frame -/

/-- The frozen-`K3` situation: the latched root `B` never sent
its own declaration, so the gap `B` owns carries no declaration and its right
endpoint `C` still has a free incoming port. -/
structure FrozenK3 (R : RFrame) (g : Fin R.m) (cfg : Vtx R → Node) : Prop where
  latched : ∃ cw out inc, cfg (rootV R (next R g)) = .root .in0 cw .heldCandidate out inc
  quiet : ∀ p : Fin R.h, 0 < p.val → cfg (next R g,p) = .interior (.selection .empty)
  free : ∃ c cw out inc, cfg (rootV R (next R (next R g))) = .root c cw .free out inc

/-- No pre-commit step of the frozen dispatcher writes the stranded right
endpoint's incoming port. -/
theorem k3_right_port_frame (R : RFrame) (g : Fin R.m) (cfg : Vtx R → Node)
    (h : FrozenK3 R g cfg) (e : Vtx R) :
    ∃ c cw out inc,
      pairStep R runtimeRow cfg e (rootV R (next R (next R g))) = .root c cw .free out inc := by
  obtain ⟨c0,cw0,out0,inc0,hC⟩ := h.free
  by_cases hi : rootV R (next R (next R g)) = e
  · rw [pairStep_initiator' R runtimeRow cfg e _ hi]
    rw [show cfg e = .root c0 cw0 .free out0 inc0 by rw [← hi]; exact hC]
    obtain ⟨c',cw',out',inc',hr⟩ := runtimeRow_initiator_keeps_ccw c0 cw0 .free out0 inc0
      (cfg (rn R e)) (by intro hh; cases hh)
    exact ⟨c',cw',out',inc',hr⟩
  · by_cases hr : rootV R (next R (next R g)) = rn R e
    · rw [pairStep_responder R runtimeRow cfg e _ hi hr]
      have hlast : ¬ (e.2.val+1 < R.h) := by
        intro hp
        rw [rn_of_lt R e hp] at hr
        have hz := congrArg (fun v : Vtx R => v.2.val) hr
        change 0 = e.2.val+1 at hz
        omega
      rw [rn_of_last R e hlast] at hr
      have hfst : next R e.1 = next R (next R g) := (congrArg Prod.fst hr).symm
      have hgap : e.1 = next R g := next_inj R e.1 (next R g) hfst
      have hpos : e.2.val+1 = R.h := by have := e.2.isLt; omega
      have hcfg : cfg e = .interior (.selection .empty) ∨
          ∃ cw1 out1 inc1, cfg e = .root .in0 cw1 .heldCandidate out1 inc1 := by
        by_cases hz : e.2.val = 0
        · obtain ⟨cw1,out1,inc1,hB⟩ := h.latched
          refine Or.inr ⟨cw1,out1,inc1,?_⟩
          rw [show e = rootV R (next R g) from Prod.ext hgap (Fin.ext hz)]
          exact hB
        · refine Or.inl ?_
          have := h.quiet e.2 (Nat.pos_of_ne_zero hz)
          rw [show (next R g,e.2) = e from Prod.ext hgap.symm rfl] at this
          exact this
      rw [show cfg (rn R e) = .root c0 cw0 .free out0 inc0 by
        rw [rn_of_last R e hlast,← hr]; exact hC]
      exact runtimeRow_keeps_free_responder (cfg e) c0 cw0 out0 inc0 hcfg
    · exact ⟨c0,cw0,out0,inc0,by rw [pairStep_frame R runtimeRow cfg e _ hi hr]; exact hC⟩

/-- Frame statement: any potential of the stranded endpoint's
incoming port is unchanged by every pre-commit step, so its local debt
contribution cannot increase and no denial has to be fabricated for it. -/
theorem k3_port_stutter (R : RFrame) (g : Fin R.m) (cfg : Vtx R → Node)
    (h : FrozenK3 R g cfg) (e : Vtx R) (Phi : Option CcwPort → Nat) :
    Phi ((pairStep R runtimeRow cfg e (rootV R (next R (next R g)))).ccwPort) =
      Phi ((cfg (rootV R (next R (next R g)))).ccwPort) := by
  obtain ⟨c1,cw1,out1,inc1,h1⟩ := k3_right_port_frame R g cfg h e
  obtain ⟨c0,cw0,out0,inc0,h0⟩ := h.free
  rw [h1,h0]
  rfl

/-- The frozen-`K3` shape is preserved by every pre-commit step of the frozen
dispatcher, so the port frame above is a genuine invariant and not a
single-step accident.  The latched root keeps its candidate incoming port and
its closed producer; the gap it owns stays free of declarations. -/
theorem frozenK3_step (R : RFrame) (g : Fin R.m) (cfg : Vtx R → Node)
    (h : FrozenK3 R g cfg) (e : Vtx R) : FrozenK3 R g (pairStep R runtimeRow cfg e) := by
  obtain ⟨cwB,outB,incB,hB⟩ := h.latched
  refine ⟨?_,?_,k3_right_port_frame R g cfg h e⟩
  · by_cases hi : rootV R (next R g) = e
    · rw [pairStep_initiator' R runtimeRow cfg e _ hi,
        show cfg e = .root .in0 cwB .heldCandidate outB incB by rw [← hi]; exact hB]
      obtain ⟨cw',hr⟩ := runtime_target_side cwB outB incB (cfg (rn R e))
      exact ⟨cw',outB,incB,hr⟩
    · by_cases hr : rootV R (next R g) = rn R e
      · rw [pairStep_responder R runtimeRow cfg e _ hi hr,
          show cfg (rn R e) = .root .in0 cwB .heldCandidate outB incB by rw [← hr]; exact hB]
        exact runtimeRow_latched_responder (cfg e) cwB outB incB
      · exact ⟨cwB,outB,incB,by rw [pairStep_frame R runtimeRow cfg e _ hi hr]; exact hB⟩
  · intro p hp
    have hv0 : cfg (next R g,p) = .interior (.selection .empty) := h.quiet p hp
    by_cases hi : ((next R g,p) : Vtx R) = e
    · rw [pairStep_initiator' R runtimeRow cfg e _ hi,
        show cfg e = .interior (.selection .empty) by rw [← hi]; exact hv0]
      by_cases hlt : p.val+1 < R.h
      · rw [show rn R e = ((next R g,(⟨p.val+1,hlt⟩ : Fin R.h)) : Vtx R) by
          rw [← hi]; exact rn_of_lt R _ hlt, h.quiet ⟨p.val+1,hlt⟩ (by simp)]
        exact congrArg Prod.fst runtimeRow_empty_empty
      · obtain ⟨c0,cw0,out0,inc0,hC⟩ := h.free
        rw [show rn R e = rootV R (next R (next R g)) by
          rw [← hi]; exact rn_of_last R _ hlt, hC]
        exact runtimeRow_empty_free_root c0 cw0 out0 inc0
    · by_cases hr : ((next R g,p) : Vtx R) = rn R e
      · rw [pairStep_responder R runtimeRow cfg e _ hi hr,
          show cfg (rn R e) = .interior (.selection .empty) by rw [← hr]; exact hv0]
        have hlt : e.2.val+1 < R.h := by
          by_cases hc : e.2.val+1 < R.h
          · exact hc
          · exfalso
            rw [rn_of_last R e hc] at hr
            have hz := congrArg (fun v : Vtx R => v.2.val) hr
            change p.val = 0 at hz
            omega
        have hr' := hr
        rw [rn_of_lt R e hlt] at hr'
        have hgap : e.1 = next R g := (congrArg Prod.fst hr').symm
        by_cases hz : e.2.val = 0
        · rw [show cfg e = .root .in0 cwB .heldCandidate outB incB by
            rw [show e = rootV R (next R g) from Prod.ext hgap (Fin.ext hz)]
            exact hB]
          exact runtimeRow_latched_left_empty cwB outB incB
        · rw [show cfg e = .interior (.selection .empty) by
            have hq := h.quiet e.2 (Nat.pos_of_ne_zero hz)
            rw [show ((next R g,e.2) : Vtx R) = e from Prod.ext hgap.symm rfl] at hq
            exact hq]
          exact congrArg Prod.snd runtimeRow_empty_empty
      · rw [pairStep_frame R runtimeRow cfg e _ hi hr]
        exact hv0

/-! ### Non-vacuity, and the gate is load-bearing -/

def frozenExampleFrame : RFrame := ⟨3,2,by decide,by decide,.out1,Or.inl rfl⟩

def frozenExampleGap : Fin frozenExampleFrame.m := ⟨0,by decide⟩

/-- Gap `0` is latched: the shared root between gap `0` and gap `1` is
`in0`/`heldCandidate` with a live reservation and an unsent declaration, gap
`1` is empty, and the right endpoint of gap `1` still has a free incoming
port.  This is the exact stranded-`K3` branch. -/
def frozenExampleCfg : Vtx frozenExampleFrame → Node :=
  fun v =>
    if v.2.val = 0 then
      (if v.1.val = 1 then .root .in0 .toSend .heldCandidate .home .reserved
        else .root .out1 .heldCandidate .free .home .open)
    else .interior (.selection .empty)

theorem frozenExample_frozenK3 :
    FrozenK3 frozenExampleFrame frozenExampleGap frozenExampleCfg := by
  refine ⟨⟨.toSend,.home,.reserved,rfl⟩,?_,⟨.out1,.heldCandidate,.home,.open,rfl⟩⟩
  intro p hp
  have h2 : p.val < 2 := p.isLt
  have hv : ¬ p.val = 0 := by omega
  simp [frozenExampleCfg,hv]

/-- Without the gate the very same latched root would launch on the gap it
owns, and in the fused length-one row it would write a fabricated denial into
the right endpoint's incoming port.  With the gate the pair stutters. -/
theorem freeze_is_load_bearing (c : Choice) (cw' : CwPort) :
    (row (.root c .toSend .heldCandidate) (.interior .empty)).2
        = .interior (.decl (resolveInit c)) ∧
      ((row (.root .in0 .toSend .heldCandidate) (.root .out1 cw' .free)).2).ccwPort
        = some .heldDenial ∧
      selectionPair (.root c .toSend .heldCandidate .home .reserved)
          (.interior (.selection .empty))
        = (.root c .toSend .heldCandidate .home .reserved,.interior (.selection .empty)) ∧
      selectionPair (.root .in0 .toSend .heldCandidate .home .reserved)
          (.root .out1 cw' .free .home .open)
        = (.root .in0 .toSend .heldCandidate .home .reserved,
            .root .out1 cw' .free .home .open) :=
  ⟨rfl,rfl,rfl,rfl⟩

/-! ## Neighbour skew needs no exception -/

/-- The latch does not require a `neighborSkew` exception.  The global
clause holds at the latched gap, the latch survives every selection step, and
the clause survives with it. -/
theorem latched_preserves_neighborSkew (R : RFrame) (s : GhostRing2 R) (hs : Lineage2 R s)
    (g : Fin R.m) (hc : BothCandidate R s g) :
    ShortGapCurrentCohort.NeighborSkew R (physical2 R s) ∧
      ∀ e : Vtx R, BothCandidate R (ghostStep2 R s e) g ∧
        ShortGapCurrentCohort.NeighborSkew R (physical2 R (ghostStep2 R s e)) :=
  ⟨neighborSkew_of_lineage2 R s hs,
    fun e => ⟨ShortGapCaptureEntry.bothCandidate_stable R s hs g hc e,
      neighborSkew_of_lineage2 R _ (lineage2_step R s hs e)⟩⟩

/-! ## Entry from the actual clean selection producer -/

theorem reachable_lineage (R : RFrame) (s : ReservationState R) (h : SelectionReachable R s) :
    Lineage2 R s.selection := by
  induction h with
  | start => exact lineage2_start R
  | step h e ih => exact lineage2_step R _ ih e

/-- `CaptureReady` is *not* strengthened by a mover-idle clause.  The
target-side reservation and the unchanged `ShortGapCaptureEntry.CaptureReady`
are both available from the latch alone, even when the target's own gap-owner
epoch on its clockwise gap is live — which is exactly the configuration of
`ShortGapCaptureEntry.local_launch_with_busy_target_mover`. -/
theorem reservation_needs_no_mover_idle (R : RFrame) (s : ReservationState R)
    (h : SelectionReachable R s) (g : Fin R.m) (hc : BothCandidate R s.selection g)
    (_hbusy : Live (s.selection.epoch (next R g)).cur) :
    s.incoming (next R g) = .reserved ∧
      ShortGapCaptureEntry.CaptureReady R g ⟨s.selection,fun _ => .freeHome⟩ :=
  ⟨target_reserved_of_bothCandidate R s h g hc,
    ShortGapCaptureEntry.captureReady_of_bothCandidate R _ (reachable_lineage R s h)
      (fun _ => rfl) g hc⟩

/-- Clean capture controls are added to the existing selection configuration.
The target's cw selection task is preserved verbatim, including waiting. -/
def selectionLift (R : RFrame) (s : ReservationState R) : Vtx R → Node :=
  fun v => match s.selection.cfg v with
    | .root c cw ccw => .root c cw ccw .home (s.incoming v.1)
    | .interior t => .interior (.selection t)

/-- No new clean-gap hypothesis is required: the retained-lineage invariant
supplies it, and the atomic comparison update supplies the reservation. -/
theorem ready_selection_shape (R : RFrame) (s : ReservationState R)
    (hr : SelectionReachable R s) (g : Fin R.m) (hc : BothCandidate R s.selection g) :
    ∃ ccw cw,
      selectionLift R s (rootV R g) = .root .out1 .heldCandidate ccw .home (s.incoming g) ∧
      selectionLift R s (rootV R (next R g)) = .root .in0 cw .heldCandidate .home .reserved ∧
      ∀ a : Fin R.h, 0 < a.val → selectionLift R s (g,a) = .interior (.selection .empty) := by
  have hs := reachable_lineage R s hr
  have hl := ShortGapCaptureEntry.owner_candidate_lock R s.selection hs g hc.1
  obtain ⟨cw,ccw,ha⟩ := hl.root_choices.1
  obtain ⟨dw,dd,hb⟩ := hl.root_choices.2
  have hp := hc.1
  have hq := hc.2
  rw [ha] at hp
  rw [hb] at hq
  have hp' : cw = .heldCandidate := Option.some.inj hp
  have hq' : dd = .heldCandidate := Option.some.inj hq
  subst cw; subst dd
  refine ⟨ccw,dw,?_,?_,?_⟩
  · simp [selectionLift,ha,rootV]
  · simp [selectionLift,hb,rootV,target_reserved_of_bothCandidate R s hr g hc]
  · intro a hp
    have hi := ShortGapCaptureEntry.bothCandidate_empty R s.selection hs g hc a hp
    change s.selection.cfg (g,a) = .interior .empty at hi
    simp [selectionLift,hi]

/-- The service start is the actual selected gap, with no copied token,
reset selection field or assumed simulation law. Capture outgoing controls
are clean at this entry; incoming reservation comes from the producer. -/
theorem ready_encodes_start (R : RFrame) (s : ReservationState R)
    (hr : SelectionReachable R s) (g : Fin R.m) (hc : BothCandidate R s.selection g) :
    ∃ ccw cw, (fun k : Fin (R.h+1) => selectionLift R s (gapVertex R g k)) =
      encodeConfig ⟨s.incoming g,.home⟩ (configOf (walkFrame R ccw cw) .prelaunch) := by
  obtain ⟨ccw,cw,hs,ht,hi⟩ := ready_selection_shape R s hr g hc
  refine ⟨ccw,cw,?_⟩
  funext k
  have hpos := R.hh
  show selectionLift R s (gapVertex R g k) =
    encodeAgent ⟨s.incoming g,.home⟩ (siteOf (walkFrame R ccw cw) .prelaunch k.val)
  by_cases h0 : k.val = 0
  · have hv : gapVertex R g k = rootV R g := by
      have hk : k.val < R.h := by omega
      rw [show gapVertex R g k = (g,(⟨k.val,hk⟩ : Fin R.h)) from dif_pos hk]
      exact Prod.ext rfl (Fin.ext h0)
    rw [hv,hs]
    show _ = encodeAgent ⟨s.incoming g,.home⟩
      (if k.val = 0 then .root .out1 CwPort.toSend ccw
        else if k.val = R.h then .root .in0 cw CcwPort.free else .interior Slot.empty)
    rw [if_pos h0]
    rfl
  · by_cases hh : k.val = R.h
    · have hv : gapVertex R g k = rootV R (next R g) := dif_neg (by omega)
      rw [hv,ht]
      show _ = encodeAgent ⟨s.incoming g,.home⟩
        (if k.val = 0 then .root .out1 CwPort.toSend ccw
          else if k.val = R.h then .root .in0 cw CcwPort.free else .interior Slot.empty)
      rw [if_neg h0,if_pos hh]
      rfl
    · have hk : k.val < R.h := by have := k.isLt; omega
      have hv : gapVertex R g k = (g,(⟨k.val,hk⟩ : Fin R.h)) := dif_pos hk
      rw [hv,hi _ (Nat.pos_of_ne_zero h0)]
      show _ = encodeAgent ⟨s.incoming g,.home⟩
        (if k.val = 0 then .root .out1 CwPort.toSend ccw
          else if k.val = R.h then .root .in0 cw CcwPort.free else .interior Slot.empty)
      rw [if_neg h0,if_neg hh]
      rfl

#print axioms target_reserved_of_bothCandidate
#print axioms target_side_separation
#print axioms captureRow_encodes_row
#print axioms proposalWalk_bellman
#print axioms proposalWalk_start_potential
#print axioms proposalWalk_success_sound
#print axioms semantic_proposal_handoff
#print axioms semantic_final_deposit_extends
#print axioms latch_step_closes_owner
#print axioms latched_no_L1
#print axioms latched_no_P1
#print axioms latched_return_retires
#print axioms latched_owner_cannot_win
#print axioms latched_owner_producer_closed
#print axioms latched_blocks_join
#print axioms runtimeRow_keeps_free_responder
#print axioms freeze_is_load_bearing
#print axioms latched_preserves_neighborSkew
#print axioms k3_right_port_frame
#print axioms k3_port_stutter
#print axioms frozenK3_step
#print axioms frozenExample_frozenK3
#print axioms other_gap_walk_stutter
#print axioms joins_observed_stutter
#print axioms selection_disabled_during_capture
#print axioms runtimeRow_encodes_row
#print axioms captureSchedStep_other_gap
#print axioms reservation_needs_no_mover_idle
#print axioms ready_encodes_start

end ShortGapCaptureReservation

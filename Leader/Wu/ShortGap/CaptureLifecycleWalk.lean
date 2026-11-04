import Leader.Wu.ShortGap.CaptureCommitRows

/-!
# The whole capture lifecycle on one gap as a stopped walk

New file: `Leader/Wu/ShortGap/CaptureLifecycleWalk.lean`.

`Leader/Wu/ShortGap/CaptureReservation.lean` gives the literal proposal/FINAL rows
and their one-gap walk; `Leader/Wu/ShortGap/CaptureCommitRows.lean` extends the
same physical pair row to the post-FINAL commit lane.  This file runs the
*entire* clean lifecycle of one selected short gap as a single stopped process
on the ambient `Fin n` scheduler:

  `proposalAt j | finalAt j | protectedWait | commitAt j | committedAt j t |
   postcommit ackDone tgtDone`,

success = clean, and no failure node at all.

Four things are proved about it.

* Every scheduler edge acts on the encoded gap as the *literal* imported pair
  row: `commitRow` on both endpoints of that edge, framing every other site
  (`lifecycleStep_encodes_rows`), and on the capture phases the raw components
  are the imported `captureRow` / `captureGapStep` / `captureSchedStep`
  (`lifecycleStep_encodes_captureRows`).  The `h = 1` fusions are the imported
  `direct_row` and `commit_direct` rows.

* The exact useful-firing debt of the whole lifecycle is `4 * h`:

  ```
  proposal launch / forward / acceptance   h
  FINAL return / deposit                   h - 1
  protected COMMIT launch                  1
  COMMIT forward / acceptance              h - 1
  COMMITTED return / deposit               h - 1
  two independent postcommit discharges    2
  ```

  i.e. the four gap crossings counted by `cleanCommitSchedule_crossings`, plus
  the protected launch, plus the two discharges.  For `h = 1` each crossing
  group fuses into its imported direct row and the total is `1 + 1 + 2 = 4`,
  the same `4 * h`.  This gives a scale-one `NatBellmanSuperSolution` for the
  potential `n * lifeDebt`, with exact start potential `n * (4 * h)`.

* The three row-level safety theorems of the commit file transport verbatim to
  every scheduler edge of the walk.

* The literal walk refines the semantic macro lifecycle of
  `Leader/Wu/ShortGap/CaptureLifecycle.lean`: every scheduler edge from every state
  is a (possibly empty) semantic `Trace`, and the canonical `4 * h`-firing run
  emits exactly `cleanCommitSchedule`.

Two ambient controls are constants, not free parameters.  The source root's
*incoming* capture lease is `open` and the captured target's *outgoing* capture
control is `home`: these are the two opposite-side controls, and they are the
frozen clean-lane values (the candidate-owned freeze of the reservation file
closes the target's owner producer, and the source is not itself a reserved
target).  Every literal row quoted below is nevertheless the imported row with
those two controls arbitrary; only the wrapper's seed observation needs them
concrete.

Scope.  This is one selected gap with a clean lane and a frozen owner.  No
arbitrary-residue cleanup, no fairness, no global reachability, and no
composition with the selection runtime is claimed here.
-/

namespace ShortGapCaptureLifecycleWalk

open ShortGapLiteralGapRows ShortGapCaptureReservation ShortGapCaptureCommitRows
open FiniteUniformStoppingTree

set_option autoImplicit false

/-! ## The finite clean-lane alphabet and its literal interpretation -/

/-- Every site state occurring in one clean capture lifecycle. -/
inductive Tag where
  | sHome | sProposal | sProtected | sCommitting | sReceived | sClean
  | tReserved | tHeld | tCommitted | tClean
  | empty | proposal | finalBack | commit | committedBack
  deriving DecidableEq

/-- The literal `CNode` denoted by a tag.  Nothing here is new state: the raw
component is an imported `ShortGapCaptureReservation.Node` and the four wrapper
fields are the imported commit-lane fields. -/
def render (F : Frame) : Tag → CNode
  | .sHome =>
      ⟨.root .out1 .heldCandidate F.ccw0 .home .open,
        true, .capturing, .unreserved, .none⟩
  | .sProposal =>
      ⟨.root .out1 .heldCandidate F.ccw0 .proposal .open,
        true, .capturing, .unreserved, .none⟩
  | .sProtected => ownerNode F.ccw0 .open .protectedFinal .unreserved true
  | .sCommitting => ownerNode F.ccw0 .open .committing .unreserved true
  | .sReceived => ownerNode F.ccw0 .open .committedReceived .unreserved true
  | .sClean => ownerNode F.ccw0 .open .clean .unreserved true
  | .tReserved =>
      ⟨.root .in0 F.cw0 .heldCandidate .home .reserved,
        true, .capturing, .unreserved, .none⟩
  | .tHeld => targetNode F.cw0 .home .capturing .reserved true
  | .tCommitted => targetNode F.cw0 .home .capturing .committed false
  | .tClean => targetNode F.cw0 .home .capturing .clean false
  | .empty => slotNode .none
  | .proposal => ⟨.interior (.capture .proposal), false, .capturing, .unreserved, .none⟩
  | .finalBack => ⟨.interior (.capture .finalBack), false, .capturing, .unreserved, .none⟩
  | .commit => slotNode .commit
  | .committedBack => slotNode .committedBack

/-- The pairs that actually occur on one clean lane (or on the target's
outgoing service edge).  Nothing outside this table is claimed. -/
def pairAllowed : Tag → Tag → Bool
  | .sHome, .empty | .sHome, .tReserved => true
  | .sProposal, .empty | .sProposal, .proposal | .sProposal, .finalBack => true
  | .sProtected, .empty | .sProtected, .tHeld => true
  | .sCommitting, .empty | .sCommitting, .commit
  | .sCommitting, .committedBack => true
  | .sReceived, .empty | .sReceived, .tCommitted | .sReceived, .tClean => true
  | .sClean, .empty | .sClean, .tCommitted | .sClean, .tClean => true
  | .empty, .empty | .empty, .proposal | .empty, .finalBack
  | .empty, .commit | .empty, .committedBack
  | .empty, .tReserved | .empty, .tHeld
  | .empty, .tCommitted | .empty, .tClean => true
  | .proposal, .empty | .proposal, .tReserved => true
  | .finalBack, .empty | .finalBack, .tHeld => true
  | .commit, .empty | .commit, .tHeld => true
  | .committedBack, .empty | .committedBack, .tCommitted
  | .committedBack, .tClean => true
  | .tReserved, .empty | .tHeld, .empty
  | .tCommitted, .empty | .tClean, .empty => true
  | _, _ => false

/-- The finite tag-level row.  It is *checked* against the imported total
dispatcher `commitRow` in `tagRow_literal` below; it is not a new dispatcher. -/
def tagRow : Tag → Tag → Tag × Tag
  | .sReceived, b => (.sClean, b)
  | .tCommitted, b => (.tClean, b)
  | .sHome, .empty => (.sProposal, .proposal)
  | .proposal, .empty => (.empty, .proposal)
  | .proposal, .tReserved => (.finalBack, .tHeld)
  | .empty, .finalBack => (.finalBack, .empty)
  | .sProposal, .finalBack => (.sProtected, .empty)
  | .sHome, .tReserved => (.sProtected, .tHeld)
  | .sProtected, .empty => (.sCommitting, .commit)
  | .commit, .empty => (.empty, .commit)
  | .commit, .tHeld => (.committedBack, .tCommitted)
  | .empty, .committedBack => (.committedBack, .empty)
  | .sCommitting, .committedBack => (.sReceived, .empty)
  | .sProtected, .tHeld => (.sReceived, .tCommitted)
  | a, b => (a, b)

def isSlotTag : Tag → Bool
  | .empty | .proposal | .finalBack | .commit | .committedBack => true
  | _ => false

def isTargetTag : Tag → Bool
  | .tReserved | .tHeld | .tCommitted | .tClean => true
  | _ => false

/-- Tags whose literal row is still the *pure capture* row of the imported
reservation file, with no commit-lane field in play. -/
def isCaptureTag : Tag → Bool
  | .sHome | .sProposal | .tReserved | .tHeld
  | .empty | .proposal | .finalBack => true
  | _ => false

/-! ### Guard bookkeeping for the imported total dispatcher

`commitRow` is a nine-way guarded dispatch.  Rather than unfolding it by
`simp`, each tag pair below discharges the guards it fails and then quotes the
imported row theorem for the guard it meets. -/

private theorem idle_of_guards (a b : CNode)
    (h1 : ¬ SourceAck a) (h2 : ¬ TargetCleanup a) (h3 : ¬ Legacy a b)
    (h4 : ¬ Launch a b) (h5 : ¬ Forward a b) (h6 : ¬ AtTarget a b)
    (h7 : ¬ Backward a b) (h8 : ¬ Deposit a b) (h9 : ¬ Direct a b) :
    commitRow a b = (a, b) := by
  simp only [commitRow, run, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4,
    dif_neg h5, dif_neg h6, dif_neg h7, dif_neg h8, dif_neg h9]

private theorem capture_of_guards (a b : CNode)
    (h1 : ¬ SourceAck a) (h2 : ¬ TargetCleanup a) (h3 : Legacy a b) :
    commitRow a b =
      (liftCapture a (captureRow a.raw b.raw).1,
       liftCapture b (captureRow a.raw b.raw).2) := by
  simp only [commitRow, run, dif_neg h1, dif_neg h2, dif_pos h3]

private theorem rawOwner_ne {a : CNode} (h : rawOwner a.raw = false) :
    rawOwner a.raw ≠ true := by
  rw [h]
  intro hb
  exact Bool.noConfusion hb

private theorem sourceAck_false_owner {a : CNode} (h : rawOwner a.raw = false) :
    ¬ SourceAck a := fun hh => rawOwner_ne h hh.1.1

private theorem launch_false_owner {a : CNode} (b : CNode)
    (h : rawOwner a.raw = false) : ¬ Launch a b := fun hh => rawOwner_ne h hh.1.1

private theorem deposit_false_owner {a : CNode} (b : CNode)
    (h : rawOwner a.raw = false) : ¬ Deposit a b := fun hh => rawOwner_ne h hh.1.1

private theorem direct_false_owner {a : CNode} (b : CNode)
    (h : rawOwner a.raw = false) : ¬ Direct a b := fun hh => rawOwner_ne h hh.1.1

private theorem target_rule_false {a : CNode} (h : rawTarget a.raw = false) :
    ¬ TargetCleanup a := by
  intro hh
  have hb : rawTarget a.raw = true := hh.1.1
  rw [h] at hb
  exact Bool.noConfusion hb

private theorem cleanup_rule_false {a : CNode} (h : a.incoming ≠ CommitIn.committed) :
    ¬ TargetCleanup a := fun hh => h hh.2.1

private theorem raw_rules_false {a : CNode} (h : a.raw ≠ emptyRaw) (b : CNode) :
    ¬ Forward a b ∧ ¬ AtTarget a b ∧ ¬ Backward a b :=
  ⟨fun hh => h hh.1.1, fun hh => h hh.1.1, fun hh => h hh.1.1⟩

private theorem commit_carrier_rules_false {a : CNode}
    (h : a.carrier ≠ CommitCarrier.commit) (b : CNode) :
    ¬ Forward a b ∧ ¬ AtTarget a b :=
  ⟨fun hh => h hh.1.2, fun hh => h hh.1.2⟩

private theorem legacy_of_row_id {a b : CNode}
    (h : captureRow a.raw b.raw = (a.raw, b.raw)) : ¬ Legacy a b :=
  fun hh => hh.2.2.2.2 h

private theorem legacy_of_left_view {a b : CNode} (h : a.outgoing ≠ seedOut a.raw) :
    ¬ Legacy a b := fun hh => h hh.1.1

private theorem legacy_of_right_view {a b : CNode} (h : b.incoming ≠ seedIn b.raw) :
    ¬ Legacy a b := fun hh => h hh.2.1.2

private theorem legacy_of_left_carrier {a b : CNode}
    (h : a.carrier ≠ CommitCarrier.none) : ¬ Legacy a b := fun hh => h hh.2.2.1

private theorem legacy_of_right_carrier {a b : CNode}
    (h : b.carrier ≠ CommitCarrier.none) : ¬ Legacy a b := fun hh => h hh.2.2.2.1

private theorem sourceAck_false {a : CNode}
    (h : a.outgoing ≠ CommitCtl.committedReceived) : ¬ SourceAck a := fun hh => h hh.2

private theorem launch_false {a b : CNode}
    (h : a.outgoing ≠ CommitCtl.protectedFinal) : ¬ Launch a b := fun hh => h hh.2.1

private theorem direct_false {a b : CNode}
    (h : a.outgoing ≠ CommitCtl.protectedFinal) : ¬ Direct a b := fun hh => h hh.2.1

private theorem deposit_false {a b : CNode}
    (h : a.outgoing ≠ CommitCtl.committing) : ¬ Deposit a b := fun hh => h hh.2.1

private theorem deposit_false' {a b : CNode} (h : ¬ BackSlot b) :
    ¬ Deposit a b := fun hh => h hh.2.2

private theorem backward_false {a b : CNode}
    (h : a.carrier ≠ CommitCarrier.none) : ¬ Backward a b := fun hh => h hh.1.2

private theorem backward_false' {a b : CNode} (h : ¬ BackSlot b) :
    ¬ Backward a b := fun hh => h hh.2

private theorem not_backSlot {b : CNode}
    (h : b.carrier ≠ CommitCarrier.committedBack) : ¬ BackSlot b := fun hh => h hh.2

private theorem root_ne_out {ch ch' : Choice} {cw cw' : CwPort} {ccw ccw' : CcwPort}
    {o o' : OutControl} {i i' : InControl} (h : o ≠ o') :
    Node.root ch cw ccw o i ≠ Node.root ch' cw' ccw' o' i' := by
  intro hh
  injection hh with _ _ _ h4 _
  exact h h4

private theorem interior_ne {w w' : Wire} (h : w ≠ w') :
    Node.interior w ≠ Node.interior w' := by
  intro hh
  injection hh with h1
  exact h h1

private theorem pair_ne_of_fst {X Y : Type} {x y : X} {u v : Y} (h : x ≠ y) :
    ((x, u) : X × Y) ≠ (y, v) := fun hh => h (congrArg Prod.fst hh)

/-- Left endpoints whose raw state does not decode as a capture initiator, are
not owners, are not live cleanup targets and are not slots: inert against every
right neighbour. -/
private theorem idle_undecodable_left (a b : CNode)
    (hd : decodeLeft a.raw = none) (ho : rawOwner a.raw = false)
    (ht : ¬ TargetCleanup a) (he : a.raw ≠ emptyRaw) :
    commitRow a b = (a, b) := by
  obtain ⟨h5, h6, h7⟩ := raw_rules_false he b
  exact idle_of_guards a b (sourceAck_false_owner ho) ht
    (legacy_of_row_id (captureRow_of_left_none a.raw b.raw hd))
    (launch_false_owner b ho) h5 h6 h7 (deposit_false_owner b ho)
    (direct_false_owner b ho)

/-! ### The literal row of every clean-lane pair

Each equation below is the imported `commitRow` on the two rendered sites.
The capture-lane rows quote `ShortGapCaptureReservation`; the commit-lane rows
quote `ShortGapCaptureCommitRows`, including both `h = 1` direct rows. -/

private theorem lit_sHome_empty (F : Frame) :
    commitRow (render F .sHome) (render F .empty) =
      (render F .sProposal, render F .proposal) := by
  have hcap : captureRow (render F .sHome).raw (render F .empty).raw =
      ((render F .sProposal).raw, (render F .proposal).raw) :=
    launch_row F.ccw0 .open
  have h1 : ¬ SourceAck (render F .sHome) :=
    sourceAck_false (by intro h; exact CommitCtl.noConfusion h)
  have h2 : ¬ TargetCleanup (render F .sHome) := target_rule_false rfl
  have h3 : Legacy (render F .sHome) (render F .empty) := by
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ?_⟩
    rw [hcap]
    exact pair_ne_of_fst (root_ne_out (by intro h; exact OutControl.noConfusion h))
  rw [capture_of_guards _ _ h1 h2 h3, hcap]
  rfl

/-- `h = 1`: the imported fused capture row. -/
private theorem lit_sHome_tReserved (F : Frame) :
    commitRow (render F .sHome) (render F .tReserved) =
      (render F .sProtected, render F .tHeld) := by
  have hcap : captureRow (render F .sHome).raw (render F .tReserved).raw =
      ((render F .sProtected).raw, (render F .tHeld).raw) :=
    direct_row F.ccw0 F.cw0 .open .home
  have h1 : ¬ SourceAck (render F .sHome) :=
    sourceAck_false (by intro h; exact CommitCtl.noConfusion h)
  have h2 : ¬ TargetCleanup (render F .sHome) := target_rule_false rfl
  have h3 : Legacy (render F .sHome) (render F .tReserved) := by
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ?_⟩
    rw [hcap]
    exact pair_ne_of_fst (root_ne_out (by intro h; exact OutControl.noConfusion h))
  rw [capture_of_guards _ _ h1 h2 h3, hcap]
  rfl

private theorem lit_proposal_empty (F : Frame) :
    commitRow (render F .proposal) (render F .empty) =
      (render F .empty, render F .proposal) := by
  have hcap : captureRow (render F .proposal).raw (render F .empty).raw =
      ((render F .empty).raw, (render F .proposal).raw) := proposal_forward_row
  have h1 : ¬ SourceAck (render F .proposal) := sourceAck_false_owner rfl
  have h2 : ¬ TargetCleanup (render F .proposal) := target_rule_false rfl
  have h3 : Legacy (render F .proposal) (render F .empty) := by
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ?_⟩
    rw [hcap]
    exact pair_ne_of_fst (interior_ne (by intro h; exact Wire.noConfusion h))
  rw [capture_of_guards _ _ h1 h2 h3, hcap]
  rfl

private theorem lit_proposal_tReserved (F : Frame) :
    commitRow (render F .proposal) (render F .tReserved) =
      (render F .finalBack, render F .tHeld) := by
  have hcap : captureRow (render F .proposal).raw (render F .tReserved).raw =
      ((render F .finalBack).raw, (render F .tHeld).raw) := TGT_row F.cw0 .home
  have h1 : ¬ SourceAck (render F .proposal) := sourceAck_false_owner rfl
  have h2 : ¬ TargetCleanup (render F .proposal) := target_rule_false rfl
  have h3 : Legacy (render F .proposal) (render F .tReserved) := by
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ?_⟩
    rw [hcap]
    refine pair_ne_of_fst (interior_ne ?_)
    intro h
    injection h with h'
    exact CaptureMessage.noConfusion h'
  rw [capture_of_guards _ _ h1 h2 h3, hcap]
  rfl

private theorem lit_empty_finalBack (F : Frame) :
    commitRow (render F .empty) (render F .finalBack) =
      (render F .finalBack, render F .empty) := by
  have hcap : captureRow (render F .empty).raw (render F .finalBack).raw =
      ((render F .finalBack).raw, (render F .empty).raw) := FINAL_backward_row
  have h1 : ¬ SourceAck (render F .empty) := sourceAck_false_owner rfl
  have h2 : ¬ TargetCleanup (render F .empty) := target_rule_false rfl
  have h3 : Legacy (render F .empty) (render F .finalBack) := by
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ?_⟩
    rw [hcap]
    exact pair_ne_of_fst (interior_ne (by intro h; exact Wire.noConfusion h))
  rw [capture_of_guards _ _ h1 h2 h3, hcap]
  rfl

private theorem lit_sProposal_finalBack (F : Frame) :
    commitRow (render F .sProposal) (render F .finalBack) =
      (render F .sProtected, render F .empty) := by
  have hcap : captureRow (render F .sProposal).raw (render F .finalBack).raw =
      ((render F .sProtected).raw, (render F .empty).raw) :=
    FINAL_deposit_row F.ccw0 .open
  have h1 : ¬ SourceAck (render F .sProposal) :=
    sourceAck_false (by intro h; exact CommitCtl.noConfusion h)
  have h2 : ¬ TargetCleanup (render F .sProposal) := target_rule_false rfl
  have h3 : Legacy (render F .sProposal) (render F .finalBack) := by
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, ?_⟩
    rw [hcap]
    exact pair_ne_of_fst (root_ne_out (by intro h; exact OutControl.noConfusion h))
  rw [capture_of_guards _ _ h1 h2 h3, hcap]
  rfl

private theorem lit_sProtected_empty (F : Frame) :
    commitRow (render F .sProtected) (render F .empty) =
      (render F .sCommitting, render F .commit) :=
  commit_launch F.ccw0 .open .unreserved true

/-- `h = 1`: the imported fused commit row. -/
private theorem lit_sProtected_tHeld (F : Frame) :
    commitRow (render F .sProtected) (render F .tHeld) =
      (render F .sReceived, render F .tCommitted) :=
  commit_direct F.ccw0 .open .unreserved true F.cw0 .home .capturing

private theorem lit_commit_empty (F : Frame) :
    commitRow (render F .commit) (render F .empty) =
      (render F .empty, render F .commit) :=
  commit_forward

private theorem lit_commit_tHeld (F : Frame) :
    commitRow (render F .commit) (render F .tHeld) =
      (render F .committedBack, render F .tCommitted) :=
  commit_at_target F.cw0 .home .capturing

private theorem lit_empty_committedBack (F : Frame) :
    commitRow (render F .empty) (render F .committedBack) =
      (render F .committedBack, render F .empty) :=
  committed_backward

private theorem lit_sCommitting_committedBack (F : Frame) :
    commitRow (render F .sCommitting) (render F .committedBack) =
      (render F .sReceived, render F .empty) :=
  committed_deposit F.ccw0 .open .unreserved true

/-- The source receipt discharge frames its neighbour completely. -/
private theorem lit_sReceived_any (F : Frame) (b : CNode) :
    commitRow (render F .sReceived) b = (render F .sClean, b) :=
  source_ack _ b ⟨⟨rfl, rfl⟩, rfl⟩

/-- The target residue discharge frames its neighbour completely. -/
private theorem lit_tCommitted_any (F : Frame) (b : CNode) :
    commitRow (render F .tCommitted) b = (render F .tClean, b) :=
  target_cleanup _ b ⟨⟨rfl, rfl⟩, rfl, rfl⟩

private theorem lit_tReserved_any (F : Frame) (b : CNode) :
    commitRow (render F .tReserved) b = (render F .tReserved, b) :=
  idle_undecodable_left _ b rfl rfl (target_rule_false rfl)
    (by intro h; exact Node.noConfusion h)

private theorem lit_tHeld_any (F : Frame) (b : CNode) :
    commitRow (render F .tHeld) b = (render F .tHeld, b) :=
  idle_undecodable_left _ b rfl rfl
    (cleanup_rule_false (by intro h; exact CommitIn.noConfusion h))
    (by intro h; exact Node.noConfusion h)

private theorem lit_tClean_any (F : Frame) (b : CNode) :
    commitRow (render F .tClean) b = (render F .tClean, b) :=
  idle_undecodable_left _ b rfl rfl
    (cleanup_rule_false (by intro h; exact CommitIn.noConfusion h))
    (by intro h; exact Node.noConfusion h)

private theorem lit_sClean_any (F : Frame) (b : CNode) :
    commitRow (render F .sClean) b = (render F .sClean, b) := by
  have hs : seedOut (render F .sClean).raw = CommitCtl.protectedFinal := rfl
  have hview : (render F .sClean).outgoing ≠ seedOut (render F .sClean).raw := by
    rw [hs]
    intro h
    exact CommitCtl.noConfusion h
  have hne1 : (render F .sClean).outgoing ≠ CommitCtl.committedReceived := by
    intro h
    exact CommitCtl.noConfusion h
  have hne2 : (render F .sClean).outgoing ≠ CommitCtl.protectedFinal := by
    intro h
    exact CommitCtl.noConfusion h
  have hne3 : (render F .sClean).outgoing ≠ CommitCtl.committing := by
    intro h
    exact CommitCtl.noConfusion h
  obtain ⟨h5, h6, h7⟩ :=
    raw_rules_false (a := render F .sClean) (by intro h; exact Node.noConfusion h) b
  exact idle_of_guards _ b (sourceAck_false hne1) (target_rule_false rfl)
    (legacy_of_left_view hview) (launch_false hne2) h5 h6 h7
    (deposit_false hne3) (direct_false hne2)

private theorem lit_committedBack_any (F : Frame) (b : CNode) :
    commitRow (render F .committedBack) b = (render F .committedBack, b) := by
  have hcar : (render F .committedBack).carrier ≠ CommitCarrier.none := by
    intro h
    exact CommitCarrier.noConfusion h
  have hcar' : (render F .committedBack).carrier ≠ CommitCarrier.commit := by
    intro h
    exact CommitCarrier.noConfusion h
  obtain ⟨h5, h6⟩ := commit_carrier_rules_false hcar' b
  exact idle_of_guards _ b (sourceAck_false_owner rfl) (target_rule_false rfl)
    (legacy_of_left_carrier hcar) (launch_false_owner b rfl) h5 h6
    (backward_false hcar) (deposit_false_owner b rfl) (direct_false_owner b rfl)

private theorem idle_nonslot (a b : CNode) (ho : rawOwner a.raw = false)
    (hT : rawTarget a.raw = false) (he : a.raw ≠ emptyRaw) (hleg : ¬ Legacy a b) :
    commitRow a b = (a, b) := by
  obtain ⟨h5, h6, h7⟩ := raw_rules_false he b
  exact idle_of_guards a b (sourceAck_false_owner ho) (target_rule_false hT)
    hleg (launch_false_owner b ho) h5 h6 h7 (deposit_false_owner b ho)
    (direct_false_owner b ho)

private theorem idle_none_carrier (a b : CNode) (ho : rawOwner a.raw = false)
    (hT : rawTarget a.raw = false) (hc : a.carrier ≠ CommitCarrier.commit)
    (hb : ¬ BackSlot b) (hleg : ¬ Legacy a b) :
    commitRow a b = (a, b) := by
  obtain ⟨h5, h6⟩ := commit_carrier_rules_false hc b
  exact idle_of_guards a b (sourceAck_false_owner ho) (target_rule_false hT)
    hleg (launch_false_owner b ho) h5 h6 (backward_false' hb)
    (deposit_false_owner b ho) (direct_false_owner b ho)

private theorem idle_committing (a b : CNode)
    (h1 : a.outgoing ≠ CommitCtl.committedReceived)
    (h2 : a.outgoing ≠ CommitCtl.protectedFinal)
    (hT : rawTarget a.raw = false) (he : a.raw ≠ emptyRaw)
    (hb : ¬ BackSlot b) (hleg : ¬ Legacy a b) :
    commitRow a b = (a, b) := by
  obtain ⟨h5, h6, h7⟩ := raw_rules_false he b
  exact idle_of_guards a b (sourceAck_false h1) (target_rule_false hT) hleg
    (launch_false h2) h5 h6 h7 (deposit_false' hb) (direct_false h2)

private theorem sProposal_idle (F : Frame) (b : Tag)
    (hleg : ¬ Legacy (render F .sProposal) (render F b)) :
    commitRow (render F .sProposal) (render F b) = (render F .sProposal, render F b) :=
  idle_nonslot _ _ rfl rfl (by intro h; exact Node.noConfusion h) hleg

private theorem lit_sProposal_empty (F : Frame) :
    commitRow (render F .sProposal) (render F .empty) =
      (render F .sProposal, render F .empty) :=
  sProposal_idle F .empty (legacy_of_row_id rfl)

private theorem lit_sProposal_proposal (F : Frame) :
    commitRow (render F .sProposal) (render F .proposal) =
      (render F .sProposal, render F .proposal) :=
  sProposal_idle F .proposal (legacy_of_row_id rfl)

private theorem sCommitting_idle (F : Frame) (b : Tag)
    (hb : ¬ BackSlot (render F b)) :
    commitRow (render F .sCommitting) (render F b) =
      (render F .sCommitting, render F b) := by
  have hs : seedOut (render F .sCommitting).raw = CommitCtl.protectedFinal := rfl
  have hview : (render F .sCommitting).outgoing ≠ seedOut (render F .sCommitting).raw := by
    rw [hs]
    intro h
    exact CommitCtl.noConfusion h
  exact idle_committing _ _ (by intro h; exact CommitCtl.noConfusion h)
    (by intro h; exact CommitCtl.noConfusion h) rfl
    (by intro h; exact Node.noConfusion h) hb (legacy_of_left_view hview)

private theorem lit_sCommitting_empty (F : Frame) :
    commitRow (render F .sCommitting) (render F .empty) =
      (render F .sCommitting, render F .empty) :=
  sCommitting_idle F .empty (not_backSlot (by intro h; exact CommitCarrier.noConfusion h))

private theorem lit_sCommitting_commit (F : Frame) :
    commitRow (render F .sCommitting) (render F .commit) =
      (render F .sCommitting, render F .commit) :=
  sCommitting_idle F .commit (not_backSlot (by intro h; exact CommitCarrier.noConfusion h))

private theorem empty_idle (F : Frame) (b : Tag)
    (hb : ¬ BackSlot (render F b))
    (hleg : ¬ Legacy (render F .empty) (render F b)) :
    commitRow (render F .empty) (render F b) = (render F .empty, render F b) :=
  idle_none_carrier _ _ rfl rfl (by intro h; exact CommitCarrier.noConfusion h) hb hleg

private theorem lit_empty_empty (F : Frame) :
    commitRow (render F .empty) (render F .empty) = (render F .empty, render F .empty) :=
  empty_idle F .empty (not_backSlot (by intro h; exact CommitCarrier.noConfusion h))
    (legacy_of_row_id rfl)

private theorem lit_empty_proposal (F : Frame) :
    commitRow (render F .empty) (render F .proposal) =
      (render F .empty, render F .proposal) :=
  empty_idle F .proposal (not_backSlot (by intro h; exact CommitCarrier.noConfusion h))
    (legacy_of_row_id rfl)

private theorem lit_empty_commit (F : Frame) :
    commitRow (render F .empty) (render F .commit) = (render F .empty, render F .commit) :=
  empty_idle F .commit (not_backSlot (by intro h; exact CommitCarrier.noConfusion h))
    (legacy_of_right_carrier (by intro h; exact CommitCarrier.noConfusion h))

private theorem lit_empty_tReserved (F : Frame) :
    commitRow (render F .empty) (render F .tReserved) =
      (render F .empty, render F .tReserved) :=
  empty_idle F .tReserved (not_backSlot (by intro h; exact CommitCarrier.noConfusion h))
    (legacy_of_row_id rfl)

private theorem lit_empty_tHeld (F : Frame) :
    commitRow (render F .empty) (render F .tHeld) = (render F .empty, render F .tHeld) :=
  empty_idle F .tHeld (not_backSlot (by intro h; exact CommitCarrier.noConfusion h))
    (legacy_of_row_id rfl)

private theorem lit_empty_tCommitted (F : Frame) :
    commitRow (render F .empty) (render F .tCommitted) =
      (render F .empty, render F .tCommitted) := by
  have hs : seedIn (render F .tCommitted).raw = CommitIn.reserved := rfl
  refine empty_idle F .tCommitted
    (not_backSlot (by intro h; exact CommitCarrier.noConfusion h))
    (legacy_of_right_view ?_)
  rw [hs]
  intro h
  exact CommitIn.noConfusion h

private theorem lit_empty_tClean (F : Frame) :
    commitRow (render F .empty) (render F .tClean) =
      (render F .empty, render F .tClean) := by
  have hs : seedIn (render F .tClean).raw = CommitIn.reserved := rfl
  refine empty_idle F .tClean
    (not_backSlot (by intro h; exact CommitCarrier.noConfusion h))
    (legacy_of_right_view ?_)
  rw [hs]
  intro h
  exact CommitIn.noConfusion h

private theorem finalBack_idle (F : Frame) (b : Tag)
    (hleg : ¬ Legacy (render F .finalBack) (render F b)) :
    commitRow (render F .finalBack) (render F b) = (render F .finalBack, render F b) :=
  idle_nonslot _ _ rfl rfl
    (by intro h; exact interior_ne (by intro hw; exact Wire.noConfusion hw) h) hleg

private theorem lit_finalBack_empty (F : Frame) :
    commitRow (render F .finalBack) (render F .empty) =
      (render F .finalBack, render F .empty) :=
  finalBack_idle F .empty (legacy_of_row_id rfl)

private theorem lit_finalBack_tHeld (F : Frame) :
    commitRow (render F .finalBack) (render F .tHeld) =
      (render F .finalBack, render F .tHeld) :=
  finalBack_idle F .tHeld (legacy_of_row_id rfl)

/-! ### The tag table is a proved restriction of the imported dispatcher -/

/-- Every clean-lane pair fires exactly the imported `commitRow`. -/
theorem tagRow_literal (F : Frame) (a b : Tag) (h : pairAllowed a b = true) :
    commitRow (render F a) (render F b) =
      (render F (tagRow a b).1, render F (tagRow a b).2) := by
  cases a with
  | sReceived => exact lit_sReceived_any F (render F b)
  | tCommitted => exact lit_tCommitted_any F (render F b)
  | sClean => exact lit_sClean_any F (render F b)
  | tReserved => exact lit_tReserved_any F (render F b)
  | tHeld => exact lit_tHeld_any F (render F b)
  | tClean => exact lit_tClean_any F (render F b)
  | committedBack => exact lit_committedBack_any F (render F b)
  | sHome =>
      cases b <;> first
        | exact Bool.noConfusion h
        | exact lit_sHome_empty F
        | exact lit_sHome_tReserved F
  | sProposal =>
      cases b <;> first
        | exact Bool.noConfusion h
        | exact lit_sProposal_empty F
        | exact lit_sProposal_proposal F
        | exact lit_sProposal_finalBack F
  | sProtected =>
      cases b <;> first
        | exact Bool.noConfusion h
        | exact lit_sProtected_empty F
        | exact lit_sProtected_tHeld F
  | sCommitting =>
      cases b <;> first
        | exact Bool.noConfusion h
        | exact lit_sCommitting_empty F
        | exact lit_sCommitting_commit F
        | exact lit_sCommitting_committedBack F
  | empty =>
      cases b <;> first
        | exact Bool.noConfusion h
        | exact lit_empty_empty F
        | exact lit_empty_proposal F
        | exact lit_empty_finalBack F
        | exact lit_empty_commit F
        | exact lit_empty_committedBack F
        | exact lit_empty_tReserved F
        | exact lit_empty_tHeld F
        | exact lit_empty_tCommitted F
        | exact lit_empty_tClean F
  | proposal =>
      cases b <;> first
        | exact Bool.noConfusion h
        | exact lit_proposal_empty F
        | exact lit_proposal_tReserved F
  | finalBack =>
      cases b <;> first
        | exact Bool.noConfusion h
        | exact lit_finalBack_empty F
        | exact lit_finalBack_tHeld F
  | commit =>
      cases b <;> first
        | exact Bool.noConfusion h
        | exact lit_commit_empty F
        | exact lit_commit_tHeld F

/-- The target's outgoing service neighbour is arbitrary and is never changed:
the residue discharge is a purely local left-endpoint service. -/
theorem target_tag_service (F : Frame) (a : Tag) (b : CNode)
    (h : isTargetTag a = true) :
    commitRow (render F a) b = (render F (tagRow a .empty).1, b) := by
  cases a <;> first
    | exact Bool.noConfusion h
    | exact lit_tReserved_any F b
    | exact lit_tHeld_any F b
    | exact lit_tCommitted_any F b
    | exact lit_tClean_any F b

/-- On the capture phases the raw components are literally the imported
`captureRow`, so the first half of the lifecycle reuses the reservation file's
own row table with no commit-lane field in play. -/
theorem capture_tagRow_literal (F : Frame) (a b : Tag) (h : pairAllowed a b = true)
    (ha : isCaptureTag a = true) (hb : isCaptureTag b = true) :
    captureRow (render F a).raw (render F b).raw =
      ((render F (tagRow a b).1).raw, (render F (tagRow a b).2).raw) := by
  cases a <;> cases b <;> first
    | exact Bool.noConfusion h
    | exact Bool.noConfusion ha
    | exact Bool.noConfusion hb
    | rfl

/-! ## The lifecycle phase carrier and the real scheduler embedding -/

/-- The active phases of one clean capture lifecycle.  Positive proposal
indices are physical slot positions; the other carrier indices `j : Fin (h-1)`
name physical slot `j + 1`.  `committedAt j tgtDone` retains the target-cleanup
bit while the COMMITTED receipt returns; that bit describes the existing
incoming control of the target, not extra protocol state. -/
inductive LifecycleState (F : Frame) where
  | proposalAt (j : Fin F.h)
  | finalAt (j : Fin (F.h - 1))
  | protectedWait
  | commitAt (j : Fin (F.h - 1))
  | committedAt (j : Fin (F.h - 1)) (tgtDone : Bool)
  | postcommit (ackDone tgtDone : Bool) (pending : ackDone = false ∨ tgtDone = false)

/-- Success is `clean`: both postcommit obligations are discharged. -/
def finishPost (F : Frame) : Bool → Bool → StopNode (LifecycleState F)
  | false, t => .active (.postcommit false t (Or.inl rfl))
  | true, false => .active (.postcommit true false (Or.inr rfl))
  | true, true => .success

/-- The single useful firing available on the gap's own edges. -/
def advance (F : Frame) : LifecycleState F → StopNode (LifecycleState F)
  | .proposalAt j =>
      if hj : j.val + 1 < F.h then
        .active (.proposalAt ⟨j.val + 1, hj⟩)
      else if hz : j.val = 0 then
        .active .protectedWait
      else
        .active (.finalAt ⟨j.val - 1, by
          have hb := j.isLt
          omega⟩)
  | .finalAt j =>
      if hz : j.val = 0 then .active .protectedWait
      else .active (.finalAt ⟨j.val - 1, by have hb := j.isLt; omega⟩)
  | .protectedWait =>
      if hh : 1 < F.h then
        .active (.commitAt ⟨0, by omega⟩)
      else finishPost F false false
  | .commitAt j =>
      if hj : j.val + 2 < F.h then
        .active (.commitAt ⟨j.val + 1, by omega⟩)
      else .active (.committedAt j false)
  | .committedAt j t =>
      if hz : j.val = 0 then finishPost F false t
      else .active (.committedAt ⟨j.val - 1, by have hb := j.isLt; omega⟩ t)
  | .postcommit false t _ => finishPost F true t
  | .postcommit true _ _ => .success

/-- The target's residue discharge.  It is an actual local service at the
target root, available at any time after the commit, including while the
COMMITTED receipt is still returning. -/
def cleanupAttempt (F : Frame) : LifecycleState F → StopNode (LifecycleState F)
  | .committedAt j _ => .active (.committedAt j true)
  | .postcommit a _ _ => finishPost F a true
  | s => .active s

/-- Whether the gap's own edges still carry work. -/
def gapWork {F : Frame} : LifecycleState F → Bool
  | .postcommit true _ _ => false
  | _ => true

/-- The unique gap edge that can fire in a phase. -/
def carrierEdge (F : Frame) : LifecycleState F → Fin F.h
  | .proposalAt j => j
  | .finalAt j => ⟨j.val, by have hb := j.isLt; have := F.hpos; omega⟩
  | .protectedWait => ⟨0, F.hpos⟩
  | .commitAt j => ⟨j.val + 1, by have hb := j.isLt; have := F.hpos; omega⟩
  | .committedAt j _ => ⟨j.val, by have hb := j.isLt; have := F.hpos; omega⟩
  | .postcommit _ _ _ => ⟨0, F.hpos⟩

/-- One gap edge acting on the lifecycle. -/
def gapNext (F : Frame) (s : LifecycleState F) (a : Fin F.h) :
    StopNode (LifecycleState F) :=
  if gapWork s = true ∧ a = carrierEdge F s then advance F s else .active s

/-- The gap's `h` physical edges inside the ambient scheduler, together with
the target root's *outgoing* service edge.  That extra edge is geometry, not a
new runtime guard: the target is the left endpoint of its own outgoing edge,
which is where its local residue discharge fires. -/
structure Layout (F : Frame) (n : Nat) where
  embedding : GapEmbedding F n
  targetEdge : Fin n
  targetOutside : ∀ a : Fin F.h, embedding.edgeAt a ≠ targetEdge

/-- A concrete layout inside the literal ring: the selected gap's own edges
plus the first edge of the next gap, whose left endpoint is this gap's target
root. -/
def ringLayout (R : ShortGapLiteralRingRows.RFrame) (g : Fin R.m)
    (ccw : CcwPort) (cw : CwPort)
    (hnext : g ≠ ShortGapLiteralRingRows.next R g) :
    Layout (walkFrame R ccw cw) R.n where
  embedding := walkEmbedding R g ccw cw
  targetEdge :=
    ShortGapLiteralRingRows.encE R (ShortGapLiteralRingRows.next R g) ⟨0, R.hh⟩
  targetOutside a h := by
    have he := congrArg (ShortGapLiteralRingRows.edgeVtx R) h
    have he' : (g, (a : Fin R.h)) =
        (ShortGapLiteralRingRows.next R g, (⟨0, R.hh⟩ : Fin R.h)) :=
      (ShortGapLiteralRingRows.edgeVtx_encE R g a).symm.trans
        (he.trans (ShortGapLiteralRingRows.edgeVtx_encE R
          (ShortGapLiteralRingRows.next R g) ⟨0, R.hh⟩))
    exact hnext (congrArg Prod.fst he')

open Classical in
/-- One ambient scheduler edge acting on the whole lifecycle. -/
noncomputable def lifecycleStep {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (e : Fin n) :
    StopNode (LifecycleState F) :=
  if hx : ∃ a : Fin F.h, L.embedding.edgeAt a = e then
    gapNext F s hx.choose
  else if e = L.targetEdge then cleanupAttempt F s else .active s

theorem lifecycleStep_gap {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (a : Fin F.h) :
    lifecycleStep L s (L.embedding.edgeAt a) = gapNext F s a := by
  classical
  have hx : ∃ b : Fin F.h, L.embedding.edgeAt b = L.embedding.edgeAt a := ⟨a, rfl⟩
  have hc : hx.choose = a := L.embedding.inj _ _ hx.choose_spec
  simp only [lifecycleStep, dif_pos hx, hc]

theorem lifecycleStep_target {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) :
    lifecycleStep L s L.targetEdge = cleanupAttempt F s := by
  classical
  have hx : ¬ ∃ a : Fin F.h, L.embedding.edgeAt a = L.targetEdge := by
    rintro ⟨a, ha⟩
    exact L.targetOutside a ha
  simp [lifecycleStep, dif_neg hx]

/-- The target may discharge its residue while the receipt is still in
flight. -/
theorem committed_cleanup_early {F : Frame} {n : Nat}
    (L : Layout F n) (j : Fin (F.h - 1)) :
    lifecycleStep L (.committedAt j false) L.targetEdge =
      .active (.committedAt j true) := by
  rw [lifecycleStep_target]
  rfl

/-- The unique scheduler edge that lowers the debt in a given phase. -/
def usefulEdge {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) : Fin n :=
  if gapWork s = true then L.embedding.edgeAt (carrierEdge F s) else L.targetEdge

/-- The lifecycle starts before proposal launch. -/
def lifecycleStart (F : Frame) : LifecycleState F := .proposalAt ⟨0, F.hpos⟩

/-- `h = 1`: launch, acceptance and FINAL deposit are one firing. -/
theorem h1_proposal_direct (F : Frame) (hh : F.h = 1) :
    advance F (lifecycleStart F) = .active .protectedWait := by
  have hj : ¬ ((⟨0, F.hpos⟩ : Fin F.h).val + 1 < F.h) := by
    simp only []
    omega
  simp [lifecycleStart, advance, dif_neg hj]

/-- `h = 1`: the protected launch, the commit at the target and the committed
receipt are one firing. -/
theorem h1_commit_direct (F : Frame) (hh : F.h = 1) :
    advance F .protectedWait = finishPost F false false := by
  have hp : ¬ (1 < F.h) := by omega
  simp only [advance, dif_neg hp]

/-! ## The exact useful-firing debt and the Bellman supersolution -/

/-- An undischarged postcommit obligation costs one firing. -/
def bitDebt : Bool → Nat
  | false => 1
  | true => 0

/-- Remaining useful firings of the whole lifecycle.  The four arithmetic
formulas are the four transport groups; the two `bitDebt` summands are the two
independent postcommit discharges. -/
def activeDebt (F : Frame) : LifecycleState F → Nat
  | .proposalAt j => 4 * F.h - j.val
  | .finalAt j => 2 * F.h + j.val + 2
  | .protectedWait => 2 * F.h + 1
  | .commitAt j => 2 * F.h - j.val
  | .committedAt j t => j.val + 2 + bitDebt t
  | .postcommit a t _ => bitDebt a + bitDebt t

def lifeDebt (F : Frame) : StopNode (LifecycleState F) → Nat
  | .active s => activeDebt F s
  | .success => 0
  | .failure => 0

private theorem finishPost_debt (F : Frame) (a t : Bool) :
    lifeDebt F (finishPost F a t) = bitDebt a + bitDebt t := by
  cases a <;> cases t <;> rfl

/-- The gap's own useful firing costs exactly one. -/
private theorem advance_debt (F : Frame) (s : LifecycleState F) :
    lifeDebt F (advance F s) + 1 = lifeDebt F (.active s) := by
  have hh := F.hpos
  cases s with
  | proposalAt j =>
      have hb := j.isLt
      by_cases hj : j.val + 1 < F.h
      · simp only [advance, dif_pos hj, lifeDebt, activeDebt]
        omega
      · by_cases hz : j.val = 0
        · simp only [advance, dif_neg hj, dif_pos hz, lifeDebt, activeDebt]
          omega
        · simp only [advance, dif_neg hj, dif_neg hz, lifeDebt, activeDebt]
          omega
  | finalAt j =>
      have hb := j.isLt
      by_cases hz : j.val = 0
      · simp only [advance, dif_pos hz, lifeDebt, activeDebt]
        omega
      · simp only [advance, dif_neg hz, lifeDebt, activeDebt]
        omega
  | protectedWait =>
      by_cases hp : 1 < F.h
      · simp only [advance, dif_pos hp, lifeDebt, activeDebt]
        omega
      · have he : advance F (LifecycleState.protectedWait : LifecycleState F) =
            finishPost F false false := by
          simp only [advance, dif_neg hp]
        rw [he, finishPost_debt]
        simp only [lifeDebt, activeDebt, bitDebt]
        omega
  | commitAt j =>
      have hb := j.isLt
      by_cases hj : j.val + 2 < F.h
      · simp only [advance, dif_pos hj, lifeDebt, activeDebt]
        omega
      · simp only [advance, dif_neg hj, lifeDebt, activeDebt, bitDebt]
        omega
  | committedAt j t =>
      have hb := j.isLt
      by_cases hz : j.val = 0
      · have he : advance F (LifecycleState.committedAt j t) = finishPost F false t := by
          simp only [advance, dif_pos hz]
        rw [he, finishPost_debt]
        simp only [lifeDebt, activeDebt, bitDebt]
        omega
      · simp only [advance, dif_neg hz, lifeDebt, activeDebt]
        omega
  | postcommit a t hp =>
      cases a with
      | false =>
          show lifeDebt F (finishPost F true t) + 1 = _
          rw [finishPost_debt]
          cases t <;> rfl
      | true =>
          cases t with
          | false => rfl
          | true => rcases hp with h | h <;> exact Bool.noConfusion h

/-- The target residue discharge never increases the debt. -/
private theorem cleanup_debt_le (F : Frame) (s : LifecycleState F) :
    lifeDebt F (cleanupAttempt F s) ≤ lifeDebt F (.active s) := by
  cases s with
  | proposalAt j => exact Nat.le_refl _
  | finalAt j => exact Nat.le_refl _
  | protectedWait => exact Nat.le_refl _
  | commitAt j => exact Nat.le_refl _
  | committedAt j t =>
      cases t with
      | false =>
          show j.val + 2 + bitDebt true ≤ j.val + 2 + bitDebt false
          simp only [bitDebt]
          omega
      | true => exact Nat.le_refl _
  | postcommit a t hp =>
      show lifeDebt F (finishPost F a true) ≤ _
      rw [finishPost_debt]
      cases a <;> cases t <;> simp only [lifeDebt, activeDebt, bitDebt] <;> omega

/-- When the gap edges are exhausted, the target discharge is the useful
firing and costs exactly one. -/
private theorem cleanup_debt_strict (F : Frame) (s : LifecycleState F)
    (hs : gapWork s ≠ true) :
    lifeDebt F (cleanupAttempt F s) + 1 = lifeDebt F (.active s) := by
  cases s with
  | proposalAt j => exact absurd rfl hs
  | finalAt j => exact absurd rfl hs
  | protectedWait => exact absurd rfl hs
  | commitAt j => exact absurd rfl hs
  | committedAt j t => exact absurd rfl hs
  | postcommit a t hp =>
      cases a with
      | false => exact absurd rfl hs
      | true =>
          cases t with
          | false => rfl
          | true => rcases hp with h | h <;> exact Bool.noConfusion h

private theorem gapNext_debt_le (F : Frame) (s : LifecycleState F) (a : Fin F.h) :
    lifeDebt F (gapNext F s a) ≤ lifeDebt F (.active s) := by
  by_cases h : gapWork s = true ∧ a = carrierEdge F s
  · rw [gapNext, if_pos h]
    have hd := advance_debt F s
    omega
  · simp only [gapNext, if_neg h, Nat.le_refl]

/-- Every raw scheduler edge has no larger debt. -/
theorem lifeDebt_step_le {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (e : Fin n) :
    lifeDebt F (lifecycleStep L s e) ≤ lifeDebt F (.active s) := by
  classical
  by_cases hx : ∃ a : Fin F.h, L.embedding.edgeAt a = e
  · simp only [lifecycleStep, dif_pos hx]
    exact gapNext_debt_le F s hx.choose
  · simp only [lifecycleStep, dif_neg hx]
    by_cases he : e = L.targetEdge
    · rw [if_pos he]
      exact cleanup_debt_le F s
    · simp only [if_neg he, Nat.le_refl]

/-- The explicit real scheduler edge that lowers the debt by exactly one. -/
theorem lifeDebt_advancing_edge {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) :
    lifeDebt F (lifecycleStep L s (usefulEdge L s)) + 1 = lifeDebt F (.active s) := by
  by_cases hs : gapWork s = true
  · simp only [usefulEdge, if_pos hs]
    rw [lifecycleStep_gap]
    have hg : gapWork s = true ∧ carrierEdge F s = carrierEdge F s := ⟨hs, rfl⟩
    rw [gapNext, if_pos hg]
    exact advance_debt F s
  · simp only [usefulEdge, if_neg hs]
    rw [lifecycleStep_target]
    exact cleanup_debt_strict F s hs

theorem lifeDebt_active_pos (F : Frame) (s : LifecycleState F) :
    0 < lifeDebt F (.active s) := by
  have h := advance_debt F s
  omega

private theorem ofFn_sum_lt_of_single_lt
    {N : Nat} (f g : Fin N → Nat) (chosen : Fin N)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction N with
  | zero => exact Fin.elim0 chosen
  | succ N ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin N => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        have hprev : chosen.val - 1 < N := by
          have := chosen.isLt
          omega
        have hsucc : (⟨chosen.val - 1, hprev⟩ : Fin N).succ = chosen :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        have htail := ih
          (fun i : Fin N => f i.succ) (fun i => g i.succ)
          ⟨chosen.val - 1, hprev⟩
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

/-- The exact child-sum inequality of the scale-one Bellman argument. -/
theorem lifeDebt_child_sum {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) :
    1 + (List.ofFn (fun e : Fin n => lifeDebt F (lifecycleStep L s e))).sum ≤
      n * lifeDebt F (.active s) := by
  have ha := lifeDebt_advancing_edge L s
  have hlt := ofFn_sum_lt_of_single_lt
    (fun e : Fin n => lifeDebt F (lifecycleStep L s e))
    (fun _ : Fin n => lifeDebt F (.active s)) (usefulEdge L s)
    (fun e => lifeDebt_step_le L s e) (by omega)
  rw [ofFn_sum_const] at hlt
  omega

/-- Scale one on the physical `n`-edge scheduler, for the *whole* lifecycle. -/
theorem lifecycle_bellman {F : Frame} {n : Nat} (L : Layout F n) :
    NatBellmanSuperSolution (lifecycleStep L) 1 (fun x => n * lifeDebt F x) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have h := Nat.mul_le_mul_left n (lifeDebt_child_sum L s)
  rw [Nat.mul_add, Nat.mul_one] at h
  show 1 * n +
      (List.ofFn (fun e : Fin n => n * lifeDebt F (lifecycleStep L s e))).sum ≤
    n * (n * lifeDebt F (.active s))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  exact h

private theorem finishPost_no_failure (F : Frame) (a t : Bool) :
    finishPost F a t ≠ .failure := by
  cases a <;> cases t <;> simp [finishPost]

private theorem advance_no_failure (F : Frame) (s : LifecycleState F) :
    advance F s ≠ .failure := by
  cases s with
  | proposalAt j =>
      by_cases hj : j.val + 1 < F.h
      · rw [advance, dif_pos hj]
        intro h
        cases h
      · by_cases hz : j.val = 0
        · rw [advance, dif_neg hj, dif_pos hz]
          intro h
          cases h
        · rw [advance, dif_neg hj, dif_neg hz]
          intro h
          cases h
  | finalAt j =>
      by_cases hz : j.val = 0
      · rw [advance, dif_pos hz]
        intro h
        cases h
      · rw [advance, dif_neg hz]
        intro h
        cases h
  | protectedWait =>
      by_cases hp : 1 < F.h
      · rw [advance, dif_pos hp]
        intro h
        cases h
      · rw [advance, dif_neg hp]
        exact finishPost_no_failure F false false
  | commitAt j =>
      by_cases hj : j.val + 2 < F.h
      · rw [advance, dif_pos hj]
        intro h
        cases h
      · rw [advance, dif_neg hj]
        intro h
        cases h
  | committedAt j t =>
      by_cases hz : j.val = 0
      · rw [advance, dif_pos hz]
        exact finishPost_no_failure F false t
      · rw [advance, dif_neg hz]
        intro h
        cases h
  | postcommit a t hp =>
      cases a with
      | false => exact finishPost_no_failure F true t
      | true =>
          intro h
          cases h

private theorem cleanup_no_failure (F : Frame) (s : LifecycleState F) :
    cleanupAttempt F s ≠ .failure := by
  cases s with
  | proposalAt j => intro h; cases h
  | finalAt j => intro h; cases h
  | protectedWait => intro h; cases h
  | commitAt j => intro h; cases h
  | committedAt j t => intro h; cases h
  | postcommit a t hp => exact finishPost_no_failure F a true

private theorem gapNext_no_failure (F : Frame) (s : LifecycleState F) (a : Fin F.h) :
    gapNext F s a ≠ .failure := by
  by_cases h : gapWork s = true ∧ a = carrierEdge F s
  · rw [gapNext, if_pos h]
    exact advance_no_failure F s
  · rw [gapNext, if_neg h]
    intro hbad
    cases hbad

/-- The lifecycle has no failure node at all. -/
theorem lifecycle_no_failure {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (e : Fin n) :
    lifecycleStep L s e ≠ .failure := by
  classical
  by_cases hx : ∃ a : Fin F.h, L.embedding.edgeAt a = e
  · simp only [lifecycleStep, dif_pos hx]
    exact gapNext_no_failure F s hx.choose
  · simp only [lifecycleStep, dif_neg hx]
    by_cases he : e = L.targetEdge
    · rw [if_pos he]
      exact cleanup_no_failure F s
    · rw [if_neg he]
      intro hbad
      cases hbad

/-- The exact start potential: `n * (4 * h)`. -/
theorem lifecycle_start_potential (F : Frame) (n : Nat) :
    (fun x => n * lifeDebt F x) (StopNode.active (lifecycleStart F)) = n * (4 * F.h) := by
  show n * (4 * F.h - (0 : Nat)) = n * (4 * F.h)
  rw [Nat.sub_zero]

/-- The imported proposal/FINAL kernel is exactly the first summand of the
lifecycle budget; the remaining `n * (2h+1)` is the protected commit lane and
the two discharges. -/
theorem lifecycle_start_eq_proposal (R : ShortGapLiteralRingRows.RFrame)
    (ccw : CcwPort) (cw : CwPort) :
    R.n * lifeDebt (walkFrame R ccw cw)
        (.active (lifecycleStart (walkFrame R ccw cw))) =
      proposalWalkPotential R ccw cw (.active (proposalWalkStart R ccw cw)) +
        R.n * (2 * R.h + 1) := by
  have hh := R.hh
  have ha : 4 * R.h = (2 * R.h - 1) + (2 * R.h + 1) := by omega
  calc
    R.n * lifeDebt (walkFrame R ccw cw)
        (.active (lifecycleStart (walkFrame R ccw cw)))
        = R.n * (4 * R.h) := lifecycle_start_potential (walkFrame R ccw cw) R.n
    _ = R.n * (2 * R.h - 1) + R.n * (2 * R.h + 1) := by rw [ha, Nat.mul_add]
    _ = _ := by rw [proposalWalk_start_potential]

theorem lifecycle_truncatedCost_le {F : Frame} {n : Nat} (L : Layout F n) (T : Nat) :
    truncatedActiveCostNumerator (lifecycleStep L)
        (.active (lifecycleStart F)) T ≤ n ^ T * (n * (4 * F.h)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (lifecycleStep L) 1 (fun x => n * lifeDebt F x) (lifecycle_bellman L)
    (.active (lifecycleStart F)) T
  simpa only [Nat.one_mul, lifecycle_start_potential] using h

/-! ## The spatial clean-lane encoding -/

def targetSite (F : Frame) : Fin (F.h + 1) := ⟨F.h, Nat.lt_succ_self _⟩

def sourceTag {F : Frame} : StopNode (LifecycleState F) → Tag
  | .active (.proposalAt j) => if j.val = 0 then .sHome else .sProposal
  | .active (.finalAt _) => .sProposal
  | .active .protectedWait => .sProtected
  | .active (.commitAt _) => .sCommitting
  | .active (.committedAt _ _) => .sCommitting
  | .active (.postcommit a _ _) => if a = true then .sClean else .sReceived
  | .success => .sClean
  | .failure => .sClean

def targetTag {F : Frame} : StopNode (LifecycleState F) → Tag
  | .active (.proposalAt _) => .tReserved
  | .active (.finalAt _) => .tHeld
  | .active .protectedWait => .tHeld
  | .active (.commitAt _) => .tHeld
  | .active (.committedAt _ t) => if t = true then .tClean else .tCommitted
  | .active (.postcommit _ t _) => if t = true then .tClean else .tCommitted
  | .success => .tClean
  | .failure => .tClean

/-- The physical slot occupied by the phase's carrier.  Position `0` is the
source root, so `tokPos = 0` means "no interior carrier". -/
def tokPos {F : Frame} : LifecycleState F → Nat
  | .proposalAt j => j.val
  | .finalAt j => j.val + 1
  | .protectedWait => 0
  | .commitAt j => j.val + 1
  | .committedAt j _ => j.val + 1
  | .postcommit _ _ _ => 0

def tokKind {F : Frame} : LifecycleState F → Tag
  | .proposalAt _ => .proposal
  | .finalAt _ => .finalBack
  | .commitAt _ => .commit
  | .committedAt _ _ => .committedBack
  | .protectedWait => .empty
  | .postcommit _ _ _ => .empty

def tokenTag {F : Frame} : StopNode (LifecycleState F) → Nat → Tag
  | .active s, k => if k = tokPos s then tokKind s else .empty
  | .success, _ => .empty
  | .failure, _ => .empty

/-- The tag at physical position `k` of the gap. -/
def tagAt (F : Frame) (x : StopNode (LifecycleState F)) (k : Nat) : Tag :=
  if k = 0 then sourceTag x else if k = F.h then targetTag x else tokenTag x k

/-- The whole gap as a tag configuration on `Fin (h+1)`. -/
def tagConfig (F : Frame) (x : StopNode (LifecycleState F)) : Fin (F.h + 1) → Tag :=
  fun k => tagAt F x k.val

/-- The literal `CNode` configuration of the whole gap. -/
def encodeLife (F : Frame) (x : StopNode (LifecycleState F)) : Fin (F.h + 1) → CNode :=
  fun k => render F (tagConfig F x k)

def pairUpdate {A : Type} (F : Frame) (cfg : Fin (F.h + 1) → A) (a : Fin F.h)
    (p : A × A) : Fin (F.h + 1) → A :=
  fun k => if k.val = a.val then p.1 else if k.val = a.val + 1 then p.2 else cfg k

def targetUpdate {A : Type} (F : Frame) (cfg : Fin (F.h + 1) → A) (v : A) :
    Fin (F.h + 1) → A := fun k => if k.val = F.h then v else cfg k

def tagGapStep (F : Frame) (cfg : Fin (F.h + 1) → Tag) (a : Fin F.h) : Fin (F.h + 1) → Tag :=
  pairUpdate F cfg a (tagRow (cfg (leftEnd F a)) (cfg (rightEnd F a)))

def tagCleanupStep (F : Frame) (cfg : Fin (F.h + 1) → Tag) : Fin (F.h + 1) → Tag :=
  targetUpdate F cfg (tagRow (cfg (targetSite F)) .empty).1

private theorem pairUpdate_eq {A : Type} (F : Frame) (cfg cfg' : Fin (F.h + 1) → A)
    (a : Fin F.h) (p : A × A)
    (hx : cfg' (leftEnd F a) = p.1) (hy : cfg' (rightEnd F a) = p.2)
    (hrest : ∀ k : Fin (F.h + 1), k.val ≠ a.val → k.val ≠ a.val + 1 → cfg' k = cfg k) :
    pairUpdate F cfg a p = cfg' := by
  funext k
  show (if k.val = a.val then p.1 else if k.val = a.val + 1 then p.2 else cfg k) = cfg' k
  by_cases h0 : k.val = a.val
  · rw [if_pos h0, ← hx]
    exact congrArg cfg' (Fin.ext (show (leftEnd F a).val = k.val from h0.symm))
  · rw [if_neg h0]
    by_cases h1 : k.val = a.val + 1
    · rw [if_pos h1, ← hy]
      exact congrArg cfg' (Fin.ext (show (rightEnd F a).val = k.val from h1.symm))
    · rw [if_neg h1]
      exact (hrest k h0 h1).symm

private theorem targetUpdate_eq {A : Type} (F : Frame) (cfg cfg' : Fin (F.h + 1) → A)
    (v : A) (hv : cfg' (targetSite F) = v)
    (hrest : ∀ k : Fin (F.h + 1), k.val ≠ F.h → cfg' k = cfg k) :
    targetUpdate F cfg v = cfg' := by
  funext k
  show (if k.val = F.h then v else cfg k) = cfg' k
  by_cases hk : k.val = F.h
  · rw [if_pos hk, ← hv]
    exact congrArg cfg' (Fin.ext (show (targetSite F).val = k.val from hk.symm))
  · rw [if_neg hk]
    exact (hrest k hk).symm

private theorem tagAt_src (F : Frame) (x : StopNode (LifecycleState F)) (k : Nat)
    (h : k = 0) : tagAt F x k = sourceTag x := by
  show (if k = 0 then sourceTag x else if k = F.h then targetTag x else tokenTag x k) =
    sourceTag x
  rw [if_pos h]

private theorem tagAt_tgt (F : Frame) (x : StopNode (LifecycleState F)) (k : Nat)
    (h0 : ¬ (k = 0)) (h : k = F.h) : tagAt F x k = targetTag x := by
  show (if k = 0 then sourceTag x else if k = F.h then targetTag x else tokenTag x k) =
    targetTag x
  rw [if_neg h0, if_pos h]

private theorem tagAt_mid (F : Frame) (x : StopNode (LifecycleState F)) (k : Nat)
    (h0 : ¬ (k = 0)) (h : ¬ (k = F.h)) : tagAt F x k = tokenTag x k := by
  show (if k = 0 then sourceTag x else if k = F.h then targetTag x else tokenTag x k) =
    tokenTag x k
  rw [if_neg h0, if_neg h]

private theorem left_src (F : Frame) (x : StopNode (LifecycleState F)) (a : Fin F.h)
    (h : a.val = 0) : tagConfig F x (leftEnd F a) = sourceTag x :=
  tagAt_src F x a.val h

private theorem left_tok (F : Frame) (x : StopNode (LifecycleState F)) (a : Fin F.h)
    (h : ¬ (a.val = 0)) : tagConfig F x (leftEnd F a) = tokenTag x a.val :=
  tagAt_mid F x a.val h (Nat.ne_of_lt a.isLt)

private theorem right_tgt (F : Frame) (x : StopNode (LifecycleState F)) (a : Fin F.h)
    (h : a.val + 1 = F.h) : tagConfig F x (rightEnd F a) = targetTag x :=
  tagAt_tgt F x (a.val + 1) (by omega) h

private theorem right_tok (F : Frame) (x : StopNode (LifecycleState F)) (a : Fin F.h)
    (h : ¬ (a.val + 1 = F.h)) : tagConfig F x (rightEnd F a) = tokenTag x (a.val + 1) :=
  tagAt_mid F x (a.val + 1) (by omega) h

private theorem tagConfig_targetSite (F : Frame) (x : StopNode (LifecycleState F)) :
    tagConfig F x (targetSite F) = targetTag x :=
  tagAt_tgt F x F.h (by have := F.hpos; omega) rfl

private theorem tok_hit (F : Frame) (s : LifecycleState F) (k : Nat) (h : k = tokPos s) :
    tokenTag (StopNode.active s) k = tokKind s := by
  show (if k = tokPos s then tokKind s else Tag.empty) = tokKind s
  rw [if_pos h]

private theorem tok_miss (F : Frame) (s : LifecycleState F) (k : Nat)
    (h : ¬ (k = tokPos s)) : tokenTag (StopNode.active s) k = Tag.empty := by
  show (if k = tokPos s then tokKind s else Tag.empty) = Tag.empty
  rw [if_neg h]

/-! ### Framing: only the two endpoints of the scheduled edge can change -/

private theorem tokPos_carrier (F : Frame) (s : LifecycleState F) :
    tokPos s = (carrierEdge F s).val ∨ tokPos s = (carrierEdge F s).val + 1 := by
  cases s with
  | proposalAt j => exact Or.inl rfl
  | finalAt j => exact Or.inr rfl
  | protectedWait => exact Or.inl rfl
  | commitAt j => exact Or.inl rfl
  | committedAt j t => exact Or.inr rfl
  | postcommit a t hp => exact Or.inl rfl

private theorem advance_token (F : Frame) (s : LifecycleState F) :
    advance F s = .success ∨
      ∃ s' : LifecycleState F, advance F s = .active s' ∧
        (tokPos s' = (carrierEdge F s).val ∨ tokPos s' = (carrierEdge F s).val + 1) := by
  cases s with
  | proposalAt j =>
      have hb := j.isLt
      by_cases hj : j.val + 1 < F.h
      · exact Or.inr ⟨LifecycleState.proposalAt ⟨j.val + 1, hj⟩,
          by rw [advance, dif_pos hj], Or.inr rfl⟩
      · by_cases hz : j.val = 0
        · exact Or.inr ⟨LifecycleState.protectedWait,
            by rw [advance, dif_neg hj, dif_pos hz], Or.inl hz.symm⟩
        · refine Or.inr ⟨LifecycleState.finalAt ⟨j.val - 1, by omega⟩,
            by rw [advance, dif_neg hj, dif_neg hz], Or.inl ?_⟩
          show j.val - 1 + 1 = j.val
          omega
  | finalAt j =>
      have hb := j.isLt
      by_cases hz : j.val = 0
      · exact Or.inr ⟨LifecycleState.protectedWait,
          by rw [advance, dif_pos hz], Or.inl hz.symm⟩
      · refine Or.inr ⟨LifecycleState.finalAt ⟨j.val - 1, by omega⟩,
          by rw [advance, dif_neg hz], Or.inl ?_⟩
        show j.val - 1 + 1 = j.val
        omega
  | protectedWait =>
      by_cases hp : 1 < F.h
      · exact Or.inr ⟨LifecycleState.commitAt ⟨0, by omega⟩,
          by rw [advance, dif_pos hp], Or.inr rfl⟩
      · exact Or.inr ⟨LifecycleState.postcommit false false (Or.inl rfl),
          (by rw [advance, dif_neg hp]; rfl), Or.inl rfl⟩
  | commitAt j =>
      have hb := j.isLt
      by_cases hj : j.val + 2 < F.h
      · exact Or.inr ⟨LifecycleState.commitAt ⟨j.val + 1, by omega⟩,
          by rw [advance, dif_pos hj], Or.inr rfl⟩
      · exact Or.inr ⟨LifecycleState.committedAt j false,
          by rw [advance, dif_neg hj], Or.inl rfl⟩
  | committedAt j t =>
      have hb := j.isLt
      by_cases hz : j.val = 0
      · exact Or.inr ⟨LifecycleState.postcommit false t (Or.inl rfl),
          (by rw [advance, dif_pos hz]; rfl), Or.inl hz.symm⟩
      · refine Or.inr ⟨LifecycleState.committedAt ⟨j.val - 1, by omega⟩ t,
          by rw [advance, dif_neg hz], Or.inl ?_⟩
        show j.val - 1 + 1 = j.val
        omega
  | postcommit a t hp =>
      cases a with
      | false =>
          cases t with
          | false =>
              exact Or.inr ⟨LifecycleState.postcommit true false (Or.inr rfl),
                rfl, Or.inl rfl⟩
          | true => exact Or.inl rfl
      | true => exact Or.inl rfl

private theorem tokenTag_gapNext_off (F : Frame) (s : LifecycleState F) (a : Fin F.h)
    (k : Nat) (h1 : ¬ (k = a.val)) (h2 : ¬ (k = a.val + 1)) :
    tokenTag (gapNext F s a) k = tokenTag (StopNode.active s) k := by
  by_cases hc : gapWork s = true ∧ a = carrierEdge F s
  · have hv : (carrierEdge F s).val = a.val := congrArg Fin.val hc.2.symm
    have hold : tokenTag (StopNode.active s) k = Tag.empty := by
      refine tok_miss F s k ?_
      rcases tokPos_carrier F s with hp | hp <;> rw [hp, hv] <;> assumption
    rw [gapNext, if_pos hc, hold]
    rcases advance_token F s with hs | ⟨s', hs, hp⟩
    · rw [hs]
      rfl
    · rw [hs]
      refine tok_miss F s' k ?_
      rcases hp with hp | hp <;> rw [hp, hv] <;> assumption
  · rw [gapNext, if_neg hc]

private theorem sourceTag_advance (F : Frame) (s : LifecycleState F)
    (h : ¬ ((carrierEdge F s).val = 0)) :
    sourceTag (advance F s) = sourceTag (StopNode.active s) := by
  cases s with
  | proposalAt j =>
      have hz : ¬ (j.val = 0) := h
      by_cases hj : j.val + 1 < F.h
      · rw [advance, dif_pos hj]
        show (if j.val + 1 = 0 then Tag.sHome else Tag.sProposal) =
          (if j.val = 0 then Tag.sHome else Tag.sProposal)
        rw [if_neg (show ¬ (j.val + 1 = 0) by omega), if_neg hz]
      · rw [advance, dif_neg hj, dif_neg hz]
        show Tag.sProposal = (if j.val = 0 then Tag.sHome else Tag.sProposal)
        rw [if_neg hz]
  | finalAt j =>
      have hz : ¬ (j.val = 0) := h
      rw [advance, dif_neg hz]; rfl
  | protectedWait => exact absurd rfl h
  | commitAt j =>
      by_cases hj : j.val + 2 < F.h
      · rw [advance, dif_pos hj]; rfl
      · rw [advance, dif_neg hj]; rfl
  | committedAt j t =>
      have hz : ¬ (j.val = 0) := h
      rw [advance, dif_neg hz]; rfl
  | postcommit a t hp => exact absurd rfl h

private theorem targetTag_advance (F : Frame) (s : LifecycleState F)
    (hw : gapWork s = true) (h : ¬ ((carrierEdge F s).val + 1 = F.h)) :
    targetTag (advance F s) = targetTag (StopNode.active s) := by
  have hh := F.hpos
  cases s with
  | proposalAt j =>
      have hb := j.isLt
      have hne : ¬ (j.val + 1 = F.h) := h
      have hj : j.val + 1 < F.h := by omega
      rw [advance, dif_pos hj]; rfl
  | finalAt j =>
      by_cases hz : j.val = 0
      · rw [advance, dif_pos hz]; rfl
      · rw [advance, dif_neg hz]; rfl
  | protectedWait =>
      have hne : ¬ ((0 : Nat) + 1 = F.h) := h
      have hp : 1 < F.h := by omega
      rw [advance, dif_pos hp]; rfl
  | commitAt j =>
      have hb := j.isLt
      have hne : ¬ (j.val + 1 + 1 = F.h) := h
      have hj : j.val + 2 < F.h := by omega
      rw [advance, dif_pos hj]; rfl
  | committedAt j t =>
      by_cases hz : j.val = 0
      · rw [advance, dif_pos hz]
        cases t <;> rfl
      · rw [advance, dif_neg hz]; rfl
  | postcommit a t hp =>
      cases a with
      | false => cases t <;> rfl
      | true => exact Bool.noConfusion hw

private theorem sourceTag_gapNext (F : Frame) (s : LifecycleState F) (a : Fin F.h)
    (h : ¬ (a.val = 0)) :
    sourceTag (gapNext F s a) = sourceTag (StopNode.active s) := by
  by_cases hc : gapWork s = true ∧ a = carrierEdge F s
  · rw [gapNext, if_pos hc]
    refine sourceTag_advance F s ?_
    have hv : (carrierEdge F s).val = a.val := congrArg Fin.val hc.2.symm
    rw [hv]
    exact h
  · rw [gapNext, if_neg hc]

private theorem targetTag_gapNext (F : Frame) (s : LifecycleState F) (a : Fin F.h)
    (h : ¬ (a.val + 1 = F.h)) :
    targetTag (gapNext F s a) = targetTag (StopNode.active s) := by
  by_cases hc : gapWork s = true ∧ a = carrierEdge F s
  · rw [gapNext, if_pos hc]
    refine targetTag_advance F s hc.1 ?_
    have hv : (carrierEdge F s).val = a.val := congrArg Fin.val hc.2.symm
    rw [hv]
    exact h
  · rw [gapNext, if_neg hc]

private theorem geometry_frame (F : Frame) (s : LifecycleState F) (a : Fin F.h) :
    ∀ k : Fin (F.h + 1), k.val ≠ a.val → k.val ≠ a.val + 1 →
      tagConfig F (gapNext F s a) k = tagConfig F (StopNode.active s) k := by
  intro k h1 h2
  show tagAt F (gapNext F s a) k.val = tagAt F (StopNode.active s) k.val
  by_cases h0 : k.val = 0
  · rw [tagAt_src F _ k.val h0, tagAt_src F _ k.val h0]
    exact sourceTag_gapNext F s a (by omega)
  · by_cases hh : k.val = F.h
    · rw [tagAt_tgt F _ k.val h0 hh, tagAt_tgt F _ k.val h0 hh]
      exact targetTag_gapNext F s a (by omega)
    · rw [tagAt_mid F _ k.val h0 hh, tagAt_mid F _ k.val h0 hh]
      exact tokenTag_gapNext_off F s a k.val h1 h2

/-- The one-edge geometry obligation for the tag lane. -/
private def GapGeom (F : Frame) (s : LifecycleState F) (a : Fin F.h) : Prop :=
  pairAllowed (tagConfig F (StopNode.active s) (leftEnd F a))
      (tagConfig F (StopNode.active s) (rightEnd F a)) = true ∧
    tagGapStep F (tagConfig F (StopNode.active s)) a = tagConfig F (gapNext F s a)

/-- One branch of the geometry: name the two endpoint tags, check the finite
table entry, and check the two updated endpoints. -/
private theorem geom_of (F : Frame) (s : LifecycleState F) (a : Fin F.h) (lt rt : Tag)
    (hl : tagConfig F (StopNode.active s) (leftEnd F a) = lt)
    (hr : tagConfig F (StopNode.active s) (rightEnd F a) = rt)
    (hok : pairAllowed lt rt = true)
    (hA : tagConfig F (gapNext F s a) (leftEnd F a) = (tagRow lt rt).1)
    (hB : tagConfig F (gapNext F s a) (rightEnd F a) = (tagRow lt rt).2) :
    GapGeom F s a := by
  refine ⟨by rw [hl, hr]; exact hok, ?_⟩
  show pairUpdate F (tagConfig F (StopNode.active s)) a
      (tagRow (tagConfig F (StopNode.active s) (leftEnd F a))
        (tagConfig F (StopNode.active s) (rightEnd F a))) = _
  rw [hl, hr]
  exact pairUpdate_eq F _ _ a (tagRow lt rt) hA hB (geometry_frame F s a)

/-! ### The geometry of every phase, edge by edge -/

private theorem geom_proposalAt (F : Frame) (j a : Fin F.h) :
    GapGeom F (.proposalAt j) a := by
  have hh := F.hpos
  have hja := j.isLt
  have haa := a.isLt
  by_cases hc : a.val = j.val
  · have hcond : gapWork (LifecycleState.proposalAt j) = true ∧
        a = carrierEdge F (LifecycleState.proposalAt j) := ⟨rfl, Fin.ext hc⟩
    by_cases hz : a.val = 0
    · have hjz : j.val = 0 := by omega
      by_cases h1 : a.val + 1 = F.h
      · have hadv : gapNext F (LifecycleState.proposalAt j) a =
            StopNode.active (LifecycleState.protectedWait : LifecycleState F) := by
          rw [gapNext, if_pos hcond, advance,
            dif_neg (show ¬ (j.val + 1 < F.h) by omega), dif_pos hjz]
        refine geom_of F _ a .sHome .tReserved ?_ (right_tgt F _ a h1) rfl ?_ ?_
        · refine (left_src F _ a hz).trans ?_
          show (if j.val = 0 then Tag.sHome else Tag.sProposal) = Tag.sHome
          rw [if_pos hjz]
        · rw [hadv]
          exact left_src F _ a hz
        · rw [hadv]
          exact right_tgt F _ a h1
      · have hj1 : j.val + 1 < F.h := by omega
        have hadv : gapNext F (LifecycleState.proposalAt j) a =
            StopNode.active (LifecycleState.proposalAt ⟨j.val + 1, hj1⟩) := by
          rw [gapNext, if_pos hcond, advance, dif_pos hj1]
        refine geom_of F _ a .sHome .empty ?_ ?_ rfl ?_ ?_
        · refine (left_src F _ a hz).trans ?_
          show (if j.val = 0 then Tag.sHome else Tag.sProposal) = Tag.sHome
          rw [if_pos hjz]
        · exact (right_tok F _ a h1).trans
            (tok_miss F _ _ (show ¬ (a.val + 1 = j.val) by omega))
        · rw [hadv]
          refine (left_src F _ a hz).trans ?_
          show (if j.val + 1 = 0 then Tag.sHome else Tag.sProposal) = _
          rw [if_neg (show ¬ (j.val + 1 = 0) by omega)]; rfl
        · rw [hadv]
          exact (right_tok F _ a h1).trans
            (tok_hit F _ _ (show a.val + 1 = j.val + 1 by omega))
    · by_cases h1 : a.val + 1 = F.h
      · have hadv : gapNext F (LifecycleState.proposalAt j) a =
            StopNode.active (LifecycleState.finalAt ⟨j.val - 1, by omega⟩) := by
          rw [gapNext, if_pos hcond, advance,
            dif_neg (show ¬ (j.val + 1 < F.h) by omega),
            dif_neg (show ¬ (j.val = 0) by omega)]
        refine geom_of F _ a .proposal .tReserved
          ((left_tok F _ a hz).trans (tok_hit F _ _ hc)) (right_tgt F _ a h1) rfl ?_ ?_
        · rw [hadv]
          exact (left_tok F _ a hz).trans
            (tok_hit F _ _ (show a.val = j.val - 1 + 1 by omega))
        · rw [hadv]
          exact right_tgt F _ a h1
      · have hj1 : j.val + 1 < F.h := by omega
        have hadv : gapNext F (LifecycleState.proposalAt j) a =
            StopNode.active (LifecycleState.proposalAt ⟨j.val + 1, hj1⟩) := by
          rw [gapNext, if_pos hcond, advance, dif_pos hj1]
        refine geom_of F _ a .proposal .empty
          ((left_tok F _ a hz).trans (tok_hit F _ _ hc))
          ((right_tok F _ a h1).trans
            (tok_miss F _ _ (show ¬ (a.val + 1 = j.val) by omega))) rfl ?_ ?_
        · rw [hadv]
          exact (left_tok F _ a hz).trans
            (tok_miss F _ _ (show ¬ (a.val = j.val + 1) by omega))
        · rw [hadv]
          exact (right_tok F _ a h1).trans
            (tok_hit F _ _ (show a.val + 1 = j.val + 1 by omega))
  · have hnc : ¬ (gapWork (LifecycleState.proposalAt j) = true ∧
        a = carrierEdge F (LifecycleState.proposalAt j)) := by
      rintro ⟨-, hx⟩
      exact hc (congrArg Fin.val hx)
    have hg : gapNext F (LifecycleState.proposalAt j) a =
        StopNode.active (LifecycleState.proposalAt j) := by
      rw [gapNext, if_neg hnc]
    by_cases hz : a.val = 0
    · have hjz : ¬ (j.val = 0) := by omega
      have hlt : tagConfig F (StopNode.active (LifecycleState.proposalAt j))
          (leftEnd F a) = .sProposal := by
        refine (left_src F _ a hz).trans ?_
        show (if j.val = 0 then Tag.sHome else Tag.sProposal) = Tag.sProposal
        rw [if_neg hjz]
      by_cases h1 : a.val + 1 = F.h
      · exact absurd (show a.val = j.val by omega) hc
      · by_cases hp : a.val + 1 = j.val
        · exact geom_of F _ a .sProposal .proposal hlt
            ((right_tok F _ a h1).trans (tok_hit F _ _ hp)) rfl
            (by rw [hg]; exact hlt)
            (by rw [hg]; exact (right_tok F _ a h1).trans (tok_hit F _ _ hp))
        · exact geom_of F _ a .sProposal .empty hlt
            ((right_tok F _ a h1).trans (tok_miss F _ _ hp)) rfl
            (by rw [hg]; exact hlt)
            (by rw [hg]; exact (right_tok F _ a h1).trans (tok_miss F _ _ hp))
    · have hlt : tagConfig F (StopNode.active (LifecycleState.proposalAt j))
          (leftEnd F a) = .empty := (left_tok F _ a hz).trans (tok_miss F _ _ hc)
      by_cases h1 : a.val + 1 = F.h
      · exact geom_of F _ a .empty .tReserved hlt (right_tgt F _ a h1) rfl
          (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
      · by_cases hp : a.val + 1 = j.val
        · exact geom_of F _ a .empty .proposal hlt
            ((right_tok F _ a h1).trans (tok_hit F _ _ hp)) rfl
            (by rw [hg]; exact hlt)
            (by rw [hg]; exact (right_tok F _ a h1).trans (tok_hit F _ _ hp))
        · exact geom_of F _ a .empty .empty hlt
            ((right_tok F _ a h1).trans (tok_miss F _ _ hp)) rfl
            (by rw [hg]; exact hlt)
            (by rw [hg]; exact (right_tok F _ a h1).trans (tok_miss F _ _ hp))


private theorem tok_success (F : Frame) (k : Nat) :
    tokenTag (StopNode.success : StopNode (LifecycleState F)) k = Tag.empty := rfl

private theorem geom_finalAt (F : Frame) (j : Fin (F.h - 1)) (a : Fin F.h) :
    GapGeom F (.finalAt j) a := by
  have hh := F.hpos
  have hjb := j.isLt
  have haa := a.isLt
  by_cases hc : a.val = j.val
  · have hcond : gapWork (LifecycleState.finalAt j) = true ∧
        a = carrierEdge F (LifecycleState.finalAt j) := ⟨rfl, Fin.ext hc⟩
    have h1 : ¬ (a.val + 1 = F.h) := by omega
    have hrt : tagConfig F (StopNode.active (LifecycleState.finalAt j)) (rightEnd F a)
        = .finalBack :=
      (right_tok F _ a h1).trans (tok_hit F _ _ (show a.val + 1 = j.val + 1 by omega))
    by_cases hz : a.val = 0
    · have hjz : j.val = 0 := by omega
      have hadv : gapNext F (LifecycleState.finalAt j) a =
          StopNode.active (LifecycleState.protectedWait : LifecycleState F) := by
        rw [gapNext, if_pos hcond, advance, dif_pos hjz]
      refine geom_of F _ a .sProposal .finalBack (left_src F _ a hz) hrt rfl ?_ ?_
      · rw [hadv]
        exact left_src F _ a hz
      · rw [hadv]
        exact (right_tok F _ a h1).trans
          (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))
    · have hjz : ¬ (j.val = 0) := by omega
      have hadv : gapNext F (LifecycleState.finalAt j) a =
          StopNode.active (LifecycleState.finalAt ⟨j.val - 1, by omega⟩) := by
        rw [gapNext, if_pos hcond, advance, dif_neg hjz]
      refine geom_of F _ a .empty .finalBack
        ((left_tok F _ a hz).trans
          (tok_miss F _ _ (show ¬ (a.val = j.val + 1) by omega))) hrt rfl ?_ ?_
      · rw [hadv]
        exact (left_tok F _ a hz).trans
          (tok_hit F _ _ (show a.val = j.val - 1 + 1 by omega))
      · rw [hadv]
        exact (right_tok F _ a h1).trans
          (tok_miss F _ _ (show ¬ (a.val + 1 = j.val - 1 + 1) by omega))
  · have hnc : ¬ (gapWork (LifecycleState.finalAt j) = true ∧
        a = carrierEdge F (LifecycleState.finalAt j)) := by
      rintro ⟨-, hx⟩
      exact hc (congrArg Fin.val hx)
    have hg : gapNext F (LifecycleState.finalAt j) a =
        StopNode.active (LifecycleState.finalAt j) := by
      rw [gapNext, if_neg hnc]
    by_cases hz : a.val = 0
    · have h1 : ¬ (a.val + 1 = F.h) := by omega
      have hlt := left_src F (StopNode.active (LifecycleState.finalAt j)) a hz
      have hrt : tagConfig F (StopNode.active (LifecycleState.finalAt j)) (rightEnd F a)
          = .empty :=
        (right_tok F _ a h1).trans
          (tok_miss F _ _ (show ¬ (a.val + 1 = j.val + 1) by omega))
      exact geom_of F _ a .sProposal .empty hlt hrt rfl
        (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)
    · by_cases hp : a.val = j.val + 1
      · have hlt : tagConfig F (StopNode.active (LifecycleState.finalAt j)) (leftEnd F a)
            = .finalBack := (left_tok F _ a hz).trans (tok_hit F _ _ hp)
        by_cases h1 : a.val + 1 = F.h
        · exact geom_of F _ a .finalBack .tHeld hlt (right_tgt F _ a h1) rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
        · have hrt : tagConfig F (StopNode.active (LifecycleState.finalAt j)) (rightEnd F a)
              = .empty :=
            (right_tok F _ a h1).trans
              (tok_miss F _ _ (show ¬ (a.val + 1 = j.val + 1) by omega))
          exact geom_of F _ a .finalBack .empty hlt hrt rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)
      · have hlt : tagConfig F (StopNode.active (LifecycleState.finalAt j)) (leftEnd F a)
            = .empty := (left_tok F _ a hz).trans (tok_miss F _ _ hp)
        by_cases h1 : a.val + 1 = F.h
        · exact geom_of F _ a .empty .tHeld hlt (right_tgt F _ a h1) rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
        · have hrt : tagConfig F (StopNode.active (LifecycleState.finalAt j)) (rightEnd F a)
              = .empty :=
            (right_tok F _ a h1).trans
              (tok_miss F _ _ (show ¬ (a.val + 1 = j.val + 1) by omega))
          exact geom_of F _ a .empty .empty hlt hrt rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)

private theorem geom_protectedWait (F : Frame) (a : Fin F.h) :
    GapGeom F (.protectedWait) a := by
  have hh := F.hpos
  have haa := a.isLt
  by_cases hz : a.val = 0
  · have hcond : gapWork (LifecycleState.protectedWait : LifecycleState F) = true ∧
        a = carrierEdge F (LifecycleState.protectedWait : LifecycleState F) :=
      ⟨rfl, Fin.ext hz⟩
    by_cases h1 : a.val + 1 = F.h
    · have hp : ¬ (1 < F.h) := by omega
      have hadv : gapNext F (LifecycleState.protectedWait : LifecycleState F) a =
          StopNode.active (LifecycleState.postcommit false false (Or.inl rfl)) := by
        rw [gapNext, if_pos hcond, advance, dif_neg hp]; rfl
      refine geom_of F _ a .sProtected .tHeld (left_src F _ a hz)
        (right_tgt F _ a h1) rfl ?_ ?_
      · rw [hadv]
        exact left_src F _ a hz
      · rw [hadv]
        exact right_tgt F _ a h1
    · have hp : 1 < F.h := by omega
      have hadv : gapNext F (LifecycleState.protectedWait : LifecycleState F) a =
          StopNode.active (LifecycleState.commitAt ⟨0, by omega⟩) := by
        rw [gapNext, if_pos hcond, advance, dif_pos hp]
      refine geom_of F _ a .sProtected .empty (left_src F _ a hz)
        ((right_tok F _ a h1).trans
          (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))) rfl ?_ ?_
      · rw [hadv]
        exact left_src F _ a hz
      · rw [hadv]
        exact (right_tok F _ a h1).trans
          (tok_hit F _ _ (show a.val + 1 = 0 + 1 by omega))
  · have hnc : ¬ (gapWork (LifecycleState.protectedWait : LifecycleState F) = true ∧
        a = carrierEdge F (LifecycleState.protectedWait : LifecycleState F)) := by
      rintro ⟨-, hx⟩
      exact hz (congrArg Fin.val hx)
    have hg : gapNext F (LifecycleState.protectedWait : LifecycleState F) a =
        StopNode.active (LifecycleState.protectedWait : LifecycleState F) := by
      rw [gapNext, if_neg hnc]
    have hlt : tagConfig F
        (StopNode.active (LifecycleState.protectedWait : LifecycleState F))
        (leftEnd F a) = .empty :=
      (left_tok F _ a hz).trans (tok_miss F _ _ (show ¬ (a.val = 0) from hz))
    by_cases h1 : a.val + 1 = F.h
    · exact geom_of F _ a .empty .tHeld hlt (right_tgt F _ a h1) rfl
        (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
    · have hrt : tagConfig F
          (StopNode.active (LifecycleState.protectedWait : LifecycleState F))
          (rightEnd F a) = .empty :=
        (right_tok F _ a h1).trans
          (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))
      exact geom_of F _ a .empty .empty hlt hrt rfl
        (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)

private theorem geom_commitAt (F : Frame) (j : Fin (F.h - 1)) (a : Fin F.h) :
    GapGeom F (.commitAt j) a := by
  have hh := F.hpos
  have hjb := j.isLt
  have haa := a.isLt
  by_cases hc : a.val = j.val + 1
  · have hcond : gapWork (LifecycleState.commitAt j) = true ∧
        a = carrierEdge F (LifecycleState.commitAt j) := ⟨rfl, Fin.ext hc⟩
    have hz : ¬ (a.val = 0) := by omega
    have hlt : tagConfig F (StopNode.active (LifecycleState.commitAt j)) (leftEnd F a)
        = .commit := (left_tok F _ a hz).trans (tok_hit F _ _ hc)
    by_cases h1 : a.val + 1 = F.h
    · have hj : ¬ (j.val + 2 < F.h) := by omega
      have hadv : gapNext F (LifecycleState.commitAt j) a =
          StopNode.active (LifecycleState.committedAt j false) := by
        rw [gapNext, if_pos hcond, advance, dif_neg hj]
      refine geom_of F _ a .commit .tHeld hlt (right_tgt F _ a h1) rfl ?_ ?_
      · rw [hadv]
        exact (left_tok F _ a hz).trans (tok_hit F _ _ hc)
      · rw [hadv]
        exact right_tgt F _ a h1
    · have hj : j.val + 2 < F.h := by omega
      have hadv : gapNext F (LifecycleState.commitAt j) a =
          StopNode.active (LifecycleState.commitAt ⟨j.val + 1, by omega⟩) := by
        rw [gapNext, if_pos hcond, advance, dif_pos hj]
      refine geom_of F _ a .commit .empty hlt
        ((right_tok F _ a h1).trans
          (tok_miss F _ _ (show ¬ (a.val + 1 = j.val + 1) by omega))) rfl ?_ ?_
      · rw [hadv]
        exact (left_tok F _ a hz).trans
          (tok_miss F _ _ (show ¬ (a.val = j.val + 1 + 1) by omega))
      · rw [hadv]
        exact (right_tok F _ a h1).trans
          (tok_hit F _ _ (show a.val + 1 = j.val + 1 + 1 by omega))
  · have hnc : ¬ (gapWork (LifecycleState.commitAt j) = true ∧
        a = carrierEdge F (LifecycleState.commitAt j)) := by
      rintro ⟨-, hx⟩
      exact hc (congrArg Fin.val hx)
    have hg : gapNext F (LifecycleState.commitAt j) a =
        StopNode.active (LifecycleState.commitAt j) := by
      rw [gapNext, if_neg hnc]
    by_cases hz : a.val = 0
    · have h1 : ¬ (a.val + 1 = F.h) := by omega
      have hlt := left_src F (StopNode.active (LifecycleState.commitAt j)) a hz
      by_cases hp : a.val + 1 = j.val + 1
      · have hrt : tagConfig F (StopNode.active (LifecycleState.commitAt j)) (rightEnd F a)
            = .commit := (right_tok F _ a h1).trans (tok_hit F _ _ hp)
        exact geom_of F _ a .sCommitting .commit hlt hrt rfl
          (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)
      · have hrt : tagConfig F (StopNode.active (LifecycleState.commitAt j)) (rightEnd F a)
            = .empty := (right_tok F _ a h1).trans (tok_miss F _ _ hp)
        exact geom_of F _ a .sCommitting .empty hlt hrt rfl
          (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)
    · have hlt : tagConfig F (StopNode.active (LifecycleState.commitAt j)) (leftEnd F a)
          = .empty := (left_tok F _ a hz).trans (tok_miss F _ _ hc)
      by_cases h1 : a.val + 1 = F.h
      · exact geom_of F _ a .empty .tHeld hlt (right_tgt F _ a h1) rfl
          (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
      · by_cases hp : a.val + 1 = j.val + 1
        · have hrt : tagConfig F (StopNode.active (LifecycleState.commitAt j)) (rightEnd F a)
              = .commit := (right_tok F _ a h1).trans (tok_hit F _ _ hp)
          exact geom_of F _ a .empty .commit hlt hrt rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)
        · have hrt : tagConfig F (StopNode.active (LifecycleState.commitAt j)) (rightEnd F a)
              = .empty := (right_tok F _ a h1).trans (tok_miss F _ _ hp)
          exact geom_of F _ a .empty .empty hlt hrt rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)

private theorem geom_committedAt (F : Frame) (j : Fin (F.h - 1)) (t : Bool) (a : Fin F.h) :
    GapGeom F (.committedAt j t) a := by
  have hh := F.hpos
  have hjb := j.isLt
  have haa := a.isLt
  by_cases hc : a.val = j.val
  · have hcond : gapWork (LifecycleState.committedAt j t) = true ∧
        a = carrierEdge F (LifecycleState.committedAt j t) := ⟨rfl, Fin.ext hc⟩
    have h1 : ¬ (a.val + 1 = F.h) := by omega
    have hrt : tagConfig F (StopNode.active (LifecycleState.committedAt j t)) (rightEnd F a)
        = .committedBack :=
      (right_tok F _ a h1).trans (tok_hit F _ _ (show a.val + 1 = j.val + 1 by omega))
    by_cases hz : a.val = 0
    · have hjz : j.val = 0 := by omega
      have hadv : gapNext F (LifecycleState.committedAt j t) a =
          StopNode.active (LifecycleState.postcommit false t (Or.inl rfl)) := by
        rw [gapNext, if_pos hcond, advance, dif_pos hjz]; rfl
      refine geom_of F _ a .sCommitting .committedBack (left_src F _ a hz) hrt rfl ?_ ?_
      · rw [hadv]
        exact left_src F _ a hz
      · rw [hadv]
        exact (right_tok F _ a h1).trans
          (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))
    · have hjz : ¬ (j.val = 0) := by omega
      have hadv : gapNext F (LifecycleState.committedAt j t) a =
          StopNode.active (LifecycleState.committedAt ⟨j.val - 1, by omega⟩ t) := by
        rw [gapNext, if_pos hcond, advance, dif_neg hjz]
      refine geom_of F _ a .empty .committedBack
        ((left_tok F _ a hz).trans
          (tok_miss F _ _ (show ¬ (a.val = j.val + 1) by omega))) hrt rfl ?_ ?_
      · rw [hadv]
        exact (left_tok F _ a hz).trans
          (tok_hit F _ _ (show a.val = j.val - 1 + 1 by omega))
      · rw [hadv]
        exact (right_tok F _ a h1).trans
          (tok_miss F _ _ (show ¬ (a.val + 1 = j.val - 1 + 1) by omega))
  · have hnc : ¬ (gapWork (LifecycleState.committedAt j t) = true ∧
        a = carrierEdge F (LifecycleState.committedAt j t)) := by
      rintro ⟨-, hx⟩
      exact hc (congrArg Fin.val hx)
    have hg : gapNext F (LifecycleState.committedAt j t) a =
        StopNode.active (LifecycleState.committedAt j t) := by
      rw [gapNext, if_neg hnc]
    by_cases hz : a.val = 0
    · have h1 : ¬ (a.val + 1 = F.h) := by omega
      have hlt := left_src F (StopNode.active (LifecycleState.committedAt j t)) a hz
      have hrt : tagConfig F (StopNode.active (LifecycleState.committedAt j t)) (rightEnd F a)
          = .empty :=
        (right_tok F _ a h1).trans
          (tok_miss F _ _ (show ¬ (a.val + 1 = j.val + 1) by omega))
      exact geom_of F _ a .sCommitting .empty hlt hrt rfl
        (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)
    · by_cases hp : a.val = j.val + 1
      · have hlt : tagConfig F (StopNode.active (LifecycleState.committedAt j t))
            (leftEnd F a) = .committedBack := (left_tok F _ a hz).trans (tok_hit F _ _ hp)
        by_cases h1 : a.val + 1 = F.h
        · cases t with
          | false =>
              exact geom_of F _ a .committedBack .tCommitted hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
          | true =>
              exact geom_of F _ a .committedBack .tClean hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
        · have hrt : tagConfig F (StopNode.active (LifecycleState.committedAt j t))
              (rightEnd F a) = .empty :=
            (right_tok F _ a h1).trans
              (tok_miss F _ _ (show ¬ (a.val + 1 = j.val + 1) by omega))
          exact geom_of F _ a .committedBack .empty hlt hrt rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)
      · have hlt : tagConfig F (StopNode.active (LifecycleState.committedAt j t))
            (leftEnd F a) = .empty := (left_tok F _ a hz).trans (tok_miss F _ _ hp)
        by_cases h1 : a.val + 1 = F.h
        · cases t with
          | false =>
              exact geom_of F _ a .empty .tCommitted hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
          | true =>
              exact geom_of F _ a .empty .tClean hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
        · have hrt : tagConfig F (StopNode.active (LifecycleState.committedAt j t))
              (rightEnd F a) = .empty :=
            (right_tok F _ a h1).trans
              (tok_miss F _ _ (show ¬ (a.val + 1 = j.val + 1) by omega))
          exact geom_of F _ a .empty .empty hlt hrt rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)

private theorem geom_postcommit (F : Frame) (ack tgt : Bool)
    (hpend : ack = false ∨ tgt = false) (a : Fin F.h) :
    GapGeom F (.postcommit ack tgt hpend) a := by
  have hh := F.hpos
  have haa := a.isLt
  cases ack with
  | true =>
      have hnc : ¬ (gapWork (LifecycleState.postcommit true tgt hpend : LifecycleState F) = true ∧
          a = carrierEdge F (LifecycleState.postcommit true tgt hpend)) := by
        rintro ⟨hw, -⟩
        exact Bool.noConfusion hw
      have hg : gapNext F (LifecycleState.postcommit true tgt hpend) a =
          StopNode.active (LifecycleState.postcommit true tgt hpend) := by
        rw [gapNext, if_neg hnc]
      by_cases hz : a.val = 0
      · have hlt := left_src F
          (StopNode.active (LifecycleState.postcommit true tgt hpend)) a hz
        by_cases h1 : a.val + 1 = F.h
        · cases tgt with
          | false =>
              exact geom_of F _ a .sClean .tCommitted hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
          | true =>
              exact geom_of F _ a .sClean .tClean hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
        · have hrt : tagConfig F
              (StopNode.active (LifecycleState.postcommit true tgt hpend))
              (rightEnd F a) = .empty :=
            (right_tok F _ a h1).trans
              (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))
          exact geom_of F _ a .sClean .empty hlt hrt rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)
      · have hlt : tagConfig F
            (StopNode.active (LifecycleState.postcommit true tgt hpend))
            (leftEnd F a) = .empty :=
          (left_tok F _ a hz).trans (tok_miss F _ _ (show ¬ (a.val = 0) from hz))
        by_cases h1 : a.val + 1 = F.h
        · cases tgt with
          | false =>
              exact geom_of F _ a .empty .tCommitted hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
          | true =>
              exact geom_of F _ a .empty .tClean hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
        · have hrt : tagConfig F
              (StopNode.active (LifecycleState.postcommit true tgt hpend))
              (rightEnd F a) = .empty :=
            (right_tok F _ a h1).trans
              (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))
          exact geom_of F _ a .empty .empty hlt hrt rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)
  | false =>
      by_cases hz : a.val = 0
      · have hcond : gapWork (LifecycleState.postcommit false tgt hpend : LifecycleState F) = true ∧
            a = carrierEdge F (LifecycleState.postcommit false tgt hpend) :=
          ⟨rfl, Fin.ext hz⟩
        have hlt := left_src F
          (StopNode.active (LifecycleState.postcommit false tgt hpend)) a hz
        cases tgt with
        | false =>
            have hadv : gapNext F (LifecycleState.postcommit false false hpend) a =
                StopNode.active (LifecycleState.postcommit true false (Or.inr rfl)) := by
              rw [gapNext, if_pos hcond, advance]; rfl
            by_cases h1 : a.val + 1 = F.h
            · refine geom_of F _ a .sReceived .tCommitted hlt
                (right_tgt F _ a h1) rfl ?_ ?_
              · rw [hadv]
                exact left_src F _ a hz
              · rw [hadv]
                exact right_tgt F _ a h1
            · have hrt : tagConfig F
                  (StopNode.active (LifecycleState.postcommit false false hpend))
                  (rightEnd F a) = .empty :=
                (right_tok F _ a h1).trans
                  (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))
              refine geom_of F _ a .sReceived .empty hlt hrt rfl ?_ ?_
              · rw [hadv]
                exact left_src F _ a hz
              · rw [hadv]
                exact (right_tok F _ a h1).trans
                  (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))
        | true =>
            have hadv : gapNext F (LifecycleState.postcommit false true hpend) a =
                (StopNode.success : StopNode (LifecycleState F)) := by
              rw [gapNext, if_pos hcond, advance]; rfl
            by_cases h1 : a.val + 1 = F.h
            · refine geom_of F _ a .sReceived .tClean hlt (right_tgt F _ a h1) rfl ?_ ?_
              · rw [hadv]
                exact tagAt_src F _ a.val hz
              · rw [hadv]
                exact tagAt_tgt F _ (a.val + 1) (by omega) h1
            · have hrt : tagConfig F
                  (StopNode.active (LifecycleState.postcommit false true hpend))
                  (rightEnd F a) = .empty :=
                (right_tok F _ a h1).trans
                  (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))
              refine geom_of F _ a .sReceived .empty hlt hrt rfl ?_ ?_
              · rw [hadv]
                exact tagAt_src F _ a.val hz
              · rw [hadv]
                exact (tagAt_mid F _ (a.val + 1) (by omega) h1).trans
                  (tok_success F (a.val + 1))
      · have hnc : ¬ (gapWork (LifecycleState.postcommit false tgt hpend : LifecycleState F) = true ∧
            a = carrierEdge F (LifecycleState.postcommit false tgt hpend)) := by
          rintro ⟨-, hx⟩
          exact hz (congrArg Fin.val hx)
        have hg : gapNext F (LifecycleState.postcommit false tgt hpend) a =
            StopNode.active (LifecycleState.postcommit false tgt hpend) := by
          rw [gapNext, if_neg hnc]
        have hlt : tagConfig F
            (StopNode.active (LifecycleState.postcommit false tgt hpend))
            (leftEnd F a) = .empty :=
          (left_tok F _ a hz).trans (tok_miss F _ _ (show ¬ (a.val = 0) from hz))
        by_cases h1 : a.val + 1 = F.h
        · cases tgt with
          | false =>
              exact geom_of F _ a .empty .tCommitted hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
          | true =>
              exact geom_of F _ a .empty .tClean hlt (right_tgt F _ a h1) rfl
                (by rw [hg]; exact hlt) (by rw [hg]; exact right_tgt F _ a h1)
        · have hrt : tagConfig F
              (StopNode.active (LifecycleState.postcommit false tgt hpend))
              (rightEnd F a) = .empty :=
            (right_tok F _ a h1).trans
              (tok_miss F _ _ (show ¬ (a.val + 1 = 0) from Nat.succ_ne_zero _))
          exact geom_of F _ a .empty .empty hlt hrt rfl
            (by rw [hg]; exact hlt) (by rw [hg]; exact hrt)

/-- Every phase, on every gap edge, satisfies the one-edge tag geometry. -/
private theorem gap_geom (F : Frame) (s : LifecycleState F) (a : Fin F.h) :
    GapGeom F s a := by
  cases s with
  | proposalAt j => exact geom_proposalAt F j a
  | finalAt j => exact geom_finalAt F j a
  | protectedWait => exact geom_protectedWait F a
  | commitAt j => exact geom_commitAt F j a
  | committedAt j t => exact geom_committedAt F j t a
  | postcommit ack tgt hpend => exact geom_postcommit F ack tgt hpend a

/-! ### The target's own residue service edge -/

private theorem cleanup_sourceTag (F : Frame) (s : LifecycleState F) :
    sourceTag (cleanupAttempt F s) = sourceTag (StopNode.active s) := by
  cases s with
  | proposalAt j => rfl
  | finalAt j => rfl
  | protectedWait => rfl
  | commitAt j => rfl
  | committedAt j t => rfl
  | postcommit ack tgt hpend =>
      cases ack with
      | false => rfl
      | true =>
          cases tgt with
          | false => rfl
          | true =>
              exact hpend.elim (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)

private theorem cleanup_tokenTag (F : Frame) (s : LifecycleState F) (k : Nat) :
    tokenTag (cleanupAttempt F s) k = tokenTag (StopNode.active s) k := by
  cases s with
  | proposalAt j => rfl
  | finalAt j => rfl
  | protectedWait => rfl
  | commitAt j => rfl
  | committedAt j t => rfl
  | postcommit ack tgt hpend =>
      cases ack with
      | false => rfl
      | true =>
          cases tgt with
          | false =>
              show Tag.empty = (if k = 0 then Tag.empty else Tag.empty)
              by_cases hk : k = 0
              · rw [if_pos hk]
              · rw [if_neg hk]
          | true =>
              exact hpend.elim (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)

private theorem cleanup_targetTag (F : Frame) (s : LifecycleState F) :
    targetTag (cleanupAttempt F s) =
      (tagRow (targetTag (StopNode.active s)) .empty).1 := by
  cases s with
  | proposalAt j => rfl
  | finalAt j => rfl
  | protectedWait => rfl
  | commitAt j => rfl
  | committedAt j t => cases t <;> rfl
  | postcommit ack tgt hpend =>
      cases ack with
      | false => cases tgt <;> rfl
      | true =>
          cases tgt with
          | false => rfl
          | true =>
              exact hpend.elim (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)

private theorem isTargetTag_targetTag (F : Frame) (x : StopNode (LifecycleState F)) :
    isTargetTag (targetTag x) = true := by
  cases x with
  | active s =>
      cases s with
      | proposalAt j => rfl
      | finalAt j => rfl
      | protectedWait => rfl
      | commitAt j => rfl
      | committedAt j t => cases t <;> rfl
      | postcommit ack tgt hpend => cases tgt <;> rfl
  | success => rfl
  | failure => rfl

private theorem cleanup_geom (F : Frame) (s : LifecycleState F) :
    isTargetTag (tagConfig F (StopNode.active s) (targetSite F)) = true ∧
      tagCleanupStep F (tagConfig F (StopNode.active s)) =
        tagConfig F (cleanupAttempt F s) := by
  refine ⟨?_, ?_⟩
  · rw [tagConfig_targetSite]
    exact isTargetTag_targetTag F _
  · show targetUpdate F (tagConfig F (StopNode.active s))
      (tagRow (tagConfig F (StopNode.active s) (targetSite F)) Tag.empty).1 = _
    refine targetUpdate_eq F _ _ _ ?_ ?_
    · rw [tagConfig_targetSite, tagConfig_targetSite]
      exact cleanup_targetTag F s
    · intro k hk
      show tagAt F (cleanupAttempt F s) k.val = tagAt F (StopNode.active s) k.val
      by_cases h0 : k.val = 0
      · rw [tagAt_src F _ k.val h0, tagAt_src F _ k.val h0]
        exact cleanup_sourceTag F s
      · rw [tagAt_mid F _ k.val h0 hk, tagAt_mid F _ k.val h0 hk]
        exact cleanup_tokenTag F s k.val

/-! ### The tag update and the literal update are the same update -/

private theorem pairUpdate_render (F : Frame) (cfg : Fin (F.h + 1) → Tag) (a : Fin F.h)
    (p : Tag × Tag) :
    pairUpdate F (fun k => render F (cfg k)) a (render F p.1, render F p.2) =
      fun k => render F (pairUpdate F cfg a p k) := by
  funext k
  show (if k.val = a.val then render F p.1
      else if k.val = a.val + 1 then render F p.2 else render F (cfg k)) =
    render F (if k.val = a.val then p.1 else if k.val = a.val + 1 then p.2 else cfg k)
  by_cases h0 : k.val = a.val
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : k.val = a.val + 1
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]

private theorem targetUpdate_render (F : Frame) (cfg : Fin (F.h + 1) → Tag) (v : Tag) :
    targetUpdate F (fun k => render F (cfg k)) (render F v) =
      fun k => render F (targetUpdate F cfg v k) := by
  funext k
  show (if k.val = F.h then render F v else render F (cfg k)) =
    render F (if k.val = F.h then v else cfg k)
  by_cases hk : k.val = F.h
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk]

/-! ## The lifecycle walk *is* the imported literal row -/

/-- **Row encoding.**  On every scheduled gap edge the two encoded endpoints
are an allowed clean-lane pair, and the walk's own transition is exactly the
imported total dispatcher `commitRow` fired there, with every other site of the
gap framed.  Nothing is asserted outside the finite `pairAllowed` table.  The
`h = 1` instances are the fused direct rows, where the right endpoint of edge
`0` is the target root itself. -/
theorem lifecycleStep_encodes_rows {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (a : Fin F.h) :
    pairAllowed (tagConfig F (StopNode.active s) (leftEnd F a))
        (tagConfig F (StopNode.active s) (rightEnd F a)) = true ∧
      encodeLife F (lifecycleStep L s (L.embedding.edgeAt a)) =
        pairUpdate F (encodeLife F (StopNode.active s)) a
          (commitRow (encodeLife F (StopNode.active s) (leftEnd F a))
            (encodeLife F (StopNode.active s) (rightEnd F a))) := by
  obtain ⟨hok, hstep⟩ := gap_geom F s a
  refine ⟨hok, ?_⟩
  rw [lifecycleStep_gap]
  show (fun k => render F (tagConfig F (gapNext F s a) k)) =
    pairUpdate F (fun k => render F (tagConfig F (StopNode.active s) k)) a
      (commitRow (render F (tagConfig F (StopNode.active s) (leftEnd F a)))
        (render F (tagConfig F (StopNode.active s) (rightEnd F a))))
  rw [tagRow_literal F _ _ hok, ← hstep]
  exact (pairUpdate_render F (tagConfig F (StopNode.active s)) a
    (tagRow (tagConfig F (StopNode.active s) (leftEnd F a))
      (tagConfig F (StopNode.active s) (rightEnd F a)))).symm

/-- **Service encoding.**  On the target's own outgoing edge the left endpoint
is always a target tag, the row writes only that site, and the neighbour --
which is outside the selected gap and therefore arbitrary -- is framed. -/
theorem lifecycleStep_encodes_target_service {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (b : CNode) :
    isTargetTag (tagConfig F (StopNode.active s) (targetSite F)) = true ∧
      commitRow (encodeLife F (StopNode.active s) (targetSite F)) b =
        (encodeLife F (lifecycleStep L s L.targetEdge) (targetSite F), b) ∧
      encodeLife F (lifecycleStep L s L.targetEdge) =
        targetUpdate F (encodeLife F (StopNode.active s))
          (commitRow (encodeLife F (StopNode.active s) (targetSite F)) b).1 := by
  obtain ⟨htgt, hstep⟩ := cleanup_geom F s
  have hrow := target_tag_service F
    (tagConfig F (StopNode.active s) (targetSite F)) b htgt
  have hv : tagConfig F (cleanupAttempt F s) (targetSite F) =
      (tagRow (tagConfig F (StopNode.active s) (targetSite F)) Tag.empty).1 := by
    rw [← hstep]
    show (if (targetSite F).val = F.h then
        (tagRow (tagConfig F (StopNode.active s) (targetSite F)) Tag.empty).1
      else tagConfig F (StopNode.active s) (targetSite F)) =
      (tagRow (tagConfig F (StopNode.active s) (targetSite F)) Tag.empty).1
    rw [if_pos (show (targetSite F).val = F.h from rfl)]
  refine ⟨htgt, ?_, ?_⟩
  · rw [lifecycleStep_target]
    show commitRow (render F (tagConfig F (StopNode.active s) (targetSite F))) b =
      (render F (tagConfig F (cleanupAttempt F s) (targetSite F)), b)
    rw [hv]
    exact hrow
  · rw [lifecycleStep_target]
    show (fun k => render F (tagConfig F (cleanupAttempt F s) k)) =
      targetUpdate F (fun k => render F (tagConfig F (StopNode.active s) k))
        (commitRow (render F (tagConfig F (StopNode.active s) (targetSite F))) b).1
    rw [hrow, ← hstep]
    exact (targetUpdate_render F (tagConfig F (StopNode.active s))
      (tagRow (tagConfig F (StopNode.active s) (targetSite F)) Tag.empty).1).symm

/-! ## Transported literal safety on the encoded lane

Each statement is the imported `ShortGapCaptureCommitRows` row theorem read at
the two encoded endpoints of a scheduled gap edge.  Nothing new is proved about
the dispatcher; the content is that the lifecycle's own configuration is a
legal argument for it. -/

/-- The commit literal (both the `h > 1` commit-at-target row and the fused
`h = 1` direct row) still needs the extended reserved lease, a live target
leader and an accepted raw target at the right endpoint. -/
theorem lifecycle_commit_needs_lease (F : Frame) (x : StopNode (LifecycleState F))
    (a : Fin F.h)
    (h : IsCommitLiteral (commitRule (encodeLife F x (leftEnd F a))
      (encodeLife F x (rightEnd F a)))) :
    (encodeLife F x (rightEnd F a)).incoming = CommitIn.reserved ∧
      (encodeLife F x (rightEnd F a)).carrier = CommitCarrier.none ∧
      (encodeLife F x (rightEnd F a)).leader = true ∧
      rawTarget (encodeLife F x (rightEnd F a)).raw = true := by
  obtain ⟨h1, h2, h3, cw, out, h4⟩ := commit_needs_lease _ _ h
  exact ⟨h1, h2, h3, by rw [h4]; rfl⟩

/-- On every scheduled gap edge the target leader falls exactly on the commit
literal; in particular no other lifecycle row can delete a leader. -/
theorem lifecycle_targetLeader_falls_iff_commit (F : Frame)
    (x : StopNode (LifecycleState F)) (a : Fin F.h) :
    ((commitRow (encodeLife F x (leftEnd F a))
          (encodeLife F x (rightEnd F a))).2.leader ≠
        (encodeLife F x (rightEnd F a)).leader ↔
      IsCommitLiteral (commitRule (encodeLife F x (leftEnd F a))
        (encodeLife F x (rightEnd F a)))) ∧
    (((encodeLife F x (rightEnd F a)).leader = true ∧
        (commitRow (encodeLife F x (leftEnd F a))
          (encodeLife F x (rightEnd F a))).2.leader = false) ↔
      IsCommitLiteral (commitRule (encodeLife F x (leftEnd F a))
        (encodeLife F x (rightEnd F a)))) :=
  targetLeader_falls_iff_commit_literal _ _

/-- A deposited `protectedFinal` control is never returned to `capturing` by
any lifecycle row: the abort lane is closed at both endpoints. -/
theorem lifecycle_protected_no_abort (F : Frame)
    (x : StopNode (LifecycleState F)) (a : Fin F.h) :
    ((encodeLife F x (leftEnd F a)).outgoing = CommitCtl.protectedFinal →
        (commitRow (encodeLife F x (leftEnd F a))
          (encodeLife F x (rightEnd F a))).1.outgoing ≠ CommitCtl.capturing) ∧
    ((encodeLife F x (rightEnd F a)).outgoing = CommitCtl.protectedFinal →
        (commitRow (encodeLife F x (leftEnd F a))
          (encodeLife F x (rightEnd F a))).2.outgoing ≠ CommitCtl.capturing) :=
  protected_no_abort_literal _ _

/-- Spent target state and a completed source receipt survive every lifecycle
row, at either endpoint. -/
theorem lifecycle_postcommit_irreversible (F : Frame)
    (x : StopNode (LifecycleState F)) (a : Fin F.h) :
    (PostCommitted (encodeLife F x (leftEnd F a)) →
        PostCommitted (commitRow (encodeLife F x (leftEnd F a))
          (encodeLife F x (rightEnd F a))).1) ∧
    (PostCommitted (encodeLife F x (rightEnd F a)) →
        PostCommitted (commitRow (encodeLife F x (leftEnd F a))
          (encodeLife F x (rightEnd F a))).2) ∧
    (ReceiptDone (encodeLife F x (leftEnd F a)) →
        ReceiptDone (commitRow (encodeLife F x (leftEnd F a))
          (encodeLife F x (rightEnd F a))).1) ∧
    (ReceiptDone (encodeLife F x (rightEnd F a)) →
        ReceiptDone (commitRow (encodeLife F x (leftEnd F a))
          (encodeLife F x (rightEnd F a))).2) :=
  postcommit_irreversible_literal _ _

/-! ## Refinement of the semantic clean-commit lifecycle -/

open ShortGapCaptureLifecycle (Control Action Trace) in
/-- The semantic control class of a walk node.  `proposalAt 0` is still the
pre-launch candidate: position `0` is the source root and its outgoing wire
is `home` until the first row on edge `0` fires. -/
def control (F : Frame) : StopNode (LifecycleState F) → Control
  | .active (.proposalAt j) => if j.val = 0 then .candidate else .proposalOutbound
  | .active (.finalAt _) => .finalReturning
  | .active .protectedWait => .finalReady
  | .active (.commitAt _) => .protectedCommitOutbound
  | .active (.committedAt _ t) => .committed ⟨true, !t⟩
  | .active (.postcommit a t _) => .committed ⟨!a, !t⟩
  | .success => .clean .deleted
  | .failure => .clean .kept

open ShortGapCaptureLifecycle (Control Action Trace) in
private theorem control_prop_zero (F : Frame) (j : Fin F.h) (h : j.val = 0) :
    control F (StopNode.active (LifecycleState.proposalAt j)) = Control.candidate := by
  show (if j.val = 0 then Control.candidate else Control.proposalOutbound) = _
  rw [if_pos h]

open ShortGapCaptureLifecycle (Control Action Trace) in
private theorem control_prop_succ (F : Frame) (j : Fin F.h) (h : ¬ (j.val = 0)) :
    control F (StopNode.active (LifecycleState.proposalAt j)) = Control.proposalOutbound := by
  show (if j.val = 0 then Control.candidate else Control.proposalOutbound) = _
  rw [if_neg h]

open ShortGapCaptureLifecycle (Control Action Trace) in
private theorem trace_append {c1 c2 c3 : Control} {as bs : List Action}
    (h1 : Trace c1 as c2) : Trace c2 bs c3 → Trace c1 (as ++ bs) c3 := by
  induction h1 with
  | refl _ => exact fun h => h
  | cons head _ ih => exact fun h => .cons head (ih h)

open ShortGapCaptureLifecycle (Control Action Trace) in
/-- Every gap-edge firing is refined by an accepted semantic macro trace.
`h = 1` fuses several macro actions into one physical row; that is exactly the
multi-action list this existential provides. -/
private theorem advance_refines (F : Frame) (s : LifecycleState F) :
    ∃ acts : List Action,
      Trace (control F (StopNode.active s)) acts (control F (advance F s)) := by
  cases s with
  | proposalAt j =>
      have hb := j.isLt
      by_cases hj : j.val + 1 < F.h
      · rw [advance, dif_pos hj,
          control_prop_succ F ⟨j.val + 1, hj⟩ (Nat.succ_ne_zero _)]
        by_cases hz : j.val = 0
        · rw [control_prop_zero F j hz]
          exact ⟨[.launchProposal], .cons .launchProposal (.refl _)⟩
        · rw [control_prop_succ F j hz]
          exact ⟨[], .refl _⟩
      · by_cases hz : j.val = 0
        · rw [advance, dif_neg hj, dif_pos hz, control_prop_zero F j hz]
          exact ⟨[.launchProposal, .proposalAtCleanTarget, .returnFinal],
            .cons .launchProposal (.cons .proposalAtCleanTarget
              (.cons .returnFinal (.refl _)))⟩
        · rw [advance, dif_neg hj, dif_neg hz, control_prop_succ F j hz]
          exact ⟨[.proposalAtCleanTarget], .cons .proposalAtCleanTarget (.refl _)⟩
  | finalAt j =>
      have hb := j.isLt
      by_cases hz : j.val = 0
      · rw [advance, dif_pos hz]
        exact ⟨[.returnFinal], .cons .returnFinal (.refl _)⟩
      · rw [advance, dif_neg hz]
        exact ⟨[], .refl _⟩
  | protectedWait =>
      by_cases hp : 1 < F.h
      · rw [advance, dif_pos hp]
        exact ⟨[.acceptFinal], .cons .acceptFinal (.refl _)⟩
      · rw [advance, dif_neg hp]
        exact ⟨[.acceptFinal, .commitAtTarget],
          .cons .acceptFinal (.cons .commitAtTarget (.refl _))⟩
  | commitAt j =>
      have hb := j.isLt
      by_cases hj : j.val + 2 < F.h
      · rw [advance, dif_pos hj]
        exact ⟨[], .refl _⟩
      · rw [advance, dif_neg hj]
        exact ⟨[.commitAtTarget], .cons .commitAtTarget (.refl _)⟩
  | committedAt j t =>
      have hb := j.isLt
      by_cases hz : j.val = 0
      · rw [advance, dif_pos hz]
        cases t <;> exact ⟨[], .refl _⟩
      · rw [advance, dif_neg hz]
        exact ⟨[], .refl _⟩
  | postcommit a t hp =>
      cases a with
      | false =>
          cases t with
          | false =>
              exact ⟨[.dischargePostCommit .sourceAck],
                .cons (.dischargePostCommit ⟨true, true⟩ .sourceAck rfl) (.refl _)⟩
          | true =>
              exact ⟨[.dischargePostCommit .sourceAck, .finishCommitted],
                .cons (.dischargePostCommit ⟨true, false⟩ .sourceAck rfl)
                  (.cons (.finishCommitted ⟨false, false⟩ ⟨rfl, rfl⟩) (.refl _))⟩
      | true =>
          cases t with
          | false =>
              exact ⟨[.dischargePostCommit .targetCleanup, .finishCommitted],
                .cons (.dischargePostCommit ⟨false, true⟩ .targetCleanup rfl)
                  (.cons (.finishCommitted ⟨false, false⟩ ⟨rfl, rfl⟩) (.refl _))⟩
          | true =>
              exact ⟨[.finishCommitted],
                .cons (.finishCommitted ⟨false, false⟩ ⟨rfl, rfl⟩) (.refl _)⟩

open ShortGapCaptureLifecycle (Control Action Trace) in
/-- The target's own residue discharge is refined the same way. -/
private theorem cleanup_refines (F : Frame) (s : LifecycleState F) :
    ∃ acts : List Action,
      Trace (control F (StopNode.active s)) acts (control F (cleanupAttempt F s)) := by
  cases s with
  | proposalAt j => exact ⟨[], .refl _⟩
  | finalAt j => exact ⟨[], .refl _⟩
  | protectedWait => exact ⟨[], .refl _⟩
  | commitAt j => exact ⟨[], .refl _⟩
  | committedAt j t =>
      cases t with
      | false =>
          exact ⟨[.dischargePostCommit .targetCleanup],
            .cons (.dischargePostCommit ⟨true, true⟩ .targetCleanup rfl) (.refl _)⟩
      | true => exact ⟨[], .refl _⟩
  | postcommit a t hp =>
      cases a with
      | false =>
          cases t with
          | false =>
              exact ⟨[.dischargePostCommit .targetCleanup],
                .cons (.dischargePostCommit ⟨true, true⟩ .targetCleanup rfl) (.refl _)⟩
          | true => exact ⟨[], .refl _⟩
      | true =>
          cases t with
          | false =>
              exact ⟨[.dischargePostCommit .targetCleanup, .finishCommitted],
                .cons (.dischargePostCommit ⟨false, true⟩ .targetCleanup rfl)
                  (.cons (.finishCommitted ⟨false, false⟩ ⟨rfl, rfl⟩) (.refl _))⟩
          | true =>
              exact ⟨[.finishCommitted],
                .cons (.finishCommitted ⟨false, false⟩ ⟨rfl, rfl⟩) (.refl _)⟩

open ShortGapCaptureLifecycle (Control Action Trace) in
/-- One ambient scheduler edge, whatever it is, is refined by an accepted
semantic trace. -/
theorem lifecycleStep_refines {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (e : Fin n) :
    ∃ acts : List Action,
      Trace (control F (StopNode.active s)) acts (control F (lifecycleStep L s e)) := by
  classical
  by_cases hx : ∃ a : Fin F.h, L.embedding.edgeAt a = e
  · simp only [lifecycleStep, dif_pos hx]
    by_cases hc : gapWork s = true ∧ hx.choose = carrierEdge F s
    · rw [gapNext, if_pos hc]
      exact advance_refines F s
    · rw [gapNext, if_neg hc]
      exact ⟨[], .refl _⟩
  · simp only [lifecycleStep, dif_neg hx]
    by_cases he : e = L.targetEdge
    · rw [if_pos he]
      exact cleanup_refines F s
    · rw [if_neg he]
      exact ⟨[], .refl _⟩

/-- One ambient edge applied to a stopped node. -/
noncomputable def stepNode {F : Frame} {n : Nat} (L : Layout F n) :
    StopNode (LifecycleState F) → Fin n → StopNode (LifecycleState F)
  | .active s, e => lifecycleStep L s e
  | .success, _ => .success
  | .failure, _ => .failure

/-- A finite ambient schedule applied to the lifecycle. -/
noncomputable def runEdges {F : Frame} {n : Nat} (L : Layout F n) :
    StopNode (LifecycleState F) → List (Fin n) → StopNode (LifecycleState F)
  | x, [] => x
  | x, e :: es => runEdges L (stepNode L x e) es

open ShortGapCaptureLifecycle (Control Action Trace) in
private theorem stepNode_refines {F : Frame} {n : Nat}
    (L : Layout F n) (x : StopNode (LifecycleState F)) (e : Fin n) :
    ∃ acts : List Action, Trace (control F x) acts (control F (stepNode L x e)) := by
  cases x with
  | active s => exact lifecycleStep_refines L s e
  | success => exact ⟨[], .refl _⟩
  | failure => exact ⟨[], .refl _⟩

open ShortGapCaptureLifecycle (Control Action Trace) in
private theorem runEdges_refines {F : Frame} {n : Nat}
    (L : Layout F n) (es : List (Fin n)) (x : StopNode (LifecycleState F)) :
    ∃ acts : List Action, Trace (control F x) acts (control F (runEdges L x es)) := by
  induction es generalizing x with
  | nil => exact ⟨[], .refl _⟩
  | cons e es ih =>
      obtain ⟨as, ha⟩ := stepNode_refines L x e
      obtain ⟨bs, hb⟩ := ih (stepNode L x e)
      exact ⟨as ++ bs, trace_append ha hb⟩

open ShortGapCaptureLifecycle (Control Action Trace) in
/-- **Refinement.**  Whatever finite ambient schedule the adversary plays, the
control class of the resulting walk node is reachable from `candidate` by an
accepted semantic macro trace of `ShortGapCaptureLifecycle.Step`.  The physical
walk therefore adds no behaviour outside the accepted lifecycle. -/
theorem lifecycle_refines_cleanCommitTrace {F : Frame} {n : Nat}
    (L : Layout F n) (es : List (Fin n)) :
    ∃ acts : List Action,
      Trace Control.candidate acts (control F (runEdges L (.active (lifecycleStart F)) es)) := by
  have h := runEdges_refines L es (StopNode.active (lifecycleStart F))
  have h0 : control F (StopNode.active (lifecycleStart F)) = Control.candidate :=
    control_prop_zero F ⟨0, F.hpos⟩ rfl
  rw [h0] at h
  exact h

open ShortGapCaptureLifecycle (Control Action Trace) in
/-- Reaching the walk's `success` reproduces exactly the endpoints of the
imported semantic witness `ShortGapCaptureLifecycle.cleanCommitTrace`:
`candidate` to `clean deleted`. -/
theorem lifecycle_success_refines_cleanCommit {F : Frame} {n : Nat}
    (L : Layout F n) (es : List (Fin n))
    (h : runEdges L (.active (lifecycleStart F)) es = .success) :
    ∃ acts : List Action,
      Trace Control.candidate acts (.clean .deleted) := by
  have hr := lifecycle_refines_cleanCommitTrace L es
  rw [h] at hr
  exact hr

/-! ## Endpoint reads of the encoded row, and the safety statements they carry -/

theorem lifecycleStep_left_endpoint {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (a : Fin F.h) :
    encodeLife F (lifecycleStep L s (L.embedding.edgeAt a)) (leftEnd F a) =
      (commitRow (encodeLife F (StopNode.active s) (leftEnd F a))
        (encodeLife F (StopNode.active s) (rightEnd F a))).1 := by
  rw [(lifecycleStep_encodes_rows L s a).2]
  show (if a.val = a.val then
      (commitRow (encodeLife F (StopNode.active s) (leftEnd F a))
        (encodeLife F (StopNode.active s) (rightEnd F a))).1
    else if a.val = a.val + 1 then
      (commitRow (encodeLife F (StopNode.active s) (leftEnd F a))
        (encodeLife F (StopNode.active s) (rightEnd F a))).2
    else encodeLife F (StopNode.active s) (leftEnd F a)) =
    (commitRow (encodeLife F (StopNode.active s) (leftEnd F a))
      (encodeLife F (StopNode.active s) (rightEnd F a))).1
  rw [if_pos (show a.val = a.val from rfl)]

theorem lifecycleStep_right_endpoint {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (a : Fin F.h) :
    encodeLife F (lifecycleStep L s (L.embedding.edgeAt a)) (rightEnd F a) =
      (commitRow (encodeLife F (StopNode.active s) (leftEnd F a))
        (encodeLife F (StopNode.active s) (rightEnd F a))).2 := by
  rw [(lifecycleStep_encodes_rows L s a).2]
  show (if a.val + 1 = a.val then
      (commitRow (encodeLife F (StopNode.active s) (leftEnd F a))
        (encodeLife F (StopNode.active s) (rightEnd F a))).1
    else if a.val + 1 = a.val + 1 then
      (commitRow (encodeLife F (StopNode.active s) (leftEnd F a))
        (encodeLife F (StopNode.active s) (rightEnd F a))).2
    else encodeLife F (StopNode.active s) (rightEnd F a)) =
    (commitRow (encodeLife F (StopNode.active s) (leftEnd F a))
      (encodeLife F (StopNode.active s) (rightEnd F a))).2
  rw [if_neg (show ¬ (a.val + 1 = a.val) by omega),
    if_pos (show a.val + 1 = a.val + 1 from rfl)]

/-- **Safety 1 on the walk.**  A firing of the lifecycle that is a commit
literal needs the extended reserved lease, an intact target leader and an
accepted raw target at the right endpoint of the scheduled edge. -/
theorem lifecycle_step_commit_needs_lease {F : Frame}
    (s : LifecycleState F) (a : Fin F.h)
    (h : IsCommitLiteral (commitRule (encodeLife F (StopNode.active s) (leftEnd F a))
      (encodeLife F (StopNode.active s) (rightEnd F a)))) :
    (encodeLife F (StopNode.active s) (rightEnd F a)).incoming = CommitIn.reserved ∧
      (encodeLife F (StopNode.active s) (rightEnd F a)).carrier = CommitCarrier.none ∧
      (encodeLife F (StopNode.active s) (rightEnd F a)).leader = true ∧
      rawTarget (encodeLife F (StopNode.active s) (rightEnd F a)).raw = true :=
  lifecycle_commit_needs_lease F (StopNode.active s) a h

/-- **Safety 2 on the walk.**  Across one lifecycle firing the right endpoint's
leader flag falls exactly on the commit literal.  No other row of the lifecycle
deletes a leader, and an already-deleted target is not a commit row. -/
theorem lifecycle_step_targetLeader_falls_iff_commit {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (a : Fin F.h) :
    ((encodeLife F (StopNode.active s) (rightEnd F a)).leader = true ∧
        (encodeLife F (lifecycleStep L s (L.embedding.edgeAt a))
          (rightEnd F a)).leader = false) ↔
      IsCommitLiteral (commitRule (encodeLife F (StopNode.active s) (leftEnd F a))
        (encodeLife F (StopNode.active s) (rightEnd F a))) := by
  rw [lifecycleStep_right_endpoint]
  exact (targetLeader_falls_iff_commit_literal
    (encodeLife F (StopNode.active s) (leftEnd F a))
    (encodeLife F (StopNode.active s) (rightEnd F a))).2

/-- **Safety 3 on the walk.**  A deposited `protectedFinal` is never returned
to `capturing` by any lifecycle firing, at either endpoint: once FINAL is in,
the abort lane is closed while the commit carrier is remote. -/
theorem lifecycle_step_protected_no_abort {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (a : Fin F.h) :
    ((encodeLife F (StopNode.active s) (leftEnd F a)).outgoing = CommitCtl.protectedFinal →
        (encodeLife F (lifecycleStep L s (L.embedding.edgeAt a))
          (leftEnd F a)).outgoing ≠ CommitCtl.capturing) ∧
    ((encodeLife F (StopNode.active s) (rightEnd F a)).outgoing = CommitCtl.protectedFinal →
        (encodeLife F (lifecycleStep L s (L.embedding.edgeAt a))
          (rightEnd F a)).outgoing ≠ CommitCtl.capturing) := by
  rw [lifecycleStep_left_endpoint, lifecycleStep_right_endpoint]
  exact protected_no_abort_literal _ _

/-- Spent target state and a completed source receipt survive every lifecycle
firing at either endpoint of the scheduled edge. -/
theorem lifecycle_step_postcommit_irreversible {F : Frame} {n : Nat}
    (L : Layout F n) (s : LifecycleState F) (a : Fin F.h) :
    (PostCommitted (encodeLife F (StopNode.active s) (leftEnd F a)) →
        PostCommitted (encodeLife F (lifecycleStep L s (L.embedding.edgeAt a))
          (leftEnd F a))) ∧
    (PostCommitted (encodeLife F (StopNode.active s) (rightEnd F a)) →
        PostCommitted (encodeLife F (lifecycleStep L s (L.embedding.edgeAt a))
          (rightEnd F a))) ∧
    (ReceiptDone (encodeLife F (StopNode.active s) (leftEnd F a)) →
        ReceiptDone (encodeLife F (lifecycleStep L s (L.embedding.edgeAt a))
          (leftEnd F a))) ∧
    (ReceiptDone (encodeLife F (StopNode.active s) (rightEnd F a)) →
        ReceiptDone (encodeLife F (lifecycleStep L s (L.embedding.edgeAt a))
          (rightEnd F a))) := by
  rw [lifecycleStep_left_endpoint, lifecycleStep_right_endpoint]
  exact postcommit_irreversible_literal _ _

/-! ## The `h = 1` fused direct rows -/

/-- The two literal rows a one-slot gap fires.  The first fuses proposal
launch, target acceptance and FINAL deposit; the second fuses the protected
commit launch, the commit at the target and the committed receipt. -/
theorem lifecycle_h1_direct_rows (F : Frame) :
    commitRow (render F .sHome) (render F .tReserved) =
        (render F .sProtected, render F .tHeld) ∧
      commitRow (render F .sProtected) (render F .tHeld) =
        (render F .sReceived, render F .tCommitted) :=
  ⟨tagRow_literal F .sHome .tReserved rfl, tagRow_literal F .sProtected .tHeld rfl⟩

/-- `h = 1`: the lifecycle's first firing on the gap's only edge is exactly the
fused proposal/FINAL row. -/
theorem lifecycleStep_h1_encodes_proposal {F : Frame} {n : Nat}
    (L : Layout F n) (hh : F.h = 1) :
    encodeLife F (StopNode.active (lifecycleStart F)) (leftEnd F ⟨0, F.hpos⟩) =
        render F .sHome ∧
      encodeLife F (StopNode.active (lifecycleStart F)) (rightEnd F ⟨0, F.hpos⟩) =
        render F .tReserved ∧
      encodeLife F (lifecycleStep L (lifecycleStart F)
          (L.embedding.edgeAt ⟨0, F.hpos⟩)) =
        pairUpdate F (encodeLife F (StopNode.active (lifecycleStart F))) ⟨0, F.hpos⟩
          (commitRow (render F .sHome) (render F .tReserved)) := by
  have hl : tagConfig F (StopNode.active (lifecycleStart F))
      (leftEnd F ⟨0, F.hpos⟩) = Tag.sHome := by
    refine (left_src F _ ⟨0, F.hpos⟩ rfl).trans ?_
    show (if (0 : Nat) = 0 then Tag.sHome else Tag.sProposal) = Tag.sHome
    rw [if_pos (show (0 : Nat) = 0 from rfl)]
  have hr : tagConfig F (StopNode.active (lifecycleStart F))
      (rightEnd F ⟨0, F.hpos⟩) = Tag.tReserved :=
    right_tgt F _ ⟨0, F.hpos⟩ (by omega)
  have e1 : encodeLife F (StopNode.active (lifecycleStart F))
      (leftEnd F ⟨0, F.hpos⟩) = render F .sHome := by
    show render F (tagConfig F (StopNode.active (lifecycleStart F))
      (leftEnd F ⟨0, F.hpos⟩)) = render F Tag.sHome
    rw [hl]
  have e2 : encodeLife F (StopNode.active (lifecycleStart F))
      (rightEnd F ⟨0, F.hpos⟩) = render F .tReserved := by
    show render F (tagConfig F (StopNode.active (lifecycleStart F))
      (rightEnd F ⟨0, F.hpos⟩)) = render F Tag.tReserved
    rw [hr]
  refine ⟨e1, e2, ?_⟩
  rw [← e1, ← e2]
  exact (lifecycleStep_encodes_rows L (lifecycleStart F) ⟨0, F.hpos⟩).2

/-- `h = 1`: the next firing on the same edge is exactly the fused commit /
committed-receipt row. -/
theorem lifecycleStep_h1_encodes_commit {F : Frame} {n : Nat}
    (L : Layout F n) (hh : F.h = 1) :
    encodeLife F (StopNode.active (LifecycleState.protectedWait : LifecycleState F))
        (leftEnd F ⟨0, F.hpos⟩) = render F .sProtected ∧
      encodeLife F (StopNode.active (LifecycleState.protectedWait : LifecycleState F))
        (rightEnd F ⟨0, F.hpos⟩) = render F .tHeld ∧
      encodeLife F (lifecycleStep L (LifecycleState.protectedWait : LifecycleState F)
          (L.embedding.edgeAt ⟨0, F.hpos⟩)) =
        pairUpdate F (encodeLife F
            (StopNode.active (LifecycleState.protectedWait : LifecycleState F)))
          ⟨0, F.hpos⟩ (commitRow (render F .sProtected) (render F .tHeld)) := by
  have e1 : encodeLife F
      (StopNode.active (LifecycleState.protectedWait : LifecycleState F))
      (leftEnd F ⟨0, F.hpos⟩) = render F .sProtected := by
    show render F (tagConfig F
      (StopNode.active (LifecycleState.protectedWait : LifecycleState F))
      (leftEnd F ⟨0, F.hpos⟩)) = render F Tag.sProtected
    rw [left_src F _ ⟨0, F.hpos⟩ rfl]
    rfl
  have e2 : encodeLife F
      (StopNode.active (LifecycleState.protectedWait : LifecycleState F))
      (rightEnd F ⟨0, F.hpos⟩) = render F .tHeld := by
    show render F (tagConfig F
      (StopNode.active (LifecycleState.protectedWait : LifecycleState F))
      (rightEnd F ⟨0, F.hpos⟩)) = render F Tag.tHeld
    rw [right_tgt F _ ⟨0, F.hpos⟩ (by omega)]
    rfl
  refine ⟨e1, e2, ?_⟩
  rw [← e1, ← e2]
  exact (lifecycleStep_encodes_rows L
    (LifecycleState.protectedWait : LifecycleState F) ⟨0, F.hpos⟩).2

end ShortGapCaptureLifecycleWalk

#print axioms ShortGapCaptureLifecycleWalk.tagRow_literal
#print axioms ShortGapCaptureLifecycleWalk.lifecycleStep_encodes_rows
#print axioms ShortGapCaptureLifecycleWalk.lifecycleStep_encodes_target_service
#print axioms ShortGapCaptureLifecycleWalk.lifecycleStep_h1_encodes_proposal
#print axioms ShortGapCaptureLifecycleWalk.lifecycleStep_h1_encodes_commit
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_bellman
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_no_failure
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_start_potential
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_truncatedCost_le
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_step_commit_needs_lease
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_step_targetLeader_falls_iff_commit
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_step_protected_no_abort
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_step_postcommit_irreversible
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_refines_cleanCommitTrace
#print axioms ShortGapCaptureLifecycleWalk.lifecycle_success_refines_cleanCommit

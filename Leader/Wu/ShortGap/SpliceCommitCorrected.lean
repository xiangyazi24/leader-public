import Leader.Wu.ShortGap.SpliceCommit
import Leader.Wu.ShortGap.SpliceAdoptCorrected
import Leader.Wu.ShortGap.SpliceFusedRow
import Leader.Wu.ShortGap.SpliceCorridor

namespace ShortGapSpliceCommitCorrected

open ShortGapLiteralGapRows ShortGapCaptureReservation ShortGapCaptureCommitRows
open ShortGapSpliceCommit ShortGapSpliceFusedRow ShortGapSpliceCorridor
open FiniteUniformStoppingTree

set_option autoImplicit false

/-!
# The corrected splice-commit table, and its corridor simulation

Table names used below: `Original` is the first splice table of
`Leader/Wu/ShortGap/SpliceCommit.lean`; `Corrected` is the table of this file;
`WithDemotion` is `spliceRowWithDemotion` in
`Leader/Wu/ShortGap/SpliceDemotionTable.lean`.

`Leader/Wu/ShortGap/SpliceCommit.lean` supplies the first splice table
(`SRule`/`SRowStep`/`srun`/`spliceRow`).  Three defects of that table were
isolated afterwards:

* **adoption manufactures `waiting`.**  `adoptCw` sends every settled old
  `(B,C)` verdict to `waiting`, so a *delivered* denial makes the new owner
  wait for a token that no longer exists.  `Leader/Wu/ShortGap/SpliceAdoptCorrected.lean`
  replaces it by `adoptCwCorrected`, for which `adoptCorrected_waiting_iff` says
  `waiting` holds exactly when the snapshot still records a live carrier.

* **the length-one corridor stalls.**  `ShortGapSpliceCorridor.corridor_length_one_stalls`
  exhibits the configuration `x = 1` on which no `Original` row is enabled at all.
  `Leader/Wu/ShortGap/SpliceFusedRow.lean` supplies the missing fused row
  `RetireFused`/`retireFused`.

* **the source acknowledgement is skipped.**  `Original`'s `adoptDeposit` writes
  `A.cw := adopt(snapshot)` in the same firing that sets
  `A.outgoing := .committedReceived`.  Since `adoptCwOf` is never
  `heldCandidate`, that write destroys `rawOwner A`, hence destroys
  `Owner A`, hence disables the imported `sourceAck` row *forever*: `A`'s
  commit lifecycle is stuck at `.committedReceived` and is never returned to
  `.clean`.  The accounting boundary is fixed at "after `A` receives
  COMMITTED, performs adoption **and discharges `sourceAck`**", so the table
  has to make that order possible.

`Corrected` below is `Original` with exactly those three changes and nothing else:

1. `adoptCwOfCorrected` (built on the imported `adoptCwCorrected`) replaces `adoptCwOf` in
   the only row that writes the clockwise port, `directAdopt`;
2. the fused row `RetireFused` is a row of the table, placed *after* the
   three fresh-declaration rows so that the flush keeps absolute priority
   (`stale_receipt_inertCorrected`);
3. `adoptDeposit` no longer writes the clockwise port.  It performs exactly
   the imported `committedDeposit` core update and *transports the snapshot
   into `A.payload`*.  `A` therefore stays `Owner`, the imported `sourceAck`
   row fires next, and only then is `DirectAdopt` -- whose guard already
   demands `a.core.outgoing = .clean`, i.e. *the ack discharged* -- enabled.
   The ordering is thus enforced by the existing `CNode.outgoing` field; no
   new field is added.

Everything proved here is local: row equations, guard disjointness, frames,
a literal corridor simulation, an exact firing count and one arithmetic
potential instantiation.  No freshness, reachability, fairness or global
completion-time statement is made.
-/

/-! ## Corrected adoption on an optional snapshot -/

/-- `adoptCwCorrected` on the optional payload actually carried by the receipt.
No snapshot means no live carrier at all, hence `toSend`; this differs from
`Original`'s `adoptCwOf`, which returned `waiting` and so re-created the very defect
`adoptCwCorrected` removes. -/
def adoptCwOfCorrected : Option SnapPhase -> CwPort
  | none => .toSend
  | some s => adoptCwCorrected s

theorem adoptCwOfCorrected_ne_denial (s : Option SnapPhase) :
    adoptCwOfCorrected s ≠ CwPort.heldDenial := by
  cases s with
  | none => intro h; cases h
  | some v => exact adoptCorrected_ne_denial v

theorem adoptCwOfCorrected_ne_candidate (s : Option SnapPhase) :
    adoptCwOfCorrected s ≠ CwPort.heldCandidate := by
  cases s with
  | none => intro h; cases h
  | some v => exact adoptCorrected_ne_candidate v

/-- The corrected liveness characterisation, lifted to the optional payload:
the adopted port waits exactly when the transported snapshot still records a
live carrier. -/
theorem adoptCwOfCorrected_waiting_iff (s : Option SnapPhase) :
    adoptCwOfCorrected s = CwPort.waiting <-> ∃ t, s = some t ∧ SnapPhase.isLive t = true := by
  cases s with
  | none =>
      constructor
      · intro h; cases h
      · intro h; obtain ⟨t, ht, _⟩ := h; cases ht
  | some v =>
      constructor
      · intro h
        exact ⟨v, rfl, (adoptCorrected_waiting_iff v).mp h⟩
      · intro h
        obtain ⟨t, ht, hl⟩ := h
        have hv : t = v := (Option.some.inj ht).symm
        subst hv
        exact (adoptCorrected_waiting_iff t).mpr hl

/-- `Original`'s adoption really is different: on a settled denial that carries no
token it waits, while `Corrected` re-arms. -/
theorem adoptOriginal_ne_adoptCorrected :
    adoptCwOf (some ⟨.heldDenial, .home⟩) = CwPort.waiting ∧
      adoptCwOfCorrected (some ⟨.heldDenial, .home⟩) = CwPort.toSend := ⟨rfl, rfl⟩

/-! ## The ack witness, in the fields the wrapper already has -/

/-- The source acknowledgement of the committed receipt is still pending. -/
abbrev AckPending (a : SNode) : Prop := a.core.outgoing = .committedReceived

/-- The source acknowledgement has been discharged. -/
abbrev AckDischarged (a : SNode) : Prop := a.core.outgoing = .clean

/-! ## Effects of the two corrected adopt rows -/

/-- `Corrected` deposit-at-A.  Exactly the imported `committedDeposit` left update,
plus the transport of the snapshot into `A.payload`.  The clockwise port is
*not* written, so `A` remains `Owner` and the imported `sourceAck` row is the
next enabled row. -/
def adoptDepositLCorrected (a : SNode) (s : Option SnapPhase) : SNode :=
  { a with core := setOut a.core .committedReceived, payload := s }

/-- `Corrected` adopt-at-A.  The clockwise write, with the corrected `adoptCwCorrected`.
Its guard `DirectAdopt` already demands `a.core.outgoing = .clean`, i.e. the
ack discharged. -/
def directAdoptLCorrected (a : SNode) : SNode :=
  { a with
    core := { a.core with raw := setRawCw a.core.raw (adoptCwOfCorrected a.payload) },
    splice := .adopted, payload := none }

/-! ## The table -/

inductive SRuleCorrected where
  | core (k : Rule)
  | freshFlush | freshLaunch | freshForward
  | retireFused
  | retireLaunch | retireBackward | retireDeposit
  | adoptDeposit | directAdopt | handoffArm
  deriving DecidableEq

def IsNewCorrected : SRuleCorrected -> Bool
  | .core _ => false
  | _ => true

inductive SRowStepCorrected (a b : SNode) : SRuleCorrected -> SNode -> SNode -> Prop where
  | core :
      SRowStepCorrected a b (.core (commitRule a.core b.core))
        (liftPair a b (commitRow a.core b.core)).1
        (liftPair a b (commitRow a.core b.core)).2
  | freshFlush (h : FreshFlush a b) :
      SRowStepCorrected a b .freshFlush (flushL a) (flushR b)
  | freshLaunch (h : FreshLaunch a b) :
      SRowStepCorrected a b .freshLaunch (launchL a) (declR b)
  | freshForward (h : FreshForward a b) :
      SRowStepCorrected a b .freshForward (fwdL a) (declR b)
  | retireFused (h : RetireFused a b) :
      SRowStepCorrected a b .retireFused (retiredL a) (drainR b)
  | retireLaunch (h : RetireLaunch a b) :
      SRowStepCorrected a b .retireLaunch (witnessL a) (drainR b)
  | retireBackward (h : RetireBackward a b) :
      SRowStepCorrected a b .retireBackward (witnessL a) (clearWitnessR b)
  | retireDeposit (h : RetireDeposit a b) :
      SRowStepCorrected a b .retireDeposit (retiredL a) (clearWitnessR b)
  | adoptDeposit (h : AdoptDeposit a b) :
      SRowStepCorrected a b .adoptDeposit (adoptDepositLCorrected a b.payload) (adoptR b)
  | directAdopt (h : DirectAdopt a) :
      SRowStepCorrected a b .directAdopt (directAdoptLCorrected a) b
  | handoffArm (h : HandoffArm a) :
      SRowStepCorrected a b .handoffArm (armL a) b

structure SResultCorrected (a b : SNode) where
  rule : SRuleCorrected
  left : SNode
  right : SNode
  valid : SRowStepCorrected a b rule left right

/-- Total, deterministic, radius-one dispatch.  The flush keeps absolute
priority; the fused retirement is inserted directly after the three
fresh-declaration rows. -/
def srunCorrected (a b : SNode) : SResultCorrected a b :=
  if h : FreshFlush a b then
    ⟨.freshFlush, flushL a, flushR b, .freshFlush h⟩
  else if h : FreshLaunch a b then
    ⟨.freshLaunch, launchL a, declR b, .freshLaunch h⟩
  else if h : FreshForward a b then
    ⟨.freshForward, fwdL a, declR b, .freshForward h⟩
  else if h : RetireFused a b then
    ⟨.retireFused, retiredL a, drainR b, .retireFused h⟩
  else if h : RetireLaunch a b then
    ⟨.retireLaunch, witnessL a, drainR b, .retireLaunch h⟩
  else if h : RetireBackward a b then
    ⟨.retireBackward, witnessL a, clearWitnessR b, .retireBackward h⟩
  else if h : RetireDeposit a b then
    ⟨.retireDeposit, retiredL a, clearWitnessR b, .retireDeposit h⟩
  else if h : AdoptDeposit a b then
    ⟨.adoptDeposit, adoptDepositLCorrected a b.payload, adoptR b, .adoptDeposit h⟩
  else if h : DirectAdopt a then
    ⟨.directAdopt, directAdoptLCorrected a, b, .directAdopt h⟩
  else if h : HandoffArm a then
    ⟨.handoffArm, armL a, b, .handoffArm h⟩
  else
    ⟨.core (commitRule a.core b.core),
      (liftPair a b (commitRow a.core b.core)).1,
      (liftPair a b (commitRow a.core b.core)).2, .core⟩

def spliceRowCorrected (a b : SNode) : SNode × SNode := ((srunCorrected a b).left, (srunCorrected a b).right)

def spliceRuleCorrected (a b : SNode) : SRuleCorrected := (srunCorrected a b).rule

theorem spliceRowCorrected_spec (a b : SNode) :
    SRowStepCorrected a b (spliceRuleCorrected a b) (spliceRowCorrected a b).1 (spliceRowCorrected a b).2 :=
  (srunCorrected a b).valid

/-! ## Dispatch lemmas of the `Corrected` table -/

theorem dispatchCorrected_flush (a b : SNode) (h : FreshFlush a b) :
    srunCorrected a b = ⟨.freshFlush, flushL a, flushR b, .freshFlush h⟩ := by
  simp only [srunCorrected, dif_pos h]

theorem dispatchCorrected_fused (a b : SNode) (h1 : ¬ FreshFlush a b) (h2 : ¬ FreshLaunch a b)
    (h3 : ¬ FreshForward a b) (h : RetireFused a b) :
    srunCorrected a b = ⟨.retireFused, retiredL a, drainR b, .retireFused h⟩ := by
  simp only [srunCorrected, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h]

theorem dispatchCorrected_retireLaunch (a b : SNode) (h1 : ¬ FreshFlush a b)
    (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b) (hf : ¬ RetireFused a b)
    (h : RetireLaunch a b) :
    srunCorrected a b = ⟨.retireLaunch, witnessL a, drainR b, .retireLaunch h⟩ := by
  simp only [srunCorrected, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg hf, dif_pos h]

theorem dispatchCorrected_retireBackward (a b : SNode) (h1 : ¬ FreshFlush a b)
    (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b) (hf : ¬ RetireFused a b)
    (h4 : ¬ RetireLaunch a b) (h : RetireBackward a b) :
    srunCorrected a b = ⟨.retireBackward, witnessL a, clearWitnessR b, .retireBackward h⟩ := by
  simp only [srunCorrected, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg hf, dif_neg h4, dif_pos h]

theorem dispatchCorrected_retireDeposit (a b : SNode) (h1 : ¬ FreshFlush a b)
    (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b) (hf : ¬ RetireFused a b)
    (h4 : ¬ RetireLaunch a b) (h5 : ¬ RetireBackward a b) (h : RetireDeposit a b) :
    srunCorrected a b = ⟨.retireDeposit, retiredL a, clearWitnessR b, .retireDeposit h⟩ := by
  simp only [srunCorrected, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg hf, dif_neg h4,
    dif_neg h5, dif_pos h]

theorem dispatchCorrected_adoptDeposit (a b : SNode) (h1 : ¬ FreshFlush a b)
    (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b) (hf : ¬ RetireFused a b)
    (h4 : ¬ RetireLaunch a b) (h5 : ¬ RetireBackward a b) (h6 : ¬ RetireDeposit a b)
    (h : AdoptDeposit a b) :
    srunCorrected a b = ⟨.adoptDeposit, adoptDepositLCorrected a b.payload, adoptR b, .adoptDeposit h⟩ := by
  simp only [srunCorrected, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg hf, dif_neg h4,
    dif_neg h5, dif_neg h6, dif_pos h]

theorem dispatchCorrected_directAdopt (a b : SNode) (h1 : ¬ FreshFlush a b)
    (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b) (hf : ¬ RetireFused a b)
    (h4 : ¬ RetireLaunch a b) (h5 : ¬ RetireBackward a b) (h6 : ¬ RetireDeposit a b)
    (h7 : ¬ AdoptDeposit a b) (h : DirectAdopt a) :
    srunCorrected a b = ⟨.directAdopt, directAdoptLCorrected a, b, .directAdopt h⟩ := by
  simp only [srunCorrected, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg hf, dif_neg h4,
    dif_neg h5, dif_neg h6, dif_neg h7, dif_pos h]

theorem dispatchCorrected_handoff (a b : SNode) (h1 : ¬ FreshFlush a b)
    (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b) (hf : ¬ RetireFused a b)
    (h4 : ¬ RetireLaunch a b) (h5 : ¬ RetireBackward a b) (h6 : ¬ RetireDeposit a b)
    (h7 : ¬ AdoptDeposit a b) (h8 : ¬ DirectAdopt a) (h : HandoffArm a) :
    srunCorrected a b = ⟨.handoffArm, armL a, b, .handoffArm h⟩ := by
  simp only [srunCorrected, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg hf, dif_neg h4,
    dif_neg h5, dif_neg h6, dif_neg h7, dif_neg h8, dif_pos h]

theorem dispatchCorrected_core (a b : SNode) (h1 : ¬ FreshFlush a b)
    (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b) (hf : ¬ RetireFused a b)
    (h4 : ¬ RetireLaunch a b) (h5 : ¬ RetireBackward a b) (h6 : ¬ RetireDeposit a b)
    (h7 : ¬ AdoptDeposit a b) (h8 : ¬ DirectAdopt a) (h9 : ¬ HandoffArm a) :
    srunCorrected a b =
      { rule := .core (commitRule a.core b.core)
        left := (liftPair a b (commitRow a.core b.core)).1
        right := (liftPair a b (commitRow a.core b.core)).2
        valid := .core } := by
  simp only [srunCorrected, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg hf, dif_neg h4,
    dif_neg h5, dif_neg h6, dif_neg h7, dif_neg h8, dif_neg h9]

private def pairOf {a b : SNode} (r : SResultCorrected a b) : SNode × SNode := (r.left, r.right)

theorem rowCorrected_of_dispatch {a b : SNode} {r : SResultCorrected a b} (h : srunCorrected a b = r) :
    spliceRowCorrected a b = (r.left, r.right) :=
  congrArg (fun t : SResultCorrected a b => (t.left, t.right)) h

theorem ruleCorrected_of_dispatch {a b : SNode} {r : SResultCorrected a b} (h : srunCorrected a b = r) :
    spliceRuleCorrected a b = r.rule :=
  congrArg SResultCorrected.rule h

theorem spliceRowCorrected_core_of (a b : SNode) (h1 : ¬ FreshFlush a b)
    (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b) (hf : ¬ RetireFused a b)
    (h4 : ¬ RetireLaunch a b) (h5 : ¬ RetireBackward a b) (h6 : ¬ RetireDeposit a b)
    (h7 : ¬ AdoptDeposit a b) (h8 : ¬ DirectAdopt a) (h9 : ¬ HandoffArm a) :
    spliceRowCorrected a b = liftPair a b (commitRow a.core b.core) :=
  rowCorrected_of_dispatch (dispatchCorrected_core a b h1 h2 h3 hf h4 h5 h6 h7 h8 h9)

theorem spliceRuleCorrected_core_of (a b : SNode) (h1 : ¬ FreshFlush a b)
    (h2 : ¬ FreshLaunch a b) (h3 : ¬ FreshForward a b) (hf : ¬ RetireFused a b)
    (h4 : ¬ RetireLaunch a b) (h5 : ¬ RetireBackward a b) (h6 : ¬ RetireDeposit a b)
    (h7 : ¬ AdoptDeposit a b) (h8 : ¬ DirectAdopt a) (h9 : ¬ HandoffArm a) :
    spliceRuleCorrected a b = .core (commitRule a.core b.core) :=
  ruleCorrected_of_dispatch (dispatchCorrected_core a b h1 h2 h3 hf h4 h5 h6 h7 h8 h9)

/-- A pair on which neither the `Corrected` splice table nor the imported commit
table has an enabled row is a literal stutter of the whole wrapper. -/
theorem spliceRowCorrected_stutter_of (a b : SNode)
    (hcore : spliceRowCorrected a b = liftPair a b (commitRow a.core b.core))
    (hidle : commitRow a.core b.core = (a.core, b.core))
    (hc : committedNow b.core b.core = false)
    (hm : receiptMoved b.core a.core b.core = false) :
    spliceRowCorrected a b = (a, b) := by
  rw [hcore, hidle]
  show (liftLeft a b a.core b.core, liftRight b a.core b.core) = (a, b)
  unfold liftLeft liftRight
  rw [hc, hm]
  rfl

/-! ## Conservativity: on a neutral pair the imported commit row is executed -/

private theorem neutral_no_newCorrected (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    (¬ FreshFlush a b) ∧ (¬ FreshLaunch a b) ∧ (¬ FreshForward a b) ∧
    (¬ RetireFused a b) ∧
    (¬ RetireLaunch a b) ∧ (¬ RetireBackward a b) ∧ (¬ RetireDeposit a b) ∧
    (¬ AdoptDeposit a b) ∧ (¬ DirectAdopt a) ∧ (¬ HandoffArm a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have hx := h.1; rw [hna.2.2.2.2] at hx; cases hx
  · intro h; have hx := h.1; rw [hna.2.2.1] at hx; cases hx
  · intro h; have hx := h.1; rw [hna.2.2.2.2] at hx; cases hx
  · intro h; have hx := h.1; rw [hna.2.2.1] at hx; cases hx
  · intro h; have hx := h.2.2.1; rw [hnb.2.2.1] at hx; cases hx
  · intro h; have hx := h.2.2.2; rw [hnb.2.2.2.1] at hx; cases hx
  · intro h; have hx := h.1; rw [hna.2.2.1] at hx; cases hx
  · intro h; exact h.2.1 hnb.2.1
  · intro h; exact h.2.1 hna.2.1
  · intro h; have hx := h.1; rw [hna.2.2.1] at hx; cases hx

theorem splice_core_dispatchCorrected (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    srunCorrected a b =
      { rule := .core (commitRule a.core b.core)
        left := (liftPair a b (commitRow a.core b.core)).1
        right := (liftPair a b (commitRow a.core b.core)).2
        valid := .core } := by
  obtain ⟨h1, h2, h3, hf, h4, h5, h6, h7, h8, h9⟩ := neutral_no_newCorrected a b hna hnb
  exact dispatchCorrected_core a b h1 h2 h3 hf h4 h5 h6 h7 h8 h9

theorem spliceRuleCorrected_core (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    spliceRuleCorrected a b = .core (commitRule a.core b.core) :=
  ruleCorrected_of_dispatch (splice_core_dispatchCorrected a b hna hnb)

theorem spliceRowCorrected_core (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    spliceRowCorrected a b = liftPair a b (commitRow a.core b.core) :=
  rowCorrected_of_dispatch (splice_core_dispatchCorrected a b hna hnb)

/-- The `Corrected` table is conservative over `commitRow`: on a pre-splice pair the
whole imported core pair transition is executed unchanged. -/
theorem spliceRowCorrected_agrees_commitRow (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    projectCore (spliceRowCorrected a b) = commitRow a.core b.core := by
  rw [spliceRowCorrected_core a b hna hnb]
  rfl

/-- The full chain down to the imported literal capture row. -/
theorem spliceRowCorrected_agrees_captureRow (a b : Node) (la lb : Bool)
    (h : captureRow a b ≠ (a, b)) :
    projectRaw (spliceRowCorrected (sembed a la) (sembed b lb)) = captureRow a b := by
  have hn : Neutral (sembed a la) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hm : Neutral (sembed b lb) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hcore := spliceRowCorrected_agrees_commitRow (sembed a la) (sembed b lb) hn hm
  have hraw := commitRow_agrees_captureRow a b la lb h
  have h1 : (spliceRowCorrected (sembed a la) (sembed b lb)).1.core
      = (commitRow (embed a la) (embed b lb)).1 :=
    congrArg (fun p : CNode × CNode => p.1) hcore
  have h2 : (spliceRowCorrected (sembed a la) (sembed b lb)).2.core
      = (commitRow (embed a la) (embed b lb)).2 :=
    congrArg (fun p : CNode × CNode => p.2) hcore
  calc projectRaw (spliceRowCorrected (sembed a la) (sembed b lb))
      = projectPair (commitRow (embed a la) (embed b lb)) := by
        unfold projectRaw projectPair
        rw [h1, h2]
    _ = captureRow a b := hraw

private theorem committedNow_iffCorrected (b b' : CNode) :
    committedNow b b' = true ↔ (b.leader = true ∧ b'.leader = false) := by
  unfold committedNow
  cases hb : b.leader <;> cases hb' : b'.leader <;> simp

/-- Commit-at-B still installs the bridge and hands the snapshot to the
returning COMMITTED receipt: `Corrected` changes nothing on the neutral pair. -/
theorem commit_installs_bridgeCorrected (a b : SNode) (hna : Neutral a) (hnb : Neutral b) :
    ((spliceRowCorrected a b).2.bridge = some (snapNode b.core.raw) ∧
      (spliceRowCorrected a b).2.splice = .bridged ∧
      (spliceRowCorrected a b).1.payload = some (snapNode b.core.raw)) ↔
      IsCommitLiteral (commitRule a.core b.core) := by
  have hrow := spliceRowCorrected_core a b hna hnb
  have hfall := (targetLeader_falls_iff_commit_literal a.core b.core).2
  constructor
  · intro h
    have hbridge : (spliceRowCorrected a b).2.bridge =
        (if committedNow b.core (commitRow a.core b.core).2 then
          some (snapNode b.core.raw) else b.bridge) := by
      rw [hrow]; rfl
    rw [hnb.1] at hbridge
    by_cases hc : committedNow b.core (commitRow a.core b.core).2 = true
    · exact hfall.mp ((committedNow_iffCorrected _ _).mp hc)
    · rw [if_neg hc] at hbridge
      rw [hbridge] at h
      exact absurd h.1 (by simp)
  · intro h
    have hc : committedNow b.core (commitRow a.core b.core).2 = true :=
      (committedNow_iffCorrected _ _).mpr (hfall.mpr h)
    refine ⟨?_, ?_, ?_⟩
    · rw [hrow]
      show (if committedNow b.core (commitRow a.core b.core).2 then
            some (snapNode b.core.raw) else b.bridge) = some (snapNode b.core.raw)
      rw [if_pos hc]
    · rw [hrow]
      show (if committedNow b.core (commitRow a.core b.core).2 then
            SpliceCtl.bridged else b.splice) = .bridged
      rw [if_pos hc]
    · rw [hrow]
      show (if committedNow b.core (commitRow a.core b.core).2 then
            some (snapNode b.core.raw)
            else if receiptMoved b.core (commitRow a.core b.core).1
              (commitRow a.core b.core).2 then b.payload else a.payload) =
          some (snapNode b.core.raw)
      rw [if_pos hc]

/-! ## The stale `C.ccw` receipt is still inert until consumed -/

private theorem ccwPort_setRawCcw_of_someCorrected (n : Node) (v w : CcwPort)
    (h : n.ccwPort = some w) : (setRawCcw n v).ccwPort = some v := by
  cases n with
  | root => rfl
  | interior => cases h

private theorem cwPort_setRawCw_neCorrected (n : Node) (v w : CwPort) (hvw : v ≠ w) :
    (setRawCw n v).cwPort ≠ some w := by
  cases n with
  | root =>
      intro h
      exact hvw (Option.some.inj h)
  | interior =>
      intro h
      cases h

/-- The `Original` statement, re-proved on the `Corrected` table: a fresh `A -> C`
declaration meeting a stale `heldDenial` on `C.ccw` fires the flush and
nothing else.  The fused row does not disturb this, because it is dispatched
*after* the three fresh-declaration rows. -/
theorem stale_receipt_inertCorrected (a b : SNode) (h : FreshFlush a b) :
    spliceRuleCorrected a b = .freshFlush ∧
    (∀ k : Rule, spliceRuleCorrected a b ≠ .core k) ∧
    spliceRuleCorrected a b ≠ .retireFused ∧
    spliceRowCorrected a b = (flushL a, flushR b) ∧
    (spliceRowCorrected a b).2.core.raw.ccwPort = some .free ∧
    (spliceRowCorrected a b).2.core.raw.ccwPort ≠ some .heldDenial ∧
    (spliceRowCorrected a b).1.flush = .flushed ∧
    (spliceRowCorrected a b).1.core = a.core ∧
    (spliceRowCorrected a b).2.core.leader = b.core.leader ∧
    (spliceRowCorrected a b).2.core.incoming = b.core.incoming ∧
    (spliceRowCorrected a b).2.core.carrier = b.core.carrier ∧
    (spliceRowCorrected a b).2.core.raw.cwPort = b.core.raw.cwPort ∧
    ¬ FreshFlush (spliceRowCorrected a b).1 (spliceRowCorrected a b).2 := by
  have hd := dispatchCorrected_flush a b h
  have hrule : spliceRuleCorrected a b = .freshFlush := ruleCorrected_of_dispatch hd
  have hrow : spliceRowCorrected a b = (flushL a, flushR b) := rowCorrected_of_dispatch hd
  have hccw : (flushR b).core.raw.ccwPort = some .free :=
    ccwPort_setRawCcw_of_someCorrected b.core.raw .free .heldDenial h.2.1
  refine ⟨hrule, ?_, ?_, hrow, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; rw [hrule] at hk; cases hk
  · rw [hrule]; intro hk; cases hk
  · rw [hrow]; exact hccw
  · rw [hrow]
    intro hbad
    rw [hccw] at hbad
    cases hbad
  · rw [hrow]; rfl
  · rw [hrow]; rfl
  · rw [hrow]; rfl
  · rw [hrow]; rfl
  · rw [hrow]; rfl
  · rw [hrow]
    show (setRawCcw b.core.raw .free).cwPort = b.core.raw.cwPort
    exact cwPort_setRawCcw _ _
  · rw [hrow]
    intro hbad
    have hx : DeclFlush.flushed = .unflushed := hbad.1
    cases hx

/-! ## Frames of the next gap and of the A-side verdict slots -/

def RetireRuleCorrected : SRuleCorrected -> Prop
  | .retireFused => True
  | .retireLaunch => True
  | .retireBackward => True
  | .retireDeposit => True
  | _ => False

private theorem step_raw_frameCorrected {a b x y : SNode} {k : SRuleCorrected} (h : SRowStepCorrected a b k x y) :
    (RetireRuleCorrected k -> x.core.raw = a.core.raw ∧ y.core.raw = b.core.raw) ∧
    (IsNewCorrected k = true -> k ≠ .freshFlush -> y.core.raw.ccwPort = b.core.raw.ccwPort) ∧
    (IsNewCorrected k = true -> x.core.raw.ccwPort = a.core.raw.ccwPort) ∧
    (IsNewCorrected k = true -> x.core.raw.cwPort = some .heldDenial ->
        a.core.raw.cwPort = some .heldDenial) ∧
    (IsNewCorrected k = true -> y.core.raw.cwPort = some .heldDenial ->
        b.core.raw.cwPort = some .heldDenial) := by
  cases h with
  | core =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshFlush hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ hne; exact absurd rfl hne
      · intro _; rfl
      · intro _ hx; exact hx
      · intro _ hx
        have hx' : (setRawCcw b.core.raw .free).cwPort = some .heldDenial := hx
        rwa [cwPort_setRawCcw] at hx'
  | freshLaunch hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _
        show declRaw.ccwPort = b.core.raw.ccwPort
        rw [hg.2.2.2.1.1]
        rfl
      · intro _
        exact ccwPort_setRawCw a.core.raw .waiting
      · intro _ hx
        exact absurd hx (cwPort_setRawCw_neCorrected a.core.raw .waiting .heldDenial (by simp))
      · intro _ hx
        cases hx
  | freshForward hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _
        show declRaw.ccwPort = b.core.raw.ccwPort
        rw [hg.2.2.1.1]
        rfl
      · intro _
        show emptyRaw.ccwPort = a.core.raw.ccwPort
        rw [hg.2.1]
        rfl
      · intro _ hx
        cases hx
      · intro _ hx
        cases hx
  | retireFused hg =>
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ hx => hx, fun _ hx => hx⟩
  | retireLaunch hg =>
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ hx => hx, fun _ hx => hx⟩
  | retireBackward hg =>
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ hx => hx, fun _ hx => hx⟩
  | retireDeposit hg =>
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ hx => hx, fun _ hx => hx⟩
  | adoptDeposit hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _; rfl
      · intro _; rfl
      · intro _ hx; exact hx
      · intro _ hx; exact hx
  | directAdopt hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _; rfl
      · intro _
        exact ccwPort_setRawCw a.core.raw (adoptCwOfCorrected a.payload)
      · intro _ hx
        exact absurd hx (cwPort_setRawCw_neCorrected a.core.raw (adoptCwOfCorrected a.payload) .heldDenial
          (adoptCwOfCorrected_ne_denial a.payload))
      · intro _ hx; exact hx
  | handoffArm hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hk; cases hk
      · intro _ _; rfl
      · intro _
        exact ccwPort_setRawCw a.core.raw .toSend
      · intro _ hx
        exact absurd hx (cwPort_setRawCw_neCorrected a.core.raw .toSend .heldDenial (by simp))
      · intro _ hx; exact hx

private theorem step_guardsCorrected {a b x y : SNode} {k : SRuleCorrected} (h : SRowStepCorrected a b k x y) :
    (k = .freshFlush -> a.flush = .unflushed) ∧
    (k = .freshLaunch -> a.splice = .armed ∧ a.flush = .unflushed) ∧
    (k = .freshForward -> a.flush = .unflushed) ∧
    (k = .handoffArm -> a.splice = .retired) ∧
    (k = .retireDeposit -> a.splice = .adopted ∧ b.witness = .token) ∧
    (k = .retireFused -> a.splice = .adopted ∧ b.splice = .bridged ∧
        a.witness = .none ∧ b.witness = .none) ∧
    (k = .directAdopt -> AckDischarged a ∧ a.payload ≠ none) ∧
    (k = .adoptDeposit -> a.core.outgoing = .committing ∧ b.payload ≠ none) := by
  cases h with
  | core =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshFlush hg =>
      refine ⟨fun _ => hg.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshLaunch hg =>
      refine ⟨?_, fun _ => ⟨hg.1, hg.2.1⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshForward hg =>
      refine ⟨?_, ?_, fun _ => hg.1, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireFused hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_,
        fun _ => ⟨hg.1, hg.2.2.1, hg.2.1, hg.2.2.2.2.2.1⟩, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireLaunch hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireBackward hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireDeposit hg =>
      refine ⟨?_, ?_, ?_, ?_, fun _ => ⟨hg.1, hg.2.2⟩, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | adoptDeposit hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨hg.1.2.1, hg.2.1⟩⟩ <;> (intro hk; cases hk)
  | directAdopt hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨hg.2.2.2, hg.2.1⟩, ?_⟩ <;> (intro hk; cases hk)
  | handoffArm hg =>
      refine ⟨?_, ?_, ?_, fun _ => hg.1, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)

/-- The `(B,C)` side is framed by the `Corrected` splice, exactly as in `Original`, with
the fused retirement added to the framing retirement rows and the two adopt
rows carrying their ack-ordering guards. -/
theorem splice_frames_next_gapCorrected (a b : SNode) :
    (RetireRuleCorrected (spliceRuleCorrected a b) ->
      (spliceRowCorrected a b).1.core.raw = a.core.raw ∧
        (spliceRowCorrected a b).2.core.raw = b.core.raw) ∧
    (IsNewCorrected (spliceRuleCorrected a b) = true -> spliceRuleCorrected a b ≠ .freshFlush ->
      (spliceRowCorrected a b).2.core.raw.ccwPort = b.core.raw.ccwPort) ∧
    (spliceRuleCorrected a b = .freshFlush -> a.flush = .unflushed) ∧
    (spliceRuleCorrected a b = .freshLaunch -> a.splice = .armed ∧ a.flush = .unflushed) ∧
    (spliceRuleCorrected a b = .freshForward -> a.flush = .unflushed) ∧
    (spliceRuleCorrected a b = .handoffArm -> a.splice = .retired) ∧
    (spliceRuleCorrected a b = .retireDeposit -> a.splice = .adopted ∧ b.witness = .token) ∧
    (spliceRuleCorrected a b = .retireFused -> a.splice = .adopted ∧ b.splice = .bridged ∧
        a.witness = .none ∧ b.witness = .none) ∧
    (spliceRuleCorrected a b = .directAdopt -> AckDischarged a ∧ a.payload ≠ none) ∧
    (spliceRuleCorrected a b = .adoptDeposit -> a.core.outgoing = .committing ∧ b.payload ≠ none) := by
  have hf := step_raw_frameCorrected (spliceRowCorrected_spec a b)
  have hg := step_guardsCorrected (spliceRowCorrected_spec a b)
  exact ⟨hf.1, hf.2.1, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1,
    hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2⟩

/-- No `Corrected` splice row turns an old `(B,C)` verdict into an A-side verdict. -/
theorem splice_never_retags_denialCorrected (a b : SNode) (h : IsNewCorrected (spliceRuleCorrected a b) = true) :
    ((spliceRowCorrected a b).1.core.raw.cwPort = some .heldDenial ->
        a.core.raw.cwPort = some .heldDenial) ∧
    ((spliceRowCorrected a b).2.core.raw.cwPort = some .heldDenial ->
        b.core.raw.cwPort = some .heldDenial) ∧
    (spliceRowCorrected a b).1.core.raw.ccwPort = a.core.raw.ccwPort ∧
    (∀ w : RetireWitness, w = .none ∨ w = .token) := by
  have hf := step_raw_frameCorrected (spliceRowCorrected_spec a b)
  exact ⟨hf.2.2.2.1 h, hf.2.2.2.2 h, hf.2.2.1 h, witness_carries_no_verdict⟩

/-! ## What creates the fresh-declaration mark and the `.retired` mark -/

private theorem step_flush_createdCorrected {a b x y : SNode} {k : SRuleCorrected} (h : SRowStepCorrected a b k x y)
    (ha : a.flush = .none) (hb : b.flush = .none) :
    x.flush ≠ .none ∨ y.flush ≠ .none -> k = .handoffArm := by
  cases h with
  | core =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | freshFlush hg =>
      intro _; exfalso; have hz := hg.1; rw [ha] at hz; cases hz
  | freshLaunch hg =>
      intro _; exfalso; have hz := hg.2.1; rw [ha] at hz; cases hz
  | freshForward hg =>
      intro _; exfalso; have hz := hg.1; rw [ha] at hz; cases hz
  | retireFused hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | retireLaunch hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | retireBackward hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | retireDeposit hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | adoptDeposit hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | directAdopt hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact h1 ha
      · exact h1 hb
  | handoffArm hg => intro _; rfl

private theorem step_retired_createdCorrected {a b x y : SNode} {k : SRuleCorrected} (h : SRowStepCorrected a b k x y)
    (ha : a.splice ≠ .retired) (hb : b.splice ≠ .retired) :
    x.splice = .retired ∨ y.splice = .retired ->
      (k = .retireDeposit ∧ b.witness = .token) ∨ (k = .retireFused ∧ RetireFused a b) := by
  cases h with
  | core =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact ha h1
      · have h2 : (if committedNow b.core (commitRow a.core b.core).2 then
            SpliceCtl.bridged else b.splice) = .retired := h1
        split at h2
        · cases h2
        · exact hb h2
  | freshFlush hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact ha h1
      · exact hb h1
  | freshLaunch hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact ha h1
      · exact hb h1
  | freshForward hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact ha h1
      · exact hb h1
  | retireFused hg => intro _; exact Or.inr ⟨rfl, hg⟩
  | retireLaunch hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact ha h1
      · have h2 : SpliceCtl.drained = .retired := h1
        cases h2
  | retireBackward hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact ha h1
      · exact hb h1
  | retireDeposit hg => intro _; exact Or.inl ⟨rfl, hg.2.2⟩
  | adoptDeposit hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · exact ha h1
      · exact hb h1
  | directAdopt hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · have h2 : SpliceCtl.adopted = .retired := h1
        cases h2
      · exact hb h1
  | handoffArm hg =>
      intro hx; exfalso; rcases hx with h1 | h1
      · have h2 : SpliceCtl.armed = .retired := h1
        cases h2
      · exact hb h1

/-- A fresh declaration mark is created only by the post-retirement handoff. -/
theorem unflushed_only_from_armCorrected (a b : SNode) (ha : a.flush = .none) (hb : b.flush = .none)
    (h : (spliceRowCorrected a b).1.flush ≠ .none ∨ (spliceRowCorrected a b).2.flush ≠ .none) :
    spliceRuleCorrected a b = .handoffArm :=
  step_flush_createdCorrected (spliceRowCorrected_spec a b) ha hb h

/-- The `.retired` mark is created either by the arrival of a retirement
witness, or -- and this is new in `Corrected` -- by the fused length-one retirement,
which needs no witness because the bridge is the immediate neighbour. -/
theorem retired_only_from_witness_or_fusedCorrected (a b : SNode)
    (ha : a.splice ≠ .retired) (hb : b.splice ≠ .retired)
    (h : (spliceRowCorrected a b).1.splice = .retired ∨ (spliceRowCorrected a b).2.splice = .retired) :
    (spliceRuleCorrected a b = .retireDeposit ∧ b.witness = .token) ∨
      (spliceRuleCorrected a b = .retireFused ∧ RetireFused a b) :=
  step_retired_createdCorrected (spliceRowCorrected_spec a b) ha hb h

/-! ## The retirement witness is still conserved -/

private theorem step_witnessCorrected {a b x y : SNode} {k : SRuleCorrected} (h : SRowStepCorrected a b k x y) :
    (k = .retireLaunch ->
      x.witness = .token ∧ y.witness = .none ∧ y.splice = .drained) ∧
    (k = .retireBackward -> x.witness = .token ∧ y.witness = .none) ∧
    (k = .retireDeposit -> y.witness = .none) ∧
    (k = .retireFused -> x.witness = .none ∧ y.witness = .none ∧ y.splice = .drained) := by
  cases h with
  | core => refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshFlush hg => refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshLaunch hg => refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshForward hg => refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireFused hg =>
      refine ⟨?_, ?_, ?_, fun _ => ⟨hg.2.1, hg.2.2.2.2.2.1, rfl⟩⟩ <;> (intro hk; cases hk)
  | retireLaunch hg =>
      refine ⟨fun _ => ⟨rfl, hg.2.2.2.2.2, rfl⟩, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireBackward hg =>
      refine ⟨?_, fun _ => ⟨rfl, rfl⟩, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireDeposit hg => refine ⟨?_, ?_, fun _ => rfl, ?_⟩ <;> (intro hk; cases hk)
  | adoptDeposit hg => refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | directAdopt hg => refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | handoffArm hg => refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)

/-- Exactly one retirement witness per commit, never duplicated; and the fused
row spends the bridge without ever creating a witness at all. -/
theorem retire_witness_conservationCorrected (a b : SNode) :
    (spliceRuleCorrected a b = .retireLaunch ->
      (spliceRowCorrected a b).1.witness = .token ∧ (spliceRowCorrected a b).2.witness = .none ∧
        (spliceRowCorrected a b).2.splice = .drained ∧
        ¬ RetireLaunch (spliceRowCorrected a b).1 (spliceRowCorrected a b).2) ∧
    (spliceRuleCorrected a b = .retireBackward ->
      (spliceRowCorrected a b).1.witness = .token ∧ (spliceRowCorrected a b).2.witness = .none) ∧
    (spliceRuleCorrected a b = .retireDeposit -> (spliceRowCorrected a b).2.witness = .none) ∧
    (spliceRuleCorrected a b = .retireFused ->
      (spliceRowCorrected a b).1.witness = .none ∧ (spliceRowCorrected a b).2.witness = .none ∧
        (spliceRowCorrected a b).2.splice = .drained ∧
        ¬ RetireFused (spliceRowCorrected a b).1 (spliceRowCorrected a b).2) := by
  have hw := step_witnessCorrected (spliceRowCorrected_spec a b)
  refine ⟨?_, hw.2.1, hw.2.2.1, ?_⟩
  · intro hk
    obtain ⟨h1, h2, h3⟩ := hw.1 hk
    refine ⟨h1, h2, h3, ?_⟩
    intro hbad
    have hx := hbad.2.2.1
    rw [h3] at hx
    cases hx
  · intro hk
    obtain ⟨h1, h2, h3⟩ := hw.2.2.2 hk
    refine ⟨h1, h2, h3, ?_⟩
    intro hbad
    have hx := hbad.2.2.1
    rw [h3] at hx
    cases hx

/-! ## The adopt rows never produce a verdict -/

private theorem step_adoptCorrected {a b x y : SNode} {k : SRuleCorrected} (h : SRowStepCorrected a b k x y) :
    (k = .adoptDeposit -> x.core.raw = a.core.raw ∧ y.core.raw = b.core.raw ∧
        x.payload = b.payload) ∧
    (k = .directAdopt -> x.core.raw.cwPort ≠ some .heldCandidate ∧
        x.core.raw.cwPort ≠ some .heldDenial ∧ y = b ∧ x.splice = .adopted) := by
  cases h with
  | core => refine ⟨?_, ?_⟩ <;> (intro hk; cases hk)
  | freshFlush hg => refine ⟨?_, ?_⟩ <;> (intro hk; cases hk)
  | freshLaunch hg => refine ⟨?_, ?_⟩ <;> (intro hk; cases hk)
  | freshForward hg => refine ⟨?_, ?_⟩ <;> (intro hk; cases hk)
  | retireFused hg => refine ⟨?_, ?_⟩ <;> (intro hk; cases hk)
  | retireLaunch hg => refine ⟨?_, ?_⟩ <;> (intro hk; cases hk)
  | retireBackward hg => refine ⟨?_, ?_⟩ <;> (intro hk; cases hk)
  | retireDeposit hg => refine ⟨?_, ?_⟩ <;> (intro hk; cases hk)
  | adoptDeposit hg => refine ⟨fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩ <;> (intro hk; cases hk)
  | directAdopt hg =>
      refine ⟨?_, fun _ => ⟨?_, ?_, rfl, rfl⟩⟩
      · intro hk; cases hk
      · exact cwPort_setRawCw_neCorrected a.core.raw (adoptCwOfCorrected a.payload) .heldCandidate
          (adoptCwOfCorrected_ne_candidate a.payload)
      · exact cwPort_setRawCw_neCorrected a.core.raw (adoptCwOfCorrected a.payload) .heldDenial
          (adoptCwOfCorrected_ne_denial a.payload)
  | handoffArm hg => refine ⟨?_, ?_⟩ <;> (intro hk; cases hk)

/-- **The `Corrected` adopt rows write no verdict.**  The deposit row does not touch
either raw node at all -- it only advances the imported commit lifecycle and
transports the snapshot -- and the adopt row writes `adoptCwOfCorrected`, which by
`adoptCorrected_ne_candidate`/`adoptCorrected_ne_denial` is never a verdict. -/
theorem adopt_rows_write_no_verdictCorrected (a b : SNode) :
    (spliceRuleCorrected a b = .adoptDeposit ->
      (spliceRowCorrected a b).1.core.raw = a.core.raw ∧
        (spliceRowCorrected a b).2.core.raw = b.core.raw ∧
        (spliceRowCorrected a b).1.payload = b.payload) ∧
    (spliceRuleCorrected a b = .directAdopt ->
      (spliceRowCorrected a b).1.core.raw.cwPort ≠ some .heldCandidate ∧
        (spliceRowCorrected a b).1.core.raw.cwPort ≠ some .heldDenial ∧
        (spliceRowCorrected a b).2 = b ∧ (spliceRowCorrected a b).1.splice = .adopted) :=
  step_adoptCorrected (spliceRowCorrected_spec a b)

/-- Restated on the carrier: no optional snapshot at all can be adopted into a
verdict. -/
theorem adoptCorrected_carrier_has_no_verdict :
    (∀ s : Option SnapPhase, adoptCwOfCorrected s ≠ CwPort.heldCandidate) ∧
      (∀ s : Option SnapPhase, adoptCwOfCorrected s ≠ CwPort.heldDenial) :=
  ⟨adoptCwOfCorrected_ne_candidate, adoptCwOfCorrected_ne_denial⟩

/-! ## The ack-before-adopt ordering, as a literal three-firing pipeline -/

/-- The source root, with an explicit optional payload slot. -/
def sOwnerP (ccw : CcwPort) (inc : InControl) (ctl : CommitCtl) (lease : CommitIn)
    (live : Bool) (pay : Option SnapPhase) : SNode :=
  ⟨ownerNode ccw inc ctl lease live, none, pay, .inactive, .none, .none⟩

theorem sOwner_eq_sOwnerP (ccw : CcwPort) (inc : InControl) (ctl : CommitCtl)
    (lease : CommitIn) (live : Bool) :
    sOwner ccw inc ctl lease live = sOwnerP ccw inc ctl lease live none := rfl

private theorem rawOwner_setRawCw_eq (n : Node) (v : CwPort) :
    rawOwner (setRawCw n v) = true -> v = .heldCandidate := by
  cases n with
  | interior w =>
      show rawOwner (Node.interior w) = true -> v = .heldCandidate
      intro h; cases h
  | root ch cw ccw out inc =>
      show rawOwner (Node.root ch v ccw out inc) = true -> v = .heldCandidate
      cases ch <;> cases out <;> cases v <;> intro h <;> first | rfl | cases h

/-- **The `Original` defect that `Corrected` repairs.**  `Original`'s adopt row writes
`A.cw := adoptCwOf s`, a value that is never `heldCandidate`; therefore
`rawOwner` falls in the same firing, `Owner` fails, and the imported
`sourceAck` row -- the only row that returns `A.outgoing` to `.clean` -- is
disabled for ever.  `A`'s commit lifecycle is stuck at `.committedReceived`. -/
theorem original_adopt_kills_sourceAck (a : SNode) (s : Option SnapPhase) :
    ¬ SourceAck (adoptL a s).core := by
  intro h
  have hx : rawOwner (setRawCw a.core.raw (adoptCwOf s)) = true := h.1.1
  exact adoptCwOf_ne_candidate s (rawOwner_setRawCw_eq a.core.raw (adoptCwOf s) hx)

/-- **The ordering guard.**  While the source acknowledgement is pending
(`A.outgoing = .committedReceived`) neither adopt row of `Corrected` is enabled:
`DirectAdopt` demands `.clean`, `AdoptDeposit` demands `.committing`. -/
theorem adopt_disabled_while_ack_pendingCorrected (a b : SNode) (h : AckPending a) :
    ¬ DirectAdopt a ∧ ¬ AdoptDeposit a b := by
  constructor
  · intro hd
    have hx : CommitCtl.committedReceived = .clean := h.symm.trans hd.2.2.2
    cases hx
  · intro hd
    have hx : CommitCtl.committedReceived = .committing := h.symm.trans hd.1.2.1
    cases hx

/-- Conversely, the clockwise-writing adopt row can only fire once the ack has
been discharged. -/
theorem directAdopt_needs_ack_dischargedCorrected (a : SNode) (h : DirectAdopt a) :
    AckDischarged a := h.2.2.2

private theorem run_sourceAck (a b : CNode) (h : SourceAck a) :
    run a b = { rule := .sourceAck, left := setOut a .clean, right := b,
                valid := .sourceAck h } := by
  simp only [run, dif_pos h]

private theorem commitRule_sourceAck (a b : CNode) (h : SourceAck a) :
    commitRule a b = .sourceAck :=
  congrArg Result.rule (run_sourceAck a b h)

/-- Firing 1.  The COMMITTED receipt lands at `A`.  `Corrected` performs exactly the
imported `committedDeposit` core update and transports the snapshot into
`A.payload`; the clockwise port is untouched, so `A` is still `Owner`. -/
theorem ackCorrected_deposit_fires (ccw : CcwPort) (inc : InControl) (lease : CommitIn)
    (live : Bool) (snap : SnapPhase) :
    spliceRuleCorrected (sOwnerP ccw inc .committing lease live none)
        (sCell .committedBack .none .none (some snap)) = .adoptDeposit ∧
    spliceRowCorrected (sOwnerP ccw inc .committing lease live none)
        (sCell .committedBack .none .none (some snap))
      = (sOwnerP ccw inc .committedReceived lease live (some snap),
         sCell .none .none .none none) := by
  let a := sOwnerP ccw inc .committing lease live none
  let b := sCell .committedBack .none .none (some snap)
  have h1 : ¬ FreshFlush a b := by intro h; cases h.1
  have h2 : ¬ FreshLaunch a b := by intro h; cases h.1
  have h3 : ¬ FreshForward a b := by intro h; cases h.1
  have hf : ¬ RetireFused a b := by intro h; cases h.1
  have h4 : ¬ RetireLaunch a b := by intro h; cases h.1.1
  have h5 : ¬ RetireBackward a b := by intro h; cases h.1.1
  have h6 : ¬ RetireDeposit a b := by intro h; cases h.1
  have hg : AdoptDeposit a b := ⟨⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩⟩, (by intro hz; cases hz), rfl⟩
  have hd := dispatchCorrected_adoptDeposit a b h1 h2 h3 hf h4 h5 h6 hg
  exact ⟨ruleCorrected_of_dispatch hd, rowCorrected_of_dispatch hd⟩

/-- Firing 2.  The ack is pending, both adopt rows are disabled, and the row
that fires is the *imported* `sourceAck`, which returns `A.outgoing` to
`.clean` and touches nothing else. -/
theorem ackCorrected_sourceAck_fires (ccw : CcwPort) (inc : InControl) (lease : CommitIn)
    (live : Bool) (snap : SnapPhase) :
    AckPending (sOwnerP ccw inc .committedReceived lease live (some snap)) ∧
    ¬ DirectAdopt (sOwnerP ccw inc .committedReceived lease live (some snap)) ∧
    ¬ AdoptDeposit (sOwnerP ccw inc .committedReceived lease live (some snap))
        (sCell .none .none .none none) ∧
    spliceRuleCorrected (sOwnerP ccw inc .committedReceived lease live (some snap))
        (sCell .none .none .none none) = .core .sourceAck ∧
    spliceRowCorrected (sOwnerP ccw inc .committedReceived lease live (some snap))
        (sCell .none .none .none none)
      = (sOwnerP ccw inc .clean lease live (some snap), sCell .none .none .none none) := by
  let a := sOwnerP ccw inc .committedReceived lease live (some snap)
  let b := sCell .none .none .none none
  have hpend : AckPending a := rfl
  obtain ⟨hnd, hna⟩ := adopt_disabled_while_ack_pendingCorrected a b hpend
  have h1 : ¬ FreshFlush a b := by intro h; cases h.1
  have h2 : ¬ FreshLaunch a b := by intro h; cases h.1
  have h3 : ¬ FreshForward a b := by intro h; cases h.1
  have hf : ¬ RetireFused a b := by intro h; cases h.1
  have h4 : ¬ RetireLaunch a b := by intro h; cases h.1.1
  have h5 : ¬ RetireBackward a b := by intro h; cases h.1.1
  have h6 : ¬ RetireDeposit a b := by intro h; cases h.1
  have h9 : ¬ HandoffArm a := by intro h; cases h.1
  have hsa : SourceAck a.core := ⟨⟨rfl, rfl⟩, rfl⟩
  refine ⟨hpend, hnd, hna, ?_, ?_⟩
  · rw [spliceRuleCorrected_core_of a b h1 h2 h3 hf h4 h5 h6 hna hnd h9,
      commitRule_sourceAck a.core b.core hsa]
  · rw [spliceRowCorrected_core_of a b h1 h2 h3 hf h4 h5 h6 hna hnd h9,
      source_ack a.core b.core hsa]
    rfl

/-- Firing 3.  Only now, with the ack discharged, does the adopt row write the
clockwise port -- and it writes the *corrected* `adoptCwCorrected` of the transported
snapshot. -/
theorem ackCorrected_adopt_fires (ccw : CcwPort) (inc : InControl) (lease : CommitIn)
    (live : Bool) (snap : SnapPhase) :
    AckDischarged (sOwnerP ccw inc .clean lease live (some snap)) ∧
    spliceRuleCorrected (sOwnerP ccw inc .clean lease live (some snap))
        (sCell .none .none .none none) = .directAdopt ∧
    spliceRowCorrected (sOwnerP ccw inc .clean lease live (some snap))
        (sCell .none .none .none none)
      = (⟨⟨.root .out1 (adoptCwCorrected snap) ccw .finalReady inc, live, .clean, lease, .none⟩,
           none, none, .adopted, .none, .none⟩,
         sCell .none .none .none none) := by
  let a := sOwnerP ccw inc .clean lease live (some snap)
  let b := sCell .none .none .none none
  have h1 : ¬ FreshFlush a b := by intro h; cases h.1
  have h2 : ¬ FreshLaunch a b := by intro h; cases h.1
  have h3 : ¬ FreshForward a b := by intro h; cases h.1
  have hf : ¬ RetireFused a b := by intro h; cases h.1
  have h4 : ¬ RetireLaunch a b := by intro h; cases h.1.1
  have h5 : ¬ RetireBackward a b := by intro h; cases h.1.1
  have h6 : ¬ RetireDeposit a b := by intro h; cases h.1
  have h7 : ¬ AdoptDeposit a b := by intro h; cases h.1.2.1
  have hg : DirectAdopt a := ⟨rfl, (by intro hz; cases hz), rfl, rfl⟩
  have hd := dispatchCorrected_directAdopt a b h1 h2 h3 hf h4 h5 h6 h7 hg
  exact ⟨rfl, ruleCorrected_of_dispatch hd, rowCorrected_of_dispatch hd⟩

/-- **The pipeline, in order.**  Deposit, then the imported source
acknowledgement, then the adopt: three firings on the same edge, in the only
order the `Corrected` guards allow. -/
theorem ackCorrected_precedes_adopt (ccw : CcwPort) (inc : InControl) (lease : CommitIn)
    (live : Bool) (snap : SnapPhase) :
    spliceRowCorrected (sOwnerP ccw inc .committing lease live none)
        (sCell .committedBack .none .none (some snap))
      = (sOwnerP ccw inc .committedReceived lease live (some snap),
         sCell .none .none .none none) ∧
    spliceRowCorrected (sOwnerP ccw inc .committedReceived lease live (some snap))
        (sCell .none .none .none none)
      = (sOwnerP ccw inc .clean lease live (some snap), sCell .none .none .none none) ∧
    spliceRowCorrected (sOwnerP ccw inc .clean lease live (some snap))
        (sCell .none .none .none none)
      = (⟨⟨.root .out1 (adoptCwCorrected snap) ccw .finalReady inc, live, .clean, lease, .none⟩,
           none, none, .adopted, .none, .none⟩,
         sCell .none .none .none none) ∧
    (∀ b : SNode, ¬ DirectAdopt (sOwnerP ccw inc .committedReceived lease live (some snap)) ∧
        ¬ AdoptDeposit (sOwnerP ccw inc .committedReceived lease live (some snap)) b) := by
  refine ⟨(ackCorrected_deposit_fires ccw inc lease live snap).2,
    (ackCorrected_sourceAck_fires ccw inc lease live snap).2.2.2.2,
    (ackCorrected_adopt_fires ccw inc lease live snap).2.2, ?_⟩
  intro b
  exact adopt_disabled_while_ack_pendingCorrected _ b rfl

/-! ## The `Corrected` splice corridor

The corridor is the physical interval left behind by one commit at `B`:
offset `0` is `A` (already `adopted`, i.e. the pipeline of the previous
section has run to completion), offsets `1 .. x-1` are the cleaned former
capture cells, offset `x` is former `B`, carrying the stationary bridge.

Unlike `ShortGapSpliceCorridor.SFrame`, the `Corrected` frame admits `x = 1`: the
fused row supplies the missing length-one firing.
-/

structure SFrameCorrected where
  x : Nat
  hx : 1 ≤ x
  aCw : CwPort
  haCw : aCw ≠ .heldCandidate
  aCcw : CcwPort
  aInc : InControl
  aCtl : CommitCtl
  aLease : CommitIn
  bCw : CwPort
  hbCw : bCw = .heldDenial ∨ bCw = .heldCandidate
  bOut : OutControl
  bCtl : CommitCtl
  bSnap : SnapPhase

/-- Padding to a length-two `Original` frame.  Only the *length* field differs, so
every node-level `Original` fact -- about `aRaw`, `bridgeRaw`, `aNode`, `bridgeN`,
`rawOwner_aRaw`, `settledCw_bridgeRaw`, `captureRow_aRaw` -- transports along
`pad` definitionally.  Nothing about the corridor's geometry is transported. -/
def SFrameCorrected.pad (F : SFrameCorrected) : SFrame :=
  ⟨2, by omega, F.aCw, F.haCw, F.aCcw, F.aInc, F.aCtl, F.aLease, F.bCw, F.hbCw,
    F.bOut, F.bCtl, F.bSnap⟩

/-- `A` at offset `0`, in splice lifecycle state `sp`. -/
abbrev aN (F : SFrameCorrected) (sp : SpliceCtl) : SNode := aNode F.pad sp

/-- Former `B` at offset `x`, in splice lifecycle state `sp`. -/
abbrev bN (F : SFrameCorrected) (sp : SpliceCtl) : SNode := bridgeN F.pad sp

/-! ### The literal pair firings of the `Corrected` corridor -/

/-- The conversion at the bridge: the settled old `(B,C)` verdict becomes a
retirement witness on the last capture cell.  The bridge is spent. -/
theorem rowCorrected_convert (F : SFrameCorrected) :
    spliceRowCorrected (cellN .none) (bN F .bridged) = (cellN .token, bN F .drained) := by
  have h1 : ¬ FreshFlush (cellN .none) (bN F .bridged) := by intro h; cases h.1
  have h2 : ¬ FreshLaunch (cellN .none) (bN F .bridged) := by intro h; cases h.1
  have h3 : ¬ FreshForward (cellN .none) (bN F .bridged) := by intro h; cases h.1
  have hf : ¬ RetireFused (cellN .none) (bN F .bridged) := by intro h; cases h.1
  have hg : RetireLaunch (cellN .none) (bN F .bridged) :=
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, settledCw_bridgeRaw F.pad, rfl⟩
  exact rowCorrected_of_dispatch (dispatchCorrected_retireLaunch _ _ h1 h2 h3 hf hg)

/-- The witness travels one cell towards `A`. -/
theorem rowCorrected_carry :
    spliceRowCorrected (cellN .none) (cellN .token) = (cellN .token, cellN .none) := by
  have h1 : ¬ FreshFlush (cellN .none) (cellN .token) := by intro h; cases h.1
  have h2 : ¬ FreshLaunch (cellN .none) (cellN .token) := by intro h; cases h.1
  have h3 : ¬ FreshForward (cellN .none) (cellN .token) := by intro h; cases h.1
  have hf : ¬ RetireFused (cellN .none) (cellN .token) := by intro h; cases h.2.2.1
  have h4 : ¬ RetireLaunch (cellN .none) (cellN .token) := by intro h; cases h.2.2.1
  have hg : RetireBackward (cellN .none) (cellN .token) := ⟨⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩
  exact rowCorrected_of_dispatch (dispatchCorrected_retireBackward _ _ h1 h2 h3 hf h4 hg)

/-- The witness lands at the adopted `A`, which retires. -/
theorem rowCorrected_land (F : SFrameCorrected) :
    spliceRowCorrected (aN F .adopted) (cellN .token) = (aN F .retired, cellN .none) := by
  have h1 : ¬ FreshFlush (aN F .adopted) (cellN .token) := by intro h; cases h.1
  have h2 : ¬ FreshLaunch (aN F .adopted) (cellN .token) := by intro h; cases h.1
  have h3 : ¬ FreshForward (aN F .adopted) (cellN .token) := by intro h; cases h.1
  have hf : ¬ RetireFused (aN F .adopted) (cellN .token) := by intro h; cases h.2.2.1
  have h4 : ¬ RetireLaunch (aN F .adopted) (cellN .token) := by intro h; cases h.1.1
  have h5 : ¬ RetireBackward (aN F .adopted) (cellN .token) := by intro h; cases h.1.1
  have hg : RetireDeposit (aN F .adopted) (cellN .token) := ⟨rfl, ⟨rfl, rfl⟩, rfl⟩
  exact rowCorrected_of_dispatch (dispatchCorrected_retireDeposit _ _ h1 h2 h3 hf h4 h5 hg)

/-- **The new row.**  On a length-one corridor `A` and the bridge are
neighbours: one firing converts the old verdict and retires `A`, with no
witness in flight at all.  This is exactly the firing whose absence made
`ShortGapSpliceCorridor.corridor_length_one_stalls` true for `Original`. -/
theorem rowCorrected_fused (F : SFrameCorrected) :
    spliceRowCorrected (aN F .adopted) (bN F .bridged) = (aN F .retired, bN F .drained) := by
  have h1 : ¬ FreshFlush (aN F .adopted) (bN F .bridged) := by intro h; cases h.1
  have h2 : ¬ FreshLaunch (aN F .adopted) (bN F .bridged) := by intro h; cases h.1
  have h3 : ¬ FreshForward (aN F .adopted) (bN F .bridged) := by intro h; cases h.1
  have hne : ¬ SEmpty (aN F .adopted) := by intro h; cases h.1
  have hg : RetireFused (aN F .adopted) (bN F .bridged) :=
    ⟨rfl, rfl, rfl, rfl, settledCw_bridgeRaw F.pad, rfl, hne⟩
  exact rowCorrected_of_dispatch (dispatchCorrected_fused _ _ h1 h2 h3 hg)

/-- Two cleaned cells: nothing is enabled. -/
theorem rowCorrected_cells (w : RetireWitness) :
    spliceRowCorrected (cellN w) (cellN .none) = (cellN w, cellN .none) := by
  cases w <;> rfl

/-- The adopted `A` and a cleaned cell: nothing is enabled. -/
theorem rowCorrected_idleA (F : SFrameCorrected) :
    spliceRowCorrected (aN F .adopted) (cellN .none) = (aN F .adopted, cellN .none) := by
  have hown : ¬ Owner (aN F .adopted).core := by
    intro h
    have hx : rawOwner (aRaw F.pad) = true := h.1
    rw [rawOwner_aRaw F.pad] at hx
    cases hx
  have hcore : spliceRowCorrected (aN F .adopted) (cellN .none) =
      liftPair (aN F .adopted) (cellN .none)
        (commitRow (aN F .adopted).core (cellN .none).core) := by
    refine spliceRowCorrected_core_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.2.2.1
    · intro h; cases h.1.1
    · intro h; cases h.1.1
    · intro h; cases h.2.2
    · intro h; exact h.2.1 rfl
    · intro h; exact h.2.1 rfl
    · intro h; cases h.1
  have hidle : commitRow (aN F .adopted).core (cellN .none).core =
      ((aN F .adopted).core, (cellN .none).core) := by
    refine commitRow_idle_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; exact hown h.1
    · intro h; cases h.1.1
    · intro h; exact h.2.2.2.2 (captureRow_aRaw F.pad _)
    · intro h; exact hown h.1
    · intro h; cases h.1.2
    · intro h; cases h.1.2
    · intro h; cases h.1.1
    · intro h; exact hown h.1
    · intro h; exact hown h.1
  exact spliceRowCorrected_stutter_of _ _ hcore hidle rfl rfl

/-- A spent bridge: no retirement row is enabled against it any more. -/
theorem rowCorrected_idleBridge (F : SFrameCorrected) (w : RetireWitness) :
    spliceRowCorrected (cellN w) (bN F .drained) = (cellN w, bN F .drained) := by
  have hcore : spliceRowCorrected (cellN w) (bN F .drained) =
      liftPair (cellN w) (bN F .drained)
        (commitRow (cellN w).core (bN F .drained).core) := by
    refine spliceRowCorrected_core_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.1
    · intro h; cases h.2.2.1
    · intro h; cases h.2.2.1.1
    · intro h; cases h.1
    · intro h; exact h.2.1 rfl
    · intro h; exact h.2.1 rfl
    · intro h; cases h.1
  have hseed : seedIn (bridgeRaw F.pad) = .reserved := rfl
  have hidle : commitRow (cellN w).core (bN F .drained).core =
      ((cellN w).core, (bN F .drained).core) := by
    refine commitRow_idle_of _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; cases h.1.1
    · intro h; cases h.1.1
    · intro h
      have hx : CommitIn.committed = seedIn (bridgeRaw F.pad) := h.2.1.2
      rw [hseed] at hx
      cases hx
    · intro h; cases h.1.1
    · intro h; cases h.1.2
    · intro h; cases h.1.2
    · intro h; cases h.2.1
    · intro h; cases h.1.1
    · intro h; cases h.1.1
  exact spliceRowCorrected_stutter_of _ _ hcore hidle rfl rfl

/-- At the landed corridor the retired `A` rearms for the *next* episode. -/
theorem rowCorrected_handoff (F : SFrameCorrected) :
    spliceRuleCorrected (aN F .retired) (cellN .none) = .handoffArm ∧
    spliceRowCorrected (aN F .retired) (cellN .none)
      = (sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed, cellN .none) := by
  have h1 : ¬ FreshFlush (aN F .retired) (cellN .none) := by intro h; cases h.1
  have h2 : ¬ FreshLaunch (aN F .retired) (cellN .none) := by intro h; cases h.1
  have h3 : ¬ FreshForward (aN F .retired) (cellN .none) := by intro h; cases h.1
  have hf : ¬ RetireFused (aN F .retired) (cellN .none) := by intro h; cases h.1
  have h4 : ¬ RetireLaunch (aN F .retired) (cellN .none) := by intro h; cases h.1.1
  have h5 : ¬ RetireBackward (aN F .retired) (cellN .none) := by intro h; cases h.1.1
  have h6 : ¬ RetireDeposit (aN F .retired) (cellN .none) := by intro h; cases h.1
  have h7 : ¬ AdoptDeposit (aN F .retired) (cellN .none) := by intro h; exact h.2.1 rfl
  have h8 : ¬ DirectAdopt (aN F .retired) := by intro h; exact h.2.1 rfl
  have hg : HandoffArm (aN F .retired) := ⟨rfl, (by intro hz; cases hz)⟩
  have hd := dispatchCorrected_handoff _ _ h1 h2 h3 hf h4 h5 h6 h7 h8 hg
  exact ⟨ruleCorrected_of_dispatch hd, rowCorrected_of_dispatch hd⟩

/-- The same rearming on a length-one corridor, where `A`'s right neighbour is
the spent bridge itself. -/
theorem rowCorrected_handoffBridge (F : SFrameCorrected) :
    spliceRuleCorrected (aN F .retired) (bN F .drained) = .handoffArm ∧
    spliceRowCorrected (aN F .retired) (bN F .drained)
      = (sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed, bN F .drained) := by
  have h1 : ¬ FreshFlush (aN F .retired) (bN F .drained) := by intro h; cases h.1
  have h2 : ¬ FreshLaunch (aN F .retired) (bN F .drained) := by intro h; cases h.1
  have h3 : ¬ FreshForward (aN F .retired) (bN F .drained) := by intro h; cases h.1
  have hf : ¬ RetireFused (aN F .retired) (bN F .drained) := by intro h; cases h.1
  have h4 : ¬ RetireLaunch (aN F .retired) (bN F .drained) := by intro h; cases h.1.1
  have h5 : ¬ RetireBackward (aN F .retired) (bN F .drained) := by intro h; cases h.1.1
  have h6 : ¬ RetireDeposit (aN F .retired) (bN F .drained) := by intro h; cases h.1
  have h7 : ¬ AdoptDeposit (aN F .retired) (bN F .drained) := by intro h; cases h.2.2
  have h8 : ¬ DirectAdopt (aN F .retired) := by intro h; exact h.2.1 rfl
  have hg : HandoffArm (aN F .retired) := ⟨rfl, (by intro hz; cases hz)⟩
  have hd := dispatchCorrected_handoff _ _ h1 h2 h3 hf h4 h5 h6 h7 h8 hg
  exact ⟨ruleCorrected_of_dispatch hd, rowCorrected_of_dispatch hd⟩

/-! ### The corridor as a configuration on `Fin (x+1)` -/

abbrev SpliceConfigCorrected (F : SFrameCorrected) := Fin (F.x + 1) → SNode

def leftEndCorrected (F : SFrameCorrected) (a : Fin F.x) : Fin (F.x + 1) :=
  ⟨a.val, Nat.lt_succ_of_lt a.isLt⟩

def rightEndCorrected (F : SFrameCorrected) (a : Fin F.x) : Fin (F.x + 1) :=
  ⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩

/-- Scheduling corridor edge `a`: apply the literal `Corrected` splice row to offsets
`a` and `a+1`, and update exactly those two offsets. -/
def spliceGapStepCorrected (F : SFrameCorrected) (cfg : SpliceConfigCorrected F) (a : Fin F.x) : SpliceConfigCorrected F :=
  fun k =>
    if k.val = a.val then (spliceRowCorrected (cfg (leftEndCorrected F a)) (cfg (rightEndCorrected F a))).1
    else if k.val = a.val + 1 then (spliceRowCorrected (cfg (leftEndCorrected F a)) (cfg (rightEndCorrected F a))).2
    else cfg k

theorem spliceGapStepCorrected_of (F : SFrameCorrected) (cfg cfg' : SpliceConfigCorrected F) (a : Fin F.x)
    (hrow : spliceRowCorrected (cfg (leftEndCorrected F a)) (cfg (rightEndCorrected F a))
      = (cfg' (leftEndCorrected F a), cfg' (rightEndCorrected F a)))
    (hframe : ∀ k : Fin (F.x + 1), k.val ≠ a.val → k.val ≠ a.val + 1 → cfg' k = cfg k) :
    spliceGapStepCorrected F cfg a = cfg' := by
  funext k
  unfold spliceGapStepCorrected
  by_cases h1 : k.val = a.val
  · rw [if_pos h1, hrow]
    exact congrArg cfg' (Fin.ext (show (leftEndCorrected F a).val = k.val from h1.symm))
  · rw [if_neg h1]
    by_cases h2 : k.val = a.val + 1
    · rw [if_pos h2, hrow]
      exact congrArg cfg' (Fin.ext (show (rightEndCorrected F a).val = k.val from h2.symm))
    · rw [if_neg h2]
      exact (hframe k h1 h2).symm

theorem spliceGapStepCorrected_id (F : SFrameCorrected) (cfg : SpliceConfigCorrected F) (a : Fin F.x)
    (hrow : spliceRowCorrected (cfg (leftEndCorrected F a)) (cfg (rightEndCorrected F a))
      = (cfg (leftEndCorrected F a), cfg (rightEndCorrected F a))) :
    spliceGapStepCorrected F cfg a = cfg :=
  spliceGapStepCorrected_of F cfg cfg a hrow (fun _ _ _ => rfl)

theorem spliceGapStepCorrected_frame (F : SFrameCorrected) (cfg : SpliceConfigCorrected F) (a : Fin F.x)
    (k : Fin (F.x + 1)) (h1 : k.val ≠ a.val) (h2 : k.val ≠ a.val + 1) :
    spliceGapStepCorrected F cfg a k = cfg k := by
  unfold spliceGapStepCorrected
  rw [if_neg h1, if_neg h2]

/-- The clean lane of the corridor. -/
def corridorNodeCorrected (F : SFrameCorrected) (asp bsp : SpliceCtl) (tok k : Nat) : SNode :=
  if k = 0 then aN F asp
  else if k = F.x then bN F bsp
  else if k = tok then cellN .token
  else cellN .none

def corridorCfgCorrected (F : SFrameCorrected) (asp bsp : SpliceCtl) (tok : Nat) : SpliceConfigCorrected F :=
  fun k => corridorNodeCorrected F asp bsp tok k.val

theorem cfgCorrected_at_zero (F : SFrameCorrected) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h : k.val = 0) : corridorCfgCorrected F asp bsp tok k = aN F asp := by
  unfold corridorCfgCorrected corridorNodeCorrected
  rw [if_pos h]

theorem cfgCorrected_at_top (F : SFrameCorrected) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h : k.val = F.x) : corridorCfgCorrected F asp bsp tok k = bN F bsp := by
  have hx := F.hx
  unfold corridorCfgCorrected corridorNodeCorrected
  rw [if_neg (by omega), if_pos h]

theorem cfgCorrected_at_tok (F : SFrameCorrected) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h0 : k.val ≠ 0) (hx : k.val ≠ F.x) (h : k.val = tok) :
    corridorCfgCorrected F asp bsp tok k = cellN .token := by
  unfold corridorCfgCorrected corridorNodeCorrected
  rw [if_neg h0, if_neg hx, if_pos h]

theorem cfgCorrected_at_cell (F : SFrameCorrected) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h0 : k.val ≠ 0) (hx : k.val ≠ F.x) (h : k.val ≠ tok) :
    corridorCfgCorrected F asp bsp tok k = cellN .none := by
  unfold corridorCfgCorrected corridorNodeCorrected
  rw [if_neg h0, if_neg hx, if_neg h]

theorem cfgCorrected_at_any (F : SFrameCorrected) (asp bsp : SpliceCtl) (tok : Nat)
    (k : Fin (F.x + 1)) (h0 : k.val ≠ 0) (hx : k.val ≠ F.x) :
    corridorCfgCorrected F asp bsp tok k = cellN (if k.val = tok then .token else .none) := by
  by_cases h : k.val = tok
  · rw [cfgCorrected_at_tok F asp bsp tok k h0 hx h, if_pos h]
  · rw [cfgCorrected_at_cell F asp bsp tok k h0 hx h, if_neg h]

theorem cfgCorrected_frame (F : SFrameCorrected) (asp asp' bsp bsp' : SpliceCtl) (tok tok' : Nat)
    (k : Fin (F.x + 1))
    (ha : k.val = 0 → asp' = asp) (hb : k.val = F.x → bsp' = bsp)
    (ht1 : k.val ≠ 0 → k.val ≠ F.x → k.val ≠ tok)
    (ht2 : k.val ≠ 0 → k.val ≠ F.x → k.val ≠ tok') :
    corridorCfgCorrected F asp' bsp' tok' k = corridorCfgCorrected F asp bsp tok k := by
  unfold corridorCfgCorrected corridorNodeCorrected
  by_cases h0 : k.val = 0
  · rw [if_pos h0, if_pos h0, ha h0]
  · rw [if_neg h0, if_neg h0]
    by_cases hx : k.val = F.x
    · rw [if_pos hx, if_pos hx, hb hx]
    · rw [if_neg hx, if_neg hx, if_neg (ht1 h0 hx), if_neg (ht2 h0 hx)]

/-! ### The corridor firings -/

/-- The bridge edge `(x-1, x)`. -/
def convEdgeCorrected (F : SFrameCorrected) : Fin F.x := ⟨F.x - 1, by have := F.hx; omega⟩

/-- The conversion firing (needs an interior cell, hence `x ≥ 2`). -/
theorem step_convertCorrected (F : SFrameCorrected) (h2 : 2 ≤ F.x) :
    spliceGapStepCorrected F (corridorCfgCorrected F .adopted .bridged 0) (convEdgeCorrected F)
      = corridorCfgCorrected F .adopted .drained (F.x - 1) := by
  have hlv : (leftEndCorrected F (convEdgeCorrected F)).val = F.x - 1 := rfl
  have hrv : (rightEndCorrected F (convEdgeCorrected F)).val = F.x := by
    show F.x - 1 + 1 = F.x
    omega
  refine spliceGapStepCorrected_of F _ _ _ ?_ ?_
  · rw [cfgCorrected_at_cell F .adopted .bridged 0 _ (by rw [hlv]; omega) (by rw [hlv]; omega)
          (by rw [hlv]; omega),
        cfgCorrected_at_top F .adopted .bridged 0 _ hrv,
        cfgCorrected_at_tok F .adopted .drained (F.x - 1) _ (by rw [hlv]; omega)
          (by rw [hlv]; omega) hlv,
        cfgCorrected_at_top F .adopted .drained (F.x - 1) _ hrv]
    exact rowCorrected_convert F
  · intro k h1 h2'
    have h1' : k.val ≠ F.x - 1 := h1
    have h2'' : k.val ≠ F.x - 1 + 1 := h2'
    exact cfgCorrected_frame F .adopted .adopted .bridged .drained 0 (F.x - 1) k
      (fun _ => rfl) (fun hk => absurd hk (by omega)) (fun h _ => h) (fun _ _ => h1')

/-- The witness travels one cell towards `A`. -/
theorem step_carryCorrected (F : SFrameCorrected) (j : Nat) (hj2 : 2 ≤ j) (hjx : j ≤ F.x - 1)
    (a : Fin F.x) (ha : a.val = j - 1) :
    spliceGapStepCorrected F (corridorCfgCorrected F .adopted .drained j) a
      = corridorCfgCorrected F .adopted .drained (j - 1) := by
  have hx2 := F.hx
  have hlv : (leftEndCorrected F a).val = j - 1 := ha
  have hrv : (rightEndCorrected F a).val = j := by
    show a.val + 1 = j
    omega
  refine spliceGapStepCorrected_of F _ _ _ ?_ ?_
  · rw [cfgCorrected_at_cell F .adopted .drained j _ (by rw [hlv]; omega) (by rw [hlv]; omega)
          (by rw [hlv]; omega),
        cfgCorrected_at_tok F .adopted .drained j _ (by rw [hrv]; omega) (by rw [hrv]; omega) hrv,
        cfgCorrected_at_tok F .adopted .drained (j - 1) _ (by rw [hlv]; omega)
          (by rw [hlv]; omega) hlv,
        cfgCorrected_at_cell F .adopted .drained (j - 1) _ (by rw [hrv]; omega)
          (by rw [hrv]; omega) (by rw [hrv]; omega)]
    exact rowCorrected_carry
  · intro k h1 h2
    have h1' : k.val ≠ j - 1 := by rw [ha] at h1; exact h1
    have h2' : k.val ≠ j := by rw [ha] at h2; omega
    exact cfgCorrected_frame F .adopted .adopted .drained .drained j (j - 1) k
      (fun _ => rfl) (fun _ => rfl) (fun _ _ => h2') (fun _ _ => h1')

/-- The witness lands at `A`, which retires (needs `x ≥ 2`). -/
theorem step_landCorrected (F : SFrameCorrected) (h2 : 2 ≤ F.x) (a : Fin F.x) (ha : a.val = 0) :
    spliceGapStepCorrected F (corridorCfgCorrected F .adopted .drained 1) a
      = corridorCfgCorrected F .retired .drained 0 := by
  have hlv : (leftEndCorrected F a).val = 0 := ha
  have hrv : (rightEndCorrected F a).val = 1 := by
    show a.val + 1 = 1
    omega
  refine spliceGapStepCorrected_of F _ _ _ ?_ ?_
  · rw [cfgCorrected_at_zero F .adopted .drained 1 _ hlv,
        cfgCorrected_at_tok F .adopted .drained 1 _ (by rw [hrv]; omega) (by rw [hrv]; omega) hrv,
        cfgCorrected_at_zero F .retired .drained 0 _ hlv,
        cfgCorrected_at_cell F .retired .drained 0 _ (by rw [hrv]; omega) (by rw [hrv]; omega)
          (by rw [hrv]; omega)]
    exact rowCorrected_land F
  · intro k h1 h2'
    have h1' : k.val ≠ 0 := by rw [ha] at h1; exact h1
    have h2'' : k.val ≠ 1 := by rw [ha] at h2'; exact h2'
    exact cfgCorrected_frame F .adopted .retired .drained .drained 1 0 k
      (fun hk => absurd hk h1') (fun _ => rfl) (fun _ _ => h2'') (fun _ _ => h1')

/-- **The length-one firing.**  With `x = 1` the single corridor edge carries
the fused row, and the corridor lands in one firing. -/
theorem step_fusedCorrected (F : SFrameCorrected) (hx1 : F.x = 1) (a : Fin F.x) :
    spliceGapStepCorrected F (corridorCfgCorrected F .adopted .bridged 0) a
      = corridorCfgCorrected F .retired .drained 0 := by
  have haLt := a.isLt
  have ha0 : a.val = 0 := by omega
  have hlv : (leftEndCorrected F a).val = 0 := ha0
  have hrv : (rightEndCorrected F a).val = F.x := by
    show a.val + 1 = F.x
    omega
  refine spliceGapStepCorrected_of F _ _ _ ?_ ?_
  · rw [cfgCorrected_at_zero F .adopted .bridged 0 _ hlv,
        cfgCorrected_at_top F .adopted .bridged 0 _ hrv,
        cfgCorrected_at_zero F .retired .drained 0 _ hlv,
        cfgCorrected_at_top F .retired .drained 0 _ hrv]
    exact rowCorrected_fused F
  · intro k h1 h2
    exfalso
    have hk := k.isLt
    rw [ha0] at h1 h2
    omega

/-- Every other edge stutters on the pre-conversion configuration. -/
theorem step_stutter_convertCorrected (F : SFrameCorrected) (a : Fin F.x) (ha : a.val ≠ F.x - 1) :
    spliceGapStepCorrected F (corridorCfgCorrected F .adopted .bridged 0) a
      = corridorCfgCorrected F .adopted .bridged 0 := by
  have haLt := a.isLt
  have hx1 := F.hx
  have hx2 : 2 ≤ F.x := by omega
  have hlv : (leftEndCorrected F a).val = a.val := rfl
  have hrv : (rightEndCorrected F a).val = a.val + 1 := rfl
  refine spliceGapStepCorrected_id F _ _ ?_
  by_cases h0 : a.val = 0
  · rw [cfgCorrected_at_zero F .adopted .bridged 0 _ (by rw [hlv]; omega),
        cfgCorrected_at_cell F .adopted .bridged 0 _ (by rw [hrv]; omega) (by rw [hrv]; omega)
          (by rw [hrv]; omega)]
    exact rowCorrected_idleA F
  · rw [cfgCorrected_at_cell F .adopted .bridged 0 _ (by rw [hlv]; omega) (by rw [hlv]; omega)
          (by rw [hlv]; omega),
        cfgCorrected_at_cell F .adopted .bridged 0 _ (by rw [hrv]; omega) (by rw [hrv]; omega)
          (by rw [hrv]; omega)]
    exact rowCorrected_cells .none

/-- Every edge other than the witness's own edge stutters while it walks. -/
theorem step_stutter_witnessCorrected (F : SFrameCorrected) (hx2 : 2 ≤ F.x) (j : Nat)
    (a : Fin F.x) (ha : a.val ≠ j - 1) :
    spliceGapStepCorrected F (corridorCfgCorrected F .adopted .drained j) a
      = corridorCfgCorrected F .adopted .drained j := by
  have haLt := a.isLt
  have hlv : (leftEndCorrected F a).val = a.val := rfl
  have hrv : (rightEndCorrected F a).val = a.val + 1 := rfl
  refine spliceGapStepCorrected_id F _ _ ?_
  by_cases h0 : a.val = 0
  · rw [cfgCorrected_at_zero F .adopted .drained j _ (by rw [hlv]; omega),
        cfgCorrected_at_cell F .adopted .drained j _ (by rw [hrv]; omega) (by rw [hrv]; omega)
          (by rw [hrv]; omega)]
    exact rowCorrected_idleA F
  · by_cases htop : a.val + 1 = F.x
    · rw [cfgCorrected_at_any F .adopted .drained j _ (by rw [hlv]; omega) (by rw [hlv]; omega),
          cfgCorrected_at_top F .adopted .drained j _ (by rw [hrv]; omega)]
      exact rowCorrected_idleBridge F _
    · rw [cfgCorrected_at_any F .adopted .drained j _ (by rw [hlv]; omega) (by rw [hlv]; omega),
          cfgCorrected_at_cell F .adopted .drained j _ (by rw [hrv]; omega) (by rw [hrv]; omega)
            (by rw [hrv]; omega)]
      exact rowCorrected_cells _

/-! ### The clean-lane configuration of each tail phase -/

def spliceConfigOfCorrected (F : SFrameCorrected) : TailPhase F.x → SpliceConfigCorrected F
  | .convert _ => corridorCfgCorrected F .adopted .bridged 0
  | .back j _ =>
      if j = F.x then corridorCfgCorrected F .adopted .bridged 0
      else corridorCfgCorrected F .adopted .drained j
  | .landed => corridorCfgCorrected F .retired .drained 0

theorem configCorrected_convert (F : SFrameCorrected) (hx : 0 < F.x) :
    spliceConfigOfCorrected F (.convert hx) = corridorCfgCorrected F .adopted .bridged 0 := rfl

theorem configCorrected_back_top (F : SFrameCorrected) (j : Nat) (hj : 1 ≤ j ∧ j ≤ F.x) (h : j = F.x) :
    spliceConfigOfCorrected F (.back j hj) = corridorCfgCorrected F .adopted .bridged 0 := by
  show (if j = F.x then corridorCfgCorrected F .adopted .bridged 0
        else corridorCfgCorrected F .adopted .drained j) = _
  rw [if_pos h]

theorem configCorrected_back_mid (F : SFrameCorrected) (j : Nat) (hj : 1 ≤ j ∧ j ≤ F.x) (h : j ≠ F.x) :
    spliceConfigOfCorrected F (.back j hj) = corridorCfgCorrected F .adopted .drained j := by
  show (if j = F.x then corridorCfgCorrected F .adopted .bridged 0
        else corridorCfgCorrected F .adopted .drained j) = _
  rw [if_neg h]

theorem configCorrected_landed (F : SFrameCorrected) :
    spliceConfigOfCorrected F (.landed : TailPhase F.x) = corridorCfgCorrected F .retired .drained 0 := rfl

/-- The physical retiming of the tail machine: the machine's `convert` step is
pure accounting and is invisible on configurations. -/
def retimeCorrected (F : SFrameCorrected) : TailPhase F.x → TailPhase F.x
  | .convert hx => .back F.x ⟨hx, Nat.le_refl _⟩
  | .back j hj => .back j hj
  | .landed => .landed

theorem retimeCorrected_convert (F : SFrameCorrected) (hx : 0 < F.x) :
    retimeCorrected F (.convert hx) = TailPhase.advance (.convert hx) := rfl

theorem configCorrected_retime (F : SFrameCorrected) (p : TailPhase F.x) :
    spliceConfigOfCorrected F (retimeCorrected F p) = spliceConfigOfCorrected F p := by
  cases p with
  | convert hx =>
      show spliceConfigOfCorrected F (.back F.x ⟨hx, Nat.le_refl _⟩)
        = corridorCfgCorrected F .adopted .bridged 0
      exact configCorrected_back_top F F.x _ rfl
  | back j hj => rfl
  | landed => rfl

/-! ### Local step lemmas of the imported machine -/

private theorem advanceEdge_backCorrected {x j : Nat} (hj : 1 ≤ j ∧ j ≤ x) (b : Fin x)
    (hb : b.val = j - 1) : (TailPhase.back j hj : TailPhase x).advanceEdge = some b := by
  have h1 := hj.1
  have h2 := hj.2
  have hrfl : (TailPhase.back j hj : TailPhase x).advanceEdge = some ⟨j - 1, by omega⟩ := rfl
  rw [hrfl]
  exact congrArg some (Fin.ext hb.symm)

private theorem localStep_hitCorrected {x : Nat} (s : TailPhase x) (a : Fin x)
    (hae : s.advanceEdge = some a) :
    TailPhase.localStep (fun c : Fin x => c) s a = s.advance :=
  TailPhase.localStep_advance (fun c : Fin x => c) s a hae

private theorem localStep_missCorrected {x : Nat} (s : TailPhase x) (a b : Fin x)
    (hae : s.advanceEdge = some b) (h : b ≠ a) :
    TailPhase.localStep (fun c : Fin x => c) s a = s := by
  unfold TailPhase.localStep
  rw [hae]
  exact if_neg h

private theorem advance_back_geCorrected {x j : Nat} (hj : 1 ≤ j ∧ j ≤ x) (h2 : 2 ≤ j)
    (hj' : 1 ≤ j - 1 ∧ j - 1 ≤ x) :
    TailPhase.advance (.back j hj : TailPhase x) = .back (j - 1) hj' := by
  simp only [TailPhase.advance]
  rw [dif_pos h2]

private theorem advance_back_ltCorrected {x j : Nat} (hj : 1 ≤ j ∧ j ≤ x) (h2 : ¬ 2 ≤ j) :
    TailPhase.advance (.back j hj : TailPhase x) = .landed := by
  simp only [TailPhase.advance]
  rw [dif_neg h2]

/-! ### Exact simulation of the tail machine by the literal `Corrected` corridor -/

/-- **Exact simulation on every `back` phase and every corridor edge**, for
every corridor length `x ≥ 1`.  The case `j = x = 1` is the fused row; it is
the case on which `Original` stalled. -/
theorem spliceGapStepCorrected_back (F : SFrameCorrected) (j : Nat) (hj : 1 ≤ j ∧ j ≤ F.x) (a : Fin F.x) :
    spliceGapStepCorrected F (spliceConfigOfCorrected F (.back j hj)) a
      = spliceConfigOfCorrected F (TailPhase.localStep (fun b : Fin F.x => b) (.back j hj) a) := by
  have hx1 := F.hx
  have hj1 := hj.1
  have hj2 := hj.2
  by_cases hhit : a.val = j - 1
  · have hae : (TailPhase.back j hj : TailPhase F.x).advanceEdge = some a :=
      advanceEdge_backCorrected hj a hhit
    rw [localStep_hitCorrected _ a hae]
    by_cases h2 : 2 ≤ j
    · have hj' : 1 ≤ j - 1 ∧ j - 1 ≤ F.x := ⟨by omega, by omega⟩
      rw [advance_back_geCorrected hj h2 hj']
      by_cases htop : j = F.x
      · rw [configCorrected_back_top F j hj htop, configCorrected_back_mid F (j - 1) hj' (by omega)]
        have hae2 : a = convEdgeCorrected F := Fin.ext (by show a.val = F.x - 1; omega)
        rw [hae2, htop]
        exact step_convertCorrected F (by omega)
      · rw [configCorrected_back_mid F j hj htop, configCorrected_back_mid F (j - 1) hj' (by omega)]
        exact step_carryCorrected F j h2 (by omega) a hhit
    · rw [advance_back_ltCorrected hj h2]
      have hjone : j = 1 := by omega
      subst hjone
      by_cases hone : F.x = 1
      · rw [configCorrected_back_top F 1 hj hone.symm]
        rw [configCorrected_landed F]
        exact step_fusedCorrected F hone a
      · rw [configCorrected_back_mid F 1 hj (by omega), configCorrected_landed F]
        exact step_landCorrected F (by omega) a (by omega)
  · have hb : (⟨j - 1, by omega⟩ : Fin F.x) ≠ a := by
      intro hz
      exact hhit (congrArg Fin.val hz).symm
    rw [localStep_missCorrected _ a ⟨j - 1, by omega⟩ (advanceEdge_backCorrected hj _ rfl) hb]
    by_cases htop : j = F.x
    · rw [configCorrected_back_top F j hj htop]
      exact step_stutter_convertCorrected F a (by omega)
    · rw [configCorrected_back_mid F j hj htop]
      exact step_stutter_witnessCorrected F (by omega) j a hhit

/-- The same, at every undischarged phase, through the retiming. -/
theorem spliceGapStepCorrected_phase (F : SFrameCorrected) (p : TailPhase F.x) (hp : 0 < p.debt)
    (a : Fin F.x) :
    spliceGapStepCorrected F (spliceConfigOfCorrected F p) a
      = spliceConfigOfCorrected F (TailPhase.localStep (fun b : Fin F.x => b) (retimeCorrected F p) a) := by
  cases p with
  | convert hx =>
      have hcfg : spliceConfigOfCorrected F (.convert hx) =
          spliceConfigOfCorrected F (.back F.x ⟨hx, Nat.le_refl _⟩) :=
        (configCorrected_back_top F F.x ⟨hx, Nat.le_refl _⟩ rfl).symm
      rw [hcfg]
      exact spliceGapStepCorrected_back F F.x ⟨hx, Nat.le_refl _⟩ a
  | back j hj => exact spliceGapStepCorrected_back F j hj a
  | landed => exact absurd hp (by simp [TailPhase.debt])

/-! ### The corridor inside the `n`-edge scheduler -/

structure SEmbeddingCorrected (F : SFrameCorrected) (n : Nat) where
  edgeAt : Fin F.x → Fin n
  inj : ∀ a b, edgeAt a = edgeAt b → a = b

theorem localStep_embedCorrected {n : Nat} (F : SFrameCorrected) (E : SEmbeddingCorrected F n)
    (q : TailPhase F.x) (a : Fin F.x) :
    TailPhase.localStep E.edgeAt q (E.edgeAt a)
      = TailPhase.localStep (fun b : Fin F.x => b) q a := by
  unfold TailPhase.localStep
  cases hq : q.advanceEdge with
  | none => rfl
  | some b =>
      show (if E.edgeAt b = E.edgeAt a then q.advance else q)
          = (if b = a then q.advance else q)
      by_cases hb : b = a
      · rw [hb, if_pos rfl, if_pos rfl]
      · rw [if_neg (fun hz => hb (E.inj b a hz)), if_neg hb]

theorem localStep_off_corridorCorrected {n : Nat} (F : SFrameCorrected) (E : SEmbeddingCorrected F n)
    (q : TailPhase F.x) (e : Fin n) (he : ∀ a : Fin F.x, E.edgeAt a ≠ e) :
    TailPhase.localStep E.edgeAt q e = q := by
  unfold TailPhase.localStep
  cases hq : q.advanceEdge with
  | none => rfl
  | some b => exact if_neg (he b)

private theorem tailStep_phaseCorrected {n x : Nat} (edgeAt : Fin x → Fin n) (s s' : TailState x)
    (e : Fin n) (h : spliceTailStep edgeAt s e = .active s') :
    s'.phase = TailPhase.localStep edgeAt s.phase e := by
  unfold spliceTailStep at h
  split at h
  · injection h with h1
    exact (congrArg TailState.phase h1).symm
  · cases h

private theorem tailStep_successCorrected {n x : Nat} (edgeAt : Fin x → Fin n) (s : TailState x)
    (e : Fin n) (h : spliceTailStep edgeAt s e = .success) :
    TailPhase.localStep edgeAt s.phase e = .landed := by
  unfold spliceTailStep at h
  split at h
  · cases h
  · next hz => exact TailPhase.debt_eq_zero _ (by omega)

/-- **The `Corrected` corridor process is the imported tail machine.** -/
theorem spliceCorridorCorrected_tracks {n : Nat} (F : SFrameCorrected) (E : SEmbeddingCorrected F n)
    (s s' : TailState F.x) (hs : IsBack s.phase) (a : Fin F.x)
    (hstep : spliceTailStep E.edgeAt s (E.edgeAt a) = .active s') :
    spliceGapStepCorrected F (spliceConfigOfCorrected F s.phase) a = spliceConfigOfCorrected F s'.phase := by
  have hph := tailStep_phaseCorrected E.edgeAt s s' (E.edgeAt a) hstep
  rw [hph, localStep_embedCorrected F E s.phase a]
  have hact := s.active
  cases hq : s.phase with
  | convert hx => rw [hq] at hs; exact hs.elim
  | back j hj => exact spliceGapStepCorrected_back F j hj a
  | landed =>
      rw [hq] at hact
      exact absurd hact (by simp [TailPhase.debt])

/-- **The landing transition, for every corridor length `x ≥ 1`.**  The last
corridor firing produces exactly the landed configuration, in which `A` is
retired.  For `x = 1` that firing is the fused row; the `Original` table had no such
firing at all (`ShortGapSpliceCorridor.corridor_length_one_stalls`). -/
theorem spliceCorridorCorrected_lands {n : Nat} (F : SFrameCorrected) (E : SEmbeddingCorrected F n)
    (s : TailState F.x) (hs : IsBack s.phase) (a : Fin F.x)
    (hstep : spliceTailStep E.edgeAt s (E.edgeAt a) = .success) :
    spliceGapStepCorrected F (spliceConfigOfCorrected F s.phase) a = corridorCfgCorrected F .retired .drained 0 := by
  have hph := tailStep_successCorrected E.edgeAt s (E.edgeAt a) hstep
  rw [localStep_embedCorrected F E s.phase a] at hph
  have hact := s.active
  cases hq : s.phase with
  | convert hx => rw [hq] at hs; exact hs.elim
  | back j hj =>
      rw [hq] at hph
      rw [spliceGapStepCorrected_back F j hj a, hph]
      exact configCorrected_landed F
  | landed =>
      rw [hq] at hact
      exact absurd hact (by simp [TailPhase.debt])

/-- The corridor starts at the conversion, i.e. at the retimed phase `back x`. -/
def spliceCorridorCorrectedStart (F : SFrameCorrected) : TailState F.x :=
  ⟨.back F.x ⟨F.hx, Nat.le_refl _⟩, by
    have := F.hx
    show 0 < F.x
    omega⟩

theorem spliceCorridorCorrectedStart_config (F : SFrameCorrected) :
    spliceConfigOfCorrected F (spliceCorridorCorrectedStart F).phase = corridorCfgCorrected F .adopted .bridged 0 :=
  configCorrected_back_top F F.x _ rfl

theorem spliceCorridorCorrectedStart_isBack (F : SFrameCorrected) :
    IsBack (spliceCorridorCorrectedStart F).phase := trivial

/-- **The length-one corridor lands in one firing.**  This is the configuration
on which `Original` stalled for ever. -/
theorem corridorCorrected_length_one_lands (F : SFrameCorrected) (hx1 : F.x = 1) (a : Fin F.x) :
    spliceGapStepCorrected F (spliceConfigOfCorrected F (spliceCorridorCorrectedStart F).phase) a
        = corridorCfgCorrected F .retired .drained 0 ∧
      (spliceCorridorCorrectedStart F).phase.debt = 1 := by
  refine ⟨?_, hx1⟩
  rw [spliceCorridorCorrectedStart_config F]
  exact step_fusedCorrected F hx1 a

/-! ### The transported cost of the corridor -/

theorem spliceCorridorCorrected_start_potential {n : Nat} (F : SFrameCorrected) :
    spliceTailPotential n (.active (spliceCorridorCorrectedStart F)) = n * F.x := rfl

theorem spliceCorridorCorrected_truncatedCost_le {n : Nat} (F : SFrameCorrected) (E : SEmbeddingCorrected F n)
    (T : Nat) :
    truncatedActiveCostNumerator (spliceTailStep E.edgeAt)
        (.active (spliceCorridorCorrectedStart F)) T ≤ n ^ T * (n * (F.x + 1)) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (spliceTailStep E.edgeAt) 1 (spliceTailPotential n) (splice_bellman E.edgeAt)
    (.active (spliceCorridorCorrectedStart F)) T
  have hstart : spliceTailPotential n (.active (spliceCorridorCorrectedStart F)) = n * F.x := rfl
  rw [Nat.one_mul, hstart] at h
  have hmono : n * F.x ≤ n * (F.x + 1) := Nat.mul_le_mul_left n (by omega)
  exact Nat.le_trans h (Nat.mul_le_mul_left (n ^ T) hmono)

theorem spliceCorridorCorrected_no_failure {n : Nat} (F : SFrameCorrected) (E : SEmbeddingCorrected F n)
    (s : TailState F.x) (e : Fin n) : spliceTailStep E.edgeAt s e ≠ .failure :=
  spliceTailStep_ne_failure E.edgeAt s e

/-- **The firing count.**  The corridor's tail-phase rank starts at `x`, hence
at most `spliceDebt x = x+1`; every designated firing lowers it by exactly one
and no other firing raises it; the corridor lands after exactly `x` designated
firings and not before.  So `spliceDebt x` is a conservative charge for every
`x ≥ 1`, `x = 1` included. -/
theorem corridorCorrected_exact_firings (F : SFrameCorrected) :
    (spliceCorridorCorrectedStart F).phase.debt = F.x ∧
      (spliceCorridorCorrectedStart F).phase.debt ≤ spliceDebt F.x ∧
      spliceDebt F.x = F.x + 1 ∧
      TailPhase.iter F.x (spliceCorridorCorrectedStart F).phase = .landed ∧
      (∀ k, k < F.x → TailPhase.iter k (spliceCorridorCorrectedStart F).phase ≠ .landed) ∧
      (∀ (s : TailPhase F.x) (a : Fin F.x), s.advanceEdge = some a → 0 < s.debt →
        (TailPhase.localStep (fun b : Fin F.x => b) s a).debt + 1 = s.debt) ∧
      (∀ (s : TailPhase F.x) (a : Fin F.x),
        (TailPhase.localStep (fun b : Fin F.x => b) s a).debt ≤ s.debt) := by
  have hx1 := F.hx
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · show F.x ≤ F.x + 1
    omega
  · apply TailPhase.debt_eq_zero
    rw [TailPhase.debt_iter]
    show F.x - F.x = 0
    omega
  · intro k hk hbad
    have hd : (TailPhase.iter k (spliceCorridorCorrectedStart F).phase).debt
        = (spliceCorridorCorrectedStart F).phase.debt - k := TailPhase.debt_iter k _
    rw [hbad] at hd
    have hzero : (TailPhase.landed : TailPhase F.x).debt = 0 := rfl
    have hstart : (spliceCorridorCorrectedStart F).phase.debt = F.x := rfl
    omega
  · intro s a ha hs
    exact TailPhase.debt_localStep_advance (fun b : Fin F.x => b) s a ha hs
  · intro s a
    exact TailPhase.debt_localStep_le (fun b : Fin F.x => b) s a

/-! ### The `(B,C)` side is framed -/

def corridorRawCorrected (F : SFrameCorrected) (k : Nat) : Node :=
  if k = 0 then aRaw F.pad else if k = F.x then bridgeRaw F.pad else emptyRaw

theorem cfgCorrected_raw (F : SFrameCorrected) (asp bsp : SpliceCtl) (tok : Nat) (k : Fin (F.x + 1)) :
    (corridorCfgCorrected F asp bsp tok k).core.raw = corridorRawCorrected F k.val := by
  unfold corridorCfgCorrected corridorNodeCorrected corridorRawCorrected
  by_cases h0 : k.val = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]
    by_cases hx : k.val = F.x
    · rw [if_pos hx, if_pos hx]; rfl
    · rw [if_neg hx, if_neg hx]
      by_cases ht : k.val = tok
      · rw [if_pos ht]; rfl
      · rw [if_neg ht]; rfl

theorem configCorrected_raw (F : SFrameCorrected) (q : TailPhase F.x) (k : Fin (F.x + 1)) :
    (spliceConfigOfCorrected F q k).core.raw = corridorRawCorrected F k.val := by
  cases q with
  | convert hx => exact cfgCorrected_raw F _ _ _ k
  | back j hj =>
      by_cases h : j = F.x
      · rw [configCorrected_back_top F j hj h]; exact cfgCorrected_raw F _ _ _ k
      · rw [configCorrected_back_mid F j hj h]; exact cfgCorrected_raw F _ _ _ k
  | landed => exact cfgCorrected_raw F _ _ _ k

/-- **The `(B,C)` side is framed by the `Corrected` corridor**, exactly as in `Original`:
a corridor firing writes only the two offsets `a` and `a+1 ≤ x`, and it writes
no raw ring field at all. -/
theorem spliceCorridorCorrected_frames_BC (F : SFrameCorrected) (p : TailPhase F.x) (hp : 0 < p.debt)
    (a : Fin F.x) :
    (∀ k : Fin (F.x + 1), k.val ≠ a.val → k.val ≠ a.val + 1 →
        spliceGapStepCorrected F (spliceConfigOfCorrected F p) a k = spliceConfigOfCorrected F p k) ∧
      a.val + 1 ≤ F.x ∧
      (∀ k : Fin (F.x + 1),
        (spliceGapStepCorrected F (spliceConfigOfCorrected F p) a k).core.raw
          = (spliceConfigOfCorrected F p k).core.raw) ∧
      (spliceGapStepCorrected F (spliceConfigOfCorrected F p) a ⟨F.x, Nat.lt_succ_self _⟩).core.raw
        = bridgeRaw F.pad ∧
      (spliceGapStepCorrected F (spliceConfigOfCorrected F p) a ⟨0, Nat.succ_pos _⟩).core.raw.ccwPort
        = some F.aCcw := by
  have hx1 := F.hx
  have hraw : ∀ k : Fin (F.x + 1),
      (spliceGapStepCorrected F (spliceConfigOfCorrected F p) a k).core.raw = corridorRawCorrected F k.val := by
    intro k
    rw [spliceGapStepCorrected_phase F p hp a]
    exact configCorrected_raw F _ k
  refine ⟨fun k h1 h2 => spliceGapStepCorrected_frame F _ a k h1 h2, a.isLt, ?_, ?_, ?_⟩
  · intro k
    rw [hraw k, configCorrected_raw F p k]
  · rw [hraw ⟨F.x, Nat.lt_succ_self _⟩]
    show corridorRawCorrected F F.x = bridgeRaw F.pad
    unfold corridorRawCorrected
    rw [if_neg (by omega), if_pos rfl]
  · rw [hraw ⟨0, Nat.succ_pos _⟩]
    show (corridorRawCorrected F 0).ccwPort = some F.aCcw
    unfold corridorRawCorrected
    rw [if_pos rfl]
    rfl

/-! ## Guard soundness of the table, and the behaviour at `landed` -/

private theorem step_ruleGuardCorrected {a b x y : SNode} {k : SRuleCorrected} (h : SRowStepCorrected a b k x y) :
    (k = .freshFlush -> FreshFlush a b) ∧
    (k = .freshLaunch -> FreshLaunch a b) ∧
    (k = .freshForward -> FreshForward a b) ∧
    (k = .retireFused -> RetireFused a b) ∧
    (k = .retireLaunch -> RetireLaunch a b) ∧
    (k = .retireBackward -> RetireBackward a b) ∧
    (k = .retireDeposit -> RetireDeposit a b) ∧
    (k = .adoptDeposit -> AdoptDeposit a b) ∧
    (k = .directAdopt -> DirectAdopt a) ∧
    (k = .handoffArm -> HandoffArm a) := by
  cases h with
  | core => refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshFlush hg =>
      refine ⟨fun _ => hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshLaunch hg =>
      refine ⟨?_, fun _ => hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | freshForward hg =>
      refine ⟨?_, ?_, fun _ => hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireFused hg =>
      refine ⟨?_, ?_, ?_, fun _ => hg, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireLaunch hg =>
      refine ⟨?_, ?_, ?_, ?_, fun _ => hg, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireBackward hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => hg, ?_, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | retireDeposit hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => hg, ?_, ?_, ?_⟩ <;> (intro hk; cases hk)
  | adoptDeposit hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => hg, ?_, ?_⟩ <;> (intro hk; cases hk)
  | directAdopt hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => hg, ?_⟩ <;> (intro hk; cases hk)
  | handoffArm hg =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => hg⟩ <;> (intro hk; cases hk)

/-- **The `Corrected` dispatcher is guard-sound**: the rule it reports is a rule whose
own guard holds on the pre-state. -/
theorem spliceRuleCorrected_sound (a b : SNode) :
    (spliceRuleCorrected a b = .freshFlush -> FreshFlush a b) ∧
    (spliceRuleCorrected a b = .freshLaunch -> FreshLaunch a b) ∧
    (spliceRuleCorrected a b = .freshForward -> FreshForward a b) ∧
    (spliceRuleCorrected a b = .retireFused -> RetireFused a b) ∧
    (spliceRuleCorrected a b = .retireLaunch -> RetireLaunch a b) ∧
    (spliceRuleCorrected a b = .retireBackward -> RetireBackward a b) ∧
    (spliceRuleCorrected a b = .retireDeposit -> RetireDeposit a b) ∧
    (spliceRuleCorrected a b = .adoptDeposit -> AdoptDeposit a b) ∧
    (spliceRuleCorrected a b = .directAdopt -> DirectAdopt a) ∧
    (spliceRuleCorrected a b = .handoffArm -> HandoffArm a) :=
  step_ruleGuardCorrected (spliceRowCorrected_spec a b)

/-- The six rows of the splice tail proper (the fused retirement, the three
witness rows and the two adopt rows).  `handoffArm` is deliberately *not*
among them: it belongs to the next episode. -/
def IsTailRuleCorrected : SRuleCorrected -> Prop
  | .retireFused => True
  | .retireLaunch => True
  | .retireBackward => True
  | .retireDeposit => True
  | .adoptDeposit => True
  | .directAdopt => True
  | _ => False

def NoTailGuardCorrected (a b : SNode) : Prop :=
  ¬ RetireFused a b ∧ ¬ RetireLaunch a b ∧ ¬ RetireBackward a b ∧
    ¬ RetireDeposit a b ∧ ¬ AdoptDeposit a b ∧ ¬ DirectAdopt a

theorem no_tail_rule_ofCorrected (a b : SNode) (h : NoTailGuardCorrected a b) :
    ¬ IsTailRuleCorrected (spliceRuleCorrected a b) := by
  have hs := spliceRuleCorrected_sound a b
  intro hbad
  cases hk : spliceRuleCorrected a b with
  | core k => rw [hk] at hbad; exact hbad
  | freshFlush => rw [hk] at hbad; exact hbad
  | freshLaunch => rw [hk] at hbad; exact hbad
  | freshForward => rw [hk] at hbad; exact hbad
  | retireFused => exact h.1 (hs.2.2.2.1 hk)
  | retireLaunch => exact h.2.1 (hs.2.2.2.2.1 hk)
  | retireBackward => exact h.2.2.1 (hs.2.2.2.2.2.1 hk)
  | retireDeposit => exact h.2.2.2.1 (hs.2.2.2.2.2.2.1 hk)
  | adoptDeposit => exact h.2.2.2.2.1 (hs.2.2.2.2.2.2.2.1 hk)
  | directAdopt => exact h.2.2.2.2.2 (hs.2.2.2.2.2.2.2.2.1 hk)
  | handoffArm => rw [hk] at hbad; exact hbad

theorem noTail_retired_cell (F : SFrameCorrected) : NoTailGuardCorrected (aN F .retired) (cellN .none) :=
  ⟨(by intro h; cases h.1),
   (by intro h; cases h.1.1),
   (by intro h; cases h.1.1),
   (by intro h; cases h.1),
   (by intro h; exact h.2.1 rfl),
   (by intro h; exact h.2.1 rfl)⟩

theorem noTail_retired_bridge (F : SFrameCorrected) :
    NoTailGuardCorrected (aN F .retired) (bN F .drained) :=
  ⟨(by intro h; cases h.1),
   (by intro h; cases h.1.1),
   (by intro h; cases h.1.1),
   (by intro h; cases h.1),
   (by intro h; cases h.2.2),
   (by intro h; exact h.2.1 rfl)⟩

theorem noTail_cell_cell : NoTailGuardCorrected (cellN .none) (cellN .none) :=
  ⟨(by intro h; cases h.2.2.1),
   (by intro h; cases h.2.2.1),
   (by intro h; cases h.2.2.2),
   (by intro h; cases h.1),
   (by intro h; exact h.2.1 rfl),
   (by intro h; exact h.2.1 rfl)⟩

theorem noTail_cell_bridge (F : SFrameCorrected) :
    NoTailGuardCorrected (cellN .none) (bN F .drained) :=
  ⟨(by intro h; cases h.2.2.1),
   (by intro h; cases h.2.2.1),
   (by intro h; cases h.2.2.1.1),
   (by intro h; cases h.1),
   (by intro h; cases h.1.1.1),
   (by intro h; exact h.2.1 rfl)⟩

/-- **`landed` is a fixed point for the splice rows.**  At the landed
configuration no row of the splice tail -- fused retirement, witness
conversion, witness transport, witness deposit, receipt deposit, adopt -- is
enabled on any corridor edge.  The tail is finished. -/
theorem landedCorrected_no_tail_row (F : SFrameCorrected) (a : Fin F.x) :
    ¬ IsTailRuleCorrected (spliceRuleCorrected (spliceConfigOfCorrected F .landed (leftEndCorrected F a))
        (spliceConfigOfCorrected F .landed (rightEndCorrected F a))) := by
  apply no_tail_rule_ofCorrected
  have hx1 := F.hx
  have haLt := a.isLt
  have hlv : (leftEndCorrected F a).val = a.val := rfl
  have hrv : (rightEndCorrected F a).val = a.val + 1 := rfl
  rw [configCorrected_landed F]
  by_cases h0 : a.val = 0
  · rw [cfgCorrected_at_zero F .retired .drained 0 _ (by rw [hlv]; omega)]
    by_cases htop : a.val + 1 = F.x
    · rw [cfgCorrected_at_top F .retired .drained 0 _ (by rw [hrv]; omega)]
      exact noTail_retired_bridge F
    · rw [cfgCorrected_at_cell F .retired .drained 0 _ (by rw [hrv]; omega) (by rw [hrv]; omega)
        (by rw [hrv]; omega)]
      exact noTail_retired_cell F
  · rw [cfgCorrected_at_cell F .retired .drained 0 _ (by rw [hlv]; omega) (by rw [hlv]; omega)
      (by rw [hlv]; omega)]
    by_cases htop : a.val + 1 = F.x
    · rw [cfgCorrected_at_top F .retired .drained 0 _ (by rw [hrv]; omega)]
      exact noTail_cell_bridge F
    · rw [cfgCorrected_at_cell F .retired .drained 0 _ (by rw [hrv]; omega) (by rw [hrv]; omega)
        (by rw [hrv]; omega)]
      exact noTail_cell_cell

/-- The handoff is kept, and it is the only firing left at `landed`: the edge
`(A, next)` rearms `A` for the *fresh* episode.  That firing belongs to the
next episode, which is why the tail process stops at the landing. -/
theorem landedCorrected_continues_with_handoff (F : SFrameCorrected) (a : Fin F.x) (ha : a.val = 0) :
    spliceRuleCorrected (spliceConfigOfCorrected F .landed (leftEndCorrected F a))
        (spliceConfigOfCorrected F .landed (rightEndCorrected F a)) = .handoffArm ∧
      spliceGapStepCorrected F (spliceConfigOfCorrected F (.landed : TailPhase F.x)) a (leftEndCorrected F a)
        = sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed ∧
      spliceGapStepCorrected F (spliceConfigOfCorrected F (.landed : TailPhase F.x)) a
        ≠ spliceConfigOfCorrected F (.landed : TailPhase F.x) := by
  have hx1 := F.hx
  have haLt := a.isLt
  have hlv : (leftEndCorrected F a).val = 0 := ha
  have hrv : (rightEndCorrected F a).val = a.val + 1 := rfl
  have hL : spliceConfigOfCorrected F (.landed : TailPhase F.x) (leftEndCorrected F a) = aN F .retired := by
    rw [configCorrected_landed F]
    exact cfgCorrected_at_zero F _ _ _ _ hlv
  have hpair : spliceRuleCorrected (spliceConfigOfCorrected F .landed (leftEndCorrected F a))
        (spliceConfigOfCorrected F .landed (rightEndCorrected F a)) = .handoffArm ∧
      spliceRowCorrected (spliceConfigOfCorrected F .landed (leftEndCorrected F a))
        (spliceConfigOfCorrected F .landed (rightEndCorrected F a))
      = (sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed,
         spliceConfigOfCorrected F .landed (rightEndCorrected F a)) := by
    rw [hL]
    by_cases htop : a.val + 1 = F.x
    · have hR : spliceConfigOfCorrected F (.landed : TailPhase F.x) (rightEndCorrected F a)
          = bN F .drained := by
        rw [configCorrected_landed F]
        exact cfgCorrected_at_top F _ _ _ _ (by rw [hrv]; omega)
      rw [hR]
      exact rowCorrected_handoffBridge F
    · have hR : spliceConfigOfCorrected F (.landed : TailPhase F.x) (rightEndCorrected F a)
          = cellN .none := by
        rw [configCorrected_landed F]
        exact cfgCorrected_at_cell F _ _ _ _ (by rw [hrv]; omega) (by rw [hrv]; omega)
          (by rw [hrv]; omega)
      rw [hR]
      exact rowCorrected_handoff F
  have hfirst : spliceGapStepCorrected F (spliceConfigOfCorrected F (.landed : TailPhase F.x)) a
      (leftEndCorrected F a) = sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed := by
    unfold spliceGapStepCorrected
    rw [if_pos (show (leftEndCorrected F a).val = a.val from rfl), hpair.2]
  refine ⟨hpair.1, hfirst, ?_⟩
  intro hbad
  have hz : (spliceGapStepCorrected F (spliceConfigOfCorrected F (.landed : TailPhase F.x)) a
      (leftEndCorrected F a)).splice
      = (spliceConfigOfCorrected F (.landed : TailPhase F.x) (leftEndCorrected F a)).splice :=
    congrArg (fun c : SpliceConfigCorrected F => (c (leftEndCorrected F a)).splice) hbad
  rw [hfirst, hL] at hz
  cases hz

/-! ## The fused row is the imported one, and it excludes the witness rows -/

theorem spliceRowCorrected_fused_eq (a b : SNode) (h : RetireFused a b) (hfl : a.flush = .none) :
    spliceRuleCorrected a b = .retireFused ∧
      spliceRowCorrected a b = retireFused a b ∧
      spliceRowCorrected a b = spliceRowF a b ∧
      ¬ RetireLaunch a b ∧ ¬ RetireDeposit a b ∧ ¬ RetireBackward a b := by
  have h1 : ¬ FreshFlush a b := by
    intro hz; have hx := hz.1; rw [hfl] at hx; cases hx
  have h2 : ¬ FreshLaunch a b := by
    intro hz; have hx := hz.2.1; rw [hfl] at hx; cases hx
  have h3 : ¬ FreshForward a b := by
    intro hz; have hx := hz.1; rw [hfl] at hx; cases hx
  have hd := dispatchCorrected_fused a b h1 h2 h3 h
  have hrow : spliceRowCorrected a b = retireFused a b := rowCorrected_of_dispatch hd
  refine ⟨ruleCorrected_of_dispatch hd, hrow, ?_, ?_, ?_, ?_⟩
  · rw [hrow, spliceRowF, dif_pos h]
  · exact (retireFused_disjoint a b h).1
  · exact (retireFused_disjoint a b h).2.1
  · exact (retireFused_disjoint a b h).2.2

/-! ## The discarded whole-corridor repair, restated for `Corrected` -/

theorem commit_merge_deficitCorrected (n x y : Nat) (hx : 0 < x) (hy : 0 < y) :
    spanPot n (x + y) + spanPot n (x + y) =
      spanPot n x + spanPot n y + 2 * n + 2 * n * (x + y - 1) :=
  commit_merge_deficit n x y hx hy

theorem commit_merge_deficit_posCorrected (n x y : Nat) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) :
    0 < 2 * n * (x + y - 1) :=
  commit_merge_deficit_pos n x y hn hx hy

theorem splice_debt_lt_merge_repairCorrected (n x y : Nat) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) :
    n * spliceDebt x < spanPot n (x + y) :=
  splice_debt_lt_merge_repair n x y hn hx hy

/-! ## The concrete commit/splice potential on the `Corrected` corridor

The accounting boundary is fixed *after* the receipt deposit, the source
acknowledgement and the adoption.  With that boundary the capture reserve
before the commit exposes the whole splice tail `n * spliceDebt x` plus the
pending target-cleanup bit `u ∈ {0,1}`, and after the landing only `n*u`
remains.  Both numbers are read off the tail-phase rank of the corridor:
the rank starts at `x` and ends at `0`, and each designated firing lowers the
potential by exactly `n`.
-/

/-- The transported potential of the corridor at tail phase `p`, plus the
pending target-cleanup bit `u`. -/
def corridorPotCorrected (n u : Nat) (F : SFrameCorrected) (p : TailPhase F.x) : Nat :=
  n * p.debt + n * u

/-- The concrete `before` potential: the corridor's start rank `x`, the
accounting-only conversion unit, and the pending cleanup. -/
def spliceBeforeCorrected (n u : Nat) (F : SFrameCorrected) : Nat :=
  corridorPotCorrected n u F (spliceCorridorCorrectedStart F).phase + n

/-- The concrete `after` potential: the landed rank `0`, and the pending
cleanup. -/
def spliceAfterCorrected (n u : Nat) (F : SFrameCorrected) : Nat :=
  corridorPotCorrected n u F (TailPhase.landed)

theorem spliceBeforeCorrected_eq (n u : Nat) (F : SFrameCorrected) :
    spliceBeforeCorrected n u F = n * (F.x + 1) + n * u := by
  show n * F.x + n * u + n = n * (F.x + 1) + n * u
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem spliceAfterCorrected_eq (n u : Nat) (F : SFrameCorrected) : spliceAfterCorrected n u F = n * u := by
  show n * 0 + n * u = n * u
  rw [Nat.mul_zero]
  omega

theorem spliceBeforeCorrected_is_capture_reserve (n u : Nat) (F : SFrameCorrected) :
    spliceBeforeCorrected n u F = n * spliceDebt F.x + n * u := by
  rw [spliceBeforeCorrected_eq]
  rfl

/-- The concrete potential falls by exactly `n` at each designated firing of
the corridor. -/
theorem corridorPotCorrected_descent (n u : Nat) (F : SFrameCorrected) (p : TailPhase F.x)
    (a : Fin F.x) (hae : p.advanceEdge = some a) (hp : 0 < p.debt) :
    corridorPotCorrected n u F (TailPhase.localStep (fun b : Fin F.x => b) p a) + n
      = corridorPotCorrected n u F p := by
  have h := TailPhase.debt_localStep_advance (fun b : Fin F.x => b) p a hae hp
  show n * (TailPhase.localStep (fun b : Fin F.x => b) p a).debt + n * u + n
      = n * p.debt + n * u
  rw [← h, Nat.mul_add, Nat.mul_one]
  omega

/-- No firing ever raises the concrete potential. -/
theorem corridorPotCorrected_monotone (n u : Nat) (F : SFrameCorrected) (p : TailPhase F.x) (a : Fin F.x) :
    corridorPotCorrected n u F (TailPhase.localStep (fun b : Fin F.x => b) p a)
      ≤ corridorPotCorrected n u F p := by
  have h := TailPhase.debt_localStep_le (fun b : Fin F.x => b) p a
  show n * (TailPhase.localStep (fun b : Fin F.x => b) p a).debt + n * u
      ≤ n * p.debt + n * u
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n h) _

/-- **The hypothesis `hcommit` of `commit_splice_potential_le_concrete`,
discharged on the `Corrected` corridor.** -/
theorem hcommitCorrected (n u : Nat) (F : SFrameCorrected) :
    spliceAfterCorrected n u F + n * ((F.x + 1) + u)
      ≤ spliceBeforeCorrected n u F + (n * u + n * (F.x + 1)) := by
  rw [spliceAfterCorrected_eq, spliceBeforeCorrected_eq, Nat.mul_add]
  omega

/-- **The commit/splice potential inequality is now a theorem about `Corrected`.**
`after ≤ before` for the concrete potentials read off the corridor's
tail-phase rank; no arithmetic hypothesis is left open. -/
theorem spliceCorridorCorrected_potential_le (n u : Nat) (F : SFrameCorrected) (hu : u ≤ 1) :
    spliceAfterCorrected n u F ≤ spliceBeforeCorrected n u F :=
  commit_splice_potential_le_concrete n F.x u (spliceBeforeCorrected n u F) (spliceAfterCorrected n u F)
    hu (hcommitCorrected n u F)

/-- The same statement in the post-deposit shape: the post-commit reserve `n*u`
plus the fused tail `n*((x+1)+u)` is covered by the pre-commit reserve
together with the two separate charges. -/
theorem cap_splice_releaseCorrected (n u : Nat) (F : SFrameCorrected) (hu : u ≤ 1) :
    n * u + n * (F.x + 1) ≤ n * ((F.x + 1) + u) :=
  cap_splice_release n F.x u hu

/-! ## Two literal corridors, to witness that none of this is vacuous -/

def demoCorrectedOne : SFrameCorrected where
  x := 1
  hx := by omega
  aCw := .waiting
  haCw := by intro h; cases h
  aCcw := .free
  aInc := .open
  aCtl := .clean
  aLease := .committed
  bCw := .heldDenial
  hbCw := Or.inl rfl
  bOut := .home
  bCtl := .clean
  bSnap := ⟨.toSend, .home⟩

def demoCorrectedTwo : SFrameCorrected where
  x := 2
  hx := by omega
  aCw := .waiting
  haCw := by intro h; cases h
  aCcw := .free
  aInc := .open
  aCtl := .clean
  aLease := .committed
  bCw := .heldDenial
  hbCw := Or.inl rfl
  bOut := .home
  bCtl := .clean
  bSnap := ⟨.toSend, .home⟩

/-- **The length-one corridor now runs.**  One firing of the single edge
converts the settled old verdict and retires `A`.  Compare
`ShortGapSpliceCorridor.corridor_length_one_stalls`. -/
theorem demoCorrectedOne_run :
    spliceGapStepCorrected demoCorrectedOne (corridorCfgCorrected demoCorrectedOne .adopted .bridged 0)
        ⟨0, Nat.succ_pos 0⟩
      = corridorCfgCorrected demoCorrectedOne .retired .drained 0 :=
  step_fusedCorrected demoCorrectedOne rfl ⟨0, Nat.succ_pos 0⟩

/-- Two literal firings run the whole tail of a length-two corridor. -/
theorem demoCorrectedTwo_run :
    spliceGapStepCorrected demoCorrectedTwo
        (spliceGapStepCorrected demoCorrectedTwo (corridorCfgCorrected demoCorrectedTwo .adopted .bridged 0)
          (convEdgeCorrected demoCorrectedTwo)) ⟨0, Nat.succ_pos 1⟩
      = corridorCfgCorrected demoCorrectedTwo .retired .drained 0 := by
  rw [step_convertCorrected demoCorrectedTwo (Nat.le_refl 2)]
  exact step_landCorrected demoCorrectedTwo (Nat.le_refl 2) ⟨0, Nat.succ_pos 1⟩ rfl

theorem demoCorrected_debt :
    (spliceCorridorCorrectedStart demoCorrectedOne).phase.debt = 1 ∧ spliceDebt demoCorrectedOne.x = 2 ∧
      (spliceCorridorCorrectedStart demoCorrectedTwo).phase.debt = 2 ∧ spliceDebt demoCorrectedTwo.x = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## The ack-ordered pipeline produces the head of the corridor

The three firings of `ackCorrected_precedes_adopt` end with `A` in exactly the state
that the corridor frame calls offset `0`: clockwise port `adoptCwCorrected snap`,
commit lifecycle `.clean` (the ack *is* discharged), splice mark `.adopted`.
-/

def frameAfterAdopt (x : Nat) (hx : 1 ≤ x) (ccw : CcwPort) (inc : InControl)
    (lease : CommitIn) (snap : SnapPhase) (bCw : CwPort)
    (hbCw : bCw = .heldDenial ∨ bCw = .heldCandidate) (bOut : OutControl)
    (bCtl : CommitCtl) (bSnap : SnapPhase) : SFrameCorrected where
  x := x
  hx := hx
  aCw := adoptCwCorrected snap
  haCw := adoptCorrected_ne_candidate snap
  aCcw := ccw
  aInc := inc
  aCtl := .clean
  aLease := lease
  bCw := bCw
  hbCw := hbCw
  bOut := bOut
  bCtl := bCtl
  bSnap := bSnap

theorem adopt_produces_corridor_head (x : Nat) (hx : 1 ≤ x) (ccw : CcwPort)
    (inc : InControl) (lease : CommitIn) (snap : SnapPhase) (bCw : CwPort)
    (hbCw : bCw = .heldDenial ∨ bCw = .heldCandidate) (bOut : OutControl)
    (bCtl : CommitCtl) (bSnap : SnapPhase) :
    (spliceRowCorrected (sOwnerP ccw inc .clean lease false (some snap))
        (sCell .none .none .none none)).1
      = aN (frameAfterAdopt x hx ccw inc lease snap bCw hbCw bOut bCtl bSnap) .adopted := by
  rw [(ackCorrected_adopt_fires ccw inc lease false snap).2.2]
  rfl

/-! ## A row-level obstruction discovered while proving the landed case

The obstruction is *not* introduced by `Corrected`; it is present in `Original` as well and
was invisible there because the `Original` corridor simulation stops at `landed`.

Former `B` keeps a **root** raw node, `bridgeRaw`.  But both rows that carry a
fresh `A -> C` declaration, `FreshLaunch` and `FreshForward`, demand
`SEmpty b`, i.e. `b.core.raw = emptyRaw`.  Hence the fresh declaration lane
cannot traverse former `B` at all: on a length-one corridor `A`'s right
neighbour *is* former `B`, so after `handoffArm` rearms `A` the declaration
cannot even launch; on a longer corridor the declaration walks the cleaned
cells and then stalls at offset `x`.

The imported `targetCleanup` row does apply to former `B` -- its guard holds
below -- but it only writes the *lease* field `incoming`, never the raw node,
so it does not unblock the lane.  A row that demotes the committed root to an
interior relay is therefore still missing from the table; it is not supplied
here, because adding it changes the corridor's row set and hence every frame
proved above.
-/

theorem bridge_never_empty (F : SFrameCorrected) (sp : SpliceCtl) : ¬ SEmpty (bN F sp) := by
  intro h
  cases h.1

/-- The declaration wire in transit, with its unflushed mark. -/
def declNode : SNode :=
  ⟨⟨declRaw, false, .capturing, .unreserved, .none⟩, none, none, .inactive, .none, .unflushed⟩

/-- **The obstruction.**  Neither fresh-declaration row can fire against former
`B`, in any lifecycle state of the bridge. -/
theorem fresh_lane_blocked_by_bridge (F : SFrameCorrected) (sp : SpliceCtl) :
    ¬ FreshLaunch (sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed)
        (bN F sp) ∧
      ¬ FreshForward declNode (bN F sp) := by
  constructor
  · intro h
    exact bridge_never_empty F sp h.2.2.2.1
  · intro h
    exact bridge_never_empty F sp h.2.2.1

/-- The imported cleanup row does apply to former `B`, but it writes only the
lease field: the raw node, and hence the obstruction, survives it. -/
theorem targetCleanup_does_not_clear_bridge (F : SFrameCorrected) (sp : SpliceCtl) :
    TargetCleanup (bN F sp).core ∧
      (setIn (bN F sp).core .clean).raw = bridgeRaw F.pad ∧
      (bN F sp).core.raw = bridgeRaw F.pad :=
  ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩


/-! ## Axiom audit -/

#print axioms adoptCwOfCorrected_ne_denial
#print axioms adoptCwOfCorrected_ne_candidate
#print axioms adoptCwOfCorrected_waiting_iff
#print axioms adoptOriginal_ne_adoptCorrected
#print axioms spliceRowCorrected_spec
#print axioms dispatchCorrected_flush
#print axioms dispatchCorrected_fused
#print axioms dispatchCorrected_retireLaunch
#print axioms dispatchCorrected_retireBackward
#print axioms dispatchCorrected_retireDeposit
#print axioms dispatchCorrected_adoptDeposit
#print axioms dispatchCorrected_directAdopt
#print axioms dispatchCorrected_handoff
#print axioms dispatchCorrected_core
#print axioms rowCorrected_of_dispatch
#print axioms ruleCorrected_of_dispatch
#print axioms spliceRowCorrected_core_of
#print axioms spliceRuleCorrected_core_of
#print axioms spliceRowCorrected_stutter_of
#print axioms splice_core_dispatchCorrected
#print axioms spliceRuleCorrected_core
#print axioms spliceRowCorrected_core
#print axioms spliceRowCorrected_agrees_commitRow
#print axioms spliceRowCorrected_agrees_captureRow
#print axioms commit_installs_bridgeCorrected
#print axioms stale_receipt_inertCorrected
#print axioms splice_frames_next_gapCorrected
#print axioms splice_never_retags_denialCorrected
#print axioms unflushed_only_from_armCorrected
#print axioms retired_only_from_witness_or_fusedCorrected
#print axioms retire_witness_conservationCorrected
#print axioms adopt_rows_write_no_verdictCorrected
#print axioms adoptCorrected_carrier_has_no_verdict
#print axioms sOwner_eq_sOwnerP
#print axioms original_adopt_kills_sourceAck
#print axioms adopt_disabled_while_ack_pendingCorrected
#print axioms directAdopt_needs_ack_dischargedCorrected
#print axioms ackCorrected_deposit_fires
#print axioms ackCorrected_sourceAck_fires
#print axioms ackCorrected_adopt_fires
#print axioms ackCorrected_precedes_adopt
#print axioms rowCorrected_convert
#print axioms rowCorrected_carry
#print axioms rowCorrected_land
#print axioms rowCorrected_fused
#print axioms rowCorrected_cells
#print axioms rowCorrected_idleA
#print axioms rowCorrected_idleBridge
#print axioms rowCorrected_handoff
#print axioms rowCorrected_handoffBridge
#print axioms spliceGapStepCorrected_of
#print axioms spliceGapStepCorrected_id
#print axioms spliceGapStepCorrected_frame
#print axioms cfgCorrected_at_zero
#print axioms cfgCorrected_at_top
#print axioms cfgCorrected_at_tok
#print axioms cfgCorrected_at_cell
#print axioms cfgCorrected_at_any
#print axioms cfgCorrected_frame
#print axioms step_convertCorrected
#print axioms step_carryCorrected
#print axioms step_landCorrected
#print axioms step_fusedCorrected
#print axioms step_stutter_convertCorrected
#print axioms step_stutter_witnessCorrected
#print axioms configCorrected_convert
#print axioms configCorrected_back_top
#print axioms configCorrected_back_mid
#print axioms configCorrected_landed
#print axioms retimeCorrected_convert
#print axioms configCorrected_retime
#print axioms spliceGapStepCorrected_back
#print axioms spliceGapStepCorrected_phase
#print axioms localStep_embedCorrected
#print axioms localStep_off_corridorCorrected
#print axioms spliceCorridorCorrected_tracks
#print axioms spliceCorridorCorrected_lands
#print axioms spliceCorridorCorrectedStart_config
#print axioms spliceCorridorCorrectedStart_isBack
#print axioms corridorCorrected_length_one_lands
#print axioms spliceCorridorCorrected_start_potential
#print axioms spliceCorridorCorrected_truncatedCost_le
#print axioms spliceCorridorCorrected_no_failure
#print axioms corridorCorrected_exact_firings
#print axioms cfgCorrected_raw
#print axioms configCorrected_raw
#print axioms spliceCorridorCorrected_frames_BC
#print axioms spliceRuleCorrected_sound
#print axioms no_tail_rule_ofCorrected
#print axioms noTail_retired_cell
#print axioms noTail_retired_bridge
#print axioms noTail_cell_cell
#print axioms noTail_cell_bridge
#print axioms landedCorrected_no_tail_row
#print axioms landedCorrected_continues_with_handoff
#print axioms spliceRowCorrected_fused_eq
#print axioms commit_merge_deficitCorrected
#print axioms commit_merge_deficit_posCorrected
#print axioms splice_debt_lt_merge_repairCorrected
#print axioms spliceBeforeCorrected_eq
#print axioms spliceAfterCorrected_eq
#print axioms spliceBeforeCorrected_is_capture_reserve
#print axioms corridorPotCorrected_descent
#print axioms corridorPotCorrected_monotone
#print axioms hcommitCorrected
#print axioms spliceCorridorCorrected_potential_le
#print axioms cap_splice_releaseCorrected
#print axioms demoCorrectedOne_run
#print axioms demoCorrectedTwo_run
#print axioms demoCorrected_debt
#print axioms adopt_produces_corridor_head
#print axioms bridge_never_empty
#print axioms fresh_lane_blocked_by_bridge
#print axioms targetCleanup_does_not_clear_bridge

end ShortGapSpliceCommitCorrected

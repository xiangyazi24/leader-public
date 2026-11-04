import Leader.L3.WordCertificate
import Leader.L3.ClosureFull

/-!
Generated W-worker phase audit.

The existing CleanWorkerPhaseInv has only five constructors:
prefix, back, sum, ready, done.  The physical wordT has additional
legitimate worker-cancellation and hard-restart branches, which
change the monitor to awaitRequest or validate.  Thus the five-case
invariant is not a universally closed post-I0 predicate without
an epoch restriction or additional idle/restart cases.

The counterexample below starts with the repo's exact
cwToyIsIZero physical I0 row, not a fabricated byte pattern
of a PREFIX.  Its initial cwToyControl is NOT certified as
reachable from BlockA.initializesWord; no J_W-generated
counterexample is claimed.  The two subsequent actual phiW
selected services suffice to demonstrate the dispatch hazard.

The useful general frame theorem proves a genuine subcase of
prefix preservation, using the actual wordT/wordWorkerNext owner.
-/

namespace L3.WordPhase

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- A PREFIX certificate has monitor phase WORKER. -/
theorem wordPhasePrefixWorker {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hp : cwPhasePrefix ring h p) :
    h.phase = .worker := by
  obtain ⟨site, index, z, a, hworker, _⟩ := hp
  exact hworker

/-- Every constructor of the existing five-case invariant is
either in the worker phase or the done phase.  In particular
it has no representation for a cancelled or validating epoch. -/
theorem wordPhaseOnlyWorkerOrDone {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hi : CleanWorkerPhaseInv ring h p) :
    h.phase = .worker ∨ h.phase = .done := by
  cases hi with
  | «prefix» hp =>
      exact Or.inl (wordPhasePrefixWorker ring h p hp)
  | back hb =>
      obtain ⟨site, target, index, hworker, _⟩ := hb
      exact Or.inl hworker
  | sum hs =>
      obtain ⟨site, target, index, z, parity, trailing,
        hworker, _⟩ := hs
      exact Or.inl hworker
  | ready hr =>
      obtain ⟨target, hworker, _⟩ := hr
      exact Or.inl hworker
  | done hd full =>
      exact Or.inr hd

/-- Neither a new validation epoch nor a cancelled idle worker
can satisfy the unextended five-case phase invariant. -/
theorem wordPhaseNoValidate {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hv : h.phase = .validate) :
    ¬ CleanWorkerPhaseInv ring h p := by
  intro hi
  rcases wordPhaseOnlyWorkerOrDone ring h p hi with hw | hd
  · rw [hv] at hw
    cases hw
  · rw [hv] at hd
    cases hd

theorem wordPhaseNoAwaitRequest {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (ha : h.phase = .awaitRequest) :
    ¬ CleanWorkerPhaseInv ring h p := by
  intro hi
  rcases wordPhaseOnlyWorkerOrDone ring h p hi with hw | hd
  · rw [ha] at hw
    cases hw
  · rw [ha] at hd
    cases hd

/-- Complete prefix frame subcase for the literal wordT, not
an arbitrary invented control update.  NoHardStart is checked
on the OLD selected pair.  The exact physical visible and SI
field agreements are explicit, as in the installed
cwPhasePrefixFrameOfUnchangedFields theorem. -/
theorem wordPhasePrefixFrameService {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hp : cwPhasePrefix ring h p)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hcase : BlockA.workerCase
      (p e) (p (ring.rightNeighbor e)) = .frame)
    (hvisible : ∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i)
    (hsi : ∀ i : Fin n,
      ((phiW ring p e) i).si = (p i).si) :
    CleanWorkerPhaseInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hworker := wordPhasePrefixWorker ring h p hp
  have hdispatch :
      BlockA.wordT ring h p e (phiW ring p e) =
        BlockA.wordWorkerNext ring h p e
          (BlockA.wordRequestNext ring h p e) := by
    simp [BlockA.wordT, hworker, hno]
  rw [hdispatch]
  exact CleanWorkerPhaseInv.prefix
    (cwPhasePrefixFrameOfUnchangedFields ring h p e
      (BlockA.wordRequestNext ring h p e)
      hp hcase hvisible hsi)

/-! The closed n = 5 toy (I0, incoming S0, hard S1) was removed:
its decide checks failed, so it is not evidence. -/

end L3.WordPhase

/-!
Restart-closed W worker-epoch accounting.

The E.G14 monitor has awaitRequest and validate phases in addition
to worker and done. wordClear and wordHardLaunch erase colored
worker authority and publication receipts; they need NOT erase
arbitrary uncolored physical SI records. The scrubbed disjuncts
below therefore refer to exact WordControl fields, not a fictional
global physical-SI reset.

The P1/P3 row certificates support genuine local numerical and
stale-tag cases. Full successful P1/P3 phase transport still
needs clockwise site geometry and publication-ledger induction.
-/

namespace L3.WordPhase

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- No colored worker can publish until a new genuine I0.
Both read ledgers and all publication receipts are empty. -/
def WordEpochScrub {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) : Prop :=
  (∀ i : Fin n,
    h.workerKind i = .empty ∧
    h.workerCursor i = .empty ∧
    h.publications i = .absent ∧
    h.visibleReceipts i = false ∧
    h.prefixMarkers i = false) ∧
  h.prefixReads.count.val = 0 ∧
  h.sumReads.count.val = 0

/-- Exactly the four possible E.G14 phases: validated and idle
monitor scrubs, or the existing five worker/done certificates. -/
def WordEpochInv {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  (h.phase = .validate ∧ WordEpochScrub h) ∨
  (h.phase = .awaitRequest ∧ WordEpochScrub h) ∨
  CleanWorkerPhaseInv ring h p

theorem wordEpochScrubClear {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (request : Bool) :
    WordEpochScrub (BlockA.wordClear h request) := by
  refine ⟨?_, rfl, rfl⟩
  intro i
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wordEpochScrubHardLaunch {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (e j : Fin n) :
    WordEpochScrub (BlockA.wordHardLaunch h e j) := by
  refine ⟨?_, rfl, rfl⟩
  intro i
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem wordEpochScrubRequested {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (request : Bool)
    (hscrub : WordEpochScrub h) :
    WordEpochScrub { h with requested := request } := by
  exact hscrub

theorem wordEpochScrubSerializer {n : Nat} {c : Compiled}
    (h : BlockA.WordControl n c) (request : Bool)
    (serializer : Fin n → BlockA.SerializerColor n)
    (hscrub : WordEpochScrub h) :
    WordEpochScrub
      { h with requested := request, serializer := serializer } := by
  exact hscrub

/-- Actual J_W gives an empty initial monitor in awaitRequest.
No false assumption about the initial physical SI alphabet occurs. -/
theorem wordEpochInitializes {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (origin : Fin n → ProjW c)
    (gamma : BlockA.Decoration
      (Fin n → ProjW c) (BlockA.WordControl n c))
    (hinit : BlockA.initializesWord ring origin gamma) :
    ∃ h : BlockA.WordControl n c,
      gamma = .live origin h ∧ WordEpochInv ring h origin := by
  obtain ⟨root, h, hgamma, _hroot, _hfixed, _hwidth,
    _hspan, hphase, _hrequested, hslots, hprefix, hsum⟩ := hinit
  refine ⟨h, hgamma, Or.inr (Or.inl ⟨hphase, ?_⟩)⟩
  refine ⟨?_, hprefix, hsum⟩
  intro i
  obtain ⟨_hser, _hparent, htag, hcursor,
    hpublication, hvisible, hmarker⟩ := hslots i
  exact ⟨htag, hcursor, hpublication, hvisible, hmarker⟩

/-- Any selected transition which actually takes wordClear
lands in the awaitRequest scrub disjunct. -/
theorem wordEpochClearedOwner {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hclear :
      BlockA.wordT ring h p e (phiW ring p e) =
        BlockA.wordClear h
          (BlockA.wordRequestNext ring h p e)) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  rw [hclear]
  exact Or.inr (Or.inl
    ⟨rfl, wordEpochScrubClear h (BlockA.wordRequestNext ring h p e)⟩)

/-- Hard S1 wins the outer E.G14 priority on every non-DONE
monitor and establishes a validating, fully scrubbed epoch. -/
theorem wordEpochHardStartService {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hnotdone : h.phase ≠ .done)
    (hstart : BlockA.wordIsHardStart ring h p e) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hstep :
      BlockA.wordT ring h p e (phiW ring p e) =
        BlockA.wordHardLaunch h e (ring.rightNeighbor e) := by
    simp [BlockA.wordT, hnotdone, hstart]
  rw [hstep]
  exact Or.inl
    ⟨rfl, wordEpochScrubHardLaunch h e (ring.rightNeighbor e)⟩

/-- Every actual awaitRequest service either hard-starts a
validation epoch or clears the monitor back into awaitRequest. -/
theorem wordEpochAwaitService {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (haw : h.phase = .awaitRequest) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hnotdone : h.phase ≠ .done := by
    intro hd
    rw [haw] at hd
    cases hd
  by_cases hstart : BlockA.wordIsHardStart ring h p e
  · exact wordEpochHardStartService ring h p e hnotdone hstart
  · have hclear :
        BlockA.wordT ring h p e (phiW ring p e) =
          BlockA.wordClear h
            (BlockA.wordRequestNext ring h p e) := by
      simp [BlockA.wordT, haw, hstart]
    exact wordEpochClearedOwner ring h p e hclear

/-- The actual worker branch has no independent scheduler
or shadow state: its selected owner is wordWorkerNext. -/
theorem wordEpochWorkerDispatch {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hworker : h.phase = .worker)
    (hno : ¬ BlockA.wordIsHardStart ring h p e) :
    BlockA.wordT ring h p e (phiW ring p e) =
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) := by
  simp [BlockA.wordT, hworker, hno]

/-- Common cancellation handoff for all six or more worker
cases which explicitly choose the installed wordClear. -/
theorem wordEpochWorkerCancellation {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hworker : h.phase = .worker)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hcancel :
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) =
      BlockA.wordClear h
        (BlockA.wordRequestNext ring h p e)) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hdispatch := wordEpochWorkerDispatch ring h p e hworker hno
  exact wordEpochClearedOwner ring h p e
    (hdispatch.trans hcancel)

/-- The physical P0 prefix-exit service discards the current
monitor; no fake PREFIX successor is introduced. -/
theorem wordEpochPrefixExitService {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hworker : h.phase = .worker)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixExit) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hcancel :
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) =
      BlockA.wordClear h
        (BlockA.wordRequestNext ring h p e) := by
    simp [BlockA.wordWorkerNext, hcase]
  exact wordEpochWorkerCancellation ring h p e hworker hno hcancel

/-- P2 is a cancellation, not the P3 publication. -/
theorem wordEpochPrefixTerminalService {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hp : cwPhasePrefix ring h p)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P2") :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hcase :=
    cwPhasePrefixTerminalRow (p e) (p (ring.rightNeighbor e)) hrow
  have hcancel := cwPhasePrefixTerminalCancels ring h p e
    (BlockA.wordRequestNext ring h p e) hcase
  exact wordEpochWorkerCancellation ring h p e
    (wordPhasePrefixWorker ring h p hp) hno hcancel

/-- An I0 worker row selected OUTSIDE the genuine validating
handoff cancels the old running monitor. -/
theorem wordEpochWorkerInitCancellation {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hworker : h.phase = .worker)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .init) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hcancel :
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) =
      BlockA.wordClear h
        (BlockA.wordRequestNext ring h p e) := by
    simp [BlockA.wordWorkerNext, hcase]
  exact wordEpochWorkerCancellation ring h p e hworker hno hcancel

/-- Exact E.G15 serializer-only updates do not touch any
worker-color, read-ledger or publication authority. -/
theorem wordEpochValidateSerializerService {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hvalidate : h.phase = .validate)
    (hscrub : WordEpochScrub h)
    (request : Bool)
    (serializer : Fin n → BlockA.SerializerColor n)
    (hstep :
      BlockA.wordT ring h p e (phiW ring p e) =
        { h with requested := request, serializer := serializer }) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  rw [hstep]
  exact Or.inl
    ⟨hvalidate, wordEpochScrubSerializer h request serializer hscrub⟩

/-- A selected E.G15 serializer FRAME either preserves monitor
scrub or cancels the validated episode. -/
theorem wordEpochValidateFrameService {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hvalidate : h.phase = .validate)
    (hscrub : WordEpochScrub h)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hcase : BlockA.serializerCase (p e)
      (p (ring.rightNeighbor e)) = .frame) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  by_cases hcancel :
      ((serW (p e) (p (ring.rightNeighbor e))).x ≠ (p e).ser ∧
        (h.serializer e).tag ≠ .empty) ∨
      ((serW (p e) (p (ring.rightNeighbor e))).y ≠
          (p (ring.rightNeighbor e)).ser ∧
        (h.serializer (ring.rightNeighbor e)).tag ≠ .empty)
  · have hcontrol :
        BlockA.wordValidateNext ring h p e
          (BlockA.wordRequestNext ring h p e) =
        BlockA.wordClear h
          (BlockA.wordRequestNext ring h p e) := by
      simp [BlockA.wordValidateNext, hcase, hcancel]
    have hstep :
        BlockA.wordT ring h p e (phiW ring p e) =
        BlockA.wordClear h
          (BlockA.wordRequestNext ring h p e) := by
      simp [BlockA.wordT, hvalidate, hno, hcontrol]
    exact wordEpochClearedOwner ring h p e hstep
  · have hcontrol :
        BlockA.wordValidateNext ring h p e
          (BlockA.wordRequestNext ring h p e) =
        { h with requested := BlockA.wordRequestNext ring h p e } := by
      simp [BlockA.wordValidateNext, hcase, hcancel]
    have hstep :
        BlockA.wordT ring h p e (phiW ring p e) =
        { h with requested := BlockA.wordRequestNext ring h p e } := by
      simp [BlockA.wordT, hvalidate, hno, hcontrol]
    rw [hstep]
    exact Or.inl
      ⟨hvalidate,
        wordEpochScrubRequested h
          (BlockA.wordRequestNext ring h p e) hscrub⟩

/-- The genuine I0 edge already has a complete, source-level
PREFIX certificate; this is not an arbitrary byte-pattern test. -/
theorem wordEpochGenuineIZero {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (clean : CleanIZero ring h p e) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  exact Or.inr (Or.inr
    (cwPhaseIZeroEstablishment ring h p e hne clean))

/-- P1: exact selected OLD row plus the genuine prefix-read
OR/AND/count algebra, but not yet the full physical site geometry. -/
theorem wordEpochPrefixPoneLocal {c : Compiled}
    (x y : ProjW c)
    (reads : List Bool) (oldBit : Bool)
    (hrow : (workerW x y).row = "P1") :
    BlockA.workerCase x y = .prefixMove ∧
      (prefixAuditOf (reads ++ [oldBit])).count =
        (prefixAuditOf reads).count + 1 ∧
      (prefixAuditOf (reads ++ [oldBit])).z =
        ((prefixAuditOf reads).z || oldBit) ∧
      (prefixAuditOf (reads ++ [oldBit])).a =
        ((prefixAuditOf reads).a && oldBit) := by
  exact ⟨cwPhasePrefixMoveRow x y hrow,
    cwPhasePrefixMoveFold reads oldBit⟩

/-- P3: exact selected OLD publication row and the nonzero kick.
The full PREFIX-to-BACK geometry remains an independent obligation. -/
theorem wordEpochPrefixPthreeLocal {c : Compiled}
    (x y : ProjW c)
    (z oldBit : Bool)
    (hrow : (workerW x y).row = "P3") :
    BlockA.workerCase x y = .prefixPublish ∧
      (z || prefixKick z oldBit) = true := by
  exact ⟨cwPhasePrefixPublishRow x y hrow,
    cwPhasePrefixPublishNonzero z oldBit⟩

/-- Uncolored P1 physical work is not accepted as an advance
of the CURRENT prefix; wordWorkerNext deletes its monitor. -/
theorem wordEpochPrefixPoneStale {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hworker : h.phase = .worker)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P1")
    (hstale : h.workerKind e = .empty) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hcase :=
    cwPhasePrefixMoveRow (p e) (p (ring.rightNeighbor e)) hrow
  have hcancel :
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) =
      BlockA.wordClear h
        (BlockA.wordRequestNext ring h p e) := by
    simp [BlockA.wordWorkerNext, hcase, hstale]
  exact wordEpochWorkerCancellation ring h p e
    hworker hno hcancel

/-- Uncolored P3 work cannot forge a first-window publication. -/
theorem wordEpochPrefixPthreeStale {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hworker : h.phase = .worker)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3")
    (hstale : h.workerKind e = .empty) :
    WordEpochInv ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hcase :=
    cwPhasePrefixPublishRow (p e) (p (ring.rightNeighbor e)) hrow
  have hcancel :
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) =
      BlockA.wordClear h
        (BlockA.wordRequestNext ring h p e) := by
    simp [BlockA.wordWorkerNext, hcase, hstale]
  exact wordEpochWorkerCancellation ring h p e
    hworker hno hcancel

/-!
OPEN GENERATED-RUN PHASE ROWS, NOT ASSERTED AS THEOREMS.

Validate: challenge/observeInt/observeLeaf/admit/feedback are
serializer-only branches when they pass their guards. Full
hardTerminal-to-I0 needs the genuine CleanIZero scrub evidence.
Target.cwPhaseIZeroEstablishment closes it once established.

P1 matching colored prefix: source site equals the clockwise
root offset idx, the appended OLD responder is the next follower,
beta is published as zero below t, and all remote physical
SI registers remain free. The installed MoveFold/MoveReceipt/
MoveRow lemmas only establish local arithmetic/receipts.

P3 matching colored prefix: idx=t and its site is the t-th
follower, then firstNonzero and marker AND must follow the
physical kick, and the new target must have correct BACK
geometry. Installed PublishNonzero/PublishReceipt/PublishRow
give only the numerical/receipt portions.

B0 back-to-back, B1 back-to-sum, S0 sum-to-sum,
S1 sum-to-ready, A1 ready-to-back, and A0 ready-to-done
still need phase-specific whole-state transport and, at A0,
construction of CleanWorkerInv.
Physical I1/hard scrub may orphan incomplete physical worker
pieces even while their monitor colors are cancelled; this is
why the idle disjunct does not claim physical SI = offSI.

There is no all-edge closure theorem for WordEpochInv in this
section and no unconditional AcceptedWord-to-static-values
producer. A genuine BlockA.Run induction awaits these rows.
-/

end L3.WordPhase


/-!
Chronological active-prefix location in the generated W epoch.

This section strengthens only the PREFIX
constructor with the actual rooted site equation.  The existing
cwPhasePrefix itself already certifies chronological prior sample
sources and their published beta=0 receipts.

The successful physical P1 and P3 owner branches have exact row
classifiers, but the pinned Target.lean does not yet contain their
whole-phase preservation proofs.  The geometric sublemmas, genuine
I0 strengthening, non-active stale cancellations, and unchanged
frame preservation below do not postulate those missing conclusions.
-/

namespace L3.WordPhase

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- The root is the zeroth clockwise site, including at a
genuine I0 launch. -/
theorem wordPhaseShiftZero {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    PPL.shiftRight ring root 0 = root := by
  apply Fin.ext
  simp only [PPL.shiftRight, Nat.add_zero]
  exact Nat.mod_eq_of_lt root.isLt

/-- The responder to the active prefix at offset j is the
next clockwise follower.  This is an exact ring identity. -/
theorem wordPhaseShiftSucc {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (j : Nat) :
    PPL.shiftRight ring root (j + 1) =
      ring.rightNeighbor (PPL.shiftRight ring root j) := by
  apply Fin.ext
  simp only [PPL.shiftRight, DirectedRing.rightNeighbor]
  rw [Nat.mod_add_mod]
  congr 1

/-- The E.G16 prefix must be at its genuine chronological site.
The left field already records all earlier source bits, the
prefix count, and zero-marker publication receipts.  The right
field forbids even a second forged prefix tag at another site. -/
def WordPhasePrefixAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  cwPhasePrefix ring h p ∧
    ∀ (site : Fin n) (index : Fin (c.t + 1))
      (z a : Bool),
      h.workerKind site = .prefix index z a →
        site = PPL.shiftRight ring h.root index.val

/-- Replace precisely the former unrestricted PREFIX disjunct,
retaining the two reset phases and unchanged BACK/SUM/READY/DONE
cases from WordEpochInv. -/
def WordEpochInvAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  (h.phase = .validate ∧ WordEpochScrub h) ∨
    (h.phase = .awaitRequest ∧ WordEpochScrub h) ∨
    WordPhasePrefixAt ring h p ∨
    cwPhaseBack ring h p ∨
    cwPhaseSum ring h p ∨
    cwPhaseReady ring h p ∨
    (h.phase = .done ∧ CleanWorkerInv ring h p)

/-- The strengthened predicate cannot hide an arbitrary new
hypothesis: forgetting its extra site equation recovers the
already installed WordEpochInv. -/
theorem wordEpochInvAtForget {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hi : WordEpochInvAt ring h p) :
    WordEpochInv ring h p := by
  rcases hi with hv | ha | hp | hb | hs | hr | hd
  · exact Or.inl hv
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr
      (CleanWorkerPhaseInv.prefix hp.1))
  · exact Or.inr (Or.inr
      (CleanWorkerPhaseInv.back hb))
  · exact Or.inr (Or.inr
      (CleanWorkerPhaseInv.sum hs))
  · exact Or.inr (Or.inr
      (CleanWorkerPhaseInv.ready hr))
  · exact Or.inr (Or.inr
      (CleanWorkerPhaseInv.done hd.1 hd.2))

/-- A canonical worker launch has exactly one PREFIX at the
root and index zero.  This proves chronological geometry,
not merely the numerical OR/AND seed. -/
theorem wordPhasePrefixAtLaunch {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hshape : CleanLaunchShape ring h.root
      (BlockA.wordWorkerLaunch h) p) :
    WordPhasePrefixAt ring (BlockA.wordWorkerLaunch h) p := by
  constructor
  · exact cwPhaseLaunchFromShape ring h.root
      (BlockA.wordWorkerLaunch h) p hshape
  · intro site index z a htag
    change
      (if site = h.root then
        (BlockA.WorkerTag.prefix (0 : Fin (c.t + 1))
          false true)
      else BlockA.WorkerTag.empty) =
        BlockA.WorkerTag.prefix index z a at htag
    by_cases hsite : site = h.root
    · subst site
      simp only [if_pos rfl] at htag
      cases htag
      exact (wordPhaseShiftZero ring h.root).symm
    · simp [hsite] at htag

/-- The exact OLD I0 owner, whose serializer has actually
validated and scrubbed the previous worker, establishes the
strengthened chronological prefix certificate. -/
theorem wordPhaseGenuineIZeroAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (clean : CleanIZero ring h p e) :
    WordEpochInvAt ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  rw [cleanI0_wordT ring h p e (phiW ring p e) clean]
  exact Or.inr (Or.inr (Or.inl
    (wordPhasePrefixAtLaunch ring h (phiW ring p e)
      (cwI0EstablishesLaunchShape ring h p e hne clean))))

/-- An old active prefix has its uniquely positioned source
site; every selected outgoing P1/P3 service visits precisely
the next chronological follower. -/
theorem wordPhasePrefixAtNextSite {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hp : WordPhasePrefixAt ring h p)
    (e : Fin n) (index : Fin (c.t + 1)) (z a : Bool)
    (hactive : h.workerKind e = .prefix index z a) :
    ring.rightNeighbor e =
      PPL.shiftRight ring h.root (index.val + 1) := by
  have hsite := hp.2 e index z a hactive
  rw [hsite]
  exact (wordPhaseShiftSucc ring h.root index.val).symm

/-- On a genuine successful P1 row, the OLD source index
increases by one at the selected physical responder.  The
equation is independent of the numerical value of the bit. -/
theorem wordPhasePoneNextIndexSite {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hp : WordPhasePrefixAt ring h p)
    (e : Fin n) (index nextIndex : Fin (c.t + 1))
    (z a : Bool)
    (hactive : h.workerKind e = .prefix index z a)
    (hindex : nextIndex.val = index.val + 1) :
    ring.rightNeighbor e =
      PPL.shiftRight ring h.root nextIndex.val := by
  rw [hindex]
  exact wordPhasePrefixAtNextSite ring h p
    hp e index z a hactive

/-- The P3 publication of a completed t-sample prefix occurs
on the service from follower t to follower t+1. -/
theorem wordPhasePthreeNextTarget {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hp : WordPhasePrefixAt ring h p)
    (e : Fin n) (index : Fin (c.t + 1)) (z a : Bool)
    (hactive : h.workerKind e = .prefix index z a)
    (hterminal : index.val = c.t) :
    ring.rightNeighbor e =
      PPL.shiftRight ring h.root (c.t + 1) := by
  have hstep := wordPhasePrefixAtNextSite
    ring h p hp e index z a hactive
  rw [hterminal] at hstep
  exact hstep

/-- From the unique PREFIX certificate, every other source
site has the empty worker-kind tag.  This is the exact
precondition for the stale P1/P3 cancellation rows. -/
theorem wordPhasePrefixAtOtherEmpty {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hp : WordPhasePrefixAt ring h p)
    (site e : Fin n) (index : Fin (c.t + 1)) (z a : Bool)
    (hactive : h.workerKind site = .prefix index z a)
    (hother : e ≠ site) :
    h.workerKind e = .empty := by
  obtain ⟨owner, oldIndex, oldZ, oldA,
    _hphase, _htag, _hcount, _hphysical, _hor, _hand,
    _hreads, _hpublished, hothers⟩ := hp.1
  have hsame : site = owner := by
    by_cases hsite : site = owner
    · exact hsite
    · have he := (hothers site hsite).1
      rw [hactive] at he
      cases he
  have hdiff : e ≠ owner := by
    intro he
    exact hother (he.trans hsame.symm)
  exact (hothers e hdiff).1

/-- When the old monitor really cancels a selected physical
row, its successor satisfies the strengthened epoch invariant
in the awaitRequest case, without a fresh site hypothesis. -/
theorem wordEpochAtClearedOwner {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hclear :
      BlockA.wordT ring h p e (phiW ring p e) =
        BlockA.wordClear h
          (BlockA.wordRequestNext ring h p e)) :
    WordEpochInvAt ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  rw [hclear]
  exact Or.inr (Or.inl
    ⟨rfl,
      wordEpochScrubClear h
        (BlockA.wordRequestNext ring h p e)⟩)

/-- A P1 physical row away from the CURRENT active prefix
cannot extend its ledger: the actual worker owner cancels the
color and yields the strengthened idle-scrub alternative. -/
theorem wordPhaseNonactivePoneCancels {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e site : Fin n)
    (index : Fin (c.t + 1)) (z a : Bool)
    (hp : WordPhasePrefixAt ring h p)
    (hactive : h.workerKind site = .prefix index z a)
    (hother : e ≠ site)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P1") :
    WordEpochInvAt ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hworker := wordPhasePrefixWorker ring h p hp.1
  have hstale := wordPhasePrefixAtOtherEmpty ring h p
    hp site e index z a hactive hother
  have hcase :=
    cwPhasePrefixMoveRow (p e) (p (ring.rightNeighbor e)) hrow
  have hcancel :
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) =
      BlockA.wordClear h
        (BlockA.wordRequestNext ring h p e) := by
    simp [BlockA.wordWorkerNext, hcase, hstale]
  exact wordEpochAtClearedOwner ring h p e
    ((wordEpochWorkerDispatch ring h p e hworker hno).trans
      hcancel)

/-- The symmetric non-active P3 physical publication is NOT
allowed to manufacture an accepted first-window receipt. -/
theorem wordPhaseNonactivePthreeCancels {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e site : Fin n)
    (index : Fin (c.t + 1)) (z a : Bool)
    (hp : WordPhasePrefixAt ring h p)
    (hactive : h.workerKind site = .prefix index z a)
    (hother : e ≠ site)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3") :
    WordEpochInvAt ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hworker := wordPhasePrefixWorker ring h p hp.1
  have hstale := wordPhasePrefixAtOtherEmpty ring h p
    hp site e index z a hactive hother
  have hcase :=
    cwPhasePrefixPublishRow (p e) (p (ring.rightNeighbor e)) hrow
  have hcancel :
      BlockA.wordWorkerNext ring h p e
        (BlockA.wordRequestNext ring h p e) =
      BlockA.wordClear h
        (BlockA.wordRequestNext ring h p e) := by
    simp [BlockA.wordWorkerNext, hcase, hstale]
  exact wordEpochAtClearedOwner ring h p e
    ((wordEpochWorkerDispatch ring h p e hworker hno).trans
      hcancel)

/-- A selected physical frame preserving word-visible fields
and SI fields also preserves the chronological prefix location.
This is the actual wordT/wordWorkerNext, not a fictitious
clock or manually chosen successor. -/
theorem wordPhasePrefixAtFrameService {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hp : WordPhasePrefixAt ring h p)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hcase : BlockA.workerCase
      (p e) (p (ring.rightNeighbor e)) = .frame)
    (hvisible : ∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i)
    (hsi : ∀ i : Fin n,
      ((phiW ring p e) i).si = (p i).si) :
    WordEpochInvAt ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hworker := wordPhasePrefixWorker ring h p hp.1
  have hframe := cwPhaseWorkerFrameControl ring h p e
    (BlockA.wordRequestNext ring h p e) hcase
  have hpost := cwPhasePrefixFrameOfUnchangedFields ring h p e
    (BlockA.wordRequestNext ring h p e)
    hp.1 hcase hvisible hsi
  rw [hframe] at hpost
  have hcontrol :
      BlockA.wordT ring h p e (phiW ring p e) =
        { h with requested := BlockA.wordRequestNext ring h p e } :=
    (wordEpochWorkerDispatch ring h p e hworker hno).trans
      hframe
  rw [hcontrol]
  refine Or.inr (Or.inr (Or.inl ⟨hpost, ?_⟩))
  intro site index z a htag
  change h.workerKind site = .prefix index z a at htag
  exact hp.2 site index z a htag

/-!
REMAINING EXACT WHOLE-ROW OBLIGATIONS.

Successful P1 (active PREFIX -> PREFIX): the chronological
responder is now located, and cwPhasePrefix already supplies
every earlier sampled site.  Still needed at the NEW state:
a successful wordWorkerNext branch writes its bounded
prefixReads.push receipt, synchronizes SI.j/z/a at the new
active site, preserves all older beta=0 receipts and OLD
prefix visible bits, and frames the physical SI of all
non-active sites. cwPhasePrefixMoveFold/MoveReceipt/MoveRow
cover only the local arithmetic and published flags.

Successful P3 (active PREFIX -> BACK): its destination site
is the next chronological target and the exact P3 row has
the nonzero kick.  Still needed is constructing the entire
cwPhaseBack witness: new target busy ROOT and BACK cursor,
initial t-window nonzero, new marker equal to trailing AND,
prefixEnd receipt at follower t, and no prior recurrence
publications. cwPhasePrefixPublishNonzero/PublishReceipt/Row
cover only selected numerical and receipt facts.

Other selected rows away from the active PREFIX require
first-match classification.  The nonactive P1/P3 rows above
cancel; FRAME is proved under exact visible/SI framing.
P0/P2 and hard-reset cancellations already have prior
WordEpochInv proofs. Their conversion to WordEpochInvAt
uses the same scrub disjunct above.

After the PREFIX work, B0 needs BACK cursor-position
decrement and physical framing, B1 needs BACK-to-SUM
index-zero/empty-ledger proof, S0 needs SUM old-bit/tap
receipt append plus OR/XOR/AND update, S1 needs SUM-to-READY
nonzero recurrence and beta marker publication, A1 needs
READY-to-BACK target handoff, and A0 needs READY-to-DONE
with CleanWorkerInv and static word-value extraction.

No generated-run counterexample is asserted.  No unconditional
successful-P1/P3 whole-state theorem is claimed here.
-/

end L3.WordPhase

/-!
Successful P1 audit.

This addendum gives the finite-ledger push and physical remote frame,
but records a concrete obstruction to the requested unconditional
successor WordPhasePrefixAt theorem.

The existing WordPhasePrefixAt has no workerCursor condition at its
active PREFIX site. A source P1 changes workerKind at the two sites
and prefixReads, but does not clear workerCursor at the old source.
Consequently a cut with inherited, nonempty workerCursor at the
active site is a valid WordPhasePrefixAt state, can take successful
P1, and is no longer WordPhasePrefixAt. This is an arbitrary-cut
counterexample; no claim is made that the poisoned control is
reachable from an unmodified J_W initial control.

The concrete physical projection below is obtained from an actual
genuine five-site I0, not from an invented PREFIX byte pattern.
Only the active monitor cursor is altered. P3 is untouched.
-/

namespace L3.WordPhase

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- The genuine finite-capacity P1 ledger push: the old count must
be strictly below the capacity, while the new count may EQUAL it.
Older entries are framed; the index just read stores the new entry.
This is the correct inclusive upper bound at the terminal P1. -/
theorem wordPhasePoneLedgerPush {A : Type} {k : Nat}
    (reads : BlockA.FiniteLedger A k) (entry : A)
    (idx : Nat)
    (hcount : reads.count.val = idx)
    (hroom : idx < k) :
    (reads.push entry).count.val = idx + 1 ∧
    (reads.push entry).count.val ≤ k ∧
    (∀ j : Fin k, j.val < idx →
      (reads.push entry).entries j = reads.entries j) ∧
    (∀ j : Fin k, j.val = idx →
      (reads.push entry).entries j = some entry) := by
  have hspace : reads.count.val < k := by
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [BlockA.FiniteLedger.push, hspace, hcount, hroom]
  · have hnew : (reads.push entry).count.val = idx + 1 := by
      simp [BlockA.FiniteLedger.push, hspace, hcount, hroom]
    omega
  · intro j hj
    have hne : j.val ≠ reads.count.val := by
      omega
    simp [BlockA.FiniteLedger.push, hspace, hne]
  · intro j hj
    have heq : j.val = reads.count.val := by
      omega
    simp [BlockA.FiniteLedger.push, hspace, heq]

/-- All ProjW fields, hence also SI and visible U/beta, are unchanged
outside the two selected endpoints of the literal physical phiW. -/
theorem wordPhasePoneRemoteFrame {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c)
    (e i : Fin n)
    (he : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (phiW ring p e) i = p i ∧
    ((phiW ring p e) i).si = (p i).si ∧
    wordVisible (phiW ring p e) i = wordVisible p i := by
  have hframe := cwPhiWFrame ring p e i he hj
  refine ⟨hframe, by rw [hframe], ?_⟩
  simp only [wordVisible, hframe]

/-- A cursor write at the ACTIVE prefix site is invisible to the
current WordPhasePrefixAt predicate. This is exactly the missing
inductive condition exposed by the P1 move. -/
theorem wordPhasePrefixAtCursorWrite {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (e : Fin n) (cursor : BlockA.WorkerTag n c.t)
    (hp : WordPhasePrefixAt ring h p)
    (hactive : ∃ (idx : Fin (c.t + 1)) (z a : Bool),
      h.workerKind e = .prefix idx z a) :
    WordPhasePrefixAt ring
      { h with workerCursor :=
          BlockA.wordPut h.workerCursor e cursor } p := by
  rcases hp with
    ⟨⟨site, idx, z, a, hphase, htag, hcount,
      hphysical, hor, hand, hreads, hpublished, hothers⟩,
      hgeometry⟩
  have he : e = site := by
    by_cases hs : e = site
    · exact hs
    · rcases hactive with ⟨otherIdx, otherZ, otherA, hcolor⟩
      have hempty := (hothers e hs).1
      rw [hcolor] at hempty
      cases hempty
  subst e
  constructor
  · refine ⟨site, idx, z, a, hphase, htag, hcount,
      hphysical, hor, hand, hreads, hpublished, ?_⟩
    intro i hi
    rcases hothers i hi with ⟨hk, hc, hfree⟩
    refine ⟨hk, ?_, hfree⟩
    change (BlockA.wordPut h.workerCursor site cursor) i = .empty
    simp [BlockA.wordPut, hi, hc]
  · intro i nextIdx nextZ nextA htag'
    change h.workerKind i = .prefix nextIdx nextZ nextA at htag'
    exact hgeometry i nextIdx nextZ nextA htag'

/-- At a genuine PREFIX certificate, a site with empty worker-kind
must also have empty worker-cursor. The active site is the ONE
exception not constrained by this statement. -/
theorem wordPhasePrefixAtEmptyKindCursor {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hp : WordPhasePrefixAt ring h p)
    (i : Fin n)
    (hempty : h.workerKind i = .empty) :
    h.workerCursor i = .empty := by
  rcases hp.1 with
    ⟨site, idx, z, a, _hphase, htag, _hcount,
      _hphysical, _hor, _hand, _hreads, _hpublished, hothers⟩
  have hi : i ≠ site := by
    intro he
    subst i
    rw [htag] at hempty
    cases hempty
  exact (hothers i hi).2.1

/-- Actual physical post-I0 projection of the pinned n=5, t=2 toy. -/
def wordPhasePonePoisonProjection : Fin 5 → ProjW cwToyCfg :=
  phiW cwToyRing cwToyProjection (0 : Fin 5)

/-- At the otherwise genuine launched PREFIX(0) control, install
one inherited BACK cursor on the active source ONLY. Since
WordPhasePrefixAt ignores that cursor, this remains a valid cut. -/
def wordPhasePonePoisonControl : BlockA.WordControl 5 cwToyCfg :=
  { BlockA.wordWorkerLaunch cwToyControl with
    workerCursor :=
      BlockA.wordPut
        (BlockA.wordWorkerLaunch cwToyControl).workerCursor
        (0 : Fin 5)
        (.back (0 : Fin 5) (0 : Fin (cwToyCfg.t + 1))) }

/-- Reuse the actual I0 launch certificate, changing only the
unconstrained cursor at its active source. -/
theorem wordPhasePonePoisonWasPrefix :
    WordPhasePrefixAt cwToyRing
      wordPhasePonePoisonControl
      wordPhasePonePoisonProjection := by
  have hne :
      cwToyRing.rightNeighbor (0 : Fin 5) ≠ (0 : Fin 5) := by
    unfold cwToyRing
    decide
  have hshape :=
    cwI0EstablishesLaunchShape cwToyRing cwToyControl
      cwToyProjection (0 : Fin 5) hne cwToyIsIZero
  have hlaunch :
      WordPhasePrefixAt cwToyRing
        (BlockA.wordWorkerLaunch cwToyControl)
        wordPhasePonePoisonProjection :=
    wordPhasePrefixAtLaunch cwToyRing cwToyControl
      wordPhasePonePoisonProjection hshape
  have hactive :
      ∃ (idx : Fin (cwToyCfg.t + 1)) (z a : Bool),
        (BlockA.wordWorkerLaunch cwToyControl).workerKind
          (0 : Fin 5) = .prefix idx z a := by
    exact ⟨0, false, true, hshape.rootTag⟩
  exact wordPhasePrefixAtCursorWrite
    cwToyRing (BlockA.wordWorkerLaunch cwToyControl)
    wordPhasePonePoisonProjection (0 : Fin 5)
    (.back (0 : Fin 5) (0 : Fin (cwToyCfg.t + 1)))
    hlaunch hactive

/-- The OLD physical selected-row classifier really reads P1 on
the poisoned cut's site 0 -> site 1 edge. This is a small closed
owner computation, not a post-state pattern assumption. -/
theorem wordPhasePonePoisonSelectedRow :
    (workerW
      (wordPhasePonePoisonProjection (0 : Fin 5))
      (wordPhasePonePoisonProjection
        (cwToyRing.rightNeighbor (0 : Fin 5)))).row = "P1" := by
  unfold wordPhasePonePoisonProjection
  decide

/-- The literal physical responder gets the new prefix j/z/a
fields from the OLD bit; its U remains unchanged and beta is
published as zero. This is the other independent P1 sublemma. -/
theorem wordPhasePonePoisonResponderFold :
    ((phiW cwToyRing wordPhasePonePoisonProjection
        (0 : Fin 5)) (1 : Fin 5)).si.kind = .PREFIX ∧
    ((phiW cwToyRing wordPhasePonePoisonProjection
        (0 : Fin 5)) (1 : Fin 5)).si.cur = .NONE ∧
    ((phiW cwToyRing wordPhasePonePoisonProjection
        (0 : Fin 5)) (1 : Fin 5)).si.j.val =
      (wordPhasePonePoisonProjection (0 : Fin 5)).si.j.val + 1 ∧
    ((phiW cwToyRing wordPhasePonePoisonProjection
        (0 : Fin 5)) (1 : Fin 5)).si.z =
      ((wordPhasePonePoisonProjection (0 : Fin 5)).si.z ||
        (wordPhasePonePoisonProjection (1 : Fin 5)).u) ∧
    ((phiW cwToyRing wordPhasePonePoisonProjection
        (0 : Fin 5)) (1 : Fin 5)).si.a =
      ((wordPhasePonePoisonProjection (0 : Fin 5)).si.a &&
        (wordPhasePonePoisonProjection (1 : Fin 5)).u) ∧
    ((phiW cwToyRing wordPhasePonePoisonProjection
        (0 : Fin 5)) (1 : Fin 5)).u =
      (wordPhasePonePoisonProjection (1 : Fin 5)).u ∧
    ((phiW cwToyRing wordPhasePonePoisonProjection
        (0 : Fin 5)) (1 : Fin 5)).beta = false := by
  unfold wordPhasePonePoisonProjection
  decide

/-- The actual monitor successor of this P1 service. -/
def wordPhasePonePoisonNextControl : BlockA.WordControl 5 cwToyCfg :=
  BlockA.wordT cwToyRing wordPhasePonePoisonControl
    wordPhasePonePoisonProjection (0 : Fin 5)
    (phiW cwToyRing wordPhasePonePoisonProjection (0 : Fin 5))

/-- Exact successful P1 computation, including new tag, the
bounded OLD read receipt, and the stale active-site cursor.
A cancelled transition would have count 0 and empty cursors,
so these checks also distinguish success from cancellation. -/
theorem wordPhasePonePoisonControlStep :
    wordPhasePonePoisonNextControl.prefixReads.count.val = 1 ∧
    wordPhasePonePoisonNextControl.workerKind (0 : Fin 5) = .empty ∧
    wordPhasePonePoisonNextControl.workerCursor (0 : Fin 5) =
      .back (0 : Fin 5) (0 : Fin (cwToyCfg.t + 1)) ∧
    wordPhasePonePoisonNextControl.workerKind (1 : Fin 5) =
      .prefix (1 : Fin (cwToyCfg.t + 1)) false false ∧
    wordPhasePonePoisonNextControl.prefixReads.entries
      (⟨0, by decide⟩ : Fin cwToyCfg.t) =
        some { source := (1 : Fin 5), oldBit := false } ∧
    wordPhasePonePoisonNextControl.publications (1 : Fin 5) =
      .prefixZero ∧
    wordPhasePonePoisonNextControl.visibleReceipts (1 : Fin 5) =
      true ∧
    wordPhasePonePoisonNextControl.prefixMarkers (1 : Fin 5) =
      true := by
  unfold wordPhasePonePoisonNextControl
    wordPhasePonePoisonControl wordPhasePonePoisonProjection
  decide

/-- The concrete ledger really increments by one and obeys
capacity <= t. The full-capacity P1 would reach count = t,
not a strict inequality. -/
theorem wordPhasePonePoisonLedgerBounded :
    wordPhasePonePoisonNextControl.prefixReads.count.val =
      wordPhasePonePoisonControl.prefixReads.count.val + 1 ∧
    wordPhasePonePoisonNextControl.prefixReads.count.val ≤
      cwToyCfg.t := by
  unfold wordPhasePonePoisonNextControl
    wordPhasePonePoisonControl wordPhasePonePoisonProjection
  decide

/-- The requested general successor certificate is FALSE for an
arbitrary WordPhasePrefixAt cut, despite a successful P1 row and
the correct P1 read/word publication effects. At the old source,
worker-kind becomes empty while its inherited BACK cursor remains. -/
theorem wordPhasePonePoisonRefutesCertificate :
    ¬ WordPhasePrefixAt cwToyRing
      wordPhasePonePoisonNextControl
      (phiW cwToyRing wordPhasePonePoisonProjection (0 : Fin 5)) := by
  intro hp
  have hempty :
      wordPhasePonePoisonNextControl.workerKind
        (0 : Fin 5) = .empty :=
    wordPhasePonePoisonControlStep.2.1
  have hcursor :
      wordPhasePonePoisonNextControl.workerCursor
        (0 : Fin 5) =
        .back (0 : Fin 5) (0 : Fin (cwToyCfg.t + 1)) :=
    wordPhasePonePoisonControlStep.2.2.1
  have hrequired := wordPhasePrefixAtEmptyKindCursor
    cwToyRing wordPhasePonePoisonNextControl
    (phiW cwToyRing wordPhasePonePoisonProjection (0 : Fin 5))
    hp (0 : Fin 5) hempty
  rw [hcursor] at hrequired
  cases hrequired

end L3.WordPhase


/-!
Repaired PREFIX cursor certificate.

Addendum. The extra prefix condition is
exactly that every worker cursor is empty. This is equivalent to
requiring the ACTIVE cursor empty, since the inherited cwPhasePrefix
already requires every nonactive cursor empty.

I0, clears, hard-start scrubs, and unchanged physical frames below
preserve this strengthening. The successful P1 interpreter lemmas
prove the actual guarded control update, bounded ledger push and
absence of stale cursors, not an invented monitor successor.

IMPORTANT PROOF STATUS: a *general* cwPhasePrefix transport through
the physical P1 row is not established in this addendum. The
complete n=5 genuine-I0/P1 instance is supplied as a small closed
decidable test. The remaining general gap is physical P1 visible/SI
transport together with previously published predecessor-markers,
OLD-bit ledger entries, and the OR/AND list folds. No counterexample
to the repaired predicate is asserted. P3 is left untouched.
-/

namespace L3.WordPhase

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- The old phase certificate already says all *other* cursors
are empty. The only new clause is the active cursor, stated
equivalently as global cursor emptiness. It introduces no
spurious all-physical-SI-off requirement. -/
def WordPhasePrefixAtClean {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  WordPhasePrefixAt ring h p ∧
    ∀ i : Fin n, h.workerCursor i = .empty

/-- The new clean condition is imposed ONLY in the PREFIX case.
Scrubbed/validating, BACK, SUM, READY, DONE are unchanged. -/
def WordEpochInvAtClean {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  (h.phase = .validate ∧ WordEpochScrub h) ∨
  (h.phase = .awaitRequest ∧ WordEpochScrub h) ∨
  WordPhasePrefixAtClean ring h p ∨
  cwPhaseBack ring h p ∨
  cwPhaseSum ring h p ∨
  cwPhaseReady ring h p ∨
  (h.phase = .done ∧ CleanWorkerInv ring h p)

/-- Erasing the added cursor clause recovers the earlier,
weaker chronological epoch invariant. -/
theorem wordEpochInvAtCleanForget {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hi : WordEpochInvAtClean ring h p) :
    WordEpochInvAt ring h p := by
  rcases hi with hv | ha | hp | hb | hs | hr | hd
  · exact Or.inl hv
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl hp.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd)))))

/-- The installed I0 launch shape supplies *all* empty
cursor slots; it is stronger than exactly what the repair
needs and does not impose new U/beta restrictions. -/
theorem wordPhasePrefixAtCleanLaunch {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hshape : CleanLaunchShape ring h.root
      (BlockA.wordWorkerLaunch h) p) :
    WordPhasePrefixAtClean ring (BlockA.wordWorkerLaunch h) p := by
  exact ⟨wordPhasePrefixAtLaunch ring h p hshape,
    hshape.cursorsEmpty⟩

/-- The actual physical I0 owner, including its fresh
serializer validation and source/responder scrubbing,
establishes the strengthened epoch predicate. -/
theorem wordPhaseGenuineIZeroAtClean {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (clean : CleanIZero ring h p e) :
    WordEpochInvAtClean ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  rw [cleanI0_wordT ring h p e (phiW ring p e) clean]
  exact Or.inr (Or.inr (Or.inl
    (wordPhasePrefixAtCleanLaunch ring h
      (phiW ring p e)
      (cwI0EstablishesLaunchShape ring h p e hne clean))))

/-- Both scrubbing constructors erase every worker cursor,
tag, ledger and publication authority. The old scrub lemmas
already prove this exact current-state assertion. -/
theorem wordEpochAtCleanClear {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hclear :
      BlockA.wordT ring h p e (phiW ring p e) =
        BlockA.wordClear h
          (BlockA.wordRequestNext ring h p e)) :
    WordEpochInvAtClean ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  rw [hclear]
  exact Or.inr (Or.inl
    ⟨rfl, wordEpochScrubClear h
      (BlockA.wordRequestNext ring h p e)⟩)

/-- Hard S1 is an outer-dispatch priority: its actual
wordT successor is a validating scrub, not PREFIX. -/
theorem wordEpochAtCleanHardStart {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hnotdone : h.phase ≠ .done)
    (hstart : BlockA.wordIsHardStart ring h p e) :
    WordEpochInvAtClean ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hstep :
      BlockA.wordT ring h p e (phiW ring p e) =
        BlockA.wordHardLaunch h e (ring.rightNeighbor e) := by
    simp [BlockA.wordT, hnotdone, hstart]
  rw [hstep]
  exact Or.inl
    ⟨rfl, wordEpochScrubHardLaunch h e (ring.rightNeighbor e)⟩

/-- A genuine F/FRAME control update preserves every colored
cursor. The same visible and physical-SI premises as the
earlier established frame theorem are retained exactly. -/
theorem wordPhasePrefixAtCleanFrameService
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (hp : WordPhasePrefixAtClean ring h p)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hcase : BlockA.workerCase
      (p e) (p (ring.rightNeighbor e)) = .frame)
    (hvisible : ∀ i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i)
    (hsi : ∀ i : Fin n,
      ((phiW ring p e) i).si = (p i).si) :
    WordEpochInvAtClean ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hworker := wordPhasePrefixWorker ring h p hp.1.1
  have hframe := cwPhaseWorkerFrameControl ring h p e
    (BlockA.wordRequestNext ring h p e) hcase
  have hpost := cwPhasePrefixFrameOfUnchangedFields
    ring h p e (BlockA.wordRequestNext ring h p e)
    hp.1.1 hcase hvisible hsi
  rw [hframe] at hpost
  have hcontrol :
      BlockA.wordT ring h p e (phiW ring p e) =
        { h with requested := BlockA.wordRequestNext ring h p e } :=
    (wordEpochWorkerDispatch ring h p e hworker hno).trans
      hframe
  rw [hcontrol]
  refine Or.inr (Or.inr (Or.inl ⟨⟨hpost, ?_⟩, ?_⟩))
  · intro site index z a htag
    change h.workerKind site = .prefix index z a at htag
    exact hp.1.2 site index z a htag
  · exact hp.2

/-- Exactly the guard tested by the positive, non-cancelling
prefixMove branch of wordWorkerNext, AFTER matching its
old source tag. This is not an invented history predicate. -/
def WordPhasePoneGuard {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (idx : Fin (c.t + 1)) (z a : Bool) : Prop :=
  (p e).si.kind = .PREFIX ∧
  (p e).si.busy = false ∧
  (p e).si.cur = .NONE ∧
  (p e).si.j = idx ∧
  (p e).si.z = z ∧ (p e).si.a = a ∧
  h.prefixReads.count.val = idx.val ∧
  h.workerKind (ring.rightNeighbor e) = .empty ∧
  h.workerCursor (ring.rightNeighbor e) = .empty ∧
  (workerW (p e) (p (ring.rightNeighbor e))).y.kind = .PREFIX ∧
  (workerW (p e) (p (ring.rightNeighbor e))).y.j.val =
    idx.val + 1 ∧
  (workerW (p e) (p (ring.rightNeighbor e))).y.z =
    (z || (p (ring.rightNeighbor e)).u) ∧
  (workerW (p e) (p (ring.rightNeighbor e))).y.a =
    (a && (p (ring.rightNeighbor e)).u) ∧
  (idx.val + 1 < c.t →
    (workerW (p e) (p (ring.rightNeighbor e))).betaY = false)

/-- Exact positive prefixMove branch of the literal interpreter,
with its existing nested publication condition. No cursor field
is written in either branch. -/
def wordPhasePoneControl {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1)) :
    BlockA.WordControl n c :=
  if idx.val + 1 < c.t then
    { h with
      requested := request
      workerKind :=
        BlockA.wordPut
          (BlockA.wordPut h.workerKind e .empty)
          (ring.rightNeighbor e)
          (.prefix
            (workerW (p e) (p (ring.rightNeighbor e))).y.j
            (workerW (p e) (p (ring.rightNeighbor e))).y.z
            (workerW (p e) (p (ring.rightNeighbor e))).y.a)
      prefixReads := h.prefixReads.push
        { source := ring.rightNeighbor e,
          oldBit := (p (ring.rightNeighbor e)).u }
      publications :=
        BlockA.wordPut h.publications
          (ring.rightNeighbor e) .prefixZero
      visibleReceipts :=
        BlockA.wordPut h.visibleReceipts
          (ring.rightNeighbor e) true
      prefixMarkers :=
        BlockA.wordPut h.prefixMarkers
          (ring.rightNeighbor e) true }
  else
    { h with
      requested := request
      workerKind :=
        BlockA.wordPut
          (BlockA.wordPut h.workerKind e .empty)
          (ring.rightNeighbor e)
          (.prefix
            (workerW (p e) (p (ring.rightNeighbor e))).y.j
            (workerW (p e) (p (ring.rightNeighbor e))).y.z
            (workerW (p e) (p (ring.rightNeighbor e))).y.a)
      prefixReads := h.prefixReads.push
        { source := ring.rightNeighbor e,
          oldBit := (p (ring.rightNeighbor e)).u } }

/-- This equality connects the directly checked OLD selected-row
classifier and every successful P1 subguard to wordWorkerNext,
without postulating a new control step. -/
theorem wordPhasePoneControlFromGuard {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool)
    (idx : Fin (c.t + 1)) (z a : Bool)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixMove)
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePoneGuard ring h p e idx z a) :
    BlockA.wordWorkerNext ring h p e request =
      wordPhasePoneControl ring h p e request idx := by
  rcases hguard with
    ⟨hk, hb, hc, hj, hz, ha, hcount, hdest, hcursor,
      hnewk, hnewj, hnewz, hnewa, hbeta⟩
  simp [BlockA.wordWorkerNext, wordPhasePoneControl,
    hcase, hkind, hk, hb, hc, hj, hz, ha, hcount,
    hdest, hcursor, hnewk, hnewj, hnewz, hnewa, hbeta]
  all_goals
    intro hlt hbt
    rw [hbeta hlt] at hbt
    cases hbt

/-- The successful control result is the ACTUAL wordT result
provided the already-running monitor has no outer hard restart.
This is a dispatch identity, not an extra transition relation. -/
theorem wordPhasePoneActualControl {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (idx : Fin (c.t + 1)) (z a : Bool)
    (hp : WordPhasePrefixAtClean ring h p)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixMove)
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePoneGuard ring h p e idx z a) :
    BlockA.wordT ring h p e (phiW ring p e) =
      wordPhasePoneControl ring h p e
        (BlockA.wordRequestNext ring h p e) idx := by
  exact (wordEpochWorkerDispatch ring h p e
    (wordPhasePrefixWorker ring h p hp.1.1) hno).trans
    (wordPhasePoneControlFromGuard ring h p e
      (BlockA.wordRequestNext ring h p e) idx z a
      hcase hkind hguard)

/-- The earlier cursor failure cannot recur in a guarded
successful P1 from a clean prefix: neither positive P1 branch
changes the old globally empty cursor array. -/
theorem wordPhasePoneSuccessfulCursors {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1)) (z a : Bool)
    (hp : WordPhasePrefixAtClean ring h p)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixMove)
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePoneGuard ring h p e idx z a) :
    ∀ i : Fin n,
      (BlockA.wordWorkerNext ring h p e request).workerCursor i =
        .empty := by
  rw [wordPhasePoneControlFromGuard ring h p e
    request idx z a hcase hkind hguard]
  unfold wordPhasePoneControl
  split <;> exact hp.2

/-- One new OLD-bit read, and bounded count <= t, from every
positive P1 control branch. Notice that count = t is allowed. -/
theorem wordPhasePoneSuccessfulLedger {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1)) (z a : Bool)
    (hroom : idx.val < c.t)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixMove)
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePoneGuard ring h p e idx z a) :
    (BlockA.wordWorkerNext ring h p e request).prefixReads.count.val =
        idx.val + 1 ∧
    (BlockA.wordWorkerNext ring h p e request).prefixReads.count.val ≤
        c.t := by
  have hcount := hguard.2.2.2.2.2.2.1
  have hread := wordPhasePoneLedgerPush h.prefixReads
    ({ source := ring.rightNeighbor e,
       oldBit := (p (ring.rightNeighbor e)).u } :
      BlockA.PrefixSample n) idx.val hcount hroom
  rw [wordPhasePoneControlFromGuard ring h p e
    request idx z a hcase hkind hguard]
  unfold wordPhasePoneControl
  split <;> exact ⟨hread.1, hread.2.1⟩

/-- The selected edge moves its unique colored prefix kind to
the responder and clears the initiating kind; no tag duplication.
The n>=2 endpoint distinction is explicitly exposed. -/
theorem wordPhasePoneSuccessfulTag {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1)) (z a : Bool)
    (hne : ring.rightNeighbor e ≠ e)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixMove)
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePoneGuard ring h p e idx z a) :
    (BlockA.wordWorkerNext ring h p e request).workerKind
      (ring.rightNeighbor e) =
        .prefix
          (workerW (p e) (p (ring.rightNeighbor e))).y.j
          (workerW (p e) (p (ring.rightNeighbor e))).y.z
          (workerW (p e) (p (ring.rightNeighbor e))).y.a ∧
    (BlockA.wordWorkerNext ring h p e request).workerKind e =
      .empty := by
  rw [wordPhasePoneControlFromGuard ring h p e
    request idx z a hcase hkind hguard]
  unfold wordPhasePoneControl
  split
  · constructor
    · simp [BlockA.wordPut]
    · simp [BlockA.wordPut, hne, Ne.symm hne]
  · constructor
    · simp [BlockA.wordPut]
    · simp [BlockA.wordPut, hne, Ne.symm hne]

/-- The new prefixZero publication is the actual guarded
wordWorkerNext receipt, not a marker inferred from the bit. -/
theorem wordPhasePoneSuccessfulReceipt {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1)) (z a : Bool)
    (hshort : idx.val + 1 < c.t)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixMove)
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePoneGuard ring h p e idx z a) :
    (BlockA.wordWorkerNext ring h p e request).publications
      (ring.rightNeighbor e) = .prefixZero ∧
    (BlockA.wordWorkerNext ring h p e request).visibleReceipts
      (ring.rightNeighbor e) = true ∧
    (BlockA.wordWorkerNext ring h p e request).prefixMarkers
      (ring.rightNeighbor e) = true := by
  rw [wordPhasePoneControlFromGuard ring h p e
    request idx z a hcase hkind hguard]
  simp [wordPhasePoneControl, hshort, BlockA.wordPut]

/-!
GENERAL P1 COMPLETION GATE (not silently assumed).

The empty-cursor repair has eliminated the earlier legitimate
arbitrary-cut counterexample. For the universal successful-P1
certificate, the remaining proof must still derive from the
literal siStep P1 branch, *without adding them as axioms*:

(a) physical source SI becomes offSI; responder SI equals the
    folded PREFIX with j=old j+1, z=old z OR OLD u_y,
    a=old a AND OLD u_y;
(b) U is unchanged everywhere and beta changes ONLY at the
    responder, to zero iff new j < t (including when the site
    overlaps an already published slot on a small ring);
(c) all remote SI fields are cwPhiWFrame'd; the source is free;
(d) List.range-snoc identities propagate cwPrefixOr/And;
(e) all old prefixReads entries remain and agree with the
    successor U, and every old prefixZero publication remains
    true, with the new follower receipt when new j < t;
(f) the new colored tag is uniquely at shiftRight root (old j+1).
    Its location follows wordPhasePoneNextIndexSite and the
    tag proof above. The quantitative guard has new count <= t.

A theorem assuming (a)-(f) is not a proof of this source claim.
The general WordPhasePrefixAtClean P1 transport is therefore
NOT marked proved in this uncompiled section. No further
counterexample is claimed or invented.

P3 still requires: selected P3 guard and chronological target
at follower t+1; source's all-zero kick making the first window
nonzero; physical beta of follower t equals prefix AND after
the kick; the old prefixZero receipts remain valid; the
prefixEnd publication and visible receipt at follower t;
new ROOT/busy physical target and BACK cursor with index t;
sumReads=0; no earlier recurrence publications. Every claim
must use the actual wordT/phiW selected service.
-/

end L3.WordPhase

/-!
Successful P1: physical row, visible U/beta, published
prefix frames, actual OLD-read ledger, List.range snoc folds,
and clean chronological successor certificate.

The publication proof handles cyclic aliasing rather than assuming
that earlier follower sites are necessarily remote from the edge.
-/

namespace L3.WordPhase

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- Projecting the row of a conditional SI result does not inspect
the other SI fields. Used to eliminate the non-P1 suffix cheaply. -/
private theorem siStepRowIte {t : Nat}
    (q : Prop) [Decidable q] (yes no : SIResult t) :
    (if q then yes else no).row =
      (if q then yes.row else no.row) := by
  split <;> rfl

/-- Source-level P1 row inversion. Resolve just the four guards
before P1; avoid splitting the full nested siStep result.
When the P1 guard is false, every remaining branch has a
different literal row name. -/
private theorem siStepRowPOne {c : Compiled}
    (ox oy : Agent c) (post : PostE) (hard : HardFlags)
    (hrow : (siStep c ox oy post hard).row = "P1") :
    siStep c ox oy post hard =
      { x := offSI c.t
        y := { kind := .PREFIX, busy := false, cur := .NONE,
               j := siJ c.t (ox.si.j.val + 1),
               z := (ox.si.z || oy.u), p := false,
               a := (ox.si.a && oy.u) }
        uX := ox.u
        uY := oy.u
        betaX := ox.beta
        betaY := if ox.si.j.val + 1 < c.t then false else oy.beta
        done := false
        row := "P1" } := by
  by_cases haccept : hard.hardAccept = true
  · have hbad : (siStep c ox oy post hard).row = "I0" := by
      simp [siStep, haccept]
    rw [hbad] at hrow
    exact absurd hrow (by decide)
  · by_cases herase :
        hard.hardLeft = true ∨ hard.hardRight = true
    · have hbad : (siStep c ox oy post hard).row = "I1" := by
        simp [siStep, haccept, herase]
      rw [hbad] at hrow
      exact absurd hrow (by decide)
    · by_cases hexit :
          (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                post.eY.l = true) ∧ freeSI oy.si = true)
      · have hbad : (siStep c ox oy post hard).row = "P0" := by
          simp [siStep, haccept, herase, hexit]
        rw [hbad] at hrow
        exact absurd hrow (by decide)
      · by_cases hmove :
            (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                  ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                  post.eY.l = false) ∧ freeSI oy.si = true)
        · simp [siStep, haccept, herase, hexit, hmove]
        · have hnot :
              (siStep c ox oy post hard).row ≠ "P1" := by
            simp [siStep, haccept, herase, hexit, hmove,
              siStepRowIte]
            repeat' split
            all_goals decide
          exact False.elim (hnot hrow)

/-- The only literal siStep row "P1" is the prefix-move branch.
Here the selected source SI is erased, the responder cursor is
NONE, U is preserved, and the only possible beta write is at y. -/
theorem wordPhasePoneOwnerFields {c : Compiled}
    (x y : ProjW c)
    (hrow : (workerW x y).row = "P1") :
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y.cur = .NONE ∧
    (workerW x y).uX = x.u ∧
    (workerW x y).uY = y.u ∧
    (workerW x y).betaX = x.beta ∧
    (workerW x y).betaY =
      (if x.si.j.val + 1 < c.t then false else y.beta) := by
  unfold workerW at hrow ⊢
  have hresult := siStepRowPOne
    x.lift y.lift (postW x y) (serW x y).hard hrow
  rw [hresult]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- (1) Physical P1 field and visible-word transport on the
actual two-endpoint phiW. Nonselected sites use cwPhiWFrame. -/
theorem wordPhasePonePhysicalFields {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P1") :
    ((phiW ring p e) e).si = offSI c.t ∧
    ((phiW ring p e) (ring.rightNeighbor e)).si.cur = .NONE ∧
    (∀ i : Fin n, ((phiW ring p e) i).u = (p i).u) ∧
    (∀ i : Fin n, i ≠ ring.rightNeighbor e →
       ((phiW ring p e) i).beta = (p i).beta) ∧
    ((phiW ring p e) (ring.rightNeighbor e)).beta =
      (if (p e).si.j.val + 1 < c.t then false
       else (p (ring.rightNeighbor e)).beta) := by
  rcases wordPhasePoneOwnerFields
    (p e) (p (ring.rightNeighbor e)) hrow with
    ⟨hsource, hcur, huX, huY, hbX, hbY⟩
  have hleft :
      (phiW ring p e) e =
        (pairW (p e) (p (ring.rightNeighbor e))).1 := by
    simp only [phiW, projectedEdge, if_pos rfl]
  have hright :
      (phiW ring p e) (ring.rightNeighbor e) =
        (pairW (p e) (p (ring.rightNeighbor e))).2 := by
    simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hleft]
    change (workerW (p e) (p (ring.rightNeighbor e))).x =
      offSI c.t
    exact hsource
  · rw [hright]
    change (workerW (p e)
      (p (ring.rightNeighbor e))).y.cur = .NONE
    exact hcur
  · intro i
    by_cases hi : i = e
    · subst i
      rw [hleft]
      change (workerW (p e)
        (p (ring.rightNeighbor e))).uX = (p e).u
      exact huX
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        rw [hright]
        change (workerW (p e)
          (p (ring.rightNeighbor e))).uY =
          (p (ring.rightNeighbor e)).u
        exact huY
      · rw [cwPhiWFrame ring p e i hi hj]
  · intro i hj
    by_cases hi : i = e
    · subst i
      rw [hleft]
      change (workerW (p e)
        (p (ring.rightNeighbor e))).betaX = (p e).beta
      exact hbX
    · rw [cwPhiWFrame ring p e i hi hj]
  · rw [hright]
    change (workerW (p e)
      (p (ring.rightNeighbor e))).betaY =
      (if (p e).si.j.val + 1 < c.t then false
       else (p (ring.rightNeighbor e)).beta)
    exact hbY

/-- U-only congruence of the next sampled clockwise bit. -/
theorem wordPhasePoneBitCongr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hu : ∀ i : Fin n, (p' i).u = (p i).u)
    (k : Nat) :
    cwBit ring root p' k = cwBit ring root p k := by
  simpa only [cwBit] using hu (PPL.shiftRight ring root k)

/-- (4a) OR fold at length idx+1 equals the old length-idx
fold with the actual next source bit appended. -/
theorem wordPhasePoneOrSucc {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (idx : Nat) :
    cwPrefixOr ring root p (idx + 1) =
      (cwPrefixOr ring root p idx ||
        cwBit ring root p (idx + 1)) := by
  simp [cwPrefixOr, List.range_succ, List.foldl_append]

/-- (4b) AND fold has the same List.range-snoc equation. -/
theorem wordPhasePoneAndSucc {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (idx : Nat) :
    cwPrefixAnd ring root p (idx + 1) =
      (cwPrefixAnd ring root p idx &&
        cwBit ring root p (idx + 1)) := by
  simp [cwPrefixAnd, List.range_succ, List.foldl_append]

/-- (4c) P1 preserves all U coordinates, hence both complete
prefix folds are equal on the OLD and successor projections. -/
theorem wordPhasePonePrefixFoldsCongr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hu : ∀ i : Fin n, (p' i).u = (p i).u)
    (len : Nat) :
    cwPrefixOr ring root p' len =
      cwPrefixOr ring root p len ∧
    cwPrefixAnd ring root p' len =
      cwPrefixAnd ring root p len := by
  constructor
  · have hf :
        (fun z k => z || cwBit ring root p' (k + 1)) =
          (fun z k => z || cwBit ring root p (k + 1)) := by
      funext z k
      rw [wordPhasePoneBitCongr ring root p' p hu (k + 1)]
    unfold cwPrefixOr
    rw [hf]
  · have hf :
        (fun a k => a && cwBit ring root p' (k + 1)) =
          (fun a k => a && cwBit ring root p (k + 1)) := by
      funext a k
      rw [wordPhasePoneBitCongr ring root p' p hu (k + 1)]
    unfold cwPrefixAnd
    rw [hf]

/-- (3a) The bounded ledger push retains all prior entries
and writes exactly the OLD responder U at the new index.
The proof uses the earlier push equation. -/
theorem wordPhasePonePushedLedgerAgreement
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p' p : Fin n → ProjW c) (e : Fin n)
    (idx : Fin (c.t + 1))
    (hcount : h.prefixReads.count.val = idx.val)
    (hroom : idx.val < c.t)
    (hreads : ∀ q : Fin c.t, q.val < idx.val →
      h.prefixReads.entries q =
        some { source := PPL.shiftRight ring h.root (q.val + 1),
               oldBit := cwBit ring h.root p (q.val + 1) })
    (hgeom : ring.rightNeighbor e =
      PPL.shiftRight ring h.root (idx.val + 1))
    (hu : ∀ i : Fin n, (p' i).u = (p i).u) :
    ∀ q : Fin c.t, q.val < idx.val + 1 →
      (h.prefixReads.push
        { source := ring.rightNeighbor e,
          oldBit := (p (ring.rightNeighbor e)).u }).entries q =
        some { source := PPL.shiftRight ring h.root (q.val + 1),
               oldBit := cwBit ring h.root p' (q.val + 1) } := by
  have hpush := wordPhasePoneLedgerPush h.prefixReads
    ({ source := ring.rightNeighbor e,
       oldBit := (p (ring.rightNeighbor e)).u } :
      BlockA.PrefixSample n) idx.val hcount hroom
  intro q hq
  by_cases hlt : q.val < idx.val
  · rw [hpush.2.2.1 q hlt]
    have hbit := wordPhasePoneBitCongr
      ring h.root p' p hu (q.val + 1)
    rw [hbit]
    exact hreads q hlt
  · have heq : q.val = idx.val := by omega
    rw [hpush.2.2.2 q heq]
    have hsource :
        PPL.shiftRight ring h.root (q.val + 1) =
          ring.rightNeighbor e := by
      rw [heq]
      exact hgeom.symm
    have hbit :
        cwBit ring h.root p' (q.val + 1) =
          (p (ring.rightNeighbor e)).u := by
      rw [wordPhasePoneBitCongr ring h.root p' p hu (q.val + 1)]
      simp only [cwBit, hsource]
    rw [hsource, hbit]

/-- (3b) The successful P1 decoded control contains that same
ledger; no additional hypothetical control is introduced. -/
theorem wordPhasePoneLedgerAgreement
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p' p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1))
    (hcount : h.prefixReads.count.val = idx.val)
    (hroom : idx.val < c.t)
    (hreads : ∀ q : Fin c.t, q.val < idx.val →
      h.prefixReads.entries q =
        some { source := PPL.shiftRight ring h.root (q.val + 1),
               oldBit := cwBit ring h.root p (q.val + 1) })
    (hgeom : ring.rightNeighbor e =
      PPL.shiftRight ring h.root (idx.val + 1))
    (hu : ∀ i : Fin n, (p' i).u = (p i).u) :
    ∀ q : Fin c.t, q.val < idx.val + 1 →
      (wordPhasePoneControl ring h p e request idx).prefixReads.entries q =
        some { source := PPL.shiftRight ring h.root (q.val + 1),
               oldBit := cwBit ring h.root p' (q.val + 1) } := by
  intro q hq
  have hentry := wordPhasePonePushedLedgerAgreement
    ring h p' p e idx hcount hroom hreads hgeom hu q hq
  unfold wordPhasePoneControl
  split <;> exact hentry

/-- P1 reissues any overlapping prefixZero receipt or frames
the original one. No nonaliasing assumption is made. -/
theorem wordPhasePoneOldPublicationFrame
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e i : Fin n)
    (request : Bool) (idx : Fin (c.t + 1))
    (hold : h.publications i = .prefixZero ∧
      h.visibleReceipts i = true ∧
      h.prefixMarkers i = true) :
    (wordPhasePoneControl ring h p e request idx).publications i =
      .prefixZero ∧
    (wordPhasePoneControl ring h p e request idx).visibleReceipts i =
      true ∧
    (wordPhasePoneControl ring h p e request idx).prefixMarkers i =
      true := by
  unfold wordPhasePoneControl
  split
  · by_cases hi : i = ring.rightNeighbor e
    · subst i
      simp [BlockA.wordPut]
    · simpa [BlockA.wordPut, hi] using hold
  · exact hold

/-- A new nonterminal P1 follower gets exactly its prefixZero
publication, visible receipt and prefix-marker control flag. -/
theorem wordPhasePoneNewPublication
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1))
    (hshort : idx.val + 1 < c.t) :
    (wordPhasePoneControl ring h p e request idx).publications
      (ring.rightNeighbor e) = .prefixZero ∧
    (wordPhasePoneControl ring h p e request idx).visibleReceipts
      (ring.rightNeighbor e) = true ∧
    (wordPhasePoneControl ring h p e request idx).prefixMarkers
      (ring.rightNeighbor e) = true := by
  simp [wordPhasePoneControl, hshort, BlockA.wordPut]

/-- A successful P1 retains the root of its monitor, in
either branch of the terminal-index publication test. -/
theorem wordPhasePoneControlRoot {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1)) :
    (wordPhasePoneControl ring h p e request idx).root = h.root := by
  unfold wordPhasePoneControl
  split <;> rfl

/-- (2) Transport of *all* prefixZero publications and marker
values, including the case where an old published site coincides
with the P1 responder on a cyclic ring. -/
theorem wordPhasePonePublishedTransport
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p' p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1))
    (hpublished : cwPhasePublishedPrefix ring h p idx.val)
    (hgeom : ring.rightNeighbor e =
      PPL.shiftRight ring h.root (idx.val + 1))
    (hbetaFrame : ∀ i : Fin n, i ≠ ring.rightNeighbor e →
      (p' i).beta = (p i).beta)
    (hbetaResponder :
      (p' (ring.rightNeighbor e)).beta =
        (if idx.val + 1 < c.t then false
         else (p (ring.rightNeighbor e)).beta)) :
    cwPhasePublishedPrefix ring
      (wordPhasePoneControl ring h p e request idx)
      p' (idx.val + 1) := by
  intro k hk hle hlt
  rw [wordPhasePoneControlRoot ring h p e request idx]
  by_cases hprev : k.val ≤ idx.val
  · rcases hpublished k hk hprev hlt with
      ⟨hpub, hvis, hmarker, hbeta⟩
    have hreceipts := wordPhasePoneOldPublicationFrame
      ring h p e (PPL.shiftRight ring h.root k.val)
      request idx ⟨hpub, hvis, hmarker⟩
    refine ⟨hreceipts.1, hreceipts.2.1,
      hreceipts.2.2, ?_⟩
    change (p' (PPL.shiftRight ring h.root k.val)).beta = false
    by_cases heq :
        PPL.shiftRight ring h.root k.val =
          ring.rightNeighbor e
    · rw [heq, hbetaResponder]
      by_cases hshort : idx.val + 1 < c.t
      · simp [hshort]
      · simp only [if_neg hshort]
        rw [← heq]
        simpa only [cwMarker] using hbeta
    · rw [hbetaFrame _ heq]
      simpa only [cwMarker] using hbeta
  · have hnew : k.val = idx.val + 1 := by omega
    have hshort : idx.val + 1 < c.t := by omega
    have heq :
        PPL.shiftRight ring h.root k.val =
          ring.rightNeighbor e := by
      rw [hnew]
      exact hgeom.symm
    have hreceipts := wordPhasePoneNewPublication
      ring h p e request idx hshort
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [heq] using hreceipts.1
    · simpa only [heq] using hreceipts.2.1
    · simpa only [heq] using hreceipts.2.2
    · change (p' (PPL.shiftRight ring h.root k.val)).beta = false
      rw [heq, hbetaResponder, if_pos hshort]

/-- A successful P1 moves the sole active color to the responder
and leaves all other worker-kind sites empty. -/
theorem wordPhasePoneOtherKinds {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) (idx : Fin (c.t + 1))
    (hne : ring.rightNeighbor e ≠ e)
    (hothers : ∀ i : Fin n, i ≠ e →
      h.workerKind i = .empty) :
    ∀ i : Fin n, i ≠ ring.rightNeighbor e →
      (wordPhasePoneControl ring h p e request idx).workerKind i =
        .empty := by
  intro i hi
  by_cases he : i = e
  · subst i
    unfold wordPhasePoneControl
    split <;> simp [BlockA.wordPut, hne, Ne.symm hne]
  · have hold := hothers i he
    unfold wordPhasePoneControl
    split <;> simp [BlockA.wordPut, he, hi, hold]

/-- The P1 initiator is offSI, and any other non-responder
site was previously free and is physically remote. -/
theorem wordPhasePoneOtherFree {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p' p : Fin n → ProjW c) (e : Fin n)
    (hsource : (p' e).si = offSI c.t)
    (hremote : ∀ i : Fin n, i ≠ e →
      i ≠ ring.rightNeighbor e → p' i = p i)
    (hothers : ∀ i : Fin n, i ≠ e →
      freeSI (p i).si = true) :
    ∀ i : Fin n, i ≠ ring.rightNeighbor e →
      freeSI (p' i).si = true := by
  intro i hi
  by_cases he : i = e
  · subst i
    rw [hsource]
    rfl
  · rw [hremote i he hi]
    exact hothers i he

/-- Assembly: the literal successful P1 control, the actual
physical P1 row, and the clean old certificate give a complete
WordPhasePrefixAtClean successor with new index idx+1. -/
theorem wordPhasePoneCleanSuccess {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (idx : Fin (c.t + 1)) (z a : Bool)
    (hp : WordPhasePrefixAtClean ring h p)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P1")
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePoneGuard ring h p e idx z a) :
    WordPhasePrefixAtClean ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hcase : BlockA.workerCase
      (p e) (p (ring.rightNeighbor e)) = .prefixMove :=
    cwPhasePrefixMoveRow (p e) (p (ring.rightNeighbor e)) hrow
  have hno : ¬ BlockA.wordIsHardStart ring h p e := by
    intro hs
    dsimp only [BlockA.wordIsHardStart] at hs
    rcases hs with ⟨_, _, _, _, _, herase⟩
    rw [hcase] at herase
    cases herase
  have hguardFacts := hguard
  rcases hguardFacts with
    ⟨_hxkind, _hbusy, _hxcur, hxj, _hxz, _hxa,
      hcount, hdest, _hcursor, hykind, hyj, hyz, hya, _hbeta⟩
  have hne : ring.rightNeighbor e ≠ e := by
    intro heq
    rw [heq, hkind] at hdest
    cases hdest
  have hroom : idx.val < c.t := by
    have hjlt :=
      (workerW (p e) (p (ring.rightNeighbor e))).y.j.isLt
    omega
  have hgeom : ring.rightNeighbor e =
      PPL.shiftRight ring h.root (idx.val + 1) :=
    wordPhasePrefixAtNextSite ring h p hp.1 e idx z a hkind
  have hphys := wordPhasePonePhysicalFields ring p e hne hrow
  rcases hphys with ⟨hsource, hcur, hu, hbetaFrame, hbetaRaw⟩
  have hbetaResponder :
      ((phiW ring p e) (ring.rightNeighbor e)).beta =
        (if idx.val + 1 < c.t then false
         else (p (ring.rightNeighbor e)).beta) := by
    rw [hxj] at hbetaRaw
    exact hbetaRaw
  have hcontrol := wordPhasePoneActualControl ring h p e
    idx z a hp hno hcase hkind hguard
  have hrootPost := wordPhasePoneControlRoot ring h p e
    (BlockA.wordRequestNext ring h p e) idx
  rw [hcontrol]
  rcases hp.1.1 with
    ⟨site, oldIdx, oldZ, oldA, hphase, htag, _oldCount,
      _oldPhysical, hor, hand, hreads, hpublished, hothers⟩
  have hsame : site = e := by
    by_cases hs : e = site
    · exact hs.symm
    · have hempty := (hothers e hs).1
      rw [hkind] at hempty
      cases hempty
  subst site
  have htagEq :
      BlockA.WorkerTag.prefix oldIdx oldZ oldA =
        .prefix idx z a := htag.symm.trans hkind
  cases htagEq
  have hnewTag :
      (wordPhasePoneControl ring h p e
        (BlockA.wordRequestNext ring h p e) idx).workerKind
          (ring.rightNeighbor e) =
        .prefix
          (workerW (p e) (p (ring.rightNeighbor e))).y.j
          (workerW (p e) (p (ring.rightNeighbor e))).y.z
          (workerW (p e) (p (ring.rightNeighbor e))).y.a := by
    have htagStep := (wordPhasePoneSuccessfulTag ring h p e
      (BlockA.wordRequestNext ring h p e)
      idx z a hne hcase hkind hguard).1
    rw [wordPhasePoneControlFromGuard ring h p e
      (BlockA.wordRequestNext ring h p e)
      idx z a hcase hkind hguard] at htagStep
    exact htagStep
  have hnewCount :
      (wordPhasePoneControl ring h p e
        (BlockA.wordRequestNext ring h p e) idx).prefixReads.count.val =
        (workerW (p e) (p (ring.rightNeighbor e))).y.j.val := by
    have hpushed := wordPhasePoneLedgerPush h.prefixReads
      ({ source := ring.rightNeighbor e,
         oldBit := (p (ring.rightNeighbor e)).u } :
        BlockA.PrefixSample n) idx.val hcount hroom
    unfold wordPhasePoneControl
    split <;> exact hpushed.1.trans hyj.symm
  have hotherKinds :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        (wordPhasePoneControl ring h p e
          (BlockA.wordRequestNext ring h p e) idx).workerKind i =
          .empty :=
    wordPhasePoneOtherKinds ring h p e
      (BlockA.wordRequestNext ring h p e) idx hne
      (fun i hi => (hothers i hi).1)
  have hotherFree :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        freeSI ((phiW ring p e) i).si = true :=
    wordPhasePoneOtherFree ring
      (phiW ring p e) p e hsource
      (fun i hi hj => cwPhiWFrame ring p e i hi hj)
      (fun i hi => (hothers i hi).2.2)
  have hcurAll :
      ∀ i : Fin n,
        (wordPhasePoneControl ring h p e
          (BlockA.wordRequestNext ring h p e) idx).workerCursor i =
          .empty := by
    unfold wordPhasePoneControl
    split <;> exact hp.2
  have hfold :=
    wordPhasePonePrefixFoldsCongr ring h.root
      (phiW ring p e) p hu (idx.val + 1)
  have hnewOr :
      (workerW (p e)
        (p (ring.rightNeighbor e))).y.z =
        cwPrefixOr ring h.root (phiW ring p e) (idx.val + 1) := by
    calc
      (workerW (p e) (p (ring.rightNeighbor e))).y.z =
          (z || (p (ring.rightNeighbor e)).u) := hyz
      _ = (cwPrefixOr ring h.root p idx.val ||
            cwBit ring h.root p (idx.val + 1)) := by
        rw [hor]
        simp only [cwBit, ← hgeom]
      _ = cwPrefixOr ring h.root p (idx.val + 1) :=
        (wordPhasePoneOrSucc ring h.root p idx.val).symm
      _ = cwPrefixOr ring h.root (phiW ring p e) (idx.val + 1) :=
        hfold.1.symm
  have hnewAnd :
      (workerW (p e)
        (p (ring.rightNeighbor e))).y.a =
        cwPrefixAnd ring h.root (phiW ring p e) (idx.val + 1) := by
    calc
      (workerW (p e) (p (ring.rightNeighbor e))).y.a =
          (a && (p (ring.rightNeighbor e)).u) := hya
      _ = (cwPrefixAnd ring h.root p idx.val &&
            cwBit ring h.root p (idx.val + 1)) := by
        rw [hand]
        simp only [cwBit, ← hgeom]
      _ = cwPrefixAnd ring h.root p (idx.val + 1) :=
        (wordPhasePoneAndSucc ring h.root p idx.val).symm
      _ = cwPrefixAnd ring h.root (phiW ring p e) (idx.val + 1) :=
        hfold.2.symm
  have hpostReads := wordPhasePoneLedgerAgreement
    ring h (phiW ring p e) p e
    (BlockA.wordRequestNext ring h p e)
    idx hcount hroom hreads hgeom hu
  have hpostPublished := wordPhasePonePublishedTransport
    ring h (phiW ring p e) p e
    (BlockA.wordRequestNext ring h p e) idx
    hpublished hgeom hbetaFrame hbetaResponder
  have hresp :
      (phiW ring p e) (ring.rightNeighbor e) =
        (pairW (p e) (p (ring.rightNeighbor e))).2 := by
    simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
  have hcurWorker :
      (workerW (p e) (p (ring.rightNeighbor e))).y.cur = .NONE := by
    rw [hresp] at hcur
    exact hcur
  refine ⟨⟨?_, ?_⟩, hcurAll⟩
  · refine ⟨ring.rightNeighbor e,
      (workerW (p e) (p (ring.rightNeighbor e))).y.j,
      (workerW (p e) (p (ring.rightNeighbor e))).y.z,
      (workerW (p e) (p (ring.rightNeighbor e))).y.a,
      ?_, hnewTag, hnewCount, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold wordPhasePoneControl
      split <;> exact hphase
    · unfold cwPhasePrefixPhysical
      rw [hresp]
      change
        (workerW (p e) (p (ring.rightNeighbor e))).y.kind = .PREFIX ∧
        (workerW (p e) (p (ring.rightNeighbor e))).y.cur = .NONE ∧
        (workerW (p e) (p (ring.rightNeighbor e))).y.j =
          (workerW (p e) (p (ring.rightNeighbor e))).y.j ∧
        (workerW (p e) (p (ring.rightNeighbor e))).y.z =
          (workerW (p e) (p (ring.rightNeighbor e))).y.z ∧
        (workerW (p e) (p (ring.rightNeighbor e))).y.a =
          (workerW (p e) (p (ring.rightNeighbor e))).y.a
      exact ⟨hykind, hcurWorker, rfl, rfl, rfl⟩
    · rw [hrootPost, hyj]
      exact hnewOr
    · rw [hrootPost, hyj]
      exact hnewAnd
    · intro q hq
      rw [hrootPost]
      rw [hyj] at hq
      exact hpostReads q hq
    · rw [hyj]
      exact hpostPublished
    · intro i hi
      exact ⟨hotherKinds i hi, hcurAll i, hotherFree i hi⟩
  · intro site nextIdx nextZ nextA htagNext
    by_cases hs : site = ring.rightNeighbor e
    · subst site
      rw [hnewTag] at htagNext
      cases htagNext
      rw [hrootPost, hyj]
      exact hgeom
    · have hempty := hotherKinds site hs
      rw [htagNext] at hempty
      cases hempty

end L3.WordPhase

/-!
P3 owner/control and a literal obstruction to an
UNQUALIFIED all-Compiled clean-BACK transport.

The legal parameter type Compiled does not require t >= 2 or
t < n. At n=5, t=1, zero OLD U and a terminal PREFIX at site 1,
P3 kicks the only sampled U to true but writes OLD a=false to
beta at the same site. NEW AND=true, beta=false, so
cwPhaseInitialPublished cannot hold after the successful P3.
The production t=2 branch is NOT refuted by this witness.
-/

namespace L3.WordPhase

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- Exact row inversion for the first-match P3 branch of siStep.
The first five earlier-row guards are checked separately. -/
private theorem siStepRowPThree {c : Compiled}
    (ox oy : Agent c) (post : PostE) (hard : HardFlags)
    (hrow : (siStep c ox oy post hard).row = "P3") :
    siStep c ox oy post hard =
      { x := offSI c.t
        y := launchRootBack c.t
        uX := if ox.si.z = false then true else ox.u
        uY := oy.u
        betaX := ox.si.a
        betaY := oy.beta
        done := false
        row := "P3" } := by
  by_cases haccept : hard.hardAccept = true
  · have hbad : (siStep c ox oy post hard).row = "I0" := by
      simp [siStep, haccept]
    rw [hbad] at hrow
    exact absurd hrow (by decide)
  · by_cases herase :
        hard.hardLeft = true ∨ hard.hardRight = true
    · have hbad : (siStep c ox oy post hard).row = "I1" := by
        simp [siStep, haccept, herase]
      rw [hbad] at hrow
      exact absurd hrow (by decide)
    · by_cases hexit :
          (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                post.eY.l = true) ∧ freeSI oy.si = true)
      · have hbad : (siStep c ox oy post hard).row = "P0" := by
          simp [siStep, haccept, herase, hexit]
        rw [hbad] at hrow
        exact absurd hrow (by decide)
      · by_cases hmove :
            (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                  ox.si.cur = .NONE) ∧ ox.si.j.val < c.t) ∧
                  post.eY.l = false) ∧ freeSI oy.si = true)
        · have hbad : (siStep c ox oy post hard).row = "P1" := by
            simp [siStep, haccept, herase, hexit, hmove]
          rw [hbad] at hrow
          exact absurd hrow (by decide)
        · by_cases hterminal :
              (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                    ox.si.cur = .NONE) ∧ ox.si.j.val = c.t) ∧
                    post.eY.l = true) ∧ freeSI oy.si = true)
          · have hbad : (siStep c ox oy post hard).row = "P2" := by
              simp [siStep, haccept, herase, hexit, hmove,
                hterminal]
            rw [hbad] at hrow
            exact absurd hrow (by decide)
          · by_cases hpublish :
                (((((ox.si.kind = .PREFIX ∧ ox.si.busy = false) ∧
                      ox.si.cur = .NONE) ∧ ox.si.j.val = c.t) ∧
                      post.eY.l = false) ∧ freeSI oy.si = true)
            · simp [siStep, haccept, herase, hexit,
                hmove, hterminal, hpublish]
            · have hnot :
                  (siStep c ox oy post hard).row ≠ "P3" := by
                simp [siStep, haccept, herase, hexit,
                  hmove, hterminal, hpublish, siStepRowIte]
                repeat' split
                all_goals decide
              exact False.elim (hnot hrow)

/-- P3 consumes its source SI, starts the responder's
ROOT/BACK cursor, and rewrites only source U/beta. -/
theorem wordPhasePthreeOwnerFields {c : Compiled}
    (x y : ProjW c)
    (hrow : (workerW x y).row = "P3") :
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = launchRootBack c.t ∧
    (workerW x y).uX =
      (if x.si.z = false then true else x.u) ∧
    (workerW x y).uY = y.u ∧
    (workerW x y).betaX = x.si.a ∧
    (workerW x y).betaY = y.beta := by
  unfold workerW at hrow ⊢
  have hresult := siStepRowPThree
    x.lift y.lift (postW x y) (serW x y).hard hrow
  rw [hresult]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- These are precisely the positive P3 control guards tested
by the installed wordWorkerNext, not a generated-history oracle. -/
def WordPhasePthreeGuard {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (idx : Fin (c.t + 1)) (z a : Bool) : Prop :=
  idx.val = c.t ∧
  (p e).si.kind = .PREFIX ∧
  (p e).si.cur = .NONE ∧
  (p e).si.busy = false ∧
  (p e).si.j = idx ∧
  (p e).si.z = z ∧
  (p e).si.a = a ∧
  h.prefixReads.count.val = c.t ∧
  h.workerKind (ring.rightNeighbor e) = .empty ∧
  h.workerCursor (ring.rightNeighbor e) = .empty ∧
  (workerW (p e) (p (ring.rightNeighbor e))).uX =
    (if z = false then true else (p e).u) ∧
  (workerW (p e) (p (ring.rightNeighbor e))).betaX = a ∧
  (workerW (p e) (p (ring.rightNeighbor e))).y.kind = .ROOT ∧
  (workerW (p e) (p (ring.rightNeighbor e))).y.busy = true ∧
  (workerW (p e) (p (ring.rightNeighbor e))).y.cur = .BACK ∧
  (workerW (p e) (p (ring.rightNeighbor e))).y.j.val = c.t

/-- Positive .prefixPublish branch: prefixEnd is at OLD source
e, and target/BACK is at NEW responder j. P3 does NOT
set prefixMarkers e; that field is not a P3 receipt. -/
def wordPhasePthreeControl {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) : BlockA.WordControl n c :=
  { h with
    requested := request
    workerKind :=
      BlockA.wordPut
        (BlockA.wordPut h.workerKind e .empty)
        (ring.rightNeighbor e)
        (.target (ring.rightNeighbor e) true)
    workerCursor :=
      BlockA.wordPut h.workerCursor
        (ring.rightNeighbor e)
        (.back (ring.rightNeighbor e)
          (workerW (p e) (p (ring.rightNeighbor e))).y.j)
    publications := BlockA.wordPut h.publications e .prefixEnd
    visibleReceipts := BlockA.wordPut h.visibleReceipts e true
    sumReads := BlockA.wordEmptyLedger }

/-- Unfold the actual successful P3 interpreter, with the
complete original positive guard. -/
theorem wordPhasePthreeControlFromGuard
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool)
    (idx : Fin (c.t + 1)) (z a : Bool)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixPublish)
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePthreeGuard ring h p e idx z a) :
    BlockA.wordWorkerNext ring h p e request =
      wordPhasePthreeControl ring h p e request := by
  rcases hguard with
    ⟨ht, hk, hc, hb, hj, hz, ha, hcount, hdest,
      hcursor, hu, hbeta, hyr, hybusy, hycur, hyj⟩
  simp [BlockA.wordWorkerNext, wordPhasePthreeControl,
    hcase, hkind, ht, hk, hc, hb, hj, hz, ha, hcount,
    hdest, hcursor, hu, hbeta, hyr, hybusy, hycur, hyj]

/-- Link the positive P3 row to the real monitored
wordT successor, not an independently constructed transition. -/
theorem wordPhasePthreeActualControl
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (idx : Fin (c.t + 1)) (z a : Bool)
    (hp : WordPhasePrefixAtClean ring h p)
    (hno : ¬ BlockA.wordIsHardStart ring h p e)
    (hcase : BlockA.workerCase (p e)
      (p (ring.rightNeighbor e)) = .prefixPublish)
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePthreeGuard ring h p e idx z a) :
    BlockA.wordT ring h p e (phiW ring p e) =
      wordPhasePthreeControl ring h p e
        (BlockA.wordRequestNext ring h p e) := by
  exact (wordEpochWorkerDispatch ring h p e
    (wordPhasePrefixWorker ring h p hp.1.1) hno).trans
    (wordPhasePthreeControlFromGuard ring h p e
      (BlockA.wordRequestNext ring h p e)
      idx z a hcase hkind hguard)

/-- Successful P3 writes the exact target, BACK cursor,
prefixEnd receipt, and the zero-count sum ledger. -/
theorem wordPhasePthreeControlReceipts
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) :
    (wordPhasePthreeControl ring h p e request).publications e =
      .prefixEnd ∧
    (wordPhasePthreeControl ring h p e request).visibleReceipts e =
      true ∧
    (wordPhasePthreeControl ring h p e request).workerKind
      (ring.rightNeighbor e) =
        .target (ring.rightNeighbor e) true ∧
    (wordPhasePthreeControl ring h p e request).workerCursor
      (ring.rightNeighbor e) =
        .back (ring.rightNeighbor e)
          (workerW (p e) (p (ring.rightNeighbor e))).y.j ∧
    (wordPhasePthreeControl ring h p e request).sumReads.count.val =
      0 := by
  simp [wordPhasePthreeControl, BlockA.wordPut,
    BlockA.wordEmptyLedger]

/-- BACK plus one uniquely colored target. This does not
weaken cwPhaseBack's physical first-window marker equation. -/
def WordPhaseBackAtClean {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  cwPhaseBack ring h p ∧
    ∃ target : Fin n,
      h.workerKind target = .target target true ∧
      (∀ i : Fin n, i ≠ target →
        h.workerKind i = .empty ∧ h.workerCursor i = .empty)

/-!
N = 5, T = 1 CUT (legal, but outside production advice).
Root = 0. U = beta = 00000. Terminal PREFIX at site 1:
idx = count = 1, z = false, a = false, cursor = empty;
its one OLD read is (source 1, oldBit false).
All other worker colors/cursors are empty, physical SI is OFF.
No prefixZero receipt is required because 0 < k < t=1
has no solution. The physical edge is 1 -> 2.
-/

def wordPhasePthreeThinCfg : Compiled :=
  { q := 2, t := 1, s := 2, kappa := 0,
    taps := fun _ => false }

def wordPhasePthreeThinRing : DirectedRing 5 :=
  ⟨by decide⟩

def wordPhasePthreeThinProjection
    (i : Fin 5) : ProjW wordPhasePthreeThinCfg :=
  { native := { l := i == (0 : Fin 5), b := 0,
                sh := false, sg := false }
    ser := { phase := .C, out := .NEW, probe := .NONE,
             cert := .IDLE, wphase := .OFF }
    siLease := 0
    si :=
      if i = (1 : Fin 5) then
        { kind := .PREFIX, busy := false, cur := .NONE,
          j := (1 : Fin (wordPhasePthreeThinCfg.t + 1)),
          z := false, p := false, a := false }
      else offSI wordPhasePthreeThinCfg.t
    u := false
    beta := false }

def wordPhasePthreeThinControl :
    BlockA.WordControl 5 wordPhasePthreeThinCfg :=
  { root := 0
    phase := .worker
    requested := false
    serializer := fun _ => BlockA.wordColor .empty none
    workerKind := fun i =>
      if i = (1 : Fin 5) then
        .prefix (1 : Fin (wordPhasePthreeThinCfg.t + 1))
          false false
      else .empty
    workerCursor := fun _ => .empty
    prefixReads :=
      { count := (1 : Fin (wordPhasePthreeThinCfg.t + 1))
        entries := fun _ =>
          some { source := (1 : Fin 5), oldBit := false } }
    sumReads := BlockA.wordEmptyLedger
    publications := fun _ => .absent
    visibleReceipts := fun _ => false
    prefixMarkers := fun _ => false }

/-- The explicit terminal PREFIX cut is clean at all sites. -/
theorem wordPhasePthreeThinCleanCut :
    WordPhasePrefixAtClean wordPhasePthreeThinRing
      wordPhasePthreeThinControl
      wordPhasePthreeThinProjection := by
  constructor
  · constructor
    · refine ⟨(1 : Fin 5),
        (1 : Fin (wordPhasePthreeThinCfg.t + 1)),
        false, false, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · unfold cwPhasePrefixPhysical
        decide
      · unfold cwPrefixOr cwBit
        decide
      · unfold cwPrefixAnd cwBit
        decide
      · intro j hj
        have hjzero : j = (⟨0, by decide⟩ : Fin wordPhasePthreeThinCfg.t) := by
          apply Fin.ext
          have ht : wordPhasePthreeThinCfg.t = 1 := rfl
          have hj' := j.isLt
          show j.val = 0
          omega
        subst j
        decide
      · intro k hk _hle hlt
        change k.val < 1 at hlt
        omega
      · intro i hi
        refine ⟨?_, ?_, ?_⟩
        · simp [wordPhasePthreeThinControl, hi]
        · rfl
        · simp [wordPhasePthreeThinProjection, hi, freeSI, offSI]
    · intro site index z a htag
      by_cases hs : site = (1 : Fin 5)
      · subst site
        have hshape :
            BlockA.WorkerTag.prefix (n := 5)
              (1 : Fin (wordPhasePthreeThinCfg.t + 1))
              false false = .prefix index z a := by
          simpa [wordPhasePthreeThinControl] using htag
        cases hshape
        decide
      · have hempty :
            wordPhasePthreeThinControl.workerKind site = .empty := by
          simp [wordPhasePthreeThinControl, hs]
        rw [hempty] at htag
        cases htag
  · intro i
    rfl

theorem wordPhasePthreeThinSelected :
    (workerW
      (wordPhasePthreeThinProjection (1 : Fin 5))
      (wordPhasePthreeThinProjection (2 : Fin 5))).row =
        "P3" := by
  unfold wordPhasePthreeThinProjection wordPhasePthreeThinCfg
  decide

def wordPhasePthreeThinNextProjection :
    Fin 5 → ProjW wordPhasePthreeThinCfg :=
  phiW wordPhasePthreeThinRing wordPhasePthreeThinProjection
    (1 : Fin 5)

def wordPhasePthreeThinNextControl :
    BlockA.WordControl 5 wordPhasePthreeThinCfg :=
  BlockA.wordT wordPhasePthreeThinRing
    wordPhasePthreeThinControl wordPhasePthreeThinProjection
    (1 : Fin 5) wordPhasePthreeThinNextProjection

/-- The same actual edge executes the successful P3 monitor
branch: target/BACK at 2, prefixEnd at source 1. -/
theorem wordPhasePthreeThinSuccessfulControl :
    wordPhasePthreeThinNextControl.workerKind (2 : Fin 5) =
      .target (2 : Fin 5) true ∧
    wordPhasePthreeThinNextControl.workerCursor (2 : Fin 5) =
      .back (2 : Fin 5)
        (1 : Fin (wordPhasePthreeThinCfg.t + 1)) ∧
    wordPhasePthreeThinNextControl.publications (1 : Fin 5) =
      .prefixEnd := by
  unfold wordPhasePthreeThinNextControl
    wordPhasePthreeThinNextProjection
    wordPhasePthreeThinControl
    wordPhasePthreeThinProjection wordPhasePthreeThinCfg
  decide

/-- After P3 the only sampled U is true, but its beta is
the false OLD AND. The demanded NEW marker equality fails. -/
theorem wordPhasePthreeThinMarkerMismatch :
    cwMarker wordPhasePthreeThinRing (0 : Fin 5)
      wordPhasePthreeThinNextProjection 1 = false ∧
    cwPrefixAnd wordPhasePthreeThinRing (0 : Fin 5)
      wordPhasePthreeThinNextProjection
        wordPhasePthreeThinCfg.t = true := by
  unfold wordPhasePthreeThinNextProjection
    wordPhasePthreeThinProjection wordPhasePthreeThinCfg
    cwMarker cwPrefixAnd cwBit
  decide

theorem wordPhasePthreeThinNextRoot :
    wordPhasePthreeThinNextControl.root = (0 : Fin 5) := by
  unfold wordPhasePthreeThinNextControl
    wordPhasePthreeThinNextProjection
    wordPhasePthreeThinControl
    wordPhasePthreeThinProjection wordPhasePthreeThinCfg
  decide

/-- No successful-P3 clean-BACK theorem can hold for *every*
Compiled parameter and clean terminal PREFIX without a width
condition. Failing field: beta[t] = NEW AND[t]. -/
theorem wordPhasePthreeThinNotBack :
    ¬ WordPhaseBackAtClean wordPhasePthreeThinRing
      wordPhasePthreeThinNextControl
      wordPhasePthreeThinNextProjection := by
  intro hback
  rcases hback.1 with
    ⟨site, target, idx, hphase, htag, hcursor,
      hphysicalCur, hphysicalIdx, htargetKind,
      htargetBusy, hsum, hinitial, hearlier⟩
  have hmark := hinitial.2.2.2.2
  rw [wordPhasePthreeThinNextRoot] at hmark
  change
    cwMarker wordPhasePthreeThinRing (0 : Fin 5)
      wordPhasePthreeThinNextProjection 1 =
    cwPrefixAnd wordPhasePthreeThinRing (0 : Fin 5)
      wordPhasePthreeThinNextProjection 1 at hmark
  rw [wordPhasePthreeThinMarkerMismatch.1] at hmark
  exact Bool.noConfusion
    (hmark.trans wordPhasePthreeThinMarkerMismatch.2)

end L3.WordPhase

namespace L3.WordPhase

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- Offsets below the circumference decode without wrapping. -/
theorem wordPhasePthreeShiftOffset {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (d : Nat) (hd : d < n) :
    PPL.cyclicOffset ring root (PPL.shiftRight ring root d) = d := by
  unfold PPL.cyclicOffset PPL.shiftRight
  change (((root.val + d) % n + n - root.val) % n) = d
  by_cases hs : root.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq : root.val + d + n - root.val = n + d := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hd]
  · have hge : n ≤ root.val + d := by omega
    have hlt : root.val + d - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have heq : root.val + d - n + n - root.val = d := by omega
    rw [heq, Nat.mod_eq_of_lt hd]

/-- The terminal P3 source is not any earlier first-window site. -/
theorem wordPhasePthreeDistinctBefore {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (t k : Nat) (ht : t < n) (hk : k < t) :
    PPL.shiftRight ring root k ≠ PPL.shiftRight ring root t := by
  intro heq
  have hoff := congrArg
    (fun i : Fin n => PPL.cyclicOffset ring root i) heq
  rw [wordPhasePthreeShiftOffset ring root k (by omega),
    wordPhasePthreeShiftOffset ring root t ht] at hoff
  omega

/-- The actual P3 physical owner: the source is cleared and
the responder receives ROOT/BACK.  Only the source U/beta can
change. -/
theorem wordPhasePthreePhysicalFields {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3") :
    ((phiW ring p e) e).si = offSI c.t ∧
    ((phiW ring p e) (ring.rightNeighbor e)).si =
      launchRootBack c.t ∧
    ((phiW ring p e) e).u =
      (if (p e).si.z = false then true else (p e).u) ∧
    ((phiW ring p e) e).beta = (p e).si.a ∧
    (∀ i : Fin n, i ≠ e →
      ((phiW ring p e) i).u = (p i).u ∧
      ((phiW ring p e) i).beta = (p i).beta) := by
  rcases wordPhasePthreeOwnerFields
    (p e) (p (ring.rightNeighbor e)) hrow with
    ⟨hs, hr, huX, huY, hbX, hbY⟩
  have hleft :
      (phiW ring p e) e =
        (pairW (p e) (p (ring.rightNeighbor e))).1 := by
    simp only [phiW, projectedEdge, if_pos rfl]
  have hright :
      (phiW ring p e) (ring.rightNeighbor e) =
        (pairW (p e) (p (ring.rightNeighbor e))).2 := by
    simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hleft]
    change (workerW (p e) (p (ring.rightNeighbor e))).x =
      offSI c.t
    exact hs
  · rw [hright]
    change (workerW (p e) (p (ring.rightNeighbor e))).y =
      launchRootBack c.t
    exact hr
  · rw [hleft]
    change (workerW (p e) (p (ring.rightNeighbor e))).uX =
      (if (p e).si.z = false then true else (p e).u)
    exact huX
  · rw [hleft]
    change (workerW (p e) (p (ring.rightNeighbor e))).betaX =
      (p e).si.a
    exact hbX
  · intro i hi
    by_cases hj : i = ring.rightNeighbor e
    · subst i
      rw [hright]
      change
        (workerW (p e) (p (ring.rightNeighbor e))).uY =
          (p (ring.rightNeighbor e)).u ∧
        (workerW (p e) (p (ring.rightNeighbor e))).betaY =
          (p (ring.rightNeighbor e)).beta
      exact ⟨huY, hbY⟩
    · rw [cwPhiWFrame ring p e i hi hj]
      exact ⟨rfl, rfl⟩

/-- A zero OR on a nonempty Boolean prefix forces a zero AND.
This is independent of ring aliasing; it uses the exact snoc folds. -/
theorem wordPhasePthreeOrFalseAndFalse {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (len : Nat) :
    0 < len →
    cwPrefixOr ring root p len = false →
    cwPrefixAnd ring root p len = false := by
  induction len with
  | zero =>
      intro hpos _
      omega
  | succ k ih =>
      intro _ hzero
      cases k with
      | zero =>
          have hb : cwBit ring root p 1 = false := by
            rw [wordPhasePoneOrSucc] at hzero
            simpa [cwPrefixOr] using hzero
          rw [wordPhasePoneAndSucc]
          simp [cwPrefixAnd, hb]
      | succ k =>
          have hprev :
              cwPrefixOr ring root p (k + 1) = false := by
            rw [wordPhasePoneOrSucc] at hzero
            cases hcase : cwPrefixOr ring root p (k + 1) with
            | false => rfl
            | true => simp [hcase] at hzero
          have ha := ih (by omega) hprev
          rw [wordPhasePoneAndSucc, ha]
          rfl

/-- Folds on all followers strictly before the P3 source are
unchanged whenever their individual U bits are unchanged. -/
theorem wordPhasePthreePrefixBefore {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c) (t : Nat)
    (hbits : ∀ k : Nat, 0 < k → k < t →
      cwBit ring root p' k = cwBit ring root p k)
    (len : Nat) :
    len < t →
    cwPrefixOr ring root p' len = cwPrefixOr ring root p len ∧
    cwPrefixAnd ring root p' len = cwPrefixAnd ring root p len := by
  induction len with
  | zero =>
      intro _
      exact ⟨rfl, rfl⟩
  | succ k ih =>
      intro hlt
      have hprev := ih (by omega)
      have hbit := hbits (k + 1) (by omega) hlt
      constructor
      · calc
          cwPrefixOr ring root p' (k + 1) =
              (cwPrefixOr ring root p' k ||
                cwBit ring root p' (k + 1)) :=
            wordPhasePoneOrSucc ring root p' k
          _ = (cwPrefixOr ring root p k ||
                cwBit ring root p (k + 1)) := by
            rw [hprev.1, hbit]
          _ = cwPrefixOr ring root p (k + 1) :=
            (wordPhasePoneOrSucc ring root p k).symm
      · calc
          cwPrefixAnd ring root p' (k + 1) =
              (cwPrefixAnd ring root p' k &&
                cwBit ring root p' (k + 1)) :=
            wordPhasePoneAndSucc ring root p' k
          _ = (cwPrefixAnd ring root p k &&
                cwBit ring root p (k + 1)) := by
            rw [hprev.2, hbit]
          _ = cwPrefixAnd ring root p (k + 1) :=
            (wordPhasePoneAndSucc ring root p k).symm

/-- Boolean core of P3: the old OR decides whether to kick the
terminal bit; if zero OR implies zero AND on the *earlier* window,
the new OR is true and the new AND is still the old AND. -/
theorem wordPhasePthreeBoolKicked
    (frontOr frontAnd bit : Bool)
    (hzero : frontOr = false → frontAnd = false) :
    (frontOr || (if (frontOr || bit) = false then true else bit)) =
        true ∧
    (frontAnd && bit) =
      (frontAnd &&
        (if (frontOr || bit) = false then true else bit)) := by
  cases frontOr <;> cases frontAnd <;> cases bit <;>
    simp at hzero ⊢

/-- P3 does not destroy a prefixZero publication at a smaller
offset, including its physical beta=0 marker. -/
theorem wordPhasePthreePriorReceipts {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p' p : Fin n → ProjW c) (e : Fin n)
    (request : Bool)
    (hn : c.t < n)
    (hsite : e = PPL.shiftRight ring h.root c.t)
    (hpub : cwPhasePublishedPrefix ring h p c.t)
    (hremote : ∀ i : Fin n, i ≠ e →
      (p' i).beta = (p i).beta) :
    cwPhasePublishedPrefix ring
      (wordPhasePthreeControl ring h p e request) p' c.t := by
  intro k hk hle hlt
  have hne :
      PPL.shiftRight ring h.root k.val ≠ e := by
    rw [hsite]
    exact wordPhasePthreeDistinctBefore
      ring h.root c.t k.val hn hlt
  rcases hpub k hk hle hlt with ⟨hpubOld, hvisOld, hmarkerOld, hbetaOld⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [wordPhasePthreeControl, BlockA.wordPut, hne]
      using hpubOld
  · simpa [wordPhasePthreeControl, BlockA.wordPut, hne]
      using hvisOld
  · exact hmarkerOld
  · change (p' (PPL.shiftRight ring h.root k.val)).beta = false
    change (p (PPL.shiftRight ring h.root k.val)).beta =
      false at hbetaOld
    exact (hremote _ hne).trans hbetaOld

/-- All non-target worker colors are erased by the positive P3
publication, provided the source was the unique old colored site. -/
theorem wordPhasePthreeOtherKinds {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool)
    (hne : ring.rightNeighbor e ≠ e)
    (hothers : ∀ i : Fin n, i ≠ e → h.workerKind i = .empty) :
    ∀ i : Fin n, i ≠ ring.rightNeighbor e →
      (wordPhasePthreeControl ring h p e request).workerKind i =
        .empty := by
  intro i hi
  by_cases he : i = e
  · subst i
    simp [wordPhasePthreeControl, BlockA.wordPut, hne, Ne.symm hne]
  · have hold := hothers i he
    simp [wordPhasePthreeControl, BlockA.wordPut, hi, he, hold]

/-- P3 changes only the new target cursor. -/
theorem wordPhasePthreeOtherCursors {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool)
    (hempty : ∀ i : Fin n, h.workerCursor i = .empty) :
    ∀ i : Fin n, i ≠ ring.rightNeighbor e →
      (wordPhasePthreeControl ring h p e request).workerCursor i =
        .empty := by
  intro i hi
  simpa [wordPhasePthreeControl, BlockA.wordPut, hi] using
    hempty i

/-- The positive P3 control preserves the old root. -/
theorem wordPhasePthreeControlRoot {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (request : Bool) :
    (wordPhasePthreeControl ring h p e request).root = h.root := rfl

/-- The positive P3 control has the complete clean-BACK postcondition
when the first window contains at least two distinct sampled sites. -/
theorem wordPhasePthreeControlCleanSuccess {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (idx : Fin (c.t + 1)) (z a : Bool) (request : Bool)
    (hp : WordPhasePrefixAtClean ring h p)
    (h2 : 2 ≤ c.t) (hn : c.t < n)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3")
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePthreeGuard ring h p e idx z a) :
    WordPhaseBackAtClean ring
      (wordPhasePthreeControl ring h p e request)
      (phiW ring p e) := by
  have hguardFacts := hguard
  rcases hguardFacts with
    ⟨ht, _hk, _hc, _hb, _hj, hz, ha, _hcount,
      hdest, _hcursor, _hu, _hbeta,
      hyr, hybusy, hycur, _hyj⟩
  have hsite : e = PPL.shiftRight ring h.root c.t := by
    have hs := hp.1.2 e idx z a hkind
    rw [ht] at hs
    exact hs
  have htargetSite :
      ring.rightNeighbor e =
        PPL.shiftRight ring h.root (c.t + 1) :=
    wordPhasePthreeNextTarget ring h p hp.1
      e idx z a hkind ht
  have hne : ring.rightNeighbor e ≠ e := by
    intro heq
    rw [heq, hkind] at hdest
    cases hdest
  rcases wordPhasePthreePhysicalFields ring p e hne hrow with
    ⟨_hsource, _hback, huSource, hbetaSource, hremote⟩
  have hbefore : ∀ k : Nat, 0 < k → k < c.t →
      cwBit ring h.root (phiW ring p e) k =
        cwBit ring h.root p k := by
    intro k _ hk
    have hdistinct :
        PPL.shiftRight ring h.root k ≠ e := by
      rw [hsite]
      exact wordPhasePthreeDistinctBefore
        ring h.root c.t k hn hk
    change ((phiW ring p e)
      (PPL.shiftRight ring h.root k)).u =
      (p (PPL.shiftRight ring h.root k)).u
    exact (hremote _ hdistinct).1
  have hfolds := wordPhasePthreePrefixBefore ring h.root
    (phiW ring p e) p c.t hbefore (c.t - 1) (by omega)
  have hpostBit :
      cwBit ring h.root (phiW ring p e) c.t =
        (if z = false then true else cwBit ring h.root p c.t) := by
    change ((phiW ring p e)
        (PPL.shiftRight ring h.root c.t)).u =
      (if z = false then true else
        (p (PPL.shiftRight ring h.root c.t)).u)
    rw [← hsite, huSource, hz]
  rcases hp.1.1 with
    ⟨site, oldIdx, oldZ, oldA, hphase, htag, _oldCount,
      _oldPhysical, hor, hand, _oldReads, hpublished, hothers⟩
  have hsame : site = e := by
    by_cases hs : e = site
    · exact hs.symm
    · have hempty := (hothers e hs).1
      rw [hkind] at hempty
      cases hempty
  subst site
  have htagEq :
      BlockA.WorkerTag.prefix oldIdx oldZ oldA =
        .prefix idx z a := htag.symm.trans hkind
  cases htagEq
  have hOldOr : z = cwPrefixOr ring h.root p c.t := by
    calc
      z = cwPrefixOr ring h.root p idx.val := hor
      _ = cwPrefixOr ring h.root p c.t := by rw [ht]
  have hOldAnd : a = cwPrefixAnd ring h.root p c.t := by
    calc
      a = cwPrefixAnd ring h.root p idx.val := hand
      _ = cwPrefixAnd ring h.root p c.t := by rw [ht]
  have hpred : c.t - 1 + 1 = c.t := by omega
  have hOldOrEq :
      z = (cwPrefixOr ring h.root p (c.t - 1) ||
        cwBit ring h.root p c.t) := by
    calc
      z = cwPrefixOr ring h.root p c.t := hOldOr
      _ = _ := by
        simpa only [hpred] using
          wordPhasePoneOrSucc ring h.root p (c.t - 1)
  have hOldAndEq :
      a = (cwPrefixAnd ring h.root p (c.t - 1) &&
        cwBit ring h.root p c.t) := by
    calc
      a = cwPrefixAnd ring h.root p c.t := hOldAnd
      _ = _ := by
        simpa only [hpred] using
          wordPhasePoneAndSucc ring h.root p (c.t - 1)
  have hpostOrEq :
      cwPrefixOr ring h.root (phiW ring p e) c.t =
        (cwPrefixOr ring h.root p (c.t - 1) ||
          (if z = false then true else cwBit ring h.root p c.t)) := by
    calc
      cwPrefixOr ring h.root (phiW ring p e) c.t =
          (cwPrefixOr ring h.root (phiW ring p e) (c.t - 1) ||
            cwBit ring h.root (phiW ring p e) c.t) := by
        simpa only [hpred] using
          wordPhasePoneOrSucc ring h.root (phiW ring p e) (c.t - 1)
      _ = _ := by rw [hfolds.1, hpostBit]
  have hpostAndEq :
      cwPrefixAnd ring h.root (phiW ring p e) c.t =
        (cwPrefixAnd ring h.root p (c.t - 1) &&
          (if z = false then true else cwBit ring h.root p c.t)) := by
    calc
      cwPrefixAnd ring h.root (phiW ring p e) c.t =
          (cwPrefixAnd ring h.root (phiW ring p e) (c.t - 1) &&
            cwBit ring h.root (phiW ring p e) c.t) := by
        simpa only [hpred] using
          wordPhasePoneAndSucc ring h.root (phiW ring p e) (c.t - 1)
      _ = _ := by rw [hfolds.2, hpostBit]
  have hbool := wordPhasePthreeBoolKicked
    (cwPrefixOr ring h.root p (c.t - 1))
    (cwPrefixAnd ring h.root p (c.t - 1))
    (cwBit ring h.root p c.t)
    (wordPhasePthreeOrFalseAndFalse
      ring h.root p (c.t - 1) (by omega))
  have hnewOr :
      cwPrefixOr ring h.root (phiW ring p e) c.t = true := by
    rw [hpostOrEq, hOldOrEq]
    exact hbool.1
  have hnewAnd :
      a = cwPrefixAnd ring h.root (phiW ring p e) c.t := by
    calc
      a = (cwPrefixAnd ring h.root p (c.t - 1) &&
        cwBit ring h.root p c.t) := hOldAndEq
      _ = (cwPrefixAnd ring h.root p (c.t - 1) &&
        (if (cwPrefixOr ring h.root p (c.t - 1) ||
          cwBit ring h.root p c.t) = false then true
          else cwBit ring h.root p c.t)) := hbool.2
      _ = cwPrefixAnd ring h.root (phiW ring p e) c.t := by
        rw [hpostAndEq, hOldOrEq]
  have hnewMarker :
      cwMarker ring h.root (phiW ring p e) c.t =
        cwPrefixAnd ring h.root (phiW ring p e) c.t := by
    calc
      cwMarker ring h.root (phiW ring p e) c.t = a := by
        change ((phiW ring p e)
          (PPL.shiftRight ring h.root c.t)).beta = a
        rw [← hsite, hbetaSource, ha]
      _ = cwPrefixAnd ring h.root (phiW ring p e) c.t := hnewAnd
  have hpublishedT : cwPhasePublishedPrefix ring h p c.t := by
    simpa only [ht] using hpublished
  have hpostPublished := wordPhasePthreePriorReceipts
    ring h (phiW ring p e) p e request hn hsite hpublishedT
    (fun i hi => (hremote i hi).2)
  have hreceipts := wordPhasePthreeControlReceipts
    ring h p e request
  have hpostInitial :
      cwPhaseInitialPublished ring
        (wordPhasePthreeControl ring h p e request)
        (phiW ring p e) := by
    refine ⟨hpostPublished, ?_, ?_, ?_, ?_⟩
    · change (wordPhasePthreeControl ring h p e request).publications
        (PPL.shiftRight ring h.root c.t) = .prefixEnd
      rw [← hsite]
      exact hreceipts.1
    · change (wordPhasePthreeControl ring h p e request).visibleReceipts
        (PPL.shiftRight ring h.root c.t) = true
      rw [← hsite]
      exact hreceipts.2.1
    · change cwPrefixOr ring h.root (phiW ring p e) c.t = true
      exact hnewOr
    · change cwMarker ring h.root (phiW ring p e) c.t =
        cwPrefixAnd ring h.root (phiW ring p e) c.t
      exact hnewMarker
  have hpostEarlier :
      cwPhaseEarlierPublished ring
        (wordPhasePthreeControl ring h p e request)
        (phiW ring p e)
        (PPL.cyclicOffset ring
          (wordPhasePthreeControl ring h p e request).root
          (ring.rightNeighbor e)) := by
    intro k hk hlt
    change k.val <
      PPL.cyclicOffset ring h.root (ring.rightNeighbor e) at hlt
    rw [htargetSite] at hlt
    by_cases hfit : c.t + 1 < n
    · rw [wordPhasePthreeShiftOffset
        ring h.root (c.t + 1) hfit] at hlt
      omega
    · have hkl := k.isLt
      omega
  have hotherKinds :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        (wordPhasePthreeControl ring h p e request).workerKind i =
          .empty :=
    wordPhasePthreeOtherKinds ring h p e request hne
      (fun i hi => (hothers i hi).1)
  have hotherCursors :
      ∀ i : Fin n, i ≠ ring.rightNeighbor e →
        (wordPhasePthreeControl ring h p e request).workerCursor i =
          .empty :=
    wordPhasePthreeOtherCursors ring h p e request hp.2
  have hresp :
      (phiW ring p e) (ring.rightNeighbor e) =
        (pairW (p e) (p (ring.rightNeighbor e))).2 := by
    simp only [phiW, projectedEdge, if_neg hne, ↓reduceIte]
  refine ⟨⟨ring.rightNeighbor e, ring.rightNeighbor e,
    (workerW (p e) (p (ring.rightNeighbor e))).y.j,
    ?_, hreceipts.2.2.1, hreceipts.2.2.2.1,
    ?_, ?_, ?_, ?_, hreceipts.2.2.2.2,
    hpostInitial, hpostEarlier⟩,
    ⟨ring.rightNeighbor e, hreceipts.2.2.1, ?_⟩⟩
  · change h.phase = .worker
    exact hphase
  · rw [hresp]
    change (workerW (p e)
      (p (ring.rightNeighbor e))).y.cur = .BACK
    exact hycur
  · rw [hresp]
    rfl
  · rw [hresp]
    change (workerW (p e)
      (p (ring.rightNeighbor e))).y.kind = .ROOT
    exact hyr
  · rw [hresp]
    change (workerW (p e)
      (p (ring.rightNeighbor e))).y.busy = true
    exact hybusy
  · intro i hi
    exact ⟨hotherKinds i hi, hotherCursors i hi⟩

/-- Complete P3-to-clean-BACK transport for the actual monitored
wordT edge, under the necessary width and nonaliasing conditions. -/
theorem wordPhasePthreeCleanSuccess {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) (e : Fin n)
    (idx : Fin (c.t + 1)) (z a : Bool)
    (hp : WordPhasePrefixAtClean ring h p)
    (h2 : 2 ≤ c.t) (hn : c.t < n)
    (hrow : (workerW (p e)
      (p (ring.rightNeighbor e))).row = "P3")
    (hkind : h.workerKind e = .prefix idx z a)
    (hguard : WordPhasePthreeGuard ring h p e idx z a) :
    WordPhaseBackAtClean ring
      (BlockA.wordT ring h p e (phiW ring p e))
      (phiW ring p e) := by
  have hcase : BlockA.workerCase
      (p e) (p (ring.rightNeighbor e)) = .prefixPublish :=
    cwPhasePrefixPublishRow (p e)
      (p (ring.rightNeighbor e)) hrow
  have hno : ¬ BlockA.wordIsHardStart ring h p e := by
    intro hs
    dsimp only [BlockA.wordIsHardStart] at hs
    rcases hs with ⟨_, _, _, _, _, herase⟩
    rw [hcase] at herase
    cases herase
  have hcontrol := wordPhasePthreeActualControl ring h p e
    idx z a hp hno hcase hkind hguard
  rw [hcontrol]
  exact wordPhasePthreeControlCleanSuccess ring h p e
    idx z a (BlockA.wordRequestNext ring h p e)
    hp h2 hn hrow hkind hguard

end L3.WordPhase

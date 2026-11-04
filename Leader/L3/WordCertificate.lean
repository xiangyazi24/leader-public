import Leader.L3.ClosureFull

/-!
Post-A0 worker-row certificate, at the exact projected W owner.

The finite DONE receipts do not
automatically imply the infinite QWord safety property.

The proposed invariant is local to a current finite W projection
and a fixed DONE monitor.  CleanWorkerInv (from Target.lean) already
spells out root/width, OLD prefix/sum receipts and accumulators,
physical PREFIX/BACK/SUM/ROOT geometry, static word equations,
orphan guards, and all five publishing/nonpublishing case checks.

The decisive missing statement is preservation under EVERY future
physical phiW edge.  wordT_done freezes the monitor; it does not
freeze the physical serializer or SI workers.
-/

namespace L3
namespace WordCertificate

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false
set_option Elab.async false

/-- Finite current-state candidate for the post-A0 invariant.
No Reachable, QWord, SafeAll or future execution occurs here.
The physical OLD worker/serializer rows and the hard-scrub
cases are checked by the CleanWorkerInv fields. -/
def DoneWorkerRows {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c) : Prop :=
  h.phase = .done ∧
  BlockA.wordValidated ring h ∧
  BlockA.wordAllPublished ring h ∧
  CleanWorkerInv ring h p

/-- The physical OLD row leaves all four selected visible fields
unchanged, not just their monitor publication flags. -/
theorem doneWorkerRows_selectedQuiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hc : DoneWorkerRows ring h p) :
    WordRowsQuiet ring p := by
  exact cleanWorkerInv_wordRowsQuiet ring h p hc.2.2.2

/-- The first future physical edge is word-visible silent. -/
theorem doneWorkerRows_firstEdge {n : Nat} {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hc : DoneWorkerRows ring h p) :
    ∀ e i : Fin n,
      wordVisible (phiW ring p e) i = wordVisible p i := by
  exact wordRowsQuiet_first_step ring p
    (fun e => EWord.rightNeighborDifferent ring hn e)
    (doneWorkerRows_selectedQuiet ring h p hc)

/-- Nonzero/recurrence/trailing-marker equations persist across
the first quiet edge.  Worker provenance is not claimed stable. -/
theorem doneWorkerRows_staticStep {n : Nat} {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (e : Fin n)
    (hc : DoneWorkerRows ring h p) :
    CleanWorkerWordValues ring h.root (phiW ring p e) := by
  exact cleanWorkerInv_wordValues_step ring h p e
    (fun f => EWord.rightNeighborDifferent ring hn f)
    hc.2.2.2

/-- Only the control record is frozen, not the physical SI rows. -/
theorem doneWorkerRows_controlFrozen {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (e : Fin n)
    (hc : DoneWorkerRows ring h p) :
    BlockA.wordT ring h p e (phiW ring p e) = h := by
  exact BlockA.wordT_done ring h p e (phiW ring p e) hc.1

/-- Extract the entire DONE field-level invariant from a
phase-local certificate, IF the latter has been transported
through the actual physical worker epoch. -/
theorem workerPhaseDoneExtract {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hdone : h.phase = .done)
    (hphase : CleanWorkerPhaseInv ring h p) :
    CleanWorkerInv ring h p := by
  cases hphase with
  | «prefix» hp =>
      rcases hp with ⟨_, _, _, _, hw, _⟩
      cases hw.symm.trans hdone
  | back hb =>
      rcases hb with ⟨_, _, _, hw, _⟩
      cases hw.symm.trans hdone
  | sum hs =>
      rcases hs with ⟨_, _, _, _, _, _, hw, _⟩
      cases hw.symm.trans hdone
  | ready hr =>
      rcases hr with ⟨_, hw, _⟩
      cases hw.symm.trans hdone
  | done _ full =>
      exact full

/-- Exact first-A0 membership reduction; no completed
worker epoch is manufactured from bare receipt flags. -/
theorem doneWorkerRows_ofPhaseCertificate {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hdone : h.phase = .done)
    (hvalidated : BlockA.wordValidated ring h)
    (hpublished : BlockA.wordAllPublished ring h)
    (hphase : CleanWorkerPhaseInv ring h p) :
    DoneWorkerRows ring h p := by
  exact ⟨hdone, hvalidated, hpublished,
    workerPhaseDoneExtract ring h p hdone hphase⟩

/-- The first unresolved native-row proof is stated here as
an EXPLICIT PREMISE, not as a theorem: arbitrary physical
SI/serializer services must preserve the SAME frozen monitor's
CleanWorkerInv, including all future publishing row checks.
The other half of FutureWorkerCertificate is proved below. -/
theorem futureWorkerCertificate_ofRowTransport {n : Nat}
    {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (htransport : ∀ p : Fin n → ProjW c,
      DoneWorkerRows ring h p →
      ∀ e : Fin n,
        CleanWorkerInv ring h (phiW ring p e)) :
    FutureWorkerCertificate ring (DoneWorkerRows ring h) := by
  intro p hp e
  refine ⟨doneWorkerRows_firstEdge hn ring h p hp e, ?_⟩
  exact ⟨hp.1, hp.2.1, hp.2.2.1,
    htransport p hp e⟩

/-- QWord follows from a REAL proved transport premise.
This does not prove the premise. -/
theorem qword_ofRowTransport {n : Nat} {c : Compiled}
    (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (h : BlockA.WordControl n c)
    (p : Fin n → ProjW c)
    (hfirst : DoneWorkerRows ring h p)
    (htransport : ∀ s : Fin n → ProjW c,
      DoneWorkerRows ring h s →
      ∀ e : Fin n,
        CleanWorkerInv ring h (phiW ring s e)) :
    QWord ring p := by
  exact futureWorkerCertificate_qword ring
    (DoneWorkerRows ring h)
    (futureWorkerCertificate_ofRowTransport hn ring h
      htransport) p hfirst

/-- A physically observed changed edge would rule out membership
in any candidate future-worker certificate.  No reachable
post-DONE witness of this kind is asserted here. -/
theorem changingEdgeRefutesFutureMembership {n : Nat}
    {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c)
    (hchange : ∃ e i : Fin n,
      wordVisible (phiW ring p e) i ≠ wordVisible p i)
    (I : (Fin n → ProjW c) → Prop)
    (hI : FutureWorkerCertificate ring I) :
    ¬ I p := by
  intro hp
  obtain ⟨e, i, hneq⟩ := hchange
  exact hneq ((hI p hp e).1 i)

end WordCertificate
end L3

/-!
Obstruction to the universal transport premise.

This is NOT a trace claimed to come from the canonical I0 launch.
It shows why the current DONE predicate, which no longer constrains
uncolored physical SI sites via workerOrigin, is not a generated-control
predicate.  The first S0 is silent; its resulting S1 targets the leader.
The source is the actual projected owner, not a symbolic transition.
All checks below are proposed finite kernel-decision certificates.
-/

namespace L3
namespace WordCertificate

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false

/-- Five sites, width two, and the existing toy's unique native
leader at zero. The public word has U[2]=1 and all other bits zero;
every marker is zero. An untracked SUM(0,0,0,1) is at site three,
and an untracked busy ROOT is at zero. The serializer is non-hard
at every OLD edge. -/
def rogueWorkerProjection (i : Fin 5) : ProjW cwToyCfg :=
  { (cwToyProjection i) with
    ser := { phase := .C, out := .NEW, probe := .NONE,
             cert := .IDLE, wphase := .OFF }
    si :=
      if i = (0 : Fin 5) then
        { (offSI cwToyCfg.t) with kind := .ROOT, busy := true }
      else if i = (3 : Fin 5) then
        { (offSI cwToyCfg.t) with cur := .SUM }
      else offSI cwToyCfg.t
    u := i == (2 : Fin 5)
    beta := false }

/-- Correct finite receipt flags but no worker provenance: the
frozen monitor tags every SI site and cursor as empty. -/
def rogueDoneControl : BlockA.WordControl 5 cwToyCfg :=
  { cwToyControl with
    phase := .done
    publications := fun i =>
      if i = (1 : Fin 5) then .prefixZero
      else if i = (2 : Fin 5) then .prefixEnd
      else if i = (0 : Fin 5) then .absent
      else .recurrence
    visibleReceipts := fun i => i != (0 : Fin 5)
    prefixMarkers := fun i => i == (1 : Fin 5) }

/-- All five paper word-value equations really hold on this
example; this is not an invalid recurrence/marker word. -/
theorem rogueWordValues :
    CleanWorkerWordValues cwToyRing (0 : Fin 5)
      rogueWorkerProjection := by
  refine {
    prefixZeros := by decide
    firstNonzero := by decide
    laterNonzero := by decide
    recurrence := by decide
    markers := by decide }

/-- At DONE the existing CleanWorkerInv.workerOrigin condition is
vacuous. Its colored prefix, backward and summation obligations are
also vacuous for this monitor. The remaining physical checks are
genuine closed tests of the OLD SI owner on the five edges. -/
theorem rogueDoneRows :
    DoneWorkerRows cwToyRing rogueDoneControl
      rogueWorkerProjection := by
  have hvalidated :
      BlockA.wordValidated cwToyRing rogueDoneControl := by
    unfold BlockA.wordValidated
    decide
  refine ⟨by decide, hvalidated, by decide, ?_⟩
  refine {
    rootFixed := by
      unfold WFixedRoot
      decide
    width := by decide
    workerOrigin := by
      intro i hw
      cases hw
    prefixReads := by
      intro j hj
      have hz : rogueDoneControl.prefixReads.count.val = 0 := rfl
      rw [hz] at hj
      exact False.elim (Nat.not_lt_zero j.val hj)
    prefixAcc := by
      intro i idx z a hk
      have hz : rogueDoneControl.workerKind i = .empty := rfl
      rw [hz] at hk
      cases hk
    prefixGeometry := by
      intro i idx z a hk
      have hz : rogueDoneControl.workerKind i = .empty := rfl
      rw [hz] at hk
      cases hk
    wordValues := rogueWordValues
    backGeometry := by
      intro i target idx hc
      have hz : rogueDoneControl.workerCursor i = .empty := rfl
      rw [hz] at hc
      cases hc
    sumReads := by
      intro i target idx z parity trailing hc
      have hz : rogueDoneControl.workerCursor i = .empty := rfl
      rw [hz] at hc
      cases hc
    sumAcc := by
      intro i target idx z parity trailing hc
      have hz : rogueDoneControl.workerCursor i = .empty := rfl
      rw [hz] at hc
      cases hc
    sumGeometry := by
      intro i target idx z parity trailing hc
      have hz : rogueDoneControl.workerCursor i = .empty := rfl
      rw [hz] at hc
      cases hc
    readyGeometry := by
      intro i hk hw
      cases hw
    orphanGuard := by
      simp only [SelectedWordQuiet]
      decide
    prefixMoveQuiet := by
      simp only [SelectedWordQuiet]
      decide
    prefixTerminalQuiet := by
      simp only [SelectedWordQuiet]
      decide
    prefixPublishQuiet := by
      simp only [SelectedWordQuiet]
      decide
    sumPublishQuiet := by
      simp only [SelectedWordQuiet]
      decide
    nonPublishingQuiet := by
      simp only [SelectedWordQuiet]
      decide }

/-- The existing theorem certifies every FIRST edge, including
the nonpublishing service from site three to site four. -/
theorem rogueInitiallyQuiet :
    ∀ e i : Fin 5,
      wordVisible (phiW cwToyRing rogueWorkerProjection e) i =
        wordVisible rogueWorkerProjection i := by
  exact doneWorkerRows_firstEdge (by decide) cwToyRing
    rogueDoneControl rogueWorkerProjection rogueDoneRows

/-- Exact OLD physical row for 3 -> 4: S0 moves the bad cursor
to site four with index one, without publishing. -/
theorem rogueFirstRow :
    (workerW (rogueWorkerProjection (3 : Fin 5))
      (rogueWorkerProjection (4 : Fin 5))).row = "S0" := by
  decide

/-- Exact OLD physical row on the NEXT 4 -> 0 edge: S1. -/
theorem rogueSecondRow :
    (workerW
      ((phiW cwToyRing rogueWorkerProjection (3 : Fin 5))
        (4 : Fin 5))
      ((phiW cwToyRing rogueWorkerProjection (3 : Fin 5))
        (0 : Fin 5))).row = "S1" := by
  decide

/-- Because both late source bits are zero, the zero-kick writes
true to the busy leader target, whose old U is false. -/
theorem rogueSecondChangesRoot :
    wordVisible
      (phiW cwToyRing
        (phiW cwToyRing rogueWorkerProjection (3 : Fin 5))
        (4 : Fin 5)) (0 : Fin 5) ≠
    wordVisible
      (phiW cwToyRing rogueWorkerProjection (3 : Fin 5))
      (0 : Fin 5) := by
  decide

/-- Any CleanWorkerInv on the post-S0 state would imply that the
next S1 was quiet, contradicting the concrete changed leader bit. -/
theorem roguePostMoveNotClean :
    ¬ CleanWorkerInv cwToyRing rogueDoneControl
      (phiW cwToyRing rogueWorkerProjection (3 : Fin 5)) := by
  intro hc
  have hquiet :
      ∀ i : Fin 5,
        wordVisible
          (phiW cwToyRing
            (phiW cwToyRing rogueWorkerProjection (3 : Fin 5))
            (4 : Fin 5)) i =
        wordVisible
          (phiW cwToyRing rogueWorkerProjection (3 : Fin 5)) i :=
    (selectedWordQuiet_iff_edge cwToyRing
      (phiW cwToyRing rogueWorkerProjection (3 : Fin 5))
      (4 : Fin 5) (by decide)).mp
      ((cleanWorkerInv_wordRowsQuiet cwToyRing rogueDoneControl
        (phiW cwToyRing rogueWorkerProjection (3 : Fin 5))
        hc) (4 : Fin 5))
  exact rogueSecondChangesRoot (hquiet (0 : Fin 5))

/-- Refutes exactly the quantified row-transport premise requested
for the current DoneWorkerRows definition. It does NOT refute a
stronger invariant that certifies canonical generation. -/
theorem rogueUniversalRowTransportFalse :
    ¬ (∀ p : Fin 5 → ProjW cwToyCfg,
      DoneWorkerRows cwToyRing rogueDoneControl p →
      ∀ e : Fin 5,
        CleanWorkerInv cwToyRing rogueDoneControl
          (phiW cwToyRing p e)) := by
  intro ht
  exact roguePostMoveNotClean
    (ht rogueWorkerProjection rogueDoneRows (3 : Fin 5))

end WordCertificate
end L3


/-!
A monitor-independent physical generated-control SHAPE
and an explicit serializer-frontier obstruction.

The fields below encode the four paper shapes, their removable
halves, and exact prefix/summation folds.  gcAcceptClean asserts
that an acceptance currently enabled by the OLD serializer finds
every remote SI site free.  This is a necessary instantaneous
consequence of the claimed validating-frontier scrub.  It is NOT
a historical validating-frontier certificate.

All propositions are built from the actual ProjW fields and ring
geometry; no frozen WordControl color is consulted.
-/

namespace L3
namespace WordCertificate

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false

def gcOtherFree {n : Nat} {c : Compiled}
    (p : Fin n → ProjW c) (site : Fin n) : Prop :=
  ∀ i : Fin n, i ≠ site → freeSI (p i).si = true

def gcOutsidePair {n : Nat} {c : Compiled}
    (p : Fin n → ProjW c)
    (site target : Fin n) : Prop :=
  ∀ i : Fin n, i ≠ site → i ≠ target →
    freeSI (p i).si = true

/-- No worker, including no surviving orphan. -/
def gcEmptyShape {n : Nat} {c : Compiled}
    (p : Fin n → ProjW c) : Prop :=
  ∀ i : Fin n, freeSI (p i).si = true

/-- A single PREFIX at root-relative offset j. Its OR/AND
accumulators are the exact prefix folds over followers 1..j. -/
def gcPrefixShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop :=
  ∃ site : Fin n,
    (p site).si.kind = .PREFIX ∧
    (p site).si.busy = false ∧
    (p site).si.cur = .NONE ∧
    (p site).si.j.val = PPL.cyclicOffset ring root site ∧
    (p site).si.z =
      cwPrefixOr ring root p (p site).si.j.val ∧
    (p site).si.a =
      cwPrefixAnd ring root p (p site).si.j.val ∧
    gcOtherFree p site

/-- An ordinary busy target has passed the initial t-window and
cannot be the leader. -/
def gcBusyTarget {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (target : Fin n) : Prop :=
  target ≠ root ∧
    c.t < PPL.cyclicOffset ring root target ∧
    (p target).si.kind = .ROOT ∧
    (p target).si.busy = true

/-- A backward cursor with physical site Y-t+j, j in 1..t,
and the canonical zero/zero/one accumulator fields. -/
def gcBackCursorAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (target cursor : Fin n) : Prop :=
  target ≠ root ∧
    c.t < PPL.cyclicOffset ring root target ∧
    (p cursor).si.cur = .BACK ∧
    0 < (p cursor).si.j.val ∧
    cursor = PPL.shiftRight ring root
      (PPL.cyclicOffset ring root target - c.t +
        (p cursor).si.j.val) ∧
    (p cursor).si.z = false ∧
    (p cursor).si.p = false ∧
    (p cursor).si.a = true

/-- Busy target and its backward cursor; the cursor may initially
be on the ROOT target itself when j=t. -/
def gcBackShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop :=
  ∃ (target cursor : Fin n),
    gcBusyTarget ring root p target ∧
    gcBackCursorAt ring root p target cursor ∧
    (cursor ≠ target →
      (p cursor).si.kind = .OFF ∧
      (p target).si.cur = .NONE) ∧
    gcOutsidePair p cursor target

/-- Exact index-k source cursor at Y-t+k with all three
OR/XOR/trailing-AND equations, excluding the first source from AND. -/
def gcSumCursorAt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (target cursor : Fin n) : Prop :=
  target ≠ root ∧
    c.t < PPL.cyclicOffset ring root target ∧
    (p cursor).si.kind = .OFF ∧
    (p cursor).si.cur = .SUM ∧
    (p cursor).si.j.val < c.t ∧
    cursor = PPL.shiftRight ring root
      (PPL.cyclicOffset ring root target - c.t +
        (p cursor).si.j.val) ∧
    (p cursor).si.z = cwSumOr ring root p
      (PPL.cyclicOffset ring root target) (p cursor).si.j.val ∧
    (p cursor).si.p = cwSumParity ring root p
      (PPL.cyclicOffset ring root target) (p cursor).si.j.val ∧
    (p cursor).si.a = cwSumTrailing ring root p
      (PPL.cyclicOffset ring root target) (p cursor).si.j.val

/-- Busy target with a live consistent SUM cursor. -/
def gcSumShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop :=
  ∃ (target cursor : Fin n),
    gcBusyTarget ring root p target ∧
    (p target).si.cur = .NONE ∧
    gcSumCursorAt ring root p target cursor ∧
    gcOutsidePair p cursor target

/-- Completed target before A1 or A0, with no remote cursor. -/
def gcReadyShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop :=
  ∃ target : Fin n,
    target ≠ root ∧
    c.t < PPL.cyclicOffset ring root target ∧
    (p target).si.kind = .ROOT ∧
    (p target).si.busy = false ∧
    (p target).si.cur = .NONE ∧
    gcOtherFree p target

/-- A scrubbed cursor leaves its busy target alone. -/
def gcLoneBusyShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop :=
  ∃ target : Fin n,
    gcBusyTarget ring root p target ∧
    (p target).si.cur = .NONE ∧
    gcOtherFree p target

/-- A scrubbed target leaves an orphan BACK cursor whose source
and index still refer to its now-free former target. -/
def gcOrphanBackShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop :=
  ∃ (target cursor : Fin n),
    cursor ≠ target ∧
    freeSI (p target).si = true ∧
    (p cursor).si.kind = .OFF ∧
    gcBackCursorAt ring root p target cursor ∧
    gcOutsidePair p cursor target

/-- A scrubbed target leaves a SUM cursor with the correct
historical folds, but no busy target on which S1 can publish. -/
def gcOrphanSumShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop :=
  ∃ (target cursor : Fin n),
    cursor ≠ target ∧
    freeSI (p target).si = true ∧
    gcSumCursorAt ring root p target cursor ∧
    gcOutsidePair p cursor target

/-- Current-edge scrub requirement for OLD hard acceptance.
It is weaker than the paper's historical validating-frontier
property, which must also prohibit a future acceptance becoming
enabled while a remote old worker survives. -/
def gcAcceptClean {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c) : Prop :=
  ∀ e : Fin n,
    (serW (p e) (p (ring.rightNeighbor e))).hard.hardAccept =
      true →
    ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
      freeSI (p i).si = true

/-- Monitor-independent physical generated-control shape package.
The unique-prefix field makes the one-worker clause explicit.
Its acceptClean field states the visible effect of prior scrubbing
at a CURRENT acceptance, but not validation causality. -/
structure GeneratedControl {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop where
  width : 2 ≤ c.t ∧ c.t < n
  rootNotBusy :
    ¬ ((p root).si.kind = .ROOT ∧ (p root).si.busy = true)
  uniquePrefix : ∀ i j : Fin n,
    (p i).si.kind = .PREFIX →
    (p j).si.kind = .PREFIX → i = j
  shape :
    gcEmptyShape p ∨
    gcPrefixShape ring root p ∨
    gcBackShape ring root p ∨
    gcSumShape ring root p ∨
    gcReadyShape ring root p ∨
    gcLoneBusyShape ring root p ∨
    gcOrphanBackShape ring root p ∨
    gcOrphanSumShape ring root p
  acceptClean : gcAcceptClean ring p

/-- The original rogue DONE state is explicitly excluded:
it has a busy ordinary ROOT target at the leader. -/
theorem rogueNotGenerated :
    ¬ GeneratedControl cwToyRing (0 : Fin 5)
      rogueWorkerProjection := by
  intro h
  have hbad :
      (rogueWorkerProjection (0 : Fin 5)).si.kind = .ROOT ∧
      (rogueWorkerProjection (0 : Fin 5)).si.busy = true := by
    decide
  exact h.rootNotBusy hbad

/-- A clean-looking prefix at offset two, with the correct static
word, but a forged serializer validation frontier. This is a
Cartesian projected W state, NOT a claimed canonical-I0 descendant.
Root zero has WAIT, follower one has a LEAF_OK response; the next
edge installs hard acceptance while leaving the prefix at two. -/
def frontierInterferenceProjection
    (i : Fin 5) : ProjW cwToyCfg :=
  { (rogueWorkerProjection i) with
    ser :=
      if i = (0 : Fin 5) then
        { phase := .B, out := .WAIT, probe := .NONE,
          cert := .RUNNING, wphase := .VALIDATING }
      else if i = (1 : Fin 5) then
        { phase := .C, out := .NEW, probe := .LEAF_OK,
          cert := .IDLE, wphase := .OFF }
      else
        { phase := .C, out := .NEW, probe := .NONE,
          cert := .IDLE, wphase := .OFF }
    si :=
      if i = (2 : Fin 5) then
        { (launchPrefix cwToyCfg.t) with
          j := siJ cwToyCfg.t 2, z := true, a := false }
      else offSI cwToyCfg.t }

/-- All recurrence, first-window, and marker equations hold. -/
theorem frontierInterferenceWordValues :
    CleanWorkerWordValues cwToyRing (0 : Fin 5)
      frontierInterferenceProjection := by
  refine {
    prefixZeros := by decide
    firstNonzero := by decide
    laterNonzero := by decide
    recurrence := by decide
    markers := by decide }

/-- This state meets EVERY declared field of GeneratedControl.
In particular, hardAccept is not yet enabled, so the instantaneous
acceptClean guard is true. -/
theorem frontierInterferenceGenerated :
    GeneratedControl cwToyRing (0 : Fin 5)
      frontierInterferenceProjection := by
  refine {
    width := by decide
    rootNotBusy := by decide
    uniquePrefix := by decide
    shape := ?_
    acceptClean := by
      unfold gcAcceptClean
      decide }
  exact Or.inr (Or.inl
    (by simp only [gcPrefixShape, gcOtherFree]; decide))

/-- The OLD root-to-follower serializer row is S2R, not
an acceptance, and its hard-left worker priority gives I1. -/
theorem frontierInterferenceSerializerRow :
    (serW (frontierInterferenceProjection (0 : Fin 5))
      (frontierInterferenceProjection (1 : Fin 5))).row =
        "S2R" := by
  decide

theorem frontierInterferenceWorkerRow :
    (workerW (frontierInterferenceProjection (0 : Fin 5))
      (frontierInterferenceProjection (1 : Fin 5))).row =
        "I1" := by
  decide

/-- The first service only scrubs the incident root; the remote
prefix and every visible word field survive. -/
theorem frontierInterferenceFirstQuiet :
    ∀ i : Fin 5,
      wordVisible
        (phiW cwToyRing frontierInterferenceProjection
          (0 : Fin 5)) i =
      wordVisible frontierInterferenceProjection i := by
  apply hardErase_edge_quiet cwToyRing frontierInterferenceProjection
    (0 : Fin 5) (by decide)
  · decide
  · decide

/-- After S2R/I1, the exact next OLD serializer pair admits I0
while a remote PREFIX still occupies site two. -/
theorem frontierInterferenceAcceptEnabled :
    (serW
      ((phiW cwToyRing frontierInterferenceProjection
        (0 : Fin 5)) (0 : Fin 5))
      ((phiW cwToyRing frontierInterferenceProjection
        (0 : Fin 5)) (1 : Fin 5))).hard.hardAccept = true := by
  decide

theorem frontierInterferencePrefixSurvives :
    ((phiW cwToyRing frontierInterferenceProjection
      (0 : Fin 5)) (2 : Fin 5)).si.kind = .PREFIX := by
  decide

/-- The successor violates the acceptance-scrub field of the
generated-control package, despite unchanged visible word bits. -/
theorem frontierInterferenceNotGenerated :
    ¬ GeneratedControl cwToyRing (0 : Fin 5)
      (phiW cwToyRing frontierInterferenceProjection
        (0 : Fin 5)) := by
  intro hg
  have hfree :
      freeSI
        ((phiW cwToyRing frontierInterferenceProjection
          (0 : Fin 5)) (2 : Fin 5)).si = true :=
    hg.acceptClean (0 : Fin 5)
      frontierInterferenceAcceptEnabled (2 : Fin 5)
      (by decide) (by decide)
  have hnot :
      freeSI
        ((phiW cwToyRing frontierInterferenceProjection
          (0 : Fin 5)) (2 : Fin 5)).si ≠ true := by
    decide
  exact hnot hfree

/-- The next root-to-follower service does start a second prefix
by the literal priority-I0 row, without deleting the first one. -/
theorem frontierInterferenceNextWorkerRow :
    (workerW
      ((phiW cwToyRing frontierInterferenceProjection
        (0 : Fin 5)) (0 : Fin 5))
      ((phiW cwToyRing frontierInterferenceProjection
        (0 : Fin 5)) (1 : Fin 5))).row = "I0" := by
  decide

theorem frontierInterferenceTwoPrefixes :
    ((phiW cwToyRing
        (phiW cwToyRing frontierInterferenceProjection
          (0 : Fin 5)) (0 : Fin 5))
      (0 : Fin 5)).si.kind = .PREFIX ∧
    ((phiW cwToyRing
        (phiW cwToyRing frontierInterferenceProjection
          (0 : Fin 5)) (0 : Fin 5))
      (2 : Fin 5)).si.kind = .PREFIX := by
  decide

/-- Refutation of the proposed purely physical-shape plus
instantaneous-scrub transport statement. The missing invariant is
the HISTORICAL validating frontier, not merely the current row. -/
theorem generatedControlShapeNotClosed :
    ¬ (∀ p : Fin 5 → ProjW cwToyCfg,
      GeneratedControl cwToyRing (0 : Fin 5) p →
      CleanWorkerWordValues cwToyRing (0 : Fin 5) p →
      ∀ e : Fin 5,
        GeneratedControl cwToyRing (0 : Fin 5)
          (phiW cwToyRing p e)) := by
  intro htransport
  exact frontierInterferenceNotGenerated
    (htransport frontierInterferenceProjection
      frontierInterferenceGenerated
      frontierInterferenceWordValues (0 : Fin 5))

end WordCertificate
end L3


/-!
An attempted serializer/frontier certificate, coupled to
the physical SI projection and independent of WordControl colors.

The validating broadcast site supplies a root-relative offset; the
scrubbed-prefix clause below demands free physical workers on the
already validated arc.  The other fields test the OLD serializer
response and hard-acceptance enabling patterns.  These are necessary
current-state checks, NOT an established characterization of the
historical validating transaction.

The three strengthenings below are deliberately separate, matching
the three bounded search iterations.  The final predicate is not
claimed invariant.  The paper's historical scrub statement has not
been proved from the physical serializer fields alone.
-/

namespace L3
namespace WordCertificate

open AcceptedReceipts
open AcceptedReceipts.WordEntrance
open AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false

/-- First candidate. At every validating broadcasting site e, all
sites from the unique root through the candidate frontier offset
cyclicOffset(root,e) have already been scrubbed. When a LEAF_OK
response or a hard-acceptance pair is present, no remote worker may
remain. The hypotheses use actual OLD serializer fields. -/
structure FrontierCertBase {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop where
  scrubbedBroadcast :
    ∀ e : Fin n,
      (p e).ser.wphase = .VALIDATING →
      (p e).ser.phase = .B →
      ∀ k : Fin n,
        k.val ≤ PPL.cyclicOffset ring root e →
        freeSI
          (p (PPL.shiftRight ring root k.val)).si = true
  responseRemote :
    ∀ e : Fin n,
      (p e).ser.wphase = .VALIDATING →
      (p e).ser.out = .WAIT →
      (p (ring.rightNeighbor e)).ser.probe = .LEAF_OK →
      ∀ i : Fin n,
        i ≠ e → i ≠ ring.rightNeighbor e →
        freeSI (p i).si = true
  acceptanceRemote :
    ∀ e : Fin n,
      (p e).ser.wphase = .VALIDATING →
      (p e).ser.out = .DONE →
      (p (ring.rightNeighbor e)).ser.phase = .F →
      ∀ i : Fin n,
        i ≠ e → i ≠ ring.rightNeighbor e →
        freeSI (p i).si = true

/-- Second candidate: a positive internal observation on a
validating parent must itself have validating provenance. A leaf
response must be physically scrubbed, including the responder
excluded by responseRemote. -/
structure FrontierCertFresh {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop where
  base : FrontierCertBase ring root p
  internalResponderValidating :
    ∀ e : Fin n,
      (p e).ser.wphase = .VALIDATING →
      (p e).ser.out = .WAIT →
      (p (ring.rightNeighbor e)).ser.probe = .INTERNAL_OK →
      (p (ring.rightNeighbor e)).ser.wphase = .VALIDATING
  leafResponderFree :
    ∀ e : Fin n,
      (p e).ser.wphase = .VALIDATING →
      (p e).ser.out = .WAIT →
      (p (ring.rightNeighbor e)).ser.probe = .LEAF_OK →
      freeSI (p (ring.rightNeighbor e)).si = true

/-- Third candidate: pending validating children and already
admitted final responders must be scrubbed. This strengthens
the first two snapshots but still lacks serializer-epoch causality,
as the finite witness below demonstrates. -/
structure FrontierCert {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop where
  fresh : FrontierCertFresh ring root p
  pendingResponderFree :
    ∀ e : Fin n,
      (p e).ser.wphase = .VALIDATING →
      (p e).ser.out = .WAIT →
      (p (ring.rightNeighbor e)).ser.probe = .PENDING →
      (p (ring.rightNeighbor e)).ser.wphase = .VALIDATING →
      freeSI (p (ring.rightNeighbor e)).si = true
  acceptedResponderFree :
    ∀ e : Fin n,
      (p e).ser.wphase = .VALIDATING →
      (p e).ser.out = .DONE →
      (p (ring.rightNeighbor e)).ser.phase = .F →
      freeSI (p (ring.rightNeighbor e)).si = true

/-- The old frontier-forgery snapshot violates even the
first candidate: root zero has a validating WAIT with a LEAF_OK
responder, while site two still contains a PREFIX. -/
theorem frontierInterferenceNotFrontierBase :
    ¬ FrontierCertBase cwToyRing (0 : Fin 5)
      frontierInterferenceProjection := by
  intro hf
  have hclean :
      freeSI (frontierInterferenceProjection (2 : Fin 5)).si =
        true :=
    hf.responseRemote (0 : Fin 5)
      (by decide) (by decide) (by decide)
      (2 : Fin 5) (by decide) (by decide)
  have hdirty :
      freeSI (frontierInterferenceProjection (2 : Fin 5)).si ≠
        true := by
    decide
  exact hdirty hclean

theorem frontierInterferenceNotFrontier :
    ¬ FrontierCert cwToyRing (0 : Fin 5)
      frontierInterferenceProjection := by
  intro hf
  exact frontierInterferenceNotFrontierBase hf.fresh.base

/-! The following three concrete field-level patterns correspond
to the three stages of the bounded n=5, t=2 scan. A scan is not
a proof of universal transport. The closed Lean observations do
not assert that any pattern is reachable from the canonical I0. -/

/-- Iteration zero: correct static word, a generated prefix at site
one, validating root WAIT, and a forged LEAF_OK at the responder.
The prefix may move from site one to site two on edge 1->2. -/
def frontierScanMoveProjection (i : Fin 5) : ProjW cwToyCfg :=
  { (rogueWorkerProjection i) with
    ser :=
      if i = (0 : Fin 5) then
        { phase := .B, out := .WAIT, probe := .NONE,
          cert := .RUNNING, wphase := .VALIDATING }
      else if i = (1 : Fin 5) then
        { phase := .C, out := .NEW, probe := .LEAF_OK,
          cert := .IDLE, wphase := .OFF }
      else
        { phase := .C, out := .NEW, probe := .NONE,
          cert := .IDLE, wphase := .OFF }
    si :=
      if i = (1 : Fin 5) then
        { (launchPrefix cwToyCfg.t) with
          j := siJ cwToyCfg.t 1, z := false, a := false }
      else offSI cwToyCfg.t }

theorem frontierScanMoveWordValues :
    CleanWorkerWordValues cwToyRing (0 : Fin 5)
      frontierScanMoveProjection := by
  refine {
    prefixZeros := by decide
    firstNonzero := by decide
    laterNonzero := by decide
    recurrence := by decide
    markers := by decide }

theorem frontierScanMoveGenerated :
    GeneratedControl cwToyRing (0 : Fin 5)
      frontierScanMoveProjection := by
  refine {
    width := by decide
    rootNotBusy := by decide
    uniquePrefix := by decide
    shape := ?_
    acceptClean := by
      unfold gcAcceptClean
      decide }
  exact Or.inr (Or.inl
    (by simp only [gcPrefixShape, gcOtherFree]; decide))

theorem frontierScanMoveInitialBase :
    FrontierCertBase cwToyRing (0 : Fin 5)
      frontierScanMoveProjection := by
  refine {
    scrubbedBroadcast := by decide
    responseRemote := by decide
    acceptanceRemote := by decide }

theorem frontierScanMoveRows :
    (serW (frontierScanMoveProjection (1 : Fin 5))
      (frontierScanMoveProjection (2 : Fin 5))).row = "S3" ∧
    (workerW (frontierScanMoveProjection (1 : Fin 5))
      (frontierScanMoveProjection (2 : Fin 5))).row = "P1" := by
  decide

theorem frontierScanMoveNotBase :
    ¬ FrontierCertBase cwToyRing (0 : Fin 5)
      (phiW cwToyRing frontierScanMoveProjection
        (1 : Fin 5)) := by
  intro hf
  have hclean :
      freeSI
        ((phiW cwToyRing frontierScanMoveProjection
          (1 : Fin 5)) (2 : Fin 5)).si = true :=
    hf.responseRemote (0 : Fin 5)
      (by decide) (by decide) (by decide)
      (2 : Fin 5) (by decide) (by decide)
  have hdirty :
      freeSI
        ((phiW cwToyRing frontierScanMoveProjection
          (1 : Fin 5)) (2 : Fin 5)).si ≠ true := by
    decide
  exact hdirty hclean

/-- Iteration one: make the responder F rather than LEAF_OK,
and put the validating root in DONE. The first strengthening does
not prohibit an old PREFIX at the responder itself. -/
def frontierScanAcceptProjection (i : Fin 5) : ProjW cwToyCfg :=
  { (frontierScanMoveProjection i) with
    ser :=
      if i = (0 : Fin 5) then
        { phase := .B, out := .DONE, probe := .NONE,
          cert := .RUNNING, wphase := .VALIDATING }
      else if i = (1 : Fin 5) then
        { phase := .F, out := .NEW, probe := .NONE,
          cert := .IDLE, wphase := .OFF }
      else
        { phase := .C, out := .NEW, probe := .NONE,
          cert := .IDLE, wphase := .OFF } }

theorem frontierScanAcceptWordValues :
    CleanWorkerWordValues cwToyRing (0 : Fin 5)
      frontierScanAcceptProjection := by
  refine {
    prefixZeros := by decide
    firstNonzero := by decide
    laterNonzero := by decide
    recurrence := by decide
    markers := by decide }

theorem frontierScanAcceptGenerated :
    GeneratedControl cwToyRing (0 : Fin 5)
      frontierScanAcceptProjection := by
  refine {
    width := by decide
    rootNotBusy := by decide
    uniquePrefix := by decide
    shape := ?_
    acceptClean := by
      unfold gcAcceptClean
      decide }
  exact Or.inr (Or.inl
    (by simp only [gcPrefixShape, gcOtherFree]; decide))

theorem frontierScanAcceptInitialFresh :
    FrontierCertFresh cwToyRing (0 : Fin 5)
      frontierScanAcceptProjection := by
  refine {
    base := {
      scrubbedBroadcast := by decide
      responseRemote := by decide
      acceptanceRemote := by decide }
    internalResponderValidating := by decide
    leafResponderFree := by decide }

theorem frontierScanAcceptRows :
    (serW (frontierScanAcceptProjection (0 : Fin 5))
      (frontierScanAcceptProjection (1 : Fin 5))).row = "S6" ∧
    (workerW (frontierScanAcceptProjection (0 : Fin 5))
      (frontierScanAcceptProjection (1 : Fin 5))).row = "I0" := by
  decide

/-- Hard acceptance creates a PREFIX at the root but does not
scrub the old PREFIX at site one, contradicting uniqueness. -/
theorem frontierScanAcceptNotGenerated :
    ¬ GeneratedControl cwToyRing (0 : Fin 5)
      (phiW cwToyRing frontierScanAcceptProjection
        (0 : Fin 5)) := by
  intro hg
  have hroot :
      ((phiW cwToyRing frontierScanAcceptProjection
        (0 : Fin 5)) (0 : Fin 5)).si.kind = .PREFIX := by
    decide
  have hchild :
      ((phiW cwToyRing frontierScanAcceptProjection
        (0 : Fin 5)) (1 : Fin 5)).si.kind = .PREFIX := by
    decide
  have hneq : (0 : Fin 5) ≠ (1 : Fin 5) := by
    decide
  exact hneq (hg.uniquePrefix (0 : Fin 5) (1 : Fin 5)
    hroot hchild)

/-- Iteration two: all workers are initially free. Root zero is
ready for hard acceptance, but the remote site four retains a
validating broadcasting serializer mark from a competing epoch. -/
def frontierScanStaleProjection (i : Fin 5) : ProjW cwToyCfg :=
  { (rogueWorkerProjection i) with
    ser :=
      if i = (0 : Fin 5) then
        { phase := .B, out := .DONE, probe := .NONE,
          cert := .RUNNING, wphase := .VALIDATING }
      else if i = (1 : Fin 5) then
        { phase := .F, out := .NEW, probe := .NONE,
          cert := .IDLE, wphase := .OFF }
      else if i = (4 : Fin 5) then
        { phase := .B, out := .NEW, probe := .NONE,
          cert := .IDLE, wphase := .VALIDATING }
      else
        { phase := .C, out := .NEW, probe := .NONE,
          cert := .IDLE, wphase := .OFF }
    si := offSI cwToyCfg.t }

theorem frontierScanStaleWordValues :
    CleanWorkerWordValues cwToyRing (0 : Fin 5)
      frontierScanStaleProjection := by
  refine {
    prefixZeros := by decide
    firstNonzero := by decide
    laterNonzero := by decide
    recurrence := by decide
    markers := by decide }

theorem frontierScanStaleGenerated :
    GeneratedControl cwToyRing (0 : Fin 5)
      frontierScanStaleProjection := by
  refine {
    width := by decide
    rootNotBusy := by decide
    uniquePrefix := by decide
    shape := ?_
    acceptClean := by
      unfold gcAcceptClean
      decide }
  exact Or.inl (by unfold gcEmptyShape; decide)

theorem frontierScanStaleInitialFrontier :
    FrontierCert cwToyRing (0 : Fin 5)
      frontierScanStaleProjection := by
  refine {
    fresh := {
      base := {
        scrubbedBroadcast := by decide
        responseRemote := by decide
        acceptanceRemote := by decide }
      internalResponderValidating := by decide
      leafResponderFree := by decide }
    pendingResponderFree := by decide
    acceptedResponderFree := by decide }

theorem frontierScanStaleRows :
    (serW (frontierScanStaleProjection (0 : Fin 5))
      (frontierScanStaleProjection (1 : Fin 5))).row = "S6" ∧
    (workerW (frontierScanStaleProjection (0 : Fin 5))
      (frontierScanStaleProjection (1 : Fin 5))).row = "I0" := by
  decide

/-- The new PREFIX at root zero violates the scrubbed-prefix
equation relative to the stale validating broadcaster at four. -/
theorem frontierScanStaleNotFrontier :
    ¬ FrontierCert cwToyRing (0 : Fin 5)
      (phiW cwToyRing frontierScanStaleProjection
        (0 : Fin 5)) := by
  intro hf
  have hclean :
      freeSI
        ((phiW cwToyRing frontierScanStaleProjection
          (0 : Fin 5))
          (PPL.shiftRight cwToyRing (0 : Fin 5)
            (0 : Fin 5).val)).si = true :=
    hf.fresh.base.scrubbedBroadcast (4 : Fin 5)
      (by decide) (by decide) (0 : Fin 5) (by decide)
  have hdirty :
      freeSI
        ((phiW cwToyRing frontierScanStaleProjection
          (0 : Fin 5))
          (PPL.shiftRight cwToyRing (0 : Fin 5)
            (0 : Fin 5).val)).si ≠ true := by
    decide
  exact hdirty hclean

/-! Deliberate stopping point: three successive finite
strengthenings fail one-edge closure on the bounded alphabet.
No universal preservation or real-run membership theorem follows.
In particular the still-conditional FutureWorkerCertificate
is NOT instantiated here. -/

end WordCertificate
end L3


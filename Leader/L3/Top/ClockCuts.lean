import Leader.L3.Top.FreshTail

/-!
# Q7: the cut classes of Lemma P.1 (packet-transport.tex, P.3--P.13)

`topClockMarkedClasses` is the class record used for the marked-debt phase.
Its predicates are the concrete receipt/physical predicates of
`TopPortPhase.lean` (`topClockConcrete*`), with `firstTail` the permanent cut
of `TopFreshTail.lean` (`topFreshTailPermanentCut`): the genuine tail is
accepted now and the source stream is pure for every continuation.  Each
predicate is a function of the fixed-trace state `Z` (physical target
`qIn`/`qCarry` registers) and its history (the audit frames of `Z.1.2`,
the word `Z.2`); none adds a coordinate to the machine.

Clause map (packet-transport.tex, line numbers of the displayed file):

* `firstTail` -- P.3, lines 373--382, 429--436: the first genuinely sampled
  border tail is accepted at the present cut, `topClockReached`,
  `topClockGenuineTailAccepted`, and the anchored pure stream, here for all
  future words (`topFreshTailPermanentCut`).
* `pureCohorts` -- 62--69, 429--436: serial `i` of the exports after the
  anchor has sampled origin `r-1-(i mod r)`, tail exactly at `i mod r = r-1`.
* `movingBarrier` -- invariant (i), 438--450: pending packets strictly left
  of every settled input, erasure front and live carry.
* `generatedCarryGap` -- invariant (ii), 452--471: a live carry has an empty
  host, only empty or pending inputs on its left, no second carry, and a
  ledger with no inherited origin (a carry born by `launch`).
* `frontProtection` -- invariant (iii), 473--503.  See
  `topClockConcreteFrontProtection_all`: as stated the predicate holds at
  every state; the active/doomed colouring is recoverable from the state
  (`topClockDoomedAt`), so the protection content is carried by the P.6
  potential, not by this predicate.
* `noTerminalReseed` -- invariant (iv), 505--513: while a settled input
  exists, no edge creates a settled terminal input.
* `coloured` -- the conjunction of the above, 410--427 and 438--513.
* `settledEmpty` -- T_(S=0), 797--835; `pendingOnly` -- pi, 822--847;
  `misplacedTail`, `favourable`, `unfavourable` -- 919--1055.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! ### Recorded samples and exports persist -/

/-- A recorded export stays recorded after one more audit step.

Consumer: `topClockTailAnchorNext`. -/
theorem digitRecordedExportStep {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (x : DigitExport c n)
    (h : DigitRecordedExport A x) :
    DigitRecordedExport (digitAuditStep ring S A e) x := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  exact ⟨f, List.mem_cons_of_mem _ hf, h1, h2, h3⟩

/-- A recorded sample stays recorded after one more audit step.

Consumer: `topClockTailAnchorNext`. -/
theorem digitRecordedSampleStep {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (x : DigitSample c n)
    (h : DigitRecordedSample A x) :
    DigitRecordedSample (digitAuditStep ring S A e) x := by
  obtain ⟨f, hf, h1, h2, h3, h4⟩ := h
  exact ⟨f, List.mem_cons_of_mem _ hf, h1, h2, h3, h4⟩

/-- A tail anchor stays an anchor along the fixed trace.

Consumer: `topClockPureCohortsOfPermanent`. -/
theorem topClockTailAnchorNext {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : topClockConcreteTailAnchor s Z anchor) :
    topClockConcreteTailAnchor s (topFixedTraceNext ring C Z e) anchor := by
  refine ⟨digitRecordedExportStep ring (piD Z.1.1) Z.1.2 e anchor h.1,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  obtain ⟨sample, hsample⟩ := h.2.2.2.2.2
  exact ⟨sample,
    digitRecordedSampleStep ring (piD Z.1.1) Z.1.2 e sample hsample.1,
    hsample.2⟩

/-- The fixed trace run on a concatenated word.

Consumer: `topClockPureCohortsOfPermanent`. -/
theorem topFixedTraceRunAppendWord {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (a b : List (Fin n)) :
    topFixedTraceRun ring C (a ++ b) =
      b.foldl (topFixedTraceNext ring C) (topFixedTraceRun ring C a) := by
  unfold topFixedTraceRun
  exact List.foldl_append

/-- A reached cut stays reached after one more edge.

Consumer: `topMarkedCostOfRows`. -/
theorem topClockReachedNext {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (h : topClockReached ring C Z) :
    topClockReached ring C (topFixedTraceNext ring C Z e) := by
  unfold topClockReached at h ⊢
  have hrun := topFixedTraceRunAppendWord ring C Z.2 [e]
  rw [← h] at hrun
  have hnext : (topFixedTraceNext ring C Z e).2 = Z.2 ++ [e] := rfl
  rw [hnext, hrun]
  rfl

/-- A tail anchor persists along every continuation word.

Consumer: `topClockPureCohortsOfPermanent`. -/
theorem topClockTailAnchorWord {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n),
      topClockConcreteTailAnchor s Z anchor →
      topClockConcreteTailAnchor s
        (w.foldl (topFixedTraceNext ring C) Z) anchor := by
  intro w
  induction w with
  | nil => intro Z h; exact h
  | cons e rest ih =>
      intro Z h
      exact ih _ (topClockTailAnchorNext ring C s Z e anchor h)

/-- **Purity is permanent from the permanent first-tail cut.**  If the
permanent cut holds at `Z`, the anchored pure source stream holds at every
later reached cut of the same word.

Consumer: the coloured cut of `topClockMarkedClasses` (P.4--P.5 closing
step). -/
theorem topClockPureCohortsOfPermanent {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (h : topFreshTailPermanentCut ring C s Z)
    (w : List (Fin n)) :
    topClockConcretePureCohorts s
      (topFixedTraceRun ring C (Z.2 ++ w)) := by
  obtain ⟨hreach, _, anchor, hanchor, _, hfuture⟩ := h
  refine ⟨anchor, ?_, hfuture w⟩
  rw [topFixedTraceRunAppendWord ring C Z.2 w, ← hreach]
  exact topClockTailAnchorWord ring C s anchor w Z hanchor

/-! ### The front-protection predicate is state-determined -/

/-- The doomed settled members, read from the state: a settled input with an
erasure front on its left and only settled inputs in between.

Consumer: `topClockConcreteFrontProtection_all`. -/
def topClockDoomedAt {n : Nat} (s : Fin n) (Z : TopFixedTraceState n)
    (j : Fin (topClockSpan n)) : Prop :=
  (topClockConcreteInputAt s Z j).isS = true ∧
  ∃ left : Fin (topClockSpan n),
    left.val < j.val ∧
    topClockConcreteInputAt s Z left = .X ∧
    ∀ k : Fin (topClockSpan n),
      left.val < k.val → k.val ≤ j.val →
      (topClockConcreteInputAt s Z k).isS = true

/-- **Invariant (iii) holds at every state with the recovered colouring.**
`topClockConcreteFrontProtection` is therefore not a restriction on the
state; the doomed set is the state-determined one above.

Consumer: `topClockColouredIff`. -/
theorem topClockConcreteFrontProtection_all {n : Nat}
    (s : Fin n) (Z : TopFixedTraceState n) :
    topClockConcreteFrontProtection s Z := by
  refine ⟨topClockDoomedAt s Z, ?_, ?_, ?_⟩
  · intro j hj
    exact hj.1
  · intro j hj
    obtain ⟨hS, left, hl, hX, hmid⟩ := hj
    refine ⟨left, hl, hX, ?_⟩
    intro k hk1 hk2
    refine ⟨hmid k hk1 hk2, hmid k hk1 hk2, left, hk1, hX, ?_⟩
    intro m hm1 hm2
    exact hmid m hm1 (Nat.le_trans hm2 hk2)
  · intro left j hX hj hS
    refine ⟨hS, left, ?_, hX, ?_⟩
    · omega
    · intro k hk1 hk2
      have : k.val = j.val := by omega
      have hkj : k = j := Fin.ext this
      rw [hkj]
      exact hS

/-- The coloured cut is the conjunction of reachedness, purity, the barrier,
the carry gap and the terminal no-reseed condition.

Consumer: `topClockMarkedDebtPhaseOfRows` (target form). -/
theorem topClockColouredIff {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) :
    topClockConcreteColoured ring C s Z ↔
      topClockReached ring C Z ∧ topClockConcretePureCohorts s Z ∧
      topClockConcreteMovingBarrier s Z ∧
      topClockConcreteGeneratedCarryGap s Z ∧
      topClockConcreteNoTerminalReseed ring C s Z := by
  constructor
  · rintro ⟨h1, h2, h3, h4, _, h6⟩
    exact ⟨h1, h2, h3, h4, h6⟩
  · rintro ⟨h1, h2, h3, h4, h6⟩
    exact ⟨h1, h2, h3, h4, topClockConcreteFrontProtection_all s Z, h6⟩

/-- **The cut classes for the marked-debt phase.**  The first-tail class is
the permanent cut; every other class is the concrete one.  The eight spec
fields are the ones carried by the record.

Consumer: `TopClockMarkedDebtPhase` (via `TopClockPhaseBundle.cuts`). -/
noncomputable def topClockMarkedClasses {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) : TopClockCutClasses ring C s :=
  topFreshTailCorrectedClasses ring C s

/-- The first-tail class of the marked-debt record is the permanent cut. -/
theorem topClockMarkedClasses_firstTail {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) :
    (topClockMarkedClasses ring C s).firstTail Z ↔
      topFreshTailPermanentCut ring C s Z := Iff.rfl

/-- The coloured class of the marked-debt record is the concrete one. -/
theorem topClockMarkedClasses_coloured {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) :
    (topClockMarkedClasses ring C s).coloured Z ↔
      topClockConcreteColoured ring C s Z := Iff.rfl

/-- The eight spec fields of the marked-debt record, as one statement.

Consumer: `TopClockPhaseBundle` assembly. -/
theorem topClockMarkedClasses_spec {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n) :
    let cuts := topClockMarkedClasses ring C s
    (∀ Z, cuts.firstTail Z →
      topClockReached ring C Z ∧
      topClockGenuineTailAccepted C s Z ∧ cuts.pureCohorts Z) ∧
    (∀ Z, cuts.coloured Z →
      topClockReached ring C Z ∧ cuts.pureCohorts Z ∧
      cuts.movingBarrier Z ∧ cuts.generatedCarryGap Z ∧
      cuts.frontProtection Z ∧ cuts.noTerminalReseed Z) ∧
    (∀ Z, cuts.settledEmpty Z →
      topClockReached ring C Z ∧ cuts.pureCohorts Z ∧
      topClockTargetSettledEmpty s Z) ∧
    (∀ Z, cuts.pendingOnly Z →
      topClockReached ring C Z ∧ cuts.pureCohorts Z ∧
      cuts.consecutivePendingSuffix Z ∧ topClockTargetPendingOnly s Z) ∧
    (∀ Z, cuts.misplacedTail Z →
      topClockReached ring C Z ∧ cuts.pureCohorts Z ∧
      cuts.consecutivePendingSuffix Z) ∧
    (∀ Z, cuts.favourable Z → topClockReached ring C Z) ∧
    (∀ Z, cuts.unfavourable Z → cuts.coloured Z) :=
  ⟨(topClockMarkedClasses ring C s).firstTailSpec,
   (topClockMarkedClasses ring C s).colouredSpec,
   (topClockMarkedClasses ring C s).settledSpec,
   (topClockMarkedClasses ring C s).pendingSpec,
   (topClockMarkedClasses ring C s).misplacedSpec,
   (topClockMarkedClasses ring C s).favourableSpec,
   (topClockMarkedClasses ring C s).unfavourableSpec⟩

end L3

#print axioms L3.topClockPureCohortsOfPermanent
#print axioms L3.topClockReachedNext
#print axioms L3.topClockConcreteFrontProtection_all
#print axioms L3.topClockColouredIff
#print axioms L3.topClockMarkedClasses_spec

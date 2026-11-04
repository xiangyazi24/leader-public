import Leader.L3.Top.FreshTail

/-!
Q7c P.3: actual source-row FIFO/rearm equations, exact trace
replay, finite source/visit capacity, and a conditional
history-charge reduction. The unproved history-level producer
is NOT replaced by the local one-step interface.

There is no asserted unconditional FIFOReceiptBound, no
unconditional backwards-purity theorem, and no constructed
adapted ledger. All comments describing those gaps are factual.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ## Literal source transition rows -/

/-- A source D travels only into an OLD empty nonborder output.
An outgoing tail leaves U, a non-tail leaves E. -/
theorem topFreshTailFifoDataMove
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n)
    (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (tail : Bool)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hxo : (Z.1.1 e).qOut = .D v tail)
    (hyo : (Z.1.1 (ring.rightNeighbor e)).qOut = .E)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        (if tail then .U else .E) ∧
    ((topFixedTraceNext ring C Z e).1.1
        (ring.rightNeighbor e)).qOut = .D v tail := by
  have howner :
      (topPortLiteralTopOwner ring Z.1.1 e).x.qOut =
          (if tail then .U else .E) ∧
      (topPortLiteralTopOwner ring Z.1.1 e).y.qOut =
          .D v tail := by
    unfold topPortLiteralTopOwner
    exact topPortOwnerQODataMoves
      _ _ _ _ _ v tail hxl hyl hxo hyo hyb
  have hx := (topPortLiteralSourceFields ring C Z.1.1 e).2.2
  have hy := (topPortLiteralResponderFields
    ring hn C Z.1.1 e).2.2
  change
    (topFixedPublicNext ring C Z.1.1 e e).qOut =
        (if tail then .U else .E) ∧
    (topFixedPublicNext ring C Z.1.1 e
        (ring.rightNeighbor e)).qOut = .D v tail
  exact ⟨hx.trans howner.1, hy.trans howner.2⟩

/-- A D cannot jump into an occupied nonborder output. -/
theorem topFreshTailFifoOccupiedOwner
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxo : x.qOut = .D v tail)
    (hyb : y.beta = false)
    (hoccupied : y.qOut ≠ .E) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      .D v tail := by
  cases hyo : y.qOut with
  | E =>
      exact False.elim (hoccupied hyo)
  | U =>
      simp [liveTopPair, hxl, hyl, hxo, hyb, hyo,
        OutTok.isD, OutTok.isE, OutTok.isU]
  | D w t =>
      simp [liveTopPair, hxl, hyl, hxo, hyb, hyo,
        OutTok.isD, OutTok.isE, OutTok.isU]

theorem topFreshTailFifoOccupiedFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n)
    (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (tail : Bool)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hxo : (Z.1.1 e).qOut = .D v tail)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false)
    (hoccupied : (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      .D v tail := by
  have howner :
      (topPortLiteralTopOwner ring Z.1.1 e).x.qOut =
        .D v tail := by
    unfold topPortLiteralTopOwner
    exact topFreshTailFifoOccupiedOwner
      _ _ _ _ _ v tail hxl hyl hxo hyb hoccupied
  change (topFixedPublicNext ring C Z.1.1 e e).qOut =
    .D v tail
  exact (topPortLiteralSourceFields ring C Z.1.1 e).2.2.trans
    howner

/-- U samples the OLD local digit and marker, not the
output of a service that occurs simultaneously. -/
theorem topFreshTailFifoUnreadSamples
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n)
    (e : Fin n)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hu : (Z.1.1 e).qOut = .U) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      .D (Z.1.1 e).d (Z.1.1 e).beta := by
  change (topFixedPublicNext ring C Z.1.1 e e).qOut =
    .D (Z.1.1 e).d (Z.1.1 e).beta
  exact topPortPhysicalQOUnreadSamples
    ring C Z.1.1 e hxl hyl hu

/-- The fixed source border can bootstrap U from E. -/
theorem topFreshTailFifoMarkerBootstraps
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n)
    (e : Fin n)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hmarker : (Z.1.1 e).beta = true)
    (hempty : (Z.1.1 e).qOut = .E) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      .U := by
  have howner :
      (topPortLiteralTopOwner ring Z.1.1 e).x.qOut =
        .U := by
    unfold topPortLiteralTopOwner
    exact (topPortOwnerQOMarkerBootstraps
      _ _ _ _ _ hxl hyl hmarker hempty).1
  change (topFixedPublicNext ring C Z.1.1 e e).qOut = .U
  exact (topPortLiteralSourceFields ring C Z.1.1 e).2.2.trans
    howner

private theorem topFreshTailFifoPortAcceptsOwner
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxi : x.qIn = .E) (hxc : x.qCarry = .OFF)
    (hyi : y.qIn = .E) (hyc : y.qCarry = .OFF)
    (hyb : y.beta = true)
    (hxo : x.qOut = .D v true) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut = .U ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .P v true := by
  have hr := topPortOwnerQOPortAccepts c x y resolvedX resolvedY
    v true hxl hyl hxi hxc hyi hyc hyb hxo
  exact ⟨by simpa using hr.2.1, hr.1⟩

/-- A successful OLD true-tail offer leaves U and creates
the corresponding target-border pending input. -/
theorem topFreshTailFifoPortTailRearms
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n)
    (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (Z.1.1 e).l = false)
    (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hxi : (Z.1.1 e).qIn = .E)
    (hxc : (Z.1.1 e).qCarry = .OFF)
    (hyi : (Z.1.1 (ring.rightNeighbor e)).qIn = .E)
    (hyc : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF)
    (hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true)
    (hxo : (Z.1.1 e).qOut = .D v true) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut = .U ∧
    ((topFixedTraceNext ring C Z e).1.1
       (ring.rightNeighbor e)).qIn = .P v true := by
  have howner :
      (topPortLiteralTopOwner ring Z.1.1 e).x.qOut = .U ∧
      (topPortLiteralTopOwner ring Z.1.1 e).y.qIn =
        .P v true := by
    unfold topPortLiteralTopOwner
    exact topFreshTailFifoPortAcceptsOwner _ _ _ _ _ v
      hxl hyl hxi hxc hyi hyc hyb hxo
  have hx := (topPortLiteralSourceFields ring C Z.1.1 e).2.2
  have hy := (topPortLiteralResponderFields
    ring hn C Z.1.1 e).1
  change
    (topFixedPublicNext ring C Z.1.1 e e).qOut = .U ∧
    (topFixedPublicNext ring C Z.1.1 e
      (ring.rightNeighbor e)).qIn = .P v true
  exact ⟨hx.trans howner.1, hy.trans howner.2⟩

/-! ## A local FIFO row contract, true at every trace state -/

/-- This is a local owner-row invariant, not yet a finite
historical rank or an ancestry accounting invariant. -/
def TopFreshTailSourceRowInvariant
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) :
    Prop :=
  (∀ (e : Fin n)
       (v : Fin (compileAdvice (ceilLogTwo n)).topA)
       (tail : Bool),
      (Z.1.1 e).l = false →
      (Z.1.1 (ring.rightNeighbor e)).l = false →
      (Z.1.1 e).qOut = .D v tail →
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E →
      (Z.1.1 (ring.rightNeighbor e)).beta = false →
      ((topFixedTraceNext ring C Z e).1.1 e).qOut =
          (if tail then .U else .E) ∧
      ((topFixedTraceNext ring C Z e).1.1
        (ring.rightNeighbor e)).qOut = .D v tail) ∧
  (∀ (e : Fin n)
       (v : Fin (compileAdvice (ceilLogTwo n)).topA)
       (tail : Bool),
      (Z.1.1 e).l = false →
      (Z.1.1 (ring.rightNeighbor e)).l = false →
      (Z.1.1 e).qOut = .D v tail →
      (Z.1.1 (ring.rightNeighbor e)).beta = false →
      (Z.1.1 (ring.rightNeighbor e)).qOut ≠ .E →
      ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        .D v tail) ∧
  (∀ e : Fin n,
      (Z.1.1 e).l = false →
      (Z.1.1 (ring.rightNeighbor e)).l = false →
      (Z.1.1 e).qOut = .U →
      ((topFixedTraceNext ring C Z e).1.1 e).qOut =
        .D (Z.1.1 e).d (Z.1.1 e).beta)

theorem topFreshTailSourceRowInvariantAll
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) :
    TopFreshTailSourceRowInvariant ring C Z := by
  refine ⟨?_, ?_, ?_⟩
  · intro e v tail hxl hyl hxo hyo hyb
    exact topFreshTailFifoDataMove ring hn C Z
      e v tail hxl hyl hxo hyo hyb
  · intro e v tail hxl hyl hxo hyb hoccupied
    exact topFreshTailFifoOccupiedFrame ring C Z
      e v tail hxl hyl hxo hyb hoccupied
  · intro e hxl hyl hu
    exact topFreshTailFifoUnreadSamples
      ring C Z e hxl hyl hu

theorem topFreshTailSourceRowInvariantStart
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) :
    TopFreshTailSourceRowInvariant ring C
      ((C, digitAuditInitial (piD C)), []) :=
  topFreshTailSourceRowInvariantAll ring hn C _

theorem topFreshTailSourceRowInvariantStep
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n)
    (e : Fin n)
    (_hrow : TopFreshTailSourceRowInvariant ring C Z) :
    TopFreshTailSourceRowInvariant ring C
      (topFixedTraceNext ring C Z e) :=
  topFreshTailSourceRowInvariantAll ring hn C _

/-! ## An exact reached trace replay invariant -/

private theorem topFreshTailFifoFoldWord
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (word : List (Fin n)) :
    (word.foldl (topFixedTraceNext ring C) Z).2 =
      Z.2 ++ word := by
  induction word generalizing Z with
  | nil =>
      simp
  | cons e rest ih =>
      change
        (rest.foldl (topFixedTraceNext ring C)
          (topFixedTraceNext ring C Z e)).2 =
        Z.2 ++ (e :: rest)
      rw [ih]
      change (Z.2 ++ [e]) ++ rest = Z.2 ++ (e :: rest)
      rw [List.append_assoc]
      rfl

theorem topFreshTailFifoRunWord
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (word : List (Fin n)) :
    (topFixedTraceRun ring C word).2 = word := by
  change
    (word.foldl (topFixedTraceNext ring C)
      ((C, digitAuditInitial (piD C)), [])).2 = word
  simpa using topFreshTailFifoFoldWord
    ring C ((C, digitAuditInitial (piD C)), []) word

private theorem topFreshTailFifoFoldSnoc
    {α β : Type} (f : β → α → β)
    (z : β) (word : List α) (e : α) :
    (word ++ [e]).foldl f z =
      f (word.foldl f z) e := by
  induction word generalizing z with
  | nil =>
      rfl
  | cons x xs ih =>
      exact ih (f z x)

theorem topFreshTailFifoRunSnoc
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (word : List (Fin n)) (e : Fin n) :
    topFixedTraceRun ring C (word ++ [e]) =
      topFixedTraceNext ring C
        (topFixedTraceRun ring C word) e := by
  change
    (word ++ [e]).foldl (topFixedTraceNext ring C)
      ((C, digitAuditInitial (piD C)), []) =
    topFixedTraceNext ring C
      (word.foldl (topFixedTraceNext ring C)
        ((C, digitAuditInitial (piD C)), [])) e
  exact topFreshTailFifoFoldSnoc
    (topFixedTraceNext ring C)
    ((C, digitAuditInitial (piD C)), []) word e

def TopFreshTailTraceReplayInvariant
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) :
    Prop :=
  ∃ word : List (Fin n),
    Z = topFixedTraceRun ring C word ∧ Z.2 = word

theorem topFreshTailTraceReplayStart
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) :
    TopFreshTailTraceReplayInvariant ring C
      ((C, digitAuditInitial (piD C)), []) := by
  exact ⟨[], rfl, rfl⟩

theorem topFreshTailTraceReplayStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (h : TopFreshTailTraceReplayInvariant ring C Z) :
    TopFreshTailTraceReplayInvariant ring C
      (topFixedTraceNext ring C Z e) := by
  obtain ⟨word, hz, hw⟩ := h
  refine ⟨word ++ [e], ?_, ?_⟩
  · rw [hz]
    exact (topFreshTailFifoRunSnoc ring C word e).symm
  · change Z.2 ++ [e] = word ++ [e]
    rw [hw]

theorem topFreshTailTraceReplayReached
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n)
    (h : TopFreshTailTraceReplayInvariant ring C Z) :
    topClockReached ring C Z := by
  obtain ⟨word, hz, hw⟩ := h
  change Z = topFixedTraceRun ring C Z.2
  rw [hw]
  exact hz

/-! ## Counting capacity without Finset -/

private theorem topFreshTailBooleanSlots
    (r : Nat) (f : Fin r → Bool) :
    (List.ofFn (fun i : Fin r =>
      if f i then 1 else 0)).sum ≤ r := by
  have h := ofFn_sum_le
    (fun i : Fin r => if f i then 1 else 0)
    (fun _ : Fin r => 1)
    (by
      intro i
      cases hf : f i <;> simp [hf])
  simpa only [ofFn_sum_const, Nat.mul_one] using h

/-- The physical source block has at most r occupied D slots
at every time, regardless of the arbitrary private start. -/
def topFreshTailOccupiedSourceSlots
    {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) : Nat :=
  (List.ofFn (fun j : Fin (topClockSpan n) =>
    if (Z.1.1 (certSite s j.val)).qOut.isD
    then 1 else 0)).sum

theorem topFreshTailOccupiedSourceSlotsLe
    {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) :
    topFreshTailOccupiedSourceSlots s Z ≤ topClockSpan n := by
  unfold topFreshTailOccupiedSourceSlots
  exact topFreshTailBooleanSlots
    (topClockSpan n)
    (fun j : Fin (topClockSpan n) =>
      (Z.1.1 (certSite s j.val)).qOut.isD)

/-- Capacity of the r-by-r array of old-tail/site visit slots.
To charge actual receipts to these slots, an injection still
has to be proved from the physical FIFO ancestry rows. -/
theorem topFreshTailVisitGridBound
    (r : Nat) (charged : Fin r → Fin r → Bool) :
    (List.ofFn (fun i : Fin r =>
      (List.ofFn (fun j : Fin r =>
        if charged i j then 1 else 0)).sum)).sum ≤ r * r := by
  have hrow (i : Fin r) :
      (List.ofFn (fun j : Fin r =>
        if charged i j then 1 else 0)).sum ≤ r :=
    topFreshTailBooleanSlots r (charged i)
  have hsum := ofFn_sum_le
    (fun i : Fin r =>
      (List.ofFn (fun j : Fin r =>
        if charged i j then 1 else 0)).sum)
    (fun _ : Fin r => r)
    hrow
  simpa only [ofFn_sum_const] using hsum

/-- Permanent purity, if established at one fixed anchor
for ALL continuation words, persists under every suffix. -/
theorem topFreshTailFifoPureFutureShift
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (pre : List (Fin n))
    (hfuture : ∀ suffix : List (Fin n),
      topClockConcretePureStream s
        (topFixedTraceRun ring C (pre ++ suffix)) anchor)
    (e : Fin n) :
    ∀ suffix : List (Fin n),
      topClockConcretePureStream s
        (topFixedTraceRun ring C
          ((pre ++ [e]) ++ suffix)) anchor := by
  intro suffix
  have h := hfuture (e :: suffix)
  simpa only [List.append_assoc, List.singleton_append] using h

/-! ## Remaining GLOBAL source-history obligations -/

/-- Actual receipts must be charged injectively to:
at most r inherited source occupancies, and at most r²
old-tail/site visits, plus the first genuine accepted tail.
The physical ancestry injection is NOT proved here. -/
noncomputable def TopFreshTailPreTailCharge
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockReached ring C Z →
    (∀ (pre suffix : List (Fin n)),
      pre ++ suffix = Z.2 → suffix ≠ [] →
      ¬ topClockGenuineTailAccepted C s
        (topFixedTraceRun ring C pre)) →
    ∃ inherited descendants : Nat,
      inherited ≤ topClockSpan n ∧
      descendants ≤ topClockSpan n ^ 2 ∧
      topFreshTailPortReceiptCount s Z ≤
        inherited + descendants + 1

theorem topFreshTailFIFOReceiptBoundOfCharge
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hcharge : TopFreshTailPreTailCharge ring C s) :
    TopFreshTailFIFOReceiptBound ring C s := by
  intro Z hreach hpre
  obtain ⟨inherited, descendants, hi, hd, hcount⟩ :=
    hcharge Z hreach hpre
  have hwidth : 1 ≤ topClockSpan n := by
    have h := cert_rho_ge_three n hn
    change 3 ≤ topClockSpan n at h
    omega
  have hsum :
      inherited + descendants + 1 ≤
        topClockSpan n ^ 2 + topClockSpan n + 1 := by
    omega
  exact Nat.le_trans hcount
    (Nat.le_trans hsum
      (topFreshTailOperandArithmetic
        (topClockSpan n) hwidth))

/-- The missing backwards-offset induction: at the FIRST
actual genuine tail (no earlier such prefix), all future
source serials use the same current sampled anchor. -/
noncomputable def TopFreshTailBackwardsPurity
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockReached ring C Z →
    (∀ (pre suffix : List (Fin n)),
      pre ++ suffix = Z.2 → suffix ≠ [] →
      ¬ topClockGenuineTailAccepted C s
        (topFixedTraceRun ring C pre)) →
    topClockGenuineTailAccepted C s Z →
    ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
      topClockConcreteTailAnchor s Z anchor ∧
      anchor.time = Z.1.2.clock ∧
      ∀ word : List (Fin n),
        topClockConcretePureStream s
          (topFixedTraceRun ring C (Z.2 ++ word)) anchor

theorem topFreshTailPermanentCutOfBackwardsPurity
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hpurity : TopFreshTailBackwardsPurity ring C s)
    (Z : TopFixedTraceState n)
    (hreached : topClockReached ring C Z)
    (hfirst : ∀ (pre suffix : List (Fin n)),
      pre ++ suffix = Z.2 → suffix ≠ [] →
      ¬ topClockGenuineTailAccepted C s
        (topFixedTraceRun ring C pre))
    (htail : topClockGenuineTailAccepted C s Z) :
    topFreshTailPermanentCut ring C s Z := by
  obtain ⟨anchor, ha, ht, hfuture⟩ :=
    hpurity Z hreached hfirst htail
  exact ⟨hreached, htail, anchor, ha, ht, hfuture⟩

/-- Conditional corrected P.3 from an ACTUAL adapted ledger.
A separate physical FIFO/charging proof must construct it. -/
theorem topFreshTailCorrectedPhaseOfAdaptedLedger
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (ledger : TopFreshTailAdaptedLedger
      ring C s (topFreshTailCorrectedClasses ring C s)) :
    TopClockFreshTailPhase ring C s
      (topFreshTailCorrectedClasses ring C s) := by
  exact topFreshTailPhaseOfAdaptedLedger ring C s hbad
    (topFreshTailCorrectedClasses ring C s) ledger

end L3

#print axioms L3.topFreshTailFifoDataMove
#print axioms L3.topFreshTailFifoOccupiedFrame
#print axioms L3.topFreshTailSourceRowInvariantStep
#print axioms L3.topFreshTailTraceReplayStep
#print axioms L3.topFreshTailVisitGridBound
#print axioms L3.topFreshTailFIFOReceiptBoundOfCharge
#print axioms L3.topFreshTailPermanentCutOfBackwardsPurity
#print axioms L3.topFreshTailCorrectedPhaseOfAdaptedLedger

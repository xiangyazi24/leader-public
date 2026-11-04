import Leader.L3.RenewalReferenceClockInFlightRows

/-!
BANK inherited-atom extinction: replay and zero-stock safety reductions.

It intentionally does not assert the still-unproved twelve-row local
selected-pair census. The last two extinction lemmas make that exact
remaining premise explicit; they are not unconditional L10/L11.

The in-flight invariant is now available on every seed/word replay.
In particular it forbids the empty-controller/empty-worker fallback
entrance payloads at genuinely effectful old BANK rows.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A valid reference step is literally the next replayed old BANK
edge. No supplementary transition is defined. -/
theorem bankInheritedReferenceStepReplay
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (z : BankReferenceState ring hbank)
    (hReplay :
      z.val = rbRun ring (renewalBankStart ring seed) pre)
    (e : Fin n) :
    ((bankValidRootedReferenceData ring hbank).referenceNext z e).val =
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) := by
  change renewalBankNext ring z.val e =
    rbRun ring (renewalBankStart ring seed) (pre ++ [e])
  rw [rbRunAppend]
  rw [← hReplay]
  rfl

/-- The valid subtype run and unrestricted BANK ghost run have the
same physical/ghost value on every scheduler word. -/
theorem bankInheritedAuthorityRunReplay
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (word : List (Fin n)) :
    (bankValidAuthorityRun ring hbank z word).val =
      rbRun ring z.val word := by
  induction word generalizing z with
  | nil =>
      rfl
  | cons e tail ih =>
      change
        (bankValidAuthorityRun ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext z e)
          tail).val =
        rbRun ring (renewalBankNext ring z.val e) tail
      exact ih _

/-- An actual root ARMED/CSTART controller never uses the
renewalBankActivePayload empty/waiting fallback. -/
theorem bankInheritedAlignedActivePayloadCount
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hAligned : BankInFlightAligned ring r)
    (e : Fin n)
    (hroot : (r.1 e).pack.val = 0)
    (hmode :
      (r.1 e).mode = .ARMED ∨
        (r.1 e).mode = .CSTART) :
    bankInheritedPayloadAtomCount
        (renewalBankActivePayload (r.2.sites e).controller e) =
      bankInheritedControllerAtomCount
        (r.2.sites e).controller := by
  obtain ⟨p, hp⟩ :=
    bankInFlightAlignedActiveAtRoot
      ring r hAligned e hroot hmode
  rw [hp]
  rfl

/-- On an ordinary nonreset return token, the old destination worker
is a genuine payload, not an entrance fallback. RL is different:
it may be a pending receipt and requires the zeroAccept branch. -/
theorem bankInheritedAlignedOrdinaryReturnPayload
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hAligned : BankInFlightAligned ring r)
    (e : Fin n)
    (htok :
      (r.1 (ring.rightNeighbor e)).tok = .AL ∨
      (r.1 (ring.rightNeighbor e)).tok = .CL0 ∨
      (r.1 (ring.rightNeighbor e)).tok = .CL1) :
    ∃ p : RenewalBankPayload n,
      (r.2.sites (ring.rightNeighbor e)).worker = .payload p := by
  have hw := (hAligned (ring.rightNeighbor e)).2
  rcases htok with ht | ht | ht
  · rw [ht] at hw
    exact hw
  · rw [ht] at hw
    exact hw
  · rw [ht] at hw
    exact hw

/-- At a physically enabled OLD success, the broad in-flight
invariant supplies the actual waiting/payload pair needed by the
zero-stock origin lemma. No row-wide BankOccupancyAligned assumption
is needed. For nonsuccess edges BankFreshAuthorityAt is vacuous. -/
theorem bankInheritedSuccessPairOfInFlight
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hAligned : BankInFlightAligned ring r)
    (e : Fin n)
    (hSuccess :
      bankSuccess
        (bankCell (r.1 e) (r.1 e).pack.val)
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val)
        (packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b = true) :
    ∃ atoms : List (RenewalBankAtom n),
      ∃ p : RenewalBankPayload n,
        (r.2.sites e).controller = .waiting atoms ∧
          (r.2.sites (ring.rightNeighbor e)).worker =
            .payload p := by
  have hrow :=
    bankInheritedPhysicalSuccessRow ring r e hSuccess
  have hmode :=
    (bankInheritedOrdinaryReturnModeToken
      ring r e hrow.1
      (Or.inr (Or.inr (Or.inr hrow.2)))).1
  obtain ⟨atoms, hc⟩ :=
    bankInFlightAlignedWaitingAtRoot
      ring r hAligned e hrow.1 hmode
  have htoken :
      (r.1 (ring.rightNeighbor e)).tok = .CL1 := by
    by_cases ht : (r.1 (ring.rightNeighbor e)).tok = .CL1
    · exact ht
    · simp [bankSuccess, bankCell, ht] at hSuccess
  obtain ⟨p, hw⟩ :=
    bankInheritedAlignedOrdinaryReturnPayload
      ring r hAligned e (Or.inr (Or.inr htoken))
  exact ⟨atoms, p, hc, hw⟩

/-- L11's current-state fresh payer, unconditionally for a real
reachable zero-atom state. ReceiptInv supplies the completed origin;
in-flight C/W shape supplies actual waiting/payload OLD fields. -/
theorem bankInheritedZeroFreshPayerOfReplay
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (z : BankReferenceState ring hbank)
    (hReplay :
      z.val = rbRun ring (renewalBankStart ring seed) pre)
    (hzero :
      bankInheritedStateAtomCount ring hbank z = 0) :
    BankFreshAuthorityAt ring hbank z := by
  have hi : ReceiptInv ring seed pre z.val := by
    rw [hReplay]
    exact rbReceiptInvBankWordOfInv
      ring (by omega) seed hbank pre
  have hAligned : BankInFlightAligned ring z.val := by
    rw [hReplay]
    exact bankInFlightAlignedWord ring hn seed hbank pre
  intro e hSuccess
  obtain ⟨atoms, p, hc, hw⟩ :=
    bankInheritedSuccessPairOfInFlight
      ring z.val hAligned e hSuccess
  exact bankInheritedZeroActualPairFreshPayer
    ring hbank z hzero seed pre hi e atoms p hc hw

/-- This is the exact MISSING L10 leaf, isolated as a Prop rather
than as an axiom/theorem. A proof must case-split the old ordered
renewalBankPairMemory guards. Pure frame gives equality, reset
acceptance keeps waiting stock, both sends move active stock,
matched returns merge it, transport moves one worker, and
sanitation/collision/timeout delete stock. The two fallback
entrance constructors must be excluded using BankInFlightAligned. -/
def BankInheritedSelectedPairCensus {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ r : RenewalBankReference n,
    BankInFlightAligned ring r →
      ∀ e : Fin n,
        bankInheritedSiteAtomCount
            ((renewalBankNext ring r e).2.sites e) +
          bankInheritedSiteAtomCount
            ((renewalBankNext ring r e).2.sites
              (ring.rightNeighbor e)) ≤
        bankInheritedSiteAtomCount (r.2.sites e) +
          bankInheritedSiteAtomCount
            (r.2.sites (ring.rightNeighbor e))

/-- L10 reduction using the proved global/two-site equivalence
and unconditional reachable-word occupancy. This theorem is
conditional on the explicitly stated selected-pair census. -/
theorem bankInheritedAtomStepLeOfCensus
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hCensus : BankInheritedSelectedPairCensus ring)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (z : BankReferenceState ring hbank)
    (hReplay :
      z.val = rbRun ring (renewalBankStart ring seed) pre)
    (e : Fin n) :
    bankInheritedStateAtomCount ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) ≤
      bankInheritedStateAtomCount ring hbank z := by
  have hAligned : BankInFlightAligned ring z.val := by
    rw [hReplay]
    exact bankInFlightAlignedWord ring hn seed hbank pre
  exact
    (bankInheritedStateAtomCountLeIffPair
      ring (by omega) hbank z e).2
      (hCensus z.val hAligned e)

/-- Once the exact local census is provided, atom count is
nonincreasing over EVERY suffix of an actual BANK seed replay. -/
theorem bankInheritedAtomWordLeOfCensus
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hCensus : BankInheritedSelectedPairCensus ring)
    (seed : RootedSeed ring) :
    ∀ (pre : List (Fin n))
      (z : BankReferenceState ring hbank)
      (word : List (Fin n)),
      z.val = rbRun ring (renewalBankStart ring seed) pre →
      bankInheritedStateAtomCount ring hbank
          (bankValidAuthorityRun ring hbank z word) ≤
        bankInheritedStateAtomCount ring hbank z := by
  intro pre z word
  induction word generalizing pre z with
  | nil =>
      intro _
      exact Nat.le_refl _
  | cons e tail ih =>
      intro hReplay
      have hReplayNext :=
        bankInheritedReferenceStepReplay
          ring hbank seed pre z hReplay e
      have hTail :=
        ih (pre ++ [e])
          ((bankValidRootedReferenceData ring hbank).referenceNext z e)
          hReplayNext
      have hHead :=
        bankInheritedAtomStepLeOfCensus
          ring hn hbank hCensus seed pre z hReplay e
      change
        bankInheritedStateAtomCount ring hbank
          (bankValidAuthorityRun ring hbank
            ((bankValidRootedReferenceData ring hbank).referenceNext z e)
            tail) ≤
          bankInheritedStateAtomCount ring hbank z
      exact Nat.le_trans hTail hHead

/-- The precise L11 safety implication requires only zero stock
on all suffixes. It does not require the stronger numerical L10
inequality if that absorption property is obtained another way. -/
theorem bankInheritedZeroExtinctOfZeroSuffixes
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (z : BankReferenceState ring hbank)
    (hReplay :
      z.val = rbRun ring (renewalBankStart ring seed) pre)
    (hSuffixZero :
      ∀ word : List (Fin n),
        bankInheritedStateAtomCount ring hbank
          (bankValidAuthorityRun ring hbank z word) = 0) :
    InheritedAuthorityExtinct ring hbank z := by
  intro word
  have hReplaySuffix :
      (bankValidAuthorityRun ring hbank z word).val =
        rbRun ring (renewalBankStart ring seed) (pre ++ word) := by
    rw [bankInheritedAuthorityRunReplay, hReplay, rbRunAppend]
  exact bankInheritedZeroFreshPayerOfReplay
    ring hn hbank seed (pre ++ word)
    (bankValidAuthorityRun ring hbank z word)
    hReplaySuffix (hSuffixZero word)

/-- L11 with L10's exact unproved local leaf made explicit.
Neither ReceiptInv nor in-flight alignment is left as an input:
both are instantiated for every appended scheduler word. -/
theorem bankInheritedZeroExtinctOfCensus
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hCensus : BankInheritedSelectedPairCensus ring)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (z : BankReferenceState ring hbank)
    (hReplay :
      z.val = rbRun ring (renewalBankStart ring seed) pre)
    (hzero :
      bankInheritedStateAtomCount ring hbank z = 0) :
    InheritedAuthorityExtinct ring hbank z := by
  apply bankInheritedZeroExtinctOfZeroSuffixes
    ring hn hbank seed pre z hReplay
  intro word
  have hle :=
    bankInheritedAtomWordLeOfCensus
      ring hn hbank hCensus seed pre z word hReplay
  rw [hzero] at hle
  omega

/-- The actual valid-reference seed replay, usable for stating
the cost target without inventing a new reference process. -/
def bankInheritedFromSeedRun
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (word : List (Fin n)) :
    BankReferenceState ring hbank :=
  bankValidAuthorityRun ring hbank
    ((bankValidRootedReferenceData ring hbank).referenceStart seed)
    word

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInheritedReferenceStepReplay
#print axioms L3.RenewalReferenceClock.bankInheritedZeroFreshPayerOfReplay
#print axioms L3.RenewalReferenceClock.bankInheritedAtomWordLeOfCensus
#print axioms L3.RenewalReferenceClock.bankInheritedZeroExtinctOfCensus

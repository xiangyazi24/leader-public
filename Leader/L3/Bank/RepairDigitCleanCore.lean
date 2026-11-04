import Leader.L3.Bank.RepairDigitClean
import Leader.L3.Bank.RepairDigitBlockEntry

/-!
Clean R10c, suffix after the boundary stage.

The same masked BANK reference successor is used throughout.
The boundary cut is strengthened by the actual gone-cut ancestry
required by the installed first-zero theorem, and all three later
cuts retain the already earned grant-drain invariant.

The comparison pre-drain is the forward-reachable closure of the
actual comparison-receipt cut, not an arbitrary "all is good" state.
It is closed and FIRE-disabled.  The comparison clock, writer/both-
lane receipts, identity proposals, and clean-origin generated
digit membership at zero dirty are not asserted without producers.

Only the clock theorems below are scoped to t <= 17.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Concrete successor-closed pre-drain: a genuine comparison
receipt on a grant-drained BANK state, followed by zero or more
physical BANK steps.  Consumer: bankCleanDigitCorePreDrainClosed,
bankCleanDigitCoreComparisonClock, and bankCleanDigitCoreDirtyRank. -/
def BankCleanDigitCorePreDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank)
    (word : List (Fin n)),
    BankPostInheritedGrantDrain ring hbank start ∧
    BankRepairDigitComparisonCut ring hbank start ∧
    z = word.foldl (bankRepairNext ring hbank) start

/-- The concrete T19/T20 cut family with the grant-drain retained.
The boundary is the *reachable full receipt*, not the unrestricted
old boundary receipt.  Consumer: bankDigitCausalCoreOfBoundary. -/
def bankCleanDigitCoreCuts {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairDigitPreDrainCuts ring hbank where
  boundaryRetired := fun z =>
    BankPostInheritedGrantDrain ring hbank z ∧
    (BankRepairDigitBoundaryRetiredCut ring hbank z ∧
      BankRepairDigitGoneReachable ring hbank z)
  firstBlockZero := fun z =>
    BankPostInheritedGrantDrain ring hbank z ∧
    BankRepairDigitFirstZeroCut ring hbank z
  successorValuesStable := fun z =>
    BankPostInheritedGrantDrain ring hbank z ∧
    BankRepairDigitValuesStableCut ring hbank z

/-- Actual post-inherited grant-drain invariance through an arbitrary
BANK word.  Consumer: bankCleanDigitCorePreDrainDrain and every
charged-stage strengthening below. -/
theorem bankCleanDigitDrainWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (word : List (Fin n))
    (hz : BankPostInheritedGrantDrain ring hbank z) :
    BankPostInheritedGrantDrain ring hbank
      (word.foldl (bankRepairNext ring hbank) z) := by
  induction word generalizing z with
  | nil =>
      exact hz
  | cons e rest ih =>
      exact ih (bankRepairNext ring hbank z e)
        (bankPostInheritedGrantDrainClosed ring hn hbank z hz e)

/-- The comparison-reachable pre-drain is closed under the real
BANK scheduler, without an assumed comparison-cut step lemma.
Consumer: bankDigitCausalCoreOfBoundary. -/
theorem bankCleanDigitCorePreDrainClosed {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairDigitPreDrainClosed ring hbank
      (BankCleanDigitCorePreDrain ring hbank) := by
  rintro z ⟨start, word, hD, hC, rfl⟩ e
  refine ⟨start, word ++ [e], hD, hC, ?_⟩
  rw [List.foldl_append]
  rfl

/-- Every state in the comparison-reachable class is still
grant-drained. Consumer: bankCleanDigitCorePreDrainNoFire. -/
theorem bankCleanDigitCorePreDrainDrain {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankCleanDigitCorePreDrain ring hbank z) :
    BankPostInheritedGrantDrain ring hbank z := by
  obtain ⟨start, word, hD, _hC, rfl⟩ := hz
  exact bankCleanDigitDrainWord ring hn hbank start word hD

/-- The actual BANK physical no-FIRE property throughout the
comparison-reachable pre-drain.  Consumer: the dirty TOP-row
constructor of bankCleanDigitCoreDirtyRank. -/
theorem bankCleanDigitCorePreDrainNoFire {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairDigitNoFireClass ring hbank
      (BankCleanDigitCorePreDrain ring hbank) := by
  intro z hz e
  exact bankRepairCloseNoFireOfDrain ring hbank z
    (bankCleanDigitCorePreDrainDrain ring hn hbank z hz) e

/-- No additional half-unit is charged for carrying the
forward-closed grant-drain receipt through a real BANK first-hit
stage.  Consumer: the first-zero, value-wave and comparison
transport lemmas. -/
theorem bankCleanDigitChargedCarryDrain {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (A Q : BankReferenceState ring hbank → Prop)
    (charge : Nat)
    (hA : ∀ z, A z → BankPostInheritedGrantDrain ring hbank z)
    (hclock : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      A Q charge) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      A (fun z => BankPostInheritedGrantDrain ring hbank z ∧ Q z)
      charge := by
  intro z hz T
  have hstrength := costNumeratorTargetOnClosed
    (bankRepairNext ring hbank)
    (BankPostInheritedGrantDrain ring hbank)
    (fun y => BankPostInheritedGrantDrain ring hbank y ∧ Q y)
    Q
    (fun y hy e =>
      bankPostInheritedGrantDrainClosed ring hn hbank y hy e)
    (fun y hy hq => ⟨hy, hq⟩)
    T z (hA z hz)
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hstrength)
    (hclock z hz T)

/-- T19: the existing first-zero clock works on the strengthened
boundary cut (full boundary receipt AND gone ancestry); the
grant-drain is retained at no extra charge.  This fact does NOT
hold merely by invoking the old theorem on the weaker full
boundary cut.  Consumer: bankDigitCausalCoreOfBoundary. -/
theorem bankCleanDigitCoreFirstZeroClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (bankCleanDigitCoreCuts ring hbank).boundaryRetired
      (bankCleanDigitCoreCuts ring hbank).firstBlockZero
      (bankRepairDigitFirstZeroMicroCharge n) := by
  have hraw : BankRepairDigitChargedStage
      (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        (BankRepairDigitBoundaryRetiredCut ring hbank z ∧
          BankRepairDigitGoneReachable ring hbank z))
      (BankRepairDigitFirstZeroCut ring hbank)
      (bankRepairDigitFirstZeroMicroCharge n) :=
    bankRepairDigitChargedWeaken
      (bankRepairNext ring hbank)
      (fun z => BankRepairDigitBoundaryRetiredCut ring hbank z ∧
        BankRepairDigitGoneReachable ring hbank z)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        (BankRepairDigitBoundaryRetiredCut ring hbank z ∧
          BankRepairDigitGoneReachable ring hbank z))
      (fun z => BankRepairDigitFirstZeroCut ring hbank z ∧
        BankRepairDigitLeaderReceipt ring hbank z)
      (BankRepairDigitFirstZeroCut ring hbank)
      (bankRepairDigitFirstZeroMicroCharge n)
      (fun z hz => hz.2) (fun z hz => hz.1)
      (bankRepairDigitFirstZeroKeepStage ring hn hbank)
  exact bankCleanDigitChargedCarryDrain ring hn hbank
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      (BankRepairDigitBoundaryRetiredCut ring hbank z ∧
        BankRepairDigitGoneReachable ring hbank z))
    (BankRepairDigitFirstZeroCut ring hbank)
    (bankRepairDigitFirstZeroMicroCharge n)
    (fun z hz => hz.1) hraw

/-- T34/T35: the already-proved block-stage arithmetic and
same-BANK projection give the 200 n^2 value-wave clock on the
clean receipt-preserving cuts, CONDITIONAL on the genuine
first-zero pair pins and the BOTH-lane/ordered receipts
conversion.  Consumer: bankDigitCausalCoreOfBoundary. -/
theorem bankCleanDigitCoreValueWaveClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpairs : L3.BlockEntry.FirstZeroPairs ring hbank)
    (hclose : L3.ValueWaveClose.ReceiptsClose ring hbank) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (bankCleanDigitCoreCuts ring hbank).firstBlockZero
      (bankCleanDigitCoreCuts ring hbank).successorValuesStable
      (bankRepairDigitValueWaveMicroCharge n) := by
  have hclock : BankRepairDigitValueWaveClock ring hbank :=
    L3.BlockEntry.bankRepairDigitValueWaveClockOfPairs
      ring hbank hn hpairs hclose
  have hraw : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairDigitFirstZeroCut ring hbank z)
      (BankRepairDigitValuesStableCut ring hbank)
      (bankRepairDigitValueWaveMicroCharge n) :=
    bankRepairDigitChargedWeaken (bankRepairNext ring hbank)
      (BankRepairDigitFirstZeroCut ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairDigitFirstZeroCut ring hbank z)
      (BankRepairDigitValuesStableCut ring hbank)
      (BankRepairDigitValuesStableCut ring hbank)
      (bankRepairDigitValueWaveMicroCharge n)
      (fun z hz => hz.2) (fun z hz => hz) hclock
  exact bankCleanDigitChargedCarryDrain ring hn hbank
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairDigitFirstZeroCut ring hbank z)
    (BankRepairDigitValuesStableCut ring hbank)
    (bankRepairDigitValueWaveMicroCharge n)
    (fun z hz => hz.1) hraw

/-- T20 comparison: if the original restarted comparison clock
is actually supplied, its genuine cut can be weakened to the
forward-closed pre-drain while retaining the grant-drain.
No AcceptedWord-to-CleanWord coercion is used here.
Consumer: bankDigitCausalCoreOfBoundary. -/
theorem bankCleanDigitCoreComparisonClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcompare : BankRepairDigitComparisonClock ring hbank) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (bankCleanDigitCoreCuts ring hbank).successorValuesStable
      (BankCleanDigitCorePreDrain ring hbank)
      (bankRepairDigitComparisonMicroCharge n) := by
  have hraw : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairDigitValuesStableCut ring hbank z)
      (BankRepairDigitComparisonCut ring hbank)
      (bankRepairDigitComparisonMicroCharge n) :=
    bankRepairDigitChargedWeaken (bankRepairNext ring hbank)
      (BankRepairDigitValuesStableCut ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairDigitValuesStableCut ring hbank z)
      (BankRepairDigitComparisonCut ring hbank)
      (BankRepairDigitComparisonCut ring hbank)
      (bankRepairDigitComparisonMicroCharge n)
      (fun z hz => hz.2) (fun z hz => hz) hcompare
  have hkeep : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairDigitValuesStableCut ring hbank z)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairDigitComparisonCut ring hbank z)
      (bankRepairDigitComparisonMicroCharge n) :=
    bankCleanDigitChargedCarryDrain ring hn hbank
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairDigitValuesStableCut ring hbank z)
      (BankRepairDigitComparisonCut ring hbank)
      (bankRepairDigitComparisonMicroCharge n)
      (fun z hz => hz.1) hraw
  exact bankRepairDigitChargedWeaken (bankRepairNext ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairDigitValuesStableCut ring hbank z)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairDigitValuesStableCut ring hbank z)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairDigitComparisonCut ring hbank z)
    (BankCleanDigitCorePreDrain ring hbank)
    (bankRepairDigitComparisonMicroCharge n)
    (fun z hz => hz)
    (fun z hz => ⟨z, [], hz.1, hz.2, rfl⟩)
    hkeep

/-- The literal sum of zero dirty bits is zero; this is a
physical TOP-row fact, not a generated-history acceptance.
Consumer: bankCleanDigitCoreDirtyRank. -/
private theorem bankCleanDigitCoreZeroCount {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hzero : ∀ i : Fin n, (z.val.1 i).topDirty = false) :
    bankRepairDigitDirtyCount ring hbank z = 0 := by
  unfold bankRepairDigitDirtyCount
  have hsum := ofFn_sum_eq
    (fun i : Fin n => bankRepairDigitDirtyUnit (z.val.1 i).topDirty)
    (fun _ : Fin n => 0)
    (by intro i; simp [bankRepairDigitDirtyUnit, hzero i])
  rw [hsum, ofFn_sum_const]
  omega

/-- E.G36/T20: the real incoming edge into the leftmost dirty
site gives a nominated-edge rank on the clean comparison-reachable
class.  Identity proposals and clean-origin generated acceptance
at zero dirty are the two substantive external row/history facts.
Consumer: bankDigitCausalCoreOfBoundary. -/
theorem bankCleanDigitCoreDirtyRank {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hidentity : BankRepairDigitIdentityProposals ring hbank
      (BankCleanDigitCorePreDrain ring hbank))
    (haccept : ∀ z, BankCleanDigitCorePreDrain ring hbank z →
      bankRepairDigitDirtyCount ring hbank z = 0 →
      BankCleanDigit ring hbank z) :
    ∃ (rank : BankReferenceState ring hbank → Nat)
      (chosen : BankReferenceState ring hbank → Fin n),
      (∀ z, BankCleanDigitCorePreDrain ring hbank z → rank z ≤ n) ∧
      (∀ z, BankCleanDigitCorePreDrain ring hbank z →
        rank z = 0 → BankCleanDigit ring hbank z) ∧
      (∀ z, BankCleanDigitCorePreDrain ring hbank z →
        ¬ BankCleanDigit ring hbank z →
        rank (bankRepairNext ring hbank z (chosen z)) + 1 ≤ rank z) ∧
      (∀ z, BankCleanDigitCorePreDrain ring hbank z →
        ¬ BankCleanDigit ring hbank z →
        ∀ e : Fin n,
          rank (bankRepairNext ring hbank z e) ≤ rank z) := by
  classical
  have hrows : BankRepairDigitDirtyClearRows ring hbank
      (BankCleanDigitCorePreDrain ring hbank) :=
    bankRepairDigitDirtyRowsOfNoFireIdentity ring hn hbank
      (BankCleanDigitCorePreDrain ring hbank)
      (bankCleanDigitCorePreDrainNoFire ring hn hbank)
      hidentity
  refine ⟨bankRepairDigitDirtyCount ring hbank,
    bankRepairDigitIntoLeftmostDirty ring hbank, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact bankRepairDigitDirtyCountCap ring hbank z
  · intro z hz hzero
    exact haccept z hz hzero
  · intro z hz hnot
    have hex : ∃ i : Fin n, (z.val.1 i).topDirty = true := by
      by_cases hdirty : ∃ i : Fin n, (z.val.1 i).topDirty = true
      · exact hdirty
      · have hclean : ∀ i : Fin n, (z.val.1 i).topDirty = false := by
          intro i
          cases hb : (z.val.1 i).topDirty with
          | false => rfl
          | true => exact False.elim (hdirty ⟨i, hb⟩)
        have hzero := bankCleanDigitCoreZeroCount ring hbank z hclean
        exact False.elim (hnot (haccept z hz hzero))
    have hchosen := (bankRepairDigitLeftmostDirtySpec ring hbank z hex).1
    change bankRepairDigitDirtyCount ring hbank
        (bankRepairNext ring hbank z
          (bankRepairDigitIntoLeftmostDirty ring hbank z)) + 1 ≤
      bankRepairDigitDirtyCount ring hbank z
    unfold bankRepairDigitIntoLeftmostDirty
    exact bankRepairDigitDirtyCountDrop ring hbank
      (BankCleanDigitCorePreDrain ring hbank) hrows
      z hz (bankRepairDigitLeftmostDirtySite ring hbank z) hchosen
  · intro z hz hnot e
    exact bankRepairDigitDirtyCountNonincreasing ring hbank
      (BankCleanDigitCorePreDrain ring hbank) hrows z hz e

/-- Conditional R10c core assembly.  It is NOT a boundary-only
producer: the three independent unproved receipt/row inputs below
remain explicit.  If those inputs are supplied, the boundary
clock is the only remaining conjunct of BankDigitCausalCore.
Consumer: bankCleanDigitHalfOnDrainOfCausalCore. -/
theorem bankDigitCausalCoreOfBoundary {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpairs : L3.BlockEntry.FirstZeroPairs ring hbank)
    (hreceipts : L3.ValueWaveClose.ReceiptsClose ring hbank)
    (hcomparison : BankRepairDigitComparisonClock ring hbank)
    (hidentity : BankRepairDigitIdentityProposals ring hbank
      (BankCleanDigitCorePreDrain ring hbank))
    (hcleanZero : ∀ z, BankCleanDigitCorePreDrain ring hbank z →
      bankRepairDigitDirtyCount ring hbank z = 0 →
      BankCleanDigit ring hbank z)
    (hboundary : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankCleanRFold ring hbank z)
      (bankCleanDigitCoreCuts ring hbank).boundaryRetired
      (bankRepairDigitBoundaryMicroCharge n)) :
    BankDigitCausalCore ring hbank
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankCleanRFold ring hbank z)
      (BankCleanDigitCorePreDrain ring hbank)
      (BankCleanDigit ring hbank)
      (bankCleanDigitCoreCuts ring hbank) := by
  obtain ⟨rank, chosen, hcap, hzero, hdrop, hnoninc⟩ :=
    bankCleanDigitCoreDirtyRank ring hn hbank hidentity hcleanZero
  exact ⟨hboundary,
    bankCleanDigitCoreFirstZeroClock ring hn hbank,
    bankCleanDigitCoreValueWaveClock ring hn hbank hpairs hreceipts,
    bankCleanDigitCoreComparisonClock ring hn hbank hcomparison,
    bankCleanDigitCorePreDrainClosed ring hbank,
    rank, chosen, hcap, hzero, hdrop, hnoninc⟩

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-!
E.G35/E.G36: on a grant-drained physical BANK run, a fixed clean
word root, correct digit values, and QDigit all persist. This is
the concrete successor lemma needed by the two clean R10c gaps.
It does not claim these three facts hold at the comparison cut.
-/

/-- Consumer: bankCleanDigitCoreSafeValuesOfComparisonCertificate.
The projected D and W successors are both the real masked BANK
successors, rather than independent observer scheduler steps. -/
theorem bankCleanDigitCoreSafeValuesWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank z →
      CleanWordAtRoot ring root (piW z.val.1) →
      AcceptedReceipts.DigitValuesCorrect ring root
        (AcceptedReceipts.digitValueView (piD z.val.1)) →
      AcceptedReceipts.QDigit ring (piD z.val.1) →
      CleanWordAtRoot ring root
        (piW (word.foldl (bankRepairNext ring hbank) z).val.1) ∧
      AcceptedReceipts.DigitValuesCorrect ring root
        (AcceptedReceipts.digitValueView
          (piD (word.foldl (bankRepairNext ring hbank) z).val.1)) ∧
      AcceptedReceipts.QDigit ring
        (piD (word.foldl (bankRepairNext ring hbank) z).val.1) := by
  induction word with
  | nil =>
      intro z hD hW hV hQ
      exact ⟨hW, hV, hQ⟩
  | cons e rest ih =>
      intro z hD hW hV hQ
      have hfire := bankRepairCloseNoFireOfDrain ring hbank z hD e
      have hprojectD :=
        bankRepairDigitMaskedProjectionOfNoFire ring hbank z e hfire
      have hprojectW :=
        bankRepairDigitWordProjectionOfNoFire ring hbank z e hfire
      have hD' :=
        bankPostInheritedGrantDrainClosed ring hn hbank z hD e
      have hW' : CleanWordAtRoot ring root
          (piW (bankRepairNext ring hbank z e).val.1) := by
        rw [hprojectW]
        exact cleanWordRootPhiStep (by omega : 3 ≤ n)
          ring root (piW z.val.1) e hW
      have hV' : AcceptedReceipts.DigitValuesCorrect ring root
          (AcceptedReceipts.digitValueView
            (piD (bankRepairNext ring hbank z e).val.1)) := by
        rw [hprojectD]
        rw [AcceptedReceipts.digitValueView_phiD
          ring (piD z.val.1) hQ e]
        exact hV
      have hQ' : AcceptedReceipts.QDigit ring
          (piD (bankRepairNext ring hbank z e).val.1) := by
        rw [hprojectD]
        exact (AcceptedReceipts.qdigit_step ring (piD z.val.1) hQ e).2
      exact ih (bankRepairNext ring hbank z e) hD' hW' hV' hQ'

/-- E.G12: QDigit at one physical pre-drain state rules out
every visible digit change on its next masked BANK edge.
Consumer: bankCleanDigitCoreIdentityFromComparisonCertificate. -/
theorem bankCleanDigitCoreIdentityOnSafeState {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankCleanDigitCorePreDrain ring hbank z)
    (hQ : AcceptedReceipts.QDigit ring (piD z.val.1)) :
    ∀ (e i : Fin n),
      ((bankRepairNext ring hbank z e).val.1 i).d =
        (z.val.1 i).d := by
  intro e i
  have hproject :=
    bankRepairDigitMaskedProjectionOfNoFire ring hbank z e
      (bankCleanDigitCorePreDrainNoFire ring hn hbank z hz e)
  have hpoint := congrArg
    (fun p : Fin n → ProjD (compileAdvice (ceilLogTwo n)) => (p i).top.d)
    hproject
  change ((bankRepairNext ring hbank z e).val.1 i).d =
    ((phiD ring (piD z.val.1) e) i).top.d at hpoint
  have hvisible := AcceptedReceipts.qdigit_visible_fixed
    ring (piD z.val.1) hQ e i
  have hvalue := congrArg
    (fun v : Bool × Bool × Fin (compileAdvice (ceilLogTwo n)).topA =>
      v.2.2) hvisible
  change ((phiD ring (piD z.val.1) e) i).top.d =
    (z.val.1 i).d at hvalue
  exact hpoint.trans hvalue

/-- A zero physical dirty-count forces every actual site bit
to be false, without assuming a generated digit observer.
Consumer: bankCleanDigitCoreZeroOfSafeValues. -/
theorem bankCleanDigitCoreNoDirtyOfZero {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hzero : bankRepairDigitDirtyCount ring hbank z = 0) :
    ∀ i : Fin n, (z.val.1 i).topDirty = false := by
  have hterm : ∀ {m : Nat} (f : Fin m → Nat) (i : Fin m),
      f i ≤ (List.ofFn f).sum := by
    intro m
    induction m with
    | zero =>
        intro f i
        exact i.elim0
    | succ m ih =>
        intro f i
        rw [List.ofFn_succ, List.sum_cons]
        cases i using Fin.cases with
        | zero =>
            exact Nat.le_add_right _ _
        | succ k =>
            have hle := ih (fun j : Fin m => f j.succ) k
            omega
  intro i
  have hbound := hterm
    (fun j : Fin n =>
      bankRepairDigitDirtyUnit (z.val.1 j).topDirty) i
  change bankRepairDigitDirtyUnit (z.val.1 i).topDirty ≤
    bankRepairDigitDirtyCount ring hbank z at hbound
  rw [hzero] at hbound
  cases h : (z.val.1 i).topDirty with
  | false =>
      rfl
  | true =>
      simp [bankRepairDigitDirtyUnit] at hbound
      rw [h] at hbound
      exact hbound

/-- E.G36: a CURRENT clean-root S_D witness, plus the literal
zero-dirty count, constructs BarredDigitClass with an EMPTY
generated word. There is no need to invent a historical receipt
once S_D and its QDigit future-safety field are established.
Consumer: bankCleanDigitCoreZeroFromComparisonCertificate. -/
theorem bankCleanDigitCoreZeroOfSafeValues {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (root : Fin n)
    (hW : CleanWordAtRoot ring root (piW z.val.1))
    (hV : AcceptedReceipts.DigitValuesCorrect ring root
      (AcceptedReceipts.digitValueView (piD z.val.1)))
    (hQ : AcceptedReceipts.QDigit ring (piD z.val.1))
    (hzero : bankRepairDigitDirtyCount ring hbank z = 0) :
    BankCleanDigit ring hbank z := by
  have hword : CleanWordAtRoot ring root
      (AcceptedReceipts.wordProjection (piD z.val.1)) := by
    change CleanWordAtRoot ring root (piW z.val.1)
    exact hW
  have hgood : AcceptedReceipts.WeakDigitGood ring
      (CleanWordAtRoot ring) (piD z.val.1) := by
    refine ⟨⟨root, hword, hV⟩, ?_, hQ⟩
    intro i
    change (z.val.1 i).topDirty = false
    exact bankCleanDigitCoreNoDirtyOfZero ring hbank z hzero i
  change AcceptedReceipts.BarredDigitClass ring
    (CleanWordAtRoot ring) (piD z.val.1)
  refine ⟨piD z.val.1, .live (piD z.val.1) true,
    [], .live (piD z.val.1) true, ?_, ?_, ?_⟩
  · exact ⟨⟨root, hword⟩, Or.inl ⟨hgood, rfl⟩⟩
  · exact BlockA.Run.empty
  · exact ⟨rfl, rfl, hgood⟩

/-- T20-to-E.G35 transport. A single CURRENT comparison-entry
certificate is propagated over the whole actual comparison-reachable
pre-drain. The missing certificate is NOT obtained merely from
the historical old-origin ComparisonCut definition.
Consumers: the next two clean R10c lemmas. -/
theorem bankCleanDigitCoreSafeValuesOfComparisonCertificate {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcertificate : ∀ start : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank start →
      BankRepairDigitComparisonCut ring hbank start →
      ∃ root : Fin n,
        CleanWordAtRoot ring root (piW start.val.1) ∧
        AcceptedReceipts.DigitValuesCorrect ring root
          (AcceptedReceipts.digitValueView (piD start.val.1)) ∧
        AcceptedReceipts.QDigit ring (piD start.val.1))
    (z : BankReferenceState ring hbank)
    (hz : BankCleanDigitCorePreDrain ring hbank z) :
    ∃ root : Fin n,
      CleanWordAtRoot ring root (piW z.val.1) ∧
      AcceptedReceipts.DigitValuesCorrect ring root
        (AcceptedReceipts.digitValueView (piD z.val.1)) ∧
      AcceptedReceipts.QDigit ring (piD z.val.1) := by
  obtain ⟨start, word, hD, hC, rfl⟩ := hz
  obtain ⟨root, hW, hV, hQ⟩ := hcertificate start hD hC
  obtain ⟨hW', hV', hQ'⟩ :=
    bankCleanDigitCoreSafeValuesWord ring hn hbank root word
      start hD hW hV hQ
  exact ⟨root, hW', hV', hQ'⟩

/-- E.G12: the source's current safe comparison certificate
produces the requested BankRepairDigitIdentityProposals property
on the entire concrete pre-drain. It is CONDITIONAL on the
comparison-entry certificate, not a proof of that certificate.
Consumer: bankDigitCausalCoreOfOldCoreWithComparisonCertificate. -/
theorem bankCleanDigitCoreIdentityFromComparisonCertificate {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcertificate : ∀ start : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank start →
      BankRepairDigitComparisonCut ring hbank start →
      ∃ root : Fin n,
        CleanWordAtRoot ring root (piW start.val.1) ∧
        AcceptedReceipts.DigitValuesCorrect ring root
          (AcceptedReceipts.digitValueView (piD start.val.1)) ∧
        AcceptedReceipts.QDigit ring (piD start.val.1)) :
    BankRepairDigitIdentityProposals ring hbank
      (BankCleanDigitCorePreDrain ring hbank) := by
  intro z hz e i
  obtain ⟨root, hW, hV, hQ⟩ :=
    bankCleanDigitCoreSafeValuesOfComparisonCertificate
      ring hn hbank hcertificate z hz
  exact bankCleanDigitCoreIdentityOnSafeState
    ring hn hbank z hz hQ e i

/-- E.G36: correct values and future-safe current comparison
origin, together with a zero dirty-count, give the actual
clean-origin barred generated class.
Consumer: bankDigitCausalCoreOfOldCoreWithComparisonCertificate. -/
theorem bankCleanDigitCoreZeroFromComparisonCertificate {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcertificate : ∀ start : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank start →
      BankRepairDigitComparisonCut ring hbank start →
      ∃ root : Fin n,
        CleanWordAtRoot ring root (piW start.val.1) ∧
        AcceptedReceipts.DigitValuesCorrect ring root
          (AcceptedReceipts.digitValueView (piD start.val.1)) ∧
        AcceptedReceipts.QDigit ring (piD start.val.1))
    (z : BankReferenceState ring hbank)
    (hz : BankCleanDigitCorePreDrain ring hbank z)
    (hzero : bankRepairDigitDirtyCount ring hbank z = 0) :
    BankCleanDigit ring hbank z := by
  obtain ⟨root, hW, hV, hQ⟩ :=
    bankCleanDigitCoreSafeValuesOfComparisonCertificate
      ring hn hbank hcertificate z hz
  exact bankCleanDigitCoreZeroOfSafeValues
    ring hbank z root hW hV hQ hzero

/-- Conditional consumer assembly. This removes both independent
clean-specific premises of bankDigitCausalCoreOfBoundary in favor
of ONE concrete source certificate at a comparison-receipt cut.
The theorem with ONLY the four old R10c premises remains OPEN.
Consumer: bankCleanDigitHalfOnDrainOfCausalCore. -/
theorem bankDigitCausalCoreOfOldCoreWithComparisonCertificate {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcertificate : ∀ start : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank start →
      BankRepairDigitComparisonCut ring hbank start →
      ∃ root : Fin n,
        CleanWordAtRoot ring root (piW start.val.1) ∧
        AcceptedReceipts.DigitValuesCorrect ring root
          (AcceptedReceipts.digitValueView (piD start.val.1)) ∧
        AcceptedReceipts.QDigit ring (piD start.val.1))
    (hpairs : L3.BlockEntry.FirstZeroPairs ring hbank)
    (hreceipts : L3.ValueWaveClose.ReceiptsClose ring hbank)
    (hcomparison : BankRepairDigitComparisonClock ring hbank)
    (hboundary : BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankCleanRFold ring hbank z)
      (bankCleanDigitCoreCuts ring hbank).boundaryRetired
      (bankRepairDigitBoundaryMicroCharge n)) :
    BankDigitCausalCore ring hbank
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankCleanRFold ring hbank z)
      (BankCleanDigitCorePreDrain ring hbank)
      (BankCleanDigit ring hbank)
      (bankCleanDigitCoreCuts ring hbank) := by
  exact bankDigitCausalCoreOfBoundary ring hn hbank
    hpairs hreceipts hcomparison
    (bankCleanDigitCoreIdentityFromComparisonCertificate
      ring hn hbank hcertificate)
    (fun z hz hzero =>
      bankCleanDigitCoreZeroFromComparisonCertificate
        ring hn hbank hcertificate z hz hzero)
    hboundary

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankCleanDigitDrainWord
#print axioms L3.RenewalReferenceClock.bankCleanDigitCorePreDrainClosed
#print axioms L3.RenewalReferenceClock.bankCleanDigitCorePreDrainDrain
#print axioms L3.RenewalReferenceClock.bankCleanDigitCorePreDrainNoFire
#print axioms L3.RenewalReferenceClock.bankCleanDigitChargedCarryDrain
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreFirstZeroClock
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreValueWaveClock
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreComparisonClock
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreDirtyRank
#print axioms L3.RenewalReferenceClock.bankDigitCausalCoreOfBoundary
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreSafeValuesWord
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreIdentityOnSafeState
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreNoDirtyOfZero
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreZeroOfSafeValues
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreSafeValuesOfComparisonCertificate
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreIdentityFromComparisonCertificate
#print axioms L3.RenewalReferenceClock.bankCleanDigitCoreZeroFromComparisonCertificate
#print axioms L3.RenewalReferenceClock.bankDigitCausalCoreOfOldCoreWithComparisonCertificate

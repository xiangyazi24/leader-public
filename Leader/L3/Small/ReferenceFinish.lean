import Leader.L3.Small.RenewalNative
import Leader.L3.Grant.DrainStageTransfer

/-!
SMALL reference prepared-to-generated finish: source-level audit.

The current native-only prepared
predicate is weaker than the paper's same-history native/candidate
handoff. A literal five-site reference witness below refutes
promoting that native-only cut directly to EmptyCandidates.

The final stage and clock are CONDITIONAL on two separately named
finite-horizon expected-time obligations. No unconditional
generated-finish or ReferenceClock theorem is claimed.
-/

namespace L3.SmallReferenceFinish

open L3
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.GrantDrainEntrance
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The PAPER entrance requires native and candidate factors at
the SAME reference cut. Existing native preparation alone does
not supply the last two conjuncts. -/
def smallFinishPaperPrepared {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  smallReferenceNativePrepared ring r ∧
  C_native ring (smallReferenceNativeView r) ∧
  EmptyCandidates (fun i => NativeCand.ofAgent (r.1 i))

/-- Literal physical prepared-core transport once the missing
candidate and native-clean facts have actually been obtained. -/
theorem smallFinishPaperPreparedCore {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (h : smallFinishPaperPrepared ring r) :
    ReferencePreparationPreparedCore ring r.1 := by
  exact smallReferenceNativePreparedCoreOfCleanCandidates
    ring r h.1 h.2.1 h.2.2

/-- Native prepared lies inside the proven OLD-grant-free class. -/
theorem smallFinishNativePreparedGrantFree {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (h : smallReferenceNativePrepared ring r) :
    NativeLiftGrantFree r.1 := by
  exact h.1.1.2.2

/-- Every next native service is exactly birth-free nativeE.
The reference SMALL success mask affects no native coordinate. -/
theorem smallFinishNativePreparedNativeStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (h : smallReferenceNativePrepared ring r)
    (e : Fin n) :
    smallReferenceNativeView (renewalSmallNext ring r e) =
      nativeE ring (smallReferenceNativeView r) e := by
  exact smallReferenceNativeRootedStep
    ring (by omega : 3 ≤ n) r h.1 e

/-- Every production SMALL q=3..79 has at least six units of
unused finish-stage allowance. This does NOT certify either
paper stopping-time claim needed to spend those units. -/
theorem smallFinishRateHasSixReserve
    (q : Nat) (hthree : 3 ≤ q)
    (hsmall : (compileAdvice q).useSmall = true) :
    6 ≤ headlineReferenceFinishRate q := by
  have hqstar : q ≤ qStar := by
    have he :
        (compileAdvice q).useSmall = decide (q ≤ qStar) := rfl
    rw [he] at hsmall
    exact of_decide_eq_true hsmall
  have hlt : q < 80 := by
    have hstar : qStar = 79 := rfl
    omega
  have hcheck :
      ∀ i : Fin 80, 3 ≤ i.val →
        6 ≤ headlineReferenceFinishRate i.val := by
    decide +kernel
  exact hcheck ⟨q, hlt⟩ hthree

/-- The smallest actual SMALL witness, n=5 and q=3, uses K=20
and has finish allowance 3224. -/
theorem smallFinishLowestThreshold :
    (compileAdvice 3).K = 20 := by
  decide

theorem smallFinishLowestReserve :
    headlineReferenceFinishRate 3 = 3224 := by
  decide

/-- Source SMALL rows on genuinely closed, small inputs. -/
private def smallFinishThresholdSource :
    Agent (compileAdvice 3) :=
  { Agent.blank (compileAdvice 3) with
    small := Small.RUN ⟨19, by decide⟩ }

private def smallFinishInvalidSource :
    Agent (compileAdvice 3) :=
  { Agent.blank (compileAdvice 3) with
    small := Small.RUN ⟨20, by decide⟩ }

private def smallFinishSpentResponder :
    Agent (compileAdvice 3) :=
  { Agent.blank (compileAdvice 3) with small := .SPENT }

theorem smallFinishLiteralThresholdRow :
    smallPair smallFinishThresholdSource smallFinishSpentResponder
      (compileAdvice 3).K =
      (Small.SPENT, smallRunZero, true) := by
  rfl

theorem smallFinishLiteralSanitizeRow :
    smallPair smallFinishInvalidSource smallFinishSpentResponder
      (compileAdvice 3).K =
      (smallRunZero, smallRunZero, false) := by
  rfl

/-! First failed shortcut: native-ready does not imply
candidate-zero at the SAME cut. This is an actual SMALL reference
step with n=5, memory all true, and all physical SMALL fields OFF.
The old physical native/candidate word agrees with the published
ReferencePreparationCandidate first-native-hit witness. -/

private def smallFinishWitnessRing : DirectedRing 5 :=
  ⟨by decide⟩

private def smallFinishWitnessPhysical : HeadlineConfiguration 5 :=
  fun i =>
    { Agent.blank (compileAdvice (ceilLogTwo 5)) with
      l := (i.val == 0)
      sh := (i.val == 0)
      sg := !(i.val == 0)
      C := (i.val == 2) }

private def smallFinishWitnessStart : RenewalSmallReference 5 :=
  (smallFinishWitnessPhysical, fun _ => true)

private theorem smallFinishWitnessGrantFree :
    NativeLiftGrantFree smallFinishWitnessPhysical := by
  intro i
  rfl

private theorem smallFinishWitnessNoCut :
    renewalSmallCut smallFinishWitnessRing
      smallFinishWitnessStart.1 smallFinishWitnessStart.2
      (0 : Fin 5) = false := by
  rfl

private theorem smallFinishWitnessPhysicalStep :
    (renewalSmallNext smallFinishWitnessRing
      smallFinishWitnessStart (0 : Fin 5)).1 =
    headlinePhysicalNext smallFinishWitnessRing
      smallFinishWitnessPhysical (0 : Fin 5) := by
  exact renewalSmallPhysicalBeforeCut
    smallFinishWitnessRing smallFinishWitnessStart
    (0 : Fin 5) smallFinishWitnessNoCut

private theorem smallFinishWitnessNativeRooted :
    smallReferenceNativeRooted
      smallFinishWitnessRing smallFinishWitnessStart := by
  constructor
  · refine ⟨?_, ?_, smallFinishWitnessGrantFree⟩
    · unfold headlineRooted
      decide +kernel
    · intro i
      rfl
  · refine ⟨(0 : Fin 5), ?_⟩
    unfold ReferencePreparationTrail.Rooted
    decide +kernel

/-- After the literal edge 0 -> 1 the native projection has one
leader, no bullet and signals one at all five sites. -/
theorem smallFinishWitnessNativeReady :
    ReferencePreparationNativePreparedAt (0 : Fin 5)
      (smallReferenceNativeView
        (renewalSmallNext smallFinishWitnessRing
          smallFinishWitnessStart (0 : Fin 5))) := by
  rw [smallReferenceNativeFrame
    smallFinishWitnessRing smallFinishWitnessStart (0 : Fin 5)]
  have hfire : NativeLiftNoFireOn
      smallFinishWitnessRing smallFinishWitnessPhysical
      (0 : Fin 5) :=
    (native_lift_no_fire_cut_of_grant_free
      smallFinishWitnessRing smallFinishWitnessPhysical
      smallFinishWitnessGrantFree) (0 : Fin 5)
  have hphysical := native_lift_no_fire_step
    (by decide : 3 ≤ 5)
    smallFinishWitnessRing smallFinishWitnessPhysical
    (0 : Fin 5) hfire
  have hready : ReferencePreparationNativePreparedAt (0 : Fin 5)
      (nativeE smallFinishWitnessRing
        (nativeProjection smallFinishWitnessPhysical) (0 : Fin 5)) := by
    unfold ReferencePreparationNativePreparedAt
    decide +kernel
  rw [← hphysical] at hready
  exact hready

theorem smallFinishWitnessInNativePrepared :
    smallReferenceNativePrepared smallFinishWitnessRing
      (renewalSmallNext smallFinishWitnessRing
        smallFinishWitnessStart (0 : Fin 5)) := by
  have hsmall :
      (compileAdvice (ceilLogTwo 5)).useSmall = true := by
    decide
  have hroot := smallReferenceNativeRootedClosed
    smallFinishWitnessRing (by decide : 5 ≤ 5) hsmall
    smallFinishWitnessStart smallFinishWitnessNativeRooted
    (0 : Fin 5)
  exact ⟨hroot, (0 : Fin 5), smallFinishWitnessNativeReady⟩

/-- The off-pair site two retains its inherited occupied C record. -/
private theorem smallFinishWitnessCandidateAtTwo :
    ((renewalSmallNext smallFinishWitnessRing
      smallFinishWitnessStart (0 : Fin 5)).1
      (2 : Fin 5)).C = true := by
  rw [smallFinishWitnessPhysicalStep]
  rfl

theorem smallFinishWitnessCandidateNotEmpty :
    ¬ EmptyCandidates
      (fun i : Fin 5 => NativeCand.ofAgent
        ((renewalSmallNext smallFinishWitnessRing
          smallFinishWitnessStart (0 : Fin 5)).1 i)) := by
  intro hempty
  have hzero := congrArg
    (fun c : CPriv => c.C) (hempty (2 : Fin 5))
  change ((renewalSmallNext smallFinishWitnessRing
    smallFinishWitnessStart (0 : Fin 5)).1
    (2 : Fin 5)).C = false at hzero
  rw [smallFinishWitnessCandidateAtTwo] at hzero
  cases hzero

/-- This fails the naive same-cut promotion, not the requested
eventual hitting-time claim or its numerical finish allowance. -/
theorem smallFinishNativePreparedNotPaperPrepared :
    ∃ r : RenewalSmallReference 5,
      smallReferenceNativePrepared smallFinishWitnessRing r ∧
      ¬ smallFinishPaperPrepared smallFinishWitnessRing r := by
  refine ⟨renewalSmallNext smallFinishWitnessRing
    smallFinishWitnessStart (0 : Fin 5),
    smallFinishWitnessInNativePrepared, ?_⟩
  intro h
  exact smallFinishWitnessCandidateNotEmpty h.2.2

/-! The two remaining SAME-SCHEDULER clocks are named in one
open Prop. The first pays a new candidate/native joint handoff
from a native-only prepared cut. The second pays the full
generated repair from that actual strengthened cut. -/

def SmallFinishPaperStages {n : Nat}
    (ring : DirectedRing n) : Prop :=
  (∀ r : RenewalSmallReference n,
    smallReferenceNativePrepared ring r →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (renewalSmallNext ring)
      (smallFinishPaperPrepared ring) r
      ((6 * n ^ 2 : Nat) : Rat)) ∧
  (∀ r : RenewalSmallReference n,
    smallFinishPaperPrepared ring r →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (renewalSmallNext ring)
      (renewalSmallStop ring) r
      (((headlineReferenceFinishRate (ceilLogTwo n) - 6) *
        n ^ 2 : Nat) : Rat))

/-- Use the existing ceilLogTwo specification rather than an
unverified substitution of a SMALL advice integer. -/
private theorem smallFinishAdviceAtLeastThree (n : Nat)
    (hn : 5 ≤ n) : 3 ≤ ceilLogTwo n := by
  have hupper := (ceilLogTwo_spec n (by omega : 2 ≤ n)).2
  by_cases htwo : ceilLogTwo n ≤ 2
  · have hfour : 2 ^ ceilLogTwo n ≤ 4 := by
      have hp : 2 ^ ceilLogTwo n ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by omega) htwo
      exact hp
    omega
  · omega

/-- Once both independent paper obligations are supplied, the
six-unit extra handoff fits INSIDE the existing finishRate.
No premise of this theorem is concealed. -/
theorem smallReferenceGeneratedFinishStageOfPaperStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hpaper : SmallFinishPaperStages ring) :
    StageReferenceGeneratedFinish (renewalSmallNext ring)
      (smallReferenceNativePrepared ring)
      (renewalSmallStop ring)
      (headlineReferenceFinishRate (ceilLogTwo n)) := by
  have hq : 3 ≤ ceilLogTwo n :=
    smallFinishAdviceAtLeastThree n hn
  have hreserve := smallFinishRateHasSixReserve
    (ceilLogTwo n) hq hsmall
  intro r hr
  have hfirst : UniformFirstHit.ExpectedHittingTimeAtMost
      (renewalSmallNext ring)
      (fun z => smallFinishPaperPrepared ring z ∨
        renewalSmallStop ring z) r
      ((6 * n ^ 2 : Nat) : Rat) := by
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (renewalSmallNext ring)
      (fun z => smallFinishPaperPrepared ring z ∨
        renewalSmallStop ring z)
      (by omega : 0 < n) r (6 * n ^ 2)).2
    intro T
    exact Nat.le_trans
      (Prob.costNumerator_target_mono
        (renewalSmallNext ring)
        (smallFinishPaperPrepared ring)
        (fun z => smallFinishPaperPrepared ring z ∨
          renewalSmallStop ring z)
        (fun z hz => Or.inl hz) r T)
      ((UniformFirstHit.expectedHittingTimeAtMost_iff_cost
        (renewalSmallNext ring) (smallFinishPaperPrepared ring)
        (by omega : 0 < n) r (6 * n ^ 2)).1
        (hpaper.1 r hr) T)
  have hbound := Prob.expectedHittingTimeAtMost_stage_le
    (renewalSmallNext ring) (by omega : 0 < n) r
    (smallFinishPaperPrepared ring)
    (renewalSmallStop ring)
    (6 * n ^ 2)
    ((headlineReferenceFinishRate (ceilLogTwo n) - 6) * n ^ 2)
    hfirst hpaper.2
  have hsum :
      6 * n ^ 2 +
        (headlineReferenceFinishRate (ceilLogTwo n) - 6) *
          n ^ 2 =
        headlineReferenceFinishRate (ceilLogTwo n) * n ^ 2 := by
    rw [← Nat.add_mul]
    have hcancel :
        6 + (headlineReferenceFinishRate (ceilLogTwo n) - 6) =
          headlineReferenceFinishRate (ceilLogTwo n) := by
      omega
    rw [hcancel]
  simpa only [hsum] using hbound

/-- The merged 37n^2 drain is now used without another
hypothesis. The only remaining input is the OPEN paper-stage
conjunction above. This is NOT an unconditional ReferenceClock. -/
theorem smallReferenceClockOfDrainOfPaperStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hpaper : SmallFinishPaperStages ring) :
    ReferenceClock ring (smallRootedReferenceData ring hsmall)
      (headlineReferenceRate (ceilLogTwo n)) := by
  exact smallReferenceClockOfDrainAndFinish
    ring hn hsmall
    (smallReferenceGrantDrainStage ring hn hsmall)
    (smallReferenceGeneratedFinishStageOfPaperStages
      ring hn hsmall hpaper)

end L3.SmallReferenceFinish
#print axioms L3.SmallReferenceFinish.smallFinishPaperPreparedCore
#print axioms L3.SmallReferenceFinish.smallFinishNativePreparedGrantFree
#print axioms L3.SmallReferenceFinish.smallFinishNativePreparedNativeStep
#print axioms L3.SmallReferenceFinish.smallFinishRateHasSixReserve
#print axioms L3.SmallReferenceFinish.smallFinishLowestThreshold
#print axioms L3.SmallReferenceFinish.smallFinishLowestReserve
#print axioms L3.SmallReferenceFinish.smallFinishLiteralThresholdRow
#print axioms L3.SmallReferenceFinish.smallFinishLiteralSanitizeRow
#print axioms L3.SmallReferenceFinish.smallFinishWitnessNativeReady
#print axioms L3.SmallReferenceFinish.smallFinishWitnessInNativePrepared
#print axioms L3.SmallReferenceFinish.smallFinishWitnessCandidateNotEmpty
#print axioms L3.SmallReferenceFinish.smallFinishNativePreparedNotPaperPrepared
#print axioms L3.SmallReferenceFinish.smallReferenceGeneratedFinishStageOfPaperStages
#print axioms L3.SmallReferenceFinish.smallReferenceClockOfDrainOfPaperStages

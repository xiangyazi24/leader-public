import Leader.L3.Small.ReferenceFinish
import Leader.L3.RenewalPreparationStage

/-!
SMALL candidate preparation on the ORIGINAL renewalSmallNext reference.

This is a direct transfer of the
BANK proof, but no BANK memory, BANK success token, or inherited
authority is used: the shared fact is only that renewalMaskedStep
changes request/grant rather than native or candidate coordinates.

The sigma_p cut is strengthened to CandidateReturnTarget at the
SAME stopped reference state. The only remaining conditional
clock input is SmallFinishFromCandidate.
-/

namespace L3.SmallCandidatePreparation

open L3
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.SmallReferenceFinish
open L3.RenewalReferenceClock
open L3.ReferencePreparationTrail
open L3.ReferencePreparationCandidate
open L3.GrantDrainEntrance
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Literal existing native/C-owner fields; the proof-side SMALL
seen bit is not a physical state or an additional candidate bit. -/
def smallCandidateView {n : Nat}
    (r : RenewalSmallReference n) : Fin n → NativeCand :=
  physicalCandidates r.1

/-- Exact SMALL analogue of bankValidCandidateFrame: neither SMALL
counter success nor masking changes the native/candidate physical
projection on the selected edge. -/
theorem smallReferenceCandidateFrame {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n) :
    smallCandidateView (renewalSmallNext ring r e) =
      physicalCandidates (headlinePhysicalNext ring r.1 e) := by
  change physicalCandidates
      (renewalMaskedStep ring r.1 e
        (renewalSmallCut ring r.1 r.2 e)) =
    physicalCandidates (headlinePhysicalNext ring r.1 e)
  exact bankMaskedCandidateFrame ring r.1 e
    (renewalSmallCut ring r.1 r.2 e)

/-- OLD grants are zero after the proved SMALL drain. FIRE is
disabled regardless of OLD requests and candidate credits. -/
theorem smallCandidateNoFireOn {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (hr : smallReferenceGrantFreeRootedSeen ring r)
    (e : Fin n) :
    NativeLiftNoFireOn ring r.1 e := by
  exact native_lift_no_fire_of_pair_grant_free
    ring r.1 e (hr.2.2 e)
    (hr.2.2 (ring.rightNeighbor e))

/-- Genuine SMALL masked reference equals the existing
birthFreeCandidateStep on the closed grant-free class. -/
theorem smallCandidateStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hr : smallReferenceGrantFreeRootedSeen ring r)
    (e : Fin n) :
    smallCandidateView (renewalSmallNext ring r e) =
      birthFreeCandidateStep ring (smallCandidateView r) e := by
  have hphysical := noFirePhysicalStep hn ring r.1 e
    (smallCandidateNoFireOn ring r hr e)
  exact (smallReferenceCandidateFrame ring r e).trans hphysical

/-- Native component is the already established native reference
view, by definitional equality. -/
theorem smallCandidateNativeView {n : Nat}
    (r : RenewalSmallReference n) :
    candidateNative (smallCandidateView r) =
      smallReferenceNativeView r := by
  rfl

/-- Fixed-root singleton suffix on the SAME SMALL reference,
with grant-free, seen-complete, rooted native fields. -/
def SmallCandidateSingletonAtRoot {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (r : RenewalSmallReference n) : Prop :=
  smallReferenceGrantFreeRootedSeen ring r ∧
    Rooted ring root (smallReferenceNativeView r)

/-- SMALL grant absence and the original native root persist
along every edge. Neither projection nor the history is frozen. -/
theorem smallCandidateSingletonAtRootClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (root : Fin n)
    (r : RenewalSmallReference n)
    (hr : SmallCandidateSingletonAtRoot ring root r)
    (e : Fin n) :
    SmallCandidateSingletonAtRoot ring root
      (renewalSmallNext ring r e) := by
  have hroot := rootedStep hn ring root
    (smallReferenceNativeView r) e hr.2
  have hnative := smallReferenceGrantFreeNativeStep
    ring (by omega : 3 ≤ n) r hr.1 e
  rw [← hnative] at hroot
  exact ⟨smallReferenceGrantFreeClosed
    ring hn hsmall r hr.1 e, hroot⟩

/-- Exact same-scheduler cost projection on all finite horizons.
This is not a mere claim that one selected row agrees. -/
theorem smallCandidateProjectedCostNumerator {n : Nat}
    (ring : DirectedRing n)
    (P : (Fin n → NativeCand) → Prop)
    (H : RenewalSmallReference n → Prop)
    (hstep : ∀ r, H r → ∀ e : Fin n,
      smallCandidateView (renewalSmallNext ring r e) =
        birthFreeCandidateStep ring (smallCandidateView r) e)
    (hclosed : ∀ r, H r → ∀ e : Fin n,
      H (renewalSmallNext ring r e)) :
    ∀ T (r : RenewalSmallReference n), H r →
      costNumerator (renewalSmallNext ring)
        (fun a => P (smallCandidateView a)) r T =
      costNumerator (birthFreeCandidateStep ring) P
        (smallCandidateView r) T := by
  classical
  intro T
  induction T with
  | zero =>
      intro r _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro r hr
      by_cases hp : P (smallCandidateView r)
      · rw [costNumerator_terminal (renewalSmallNext ring)
          (fun a => P (smallCandidateView a))
          r hp (T + 1),
          costNumerator_terminal (birthFreeCandidateStep ring)
            P (smallCandidateView r) hp (T + 1)]
      · rw [costNumerator_succ (renewalSmallNext ring)
          (fun a => P (smallCandidateView a)) r hp T,
          costNumerator_succ (birthFreeCandidateStep ring)
            P (smallCandidateView r) hp T]
        congr 1
        exact ofFn_sum_eq _ _ (fun e => by
          have hh := ih (renewalSmallNext ring r e)
            (hclosed r hr e)
          rw [hstep r hr e] at hh
          exact hh)

/-- The sharp existing doubled candidate clock, transported to
the original SMALL reference from arbitrary legal candidate
scratch, with a genuinely fixed and protected original root. -/
theorem smallCandidatePreparationDoubledCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (root : Fin n) (r : RenewalSmallReference n)
    (hr : SmallCandidateSingletonAtRoot ring root r)
    (T : Nat) :
    2 * costNumerator (renewalSmallNext ring)
      (fun a => CandidateReturnTarget root (smallCandidateView a))
      r T ≤ n ^ T * (10 * n ^ 2 + n) := by
  have hcost := smallCandidateProjectedCostNumerator ring
    (CandidateReturnTarget root)
    (SmallCandidateSingletonAtRoot ring root)
    (fun a ha e => smallCandidateStep ring hn a ha.1 e)
    (smallCandidateSingletonAtRootClosed ring hn hsmall root)
    T r hr
  rw [hcost]
  have hroot : Rooted ring root
      (candidateNative (smallCandidateView r)) := by
    rw [smallCandidateNativeView r]
    exact hr.2
  exact candidateSingletonPreparationDoubledCost hn ring root
    (smallCandidateView r) hroot T

/-- Fixed-root 6*n^2 sigma_p stage including both native readiness
and the EmptyCandidates factor at the same actual stopping cut. -/
theorem smallCandidatePreparationStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (root : Fin n) :
    StageReferencePreparation (renewalSmallNext ring)
      (SmallCandidateSingletonAtRoot ring root)
      (fun r => CandidateReturnTarget root (smallCandidateView r)) := by
  intro r hr
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (renewalSmallNext ring)
    (fun a => CandidateReturnTarget root (smallCandidateView a))
    (by omega : 0 < n) r (6 * n ^ 2)).2
  intro T
  exact renewalBankDoubledPreparationSix n T
    (costNumerator (renewalSmallNext ring)
      (fun a => CandidateReturnTarget root (smallCandidateView a))
      r T)
    (by omega : 1 ≤ n)
    (smallCandidatePreparationDoubledCost
      ring hn hsmall root r hr T)

/-- The original singleton-root suffix and CandidateReturnTarget
are retained together at the stopped sigma_p reference state. -/
def SmallPreparedAtSomeRoot {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) : Prop :=
  ∃ root : Fin n,
    SmallCandidateSingletonAtRoot ring root r ∧
      CandidateReturnTarget root (smallCandidateView r)

/-- Existential root version of the six-unit preparation theorem,
suitable for the actual SMALL stage composition. -/
theorem smallPreparedAtSomeRootStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    StageReferencePreparation (renewalSmallNext ring)
      (smallReferenceNativeRooted ring)
      (SmallPreparedAtSomeRoot ring) := by
  intro r hr
  obtain ⟨root, hroot⟩ := hr.2
  have hfixed : SmallCandidateSingletonAtRoot ring root r :=
    ⟨hr.1, hroot⟩
  have hraw :=
    smallCandidatePreparationStage ring hn hsmall root r hfixed
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (renewalSmallNext ring)
    (SmallPreparedAtSomeRoot ring)
    (by omega : 0 < n) r (6 * n ^ 2)).2
  intro T
  have hcost :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (renewalSmallNext ring)
      (fun a => CandidateReturnTarget root (smallCandidateView a))
      (by omega : 0 < n) r (6 * n ^ 2)).1 hraw T
  have hstrength := costNumeratorTargetOnClosed
    (renewalSmallNext ring)
    (SmallCandidateSingletonAtRoot ring root)
    (SmallPreparedAtSomeRoot ring)
    (fun a => CandidateReturnTarget root (smallCandidateView a))
    (fun a ha e =>
      smallCandidateSingletonAtRootClosed ring hn hsmall root a ha e)
    (by
      intro a ha htarget
      exact ⟨root, ha, htarget⟩)
    T r hfixed
  exact Nat.le_trans hstrength hcost

/-- Literal physical prepared-core target. C_native follows from
native preparedness; candidate emptiness comes from the genuine
CandidateReturnTarget and is not a new extra assumption. -/
theorem smallPreparedAtSomeRootCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallPreparedAtSomeRoot ring r) :
    ReferencePreparationPreparedCore ring r.1 := by
  obtain ⟨root, hroot, htarget⟩ := hr
  have hnative :
      ReferencePreparationNativePreparedAt root
        (smallReferenceNativeView r) := by
    rw [← smallCandidateNativeView r]
    exact htarget.1
  have hclean : C_native ring (smallReferenceNativeView r) :=
    bankNativePreparedClean hn ring root
      (smallReferenceNativeView r) hnative
  have hprotected : Protected ring (nativeProjection r.1) :=
    hclean.1.1
  exact nativePreparedPhysicalCandidateHandoff
    ring root r.1 hnative hprotected hroot.1.2.2
    hclean htarget.2

/-- The candidate-history conjunct is generated at the same
reference state and is not inferred from an arbitrary clean slot. -/
theorem smallPreparedAtSomeRootCandidateHistory {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallPreparedAtSomeRoot ring r) :
    H_cand ring (smallCandidateView r) := by
  exact referencePreparation_prepared_has_candidate_history
    ring r.1 (smallPreparedAtSomeRootCore ring hn r hr)

/-- Only remaining input: actual reference generated finish
from the joint sigma_p state. No bound on this has been proven
by the candidate preparation theorem alone. -/
def SmallFinishFromCandidate {n : Nat}
    (ring : DirectedRing n) : Prop :=
  StageReferenceGeneratedFinish (renewalSmallNext ring)
    (SmallPreparedAtSomeRoot ring)
    (renewalSmallStop ring)
    (headlineReferenceFinishRate (ceilLogTwo n))

/-- Reference-rate arithmetic: candidate retirement occupies the
original six-unit preparation allowance, not another six units. -/
theorem smallCandidateReferenceRateLedger {n : Nat}
    (hn : 5 ≤ n) :
    headlineInheritedRate (ceilLogTwo n) + 37 + 4917 + 6 +
      headlineReferenceFinishRate (ceilLogTwo n) =
        headlineReferenceRate (ceilLogTwo n) := by
  have hspec := (ceilLogTwo_spec n (by omega : 2 ≤ n)).2
  have hthree : 3 ≤ ceilLogTwo n := by
    by_cases hlow : ceilLogTwo n < 3
    · have hbound : 2 ^ ceilLogTwo n ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · omega
  exact headlineReferenceRate_decompose (ceilLogTwo n) hthree

/-- Conditional clock: the grant drain, singleton
and now stronger candidate preparation have been discharged.
No unconditional generated finish is asserted. -/
theorem smallReferenceClockOfCandidateFinish {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hFinish : SmallFinishFromCandidate ring) :
    ReferenceClock ring (smallRootedReferenceData ring hsmall)
      (headlineReferenceRate (ceilLogTwo n)) := by
  have hstages : SmallReferencePostSeenStageData ring :=
    smallReferencePostSeenStageDataOfStages
      ring hn
      (smallReferenceGrantFreeRootedSeen ring)
      (smallReferenceNativeRooted ring)
      (SmallPreparedAtSomeRoot ring)
      (smallReferenceGrantDrainStage ring hn hsmall)
      (smallReferenceSingletonStageRooted ring hn hsmall)
      (smallPreparedAtSomeRootStage ring hn hsmall)
      hFinish
  exact smallReferenceClockOfStageData ring hn hsmall hstages

end L3.SmallCandidatePreparation
#print axioms L3.SmallCandidatePreparation.smallReferenceCandidateFrame
#print axioms L3.SmallCandidatePreparation.smallCandidateNoFireOn
#print axioms L3.SmallCandidatePreparation.smallCandidateStep
#print axioms L3.SmallCandidatePreparation.smallCandidateNativeView
#print axioms L3.SmallCandidatePreparation.smallCandidateSingletonAtRootClosed
#print axioms L3.SmallCandidatePreparation.smallCandidateProjectedCostNumerator
#print axioms L3.SmallCandidatePreparation.smallCandidatePreparationDoubledCost
#print axioms L3.SmallCandidatePreparation.smallCandidatePreparationStage
#print axioms L3.SmallCandidatePreparation.smallPreparedAtSomeRootStage
#print axioms L3.SmallCandidatePreparation.smallPreparedAtSomeRootCore
#print axioms L3.SmallCandidatePreparation.smallPreparedAtSomeRootCandidateHistory
#print axioms L3.SmallCandidatePreparation.smallCandidateReferenceRateLedger
#print axioms L3.SmallCandidatePreparation.smallReferenceClockOfCandidateFinish

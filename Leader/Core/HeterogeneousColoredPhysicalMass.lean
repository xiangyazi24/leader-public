import Leader.Core.PredictableColoredSixFiniteTree
import Leader.Core.BalancedFailureRestart

set_option autoImplicit false

namespace HeterogeneousColoredPhysicalMass

open FiniteUniformStoppingTree
open PayloadFiniteStoppingTree
open PredictablePairHitCounterFiniteTree
open PredictableColoredSixFiniteTree

/-- Same scheduler edge, different active carriers.
Colored failure is intentionally unconstrained. -/
def SuccessRefinesRel
    {CA PA CS CF PS PF : Type} {n : Nat}
    (R : CA → PA → Prop)
    (colored : CA → Fin n → PayloadNode CA CS CF)
    (physical : PA → Fin n → PayloadNode PA PS PF) : Prop :=
  ∀ ca pa, R ca pa → ∀ e,
    match colored ca e with
    | .success _ =>
        ∃ ps, physical pa e = .success ps
    | .failure _ =>
        True
    | .active ca' =>
        (∃ pa',
          physical pa e = .active pa' ∧ R ca' pa') ∨
        (∃ ps, physical pa e = .success ps)

private theorem successMass_le_pow
    {A S F : Type} {n : Nat}
    (step : A → Fin n → PayloadNode A S F)
    (x : PayloadNode A S F) (T : Nat) :
    successMass step x T ≤ n ^ T := by
  rw [successMass_eq_successCount step x T]
  have hp := node_count_partition (eraseStep step) x.erase T
  omega

/-- Heterogeneous same-word success inclusion. -/
theorem successMass_le_of_rel_refines
    {CA PA CS CF PS PF : Type} {n : Nat}
    (R : CA → PA → Prop)
    (colored : CA → Fin n → PayloadNode CA CS CF)
    (physical : PA → Fin n → PayloadNode PA PS PF)
    (href : SuccessRefinesRel R colored physical) :
    ∀ ca pa, R ca pa → ∀ T,
      successMass colored (.active ca) T ≤
        successMass physical (.active pa) T := by
  unfold SuccessRefinesRel at href
  intro ca pa hrel T
  induction T generalizing ca pa with
  | zero =>
      simp [successMass]
  | succ T ih =>
      simp only [successMass, PayloadFiniteStoppingTree.stepNode]
      apply ofFn_sum_le
      intro e
      cases hc : colored ca e with
      | failure cf =>
          simp [hc]
      | success cs =>
          have hr := href ca pa hrel e
          rw [hc] at hr
          rcases hr with ⟨ps, hp⟩
          simp [hc, hp]
      | active ca' =>
          have hr := href ca pa hrel e
          rw [hc] at hr
          rcases hr with ⟨pa', hp, hr'⟩ | ⟨ps, hp⟩
          · simpa [hc, hp] using ih ca' pa' hr'
          · have hb := successMass_le_pow colored (.active ca') T
            simpa [hc, hp] using hb

private theorem pairHitCounterStep_ne_failure
    {S : Type} {n d : Nat}
    (first second : S → Fin n) (next : S → Fin n → S) :
    ∀ st e,
      pairHitCounterStep (d := d) first second next st e ≠ .failure := by
  intro st e
  by_cases h1 : e = first st.payload
  · by_cases hd : st.hits + 1 = d <;>
      simp [pairHitCounterStep, h1, hd]
  · by_cases h2 : e = second st.payload
    · by_cases hd : st.hits + 1 = d <;>
        simp [pairHitCounterStep, h1, h2, hd]
    · simp [pairHitCounterStep, h1, h2]

/-- Public exact-64 colored identity + six-hit timeout + heterogeneous
success refinement imply the exact 127/8192 physical-success lower bound. -/
theorem exact64_rel_refined_timeout
    {S PA PS PF : Type} {n : Nat}
    (good bad : S → Fin n) (next : S → Fin n → S)
    (hdistinct : ∀ s, good s ≠ bad s)
    (payload : S) (physicalStart : PA)
    (R : ActivePairHitState S 6 → PA → Prop)
    (physical : PA → Fin n → PayloadNode PA PS PF)
    (hstart :
      R (initialState payload 6 (by omega)) physicalStart)
    (href :
      SuccessRefinesRel R (gstep good bad next) physical) :
    127 * n ^ (384 * n) ≤
      8192 *
        successMass physical (.active physicalStart) (384 * n) := by
  let p := pairHitCounterStep (d := 6) good bad next
  let c := gstep good bad next
  let st : ActivePairHitState S 6 :=
    initialState payload 6 (by omega)
  let H := 384 * n

  have hdom :
      successMass c (.active st) H ≤
        successMass physical (.active physicalStart) H := by
    exact successMass_le_of_rel_refines
      R c physical href st physicalStart
      (by simpa [st] using hstart) H

  have hfail :
      failureCount p (.active st) H = 0 := by
    exact
      BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
        p
        (by
          intro q e
          exact pairHitCounterStep_ne_failure
            (d := 6) good bad next q e)
        st H

  have hpart := node_count_partition p (.active st) H

  have h64 :
      successCount p (.active st) H =
        64 * successMass c (.active st) H := by
    simpa [p, c, st, H] using
      six_colored_success_exact_pair_completion
        good bad next hdistinct payload H

  have htimeout :
      128 * activeCount p (.active st) H ≤ n ^ H := by
    simpa [p, st, H] using
      six_hits_timeout_128 good bad next hdistinct payload

  have hcolored :
      127 * n ^ H ≤
        8192 * successMass c (.active st) H := by
    omega

  have hphysical :=
    Nat.mul_le_mul_left 8192 hdom

  have hfinal :
      127 * n ^ H ≤
        8192 * successMass physical (.active physicalStart) H :=
    by omega

  simpa [H] using hfinal

#print axioms successMass_le_of_rel_refines
#print axioms exact64_rel_refined_timeout

end HeterogeneousColoredPhysicalMass

import Leader.PPL.Elim.Attempt

/-!
# LD(736): moderate-attempt retry mass

The probability part of the moderate attempt is proved here at the exact
finite-word denominator 96.

For a vulnerable entry with target phase Dummy(0):
* target_cycle_pathwise + the predictable-service compensator + the checked
  attacker Bellman cost give the collapse moment;
* moderate_collapse_moment reduces it to 3 C <= 20 n^T;
* W1_scaled is summed over all controlled words;
* weighted_changeOfMeasure_nonretry transfers the retained controlled mass
  back to the original vulnerable tree;
* node_count_partition yields 96 failure <= 95 n^T.

The only residual below is a stage-level transport fact for the concrete
moderateAttemptKernel: preparation and recovery contain no retry, so a
completed retry must be charged to the unique vulnerable failure episode.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-! ## Match the File-5 target service charge with File-6 compensator data -/

def moderateTargetServiceActive
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (x : VulnerableState F) : Bool :=
  match x.targetPhase with
  | .dummy _ => true
  | .ret _ => true
  | .ready => false
  | .live _ => false

def moderateTargetServiceRequired
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (x : VulnerableState F) : Fin n :=
  targetServiceEdge F x

theorem targetServiceCharge_eq_serviceCharge_moderate
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n) :
    targetServiceCharge F hb (.active x) e =
      serviceCharge
        (moderateTargetServiceActive F)
        (moderateTargetServiceRequired F) x e := by
  cases hph : x.targetPhase with
  | ready =>
      simp [targetServiceCharge, serviceCharge,
        moderateTargetServiceActive, moderateTargetServiceRequired, hph]
  | live p =>
      simp [targetServiceCharge, serviceCharge,
        moderateTargetServiceActive, moderateTargetServiceRequired, hph]
  | dummy p =>
      have hnot : x.targetPhase ≠ .ready := by
        simp [hph]
      have heff :=
        targetRedirection_effective_of_not_ready F hb x e hnot
      simp [targetServiceCharge, serviceCharge,
        moderateTargetServiceActive, moderateTargetServiceRequired,
        targetServiceEdge, hph, heff, beq_iff_eq]
  | ret q =>
      have hnot : x.targetPhase ≠ .ready := by
        simp [hph]
      have heff :=
        targetRedirection_effective_of_not_ready F hb x e hnot
      simp [targetServiceCharge, serviceCharge,
        moderateTargetServiceActive, moderateTargetServiceRequired,
        targetServiceEdge, hph, heff, beq_iff_eq]

theorem targetServiceWordCount_eq_wordCharge_moderate
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (z : StopNode (VulnerableState F))
    (w : List (Fin n)) :
    targetServiceWordCount hseal F hb z w =
      wordCharge (qStep hseal F hb)
        (serviceCharge
          (moderateTargetServiceActive F)
          (moderateTargetServiceRequired F)) z w := by
  induction w generalizing z with
  | nil =>
      cases z <;> rfl
  | cons e es ih =>
      cases z with
      | success =>
          rfl
      | failure =>
          rfl
      | active x =>
          simp only [targetServiceWordCount, wordCharge]
          rw [targetServiceCharge_eq_serviceCharge_moderate F hb x e]
          exact congrArg
            (serviceCharge
                (moderateTargetServiceActive F)
                (moderateTargetServiceRequired F) x e + ·)
            (ih (qStep hseal F hb x e))

/-! ## The checked physical rows imply the moderate collapse moment -/

theorem moderate_vulnerable_collapse_moment
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b) (hab : F.a ≤ 2 * F.b)
    (x : VulnerableState F)
    (hstart : x.targetPhase = .dummy 0)
    (T : Nat) :
    3 *
        collapseCountNumerator
          (vulnerableStep hseal F)
          (targetRedirection F hb)
          (.active x) T ≤
      20 * n ^ T := by
  have hrows :
      ControlRowSpec hseal F hb :=
    controlRowSpec_proved hseal F hb
  have hcycle :
      ∀ w : List (Fin n), w.length = T →
        (2 * F.b - 1) *
            ControlledSchedulerMass.eventCount
              (ControlledSchedulerMass.controlledStep
                (vulnerableStep hseal F)
                (targetRedirection F hb))
              (targetRedirection F hb)
              (.active x) w ≤
          wordCharge
            (ControlledSchedulerMass.controlledStep
              (vulnerableStep hseal F)
              (targetRedirection F hb))
            (serviceCharge
              (moderateTargetServiceActive F)
              (moderateTargetServiceRequired F))
            (.active x) w := by
    intro w _hw
    have hp :=
      target_cycle_pathwise
        hseal F hb hrows x hstart w
    rw [targetServiceWordCount_eq_wordCharge_moderate
      hseal F hb (.active x) w] at hp
    simpa [qStep] using hp
  have hnum :=
    collapseNumerator_le_serviceNumerator
      (vulnerableStep hseal F)
      (targetRedirection F hb)
      (moderateTargetServiceActive F)
      (moderateTargetServiceRequired F)
      (2 * F.b - 1) (.active x) T hcycle
  have hcycleNumerator :
      (2 * F.b - 1) *
          collapseCountNumerator
            (vulnerableStep hseal F)
            (targetRedirection F hb)
            (.active x) T ≤
        edgeChargeNumerator
          (qStep hseal F hb)
          (serviceCharge
            (moderateTargetServiceActive F)
            (moderateTargetServiceRequired F))
          (.active x) T := by
    simpa [targetServiceNumerator, qStep] using hnum
  have hcost0 :=
    qTrial_cost_five_na
      hseal F hb hrows x T
  have hcost :
      truncatedActiveCostNumerator
          (qStep hseal F hb) (.active x) T ≤
        n ^ T * (n * (5 * F.a)) := by
    calc
      truncatedActiveCostNumerator
          (qStep hseal F hb) (.active x) T ≤
        n ^ T * (5 * n * F.a) := hcost0
      _ = n ^ T * (n * (5 * F.a)) := by
        ac_rfl
  have hn0 : 0 < n := by
    have hn2 := frame_two_le_control F
    omega
  have hmoment :=
    collapse_moment_cleared
      (qStep hseal F hb)
      (moderateTargetServiceActive F)
      (moderateTargetServiceRequired F)
      (collapseCountNumerator
        (vulnerableStep hseal F)
        (targetRedirection F hb))
      (2 * F.b - 1) (5 * F.a) hn0
      (.active x) T hcycleNumerator hcost
  exact
    moderate_collapse_moment
      F.b F.a
      (collapseCountNumerator
        (vulnerableStep hseal F)
        (targetRedirection F hb)
        (.active x) T)
      (n ^ T)
      hb hab hmoment

/-! ## W1 summed over complete controlled words -/

theorem eventCount_le_length_moderate
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S) (w : List (Fin n)) :
    ControlledSchedulerMass.eventCount step r z w ≤
      w.length := by
  induction w generalizing z with
  | nil =>
      simp [ControlledSchedulerMass.eventCount]
  | cons e es ih =>
      have hc :
          ControlledSchedulerMass.eventCost r z e ≤ 1 := by
        cases z with
        | active s =>
            simp [ControlledSchedulerMass.eventCost]
            split <;> omega
        | success =>
            simp [ControlledSchedulerMass.eventCost]
        | failure =>
            simp [ControlledSchedulerMass.eventCost]
      have ht :=
        ih (stepNode step z e)
      simp only [ControlledSchedulerMass.eventCount,
        List.length_cons]
      omega

theorem runWord_ne_failure_moderate
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (hstep : ∀ s e, step s e ≠ .failure)
    (z : StopNode S) (hz : z ≠ .failure)
    (w : List (Fin n)) :
    ControlledSchedulerMass.runWord step z w ≠ .failure := by
  induction w generalizing z with
  | nil =>
      exact hz
  | cons e es ih =>
      apply ih
      cases z with
      | active s =>
          exact hstep s e
      | success =>
          simp [stepNode]
      | failure =>
          exact False.elim (hz rfl)

theorem W1_wordSum_moderate
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S) (hz : z ≠ .failure)
    (hcontrolled :
      ∀ s e,
        ControlledSchedulerMass.controlledStep step r s e ≠
          .failure)
    (T : Nat) :
    8 * (2 ^ T * n ^ T) ≤
      128 * weightedQNonRetryNumerator step r z T +
        2 ^ T * collapseCountNumerator step r z T := by
  let q :=
    ControlledSchedulerMass.controlledStep step r
  have hpoint :
      ∀ i : Fin (n ^ T),
        8 * 2 ^ T ≤
          128 *
              powSuccessOrActive
                (ControlledSchedulerMass.runWord q z
                  (FixedSpanRenewalPayload.rawWord n T i))
                (T -
                  ControlledSchedulerMass.eventCount
                    q r z
                    (FixedSpanRenewalPayload.rawWord n T i)) +
            2 ^ T *
              ControlledSchedulerMass.eventCount
                q r z
                (FixedSpanRenewalPayload.rawWord n T i) := by
    intro i
    let w :=
      FixedSpanRenewalPayload.rawWord n T i
    let N :=
      ControlledSchedulerMass.eventCount q r z w
    have hN : N ≤ T := by
      have h :=
        eventCount_le_length_moderate q r z w
      simpa [N, w,
        FixedSpanRenewalPayload.rawWord_length] using h
    have hw :=
      W1_scaled N T hN
    have hnf :
        ControlledSchedulerMass.runWord q z w ≠
          .failure :=
      runWord_ne_failure_moderate
        q hcontrolled z hz w
    cases hr :
        ControlledSchedulerMass.runWord q z w with
    | active y =>
        simpa [powSuccessOrActive, hr, N, w,
          Nat.mul_comm] using hw
    | success =>
        simpa [powSuccessOrActive, hr, N, w,
          Nat.mul_comm] using hw
    | failure =>
        exact False.elim (hnf hr)
  have hsum :=
    ofFn_sum_le
      (fun _ : Fin (n ^ T) => 8 * 2 ^ T)
      (fun i : Fin (n ^ T) =>
        128 *
            powSuccessOrActive
              (ControlledSchedulerMass.runWord q z
                (FixedSpanRenewalPayload.rawWord n T i))
              (T -
                ControlledSchedulerMass.eventCount
                  q r z
                  (FixedSpanRenewalPayload.rawWord n T i)) +
          2 ^ T *
            ControlledSchedulerMass.eventCount
              q r z
              (FixedSpanRenewalPayload.rawWord n T i))
      hpoint
  rw [ofFn_sum_const, ofFn_sum_add,
    ofFn_sum_mul_left, ofFn_sum_mul_left] at hsum
  rw [
    FixedSpanRenewalPayload.rawWord_sum n T
      (fun w =>
        powSuccessOrActive
          (ControlledSchedulerMass.runWord q z w)
          (T -
            ControlledSchedulerMass.eventCount q r z w)),
    FixedSpanRenewalPayload.rawWord_sum n T
      (fun w =>
        ControlledSchedulerMass.eventCount q r z w)
  ] at hsum
  have hsum' :
      n ^ T * (8 * 2 ^ T) ≤
        128 * weightedQNonRetryNumerator step r z T +
          2 ^ T * collapseCountNumerator step r z T := by
    simpa [q, weightedQNonRetryNumerator,
      collapseCountNumerator] using hsum
  calc
    8 * (2 ^ T * n ^ T) =
        n ^ T * (8 * 2 ^ T) := by
      ac_rfl
    _ ≤
      128 * weightedQNonRetryNumerator step r z T +
        2 ^ T * collapseCountNumerator step r z T :=
      hsum'

theorem nonretry_mass_96_of_collapse_moderate
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S) (hz : z ≠ .failure)
    (hcontrolled :
      ∀ s e,
        ControlledSchedulerMass.controlledStep step r s e ≠
          .failure)
    (T : Nat)
    (hcollapse :
      3 * collapseCountNumerator step r z T ≤
        20 * n ^ T) :
    n ^ T ≤
      96 *
        (activeCount step z T +
          successCount step z T) := by
  have hw :=
    W1_wordSum_moderate
      step r z hz hcontrolled T
  let P := 2 ^ T * n ^ T
  let Q :=
    2 ^ T * collapseCountNumerator step r z T
  let W :=
    weightedQNonRetryNumerator step r z T
  have hw' :
      8 * P ≤ 128 * W + Q := by
    simpa [P, Q, W] using hw
  have hc0 :=
    Nat.mul_le_mul_left (2 ^ T) hcollapse
  have hc :
      3 * Q ≤ 20 * P := by
    calc
      3 * Q =
          2 ^ T *
            (3 * collapseCountNumerator step r z T) := by
        simp [Q]
        ac_rfl
      _ ≤
        2 ^ T * (20 * n ^ T) :=
          hc0
      _ = 20 * P := by
        simp [P]
        ac_rfl
  have hw3 :=
    Nat.mul_le_mul_left 3 hw'
  have hP :
      P ≤ 96 * W := by
    omega
  have hchange :=
    weighted_changeOfMeasure_nonretry
      step r z T
  have hchange96 :=
    Nat.mul_le_mul_left 96 hchange
  have hscaled :
      2 ^ T * n ^ T ≤
        2 ^ T *
          (96 *
            (activeCount step z T +
              successCount step z T)) := by
    calc
      2 ^ T * n ^ T = P := rfl
      _ ≤ 96 * W := hP
      _ ≤
        96 *
          (2 ^ T *
            (activeCount step z T +
              successCount step z T)) := hchange96
      _ =
        2 ^ T *
          (96 *
            (activeCount step z T +
              successCount step z T)) := by
        ac_rfl
  have hpow : 0 < 2 ^ T :=
    Nat.pow_pos (by decide)
  exact
    Nat.le_of_mul_le_mul_left
      hscaled hpow

theorem failure_mass_95_of_collapse_moderate
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S) (hz : z ≠ .failure)
    (hcontrolled :
      ∀ s e,
        ControlledSchedulerMass.controlledStep step r s e ≠
          .failure)
    (T : Nat)
    (hcollapse :
      3 * collapseCountNumerator step r z T ≤
        20 * n ^ T) :
    96 * failureCount step z T ≤
      95 * n ^ T := by
  have hnonretry :=
    nonretry_mass_96_of_collapse_moderate
      step r z hz hcontrolled T hcollapse
  have hpart :=
    node_count_partition step z T
  omega

theorem moderate_vulnerable_failure_mass
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b) (hab : F.a ≤ 2 * F.b)
    (x : VulnerableState F)
    (hstart : x.targetPhase = .dummy 0) :
    ∀ T,
      96 *
          failureCount
            (vulnerableStep hseal F)
            (.active x) T ≤
        95 * n ^ T := by
  intro T
  apply
    failure_mass_95_of_collapse_moderate
      (vulnerableStep hseal F)
      (targetRedirection F hb)
      (.active x)
      (by simp)
      ?_ T
      (moderate_vulnerable_collapse_moment
        hseal F hb hab x hstart T)
  intro s e
  simpa [qStep] using
    (qStep_no_failure hseal F hb s e)

/-! ## Single residual: splice the concrete stages around the vulnerable trial -/

/--
The remaining File-7 stage fact.

It contains no probability estimate of its own: it says that any uniform
95/96 failure estimate for every actual Dummy(0) vulnerable entry lifts
through the concrete moderateAttemptKernel preparation and recovery stages to
the completed-retry numerator.  The preparation stages never retry; recovery
can only delay a retry, so active residual mass must be retained rather than
discarded.
-/
def ModerateVulnerableStageLiftSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      (∀ x : VulnerableState F,
        x.targetPhase = .dummy 0 →
        ∀ T,
          96 *
              failureCount
                (vulnerableStep hSealed F)
                (.active x) T ≤
            95 * n ^ T) →
      ∀ s T,
        96 *
            retryCount
              (moderateAttemptKernel ring F)
              (.active
                ((moderateAttemptKernel ring F).start s))
              T ≤
          95 * n ^ T

/--
The requested residual theorem, with exactly one stage-level fact left.
All 1/96 probability arithmetic is discharged above.
-/
theorem moderateAttemptRetryMass_of_vulnerableStageLift
    (hLift : ModerateVulnerableStageLiftSpec) :
    ModerateAttemptRetryMassSpec := by
  intro hSealed
  intro n ring C0 F hb hab s T
  apply hLift hSealed ring F hb
  · intro x hstart U
    exact
      moderate_vulnerable_failure_mass
        hSealed F hb hab x hstart U
  all_goals first | exact s | exact T

#print axioms PPL.Convergence.LDLocal.targetServiceCharge_eq_serviceCharge_moderate
#print axioms PPL.Convergence.LDLocal.targetServiceWordCount_eq_wordCharge_moderate
#print axioms PPL.Convergence.LDLocal.moderate_vulnerable_collapse_moment
#print axioms PPL.Convergence.LDLocal.eventCount_le_length_moderate
#print axioms PPL.Convergence.LDLocal.runWord_ne_failure_moderate
#print axioms PPL.Convergence.LDLocal.W1_wordSum_moderate
#print axioms PPL.Convergence.LDLocal.nonretry_mass_96_of_collapse_moderate
#print axioms PPL.Convergence.LDLocal.failure_mass_95_of_collapse_moderate
#print axioms PPL.Convergence.LDLocal.moderate_vulnerable_failure_mass
#print axioms PPL.Convergence.LDLocal.moderateAttemptRetryMass_of_vulnerableStageLift

end PPL.Convergence.LDLocal

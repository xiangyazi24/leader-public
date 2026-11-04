import Leader.PPL.Elim.AttemptLongIncident
import Leader.PPL.Elim.ControlRows
import Leader.PPL.Elim.LocalDeletionCounting

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# Long retained bridge on the first-cut carriers

There are two different kernels here.

* vulnerableStep is the original stopped physical retained trial.
* qStep is its controlled change-of-measure kernel.  At a ready target,
  scheduler letter R_j is redirected to physical letter L_j.

Therefore the raw long attempt cannot simulate qStep letter-for-letter.
The correct physical simulation is raw retained/recovery versus vulnerableStep.
The controlled qStep enters only in the finite-word counting argument.
-/

/-! ## 1. Raw retained state versus the original vulnerable stopped tree -/

/-- Proof fields live on the VulnerableState witness.  The relation itself
only asks that the physical configuration and the two phase labels agree. -/
def longRetainedVulnerableRel
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> VulnerableState F -> Prop
  | .junk _, _ => False
  | .live C _ stage, x =>
      match stage with
      | .retained targetPhase attackPhase =>
          And
            (x.cfg = C)
            (And
              (x.attackPhase = attackPhase)
              (x.targetPhase = targetPhase))
      | _ => False

/-- A stopped vulnerable failure needs no matching raw child: in the raw long
kernel that port enters recovery, and the whole stopped failure subtree is
available to pay any later raw retry. -/
structure LongRetainedFailureSimulation
    {A S V : Type} {n : Nat}
    (K : RetryKernel A S n)
    (vstep : V -> Fin n -> StopNode V)
    (rel : A -> V -> Prop) : Prop where
  success :
    forall a v e,
      rel a v ->
      vstep v e = .success ->
      K.step a e = .success
  active :
    forall a v e v',
      rel a v ->
      vstep v e = .active v' ->
      Exists fun a' =>
        And
          (K.step a e = .active a')
          (rel a' v')

/-- The literal retained branch of longStep reproduces every success and
active child of vulnerableStep.  The ready/R_j vulnerable failure is
deliberately unconstrained and is exactly the raw recovery branch. -/
theorem longRetainedVulnerableSimulation
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongRetainedFailureSimulation
      (longAttemptKernel ring F)
      (vulnerableStep hSealed F)
      (longRetainedVulnerableRel F) := by
  refine {
    success := ?_
    active := ?_
  }
  · intro a x e hrel hv
    cases a with
    | junk C =>
        simp [longRetainedVulnerableRel] at hrel
    | live C hgood stage =>
        cases stage with
        | targetCR mode =>
            simp [longRetainedVulnerableRel] at hrel
        | attackerCR targetPhase mode =>
            simp [longRetainedVulnerableRel] at hrel
        | liveWait targetPhase attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | advance targetPhase attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | race targetPhase attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | incident attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | recovery targetPhase attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | stuck =>
            simp [longRetainedVulnerableRel] at hrel
        | retained targetPhase attackPhase =>
            have hr :
                And
                  (x.cfg = C)
                  (And
                    (x.attackPhase = attackPhase)
                    (x.targetPhase = targetPhase)) := by
              simpa [longRetainedVulnerableRel] using hrel
            rcases hr with ⟨hcfg, hrest⟩
            rcases hrest with ⟨hattack, htarget⟩
            subst C
            subst attackPhase
            subst targetPhase
            classical
            by_cases hfail :
                And
                  (x.targetPhase = .ready)
                  (e = R_j F)
            · have hbad : False := by
                simpa [vulnerableStep, hfail] using hv
              exact False.elim hbad
            · let D := stepE ring x.cfg e
              by_cases htag : TaggedDeleted F D
              · simpa
                  [longAttemptKernel, longStep, D, htag]
              · have hbad : False := by
                  simpa
                    [vulnerableStep, hfail, D, htag]
                    using hv
                exact False.elim hbad
  · intro a x e x' hrel hv
    cases a with
    | junk C =>
        simp [longRetainedVulnerableRel] at hrel
    | live C hgood stage =>
        cases stage with
        | targetCR mode =>
            simp [longRetainedVulnerableRel] at hrel
        | attackerCR targetPhase mode =>
            simp [longRetainedVulnerableRel] at hrel
        | liveWait targetPhase attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | advance targetPhase attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | race targetPhase attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | incident attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | recovery targetPhase attackPhase =>
            simp [longRetainedVulnerableRel] at hrel
        | stuck =>
            simp [longRetainedVulnerableRel] at hrel
        | retained targetPhase attackPhase =>
            have hr :
                And
                  (x.cfg = C)
                  (And
                    (x.attackPhase = attackPhase)
                    (x.targetPhase = targetPhase)) := by
              simpa [longRetainedVulnerableRel] using hrel
            rcases hr with ⟨hcfg, hrest⟩
            rcases hrest with ⟨hattack, htarget⟩
            subst C
            subst attackPhase
            subst targetPhase
            classical
            by_cases hfail :
                And
                  (x.targetPhase = .ready)
                  (e = R_j F)
            · have hbad : False := by
                simpa [vulnerableStep, hfail] using hv
              exact False.elim hbad
            · let D := stepE ring x.cfg e
              by_cases htag : TaggedDeleted F D
              · have hbad : False := by
                  simpa
                    [vulnerableStep, hfail, D, htag]
                    using hv
                exact False.elim hbad
              · have hnot :
                    Not
                      (TaggedDeleted F
                        (stepE ring x.cfg e)) := by
                  simpa [D] using htag
                have hport :
                    x.targetPhase = .ready ->
                      e ≠ F.j := by
                  intro hready he
                  apply hfail
                  exact
                    And.intro
                      hready
                      (by simpa [R_j] using he)
                let child :=
                  vulnerableChild
                    hSealed F x e hport hnot
                have hvchild :
                    vulnerableStep hSealed F x e =
                      .active child := by
                  simp
                    [vulnerableStep, hfail,
                      hnot, child]
                have hchildEq : child = x' := by
                  have hnodes :
                      (StopNode.active child :
                        StopNode (VulnerableState F)) =
                        .active x' :=
                    hvchild.symm.trans hv
                  injection hnodes
                subst x'
                have hgoodD :
                    AttemptGood ring F D := by
                  simpa [D] using
                    (attemptGood_step
                      ring F x.cfg e hgood hnot)
                let a' : LongAttemptState ring F :=
                  .live D hgoodD
                    (.retained
                      (nextSectorPhase
                        F.B x.targetPhase e)
                      (nextSectorPhase
                        F.A x.attackPhase e))
                refine ⟨a', ?_, ?_⟩
                · simpa
                    [longAttemptKernel,
                      longStep, D, hnot,
                      hfail, a']
                · have hAeq :
                      child.attackPhase =
                        nextSectorPhase
                          F.A x.attackPhase e := by
                    simpa [child, PhaseTransition]
                      using
                        (vulnerableChild_attack_transition
                          hSealed F x e hport hnot)
                  have hBeq :
                      child.targetPhase =
                        nextSectorPhase
                          F.B x.targetPhase e := by
                    simpa [child, PhaseTransition]
                      using
                        (vulnerableChild_target_transition
                          hSealed F x e hport hnot)
                  change
                    And
                      (child.cfg = D)
                      (And
                        (child.attackPhase =
                          nextSectorPhase
                            F.A x.attackPhase e)
                        (child.targetPhase =
                          nextSectorPhase
                            F.B x.targetPhase e))
                  exact
                    And.intro rfl
                      (And.intro hAeq hBeq)

/-! ## 2. Generic finite-tree consequence of the simulation -/

theorem longRetainedRetryCount_le_pow
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) :
    forall x T, retryCount K x T <= n ^ T := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x <;> simp [retryCount]
  | succ T ih =>
      cases x with
      | success =>
          simp [retryCount]
      | retry s =>
          simp [retryCount]
      | active a =>
          simp only [retryCount]
          calc
            (List.ofFn
              (fun e : Fin n =>
                retryCount K (K.step a e) T)).sum
                <=
              (List.ofFn
                (fun _ : Fin n => n ^ T)).sum :=
              ofFn_sum_le _ _ (fun e => ih (K.step a e))
            _ = n * n ^ T :=
              ofFn_sum_const n (n ^ T)
            _ = n ^ (T + 1) := by
              rw [Nat.pow_succ]
              ac_rfl

theorem longRetainedOfFnSumZero :
    forall m : Nat,
      (List.ofFn
        (fun _ : Fin m => (0 : Nat))).sum = 0
  | 0 => rfl
  | m + 1 => by
      rw [List.ofFn_succ, List.sum_cons,
        longRetainedOfFnSumZero m]

theorem longRetainedFailureCountSuccessZero
    {V : Type} {n : Nat}
    (step : V -> Fin n -> StopNode V) :
    forall T, failureCount step (.success) T = 0 := by
  intro T
  induction T with
  | zero =>
      rfl
  | succ T ih =>
      change
        (List.ofFn
          (fun _ : Fin n =>
            failureCount step (.success) T)).sum = 0
      rw [ofFn_sum_eq
        _ (fun _ : Fin n => 0) (fun _ => ih)]
      exact longRetainedOfFnSumZero n

theorem longRetainedFailureCountFailurePow
    {V : Type} {n : Nat}
    (step : V -> Fin n -> StopNode V) :
    forall T, failureCount step (.failure) T = n ^ T := by
  intro T
  induction T with
  | zero =>
      rfl
  | succ T ih =>
      change
        (List.ofFn
          (fun _ : Fin n =>
            failureCount step (.failure) T)).sum =
          n ^ (T + 1)
      rw [ofFn_sum_eq
        _ (fun _ : Fin n => n ^ T)
        (fun _ => ih),
        ofFn_sum_const, Nat.pow_succ]
      ac_rfl

theorem longRetainedRetry_le_failure_of_sim
    {A S V : Type} {n : Nat}
    (K : RetryKernel A S n)
    (vstep : V -> Fin n -> StopNode V)
    (rel : A -> V -> Prop)
    (hsim :
      LongRetainedFailureSimulation
        K vstep rel) :
    forall a v,
      rel a v ->
      forall T,
        retryCount K (.active a) T <=
          failureCount vstep (.active v) T := by
  intro a v hrel T
  induction T generalizing a v with
  | zero =>
      exact Nat.le_refl _
  | succ T ih =>
      change
        (List.ofFn
          (fun e : Fin n =>
            retryCount K (K.step a e) T)).sum <=
        (List.ofFn
          (fun e : Fin n =>
            failureCount vstep (vstep v e) T)).sum
      apply ofFn_sum_le
      intro e
      cases hv : vstep v e with
      | success =>
          have hk :=
            hsim.success a v e hrel hv
          rw [hk]
          exact
            Nat.le_of_eq
              (by
                rw [
                  longRetainedFailureCountSuccessZero
                    vstep T]
                cases T <;> rfl)
      | failure =>
          have hp :=
            longRetainedRetryCount_le_pow
              K (K.step a e) T
          rw [
            longRetainedFailureCountFailurePow
              vstep T]
          exact hp
      | active v' =>
          obtain ⟨a', hk, hr⟩ :=
            hsim.active a v e v' hrel hv
          rw [hk]
          exact ih a' v' hr

/-- Success-plus-active mass of the original vulnerable tree is no larger
than raw long-attempt nonretry mass. -/
theorem longRetainedNonretry_le_attemptNonretry
    {A S V : Type} {n : Nat}
    (K : RetryKernel A S n)
    (vstep : V -> Fin n -> StopNode V)
    (rel : A -> V -> Prop)
    (hsim :
      LongRetainedFailureSimulation
        K vstep rel)
    (a : A) (v : V)
    (hrel : rel a v) (T : Nat) :
    activeCount vstep (.active v) T +
        successCount vstep (.active v) T <=
      attemptNonRetryCount K a T := by
  have hr :=
    longRetainedRetry_le_failure_of_sim
      K vstep rel hsim a v hrel T
  have hvpart :=
    node_count_partition
      vstep (.active v) T
  have hkpart :=
    retryCount_add_attemptNonRetryCount_eq_pow
      K a T
  omega

/-- This is the requested raw-mass domination statement.  Note that its
right-hand stopped tree is the original vulnerableStep tree, i.e. the tree
appearing after weighted change of measure has been transferred back from
qStep. -/
theorem longFullMassFrom_dominates_vulnerable
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (x : VulnerableState F)
    (hrel : longRetainedVulnerableRel F a x) :
    forall T,
      activeCount
          (vulnerableStep hSealed F)
          (.active x) T +
        successCount
          (vulnerableStep hSealed F)
          (.active x) T <=
      longFullMassFrom ring F a T := by
  intro T
  rw [longFullMassFrom_eq_attemptNonRetryCount]
  exact
    longRetainedNonretry_le_attemptNonretry
      (longAttemptKernel ring F)
      (vulnerableStep hSealed F)
      (longRetainedVulnerableRel F)
      (longRetainedVulnerableSimulation
        hSealed ring F)
      a x hrel T

/-! ## 3. The first-cut payload bridge -/

/-- Remaining physical/provenance bridge.

RetainedState packages exactly the facts needed by the retained denominator:
the File-5 VulnerableState proof payload, a live attacker coordinate p, and
F.a-p <= 2*F.b.  At the literal first incident-win cut the target phase must
be Dummy(0).

The subtree simulation itself is already proved above.  Thus this Prop is only
the root reconstruction from the first-cut carrier.
-/
def LongRetainedControlBridge : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s a,
        LongAttemptFirstIncidentGood
          ring F s a ->
        longIncidentWonCut ring F a = true ->
        Exists fun r : RetainedState F =>
          And
            (r.base.targetPhase = .dummy 0)
            (longRetainedVulnerableRel
              F a r.base)

/-- The aggregate domination furnished by the bridge. -/
theorem longRetainedControlBridge_mass
    (h : LongRetainedControlBridge)
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (s : Config n)
    (a : LongAttemptState ring F)
    (hfirst :
      LongAttemptFirstIncidentGood
        ring F s a)
    (hcut :
      longIncidentWonCut ring F a = true) :
    Exists fun r : RetainedState F =>
      And
        (r.base.targetPhase = .dummy 0)
        (And
          (longRetainedVulnerableRel
            F a r.base)
          (forall T,
            activeCount
                (vulnerableStep hSealed F)
                (.active r.base) T +
              successCount
                (vulnerableStep hSealed F)
                (.active r.base) T <=
            longFullMassFrom ring F a T)) := by
  rcases
      h hSealed ring F hb hab s a
        hfirst hcut with
    ⟨r, htarget, hrel⟩
  refine ⟨r, htarget, hrel, ?_⟩
  intro T
  exact
    longFullMassFrom_dominates_vulnerable
      hSealed ring F a r.base hrel T

/-! ## 4. Controlled retained cost and denominator-four counting -/

def retainedBridgeTargetServiceActive
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0)
    (x : VulnerableState F) : Bool :=
  match x.targetPhase with
  | .dummy _ => true
  | .ret _ => true
  | .ready => false
  | .live _ => false

def retainedBridgeTargetServiceRequired
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0)
    (x : VulnerableState F) : Fin n :=
  targetServiceEdge F x

theorem retainedBridgeTargetServiceCharge_eq
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 <= F.b)
    (x : VulnerableState F) (e : Fin n) :
    targetServiceCharge F hb (.active x) e =
      serviceCharge
        (retainedBridgeTargetServiceActive F)
        (retainedBridgeTargetServiceRequired F)
        x e := by
  cases hph : x.targetPhase with
  | ready =>
      simp [targetServiceCharge, serviceCharge,
        retainedBridgeTargetServiceActive,
        retainedBridgeTargetServiceRequired, hph]
  | live p =>
      simp [targetServiceCharge, serviceCharge,
        retainedBridgeTargetServiceActive,
        retainedBridgeTargetServiceRequired, hph]
  | dummy p =>
      have hnot : x.targetPhase ≠ .ready := by
        simp [hph]
      have heff :=
        targetRedirection_effective_of_not_ready
          F hb x e hnot
      simp [targetServiceCharge, serviceCharge,
        retainedBridgeTargetServiceActive,
        retainedBridgeTargetServiceRequired,
        targetServiceEdge, hph, heff, beq_iff_eq]
  | ret q =>
      have hnot : x.targetPhase ≠ .ready := by
        simp [hph]
      have heff :=
        targetRedirection_effective_of_not_ready
          F hb x e hnot
      simp [targetServiceCharge, serviceCharge,
        retainedBridgeTargetServiceActive,
        retainedBridgeTargetServiceRequired,
        targetServiceEdge, hph, heff, beq_iff_eq]

theorem retainedBridgeTargetServiceWordCount_eq
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 <= F.b)
    (z : StopNode (VulnerableState F))
    (w : List (Fin n)) :
    targetServiceWordCount hSealed F hb z w =
      wordCharge
        (qStep hSealed F hb)
        (serviceCharge
          (retainedBridgeTargetServiceActive F)
          (retainedBridgeTargetServiceRequired F))
        z w := by
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
          simp only [
            targetServiceWordCount,
            wordCharge]
          rw [
            retainedBridgeTargetServiceCharge_eq
              F hb x e]
          exact
            congrArg
              (serviceCharge
                  (retainedBridgeTargetServiceActive F)
                  (retainedBridgeTargetServiceRequired F)
                  x e + ·)
              (ih (qStep hSealed F hb x e))

/-- The named retainedTrial_cost_nr producer on the RetainedState kernel. -/
theorem longRetainedControlledCost
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 <= F.b)
    (r : RetainedState F) :
    forall T,
      truncatedActiveCostNumerator
          (retainedStep hSealed F hb)
          (.active r) T <=
        n ^ T * (n * (F.a - r.p)) := by
  exact
    retainedTrial_cost_nr
      hSealed F hb
      (controlRowSpec_proved hSealed F hb)
      r

/-- For the change-of-measure tree itself we need the same n*(a-p) cost
bound on qStep.  It is the live-p specialization of the attacker Bellman row.
This is the type-aligned companion of retainedTrial_cost_nr. -/
theorem longRetainedQTrialCost
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 <= F.b)
    (r : RetainedState F) :
    forall T,
      truncatedActiveCostNumerator
          (qStep hSealed F hb)
          (.active r.base) T <=
        n ^ T * (n * (F.a - r.p)) := by
  intro T
  have hrows :
      ControlRowSpec hSealed F hb :=
    controlRowSpec_proved hSealed F hb
  have hraw :=
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (qStep hSealed F hb)
      1
      (attackerPotential F)
      (attackerPotential_super
        hSealed F hb hrows)
      (.active r.base) T
  have h0 :
      truncatedActiveCostNumerator
          (qStep hSealed F hb)
          (.active r.base) T <=
        n ^ T *
          attackerPotential F (.active r.base) := by
    simpa using hraw
  simpa
    [attackerPotential, attackerCoeff, r.phase_eq]
    using h0

theorem longRetainedVulnerableCollapseMoment
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (r : RetainedState F)
    (hstart : r.base.targetPhase = .dummy 0)
    (T : Nat) :
    collapseCountNumerator
        (vulnerableStep hSealed F)
        (targetRedirection F hb)
        (.active r.base) T <=
      2 * n ^ T := by
  have hrows :
      ControlRowSpec hSealed F hb :=
    controlRowSpec_proved hSealed F hb
  have hcycle :
      forall w : List (Fin n),
        w.length = T ->
        (2 * F.b - 1) *
            ControlledSchedulerMass.eventCount
              (ControlledSchedulerMass.controlledStep
                (vulnerableStep hSealed F)
                (targetRedirection F hb))
              (targetRedirection F hb)
              (.active r.base) w <=
          wordCharge
            (ControlledSchedulerMass.controlledStep
              (vulnerableStep hSealed F)
              (targetRedirection F hb))
            (serviceCharge
              (retainedBridgeTargetServiceActive F)
              (retainedBridgeTargetServiceRequired F))
            (.active r.base) w := by
    intro w _hw
    have hp :=
      target_cycle_pathwise
        hSealed F hb hrows
        r.base hstart w
    rw [
      retainedBridgeTargetServiceWordCount_eq
        hSealed F hb (.active r.base) w] at hp
    simpa [qStep] using hp
  have hnum :=
    collapseNumerator_le_serviceNumerator
      (vulnerableStep hSealed F)
      (targetRedirection F hb)
      (retainedBridgeTargetServiceActive F)
      (retainedBridgeTargetServiceRequired F)
      (2 * F.b - 1)
      (.active r.base) T hcycle
  have hcycleNumerator :
      (2 * F.b - 1) *
          collapseCountNumerator
            (vulnerableStep hSealed F)
            (targetRedirection F hb)
            (.active r.base) T <=
        edgeChargeNumerator
          (qStep hSealed F hb)
          (serviceCharge
            (retainedBridgeTargetServiceActive F)
            (retainedBridgeTargetServiceRequired F))
          (.active r.base) T := by
    simpa [targetServiceNumerator, qStep]
      using hnum
  have hcost :=
    longRetainedQTrialCost
      hSealed F hb r T
  have hn0 : 0 < n := by
    have hn2 := frame_two_le_control F
    omega
  have hmoment :=
    collapse_moment_cleared
      (qStep hSealed F hb)
      (retainedBridgeTargetServiceActive F)
      (retainedBridgeTargetServiceRequired F)
      (collapseCountNumerator
        (vulnerableStep hSealed F)
        (targetRedirection F hb))
      (2 * F.b - 1)
      (F.a - r.p)
      hn0
      (.active r.base) T
      hcycleNumerator hcost
  exact
    retained_collapse_moment
      F.b
      (F.a - r.p)
      (collapseCountNumerator
        (vulnerableStep hSealed F)
        (targetRedirection F hb)
        (.active r.base) T)
      (n ^ T)
      hb r.remaining_le hmoment

/-! ## 5. W2 and change of measure -/

theorem eventCount_le_length_longRetained
    {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S)
    (w : List (Fin n)) :
    ControlledSchedulerMass.eventCount step r z w <=
      w.length := by
  induction w generalizing z with
  | nil =>
      simp [ControlledSchedulerMass.eventCount]
  | cons e es ih =>
      have hc :
          ControlledSchedulerMass.eventCost r z e <= 1 := by
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
      simp only [
        ControlledSchedulerMass.eventCount,
        List.length_cons]
      omega

theorem runWord_ne_failure_longRetained
    {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S)
    (hstep :
      forall s e, step s e ≠ .failure)
    (z : StopNode S)
    (hz : z ≠ .failure)
    (w : List (Fin n)) :
    ControlledSchedulerMass.runWord step z w ≠
      .failure := by
  induction w generalizing z with
  | nil =>
      exact hz
  | cons e es ih =>
      simp only [ControlledSchedulerMass.runWord]
      apply ih
      cases z with
      | active s =>
          exact hstep s e
      | success =>
          simp [stepNode]
      | failure =>
          exact False.elim (hz rfl)

theorem W2_wordSum_longRetained
    {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S)
    (hz : z ≠ .failure)
    (hcontrolled :
      forall s e,
        ControlledSchedulerMass.controlledStep
          step r s e ≠ .failure)
    (T : Nat) :
    4 * (2 ^ T * n ^ T) <=
      8 * weightedQNonRetryNumerator
            step r z T +
        2 ^ T *
          collapseCountNumerator step r z T := by
  let q :=
    ControlledSchedulerMass.controlledStep step r
  have hpoint :
      forall i : Fin (n ^ T),
        4 * 2 ^ T <=
          8 *
              powSuccessOrActive
                (ControlledSchedulerMass.runWord
                  q z
                  (FixedSpanRenewalPayload.rawWord
                    n T i))
                (T -
                  ControlledSchedulerMass.eventCount
                    q r z
                    (FixedSpanRenewalPayload.rawWord
                      n T i)) +
            2 ^ T *
              ControlledSchedulerMass.eventCount
                q r z
                (FixedSpanRenewalPayload.rawWord
                  n T i) := by
    intro i
    let w :=
      FixedSpanRenewalPayload.rawWord n T i
    let N :=
      ControlledSchedulerMass.eventCount
        q r z w
    have hN : N <= T := by
      have h :=
        eventCount_le_length_longRetained
          q r z w
      simpa [N, w,
        FixedSpanRenewalPayload.rawWord_length]
        using h
    have hw :=
      W2_scaled N T hN
    have hnf :
        ControlledSchedulerMass.runWord
            q z w ≠ .failure :=
      runWord_ne_failure_longRetained
        q hcontrolled z hz w
    cases hr :
        ControlledSchedulerMass.runWord q z w with
    | active y =>
        simpa
          [powSuccessOrActive, hr, N, w,
            Nat.mul_comm]
          using hw
    | success =>
        simpa
          [powSuccessOrActive, hr, N, w,
            Nat.mul_comm]
          using hw
    | failure =>
        exact False.elim (hnf hr)
  have hsum :=
    ofFn_sum_le
      (fun _ : Fin (n ^ T) =>
        4 * 2 ^ T)
      (fun i : Fin (n ^ T) =>
        8 *
            powSuccessOrActive
              (ControlledSchedulerMass.runWord
                q z
                (FixedSpanRenewalPayload.rawWord
                  n T i))
              (T -
                ControlledSchedulerMass.eventCount
                  q r z
                  (FixedSpanRenewalPayload.rawWord
                    n T i)) +
          2 ^ T *
            ControlledSchedulerMass.eventCount
              q r z
              (FixedSpanRenewalPayload.rawWord
                n T i))
      hpoint
  rw [ofFn_sum_const, ofFn_sum_add,
    ofFn_sum_mul_left, ofFn_sum_mul_left] at hsum
  rw [
    FixedSpanRenewalPayload.rawWord_sum
      n T
      (fun w =>
        powSuccessOrActive
          (ControlledSchedulerMass.runWord
            q z w)
          (T -
            ControlledSchedulerMass.eventCount
              q r z w)),
    FixedSpanRenewalPayload.rawWord_sum
      n T
      (fun w =>
        ControlledSchedulerMass.eventCount
          q r z w)
  ] at hsum
  have hsum' :
      n ^ T * (4 * 2 ^ T) <=
        8 *
            weightedQNonRetryNumerator
              step r z T +
          2 ^ T *
            collapseCountNumerator
              step r z T := by
    simpa [q, weightedQNonRetryNumerator,
      collapseCountNumerator] using hsum
  calc
    4 * (2 ^ T * n ^ T) =
        n ^ T * (4 * 2 ^ T) := by
      ac_rfl
    _ <=
      8 *
          weightedQNonRetryNumerator
            step r z T +
        2 ^ T *
          collapseCountNumerator
            step r z T :=
      hsum'

theorem nonretry_mass_four_of_collapse_longRetained
    {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S)
    (r : ControlledSchedulerMass.Redirection S n)
    (z : StopNode S)
    (hz : z ≠ .failure)
    (hcontrolled :
      forall s e,
        ControlledSchedulerMass.controlledStep
          step r s e ≠ .failure)
    (T : Nat)
    (hcollapse :
      collapseCountNumerator step r z T <=
        2 * n ^ T) :
    n ^ T <=
      4 *
        (activeCount step z T +
          successCount step z T) := by
  have hw :=
    W2_wordSum_longRetained
      step r z hz hcontrolled T
  let P := 2 ^ T * n ^ T
  let Q :=
    2 ^ T *
      collapseCountNumerator step r z T
  let W :=
    weightedQNonRetryNumerator step r z T
  have hw' :
      4 * P <= 8 * W + Q := by
    simpa [P, Q, W] using hw
  have hc0 :=
    Nat.mul_le_mul_left (2 ^ T) hcollapse
  have hc :
      Q <= 2 * P := by
    calc
      Q =
          2 ^ T *
            collapseCountNumerator
              step r z T := rfl
      _ <=
          2 ^ T * (2 * n ^ T) :=
        hc0
      _ = 2 * P := by
        simp [P]
        ac_rfl
  have hP :
      P <= 4 * W := by
    omega
  have hchange :=
    weighted_changeOfMeasure_nonretry
      step r z T
  have hchange4 :=
    Nat.mul_le_mul_left 4 hchange
  have hscaled :
      2 ^ T * n ^ T <=
        2 ^ T *
          (4 *
            (activeCount step z T +
              successCount step z T)) := by
    calc
      2 ^ T * n ^ T = P := rfl
      _ <= 4 * W := hP
      _ <=
        4 *
          (2 ^ T *
            (activeCount step z T +
              successCount step z T)) :=
        hchange4
      _ =
        2 ^ T *
          (4 *
            (activeCount step z T +
              successCount step z T)) := by
        ac_rfl
  have hpow : 0 < 2 ^ T :=
    Nat.pow_pos (by omega)
  exact
    Nat.le_of_mul_le_mul_left
      hscaled hpow

theorem longRetainedVulnerableQuarter
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (r : RetainedState F)
    (hstart : r.base.targetPhase = .dummy 0) :
    forall T,
      n ^ T <=
        4 *
          (activeCount
              (vulnerableStep hSealed F)
              (.active r.base) T +
            successCount
              (vulnerableStep hSealed F)
              (.active r.base) T) := by
  intro T
  apply
    nonretry_mass_four_of_collapse_longRetained
      (vulnerableStep hSealed F)
      (targetRedirection F hb)
      (.active r.base)
      (by simp)
      ?_ T
      (longRetainedVulnerableCollapseMoment
        hSealed F hb r hstart T)
  intro x e
  simpa [qStep] using
    (qStep_no_failure
      hSealed F hb x e)

/-! ## 6. Conjunct 4 from the bridge -/

theorem longFullFactor_of_bridge
    (h : LongRetainedControlBridge) :
    forall (hSealed : SealedStepSpec),
      forall {n : Nat} (ring : DirectedRing n)
        {C0 : Config n} (F : TripleFrame ring C0),
        2 <= F.b ->
        2 * F.b + 1 <= F.a ->
        forall s a,
          LongAttemptFirstIncidentGood
            ring F s a ->
          longIncidentWonCut ring F a = true ->
          forall T,
            n ^ T <=
              4 * longFullMassFrom ring F a T := by
  intro hSealed n ring C0 F hb hab
  intro s a hfirst hcut T
  rcases
      longRetainedControlBridge_mass
        h hSealed ring F hb hab
        s a hfirst hcut with
    ⟨r, hstart, hrel, hdom⟩
  have hquarter :=
    longRetainedVulnerableQuarter
      hSealed F hb r hstart T
  exact
    Nat.le_trans
      hquarter
      (Nat.mul_le_mul_left 4 (hdom T))

/-
The theorem longRetainedControlBridge_proved is intentionally not claimed
here.  The remaining leaf is the root-payload reconstruction:

  first incident cut
    -> retained target = Dummy(0)
    -> PhaseHolds for both sectors
    -> targetUnshielded
    -> attackerPhase = live p with F.a-p <= 2*F.b.

Once those fields are assembled into RetainedState, every subtree and counting
step is closed above.
-/

#print axioms PPL.Convergence.LDLocal.longRetainedVulnerableSimulation
#print axioms PPL.Convergence.LDLocal.longRetainedRetry_le_failure_of_sim
#print axioms PPL.Convergence.LDLocal.longRetainedNonretry_le_attemptNonretry
#print axioms PPL.Convergence.LDLocal.longFullMassFrom_dominates_vulnerable
#print axioms PPL.Convergence.LDLocal.longRetainedControlBridge_mass
#print axioms PPL.Convergence.LDLocal.longRetainedControlledCost
#print axioms PPL.Convergence.LDLocal.longRetainedQTrialCost
#print axioms PPL.Convergence.LDLocal.longRetainedVulnerableCollapseMoment
#print axioms PPL.Convergence.LDLocal.W2_wordSum_longRetained
#print axioms PPL.Convergence.LDLocal.nonretry_mass_four_of_collapse_longRetained
#print axioms PPL.Convergence.LDLocal.longRetainedVulnerableQuarter
#print axioms PPL.Convergence.LDLocal.longFullFactor_of_bridge

end PPL.Convergence.LDLocal

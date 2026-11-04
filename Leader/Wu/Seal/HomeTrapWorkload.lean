import Leader.Wu.Seal.HomeTrapCurrent

/-!
# Successful-current workloads for the seal-sweep home trap

The scheduler clock is not a useful progress variable for the exact R82
home/front quotient: a selected edge may stutter.  This file instead records
the successful current through every edge.  On a collision-free word, the
residual workload at a site,

`initial front + incoming successful current - outgoing successful current`,

is exactly its endpoint front occupancy.  Fixed homes and two neighboring
unit workloads therefore characterize a loaded home trap at the endpoint.
Together with exact home-count accounting, this gives an equivalent
successful-current form of the remaining ready-endpoint exposure premise.

No stochastic lower bound is asserted here.  The last definition is the
precise finite counting statement still needed from a tagged-gap or queue
argument.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepHomeTrapWorkloadSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPartialDynamicSweepLockSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepMixedNormalizerSol
open PPartialSealSweepIidDriftObstructionSol
open PPartialSealSweepIidCoalescenceBarrierSol
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPLLEpochVoterTwoDomain
open PPartialSealSweepConcurrencyNoGoSol
open PPartialSealSweepConcurrentCounterfamilySol
open SealSweepConcurrentCycleSol
open SealSweepConcurrentCycleSol.SealMacroState
open PPLLSchedulerBlocks

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## A workload made only from successful crossings -/

/-- Residual front workload at `i`: initial occupancy plus successful incoming
crossings, minus successful outgoing crossings.  Unlike a raw scheduler-clock
count, every term records an actual `10 -> 01` front move. -/
def homeFrontCurrentWorkload
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (word : DetSchedule n) (i : Fin n) : Nat :=
  homeFrontOccupancy X i +
      homeFrontSuccessfulCrossings ring X word (ring.leftNeighbor i) -
    homeFrontSuccessfulCrossings ring X word i

/-- The continuity equation says exactly that collision-free residual
workload is the endpoint front bit. -/
theorem homeFrontCurrentWorkload_eq_endpointOccupancy
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (word : DetSchedule n)
    (hnoHit : HomeFrontNoHitSchedule ring X word) (i : Fin n) :
    homeFrontCurrentWorkload ring X word i =
      homeFrontOccupancy
        (runLocalSchedule ring sealSweepHomeFrontPair X word) i := by
  have hbalance := homeFrontSuccessfulCrossings_conservation
    ring hn X word hnoHit i
  unfold homeFrontCurrentWorkload
  omega

/-- A collision-free workload is Boolean: it can only be zero or one. -/
theorem homeFrontCurrentWorkload_le_one
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (word : DetSchedule n)
    (hnoHit : HomeFrontNoHitSchedule ring X word) (i : Fin n) :
    homeFrontCurrentWorkload ring X word i ≤ 1 := by
  rw [homeFrontCurrentWorkload_eq_endpointOccupancy
    ring hn X word hnoHit i]
  unfold homeFrontOccupancy
  split <;> omega

/-- Unit residual workload is equivalent to endpoint front occupancy. -/
theorem homeFrontCurrentWorkload_eq_one_iff_endpointFront
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (word : DetSchedule n)
    (hnoHit : HomeFrontNoHitSchedule ring X word) (i : Fin n) :
    homeFrontCurrentWorkload ring X word i = 1 ↔
      (runLocalSchedule ring sealSweepHomeFrontPair X word i).2 = true := by
  rw [homeFrontCurrentWorkload_eq_endpointOccupancy
    ring hn X word hnoHit i]
  unfold homeFrontOccupancy
  cases hfront :
      (runLocalSchedule ring sealSweepHomeFrontPair X word i).2 <;>
    simp

/-! ## Homes are fixed until the first hit -/

/-- A non-hit pair update preserves both home bits. -/
theorem sealSweepHomeFrontPair_home_eq_of_noHit
    (l r : SealSweepHomeFrontSite)
    (hnoHit : sealSweepFrontHitsHomePair l r = false) :
    (sealSweepHomeFrontPair l r).1.1 = l.1 ∧
      (sealSweepHomeFrontPair l r).2.1 = r.1 := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [sealSweepFrontHitsHomePair, sealSweepHomeFrontPair] at hnoHit ⊢

/-- One non-hit local step fixes the home bit at every site. -/
theorem homeFrontLocalStep_home_eq_of_noHit
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (e i : Fin n)
    (hnoHit : sealSweepFrontHitsHomePair
      (X e) (X (ring.rightNeighbor e)) = false) :
    (localStep ring sealSweepHomeFrontPair X e i).1 = (X i).1 := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hpair := sealSweepHomeFrontPair_home_eq_of_noHit
    (X e) (X j) (by simpa [j] using hnoHit)
  by_cases hie : i = e
  · subst i
    simpa [localStep, j] using hpair.1
  · by_cases hij : i = j
    · subst i
      simpa [localStep, j, hje] using hpair.2
    · simp [localStep, j, hie, hij]

/-- Along a collision-free word every home remains at its original site. -/
theorem HomeFrontNoHitSchedule_home_preserved
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (word : DetSchedule n)
    (hnoHit : HomeFrontNoHitSchedule ring X word) (i : Fin n) :
    (runLocalSchedule ring sealSweepHomeFrontPair X word i).1 = (X i).1 := by
  induction word generalizing X with
  | nil => rfl
  | cons e rest ih =>
      rcases hnoHit with ⟨hfirst, hrest⟩
      simp only [runLocalSchedule]
      calc
        (runLocalSchedule ring sealSweepHomeFrontPair
            (localStep ring sealSweepHomeFrontPair X e) rest i).1 =
            (localStep ring sealSweepHomeFrontPair X e i).1 :=
          ih (X := localStep ring sealSweepHomeFrontPair X e) hrest
        _ = (X i).1 :=
          homeFrontLocalStep_home_eq_of_noHit ring hn X e i hfirst

/-! ## Exact endpoint characterization -/

/-- Successful-current form of a loaded endpoint trap.  The right endpoint
is one of the fixed source homes and both adjacent residual workloads are one. -/
def HomeFrontCurrentReady
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (word : DetSchedule n) : Prop :=
  ∃ e : Fin n,
    (X (ring.rightNeighbor e)).1 = true ∧
      homeFrontCurrentWorkload ring X word e = 1 ∧
      homeFrontCurrentWorkload ring X word (ring.rightNeighbor e) = 1

/-- Before a hit, the current-ready certificate is exactly the ordinary
loaded-home predicate at the endpoint. -/
theorem homeFrontCurrentReady_iff_endpointReady
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (word : DetSchedule n)
    (hnoHit : HomeFrontNoHitSchedule ring X word) :
    HomeFrontCurrentReady ring X word ↔
      HomeFrontHitReady ring
        (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
  constructor
  · rintro ⟨e, hhome, hleft, hright⟩
    refine ⟨e, ?_⟩
    have hleft' :=
      (homeFrontCurrentWorkload_eq_one_iff_endpointFront
        ring hn X word hnoHit e).1 hleft
    have hright' :=
      (homeFrontCurrentWorkload_eq_one_iff_endpointFront
        ring hn X word hnoHit (ring.rightNeighbor e)).1 hright
    have hhome' := HomeFrontNoHitSchedule_home_preserved
      ring hn X word hnoHit (ring.rightNeighbor e)
    simp [sealSweepFrontHitsHomePair, hleft', hright', hhome'.trans hhome]
  · rintro ⟨e, he⟩
    have he' := he
    simp [sealSweepFrontHitsHomePair] at he'
    rcases he' with ⟨⟨hleft, hhome⟩, hright⟩
    refine ⟨e, ?_, ?_, ?_⟩
    · have hpreserved := HomeFrontNoHitSchedule_home_preserved
        ring hn X word hnoHit (ring.rightNeighbor e)
      exact hpreserved.symm.trans hhome
    · exact (homeFrontCurrentWorkload_eq_one_iff_endpointFront
        ring hn X word hnoHit e).2 hleft
    · exact (homeFrontCurrentWorkload_eq_one_iff_endpointFront
        ring hn X word hnoHit (ring.rightNeighbor e)).2 hright

/-! ## A hit is exactly strict endpoint home loss -/

/-- On a positive quotient trajectory, a word is collision-free exactly when
its endpoint retains the source home count. -/
theorem positiveHomeFrontState_noHit_iff_homeCount_eq
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (word : DetSchedule n) :
    HomeFrontNoHitSchedule ring X word ↔
      homeFrontHomeCount
          (runLocalSchedule ring sealSweepHomeFrontPair X word) =
        homeFrontHomeCount X := by
  induction word generalizing X with
  | nil => simp [HomeFrontNoHitSchedule, runLocalSchedule]
  | cons e rest ih =>
      let Y := localStep ring sealSweepHomeFrontPair X e
      have hY : SealSweepPositiveHomeFrontState
          (psi := psi) (kappa := kappa) (tau := tau) ring Y :=
        positiveHomeFrontState_localStep ring X hX e
      have hstepLe : homeFrontHomeCount Y ≤ homeFrontHomeCount X := by
        have h := positiveHomeFrontState_run_homeCount_le ring X hX [e]
        simpa [Y, runLocalSchedule] using h
      have htailLe : homeFrontHomeCount
          (runLocalSchedule ring sealSweepHomeFrontPair Y rest) ≤
          homeFrontHomeCount Y :=
        positiveHomeFrontState_run_homeCount_le ring Y hY rest
      have hstepIff := positiveHomeFrontState_homeCount_localStep_lt_iff
        ring hn X hX e
      change
        (sealSweepFrontHitsHomePair
              (X e) (X (ring.rightNeighbor e)) = false ∧
            HomeFrontNoHitSchedule ring Y rest) ↔
          homeFrontHomeCount
              (runLocalSchedule ring sealSweepHomeFrontPair Y rest) =
            homeFrontHomeCount X
      constructor
      · rintro ⟨hfirst, hrest⟩
        have hnotLt : ¬ homeFrontHomeCount Y < homeFrontHomeCount X := by
          rw [hstepIff]
          simp [hfirst]
        have hstepEq : homeFrontHomeCount Y = homeFrontHomeCount X := by
          omega
        have htailEq := (ih (X := Y) hY).1 hrest
        omega
      · intro hfinalEq
        have hfirst : sealSweepFrontHitsHomePair
            (X e) (X (ring.rightNeighbor e)) = false := by
          cases hhit : sealSweepFrontHitsHomePair
              (X e) (X (ring.rightNeighbor e)) with
          | false => rfl
          | true =>
              have hstepLt :
                  homeFrontHomeCount Y < homeFrontHomeCount X :=
                hstepIff.2 hhit
              omega
        have hnotLt : ¬ homeFrontHomeCount Y < homeFrontHomeCount X := by
          rw [hstepIff]
          simp [hfirst]
        have hstepEq : homeFrontHomeCount Y = homeFrontHomeCount X := by
          omega
        have htailEq : homeFrontHomeCount
              (runLocalSchedule ring sealSweepHomeFrontPair Y rest) =
            homeFrontHomeCount Y := by
          omega
        refine ⟨hfirst, ?_⟩
        exact (ih (X := Y) hY).2 htailEq

/-- Equivalently, the complement of no-hit is strict endpoint home loss. -/
theorem positiveHomeFrontState_not_noHit_iff_homeCount_lt
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (word : DetSchedule n) :
    ¬ HomeFrontNoHitSchedule ring X word ↔
      homeFrontHomeCount
          (runLocalSchedule ring sealSweepHomeFrontPair X word) <
        homeFrontHomeCount X := by
  have hle := positiveHomeFrontState_run_homeCount_le ring X hX word
  have heq := positiveHomeFrontState_noHit_iff_homeCount_eq
    ring hn X hX word
  constructor
  · intro hnot
    have hne : homeFrontHomeCount
          (runLocalSchedule ring sealSweepHomeFrontPair X word) ≠
        homeFrontHomeCount X := by
      intro hsamen
      exact hnot (heq.2 hsamen)
    omega
  · intro hlt hnoHit
    have hsame := heq.1 hnoHit
    omega

/-- Exact successful-current certificate for the endpoint test: either a hit
has already occurred, or the collision-free workload ends with a loaded home. -/
theorem positiveHomeFrontState_dropOrReady_iff_current
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (word : DetSchedule n) :
    homeFrontDropOrReadyEndpointTest ring X
        (runLocalSchedule ring sealSweepHomeFrontPair X word) = true ↔
      ¬ HomeFrontNoHitSchedule ring X word ∨
        HomeFrontCurrentReady ring X word := by
  rw [homeFrontDropOrReadyEndpointTest_spec]
  rw [← positiveHomeFrontState_not_noHit_iff_homeCount_lt
    ring hn X hX word]
  by_cases hnoHit : HomeFrontNoHitSchedule ring X word
  · simp only [hnoHit, not_true_eq_false, false_or]
    exact homeFrontCurrentReady_iff_endpointReady ring hn X word hnoHit |>.symm
  · simp [hnoHit]

/-! ## The exact current-counting target -/

/-- Boolean form of the successful-current certificate. -/
noncomputable def homeFrontCurrentDropOrReadyTest
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (word : DetSchedule n) : Bool := by
  classical
  exact decide
    (¬ HomeFrontNoHitSchedule ring X word ∨
      HomeFrontCurrentReady ring X word)

theorem homeFrontCurrentDropOrReadyTest_spec
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (word : DetSchedule n) :
    homeFrontCurrentDropOrReadyTest ring X word = true ↔
      ¬ HomeFrontNoHitSchedule ring X word ∨
        HomeFrontCurrentReady ring X word := by
  classical
  simp [homeFrontCurrentDropOrReadyTest]

/-- Number of length-`t` scheduler words certified using only successful
currents (with already-hit words included explicitly). -/
noncomputable def homeFrontCurrentDropOrReadyCount
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) (t : Nat) : Nat :=
  (allSchedules n t).countP (homeFrontCurrentDropOrReadyTest ring X)

/-- The current count is exactly the earlier dropped-or-ready endpoint count
on every positive quotient state. -/
theorem positiveHomeFrontState_currentCount_eq_endpointCount
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (t : Nat) :
    homeFrontCurrentDropOrReadyCount ring X t =
      homeFrontDropOrReadyEndpointCount ring X t := by
  unfold homeFrontCurrentDropOrReadyCount
  unfold homeFrontDropOrReadyEndpointCount
  apply List.countP_congr
  intro word _hword
  exact (homeFrontCurrentDropOrReadyTest_spec ring X word).trans
    (positiveHomeFrontState_dropOrReady_iff_current
      ring hn X hX word).symm

/-- Pure successful-current version of the remaining finite-window premise. -/
def SealSweepHomeFrontCurrentReadyExposure
    (ring : DirectedRing n) (horizon favorable : Nat) : Prop :=
  ∀ X : Fin n → SealSweepHomeFrontSite,
    SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X →
    2 ≤ homeFrontHomeCount X →
    favorable ≤ homeFrontCurrentDropOrReadyCount ring X horizon

/-- The successful-current premise is neither stronger nor weaker than the
ready-endpoint premise: they are extensionally identical on the exact positive
domain. -/
theorem homeFrontCurrentReadyExposure_iff_readyEndpointExposure
    (ring : DirectedRing n) (hn : 1 < n)
    (horizon favorable : Nat) :
    SealSweepHomeFrontCurrentReadyExposure
        (psi := psi) (kappa := kappa) (tau := tau)
        ring horizon favorable ↔
      SealSweepHomeFrontReadyEndpointExposure
        (psi := psi) (kappa := kappa) (tau := tau)
        ring horizon favorable := by
  constructor
  · intro hcurrent X hX hhomes
    rw [← positiveHomeFrontState_currentCount_eq_endpointCount
      ring hn X hX horizon]
    exact hcurrent X hX hhomes
  · intro hready X hX hhomes
    rw [positiveHomeFrontState_currentCount_eq_endpointCount
      ring hn X hX horizon]
    exact hready X hX hhomes

/-- The exact cubic half-mass statement after eliminating endpoint state from
the stochastic premise.  A tagged-gap proof may work entirely with successful
crossing counts and this definition. -/
def SealSweepHomeFrontCubicCurrentReadyExposure
    (ring : DirectedRing n) : Prop :=
  SealSweepHomeFrontCurrentReadyExposure
    (psi := psi) (kappa := kappa) (tau := tau) ring
    (homeFrontCubicHorizon n) (homeFrontCubicHalfFavorable n)

theorem homeFrontCubicCurrentReadyExposure_iff_readyHalf
    (ring : DirectedRing n) (hn : 1 < n) :
    SealSweepHomeFrontCubicCurrentReadyExposure
        (psi := psi) (kappa := kappa) (tau := tau) ring ↔
      SealSweepHomeFrontCubicReadyHalfExposure
        (psi := psi) (kappa := kappa) (tau := tau) ring := by
  exact homeFrontCurrentReadyExposure_iff_readyEndpointExposure
    ring hn _ _

/-! ## The exact one-step service dichotomy -/

/-- At the carrier level, simultaneous absence of a quotient front move and a
front hit means that the exact R82 pair transition is a stutter. -/
theorem P_partialSealSweep_eq_self_of_no_frontMove_no_hit
    (l r : SealSweepState psi kappa tau)
    (hmove : sealSweepFrontMovePair
      (sealSweepHomeFrontSite l) (sealSweepHomeFrontSite r) = false)
    (hhit : sealSweepFrontHitsHomePair
      (sealSweepHomeFrontSite l) (sealSweepHomeFrontSite r) = false) :
    P_partialSealSweep l r = (l, r) := by
  cases hl : sweepLockLeader l <;>
    cases hlc : l.2 <;>
    cases hr : sweepLockLeader r <;>
    cases hrc : r.2
  all_goals
    simp only [sweepLockLeader] at hl hr
    simp [sealSweepFrontMovePair, sealSweepFrontHitsHomePair,
      sealSweepHomeFrontSite, sealSweepHomeBit, sealSweepFrontBit,
      P_partialSealSweep, hl, hlc, hr, hrc, sweepLockLeader] at hmove hhit ⊢

private theorem homeFrontPhysicalLocalStep_eq_self_of_pair_eq
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hpair : P_partialSealSweep (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))) :
    localStep ring P_partialSealSweep C e = C := by
  funext i
  by_cases hie : i = e
  · subst i
    simp [localStep, hpair]
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      have hne : ring.rightNeighbor e ≠ e := by
        intro h
        exact hie h
      simp [localStep, hne, hpair]
    · simp [localStep, hie, hij]

/-- Every exact positive quotient state either already exposes a loaded home
or has at least one edge that performs a genuine successful crossing.  The
proof uses the existing mixed-rank descent only to select an edge: if both its
move and hit bits were false, the exact physical step would stutter and could
not decrease that rank. -/
theorem positiveHomeFrontState_ready_or_successfulMove
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X) :
    HomeFrontHitReady ring X ∨
      ∃ e : Fin n, sealSweepFrontMovePair
        (X e) (X (ring.rightNeighbor e)) = true := by
  obtain ⟨C, hdesc, hprojection⟩ := hX
  have hbalancedLeader :=
    positiveDescendant_balanced_hasLeader ring C hdesc
  by_cases hclosed : SealSweepAllClosed C
  · obtain ⟨e, heLeader⟩ := hbalancedLeader.2
    cases hrLeader : sweepLockLeader (C (ring.rightNeighbor e)) with
    | false =>
        right
        refine ⟨e, ?_⟩
        rw [← hprojection]
        simp [sealSweepHomeFrontConfig, sealSweepHomeFrontSite,
          sealSweepHomeBit, sealSweepFrontBit, sealSweepFrontMovePair,
          heLeader, hrLeader, hclosed e,
          hclosed (ring.rightNeighbor e)]
    | true =>
        left
        refine ⟨e, ?_⟩
        rw [← hprojection]
        simp [sealSweepHomeFrontConfig, sealSweepHomeFrontSite,
          sealSweepHomeBit, sealSweepFrontBit,
          sealSweepFrontHitsHomePair, heLeader, hrLeader,
          hclosed e, hclosed (ring.rightNeighbor e)]
  · obtain ⟨e, _hbalancedAfter, _hleaderAfter, hrank⟩ :=
      sealSweep_mixedRank_descent ring C hbalancedLeader.1
        hbalancedLeader.2 hclosed
    cases hmove : sealSweepFrontMovePair
        (sealSweepHomeFrontSite (C e))
        (sealSweepHomeFrontSite (C (ring.rightNeighbor e))) with
    | true =>
        right
        refine ⟨e, ?_⟩
        rw [← hprojection]
        exact hmove
    | false =>
        cases hhit : sealSweepFrontHitsHomePair
            (sealSweepHomeFrontSite (C e))
            (sealSweepHomeFrontSite (C (ring.rightNeighbor e))) with
        | true =>
            left
            refine ⟨e, ?_⟩
            rw [← hprojection]
            exact hhit
        | false =>
            have hpair := P_partialSealSweep_eq_self_of_no_frontMove_no_hit
              (C e) (C (ring.rightNeighbor e)) hmove hhit
            have hstep := homeFrontPhysicalLocalStep_eq_self_of_pair_eq
              ring C e hpair
            rw [hstep] at hrank
            omega

/-- Number of edges that currently perform a genuine successful crossing. -/
def homeFrontSuccessfulMoveEdgeCount
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) : Nat :=
  (List.ofFn fun e : Fin n => e).countP (fun e =>
    sealSweepFrontMovePair (X e) (X (ring.rightNeighbor e)))

/-- If the endpoint is not ready, at least one of the `n` iid scheduler choices
is a successful crossing.  Thus the conditional one-step service probability
is at least `1/n`; what remains open is turning repeated service into trap mass. -/
theorem positiveHomeFrontState_one_le_successfulMoveEdgeCount_of_not_ready
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hnotReady : ¬ HomeFrontHitReady ring X) :
    1 ≤ homeFrontSuccessfulMoveEdgeCount ring X := by
  obtain hready | ⟨e, he⟩ :=
    positiveHomeFrontState_ready_or_successfulMove ring X hX
  · exact False.elim (hnotReady hready)
  · unfold homeFrontSuccessfulMoveEdgeCount
    apply List.countP_pos_iff.mpr
    refine ⟨e, ?_, he⟩
    rw [List.mem_ofFn]
    exact ⟨e, rfl⟩

/-- If a state is already ready, one kill edge followed by an arbitrary
length-`t` suffix gives `n^t` favorable words at horizon `1+t`. -/
theorem positiveHomeFrontState_ready_drop_suffix_mass
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hready : HomeFrontHitReady ring X) (t : Nat) :
    n ^ t ≤ localHitCount ring sealSweepHomeFrontPair
      (homeFrontHomeDropTest X) X (1 + t) := by
  have hgood : homeFrontDropOrReadyEndpointTest ring X
      (runLocalSchedule ring sealSweepHomeFrontPair X []) = true := by
    rw [homeFrontDropOrReadyEndpointTest_spec]
    exact Or.inr hready
  obtain ⟨e, he⟩ := homeFrontDropOrReadyEndpoint_has_hit_extension
    ring hn X hX [] hgood
  have he' : hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontHomeDropTest X) X [e] = true := by
    simpa using he
  exact PPartialSealSweepIidComplexitySol.localHitCount_add_lower_of_hit
    ring sealSweepHomeFrontPair (homeFrontHomeDropTest X) X
    1 t [e] (by simp) he'

/-! ## Unbounded balanced-current obstruction

The workload identity is exact, but current magnitude alone still does not
force a trap.  On four sites the word `ACAC` admits the genuine-move cycle
`0,2,1,3`.  Every edge carries one successful crossing per period, while the
endpoint returns to `ACAC`, which is not hit-ready.  Repetition makes all four
currents arbitrarily large and perfectly equal.
-/

/-- Successful currents split exactly across concatenated scheduler words. -/
theorem homeFrontSuccessfulCrossings_append
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (xs ys : DetSchedule n) (edge : Fin n) :
    homeFrontSuccessfulCrossings ring X (xs ++ ys) edge =
      homeFrontSuccessfulCrossings ring X xs edge +
        homeFrontSuccessfulCrossings ring
          (runLocalSchedule ring sealSweepHomeFrontPair X xs)
          ys edge := by
  induction xs generalizing X with
  | nil => simp [homeFrontSuccessfulCrossings, runLocalSchedule]
  | cons e rest ih =>
      simp only [List.cons_append, homeFrontSuccessfulCrossings,
        runLocalSchedule]
      rw [ih]
      omega

/-- The concrete four-site directed ring used by the balanced-current cycle. -/
theorem homeFrontFourRing : DirectedRing 4 := ⟨by omega⟩

/-- The all-closed two-home source `A C A C`. -/
def homeFrontFourSource : Fin 4 → SealSweepHomeFrontSite :=
  homeFrontACAC 4 (by omega)

/-- One genuine-move period: both even edges, then both odd edges. -/
def homeFrontFourCycleWord : DetSchedule 4 := [0, 2, 1, 3]

/-- Recursive concatenation of `cycles` complete periods. -/
def homeFrontFourRepeatedCycle : Nat → DetSchedule 4
  | 0 => []
  | cycles + 1 =>
      homeFrontFourRepeatedCycle cycles ++ homeFrontFourCycleWord

/-- `cycles` complete four-edge periods have exact scheduler horizon
`4 * cycles`. -/
theorem homeFrontFourRepeatedCycle_length (cycles : Nat) :
    (homeFrontFourRepeatedCycle cycles).length = 4 * cycles := by
  induction cycles with
  | zero => rfl
  | succ cycles ih =>
      simp [homeFrontFourRepeatedCycle, homeFrontFourCycleWord, ih,
        Nat.mul_succ]

private theorem homeFrontFinFour_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
    omega
  rcases hi with hi | hi | hi | hi
  · exact Or.inl (Fin.ext hi)
  · exact Or.inr (Or.inl (Fin.ext hi))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext hi)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext hi)))

/-- One period returns exactly to `A C A C`. -/
theorem homeFrontFourCycle_run_eq :
    runLocalSchedule homeFrontFourRing sealSweepHomeFrontPair
      homeFrontFourSource homeFrontFourCycleWord =
      homeFrontFourSource := by
  funext i
  rcases homeFrontFinFour_cases i with rfl | rfl | rfl | rfl <;> rfl

/-- Every edge, not merely every scheduler clock, performs one successful
crossing during a period. -/
theorem homeFrontFourCycle_crossings :
    ∀ edge : Fin 4,
      homeFrontSuccessfulCrossings homeFrontFourRing
        homeFrontFourSource homeFrontFourCycleWord edge = 1 := by
  intro edge
  rcases homeFrontFinFour_cases edge with rfl | rfl | rfl | rfl <;> rfl

/-- The source endpoint has no loaded home trap. -/
theorem homeFrontFourSource_not_ready :
    ¬ HomeFrontHitReady homeFrontFourRing homeFrontFourSource := by
  rintro ⟨edge, hedge⟩
  rcases homeFrontFinFour_cases edge with rfl | rfl | rfl | rfl <;>
    simp [DirectedRing.rightNeighbor, homeFrontFourSource, homeFrontACAC,
      homeFrontTwoAt, sealSweepFrontHitsHomePair] at hedge

/-- The four-site source is in the exact positive image for arbitrary carrier
parameters. -/
theorem homeFrontFourSource_positiveState (kappa tau : Nat) :
    SealSweepPositiveHomeFrontState
      (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
      homeFrontFourRing homeFrontFourSource := by
  let C := sealSweepPhysicalACAC 4 (by omega) kappa tau
  refine ⟨C, ?_, ?_⟩
  · exact allClosedPositive_mem_positiveDescendant homeFrontFourRing C
      ⟨sealSweepPhysicalACAC_allClosed 4 (by omega) kappa tau,
        sealSweepPhysicalACAC_positive 4 (by omega) kappa tau⟩
  · exact sealSweepPhysicalACAC_projection 4 (by omega) kappa tau

/-- Any number of complete periods returns to the same endpoint. -/
theorem homeFrontFourRepeatedCycle_run_eq (cycles : Nat) :
    runLocalSchedule homeFrontFourRing sealSweepHomeFrontPair
        homeFrontFourSource (homeFrontFourRepeatedCycle cycles) =
      homeFrontFourSource := by
  induction cycles with
  | zero => rfl
  | succ cycles ih =>
      rw [homeFrontFourRepeatedCycle,
        PPLLSchedulerBlocks.runLocalSchedule_append]
      rw [ih]
      exact homeFrontFourCycle_run_eq

/-- After `cycles` periods every directed edge has successful current exactly
`cycles`. -/
theorem homeFrontFourRepeatedCycle_crossings (cycles : Nat) :
    ∀ edge : Fin 4,
      homeFrontSuccessfulCrossings homeFrontFourRing homeFrontFourSource
          (homeFrontFourRepeatedCycle cycles) edge = cycles := by
  intro edge
  induction cycles with
  | zero => rfl
  | succ cycles ih =>
      rw [homeFrontFourRepeatedCycle,
        homeFrontSuccessfulCrossings_append]
      rw [homeFrontFourRepeatedCycle_run_eq, ih,
        homeFrontFourCycle_crossings]

/-- Every repeated balanced-current cycle is collision-free. -/
theorem homeFrontFourRepeatedCycle_noHit (cycles : Nat) :
    HomeFrontNoHitSchedule homeFrontFourRing homeFrontFourSource
      (homeFrontFourRepeatedCycle cycles) := by
  apply (positiveHomeFrontState_noHit_iff_homeCount_eq
    (psi := OverlayNoGoPsi) (kappa := 0) (tau := 0)
    homeFrontFourRing (by omega) homeFrontFourSource
    (homeFrontFourSource_positiveState 0 0)
    (homeFrontFourRepeatedCycle cycles)).2
  rw [homeFrontFourRepeatedCycle_run_eq]

/-- Even with all four successful currents equal to an arbitrarily prescribed
value, the collision-free endpoint is not current-ready. -/
theorem homeFrontFourRepeatedCycle_not_currentReady (cycles : Nat) :
    ¬ HomeFrontCurrentReady homeFrontFourRing homeFrontFourSource
      (homeFrontFourRepeatedCycle cycles) := by
  intro hready
  have hend := (homeFrontCurrentReady_iff_endpointReady
    homeFrontFourRing (by omega) homeFrontFourSource
    (homeFrontFourRepeatedCycle cycles)
    (homeFrontFourRepeatedCycle_noHit cycles)).1 hready
  rw [homeFrontFourRepeatedCycle_run_eq] at hend
  exact homeFrontFourSource_not_ready hend

/-- Exact narrow obstruction to deterministic current-threshold arguments.
This family does not refute an iid mass bound: it contributes only one highly
ordered word per period count. -/
theorem homeFrontFour_unbounded_balancedCurrent_obstruction (cycles : Nat) :
    SealSweepPositiveHomeFrontState
        (psi := OverlayNoGoPsi) (kappa := 0) (tau := 0)
        homeFrontFourRing homeFrontFourSource ∧
      (homeFrontFourRepeatedCycle cycles).length = 4 * cycles ∧
      runLocalSchedule homeFrontFourRing sealSweepHomeFrontPair
          homeFrontFourSource (homeFrontFourRepeatedCycle cycles) =
        homeFrontFourSource ∧
      HomeFrontNoHitSchedule homeFrontFourRing homeFrontFourSource
        (homeFrontFourRepeatedCycle cycles) ∧
      (∀ edge : Fin 4,
        homeFrontSuccessfulCrossings homeFrontFourRing homeFrontFourSource
          (homeFrontFourRepeatedCycle cycles) edge = cycles) ∧
      ¬ HomeFrontCurrentReady homeFrontFourRing homeFrontFourSource
        (homeFrontFourRepeatedCycle cycles) := by
  exact ⟨homeFrontFourSource_positiveState 0 0,
    homeFrontFourRepeatedCycle_length cycles,
    homeFrontFourRepeatedCycle_run_eq cycles,
    homeFrontFourRepeatedCycle_noHit cycles,
    homeFrontFourRepeatedCycle_crossings cycles,
    homeFrontFourRepeatedCycle_not_currentReady cycles⟩

end PPartialSealSweepHomeTrapWorkloadSol
end PPLLCompleteMultiLeaderCleanup

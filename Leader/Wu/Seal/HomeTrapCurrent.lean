import Leader.Wu.Seal.HomeFrontQuotient
import Leader.Wu.Epoch.VoterTwoDomain

/-!
# Conserved currents and the blocked-service obstruction for the home trap

R106 identifies positive seal-sweep coalescence with a home-trap exclusion
process.  This file isolates the next exact stochastic seam.  On every
collision-free word, successful front crossings satisfy the usual discrete
continuity equation

`final front + outgoing current = initial front + incoming current`.

The scheduler clock itself is not that current.  A scalable reachable family
contains an `A B` bond: its left home carries a front and its right home is
empty.  The exact seal rule blocks this bond.  Repeating its scheduler edge an
arbitrary number of times therefore produces arbitrarily large raw clock mass
but zero successful current and no home hit.  Thus a polynomial R106 proof
needs a queue/workload or tagged-gap estimate controlling unused service; a
concentration statement for raw edge-selection counts alone cannot close the
gap.

The results below are finite deterministic identities.  They introduce no
probability space and do not assert the still-missing cubic half-mass theorem.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepHomeTrapCurrentSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPartialDynamicSweepLockSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepMixedNormalizerSol
open PPartialSealSweepIidDriftObstructionSol
open PPartialSealSweepIidCoalescenceBarrierSol
open PPartialSealSweepHomeFrontQuotientSol
open PPLLEpochVoterTwoDomain
open PPartialSealSweepConcurrencyNoGoSol
open PPartialSealSweepConcurrentCounterfamilySol
open SealSweepConcurrentCycleSol
open SealSweepConcurrentCycleSol.SealMacroState
open PPLLSchedulerBlocks

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Successful-current bookkeeping -/

/-- Natural-number indicator of front occupancy at one quotient site. -/
def homeFrontOccupancy
    (X : Fin n → SealSweepHomeFrontSite) (i : Fin n) : Nat :=
  if (X i).2 then 1 else 0

/-- Natural-number indicator that the selected edge performs the exact
noncollision `10 → 01` front move. -/
def homeFrontMoveIndicator
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) (e : Fin n) : Nat :=
  if sealSweepFrontMovePair
      (X e) (X (ring.rightNeighbor e)) then 1 else 0

/-- A schedule is collision-free when no selected edge is a front hit at the
state in which that edge is selected. -/
def HomeFrontNoHitSchedule
    (ring : DirectedRing n) :
    (Fin n → SealSweepHomeFrontSite) → DetSchedule n → Prop
  | _X, [] => True
  | X, e :: rest =>
      sealSweepFrontHitsHomePair
          (X e) (X (ring.rightNeighbor e)) = false ∧
        HomeFrontNoHitSchedule ring
          (localStep ring sealSweepHomeFrontPair X e) rest

/-- Number of successful noncollision crossings of one fixed directed edge
along a concrete scheduler word.  Scheduler selections that stutter do not
contribute. -/
def homeFrontSuccessfulCrossings
    (ring : DirectedRing n) :
    (Fin n → SealSweepHomeFrontSite) →
      DetSchedule n → Fin n → Nat
  | _X, [], _edge => 0
  | X, e :: rest, edge =>
      (if e = edge then homeFrontMoveIndicator ring X e else 0) +
        homeFrontSuccessfulCrossings ring
          (localStep ring sealSweepHomeFrontPair X e) rest edge

/-- One collision-free interaction satisfies the pointwise continuity
equation.  The selected move removes one front at its left endpoint and adds
one at its right endpoint; a stutter changes neither side. -/
theorem homeFrontOccupancy_localStep_balance
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (e i : Fin n)
    (hnoHit : sealSweepFrontHitsHomePair
        (X e) (X (ring.rightNeighbor e)) = false) :
    homeFrontOccupancy
          (localStep ring sealSweepHomeFrontPair X e) i +
        (if e = i then homeFrontMoveIndicator ring X e else 0) =
      homeFrontOccupancy X i +
        (if ring.rightNeighbor e = i
          then homeFrontMoveIndicator ring X e else 0) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  by_cases hie : i = e
  · subst i
    have hji : j ≠ e := hje
    rcases hl : X e with ⟨lh, lf⟩
    rcases hr : X j with ⟨rh, rf⟩
    cases lh <;> cases lf <;> cases rh <;> cases rf <;>
      simp [homeFrontOccupancy, homeFrontMoveIndicator, localStep,
        sealSweepHomeFrontPair, sealSweepFrontMovePair,
        sealSweepFrontHitsHomePair, j, hje, hji, hl, hr] at hnoHit ⊢
  · by_cases hij : i = j
    · subst i
      have hei : e ≠ j := hje.symm
      rcases hl : X e with ⟨lh, lf⟩
      rcases hr : X j with ⟨rh, rf⟩
      cases lh <;> cases lf <;> cases rh <;> cases rf <;>
        simp [homeFrontOccupancy, homeFrontMoveIndicator, localStep,
          sealSweepHomeFrontPair, sealSweepFrontMovePair,
          sealSweepFrontHitsHomePair, j, hje, hei, hl, hr] at hnoHit ⊢
    · have hei : e ≠ i := by exact fun h => hie h.symm
      have hji : ring.rightNeighbor e ≠ i := by
        simpa [j] using fun h => hij h.symm
      have hij' : i ≠ ring.rightNeighbor e := by
        simpa [j] using hij
      simp [homeFrontOccupancy, localStep, hie, hij', hei, hji]

/-- Exact finite-word current conservation.  Incoming current at `i` is the
successful current across `leftNeighbor i`; no probabilistic or fairness
assumption is present. -/
theorem homeFrontSuccessfulCrossings_conservation
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (word : DetSchedule n)
    (hnoHit : HomeFrontNoHitSchedule ring X word) (i : Fin n) :
    homeFrontOccupancy
          (runLocalSchedule ring sealSweepHomeFrontPair X word) i +
        homeFrontSuccessfulCrossings ring X word i =
      homeFrontOccupancy X i +
        homeFrontSuccessfulCrossings ring X word
          (ring.leftNeighbor i) := by
  induction word generalizing X with
  | nil => rfl
  | cons e rest ih =>
      rcases hnoHit with ⟨hfirst, hrest⟩
      let Y := localStep ring sealSweepHomeFrontPair X e
      have htail := ih (X := Y) hrest
      have hone := homeFrontOccupancy_localStep_balance
        ring hn X e i hfirst
      have hincoming :
          (if e = ring.leftNeighbor i
            then homeFrontMoveIndicator ring X e else 0) =
          (if ring.rightNeighbor e = i
            then homeFrontMoveIndicator ring X e else 0) := by
        by_cases h : e = ring.leftNeighbor i
        · subst e
          rw [rightNeighbor_leftNeighbor]
          simp
        · have hr : ring.rightNeighbor e ≠ i := by
            intro hr
            apply h
            rw [← hr]
            exact (leftNeighbor_rightNeighbor ring e).symm
          simp [h, hr]
      simp only [runLocalSchedule, homeFrontSuccessfulCrossings]
      change
        homeFrontOccupancy
              (runLocalSchedule ring sealSweepHomeFrontPair Y rest) i +
            ((if e = i then homeFrontMoveIndicator ring X e else 0) +
              homeFrontSuccessfulCrossings ring Y rest i) =
          homeFrontOccupancy X i +
            ((if e = ring.leftNeighbor i
                then homeFrontMoveIndicator ring X e else 0) +
              homeFrontSuccessfulCrossings ring Y rest
                (ring.leftNeighbor i))
      rw [hincoming]
      calc
        homeFrontOccupancy
              (runLocalSchedule ring sealSweepHomeFrontPair Y rest) i +
            ((if e = i then homeFrontMoveIndicator ring X e else 0) +
              homeFrontSuccessfulCrossings ring Y rest i) =
            (homeFrontOccupancy
                (runLocalSchedule ring sealSweepHomeFrontPair Y rest) i +
              homeFrontSuccessfulCrossings ring Y rest i) +
                (if e = i then homeFrontMoveIndicator ring X e else 0) := by
                  omega
        _ = (homeFrontOccupancy Y i +
              homeFrontSuccessfulCrossings ring Y rest
                (ring.leftNeighbor i)) +
                (if e = i then homeFrontMoveIndicator ring X e else 0) := by
              rw [htail]
        _ = (homeFrontOccupancy Y i +
                (if e = i then homeFrontMoveIndicator ring X e else 0)) +
              homeFrontSuccessfulCrossings ring Y rest
                (ring.leftNeighbor i) := by omega
        _ = (homeFrontOccupancy X i +
                (if ring.rightNeighbor e = i
                  then homeFrontMoveIndicator ring X e else 0)) +
              homeFrontSuccessfulCrossings ring Y rest
                (ring.leftNeighbor i) := by rw [hone]
        _ = homeFrontOccupancy X i +
            ((if ring.rightNeighbor e = i
                then homeFrontMoveIndicator ring X e else 0) +
              homeFrontSuccessfulCrossings ring Y rest
                (ring.leftNeighbor i)) := by omega

/-- On a collision-free word, neighboring successful currents differ by at
most one.  This is the sharp local restriction supplied by conservation; it
does not relate either current to the raw number of times its edge was
selected. -/
theorem homeFrontSuccessfulCrossings_adjacent_diff_le_one
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite) (word : DetSchedule n)
    (hnoHit : HomeFrontNoHitSchedule ring X word) (i : Fin n) :
    homeFrontSuccessfulCrossings ring X word i ≤
        homeFrontSuccessfulCrossings ring X word
          (ring.leftNeighbor i) + 1 ∧
      homeFrontSuccessfulCrossings ring X word
          (ring.leftNeighbor i) ≤
        homeFrontSuccessfulCrossings ring X word i + 1 := by
  have hbalance := homeFrontSuccessfulCrossings_conservation
    ring hn X word hnoHit i
  have hinitial : homeFrontOccupancy X i ≤ 1 := by
    simp only [homeFrontOccupancy]
    split <;> omega
  have hfinal : homeFrontOccupancy
      (runLocalSchedule ring sealSweepHomeFrontPair X word) i ≤ 1 := by
    simp only [homeFrontOccupancy]
    split <;> omega
  omega

/-! ## Exact reduction to endpoint exposure of a loaded home trap -/

/-- A loaded home trap is present when some scheduler edge has a front on its
left and an occupied home on its right.  Selecting that edge is exactly a
leader drop. -/
def HomeFrontHitReady
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) : Prop :=
  ∃ e : Fin n,
    sealSweepFrontHitsHomePair
      (X e) (X (ring.rightNeighbor e)) = true

/-- Endpoint test used by the reduced stochastic target: either the source
home count has already fallen, or the endpoint contains a loaded home trap. -/
noncomputable def homeFrontDropOrReadyEndpointTest
    (ring : DirectedRing n)
    (source current : Fin n → SealSweepHomeFrontSite) : Bool := by
  classical
  exact decide
    (homeFrontHomeCount current < homeFrontHomeCount source ∨
      HomeFrontHitReady ring current)

theorem homeFrontDropOrReadyEndpointTest_spec
    (ring : DirectedRing n)
    (source current : Fin n → SealSweepHomeFrontSite) :
    homeFrontDropOrReadyEndpointTest ring source current = true ↔
      homeFrontHomeCount current < homeFrontHomeCount source ∨
        HomeFrontHitReady ring current := by
  classical
  simp [homeFrontDropOrReadyEndpointTest]

/-- Number of exact length-`t` words whose endpoint has already dropped a
home or currently exposes a loaded home trap.  Unlike `localHitCount`, this is
an endpoint count; the distinction is what permits a one-step extension. -/
noncomputable def homeFrontDropOrReadyEndpointCount
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) (t : Nat) : Nat :=
  (allSchedules n t).countP (fun word =>
    homeFrontDropOrReadyEndpointTest ring X
      (runLocalSchedule ring sealSweepHomeFrontPair X word))

/-- The exact reachable quotient domain is closed under one quotient step. -/
theorem positiveHomeFrontState_localStep
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (e : Fin n) :
    SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring
      (localStep ring sealSweepHomeFrontPair X e) := by
  obtain ⟨C, hC, rfl⟩ := hX
  refine ⟨localStep ring P_partialSealSweep C e, ?_, ?_⟩
  · exact positiveDescendant_localStepClosed ring C hC e
  · exact sealSweepHomeFrontConfig_localStep_exact ring C e

/-- On a reachable quotient state, strict one-step home loss is equivalent
to the exact loaded-home predicate. -/
theorem positiveHomeFrontState_homeCount_localStep_lt_iff
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (e : Fin n) :
    homeFrontHomeCount
        (localStep ring sealSweepHomeFrontPair X e) <
        homeFrontHomeCount X ↔
      sealSweepFrontHitsHomePair
        (X e) (X (ring.rightNeighbor e)) = true := by
  obtain ⟨C, _hC, rfl⟩ := hX
  rw [← sealSweepHomeFrontConfig_localStep_exact]
  rw [homeFrontHomeCount_projection, homeFrontHomeCount_projection]
  rw [sealSweepLeaderCount_localStep_lt_iff ring hn]
  rw [sealSweepKillEdge_eq_frontHitsHome]

/-- Every quotient endpoint of a positive-state scheduler word remains in the
exact positive-state image. -/
theorem positiveHomeFrontState_run
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (word : DetSchedule n) :
    SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring
      (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
  induction word generalizing X with
  | nil => simpa [runLocalSchedule] using hX
  | cons e rest ih =>
      simp only [runLocalSchedule]
      exact ih (X := localStep ring sealSweepHomeFrontPair X e)
        (positiveHomeFrontState_localStep ring X hX e)

/-- Home count cannot increase along a quotient scheduler word from the exact
positive image. -/
theorem positiveHomeFrontState_run_homeCount_le
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (word : DetSchedule n) :
    homeFrontHomeCount
        (runLocalSchedule ring sealSweepHomeFrontPair X word) ≤
      homeFrontHomeCount X := by
  obtain ⟨C, _hC, rfl⟩ := hX
  rw [← sealSweepHomeFrontConfig_runLocalSchedule_exact]
  rw [homeFrontHomeCount_projection, homeFrontHomeCount_projection]
  exact sealSweepLeaderCount_reachable_le ring
    (P_partialSealSweep_runLocalSchedule_reachable ring C word)

private theorem homeFront_hitsWithinLocal_of_final
    (ring : DirectedRing n)
    (source current : Fin n → SealSweepHomeFrontSite)
    (word : DetSchedule n)
    (hfinal : homeFrontHomeDropTest source
        (runLocalSchedule ring sealSweepHomeFrontPair current word) = true) :
    hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontHomeDropTest source) current word = true := by
  induction word generalizing current with
  | nil => exact hfinal
  | cons e rest ih =>
      simp only [runLocalSchedule] at hfinal
      simp only [hitsWithinLocal]
      rw [Bool.or_eq_true]
      exact Or.inr (ih
        (localStep ring sealSweepHomeFrontPair current e) hfinal)

/-- Every good endpoint has a one-edge extension that actually drops a home.
If the endpoint has already dropped, any edge suffices; otherwise select one
of its loaded traps. -/
theorem homeFrontDropOrReadyEndpoint_has_hit_extension
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (word : DetSchedule n)
    (hgood : homeFrontDropOrReadyEndpointTest ring X
        (runLocalSchedule ring sealSweepHomeFrontPair X word) = true) :
    ∃ e : Fin n,
      hitsWithinLocal ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest X) X (word ++ [e]) = true := by
  let Y := runLocalSchedule ring sealSweepHomeFrontPair X word
  have hspec := (homeFrontDropOrReadyEndpointTest_spec ring X Y).1 hgood
  by_cases hdrop : homeFrontHomeCount Y < homeFrontHomeCount X
  · let e : Fin n := ⟨0, ring.hn⟩
    refine ⟨e, ?_⟩
    have hfinal : homeFrontHomeDropTest X Y = true := by
      simp [homeFrontHomeDropTest, hdrop]
    have hprefix := homeFront_hitsWithinLocal_of_final
      ring X X word (by simpa [Y] using hfinal)
    rw [hitsWithinLocal_append, hprefix]
    rfl
  · have hready : HomeFrontHitReady ring Y := by
      exact hspec.resolve_left hdrop
    obtain ⟨e, he⟩ := hready
    refine ⟨e, ?_⟩
    have hY : SealSweepPositiveHomeFrontState
        (psi := psi) (kappa := kappa) (tau := tau) ring Y := by
      simpa [Y] using positiveHomeFrontState_run ring X hX word
    have hle := positiveHomeFrontState_run_homeCount_le ring X hX word
    change homeFrontHomeCount Y ≤ homeFrontHomeCount X at hle
    have heq : homeFrontHomeCount Y = homeFrontHomeCount X := by omega
    have hstep : homeFrontHomeCount
          (localStep ring sealSweepHomeFrontPair Y e) <
        homeFrontHomeCount Y :=
      (positiveHomeFrontState_homeCount_localStep_lt_iff
        ring hn Y hY e).2 he
    have htail : hitsWithinLocal ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest X) Y [e] = true := by
      have hstepX : homeFrontHomeCount
          (localStep ring sealSweepHomeFrontPair Y e) <
          homeFrontHomeCount X := by
        rw [← heq]
        exact hstep
      simp only [hitsWithinLocal, Bool.or_eq_true]
      apply Or.inr
      simp [homeFrontHomeDropTest, hstepX]
    rw [hitsWithinLocal_append, htail, Bool.or_true]

private theorem countP_le_sum_of_pointwise_one
    {alpha : Type} (xs : List alpha) (p : alpha → Bool) (f : alpha → Nat)
    (h : ∀ x, x ∈ xs → p x = true → 1 ≤ f x) :
    xs.countP p ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      cases hx : p x
      · simp only [hx, Bool.false_eq_true, if_false]
        have htail := ih (fun y hy => h y (by simp [hy]))
        omega
      · simp only [hx, if_true]
        have hxone := h x (by simp) hx
        have htail := ih (fun y hy => h y (by simp [hy]))
        omega

/-- Exact scheduler-tree reduction: each endpoint word counted as already
dropped or hit-ready contributes at least one distinct favorable child at the
next horizon. -/
theorem homeFrontDropOrReadyEndpointCount_le_nextHitCount
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (t : Nat) :
    homeFrontDropOrReadyEndpointCount ring X t ≤
      localHitCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest X) X (t + 1) := by
  unfold homeFrontDropOrReadyEndpointCount localHitCount
  rw [show t + 1 = Nat.succ t by omega]
  simp only [allSchedules, List.countP_flatMap]
  let chunk : DetSchedule n → Nat := fun word =>
    (List.ofFn (fun e : Fin n => word ++ [e])).countP
      (hitsWithinLocal ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest X) X)
  change
    (allSchedules n t).countP (fun word =>
      homeFrontDropOrReadyEndpointTest ring X
        (runLocalSchedule ring sealSweepHomeFrontPair X word)) ≤
      ((allSchedules n t).map chunk).sum
  apply countP_le_sum_of_pointwise_one
  intro word hword hgood
  obtain ⟨e, he⟩ :=
    homeFrontDropOrReadyEndpoint_has_hit_extension
      ring hn X hX word hgood
  unfold chunk
  apply List.countP_pos_iff.mpr
  refine ⟨word ++ [e], ?_, he⟩
  rw [List.mem_ofFn]
  exact ⟨e, rfl⟩

/-- The strictly weaker Markov target exposed by the current reduction: many
words need only end in a loaded trap (or have dropped already), not actually
select the kill edge inside the same block. -/
def SealSweepHomeFrontReadyEndpointExposure
    (ring : DirectedRing n) (horizon favorable : Nat) : Prop :=
  ∀ X : Fin n → SealSweepHomeFrontSite,
    SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X →
    2 ≤ homeFrontHomeCount X →
    favorable ≤ homeFrontDropOrReadyEndpointCount ring X horizon

/-- Any uniform ready-endpoint exposure immediately yields an actual
leader-drop exposure one interaction later with the same numerator.  Its iid
success probability loses only the polynomial factor `n`. -/
theorem homeFrontReadyEndpointExposure_to_dropExposure
    (ring : DirectedRing n) (hn : 1 < n)
    (horizon favorable : Nat)
    (hready : SealSweepHomeFrontReadyEndpointExposure
      (psi := psi) (kappa := kappa) (tau := tau)
      ring horizon favorable) :
    SealSweepHomeFrontWindowDropExposure
      (psi := psi) (kappa := kappa) (tau := tau)
      ring (horizon + 1) favorable := by
  intro X hX hhomes
  exact Nat.le_trans (hready X hX hhomes)
    (homeFrontDropOrReadyEndpointCount_le_nextHitCount
      ring hn X hX horizon)

/-- Concrete remaining sufficient target.  Half of all cubic-prefix words
ending dropped-or-ready would already give an inverse-`2n` actual drop block
at horizon `n^3+1`, enough for polynomial geometric amplification. -/
def SealSweepHomeFrontCubicReadyHalfExposure
    (ring : DirectedRing n) : Prop :=
  SealSweepHomeFrontReadyEndpointExposure
    (psi := psi) (kappa := kappa) (tau := tau) ring
    (homeFrontCubicHorizon n) (homeFrontCubicHalfFavorable n)

theorem homeFrontCubicReadyHalfExposure_to_dropExposure
    (ring : DirectedRing n) (hn : 1 < n)
    (hready : SealSweepHomeFrontCubicReadyHalfExposure
      (psi := psi) (kappa := kappa) (tau := tau) ring) :
    SealSweepHomeFrontWindowDropExposure
      (psi := psi) (kappa := kappa) (tau := tau) ring
      (homeFrontCubicHorizon n + 1)
      (homeFrontCubicHalfFavorable n) :=
  homeFrontReadyEndpointExposure_to_dropExposure
    ring hn _ _ hready

/-- Integer form of the polynomial iid consequence of the remaining
ready-endpoint target.  At horizon `n^3+1`, the total number of words is at
most `3n` times the number of leader-dropping words.  The factor three only
absorbs natural-number rounding in `floor(n^(n^3)/2)`. -/
theorem homeFrontCubicReadyHalfExposure_inverse_three_n
    (ring : DirectedRing n) (hn : 1 < n)
    (hready : SealSweepHomeFrontCubicReadyHalfExposure
      (psi := psi) (kappa := kappa) (tau := tau) ring)
    (X : Fin n → SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hhomes : 2 ≤ homeFrontHomeCount X) :
    n ^ (homeFrontCubicHorizon n + 1) ≤
      (3 * n) * localHitCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest X) X
        (homeFrontCubicHorizon n + 1) := by
  let H := homeFrontCubicHorizon n
  let N := n ^ H
  let F := homeFrontCubicHalfFavorable n
  have hHpos : 0 < H := by
    dsimp [H, homeFrontCubicHorizon]
    exact Nat.pow_pos ring.hn
  have hNtwo : 2 ≤ N := by
    exact Nat.le_trans (by omega : 2 ≤ n) (Nat.le_pow hHpos)
  have hhalf : N ≤ 3 * F := by
    change N ≤ 3 * (N / 2)
    omega
  have hdrop : F ≤ localHitCount ring sealSweepHomeFrontPair
      (homeFrontHomeDropTest X) X (H + 1) := by
    exact (homeFrontCubicReadyHalfExposure_to_dropExposure
      ring hn hready) X hX hhomes
  calc
    n ^ (homeFrontCubicHorizon n + 1) = N * n := by
      simp [H, N, Nat.pow_succ]
    _ ≤ (3 * F) * n := Nat.mul_le_mul_right n hhalf
    _ = (3 * n) * F := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (3 * n) * localHitCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest X) X
        (homeFrontCubicHorizon n + 1) := by
      simpa [H] using Nat.mul_le_mul_left (3 * n) hdrop

/-! ## A reachable blocked-service family -/

/-- Quotient word `A B D C ... C`: homes are at zero and one, while fronts
are at zero and two. -/
def homeFrontABDC (m : Nat) (hm : 4 ≤ m) :
    Fin m → SealSweepHomeFrontSite :=
  fun i =>
    (decide (i.val = 0 ∨ i.val = 1),
      decide (i.val = 0 ∨ i.val = 2))

/-- All-closed quotient source `A A C ... C`. -/
def homeFrontAAC (m : Nat) (hm : 4 ≤ m) :
    Fin m → SealSweepHomeFrontSite :=
  fun i =>
    (decide (i.val = 0 ∨ i.val = 1),
      decide (i.val = 0 ∨ i.val = 1))

/-- The all-closed physical source with leaders exactly at positions zero and
one. -/
def sealSweepPhysicalAAC
    (m : Nat) (hm : 4 ≤ m) (kappa tau : Nat) :
    SealSweepConfig m OverlayNoGoPsi kappa tau :=
  fun i => sealSweepHomeFrontSection kappa tau (homeFrontAAC m hm i)

theorem sealSweepPhysicalAAC_projection
    (m : Nat) (hm : 4 ≤ m) (kappa tau : Nat) :
    sealSweepHomeFrontConfig (sealSweepPhysicalAAC m hm kappa tau) =
      homeFrontAAC m hm := by
  funext i
  exact sealSweepHomeFrontSite_section kappa tau (homeFrontAAC m hm i)

theorem sealSweepPhysicalAAC_allClosed
    (m : Nat) (hm : 4 ≤ m) (kappa tau : Nat) :
    SealSweepAllClosed (sealSweepPhysicalAAC m hm kappa tau) := by
  intro i
  by_cases hi : i.val = 0 ∨ i.val = 1 <;>
    simp [sealSweepPhysicalAAC, homeFrontAAC,
      sealSweepHomeFrontSection, exactLS, exactFS, hi]

theorem sealSweepPhysicalAAC_positive
    (m : Nat) (hm : 4 ≤ m) (kappa tau : Nat) :
    0 < sealSweepLeaderCount
      (sealSweepPhysicalAAC m hm kappa tau) := by
  apply (sealSweep_hasLeader_iff_leaderCount_pos _).1
  refine ⟨(⟨0, by omega⟩ : Fin m), ?_⟩
  simp [sealSweepPhysicalAAC, homeFrontAAC,
    sealSweepHomeFrontSection, exactLS]

/-- Selecting position one launches its front into position two, producing
the `A B D C^(n-3)` quotient exactly. -/
theorem homeFrontAAC_step_one_eq_ABDC
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let one : Fin n := ⟨1, by omega⟩
    localStep ring sealSweepHomeFrontPair
        (homeFrontAAC n hn) one =
      homeFrontABDC n hn := by
  let one : Fin n := ⟨1, by omega⟩
  let two : Fin n := ⟨2, by omega⟩
  have hright : ring.rightNeighbor one = two := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor, one, two,
      Nat.mod_eq_of_lt (by omega : 2 < n)]
  dsimp only
  funext i
  by_cases hi1 : i = one
  · subst i
    simp [localStep, hright, homeFrontAAC, homeFrontABDC, one, two,
      sealSweepHomeFrontPair]
  · by_cases hi2 : i = two
    · subst i
      have hne : two ≠ one := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [localStep, hright, homeFrontAAC, homeFrontABDC, one, two, hne,
        sealSweepHomeFrontPair]
    · have hiv1 : i.val ≠ 1 := by
        intro h
        apply hi1
        apply Fin.ext
        simpa [one] using h
      have hiv2 : i.val ≠ 2 := by
        intro h
        apply hi2
        apply Fin.ext
        simpa [two] using h
      simp [localStep, hright, homeFrontAAC, homeFrontABDC, one, two,
        hi1, hi2, hiv1, hiv2]

/-- The blocked-service word is a genuine positive descendant, not an
arbitrary balanced quotient state. -/
theorem homeFrontABDC_positiveState
    (ring : DirectedRing n) (hn : 4 ≤ n) (kappa tau : Nat) :
    SealSweepPositiveHomeFrontState
      (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
      ring (homeFrontABDC n hn) := by
  let one : Fin n := ⟨1, by omega⟩
  let C := sealSweepPhysicalAAC n hn kappa tau
  let D := localStep ring P_partialSealSweep C one
  refine ⟨D, ?_, ?_⟩
  · refine ⟨C, ⟨sealSweepPhysicalAAC_allClosed n hn kappa tau,
        sealSweepPhysicalAAC_positive n hn kappa tau⟩, ?_⟩
    exact P_partialSealSweep_runLocalSchedule_reachable ring C [one]
  · change sealSweepHomeFrontConfig D = homeFrontABDC n hn
    dsimp [D]
    rw [sealSweepHomeFrontConfig_localStep_exact]
    rw [sealSweepPhysicalAAC_projection]
    exact homeFrontAAC_step_one_eq_ABDC ring hn

private theorem homeFrontLocalStep_eq_self_of_pair_eq
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) (e : Fin n)
    (hpair : sealSweepHomeFrontPair
        (X e) (X (ring.rightNeighbor e)) =
      (X e, X (ring.rightNeighbor e))) :
    localStep ring sealSweepHomeFrontPair X e = X := by
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

/-- The `A B` edge is an exact stutter: ordinary exclusion would move its
front, but the home-trap rule blocks occupied-home to empty-home service. -/
theorem homeFrontABDC_zeroEdge_stutters
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let zero : Fin n := ⟨0, by omega⟩
    localStep ring sealSweepHomeFrontPair
        (homeFrontABDC n hn) zero = homeFrontABDC n hn := by
  let zero : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  have hright : ring.rightNeighbor zero = one := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor, zero, one,
      Nat.mod_eq_of_lt (by omega : 1 < n)]
  dsimp only
  apply homeFrontLocalStep_eq_self_of_pair_eq
  rw [hright]
  simp [homeFrontABDC, zero, one, sealSweepHomeFrontPair]

/-- Repeating the blocked scheduler edge for an arbitrary horizon leaves the
reachable quotient state unchanged. -/
theorem homeFrontABDC_repeat_zero_run
    (ring : DirectedRing n) (hn : 4 ≤ n) (t : Nat) :
    let zero : Fin n := ⟨0, by omega⟩
    runLocalSchedule ring sealSweepHomeFrontPair
        (homeFrontABDC n hn) (List.replicate t zero) =
      homeFrontABDC n hn := by
  let zero : Fin n := ⟨0, by omega⟩
  dsimp only
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [List.replicate_succ, runLocalSchedule]
      rw [homeFrontABDC_zeroEdge_stutters ring hn]
      exact ih

/-- The same arbitrary blocked clock mass produces zero successful current
across that edge. -/
theorem homeFrontABDC_repeat_zero_crossings
    (ring : DirectedRing n) (hn : 4 ≤ n) (t : Nat) :
    let zero : Fin n := ⟨0, by omega⟩
    homeFrontSuccessfulCrossings ring (homeFrontABDC n hn)
        (List.replicate t zero) zero = 0 := by
  let zero : Fin n := ⟨0, by omega⟩
  dsimp only
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [List.replicate_succ, homeFrontSuccessfulCrossings]
      have hstutter := homeFrontABDC_zeroEdge_stutters ring hn
      have hmove : homeFrontMoveIndicator ring
          (homeFrontABDC n hn) zero = 0 := by
        let one : Fin n := ⟨1, by omega⟩
        have hright : ring.rightNeighbor zero = one := by
          apply Fin.ext
          simp [DirectedRing.rightNeighbor, zero, one,
            Nat.mod_eq_of_lt (by omega : 1 < n)]
        simp [homeFrontMoveIndicator, homeFrontABDC, zero, one,
          hright, sealSweepFrontMovePair]
      have hmove' : homeFrontMoveIndicator ring
          (homeFrontABDC n hn) (⟨0, by omega⟩ : Fin n) = 0 := by
        simpa using hmove
      have hstutter' : localStep ring sealSweepHomeFrontPair
          (homeFrontABDC n hn) (⟨0, by omega⟩ : Fin n) =
            homeFrontABDC n hn := by
        simpa using hstutter
      simp only [if_pos rfl]
      rw [hmove', hstutter']
      simpa using ih

/-- The repeated blocked edge is collision-free at every horizon. -/
theorem homeFrontABDC_repeat_zero_noHit
    (ring : DirectedRing n) (hn : 4 ≤ n) (t : Nat) :
    let zero : Fin n := ⟨0, by omega⟩
    HomeFrontNoHitSchedule ring (homeFrontABDC n hn)
      (List.replicate t zero) := by
  let zero : Fin n := ⟨0, by omega⟩
  dsimp only
  induction t with
  | zero => trivial
  | succ t ih =>
      rw [List.replicate_succ]
      constructor
      · let one : Fin n := ⟨1, by omega⟩
        have hright : ring.rightNeighbor zero = one := by
          apply Fin.ext
          simp [DirectedRing.rightNeighbor, zero, one,
            Nat.mod_eq_of_lt (by omega : 1 < n)]
        simp [homeFrontABDC, zero, one, hright,
          sealSweepFrontHitsHomePair]
      · rw [homeFrontABDC_zeroEdge_stutters ring hn]
        exact ih

/-- Exact scalable obstruction to a raw-clock drift argument.  For every
requested clock mass `t` there is a reachable balanced positive quotient word
on which all `t` selections hit the same blocked bond, while the state and
successful current remain unchanged and no collision occurs. -/
theorem homeFrontABDC_unbounded_rawClock_obstruction
    (ring : DirectedRing n) (hn : 4 ≤ n)
    (kappa tau t : Nat) :
    let zero : Fin n := ⟨0, by omega⟩
    SealSweepPositiveHomeFrontState
        (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
        ring (homeFrontABDC n hn) ∧
      (List.replicate t zero).count zero = t ∧
      runLocalSchedule ring sealSweepHomeFrontPair
          (homeFrontABDC n hn) (List.replicate t zero) =
        homeFrontABDC n hn ∧
      homeFrontSuccessfulCrossings ring (homeFrontABDC n hn)
          (List.replicate t zero) zero = 0 ∧
      HomeFrontNoHitSchedule ring (homeFrontABDC n hn)
        (List.replicate t zero) := by
  dsimp only
  refine ⟨homeFrontABDC_positiveState ring hn kappa tau, by simp,
    homeFrontABDC_repeat_zero_run ring hn t,
    homeFrontABDC_repeat_zero_crossings ring hn t,
    homeFrontABDC_repeat_zero_noHit ring hn t⟩

end PPartialSealSweepHomeTrapCurrentSol
end PPLLCompleteMultiLeaderCleanup

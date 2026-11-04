import Leader.Wu.Seal.ABStoppedDrift
import Leader.Wu.Seal.TasepRotationBridge

/-!
# The exact marked-AB gate: obstruction and a prefix-hit replacement

The endpoint-only gate `HomeFrontInverseSquareABGate` cannot hold on the full
positive quotient domain.  Homes are never created by the quotient rule, so a
positive all-closed `A C A C` source can never acquire the two adjacent homes
required by an `A B` endpoint.  The first section records this obstruction
without a reachability assumption and then instantiates it on a reachable
four-site positive state.

The replacement in the second section counts scheduler words that *visit*
either exact readiness (an adjacent marked front pair `11` at a home) or an
exact `A B` blocker.  It is an absorbing proof tree only; the physical run is
not stopped.  Once the proof tree first reaches the gate, all remaining clocks
are spent through the already verified Ready suffix involution or the verified
fixed-AB stopped-drift theorem.  This gives the same `1 / (4*n^2)` endpoint
factor as the old composition theorem.

The final section gives a deterministic bridge from the genuine clockwise
TASEP update to this prefix gate.  Its marked event is exactly adjacent `11`,
not the easier move opportunity `10`.  The only unproved input left in that
bridge is stated as a fixed-front-mass TASEP endpoint-count inequality; no
transition-mixing estimate is asserted here.

The source convention is `A=11`, `B=10`, `C=00`, `D=01`.  In raw bits the
five nontrivial quotient transitions are exactly
`11,11 -> 11,00`, `01,11 -> 00,01`, `11,00 -> 10,01`,
`01,00 -> 00,01`, and `01,10 -> 00,11`.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepABGateBreakthroughSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPLLClosedDomainSchedulerAmplificationSol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepConcurrencyNoGoSol
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepHomeTrapWorkloadSol
open PPartialSealSweepReadySuffixHalfMassSol
open PPartialSealSweepABReadyCompositionSol
open PPartialSealSweepABStoppedDriftSol
open PPartialSealSweepTasepMixingFirstBrickSol
open PPartialSealSweepTasepRotationBridgeSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## The endpoint-only AB gate is false on the positive domain -/

/-- No directed edge has homes at both endpoints. -/
def HomeFrontNoAdjacentHomes (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) : Prop :=
  forall edge : Fin n,
    ¬ ((X edge).1 = true /\
      (X (ring.rightNeighbor edge)).1 = true)

/-- Pointwise home noncreation preserves the absence of adjacent homes through
one quotient interaction. -/
theorem homeFrontNoAdjacentHomes_localStep
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hno : HomeFrontNoAdjacentHomes ring X) (scheduled : Fin n) :
    HomeFrontNoAdjacentHomes ring
      (localStep ring sealSweepHomeFrontPair X scheduled) := by
  intro edge hafter
  have hleft := homeFrontLocalStep_home_backward
    ring X scheduled edge hafter.1
  have hright := homeFrontLocalStep_home_backward
    ring X scheduled (ring.rightNeighbor edge) hafter.2
  exact hno edge <| And.intro hleft hright

/-- Consequently, quotient execution can never create adjacent homes. -/
theorem homeFrontNoAdjacentHomes_run
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hno : HomeFrontNoAdjacentHomes ring X) (word : DetSchedule n) :
    HomeFrontNoAdjacentHomes ring
      (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
  induction word generalizing X with
  | nil => exact hno
  | cons edge rest ih =>
      simp only [runLocalSchedule]
      exact ih
        (localStep ring sealSweepHomeFrontPair X edge)
        (homeFrontNoAdjacentHomes_localStep ring X hno edge)

/-- An exact `A B` anchor necessarily contains adjacent homes. -/
theorem homeFrontHasABAnchor_not_of_noAdjacentHomes
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hno : HomeFrontNoAdjacentHomes ring X) :
    ¬ HomeFrontHasABAnchor ring X := by
  rintro ⟨anchor, hleft, hright⟩
  apply hno anchor
  constructor
  · simpa using congrArg Prod.fst hleft
  · simpa using congrArg Prod.fst hright

/-- Hence the endpoint `A B` count is identically zero from every state with
no adjacent homes, at every horizon. -/
theorem homeFrontABAnchorEndpointCount_eq_zero_of_noAdjacentHomes
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hno : HomeFrontNoAdjacentHomes ring X) (t : Nat) :
    homeFrontABAnchorEndpointCount ring X t = 0 := by
  unfold homeFrontABAnchorEndpointCount
  apply List.countP_eq_zero.mpr
  intro word _hword hcounted
  have hAB : HomeFrontHasABAnchor ring
      (runLocalSchedule ring sealSweepHomeFrontPair X word) :=
    (homeFrontHasABAnchorTest_spec ring _).1 hcounted
  exact homeFrontHasABAnchor_not_of_noAdjacentHomes ring _
    (homeFrontNoAdjacentHomes_run ring X hno word) hAB

/-- The original inverse-square endpoint gate is therefore impossible on such
a state.  This is independent of the proposed gate horizon. -/
theorem homeFrontInverseSquareABGate_false_of_noAdjacentHomes
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hno : HomeFrontNoAdjacentHomes ring X) (gate : Nat) :
    ¬ HomeFrontInverseSquareABGate ring X gate := by
  intro hgate
  unfold HomeFrontInverseSquareABGate at hgate
  rw [homeFrontABAnchorEndpointCount_eq_zero_of_noAdjacentHomes
    ring X hno gate] at hgate
  have hpositive : 0 < n ^ gate := Nat.pow_pos ring.hn
  omega

/-- A concrete non-self ring used to exhibit the obstruction inside the exact
positive-state image. -/
theorem homeFrontABGateFourRing : DirectedRing 4 := ⟨by omega⟩

theorem homeFrontACAC_four_noAdjacentHomes :
    HomeFrontNoAdjacentHomes homeFrontABGateFourRing
      (homeFrontACAC 4 (by omega)) := by
  intro edge
  have hedge : edge.val = 0 ∨ edge.val = 1 ∨
      edge.val = 2 ∨ edge.val = 3 := by omega
  rcases hedge with hedge | hedge | hedge | hedge
  · have heq : edge = (0 : Fin 4) := Fin.ext hedge
    subst edge
    decide
  · have heq : edge = (1 : Fin 4) := Fin.ext hedge
    subst edge
    decide
  · have heq : edge = (2 : Fin 4) := Fin.ext hedge
    subst edge
    decide
  · have heq : edge = (3 : Fin 4) := Fin.ext hedge
    subst edge
    decide

/-- The four-site `A C A C` quotient is not an artificial Boolean word: it is
the projection of a positive all-closed physical source. -/
theorem homeFrontACAC_four_positiveState (kappa tau : Nat) :
    SealSweepPositiveHomeFrontState
      (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
      homeFrontABGateFourRing (homeFrontACAC 4 (by omega)) := by
  let C := sealSweepPhysicalACAC 4 (by omega) kappa tau
  refine ⟨C, ?_, ?_⟩
  · apply allClosedPositive_mem_positiveDescendant
    exact ⟨sealSweepPhysicalACAC_allClosed 4 (by omega) kappa tau,
      sealSweepPhysicalACAC_positive 4 (by omega) kappa tau⟩
  · exact sealSweepPhysicalACAC_projection 4 (by omega) kappa tau

/-- A reachable positive state refutes the universal endpoint-AB gate at every
horizon. -/
theorem positive_homeFrontACAC_four_not_inverseSquareABGate
    (kappa tau gate : Nat) :
    SealSweepPositiveHomeFrontState
      (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
      homeFrontABGateFourRing (homeFrontACAC 4 (by omega)) /\
      ¬ HomeFrontInverseSquareABGate homeFrontABGateFourRing
        (homeFrontACAC 4 (by omega)) gate := by
  exact ⟨homeFrontACAC_four_positiveState kappa tau,
    homeFrontInverseSquareABGate_false_of_noAdjacentHomes
      homeFrontABGateFourRing (homeFrontACAC 4 (by omega))
      homeFrontACAC_four_noAdjacentHomes gate⟩

/-! ## Exact prefix gate and its finite scheduler count -/

/-- The corrected stopping event.  The left disjunct is exact loaded readiness,
whose front event is adjacent `11`; the right disjunct is the exact `A B`
blocker required by the stopped-drift argument. -/
def HomeFrontReadyOrAB (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) : Prop :=
  HomeFrontHitReady ring X \/ HomeFrontHasABAnchor ring X

noncomputable def homeFrontReadyOrABTest (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) : Bool := by
  classical
  exact decide (HomeFrontReadyOrAB ring X)

theorem homeFrontReadyOrABTest_spec (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) :
    homeFrontReadyOrABTest ring X = true <->
      HomeFrontReadyOrAB ring X := by
  classical
  simp [homeFrontReadyOrABTest]

private def abGateFinSum {m : Nat} (f : Fin m -> Nat) : Nat :=
  (List.ofFn f).sum

private theorem abGateFinSum_succ {m : Nat}
    (f : Fin (m + 1) -> Nat) :
    abGateFinSum f = f 0 + abGateFinSum (fun i : Fin m => f i.succ) := by
  unfold abGateFinSum
  rw [List.ofFn_succ, List.sum_cons]

private theorem abGateFinSum_eq {m : Nat}
    (f g : Fin m -> Nat) (hfg : forall i, f i = g i) :
    abGateFinSum f = abGateFinSum g := by
  induction m with
  | zero => simp [abGateFinSum]
  | succ m ih =>
      rw [abGateFinSum_succ, abGateFinSum_succ]
      rw [hfg 0]
      exact congrArg (g 0 + .)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem abGateFinSum_le {m : Nat}
    (f g : Fin m -> Nat) (hfg : forall i, f i <= g i) :
    abGateFinSum f <= abGateFinSum g := by
  induction m with
  | zero => simp [abGateFinSum]
  | succ m ih =>
      rw [abGateFinSum_succ, abGateFinSum_succ]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem abGateFinSum_mul_left {m : Nat}
    (c : Nat) (f : Fin m -> Nat) :
    abGateFinSum (fun i => c * f i) = c * abGateFinSum f := by
  induction m with
  | zero => simp [abGateFinSum]
  | succ m ih =>
      rw [abGateFinSum_succ, abGateFinSum_succ, ih, Nat.mul_add]

/-- Number of exact length-`t` scheduler words whose prefix (including the
initial and final states) visits `Ready or AB`.  A node already in the event
contributes all of its remaining `n^t` continuations. -/
noncomputable def homeFrontReadyOrABHitTree (ring : DirectedRing n) :
    (Fin n -> SealSweepHomeFrontSite) -> Nat -> Nat
  | X, 0 =>
      @ite Nat (HomeFrontReadyOrAB ring X) (Classical.propDecidable _) 1 0
  | X, t + 1 =>
      @ite Nat (HomeFrontReadyOrAB ring X) (Classical.propDecidable _)
        (n ^ (t + 1))
        (abGateFinSum (fun edge =>
          homeFrontReadyOrABHitTree ring
            (localStep ring sealSweepHomeFrontPair X edge) t))

/-- The recursive proof tree is exactly the repository's finite prefix-hitting
count, including scheduler multiplicity. -/
theorem homeFrontReadyOrABHitTree_eq_localHitCount
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (t : Nat) :
    homeFrontReadyOrABHitTree ring X t =
      localHitCount ring sealSweepHomeFrontPair
        (homeFrontReadyOrABTest ring) X t := by
  induction t generalizing X with
  | zero =>
      by_cases hgate : HomeFrontReadyOrAB ring X
      · have htest := (homeFrontReadyOrABTest_spec ring X).2 hgate
        simp [homeFrontReadyOrABHitTree, localHitCount, allSchedules,
          hitsWithinLocal, hgate, htest]
      · have htest : homeFrontReadyOrABTest ring X = false := by
          cases h : homeFrontReadyOrABTest ring X
          · rfl
          · exact False.elim <| hgate <|
              (homeFrontReadyOrABTest_spec ring X).1 h
        simp [homeFrontReadyOrABHitTree, localHitCount, allSchedules,
          hitsWithinLocal, hgate, htest]
  | succ t ih =>
      by_cases hgate : HomeFrontReadyOrAB ring X
      · have htest := (homeFrontReadyOrABTest_spec ring X).2 hgate
        rw [homeFrontReadyOrABHitTree]
        rw [if_pos hgate]
        unfold localHitCount
        rw [List.countP_eq_length.mpr]
        · exact (allSchedules_length n (t + 1)).symm
        · intro word _hword
          cases word <;> simp [hitsWithinLocal, htest]
      · have htest : homeFrontReadyOrABTest ring X = false := by
          cases h : homeFrontReadyOrABTest ring X
          · rfl
          · exact False.elim <| hgate <|
              (homeFrontReadyOrABTest_spec ring X).1 h
        rw [homeFrontReadyOrABHitTree]
        rw [if_neg hgate]
        unfold localHitCount
        rw [show t + 1 = 1 + t by omega, allSchedules_add,
          List.countP_flatMap]
        have hone : allSchedules n 1 =
            List.ofFn (fun edge : Fin n => [edge]) := by
          simp [allSchedules]
        rw [hone, List.map_ofFn]
        apply abGateFinSum_eq
        intro edge
        symm
        change ((allSchedules n t).map
            (fun suffix => [edge] ++ suffix)).countP
              (hitsWithinLocal ring sealSweepHomeFrontPair
                (homeFrontReadyOrABTest ring) X) =
          homeFrontReadyOrABHitTree ring
            (localStep ring sealSweepHomeFrontPair X edge) t
        calc
          ((allSchedules n t).map
              (fun suffix => [edge] ++ suffix)).countP
                (hitsWithinLocal ring sealSweepHomeFrontPair
                  (homeFrontReadyOrABTest ring) X) =
              localHitCount ring sealSweepHomeFrontPair
                (homeFrontReadyOrABTest ring)
                (localStep ring sealSweepHomeFrontPair X edge) t := by
            rw [List.countP_map]
            unfold localHitCount
            apply congrArg
              (fun p => (allSchedules n t).countP p)
            funext suffix
            simp [Function.comp_apply, hitsWithinLocal, htest]
          _ = homeFrontReadyOrABHitTree ring
                (localStep ring sealSweepHomeFrontPair X edge) t :=
            (ih (localStep ring sealSweepHomeFrontPair X edge)).symm

/-- Corrected inverse-square gate: a `1/n^2` fraction of scheduler words has
visited exact readiness or the exact AB blocker by time `gate`. -/
def HomeFrontInverseSquareReadyOrABHitGate
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (gate : Nat) : Prop :=
  n ^ gate <= n ^ 2 * homeFrontReadyOrABHitTree ring X gate

/-! ## Completion after a prefix hit -/

/-- The stopped Ready-miss tree grows by at most the number of new scheduler
choices after an arbitrary base horizon. -/
theorem homeFrontABReadyMissTree_add_le_pow_mul
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (base extra : Nat) :
    homeFrontABReadyMissTree ring X (base + extra) <=
      n ^ extra * homeFrontABReadyMissTree ring X base := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ]
      calc
        homeFrontABReadyMissTree ring X (base + extra + 1)
            <= n * homeFrontABReadyMissTree ring X (base + extra) :=
          homeFrontABReadyMissTree_succ_le_mul ring X (base + extra)
        _ <= n * (n ^ extra *
              homeFrontABReadyMissTree ring X base) :=
          Nat.mul_le_mul_left n ih
        _ = n ^ (extra + 1) *
              homeFrontABReadyMissTree ring X base := by
          rw [Nat.pow_succ]
          ac_rfl

/-- The verified half-mass miss bound at `2*n^3` propagates to every longer
horizon. -/
theorem positiveHomeFrontABReadyMissTree_half_of_twoCubic_le
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X)
    (t : Nat) (ht : 2 * n ^ 3 <= t) :
    2 * homeFrontABReadyMissTree ring X t <= n ^ t := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hbase := positiveHomeFrontABReadyMissTree_half_at_twoCubic
    ring hn X anchor hX hanchor hnotReady
  have hgrowth := homeFrontABReadyMissTree_add_le_pow_mul
    ring X (2 * n ^ 3) extra
  calc
    2 * homeFrontABReadyMissTree ring X (2 * n ^ 3 + extra)
        <= 2 * (n ^ extra *
          homeFrontABReadyMissTree ring X (2 * n ^ 3)) :=
      Nat.mul_le_mul_left 2 hgrowth
    _ = n ^ extra *
          (2 * homeFrontABReadyMissTree ring X (2 * n ^ 3)) := by
      ac_rfl
    _ <= n ^ extra * n ^ (2 * n ^ 3) :=
      Nat.mul_le_mul_left (n ^ extra) hbase
    _ = n ^ (2 * n ^ 3 + extra) := by
      rw [Nat.pow_add]
      ac_rfl

/-- The fixed-AB quarter-mass endpoint theorem at every horizon at least
`2*n^3`.  This is the variable-remainder form needed when the prefix gate is
hit before the end of its search block. -/
theorem positiveHomeFrontABAnchor_dropOrReady_quarter_of_twoCubic_le
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X)
    (t : Nat) (ht : 2 * n ^ 3 <= t) :
    n ^ t <= 4 * homeFrontDropOrReadyEndpointCount ring X t := by
  have hpartition := positiveHomeFront_readyMiss_add_two_harvest
    ring hn X X hX rfl t
  have hsubset := homeFrontTransientReadyHarvest_le_endpointCountFrom
    ring X X t
  have hmiss := positiveHomeFrontABReadyMissTree_half_of_twoCubic_le
    ring hn X anchor hX hanchor hnotReady t ht
  rw [homeFrontDropOrReadyEndpointCountFrom_self] at hsubset
  omega

/-- From a reached `Ready or AB` gate, every sufficiently long remaining
physical suffix has at least one quarter good endpoint mass relative to the
original source.  If a home was already lost, every suffix is good. -/
theorem positiveHomeFrontReadyOrAB_completion_quarter
    (ring : DirectedRing n) (hn : 1 < n)
    (source current : Fin n -> SealSweepHomeFrontSite)
    (hcurrent : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring current)
    (hcountLe : homeFrontHomeCount current <= homeFrontHomeCount source)
    (hgate : HomeFrontReadyOrAB ring current)
    (t : Nat) (ht : 2 * n ^ 3 <= t) :
    n ^ t <=
      4 * homeFrontDropOrReadyEndpointCountFrom ring source current t := by
  by_cases hdrop :
      homeFrontHomeCount current < homeFrontHomeCount source
  · have hall : homeFrontDropOrReadyEndpointCountFrom ring source current t =
        (allSchedules n t).length := by
      unfold homeFrontDropOrReadyEndpointCountFrom
      apply List.countP_eq_length.mpr
      intro word _hword
      have hfinalLe := homeFrontHomeCount_run_le ring current word
      apply (homeFrontDropOrReadyEndpointTest_spec ring source
        (runLocalSchedule ring sealSweepHomeFrontPair current word)).2
      exact Or.inl (Nat.lt_of_le_of_lt hfinalLe hdrop)
    rw [hall, allSchedules_length]
    omega
  · have hcount : homeFrontHomeCount current =
        homeFrontHomeCount source := by omega
    by_cases hready : HomeFrontHitReady ring current
    · have hsuffix := homeFrontHitReady_suffix_half_mass
        ring current hready t
      rw [← homeFrontDropOrReadyEndpointCountFrom_eq_of_homeCount_eq
        ring source current t hcount] at hsuffix
      omega
    · have hAB : HomeFrontHasABAnchor ring current :=
        hgate.resolve_left hready
      obtain ⟨anchor, hanchor⟩ := hAB
      have hab :=
        positiveHomeFrontABAnchor_dropOrReady_quarter_of_twoCubic_le
          ring hn current anchor hcurrent hanchor hready t ht
      rw [← homeFrontDropOrReadyEndpointCountFrom_eq_of_homeCount_eq
        ring source current t hcount] at hab
      exact hab

/-- Good leaves harvested after the first `Ready or AB` node.  At a hit node
the physical execution consumes *all* remaining search clocks plus the reserve
block, so neither Ready nor AB persistence is assumed. -/
noncomputable def homeFrontReadyOrABCompletionHarvest
    (ring : DirectedRing n)
    (source : Fin n -> SealSweepHomeFrontSite) :
    (Fin n -> SealSweepHomeFrontSite) -> Nat -> Nat -> Nat
  | current, 0, reserve =>
      @ite Nat (HomeFrontReadyOrAB ring current) (Classical.propDecidable _)
        (homeFrontDropOrReadyEndpointCountFrom
          ring source current reserve) 0
  | current, search + 1, reserve =>
      @ite Nat (HomeFrontReadyOrAB ring current) (Classical.propDecidable _)
        (homeFrontDropOrReadyEndpointCountFrom
          ring source current (search + 1 + reserve))
        (abGateFinSum (fun edge =>
          homeFrontReadyOrABCompletionHarvest ring source
            (localStep ring sealSweepHomeFrontPair current edge)
            search reserve))

/-- The first-hit harvest is a literal subset of all good physical endpoints
at the same total horizon. -/
theorem homeFrontReadyOrABCompletionHarvest_le_endpointCountFrom
    (ring : DirectedRing n)
    (source current : Fin n -> SealSweepHomeFrontSite)
    (search reserve : Nat) :
    homeFrontReadyOrABCompletionHarvest ring source current search reserve <=
      homeFrontDropOrReadyEndpointCountFrom ring source current
        (search + reserve) := by
  induction search generalizing current with
  | zero =>
      by_cases hgate : HomeFrontReadyOrAB ring current <;>
        simp [homeFrontReadyOrABCompletionHarvest, hgate]
  | succ search ih =>
      by_cases hgate : HomeFrontReadyOrAB ring current
      · simp [homeFrontReadyOrABCompletionHarvest, hgate]
      · rw [homeFrontReadyOrABCompletionHarvest]
        rw [if_neg hgate]
        rw [show search + 1 + reserve = search + reserve + 1 by omega,
          homeFrontDropOrReadyEndpointCountFrom_succ]
        exact abGateFinSum_le _ _ (fun edge => ih _)

/-- Every prefix-hit word carries a full reserve factor into the physical
endpoint harvest. -/
theorem positiveHomeFrontReadyOrABHitTree_scaled_le_completionHarvest
    (ring : DirectedRing n) (hn : 1 < n)
    (source current : Fin n -> SealSweepHomeFrontSite)
    (hcurrent : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring current)
    (hcountLe : homeFrontHomeCount current <= homeFrontHomeCount source)
    (search reserve : Nat) (hreserve : 2 * n ^ 3 <= reserve) :
    n ^ reserve * homeFrontReadyOrABHitTree ring current search <=
      4 * homeFrontReadyOrABCompletionHarvest
        ring source current search reserve := by
  induction search generalizing current with
  | zero =>
      by_cases hgate : HomeFrontReadyOrAB ring current
      · have hcompletion := positiveHomeFrontReadyOrAB_completion_quarter
          ring hn source current hcurrent hcountLe hgate reserve hreserve
        simpa [homeFrontReadyOrABHitTree,
          homeFrontReadyOrABCompletionHarvest, hgate] using hcompletion
      · simp [homeFrontReadyOrABHitTree,
          homeFrontReadyOrABCompletionHarvest, hgate]
  | succ search ih =>
      by_cases hgate : HomeFrontReadyOrAB ring current
      · have hcompletion := positiveHomeFrontReadyOrAB_completion_quarter
          ring hn source current hcurrent hcountLe hgate
            (search + 1 + reserve) (by omega)
        simpa [homeFrontReadyOrABHitTree,
          homeFrontReadyOrABCompletionHarvest, hgate,
          Nat.pow_add, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using hcompletion
      · have hchildren : forall edge : Fin n,
            n ^ reserve * homeFrontReadyOrABHitTree ring
                (localStep ring sealSweepHomeFrontPair current edge) search <=
              4 * homeFrontReadyOrABCompletionHarvest ring source
                (localStep ring sealSweepHomeFrontPair current edge)
                search reserve := by
          intro edge
          apply ih
          · exact positiveHomeFrontState_localStep ring current hcurrent edge
          · exact Nat.le_trans
              (homeFrontHomeCount_localStep_le ring current edge) hcountLe
        have hsum := abGateFinSum_le
          (fun edge => n ^ reserve * homeFrontReadyOrABHitTree ring
            (localStep ring sealSweepHomeFrontPair current edge) search)
          (fun edge => 4 * homeFrontReadyOrABCompletionHarvest ring source
            (localStep ring sealSweepHomeFrontPair current edge)
            search reserve)
          hchildren
        rw [abGateFinSum_mul_left, abGateFinSum_mul_left] at hsum
        simpa [homeFrontReadyOrABHitTree,
          homeFrontReadyOrABCompletionHarvest, hgate] using hsum

/-- The corrected prefix-hit gate composes all the way to the old
`1/(4*n^2)` dropped-or-ready endpoint conclusion, with stopped drift fully
discharged. -/
theorem positiveHomeFront_inverseSquareReadyOrABHitGate_to_dropOrReady
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (gate : Nat)
    (hgate : HomeFrontInverseSquareReadyOrABHitGate ring X gate) :
    n ^ (gate + 2 * n ^ 3) <=
      4 * n ^ 2 * homeFrontDropOrReadyEndpointCount ring X
        (gate + 2 * n ^ 3) := by
  let reserve := 2 * n ^ 3
  have hscaled :=
    positiveHomeFrontReadyOrABHitTree_scaled_le_completionHarvest
      ring hn X X hX (Nat.le_refl _) gate reserve (by simp [reserve])
  have hsubset :=
    homeFrontReadyOrABCompletionHarvest_le_endpointCountFrom
      ring X X gate reserve
  rw [homeFrontDropOrReadyEndpointCountFrom_self] at hsubset
  have hgateScaled := Nat.mul_le_mul_left (n ^ reserve) hgate
  calc
    n ^ (gate + 2 * n ^ 3) = n ^ reserve * n ^ gate := by
      simp [reserve, Nat.pow_add, Nat.mul_comm]
    _ <= n ^ reserve *
          (n ^ 2 * homeFrontReadyOrABHitTree ring X gate) := hgateScaled
    _ = n ^ 2 *
          (n ^ reserve * homeFrontReadyOrABHitTree ring X gate) := by
      ac_rfl
    _ <= n ^ 2 *
          (4 * homeFrontReadyOrABCompletionHarvest
            ring X X gate reserve) := Nat.mul_le_mul_left _ hscaled
    _ <= n ^ 2 *
          (4 * homeFrontDropOrReadyEndpointCount ring X
            (gate + reserve)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 4 hsubset)
    _ = 4 * n ^ 2 * homeFrontDropOrReadyEndpointCount ring X
          (gate + 2 * n ^ 3) := by
      simp [reserve, Nat.mul_assoc, Nat.mul_comm]

/-! ## Deterministic exact-`11` TASEP bridge -/

/-- The clockwise TASEP local update: exactly `10 -> 01`, otherwise stutter. -/
def clockwiseTasepPair (l r : Bool) : Bool × Bool :=
  if l && !r then (false, true) else (l, r)

def homeFrontHomeProjection
    (X : Fin n -> SealSweepHomeFrontSite) : Fin n -> Bool :=
  fun i => (X i).1

def homeFrontFrontProjection
    (X : Fin n -> SealSweepHomeFrontSite) : Fin n -> Bool :=
  fun i => (X i).2

private theorem sealSweepHomeFrontPair_front_eq_tasep_of_no_hit_no_AB
    (l r : SealSweepHomeFrontSite)
    (hnoHit : sealSweepFrontHitsHomePair l r ≠ true)
    (hnoAB : ¬ (l = (true, true) /\ r = (true, false))) :
    ((sealSweepHomeFrontPair l r).1.2,
      (sealSweepHomeFrontPair l r).2.2) =
        clockwiseTasepPair l.2 r.2 := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [sealSweepFrontHitsHomePair, sealSweepHomeFrontPair,
      clockwiseTasepPair] at hnoHit hnoAB ⊢

private theorem sealSweepHomeFrontPair_home_eq_of_no_hit
    (l r : SealSweepHomeFrontSite)
    (hnoHit : sealSweepFrontHitsHomePair l r ≠ true) :
    ((sealSweepHomeFrontPair l r).1.1,
      (sealSweepHomeFrontPair l r).2.1) = (l.1, r.1) := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [sealSweepFrontHitsHomePair, sealSweepHomeFrontPair] at hnoHit ⊢

/-- Before the corrected gate is hit, one quotient step projects exactly to
one clockwise TASEP step on fronts. -/
theorem homeFrontFrontProjection_localStep_eq_tasep_of_not_gate
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n)
    (hnotGate : ¬ HomeFrontReadyOrAB ring X) :
    homeFrontFrontProjection
        (localStep ring sealSweepHomeFrontPair X edge) =
      localStep ring clockwiseTasepPair
        (homeFrontFrontProjection X) edge := by
  have hnoHit : sealSweepFrontHitsHomePair
      (X edge) (X (ring.rightNeighbor edge)) ≠ true := by
    intro hhit
    exact hnotGate <| Or.inl ⟨edge, hhit⟩
  have hnoAB : ¬
      (X edge = (true, true) /\
        X (ring.rightNeighbor edge) = (true, false)) := by
    intro hAB
    exact hnotGate <| Or.inr ⟨edge, hAB⟩
  have hpair := sealSweepHomeFrontPair_front_eq_tasep_of_no_hit_no_AB
    (X edge) (X (ring.rightNeighbor edge)) hnoHit hnoAB
  funext i
  let j := ring.rightNeighbor edge
  by_cases hie : i = edge
  · subst i
    simpa [homeFrontFrontProjection, localStep, j] using congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      simpa [homeFrontFrontProjection, localStep, j, hie] using
        congrArg Prod.snd hpair
    · simp [homeFrontFrontProjection, localStep, j, hie, hij]

/-- Before the corrected gate is hit, homes are fixed pointwise. -/
theorem homeFrontHomeProjection_localStep_eq_of_not_gate
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n)
    (hnotGate : ¬ HomeFrontReadyOrAB ring X) :
    homeFrontHomeProjection
        (localStep ring sealSweepHomeFrontPair X edge) =
      homeFrontHomeProjection X := by
  have hnoHit : sealSweepFrontHitsHomePair
      (X edge) (X (ring.rightNeighbor edge)) ≠ true := by
    intro hhit
    exact hnotGate <| Or.inl ⟨edge, hhit⟩
  have hpair := sealSweepHomeFrontPair_home_eq_of_no_hit
    (X edge) (X (ring.rightNeighbor edge)) hnoHit
  funext i
  let j := ring.rightNeighbor edge
  by_cases hie : i = edge
  · subst i
    simpa [homeFrontHomeProjection, localStep, j] using congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      simpa [homeFrontHomeProjection, localStep, j, hie] using
        congrArg Prod.snd hpair
    · simp [homeFrontHomeProjection, localStep, j, hie, hij]

/-- On every scheduler word that misses `Ready or AB`, quotient fronts are
exactly the TASEP run on the same word. -/
theorem homeFrontFrontProjection_run_eq_tasep_of_gate_miss
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (word : DetSchedule n)
    (hmiss : hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontReadyOrABTest ring) X word = false) :
    homeFrontFrontProjection
        (runLocalSchedule ring sealSweepHomeFrontPair X word) =
      runLocalSchedule ring clockwiseTasepPair
        (homeFrontFrontProjection X) word := by
  induction word generalizing X with
  | nil => rfl
  | cons edge rest ih =>
      cases htest : homeFrontReadyOrABTest ring X with
      | true => simp [hitsWithinLocal, htest] at hmiss
      | false =>
          have hnotGate : ¬ HomeFrontReadyOrAB ring X := by
            intro hgate
            have := (homeFrontReadyOrABTest_spec ring X).2 hgate
            rw [htest] at this
            contradiction
          have htail : hitsWithinLocal ring sealSweepHomeFrontPair
              (homeFrontReadyOrABTest ring)
              (localStep ring sealSweepHomeFrontPair X edge) rest = false := by
            simpa [hitsWithinLocal, htest] using hmiss
          calc
            homeFrontFrontProjection
                (runLocalSchedule ring sealSweepHomeFrontPair X
                  (edge :: rest)) =
              homeFrontFrontProjection
                (runLocalSchedule ring sealSweepHomeFrontPair
                  (localStep ring sealSweepHomeFrontPair X edge) rest) := rfl
            _ = runLocalSchedule ring clockwiseTasepPair
                  (homeFrontFrontProjection
                    (localStep ring sealSweepHomeFrontPair X edge)) rest :=
              ih _ htail
            _ = runLocalSchedule ring clockwiseTasepPair
                  (localStep ring clockwiseTasepPair
                    (homeFrontFrontProjection X) edge) rest := by
              rw [homeFrontFrontProjection_localStep_eq_tasep_of_not_gate
                ring X edge hnotGate]
            _ = runLocalSchedule ring clockwiseTasepPair
                  (homeFrontFrontProjection X) (edge :: rest) := rfl

/-- On the same gate-miss word, every home remains at its original site. -/
theorem homeFrontHomeProjection_run_eq_of_gate_miss
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (word : DetSchedule n)
    (hmiss : hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontReadyOrABTest ring) X word = false) :
    homeFrontHomeProjection
        (runLocalSchedule ring sealSweepHomeFrontPair X word) =
      homeFrontHomeProjection X := by
  induction word generalizing X with
  | nil => rfl
  | cons edge rest ih =>
      cases htest : homeFrontReadyOrABTest ring X with
      | true => simp [hitsWithinLocal, htest] at hmiss
      | false =>
          have hnotGate : ¬ HomeFrontReadyOrAB ring X := by
            intro hgate
            have := (homeFrontReadyOrABTest_spec ring X).2 hgate
            rw [htest] at this
            contradiction
          have htail : hitsWithinLocal ring sealSweepHomeFrontPair
              (homeFrontReadyOrABTest ring)
              (localStep ring sealSweepHomeFrontPair X edge) rest = false := by
            simpa [hitsWithinLocal, htest] using hmiss
          calc
            homeFrontHomeProjection
                (runLocalSchedule ring sealSweepHomeFrontPair X
                  (edge :: rest)) =
              homeFrontHomeProjection
                (runLocalSchedule ring sealSweepHomeFrontPair
                  (localStep ring sealSweepHomeFrontPair X edge) rest) := rfl
            _ = homeFrontHomeProjection
                  (localStep ring sealSweepHomeFrontPair X edge) := ih _ htail
            _ = homeFrontHomeProjection X :=
              homeFrontHomeProjection_localStep_eq_of_not_gate
                ring X edge hnotGate

/-- Boolean test for the exact adjacent-front event `11` on a fixed directed
edge of a TASEP configuration. -/
noncomputable def tasepMarked11EndpointTest
    (ring : DirectedRing n) (edge : Fin n)
    (F : Fin n -> Bool) : Bool := by
  classical
  exact decide (FrontConfigMarkedEdge ring F edge)

theorem tasepMarked11EndpointTest_spec
    (ring : DirectedRing n) (edge : Fin n)
    (F : Fin n -> Bool) :
    tasepMarked11EndpointTest ring edge F = true <->
      FrontConfigMarkedEdge ring F edge := by
  classical
  simp [tasepMarked11EndpointTest]

noncomputable def tasepMarked11EndpointCount
    (ring : DirectedRing n) (F : Fin n -> Bool)
    (edge : Fin n) (t : Nat) : Nat :=
  (allSchedules n t).countP (fun word =>
    tasepMarked11EndpointTest ring edge
      (runLocalSchedule ring clockwiseTasepPair F word))

/-- If the responder endpoint initially carries a home, every TASEP word whose
endpoint has exact marked `11` forces the quotient word to have visited Ready
or AB.  The proof is by contradiction through the exact pre-gate coupling. -/
theorem tasepMarked11Endpoint_implies_homeFrontReadyOrABHit
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n)
    (hhome : (X (ring.rightNeighbor edge)).1 = true)
    (word : DetSchedule n)
    (hmarked : tasepMarked11EndpointTest ring edge
      (runLocalSchedule ring clockwiseTasepPair
        (homeFrontFrontProjection X) word) = true) :
    hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontReadyOrABTest ring) X word = true := by
  cases hhit : hitsWithinLocal ring sealSweepHomeFrontPair
      (homeFrontReadyOrABTest ring) X word with
  | true => rfl
  | false =>
      let Y := runLocalSchedule ring sealSweepHomeFrontPair X word
      have hfront := homeFrontFrontProjection_run_eq_tasep_of_gate_miss
        ring X word hhit
      have hhomes := homeFrontHomeProjection_run_eq_of_gate_miss
        ring X word hhit
      have hmark : FrontConfigMarkedEdge ring
          (runLocalSchedule ring clockwiseTasepPair
            (homeFrontFrontProjection X) word) edge :=
        (tasepMarked11EndpointTest_spec ring edge _).1 hmarked
      have hleftFront : (Y edge).2 = true := by
        change homeFrontFrontProjection Y edge = true
        rw [hfront]
        exact hmark.1
      have hrightFront : (Y (ring.rightNeighbor edge)).2 = true := by
        change homeFrontFrontProjection Y (ring.rightNeighbor edge) = true
        rw [hfront]
        exact hmark.2
      have hrightHome : (Y (ring.rightNeighbor edge)).1 = true := by
        change homeFrontHomeProjection Y (ring.rightNeighbor edge) = true
        rw [hhomes]
        exact hhome
      have hready : HomeFrontHitReady ring Y := by
        refine ⟨edge, ?_⟩
        simp [sealSweepFrontHitsHomePair, hleftFront,
          hrightHome, hrightFront]
      have hendpoint : homeFrontReadyOrABTest ring Y = true :=
        (homeFrontReadyOrABTest_spec ring Y).2 (Or.inl hready)
      have hmustHit := hitsWithinLocal_of_endpoint
        ring sealSweepHomeFrontPair (homeFrontReadyOrABTest ring)
        X word hendpoint
      rw [hhit] at hmustHit
      contradiction

private theorem abGateCountP_le_countP_of_true_imp
    {alpha : Type} (p q : alpha -> Bool) (xs : List alpha)
    (himp : forall x, x ∈ xs -> p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : forall y, y ∈ xs -> p y = true -> q y = true := by
        intro y hy
        exact himp y (by simp [hy])
      have hi := ih htail
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases q x <;> simp_all <;> omega
      | true =>
          have hq : q x = true := himp x (by simp) hp
          simpa [hp, hq] using hi

/-- Scheduler multiplicities are preserved by the deterministic bridge. -/
theorem tasepMarked11EndpointCount_le_homeFrontReadyOrABHitTree
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n)
    (hhome : (X (ring.rightNeighbor edge)).1 = true) (t : Nat) :
    tasepMarked11EndpointCount ring (homeFrontFrontProjection X) edge t <=
      homeFrontReadyOrABHitTree ring X t := by
  rw [homeFrontReadyOrABHitTree_eq_localHitCount]
  unfold tasepMarked11EndpointCount localHitCount
  apply abGateCountP_le_countP_of_true_imp
  intro word _hword hmarked
  exact tasepMarked11Endpoint_implies_homeFrontReadyOrABHit
    ring X edge hhome word hmarked

/-- The exact fixed-state TASEP lower bound needed by the bridge.  This is a
premise, not a theorem claiming that transition mixing has been proved. -/
def TasepMarked11InverseSquareEndpointGate
    (ring : DirectedRing n) (F : Fin n -> Bool)
    (edge : Fin n) (t : Nat) : Prop :=
  n ^ t <= n ^ 2 * tasepMarked11EndpointCount ring F edge t

/-- A marked-`11` TASEP endpoint lower bound at a site carrying a fixed home
produces the corrected quotient prefix gate. -/
theorem tasepMarked11InverseSquareEndpointGate_to_readyOrABHitGate
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n)
    (hhome : (X (ring.rightNeighbor edge)).1 = true) (t : Nat)
    (htasep : TasepMarked11InverseSquareEndpointGate ring
      (homeFrontFrontProjection X) edge t) :
    HomeFrontInverseSquareReadyOrABHitGate ring X t := by
  unfold TasepMarked11InverseSquareEndpointGate at htasep
  unfold HomeFrontInverseSquareReadyOrABHitGate
  exact Nat.le_trans htasep <| Nat.mul_le_mul_left (n ^ 2) <|
    tasepMarked11EndpointCount_le_homeFrontReadyOrABHitTree
      ring X edge hhome t

/-- Precisely scoped remaining transition estimate on the conserved
fixed-front-mass slice.  The static slice normalization theorem
`frontSliceWordCount_le_square_mul_markedPairWordCount` supplies the stationary
`n^2` comparison, and the rotation bridge transports its marked pair to
`edge`; neither theorem proves this dynamical endpoint bound. -/
def FixedFrontMassTasepMarked11EndpointBoundAt
    (ring : DirectedRing n) (k horizon : Nat) : Prop :=
  3 <= n /\ 2 <= k /\ k < n /\
    forall (F : Fin n -> Bool) (edge : Fin n),
      frontConfigMass F = k ->
        TasepMarked11InverseSquareEndpointGate ring F edge horizon

/-- Consumer for the exact fixed-slice obligation.  This theorem claims only
the deterministic implication from that explicit premise, not arbitrary-state
mixing. -/
theorem fixedFrontMassTasepMarked11EndpointBoundAt_to_readyOrABHitGate
    (ring : DirectedRing n) (k horizon : Nat)
    (hmixing : FixedFrontMassTasepMarked11EndpointBoundAt
      ring k horizon)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n)
    (hmass : frontConfigMass (homeFrontFrontProjection X) = k)
    (hhome : (X (ring.rightNeighbor edge)).1 = true) :
    HomeFrontInverseSquareReadyOrABHitGate ring X horizon := by
  exact tasepMarked11InverseSquareEndpointGate_to_readyOrABHitGate
    ring X edge hhome horizon (hmixing.2.2.2 _ _ hmass)

#print axioms positive_homeFrontACAC_four_not_inverseSquareABGate
#print axioms positiveHomeFront_inverseSquareReadyOrABHitGate_to_dropOrReady
#print axioms tasepMarked11EndpointCount_le_homeFrontReadyOrABHitTree
#print axioms fixedFrontMassTasepMarked11EndpointBoundAt_to_readyOrABHitGate

end PPartialSealSweepABGateBreakthroughSol
end PPLLCompleteMultiLeaderCleanup

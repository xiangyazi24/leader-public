import Leader.Wu.Seal.ReadySuffixHalfMass

/-!
# Exact AB-to-endpoint composition without readiness persistence

The fixed-AB queue argument counts scheduler words that *visit* a loaded home
trap.  Such a trap need not persist: the verified seven-site regression reaches
readiness and then loses it without losing a home.  This file therefore stops
only the proof tree, not the physical run.  At the first ready state it spends
all remaining scheduler clocks through `homeFrontHitReady_suffix_half_mass`.

The resulting exact finite-count statement has two layers.

* From a positive quotient state carrying an `A B` anchor, a length
  `2 * n^3` suffix ends dropped-or-ready with at least one quarter of the
  uniform scheduler mass.
* If a preceding gate supplies `A B` endpoints with inverse-square mass, the
  composed endpoint mass is at least `1 / (4*n^2)` before the final scheduled
  home-drop edge.

The second theorem deliberately carries the still-missing TASEP gate as one
explicit integer inequality.  No persistence premise, independence axiom, or
source change is hidden in the interface.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepABReadyCompositionSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepHomeTrapWorkloadSol
open PPartialSealSweepReadySuffixHalfMassSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-- The two sites on the directed edge `anchor` are exactly the fixed `A B`
bond used by the queue-potential argument. -/
def HomeFrontABAnchor (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n) : Prop :=
  X anchor = (true, true) /\
    X (ring.rightNeighbor anchor) = (true, false)

/-! ## Finite scheduler sums and endpoint counts from an intermediate state -/

private def abReadyFinSum {m : Nat} (f : Fin m -> Nat) : Nat :=
  (List.ofFn f).sum

private theorem abReadyFinSum_succ {m : Nat}
    (f : Fin (m + 1) -> Nat) :
    abReadyFinSum f = f 0 + abReadyFinSum (fun i : Fin m => f i.succ) := by
  unfold abReadyFinSum
  rw [List.ofFn_succ, List.sum_cons]

private theorem abReadyFinSum_eq {m : Nat}
    (f g : Fin m -> Nat) (hfg : forall i, f i = g i) :
    abReadyFinSum f = abReadyFinSum g := by
  induction m with
  | zero => simp [abReadyFinSum]
  | succ m ih =>
      rw [abReadyFinSum_succ, abReadyFinSum_succ]
      rw [hfg 0]
      exact congrArg (g 0 + .)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem abReadyFinSum_le {m : Nat}
    (f g : Fin m -> Nat) (hfg : forall i, f i <= g i) :
    abReadyFinSum f <= abReadyFinSum g := by
  induction m with
  | zero => simp [abReadyFinSum]
  | succ m ih =>
      rw [abReadyFinSum_succ, abReadyFinSum_succ]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem abReadyFinSum_add {m : Nat} (f g : Fin m -> Nat) :
    abReadyFinSum (fun i => f i + g i) =
      abReadyFinSum f + abReadyFinSum g := by
  induction m with
  | zero => simp [abReadyFinSum]
  | succ m ih =>
      rw [abReadyFinSum_succ, abReadyFinSum_succ,
        abReadyFinSum_succ]
      rw [ih]
      omega

private theorem abReadyFinSum_mul_left {m : Nat}
    (c : Nat) (f : Fin m -> Nat) :
    abReadyFinSum (fun i => c * f i) = c * abReadyFinSum f := by
  induction m with
  | zero => simp [abReadyFinSum]
  | succ m ih =>
      rw [abReadyFinSum_succ, abReadyFinSum_succ]
      rw [ih, Nat.mul_add]

private theorem abReadyFinSum_const (m c : Nat) :
    abReadyFinSum (fun _ : Fin m => c) = m * c := by
  induction m with
  | zero => simp [abReadyFinSum]
  | succ m ih =>
      rw [abReadyFinSum_succ]
      rw [ih, Nat.succ_mul]
      omega

/-- Number of depth-`t` scheduler leaves that have not yet visited a loaded
home trap.  Ready nodes are absorbing only in this proof tree; the physical
quotient is never modified or assumed to remain ready. -/
noncomputable def homeFrontABReadyMissTree (ring : DirectedRing n) :
    (Fin n -> SealSweepHomeFrontSite) -> Nat -> Nat
  | X, 0 =>
      @ite Nat (HomeFrontHitReady ring X) (Classical.propDecidable _) 0 1
  | X, t + 1 =>
      @ite Nat (HomeFrontHitReady ring X) (Classical.propDecidable _) 0
        (abReadyFinSum (fun edge => homeFrontABReadyMissTree ring
          (localStep ring sealSweepHomeFrontPair X edge) t))

/-- Exact fixed-anchor stopped-drift interface.  The separate queue-potential
proof must show that at most half of the length-`2*n^3` scheduler layer avoids
first readiness. -/
def HomeFrontABStoppedReadyHalf (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n) : Prop :=
  HomeFrontABAnchor ring X anchor ->
    (¬ HomeFrontHitReady ring X) ->
      2 * homeFrontABReadyMissTree ring X (2 * n ^ 3) <=
        n ^ (2 * n ^ 3)

/-- Endpoint count relative to a fixed block source, while execution begins at
an intermediate state.  The public endpoint count is the diagonal case. -/
noncomputable def homeFrontDropOrReadyEndpointCountFrom
    (ring : DirectedRing n)
    (source current : Fin n -> SealSweepHomeFrontSite) (t : Nat) : Nat :=
  (allSchedules n t).countP (fun word =>
    homeFrontDropOrReadyEndpointTest ring source
      (runLocalSchedule ring sealSweepHomeFrontPair current word))

@[simp] theorem homeFrontDropOrReadyEndpointCountFrom_self
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (t : Nat) :
    homeFrontDropOrReadyEndpointCountFrom ring X X t =
      homeFrontDropOrReadyEndpointCount ring X t := by
  rfl

private theorem homeFrontDropOrReadyEndpointTest_eq_of_homeCount_eq
    (ring : DirectedRing n)
    (source current final : Fin n -> SealSweepHomeFrontSite)
    (hcount : homeFrontHomeCount current = homeFrontHomeCount source) :
    homeFrontDropOrReadyEndpointTest ring source final =
      homeFrontDropOrReadyEndpointTest ring current final := by
  classical
  simp only [homeFrontDropOrReadyEndpointTest]
  rw [hcount]

theorem homeFrontDropOrReadyEndpointCountFrom_eq_of_homeCount_eq
    (ring : DirectedRing n)
    (source current : Fin n -> SealSweepHomeFrontSite) (t : Nat)
    (hcount : homeFrontHomeCount current = homeFrontHomeCount source) :
    homeFrontDropOrReadyEndpointCountFrom ring source current t =
      homeFrontDropOrReadyEndpointCount ring current t := by
  unfold homeFrontDropOrReadyEndpointCountFrom
  unfold homeFrontDropOrReadyEndpointCount
  apply congrArg (fun p => (allSchedules n t).countP p)
  funext word
  exact homeFrontDropOrReadyEndpointTest_eq_of_homeCount_eq
    ring source current
      (runLocalSchedule ring sealSweepHomeFrontPair current word) hcount

/-- Split an intermediate endpoint count by its first scheduler edge. -/
theorem homeFrontDropOrReadyEndpointCountFrom_succ
    (ring : DirectedRing n)
    (source current : Fin n -> SealSweepHomeFrontSite) (t : Nat) :
    homeFrontDropOrReadyEndpointCountFrom ring source current (t + 1) =
      abReadyFinSum (fun edge =>
        homeFrontDropOrReadyEndpointCountFrom ring source
          (localStep ring sealSweepHomeFrontPair current edge) t) := by
  unfold homeFrontDropOrReadyEndpointCountFrom
  rw [show t + 1 = 1 + t by omega, allSchedules_add,
    List.countP_flatMap]
  have hone : allSchedules n 1 =
      List.ofFn (fun edge : Fin n => [edge]) := by
    simp [allSchedules]
  rw [hone, List.map_ofFn]
  apply abReadyFinSum_eq
  intro edge
  change ((allSchedules n t).map (fun suffix => [edge] ++ suffix)).countP
      (fun word => homeFrontDropOrReadyEndpointTest ring source
        (runLocalSchedule ring sealSweepHomeFrontPair current word)) =
    (allSchedules n t).countP (fun word =>
      homeFrontDropOrReadyEndpointTest ring source
        (runLocalSchedule ring sealSweepHomeFrontPair
          (localStep ring sealSweepHomeFrontPair current edge) word))
  rw [List.countP_map]
  apply congrArg (fun p => (allSchedules n t).countP p)
  funext suffix
  simp only [Function.comp_apply]
  rw [runLocalSchedule_append]
  rfl

/-! ## Stop the proof tree at first readiness, then run the physical suffix -/

/-- Good endpoint leaves harvested after the first ready state.  At a ready
node this uses the actual remaining physical run; at a non-ready node it
branches on the next scheduler edge.  Thus the definition never assumes that
readiness persists. -/
noncomputable def homeFrontTransientReadyHarvest
    (ring : DirectedRing n)
    (source : Fin n -> SealSweepHomeFrontSite) :
    (Fin n -> SealSweepHomeFrontSite) -> Nat -> Nat
  | current, 0 =>
      @ite Nat (HomeFrontHitReady ring current) (Classical.propDecidable _)
        (homeFrontDropOrReadyEndpointCountFrom ring source current 0) 0
  | current, t + 1 =>
      @ite Nat (HomeFrontHitReady ring current) (Classical.propDecidable _)
        (homeFrontDropOrReadyEndpointCountFrom ring source current (t + 1))
        (abReadyFinSum (fun edge =>
          homeFrontTransientReadyHarvest ring source
            (localStep ring sealSweepHomeFrontPair current edge) t))

/-- The harvested first-ready subtree is a literal subset of all good endpoint
words at the same horizon. -/
theorem homeFrontTransientReadyHarvest_le_endpointCountFrom
    (ring : DirectedRing n)
    (source current : Fin n -> SealSweepHomeFrontSite) (t : Nat) :
    homeFrontTransientReadyHarvest ring source current t <=
      homeFrontDropOrReadyEndpointCountFrom ring source current t := by
  induction t generalizing current with
  | zero =>
      by_cases hready : HomeFrontHitReady ring current
      · simp [homeFrontTransientReadyHarvest, hready]
      · simp [homeFrontTransientReadyHarvest, hready]
  | succ t ih =>
      by_cases hready : HomeFrontHitReady ring current
      · simp [homeFrontTransientReadyHarvest, hready]
      · rw [homeFrontTransientReadyHarvest]
        rw [if_neg hready]
        rw [homeFrontDropOrReadyEndpointCountFrom_succ]
        exact abReadyFinSum_le _ _ (fun edge => ih _)

private theorem positiveHomeFrontState_homeCount_localStep_eq_of_not_ready
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hnotReady : ¬ HomeFrontHitReady ring X) (edge : Fin n) :
    homeFrontHomeCount
        (localStep ring sealSweepHomeFrontPair X edge) =
      homeFrontHomeCount X := by
  have hle := homeFrontHomeCount_localStep_le ring X edge
  have hnotLt : ¬ (homeFrontHomeCount
      (localStep ring sealSweepHomeFrontPair X edge) <
        homeFrontHomeCount X) := by
    intro hlt
    have hhit :=
      (positiveHomeFrontState_homeCount_localStep_lt_iff
        ring hn X hX edge).1 hlt
    exact hnotReady ⟨edge, hhit⟩
  omega

/-- Every scheduler leaf is either still in the absorbing ready-miss tree, or
is charged (with factor two) to an endpoint harvested after its first ready
state.  The home-count equality is maintained exactly along every non-ready
branch. -/
theorem positiveHomeFront_readyMiss_add_two_harvest
    (ring : DirectedRing n) (hn : 1 < n)
    (source current : Fin n -> SealSweepHomeFrontSite)
    (hcurrent : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring current)
    (hcount : homeFrontHomeCount current = homeFrontHomeCount source)
    (t : Nat) :
    n ^ t <= homeFrontABReadyMissTree ring current t +
      2 * homeFrontTransientReadyHarvest ring source current t := by
  induction t generalizing current with
  | zero =>
      by_cases hready : HomeFrontHitReady ring current
      · have hsuffix := homeFrontHitReady_suffix_half_mass
          ring current hready 0
        rw [← homeFrontDropOrReadyEndpointCountFrom_eq_of_homeCount_eq
          ring source current 0 hcount] at hsuffix
        simpa [homeFrontABReadyMissTree,
          homeFrontTransientReadyHarvest, hready] using hsuffix
      · simp [homeFrontABReadyMissTree,
          homeFrontTransientReadyHarvest, hready]
  | succ t ih =>
      by_cases hready : HomeFrontHitReady ring current
      · have hsuffix := homeFrontHitReady_suffix_half_mass
          ring current hready (t + 1)
        rw [← homeFrontDropOrReadyEndpointCountFrom_eq_of_homeCount_eq
          ring source current (t + 1) hcount] at hsuffix
        simpa [homeFrontABReadyMissTree,
          homeFrontTransientReadyHarvest, hready] using hsuffix
      · have hchildren : forall edge : Fin n,
            n ^ t <=
              homeFrontABReadyMissTree ring
                  (localStep ring sealSweepHomeFrontPair current edge) t +
                2 * homeFrontTransientReadyHarvest ring source
                  (localStep ring sealSweepHomeFrontPair current edge) t := by
          intro edge
          have hstepCount :=
            positiveHomeFrontState_homeCount_localStep_eq_of_not_ready
              ring hn current hcurrent hready edge
          exact ih
            (localStep ring sealSweepHomeFrontPair current edge)
            (positiveHomeFrontState_localStep ring current hcurrent edge)
            (hstepCount.trans hcount)
        have hsum := abReadyFinSum_le
          (fun _ : Fin n => n ^ t)
          (fun edge =>
            homeFrontABReadyMissTree ring
                (localStep ring sealSweepHomeFrontPair current edge) t +
              2 * homeFrontTransientReadyHarvest ring source
                (localStep ring sealSweepHomeFrontPair current edge) t)
          hchildren
        rw [abReadyFinSum_const, abReadyFinSum_add,
          abReadyFinSum_mul_left] at hsum
        simpa [homeFrontABReadyMissTree,
          homeFrontTransientReadyHarvest, hready, Nat.pow_succ,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsum

/-! ## The quarter-mass AB theorem -/

/-- The exact composition that survives the seven-site counterexample.  The
fixed-anchor stopped drift supplies half the mass that visits readiness; the
generic suffix involution keeps half of each first-ready continuation good at
the endpoint. -/
theorem positiveHomeFrontABAnchor_dropOrReady_quarter_at_twoCubic
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite) (anchor : Fin n)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (hanchor : HomeFrontABAnchor ring X anchor)
    (hnotReady : ¬ HomeFrontHitReady ring X)
    (hprefix : HomeFrontABStoppedReadyHalf ring X anchor) :
    n ^ (2 * n ^ 3) <=
      4 * homeFrontDropOrReadyEndpointCount ring X (2 * n ^ 3) := by
  let t := 2 * n ^ 3
  have hpartition := positiveHomeFront_readyMiss_add_two_harvest
    ring hn X X hX rfl t
  have hsubset := homeFrontTransientReadyHarvest_le_endpointCountFrom
    ring X X t
  have hprefixMass := hprefix hanchor hnotReady
  change 2 * homeFrontABReadyMissTree ring X t <= n ^ t at hprefixMass
  change n ^ t <= homeFrontABReadyMissTree ring X t +
    2 * homeFrontTransientReadyHarvest ring X X t at hpartition
  rw [homeFrontDropOrReadyEndpointCountFrom_self] at hsubset
  change n ^ t <=
    4 * homeFrontDropOrReadyEndpointCount ring X t
  omega

/-! ## Precise inverse-square pre-gate interface -/

/-- Some directed edge of the endpoint is the exact `A B` bond used by the
fixed-anchor argument. -/
def HomeFrontHasABAnchor (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) : Prop :=
  exists anchor : Fin n, HomeFrontABAnchor ring X anchor

noncomputable def homeFrontHasABAnchorTest (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) : Bool := by
  classical
  exact decide (HomeFrontHasABAnchor ring X)

theorem homeFrontHasABAnchorTest_spec (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) :
    homeFrontHasABAnchorTest ring X = true <->
      HomeFrontHasABAnchor ring X := by
  classical
  simp [homeFrontHasABAnchorTest]

/-- Number of pre-gate scheduler words whose endpoint carries an `A B`
anchor.  Reachability and positivity are inherited from the source and are
therefore not duplicated inside the Boolean test. -/
noncomputable def homeFrontABAnchorEndpointCount
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (t : Nat) : Nat :=
  (allSchedules n t).countP (fun word =>
    homeFrontHasABAnchorTest ring
      (runLocalSchedule ring sealSweepHomeFrontPair X word))

/-- Exact remaining TASEP pre-gate obligation: a length-`gate` uniform layer
ends at an `A B` anchor with inverse-square mass. -/
def HomeFrontInverseSquareABGate
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (gate : Nat) : Prop :=
  n ^ gate <= n ^ 2 * homeFrontABAnchorEndpointCount ring X gate

private theorem countP_mul_le_mul_sum_of_true
    {alpha : Type} (xs : List alpha) (p : alpha -> Bool)
    (f : alpha -> Nat) (mass factor : Nat)
    (h : forall x, x ∈ xs -> p x = true -> mass <= factor * f x) :
    mass * xs.countP p <= factor * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : forall y, y ∈ xs -> p y = true ->
          mass <= factor * f y := by
        intro y hy
        exact h y (by simp [hy])
      have hi := ih htail
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      cases hp : p x
      · simp only [hp, Bool.false_eq_true, if_false]
        calc
          mass * xs.countP p <= factor * (xs.map f).sum := hi
          _ <= factor * f x + factor * (xs.map f).sum := by omega
          _ = factor * (f x + (xs.map f).sum) := by
            rw [Nat.mul_add]
      · have hx := h x (by simp) hp
        simp only [hp, if_true]
        calc
          mass * (xs.countP p + 1) =
              mass * xs.countP p + mass := by
            rw [Nat.mul_add]
            simp
          _ <= factor * (xs.map f).sum + factor * f x :=
            Nat.add_le_add hi hx
          _ = factor * (f x + (xs.map f).sum) := by
            rw [Nat.mul_add]
            ac_rfl

private theorem positiveHomeFrontHasAB_quarter_suffix_from_source
    (ring : DirectedRing n) (hn : 1 < n)
    (source current : Fin n -> SealSweepHomeFrontSite)
    (hcurrent : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring current)
    (hAB : HomeFrontHasABAnchor ring current)
    (hcountLe : homeFrontHomeCount current <= homeFrontHomeCount source)
    (hdrift : forall anchor : Fin n,
      HomeFrontABStoppedReadyHalf ring current anchor) :
    n ^ (2 * n ^ 3) <=
      4 * homeFrontDropOrReadyEndpointCountFrom ring source current
        (2 * n ^ 3) := by
  by_cases hdrop : homeFrontHomeCount current < homeFrontHomeCount source
  · have hall : homeFrontDropOrReadyEndpointCountFrom ring source current
        (2 * n ^ 3) = (allSchedules n (2 * n ^ 3)).length := by
      unfold homeFrontDropOrReadyEndpointCountFrom
      apply List.countP_eq_length.mpr
      intro word _hword
      have hfinalLe := positiveHomeFrontState_run_homeCount_le
        ring current hcurrent word
      apply (homeFrontDropOrReadyEndpointTest_spec ring source
        (runLocalSchedule ring sealSweepHomeFrontPair current word)).2
      exact Or.inl (Nat.lt_of_le_of_lt hfinalLe hdrop)
    rw [hall, allSchedules_length]
    omega
  · have hcount : homeFrontHomeCount current =
        homeFrontHomeCount source := by omega
    obtain ⟨anchor, hanchor⟩ := hAB
    by_cases hready : HomeFrontHitReady ring current
    · have hsuffix := homeFrontHitReady_suffix_half_mass
        ring current hready (2 * n ^ 3)
      rw [← homeFrontDropOrReadyEndpointCountFrom_eq_of_homeCount_eq
        ring source current (2 * n ^ 3) hcount] at hsuffix
      omega
    · have hab := positiveHomeFrontABAnchor_dropOrReady_quarter_at_twoCubic
        (psi := psi) (kappa := kappa) (tau := tau)
        ring hn current anchor hcurrent hanchor hready (hdrift anchor)
      rw [← homeFrontDropOrReadyEndpointCountFrom_eq_of_homeCount_eq
        ring source current (2 * n ^ 3) hcount] at hab
      exact hab

/-- Every inverse-square `A B` pre-gate composes with the cubic stopped-drift
and transient-ready suffix arguments.  The conclusion is the exact
`1/(4*n^2)` endpoint-mass bound requested before the final scheduled drop.

The suffix horizon is fixed to `2*n^3`; this is the only horizon at which the
fixed-anchor stopped tree has currently been proved to have half-mass. -/
theorem positiveHomeFront_inverseSquareABGate_to_dropOrReady
    (ring : DirectedRing n) (hn : 1 < n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X)
    (gate : Nat)
    (hgate : HomeFrontInverseSquareABGate ring X gate)
    (hdrift : forall Y : Fin n -> SealSweepHomeFrontSite,
      SealSweepPositiveHomeFrontState
        (psi := psi) (kappa := kappa) (tau := tau) ring Y ->
      forall anchor : Fin n,
        HomeFrontABStoppedReadyHalf ring Y anchor) :
    n ^ (gate + 2 * n ^ 3) <=
      4 * n ^ 2 * homeFrontDropOrReadyEndpointCount ring X
        (gate + 2 * n ^ 3) := by
  let suffix := 2 * n ^ 3
  let endpointFrom : DetSchedule n -> Nat := fun pre =>
    homeFrontDropOrReadyEndpointCountFrom ring X
      (runLocalSchedule ring sealSweepHomeFrontPair X pre) suffix
  have hpoint : forall pre, pre ∈ allSchedules n gate ->
      homeFrontHasABAnchorTest ring
          (runLocalSchedule ring sealSweepHomeFrontPair X pre) = true ->
      n ^ suffix <= 4 * endpointFrom pre := by
    intro pre _hpre hABTest
    let Y := runLocalSchedule ring sealSweepHomeFrontPair X pre
    have hY := positiveHomeFrontState_run ring X hX pre
    have hAB : HomeFrontHasABAnchor ring Y :=
      (homeFrontHasABAnchorTest_spec ring Y).1 hABTest
    have hcountLe := positiveHomeFrontState_run_homeCount_le
      ring X hX pre
    exact positiveHomeFrontHasAB_quarter_suffix_from_source
      ring hn X Y hY hAB hcountLe (hdrift Y hY)
  have hsum := countP_mul_le_mul_sum_of_true
    (allSchedules n gate)
    (fun pre => homeFrontHasABAnchorTest ring
      (runLocalSchedule ring sealSweepHomeFrontPair X pre))
    endpointFrom (n ^ suffix) 4 hpoint
  have hdecomp : homeFrontDropOrReadyEndpointCount ring X
        (gate + suffix) =
      ((allSchedules n gate).map endpointFrom).sum := by
    unfold homeFrontDropOrReadyEndpointCount
    unfold endpointFrom homeFrontDropOrReadyEndpointCountFrom
    rw [allSchedules_add, List.countP_flatMap]
    apply congrArg List.sum
    apply List.map_congr_left
    intro pre _hpre
    change ((allSchedules n suffix).map (fun tail => pre ++ tail)).countP
        (fun word => homeFrontDropOrReadyEndpointTest ring X
          (runLocalSchedule ring sealSweepHomeFrontPair X word)) =
      (allSchedules n suffix).countP (fun word =>
        homeFrontDropOrReadyEndpointTest ring X
          (runLocalSchedule ring sealSweepHomeFrontPair
            (runLocalSchedule ring sealSweepHomeFrontPair X pre) word))
    rw [List.countP_map]
    apply congrArg (fun p => (allSchedules n suffix).countP p)
    funext tail
    simp only [Function.comp_apply]
    rw [runLocalSchedule_append]
  change n ^ gate <= n ^ 2 *
    (allSchedules n gate).countP (fun pre =>
      homeFrontHasABAnchorTest ring
        (runLocalSchedule ring sealSweepHomeFrontPair X pre)) at hgate
  change n ^ suffix *
    (allSchedules n gate).countP (fun pre =>
      homeFrontHasABAnchorTest ring
        (runLocalSchedule ring sealSweepHomeFrontPair X pre)) <=
      4 * ((allSchedules n gate).map endpointFrom).sum at hsum
  rw [← hdecomp] at hsum
  change n ^ (gate + suffix) <=
    4 * n ^ 2 * homeFrontDropOrReadyEndpointCount ring X
      (gate + suffix)
  rw [Nat.pow_add]
  calc
    n ^ gate * n ^ suffix <=
        (n ^ 2 * homeFrontABAnchorEndpointCount ring X gate) *
          n ^ suffix := Nat.mul_le_mul_right _ hgate
    _ = n ^ 2 * (n ^ suffix *
          homeFrontABAnchorEndpointCount ring X gate) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ <= n ^ 2 *
          (4 * homeFrontDropOrReadyEndpointCount ring X
            (gate + suffix)) := by
        apply Nat.mul_le_mul_left
        simpa [homeFrontABAnchorEndpointCount] using hsum
    _ = 4 * n ^ 2 * homeFrontDropOrReadyEndpointCount ring X
          (gate + suffix) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

#print axioms homeFrontDropOrReadyEndpointCountFrom_succ
#print axioms positiveHomeFront_readyMiss_add_two_harvest
#print axioms positiveHomeFrontABAnchor_dropOrReady_quarter_at_twoCubic
#print axioms positiveHomeFront_inverseSquareABGate_to_dropOrReady

end PPartialSealSweepABReadyCompositionSol
end PPLLCompleteMultiLeaderCleanup

import Leader.Wu.Seal.TasepFiniteTime

/-!
# A first moving-particle comparison for the seal-sweep TASEP slice

This file adds a concrete analytic brick above the frozen finite-time core.
It does not assume a spectral estimate or pointwise mixing.  Instead it proves
the first nontrivial canonical path exactly: exchanging sites at clockwise
distance two is the three-adjacent-swap word

`s_x ; s_(x+1) ; s_x`.

The corresponding integer-valued observable estimate has the explicit
constant three.  Each of the three adjacent legs stays in the fixed-mass
slice, and its squared gap is controlled directly by the exact denominator-
cleared common-successor count from the frozen core.

The remaining moving-particle step is genuinely larger: route arbitrary
clockwise distances by a forward/backward adjacent word, prove the endpoint
permutation identity, and sum those paths with an explicit congestion count.
Nothing in this file treats that global comparison as an input.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepTasepMovingParticleComparisonSol

open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepRotationBridgeSol
open PPartialSealSweepTasepFiniteTimeSol

set_option autoImplicit false

variable {n : Nat}

/-! ## Coordinate transpositions and the exact distance-two word -/

/-- Exchange two arbitrary coordinates of a Boolean front configuration. -/
def transposeFrontConfig (F : Fin n -> Bool) (x z : Fin n) : Fin n -> Bool :=
  fun i => if i = x then F z else if i = z then F x else F i

/-- The site two clockwise edges after `x`. -/
def secondRightNeighbor (ring : DirectedRing n) (x : Fin n) : Fin n :=
  ring.rightNeighbor (ring.rightNeighbor x)

/-- First configuration on the distance-two canonical path. -/
def distanceTwoPathOne (ring : DirectedRing n)
    (F : Fin n -> Bool) (x : Fin n) : Fin n -> Bool :=
  swapFrontConfigAt ring F x

/-- Second configuration on the distance-two canonical path. -/
def distanceTwoPathTwo (ring : DirectedRing n)
    (F : Fin n -> Bool) (x : Fin n) : Fin n -> Bool :=
  swapFrontConfigAt ring (distanceTwoPathOne ring F x)
    (ring.rightNeighbor x)

/-- Endpoint of the three-adjacent-swap distance-two canonical path. -/
def distanceTwoPathThree (ring : DirectedRing n)
    (F : Fin n -> Bool) (x : Fin n) : Fin n -> Bool :=
  swapFrontConfigAt ring (distanceTwoPathTwo ring F x) x

/-- On a ring of size at least three, a site, its successor, and its second
successor are pairwise distinct. -/
theorem distanceTwo_sites_pairwise_distinct
    (ring : DirectedRing n) (hn : 2 < n) (x : Fin n) :
    x ≠ ring.rightNeighbor x /\
      x ≠ secondRightNeighbor ring x /\
      ring.rightNeighbor x ≠ secondRightNeighbor ring x := by
  have hxy : x ≠ ring.rightNeighbor x :=
    (rightNeighbor_ne_self_of_one_lt ring (by omega) x).symm
  have hyz : ring.rightNeighbor x ≠ secondRightNeighbor ring x := by
    exact (rightNeighbor_ne_self_of_one_lt ring (by omega)
      (ring.rightNeighbor x)).symm
  have hpos : cwPos ring x 2 = secondRightNeighbor ring x := by
    simp [secondRightNeighbor, cwPos_succ]
  have hxz : x ≠ secondRightNeighbor ring x := by
    intro hzx
    have hbounded := cwPos_bounded_unique ring x x 2 hn
      (hpos.trans hzx.symm)
    have hzero : cwDist ring x x = 0 := by
      simp [cwDist, Nat.mod_eq_of_lt x.isLt]
    omega
  exact ⟨hxy, hxz, hyz⟩

theorem distanceTwoPathThree_eq_transposeFrontConfig
    (ring : DirectedRing n) (hn : 2 < n)
    (F : Fin n -> Bool) (x : Fin n) :
    distanceTwoPathThree ring F x =
      transposeFrontConfig F x (secondRightNeighbor ring x) := by
  rcases distanceTwo_sites_pairwise_distinct ring hn x with
    ⟨hxy, hxz, hyz⟩
  funext i
  by_cases hix : i = x
  · subst i
    simp_all [distanceTwoPathThree, distanceTwoPathTwo,
      distanceTwoPathOne, transposeFrontConfig, secondRightNeighbor,
      swapFrontConfigAt, eq_comm]
  · by_cases hiy : i = ring.rightNeighbor x
    · subst i
      simp_all [distanceTwoPathThree, distanceTwoPathTwo,
        distanceTwoPathOne, transposeFrontConfig, secondRightNeighbor,
        swapFrontConfigAt, eq_comm]
    · by_cases hiz : i = secondRightNeighbor ring x
      · subst i
        simp_all [distanceTwoPathThree, distanceTwoPathTwo,
          distanceTwoPathOne, transposeFrontConfig, secondRightNeighbor,
          swapFrontConfigAt, eq_comm]
      · simp_all [distanceTwoPathThree, distanceTwoPathTwo,
          distanceTwoPathOne, transposeFrontConfig, secondRightNeighbor,
          swapFrontConfigAt, eq_comm]

theorem transposeFrontConfig_involutive (x z : Fin n) :
    forall F : Fin n -> Bool,
      transposeFrontConfig (transposeFrontConfig F x z) x z = F := by
  intro F
  funext i
  by_cases hxz : x = z
  · subst z
    by_cases hix : i = x
    · subst i
      simp [transposeFrontConfig]
    · simp [transposeFrontConfig, hix]
  · have hzx : z ≠ x := by
      intro h
      exact hxz h.symm
    by_cases hix : i = x
    · subst i
      simp [transposeFrontConfig, hxz, hzx]
    · by_cases hiz : i = z
      · subst i
        simp [transposeFrontConfig, hxz, hzx, hix]
      · simp [transposeFrontConfig, hxz, hzx, hix, hiz]

theorem swapFrontConfigAt_involutive
    (ring : DirectedRing n) (edge : Fin n) :
    forall F : Fin n -> Bool,
      swapFrontConfigAt ring
          (swapFrontConfigAt ring F edge) edge = F := by
  intro F
  change transposeFrontConfig
      (transposeFrontConfig F edge (ring.rightNeighbor edge))
        edge (ring.rightNeighbor edge) = F
  exact transposeFrontConfig_involutive edge
    (ring.rightNeighbor edge) F

/-- An adjacent coordinate swap is the identity when its two endpoint bits
agree. -/
theorem swapFrontConfigAt_eq_self_of_endpoint_eq
    (ring : DirectedRing n) (F : Fin n -> Bool) (edge : Fin n)
    (heq : F edge = F (ring.rightNeighbor edge)) :
    swapFrontConfigAt ring F edge = F := by
  funext i
  by_cases hie : i = edge
  · subst i
    simp [swapFrontConfigAt, heq]
  · by_cases hir : i = ring.rightNeighbor edge
    · subst i
      simp [swapFrontConfigAt, hie, heq]
    · simp [swapFrontConfigAt, hie, hir]

/-- Adjacent symmetric swaps preserve front mass, including the stuttering
case omitted by the oriented-neighbor theorem in the frozen core. -/
theorem frontConfigMass_swapFrontConfigAt
    (ring : DirectedRing n) (hn : 1 < n)
    (F : Fin n -> Bool) (edge : Fin n) :
    frontConfigMass (swapFrontConfigAt ring F edge) =
      frontConfigMass F := by
  by_cases hne : F edge ≠ F (ring.rightNeighbor edge)
  · exact frontConfigMass_swapFrontConfigAt_of_endpoint_ne
      ring hn F edge hne
  · have heq : F edge = F (ring.rightNeighbor edge) :=
      Decidable.not_not.mp hne
    rw [swapFrontConfigAt_eq_self_of_endpoint_eq ring F edge heq]

private theorem movingParticle_nodup_map_of_injective
    {alpha beta : Type} {xs : List alpha}
    (hxs : xs.Nodup) (f : alpha -> beta) (hf : Function.Injective f) :
    (xs.map f).Nodup := by
  exact List.Pairwise.map f (fun _ _ hne => hf.ne hne) hxs

theorem tasepFrontConfigSlice_map_swap_perm
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat) (edge : Fin n) :
    List.Perm
      ((tasepFrontConfigSlice n k).map
        (fun F => swapFrontConfigAt ring F edge))
      (tasepFrontConfigSlice n k) := by
  classical
  have hinj :
      ∀ ⦃F G : Fin n -> Bool⦄,
        swapFrontConfigAt ring F edge =
          swapFrontConfigAt ring G edge -> F = G := by
    intro F G hFG
    calc
      F = swapFrontConfigAt ring
          (swapFrontConfigAt ring F edge) edge :=
        (swapFrontConfigAt_involutive ring edge F).symm
      _ = swapFrontConfigAt ring
          (swapFrontConfigAt ring G edge) edge :=
        congrArg (fun H : Fin n -> Bool =>
          swapFrontConfigAt ring H edge) hFG
      _ = G := swapFrontConfigAt_involutive ring edge G
  have hleftNodup :
      ((tasepFrontConfigSlice n k).map
        (fun F => swapFrontConfigAt ring F edge)).Nodup :=
    movingParticle_nodup_map_of_injective
      (tasepFrontConfigSlice_nodup n k) _ hinj
  apply (List.perm_ext_iff_of_nodup hleftNodup
    (tasepFrontConfigSlice_nodup n k)).2
  intro G
  rw [List.mem_map]
  constructor
  · rintro ⟨F, hF, rfl⟩
    apply (mem_tasepFrontConfigSlice_iff _).mpr
    rw [frontConfigMass_swapFrontConfigAt ring hn]
    exact (mem_tasepFrontConfigSlice_iff F).mp hF
  · intro hG
    refine ⟨swapFrontConfigAt ring G edge, ?_, ?_⟩
    · apply (mem_tasepFrontConfigSlice_iff _).mpr
      rw [frontConfigMass_swapFrontConfigAt ring hn]
      exact (mem_tasepFrontConfigSlice_iff G).mp hG
    · exact swapFrontConfigAt_involutive ring edge G

/-- Reindexing any natural-valued slice sum by one adjacent swap leaves the
sum unchanged. -/
theorem tasepFrontConfigSlice_sum_swap
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat) (edge : Fin n)
    (weight : (Fin n -> Bool) -> Nat) :
    ((tasepFrontConfigSlice n k).map (fun F =>
      weight (swapFrontConfigAt ring F edge))).sum =
      ((tasepFrontConfigSlice n k).map weight).sum := by
  have hperm :=
    (tasepFrontConfigSlice_map_swap_perm ring hn k edge).map weight
  simpa [List.map_map, Function.comp_def] using hperm.sum_nat

/-- The first two legs, viewed as a map of the source configuration, also
permute every fixed-mass slice.  This closes the reindexing needed for the
third energy term in the distance-two global sum. -/
theorem tasepFrontConfigSlice_sum_distanceTwoPathTwo
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat) (x : Fin n)
    (weight : (Fin n -> Bool) -> Nat) :
    ((tasepFrontConfigSlice n k).map (fun F =>
      weight (distanceTwoPathTwo ring F x))).sum =
      ((tasepFrontConfigSlice n k).map weight).sum := by
  unfold distanceTwoPathTwo distanceTwoPathOne
  calc
    ((tasepFrontConfigSlice n k).map (fun F =>
        weight (swapFrontConfigAt ring
          (swapFrontConfigAt ring F x) (ring.rightNeighbor x)))).sum =
      ((tasepFrontConfigSlice n k).map (fun F =>
        weight (swapFrontConfigAt ring F (ring.rightNeighbor x)))).sum := by
          exact tasepFrontConfigSlice_sum_swap ring hn k x
            (fun F => weight
              (swapFrontConfigAt ring F (ring.rightNeighbor x)))
    _ = ((tasepFrontConfigSlice n k).map weight).sum :=
      tasepFrontConfigSlice_sum_swap ring hn k
        (ring.rightNeighbor x) weight

/-- All three configurations on the distance-two word have the initial front
mass. -/
theorem distanceTwoPath_mass_chain
    (ring : DirectedRing n) (hn : 2 < n)
    (F : Fin n -> Bool) (x : Fin n) :
    frontConfigMass (distanceTwoPathOne ring F x) = frontConfigMass F /\
      frontConfigMass (distanceTwoPathTwo ring F x) = frontConfigMass F /\
      frontConfigMass (distanceTwoPathThree ring F x) = frontConfigMass F := by
  have hn' : 1 < n := by omega
  have h1 := frontConfigMass_swapFrontConfigAt ring hn' F x
  have h2 := frontConfigMass_swapFrontConfigAt ring hn'
    (distanceTwoPathOne ring F x) (ring.rightNeighbor x)
  have h3 := frontConfigMass_swapFrontConfigAt ring hn'
    (distanceTwoPathTwo ring F x) x
  exact ⟨h1, h2.trans h1, h3.trans (h2.trans h1)⟩

/-- Membership in the concrete fixed-mass list is preserved at every point
of the distance-two route. -/
theorem distanceTwoPath_mem_slice
    (ring : DirectedRing n) (hn : 2 < n) (k : Nat)
    (F : Fin n -> Bool) (x : Fin n)
    (hF : F ∈ tasepFrontConfigSlice n k) :
    distanceTwoPathOne ring F x ∈ tasepFrontConfigSlice n k /\
      distanceTwoPathTwo ring F x ∈ tasepFrontConfigSlice n k /\
      distanceTwoPathThree ring F x ∈ tasepFrontConfigSlice n k := by
  have hmass : frontConfigMass F = k :=
    (mem_tasepFrontConfigSlice_iff F).mp hF
  rcases distanceTwoPath_mass_chain ring hn F x with ⟨h1, h2, h3⟩
  constructor
  · apply (mem_tasepFrontConfigSlice_iff _).mpr
    exact h1.trans hmass
  · constructor
    · apply (mem_tasepFrontConfigSlice_iff _).mpr
      exact h2.trans hmass
    · apply (mem_tasepFrontConfigSlice_iff _).mpr
      exact h3.trans hmass

/-! ## Division-free square comparison -/

/-- Squared absolute gap of an integer-valued observable.  The result is a
natural number, so later scheduler and common-successor counts can multiply
it without casts or division. -/
def frontSquaredGap (phi : (Fin n -> Bool) -> Int)
    (F G : Fin n -> Bool) : Nat :=
  Int.natAbs (phi F - phi G) ^ 2

private theorem int_three_term_square_le
    (a b c : Int) :
    (a + b + c) ^ 2 <=
      3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have hid :
      3 * (a ^ 2 + b ^ 2 + c ^ 2) =
        (a + b + c) ^ 2 +
          ((a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2) := by
    grind
  rw [hid]
  apply Int.le_add_of_nonneg_right
  exact Int.add_nonneg
    (Int.add_nonneg (Int.sq_nonneg (a - b)) (Int.sq_nonneg (a - c)))
    (Int.sq_nonneg (b - c))

/-- Three-step Cauchy--Schwarz with all denominators cleared. -/
theorem natAbs_three_step_square_le
    (a b c d : Int) :
    Int.natAbs (a - d) ^ 2 <=
      3 * (Int.natAbs (a - b) ^ 2 +
        Int.natAbs (b - c) ^ 2 + Int.natAbs (c - d) ^ 2) := by
  apply Int.ofNat_le.mp
  change
    (Int.natAbs (a - d) : Int) ^ 2 <=
      3 * ((Int.natAbs (a - b) : Int) ^ 2 +
        (Int.natAbs (b - c) : Int) ^ 2 +
        (Int.natAbs (c - d) : Int) ^ 2)
  rw [Int.natAbs_pow_two, Int.natAbs_pow_two,
    Int.natAbs_pow_two, Int.natAbs_pow_two]
  have h := int_three_term_square_le
    (a - b) (b - c) (c - d)
  have htel : (a - b) + (b - c) + (c - d) = a - d := by
    omega
  rw [htel] at h
  exact h

/-- Observable square gap across any three-step state path is at most three
times the sum of the three leg gaps. -/
theorem frontSquaredGap_three_step_le
    (phi : (Fin n -> Bool) -> Int)
    (F0 F1 F2 F3 : Fin n -> Bool) :
    frontSquaredGap phi F0 F3 <=
      3 * (frontSquaredGap phi F0 F1 +
        frontSquaredGap phi F1 F2 + frontSquaredGap phi F2 F3) := by
  exact natAbs_three_step_square_le
    (phi F0) (phi F1) (phi F2) (phi F3)

/-- The exact distance-two moving-particle inequality.  Its right side is the
energy of the explicit three-edge canonical route, not an abstract path
premise. -/
theorem distanceTwo_transposition_squaredGap_le
    (ring : DirectedRing n) (hn : 2 < n)
    (phi : (Fin n -> Bool) -> Int)
    (F : Fin n -> Bool) (x : Fin n) :
    frontSquaredGap phi F
        (transposeFrontConfig F x (secondRightNeighbor ring x)) <=
      3 * (frontSquaredGap phi F (distanceTwoPathOne ring F x) +
        frontSquaredGap phi (distanceTwoPathOne ring F x)
          (distanceTwoPathTwo ring F x) +
        frontSquaredGap phi (distanceTwoPathTwo ring F x)
          (distanceTwoPathThree ring F x)) := by
  rw [← distanceTwoPathThree_eq_transposeFrontConfig ring hn F x]
  exact frontSquaredGap_three_step_le phi F
    (distanceTwoPathOne ring F x)
    (distanceTwoPathTwo ring F x)
    (distanceTwoPathThree ring F x)

/-! ## Exact fixed-slice distance-two energy comparison -/

private theorem movingParticle_sum_ofFn_eq
    (f g : Fin n -> Nat) (hfg : forall i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, hfg 0]
      exact congrArg (g 0 + .)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem movingParticle_sum_map_eq
    {alpha : Type} (xs : List alpha) (f g : alpha -> Nat)
    (hfg : forall x, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, hfg x]
      exact congrArg (g x + .) ih

private theorem movingParticle_sum_ofFn_add
    (f g : Fin n -> Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

/-- Exchange the order of a concrete list sum and a `Fin` sum. -/
private theorem movingParticle_sum_list_ofFn_comm
    {alpha : Type} (xs : List alpha) (f : alpha -> Fin n -> Nat) :
    (xs.map (fun x => (List.ofFn (fun i => f x i)).sum)).sum =
      (List.ofFn (fun i => (xs.map (fun x => f x i)).sum)).sum := by
  induction xs with
  | nil =>
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [List.ofFn_succ, List.sum_cons]
          simp only [List.map_nil, List.sum_nil]
          simpa using ih
  | cons x xs ih =>
      calc
        (((x :: xs).map (fun y =>
            (List.ofFn (fun i => f y i)).sum)).sum) =
            (List.ofFn (fun i => f x i)).sum +
              (xs.map (fun y =>
                (List.ofFn (fun i => f y i)).sum)).sum := by
                  rw [List.map_cons, List.sum_cons]
        _ = (List.ofFn (fun i => f x i)).sum +
              (List.ofFn (fun i =>
                (xs.map (fun y => f y i)).sum)).sum := by
                  rw [ih]
        _ = (List.ofFn (fun i =>
              f x i + (xs.map (fun y => f y i)).sum)).sum :=
                (movingParticle_sum_ofFn_add
                  (fun i => f x i)
                  (fun i => (xs.map (fun y => f y i)).sum)).symm
        _ = (List.ofFn (fun i =>
              ((x :: xs).map (fun y => f y i)).sum)).sum := by
                apply movingParticle_sum_ofFn_eq
                intro i
                rw [List.map_cons, List.sum_cons]

/-- Reindex an exact `Fin n` sum by the directed-ring successor. -/
private theorem movingParticle_sum_ofFn_rightNeighbor
    (ring : DirectedRing n) (f : Fin n -> Nat) :
    (List.ofFn (fun i => f (ring.rightNeighbor i))).sum =
      (List.ofFn f).sum := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn
      (fun i : Fin (m + 1) => f (ring.rightNeighbor i)) =
    (List.ofFn (fun i : Fin m =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last m))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last m) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : forall i : Fin m,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin m => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin m => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

private theorem movingParticle_sum_ofFn_three_le
    (f0 f1 f2 f3 : Fin n -> Nat)
    (hpoint : forall i, f0 i <= 3 * (f1 i + f2 i + f3 i)) :
    (List.ofFn f0).sum <=
      3 * ((List.ofFn f1).sum +
        (List.ofFn f2).sum + (List.ofFn f3).sum) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      have hhead := hpoint 0
      have htail := ih
        (fun i => f0 i.succ) (fun i => f1 i.succ)
        (fun i => f2 i.succ) (fun i => f3 i.succ)
        (fun i => hpoint i.succ)
      omega

private theorem movingParticle_sum_map_three_le
    {alpha : Type} (xs : List alpha)
    (f0 f1 f2 f3 : alpha -> Nat)
    (hpoint : forall x, f0 x <= 3 * (f1 x + f2 x + f3 x)) :
    (xs.map f0).sum <=
      3 * ((xs.map f1).sum + (xs.map f2).sum + (xs.map f3).sum) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhead := hpoint x
      have htail := ih
      omega

/-- Standard cyclic adjacent-swap Dirichlet numerator, with no normalization. -/
def adjacentCyclicSquaredEnergy
    (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    (List.ofFn (fun edge =>
      frontSquaredGap phi F (swapFrontConfigAt ring F edge))).sum)).sum

/-- Global numerator for transpositions at clockwise distance two. -/
def distanceTwoTranspositionSquaredEnergy
    (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    (List.ofFn (fun x => frontSquaredGap phi F
      (transposeFrontConfig F x (secondRightNeighbor ring x)))).sum)).sum

/-- First-leg energy of all distance-two canonical paths. -/
def distanceTwoFirstLegSquaredEnergy
    (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    (List.ofFn (fun x =>
      frontSquaredGap phi F (distanceTwoPathOne ring F x))).sum)).sum

/-- Middle-leg energy of all distance-two canonical paths. -/
def distanceTwoMiddleLegSquaredEnergy
    (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    (List.ofFn (fun x => frontSquaredGap phi
      (distanceTwoPathOne ring F x) (distanceTwoPathTwo ring F x))).sum)).sum

/-- Last-leg energy of all distance-two canonical paths. -/
def distanceTwoLastLegSquaredEnergy
    (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    (List.ofFn (fun x => frontSquaredGap phi
      (distanceTwoPathTwo ring F x) (distanceTwoPathThree ring F x))).sum)).sum

/-- The first route leg is definitionally the ordinary adjacent energy. -/
theorem distanceTwoFirstLegSquaredEnergy_eq_adjacent
    (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    distanceTwoFirstLegSquaredEnergy ring k phi =
      adjacentCyclicSquaredEnergy ring k phi := by
  rfl

/-- Slice reindexing followed by cyclic edge reindexing shows that the middle
route leg has exactly the ordinary adjacent energy. -/
theorem distanceTwoMiddleLegSquaredEnergy_eq_adjacent
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    distanceTwoMiddleLegSquaredEnergy ring k phi =
      adjacentCyclicSquaredEnergy ring k phi := by
  unfold distanceTwoMiddleLegSquaredEnergy
  rw [movingParticle_sum_list_ofFn_comm]
  calc
    (List.ofFn (fun x =>
        ((tasepFrontConfigSlice n k).map (fun F => frontSquaredGap phi
          (distanceTwoPathOne ring F x)
          (distanceTwoPathTwo ring F x))).sum)).sum =
      (List.ofFn (fun x =>
        ((tasepFrontConfigSlice n k).map (fun F => frontSquaredGap phi F
          (swapFrontConfigAt ring F (ring.rightNeighbor x)))).sum)).sum := by
            apply movingParticle_sum_ofFn_eq
            intro x
            simpa [distanceTwoPathOne, distanceTwoPathTwo] using
              tasepFrontConfigSlice_sum_swap ring hn k x
                (fun F => frontSquaredGap phi F
                  (swapFrontConfigAt ring F (ring.rightNeighbor x)))
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
        (List.ofFn (fun x => frontSquaredGap phi F
          (swapFrontConfigAt ring F (ring.rightNeighbor x)))).sum)).sum :=
      (movingParticle_sum_list_ofFn_comm
        (tasepFrontConfigSlice n k)
        (fun F x => frontSquaredGap phi F
          (swapFrontConfigAt ring F (ring.rightNeighbor x)))).symm
    _ = adjacentCyclicSquaredEnergy ring k phi := by
      unfold adjacentCyclicSquaredEnergy
      apply movingParticle_sum_map_eq
      intro F
      exact movingParticle_sum_ofFn_rightNeighbor ring
        (fun edge => frontSquaredGap phi F
          (swapFrontConfigAt ring F edge))

/-- Reindexing the slice by the first two swaps shows that the last route leg
also has exactly the ordinary adjacent energy. -/
theorem distanceTwoLastLegSquaredEnergy_eq_adjacent
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    distanceTwoLastLegSquaredEnergy ring k phi =
      adjacentCyclicSquaredEnergy ring k phi := by
  unfold distanceTwoLastLegSquaredEnergy
  rw [movingParticle_sum_list_ofFn_comm]
  calc
    (List.ofFn (fun x =>
        ((tasepFrontConfigSlice n k).map (fun F => frontSquaredGap phi
          (distanceTwoPathTwo ring F x)
          (distanceTwoPathThree ring F x))).sum)).sum =
      (List.ofFn (fun x =>
        ((tasepFrontConfigSlice n k).map (fun F => frontSquaredGap phi F
          (swapFrontConfigAt ring F x))).sum)).sum := by
            apply movingParticle_sum_ofFn_eq
            intro x
            simpa [distanceTwoPathThree] using
              tasepFrontConfigSlice_sum_distanceTwoPathTwo
                ring hn k x
                (fun F => frontSquaredGap phi F
                  (swapFrontConfigAt ring F x))
    _ = adjacentCyclicSquaredEnergy ring k phi := by
      unfold adjacentCyclicSquaredEnergy
      exact (movingParticle_sum_list_ofFn_comm
        (tasepFrontConfigSlice n k)
        (fun F x => frontSquaredGap phi F
          (swapFrontConfigAt ring F x))).symm

/-- Fully summed distance-two moving-particle comparison.  The constant nine
is `3` from Cauchy--Schwarz times the exact congestion `3`: each of the three
route-leg families reindexes to the adjacent energy once. -/
theorem distanceTwoTranspositionSquaredEnergy_le_nine_mul_adjacent
    (ring : DirectedRing n) (hn : 2 < n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    distanceTwoTranspositionSquaredEnergy ring k phi <=
      9 * adjacentCyclicSquaredEnergy ring k phi := by
  have hrows :
      distanceTwoTranspositionSquaredEnergy ring k phi <=
        3 * (distanceTwoFirstLegSquaredEnergy ring k phi +
          distanceTwoMiddleLegSquaredEnergy ring k phi +
          distanceTwoLastLegSquaredEnergy ring k phi) := by
    unfold distanceTwoTranspositionSquaredEnergy
    unfold distanceTwoFirstLegSquaredEnergy
    unfold distanceTwoMiddleLegSquaredEnergy
    unfold distanceTwoLastLegSquaredEnergy
    apply movingParticle_sum_map_three_le
    intro F
    apply movingParticle_sum_ofFn_three_le
    intro x
    exact distanceTwo_transposition_squaredGap_le ring hn phi F x
  rw [distanceTwoFirstLegSquaredEnergy_eq_adjacent,
    distanceTwoMiddleLegSquaredEnergy_eq_adjacent ring (by omega),
    distanceTwoLastLegSquaredEnergy_eq_adjacent ring (by omega)] at hrows
  omega

/-! ## Exact splice to the common-successor lower bound -/

/-- The frozen `P P*` numerator controls every adjacent squared observable
gap without a nontriviality premise.  If the endpoint bits agree, the gap is
zero; otherwise this is exactly the frozen `n/2` common-successor estimate
multiplied by that nonnegative integer gap. -/
theorem n_mul_adjacentSquaredGap_le_commonSuccessor
    (ring : DirectedRing n) (hn : 1 < n)
    (phi : (Fin n -> Bool) -> Int)
    (F : Fin n -> Bool) (edge : Fin n) :
    n * frontSquaredGap phi F (swapFrontConfigAt ring F edge) <=
      2 * tasepCommonSuccessorPairCount ring F
          (swapFrontConfigAt ring F edge) *
        frontSquaredGap phi F (swapFrontConfigAt ring F edge) := by
  by_cases hne : F edge ≠ F (ring.rightNeighbor edge)
  · exact Nat.mul_le_mul_right _
      (n_le_two_mul_tasepCommonSuccessorPairCount_swap
        ring hn F edge hne)
  · have heq : F edge = F (ring.rightNeighbor edge) :=
      Decidable.not_not.mp hne
    have hself := swapFrontConfigAt_eq_self_of_endpoint_eq
      ring F edge heq
    simp [frontSquaredGap, hself]

private theorem movingParticle_sum_ofFn_scaled_le
    (left right : Nat) (f g : Fin n -> Nat)
    (hpoint : forall i, left * f i <= right * g i) :
    left * (List.ofFn f).sum <= right * (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        Nat.mul_add, Nat.mul_add]
      exact Nat.add_le_add (hpoint 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hpoint i.succ))

private theorem movingParticle_sum_map_scaled_le
    {alpha : Type} (left right : Nat) (xs : List alpha)
    (f g : alpha -> Nat)
    (hpoint : forall x, left * f x <= right * g x) :
    left * (xs.map f).sum <= right * (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
        Nat.mul_add, Nat.mul_add]
      exact Nat.add_le_add (hpoint x) ih

/-- Adjacent squared energy weighted by the exact `P P*` common-successor
numerator. -/
noncomputable def commonSuccessorWeightedAdjacentSquaredEnergy
    (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    (List.ofFn (fun edge =>
      tasepCommonSuccessorPairCount ring F
          (swapFrontConfigAt ring F edge) *
        frontSquaredGap phi F
          (swapFrontConfigAt ring F edge))).sum)).sum

/-- Full unnormalized `P P*` squared energy on the concrete fixed-mass slice.
Unlike the preceding edge-indexed subenergy, this is the literal double sum
over every source and every target in the slice. -/
noncomputable def fullCommonSuccessorSquaredEnergy
    (ring : DirectedRing n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    ((tasepFrontConfigSlice n k).map (fun G =>
      tasepCommonSuccessorPairCount ring F G *
        frontSquaredGap phi F G)).sum)).sum

private theorem movingParticle_term_le_sum_map_of_mem
    {alpha : Type} (xs : List alpha) (weight : alpha -> Nat)
    {x : alpha} (hx : x ∈ xs) :
    weight x <= (xs.map weight).sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.mem_cons] at hx
      rw [List.map_cons, List.sum_cons]
      rcases hx with hxy | hx
      · subst x
        omega
      · have htail := ih hx
        omega

private theorem movingParticle_sum_ofFn_le_card_mul
    (bound : Nat) (f : Fin n -> Nat)
    (hpoint : forall i, f i <= bound) :
    (List.ofFn f).sum <= n * bound := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons]
      have hhead := hpoint 0
      have htail := ih (fun i => f i.succ) (fun i => hpoint i.succ)
      calc
        f 0 + (List.ofFn (fun i => f i.succ)).sum <=
            bound + n * bound := Nat.add_le_add hhead htail
        _ = n * bound + bound := Nat.add_comm _ _
        _ = Nat.succ n * bound := (Nat.succ_mul n bound).symm

private theorem movingParticle_sum_map_le_mul_of_mem
    {alpha : Type} (right : Nat) (xs : List alpha)
    (leftWeight rightWeight : alpha -> Nat)
    (hpoint : forall x, x ∈ xs ->
      leftWeight x <= right * rightWeight x) :
    (xs.map leftWeight).sum <= right * (xs.map rightWeight).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons, Nat.mul_add]
      apply Nat.add_le_add
      · exact hpoint x (by simp)
      · apply ih
        intro y hy
        exact hpoint y (by simp [hy])

theorem adjacentCommonSuccessorRow_le_n_mul_fullRow
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int)
    (F : Fin n -> Bool) (hF : F ∈ tasepFrontConfigSlice n k) :
    (List.ofFn (fun edge =>
      tasepCommonSuccessorPairCount ring F
          (swapFrontConfigAt ring F edge) *
        frontSquaredGap phi F
          (swapFrontConfigAt ring F edge))).sum <=
      n * ((tasepFrontConfigSlice n k).map (fun G =>
        tasepCommonSuccessorPairCount ring F G *
          frontSquaredGap phi F G)).sum := by
  apply movingParticle_sum_ofFn_le_card_mul
  intro edge
  exact movingParticle_term_le_sum_map_of_mem
    (tasepFrontConfigSlice n k)
    (fun G =>
      tasepCommonSuccessorPairCount ring F G *
        frontSquaredGap phi F G)
    (x := swapFrontConfigAt ring F edge)
    (by
      apply (mem_tasepFrontConfigSlice_iff _).mpr
      rw [frontConfigMass_swapFrontConfigAt ring hn]
      exact (mem_tasepFrontConfigSlice_iff F).mp hF)

/-- The complete edge-indexed adjacent subenergy is bounded by `n` times the
literal full `P P*` energy.  This is a conservative provenance bridge; no
target-list injectivity or spectral premise is used. -/
theorem commonSuccessorWeightedAdjacentSquaredEnergy_le_n_mul_full
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    commonSuccessorWeightedAdjacentSquaredEnergy ring k phi <=
      n * fullCommonSuccessorSquaredEnergy ring k phi := by
  unfold commonSuccessorWeightedAdjacentSquaredEnergy
  unfold fullCommonSuccessorSquaredEnergy
  apply movingParticle_sum_map_le_mul_of_mem
  intro F hF
  exact adjacentCommonSuccessorRow_le_n_mul_fullRow
    ring hn k phi F hF

theorem n_mul_adjacentEnergy_le_two_mul_commonSuccessorEnergy
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    n * adjacentCyclicSquaredEnergy ring k phi <=
      2 * commonSuccessorWeightedAdjacentSquaredEnergy ring k phi := by
  unfold adjacentCyclicSquaredEnergy
  unfold commonSuccessorWeightedAdjacentSquaredEnergy
  apply movingParticle_sum_map_scaled_le
  intro F
  apply movingParticle_sum_ofFn_scaled_le
  intro edge
  simpa only [Nat.mul_assoc] using
    (n_mul_adjacentSquaredGap_le_commonSuccessor
      ring hn phi F edge)

/-- Complete distance-two splice.  The constant `18` is the product of the
global moving-particle constant `9` and the frozen common-successor factor
`2`; all scheduler denominators remain cleared. -/
theorem n_mul_distanceTwoEnergy_le_eighteen_mul_commonSuccessorEnergy
    (ring : DirectedRing n) (hn : 2 < n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    n * distanceTwoTranspositionSquaredEnergy ring k phi <=
      18 * commonSuccessorWeightedAdjacentSquaredEnergy ring k phi := by
  have hmove :=
    distanceTwoTranspositionSquaredEnergy_le_nine_mul_adjacent
      ring hn k phi
  have hcommon :=
    n_mul_adjacentEnergy_le_two_mul_commonSuccessorEnergy
      ring (by omega) k phi
  calc
    n * distanceTwoTranspositionSquaredEnergy ring k phi <=
        n * (9 * adjacentCyclicSquaredEnergy ring k phi) :=
      Nat.mul_le_mul_left n hmove
    _ = 9 * (n * adjacentCyclicSquaredEnergy ring k phi) := by
      ac_rfl
    _ <= 9 *
        (2 * commonSuccessorWeightedAdjacentSquaredEnergy ring k phi) :=
      Nat.mul_le_mul_left 9 hcommon
    _ = 18 * commonSuccessorWeightedAdjacentSquaredEnergy ring k phi := by
      omega

/-- Genuine full-kernel splice.  The conservative row inclusion above loses
one factor `n`; the same positive factor occurs on the left of the local
comparison and cancels.  Thus distance-two transposition energy is bounded
directly by eighteen times the literal unnormalized `P P*` energy. -/
theorem distanceTwoEnergy_le_eighteen_mul_fullCommonSuccessorEnergy
    (ring : DirectedRing n) (hn : 2 < n) (k : Nat)
    (phi : (Fin n -> Bool) -> Int) :
    distanceTwoTranspositionSquaredEnergy ring k phi <=
      18 * fullCommonSuccessorSquaredEnergy ring k phi := by
  have hlocal :=
    n_mul_distanceTwoEnergy_le_eighteen_mul_commonSuccessorEnergy
      ring hn k phi
  have hfull :=
    commonSuccessorWeightedAdjacentSquaredEnergy_le_n_mul_full
      ring (by omega) k phi
  have hscaled :
      n * distanceTwoTranspositionSquaredEnergy ring k phi <=
        n * (18 * fullCommonSuccessorSquaredEnergy ring k phi) := by
    calc
      n * distanceTwoTranspositionSquaredEnergy ring k phi <=
          18 * commonSuccessorWeightedAdjacentSquaredEnergy ring k phi :=
        hlocal
      _ <= 18 *
          (n * fullCommonSuccessorSquaredEnergy ring k phi) :=
        Nat.mul_le_mul_left 18 hfull
      _ = n * (18 * fullCommonSuccessorSquaredEnergy ring k phi) := by
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled (by omega)

/-- All three legs of the distance-two canonical path have the exact weighted
common-successor control required by the comparison argument. -/
theorem distanceTwoPath_commonSuccessor_controls
    (ring : DirectedRing n) (hn : 2 < n)
    (phi : (Fin n -> Bool) -> Int)
    (F : Fin n -> Bool) (x : Fin n) :
    n * frontSquaredGap phi F (distanceTwoPathOne ring F x) <=
        2 * tasepCommonSuccessorPairCount ring F
            (distanceTwoPathOne ring F x) *
          frontSquaredGap phi F (distanceTwoPathOne ring F x) /\
      n * frontSquaredGap phi
          (distanceTwoPathOne ring F x) (distanceTwoPathTwo ring F x) <=
        2 * tasepCommonSuccessorPairCount ring
            (distanceTwoPathOne ring F x) (distanceTwoPathTwo ring F x) *
          frontSquaredGap phi
            (distanceTwoPathOne ring F x) (distanceTwoPathTwo ring F x) /\
      n * frontSquaredGap phi
          (distanceTwoPathTwo ring F x) (distanceTwoPathThree ring F x) <=
        2 * tasepCommonSuccessorPairCount ring
            (distanceTwoPathTwo ring F x) (distanceTwoPathThree ring F x) *
          frontSquaredGap phi
            (distanceTwoPathTwo ring F x) (distanceTwoPathThree ring F x) := by
  have hn' : 1 < n := by omega
  constructor
  · exact n_mul_adjacentSquaredGap_le_commonSuccessor
      ring hn' phi F x
  · constructor
    · exact n_mul_adjacentSquaredGap_le_commonSuccessor
        ring hn' phi (distanceTwoPathOne ring F x)
          (ring.rightNeighbor x)
    · exact n_mul_adjacentSquaredGap_le_commonSuccessor
        ring hn' phi (distanceTwoPathTwo ring F x) x

/-!
The proved constant-three estimate is pointwise.  Summing it over the
fixed-mass list is now legitimate: `tasepFrontConfigSlice_sum_swap` and
`tasepFrontConfigSlice_sum_distanceTwoPathTwo` close the required source
reindexings for all three legs.  The still-open global step is the genuinely
arbitrary-distance construction: its forward/backward word must be proved to
realize the endpoint transposition and its use of each cyclic edge must be
counted uniformly.  That combinatorial theorem, not a mixing premise, is the
remaining bridge from this distance-two comparison to a full fixed-slice
variance estimate.
-/

end PPartialSealSweepTasepMovingParticleComparisonSol
end PPLLCompleteMultiLeaderCleanup

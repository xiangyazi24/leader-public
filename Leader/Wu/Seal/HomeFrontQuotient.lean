import Leader.Wu.Seal.CoalescenceBarrier

/-!
# The exact home/front quotient of the seal sweep

The four control states of the R82 seal overlay have a second exact reading.
A site is a `home` when its output-leader bit is set.  It carries a `front`
when its home bit agrees with its closed bit.  Thus the four macro states are

* `A = (home, front)`,
* `B = (home, no front)`,
* `C = (no home, no front)`, and
* `D = (no home, front)`.

This file proves that this is an exact quotient, not an approximation.  Before
a collision, each nontrivial transition moves one front clockwise from a
`10` edge to `01`.  The two collision rules are exactly the cases in which a
front selects an occupied home.  On the balanced positive domain the number
of fronts equals the number of homes, hence equals the output-leader count.

The quotient exposes the remaining stochastic core as a totally asymmetric
front process with fixed home traps between collisions.  A final family shows
why the usual squared-gap potential for unrestricted coalescing walkers does
not immediately solve that process: on the reachable word
`B C A D C ... C`, its complete one-step scheduler drift is `6 - 2*n`.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepHomeFrontQuotientSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLStaticDoubleCoverNoGo
open PPartialDynamicSweepLockSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepMixedNormalizerSol
open PPartialSealSweepIidDriftObstructionSol
open PPartialSealSweepIidCoalescenceBarrierSol
open PPartialSealSweepConcurrencyNoGoSol
open PPartialSealSweepConcurrentCounterfamilySol
open PPLLNoCheckBirthConditionTwoGeometry
open SealSweepConcurrentCycleSol
open SealSweepConcurrentCycleSol.SealMacroState

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Site quotient and its exact rule table -/

/-- A home bit and a front-occupancy bit. -/
abbrev SealSweepHomeFrontSite := Bool × Bool

/-- The fixed home is the physical output-leader bit. -/
def sealSweepHomeBit (u : SealSweepState psi kappa tau) : Bool :=
  sweepLockLeader u

/-- `A` and `D` carry fronts; `B` and `C` do not. -/
def sealSweepFrontBit (u : SealSweepState psi kappa tau) : Bool :=
  if sweepLockLeader u then u.2 else !u.2

/-- Exact site projection from the carrier to `(home, front)`. -/
def sealSweepHomeFrontSite
    (u : SealSweepState psi kappa tau) : SealSweepHomeFrontSite :=
  (sealSweepHomeBit u, sealSweepFrontBit u)

/-- The five R82 cases written solely on `(home, front)` bits. -/
def sealSweepHomeFrontPair
    (l r : SealSweepHomeFrontSite) :
    SealSweepHomeFrontSite × SealSweepHomeFrontSite :=
  match l, r with
  | (true, true), (true, true) => ((true, true), (false, false))
  | (true, true), (false, false) => ((true, false), (false, true))
  | (false, true), (false, false) => ((false, false), (false, true))
  | (false, true), (true, true) => ((false, false), (false, true))
  | (false, true), (true, false) => ((false, false), (true, true))
  | l, r => (l, r)

/-- A noncollision clockwise front move.  The sole empty-site blocker is an
occupied home immediately followed by an empty home. -/
def sealSweepFrontMovePair
    (l r : SealSweepHomeFrontSite) : Bool :=
  l.2 && !r.2 && (!l.1 || !r.1)

/-- Every enabled noncollision front action is exactly `10 → 01`. -/
theorem sealSweepHomeFrontPair_eq_move_of_frontMove
    (l r : SealSweepHomeFrontSite)
    (hmove : sealSweepFrontMovePair l r = true) :
    sealSweepHomeFrontPair l r =
      ((l.1, false), (r.1, true)) := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [sealSweepFrontMovePair, sealSweepHomeFrontPair] at hmove ⊢

/-- The carrier transition projects exactly to the home/front rule table. -/
theorem sealSweepHomeFrontSite_pair_exact
    (l r : SealSweepState psi kappa tau) :
    (sealSweepHomeFrontSite (P_partialSealSweep l r).1,
      sealSweepHomeFrontSite (P_partialSealSweep l r).2) =
    sealSweepHomeFrontPair
      (sealSweepHomeFrontSite l) (sealSweepHomeFrontSite r) := by
  cases hl : sweepLockLeader l <;>
    cases hlc : l.2 <;>
    cases hr : sweepLockLeader r <;>
    cases hrc : r.2
  all_goals
    simp only [sweepLockLeader] at hl hr
    simp [sealSweepHomeFrontSite, sealSweepHomeBit, sealSweepFrontBit,
      sealSweepHomeFrontPair, P_partialSealSweep, hl, hlc, hr, hrc,
      sweepLockLeader]

/-- A configuration projected sitewise to homes and fronts. -/
def sealSweepHomeFrontConfig
    (C : SealSweepConfig n psi kappa tau) :
    Fin n → SealSweepHomeFrontSite :=
  fun i => sealSweepHomeFrontSite (C i)

/-- Projection commutes with every exact local scheduler step. -/
theorem sealSweepHomeFrontConfig_localStep_exact
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) :
    sealSweepHomeFrontConfig
        (localStep ring P_partialSealSweep C e) =
      localStep ring sealSweepHomeFrontPair
        (sealSweepHomeFrontConfig C) e := by
  funext i
  let j := ring.rightNeighbor e
  by_cases hie : i = e
  · subst i
    have hpair := sealSweepHomeFrontSite_pair_exact
      (C e) (C (ring.rightNeighbor e))
    simpa [sealSweepHomeFrontConfig, localStep] using
      congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      have hpair := sealSweepHomeFrontSite_pair_exact
        (C e) (C (ring.rightNeighbor e))
      simpa [sealSweepHomeFrontConfig, localStep, j, hie] using
        congrArg Prod.snd hpair
    · simp [sealSweepHomeFrontConfig, localStep, j, hie, hij]

/-! ## Collision is exactly a front selecting an occupied home -/

/-- The home/front form of a collision edge. -/
def sealSweepFrontHitsHomePair
    (l r : SealSweepHomeFrontSite) : Bool :=
  l.2 && r.1 && r.2

/-- Away from a front move or a front-hit-home collision, the quotient
stutters exactly. -/
theorem sealSweepHomeFrontPair_eq_self_of_no_move_no_hit
    (l r : SealSweepHomeFrontSite)
    (hmove : sealSweepFrontMovePair l r = false)
    (hhit : sealSweepFrontHitsHomePair l r = false) :
    sealSweepHomeFrontPair l r = (l, r) := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [sealSweepFrontMovePair, sealSweepFrontHitsHomePair,
      sealSweepHomeFrontPair] at hmove hhit ⊢

private def homeFrontPairFrontCount
    (q : SealSweepHomeFrontSite × SealSweepHomeFrontSite) : Nat :=
  (if q.1.2 then 1 else 0) + (if q.2.2 then 1 else 0)

/-- The two-site front count drops by exactly one precisely on a front hit. -/
theorem sealSweepHomeFrontPair_frontCount_exact
    (l r : SealSweepHomeFrontSite) :
    homeFrontPairFrontCount (sealSweepHomeFrontPair l r) +
        (if sealSweepFrontHitsHomePair l r then 1 else 0) =
      homeFrontPairFrontCount (l, r) := by
  rcases l with ⟨lh, lf⟩
  rcases r with ⟨rh, rf⟩
  cases lh <;> cases lf <;> cases rh <;> cases rf <;>
    simp [homeFrontPairFrontCount, sealSweepFrontHitsHomePair,
      sealSweepHomeFrontPair]

theorem sealSweepKillPair_eq_frontHitsHomePair
    (l r : SealSweepState psi kappa tau) :
    sealSweepKillPair l r =
      sealSweepFrontHitsHomePair
        (sealSweepHomeFrontSite l) (sealSweepHomeFrontSite r) := by
  cases hl : sweepLockLeader l <;>
    cases hlc : l.2 <;>
    cases hr : sweepLockLeader r <;>
    cases hrc : r.2
  all_goals
    simp [sealSweepKillPair, sealSweepFrontHitsHomePair,
      sealSweepHomeFrontSite, sealSweepHomeBit, sealSweepFrontBit,
      hl, hlc, hr, hrc]

/-- The edge form of the exact front-hit-home characterization. -/
theorem sealSweepKillEdge_eq_frontHitsHome
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) :
    sealSweepKillEdge ring C e =
      sealSweepFrontHitsHomePair
        (sealSweepHomeFrontConfig C e)
        (sealSweepHomeFrontConfig C (ring.rightNeighbor e)) := by
  exact sealSweepKillPair_eq_frontHitsHomePair
    (C e) (C (ring.rightNeighbor e))

/-! ## Balanced descendants have one front per surviving home -/

private def homeFrontBoolCount {m : Nat} (bits : Fin m → Bool) : Nat :=
  (List.ofFn (fun i => if bits i then 1 else 0)).sum

/-- Number of front particles in a seal configuration. -/
def sealSweepFrontCount
    (C : SealSweepConfig n psi kappa tau) : Nat :=
  homeFrontBoolCount (fun i => sealSweepFrontBit (C i))

private theorem homeFrontBoolCount_succ {m : Nat}
    (bits : Fin (m + 1) → Bool) :
    homeFrontBoolCount bits =
      (if bits 0 then 1 else 0) +
        homeFrontBoolCount (fun i : Fin m => bits i.succ) := by
  unfold homeFrontBoolCount
  rw [List.ofFn_succ, List.sum_cons]

private theorem homeFrontSum_add {m : Nat} (f g : Fin m → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

private theorem sealSweepOpenLeaderCount_eq_homeFrontCount
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepOpenLeaderCount C =
      homeFrontBoolCount
        (fun i => sweepLockLeader (C i) && !(C i).2) := by
  rfl

private theorem sealSweepOpenFollowerCount_eq_homeFrontCount
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepOpenFollowerCount C =
      homeFrontBoolCount
        (fun i => !sweepLockLeader (C i) && !(C i).2) := by
  rfl

private theorem sealSweepLeaderCount_eq_homeFrontCount
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepLeaderCount C =
      homeFrontBoolCount (fun i => sweepLockLeader (C i)) := by
  rfl

/-- Pointwise, fronts plus open homes equal homes plus open followers. -/
theorem sealSweepFrontCount_accounting
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepFrontCount C + sealSweepOpenLeaderCount C =
      sealSweepLeaderCount C + sealSweepOpenFollowerCount C := by
  rw [sealSweepOpenLeaderCount_eq_homeFrontCount,
    sealSweepOpenFollowerCount_eq_homeFrontCount,
    sealSweepLeaderCount_eq_homeFrontCount]
  unfold sealSweepFrontCount homeFrontBoolCount
  rw [← homeFrontSum_add, ← homeFrontSum_add]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext i
  cases hl : sweepLockLeader (C i) <;> cases hc : (C i).2 <;>
    simp [sealSweepFrontBit, hl, hc]

/-- On the conserved balanced domain, front count is exactly leader count. -/
theorem sealSweepFrontCount_eq_leaderCount_of_balanced
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C) :
    sealSweepFrontCount C = sealSweepLeaderCount C := by
  have haccount := sealSweepFrontCount_accounting C
  change sealSweepOpenLeaderCount C =
    sealSweepOpenFollowerCount C at hbalanced
  omega

/-- Every positive descendant has exactly one front per surviving home. -/
theorem positiveDescendant_frontCount_eq_leaderCount
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hdesc : SealSweepPositiveDescendant ring C) :
    sealSweepFrontCount C = sealSweepLeaderCount C := by
  exact sealSweepFrontCount_eq_leaderCount_of_balanced C
    (positiveDescendant_balanced_hasLeader ring C hdesc).1

/-! ## Exact finite-schedule transport to the quotient -/

/-- Number of fixed homes in a quotient configuration. -/
def homeFrontHomeCount
    (X : Fin n → SealSweepHomeFrontSite) : Nat :=
  homeFrontBoolCount (fun i => (X i).1)

/-- Projection does not merely preserve the number of leaders: homes are the
leader bits definitionally, site by site. -/
theorem homeFrontHomeCount_projection
    (C : SealSweepConfig n psi kappa tau) :
    homeFrontHomeCount (sealSweepHomeFrontConfig C) =
      sealSweepLeaderCount C := by
  rfl

/-- Quotient Boolean target for a drop below the fixed block-source home
count. -/
def homeFrontHomeDropTest
    (X Y : Fin n → SealSweepHomeFrontSite) : Bool :=
  decide (homeFrontHomeCount Y < homeFrontHomeCount X)

theorem homeFrontHomeDropTest_projection
    (C D : SealSweepConfig n psi kappa tau) :
    homeFrontHomeDropTest
        (sealSweepHomeFrontConfig C)
        (sealSweepHomeFrontConfig D) =
      sealSweepLeaderDropTest C D := by
  simp [homeFrontHomeDropTest, sealSweepLeaderDropTest,
    homeFrontHomeCount_projection]

/-- Site projection commutes with an arbitrary finite scheduler word, not
only one local interaction. -/
theorem sealSweepHomeFrontConfig_runLocalSchedule_exact
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (word : DetSchedule n) :
    sealSweepHomeFrontConfig
        (runLocalSchedule ring P_partialSealSweep C word) =
      runLocalSchedule ring sealSweepHomeFrontPair
        (sealSweepHomeFrontConfig C) word := by
  induction word generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [runLocalSchedule]
      rw [ih, sealSweepHomeFrontConfig_localStep_exact]

private theorem homeFront_hitsWithinLocal_projection_aux
    (ring : DirectedRing n)
    (source current : SealSweepConfig n psi kappa tau)
    (word : DetSchedule n) :
    hitsWithinLocal ring P_partialSealSweep
        (sealSweepLeaderDropTest source) current word =
      hitsWithinLocal ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest (sealSweepHomeFrontConfig source))
        (sealSweepHomeFrontConfig current) word := by
  induction word generalizing current with
  | nil =>
      simpa [hitsWithinLocal] using
        homeFrontHomeDropTest_projection source current |>.symm
  | cons e rest ih =>
      simp only [hitsWithinLocal]
      rw [homeFrontHomeDropTest_projection]
      rw [ih]
      rw [sealSweepHomeFrontConfig_localStep_exact]

/-- The entire prefix-hit Boolean is exact in the home/front quotient. -/
theorem homeFront_hitsWithinLocal_projection
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (word : DetSchedule n) :
    hitsWithinLocal ring P_partialSealSweep
        (sealSweepLeaderDropTest C) C word =
      hitsWithinLocal ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest (sealSweepHomeFrontConfig C))
        (sealSweepHomeFrontConfig C) word := by
  exact homeFront_hitsWithinLocal_projection_aux ring C C word

/-- Consequently the favorable-word numerator agrees at every horizon. -/
theorem homeFront_localHitCount_projection
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (horizon : Nat) :
    localHitCount ring P_partialSealSweep
        (sealSweepLeaderDropTest C) C horizon =
      localHitCount ring sealSweepHomeFrontPair
        (homeFrontHomeDropTest (sealSweepHomeFrontConfig C))
        (sealSweepHomeFrontConfig C) horizon := by
  unfold localHitCount
  apply congrArg (fun p => (allSchedules n horizon).countP p)
  funext word
  exact homeFront_hitsWithinLocal_projection ring C word

/-- The exact reachable quotient domain.  Retaining the image condition is
essential: balance alone forgets which home/front words the four-state rule
can actually reach from an all-closed positive source. -/
def SealSweepPositiveHomeFrontState
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) : Prop :=
  ∃ C : SealSweepConfig n psi kappa tau,
    SealSweepPositiveDescendant ring C ∧
      sealSweepHomeFrontConfig C = X

/-- Pure home-trap/TASEP form of the missing finite-window exposure lemma. -/
def SealSweepHomeFrontWindowDropExposure
    (ring : DirectedRing n) (horizon favorable : Nat) : Prop :=
  ∀ X : Fin n → SealSweepHomeFrontSite,
    SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X →
    2 ≤ homeFrontHomeCount X →
    favorable ≤ localHitCount ring sealSweepHomeFrontPair
      (homeFrontHomeDropTest X) X horizon

/-- No carrier-level information remains in the exposure target: the
home-trap statement is equivalent to the original leader-drop statement. -/
theorem homeFrontWindowDropExposure_iff_leaderDropExposure
    (ring : DirectedRing n) (horizon favorable : Nat) :
    SealSweepHomeFrontWindowDropExposure
        (psi := psi) (kappa := kappa) (tau := tau)
        ring horizon favorable ↔
      SealSweepWindowLeaderDropExposure
        (psi := psi) (kappa := kappa) (tau := tau)
        ring horizon favorable := by
  constructor
  · intro hquot C hdesc hleaders
    have hhomes : 2 ≤ homeFrontHomeCount
        (sealSweepHomeFrontConfig C) := by
      rw [homeFrontHomeCount_projection]
      exact hleaders
    have hbound := hquot (sealSweepHomeFrontConfig C)
      ⟨C, hdesc, rfl⟩ hhomes
    rw [← homeFront_localHitCount_projection] at hbound
    exact hbound
  · intro hphysical X hX hhomes
    obtain ⟨C, hdesc, rfl⟩ := hX
    have hleaders : 2 ≤ sealSweepLeaderCount C := by
      rw [← homeFrontHomeCount_projection]
      exact hhomes
    have hbound := hphysical C hdesc hleaders
    rw [homeFront_localHitCount_projection] at hbound
    exact hbound

/-- A concrete polynomial block length for the remaining Markov lemma. -/
def homeFrontCubicHorizon (m : Nat) : Nat := m ^ 3

/-- Half of all iid words in the cubic block.  Establishing this lower bound
would give a state-uniform success probability at least one half. -/
def homeFrontCubicHalfFavorable (m : Nat) : Nat :=
  m ^ homeFrontCubicHorizon m / 2

theorem homeFrontCubicHalfFavorable_eq_scheduleCount_half (m : Nat) :
    homeFrontCubicHalfFavorable m =
      (allSchedules m (homeFrontCubicHorizon m)).length / 2 := by
  rw [allSchedules_length]
  rfl

/-- The first exact probabilistic target after quotienting: by the equivalence
above, this one home-trap statement is precisely a cubic-window, half-mass
leader-drop block for every positive descendant with at least two leaders. -/
def SealSweepHomeFrontCubicBlockExposure
    (ring : DirectedRing n) : Prop :=
  SealSweepHomeFrontWindowDropExposure
    (psi := psi) (kappa := kappa) (tau := tau) ring
    (homeFrontCubicHorizon n) (homeFrontCubicHalfFavorable n)

theorem homeFrontCubicBlockExposure_iff
    (ring : DirectedRing n) :
    SealSweepHomeFrontCubicBlockExposure
        (psi := psi) (kappa := kappa) (tau := tau) ring ↔
      SealSweepWindowLeaderDropExposure
        (psi := psi) (kappa := kappa) (tau := tau) ring
        (homeFrontCubicHorizon n) (homeFrontCubicHalfFavorable n) := by
  exact homeFrontWindowDropExposure_iff_leaderDropExposure _ _ _

/-! ## The natural two-front squared-gap drift can point the wrong way -/

/-- A configuration with homes at `a,b` and fronts at `x,y`. -/
def homeFrontTwoAt {m : Nat}
    (a b x y : Fin m) : Fin m → SealSweepHomeFrontSite :=
  fun i =>
    (decide (i = a ∨ i = b), decide (i = x ∨ i = y))

private theorem homeFrontTwoAt_front_swap {m : Nat}
    (a b x y : Fin m) :
    homeFrontTwoAt a b x y = homeFrontTwoAt a b y x := by
  funext i
  simp [homeFrontTwoAt, or_comm]

private theorem homeFrontTwoAt_frontMove
    (ring : DirectedRing n)
    (a b x y z : Fin n)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hneighbor : ring.rightNeighbor x = z)
    (hmove : sealSweepFrontMovePair
        (homeFrontTwoAt a b x y x)
        (homeFrontTwoAt a b x y z) = true) :
    localStep ring sealSweepHomeFrontPair
        (homeFrontTwoAt a b x y) x =
      homeFrontTwoAt a b z y := by
  have hpair := sealSweepHomeFrontPair_eq_move_of_frontMove
    (homeFrontTwoAt a b x y x)
    (homeFrontTwoAt a b x y z) hmove
  funext i
  by_cases hix : i = x
  · subst i
    have hlocal :
        localStep ring sealSweepHomeFrontPair
            (homeFrontTwoAt a b x y) x x =
          (sealSweepHomeFrontPair
            (homeFrontTwoAt a b x y x)
            (homeFrontTwoAt a b x y z)).1 := by
      simp [localStep, hneighbor]
    rw [hlocal, hpair]
    simp [homeFrontTwoAt, hxy, hxz]
  · by_cases hiz : i = z
    · subst i
      have hlocal :
          localStep ring sealSweepHomeFrontPair
              (homeFrontTwoAt a b x y) x z =
            (sealSweepHomeFrontPair
              (homeFrontTwoAt a b x y x)
              (homeFrontTwoAt a b x y z)).2 := by
        simp [localStep, hneighbor, hxz.symm]
      rw [hlocal, hpair]
      simp [homeFrontTwoAt, hxz.symm, hyz.symm]
    · simp [localStep, hneighbor, hix, hiz, homeFrontTwoAt]

/-- Rotation-invariant directed square energy.  On a two-front state this is
the sum of the squares of its two cyclic gaps. -/
def homeFrontDirectedSquareEnergy
    (ring : DirectedRing n)
    (X : Fin n → SealSweepHomeFrontSite) : Nat :=
  (List.ofFn (fun i : Fin n =>
    (List.ofFn (fun j : Fin n =>
      if (X i).2 = true ∧ (X j).2 = true
      then cwDist ring i j ^ 2 else 0)).sum)).sum

private theorem listSum_const_zero (m : Nat) :
    (List.ofFn (fun _i : Fin m => 0)).sum = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons]
      simpa using ih

private theorem listSum_support_single {m : Nat}
    (x : Fin m) (f : Fin m → Nat) :
    (List.ofFn (fun i => if i = x then f i else 0)).sum = f x := by
  induction m with
  | zero => exact Fin.elim0 x
  | succ m ih =>
      cases x using Fin.cases with
      | zero =>
          rw [List.ofFn_succ, List.sum_cons]
          have htail :
              (fun i : Fin m =>
                if i.succ = (0 : Fin (m + 1)) then f i.succ else 0) =
              (fun _i : Fin m => 0) := by
            funext i
            simp [Fin.succ_ne_zero]
          rw [htail]
          rw [listSum_const_zero]
          simp
      | succ x =>
          rw [List.ofFn_succ, List.sum_cons]
          have hzero : (0 : Fin (m + 1)) ≠ x.succ := by
            intro h
            exact Fin.succ_ne_zero x h.symm
          simp only [Fin.zero_eta, hzero, if_false]
          simpa using ih x (fun i : Fin m => f i.succ)

private theorem listSum_support_two {m : Nat}
    (x y : Fin m) (hxy : x ≠ y) (f : Fin m → Nat) :
    (List.ofFn (fun i => if i = x ∨ i = y then f i else 0)).sum =
      f x + f y := by
  have hpoint :
      (fun i => if i = x ∨ i = y then f i else 0) =
        (fun i =>
          (if i = x then f i else 0) +
            (if i = y then f i else 0)) := by
    funext i
    by_cases hix : i = x
    · subst i
      simp [hxy]
    · by_cases hiy : i = y <;> simp [hix, hiy, hxy, hxy.symm]
  rw [hpoint, homeFrontSum_add,
    listSum_support_single x f, listSum_support_single y f]

private theorem listDoubleSum_support_two {m : Nat}
    (x y : Fin m) (hxy : x ≠ y) (f : Fin m → Fin m → Nat) :
    (List.ofFn (fun i =>
      (List.ofFn (fun j =>
        if (i = x ∨ i = y) ∧ (j = x ∨ j = y)
        then f i j else 0)).sum)).sum =
      (f x x + f x y) + (f y x + f y y) := by
  have hinner : ∀ i : Fin m,
      (List.ofFn (fun j =>
        if (i = x ∨ i = y) ∧ (j = x ∨ j = y)
        then f i j else 0)).sum =
      if i = x ∨ i = y then f i x + f i y else 0 := by
    intro i
    by_cases hi : i = x ∨ i = y
    · simp only [hi, true_and, if_true]
      exact listSum_support_two x y hxy (f i)
    · have hzero :
          (fun j : Fin m =>
            if (i = x ∨ i = y) ∧ (j = x ∨ j = y)
            then f i j else 0) = (fun _j : Fin m => 0) := by
          funext j
          simp [hi]
      rw [hzero]
      rw [listSum_const_zero]
      simp [hi]
  have hfun :
      (fun i : Fin m =>
        (List.ofFn (fun j =>
          if (i = x ∨ i = y) ∧ (j = x ∨ j = y)
          then f i j else 0)).sum) =
      (fun i => if i = x ∨ i = y
        then f i x + f i y else 0) := by
    funext i
    exact hinner i
  rw [hfun, listSum_support_two x y hxy]

theorem homeFrontDirectedSquareEnergy_twoAt
    (ring : DirectedRing n) (a b x y : Fin n) (hxy : x ≠ y) :
    homeFrontDirectedSquareEnergy ring (homeFrontTwoAt a b x y) =
      cwDist ring x y ^ 2 + cwDist ring y x ^ 2 := by
  classical
  unfold homeFrontDirectedSquareEnergy homeFrontTwoAt
  simp only [decide_eq_true_eq]
  rw [listDoubleSum_support_two x y hxy]
  have hxx : cwDist ring x x = 0 := by
    simp [cwDist, Nat.mod_eq_of_lt x.isLt]
  have hyy : cwDist ring y y = 0 := by
    simp [cwDist, Nat.mod_eq_of_lt y.isLt]
  rw [hxx, hyy]
  omega

/-- All-closed two-home source `A C A C C ... C`. -/
def homeFrontACAC (m : Nat) (hm : 4 ≤ m) :
    Fin m → SealSweepHomeFrontSite :=
  let p0 : Fin m := ⟨0, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  homeFrontTwoAt p0 p2 p0 p2

/-- First intermediate word `B D A C C ... C`. -/
def homeFrontBDAC (m : Nat) (hm : 4 ≤ m) :
    Fin m → SealSweepHomeFrontSite :=
  let p0 : Fin m := ⟨0, by omega⟩
  let p1 : Fin m := ⟨1, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  homeFrontTwoAt p0 p2 p2 p1

/-- Second intermediate word `B D B D C ... C`. -/
def homeFrontBDBD (m : Nat) (hm : 4 ≤ m) :
    Fin m → SealSweepHomeFrontSite :=
  let p0 : Fin m := ⟨0, by omega⟩
  let p1 : Fin m := ⟨1, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  let p3 : Fin m := ⟨3, by omega⟩
  homeFrontTwoAt p0 p2 p3 p1

/-- The scalable reachable quotient word `B C A D C ... C`. -/
def homeFrontBCAD (m : Nat) (hm : 4 ≤ m) :
    Fin m → SealSweepHomeFrontSite :=
  let p0 : Fin m := ⟨0, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  let p3 : Fin m := ⟨3, by omega⟩
  homeFrontTwoAt p0 p2 p2 p3

/-- Three-edge witness `0,2,1` from ACAC to BCAD. -/
def homeFrontBCADWord (m : Nat) (hm : 4 ≤ m) : DetSchedule m :=
  [⟨0, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩]

/-- Its unique nontrivial scheduler choice moves the front at position three
one site clockwise. -/
def homeFrontBCADMoved
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    Fin n → SealSweepHomeFrontSite :=
  let p0 : Fin n := ⟨0, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  homeFrontTwoAt p0 p2 p2 (ring.rightNeighbor p3)

theorem homeFrontBCAD_pointwise
    (m : Nat) (hm : 4 ≤ m) (i : Fin m) :
    homeFrontBCAD m hm i =
      if i.val = 0 then (true, false)
      else if i.val = 2 then (true, true)
      else if i.val = 3 then (false, true)
      else (false, false) := by
  let p0 : Fin m := ⟨0, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  let p3 : Fin m := ⟨3, by omega⟩
  have hi0 : i = p0 ↔ i.val = 0 := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  have hi2 : i = p2 ↔ i.val = 2 := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  have hi3 : i = p3 ↔ i.val = 3 := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  change homeFrontTwoAt p0 p2 p2 p3 i = _
  by_cases h0 : i.val = 0
  · have h02 : i.val ≠ 2 := by omega
    have h03 : i.val ≠ 3 := by omega
    simp [homeFrontTwoAt, hi0, hi2, hi3, h0, h02, h03]
  · by_cases h2 : i.val = 2
    · have h23 : i.val ≠ 3 := by omega
      simp [homeFrontTwoAt, hi0, hi2, hi3, h0, h2, h23]
    · by_cases h3 : i.val = 3 <;>
        simp [homeFrontTwoAt, hi0, hi2, hi3, h0, h2, h3]

private theorem homeFrontLocalStep_eq_self_of_pair_eq
    (ring : DirectedRing n) (X : Fin n → SealSweepHomeFrontSite)
    (e : Fin n)
    (hpair : sealSweepHomeFrontPair (X e)
        (X (ring.rightNeighbor e)) =
      (X e, X (ring.rightNeighbor e))) :
    localStep ring sealSweepHomeFrontPair X e = X := by
  funext i
  by_cases hie : i = e
  · subst i
    simp [localStep, hpair]
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simp [localStep, hie, hpair]
    · simp [localStep, hie, hij, hpair]

private theorem bcad_p0_rightNeighbor_p1
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let p0 : Fin n := ⟨0, by omega⟩
    let p1 : Fin n := ⟨1, by omega⟩
    ring.rightNeighbor p0 = p1 := by
  dsimp only
  apply Fin.ext
  change (0 + 1) % n = 1
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem bcad_p1_rightNeighbor_p2
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let p1 : Fin n := ⟨1, by omega⟩
    let p2 : Fin n := ⟨2, by omega⟩
    ring.rightNeighbor p1 = p2 := by
  dsimp only
  apply Fin.ext
  change (1 + 1) % n = 2
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem bcad_p2_rightNeighbor_p3
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let p2 : Fin n := ⟨2, by omega⟩
    let p3 : Fin n := ⟨3, by omega⟩
    ring.rightNeighbor p2 = p3 := by
  dsimp only
  apply Fin.ext
  change (2 + 1) % n = 3
  rw [Nat.mod_eq_of_lt (by omega)]

theorem homeFrontACAC_step_zero
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let p0 : Fin n := ⟨0, by omega⟩
    localStep ring sealSweepHomeFrontPair
        (homeFrontACAC n hn) p0 =
      homeFrontBDAC n hn := by
  let p0 : Fin n := ⟨0, by omega⟩
  let p1 : Fin n := ⟨1, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  have h01 : p0 ≠ p1 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p1] at hv
    omega
  have h02 : p0 ≠ p2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p2] at hv
    omega
  have h12 : p1 ≠ p2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p1, p2] at hv
    omega
  have hneighbor : ring.rightNeighbor p0 = p1 :=
    bcad_p0_rightNeighbor_p1 ring hn
  have hmove : sealSweepFrontMovePair
      (homeFrontTwoAt p0 p2 p0 p2 p0)
      (homeFrontTwoAt p0 p2 p0 p2 p1) = true := by
    simp [sealSweepFrontMovePair, homeFrontTwoAt,
      h01, h02, h12, h01.symm, h02.symm, h12.symm]
  dsimp only
  change localStep ring sealSweepHomeFrontPair
      (homeFrontTwoAt p0 p2 p0 p2) p0 =
    homeFrontTwoAt p0 p2 p2 p1
  calc
    _ = homeFrontTwoAt p0 p2 p1 p2 :=
      homeFrontTwoAt_frontMove ring p0 p2 p0 p2 p1
        h02 h01 h12.symm hneighbor hmove
    _ = _ := homeFrontTwoAt_front_swap p0 p2 p1 p2

theorem homeFrontBDAC_step_two
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let p2 : Fin n := ⟨2, by omega⟩
    localStep ring sealSweepHomeFrontPair
        (homeFrontBDAC n hn) p2 =
      homeFrontBDBD n hn := by
  let p0 : Fin n := ⟨0, by omega⟩
  let p1 : Fin n := ⟨1, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  have h01 : p0 ≠ p1 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p1] at hv
    omega
  have h02 : p0 ≠ p2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p2] at hv
    omega
  have h03 : p0 ≠ p3 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p3] at hv
    omega
  have h12 : p1 ≠ p2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p1, p2] at hv
    omega
  have h13 : p1 ≠ p3 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p1, p3] at hv
    omega
  have h23 : p2 ≠ p3 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p2, p3] at hv
    omega
  have hneighbor : ring.rightNeighbor p2 = p3 :=
    bcad_p2_rightNeighbor_p3 ring hn
  have hmove : sealSweepFrontMovePair
      (homeFrontTwoAt p0 p2 p2 p1 p2)
      (homeFrontTwoAt p0 p2 p2 p1 p3) = true := by
    simp [sealSweepFrontMovePair, homeFrontTwoAt, h01, h02, h03,
      h12, h13, h23, h01.symm, h02.symm, h03.symm,
      h12.symm, h13.symm, h23.symm]
  dsimp only
  change localStep ring sealSweepHomeFrontPair
      (homeFrontTwoAt p0 p2 p2 p1) p2 =
    homeFrontTwoAt p0 p2 p3 p1
  exact homeFrontTwoAt_frontMove ring p0 p2 p2 p1 p3
    h12.symm h23 h13 hneighbor hmove

theorem homeFrontBDBD_step_one
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let p1 : Fin n := ⟨1, by omega⟩
    localStep ring sealSweepHomeFrontPair
        (homeFrontBDBD n hn) p1 =
      homeFrontBCAD n hn := by
  let p0 : Fin n := ⟨0, by omega⟩
  let p1 : Fin n := ⟨1, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  have h01 : p0 ≠ p1 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p1] at hv
    omega
  have h02 : p0 ≠ p2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p2] at hv
    omega
  have h03 : p0 ≠ p3 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p3] at hv
    omega
  have h12 : p1 ≠ p2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p1, p2] at hv
    omega
  have h13 : p1 ≠ p3 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p1, p3] at hv
    omega
  have h23 : p2 ≠ p3 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p2, p3] at hv
    omega
  have hneighbor : ring.rightNeighbor p1 = p2 :=
    bcad_p1_rightNeighbor_p2 ring hn
  have hmove : sealSweepFrontMovePair
      (homeFrontTwoAt p0 p2 p1 p3 p1)
      (homeFrontTwoAt p0 p2 p1 p3 p2) = true := by
    simp [sealSweepFrontMovePair, homeFrontTwoAt, h01, h02, h03,
      h12, h13, h23, h01.symm, h02.symm, h03.symm,
      h12.symm, h13.symm, h23.symm]
  dsimp only
  change localStep ring sealSweepHomeFrontPair
      (homeFrontTwoAt p0 p2 p3 p1) p1 =
    homeFrontTwoAt p0 p2 p2 p3
  rw [homeFrontTwoAt_front_swap p0 p2 p3 p1]
  exact homeFrontTwoAt_frontMove ring p0 p2 p1 p3 p2
    h13 h12 h23.symm hneighbor hmove

/-- The BCAD family is reached from the two-home all-closed source in exactly
three noncollision quotient moves. -/
theorem homeFront_run_BCADWord
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    runLocalSchedule ring sealSweepHomeFrontPair
        (homeFrontACAC n hn) (homeFrontBCADWord n hn) =
      homeFrontBCAD n hn := by
  simp only [homeFrontBCADWord, runLocalSchedule]
  rw [homeFrontACAC_step_zero ring hn,
    homeFrontBDAC_step_two ring hn,
    homeFrontBDBD_step_one ring hn]

/-! ## Exact physical reachability of the BCAD family -/

/-- A right inverse of the quotient on the four audited exact-carrier
representatives. -/
def sealSweepHomeFrontSection (kappa tau : Nat) :
    SealSweepHomeFrontSite →
      SealSweepState OverlayNoGoPsi kappa tau
  | (true, true) => exactLS kappa tau
  | (true, false) => exactLU kappa tau
  | (false, false) => exactFS kappa tau
  | (false, true) => exactFU kappa tau

theorem sealSweepHomeFrontSite_section
    (kappa tau : Nat) (q : SealSweepHomeFrontSite) :
    sealSweepHomeFrontSite (sealSweepHomeFrontSection kappa tau q) = q := by
  rcases q with ⟨h, f⟩
  cases h <;> cases f <;> rfl

/-- Exact-carrier lift of the ACAC source. -/
def sealSweepPhysicalACAC
    (m : Nat) (hm : 4 ≤ m) (kappa tau : Nat) :
    SealSweepConfig m OverlayNoGoPsi kappa tau :=
  fun i => sealSweepHomeFrontSection kappa tau (homeFrontACAC m hm i)

theorem sealSweepPhysicalACAC_projection
    (m : Nat) (hm : 4 ≤ m) (kappa tau : Nat) :
    sealSweepHomeFrontConfig (sealSweepPhysicalACAC m hm kappa tau) =
      homeFrontACAC m hm := by
  funext i
  exact sealSweepHomeFrontSite_section kappa tau (homeFrontACAC m hm i)

theorem sealSweepPhysicalACAC_allClosed
    (m : Nat) (hm : 4 ≤ m) (kappa tau : Nat) :
    SealSweepAllClosed (sealSweepPhysicalACAC m hm kappa tau) := by
  intro i
  let p0 : Fin m := ⟨0, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  by_cases hi : i = p0 ∨ i = p2 <;>
    simp [sealSweepPhysicalACAC, homeFrontACAC, homeFrontTwoAt,
      sealSweepHomeFrontSection, exactLS, exactFS, p0, p2, hi]

theorem sealSweepPhysicalACAC_positive
    (m : Nat) (hm : 4 ≤ m) (kappa tau : Nat) :
    0 < sealSweepLeaderCount
      (sealSweepPhysicalACAC m hm kappa tau) := by
  apply (sealSweep_hasLeader_iff_leaderCount_pos _).1
  let p0 : Fin m := ⟨0, by omega⟩
  let p2 : Fin m := ⟨2, by omega⟩
  refine ⟨p0, ?_⟩
  simp [sealSweepPhysicalACAC, homeFrontACAC, homeFrontTwoAt,
    sealSweepHomeFrontSection, exactLS, p0, p2]

/-- The physical positive descendant reached by the word `0,2,1`. -/
def sealSweepPhysicalBCAD
    (ring : DirectedRing n) (hn : 4 ≤ n) (kappa tau : Nat) :
    SealSweepConfig n OverlayNoGoPsi kappa tau :=
  runLocalSchedule ring P_partialSealSweep
    (sealSweepPhysicalACAC n hn kappa tau)
    (homeFrontBCADWord n hn)

theorem sealSweepPhysicalBCAD_projection
    (ring : DirectedRing n) (hn : 4 ≤ n) (kappa tau : Nat) :
    sealSweepHomeFrontConfig
        (sealSweepPhysicalBCAD ring hn kappa tau) =
      homeFrontBCAD n hn := by
  unfold sealSweepPhysicalBCAD
  calc
    sealSweepHomeFrontConfig
        (runLocalSchedule ring P_partialSealSweep
          (sealSweepPhysicalACAC n hn kappa tau)
          (homeFrontBCADWord n hn)) =
      runLocalSchedule ring sealSweepHomeFrontPair
        (sealSweepHomeFrontConfig
          (sealSweepPhysicalACAC n hn kappa tau))
        (homeFrontBCADWord n hn) :=
      sealSweepHomeFrontConfig_runLocalSchedule_exact ring _ _
    _ = runLocalSchedule ring sealSweepHomeFrontPair
        (homeFrontACAC n hn) (homeFrontBCADWord n hn) := by
      rw [sealSweepPhysicalACAC_projection]
    _ = homeFrontBCAD n hn := homeFront_run_BCADWord ring hn

/-- Thus the scalable BCAD word used below is the exact quotient of a
positive physical descendant for every `n ≥ 4`. -/
theorem homeFrontBCAD_positiveState
    (ring : DirectedRing n) (hn : 4 ≤ n) (kappa tau : Nat) :
    SealSweepPositiveHomeFrontState
      (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
      ring (homeFrontBCAD n hn) := by
  refine ⟨sealSweepPhysicalBCAD ring hn kappa tau, ?_,
    sealSweepPhysicalBCAD_projection ring hn kappa tau⟩
  unfold sealSweepPhysicalBCAD
  refine ⟨sealSweepPhysicalACAC n hn kappa tau, ⟨?_, ?_⟩, ?_⟩
  · exact sealSweepPhysicalACAC_allClosed n hn kappa tau
  · exact sealSweepPhysicalACAC_positive n hn kappa tau
  · exact P_partialSealSweep_runLocalSchedule_reachable ring _ _

private theorem bcad_neighbor_p3_ne_p2
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let p2 : Fin n := ⟨2, by omega⟩
    let p3 : Fin n := ⟨3, by omega⟩
    ring.rightNeighbor p3 ≠ p2 := by
  dsimp only
  intro h
  have hv := congrArg Fin.val h
  change (3 + 1) % n = 2 at hv
  by_cases hn4 : n = 4
  · subst n
    simp at hv
  · rw [show 3 + 1 = 4 by rfl,
      Nat.mod_eq_of_lt (by omega)] at hv
    omega

/-- Every edge except position three is a quotient stutter on the BCAD
family. -/
theorem homeFrontBCAD_step_eq_self_of_ne_three
    (ring : DirectedRing n) (hn : 4 ≤ n)
    (e : Fin n) (he : e.val ≠ 3) :
    localStep ring sealSweepHomeFrontPair
        (homeFrontBCAD n hn) e =
      homeFrontBCAD n hn := by
  let p2 : Fin n := ⟨2, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  have hep3 : e ≠ p3 := by
    intro h
    exact he (congrArg Fin.val h)
  by_cases hep2 : e = p2
  · subst e
    have hj : ring.rightNeighbor p2 = p3 :=
      bcad_p2_rightNeighbor_p3 ring hn
    apply homeFrontLocalStep_eq_self_of_pair_eq
    rw [hj]
    simp [homeFrontBCAD, homeFrontTwoAt, p2, p3,
      sealSweepHomeFrontPair]
  · have heFront : (homeFrontBCAD n hn e).2 = false := by
      simp [homeFrontBCAD, homeFrontTwoAt, p2, p3, hep2, hep3]
    apply homeFrontLocalStep_eq_self_of_pair_eq
    apply sealSweepHomeFrontPair_eq_self_of_no_move_no_hit
    · simp [sealSweepFrontMovePair, heFront]
    · simp [sealSweepFrontHitsHomePair, heFront]

/-- Position three performs the sole clockwise front move. -/
theorem homeFrontBCAD_step_three
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    let p3 : Fin n := ⟨3, by omega⟩
    localStep ring sealSweepHomeFrontPair
        (homeFrontBCAD n hn) p3 =
      homeFrontBCADMoved ring hn := by
  let p0 : Fin n := ⟨0, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  let j := ring.rightNeighbor p3
  have hp02 : p0 ≠ p2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p2] at hv
    omega
  have hp03 : p0 ≠ p3 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p3] at hv
    omega
  have hp23 : p2 ≠ p3 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p2, p3] at hv
    omega
  have hj3 : j ≠ p3 :=
    rightNeighbor_ne_self_of_one_lt ring (by omega) p3
  have hj2 : j ≠ p2 :=
    bcad_neighbor_p3_ne_p2 ring hn
  have hleft : homeFrontBCAD n hn p3 = (false, true) := by
    simp [homeFrontBCAD, homeFrontTwoAt, p0, p2, p3,
      hp03, hp23, hp23.symm]
  have hrightFront : (homeFrontBCAD n hn j).2 = false := by
    simp [homeFrontBCAD, homeFrontTwoAt, p0, p2, p3,
      hj2, hj3]
  have hpair :
      sealSweepHomeFrontPair (homeFrontBCAD n hn p3)
          (homeFrontBCAD n hn j) =
        ((false, false), ((homeFrontBCAD n hn j).1, true)) := by
    apply sealSweepHomeFrontPair_eq_move_of_frontMove
    simp [sealSweepFrontMovePair, hleft, hrightFront]
  dsimp only
  funext i
  by_cases hip3 : i = p3
  · subst i
    have hp3j : p3 ≠ j := hj3.symm
    have hp3right : p3 ≠ ring.rightNeighbor p3 := by
      simpa [j] using hp3j
    have hlocal :
        localStep ring sealSweepHomeFrontPair
            (homeFrontBCAD n hn) p3 p3 =
          (sealSweepHomeFrontPair (homeFrontBCAD n hn p3)
            (homeFrontBCAD n hn j)).1 := by
      simp [localStep, j, hp3j]
    rw [hlocal]
    rw [hpair]
    simp [homeFrontBCADMoved, homeFrontTwoAt,
      p0, p2, p3, hp23, hp3right]
  · by_cases hij : i = j
    · subst i
      have hp3j : p3 ≠ j := hj3.symm
      have hlocal :
          localStep ring sealSweepHomeFrontPair
              (homeFrontBCAD n hn) p3 j =
              (sealSweepHomeFrontPair (homeFrontBCAD n hn p3)
              (homeFrontBCAD n hn j)).2 := by
        simp [localStep, j, hj3]
      rw [hlocal]
      rw [hpair]
      simp [homeFrontBCADMoved, homeFrontBCAD, homeFrontTwoAt,
        p0, p2, p3, hp3j, hj2, hj3]
      apply Fin.ext
      rfl
    · simp [localStep, j, hip3, hij, homeFrontBCADMoved,
        homeFrontBCAD, homeFrontTwoAt, p0, p2, p3]

theorem homeFrontBCAD_energy
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    homeFrontDirectedSquareEnergy ring (homeFrontBCAD n hn) =
      1 + (n - 1) ^ 2 := by
  let p0 : Fin n := ⟨0, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  have hp23 : p2 ≠ p3 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p2, p3] at hv
    omega
  change homeFrontDirectedSquareEnergy ring
      (homeFrontTwoAt p0 p2 p2 p3) = _
  rw [homeFrontDirectedSquareEnergy_twoAt ring p0 p2 p2 p3 hp23]
  have h23 : cwDist ring p2 p3 = 1 := by
    change (3 + n - 2) % n = 1
    have heq : 3 + n - 2 = n + 1 := by omega
    rw [heq, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h32 : cwDist ring p3 p2 = n - 1 := by
    change (2 + n - 3) % n = n - 1
    have heq : 2 + n - 3 = n - 1 := by omega
    rw [heq, Nat.mod_eq_of_lt (by omega)]
  rw [h23, h32]

theorem homeFrontBCADMoved_energy
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    homeFrontDirectedSquareEnergy ring (homeFrontBCADMoved ring hn) =
      2 ^ 2 + (n - 2) ^ 2 := by
  let p0 : Fin n := ⟨0, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  let j := ring.rightNeighbor p3
  have hj2 : j ≠ p2 := bcad_neighbor_p3_ne_p2 ring hn
  change homeFrontDirectedSquareEnergy ring
      (homeFrontTwoAt p0 p2 p2 j) = _
  rw [homeFrontDirectedSquareEnergy_twoAt ring p0 p2 p2 j hj2.symm]
  have h2j : cwDist ring p2 j = 2 := by
    have hpos : cwPos ring p2 2 = j := by
      apply Fin.ext
      change (2 + 2) % n = (3 + 1) % n
      rfl
    exact (cwPos_bounded_unique ring p2 j 2 (by omega) hpos).symm
  have hj2dist : cwDist ring j p2 = n - 2 := by
    change (2 + n - ((3 + 1) % n)) % n = n - 2
    by_cases hn4 : n = 4
    · subst n
      simp
    · have hfour : 4 < n := by omega
      rw [show 3 + 1 = 4 by rfl, Nat.mod_eq_of_lt hfour]
      have heq : 2 + n - 4 = n - 2 := by omega
      rw [heq, Nat.mod_eq_of_lt (by omega)]
  simp [h2j, hj2dist]

private theorem homeFrontSum_single_change {m : Nat}
    (before after : Fin m → Nat) (victim : Fin m)
    (hother : ∀ i : Fin m, i ≠ victim → after i = before i) :
    (List.ofFn after).sum + before victim =
      (List.ofFn before).sum + after victim := by
  induction m with
  | zero => exact Fin.elim0 victim
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      cases victim using Fin.cases with
      | zero =>
          have htail : (fun i : Fin m => after i.succ) =
              (fun i : Fin m => before i.succ) := by
            funext i
            exact hother i.succ (Fin.succ_ne_zero i)
          rw [htail]
          omega
      | succ victim =>
          have hhead : after 0 = before 0 :=
            hother 0 (fun h => Fin.succ_ne_zero victim h.symm)
          have htail := ih
            (fun i : Fin m => before i.succ)
            (fun i : Fin m => after i.succ) victim
            (fun i hi => hother i.succ
              (fun h => hi (Fin.succ_inj.mp h)))
          rw [hhead]
          omega

private theorem homeFrontSum_const (m c : Nat) :
    (List.ofFn (fun _i : Fin m => c)).sum = m * c := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      omega

/-- Exact negative one-step scheduler drift of the ordinary two-front
squared-gap energy on the reachable-shaped BCAD family. -/
theorem homeFrontBCAD_squareEnergy_step_sum
    (ring : DirectedRing n) (hn : 4 ≤ n) :
    (List.ofFn (fun e : Fin n =>
      homeFrontDirectedSquareEnergy ring
        (localStep ring sealSweepHomeFrontPair
          (homeFrontBCAD n hn) e))).sum + (2 * n - 6) =
      n * homeFrontDirectedSquareEnergy ring (homeFrontBCAD n hn) := by
  let p3 : Fin n := ⟨3, by omega⟩
  let before : Fin n → Nat := fun _e =>
    homeFrontDirectedSquareEnergy ring (homeFrontBCAD n hn)
  let after : Fin n → Nat := fun e =>
    homeFrontDirectedSquareEnergy ring
      (localStep ring sealSweepHomeFrontPair (homeFrontBCAD n hn) e)
  have hchange := homeFrontSum_single_change before after p3 (by
    intro e he
    have heval : e.val ≠ 3 := by
      intro hval
      apply he
      apply Fin.ext
      exact hval
    dsimp [after, before]
    rw [homeFrontBCAD_step_eq_self_of_ne_three ring hn e heval])
  have hbeforeSum : (List.ofFn before).sum =
      n * homeFrontDirectedSquareEnergy ring (homeFrontBCAD n hn) := by
    exact homeFrontSum_const n _
  have hbeforeP : before p3 =
      1 + (n - 1) ^ 2 := by
    exact homeFrontBCAD_energy ring hn
  have hafterP : after p3 =
      2 ^ 2 + (n - 2) ^ 2 := by
    dsimp [after, p3]
    rw [homeFrontBCAD_step_three ring hn]
    exact homeFrontBCADMoved_energy ring hn
  change (List.ofFn after).sum + (2 * n - 6) =
    n * homeFrontDirectedSquareEnergy ring (homeFrontBCAD n hn)
  rw [hbeforeSum] at hchange
  rw [hbeforeP, hafterP] at hchange
  have hgap :
      (2 ^ 2 + (n - 2) ^ 2) + (2 * n - 6) =
        1 + (n - 1) ^ 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hk2 : 4 + k - 2 = k + 2 := by omega
    have hk1 : 4 + k - 1 = k + 3 := by omega
    have hlin : 2 * (4 + k) - 6 = 2 * k + 2 := by omega
    rw [hk2, hk1, hlin]
    simp [Nat.pow_two, Nat.add_mul, Nat.mul_add]
    omega
  omega

/-- Packaged obstruction on the actual positive-descendant quotient domain:
the ordinary two-front square energy has scheduler-average change `6-2*n`
on the physical BCAD family. -/
theorem homeFrontBCAD_positive_wrongSquareDrift
    (ring : DirectedRing n) (hn : 4 ≤ n) (kappa tau : Nat) :
    SealSweepPositiveHomeFrontState
        (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
        ring (homeFrontBCAD n hn) ∧
      (List.ofFn (fun e : Fin n =>
        homeFrontDirectedSquareEnergy ring
          (localStep ring sealSweepHomeFrontPair
            (homeFrontBCAD n hn) e))).sum + (2 * n - 6) =
        n * homeFrontDirectedSquareEnergy ring (homeFrontBCAD n hn) := by
  exact ⟨homeFrontBCAD_positiveState ring hn kappa tau,
    homeFrontBCAD_squareEnergy_step_sum ring hn⟩

end PPartialSealSweepHomeFrontQuotientSol
end PPLLCompleteMultiLeaderCleanup

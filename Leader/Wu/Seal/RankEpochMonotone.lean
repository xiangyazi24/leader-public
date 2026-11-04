import Leader.Wu.Seal.CombinatorialGate

/-!
# Exact rank-epoch audit for the home/front quotient

This file isolates the deterministic content of the proposed zero-state
rank-epoch repair.  The rank is the exact number of home bits.  It proves:

* quotient home count never increases;
* equality of the initial and final rank forces pointwise preservation of the
  complete home support, for one step and for every finite scheduler word;
* `#B = #D` is exactly the accounting identity saying that front mass equals
  home mass;
* the producer available from the existing protocol is not bare balance.  It
  is the exact positive quotient image, together with same home support.  That
  stronger epoch is closed along every same-rank finite run and supplies the
  fixed-front-mass and marked-home inputs of the TASEP bridge.

The scalable all-`C` family records why bare `BalancedBD` plus same support is
not a replacement for the exact image condition.  This is a rank-zero boundary
counterfamily only; no interior nonreachability claim is made.

No uniform scheduler-word or superblock count is asserted.  After these exact
adapters, the remaining stochastic input is still
`FixedFrontMassTasepMarked11EndpointBoundAt` (or a theorem strong enough to
imply it) on every interior fixed-mass slice.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepRankEpochAuditSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepReadySuffixHalfMassSol
open PPartialSealSweepABGateBreakthroughSol
open PPartialSealSweepCombinatorialGateAuditSol
open PPartialSealSweepTasepRotationBridgeSol
open PPartialSealSweepMixedNormalizerSol

private theorem rightNeighbor_leftNeighbor_local
    (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]


set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Finite Boolean-sum helpers -/

private theorem rankEpochSum_ofFn_le
    (f g : Fin n -> Nat) (hfg : forall i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem rankEpochSum_ofFn_lt_of_single_lt
    (f g : Fin n -> Nat) (j : Fin n)
    (hle : forall i, f i <= g i) (hlt : f j < g j) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail := rankEpochSum_ofFn_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := fun h =>
            hj0 (Fin.ext (by simpa using h))
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := Fin.ext (by simp [j']; omega)
        have htail := ih
          (fun i => f i.succ) (fun i => g i.succ) j'
          (fun i => hle i.succ) (hjsucc ▸ hlt)
        have hhead := hle 0
        omega

private theorem rankEpochSum_ofFn_add
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

/-- Transparent copy of the quotient rank. -/
private def rankEpochHomeCount
    (X : Fin n -> SealSweepHomeFrontSite) : Nat :=
  (List.ofFn (fun i : Fin n => if (X i).1 then 1 else 0)).sum

private theorem rankEpochHomeCount_eq
    (X : Fin n -> SealSweepHomeFrontSite) :
    rankEpochHomeCount X = homeFrontHomeCount X := by
  rfl

/-! ## Rank monotonicity and equality rigidity -/

/-- Public wrapper for the unrestricted quotient rank monotonicity theorem. -/
theorem quotientHomeCount_localStep_nonincreasing
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n) :
    homeFrontHomeCount
        (localStep ring sealSweepHomeFrontPair X edge) <=
      homeFrontHomeCount X := by
  exact homeFrontHomeCount_localStep_le ring X edge

/-- Since homes are never created, equality of the one-step rank forces the
entire home support to remain fixed, not merely its cardinality. -/
theorem quotientHomeSupport_localStep_eq_of_sameRank
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n)
    (hrank : homeFrontHomeCount
        (localStep ring sealSweepHomeFrontPair X edge) =
      homeFrontHomeCount X) :
    homeFrontHomeProjection
        (localStep ring sealSweepHomeFrontPair X edge) =
      homeFrontHomeProjection X := by
  funext i
  cases hbefore : (X i).1 with
  | false =>
      cases hafter :
          (localStep ring sealSweepHomeFrontPair X edge i).1 with
      | false =>
          change
            (localStep ring sealSweepHomeFrontPair X edge i).1 =
              (X i).1
          exact hafter.trans hbefore.symm
      | true =>
          have hback := homeFrontLocalStep_home_backward
            ring X edge i hafter
          rw [hbefore] at hback
          contradiction
  | true =>
      cases hafter :
          (localStep ring sealSweepHomeFrontPair X edge i).1 with
      | true =>
          change
            (localStep ring sealSweepHomeFrontPair X edge i).1 =
              (X i).1
          exact hafter.trans hbefore.symm
      | false =>
          have hle : forall j : Fin n,
              (if (localStep ring sealSweepHomeFrontPair X edge j).1
                then 1 else 0) <=
              (if (X j).1 then 1 else 0) := by
            intro j
            cases hjafter :
                (localStep ring sealSweepHomeFrontPair X edge j).1 with
            | false => simp [hjafter]
            | true =>
                have hjbefore := homeFrontLocalStep_home_backward
                  ring X edge j hjafter
                simp [hjafter, hjbefore]
          have hlt :
              (if (localStep ring sealSweepHomeFrontPair X edge i).1
                then 1 else 0) <
              (if (X i).1 then 1 else 0) := by
            simp [hafter, hbefore]
          have hstrict := rankEpochSum_ofFn_lt_of_single_lt
            (fun j : Fin n =>
              if (localStep ring sealSweepHomeFrontPair X edge j).1
                then 1 else 0)
            (fun j : Fin n => if (X j).1 then 1 else 0)
            i hle hlt
          have hstrict' :
              homeFrontHomeCount
                  (localStep ring sealSweepHomeFrontPair X edge) <
                homeFrontHomeCount X := by
            rw [← rankEpochHomeCount_eq,
              ← rankEpochHomeCount_eq]
            exact hstrict
          omega

/-- Equality of the endpoint rank along an arbitrary finite word forces
pointwise home-support preservation throughout the rank epoch. -/
theorem quotientHomeSupport_run_eq_of_sameRank
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (word : DetSchedule n)
    (hrank : homeFrontHomeCount
        (runLocalSchedule ring sealSweepHomeFrontPair X word) =
      homeFrontHomeCount X) :
    homeFrontHomeProjection
        (runLocalSchedule ring sealSweepHomeFrontPair X word) =
      homeFrontHomeProjection X := by
  induction word generalizing X with
  | nil => rfl
  | cons edge rest ih =>
      let Y := localStep ring sealSweepHomeFrontPair X edge
      have htailLe : homeFrontHomeCount
          (runLocalSchedule ring sealSweepHomeFrontPair Y rest) <=
        homeFrontHomeCount Y :=
        homeFrontHomeCount_run_le ring Y rest
      have hstepLe : homeFrontHomeCount Y <= homeFrontHomeCount X :=
        homeFrontHomeCount_localStep_le ring X edge
      have hYrank : homeFrontHomeCount Y = homeFrontHomeCount X := by
        change homeFrontHomeCount
            (runLocalSchedule ring sealSweepHomeFrontPair Y rest) =
          homeFrontHomeCount X at hrank
        omega
      have htailRank : homeFrontHomeCount
          (runLocalSchedule ring sealSweepHomeFrontPair Y rest) =
        homeFrontHomeCount Y := by
        change homeFrontHomeCount
            (runLocalSchedule ring sealSweepHomeFrontPair Y rest) =
          homeFrontHomeCount X at hrank
        omega
      calc
        homeFrontHomeProjection
            (runLocalSchedule ring sealSweepHomeFrontPair X
              (edge :: rest)) =
          homeFrontHomeProjection
            (runLocalSchedule ring sealSweepHomeFrontPair Y rest) := rfl
        _ = homeFrontHomeProjection Y := ih Y htailRank
        _ = homeFrontHomeProjection X :=
          quotientHomeSupport_localStep_eq_of_sameRank
            ring X edge hYrank

/-! ## Literal `B/D` accounting -/

/-- Number of `B = (true,false)` sites. -/
def homeFrontBCount
    (X : Fin n -> SealSweepHomeFrontSite) : Nat :=
  (List.ofFn (fun i : Fin n =>
    if X i = (true, false) then 1 else 0)).sum

/-- Number of `D = (false,true)` sites. -/
def homeFrontDCount
    (X : Fin n -> SealSweepHomeFrontSite) : Nat :=
  (List.ofFn (fun i : Fin n =>
    if X i = (false, true) then 1 else 0)).sum

/-- The literal balance condition. -/
def HomeFrontBalancedBD
    (X : Fin n -> SealSweepHomeFrontSite) : Prop :=
  homeFrontBCount X = homeFrontDCount X

/-- Pointwise four-state accounting: fronts plus `B` sites equal homes plus
`D` sites. -/
theorem homeFront_mass_accounting
    (X : Fin n -> SealSweepHomeFrontSite) :
    frontConfigMass (homeFrontFrontProjection X) + homeFrontBCount X =
      homeFrontHomeCount X + homeFrontDCount X := by
  unfold frontConfigMass homeFrontFrontProjection
  unfold homeFrontBCount homeFrontDCount
  rw [← rankEpochHomeCount_eq]
  unfold rankEpochHomeCount
  rw [← rankEpochSum_ofFn_add, ← rankEpochSum_ofFn_add]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext i
  rcases X i with ⟨home, front⟩
  cases home <;> cases front <;> simp

/-- `#B = #D` is exactly equality of front mass and home mass. -/
theorem homeFrontBalancedBD_iff_frontMass_eq_homeCount
    (X : Fin n -> SealSweepHomeFrontSite) :
    HomeFrontBalancedBD X <->
      frontConfigMass (homeFrontFrontProjection X) =
        homeFrontHomeCount X := by
  have haccount := homeFront_mass_accounting X
  unfold HomeFrontBalancedBD
  omega

/-! ## The actual rank epoch produced by the protocol -/

/-- Pointwise equality with the base home support. -/
def SameHomeSupport
    (base X : Fin n -> SealSweepHomeFrontSite) : Prop :=
  homeFrontHomeProjection X = homeFrontHomeProjection base

theorem sameHomeSupport_homeCount_eq
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hsupport : SameHomeSupport base X) :
    homeFrontHomeCount X = homeFrontHomeCount base := by
  change frontConfigMass (homeFrontHomeProjection X) =
    frontConfigMass (homeFrontHomeProjection base)
  rw [hsupport]

/-- Every exact positive quotient image satisfies the proposed `B/D`
balance, because its physical witness has equal front and leader counts. -/
theorem positiveHomeFront_balancedBD
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X) :
    HomeFrontBalancedBD X := by
  apply (homeFrontBalancedBD_iff_frontMass_eq_homeCount X).2
  obtain ⟨C, hdesc, rfl⟩ := hX
  change sealSweepFrontCount C =
    PPartialSealSweepPositiveLandingSol.sealSweepLeaderCount C
  exact positiveDescendant_frontCount_eq_leaderCount ring C hdesc

/-- The protocol-produced epoch retains the exact positive image condition;
bare `B/D` balance is only one consequence of that condition. -/
def ReachableHomeRankEpoch
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite) : Prop :=
  SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X /\
    SameHomeSupport base X

theorem reachableHomeRankEpoch_self
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (hbase : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring base) :
    ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base base := by
  exact ⟨hbase, rfl⟩

/-- The current exact-image entry produces the proposed bare epoch facts. -/
theorem positiveHomeFront_entry_balanced_sameSupport
    (ring : DirectedRing n)
    (base : Fin n -> SealSweepHomeFrontSite)
    (hbase : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring base) :
    HomeFrontBalancedBD base /\ SameHomeSupport base base := by
  exact ⟨positiveHomeFront_balancedBD ring base hbase, rfl⟩

/-- One same-rank quotient step stays in the actual rank epoch. -/
theorem reachableHomeRankEpoch_localStep_of_sameRank
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X)
    (edge : Fin n)
    (hrank : homeFrontHomeCount
        (localStep ring sealSweepHomeFrontPair X edge) =
      homeFrontHomeCount X) :
    ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base
      (localStep ring sealSweepHomeFrontPair X edge) := by
  constructor
  · exact positiveHomeFrontState_localStep ring X hX.1 edge
  · exact (quotientHomeSupport_localStep_eq_of_sameRank
      ring X edge hrank).trans hX.2

/-- Every same-rank finite failure block stays in the actual rank epoch. -/
theorem reachableHomeRankEpoch_run_of_sameRank
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X)
    (word : DetSchedule n)
    (hrank : homeFrontHomeCount
        (runLocalSchedule ring sealSweepHomeFrontPair X word) =
      homeFrontHomeCount X) :
    ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base
      (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
  constructor
  · exact positiveHomeFrontState_run ring X hX.1 word
  · exact (quotientHomeSupport_run_eq_of_sameRank
      ring X word hrank).trans hX.2

/-- Therefore every same-rank failure block from the actual entry preserves
both `BalancedBD` and the pointwise base support. -/
theorem reachableHomeRankEpoch_run_balanced_sameSupport
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X)
    (word : DetSchedule n)
    (hrank : homeFrontHomeCount
        (runLocalSchedule ring sealSweepHomeFrontPair X word) =
      homeFrontHomeCount X) :
    HomeFrontBalancedBD
        (runLocalSchedule ring sealSweepHomeFrontPair X word) /\
      SameHomeSupport base
        (runLocalSchedule ring sealSweepHomeFrontPair X word) := by
  have hrun := reachableHomeRankEpoch_run_of_sameRank
    ring base X hX word hrank
  exact ⟨positiveHomeFront_balancedBD ring _ hrun.1, hrun.2⟩

/-- Exact positive images always contain a responder home for some directed
edge.  This is the marked-home input consumed by the existing TASEP bridge. -/
theorem positiveHomeFront_exists_responderHome
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (hX : SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring X) :
    exists edge : Fin n,
      (X (ring.rightNeighbor edge)).1 = true := by
  obtain ⟨C, hdesc, rfl⟩ := hX
  obtain ⟨i, hi⟩ :=
    (positiveDescendant_balanced_hasLeader ring C hdesc).2
  refine ⟨ring.leftNeighbor i, ?_⟩
  change PPartialDynamicSweepLockSol.sweepLockLeader
    (C (ring.rightNeighbor (ring.leftNeighbor i))) = true
  rw [rightNeighbor_leftNeighbor_local ring i]
  exact hi

/-- These are all deterministic producer facts currently available from an
arbitrary state of the actual epoch.  In particular this theorem does not
manufacture the missing uniform endpoint count. -/
theorem reachableHomeRankEpoch_producer
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X) :
    SealSweepPositiveHomeFrontState
        (psi := psi) (kappa := kappa) (tau := tau) ring X /\
      HomeFrontBalancedBD X /\
      SameHomeSupport base X /\
      homeFrontHomeCount X = homeFrontHomeCount base /\
      frontConfigMass (homeFrontFrontProjection X) =
        homeFrontHomeCount base /\
      exists edge : Fin n,
        (X (ring.rightNeighbor edge)).1 = true := by
  have hbalance := positiveHomeFront_balancedBD ring X hX.1
  have hcount := sameHomeSupport_homeCount_eq base X hX.2
  have hmass : frontConfigMass (homeFrontFrontProjection X) =
      homeFrontHomeCount X :=
    (homeFrontBalancedBD_iff_frontMass_eq_homeCount X).1 hbalance
  exact ⟨hX.1, hbalance, hX.2, hcount, hmass.trans hcount,
    positiveHomeFront_exists_responderHome ring X hX.1⟩

/-- Concrete adapter to the exact fixed-mass TASEP consumer.  The stochastic
fixed-slice bound remains an explicit premise, as it must. -/
theorem reachableHomeRankEpoch_to_readyOrABHitGate
    (ring : DirectedRing n)
    (base X : Fin n -> SealSweepHomeFrontSite)
    (hX : ReachableHomeRankEpoch
      (psi := psi) (kappa := kappa) (tau := tau) ring base X)
    (horizon : Nat)
    (hmixing : FixedFrontMassTasepMarked11EndpointBoundAt ring
      (homeFrontHomeCount base) horizon) :
    HomeFrontInverseSquareReadyOrABHitGate ring X horizon := by
  obtain ⟨_hpositive, _hbalanced, _hsupport, _hcount,
    hmass, edge, hhome⟩ := reachableHomeRankEpoch_producer
      ring base X hX
  exact fixedFrontMassTasepMarked11EndpointBoundAt_to_readyOrABHitGate
    ring (homeFrontHomeCount base) horizon hmixing X edge hmass hhome

/-! ## Bare balance is not the reachable domain -/

/-- The scalable all-`C` word. -/
def rankEpochAllC (n : Nat) : Fin n -> SealSweepHomeFrontSite :=
  fun _ => (false, false)

theorem rankEpochAllC_balancedBD (n : Nat) :
    HomeFrontBalancedBD (rankEpochAllC n) := by
  simp [HomeFrontBalancedBD, homeFrontBCount,
    homeFrontDCount, rankEpochAllC]

theorem rankEpochAllC_sameHomeSupport (n : Nat) :
    SameHomeSupport (rankEpochAllC n) (rankEpochAllC n) := by
  rfl

/-- No all-`C` word lies in the exact positive quotient image, since every
physical positive descendant retains at least one leader/home. -/
theorem rankEpochAllC_not_positiveHomeFront
    (ring : DirectedRing n) :
    ¬ (SealSweepPositiveHomeFrontState
      (psi := psi) (kappa := kappa) (tau := tau) ring
      (rankEpochAllC n)) := by
  rintro ⟨C, hdesc, hprojection⟩
  obtain ⟨i, hi⟩ :=
    (positiveDescendant_balanced_hasLeader ring C hdesc).2
  have hsite := congrFun hprojection i
  have hhome := congrArg Prod.fst hsite
  change PPartialDynamicSweepLockSol.sweepLockLeader (C i) = false at hhome
  rw [hi] at hhome
  contradiction

/-- A scalable rank-zero witness that bare balance plus same support is
strictly weaker than the protocol's exact-image epoch. -/
theorem rankEpochAllC_bareEpoch_not_reachable
    (ring : DirectedRing n) :
    HomeFrontBalancedBD (rankEpochAllC n) /\
      SameHomeSupport (rankEpochAllC n) (rankEpochAllC n) /\
      ¬ (SealSweepPositiveHomeFrontState
        (psi := psi) (kappa := kappa) (tau := tau) ring
        (rankEpochAllC n)) := by
  exact ⟨rankEpochAllC_balancedBD n,
    rankEpochAllC_sameHomeSupport n,
    rankEpochAllC_not_positiveHomeFront ring⟩

#print axioms quotientHomeCount_localStep_nonincreasing
#print axioms quotientHomeSupport_localStep_eq_of_sameRank
#print axioms quotientHomeSupport_run_eq_of_sameRank
#print axioms homeFrontBalancedBD_iff_frontMass_eq_homeCount
#print axioms reachableHomeRankEpoch_run_of_sameRank
#print axioms reachableHomeRankEpoch_run_balanced_sameSupport
#print axioms reachableHomeRankEpoch_producer
#print axioms reachableHomeRankEpoch_to_readyOrABHitGate
#print axioms rankEpochAllC_bareEpoch_not_reachable

end PPartialSealSweepRankEpochAuditSol
end PPLLCompleteMultiLeaderCleanup

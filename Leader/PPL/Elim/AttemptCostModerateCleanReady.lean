import Leader.PPL.Elim.AttemptCostModerateStep

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# LD(736): moderate CR-stage rows

Truth audit: rank uniqueness is false, even on the PB/follower-interior
domain relevant to `crRankStep_proved`.

The overlap is structural: every `.sweep p` witness is also a `.drain p`
witness, because the sweep predicate is the drain predicate plus
`ZeroSignalThrough A C p`.  Their ranks differ whenever the sweep mode is
valid.

A concrete PB counterexample is the three-site directed ring
`0 -> 1 -> 2 -> 0`, with a sector from 0 to 2 of gap 2 and current cells
`[(true,0,false,false), (false,1,false,false), (true,0,false,false)]`.
There is no live bullet, so PB's peaceful-live-bullet clause is vacuous, and
the strict interior is follower-only.  Both `drain 1` and `sweep 1` hold.
Their ranks are respectively `3*2-1 = 5` and `2*2-1-1 = 2`.

Therefore the weak `Classical.choose` used by the private kernel cannot be
made strict merely by comparing it with the strict witness from
`crRankStep_proved ... .2`.  The kernel choice must be redefined to choose
from the strict existential on the required edge.  Until that upstream
definition is changed, the smallest exact residual remains
`ModerateCRMirrorRequiredStrict`.

This file proves the source-level non-uniqueness audit, keeps that one
single-interaction residual explicit, and fixes the two target-CR done-child
potential comparisons by unfolding `attemptNodePotential` and using an
explicit equality for the `.dummyWait _ .ready` child.
-/

/-! ## Mirrors of the private CR helpers -/

private theorem moderateCR_notEndpointB
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.B D := by
  intro h
  exact hgood.2.1 (endpointB_deleted_tagged F D h)

noncomputable def moderateCRInitModeMirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n)
    (hPB : PPL.Elim.PB ring D)
    (halive : ¬ EndpointDeleted A D)
    (hclean : ¬ CleanReady A D) : CRMode :=
  Classical.choose
    (crRankInit ring A D hPB
      (by
        intro hdone
        rcases hdone with hdel | hready
        · exact halive hdel
        · exact hclean hready))

theorem moderateCRInitModeMirror_spec
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n)
    (hPB : PPL.Elim.PB ring D)
    (halive : ¬ EndpointDeleted A D)
    (hclean : ¬ CleanReady A D) :
    And
      (CRModeHolds A D
        (moderateCRInitModeMirror ring A D hPB halive hclean))
      (crRank A
          (moderateCRInitModeMirror ring A D hPB halive hclean) ≤
        3 * A.gap) := by
  unfold moderateCRInitModeMirror
  exact
    Classical.choose_spec
      (crRankInit ring A D hPB
        (by
          intro hdone
          rcases hdone with hdel | hready
          · exact halive hdel
          · exact hclean hready))

noncomputable def moderateCRNextModeMirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n) (mode : CRMode)
    (hPB : PPL.Elim.PB ring D)
    (hInterior : CRInteriorFollowers A D)
    (hmode : CRModeHolds A D mode)
    (e : Fin n)
    (hnotDone : ¬ CRDone A (stepE ring D e)) : CRMode :=
  Classical.choose
    (by
      rcases
          (crRankStep_proved ring A D mode hPB hInterior hmode).1 e with
        hdone | hnext
      · exact False.elim (hnotDone hdone)
      · exact hnext)

theorem moderateCRNextModeMirror_spec
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n) (mode : CRMode)
    (hPB : PPL.Elim.PB ring D)
    (hInterior : CRInteriorFollowers A D)
    (hmode : CRModeHolds A D mode)
    (e : Fin n)
    (hnotDone : ¬ CRDone A (stepE ring D e)) :
    And
      (CRModeHolds A (stepE ring D e)
        (moderateCRNextModeMirror
          ring A D mode hPB hInterior hmode e hnotDone))
      (crRank A
          (moderateCRNextModeMirror
            ring A D mode hPB hInterior hmode e hnotDone) ≤
        crRank A mode) := by
  unfold moderateCRNextModeMirror
  exact
    Classical.choose_spec
      (by
        rcases
            (crRankStep_proved ring A D mode hPB hInterior hmode).1 e with
          hdone | hnext
        · exact False.elim (hnotDone hdone)
        · exact hnext)

/-! ## Rank non-uniqueness audit -/

/-- Every sweep witness is simultaneously a drain witness at the same
offset.  Thus CRModeHolds does not determine the mode. -/
theorem moderateCR_sweep_implies_drain
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat)
    (hsweep : CRModeHolds A C (.sweep p)) :
    CRModeHolds A C (.drain p) := by
  exact
    And.intro hsweep.1
      (And.intro hsweep.2.1 hsweep.2.2.1)

/-- The two simultaneously holding modes above have different ranks.
Consequently rank is not determined by the configuration. -/
theorem moderateCR_sweep_drain_rank_ne
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat)
    (hsweep : CRModeHolds A C (.sweep p)) :
    crRank A (.drain p) ≠ crRank A (.sweep p) := by
  have hp : p < A.gap := by
    have hv :=
      crModeHolds_valid A C (.sweep p) hsweep
    simpa [CRModeValid] using hv
  have hg : 0 < A.gap := A.gap_pos
  simp only [crRank]
  omega

/-- Definitionally identical mirror of the private post-attack stage. -/
private noncomputable def moderateCRAfterAttackStageMirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ModerateStage := by
  classical
  if hB : CleanReady F.B D then
    exact .dummyWait .ready .ready
  else
    exact .targetCR .ready
      (moderateCRInitModeMirror
        ring F.B D hgood.1
        (moderateCR_notEndpointB F D hgood) hB)

/-! ## The exact choice-specific residual -/

/--
The exact missing microfact.

The mirror is definitionally the private kernel choice.  Its ordinary
`choose_spec` is `moderateCRNextModeMirror_spec` above and proves only the
weak inequality.  This Prop asks only for strictness when the scheduler edge
is the CR required edge.
-/
def ModerateCRMirrorRequiredStrict : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (mode : CRMode)
    (hPB : PPL.Elim.PB ring C)
    (hInterior : CRInteriorFollowers A C)
    (hmode : CRModeHolds A C mode)
    (hnotDone :
      ¬ CRDone A (stepE ring C (crRequiredEdge A mode))),
    crRank A
        (moderateCRNextModeMirror
          ring A C mode hPB hInterior hmode
          (crRequiredEdge A mode) hnotDone) <
      crRank A mode

/-! ## Definitional equality with the private kernel choice -/

theorem moderateAttackCR_notDone_step_mirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (mode : CRMode) (e : Fin n)
    (htag : ¬ TaggedDeleted F (stepE ring C e))
    (hmode : CRModeHolds F.A C mode)
    (hdone : ¬ CRDone F.A (stepE ring C e)) :
    (moderateAttemptKernel ring F).step
        (.live C hgood (.attackCR mode)) e =
      .active
        (.live (stepE ring C e)
          (attemptGood_step ring F C e hgood htag)
          (.attackCR
            (moderateCRNextModeMirror
              ring F.A C mode hgood.1 hgood.2.2.1
              hmode e hdone))) := by
  simp
    [moderateAttemptKernel, moderateStep,
      htag, hmode, hdone,
      moderateCRNextModeMirror]
  all_goals rfl

theorem moderateTargetCR_notDone_step_mirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (attackPhase : SectorPhase) (mode : CRMode)
    (e : Fin n)
    (htag : ¬ TaggedDeleted F (stepE ring C e))
    (hmode : CRModeHolds F.B C mode)
    (hdone : ¬ CRDone F.B (stepE ring C e)) :
    (moderateAttemptKernel ring F).step
        (.live C hgood (.targetCR attackPhase mode)) e =
      .active
        (.live (stepE ring C e)
          (attemptGood_step ring F C e hgood htag)
          (.targetCR
            (nextSectorPhase F.A attackPhase e)
            (moderateCRNextModeMirror
              ring F.B C mode hgood.1 hgood.2.2.2
              hmode e hdone))) := by
  simp
    [moderateAttemptKernel, moderateStep,
      htag, hmode, hdone,
      moderateCRNextModeMirror]
  all_goals rfl

theorem moderateAttackCR_done_step_mirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (mode : CRMode) (e : Fin n)
    (htag : ¬ TaggedDeleted F (stepE ring C e))
    (hmode : CRModeHolds F.A C mode)
    (hdone : CRDone F.A (stepE ring C e)) :
    (moderateAttemptKernel ring F).step
        (.live C hgood (.attackCR mode)) e =
      .active
        (.live (stepE ring C e)
          (attemptGood_step ring F C e hgood htag)
          (moderateCRAfterAttackStageMirror
            ring F (stepE ring C e)
            (attemptGood_step ring F C e hgood htag))) := by
  simp
    [moderateAttemptKernel, moderateStep,
      htag, hmode, hdone,
      moderateCRAfterAttackStageMirror,
      moderateCRInitModeMirror]
  all_goals rfl

/-! ## Sealed phase closure used by targetCR -/

private theorem moderateCR_phaseReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hInterior : CRInteriorFollowers A C)
    (hclean : CleanReady A C) :
    PhaseHolds A C .ready := by
  constructor
  · intro q hq0 hq
    exact hInterior q hq0 hq
  · exact hclean

private theorem moderateCR_phaseANext
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (ph : SectorPhase)
    (hph : PhaseHolds F.A C ph)
    (e : Fin n)
    (hnot : ¬ TaggedDeleted F (stepE ring C e)) :
    PhaseHolds F.A (stepE ring C e)
      (nextSectorPhase F.A ph e) := by
  have hcur : ¬ EndpointDeleted F.A C := by
    intro hdel
    exact hgood.2.1
      (endpointA_deleted_tagged F C hdel)
  have hnext :
      ¬ EndpointDeleted F.A (stepE ring C e) := by
    intro hdel
    exact hnot
      (endpointA_deleted_tagged
        F (stepE ring C e) hdel)
  rcases
      hSealed ring F.A C ph hph hcur e with
    hdel | hsurvive
  · exact False.elim (hnext hdel)
  · rcases hsurvive with
      ⟨ph', hph', htr⟩
    have heq :
        ph' = nextSectorPhase F.A ph e := by
      simpa [PhaseTransition] using htr
    rw [heq] at hph'
    exact hph'

/-! ## Post-attack closure and budget -/

private theorem moderateCR_afterAttack_good
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D)
    (hAready : PhaseHolds F.A D .ready) :
    ModerateReachableGood ring F
      (.live D hgood
        (moderateCRAfterAttackStageMirror ring F D hgood)) := by
  classical
  by_cases hB : CleanReady F.B D
  · have hBready :
        PhaseHolds F.B D .ready :=
      moderateCR_phaseReady F.B D hgood.2.2.2 hB
    simpa
      [moderateCRAfterAttackStageMirror, hB,
        ModerateReachableGood]
      using And.intro hAready hBready
  · have hinit :=
      moderateCRInitModeMirror_spec
        ring F.B D hgood.1
        (moderateCR_notEndpointB F D hgood) hB
    simpa
      [moderateCRAfterAttackStageMirror, hB,
        ModerateReachableGood]
      using And.intro hAready hinit.1

private theorem moderateCR_targetPreparation_exact
    (n b : Nat) :
    3 * n * b + n * (2 * b - 1) =
      n * (5 * b - 1) := by
  calc
    3 * n * b + n * (2 * b - 1)
        = n * (3 * b) + n * (2 * b - 1) := by
            ac_rfl
    _ = n * (3 * b + (2 * b - 1)) := by
          rw [Nat.mul_add]
    _ = n * (5 * b - 1) := by
          congr 1
          omega

private theorem moderateCR_waitBudget_le_afterAttack
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    moderateWaitBudget F ≤ moderateAfterAttackBudget F := by
  unfold moderateWaitBudget moderateAfterAttackBudget
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  have hb : 0 < F.b := by
    have h := F.B.gap_pos
    simpa [F.B_gap] using h
  omega

private theorem moderateCR_targetInit_le_afterAttack
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (mode : CRMode)
    (hrank : crRank F.B mode ≤ 3 * F.B.gap) :
    n * crRank F.B mode + moderateWaitBudget F ≤
      moderateAfterAttackBudget F := by
  have hrank' :
      n * crRank F.B mode ≤ 3 * n * F.b := by
    have h := Nat.mul_le_mul_left n hrank
    simpa
      [F.B_gap, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
      using h
  unfold moderateWaitBudget moderateAfterAttackBudget
  have hex := moderateCR_targetPreparation_exact n F.b
  unfold moderateVulnerableBudget moderateRecoveryBudget
  omega

private theorem moderateCR_afterAttack_potential_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    moderateStagePotential F
        (moderateCRAfterAttackStageMirror ring F D hgood) ≤
      moderateAfterAttackBudget F := by
  classical
  by_cases hB : CleanReady F.B D
  · simpa
      [moderateCRAfterAttackStageMirror, hB,
        moderateStagePotential, phaseDebt]
      using moderateCR_waitBudget_le_afterAttack F
  · have hinit :=
      moderateCRInitModeMirror_spec
        ring F.B D hgood.1
        (moderateCR_notEndpointB F D hgood) hB
    simpa
      [moderateCRAfterAttackStageMirror, hB,
        moderateStagePotential]
      using
        moderateCR_targetInit_le_afterAttack
          F
          (moderateCRInitModeMirror
            ring F.B D hgood.1
            (moderateCR_notEndpointB F D hgood) hB)
          hinit.2

/-! ## Exact potential of a completed target-CR child -/

/-- A target-CR completion enters dummyWait with the target already Ready.
The attack phase may have advanced, but dummyWait's stage potential depends
only on the target phase, so this child carries exactly moderateWaitBudget. -/
private theorem moderateCR_dummyWaitReady_potential
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D)
    (attackPhase : SectorPhase) :
    moderateLivePotential F
        (.live D hgood (.dummyWait attackPhase .ready)) =
      moderateWaitBudget F := by
  simp
    [moderateLivePotential, moderateStagePotential,
      phaseDebt]

/-! ## One-service-edge Bellman arithmetic -/

private theorem moderateCR_oneExceptionAffine
    {n r tail : Nat}
    (a : Fin n) (f : Fin n → Nat)
    (hr : 0 < r)
    (ha : f a ≤ n * (r - 1) + tail)
    (hother :
      ∀ e, e ≠ a →
        f e ≤ n * r + tail) :
    n + (List.ofFn f).sum ≤
      n * (n * r + tail) := by
  let c := n * r + tail
  let g : Fin n → Nat :=
    fun e => if e = a then f e else c
  have hfg : ∀ e, f e ≤ g e := by
    intro e
    by_cases he : e = a
    · simp [g, he]
    · simpa [g, he] using hother e he
  have hsum0 :
      (List.ofFn f).sum ≤
        (List.ofFn g).sum :=
    ofFn_sum_le f g hfg
  have hsumg :
      (List.ofFn g).sum =
        f a + (n - 1) * c := by
    have h :=
      PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const
        a g c (by
          intro e he
          simp [g, he])
    simpa [g] using h
  have hsum :
      (List.ofFn f).sum ≤
        f a + (n - 1) * c := by
    rw [hsumg] at hsum0
    exact hsum0
  have hsum' :
      (List.ofFn f).sum ≤
        (n * (r - 1) + tail) +
          (n - 1) * c :=
    Nat.le_trans hsum
      (Nat.add_le_add_right ha _)
  have hc :
      c = n + (n * (r - 1) + tail) := by
    obtain ⟨q, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show r ≠ 0 by omega)
    subst r
    dsimp [c]
    rw [Nat.mul_succ]
    omega
  have hnpos : 0 < n := by
    have haLt := a.isLt
    omega
  have hm :
      n * c = c + (n - 1) * c := by
    obtain ⟨q, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show n ≠ 0 by omega)
    rw [hq]
    simp [Nat.succ_mul, Nat.add_comm]
  have hfinal :
      n + (List.ofFn f).sum ≤ n * c := by
    calc
      n + (List.ofFn f).sum
          ≤ n +
              ((n * (r - 1) + tail) +
                (n - 1) * c) :=
        Nat.add_le_add_left hsum' n
      _ = (n + (n * (r - 1) + tail)) +
            (n - 1) * c := by
        omega
      _ = c + (n - 1) * c := by
        rw [← hc]
      _ = n * c := hm.symm
  simpa [c] using hfinal

/-! ## The two CR stage rows, conditional only on the choice microfact -/

theorem moderateCRStageRows_of_mirrorRequiredStrict
    (hStrict : ModerateCRMirrorRequiredStrict) :
    ModerateCRStageRows := by
  intro hSealed n ring C0 F _hb C hgood stage hCR hreach
  cases stage with
  | attackCR mode =>
      have hmode : CRModeHolds F.A C mode := by
        simpa [ModerateReachableGood] using hreach
      refine And.intro ?_ ?_
      · intro e a' hstep
        by_cases htag :
            TaggedDeleted F (stepE ring C e)
        · have hs :
              (moderateAttemptKernel ring F).step
                  (.live C hgood (.attackCR mode)) e =
                .success := by
            simp
              [moderateAttemptKernel,
                moderateStep, htag]
          have hbad :
              (AttemptNode.success :
                AttemptNode
                  (ModerateAttemptState ring F)
                  (Config n)) =
                .active a' :=
            hs.symm.trans hstep
          cases hbad
        · have hgoodD :
              AttemptGood ring F (stepE ring C e) :=
            attemptGood_step ring F C e hgood htag
          by_cases hdone :
              CRDone F.A (stepE ring C e)
          · have hnotA :
                ¬ EndpointDeleted F.A
                  (stepE ring C e) := by
              intro hdel
              exact htag
                (endpointA_deleted_tagged
                  F (stepE ring C e) hdel)
            have hcleanA :
                CleanReady F.A (stepE ring C e) :=
              Or.resolve_left hdone hnotA
            have hAready :
                PhaseHolds F.A
                  (stepE ring C e) .ready :=
              moderateCR_phaseReady
                F.A (stepE ring C e)
                hgoodD.2.2.1 hcleanA
            have hs :=
              moderateAttackCR_done_step_mirror
                ring F C hgood mode e htag hmode hdone
            let child : ModerateAttemptState ring F :=
              .live (stepE ring C e) hgoodD
                (moderateCRAfterAttackStageMirror
                  ring F (stepE ring C e) hgoodD)
            have hs' :
                (moderateAttemptKernel ring F).step
                    (.live C hgood (.attackCR mode)) e =
                  .active child := by
              simpa [child] using hs
            have hnodes :
                (AttemptNode.active child :
                  AttemptNode
                    (ModerateAttemptState ring F)
                    (Config n)) =
                  .active a' :=
              hs'.symm.trans hstep
            have ha : child = a' := by
              injection hnodes
            rw [← ha]
            exact
              moderateCR_afterAttack_good
                ring F (stepE ring C e)
                hgoodD hAready
          · have hs :=
              moderateAttackCR_notDone_step_mirror
                ring F C hgood mode e htag hmode hdone
            let child : ModerateAttemptState ring F :=
              .live (stepE ring C e) hgoodD
                (.attackCR
                  (moderateCRNextModeMirror
                    ring F.A C mode hgood.1
                    hgood.2.2.1 hmode e hdone))
            have hs' :
                (moderateAttemptKernel ring F).step
                    (.live C hgood (.attackCR mode)) e =
                  .active child := by
              simpa [child] using hs
            have hnodes :
                (AttemptNode.active child :
                  AttemptNode
                    (ModerateAttemptState ring F)
                    (Config n)) =
                  .active a' :=
              hs'.symm.trans hstep
            have ha : child = a' := by
              injection hnodes
            rw [← ha]
            have hn :=
              moderateCRNextModeMirror_spec
                ring F.A C mode hgood.1
                hgood.2.2.1 hmode e hdone
            simpa
              [child, ModerateReachableGood]
              using hn.1
      · simp only
          [moderateLivePotential,
            moderateStagePotential]
        have hrpos :
            0 < crRank F.A mode :=
          crRank_pos F.A mode
            (crModeHolds_valid F.A C mode hmode)
        apply
          moderateCR_oneExceptionAffine
            (a := crRequiredEdge F.A mode)
            (f := fun e : Fin n =>
              attemptNodePotential
                (moderateLivePotential F)
                ((moderateAttemptKernel ring F).step
                  (.live C hgood (.attackCR mode)) e))
            (r := crRank F.A mode)
            (tail := moderateAfterAttackBudget F)
            hrpos
        · let e := crRequiredEdge F.A mode
          by_cases htag :
              TaggedDeleted F (stepE ring C e)
          · have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood (.attackCR mode)) e =
                  .success := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag]
            rw [hs]
            simp [attemptNodePotential]
          · by_cases hdone :
                CRDone F.A (stepE ring C e)
            · have hs :=
                moderateAttackCR_done_step_mirror
                  ring F C hgood mode e htag hmode hdone
              rw [hs]
              change
                moderateStagePotential F
                    (moderateCRAfterAttackStageMirror
                      ring F (stepE ring C e)
                      (attemptGood_step
                        ring F C e hgood htag)) ≤
                  n * (crRank F.A mode - 1) +
                    moderateAfterAttackBudget F
              have hp :=
                moderateCR_afterAttack_potential_le
                  ring F (stepE ring C e)
                  (attemptGood_step
                    ring F C e hgood htag)
              exact
                Nat.le_trans hp
                  (Nat.le_add_left _ _)
            · have hs :=
                moderateAttackCR_notDone_step_mirror
                  ring F C hgood mode e htag hmode hdone
              rw [hs]
              change
                n *
                    crRank F.A
                      (moderateCRNextModeMirror
                        ring F.A C mode hgood.1
                        hgood.2.2.1 hmode e hdone) +
                    moderateAfterAttackBudget F ≤
                  n * (crRank F.A mode - 1) +
                    moderateAfterAttackBudget F
              have hlt :
                  crRank F.A
                      (moderateCRNextModeMirror
                        ring F.A C mode hgood.1
                        hgood.2.2.1 hmode e hdone) <
                    crRank F.A mode := by
                dsimp [e] at hdone ⊢
                exact
                  hStrict ring F.A C mode
                    hgood.1 hgood.2.2.1
                    hmode hdone
              have hle :
                  crRank F.A
                      (moderateCRNextModeMirror
                        ring F.A C mode hgood.1
                        hgood.2.2.1 hmode e hdone) ≤
                    crRank F.A mode - 1 := by
                omega
              exact
                Nat.add_le_add_right
                  (Nat.mul_le_mul_left n hle) _
        · intro e _hne
          by_cases htag :
              TaggedDeleted F (stepE ring C e)
          · have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood (.attackCR mode)) e =
                  .success := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag]
            rw [hs]
            simp [attemptNodePotential]
          · by_cases hdone :
                CRDone F.A (stepE ring C e)
            · have hs :=
                moderateAttackCR_done_step_mirror
                  ring F C hgood mode e htag hmode hdone
              rw [hs]
              change
                moderateStagePotential F
                    (moderateCRAfterAttackStageMirror
                      ring F (stepE ring C e)
                      (attemptGood_step
                        ring F C e hgood htag)) ≤
                  n * crRank F.A mode +
                    moderateAfterAttackBudget F
              have hp :=
                moderateCR_afterAttack_potential_le
                  ring F (stepE ring C e)
                  (attemptGood_step
                    ring F C e hgood htag)
              exact
                Nat.le_trans hp
                  (Nat.le_add_left _ _)
            · have hs :=
                moderateAttackCR_notDone_step_mirror
                  ring F C hgood mode e htag hmode hdone
              rw [hs]
              change
                n *
                    crRank F.A
                      (moderateCRNextModeMirror
                        ring F.A C mode hgood.1
                        hgood.2.2.1 hmode e hdone) +
                    moderateAfterAttackBudget F ≤
                  n * crRank F.A mode +
                    moderateAfterAttackBudget F
              have hn :=
                (moderateCRNextModeMirror_spec
                  ring F.A C mode hgood.1
                  hgood.2.2.1 hmode e hdone).2
              exact
                Nat.add_le_add_right
                  (Nat.mul_le_mul_left n hn) _
  | targetCR attackPhase mode =>
      have hparts :
          And
            (PhaseHolds F.A C attackPhase)
            (CRModeHolds F.B C mode) := by
        simpa [ModerateReachableGood] using hreach
      have hA := hparts.1
      have hmode := hparts.2
      refine And.intro ?_ ?_
      · intro e a' hstep
        by_cases htag :
            TaggedDeleted F (stepE ring C e)
        · have hs :
              (moderateAttemptKernel ring F).step
                  (.live C hgood
                    (.targetCR attackPhase mode)) e =
                .success := by
            simp
              [moderateAttemptKernel,
                moderateStep, htag]
          have hbad :
              (AttemptNode.success :
                AttemptNode
                  (ModerateAttemptState ring F)
                  (Config n)) =
                .active a' :=
            hs.symm.trans hstep
          cases hbad
        · have hgoodD :
              AttemptGood ring F (stepE ring C e) :=
            attemptGood_step ring F C e hgood htag
          have hA' :
              PhaseHolds F.A (stepE ring C e)
                (nextSectorPhase F.A attackPhase e) :=
            moderateCR_phaseANext
              hSealed ring F C hgood
              attackPhase hA e htag
          by_cases hdone :
              CRDone F.B (stepE ring C e)
          · have hnotB :
                ¬ EndpointDeleted F.B
                  (stepE ring C e) := by
              intro hdel
              exact htag
                (endpointB_deleted_tagged
                  F (stepE ring C e) hdel)
            have hcleanB :
                CleanReady F.B (stepE ring C e) :=
              Or.resolve_left hdone hnotB
            have hBready :
                PhaseHolds F.B
                  (stepE ring C e) .ready :=
              moderateCR_phaseReady
                F.B (stepE ring C e)
                hgoodD.2.2.2 hcleanB
            let child : ModerateAttemptState ring F :=
              .live (stepE ring C e) hgoodD
                (.dummyWait
                  (nextSectorPhase F.A attackPhase e)
                  .ready)
            have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.targetCR attackPhase mode)) e =
                  .active child := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag,
                  hmode, hdone, child]
            have hnodes :
                (AttemptNode.active child :
                  AttemptNode
                    (ModerateAttemptState ring F)
                    (Config n)) =
                  .active a' :=
              hs.symm.trans hstep
            have ha : child = a' := by
              injection hnodes
            rw [← ha]
            simpa
              [child, ModerateReachableGood]
              using And.intro hA' hBready
          · have hs :=
              moderateTargetCR_notDone_step_mirror
                ring F C hgood attackPhase mode
                e htag hmode hdone
            let child : ModerateAttemptState ring F :=
              .live (stepE ring C e) hgoodD
                (.targetCR
                  (nextSectorPhase F.A attackPhase e)
                  (moderateCRNextModeMirror
                    ring F.B C mode hgood.1
                    hgood.2.2.2 hmode e hdone))
            have hs' :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.targetCR attackPhase mode)) e =
                  .active child := by
              simpa [child] using hs
            have hnodes :
                (AttemptNode.active child :
                  AttemptNode
                    (ModerateAttemptState ring F)
                    (Config n)) =
                  .active a' :=
              hs'.symm.trans hstep
            have ha : child = a' := by
              injection hnodes
            rw [← ha]
            have hn :=
              moderateCRNextModeMirror_spec
                ring F.B C mode hgood.1
                hgood.2.2.2 hmode e hdone
            simpa
              [child, ModerateReachableGood]
              using And.intro hA' hn.1
      · simp only
          [moderateLivePotential,
            moderateStagePotential]
        have hrpos :
            0 < crRank F.B mode :=
          crRank_pos F.B mode
            (crModeHolds_valid F.B C mode hmode)
        apply
          moderateCR_oneExceptionAffine
            (a := crRequiredEdge F.B mode)
            (f := fun e : Fin n =>
              attemptNodePotential
                (moderateLivePotential F)
                ((moderateAttemptKernel ring F).step
                  (.live C hgood
                    (.targetCR attackPhase mode)) e))
            (r := crRank F.B mode)
            (tail := moderateWaitBudget F)
            hrpos
        · let e := crRequiredEdge F.B mode
          by_cases htag :
              TaggedDeleted F (stepE ring C e)
          · have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.targetCR attackPhase mode)) e =
                  .success := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag]
            rw [hs]
            simp [attemptNodePotential]
          · by_cases hdone :
                CRDone F.B (stepE ring C e)
            · have hs :
                  (moderateAttemptKernel ring F).step
                      (.live C hgood
                        (.targetCR attackPhase mode)) e =
                    .active
                      (.live (stepE ring C e)
                        (attemptGood_step
                          ring F C e hgood htag)
                        (.dummyWait
                          (nextSectorPhase
                            F.A attackPhase e)
                          .ready)) := by
                simp
                  [moderateAttemptKernel,
                    moderateStep, htag,
                    hmode, hdone]
              rw [hs]
              simpa only
                [attemptNodePotential,
                  moderateCR_dummyWaitReady_potential]
                using
                  (Nat.le_add_left
                    (moderateWaitBudget F)
                    (n * (crRank F.B mode - 1)))
            · have hs :=
                moderateTargetCR_notDone_step_mirror
                  ring F C hgood attackPhase mode
                  e htag hmode hdone
              rw [hs]
              change
                n *
                    crRank F.B
                      (moderateCRNextModeMirror
                        ring F.B C mode hgood.1
                        hgood.2.2.2 hmode e hdone) +
                    moderateWaitBudget F ≤
                  n * (crRank F.B mode - 1) +
                    moderateWaitBudget F
              have hlt :
                  crRank F.B
                      (moderateCRNextModeMirror
                        ring F.B C mode hgood.1
                        hgood.2.2.2 hmode e hdone) <
                    crRank F.B mode := by
                dsimp [e] at hdone ⊢
                exact
                  hStrict ring F.B C mode
                    hgood.1 hgood.2.2.2
                    hmode hdone
              have hle :
                  crRank F.B
                      (moderateCRNextModeMirror
                        ring F.B C mode hgood.1
                        hgood.2.2.2 hmode e hdone) ≤
                    crRank F.B mode - 1 := by
                omega
              exact
                Nat.add_le_add_right
                  (Nat.mul_le_mul_left n hle) _
        · intro e _hne
          by_cases htag :
              TaggedDeleted F (stepE ring C e)
          · have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.targetCR attackPhase mode)) e =
                  .success := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag]
            rw [hs]
            simp [attemptNodePotential]
          · by_cases hdone :
                CRDone F.B (stepE ring C e)
            · have hs :
                  (moderateAttemptKernel ring F).step
                      (.live C hgood
                        (.targetCR attackPhase mode)) e =
                    .active
                      (.live (stepE ring C e)
                        (attemptGood_step
                          ring F C e hgood htag)
                        (.dummyWait
                          (nextSectorPhase
                            F.A attackPhase e)
                          .ready)) := by
                simp
                  [moderateAttemptKernel,
                    moderateStep, htag,
                    hmode, hdone]
              rw [hs]
              simpa only
                [attemptNodePotential,
                  moderateCR_dummyWaitReady_potential]
                using
                  (Nat.le_add_left
                    (moderateWaitBudget F)
                    (n * crRank F.B mode))
            · have hs :=
                moderateTargetCR_notDone_step_mirror
                  ring F C hgood attackPhase mode
                  e htag hmode hdone
              rw [hs]
              change
                n *
                    crRank F.B
                      (moderateCRNextModeMirror
                        ring F.B C mode hgood.1
                        hgood.2.2.2 hmode e hdone) +
                    moderateWaitBudget F ≤
                  n * crRank F.B mode +
                    moderateWaitBudget F
              have hn :=
                (moderateCRNextModeMirror_spec
                  ring F.B C mode hgood.1
                  hgood.2.2.2 hmode e hdone).2
              exact
                Nat.add_le_add_right
                  (Nat.mul_le_mul_left n hn) _
  | dummyWait attackPhase targetPhase =>
      exact False.elim hCR
  | vulnerable attackPhase targetPhase =>
      exact False.elim hCR
  | recovery attackPhase targetPhase =>
      exact False.elim hCR
  | stuck =>
      exact False.elim hCR

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.moderateCR_sweep_implies_drain
#print axioms PPL.Convergence.LDLocal.moderateCR_sweep_drain_rank_ne
#print axioms PPL.Convergence.LDLocal.moderateCRInitModeMirror_spec
#print axioms PPL.Convergence.LDLocal.moderateCRNextModeMirror_spec
#print axioms PPL.Convergence.LDLocal.moderateAttackCR_notDone_step_mirror
#print axioms PPL.Convergence.LDLocal.moderateTargetCR_notDone_step_mirror
#print axioms PPL.Convergence.LDLocal.moderateAttackCR_done_step_mirror
#print axioms PPL.Convergence.LDLocal.moderateCR_phaseReady
#print axioms PPL.Convergence.LDLocal.moderateCR_phaseANext
#print axioms PPL.Convergence.LDLocal.moderateCR_afterAttack_good
#print axioms PPL.Convergence.LDLocal.moderateCR_targetPreparation_exact
#print axioms PPL.Convergence.LDLocal.moderateCR_waitBudget_le_afterAttack
#print axioms PPL.Convergence.LDLocal.moderateCR_targetInit_le_afterAttack
#print axioms PPL.Convergence.LDLocal.moderateCR_afterAttack_potential_le
#print axioms PPL.Convergence.LDLocal.moderateCR_dummyWaitReady_potential
#print axioms PPL.Convergence.LDLocal.moderateCR_oneExceptionAffine
#print axioms PPL.Convergence.LDLocal.moderateCRStageRows_of_mirrorRequiredStrict

#check PPL.Convergence.LDLocal.ModerateCRMirrorRequiredStrict
#check PPL.Convergence.LDLocal.ModerateCRStageRows

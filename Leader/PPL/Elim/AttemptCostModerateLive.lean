import Leader.PPL.Elim.AttemptCostModerate

/-!
# LD(736): moderate attempt live-stage invariant and potential

This downstream file closes the reachability/witness bookkeeping that caused
the `.stuck` obstruction in `LDLocalAttemptCostModerate.lean`.

The private CR/start helpers in `LDLocalAttempt.lean` are mirrored
definitionally under new names.  This exposes their `Classical.choose_spec`
witnesses without editing the existing file.

One bounded-round residual remains, isolated as
`ModerateLiveSingleInteractionSpec`: it is exactly the one-interaction
Bellman/closure calculation for the already-defined stage potential.  It is
the only named single-interaction Prop in this file.

The intended discharge uses:
* CR rows underlying `cleanReady_cost_proved` for attackCR/targetCR;
* `controlRowSpec_proved` (hence `qTrial_cost_five_na`) for vulnerable;
* the sealed target phase debt for dummyWait/recovery.

`retainedTrial_cost_nr` is not type-aligned with the moderate kernel:
it is a theorem on `RetainedState F` used by the long attempt.  The moderate
recovery stage is the B-sector `SectorPhase` recovery and therefore uses
`phaseDebt F.b`, not `RetainedState`.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-! ## Public copies of the private CR choices -/

private theorem moderateLive_notEndpointA
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.A D := by
  intro h
  exact hgood.2.1 (endpointA_deleted_tagged F D h)

private theorem moderateLive_notEndpointB
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.B D := by
  intro h
  exact hgood.2.1 (endpointB_deleted_tagged F D h)

private noncomputable def moderateLiveCRInitMode
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

private theorem moderateLiveCRInitMode_spec
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n)
    (hPB : PPL.Elim.PB ring D)
    (halive : ¬ EndpointDeleted A D)
    (hclean : ¬ CleanReady A D) :
    CRModeHolds A D
        (moderateLiveCRInitMode ring A D hPB halive hclean) ∧
      crRank A
          (moderateLiveCRInitMode ring A D hPB halive hclean) ≤
        3 * A.gap := by
  unfold moderateLiveCRInitMode
  exact
    Classical.choose_spec
      (crRankInit ring A D hPB
        (by
          intro hdone
          rcases hdone with hdel | hready
          · exact halive hdel
          · exact hclean hready))

private noncomputable def moderateLiveCRNextMode
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

private theorem moderateLiveCRNextMode_spec
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n) (mode : CRMode)
    (hPB : PPL.Elim.PB ring D)
    (hInterior : CRInteriorFollowers A D)
    (hmode : CRModeHolds A D mode)
    (e : Fin n)
    (hnotDone : ¬ CRDone A (stepE ring D e)) :
    CRModeHolds A (stepE ring D e)
        (moderateLiveCRNextMode
          ring A D mode hPB hInterior hmode e hnotDone) ∧
      crRank A
          (moderateLiveCRNextMode
            ring A D mode hPB hInterior hmode e hnotDone) ≤
        crRank A mode := by
  unfold moderateLiveCRNextMode
  exact
    Classical.choose_spec
      (by
        rcases
            (crRankStep_proved ring A D mode hPB hInterior hmode).1 e with
          hdone | hnext
        · exact False.elim (hnotDone hdone)
        · exact hnext)

/-! ## Definitionally identical start-stage mirror -/

private noncomputable def moderateLiveAfterAttackStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : ModerateStage := by
  classical
  if hB : CleanReady F.B D then
    exact .dummyWait .ready .ready
  else
    exact .targetCR .ready
      (moderateLiveCRInitMode
        ring F.B D hgood.1
        (moderateLive_notEndpointB F D hgood) hB)

private noncomputable def moderateLiveInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : ModerateStage := by
  classical
  if hA : CleanReady F.A D then
    exact moderateLiveAfterAttackStage ring F D hgood
  else
    exact .attackCR
      (moderateLiveCRInitMode
        ring F.A D hgood.1
        (moderateLive_notEndpointA F D hgood) hA)

private noncomputable def moderateLiveStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) : ModerateAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood
      (moderateLiveInitialStage ring F D hgood)
  else
    exact .junk D

/-- The mirror is definitionally the existing private start construction. -/
private theorem moderateStart_eq_moderateLiveStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (moderateAttemptKernel ring F).start D =
      moderateLiveStart ring F D := by
  rfl

/-! ## Reachable-good structural invariant -/

private def ModerateRecoveryPhase : SectorPhase → Prop
  | .live p => 0 < p
  | .ret _ => True
  | .ready => False
  | .dummy _ => False

/-- The witnesses needed to ensure that the physical attempt never enters the
synthetic `.stuck` branch on an actually reachable survivor. -/
def ModerateReachableGood
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    ModerateAttemptState ring F → Prop
  | .junk _ => False
  | .live C _ stage =>
      match stage with
      | .attackCR mode =>
          CRModeHolds F.A C mode
      | .targetCR attackPhase mode =>
          PhaseHolds F.A C attackPhase ∧
            CRModeHolds F.B C mode
      | .dummyWait attackPhase targetPhase =>
          PhaseHolds F.A C attackPhase ∧
            PhaseHolds F.B C targetPhase
      | .vulnerable attackPhase targetPhase =>
          PhaseHolds F.A C attackPhase ∧
            PhaseHolds F.B C targetPhase ∧
            (C F.j).shield = false
      | .recovery attackPhase targetPhase =>
          PhaseHolds F.A C attackPhase ∧
            PhaseHolds F.B C targetPhase ∧
            ModerateRecoveryPhase targetPhase
      | .stuck => False

theorem moderateReachableGood_excludes_stuck
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C) :
    ¬ ModerateReachableGood ring F
        (.live C hgood .stuck) := by
  intro h
  exact h

private theorem phaseReady_of_interior_clean
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

private theorem moderateReachableGood_afterAttack
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D)
    (hAready : PhaseHolds F.A D .ready) :
    ModerateReachableGood ring F
      (.live D hgood
        (moderateLiveAfterAttackStage ring F D hgood)) := by
  classical
  by_cases hB : CleanReady F.B D
  · have hBready :
        PhaseHolds F.B D .ready :=
      phaseReady_of_interior_clean
        F.B D hgood.2.2.2 hB
    simpa [moderateLiveAfterAttackStage, hB,
      ModerateReachableGood] using
      (And.intro hAready hBready)
  · have hinit :=
      moderateLiveCRInitMode_spec
        ring F.B D hgood.1
        (moderateLive_notEndpointB F D hgood) hB
    simpa [moderateLiveAfterAttackStage, hB,
      ModerateReachableGood] using
      (And.intro hAready hinit.1)

private theorem moderateReachableGood_initialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ModerateReachableGood ring F
      (.live D hgood
        (moderateLiveInitialStage ring F D hgood)) := by
  classical
  by_cases hA : CleanReady F.A D
  · have hAready :
        PhaseHolds F.A D .ready :=
      phaseReady_of_interior_clean
        F.A D hgood.2.2.1 hA
    simpa [moderateLiveInitialStage, hA] using
      moderateReachableGood_afterAttack
        ring F D hgood hAready
  · have hinit :=
      moderateLiveCRInitMode_spec
        ring F.A D hgood.1
        (moderateLive_notEndpointA F D hgood) hA
    simpa [moderateLiveInitialStage, hA,
      ModerateReachableGood] using hinit.1

theorem moderateReachableGood_start
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ModerateReachableGood ring F
      ((moderateAttemptKernel ring F).start D) := by
  classical
  rw [moderateStart_eq_moderateLiveStart]
  simp only [moderateLiveStart, dif_pos hgood]
  exact moderateReachableGood_initialStage
    ring F D hgood

/-! ## Budget-aligned stage potential -/

def moderateRecoveryBudget
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  n * (2 * F.b - 2)

def moderateVulnerableBudget
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  5 * n * F.a + moderateRecoveryBudget F

def moderateWaitBudget
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  n * (2 * F.b - 1) + moderateVulnerableBudget F

def moderateAfterAttackBudget
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  n * (5 * F.b - 1) + moderateVulnerableBudget F

def moderateStagePotential
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : ModerateStage → Nat
  | .attackCR mode =>
      n * crRank F.A mode + moderateAfterAttackBudget F
  | .targetCR _ mode =>
      n * crRank F.B mode + moderateWaitBudget F
  | .dummyWait _ targetPhase =>
      n * phaseDebt F.b targetPhase + moderateWaitBudget F
  | .vulnerable attackPhase _ =>
      n * attackerCoeff F attackPhase + moderateRecoveryBudget F
  | .recovery _ targetPhase =>
      n * phaseDebt F.b targetPhase
  | .stuck => 0

def moderateLivePotential
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    ModerateAttemptState ring F → Nat
  | .junk _ => 0
  | .live _ _ stage => moderateStagePotential F stage

private theorem targetPreparation_exact
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

private theorem moderateWaitBudget_le_afterAttack
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

private theorem moderateTargetInit_le_afterAttack
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (mode : CRMode)
    (hrank : crRank F.B mode ≤ 3 * F.B.gap) :
    n * crRank F.B mode + moderateWaitBudget F ≤
      moderateAfterAttackBudget F := by
  have hrank' :
      n * crRank F.B mode ≤ 3 * n * F.b := by
    have h :=
      Nat.mul_le_mul_left n hrank
    simpa [F.B_gap, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using h
  unfold moderateWaitBudget moderateAfterAttackBudget
  have hex := targetPreparation_exact n F.b
  unfold moderateVulnerableBudget moderateRecoveryBudget
  omega

private theorem moderateAfterAttackPotential_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    moderateStagePotential F
        (moderateLiveAfterAttackStage ring F D hgood) ≤
      moderateAfterAttackBudget F := by
  classical
  by_cases hB : CleanReady F.B D
  · simpa [moderateLiveAfterAttackStage, hB,
      moderateStagePotential, phaseDebt] using
      moderateWaitBudget_le_afterAttack F
  · have hinit :=
      moderateLiveCRInitMode_spec
        ring F.B D hgood.1
        (moderateLive_notEndpointB F D hgood) hB
    simpa [moderateLiveAfterAttackStage, hB,
      moderateStagePotential] using
      moderateTargetInit_le_afterAttack
        F
        (moderateLiveCRInitMode
          ring F.B D hgood.1
          (moderateLive_notEndpointB F D hgood) hB)
        hinit.2

private theorem moderateInitialStagePotential_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    moderateStagePotential F
        (moderateLiveInitialStage ring F D hgood) ≤
      moderatePaperAttemptBudget n F.a F.b := by
  classical
  by_cases hA : CleanReady F.A D
  · have htail :=
      moderateAfterAttackPotential_le
        ring F D hgood
    have ha : 0 < F.a := by
      have h := F.A.gap_pos
      simpa [F.A_gap] using h
    simpa [moderateLiveInitialStage, hA,
      moderatePaperAttemptBudget,
      moderateAfterAttackBudget,
      moderateVulnerableBudget,
      moderateRecoveryBudget] using
      Nat.le_trans htail
        (by
          simp only [moderateAfterAttackBudget, moderateVulnerableBudget,
            moderateRecoveryBudget, moderatePaperAttemptBudget]
          omega)
  · have hinit :=
      moderateLiveCRInitMode_spec
        ring F.A D hgood.1
        (moderateLive_notEndpointA F D hgood) hA
    have hrank :
        n *
            crRank F.A
              (moderateLiveCRInitMode
                ring F.A D hgood.1
                (moderateLive_notEndpointA F D hgood) hA) ≤
          3 * n * F.a := by
      have h :=
        Nat.mul_le_mul_left n hinit.2
      simpa [F.A_gap, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using h
    have htail :=
      moderateAfterAttackPotential_le
        ring F D hgood
    simp only [moderateLiveInitialStage, hA,
      moderateStagePotential]
    unfold moderatePaperAttemptBudget
    have hsum :=
      Nat.add_le_add hrank htail
    first
      | simpa [moderateAfterAttackBudget,
          moderateVulnerableBudget,
          moderateRecoveryBudget,
          Nat.add_assoc] using hsum
      | simpa [moderateAfterAttackBudget,
          moderateVulnerableBudget,
          moderateRecoveryBudget,
          Nat.add_assoc] using hrank

theorem moderateLivePotential_start_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    moderateLivePotential F
        ((moderateAttemptKernel ring F).start D) ≤
      moderatePaperAttemptBudget n F.a F.b := by
  rw [moderateStart_eq_moderateLiveStart]
  classical
  simp only [moderateLiveStart, dif_pos hgood,
    moderateLivePotential]
  exact moderateInitialStagePotential_le
    ring F D hgood

/-!
## The one bounded-round residual

This is deliberately one single-interaction Prop.  Its first conjunct is the
closure of the reachable-good witnesses across an active child; in particular
it is the exact statement needed to rule out the synthetic `.stuck` branch
on a reachable survivor.  Its second conjunct is the Bellman row for the
budget-aligned potential above.

The row calculation should be discharged stage-by-stage:
* attackCR/targetCR: `crRankStep_proved`, the same physical rows used by
  `cleanReady_cost_proved`;
* dummyWait/recovery: `nextSectorPhase` / `phaseDebt`;
* vulnerable: `controlRowSpec_proved`, whose attacker row yields
  `qTrial_cost_five_na`.

No independent stochastic argument belongs in this Prop.
-/
def ModerateLiveSingleInteractionSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0)
      (hb : 2 ≤ F.b),
      (∀ a e a',
        ModerateReachableGood ring F a →
        (moderateAttemptKernel ring F).step a e = .active a' →
        ModerateReachableGood ring F a') ∧
      AttemptCostSuperSolutionOn
        (moderateAttemptKernel ring F)
        (ModerateReachableGood ring F)
        (moderateLivePotential F)

/-- All non-row obligations in ModerateLiveStageSuperSolutionSpec are now
proved.  The sole bounded-round residual is ModerateLiveSingleInteractionSpec. -/
theorem moderateLiveStageSuperSolution
    (hlocal : ModerateLiveSingleInteractionSpec) :
    ModerateLiveStageSuperSolutionSpec := by
  intro hSealed n ring C0 F hb
  refine
    ⟨ModerateReachableGood ring F,
      moderateLivePotential F,
      ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact moderateReachableGood_start
      ring F s hs
  · exact (hlocal hSealed ring F hb).1
  · exact (hlocal hSealed ring F hb).2
  · intro s hs
    exact moderateLivePotential_start_le
      ring F s hs

theorem moderateAttemptCostSpec_proved
    (hlocal : ModerateLiveSingleInteractionSpec) :
    ModerateAttemptCostSpec :=
  moderateAttemptCostSpec_of_live_stage
    (moderateLiveStageSuperSolution hlocal)

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.moderateReachableGood_excludes_stuck
#print axioms PPL.Convergence.LDLocal.moderateReachableGood_start
#print axioms PPL.Convergence.LDLocal.moderateLivePotential_start_le
#print axioms PPL.Convergence.LDLocal.moderateLiveStageSuperSolution
#print axioms PPL.Convergence.LDLocal.moderateAttemptCostSpec_proved

#check PPL.Convergence.LDLocal.ModerateLiveSingleInteractionSpec

import Leader.PPL.Elim.AttemptCostModerateLive

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# LD(736): moderate single-interaction stage split

Truth audit.

I found no concrete counterexample to ModerateLiveSingleInteractionSpec.  The
literal moderate kernel has the intended five live stages and reachable-good
excludes stuck.  The dummy/recovery service debts and the vulnerable
redirection budgets line up with the potential in
LDLocalAttemptCostModerateLive.

There is, however, one proof-interface mismatch in the CR stages.  The public
crRankStep_proved theorem says that the required edge admits a strictly lower
rank witness.  The private moderate kernel helper attemptCRNextMode is defined
by Classical.choose from the arbitrary-edge, non-strict witness instead.
The concrete drain/repair/sweep/return implementations do make that selected
successor strict on the required edge, but that fact is not exported by the
current public interface.  cleanReady_cost_proved avoids the issue by choosing
from the strict required-edge witness directly.

In this bounded round I therefore split the exact one-letter residual into two
stage-row Props, as permitted by the task:

* ModerateCRStageRows: attackCR and targetCR.
* ModerateSealedControlStageRows: dummyWait, vulnerable, and recovery.

The rest of this file is proved: these two row families assemble exactly to
ModerateLiveSingleInteractionSpec and hence to ModerateAttemptCostSpec.
No horizon/restart/probability residual is added.
-/

/-! ## Checked upstream assets used by the two row families -/

private theorem moderate_crRank_asset :
    CRRankStepSpecCorrected :=
  crRankStep_proved

private theorem moderate_cleanReady_asset :
    CleanReadyCostObligation :=
  cleanReady_cost_proved

private theorem moderate_attemptGood_survivor
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (e : Fin n)
    (hgood : AttemptGood ring F C)
    (hnot : ¬ TaggedDeleted F (stepE ring C e)) :
    AttemptGood ring F (stepE ring C e) :=
  attemptGood_step ring F C e hgood hnot

private theorem moderate_control_rows_asset
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (hSealed : SealedStepSpec)
    (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b) :
    ControlRowSpec hSealed F hb :=
  controlRowSpec_proved hSealed F hb

private theorem moderate_qTrial_asset
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (hSealed : SealedStepSpec)
    (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (x : VulnerableState F)
    (T : Nat) :
    truncatedActiveCostNumerator
        (qStep hSealed F hb) (.active x) T ≤
      n ^ T * (5 * n * F.a) :=
  qTrial_cost_five_na
    hSealed F hb
    (controlRowSpec_proved hSealed F hb)
    x T

/-! ## Stage partition -/

def ModerateCRStage : ModerateStage → Prop
  | .attackCR _ => True
  | .targetCR _ _ => True
  | .dummyWait _ _ => False
  | .vulnerable _ _ => False
  | .recovery _ _ => False
  | .stuck => False

def ModerateSealedControlStage : ModerateStage → Prop
  | .attackCR _ => False
  | .targetCR _ _ => False
  | .dummyWait _ _ => True
  | .vulnerable _ _ => True
  | .recovery _ _ => True
  | .stuck => False

private theorem moderateStage_partition
    (stage : ModerateStage) :
    Or (ModerateCRStage stage)
      (Or (ModerateSealedControlStage stage)
          (stage = .stuck)) := by
  cases stage <;>
    simp [ModerateCRStage, ModerateSealedControlStage]

/-!
## Residual row family 1: the two CR stages

This is narrower than ModerateLiveSingleInteractionSpec.  It contains exactly
the active-child closure and Bellman row when the current stage is attackCR or
targetCR.

The intended direct proof is:
* arbitrary edges: crRankStep_proved.1 plus attemptGood_step;
* the required edge: the concrete chosen attemptCRNextMode must be shown to
  realize the strict decrease guaranteed by crRankStep_proved.2;
* CR completion crosses to the already-budgeted suffix.

The only presently unexported microfact is strictness of that particular
private Classical.choose result on the required edge.
-/
def ModerateCRStageRows : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0)
      (hb : 2 ≤ F.b)
      (C : Config n)
      (hgood : AttemptGood ring F C)
      (stage : ModerateStage),
      ModerateCRStage stage →
      ModerateReachableGood ring F
        (.live C hgood stage) →
      And
        (∀ e a',
          (moderateAttemptKernel ring F).step
              (.live C hgood stage) e =
            .active a' →
          ModerateReachableGood ring F a')
        (n +
            (List.ofFn (fun e : Fin n =>
              attemptNodePotential
                (moderateLivePotential F)
                ((moderateAttemptKernel ring F).step
                  (.live C hgood stage) e))).sum ≤
          n * moderateLivePotential F
            (.live C hgood stage))

/-!
## Residual row family 2: sealed wait, vulnerable trial, recovery

This family covers exactly dummyWait, vulnerable, and recovery.

The intended proof uses:
* hSealed and phaseDebt for dummyWait/recovery;
* controlRowSpec_proved for the attacker child-sum in vulnerable;
* qTrial_cost_five_na as the already-assembled finite-horizon consequence of
  that same vulnerable Bellman row;
* attemptGood_step for every surviving physical child.

At target Ready the raw R_j branch enters recovery while Q redirects R_j to
L_j.  The common moderateRecoveryBudget is exactly the suffix reserve needed
to compare those children.
-/
def ModerateSealedControlStageRows : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0)
      (hb : 2 ≤ F.b)
      (C : Config n)
      (hgood : AttemptGood ring F C)
      (stage : ModerateStage),
      ModerateSealedControlStage stage →
      ModerateReachableGood ring F
        (.live C hgood stage) →
      And
        (∀ e a',
          (moderateAttemptKernel ring F).step
              (.live C hgood stage) e =
            .active a' →
          ModerateReachableGood ring F a')
        (n +
            (List.ofFn (fun e : Fin n =>
              attemptNodePotential
                (moderateLivePotential F)
                ((moderateAttemptKernel ring F).step
                  (.live C hgood stage) e))).sum ≤
          n * moderateLivePotential F
            (.live C hgood stage))

/-! ## Exact assembly -/

/--
The two per-stage row families are exactly sufficient for the residual from
LDLocalAttemptCostModerateLive.  No other semantic assumption is used.
-/
theorem moderateLiveSingleInteraction
    (hCR : ModerateCRStageRows)
    (hRest : ModerateSealedControlStageRows) :
    ModerateLiveSingleInteractionSpec := by
  intro hSealed n ring C0 F hb
  constructor
  · intro a e a' hgood hstep
    cases a with
    | junk C =>
        have hf : False := by
          simpa [ModerateReachableGood] using hgood
        exact False.elim hf
    | live C hstate stage =>
        cases stage with
        | attackCR mode =>
            exact
              (hCR hSealed ring F hb C hstate
                (.attackCR mode)
                True.intro hgood).1 e a' hstep
        | targetCR attackPhase mode =>
            exact
              (hCR hSealed ring F hb C hstate
                (.targetCR attackPhase mode)
                True.intro hgood).1 e a' hstep
        | dummyWait attackPhase targetPhase =>
            exact
              (hRest hSealed ring F hb C hstate
                (.dummyWait attackPhase targetPhase)
                True.intro hgood).1 e a' hstep
        | vulnerable attackPhase targetPhase =>
            exact
              (hRest hSealed ring F hb C hstate
                (.vulnerable attackPhase targetPhase)
                True.intro hgood).1 e a' hstep
        | recovery attackPhase targetPhase =>
            exact
              (hRest hSealed ring F hb C hstate
                (.recovery attackPhase targetPhase)
                True.intro hgood).1 e a' hstep
        | stuck =>
            have hf : False := by
              simpa [ModerateReachableGood] using hgood
            exact False.elim hf
  · unfold AttemptCostSuperSolutionOn
    intro a hgood
    cases a with
    | junk C =>
        have hf : False := by
          simpa [ModerateReachableGood] using hgood
        exact False.elim hf
    | live C hstate stage =>
        cases stage with
        | attackCR mode =>
            exact
              (hCR hSealed ring F hb C hstate
                (.attackCR mode)
                True.intro hgood).2
        | targetCR attackPhase mode =>
            exact
              (hCR hSealed ring F hb C hstate
                (.targetCR attackPhase mode)
                True.intro hgood).2
        | dummyWait attackPhase targetPhase =>
            exact
              (hRest hSealed ring F hb C hstate
                (.dummyWait attackPhase targetPhase)
                True.intro hgood).2
        | vulnerable attackPhase targetPhase =>
            exact
              (hRest hSealed ring F hb C hstate
                (.vulnerable attackPhase targetPhase)
                True.intro hgood).2
        | recovery attackPhase targetPhase =>
            exact
              (hRest hSealed ring F hb C hstate
                (.recovery attackPhase targetPhase)
                True.intro hgood).2
        | stuck =>
            have hf : False := by
              simpa [ModerateReachableGood] using hgood
            exact False.elim hf

/--
Once the two literal stage-row families are discharged, the requested
one-attempt cost theorem is the already-proved live-stage reduction.
-/
theorem moderateAttemptCostSpec_closed
    (hCR : ModerateCRStageRows)
    (hRest : ModerateSealedControlStageRows) :
    ModerateAttemptCostSpec :=
  moderateAttemptCostSpec_proved
    (moderateLiveSingleInteraction hCR hRest)

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.moderateLiveSingleInteraction
#print axioms PPL.Convergence.LDLocal.moderateAttemptCostSpec_closed

#check PPL.Convergence.LDLocal.ModerateCRStageRows
#check PPL.Convergence.LDLocal.ModerateSealedControlStageRows

import Leader.PPL.Elim.AttemptCostLongStep
import Leader.PPL.Elim.AttemptLongTargetCleanReadyDone

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

elab "unfoldAttemptCRInitMode" : tactic => do
  let c := Lean.mkIdent
    ((((((`_private.Leader.PPL.Elim.Attempt).num 0).str "PPL").str
      "Convergence").str "LDLocal").str "attemptCRInitMode")
  let tac ← `(tactic| unfold $c:ident)
  Lean.Elab.Tactic.evalTactic tac

/-! # The two long CR rows

The kernel's next-mode choice stores the nonincrease witness from
`crRankStep_proved`.  The local Bellman rows also need strict decrease for
that exact chosen witness on the required edge.  This file isolates that
choice-specific source fact and proves both rows from it; it does not infer
strictness by comparing distinct valid modes.
-/

/-- Definitionally the same next-mode choice used by `longStep`, exposed so
that its weak specification and the required-edge condition can be stated
without naming the kernel's private helper. -/
noncomputable def longCRNextModeMirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (mode : CRMode)
    (hPB : PPL.Elim.PB ring C)
    (hInterior : CRInteriorFollowers A C)
    (hmode : CRModeHolds A C mode)
    (e : Fin n)
    (hnotDone : ¬ CRDone A (stepE ring C e)) : CRMode :=
  Classical.choose
    (by
      rcases
          (crRankStep_proved ring A C mode hPB hInterior hmode).1 e with
        hdone | hnext
      · exact False.elim (hnotDone hdone)
      · exact hnext)

/-- The exact public facts attached to the kernel's weak next-mode choice. -/
theorem longCRNextModeMirror_spec
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (mode : CRMode)
    (hPB : PPL.Elim.PB ring C)
    (hInterior : CRInteriorFollowers A C)
    (hmode : CRModeHolds A C mode)
    (e : Fin n)
    (hnotDone : ¬ CRDone A (stepE ring C e)) :
    And
      (CRModeHolds A (stepE ring C e)
        (longCRNextModeMirror
          ring A C mode hPB hInterior hmode e hnotDone))
      (crRank A
          (longCRNextModeMirror
            ring A C mode hPB hInterior hmode e hnotDone) ≤
        crRank A mode) := by
  unfold longCRNextModeMirror
  exact
    Classical.choose_spec
      (by
        rcases
            (crRankStep_proved ring A C mode hPB hInterior hmode).1 e with
          hdone | hnext
        · exact False.elim (hnotDone hdone)
        · exact hnext)

/-- The one source fact not supplied by the private kernel choice: at the
required physical edge, the mode selected by that exact weak choice has lower
rank.  The strict existential in `crRankStep_proved` alone does not identify
this `Classical.choose` witness.  This proposition is the precise residual
needed by the two raw-potential CR rows. -/
def LongCRChosenRequiredStrict : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (mode : CRMode)
    (hPB : PPL.Elim.PB ring C)
    (hInterior : CRInteriorFollowers A C)
    (hmode : CRModeHolds A C mode)
    (hnotDone :
      ¬ CRDone A (stepE ring C (crRequiredEdge A mode))),
    crRank A
        (longCRNextModeMirror
          ring A C mode hPB hInterior hmode
          (crRequiredEdge A mode) hnotDone) <
      crRank A mode

/-- A public mirror of the initial CR choice lets the post-target done branch
use the source's rank bound without exposing its private implementation. -/
noncomputable def longCRInitModeMirror
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

theorem longCRInitModeMirror_spec
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n)
    (hPB : PPL.Elim.PB ring D)
    (halive : ¬ EndpointDeleted A D)
    (hclean : ¬ CleanReady A D) :
    And
      (CRModeHolds A D
        (longCRInitModeMirror ring A D hPB halive hclean))
      (crRank A
          (longCRInitModeMirror ring A D hPB halive hclean) ≤
        3 * A.gap) := by
  unfold longCRInitModeMirror
  exact
    Classical.choose_spec
      (crRankInit ring A D hPB
        (by
          intro hdone
          rcases hdone with hdel | hready
          · exact halive hdel
          · exact hclean hready))

/-- Unfolded form of the private long raw potential, used only as a local
definitionally equal view of the row statement. -/
def longCRRawPhiMirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F → Nat
  | .junk _ => 0
  | .live _ _ stage => n * longStageUnits F stage

private theorem longCR_phaseReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hInterior : CRInteriorFollowers A C)
    (hclean : CleanReady A C) :
    PhaseHolds A C .ready :=
  And.intro hInterior hclean

private theorem longCR_phaseNext
    (hSealed : SealedStepSpec)
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (hph : PhaseHolds A C ph)
    (hcurrent : ¬ EndpointDeleted A C)
    (e : Fin n)
    (hnext : ¬ EndpointDeleted A (stepE ring C e)) :
    PhaseHolds A (stepE ring C e)
      (nextSectorPhase A ph e) := by
  rcases hSealed ring A C ph hph hcurrent e with
    hdel | hsurvive
  · exact False.elim (hnext hdel)
  · rcases hsurvive with ⟨ph', hph', htr⟩
    have heq : ph' = nextSectorPhase A ph e := by
      simpa [PhaseTransition] using htr
    rw [heq] at hph'
    exact hph'

/-- Bellman arithmetic for one exceptional scheduler letter. -/
private theorem longCR_oneExceptionAffine
    {n q : Nat}
    (a : Fin n) (f : Fin n → Nat)
    (hq : 0 < q)
    (ha : f a ≤ n * (q - 1))
    (hother : ∀ e, e ≠ a → f e ≤ n * q) :
    n + (List.ofFn f).sum ≤ n * (n * q) := by
  let c := n * q
  let g : Fin n → Nat := fun e => if e = a then f e else c
  have hfg : ∀ e, f e ≤ g e := by
    intro e
    by_cases he : e = a
    · simp [g, he]
    · simpa [g, he] using hother e he
  have hsum0 : (List.ofFn f).sum ≤ (List.ofFn g).sum :=
    ofFn_sum_le f g hfg
  have hsumg : (List.ofFn g).sum = f a + (n - 1) * c := by
    have h :=
      PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const
        a g c (by
          intro e he
          simp [g, he])
    simpa [g] using h
  have hsum : (List.ofFn f).sum ≤ f a + (n - 1) * c := by
    rw [hsumg] at hsum0
    exact hsum0
  have ha' : f a ≤ n * (q - 1) := ha
  have hc : c = n + (n * (q - 1)) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
    subst q
    dsimp [c]
    rw [Nat.mul_succ]
    omega
  have haLt := a.isLt
  have hnpos : 0 < n := by omega
  have hm : n * c = c + (n - 1) * c := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    rw [hk]
    simp [Nat.succ_mul, Nat.add_comm]
  calc
    n + (List.ofFn f).sum
        ≤ n + (n * (q - 1) + (n - 1) * c) := by
          apply Nat.add_le_add_left
          exact Nat.le_trans hsum
            (Nat.add_le_add_right ha' _)
    _ = (n + n * (q - 1)) + (n - 1) * c := by omega
    _ = c + (n - 1) * c := by rw [← hc]
    _ = n * c := hm.symm
    _ = n * (n * q) := by rfl

/-- Exact step equation for a non-done target-CR transition, stated through
the public mirror of the kernel's selected mode. -/
private theorem longTargetCR_notDone_step_mirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (mode : CRMode) (e : Fin n)
    (htag : ¬ TaggedDeleted F (stepE ring C e))
    (hmode : CRModeHolds F.B C mode)
    (hnotDone : ¬ CRDone F.B (stepE ring C e)) :
    (longAttemptKernel ring F).step
        (.live C hgood (.targetCR mode)) e =
      .active
        (.live (stepE ring C e)
          (attemptGood_step ring F C e hgood htag)
          (.targetCR
            (longCRNextModeMirror
              ring F.B C mode hgood.1 hgood.2.2.2
              hmode e hnotDone))) := by
  classical
  simp only [longAttemptKernel]
  unfold longStep
  dsimp only
  rw [dif_neg htag, dif_pos hmode, dif_neg hnotDone]
  rfl

/-- Exact step equation for a non-done attacker-CR transition. -/
private theorem longAttackerCR_notDone_step_mirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase : SectorPhase) (mode : CRMode) (e : Fin n)
    (htag : ¬ TaggedDeleted F (stepE ring C e))
    (hmode : CRModeHolds F.A C mode)
    (hnotDone : ¬ CRDone F.A (stepE ring C e)) :
    (longAttemptKernel ring F).step
        (.live C hgood (.attackerCR targetPhase mode)) e =
      .active
        (.live (stepE ring C e)
          (attemptGood_step ring F C e hgood htag)
          (.attackerCR (nextSectorPhase F.B targetPhase e)
            (longCRNextModeMirror
              ring F.A C mode hgood.1 hgood.2.2.1
              hmode e hnotDone))) := by
  classical
  simp only [longAttemptKernel]
  unfold longStep
  dsimp only
  rw [dif_neg htag, dif_pos hmode, dif_neg hnotDone]
  rfl

/-- Two long CR-stage local rows follow once the kernel's required-edge
choice is known to be strict.  The proof follows `longStep` branch by branch;
the one strict physical edge pays for the scheduler letter, while all other
edges use the weak rank step. -/
theorem longCRStageRowsSpec_of_chosenRequiredStrict
    (hStrict : LongCRChosenRequiredStrict) :
    LongCRStageRowsSpec := by
  intro hSealed n ring C0 F hb hab
  refine And.intro ?_ ?_
  · intro C hgood mode hlegit
    have hmode : CRModeHolds F.B C mode := hlegit
    refine And.intro ?_ ?_
    · intro e a' hstep
      simp only [longAttemptKernel] at hstep
      unfold longStep at hstep
      dsimp only at hstep
      by_cases htag : TaggedDeleted F (stepE ring C e)
      · rw [dif_pos htag] at hstep
        cases hstep
      · rw [dif_neg htag] at hstep
        have hgoodD : AttemptGood ring F (stepE ring C e) :=
          attemptGood_step ring F C e hgood htag
        by_cases hdone : CRDone F.B (stepE ring C e)
        · rw [dif_pos hmode, dif_pos hdone] at hstep
          cases hstep
          unfoldLongAfterTargetStage
          by_cases hA : CleanReady F.A (stepE ring C e)
          · have hBready :=
              longCR_phaseReady F.B (stepE ring C e)
                hgoodD.2.2.2
                (Or.resolve_left hdone (by
                  intro hdel
                  exact htag
                    (endpointB_deleted_tagged
                      F (stepE ring C e) hdel)))
            have hAready :=
              longCR_phaseReady F.A (stepE ring C e)
                hgoodD.2.2.1 hA
            simpa [hA, longStageLegit] using
              And.intro hBready
                (And.intro hAready True.intro)
          · have hBready :=
              longCR_phaseReady F.B (stepE ring C e)
                hgoodD.2.2.2
                (Or.resolve_left hdone (by
                  intro hdel
                  exact htag
                    (endpointB_deleted_tagged
                      F (stepE ring C e) hdel)))
            have hinit :=
              longCRInitModeMirror_spec ring F.A
                (stepE ring C e) hgoodD.1
                (by
                  intro hdel
                  exact htag
                    (endpointA_deleted_tagged
                      F (stepE ring C e) hdel)) hA
            unfoldAttemptCRInitMode
            simpa [longCRInitModeMirror, hA, longStageLegit] using
              And.intro hBready hinit.1
        · rw [dif_pos hmode, dif_neg hdone] at hstep
          cases hstep
          exact
            (longCRNextModeMirror_spec
              ring F.B C mode hgood.1 hgood.2.2.2
              hlegit e hdone).1
    · change
        n +
            (List.ofFn (fun e : Fin n =>
              attemptNodePotLong (longCRRawPhiMirror ring F)
                ((longAttemptKernel ring F).step
                  (.live C hgood (.targetCR mode)) e))).sum ≤
          n * (n *
            (crRank F.B mode + longAttackerCRReserveUnits F))
      have hrpos : 0 < crRank F.B mode :=
        crRank_pos F.B mode
          (crModeHolds_valid F.B C mode hlegit)
      let a := crRequiredEdge F.B mode
      let f : Fin n → Nat := fun e =>
        attemptNodePotLong (longCRRawPhiMirror ring F)
          ((longAttemptKernel ring F).step
            (.live C hgood (.targetCR mode)) e)
      apply longCR_oneExceptionAffine a f
        (by omega)
      · dsimp [f, a]
        by_cases htag : TaggedDeleted F (stepE ring C (crRequiredEdge F.B mode))
        · simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          rw [dif_pos htag]
          simp [attemptNodePotLong, longCRRawPhiMirror]
        · by_cases hdone :
              CRDone F.B (stepE ring C (crRequiredEdge F.B mode))
          · simp only [longAttemptKernel]
            unfold longStep
            dsimp only
            rw [dif_neg htag, dif_pos hmode, dif_pos hdone]
            simp only [attemptNodePotLong, longCRRawPhiMirror]
            unfoldLongAfterTargetStage
            by_cases hA :
                CleanReady F.A
                  (stepE ring C (crRequiredEdge F.B mode))
            · simp [hA, longStageUnits, longLaunchPhaseUnits,
                longLaunchReserveUnits, longAttackerCRReserveUnits]
              apply Nat.mul_le_mul_left n
              try simp only [longAdvanceReserveUnits, longRaceReserveUnits,
                longIncidentReserveUnits, longRetainedReserveUnits,
                longRecoveryReserveUnits]
              omega
            · have hinit :=
                longCRInitModeMirror_spec ring F.A
                  (stepE ring C (crRequiredEdge F.B mode))
                  (attemptGood_step ring F C
                    (crRequiredEdge F.B mode) hgood htag).1
                  (by
                    intro hdel
                    exact htag
                      (endpointA_deleted_tagged F
                        (stepE ring C (crRequiredEdge F.B mode)) hdel)) hA
              have hinitRank :
                  crRank F.A
                      (longCRInitModeMirror ring F.A
                        (stepE ring C (crRequiredEdge F.B mode))
                        (attemptGood_step ring F C
                          (crRequiredEdge F.B mode) hgood htag).1
                        (by
                          intro hdel
                          exact htag
                            (endpointA_deleted_tagged F
                              (stepE ring C (crRequiredEdge F.B mode)) hdel)) hA) ≤
                    3 * F.a := by
                simpa [F.A_gap] using hinit.2
              simp [hA, longStageUnits, longLaunchReserveUnits,
                longAttackerCRReserveUnits]
              unfoldAttemptCRInitMode
              simp only [longCRInitModeMirror] at hinitRank
              apply Nat.mul_le_mul_left n
              try simp only [longAdvanceReserveUnits, longRaceReserveUnits,
                longIncidentReserveUnits, longRetainedReserveUnits,
                longRecoveryReserveUnits]
              omega
          · have hnext :=
              longTargetCR_notDone_step_mirror
                ring F C hgood mode (crRequiredEdge F.B mode)
                htag hlegit hdone
            rw [hnext]
            simp only [attemptNodePotLong, longCRRawPhiMirror,
              longStageUnits]
            have hlt :=
              hStrict ring F.B C mode hgood.1 hgood.2.2.2
                hlegit (by simpa using hdone)
            have hrank :
                crRank F.B
                    (longCRNextModeMirror ring F.B C mode
                      hgood.1 hgood.2.2.2 hlegit
                      (crRequiredEdge F.B mode) hdone) ≤
                  crRank F.B mode - 1 := by omega
            apply Nat.mul_le_mul_left n
            omega
      · intro e hne
        dsimp [f]
        by_cases htag : TaggedDeleted F (stepE ring C e)
        · simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          rw [dif_pos htag]
          simp [attemptNodePotLong, longCRRawPhiMirror]
        · by_cases hdone : CRDone F.B (stepE ring C e)
          · simp only [longAttemptKernel]
            unfold longStep
            dsimp only
            rw [dif_neg htag, dif_pos hmode, dif_pos hdone]
            simp only [attemptNodePotLong, longCRRawPhiMirror]
            unfoldLongAfterTargetStage
            by_cases hA : CleanReady F.A (stepE ring C e)
            · simp [hA, longStageUnits, longLaunchPhaseUnits,
                longLaunchReserveUnits, longAttackerCRReserveUnits]
              apply Nat.mul_le_mul_left n
              try simp only [longAdvanceReserveUnits, longRaceReserveUnits,
                longIncidentReserveUnits, longRetainedReserveUnits,
                longRecoveryReserveUnits]
              omega
            · have hinit :=
                longCRInitModeMirror_spec ring F.A
                  (stepE ring C e)
                  (attemptGood_step ring F C e hgood htag).1
                  (by
                    intro hdel
                    exact htag
                      (endpointA_deleted_tagged F
                        (stepE ring C e) hdel)) hA
              have hinitRank :
                  crRank F.A
                      (longCRInitModeMirror ring F.A
                        (stepE ring C e)
                        (attemptGood_step ring F C e hgood htag).1
                        (by
                          intro hdel
                          exact htag
                            (endpointA_deleted_tagged F
                              (stepE ring C e) hdel)) hA) ≤
                    3 * F.a := by
                simpa [F.A_gap] using hinit.2
              simp [hA, longStageUnits, longLaunchReserveUnits,
                longAttackerCRReserveUnits]
              unfoldAttemptCRInitMode
              simp only [longCRInitModeMirror] at hinitRank
              apply Nat.mul_le_mul_left n
              try simp only [longAdvanceReserveUnits, longRaceReserveUnits,
                longIncidentReserveUnits, longRetainedReserveUnits,
                longRecoveryReserveUnits]
              omega
          · have hnext :=
              longTargetCR_notDone_step_mirror
                ring F C hgood mode e htag hlegit hdone
            rw [hnext]
            simp only [attemptNodePotLong, longCRRawPhiMirror,
              longStageUnits]
            have hweak :=
              (longCRNextModeMirror_spec ring F.B C mode
                hgood.1 hgood.2.2.2 hlegit e hdone).2
            apply Nat.mul_le_mul_left n
            exact Nat.add_le_add_right hweak _
  · intro C hgood targetPhase mode hlegit
    have hphaseB := hlegit.1
    have hmode := hlegit.2
    refine And.intro ?_ ?_
    · intro e a' hstep
      simp only [longAttemptKernel] at hstep
      unfold longStep at hstep
      dsimp only at hstep
      by_cases htag : TaggedDeleted F (stepE ring C e)
      · rw [dif_pos htag] at hstep
        cases hstep
      · rw [dif_neg htag] at hstep
        have hgoodD : AttemptGood ring F (stepE ring C e) :=
          attemptGood_step ring F C e hgood htag
        by_cases hdone : CRDone F.A (stepE ring C e)
        · rw [dif_pos hmode, dif_pos hdone] at hstep
          cases hstep
          have hcurB : ¬ EndpointDeleted F.B C := by
            intro hdel
            exact hgood.2.1 (endpointB_deleted_tagged F C hdel)
          have hnextB :
              ¬ EndpointDeleted F.B (stepE ring C e) := by
            intro hdel
            exact htag
              (endpointB_deleted_tagged F (stepE ring C e) hdel)
          have hphaseB' :=
            longCR_phaseNext hSealed F F.B C targetPhase
              hphaseB hcurB e hnextB
          have hnotA :
              ¬ EndpointDeleted F.A (stepE ring C e) := by
            intro hdel
            exact htag
              (endpointA_deleted_tagged F (stepE ring C e) hdel)
          have hcleanA :
              CleanReady F.A (stepE ring C e) :=
            Or.resolve_left hdone hnotA
          have hAready :=
            longCR_phaseReady F.A (stepE ring C e)
              hgoodD.2.2.1 hcleanA
          exact And.intro hphaseB'
            (And.intro hAready True.intro)
        · rw [dif_pos hmode, dif_neg hdone] at hstep
          cases hstep
          have hcurB : ¬ EndpointDeleted F.B C := by
            intro hdel
            exact hgood.2.1 (endpointB_deleted_tagged F C hdel)
          have hnextB :
              ¬ EndpointDeleted F.B (stepE ring C e) := by
            intro hdel
            exact htag
              (endpointB_deleted_tagged F (stepE ring C e) hdel)
          have hphaseB' :=
            longCR_phaseNext hSealed F F.B C targetPhase
              hphaseB hcurB e hnextB
          have hnext :=
            longCRNextModeMirror_spec ring F.A C mode
              hgood.1 hgood.2.2.1 hmode e hdone
          exact And.intro hphaseB' hnext.1
    · change
        n +
            (List.ofFn (fun e : Fin n =>
              attemptNodePotLong (longCRRawPhiMirror ring F)
                ((longAttemptKernel ring F).step
                  (.live C hgood (.attackerCR targetPhase mode)) e))).sum ≤
          n * (n * (crRank F.A mode + longLaunchReserveUnits F))
      have hrpos : 0 < crRank F.A mode :=
        crRank_pos F.A mode
          (crModeHolds_valid F.A C mode hmode)
      let a := crRequiredEdge F.A mode
      let f : Fin n → Nat := fun e =>
        attemptNodePotLong (longCRRawPhiMirror ring F)
          ((longAttemptKernel ring F).step
            (.live C hgood (.attackerCR targetPhase mode)) e)
      apply longCR_oneExceptionAffine a f
        (by omega)
      · dsimp [f, a]
        by_cases htag : TaggedDeleted F (stepE ring C (crRequiredEdge F.A mode))
        · simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          rw [dif_pos htag]
          simp [attemptNodePotLong, longCRRawPhiMirror]
        · by_cases hdone :
              CRDone F.A (stepE ring C (crRequiredEdge F.A mode))
          · simp only [longAttemptKernel]
            unfold longStep
            dsimp only
            rw [dif_neg htag, dif_pos hmode, dif_pos hdone]
            simp only [attemptNodePotLong, longCRRawPhiMirror,
              longStageUnits, longLaunchPhaseUnits,
              longLaunchReserveUnits]
            apply Nat.mul_le_mul_left n
            omega
          · have hnext :=
              longAttackerCR_notDone_step_mirror
                ring F C hgood targetPhase mode
                (crRequiredEdge F.A mode) htag hmode hdone
            rw [hnext]
            simp only [attemptNodePotLong, longCRRawPhiMirror,
              longStageUnits]
            have hlt :=
              hStrict ring F.A C mode hgood.1 hgood.2.2.1
                hmode (by simpa using hdone)
            have hrank :
                crRank F.A
                    (longCRNextModeMirror ring F.A C mode
                      hgood.1 hgood.2.2.1 hmode
                      (crRequiredEdge F.A mode) hdone) ≤
                  crRank F.A mode - 1 := by omega
            apply Nat.mul_le_mul_left n
            omega
      · intro e hne
        dsimp [f]
        by_cases htag : TaggedDeleted F (stepE ring C e)
        · simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          rw [dif_pos htag]
          simp [attemptNodePotLong, longCRRawPhiMirror]
        · by_cases hdone : CRDone F.A (stepE ring C e)
          · simp only [longAttemptKernel]
            unfold longStep
            dsimp only
            rw [dif_neg htag, dif_pos hmode, dif_pos hdone]
            simp only [attemptNodePotLong, longCRRawPhiMirror,
              longStageUnits, longLaunchPhaseUnits,
              longLaunchReserveUnits]
            apply Nat.mul_le_mul_left n
            omega
          · have hnext :=
              longAttackerCR_notDone_step_mirror
                ring F C hgood targetPhase mode e htag hmode hdone
            rw [hnext]
            simp only [attemptNodePotLong, longCRRawPhiMirror,
              longStageUnits]
            have hweak :=
              (longCRNextModeMirror_spec ring F.A C mode
                hgood.1 hgood.2.2.1 hmode e hdone).2
            apply Nat.mul_le_mul_left n
            exact Nat.add_le_add_right hweak _

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longCRNextModeMirror_spec
#print axioms PPL.Convergence.LDLocal.longCRInitModeMirror_spec
#print axioms PPL.Convergence.LDLocal.longCRStageRowsSpec_of_chosenRequiredStrict

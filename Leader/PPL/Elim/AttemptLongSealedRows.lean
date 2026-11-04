import Leader.PPL.Elim.AttemptLongSealedCorrected

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# L17 long post-CR sealed rows: path-qualified bounded-round reduction

The old semantic-only post-CR package is false: the kernel counterexample
`.race (.live 0) (.live 4)` is semantically legitimate but is not reachable
from the first post-CR cut.  The corrected carrier in
`LDLocalAttemptLongSealedCorrected` is therefore essential.

This file does not reintroduce that false broad quantifier.  Each residual
below is restricted to one of the six post-CR constructors *and* to an actual
descendant of an actual first post-CR cut.  Thus the race residual has exactly
the provenance needed to exclude the refuted shielded `.live 0` state.

The common path dispatcher is proved below.  Once the six stage-local rows
are supplied, it assembles `LongSealedControlStageRowsSpecCorrected` with no
additional semantic or reachability hypothesis.
-/

/-- Every node carried by the corrected post-cut path still satisfies the
cut.  This is just the last field of the inductive carrier. -/
theorem retryActiveAfterCutCorrected_cut_true_rows
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root a : A)
    (h : RetryActiveAfterCutCorrected K cut root a) :
    cut a = true := by
  cases h with
  | root hroot =>
      exact hroot
  | step h e hstep hcut =>
      exact hcut

/--
Live-wait residual, path-qualified.

Source fact: `SealedStepSpec` transports both sector witnesses through
`nextSectorPhase`; at target/attacker Ready the two distinguished physical
letters are the same launch/incoming exceptions used by the compiled moderate
row.  The long suffix reserve is `longAdvanceReserveUnits F`.
-/
def LongLiveWaitPostCarrierResidual : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s carrier C
        (hgoodC : AttemptGood ring F C)
        (targetPhase attackPhase : SectorPhase),
        AttemptGood ring F s ->
        RetryFirstCutReachableCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          ((longAttemptKernel ring F).start s)
          carrier ->
        RetryActiveAfterCutCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          carrier
          (.live C hgoodC
            (.liveWait targetPhase attackPhase)) ->
        LongPostCarrierPackageCorrected
          ring F
          (.live C hgoodC
            (.liveWait targetPhase attackPhase))

/--
Advance residual, path-qualified.

Source fact: the attacker phase is a positive `.live p` strictly before
`F.a - 2*F.b`; its unique service letter decreases
`longAdvancePhaseUnits` by one, and the crossing letter lands in race with
the preallocated `longRaceReserveUnits F`.
-/
def LongAdvancePostCarrierResidual : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s carrier C
        (hgoodC : AttemptGood ring F C)
        (targetPhase attackPhase : SectorPhase),
        AttemptGood ring F s ->
        RetryFirstCutReachableCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          ((longAttemptKernel ring F).start s)
          carrier ->
        RetryActiveAfterCutCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          carrier
          (.live C hgoodC
            (.advance targetPhase attackPhase)) ->
        LongPostCarrierPackageCorrected
          ring F
          (.live C hgoodC
            (.advance targetPhase attackPhase))

/--
Race residual, path-qualified; this is the row on which the old statement
failed.

Source fact: actual first-cut provenance starts the target phase at Ready and
advances it only by `nextSectorPhase F.B`.  Hence a shielded target live
phase has positive offset; equivalently the target recovery debt is at most
`2*F.b-2`.  The refutation's shielded `.live 0` state therefore cannot
occur here.  The remaining Bellman row uses the predictable `L_j F` /
`R_j F` exceptions.
-/
def LongRacePostCarrierResidual : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s carrier C
        (hgoodC : AttemptGood ring F C)
        (targetPhase attackPhase : SectorPhase),
        AttemptGood ring F s ->
        RetryFirstCutReachableCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          ((longAttemptKernel ring F).start s)
          carrier ->
        RetryActiveAfterCutCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          carrier
          (.live C hgoodC
            (.race targetPhase attackPhase)) ->
        LongPostCarrierPackageCorrected
          ring F
          (.live C hgoodC
            (.race targetPhase attackPhase))

/--
Incident residual, path-qualified.

Source fact: incident starts with the target phase Ready; only `L_j F` and
`R_j F` are exceptional.  The former enters retained control and the latter
enters recovery with target phase `.live 1`, whose debt is exactly
`2*F.b-2`.
-/
def LongIncidentPostCarrierResidual : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s carrier C
        (hgoodC : AttemptGood ring F C)
        (attackPhase : SectorPhase),
        AttemptGood ring F s ->
        RetryFirstCutReachableCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          ((longAttemptKernel ring F).start s)
          carrier ->
        RetryActiveAfterCutCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          carrier
          (.live C hgoodC
            (.incident attackPhase)) ->
        LongPostCarrierPackageCorrected
          ring F
          (.live C hgoodC
            (.incident attackPhase))

/--
Retained residual, path-qualified.

Source fact: `longStageLegit` supplies the unshielded target source and the
attacker live suffix.  The physical child sum is the existing
`controlRetainedBellman` / `retainedTrial_cost_nr` row, with
`longRecoveryReserveUnits F` paying the raw Ready-time recovery port.
-/
def LongRetainedPostCarrierResidual : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s carrier C
        (hgoodC : AttemptGood ring F C)
        (targetPhase attackPhase : SectorPhase),
        AttemptGood ring F s ->
        RetryFirstCutReachableCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          ((longAttemptKernel ring F).start s)
          carrier ->
        RetryActiveAfterCutCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          carrier
          (.live C hgoodC
            (.retained targetPhase attackPhase)) ->
        LongPostCarrierPackageCorrected
          ring F
          (.live C hgoodC
            (.retained targetPhase attackPhase))

/--
Recovery residual, path-qualified.

Source fact: `longStageLegit` already bounds the target phase debt by
`longRecoveryReserveUnits F`; one target service reduces `phaseDebt` by
one, all other letters stutter that debt, and reaching Ready returns `.retry`
with zero continuation potential.
-/
def LongRecoveryPostCarrierResidual : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s carrier C
        (hgoodC : AttemptGood ring F C)
        (targetPhase attackPhase : SectorPhase),
        AttemptGood ring F s ->
        RetryFirstCutReachableCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          ((longAttemptKernel ring F).start s)
          carrier ->
        RetryActiveAfterCutCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          carrier
          (.live C hgoodC
            (.recovery targetPhase attackPhase)) ->
        LongPostCarrierPackageCorrected
          ring F
          (.live C hgoodC
            (.recovery targetPhase attackPhase))

/--
Complete path/stage dispatcher.

This theorem is the bounded-round assembly: no broad semantic stage is used.
The current node is known to satisfy `longPostCRCutCorrected = true`, so
target-CR, attacker-CR, stuck, and junk are impossible; the remaining six
constructors are discharged by their path-qualified rows above.
-/
theorem longSealedControlStageRowsSpecCorrected_of_stage_residuals
    (hLiveWait : LongLiveWaitPostCarrierResidual)
    (hAdvance : LongAdvancePostCarrierResidual)
    (hRace : LongRacePostCarrierResidual)
    (hIncident : LongIncidentPostCarrierResidual)
    (hRetained : LongRetainedPostCarrierResidual)
    (hRecovery : LongRecoveryPostCarrierResidual) :
    LongSealedControlStageRowsSpecCorrected := by
  unfold LongSealedControlStageRowsSpecCorrected
  intro hSealed n ring C0 F hb hab
  intro s carrier a hgood hfirst hafter

  have hcut :
      longPostCRCutCorrected F a = true :=
    retryActiveAfterCutCorrected_cut_true_rows
      (longAttemptKernel ring F)
      (longPostCRCutCorrected F)
      carrier a hafter

  cases a with
  | junk C =>
      simp [longPostCRCutCorrected] at hcut
  | live C hgoodC stage =>
      cases stage with
      | targetCR mode =>
          simp [longPostCRCutCorrected] at hcut
      | attackerCR targetPhase mode =>
          simp [longPostCRCutCorrected] at hcut
      | liveWait targetPhase attackPhase =>
          exact
            hLiveWait hSealed ring F hb hab
              s carrier C hgoodC
              targetPhase attackPhase
              hgood hfirst hafter
      | advance targetPhase attackPhase =>
          exact
            hAdvance hSealed ring F hb hab
              s carrier C hgoodC
              targetPhase attackPhase
              hgood hfirst hafter
      | race targetPhase attackPhase =>
          exact
            hRace hSealed ring F hb hab
              s carrier C hgoodC
              targetPhase attackPhase
              hgood hfirst hafter
      | incident attackPhase =>
          exact
            hIncident hSealed ring F hb hab
              s carrier C hgoodC attackPhase
              hgood hfirst hafter
      | retained targetPhase attackPhase =>
          exact
            hRetained hSealed ring F hb hab
              s carrier C hgoodC
              targetPhase attackPhase
              hgood hfirst hafter
      | recovery targetPhase attackPhase =>
          exact
            hRecovery hSealed ring F hb hab
              s carrier C hgoodC
              targetPhase attackPhase
              hgood hfirst hafter
      | stuck =>
          simp [longPostCRCutCorrected] at hcut

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.retryActiveAfterCutCorrected_cut_true_rows
#print axioms PPL.Convergence.LDLocal.longSealedControlStageRowsSpecCorrected_of_stage_residuals


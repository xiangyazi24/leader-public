import Leader.PPL.MainTheorem.PaddingInterface
import Leader.PPL.Modes.MidEntryRetimedRooted
import Leader.PPL.Modes.MidEntryWaveResetFrontierClosed
import Leader.PPL.Modes.MidEntryWaveTTLDebtClosed
import Leader.PPL.Modes.SignalLineageClosed
import Leader.PPL.Modes.SignalAbsorptionLottery
import Leader.PPL.Modes.StoppedClockSuffixFreeze
import Leader.PPL.Probability.LotteryCounts
import Leader.PPL.Probability.LotteryMoment
import Leader.PPL.Probability.EncounterProjection

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1L5iWaveDebtExport.lean`, namespace `PPL.Superseded.LogWindow`: `theorem1L5iPaddedBound_proved`.
-/

/-!
# Lemma 5(i) export through the leader-wave debt route

This file wires the two leader-wave one-step invariants
(`Lemma5iLeaderWaveResetFrontierOneStep`, `Lemma5iLeaderWaveTTLDebtOneStep`)
into the padded Lemma 5(i) bound:

1. the two one-step rows give the wave residual
   (`lemma5iRetimedTraversalABCSweepResidualWave_of_debtRows`);
2. the wave residual gives the corrected current-max traversal projection
   (`lemma5iTraversalProjection_of_residualWave`), whose first-max count is the
   traversal half of `Lemma5iSweepMidCountRetimed`;
3. the mid half comes from the closed mid current-max suffix bound
   (`lemma5iRetimedMidCurrentMaxSuffixBound_closed`);
4. `lemma5iWordBound_of_retimedCounts_noResetLineage` turns the two counts into
   `Lemma5iWordBound`, which is the bridge consumed by
   `theorem1L5iPaddedBound_of_lemma5Bridge`.

The two first-max count lemmas are private in their defining modules; they are
reached by their mangled private names (tactic `haveLemma5Private`), so no
accepted module is edited.
-/

namespace PPL.Modes.Lemma5

set_option autoImplicit false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-- Bind `h` to a private declaration `name` of module `Leader.PPL.Modes.<mod>`
(namespace `PPL.Modes.Lemma5`), the same mangled-name pattern as
`unfoldRetimedTraversalAux` in `Lemma5iRetimedCurrentMax.lean`. -/
elab "haveLemma5Private " h:ident mod:ident name:ident : tactic => do
  let c := Lean.mkIdent
    ((((((((`_private.Leader.PPL.Modes).str mod.getId.toString).num 0).str
      "PPL").str "Modes").str "Lemma5").str name.getId.toString))
  let tac ← `(tactic| have $h:ident := $c:ident)
  Lean.Elab.Tactic.evalTactic tac

/-- Both retimed counts from the corrected current-max traversal projection and
the closed mid current-max suffix bound. -/
theorem lemma5iSweepMidCountRetimed_of_currentMaxBCCorrected
    (hprojection :
      Lemma5iRetimedTraversalCurrentMaxSuffixProjectionBCCorrected) :
    Lemma5iSweepMidCountRetimed := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz hlineage hclock hmarked
  intro hpredict hhead hlottery
  haveLemma5Private hstrong MidEntryTraversalRotation
    lemma5iRetimedTraversalCount_of_currentMaxBC_corrected_strong
  haveLemma5Private hmidCount MidEntryRetimedCurrentMax q19708MidFirstMaxCount
  have hTraversal :=
    hstrong
      hprojection
      hn3 hpsi hkappa hnpow
      ring C hlineage
      hmarked hpredict hhead hlottery
  have hMid :=
    hmidCount
      lemma5iRetimedMidCurrentMaxSuffixBound_closed
      hn3 hpsi hkappa hnpow
      ring C hcnz
      hclock hmarked hpredict hhead hlottery
  constructor
  · omega
  · have hscale :
        n * lemma5iRetimedMidClockFailureCount ring C <=
          lemma5iRetimedMidClockFailureCount ring C * 2 ^ psi := by
      rw [Nat.mul_comm n]
      exact Nat.mul_le_mul_left _ hnpow
    omega

/-- Lemma 5(i) word bound from the two leader-wave one-step rows. -/
theorem lemma5iSweepMidCountRetimed_of_waveDebtRows
    (hReset : Lemma5iLeaderWaveResetFrontierOneStep)
    (hTTL : Lemma5iLeaderWaveTTLDebtOneStep) :
    Lemma5iSweepMidCountRetimed :=
  lemma5iSweepMidCountRetimed_of_currentMaxBCCorrected
    (lemma5iTraversalProjection_of_residualWave
      (lemma5iRetimedTraversalABCSweepResidualWave_of_debtRows
        hReset hTTL))

/-- The retimed counts with both wave rows discharged. -/
theorem lemma5iSweepMidCountRetimed_waveDebt_proved :
    Lemma5iSweepMidCountRetimed :=
  lemma5iSweepMidCountRetimed_of_waveDebtRows
    lemma5iLeaderWaveResetFrontierOneStep_proved
    lemma5iLeaderWaveTTLDebtOneStep_proved

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iSweepMidCountRetimed_of_currentMaxBCCorrected
#print axioms PPL.Modes.Lemma5.lemma5iSweepMidCountRetimed_waveDebt_proved

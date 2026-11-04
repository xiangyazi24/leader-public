import Leader.PPL.PsiAtLeastN.SafeRows
import Leader.PPL.ReachCPB.CappedNoUpper
import Leader.PPL.ReachCPB.Deterministic
import Leader.PPL.MainTheorem.ReachCPBPaddedClosed
import Leader.PPL.MainTheorem.MidEntryWaveDebt
import Leader.PPL.MainTheorem.OneLeaderDynamicPadding
import Leader.PPL.MainTheorem.WindowSPLEntryDynamicPadding
import Leader.PPL.MainTheorem.GeneralPaddedRows
import Leader.PPL.MainTheorem.GeneralFirstHit

/-!
# P_PL Theorem 1 on `n ≤ psi`: the padded phase bounds

The padded interfaces of `PPL.PsiBelowN` (`Leader/PPL/PsiBelowN/PaddedRows.lean`)
with the domain premise `psi < n` replaced by `n ≤ psi`.  For L16, L5(i),
L5(ii) and L17 the premise is never consumed, and the interfaces here are
special cases of `Leader/PPL/MainTheorem/GeneralFixedCut.lean` and
`Leader/PPL/MainTheorem/GeneralPaddedRows.lean` (P_PL Theorem 1 cleanup,
phase 2, step 6a; this file used to carry full copies of the proofs).
The L18 row is replaced by the safe event `theorem1Bad18SafeB`: the
interface `Theorem1L18SafeFirstHitPhaseBound`, the cover
`theorem1L18SafeFirstHitStop_cover` and the padded bound
`theorem1L18SafeDynamicPaddedBound_of_phaseBound`; the last two are special
cases of `Leader/PPL/MainTheorem/GeneralFirstHit.lean` (step 6c).

Coefficients (12, 8, 4, 1, 1) and horizons are unchanged.
-/

namespace PPL.PsiAtLeastN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

local instance theorem1PaddedLiteralL1Decidable
    {n : Nat} (C : PPL.LiteralElimConfig n) :
    Decidable (PPL.LiteralL1 C) :=
  theorem1LiteralL1Decidable C

/-! ## L16 -/

theorem theorem1L16PaddedBound_of_mismatchWitness_core
    (hMismatchCanon :
      PPL.Convergence.ReachCPB.Lemma16MismatchWitnessCappedSpec)
    (hcore : PPL.lemma4_deterministic_core) :
    Theorem1L16PaddedBound := by
  intro n psi hn3 hpsi hnpow _ ring C0
  exact
    PPL.Theorem1General.theorem1L16PaddedBound_of_mismatchWitness_core
      hMismatchCanon hcore hn3 hpsi hnpow ring C0

/-- Theorem 1, L16 padded bound on `n ≤ psi`, unconditionally. -/
theorem theorem1L16PaddedBound_proved :
    Theorem1L16PaddedBound :=
  theorem1L16PaddedBound_of_mismatchWitness_core
    PPL.Convergence.ReachCPB.lemma16MismatchWitnessCappedSpec_proved
    PPL.lemma4_deterministic_core_proved

/-! ## L5(i) -/

/--
Static L5(i) padding.

Only the Lemma-5(i) component is required here.  The clock/tree/lineage
interfaces remain explicit; the unrelated Lemma-5(ii) component is not a
premise of this theorem.
-/
theorem theorem1L5iPaddedBound_of_lemma5Bridge
    (hclock :
      PPL.Probability.StoppedClockSuffixBoundsCorrected)
    (hmarked :
      PPL.Modes.Lemma9.ModeStoppedTreeTransfer)
    (hbridge :
      ∀ {n psi kappa : Nat}
        (hn3 : 3 ≤ n)
        (hpsi : 2 ≤ psi)
        (hkappa : 48 * psi ≤ kappa)
        (hnpow : n ≤ 2 ^ psi)
        (ring : DirectedRing n)
        (C : Config n psi kappa),
        PPL.Modes.Lemma5.neverLeaderless ring C →
        PPL.Modes.SignalLineage.SignalLineageOwnership
            (psi := psi)
            (kappa := kappa)
            ring →
        PPL.Probability.StoppedClockSuffixBoundsCorrected →
        PPL.Modes.Lemma9.ModeStoppedTreeTransfer →
        PPL.Probability.PredictableHostTails →
        PPL.Probability.WLGHeadOffsetBounds →
        PPL.Probability.LotteryCountBounds →
        PPL.Modes.Lemma5.Lemma5iWordBound ring C)
    (hlineage :
      forall {n psi kappa : Nat}
        (ring : DirectedRing n),
        PPL.Modes.SignalLineage.SignalLineageOwnership
            (psi := psi)
            (kappa := kappa)
            ring) :
    Theorem1L5iPaddedBound := by
  intro n psi hn3 hpsi hnpow _ ring C0
  exact
    PPL.Theorem1General.theorem1L5iPaddedBound_of_lemma5Bridge
      hclock hmarked hbridge hlineage hn3 hpsi hnpow ring C0

-- [copied from Leader/PPL/MainTheorem/MidEntryWaveDebt.lean:111-120]
/-- The padded Lemma 5(i) bound, with every bridge input discharged. -/
theorem theorem1L5iPaddedBound_proved :
    Theorem1L5iPaddedBound :=
  theorem1L5iPaddedBound_of_lemma5Bridge
    PPL.Probability.stoppedClockSuffixBoundsCorrected
    PPL.Modes.Lemma9.modeStoppedTreeTransfer
    (PPL.Modes.Lemma5.lemma5iWordBound_of_retimedCounts_noResetLineage
      PPL.Modes.Lemma5.lemma5iSweepMidCountRetimed_waveDebt_proved)
    (fun ring => PPL.Modes.SignalLineage.signalLineageOwnership ring)

/-! ## L17 -/

-- [copied from Leader/PPL/MainTheorem/PaddingInterface.lean:565-628]
/--
Exact adapter still missing between the earlier intended first-C_mid cut and the
generic dynamic padding theorem.

A producer from theorem1FirstHitCut must export three facts at the full-word
prefix level:

* the stopping prefixes are prefix-free;
* every stopped endpoint is a PB start for literal Lemma 17, and the exact
  H17-letter countP miss numerator is bounded by L17's l17FailureCount;
* every global theorem1Bad17B word factors as stopped prefix ++ H17 phase ++
  arbitrary pad, with that exact phase marked bad.

The count comparison is deliberately an inequality rather than an equality:
L17's current numerator is a stopping-tree wordSum, while
Theorem1DynamicCutPadding consumes List.countP on allSchedules.
-/
def Theorem1L17FirstHitCutAdapter : Prop :=
  ∀ {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hge : n ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)),
    ∃ stop : DetSchedule n → Bool,
      (∀ p q : DetSchedule n,
        stop p = true →
        stop q = true →
        List.IsPrefix p q →
        p = q) ∧
      (∀ p : DetSchedule n,
        stop p = true →
        p.length + theorem1H17 n ≤
            theorem1Horizon n psi →
        PPL.Elim.PB ring
            (PPL.Elim.viewConfig
              (PPL.Probability.runPPL
                ring C0 p)) ∧
          (allSchedules n
              (theorem1H17 n)).countP
              (theorem1L17PhaseBad
                ring C0 p) ≤
            PPL.Convergence.L17.l17FailureCount
              theorem1C17 ring
              (PPL.Elim.viewConfig
                (PPL.Probability.runPPL
                  ring C0 p))) ∧
      (∀ word : DetSchedule n,
        word ∈
            allSchedules n
              (theorem1Horizon n psi) →
        theorem1Bad17B ring C0 word = true →
        ∃ p : DetSchedule n,
          ∃ phase : DetSchedule n,
            ∃ pad : DetSchedule n,
              stop p = true ∧
                phase ∈
                  allSchedules n
                    (theorem1H17 n) ∧
                  word = p ++ phase ++ pad ∧
                    theorem1L17PhaseBad
                      ring C0 p phase = true)

/--
Coefficient-preserving dynamic L17 padding once the first-hit adapter is
available.  The phase estimate itself is unconditional on main:
lemma17_wordBound_closed supplies it at theorem1C17 = 862592.
-/
theorem theorem1L17DynamicPaddedBound_of_cutPadding
    (hCutPadding : Theorem1DynamicCutPadding)
    (hCut : Theorem1L17FirstHitCutAdapter) :
    Theorem1L17DynamicPaddedBound := by
  intro n psi hn3 hpsi hnpow hge ring C0
  exact
    PPL.Theorem1General.theorem1L17DynamicPaddedBound_of_cutPadding
      hCutPadding hn3 hpsi hnpow ring C0
      (hCut hn3 hpsi hnpow hge ring C0)

theorem theorem1L17FirstHitStop_cover
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hge : n ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (hword :
      word ∈
        allSchedules n
          (theorem1Horizon n psi))
    (hbad :
      theorem1Bad17B
        ring C0 word = true) :
    ∃ p : DetSchedule n,
      ∃ phase : DetSchedule n,
        ∃ pad : DetSchedule n,
          theorem1L17FirstHitStop
              ring C0 p = true ∧
            phase ∈
              allSchedules n
                (theorem1H17 n) ∧
            word = p ++ phase ++ pad ∧
            theorem1L17PhaseBad
              ring C0 p phase = true :=
  PPL.Theorem1General.theorem1L17FirstHitStop_cover
    hn3 hpsi hnpow ring C0 word hword hbad

theorem theorem1L17FirstHitCutAdapter_proved :
    Theorem1L17FirstHitCutAdapter := by
  intro n psi hn3 hpsi hnpow _ ring C0
  exact
    PPL.Theorem1General.theorem1L17FirstHitCut_proved
      hn3 hpsi hnpow ring C0

-- [copied from Leader/PPL/MainTheorem/OneLeaderDynamicPadding.lean:1294-1300]
theorem theorem1L17DynamicPaddedBound_proved :
    Theorem1L17DynamicPaddedBound :=
  theorem1L17DynamicPaddedBound_of_cutPadding
    theorem1DynamicCutPadding_proved
    theorem1L17FirstHitCutAdapter_proved

/-! ## L5(ii) -/

theorem theorem1L5iiDynamicPaddedBound_proved :
    Theorem1L5iiDynamicPaddedBound := by
  intro n psi hn3 hpsi hnpow _ ring C0
  exact
    PPL.Theorem1General.theorem1L5iiDynamicPaddedBound_proved
      hn3 hpsi hnpow ring C0

/-! ## Safe L18 -/

/-- Every word with the safe L18 bad event factors as a first-`C_mid` stopped
prefix, an `H5(ii)` phase that is safe-L18 bad, and a pad
(`PPL.Theorem1General.theorem1L18FirstHitStop_cover_at` for `L18SafeAt`). -/
theorem theorem1L18SafeFirstHitStop_cover
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (hword :
      word ∈
        allSchedules n
          (theorem1Horizon n psi))
    (hbad :
      theorem1Bad18SafeB ring C0 word = true) :
    ∃ p : DetSchedule n,
      ∃ phase : DetSchedule n,
        ∃ pad : DetSchedule n,
          theorem1L17FirstHitStop ring C0 p = true ∧
            phase ∈
              allSchedules n
                (theorem1H5ii n psi) ∧
            word = p ++ phase ++ pad ∧
            theorem1L18SafeFirstHitPhaseBad
              ring C0 p phase = true := by
  rw [theorem1Bad18SafeB_eq] at hbad
  obtain ⟨p, phase, pad, hstop, hmem, hfactor, hphase⟩ :=
    PPL.Theorem1General.theorem1L18FirstHitStop_cover_at
      (fun root C => decide (L18SafeAt ring root C))
      hn3 hpsi ring C0 word hword hbad
  refine ⟨p, phase, pad, hstop, hmem, hfactor, ?_⟩
  rw [theorem1L18SafeFirstHitPhaseBad_eq]
  exact hphase

/-- The safe L18 phase interface at the dynamic first-hit cut, on
`n ≤ psi`: at most `1/n` of the `H5(ii)` phases after a stopped prefix are
safe-L18 bad. -/
def Theorem1L18SafeFirstHitPhaseBound : Prop :=
  forall {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hge : n <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p : DetSchedule n),
    theorem1L17FirstHitStop ring C0 p = true ->
    p.length + theorem1H5ii n psi <=
      theorem1Horizon n psi ->
    n *
        (allSchedules n
          (theorem1H5ii n psi)).countP
          (theorem1L18SafeFirstHitPhaseBad
            ring C0 p) <=
      n ^ theorem1H5ii n psi

/-- The padded safe L18 bound from the phase interface
(`PPL.Theorem1General.theorem1L18DynamicPaddedBound_at` for `L18SafeAt`). -/
theorem theorem1L18SafeDynamicPaddedBound_of_phaseBound
    (hphase : Theorem1L18SafeFirstHitPhaseBound) :
    Theorem1L18SafeDynamicPaddedBound := by
  intro n psi hn3 hpsi hnpow hge ring C0
  have hbad :
      theorem1Bad18SafeB ring C0 =
        PPL.Theorem1General.theorem1Bad18Gen ring
          (fun root C => decide (L18SafeAt ring root C)) C0 :=
    funext (theorem1Bad18SafeB_eq ring C0)
  rw [hbad]
  refine
    PPL.Theorem1General.theorem1L18DynamicPaddedBound_at
      ring _ hn3 hpsi C0 ?_
  intro p hp hlen
  have hphaseEq :
      theorem1L18SafeFirstHitPhaseBad ring C0 p =
        PPL.Theorem1General.theorem1L18FirstHitPhaseBadGen ring
          (fun root C => decide (L18SafeAt ring root C)) C0 p :=
    funext (theorem1L18SafeFirstHitPhaseBad_eq ring C0 p)
  rw [← hphaseEq]
  exact hphase hn3 hpsi hnpow hge ring C0 p hp hlen

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.theorem1L16PaddedBound_proved
#print axioms PPL.PsiAtLeastN.theorem1L5iPaddedBound_proved
#print axioms PPL.PsiAtLeastN.theorem1L17DynamicPaddedBound_proved
#print axioms PPL.PsiAtLeastN.theorem1L5iiDynamicPaddedBound_proved
#print axioms PPL.PsiAtLeastN.theorem1L18SafeDynamicPaddedBound_of_phaseBound

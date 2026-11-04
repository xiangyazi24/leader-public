import Leader.PPL.MainTheorem.GeneralFixedCut
import Leader.PPL.MainTheorem.GeneralQuietWindowFit
import Leader.PPL.ReachCPB.CappedNoUpper
import Leader.PPL.ReachCPB.Deterministic
import Leader.PPL.MainTheorem.ReachCPBPaddedClosed
import Leader.PPL.MainTheorem.MidEntryWaveDebt
import Leader.PPL.MainTheorem.OneLeaderDynamicPadding
import Leader.PPL.MainTheorem.WindowSPLEntryDynamicPadding

/-!
# P_PL Theorem 1, general padded bounds for L5(i), L17 and L5(ii)

The padded phase bounds of the Theorem 1 chain at one `(n, psi)` with
`n ≥ 3`, `psi ≥ 2`, `n ≤ 2 ^ psi` and no domain premise: static L5(i)
padding, the L17 first-hit cut adapter and the dynamic L17 bound, and the
dynamic L5(ii) bound.  Coefficients (8, 1, 4) and horizons are those of the
chain.

The `psi < n` chain (`PsiBelowN/PaddedRows`) and the `n ≤ psi` chain
(`PsiAtLeastN/SafePaddedRows`) each carried a copy of these proofs with its
domain premise threaded and never consumed (the only consumer was the
quiet-window seam, see `Theorem1General/Steps.lean`).  Their interfaces now
follow from the lemmas below; their statements are unchanged.

P_PL Theorem 1 cleanup, phase 2, step 6a.
-/

namespace PPL.Theorem1General

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

local instance theorem1PaddedLiteralL1Decidable
    {n : Nat} (C : PPL.LiteralElimConfig n) :
    Decidable (PPL.LiteralL1 C) :=
  theorem1LiteralL1Decidable C

/-- Static L5(i) padding at one `(n, psi)`, with no domain premise.  Only the
Lemma-5(i) component is required; the clock/tree/lineage interfaces remain
explicit. -/
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
            ring)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    n *
        (allSchedules n
          (theorem1Horizon n psi)).countP
            (theorem1Bad5iB ring C0) <=
      8 * n ^ theorem1Horizon n psi := by

  let bad :
      DetSchedule n ->
      DetSchedule n ->
      Bool :=
    fun pre phase =>
      PPL.Convergence.ReachCPB.reachesCPB ring C0 pre &&
        !(PPL.Modes.Lemma5.reachesAux
          ring
          PPL.Modes.Lemma5.midPhysicalB
          (PPL.Probability.runPPL
            ring C0 pre)
          phase)

  have hATH :
      theorem1H16 n psi +
          theorem1H5i n <=
        theorem1Horizon n psi := by
    rw [theorem1Horizon_eq_phase_sum]
    omega

  have hphase :
      forall pre : DetSchedule n,
        pre ∈
            allSchedules n
              (theorem1H16 n psi) ->
        n *
            (allSchedules n
              (theorem1H5i n)).countP
              (bad pre) <=
          8 * n ^ theorem1H5i n := by
    intro pre _hpre
    cases hp :
        PPL.Convergence.ReachCPB.reachesCPB ring C0 pre with
    | false =>
        simp [bad, hp]
    | true =>
        let D :
            Config n psi
              (theorem1Kappa psi) :=
          PPL.Probability.runPPL
            ring C0 pre

        have hdec :
            decide (CPB ring D) = true := by
          dsimp [D]
          rw [←
            PPL.Convergence.ReachCPB.reachesCPB_eq_endpoint
                hn3 hpsi ring C0 pre]
          exact hp

        have hCPB :
            CPB ring D :=
          of_decide_eq_true hdec

        have hcnz :
            PPL.Modes.Lemma5.neverLeaderless ring D :=
          theorem1CPB_neverLeaderless
            hn3 hpsi ring D hCPB

        have hword :
            PPL.Modes.Lemma5.Lemma5iWordBound ring D :=
          hbridge
            hn3 hpsi
            (theorem1Kappa_ge_48_mul psi)
            hnpow ring D hcnz
            (hlineage ring)
            hclock hmarked
            PPL.Probability.predictableHostTails
            PPL.Probability.wlgHeadOffsetBounds
            PPL.Probability.lotteryCountBounds

        simpa
          [bad, hp,
            PPL.Modes.Lemma5.Lemma5iWordBound,
            PPL.Modes.Lemma5.lemma5iFailureCount,
            theorem1H5i, D]
          using hword

  have hpad :=
    theorem1_fixedCutPaddedBound
      (n := n)
      (A := theorem1H16 n psi)
      (T := theorem1H5i n)
      (H := theorem1Horizon n psi)
      (c := 8)
      hATH bad hphase

  have hfun :
      theorem1Bad5iB ring C0 =
        fun word => theorem1Bad5iB ring C0 word := rfl
  rw [hfun]
  simpa
    [bad,
      theorem1Bad5iB,
      theorem1Block16,
      theorem1Block5i,
      theorem1State16]
    using hpad

/-- The first-hit cut adapter for L17 at one `(n, psi, ring, C0)`: a
prefix-free stopping rule whose stopped endpoints are PB starts with the L17
phase miss count bounded by `l17FailureCount`, and which covers every
`theorem1Bad17B` word.  The `Theorem1L17FirstHitCutAdapter` interfaces of the
`PsiBelowN` and `PsiAtLeastN` chains are this statement under their domain
premise. -/
def theorem1L17FirstHitCutAt
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) : Prop :=
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

/-- Coefficient-preserving dynamic L17 padding at one `(n, psi)` once the
first-hit adapter is available there; the phase estimate is
`lemma17_wordBound_closed` at `theorem1C17 = 862592`. -/
theorem theorem1L17DynamicPaddedBound_of_cutPadding
    (hCutPadding : Theorem1DynamicCutPadding)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (hCut : theorem1L17FirstHitCutAt ring C0) :
    n *
        (allSchedules n
          (theorem1Horizon n psi)).countP
            (theorem1Bad17B ring C0) <=
      n ^ theorem1Horizon n psi := by
  obtain
      ⟨stop, hfree, hlocal, hcover⟩ :=
    hCut

  have hphase :
      ∀ p : DetSchedule n,
        stop p = true →
        p.length + theorem1H17 n ≤
            theorem1Horizon n psi →
        n *
            (allSchedules n
              (theorem1H17 n)).countP
              (theorem1L17PhaseBad
                ring C0 p) ≤
          1 * n ^ theorem1H17 n := by
    intro p hp hlen
    rcases hlocal p hp hlen with
      ⟨hPB, hcount⟩
    let E : PPL.LiteralElimConfig n :=
      PPL.Elim.viewConfig
        (PPL.Probability.runPPL ring C0 p)
    have hclosed :=
      PPL.Convergence.L17.lemma17_wordBound_closed
          hn3 hpsi ring E
          (by simpa [E] using hPB)
    have hclosed' :
        n *
            PPL.Convergence.L17.l17FailureCount
              theorem1C17 ring E ≤
          n ^ theorem1H17 n := by
      simpa
        [PPL.Convergence.L17.Lemma17WordBound,
          theorem1C17, theorem1H17]
        using hclosed
    have hcount' :
        (allSchedules n
            (theorem1H17 n)).countP
            (theorem1L17PhaseBad
              ring C0 p) ≤
          PPL.Convergence.L17.l17FailureCount
            theorem1C17 ring E := by
      simpa [E] using hcount
    have hscaled :=
      Nat.mul_le_mul_left n hcount'
    calc
      n *
          (allSchedules n
            (theorem1H17 n)).countP
            (theorem1L17PhaseBad
              ring C0 p) ≤
        n *
          PPL.Convergence.L17.l17FailureCount
            theorem1C17 ring E :=
        hscaled
      _ ≤ n ^ theorem1H17 n :=
        hclosed'
      _ = 1 * n ^ theorem1H17 n := by
        simp

  have hpad :=
    hCutPadding
      (n := n)
      (H := theorem1Horizon n psi)
      (T := theorem1H17 n)
      (c := 1)
      stop
      (theorem1L17PhaseBad ring C0)
      (theorem1Bad17B ring C0)
      hfree hphase hcover

  simpa using hpad

/-- Every `theorem1Bad17B` word factors as a first-`C_mid` stopped prefix, an
`H17` phase that is L17-bad, and a pad (no domain premise). -/
theorem theorem1L17FirstHitStop_cover
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
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
              ring C0 p phase = true := by
  cases hcut :
      theorem1MidCut
        ring C0 word with
  | none =>
      simp [theorem1Bad17B,
        theorem1MidState, hcut] at hbad
  | some t =>
      have hbadCore := hbad
      unfold theorem1Bad17B at hbadCore
      rw [hcut] at hbadCore
      simp only [theorem1MidState,
        hcut] at hbadCore
      have houter :=
        Bool.and_eq_true_iff.mp hbadCore
      have hinner0 :=
        Bool.and_eq_true_iff.mp houter.1
      have hreach := hinner0.1
      have hinner := And.intro hinner0.2 houter.2
      have hmiss := hinner.2


      have hfirst :
          theorem1FirstHitCut
              ring
              PPL.Modes.Lemma5.midPhysicalB
              (theorem1State16
                ring C0 word)
              (theorem1Block5i
                psi word) =
            some t := by
        simpa [theorem1MidCut] using hcut


      have htBlock :
          t ≤
            (theorem1Block5i
              psi word).length :=
        theorem1FirstHitCut_le_length
          ring
          PPL.Modes.Lemma5.midPhysicalB
          (theorem1State16
            ring C0 word)
          (theorem1Block5i
            psi word)
          hfirst


      have htH5i :
          t ≤ theorem1H5i n := by
        have hlen :
            (theorem1Block5i
              psi word).length ≤
              theorem1H5i n := by
          unfold theorem1Block5i
          simp only [List.length_take]
          exact Nat.min_le_left _ _
        exact Nat.le_trans htBlock hlen


      have hquiet :=
        theorem1H17_add_H18_le_H5ii
          hn3 hpsi hnpow
      have h17le :
          theorem1H17 n ≤
            theorem1H5ii n psi := by
        omega


      have hwordLength :
          word.length =
            theorem1Horizon n psi :=
        allSchedules_schedule_length
          n
          (theorem1Horizon n psi)
          word hword


      have hkPrefix :
          theorem1H16 n psi + t ≤
            word.length := by
        rw [hwordLength,
          theorem1Horizon_eq_phase_sum]
        omega


      have hphaseAvail :
          theorem1H17 n ≤
            (word.drop
              (theorem1H16 n psi +
                t)).length := by
        rw [List.length_drop,
          hwordLength,
          theorem1Horizon_eq_phase_sum]
        omega


      have hpLength :
          (word.take
            (theorem1H16 n psi +
              t)).length =
            theorem1H16 n psi + t := by
        simp only [List.length_take]
        exact Nat.min_eq_left hkPrefix


      have hpA :
          theorem1H16 n psi ≤
            (word.take
              (theorem1H16 n psi +
                t)).length := by
        rw [hpLength]
        omega


      have hblockPrefix :
          (word.take
            (theorem1H16 n psi +
              t)).take
              (theorem1H16 n psi) =
            theorem1Block16
              psi word := by
        unfold theorem1Block16
        rw [List.take_take]
        have hmin :
            min
                (theorem1H16 n psi)
                (theorem1H16 n psi + t) =
              theorem1H16 n psi :=
          Nat.min_eq_left (by omega)
        rw [hmin]


      have hCPB16 :
          PPL.CPB ring
            (PPL.Probability.runPPL
              ring C0
              (theorem1Block16
                psi word)) := by
        apply of_decide_eq_true
        rw [←
          PPL.Convergence.ReachCPB.reachesCPB_eq_endpoint
              hn3 hpsi ring C0
              (theorem1Block16
                psi word)]
        exact hreach


      have hCPBp :
          PPL.CPB ring
            (PPL.Probability.runPPL
              ring C0
              ((word.take
                (theorem1H16 n psi +
                  t)).take
                    (theorem1H16
                      n psi))) := by
        rw [hblockPrefix]
        exact hCPB16


      have hsuffix :
          (word.take
            (theorem1H16 n psi +
              t)).drop
              (theorem1H16 n psi) =
            (theorem1Block5i
              psi word).take t := by
        unfold theorem1Block5i
        rw [List.drop_take,
          List.take_take]
        have hsub :
            theorem1H16 n psi + t -
                theorem1H16 n psi =
              t := by
          omega
        have hmin :
            min t
                (theorem1H5i n) =
              t :=
          Nat.min_eq_left htH5i
        rw [hsub, hmin]


      have hfirstTake :=
        theorem1FirstHitCut_take
          ring
          PPL.Modes.Lemma5.midPhysicalB
          (theorem1State16
            ring C0 word)
          (theorem1Block5i
            psi word)
          hfirst


      have hsufLen :
          ((theorem1Block5i
            psi word).take t).length =
            t := by
        simp only [List.length_take]
        exact Nat.min_eq_left htBlock


      have hhitP :
          theorem1FirstHitCut
              ring
              PPL.Modes.Lemma5.midPhysicalB
              (PPL.Probability.runPPL
                ring C0
                ((word.take
                  (theorem1H16 n psi +
                    t)).take
                      (theorem1H16
                        n psi)))
              ((word.take
                (theorem1H16 n psi +
                  t)).drop
                    (theorem1H16
                      n psi)) =
            some
              ((word.take
                (theorem1H16 n psi +
                  t)).drop
                    (theorem1H16
                      n psi)).length := by
        rw [hblockPrefix, hsuffix, hsufLen]
        simpa [theorem1State16]
          using hfirstTake


      have hstop :
          theorem1L17FirstHitStop
              ring C0
              (word.take
                (theorem1H16 n psi +
                  t)) =
            true := by
        unfold theorem1L17FirstHitStop
        exact
          decide_eq_true
            ⟨hpA, hCPBp, hhitP⟩


      have hphaseLength :
          ((word.drop
            (theorem1H16 n psi +
              t)).take
                (theorem1H17 n)).length =
            theorem1H17 n := by
        simp only [List.length_take]
        exact Nat.min_eq_left hphaseAvail


      have hphaseMem :
          (word.drop
            (theorem1H16 n psi +
              t)).take
                (theorem1H17 n) ∈
            allSchedules n
              (theorem1H17 n) :=
        mem_allSchedules_of_length
          n (theorem1H17 n)
          ((word.drop
            (theorem1H16 n psi +
              t)).take
                (theorem1H17 n))
          hphaseLength


      have hpState :
          PPL.Probability.runPPL
              ring C0
              (word.take
                (theorem1H16 n psi +
                  t)) =
            PPL.Probability.runPPL
              ring
              (theorem1State16
                ring C0 word)
              ((theorem1Block5i
                psi word).take t) := by
        rw [←
          theorem1L17Take_append_take_drop
            word
            (theorem1H16 n psi)
            t]
        rw [theorem1L17RunPPL_append]
        simp only [theorem1State16,
          theorem1Block16,
          theorem1Block5i,
          List.take_take]
        rw [Nat.min_eq_left htH5i]


      have hphaseEq :
          theorem1L17Word
              psi t word =
            (word.drop
              (theorem1H16 n psi +
                t)).take
                  (theorem1H17 n) := by
        unfold theorem1L17Word
          theorem1QuietWord
        rw [List.take_take]
        rw [Nat.min_eq_left h17le]


      have hphaseBad :
          theorem1L17PhaseBad
              ring C0
              (word.take
                (theorem1H16 n psi +
                  t))
              ((word.drop
                (theorem1H16 n psi +
                  t)).take
                    (theorem1H17 n)) =
            true := by
        unfold theorem1L17PhaseBad
        rw [hpState]
        unfold theorem1Literal17End at hmiss
        rw [hphaseEq] at hmiss
        exact hmiss


      have hfactor :
          word =
            word.take
                (theorem1H16 n psi + t) ++
              ((word.drop
                (theorem1H16 n psi +
                  t)).take
                    (theorem1H17 n) ++
                (word.drop
                  (theorem1H16 n psi +
                    t)).drop
                      (theorem1H17 n)) := by
        calc
          word =
              word.take
                  (theorem1H16 n psi + t) ++
                word.drop
                  (theorem1H16 n psi + t) :=
            (List.take_append_drop
              (theorem1H16 n psi + t)
              word).symm
          _ =
              word.take
                  (theorem1H16 n psi + t) ++
                ((word.drop
                  (theorem1H16 n psi +
                    t)).take
                      (theorem1H17 n) ++
                  (word.drop
                    (theorem1H16 n psi +
                      t)).drop
                        (theorem1H17 n)) := by
            exact
              congrArg
                (fun tail =>
                  word.take
                      (theorem1H16 n psi +
                        t) ++
                    tail)
                (List.take_append_drop
                  (theorem1H17 n)
                  (word.drop
                    (theorem1H16 n psi +
                      t))).symm


      exact
        ⟨word.take
            (theorem1H16 n psi + t),
          (word.drop
            (theorem1H16 n psi + t)).take
              (theorem1H17 n),
          (word.drop
            (theorem1H16 n psi + t)).drop
              (theorem1H17 n),
          hstop,
          hphaseMem,
          (by rw [List.append_assoc]; exact hfactor),
          hphaseBad⟩

/-- The L17 first-hit cut adapter holds at every `(n, psi)` with `n ≥ 3`,
`psi ≥ 2`, `n ≤ 2 ^ psi`. -/
theorem theorem1L17FirstHitCut_proved
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    theorem1L17FirstHitCutAt ring C0 := by
  refine
    ⟨theorem1L17FirstHitStop
        ring C0,
      ?_, ?_, ?_⟩
  · exact
      theorem1L17FirstHitStop_prefixFree
        ring C0
  · intro p hp hlen
    exact
      theorem1L17FirstHitStop_local
        hn3 hpsi ring C0 p hp
  · intro word hword hbad
    exact
      theorem1L17FirstHitStop_cover
        hn3 hpsi hnpow
        ring C0 word hword hbad

/-- The dynamic L17 padded bound at one `(n, psi)`, unconditionally. -/
theorem theorem1L17DynamicPaddedBound_proved
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    n *
        (allSchedules n
          (theorem1Horizon n psi)).countP
            (theorem1Bad17B ring C0) <=
      n ^ theorem1Horizon n psi :=
  theorem1L17DynamicPaddedBound_of_cutPadding
    theorem1DynamicCutPadding_proved
    hn3 hpsi hnpow ring C0
    (theorem1L17FirstHitCut_proved hn3 hpsi hnpow ring C0)

/-- The dynamic L5(ii) padded bound at one `(n, psi)`, unconditionally. -/
theorem theorem1L5iiDynamicPaddedBound_proved
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    n *
        (allSchedules n
          (theorem1Horizon n psi)).countP
            (theorem1Bad5iiB ring C0) <=
      4 * n ^ theorem1Horizon n psi := by
  exact
    theorem1DynamicCutPadding_proved
      (n := n)
      (H := theorem1Horizon n psi)
      (T := theorem1H5ii n psi)
      (c := 4)
      (theorem1L17FirstHitStop ring C0)
      (theorem1L5iiFirstHitPhaseBad ring C0)
      (theorem1Bad5iiB ring C0)
      (theorem1L17FirstHitStop_prefixFree ring C0)
      (by
        intro p hp _hlen
        exact
          theorem1L5iiFirstHitStop_local
            hn3 hpsi hnpow
            ring C0 p hp)
      (by
        intro word hword hbad
        exact
          theorem1L5iiFirstHitStop_cover
            hn3 hpsi ring C0
            word hword hbad)

end PPL.Theorem1General

#print axioms PPL.Theorem1General.theorem1L5iPaddedBound_of_lemma5Bridge
#print axioms PPL.Theorem1General.theorem1L17DynamicPaddedBound_of_cutPadding
#print axioms PPL.Theorem1General.theorem1L17FirstHitStop_cover
#print axioms PPL.Theorem1General.theorem1L17FirstHitCut_proved
#print axioms PPL.Theorem1General.theorem1L17DynamicPaddedBound_proved
#print axioms PPL.Theorem1General.theorem1L5iiDynamicPaddedBound_proved

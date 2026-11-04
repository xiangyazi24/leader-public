import Leader.PPL.PsiBelowN.Cost
import Leader.PPL.MainTheorem.CostFromThirteenTail
import Leader.PPL.MainTheorem.GeneralSplice
import Leader.PPL.MainTheorem.GeneralExhaustive

/-!
# P_PL Theorem 1 on `psi < n`: the tiny producer for `13 ≤ n ≤ 64`

Copies of the counting-to-existence route (`Theorem1CostFrom13*.lean`) on the
domain `psi < n`.  In the originals the window is threaded into the L16
padded bound (`theorem1From13_firstTwoStages`), the quiet-window fit and the
L18 first-hit interface (`theorem1From13_tailJointSelection_of_l18FirstHit`);
`theorem1From13_tailSemanticPrefix_of_jointGood` receives it and does not use
it.  The strictness conditions (12 < n, 8 < n, 4 + 1 + 1 < n) involve `n`
only.

P_PL Theorem 1 cleanup, phase 2, step 6d: the post-`C_PB` stages
(`theorem1FirstTwoStages_of_cpbPrefix`) and the joint tail selection with
the premise it consumes, `4 + 1 + 1 < n` (`theorem1TailJointSelection_of_coeff`),
are proved once here; the `13 ≤ n` theorems of this file and the `8 < n`
theorems of `Upto12.lean` are special cases with unchanged statements.  The
private helper copies `q20290_firstHitCut_some_of_reachesAux` (identical to
`PPL.theorem1FirstHitCut_some_of_reachesAux`), `q20292_sum_if_count` and
`q20292_countP_take_pad` (`PPL.Theorem1General.theorem1_countP_take_pad`)
are gone.  Step 6f: the `q20296*` helper copies (FoldlAnd, all-roots miss,
L18 hit prefix, post-construct prefix, `runLocalSchedule = runPPL`) are
replaced by their `PPL.Theorem1General` versions.
-/

namespace PPL.PsiBelowN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol

-- [copied from Leader/PPL/MainTheorem/CostFromThirteen.lean:21-43]
/--
The C.4 producer restricted to the range where every individual
phase coefficient is strictly below n.
-/
def Theorem1TinyProducerFrom13 : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    13 ≤ n →
    n ≤ 64 →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi < n →
    ∃ L : Nat,
      ∀ ring : DirectedRing n,
        BoundedSafeScheduleProducer
          ring
          (PPL.protocol
            psi (theorem1Kappa psi)).transition
          (fun _ => True)
          (SPL ring)
          L


/--
Stages 2 and 3 of the bind, from any H16-length prefix `w16` whose
endpoint satisfies `C_PB`: the local Lemma-5(i) word bound at that endpoint
(coefficient 8, `8 < n`) selects an L5(i) word, and its first-hit cut gives a
prefix ending exactly at the dynamic first `C_mid` cut, with room for the
H5(ii) tail.  `theorem1From13_firstTwoStages` (prefix from the L16 count) and
`theorem1FromCPB_firstTwoStages` (a constant H16 prefix from `C_PB`) are the
two special cases (P_PL Theorem 1 cleanup, step 6d).
-/
theorem theorem1FirstTwoStages_of_cpbPrefix
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (h8 : 8 < n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (w16 : DetSchedule n)
    (hw16Len : w16.length = theorem1H16 n psi)
    (hCPB16 : PPL.CPB ring (PPL.Probability.runPPL ring C0 w16)) :
    ∃ p : DetSchedule n,
      p.length ≤
          theorem1H16 n psi +
            theorem1H5i n ∧
        theorem1L17FirstHitStop
            ring C0 p = true ∧
          p.length +
              theorem1H5ii n psi ≤
            theorem1Horizon n psi := by
  have hnpos : 0 < n := by
    omega

  let C16 :
      Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C0 w16

  have hCPB : PPL.CPB ring C16 := hCPB16

  /- Stage 2: use the already-landed local Lemma-5(i) word bound at the
     selected C_PB endpoint, then coefficient 8. -/
  have h5iWord :
      PPL.Modes.Lemma5.Lemma5iWordBound
        ring C16 :=
    (PPL.Modes.Lemma5.lemma5iWordBound_of_retimedCounts_noResetLineage
        PPL.Modes.Lemma5.lemma5iSweepMidCountRetimed_waveDebt_proved)
      hn3 hpsi
      (theorem1Kappa_ge_48_mul psi)
      hnpow
      ring C16
      (theorem1CPB_neverLeaderless
        hn3 hpsi ring C16 hCPB)
      (PPL.Modes.SignalLineage.signalLineageOwnership ring)
      PPL.Probability.stoppedClockSuffixBoundsCorrected
      PPL.Modes.Lemma9.modeStoppedTreeTransfer
      PPL.Probability.predictableHostTails
      PPL.Probability.wlgHeadOffsetBounds
      PPL.Probability.lotteryCountBounds


  have h5iCount :
      n *
          (allSchedules n
            (theorem1H5i n)).countP
            (fun phase =>
              !(PPL.Modes.Lemma5.reachesAux
                ring
                PPL.Modes.Lemma5.midPhysicalB
                C16 phase)) ≤
        8 * n ^ theorem1H5i n := by
    simpa
      [PPL.Modes.Lemma5.Lemma5iWordBound,
        PPL.Modes.Lemma5.lemma5iFailureCount,
        theorem1H5i]
      using h5iWord


  obtain
      ⟨w5i, _hw5iMem, hw5iLen, hgood5i⟩ :=
    theorem1From13_selectGoodSchedule
      (n := n)
      (H := theorem1H5i n)
      (c := 8)
      hnpos
      h8
      (fun phase =>
        !(PPL.Modes.Lemma5.reachesAux
          ring
          PPL.Modes.Lemma5.midPhysicalB
          C16 phase))
      h5iCount


  have hreach5i :
      PPL.Modes.Lemma5.reachesAux
          ring
          PPL.Modes.Lemma5.midPhysicalB
          C16 w5i =
        true := by
    cases h :
        PPL.Modes.Lemma5.reachesAux
          ring
          PPL.Modes.Lemma5.midPhysicalB
          C16 w5i with
    | false =>
        simp [h] at hgood5i
    | true =>
        rfl


  obtain ⟨t, hcut⟩ :=
    theorem1FirstHitCut_some_of_reachesAux
      ring
      PPL.Modes.Lemma5.midPhysicalB
      C16 w5i hreach5i


  have ht :
      t ≤ w5i.length :=
    theorem1FirstHitCut_le_length
      ring
      PPL.Modes.Lemma5.midPhysicalB
      C16 w5i (t := t) hcut


  have htH5i :
      t ≤ theorem1H5i n := by
    rw [← hw5iLen]
    exact ht


  have hcutTake :=
    theorem1FirstHitCut_take
      ring
      PPL.Modes.Lemma5.midPhysicalB
      C16 w5i hcut


  let w5iHit : DetSchedule n :=
    w5i.take t


  have hw5iHitLen :
      w5iHit.length = t := by
    dsimp [w5iHit]
    rw [List.length_take]
    exact Nat.min_eq_left ht


  let p : DetSchedule n :=
    w16 ++ w5iHit


  have hpLenEq :
      p.length =
        theorem1H16 n psi + t := by
    simp [p, hw16Len, hw5iHitLen]


  have hpBound :
      p.length ≤
        theorem1H16 n psi +
          theorem1H5i n := by
    rw [hpLenEq]
    omega


  have hpTake :
      p.take (theorem1H16 n psi) =
        w16 := by
    dsimp [p]
    rw [← hw16Len]
    exact List.take_append_length


  have hpDrop :
      p.drop (theorem1H16 n psi) =
        w5iHit := by
    dsimp [p]
    rw [← hw16Len]
    exact List.drop_append_length


  have hpCPB :
      PPL.CPB ring
        (PPL.Probability.runPPL
          ring C0
          (p.take
            (theorem1H16 n psi))) := by
    rw [hpTake]
    simpa [C16] using hCPB


  have hpCut :
      theorem1FirstHitCut
          ring
          PPL.Modes.Lemma5.midPhysicalB
          (PPL.Probability.runPPL
            ring C0
            (p.take
              (theorem1H16 n psi)))
          (p.drop
            (theorem1H16 n psi)) =
        some
          (p.drop
            (theorem1H16 n psi)).length := by
    rw [hpTake, hpDrop]
    change
      theorem1FirstHitCut
          ring
          PPL.Modes.Lemma5.midPhysicalB
          C16 w5iHit =
        some w5iHit.length
    have hcutHit :
        theorem1FirstHitCut
            ring
            PPL.Modes.Lemma5.midPhysicalB
            C16 w5iHit =
          some t := by
      simpa [w5iHit] using hcutTake
    simpa [hw5iHitLen] using hcutHit


  have hstop :
      theorem1L17FirstHitStop
          ring C0 p =
        true := by
    unfold theorem1L17FirstHitStop
    simp only [decide_eq_true_eq]
    refine ⟨?_, hpCPB, hpCut⟩
    rw [hpLenEq]
    omega


  have hroom :
      p.length +
          theorem1H5ii n psi ≤
        theorem1Horizon n psi := by
    rw [theorem1Horizon_eq_phase_sum]
    omega


  exact
    ⟨p, hpBound, hstop, hroom⟩

-- [copied from Leader/PPL/Theorem1CostFrom13Bind.lean:88-394]
/--
fallback: bind L16 and L5(i) phasewise.


The returned prefix ends exactly at the dynamic first C_mid cut, as encoded
by theorem1L17FirstHitStop.  The last conjunct is the room certificate
needed by the H5ii tail stage.
-/
theorem theorem1From13_firstTwoStages
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hn13 : 13 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    ∃ p : DetSchedule n,
      p.length ≤
          theorem1H16 n psi +
            theorem1H5i n ∧
        theorem1L17FirstHitStop
            ring C0 p = true ∧
          p.length +
              theorem1H5ii n psi ≤
            theorem1Horizon n psi := by
  have hnpos : 0 < n := by
    omega


  /- Stage 1: use the landed full-horizon L16 count and coefficient 12.
     Only its H16 prefix matters. -/
  have h16Count :=
    theorem1L16PaddedBound_proved
      hn3 hpsi hnpow hpsiK ring C0


  obtain
      ⟨full16, _hfull16Mem, hfull16Len, hgood16⟩ :=
    theorem1From13_selectGoodSchedule
      (n := n)
      (H := theorem1Horizon n psi)
      (c := 12)
      hnpos
      (theorem1From13_coeff12_lt hn13)
      (theorem1Bad16B ring C0)
      h16Count


  let w16 : DetSchedule n :=
    theorem1Block16 psi full16


  have hH16le :
      theorem1H16 n psi ≤
        theorem1Horizon n psi := by
    rw [theorem1Horizon_eq_phase_sum]
    omega


  have hw16Len :
      w16.length = theorem1H16 n psi := by
    dsimp [w16, theorem1Block16]
    rw [List.length_take, hfull16Len]
    exact Nat.min_eq_left hH16le


  have hreach16 :
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 w16 =
        true := by
    cases h :
        PPL.Convergence.ReachCPB.reachesCPB
          ring C0 w16 with
    | false =>
        simp
          [theorem1Bad16B, w16, h]
          at hgood16
    | true =>
        rfl


  let C16 :
      Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C0 w16


  have hCPB : PPL.CPB ring C16 := by
    have hdec :
        decide (PPL.CPB ring C16) = true := by
      dsimp [C16]
      rw [←
        PPL.Convergence.ReachCPB.reachesCPB_eq_endpoint
          hn3 hpsi ring C0 w16]
      exact hreach16
    exact of_decide_eq_true hdec

  exact
    theorem1FirstTwoStages_of_cpbPrefix
      hn3 (theorem1From13_coeff8_lt hn13) hpsi hnpow
      ring C0 w16 hw16Len hCPB



/--
steps 1–4 with the selector's coefficient premise `4 + 1 + 1 < n`
(L5(ii) coefficient 4, L17 coefficient 1, L18 coefficient 1): for one
first-hit prefix `p`, select one H5(ii)-length suffix on which the L5(ii),
L17 and L18 tail failure predicates are all false.
`theorem1From13_tailJointSelection_of_l18FirstHit` (`13 ≤ n`) and
`theorem1FromCPB_tailJointSelection_of_coeff` are special cases (P_PL
Theorem 1 cleanup, step 6d).
-/
theorem theorem1TailJointSelection_of_coeff
    (hL18 : Theorem1L18FirstHitPhaseBound)
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hcoeff : 4 + 1 + 1 < n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p : DetSchedule n)
    (hstop :
      theorem1L17FirstHitStop
        ring C0 p = true)
    (hroom :
      p.length +
          theorem1H5ii n psi ≤
        theorem1Horizon n psi) :
    ∃ suffix : DetSchedule n,
      suffix ∈
          allSchedules n
            (theorem1H5ii n psi) ∧
        suffix.length =
          theorem1H5ii n psi ∧
        theorem1L5iiFirstHitPhaseBad
            ring C0 p suffix = false ∧
        theorem1From13_tailL17Bad
            ring C0 p suffix = false ∧
        theorem1L18FirstHitPhaseBad
            ring C0 p suffix = false := by
  have h5ii :=
    theorem1L5iiFirstHitStop_local
      hn3 hpsi hnpow
      ring C0 p hstop

  have h17Local :=
    theorem1L17FirstHitStop_local
      hn3 hpsi ring C0 p hstop
  rcases h17Local with
    ⟨hPB, h17Count⟩

  let E : PPL.LiteralElimConfig n :=
    PPL.Elim.viewConfig
      (PPL.Probability.runPPL
        ring C0 p)

  have h17Closed :=
    PPL.Convergence.L17.lemma17_wordBound_closed
      hn3 hpsi ring E
      (by
        simpa [E] using hPB)

  have h17Closed' :
      n *
          PPL.Convergence.L17.l17FailureCount
            theorem1C17 ring E ≤
        n ^ theorem1H17 n := by
    simpa
      [PPL.Convergence.L17.Lemma17WordBound,
        theorem1C17, theorem1H17]
      using h17Closed

  have h17Count' :
      (allSchedules n
          (theorem1H17 n)).countP
          (theorem1L17PhaseBad
            ring C0 p) ≤
        PPL.Convergence.L17.l17FailureCount
          theorem1C17 ring E := by
    simpa [E] using h17Count

  have h17Scaled :=
    Nat.mul_le_mul_left n h17Count'

  have h17Base :
      n *
          (allSchedules n
            (theorem1H17 n)).countP
            (theorem1L17PhaseBad
              ring C0 p) ≤
        1 * n ^ theorem1H17 n := by
    calc
      n *
          (allSchedules n
            (theorem1H17 n)).countP
            (theorem1L17PhaseBad
              ring C0 p) ≤
        n *
          PPL.Convergence.L17.l17FailureCount
            theorem1C17 ring E :=
        h17Scaled
      _ ≤ n ^ theorem1H17 n :=
        h17Closed'
      _ = 1 * n ^ theorem1H17 n := by
        simp

  have hquiet :=
    theorem1H17_add_H18_le_H5ii
      hn3 hpsi hnpow hpsiK

  have h17le :
      theorem1H17 n ≤
        theorem1H5ii n psi := by
    omega

  have hsum :
      theorem1H17 n +
          (theorem1H5ii n psi -
            theorem1H17 n) =
        theorem1H5ii n psi :=
    Nat.add_sub_of_le h17le

  have hpadCount :=
    PPL.Theorem1General.theorem1_countP_take_pad
      (n := n)
      (T := theorem1H17 n)
      (P :=
        theorem1H5ii n psi -
          theorem1H17 n)
      (theorem1L17PhaseBad
        ring C0 p)

  rw [hsum] at hpadCount

  have h17PadCount :
      (allSchedules n
          (theorem1H5ii n psi)).countP
          (theorem1From13_tailL17Bad
            ring C0 p) =
        (allSchedules n
          (theorem1H17 n)).countP
            (theorem1L17PhaseBad
              ring C0 p) *
          n ^
            (theorem1H5ii n psi -
              theorem1H17 n) := by
    exact hpadCount

  have h17Pad :
      n *
          (allSchedules n
            (theorem1H5ii n psi)).countP
            (theorem1From13_tailL17Bad
              ring C0 p) ≤
        1 * n ^ theorem1H5ii n psi := by
    rw [h17PadCount]
    exact
      theorem1_pad_phase_bound
        h17le h17Base

  have h18 :=
    hL18
      hn3 hpsi hnpow hpsiK
      ring C0 p hstop hroom

  have h18' :
      n *
          (allSchedules n
            (theorem1H5ii n psi)).countP
            (theorem1L18FirstHitPhaseBad
              ring C0 p) ≤
        1 * n ^ theorem1H5ii n psi := by
    simpa using h18

  have h23 :=
    theorem1_countP_or_le_add
      (allSchedules n
        (theorem1H5ii n psi))
      (theorem1From13_tailL17Bad
        ring C0 p)
      (theorem1L18FirstHitPhaseBad
        ring C0 p)

  have h123 :=
    theorem1_countP_or_le_add
      (allSchedules n
        (theorem1H5ii n psi))
      (theorem1L5iiFirstHitPhaseBad
        ring C0 p)
      (fun phase =>
        theorem1From13_tailL17Bad
            ring C0 p phase ||
          theorem1L18FirstHitPhaseBad
            ring C0 p phase)

  have hUnion :
      (allSchedules n
          (theorem1H5ii n psi)).countP
          (theorem1From13_tailJointBad
            ring C0 p) ≤
        (allSchedules n
            (theorem1H5ii n psi)).countP
            (theorem1L5iiFirstHitPhaseBad
              ring C0 p) +
          ((allSchedules n
              (theorem1H5ii n psi)).countP
              (theorem1From13_tailL17Bad
                ring C0 p) +
            (allSchedules n
              (theorem1H5ii n psi)).countP
              (theorem1L18FirstHitPhaseBad
                ring C0 p)) := by
    calc
      (allSchedules n
          (theorem1H5ii n psi)).countP
          (theorem1From13_tailJointBad
            ring C0 p) ≤
        (allSchedules n
            (theorem1H5ii n psi)).countP
            (theorem1L5iiFirstHitPhaseBad
              ring C0 p) +
          (allSchedules n
            (theorem1H5ii n psi)).countP
            (fun phase =>
              theorem1From13_tailL17Bad
                  ring C0 p phase ||
                theorem1L18FirstHitPhaseBad
                  ring C0 p phase) := by
        exact h123
      _ ≤
        (allSchedules n
            (theorem1H5ii n psi)).countP
            (theorem1L5iiFirstHitPhaseBad
              ring C0 p) +
          ((allSchedules n
              (theorem1H5ii n psi)).countP
              (theorem1From13_tailL17Bad
                ring C0 p) +
            (allSchedules n
              (theorem1H5ii n psi)).countP
              (theorem1L18FirstHitPhaseBad
                ring C0 p)) :=
        Nat.add_le_add_left
          h23
          ((allSchedules n
            (theorem1H5ii n psi)).countP
            (theorem1L5iiFirstHitPhaseBad
              ring C0 p))

  have hUnionScaled :=
    Nat.mul_le_mul_left n hUnion

  have hJoint :
      n *
          (allSchedules n
            (theorem1H5ii n psi)).countP
            (theorem1From13_tailJointBad
              ring C0 p) ≤
        (4 + 1 + 1) *
          n ^ theorem1H5ii n psi := by
    calc
      n *
          (allSchedules n
            (theorem1H5ii n psi)).countP
            (theorem1From13_tailJointBad
              ring C0 p) ≤
        n *
          ((allSchedules n
              (theorem1H5ii n psi)).countP
              (theorem1L5iiFirstHitPhaseBad
                ring C0 p) +
            ((allSchedules n
                (theorem1H5ii n psi)).countP
                (theorem1From13_tailL17Bad
                  ring C0 p) +
              (allSchedules n
                (theorem1H5ii n psi)).countP
                (theorem1L18FirstHitPhaseBad
                  ring C0 p))) :=
        hUnionScaled
      _ =
        n *
            (allSchedules n
              (theorem1H5ii n psi)).countP
              (theorem1L5iiFirstHitPhaseBad
                ring C0 p) +
          (n *
              (allSchedules n
                (theorem1H5ii n psi)).countP
                (theorem1From13_tailL17Bad
                  ring C0 p) +
            n *
              (allSchedules n
                (theorem1H5ii n psi)).countP
                (theorem1L18FirstHitPhaseBad
                  ring C0 p)) := by
        simp only [Nat.mul_add]
      _ ≤
        4 * n ^ theorem1H5ii n psi +
          (1 * n ^ theorem1H5ii n psi +
            1 * n ^ theorem1H5ii n psi) :=
        Nat.add_le_add
          h5ii
          (Nat.add_le_add h17Pad h18')
      _ =
        (4 + 1 + 1) *
          n ^ theorem1H5ii n psi := by
        omega

  obtain
      ⟨suffix, hmem, hlen, hgood⟩ :=
    theorem1From13_selectGoodSchedule
      ring.hn
      hcoeff
      (theorem1From13_tailJointBad
        ring C0 p)
      hJoint

  have h5Good :
      theorem1L5iiFirstHitPhaseBad
          ring C0 p suffix = false := by
    cases h :
        theorem1L5iiFirstHitPhaseBad
          ring C0 p suffix with
    | false =>
        rfl
    | true =>
        simp
          [theorem1From13_tailJointBad, h]
          at hgood

  have h17Good :
      theorem1From13_tailL17Bad
          ring C0 p suffix = false := by
    cases h :
        theorem1From13_tailL17Bad
          ring C0 p suffix with
    | false =>
        rfl
    | true =>
        simp
          [theorem1From13_tailJointBad, h]
          at hgood

  have h18Good :
      theorem1L18FirstHitPhaseBad
          ring C0 p suffix = false := by
    cases h :
        theorem1L18FirstHitPhaseBad
          ring C0 p suffix with
    | false =>
        rfl
    | true =>
        simp
          [theorem1From13_tailJointBad, h]
          at hgood

  exact
    ⟨suffix, hmem, hlen,
      h5Good, h17Good, h18Good⟩

-- [copied from Leader/PPL/MainTheorem/CostFromThirteenTail.lean:107-465]
/--
steps 1–4.

For one particular first-hit prefix p, select one exact H5(ii) suffix on
which all three local tail bad predicates are false simultaneously.
-/
theorem theorem1From13_tailJointSelection_of_l18FirstHit
    (hL18 : Theorem1L18FirstHitPhaseBound)
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hn13 : 13 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p : DetSchedule n)
    (hstop :
      theorem1L17FirstHitStop
        ring C0 p = true)
    (hroom :
      p.length +
          theorem1H5ii n psi ≤
        theorem1Horizon n psi) :
    ∃ suffix : DetSchedule n,
      suffix ∈
          allSchedules n
            (theorem1H5ii n psi) ∧
        suffix.length =
          theorem1H5ii n psi ∧
        theorem1L5iiFirstHitPhaseBad
            ring C0 p suffix = false ∧
        theorem1From13_tailL17Bad
            ring C0 p suffix = false ∧
        theorem1L18FirstHitPhaseBad
            ring C0 p suffix = false :=
  theorem1TailJointSelection_of_coeff
    hL18 hn3 (theorem1From13_quietTailCoeff_lt hn13) hpsi hnpow hpsiK
    ring C0 p hstop hroom


-- [copied from Leader/PPL/Theorem1CostFrom13TailSemantic.lean:204-481]
theorem theorem1From13_tailSemanticPrefix_of_jointGood
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p suffix : DetSchedule n)
    (hstop :
      theorem1L17FirstHitStop
        ring C0 p = true)
    (hsuffix :
      suffix.length =
        theorem1H5ii n psi)
    (h5iiGood :
      theorem1L5iiFirstHitPhaseBad
          ring C0 p suffix = false)
    (h17Good :
      theorem1From13_tailL17Bad
          ring C0 p suffix = false)
    (h18Good :
      theorem1L18FirstHitPhaseBad
          ring C0 p suffix = false) :
    Exists fun k : Nat =>
      And (k <= suffix.length)
        (SPL ring
          (runLocalSchedule
            ring
            (PPL.protocol
              psi (theorem1Kappa psi)).transition
            C0
            (p ++ suffix.take k))) := by
  let Cmid :
      Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C0 p
  let w17 : DetSchedule n :=
    suffix.take (theorem1H17 n)
  let w18 : DetSchedule n :=
    (suffix.drop (theorem1H17 n)).take
      (theorem1H18 n psi)
  let C17 :
      Config n psi (theorem1Kappa psi) :=
    PPL.Convergence.ConstructCoupling.runPrime
      ring Cmid w17

  have hconstruct :
      PPL.Modes.Lemma5.constructAlong
          ring Cmid suffix =
        true := by
    cases hc :
        PPL.Modes.Lemma5.constructAlong
          ring Cmid suffix with
    | false =>
        have hbadTrue :
            theorem1L5iiFirstHitPhaseBad
                ring C0 p suffix =
              true := by
          simp
            [theorem1L5iiFirstHitPhaseBad,
              Cmid, hc]
        rw [hbadTrue] at h5iiGood
        contradiction
    | true =>
        rfl

  have hl1Dec :
      @decide
          (PPL.LiteralL1
            (PPL.Probability.runPopulationSchedule
              PPL.Elim.protocolE ring
              (PPL.Elim.viewConfig Cmid)
              w17))
          (theorem1LiteralL1Decidable _) =
        true := by
    cases hl :
        @decide
          (PPL.LiteralL1
            (PPL.Probability.runPopulationSchedule
              PPL.Elim.protocolE ring
              (PPL.Elim.viewConfig Cmid)
              w17))
          (theorem1LiteralL1Decidable _) with
    | false =>
        have hbadTrue :
            theorem1From13_tailL17Bad
                ring C0 p suffix =
              true := by
          simp
            [theorem1From13_tailL17Bad,
              theorem1L17PhaseBad,
              Cmid, w17, hl]
        rw [hbadTrue] at h17Good
        contradiction
    | true =>
        rfl

  have hroots :
      theorem1AllLeaderRootsMissB
          ring C17 w18 =
        false := by
    cases hr :
        theorem1AllLeaderRootsMissB
          ring C17 w18 with
    | false =>
        rfl
    | true =>
        have hbadTrue :
            theorem1L18FirstHitPhaseBad
                ring C0 p suffix =
              true := by
          simp
            [theorem1L18FirstHitPhaseBad,
              Cmid, w17, w18, C17,
              hconstruct, hl1Dec, hr]
        rw [hbadTrue] at h18Good
        contradiction

  obtain ⟨root, _hleader, hhit⟩ :=
    PPL.Theorem1General.theorem1AllLeaderRootsMissGen_false_exists_hit
      ring (fun root C => decide (SPLAt ring root C)) C17 w18
      (by rw [← PPL.Theorem1General.theorem1AllLeaderRootsMissB_eq]; exact hroots)

  obtain ⟨hit, hitSuf, hw18Hit, hsplB⟩ :=
    PPL.Theorem1General.theorem1L18HitsB_exists_prefix
      ring _ C17 w18 hhit
  have hsplPrime :
      SPLAt ring root (PPL.Convergence.L18.runPPrime ring C17 hit) := by
    simpa using hsplB

  have hpostWhole :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
        ring Cmid suffix := by
    exact
      PPL.Convergence.ConstructCoupling.constructAlong_implies_postDetermineModeConstructAlong
          hn3 hpsi ring Cmid suffix hconstruct

  have hsplit17 :
      suffix =
        w17 ++ suffix.drop (theorem1H17 n) := by
    dsimp only [w17]
    exact
      (List.take_append_drop
        (theorem1H17 n) suffix).symm

  have htailSplit18 :
      suffix.drop (theorem1H17 n) =
        w18 ++
          (suffix.drop (theorem1H17 n)).drop
            (theorem1H18 n psi) := by
    dsimp only [w18]
    exact
      (List.take_append_drop
        (theorem1H18 n psi)
        (suffix.drop (theorem1H17 n))).symm

  let pre : DetSchedule n :=
    w17 ++ hit
  let rest : DetSchedule n :=
    hitSuf ++
      (suffix.drop (theorem1H17 n)).drop
        (theorem1H18 n psi)

  have hsuffixFactor :
      suffix = pre ++ rest := by
    calc
      suffix =
          w17 ++
            suffix.drop (theorem1H17 n) :=
        hsplit17
      _ =
          w17 ++
            (w18 ++
              (suffix.drop
                (theorem1H17 n)).drop
                  (theorem1H18 n psi)) :=
        congrArg
          (fun x => w17 ++ x)
          htailSplit18
      _ =
          (w17 ++ hit) ++
            (hitSuf ++
              (suffix.drop
                (theorem1H17 n)).drop
                  (theorem1H18 n psi)) := by
        rw [hw18Hit]
        simp only [List.append_assoc]
      _ = pre ++ rest := by
        rfl

  have hpostInput :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
        ring Cmid (pre ++ rest) := by
    rw [← hsuffixFactor]
    exact hpostWhole

  have hpostPre :
      PPL.Convergence.ConstructCoupling.PostDetermineModeConstructAlong
        ring Cmid pre :=
    PPL.Theorem1General.theorem1PostConstructAlong_prefix
      ring Cmid pre rest hpostInput

  have hcouplePre :
      PPL.Probability.runPPL ring Cmid pre =
        PPL.Convergence.ConstructCoupling.runPrime
          ring Cmid pre :=
    PPL.Convergence.ConstructCoupling.runCoupling
      hpsi ring Cmid pre hpostPre

  have hprime17 :
      PPL.Convergence.L18.runPPrime
          ring Cmid w17 =
        C17 := by
    simpa [C17] using
      PPL.Convergence.PrimeUnify.runPPrime_eq_runPrime
        ring Cmid w17

  have hprimePre :
      PPL.Convergence.ConstructCoupling.runPrime
          ring Cmid pre =
        PPL.Convergence.L18.runPPrime
          ring C17 hit := by
    dsimp only [pre]
    rw [← PPL.Convergence.PrimeUnify.runPPrime_eq_runPrime
          ring Cmid (w17 ++ hit),
      PPL.Convergence.L18.runPPrime_append
          ring Cmid w17 hit,
      hprime17]

  have hphysicalPrime :
      PPL.Probability.runPPL ring Cmid pre =
        PPL.Convergence.L18.runPPrime
          ring C17 hit :=
    hcouplePre.trans hprimePre

  have hsplMid :
      SPL ring
        (PPL.Probability.runPPL
          ring Cmid pre) := by
    have hsplAt :
        SPLAt ring root
          (PPL.Probability.runPPL
            ring Cmid pre) := by
      rw [hphysicalPrime]
      exact hsplPrime
    exact ⟨root, hsplAt⟩

  have hglobalRun :
      PPL.Probability.runPPL
          ring C0 (p ++ pre) =
        PPL.Probability.runPPL
          ring Cmid pre := by
    simpa [Cmid] using
      theorem1L17RunPPL_append
        ring C0 p pre

  have hsplGlobal :
      SPL ring
        (PPL.Probability.runPPL
          ring C0 (p ++ pre)) := by
    rw [hglobalRun]
    exact hsplMid

  have hk :
      pre.length <= suffix.length := by
    have hlen := congrArg List.length hsuffixFactor
    simp only [pre, rest, List.length_append] at hlen
    show (w17 ++ hit).length <= suffix.length
    simp only [List.length_append]
    omega

  have htake :
      suffix.take pre.length = pre := by
    rw [hsuffixFactor]
    exact List.take_append_length

  refine ⟨pre.length, hk, ?_⟩
  rw [htake]
  rw [PPL.Theorem1General.theorem1RunLocalSchedule_eq_runPPL]
  exact hsplGlobal


-- [copied from Leader/PPL/Theorem1CostFrom13Producer.lean:21-75]
theorem theorem1From13_tailStage_of_l18FirstHit
    (hL18 : Theorem1L18FirstHitPhaseBound)
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hn13 : 13 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p : DetSchedule n)
    (hstop :
      theorem1L17FirstHitStop
        ring C0 p = true)
    (hroom :
      p.length +
          theorem1H5ii n psi ≤
        theorem1Horizon n psi) :
    ∃ suffix : DetSchedule n,
      (p ++ suffix).length ≤
          theorem1Horizon n psi ∧
        SPL ring
          (runLocalSchedule
            ring
            (PPL.protocol
              psi (theorem1Kappa psi)).transition
            C0
            (p ++ suffix)) := by
  obtain
      ⟨phase, _hmem, hphaseLen,
        h5Good, h17Good, h18Good⟩ :=
    theorem1From13_tailJointSelection_of_l18FirstHit
      hL18
      hn3 hn13 hpsi hnpow hpsiK
      ring C0 p hstop hroom

  obtain ⟨k, _hk, hspl⟩ :=
    theorem1From13_tailSemanticPrefix_of_jointGood
      hn3 hpsi hnpow hpsiK
      ring C0 p phase
      hstop hphaseLen
      h5Good h17Good h18Good

  refine ⟨phase.take k, ?_, hspl⟩

  have htake :
      (phase.take k).length ≤
        phase.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _

  simp only [List.length_append]
  rw [hphaseLen] at htake
  omega

-- [copied from Leader/PPL/Theorem1CostFrom13Producer.lean:76-106]
theorem theorem1From13_phaseBind_of_l18FirstHit
    (hL18 : Theorem1L18FirstHitPhaseBound)
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hn13 : 13 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    ∃ word : DetSchedule n,
      word.length ≤ theorem1Horizon n psi ∧
        SPL ring
          (runLocalSchedule
            ring
            (PPL.protocol
              psi (theorem1Kappa psi)).transition
            C0 word) := by
  obtain ⟨p, _hpBound, hstop, hroom⟩ :=
    theorem1From13_firstTwoStages
      hn3 hn13 hpsi hnpow hpsiK
      ring C0

  obtain ⟨suffix, hlen, hspl⟩ :=
    theorem1From13_tailStage_of_l18FirstHit
      hL18
      hn3 hn13 hpsi hnpow hpsiK
      ring C0 p hstop hroom

  exact ⟨p ++ suffix, hlen, hspl⟩

-- [copied from Leader/PPL/Theorem1CostFrom13Producer.lean:107-125]
theorem theorem1TinyProducerFrom13_of_l18FirstHit
    (hL18 : Theorem1L18FirstHitPhaseBound) :
    Theorem1TinyProducerFrom13 := by
  intro n psi
  intro hn3 hn13 _hn64 hpsi hnpow hpsiK

  refine
    ⟨theorem1Horizon n psi, ?_⟩

  intro ring
  unfold BoundedSafeScheduleProducer
  intro C0 _hDomain _hNotSafe

  exact
    theorem1From13_phaseBind_of_l18FirstHit
      hL18
      hn3 hn13 hpsi hnpow hpsiK
      ring C0



/-- The `13 ≤ n ≤ 64` tiny producer on `psi < n`, unconditionally. -/
theorem theorem1TinyProducerFrom13_proved : Theorem1TinyProducerFrom13 :=
  theorem1TinyProducerFrom13_of_l18FirstHit theorem1L18FirstHitPhaseBound_proved

end PPL.PsiBelowN

#print axioms PPL.PsiBelowN.theorem1TinyProducerFrom13_proved

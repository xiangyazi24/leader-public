import Leader.PPL.MainTheorem.OneLeaderDynamicPadding
import Leader.PPL.Modes.ConstructionModeFailureSplits
import Leader.PPL.Modes.ConstructWindowEncounterScale
import Leader.PPL.Modes.ConstructWindowPostResetStep
import Leader.PPL.Modes.SignalLineageClosed
import Leader.PPL.Modes.StoppedClockSuffixFreeze
import Leader.PPL.Modes.SignalAbsorptionLottery
import Leader.PPL.Probability.EncounterProjection
import Leader.PPL.Probability.LotteryMoment
import Leader.PPL.SPLEntry.CountScoped

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1L5iiL18Dynamic.lean`, namespace `PPL.Superseded.LogWindow`: `Theorem1L18FirstHitPhaseBound`, `theorem1L5iiDynamicPaddedBound_proved`, `theorem1L18DynamicPaddedBound_of_l18FirstHitPhaseBound`.

Step 6c: `theorem1L18FirstHitStop_cover` is relocated, same name and
statement, to `Leader/PPL/MainTheorem/GeneralFirstHit.lean`, where it is the
rooted-`S_PL` case of `PPL.Theorem1General.theorem1L18FirstHitStop_cover_at`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-!
# Dynamic L5(ii) and L18 padding at the first C_mid cut

The stopping family is exactly the one already used by dynamic L17.
Only the phase predicate changes.
-/

def theorem1L5iiFirstHitPhaseBad
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p phase : DetSchedule n) : Bool :=
  !(PPL.Modes.Lemma5.constructAlong
    ring
    (PPL.Probability.runPPL ring C0 p)
    phase)

def theorem1L18FirstHitPhaseBad
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p phase : DetSchedule n) : Bool :=
  let Cmid :=
    PPL.Probability.runPPL ring C0 p
  let w17 :=
    phase.take (theorem1H17 n)
  let C17 :=
    PPL.Convergence.ConstructCoupling.runPrime
      ring Cmid w17
  (PPL.Modes.Lemma5.constructAlong
      ring Cmid phase &&
    @decide
      (PPL.LiteralL1
        (PPL.Probability.runPopulationSchedule
          PPL.Elim.protocolE ring
          (PPL.Elim.viewConfig Cmid)
          w17))
      (theorem1LiteralL1Decidable _)) &&
    theorem1AllLeaderRootsMissB
      ring C17
      ((phase.drop (theorem1H17 n)).take
        (theorem1H18 n psi))

/-! ## Common first-hit prefix facts -/

theorem theorem1DynamicFirstHitPrefixState
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (t : Nat)
    (hcut :
      theorem1MidCut ring C0 word = some t) :
    PPL.Probability.runPPL
        ring C0
        (word.take
          (theorem1H16 n psi + t)) =
      PPL.Probability.runPPL
        ring
        (theorem1State16
          ring C0 word)
        ((theorem1Block5i
          psi word).take t) := by
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
      t <=
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
      t <= theorem1H5i n := by
    have hlen :
        (theorem1Block5i
          psi word).length <=
          theorem1H5i n := by
      unfold theorem1Block5i
      simp only [List.length_take]
      exact Nat.min_le_left _ _
    exact Nat.le_trans htBlock hlen
  rw [<-
    theorem1L17Take_append_take_drop
      word
      (theorem1H16 n psi)
      t]
  rw [theorem1L17RunPPL_append]
  simp only
    [theorem1State16,
      theorem1Block16,
      theorem1Block5i,
      List.take_take]
  rw [Nat.min_eq_left htH5i]

theorem theorem1DynamicFirstHitFactor
    {n psi T : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hT : T <= theorem1H5ii n psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n)
    (hword :
      word ∈
        allSchedules n
          (theorem1Horizon n psi))
    (t : Nat)
    (hcut :
      theorem1MidCut ring C0 word = some t)
    (hreach :
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0
          (theorem1Block16 psi word) =
        true) :
    ∃ p : DetSchedule n,
      ∃ phase : DetSchedule n,
        ∃ pad : DetSchedule n,
          theorem1L17FirstHitStop
              ring C0 p = true ∧
            phase ∈ allSchedules n T ∧
            word = p ++ phase ++ pad ∧
            p =
              word.take
                (theorem1H16 n psi + t) ∧
            phase =
              (word.drop
                (theorem1H16 n psi + t)).take T := by
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
      t <=
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
      t <= theorem1H5i n := by
    have hlen :
        (theorem1Block5i
          psi word).length <=
          theorem1H5i n := by
      unfold theorem1Block5i
      simp only [List.length_take]
      exact Nat.min_le_left _ _
    exact Nat.le_trans htBlock hlen

  have hwordLength :
      word.length =
        theorem1Horizon n psi :=
    allSchedules_schedule_length
      n
      (theorem1Horizon n psi)
      word hword

  have hkPrefix :
      theorem1H16 n psi + t <=
        word.length := by
    rw [hwordLength,
      theorem1Horizon_eq_phase_sum]
    omega

  have hpLength :
      (word.take
        (theorem1H16 n psi + t)).length =
        theorem1H16 n psi + t := by
    simp only [List.length_take]
    exact Nat.min_eq_left hkPrefix

  have hpA :
      theorem1H16 n psi <=
        (word.take
          (theorem1H16 n psi + t)).length := by
    rw [hpLength]
    omega

  have hblockPrefix :
      (word.take
        (theorem1H16 n psi + t)).take
          (theorem1H16 n psi) =
        theorem1Block16 psi word := by
    unfold theorem1Block16
    rw [List.take_take]
    rw [Nat.min_eq_left (by omega)]

  have hCPB16 :
      PPL.CPB ring
        (PPL.Probability.runPPL
          ring C0
          (theorem1Block16
            psi word)) := by
    apply of_decide_eq_true
    rw [<-
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
            (theorem1H16 n psi + t)).take
              (theorem1H16 n psi))) := by
    rw [hblockPrefix]
    exact hCPB16

  have hsuffix :
      (word.take
        (theorem1H16 n psi + t)).drop
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
        min t (theorem1H5i n) = t :=
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
              (theorem1H16 n psi + t)).take
                (theorem1H16 n psi)))
          ((word.take
            (theorem1H16 n psi + t)).drop
              (theorem1H16 n psi)) =
        some
          ((word.take
            (theorem1H16 n psi + t)).drop
              (theorem1H16 n psi)).length := by
    rw [hblockPrefix, hsuffix, hsufLen]
    simpa [theorem1State16]
      using hfirstTake

  have hstop :
      theorem1L17FirstHitStop
          ring C0
          (word.take
            (theorem1H16 n psi + t)) =
        true := by
    unfold theorem1L17FirstHitStop
    exact decide_eq_true
      ⟨hpA, hCPBp, hhitP⟩

  have hphaseAvail :
      T <=
        (word.drop
          (theorem1H16 n psi + t)).length := by
    rw [List.length_drop,
      hwordLength,
      theorem1Horizon_eq_phase_sum]
    omega

  have hphaseLength :
      ((word.drop
        (theorem1H16 n psi + t)).take T).length =
        T := by
    simp only [List.length_take]
    exact Nat.min_eq_left hphaseAvail

  have hphaseMem :
      (word.drop
        (theorem1H16 n psi + t)).take T ∈
        allSchedules n T :=
    mem_allSchedules_of_length
      n T
      ((word.drop
        (theorem1H16 n psi + t)).take T)
      hphaseLength

  have hfactor :
      word =
        word.take
            (theorem1H16 n psi + t) ++
          ((word.drop
            (theorem1H16 n psi + t)).take T ++
            (word.drop
              (theorem1H16 n psi + t)).drop T) := by
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
              (theorem1H16 n psi + t)).take T ++
              (word.drop
                (theorem1H16 n psi + t)).drop T) := by
        exact
          congrArg
            (fun tail =>
              word.take
                  (theorem1H16 n psi + t) ++
                tail)
            (List.take_append_drop
              T
              (word.drop
                (theorem1H16 n psi + t))).symm

  exact
    ⟨word.take
        (theorem1H16 n psi + t),
      (word.drop
        (theorem1H16 n psi + t)).take T,
      (word.drop
        (theorem1H16 n psi + t)).drop T,
      hstop,
      hphaseMem,
      (by rw [List.append_assoc]; exact hfactor),
      rfl,
      rfl⟩

/-! ## L5(ii): closed local phase count -/

theorem theorem1L5iiFirstHitStop_local
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p : DetSchedule n)
    (hp :
      theorem1L17FirstHitStop ring C0 p = true) :
    n *
        (allSchedules n
          (theorem1H5ii n psi)).countP
          (theorem1L5iiFirstHitPhaseBad
            ring C0 p) <=
      4 * n ^ theorem1H5ii n psi := by
  unfold theorem1L17FirstHitStop at hp
  have hp' := of_decide_eq_true hp
  rcases hp' with
    ⟨_hpLen, _hpCPB, hpHit⟩

  have hmid0 :=
    theorem1FirstHitCut_some_endpoint
      ring
      PPL.Modes.Lemma5.midPhysicalB
      (PPL.Probability.runPPL
        ring C0
        (p.take
          (theorem1H16 n psi)))
      (p.drop
        (theorem1H16 n psi))
      hpHit
  simp only [List.take_length] at hmid0

  have hrun :
      PPL.Probability.runPPL ring C0 p =
        PPL.Probability.runPPL
          ring
          (PPL.Probability.runPPL
            ring C0
            (p.take
              (theorem1H16 n psi)))
          (p.drop
            (theorem1H16 n psi)) := by
    have happ :=
      theorem1L17RunPPL_append
        ring C0
        (p.take
          (theorem1H16 n psi))
        (p.drop
          (theorem1H16 n psi))
    rw [List.take_append_drop] at happ
    exact happ

  let C :
      Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C0 p

  have hmid :
      PPL.Modes.Lemma5.midPhysicalB C = true := by
    dsimp only [C]
    rw [hrun]
    exact hmid0

  have hsplit :=
    PPL.Modes.Lemma5.lemma5iiFailureSplit
      hn3 hpsi
      theorem1Lemma5iiC_ge_three
      (theorem1Kappa_eq_lemma5ii_form psi)
      hnpow ring C hmid

  have henc :=
    (PPL.Modes.Lemma5.lemma5iiEncounterCount_of_scale
      PPL.Modes.Lemma5.lemma5iiEncounterScaleArithmetic)
      hn3 hpsi
      theorem1Lemma5iiC_ge_three
      (theorem1Kappa_eq_lemma5ii_form psi)
      hnpow ring
      PPL.Probability.predictableHostTails

  have hclk :=
    PPL.Modes.Lemma5.lemma5iiPostResetClockCount_proved
      hn3 hpsi
      theorem1Lemma5iiC_ge_three
      (theorem1Kappa_eq_lemma5ii_form psi)
      hnpow ring C hmid
      (PPL.Modes.SignalLineage.signalLineageOwnership ring)
      PPL.Probability.stoppedClockSuffixBoundsCorrected
      PPL.Modes.Lemma9.modeStoppedTreeTransfer
      PPL.Probability.wlgHeadOffsetBounds
      PPL.Probability.lotteryCountBounds

  have hsplit' :=
    Nat.mul_le_mul_left n hsplit
  simp only [Nat.mul_add] at hsplit'
  have hsum :=
    Nat.add_le_add henc hclk
  have htotal :=
    Nat.le_trans hsplit' hsum

  have hfun :
      theorem1L5iiFirstHitPhaseBad ring C0 p =
        fun w =>
          !(PPL.Modes.Lemma5.constructAlong
            ring
            (PPL.Probability.runPPL ring C0 p)
            w) := rfl
  rw [hfun]
  simpa
    [theorem1L5iiFirstHitPhaseBad,
      PPL.Modes.Lemma5.lemma5iiFailureCount,
      theorem1H5ii,
      C]
    using
      (show
        n * PPL.Modes.Lemma5.lemma5iiFailureCount ring C <=
          4 *
            n ^
              PPL.Modes.Lemma5.lemma5iiHorizon
                n psi (theorem1Kappa psi) by
        calc
          n * PPL.Modes.Lemma5.lemma5iiFailureCount ring C <=
              2 *
                  n ^
                    PPL.Modes.Lemma5.lemma5iiHorizon
                      n psi (theorem1Kappa psi) +
                2 *
                  n ^
                    PPL.Modes.Lemma5.lemma5iiHorizon
                      n psi (theorem1Kappa psi) :=
            htotal
          _ =
              4 *
                n ^
                  PPL.Modes.Lemma5.lemma5iiHorizon
                    n psi (theorem1Kappa psi) := by
            omega)

/-! ## Event-specific covers over the common first-hit factorization -/

theorem theorem1L5iiFirstHitStop_cover
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
      theorem1Bad5iiB ring C0 word = true) :
    ∃ p : DetSchedule n,
      ∃ phase : DetSchedule n,
        ∃ pad : DetSchedule n,
          theorem1L17FirstHitStop ring C0 p = true ∧
            phase ∈
              allSchedules n
                (theorem1H5ii n psi) ∧
            word = p ++ phase ++ pad ∧
            theorem1L5iiFirstHitPhaseBad
              ring C0 p phase = true := by
  cases hcut :
      theorem1MidCut ring C0 word with
  | none =>
      simp [theorem1Bad5iiB,
        theorem1MidState, hcut] at hbad
  | some t =>
      have hbadCore := hbad
      unfold theorem1Bad5iiB at hbadCore
      rw [hcut] at hbadCore
      simp only [theorem1MidState, hcut] at hbadCore
      have hpair :=
        Bool.and_eq_true_iff.mp hbadCore
      have hreach := hpair.1
      have hmiss := hpair.2

      obtain
          ⟨p, phase, pad,
            hstop, hphaseMem, hfactor,
            hpEq, hphaseEq⟩ :=
        theorem1DynamicFirstHitFactor
          hn3 hpsi
          (T := theorem1H5ii n psi)
          (Nat.le_refl _)
          ring C0 word hword t hcut hreach

      have hpState :=
        theorem1DynamicFirstHitPrefixState
          ring C0 word t hcut

      subst p
      subst phase

      have hphaseBad :
          theorem1L5iiFirstHitPhaseBad
              ring C0
              (word.take
                (theorem1H16 n psi + t))
              ((word.drop
                (theorem1H16 n psi + t)).take
                  (theorem1H5ii n psi)) =
            true := by
        unfold theorem1L5iiFirstHitPhaseBad
        rw [hpState]
        simpa [theorem1QuietWord]
          using hmiss

      exact
        ⟨word.take
            (theorem1H16 n psi + t),
          (word.drop
            (theorem1H16 n psi + t)).take
              (theorem1H5ii n psi),
          pad,
          hstop,
          hphaseMem,
          hfactor,
          hphaseBad⟩

end PPL

import Leader.PPL.ReachCPB.ModeDriver
import Leader.PPL.Convergence.BulletLineageSweepReach
import Leader.PPL.ReachCPB.StepDist
import Leader.PPL.ReachCPB.LastPairRow
import Leader.PPL.ReachCPB.CdGeometryPairStep
import Leader.PPL.MainTheorem.ReachCPBNewFreshExclusion
import Leader.PPL.MainTheorem.ReachCPBPaddedClosed
import Leader.PPL.MainTheorem.Kappa

/-!
# Deterministic Lemma 16: every configuration can reach `C_PB`

The probabilistic Lemma 16 (`lemma16_wordBound_capped`) counts failing
scheduler words over the horizon `lemma16Horizon n psi kappa`.  This module
proves the corresponding *possible convergence* statement: from every
configuration of the literal P_PL protocol there is an explicit scheduler word
of length at most that horizon whose endpoint is `C_PB`.

The word is the concatenation of five blocks, one per charged Lemma-16 phase,
each chosen deterministically from the configuration reached so far:

1. **H15** (bullet sweep): the fixed word `lemma15SweepWord ring`
   (`(seq_R(0,n))^2`), forced by `lemma15SublistSweep_proved`; endpoint
   `AllLivePeaceful`.
2. **H6** (mode clock): the fixed driver of `lemma16ModeForcingCapped_exists`;
   endpoint `C_PB` or `DetectReadyCapped`.
3. **HDist**: the one-letter selector of `Lemma16DistForcingCappedSpec`
   (proved by `lemma16DistForcingCapped lemma16DistForcingCappedStep`);
   endpoint `C_PB` or `DistReadyCapped`.
4. **HLast**: the length-`n` selector of `Lemma16LastForcingCappedSpec`
   (proved by `lemma16LastForcingCapped
   lemma16LastForcingCappedStepSpec_proved`); endpoint `C_PB` or
   `LastReadyCapped`.
5. **HToken**: the Lemma-4 word `PPL.lemma4Word ring k psi` at the
   mismatch witness `k` (the forcing argument inside `tokenPhaseBoundCapped`,
   exported here as `lemma16TokenForcingCapped_exists`); endpoint `C_PB`.

Whenever a block ends in `C_PB`, all later blocks are replaced by the empty
word, so no closure argument is needed for the chain itself.

Premises actually used: `3 ≤ n`, `2 ≤ psi`, `0 < kappa` (H6 driver), and
`n ≤ 2^psi` (HToken: the mismatch witness `Lemma16MismatchWitnessCappedSpec`
and `leaderless_not_perfect` need it).  No premise supplied only by a random
run is used.
-/

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false

open PPL.Probability

/-- Running a concatenated word is running the two parts in sequence. -/
private theorem det_runPPL_append
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (u v : DetSchedule n) :
    PPL.Probability.runPPL ring C (u ++ v) =
      PPL.Probability.runPPL ring
        (PPL.Probability.runPPL ring C u) v := by
  induction u generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [List.cons_append,
        PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule]
      exact
        ih
          (C :=
            PPL.Probability.pplStep ring C e)

/-! ## The mismatch witness, unconditionally -/

/-- `Lemma16MismatchWitnessCappedSpec` with every leaf discharged, assembled
from the same proved rows as `theorem1L16PaddedBound_proved`
(`Theorem1L16PaddedCoreOnly` → `TwoLeaves` → `ThreeLeaves` →
`TerminalRows` → `TerminalUnique` → `NewFresh`).
-/
theorem lemma16MismatchWitnessCappedSpec_proved :
    Lemma16MismatchWitnessCappedSpec :=
  lemma16MismatchWitnessCappedSpec_of_newFreshForcesCPB
    (lemma16MismatchHistNewFreshForcesCPB_of_canonAgedRows
      (lemma16PostEpochFreshLiveStepGeomLastCanon_of_literalAged
        lemma16PostEpochFreshSelectedLiveLiteralAgedRow_proved)
      (lemma16PostEpochFreshNewCompletionStepGeomDistCanonAged_of_stateLocalNoEarlyUnique
        lemma16FreshNoEarlyCompletionIdCanon_proved
        (lemma16PostEpochFreshNewCompletionStateLocalAgedNoEarlyRowUnique_of_terminalCompare
          (lemma16PostEpochFreshTerminalCompareLiteralRowUnique_of_selectedPassBirthView
            lemma16TerminalSelectedPassBirthViewRow_proved))))

/-! ## The five block selectors -/

/-- **H15 block.** From every configuration the fixed two-sweep word
`lemma15SweepWord ring` (length `2n ≤ lemma16H15 n`) makes every live bullet
peaceful.
-/
theorem lemma15SweepForcing_exists
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    ∃ word : DetSchedule n,
      word.length ≤ lemma16H15 n ∧
        AllLivePeaceful ring (runPPL ring C word) := by
  refine ⟨PPL.Convergence.BulletSweep.lemma15SweepWord ring, ?_, ?_⟩
  · rw [PPL.Convergence.BulletSweep.lemma15SweepWord_length]
    unfold lemma16H15
    have h1 : 1 ≤ 2 * n + 4 * lemma16K n := by omega
    have h := Nat.mul_le_mul (Nat.le_refl (2 * n)) h1
    rw [Nat.mul_one] at h
    exact h
  · exact
      PPL.Convergence.BulletLineage.lemma15SublistSweep_proved
        hn3 hpsi ring C
        (PPL.Convergence.BulletSweep.lemma15SweepWord ring)
        (List.Sublist.refl _)

/-- **HDist block.** From every `DetectReadyCapped` configuration some
one-letter word ends in `C_PB` or `DistReadyCapped`.
-/
theorem lemma16DistForcingCapped_exists
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hC : DetectReadyCapped ring C) :
    ∃ word : DetSchedule n,
      word.length ≤ lemma16HDist n ∧
        (PPL.CPB ring (runPPL ring C word) ∨
          DistReadyCapped ring (runPPL ring C word)) := by
  obtain ⟨word, hlen, hforce⟩ :=
    lemma16DistForcingCapped lemma16DistForcingCappedStep
      hn3 hpsi ring C hC
  refine ⟨word, ?_, hforce word (List.Sublist.refl _)⟩
  rw [hlen]
  unfold lemma16HDist
  have hpos : 0 < 2 * n * (1 + 4 * lemma16K n) :=
    Nat.mul_pos (by omega) (by omega)
  omega

/-- **HLast block.** From every `DistReadyCapped` configuration some word of
length `n` ends in `C_PB` or `LastReadyCapped`.
-/
theorem lemma16LastForcingCapped_exists
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hC : DistReadyCapped ring C) :
    ∃ word : DetSchedule n,
      word.length ≤ lemma16HLast n ∧
        (PPL.CPB ring (runPPL ring C word) ∨
          LastReadyCapped ring (runPPL ring C word)) := by
  obtain ⟨word, hlen, hforce⟩ :=
    lemma16LastForcingCapped lemma16LastForcingCappedStepSpec_proved
      hn3 hpsi ring C hC
  refine ⟨word, ?_, hforce word (List.Sublist.refl _)⟩
  rw [hlen]
  unfold lemma16HLast
  have h1 : 1 ≤ 2 * n := by omega
  have h2 : n ≤ n + 4 * lemma16K n := by omega
  have h := Nat.mul_le_mul h1 h2
  rw [Nat.one_mul] at h
  exact h

/-- **HToken selector.** For `3 ≤ n ≤ 2^psi`, `2 ≤ psi`, every
`LastReadyCapped` configuration has a site `k` such that every schedule
containing the Lemma-4 word `PPL.lemma4Word ring k psi` as a sublist ends in
`C_PB`.  This is the local `hforce` of `tokenPhaseBoundCapped`, exported with
every input discharged: the mismatch witness
`lemma16MismatchWitnessCappedSpec_proved`, the trace
`lemma16CdTraceUntilSuccess_proved lemma16CdGeometryPairStepSpec_proved`, and
the deterministic core `PPL.lemma4_deterministic_core_proved`.
-/
theorem lemma16TokenForcingCapped_selector
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hC : LastReadyCapped ring C) :
    ∃ k : Fin n,
      ∀ schedule : DetSchedule n,
        (PPL.lemma4Word ring k psi).Sublist schedule →
          PPL.CPB ring (runPPL ring C schedule) := by
  have hnotPerfect : ¬ PPL.Perfect ring C :=
    PPL.leaderless_not_perfect hn3 hnpow ring C hC.1.1.1.2.1
  obtain ⟨k, kind, hCd, hcompletion⟩ :=
    lemma16MismatchWitnessCappedSpec_proved
      hn3 hpsi hnpow ring C hC hnotPerfect
  refine ⟨k, ?_⟩
  intro schedule hsub
  have htrace :=
    lemma16CdTraceUntilSuccessCapped_of_uncapped
      (lemma16CdTraceUntilSuccess_proved
        lemma16CdGeometryPairStepSpec_proved)
      hn3 hpsi ring C k kind hC hCd schedule
  rcases htrace with hcpb | hCdTrace
  · exact hcpb
  · exact
      hcompletion schedule
        (PPL.lemma4_deterministic_core_proved
          hpsi ring k kind C schedule hCdTrace hsub)

/-- **HToken block.** Every `LastReadyCapped` configuration reaches `C_PB`
within `lemma16HToken n psi` steps (the witness word is
`PPL.lemma4Word ring k psi`, of length `lemma16L4 psi`).
-/
theorem lemma16TokenForcingCapped_exists
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hC : LastReadyCapped ring C) :
    ∃ word : DetSchedule n,
      word.length ≤ lemma16HToken n psi ∧
        PPL.CPB ring (runPPL ring C word) := by
  obtain ⟨k, hforce⟩ :=
    lemma16TokenForcingCapped_selector hn3 hpsi hnpow ring C hC
  refine ⟨PPL.lemma4Word ring k psi, ?_,
    hforce _ (List.Sublist.refl _)⟩
  rw [PPL.lemma4Word_length hpsi ring k]
  unfold lemma16HToken lemma16L4
  have h1 : 1 ≤ 2 * n := by omega
  have h2 : 8 * psi * psi - 4 * psi ≤
      8 * psi * psi - 4 * psi + 4 * lemma16K n := by omega
  have h := Nat.mul_le_mul h1 h2
  rw [Nat.one_mul] at h
  exact h

/-! ## Chaining the blocks -/

/-- From `C_PB` or `LastReadyCapped`: reach `C_PB` within `HToken`. -/
private theorem det_stage_token
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hD : PPL.CPB ring D ∨ LastReadyCapped ring D) :
    ∃ word : DetSchedule n,
      word.length ≤ lemma16HToken n psi ∧
        PPL.CPB ring (runPPL ring D word) := by
  rcases hD with hcpb | hlast
  · exact ⟨[], Nat.zero_le _, hcpb⟩
  · exact lemma16TokenForcingCapped_exists hn3 hpsi hnpow ring D hlast

/-- From `C_PB` or `DistReadyCapped`: reach `C_PB` within
`HLast + HToken`. -/
private theorem det_stage_last
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hD : PPL.CPB ring D ∨ DistReadyCapped ring D) :
    ∃ word : DetSchedule n,
      word.length ≤ lemma16HLast n + lemma16HToken n psi ∧
        PPL.CPB ring (runPPL ring D word) := by
  rcases hD with hcpb | hdist
  · exact ⟨[], Nat.zero_le _, hcpb⟩
  · obtain ⟨u, hu, hD'⟩ :=
      lemma16LastForcingCapped_exists hn3 hpsi ring D hdist
    obtain ⟨v, hv, hend⟩ :=
      det_stage_token hn3 hpsi hnpow ring (runPPL ring D u) hD'
    refine ⟨u ++ v, ?_, ?_⟩
    · rw [List.length_append]
      omega
    · rw [det_runPPL_append]
      exact hend

/-- From `C_PB` or `DetectReadyCapped`: reach `C_PB` within
`HDist + HLast + HToken`. -/
private theorem det_stage_dist
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hD : PPL.CPB ring D ∨ DetectReadyCapped ring D) :
    ∃ word : DetSchedule n,
      word.length ≤
          lemma16HDist n + lemma16HLast n + lemma16HToken n psi ∧
        PPL.CPB ring (runPPL ring D word) := by
  rcases hD with hcpb | hdet
  · exact ⟨[], Nat.zero_le _, hcpb⟩
  · obtain ⟨u, hu, hD'⟩ :=
      lemma16DistForcingCapped_exists hn3 hpsi ring D hdet
    obtain ⟨v, hv, hend⟩ :=
      det_stage_last hn3 hpsi hnpow ring (runPPL ring D u) hD'
    refine ⟨u ++ v, ?_, ?_⟩
    · rw [List.length_append]
      omega
    · rw [det_runPPL_append]
      exact hend

/-- From `AllLivePeaceful`: reach `C_PB` within
`H6 + HDist + HLast + HToken`. -/
private theorem det_stage_mode
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 0 < kappa)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hD : AllLivePeaceful ring D) :
    ∃ word : DetSchedule n,
      word.length ≤
          lemma16H6 n psi kappa + lemma16HDist n + lemma16HLast n +
            lemma16HToken n psi ∧
        PPL.CPB ring (runPPL ring D word) := by
  obtain ⟨u, hu, hD'⟩ :=
    lemma16ModeForcingCapped_exists hn3 hpsi hkappa ring D hD
  obtain ⟨v, hv, hend⟩ :=
    det_stage_dist hn3 hpsi hnpow ring (runPPL ring D u) hD'
  refine ⟨u ++ v, ?_, ?_⟩
  · rw [List.length_append]
    omega
  · rw [det_runPPL_append]
    exact hend

/-! ## Headline -/

/-- **Deterministic Lemma 16 (possible convergence to `C_PB`).**
For `3 ≤ n ≤ 2^psi`, `2 ≤ psi` and `0 < kappa`, every configuration `C` of
the literal P_PL protocol has a scheduler word of length at most the frozen
Lemma-16 horizon `lemma16Horizon n psi kappa`
(`= H15 + H6 + HDist + HLast + HToken`) whose endpoint is `C_PB`.

The word is the concatenation of the five block witnesses (see the module
docstring); each block after the first is selected from the configuration
reached by the earlier blocks, and is empty once `C_PB` has been reached.
-/
theorem reachCPB_exists
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 0 < kappa)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n) :
    ∀ C : Config n psi kappa,
      ∃ word : DetSchedule n,
        word.length ≤ lemma16Horizon n psi kappa ∧
          PPL.CPB ring (runPPL ring C word) := by
  intro C
  obtain ⟨u, hu, hC'⟩ := lemma15SweepForcing_exists hn3 hpsi ring C
  obtain ⟨v, hv, hend⟩ :=
    det_stage_mode hn3 hpsi hkappa hnpow ring (runPPL ring C u) hC'
  refine ⟨u ++ v, ?_, ?_⟩
  · rw [List.length_append]
    unfold lemma16Horizon
    omega
  · rw [det_runPPL_append]
    exact hend

/-- `reachCPB_exists` at the Theorem-1 parameter `kappa = theorem1Kappa
psi` (the positivity premise is discharged; `n ≤ 2^psi` remains, as in
`Theorem1L16PaddedBound`).
-/
theorem reachCPB_exists_theorem1Kappa
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n) :
    ∀ C : Config n psi (PPL.theorem1Kappa psi),
      ∃ word : DetSchedule n,
        word.length ≤
            lemma16Horizon n psi (PPL.theorem1Kappa psi) ∧
          PPL.CPB ring (runPPL ring C word) := by
  have hpos : 0 < PPL.theorem1Kappa psi := by
    rw [PPL.theorem1Kappa_eq_lemma16_form psi]
    have h6 := PPL.theorem1ModeC_ge_six
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  exact reachCPB_exists hn3 hpsi hpos hnpow ring

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16MismatchWitnessCappedSpec_proved
#print axioms PPL.Convergence.ReachCPB.lemma15SweepForcing_exists
#print axioms PPL.Convergence.ReachCPB.lemma16DistForcingCapped_exists
#print axioms PPL.Convergence.ReachCPB.lemma16LastForcingCapped_exists
#print axioms PPL.Convergence.ReachCPB.lemma16TokenForcingCapped_selector
#print axioms PPL.Convergence.ReachCPB.lemma16TokenForcingCapped_exists
#print axioms PPL.Convergence.ReachCPB.reachCPB_exists
#print axioms PPL.Convergence.ReachCPB.reachCPB_exists_theorem1Kappa

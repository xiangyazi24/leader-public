import Leader.PPL.PsiBelowN.FromThirteen
import Leader.PPL.MainTheorem.PossibleUpToEight
import Leader.PPL.Elim.OneLeaderShortWord
import Leader.PPL.MainTheorem.GeneralSmallN
import Leader.PPL.MainTheorem.GeneralExhaustive

/-!
P_PL Theorem 1 cleanup, phase 2: four unused private copies of `Theorem1PossibleUpto8` helpers were
deleted here (`up8FoldlAnd_of_all`, `up8AllAgentsB_of_forall`, `up8Forall_of_allAgentsB`, `up8RightNeighbor_ne_self`).

Step 6e: `upto8_tailSPL_of_mid` is the rooted-`S_PL` case of
`PPL.Theorem1General.theorem1TailOfMid_at` (statement unchanged); the
private copies `up8FoldlAnd_true`, `up8PB_run`, `up8SumIte_eq_countP`,
`up8Unique_of_leaderCount`, `up8L18Hit_exists_prefix` and
`up8RunLocalSchedule_eq_runPPL` are gone (general versions in
`Leader/PPL/Theorem1General/`).

Step 6d: `theorem1FromCPB_firstTwoStages` and
`theorem1FromCPB_tailJointSelection_of_coeff` are special cases of
`theorem1FirstTwoStages_of_cpbPrefix` and `theorem1TailJointSelection_of_coeff`
(`From13.lean`), statements unchanged; the private copies
`q20313cpb_sum_if_count`, `q20313cpb_countP_take_pad` and
`q20313cpb_firstHitCut_some_of_reachesAux` are gone.
-/

/-!
# P_PL Theorem 1 on `psi < n`: possible convergence and the producer for `n ≤ 12`

Copies of the deterministic small-n route on the domain `psi < n`:

* `9 ≤ n ≤ 12`: deterministic L16 (`reachCPB_exists_theorem1Kappa`, no window
  premise) followed by the CPB → SPL tail (`Theorem1PossibleFromCPB.lean`),
  whose window use is the quiet-window fit and the L18 first-hit interface;
* `n ≤ 8`: the Construct-slack tail (`Theorem1PossibleUpto8.lean`).  The
  original derived `psi < n` from the window and then used it twice: as the
  L18 scope and, with `n ≤ 8`, for `n * psi ≤ 64` in the clock-slack
  arithmetic.  Both uses need only `psi < n`.  The admissible pairs grow
  (e.g. `(8, 7)`), but the proofs are uniform in `psi`.
* the finite maximum over configurations (`Theorem1PPLUpto12FromPossible.lean`).
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
open PPL.Probability

/-! ## 9 ≤ n ≤ 12 (copied from `Theorem1PossibleFromCPB.lean`, `Theorem1PPLFrom9To12.lean`) -/

-- [copied from Leader/PPL/MainTheorem/PossibleFromCPB.lean:124-483]
/--
Copy of `theorem1From13_tailJointSelection_of_l18FirstHit` with its only
threshold use, `13 ≤ n`, replaced by the premise it actually consumes,
`4 + 1 + 1 < n` (L5(ii) coefficient 4, L17 coefficient 1, L18 coefficient 1).

For one first-hit prefix `p`, this selects one H5(ii)-length suffix on which
the L5(ii), L17 and L18 tail failure predicates are all false.  The body is
unchanged apart from the selector's coefficient premise.
-/
theorem theorem1FromCPB_tailJointSelection_of_coeff
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
            ring C0 p suffix = false :=
  theorem1TailJointSelection_of_coeff
    hL18 hn3 hcoeff hpsi hnpow hpsiK ring C0 p hstop hroom

-- [copied from Leader/PPL/MainTheorem/PossibleFromCPB.lean:536-774]
/--
First two stages restarted at a CPB configuration.

Given `C0` with `PPL.CPB ring C0`, the H16 slot of the frame is filled by
the padding word `replicate H16 e0` (CPB is preserved by every run), and the
Lemma-5(i) word bound at the padded endpoint is converted into an explicit
word by the coefficient-8 selector, which needs only `8 < n`.  The returned
prefix `p = pad ++ w5iHit` stops exactly at the first `C_mid` cut
(`theorem1L17FirstHitStop`) and leaves room for the H5(ii) tail.

This is the Stage-2 body of `theorem1From13_firstTwoStages` with the L16
selection replaced by padding.
-/
theorem theorem1FromCPB_firstTwoStages
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (h8 : 8 < n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (hCPB0 : PPL.CPB ring C0) :
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

  /- Stage 1 replaced: pad the H16 slot with one fixed edge. -/
  let e0 : Fin n := ⟨0, hnpos⟩

  let w16 : DetSchedule n :=
    List.replicate (theorem1H16 n psi) e0

  have hw16Len :
      w16.length = theorem1H16 n psi := by
    simp [w16]

  let C16 :
      Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C0 w16

  have hCPB : PPL.CPB ring C16 :=
    PPL.Convergence.ReachCPB.cpb_run_closed
      hn3 hpsi ring C0 w16 hCPB0

  exact
    theorem1FirstTwoStages_of_cpbPrefix
      hn3 h8 hpsi hnpow ring C0 w16 hw16Len hCPB

-- [copied from Leader/PPL/MainTheorem/PossibleFromCPB.lean:840-884]
/--
**Post-CPB possible convergence, `8 < n`.**

For the Theorem-1 window (`3 ≤ n`, `2 ≤ psi`, `n ≤ 2^psi`,
`psi < n`) with `8 < n`, every configuration satisfying `PPL.CPB`
has a scheduler word some prefix of which reaches `SPL`.

Proof: `theorem1FromCPB_firstTwoStages` (H16 padding + L5(i), coefficient 8),
then the joint tail selection with coefficient `4+1+1 < n` and the proved L18
first-hit bound, then the semantic prefix theorem, then the endpoint-to-prefix
adapter.
-/
theorem theorem1PossibleFromCPB_of_eight_lt
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (h8 : 8 < n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi))
    (hCPB : PPL.CPB ring C) :
    ∃ word : DetSchedule n,
      theorem1ReachesSPL ring C word = true := by
  obtain ⟨p, _hpBound, hstop, hroom⟩ :=
    theorem1FromCPB_firstTwoStages
      hn3 h8 hpsi hnpow hpsiK ring C hCPB
  obtain
      ⟨suffix, _hmem, hsuffixLen,
        h5iiGood, h17Good, h18Good⟩ :=
    theorem1FromCPB_tailJointSelection_of_coeff
      theorem1L18FirstHitPhaseBound_proved
      hn3 (by omega) hpsi hnpow hpsiK
      ring C p hstop hroom
  obtain ⟨k, _hk, hspl⟩ :=
    theorem1From13_tailSemanticPrefix_of_jointGood
      hn3 hpsi hnpow hpsiK
      ring C p suffix
      hstop hsuffixLen
      h5iiGood h17Good h18Good
  exact
    ⟨p ++ suffix.take k,
      theorem1ReachesSPL_of_runLocalEndpoint
        ring C (p ++ suffix.take k) hspl⟩

-- [copied from Leader/PPL/MainTheorem/PossibleFromCPB.lean:887-900]
/-- Pointwise possible convergence of `Theorem1PossibleConvergenceUpto12`,
restricted to `9 ≤ n ≤ 12`. -/
def Theorem1PossibleConvergenceFrom9To12 : Prop :=
  ∀ {n psi : Nat},
    9 ≤ n →
    n ≤ 12 →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi < n →
    ∀ (ring : DirectedRing n)
      (C : Config n psi (theorem1Kappa psi)),
      ∃ word : DetSchedule n,
        theorem1ReachesSPL ring C word = true

-- [copied from Leader/PPL/MainTheorem/PossibleFromCPB.lean:901-933]
/--
The 9-to-12 slice of `Theorem1PossibleConvergenceUpto12`, given
arbitrary-start → CPB reachability on the same window as a hypothesis.

First run the hypothesised word to CPB, then apply
`theorem1PossibleFromCPB_of_eight_lt`, and concatenate
(`theorem1ReachesSPL_append_of_run`).  The CPB hypothesis is conditional
input; it is not proved here.
-/
theorem theorem1PossibleConvergenceFrom9To12_of_reachCPB
    (hreachCPB :
      ∀ {n psi : Nat},
        9 ≤ n →
        n ≤ 12 →
        2 ≤ psi →
        n ≤ 2 ^ psi →
        psi < n →
        ∀ (ring : DirectedRing n)
          (C : Config n psi (theorem1Kappa psi)),
          ∃ w : DetSchedule n,
            PPL.CPB ring (PPL.Probability.runPPL ring C w)) :
    Theorem1PossibleConvergenceFrom9To12 := by
  intro n psi hn9 hn12 hpsi hnpow hpsiK ring C
  obtain ⟨w, hw⟩ :=
    hreachCPB hn9 hn12 hpsi hnpow hpsiK ring C
  obtain ⟨v, hv⟩ :=
    theorem1PossibleFromCPB_of_eight_lt
      (by omega) (by omega) hpsi hnpow hpsiK
      ring (PPL.Probability.runPPL ring C w) hw
  exact
    ⟨w ++ v,
      theorem1ReachesSPL_append_of_run ring C w v hv⟩

-- [copied from Leader/PPL/MainTheorem/PossibleUniformBound.lean:39-52]
/-- C.4 residual for `n ≤ 12`, pointwise form: for each admissible pair, every
ring and every configuration, some schedule visits `SPL`. -/
def Theorem1PossibleConvergenceUpto12 : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    n ≤ 12 →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi < n →
    ∀ (ring : DirectedRing n)
      (C : Config n psi (theorem1Kappa psi)),
      ∃ word : DetSchedule n,
        theorem1ReachesSPL ring C word = true

-- [copied from Leader/PPL/Theorem1PPLFrom9To12.lean:22-31]
/-- Possible convergence on `9 ≤ n ≤ 12`, unconditionally. -/
theorem theorem1PossibleConvergenceFrom9To12_proved :
    Theorem1PossibleConvergenceFrom9To12 :=
  theorem1PossibleConvergenceFrom9To12_of_reachCPB
    (fun hn9 _hn12 hpsi hnpow _hpsiK ring C => by
      obtain ⟨w, _hlen, hcpb⟩ :=
        PPL.Convergence.ReachCPB.reachCPB_exists_theorem1Kappa
          (by omega) hpsi hnpow ring C
      exact ⟨w, hcpb⟩)

-- [copied from Leader/PPL/Theorem1PPLFrom9To12.lean:32-44]
/-- The remaining C.4 residual: possible convergence on `n ≤ 8`. -/
def Theorem1PossibleConvergenceUpto8 : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    n ≤ 8 →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi < n →
    ∀ (ring : DirectedRing n)
      (C : Config n psi (theorem1Kappa psi)),
      ∃ word : DetSchedule n,
        theorem1ReachesSPL ring C word = true

-- [copied from Leader/PPL/Theorem1PPLFrom9To12.lean:45-54]
/-- The `n ≤ 12` pointwise statement from its `n ≤ 8` part. -/
theorem theorem1PossibleConvergenceUpto12_of_upto8
    (h8 : Theorem1PossibleConvergenceUpto8) :
    Theorem1PossibleConvergenceUpto12 := by
  intro n psi hn3 hn12 hpsi hnpow hpsiK ring C
  by_cases hn8 : n ≤ 8
  · exact h8 hn3 hn8 hpsi hnpow hpsiK ring C
  · exact theorem1PossibleConvergenceFrom9To12_proved
      (by omega) hn12 hpsi hnpow hpsiK ring C

/-! ## n ≤ 8 (copied from `Theorem1PossibleUpto8.lean`) -/

-- [copied from Leader/PPL/MainTheorem/PossibleUpToEight.lean:421-532]
/--
**Tail from `C_mid`, given a short L17 word.**  Let `Cmid` be `CPB` with every
clock at most `kappa / 2` and every mode Construct, with `3 ≤ n ≤ 8` in the
Theorem-1 window.  If the literal view of `Cmid` has a one-leader word `w17`
of length at most `5 n²`, then some literal P_PL word from `Cmid` ends in
`SPL`.

The word is `w17 ++ hit`, where `hit` is the prefix of
`l18Word ring root psi` at which the scoped L18 forcing bridge reaches
`SPLAt root` in P_PL'.  The Construct-slack lemma makes the P_PL and P_PL'
runs of `w17 ++ hit` coincide.
-/
theorem upto8_tailSPL_of_mid
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hn8 : n ≤ 8)
    (hpsi : 2 ≤ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (Cmid : Config n psi (theorem1Kappa psi))
    (hCPB : PPL.CPB ring Cmid)
    (hmid : PPL.Modes.Lemma5.midPhysicalB Cmid = true)
    (w17 : DetSchedule n)
    (hlen17 : w17.length ≤ 5 * n * n)
    (hL1 :
      PPL.LiteralL1
        (PPL.Probability.runPopulationSchedule
          PPL.Elim.protocolE ring (PPL.Elim.viewConfig Cmid) w17)) :
    ∃ word : DetSchedule n,
      SPL ring (PPL.Probability.runPPL ring Cmid word) := by
  have hlt : psi < n := theorem1_psi_lt_n hn3 hpsiK
  have hl18 := theorem1_l18Length_le (n := n) hpsi
  have hnn : n * n ≤ 8 * 8 := Nat.mul_le_mul hn8 hn8
  have hnp : n * psi ≤ 8 * 8 := Nat.mul_le_mul hn8 (by omega)
  have h5 : 5 * n * n = 5 * (n * n) := Nat.mul_assoc 5 n n
  have h8 : 8 * n * psi = 8 * (n * psi) := Nat.mul_assoc 8 n psi
  have hkappa : theorem1Kappa psi = 55206272 * psi := by
    unfold theorem1Kappa theorem1C1 theorem1C17
    omega
  have hslack :
      theorem1Kappa psi / 2 + w17.length +
          PPL.Convergence.L18.l18Length n psi <
        theorem1Kappa psi := by
    rw [hkappa]
    omega
  obtain ⟨word, root, hloc⟩ :=
    PPL.Theorem1General.theorem1TailOfMid_at hn3 hpsi ring
      (fun root C => decide (SPLAt ring root C))
      (fun root C hC hU => by
        have h :=
          l18ForcingWordReachesSPLScoped_proved
            lemma4_deterministic_core_proved
            hn3 hpsi hlt ring root C
            (PPL.Convergence.L18.l18Word ring root psi)
            hC hU (List.Sublist.refl _)
        rw [PPL.Theorem1General.l18HitsSPL_eq] at h
        exact h)
      Cmid hCPB hmid w17 hslack hL1
  exact ⟨word, root, by simpa using hloc⟩

-- [copied from Leader/PPL/MainTheorem/PossibleUpToEight.lean:535-588]
/--
**C.4 for `n ≤ 8`, conditional on a short deterministic L17 word.**

Hypothesis `hL17`: for `3 ≤ n`, every literal Algorithm-5 configuration in
`PPL.Elim.PB` has a scheduler word of length at most `5 n²` whose literal
endpoint has exactly one leader.

Proof: reach `CPB` (`reachCPB_exists_theorem1Kappa`), run the deterministic maximum-reset
wave to `C_mid` (`theorem1L5i_seqR_midPhysicalB`), then apply
`upto8_tailSPL_of_mid`, and turn the SPL endpoint into a prefix hit.
-/
theorem theorem1PossibleConvergenceUpto8_of_shortL17
    (hL17 :
      ∀ {n : Nat}, 3 ≤ n →
        ∀ (ring : DirectedRing n) (D : PPL.LiteralElimConfig n),
          PPL.Elim.PB ring D →
          ∃ w : DetSchedule n,
            w.length ≤ 5 * n * n ∧
              PPL.LiteralL1
                (PPL.Probability.runPopulationSchedule
                  PPL.Elim.protocolE ring D w)) :
    Theorem1PossibleConvergenceUpto8 := by
  intro n psi hn3 hn8 hpsi hnpow hpsiK ring C0
  obtain ⟨w0, _hw0len, hCPB1⟩ :=
    PPL.Convergence.ReachCPB.reachCPB_exists_theorem1Kappa hn3 hpsi hnpow ring C0
  let C1 : Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C0 w0
  obtain ⟨root0, _hroot0, hmid⟩ :=
    PPL.Modes.Lemma5.theorem1L5i_seqR_midPhysicalB
      hn3 hpsi ring C1 hCPB1
  let Cmid : Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C1 (PPL.seqR ring root0 n)
  have hCPBmid : PPL.CPB ring Cmid :=
    PPL.Convergence.ReachCPB.cpb_run_closed hn3 hpsi ring C1
      (PPL.seqR ring root0 n) hCPB1
  have hPBmid : PPL.Elim.PB ring (PPL.Elim.viewConfig Cmid) :=
    (PPL.Convergence.LiteralEliminationBridges.cpbViewBridge ring Cmid).mp
      hCPBmid
  obtain ⟨w17, hlen17, hL1⟩ :=
    hL17 hn3 ring (PPL.Elim.viewConfig Cmid) hPBmid
  obtain ⟨v, hv⟩ :=
    upto8_tailSPL_of_mid hn3 hn8 hpsi hpsiK ring Cmid hCPBmid hmid
      w17 hlen17 hL1
  have hvHit : theorem1ReachesSPL ring Cmid v = true := by
    apply theorem1ReachesSPL_of_runLocalEndpoint
    rw [PPL.Theorem1General.theorem1RunLocalSchedule_eq_runPPL]
    exact hv
  have hmidHit :
      theorem1ReachesSPL ring C1 (PPL.seqR ring root0 n ++ v) = true :=
    theorem1ReachesSPL_append_of_run ring C1 _ v hvHit
  exact
    ⟨w0 ++ (PPL.seqR ring root0 n ++ v),
      theorem1ReachesSPL_append_of_run ring C0 w0 _ hmidHit⟩

/-! ## Producer (copied from `Theorem1PPLFromL18Inputs.lean`, `Theorem1PPLUpto12FromPossible.lean`) -/

-- [copied from Leader/PPL/Theorem1PPLFromL18Inputs.lean:63-81]
/-- The C.4 residual for the twelve admissible pairs with `n ≤ 12`, stated
as `Theorem1TinyProducerUpto12`.  Open. -/
def Theorem1TinyProducerUpto12 : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    n ≤ 12 →
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

-- [copied from Leader/PPL/Theorem1PPLFromL18Inputs.lean:82-92]
/-- The tiny producer (`n ≤ 64`) is the union of the `n ≤ 12` and the
`13 ≤ n ≤ 64` producers. -/
theorem theorem1TinyProducer_of_split
    (hUpto12 : Theorem1TinyProducerUpto12)
    (hFrom13 : Theorem1TinyProducerFrom13) :
    Theorem1TinyProducer := by
  intro n psi hn3 hn64 hpsi hnpow hpsiK
  by_cases hn12 : n ≤ 12
  · exact hUpto12 hn3 hn12 hpsi hnpow hpsiK
  · exact hFrom13 hn3 (by omega) hn64 hpsi hnpow hpsiK

-- [copied from Leader/PPL/MainTheorem/PossibleUniformBound.lean:83-89]
/-- Any two directed rings of the same size are equal (single proof field). -/
private theorem q20310_directedRing_eq
    {n : Nat} (R R' : DirectedRing n) : R = R' := by
  cases R
  cases R'
  rfl

-- [copied from Leader/PPL/MainTheorem/PossibleUniformBound.lean:128-147]
/-- C.4 for `n ≤ 12` from the pointwise possible-convergence statement. -/
theorem theorem1TinyProducerUpto12_of_possibleConvergence
    (hpossible : Theorem1PossibleConvergenceUpto12) :
    Theorem1TinyProducerUpto12 := by
  intro n psi hn3 hn12 hpsi hnpow hpsiK
  let ring0 : DirectedRing n := ⟨by omega⟩
  obtain ⟨L, hL⟩ :=
    theorem1PossibleUniformBound_of_exhaustive ring0
      (theorem1ConfigStates n psi (theorem1Kappa psi))
      (hpossible hn3 hn12 hpsi hnpow hpsiK ring0)
  refine ⟨L, ?_⟩
  intro ring
  have hring : ring = ring0 := q20310_directedRing_eq ring ring0
  subst hring
  intro C _hTrue _hnot
  obtain ⟨word, hlen, hhit⟩ := hL C
  obtain ⟨pre, hprelen, hsafe⟩ :=
    theorem1ReachesSPL_endpoint_prefix ring0 C word hhit
  exact ⟨pre, Nat.le_trans hprelen hlen, hsafe⟩

/-- Possible convergence for `n ≤ 8` on `psi < n`, unconditionally (the short
L17 word is `literalPB_oneLeader_exists_short`). -/
theorem theorem1PossibleConvergenceUpto8_proved :
    Theorem1PossibleConvergenceUpto8 :=
  theorem1PossibleConvergenceUpto8_of_shortL17
    (fun _hn3 ring D hPB =>
      PPL.Convergence.L17Macro.literalPB_oneLeader_exists_short ring D hPB)

/-- The tiny producer (`n ≤ 64`) on `psi < n`, unconditionally. -/
theorem theorem1TinyProducer_proved : Theorem1TinyProducer :=
  theorem1TinyProducer_of_split
    (theorem1TinyProducerUpto12_of_possibleConvergence
      (theorem1PossibleConvergenceUpto12_of_upto8
        theorem1PossibleConvergenceUpto8_proved))
    theorem1TinyProducerFrom13_proved

end PPL.PsiBelowN

#print axioms PPL.PsiBelowN.theorem1PossibleConvergenceFrom9To12_proved
#print axioms PPL.PsiBelowN.theorem1PossibleConvergenceUpto8_proved
#print axioms PPL.PsiBelowN.theorem1TinyProducer_proved

import Leader.PPL.PsiAtLeastN.SafeSplice
import Leader.PPL.MainTheorem.PossibleUpToEight
import Leader.PPL.Elim.OneLeaderShortWord
import Leader.PPL.MainTheorem.GeneralSmallN

/-!
# Possible convergence to the safe target for `3 ≤ n ≤ 64`, `n ≤ psi`

A deterministic schedule from every configuration to `Theorem1SafeTarget`
when `3 ≤ n ≤ 64` and `n ≤ psi`, following the `n ≤ 8` route of
`Theorem1PossibleUpto8.lean` (copied in `PsiBelowN/Upto12.lean`):

1. reach `C_PB` (`reachCPB_exists_theorem1Kappa`);
2. the deterministic maximum-reset wave `seqR ring root0 n` to a `C_mid`
   configuration (every clock at most `kappa / 2`, every mode Construct,
   `theorem1L5i_seqR_midPhysicalB`);
3. a literal one-leader word `w17` of length at most `5 n²`
   (`literalPB_oneLeader_exists_short`), run in `P_PL'`;
4. the prefix `hit` of `l18Word` at which the `P_PL'` run first becomes
   rooted `S_PL` or rooted `C_DL` (`l18ForcingWordReachesSafe`, every `psi`).

The Construct-slack lemma makes the `P_PL` and `P_PL'` runs of `w17 ++ hit`
coincide.  With one segment `l18Length n psi = 2 n + 2 psi`, and
`n ≤ 64`, `n ≤ psi` give `5 n² + 2 n + 2 psi < kappa / 2` with
`kappa = 55206272 psi`.  The original `n ≤ 8` proof used `psi < n` for the
Lemma-18 scope and `n psi ≤ 64` for the slack; here neither is needed.

P_PL Theorem 1 cleanup, phase 2, step 6e: the tail
from `C_mid` is the rooted-safe case of
`PPL.Theorem1General.theorem1TailOfMid_at` (statement unchanged); the
private copies `psiGePB_run`, `psiGeSumIte_eq_countP` and
`psiGeUnique_of_leaderCount` are gone.
-/

namespace PPL.PsiAtLeastN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Probability
open PPLLResearchFormulation

/-! ## Safe-target prefix hits along `P_PL` runs -/

/-- A safe endpoint of the `P_PL` run is a prefix hit. -/
theorem theorem1ReachesSafeTarget_of_runPPL_endpoint
    {n psi kappa : Nat} (ring : DirectedRing n) :
    ∀ (C : Config n psi kappa) (word : DetSchedule n),
      Theorem1SafeTarget ring (PPL.Probability.runPPL ring C word) →
        theorem1ReachesSafeTarget ring C word = true := by
  intro C word
  induction word generalizing C with
  | nil =>
      intro h
      simpa [theorem1ReachesSafeTarget, PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule] using h
  | cons e rest ih =>
      intro h
      have htail :=
        ih (PopulationProtocol.step (PPL.protocol psi kappa) ring C e)
          (by
            simpa [PPL.Probability.runPPL,
              PPL.Probability.runPopulationSchedule] using h)
      simp [theorem1ReachesSafeTarget, htail]

/-- Prefix hits compose with a leading `P_PL` run. -/
theorem theorem1ReachesSafeTarget_append_of_run
    {n psi kappa : Nat} (ring : DirectedRing n) :
    ∀ (C : Config n psi kappa) (a b : DetSchedule n),
      theorem1ReachesSafeTarget ring (PPL.Probability.runPPL ring C a) b = true →
        theorem1ReachesSafeTarget ring C (a ++ b) = true := by
  intro C a b
  induction a generalizing C with
  | nil =>
      intro hb
      simpa [PPL.Probability.runPPL,
        PPL.Probability.runPopulationSchedule] using hb
  | cons e rest ih =>
      intro hb
      have htail :=
        ih (PopulationProtocol.step (PPL.protocol psi kappa) ring C e)
          (by
            simpa [PPL.Probability.runPPL,
              PPL.Probability.runPopulationSchedule] using hb)
      simp [theorem1ReachesSafeTarget, htail]

/-! ## Arithmetic -/

/-- `psi < 2 ^ psi`. -/
theorem lt_two_pow_self' : ∀ m : Nat, m < 2 ^ m
  | 0 => by decide
  | m + 1 => by
      have := lt_two_pow_self' m
      rw [Nat.pow_succ]
      omega

/-- With one segment the Lemma-18 word has length `2 n + 2 psi`. -/
theorem l18Length_of_le {n psi : Nat} (hn : 1 ≤ n) (hge : n ≤ psi) :
    PPL.Convergence.L18.l18Length n psi = 2 * n + 2 * psi := by
  unfold PPL.Convergence.L18.l18Length PPL.Convergence.L18.l18BlockCount
  rw [segmentCount_eq_one_of_le hn hge]
  simp

/-! ## The deterministic tail from `C_mid` -/

/-- **Tail from `C_mid`, `3 ≤ n ≤ 64`, `n ≤ psi`.**  From a `C_PB`
configuration with every clock at most `kappa / 2` and every mode Construct,
given a literal one-leader word `w17` of length at most `5 n²`, some `P_PL`
word from `Cmid` ends in `Theorem1SafeTarget`.  The word is `w17 ++ hit`,
where `hit` is the prefix of `l18Word ring root psi` at which the `P_PL'` run
first becomes rooted `S_PL` or rooted `C_DL`; Construct slack makes the
`P_PL` and `P_PL'` runs of `w17 ++ hit` coincide. -/
theorem psiGe_tailSafe_of_mid
    {n psi : Nat}
    (hn3 : 3 ≤ n) (hn64 : n ≤ 64) (hpsi : 2 ≤ psi) (hge : n ≤ psi)
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
      Theorem1SafeTarget ring (PPL.Probability.runPPL ring Cmid word) := by
  have hl18 := l18Length_of_le (by omega : 1 ≤ n) hge
  have hnn : n * n ≤ 64 * psi := Nat.mul_le_mul hn64 hge
  have h5 : 5 * n * n = 5 * (n * n) := Nat.mul_assoc 5 n n
  have hkappa : theorem1Kappa psi = 55206272 * psi := by
    unfold theorem1Kappa theorem1C1 theorem1C17
    omega
  have hslack :
      theorem1Kappa psi / 2 + w17.length +
          PPL.Convergence.L18.l18Length n psi <
        theorem1Kappa psi := by
    rw [hl18, hkappa]
    omega
  obtain ⟨word, root, hloc⟩ :=
    PPL.Theorem1General.theorem1TailOfMid_at hn3 hpsi ring
      (fun root C => decide (L18SafeAt ring root C))
      (fun root C hC hU => by
        have h :=
          l18ForcingWordReachesSafe hn3 hpsi ring root C hC hU
            (PPL.Convergence.L18.l18Word ring root psi) (List.Sublist.refl _)
        rw [l18HitsSafe_eq] at h
        exact h)
      Cmid hCPB hmid w17 hslack hL1
  exact
    ⟨word,
      theorem1SafeTarget_of_l18SafeAt (by omega) hge (by simpa using hloc)⟩

/-- **Possible convergence to the safe target, `3 ≤ n ≤ 64`, `n ≤ psi`.**
From every configuration some scheduler word visits `Theorem1SafeTarget`:
reach `C_PB`, run the maximum-reset wave to `C_mid`, then apply
`psiGe_tailSafe_of_mid` with the short literal L17 word. -/
theorem theorem1PossibleSafe_smallN
    {n psi : Nat}
    (hn3 : 3 ≤ n) (hn64 : n ≤ 64) (hpsi : 2 ≤ psi) (hge : n ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    ∃ word : DetSchedule n,
      theorem1ReachesSafeTarget ring C0 word = true := by
  have hnpow : n ≤ 2 ^ psi :=
    Nat.le_trans hge (Nat.le_of_lt (lt_two_pow_self' psi))
  obtain ⟨w0, _hw0len, hCPB1⟩ :=
    PPL.Convergence.ReachCPB.reachCPB_exists_theorem1Kappa hn3 hpsi hnpow ring C0
  let C1 : Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C0 w0
  obtain ⟨root0, _hroot0, hmid⟩ :=
    PPL.Modes.Lemma5.theorem1L5i_seqR_midPhysicalB hn3 hpsi ring C1 hCPB1
  let Cmid : Config n psi (theorem1Kappa psi) :=
    PPL.Probability.runPPL ring C1 (PPL.seqR ring root0 n)
  have hCPBmid : PPL.CPB ring Cmid :=
    PPL.Convergence.ReachCPB.cpb_run_closed hn3 hpsi ring C1
      (PPL.seqR ring root0 n) hCPB1
  have hPBmid : PPL.Elim.PB ring (PPL.Elim.viewConfig Cmid) :=
    (PPL.Convergence.LiteralEliminationBridges.cpbViewBridge ring Cmid).mp
      hCPBmid
  obtain ⟨w17, hlen17, hL1⟩ :=
    PPL.Convergence.L17Macro.literalPB_oneLeader_exists_short ring
      (PPL.Elim.viewConfig Cmid) hPBmid
  obtain ⟨v, hv⟩ :=
    psiGe_tailSafe_of_mid hn3 hn64 hpsi hge ring Cmid hCPBmid hmid
      w17 hlen17 hL1
  have hvHit : theorem1ReachesSafeTarget ring Cmid v = true :=
    theorem1ReachesSafeTarget_of_runPPL_endpoint ring Cmid v hv
  have hmidHit :
      theorem1ReachesSafeTarget ring C1 (PPL.seqR ring root0 n ++ v) = true :=
    theorem1ReachesSafeTarget_append_of_run ring C1 _ v hvHit
  exact
    ⟨w0 ++ (PPL.seqR ring root0 n ++ v),
      theorem1ReachesSafeTarget_append_of_run ring C0 w0 _ hmidHit⟩

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.psiGe_tailSafe_of_mid
#print axioms PPL.PsiAtLeastN.theorem1PossibleSafe_smallN

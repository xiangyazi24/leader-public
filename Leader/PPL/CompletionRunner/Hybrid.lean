import Leader.PPL.CompletionRunner.ForcedConstructTransferSweep
import Leader.PPL.TokenCompletion.SweepFreshPersist

/-!
# Step-parametric Lemma 4: the hybrid runner

The generic Lemma-4 layer quantifies over every start configuration `C0`.
The prime step props are only available from starts satisfying
`L18RiskySweepPrefix2 ring root psi C0` (with `3 ≤ n`, `psi < n`), and that
condition (`PrimeGood`) is preserved by every prime step.

Rather than re-thread a start predicate through the whole generic layer, we
use a *hybrid* runner: at a `PrimeGood` physical state it fires the prime
step (`pprimeStep` / `ghostStepPrime`), elsewhere the ordinary step
(`PopulationProtocol.step (protocol …)` / `ghostStep`).

* From a `PrimeGood` start, the hybrid run *is* the prime run
  (`hybrid_run_eq_prime`) and the hybrid `C_d` trace is the prime one
  (`hybrid_cdTrace_iff_prime`), because `PrimeGood` is preserved.
* Along *every* hybrid run, soundness, ID uniqueness, fresh kinematics and
  terminal history hold (`HybridInv`, `hybridInv_run`): ordinary steps
  preserve them for any ghost state, prime steps preserve them under the
  prelude agreement that `PrimeGood` supplies.
* Hence each generic one-step Prop holds for the hybrid runner, with no start
  restriction: in the prime case through the bridge (`primeX_ofFacts`), in the
  ordinary case directly (`ordX_ofFacts`).

This file proves `RunSound`, `IdsUniqueStep`, `FreshLineagePersistenceStep`,
`CoverageStep`, `OldOwnerProgressStep` and `SweepMissingRows` for the hybrid
runner.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Convergence.L18

/-! ## 1. The runner -/

/-- The start/region condition of the prime Lemma-4 route. -/
def PrimeGood {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  3 ≤ n ∧ psi < n ∧ ∃ root : Fin n, L18RiskySweepPrefix2 ring root psi C

/-- `PrimeGood` is preserved by every prime step. -/
theorem primeGood_step {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa) (e : Fin n)
    (h : PrimeGood ring C) : PrimeGood ring (pprimeStep ring C e) := by
  obtain ⟨hn3, hlt, root, hpref⟩ := h
  exact ⟨hn3, hlt, root,
    l18GappedRiskyInsertedStepRow_proved hn3 hpsi hlt ring root psi C e
      (Nat.le_refl psi) hpref⟩

/-- `PrimeGood` gives the prelude agreement at every selected pair. -/
theorem preludeAgree_of_good {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa) (e : Fin n)
    (h : PrimeGood ring C) :
    PreludeAgree hpsi (C e) (C (ring.rightNeighbor e)) := by
  obtain ⟨_, _, root, hpref⟩ := h
  exact preludeAgree_of_CDLAt hpsi ring root C e hpref.1

open Classical in
/-- Hybrid physical step. -/
noncomputable def hybridPhys {n psi kappa : Nat} (_hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa) (e : Fin n) :
    Config n psi kappa :=
  if PrimeGood ring C then pprimeStep ring C e
  else PopulationProtocol.step (protocol psi kappa) ring C e

open Classical in
/-- Hybrid ghost step. -/
noncomputable def hybridGStep {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n) :
    GhostConfig n psi kappa :=
  if PrimeGood ring G.phys then ghostStepPrime hpsi ring t G e
  else ghostStep hpsi ring t G e

theorem hybridPhys_good {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa) (e : Fin n)
    (h : PrimeGood ring C) : hybridPhys hpsi ring C e = pprimeStep ring C e := by
  unfold hybridPhys
  simp [h]

theorem hybridPhys_bad {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C : Config n psi kappa) (e : Fin n)
    (h : ¬ PrimeGood ring C) :
    hybridPhys hpsi ring C e = PopulationProtocol.step (protocol psi kappa) ring C e := by
  unfold hybridPhys
  simp [h]

theorem hybridGStep_good {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (h : PrimeGood ring G.phys) :
    hybridGStep hpsi ring t G e = ghostStepPrime hpsi ring t G e := by
  unfold hybridGStep
  simp [h]

theorem hybridGStep_bad {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (h : ¬ PrimeGood ring G.phys) :
    hybridGStep hpsi ring t G e = ghostStep hpsi ring t G e := by
  unfold hybridGStep
  simp [h]

/-- The hybrid runner. -/
noncomputable def hybridRunner : Lemma4Runner :=
  Lemma4Runner.ofStep
    (fun hpsi ring C e => hybridPhys hpsi ring C e)
    (fun hpsi ring t G e => hybridGStep hpsi ring t G e)
    (by
      intro n psi kappa hpsi ring t G e
      by_cases h : PrimeGood ring G.phys
      · rw [hybridGStep_good hpsi ring t G e h, hybridPhys_good hpsi ring G.phys e h]
        rfl
      · rw [hybridGStep_bad hpsi ring t G e h, hybridPhys_bad hpsi ring G.phys e h]
        rfl)
    (by
      intro n psi kappa hpsi ring t G e
      by_cases h : PrimeGood ring G.phys
      · rw [hybridGStep_good hpsi ring t G e h]
        exact ⟨_, List.append_assoc _ _ _⟩
      · rw [hybridGStep_bad hpsi ring t G e h]
        exact ⟨_, List.append_assoc _ _ _⟩)

theorem hybridRunner_gstep {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n) :
    hybridRunner.gstep hpsi ring t G e = hybridGStep hpsi ring t G e := rfl

/-! ## 2. From a good start the hybrid runner is the prime runner -/

/-- From a `PrimeGood` state, the hybrid run is the prime run. -/
theorem hybrid_run_eq_prime {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) :
    ∀ (t : Nat) (G : GhostConfig n psi kappa) (s : DetSchedule n),
      PrimeGood ring G.phys →
      hybridRunner.run hpsi ring t G s = ghostRunPrime hpsi ring t G s := by
  intro t G s hG
  induction s generalizing t G with
  | nil => rfl
  | cons e es ih =>
      rw [hybridRunner.run_cons, hybridRunner_gstep, hybridGStep_good hpsi ring t G e hG]
      exact ih (t + 1) (ghostStepPrime hpsi ring t G e)
        (primeGood_step hpsi ring G.phys e hG)

/-- From a `PrimeGood` configuration, the hybrid `C_d` trace is the prime one. -/
theorem hybrid_cdTrace_iff_prime {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) :
    ∀ (C : Config n psi kappa) (s : DetSchedule n),
      PrimeGood ring C →
      (hybridRunner.cdTrace hpsi ring k kind C s ↔
        primeRunner.cdTrace hpsi ring k kind C s) := by
  intro C s hC
  induction s generalizing C with
  | nil =>
      rw [hybridRunner.cdTrace_nil, primeRunner.cdTrace_nil]
  | cons e es ih =>
      rw [hybridRunner.cdTrace_cons, primeRunner.cdTrace_cons]
      have hstep : hybridRunner.physStep hpsi ring C e = pprimeStep ring C e :=
        hybridPhys_good hpsi ring C e hC
      have hstep' : primeRunner.physStep hpsi ring C e = pprimeStep ring C e := rfl
      rw [hstep, hstep', ih (pprimeStep ring C e) (primeGood_step hpsi ring C e hC)]

/-! ## 3. The invariant along every hybrid run -/

/-- Soundness, ID uniqueness (when `2 ≤ n`), fresh kinematics and terminal
history. -/
def HybridInv {n psi kappa : Nat} (ring : DirectedRing n) (t : Nat)
    (G : GhostConfig n psi kappa) : Prop :=
  GhostSound G ∧
    (2 ≤ n → GhostIdsUniqueAt t G) ∧
    (∀ k : Fin n, Lemma4FreshKinematics ring k G) ∧
    (∀ k : Fin n, PrimeTerminalHistory k G)

theorem hybridInv_step {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hI : HybridInv ring t G) :
    HybridInv ring (t + 1) (hybridGStep hpsi ring t G e) := by
  obtain ⟨hsound, huniq, hkin, hhist⟩ := hI
  by_cases hg : PrimeGood ring G.phys
  · rw [hybridGStep_good hpsi ring t G e hg]
    have hpre := preludeAgree_of_good hpsi ring G.phys e hg
    refine ⟨ghostSound_ghostStepPrime_of_preludeAgree hpsi ring t G e hsound hpre,
      fun hn2 => ghostIdsUnique_step_prime hpsi hn2 ring t G e (huniq hn2), ?_, ?_⟩
    · intro k
      rw [ghostStepPrime_eq_withPhys hpsi ring t G e hpre]
      exact pri_freshKinematics_step hpsi ring k t G e (hkin k)
    · intro k
      rw [ghostStepPrime_eq_withPhys hpsi ring t G e hpre]
      exact pri_terminalHistory_step hpsi ring k t G e (hhist k)
  · rw [hybridGStep_bad hpsi ring t G e hg]
    exact ⟨pb_ghostStep_sound hpsi ring t G e hsound,
      fun hn2 => ghostIdsUnique_step hpsi hn2 ring t G e (huniq hn2),
      fun k => pri_freshKinematics_step hpsi ring k t G e (hkin k),
      fun k => pri_terminalHistory_step hpsi ring k t G e (hhist k)⟩

theorem hybridInv_initial {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C0 : Config n psi kappa) :
    HybridInv ring 0 (initialGhost C0) := by
  refine ⟨lemma4CoverageGhostRunSound_proved hpsi ring C0 [],
    fun _ => ghostIdsUnique_initial C0, ?_, ?_⟩
  · intro k kind i z howner hfresh
    rcases hfresh with ⟨t, hborn, _hsite⟩
    have hU := (ghostIdsUnique_initial C0).2 kind i z kind t howner hborn
    omega
  · intro k kind i z howner hfresh
    rcases hfresh with ⟨t, hborn, _hsite⟩
    have hU := (ghostIdsUnique_initial C0).2 kind i z kind t howner hborn
    omega

theorem hybridInv_from {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) :
    ∀ (t : Nat) (G : GhostConfig n psi kappa) (s : DetSchedule n),
      HybridInv ring t G →
      HybridInv ring (t + s.length) (hybridRunner.run hpsi ring t G s) := by
  intro t G s hI
  induction s generalizing t G with
  | nil => exact hI
  | cons e es ih =>
      rw [hybridRunner.run_cons]
      have h := ih (t + 1) (hybridRunner.gstep hpsi ring t G e)
        (hybridInv_step hpsi ring t G e hI)
      simp only [List.length_cons]
      rw [show t + (es.length + 1) = t + 1 + es.length by omega]
      exact h

/-- The invariant along every hybrid run from an initial ghost. -/
theorem hybridInv_run {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C0 : Config n psi kappa) (pre : DetSchedule n) :
    HybridInv ring pre.length (hybridRunner.run hpsi ring 0 (initialGhost C0) pre) := by
  have h := hybridInv_from hpsi ring 0 (initialGhost C0) pre (hybridInv_initial hpsi ring C0)
  simpa using h

theorem hybridInv_of_hrun {n psi kappa : Nat} {hpsi : 2 ≤ psi}
    {ring : DirectedRing n} {C0 : Config n psi kappa} {pre : DetSchedule n}
    {G : GhostConfig n psi kappa}
    (hrun : G = hybridRunner.run hpsi ring 0 (initialGhost C0) pre) :
    HybridInv ring pre.length G := by
  rw [hrun]
  exact hybridInv_run hpsi ring C0 pre

/-- `Cd` forces `2 ≤ n` (the window has `2 psi ≥ 4` distinct `dist` values). -/
theorem two_le_n_of_cd {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (C : Config n psi kappa)
    (hCd : Cd ring k kind C) : 2 ≤ n :=
  (privc% Leader.PPL.TokenCompletion.SweepRows PPL.lemma4SweepCd_two_le_n)
    hpsi ring k kind C hCd

/-! ## 4. The run and ID facts -/

theorem hybrid_runSound : RunSound hybridRunner := by
  intro n psi kappa hpsi ring C0 pre
  exact (hybridInv_run hpsi ring C0 pre).1

theorem hybrid_idsUniqueStep : IdsUniqueStep hybridRunner := by
  intro n psi kappa hpsi hn2 ring step G e hU
  rw [hybridRunner_gstep]
  by_cases hg : PrimeGood ring G.phys
  · rw [hybridGStep_good hpsi ring step G e hg]
    exact ghostIdsUnique_step_prime hpsi hn2 ring step G e hU
  · rw [hybridGStep_bad hpsi ring step G e hg]
    exact ghostIdsUnique_step hpsi hn2 ring step G e hU

theorem hybrid_freshLineagePersistenceStep :
    FreshLineagePersistenceStep hybridRunner := by
  intro n psi kappa hpsi ring k kind step G e i j z z' hU hiw hi hf hjw hj hid
  rw [hybridRunner_gstep] at hj
  by_cases hg : PrimeGood ring G.phys
  · rw [hybridGStep_good hpsi ring step G e hg] at hj
    exact prime_freshLineagePersistenceStep hpsi ring k kind step G e i j z z'
      hU hiw hi hf hjw hj hid
  · rw [hybridGStep_bad hpsi ring step G e hg] at hj
    exact lemma4SweepFreshLineagePersistenceStep_proved hpsi ring k kind step G e i j z z'
      hU hiw hi hf hjw hj hid

/-! ## 5. The one-step Props -/

theorem hybrid_coverageStep : CoverageStep hybridRunner := by
  intro n psi kappa hpsi ring k kind
  refine ⟨(lemma4StepProps_proved.1 hpsi ring k kind).1, ?_⟩
  intro C0 pre G e hrun hCd hCd' hcovered
  have hI := hybridInv_of_hrun hrun
  dsimp only
  rw [hybridRunner_gstep] at hCd' ⊢
  by_cases hg : PrimeGood ring G.phys
  · rw [hybridGStep_good hpsi ring pre.length G e hg] at hCd' ⊢
    exact primeCoverage_ofSound hpsi ring k kind pre.length G e hI.1
      (preludeAgree_of_good hpsi ring G.phys e hg) hCd hCd' hcovered
  · rw [hybridGStep_bad hpsi ring pre.length G e hg] at hCd' ⊢
    exact ordCoverage_ofSound hpsi ring k kind pre.length G e hI.1 hCd hCd' hcovered

theorem hybrid_oldOwnerProgressStep : OldOwnerProgressStep hybridRunner := by
  intro n psi kappa hpsi ring k kind C0 pre G e hrun hCd hCd' hcovered i z hwin howner hnf
  have hI := hybridInv_of_hrun hrun
  have hn2 := two_le_n_of_cd hpsi ring k kind G.phys hCd
  dsimp only
  rw [hybridRunner_gstep] at hCd' ⊢
  by_cases hg : PrimeGood ring G.phys
  · rw [hybridGStep_good hpsi ring pre.length G e hg] at hCd' ⊢
    exact primeOldOwner_ofSound hpsi ring k kind pre.length G e hI.1 (hI.2.1 hn2)
      (preludeAgree_of_good hpsi ring G.phys e hg) hCd hCd' hcovered i z hwin howner hnf
  · rw [hybridGStep_bad hpsi ring pre.length G e hg] at hCd' ⊢
    have h := ordOldOwner_ofSound hpsi ring k kind pre.length G e hI.1 (hI.2.1 hn2)
      hCd hCd' hcovered i z hwin howner hnf
    exact h

theorem hybrid_sweepMissingRows : SweepMissingRows hybridRunner := by
  intro n psi kappa hpsi ring k kind C0 pre G e hrun hCd hCd' hcovered
  have hI := hybridInv_of_hrun hrun
  have hn2 := two_le_n_of_cd hpsi ring k kind G.phys hCd
  dsimp only
  rw [hybridRunner_gstep] at hCd' ⊢
  by_cases hg : PrimeGood ring G.phys
  · rw [hybridGStep_good hpsi ring pre.length G e hg] at hCd' ⊢
    exact primeSweep_ofFacts hpsi ring k kind pre.length G e hI.1 (hI.2.1 hn2)
      (hI.2.2.1 k) (preludeAgree_of_good hpsi ring G.phys e hg) hCd hCd' hcovered
  · rw [hybridGStep_bad hpsi ring pre.length G e hg] at hCd' ⊢
    exact ordSweep_ofFacts hpsi ring k kind pre.length G e hI.1 (hI.2.1 hn2)
      (hI.2.2.1 k) hCd hCd' hcovered

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.hybrid_run_eq_prime
#print axioms PPL.Lemma4Generic.hybrid_cdTrace_iff_prime
#print axioms PPL.Lemma4Generic.hybrid_runSound
#print axioms PPL.Lemma4Generic.hybrid_idsUniqueStep
#print axioms PPL.Lemma4Generic.hybrid_freshLineagePersistenceStep
#print axioms PPL.Lemma4Generic.hybrid_coverageStep
#print axioms PPL.Lemma4Generic.hybrid_oldOwnerProgressStep
#print axioms PPL.Lemma4Generic.hybrid_sweepMissingRows

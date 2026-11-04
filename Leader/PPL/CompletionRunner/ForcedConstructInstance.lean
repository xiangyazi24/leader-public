import Leader.PPL.CompletionRunner.Core
import Leader.PPL.SPLEntry.Ghost
import Leader.PPL.TokenCompletion.CoverageLeaves

/-!
# Step-parametric Lemma 4: the P_PL-prime runner

`primeRunner` instantiates `Lemma4Runner` with the P_PL-prime physical step
`pprimeStep`, the prime ghost step `ghostStepPrime` and the prime ghost run
`ghostRunPrime` of `Convergence/L18PrimeGhost.lean`.  The `C_d` trace is the
canonical `iterCdTrace` along `pprimeStep`.

What is closed here:

* all runner laws (`primeRunner` itself), and `physRun = runPPrime`;
* `IdsUniqueStep primeRunner`, from `ghostIdsUnique_step_prime`;
* the reduction of `RunSound primeRunner` to one selected-pair clause
  `PrimeSelectedPairSound`: the initial ghost is sound (ordinary theorem, the
  initial ghost is shared), and off the selected pair both the prime ghost map
  (`ghostTokenAt_ghostStep_frame_prime`) and the physical state
  (`PopulationProtocol.step`) are unchanged.

`PrimeSelectedPairSound` itself is the prime analogue of the ~1,700-line
selected-row soundness argument of `TokenCorrectnessLemma4CoverageLeaves.lean`
and is left as a named hypothesis.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Convergence.L18

/-! ## 1. The runner -/

/-- The P_PL-prime runner: `pprimeStep`, `ghostStepPrime`, `ghostRunPrime`. -/
def primeRunner : Lemma4Runner where
  physStep := fun _hpsi ring C e => pprimeStep ring C e
  gstep := fun hpsi ring t G e => ghostStepPrime hpsi ring t G e
  run := fun hpsi ring t G s => ghostRunPrime hpsi ring t G s
  cdTrace := fun hpsi ring k kind C s =>
    iterCdTrace (fun _hpsi ring C e => pprimeStep ring C e)
      hpsi ring k kind C s
  run_nil := by
    intro n psi kappa hpsi ring t G
    rfl
  run_cons := by
    intro n psi kappa hpsi ring t G e es
    rfl
  gstep_phys := by
    intro n psi kappa hpsi ring t G e
    exact ghostStepPrime_phys hpsi ring t G e
  gstep_completed := by
    intro n psi kappa hpsi ring t G e
    exact ⟨_, List.append_assoc _ _ _⟩
  cdTrace_nil := by
    intro n psi kappa hpsi ring k kind C
    exact Iff.rfl
  cdTrace_cons := by
    intro n psi kappa hpsi ring k kind C e es
    exact Iff.rfl

/-- The physical run of the prime runner is `runPPrime`. -/
theorem primeRunner_physRun
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi kappa) (s : DetSchedule n) :
    primeRunner.physRun hpsi ring C s = runPPrime ring C s := by
  induction s generalizing C with
  | nil => rfl
  | cons e es ih =>
      exact ih (pprimeStep ring C e)

/-- The prime `C_d` trace unfolds exactly as the ordinary one, along `pprimeStep`. -/
theorem primeRunner_cdTrace_cons
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (k : Fin n) (kind : TokenKind) (C : Config n psi kappa)
    (e : Fin n) (es : DetSchedule n) :
    primeRunner.cdTrace hpsi ring k kind C (e :: es) ↔
      (Cd ring k kind C ∧
        primeRunner.cdTrace hpsi ring k kind (pprimeStep ring C e) es) :=
  Iff.rfl

/-! ## 2. Lineage-ID uniqueness -/

/-- One-step ID uniqueness of the prime runner (`ghostIdsUnique_step_prime`). -/
theorem prime_idsUniqueStep : IdsUniqueStep primeRunner := by
  intro n psi kappa hpsi hn2 ring step G e hU
  exact ghostIdsUnique_step_prime hpsi hn2 ring step G e hU

/-! ## 3. Run soundness, reduced to the selected pair -/

/-- Site-wise form of `GhostSound`, with the private local-validity predicate
replaced by the public `ValidToken`. -/
def SiteSound {n psi kappa : Nat} (G : GhostConfig n psi kappa)
    (kind : TokenKind) (i : Fin n) : Prop :=
  ∀ z : GhostToken n psi,
    ghostTokenAt kind G i = some z →
      tokenAt kind (G.phys i) = some z.value ∧
        ValidToken kind G.phys i

theorem siteSound_of_ghostSound {n psi kappa : Nat}
    {G : GhostConfig n psi kappa} (h : GhostSound G)
    (kind : TokenKind) (i : Fin n) :
    SiteSound G kind i := by
  intro z hz
  cases kind with
  | black =>
      have hs := h.1 i z hz
      refine ⟨hs.1, ?_⟩
      unfold ValidToken
      rw [hs.1]
      exact hs.2
  | white =>
      have hs := h.2 i z hz
      refine ⟨hs.1, ?_⟩
      unfold ValidToken
      rw [hs.1]
      exact hs.2

theorem ghostSound_of_siteSound {n psi kappa : Nat}
    {G : GhostConfig n psi kappa}
    (h : ∀ kind i, SiteSound G kind i) :
    GhostSound G := by
  constructor
  · intro i z hz
    have hs := h .black i z hz
    have hv := hs.2
    unfold ValidToken at hv
    rw [hs.1] at hv
    exact ⟨hs.1, hv⟩
  · intro i z hz
    have hs := h .white i z hz
    have hv := hs.2
    unfold ValidToken at hv
    rw [hs.1] at hv
    exact ⟨hs.1, hv⟩

/--
The selected-pair soundness clause of the prime ghost step: if the ghost is
sound before a prime step at edge `e`, the two touched sites `e` and
`e.rightNeighbor` are sound afterwards.  This is the only part of prime run
soundness not closed here; its ordinary analogue is
`coverageLeavesGhostStep_color_sound` / `coverageLeavesMovedPair_sound`
(`TokenCorrectnessLemma4CoverageLeaves.lean:1425-2240`), which must be
re-run against the prime prelude (Algorithm-2 line 6 suppressed, line 8
unconditional) and `pprimeMoveToken`.
-/
def PrimeSelectedPairSound : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind),
    GhostSound G →
    SiteSound (ghostStepPrime hpsi ring t G e) kind e ∧
      SiteSound (ghostStepPrime hpsi ring t G e) kind
        (ring.rightNeighbor e)

/-- Off the selected pair, `pprimeStep` leaves the physical state unchanged. -/
theorem pprimeStep_frame {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) (e j : Fin n)
    (hje : j ≠ e) (hjr : j ≠ ring.rightNeighbor e) :
    pprimeStep ring C e j = C j := by
  simp [pprimeStep, PopulationProtocol.step, hje, hjr]

/-- One prime ghost step preserves soundness, given the selected-pair clause. -/
theorem prime_ghostSound_step
    (hpair : PrimeSelectedPairSound)
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hG : GhostSound G) :
    GhostSound (ghostStepPrime hpsi ring t G e) := by
  apply ghostSound_of_siteSound
  intro kind j
  by_cases hje : j = e
  · subst hje
    exact (hpair hpsi ring t G j kind hG).1
  · by_cases hjr : j = ring.rightNeighbor e
    · subst hjr
      exact (hpair hpsi ring t G e kind hG).2
    · intro z hz
      rw [ghostTokenAt_ghostStep_frame_prime
        hpsi ring t G e j kind hje hjr] at hz
      have hs := siteSound_of_ghostSound hG kind j z hz
      have hphys :
          (ghostStepPrime hpsi ring t G e).phys j = G.phys j := by
        rw [ghostStepPrime_phys]
        exact pprimeStep_frame ring G.phys e j hje hjr
      have hphysV :
          ValidToken kind (ghostStepPrime hpsi ring t G e).phys j ↔
            ValidToken kind G.phys j := by
        unfold ValidToken
        rw [hphys]
      rw [hphys]
      exact ⟨hs.1, hphysV.mpr hs.2⟩

/-- `RunSound primeRunner`, from the selected-pair clause alone. -/
theorem prime_runSound_of_selectedPair
    (hpair : PrimeSelectedPairSound) :
    RunSound primeRunner := by
  intro n psi kappa hpsi ring C0 pre
  have h0 : GhostSound (initialGhost C0) :=
    lemma4CoverageGhostRunSound_proved hpsi ring C0 []
  have hrun :
      ∀ (t : Nat) (G : GhostConfig n psi kappa) (s : DetSchedule n),
        GhostSound G → GhostSound (primeRunner.run hpsi ring t G s) := by
    intro t G s hG
    induction s generalizing t G with
    | nil => exact hG
    | cons e es ih =>
        exact ih (t + 1) (ghostStepPrime hpsi ring t G e)
          (prime_ghostSound_step hpair hpsi ring t G e hG)
  exact hrun 0 (initialGhost C0) pre h0

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.primeRunner_physRun
#print axioms PPL.Lemma4Generic.prime_idsUniqueStep
#print axioms PPL.Lemma4Generic.prime_ghostSound_step
#print axioms PPL.Lemma4Generic.prime_runSound_of_selectedPair

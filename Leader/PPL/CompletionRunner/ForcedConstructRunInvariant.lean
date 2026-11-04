import Leader.PPL.CompletionRunner.ForcedConstructBridge
import Leader.PPL.SPLEntry.GappedRiskyFlushPhaseScoped
import Leader.PPL.TokenCompletion.RunFacts
import Leader.PPL.TokenCompletion.FreshTerminalRun
import Leader.PPL.TokenCompletion.RightmostInitiatorAged

/-!
# Step-parametric Lemma 4: an invariant for prime ghost runs

The ordinary Lemma-4 producers consume their reachability hypothesis
`G = ghostRun hpsi ring 0 (initialGhost C0) pre` only through a handful of
derived facts about `G`.  A prime-reachable `G` is not ordinary-reachable,
so those facts are collected here as an invariant and shown to be preserved
by every prime ghost step:

  `PrimeRunInv ring root t G` :=
    `L18RiskySweepPrefix2 ring root psi G.phys` (CDLAt plus no risky token in
       the first `psi` offsets from `root`)
    ∧ `GhostSound G`
    ∧ `GhostIdsUniqueAt t G`
    ∧ `∀ k, Lemma4FreshKinematics ring k G`
    ∧ `∀ k, PrimeTerminalHistory k G`.

Preservation (`primeRunInv_step`) needs `3 ≤ n` and `psi < n`:

* the physical clause is `l18GappedRiskyInsertedStepRow_proved` at `j = psi`
  (an arbitrary `pprimeStep` letter);
* CDLAt gives `PreludeAgree` (`preludeAgree_of_CDLAt`), so the one-step bridge
  `ghostStepPrime_bridge` applies: the prime ghost step is the ordinary ghost
  step with the physical part replaced (`ghostStepPrime_eq_withPhys`);
* soundness is `ghostSound_ghostStepPrime_of_preludeAgree`;
* ID uniqueness is the prime step lemma `ghostIdsUnique_step_prime`;
* fresh kinematics and terminal history are ghost-only, so they follow from
  the ordinary one-step lemmas `lemma4FreshKinematics_step` (RunFacts:1578)
  and `terminalHistory_step` (FreshTerminalRun:933) through the bridge.

`primeRunInv_initial` starts the invariant at `initialGhost C0` for any `C0`
with `L18RiskySweepPrefix2 ring root psi C0`, and `primeRunInv_run` carries it
along `ghostRunPrime`.  `primeRunInv_provenance` recovers
`Lemma4FreshTerminalProvenance`.

Private upstream lemmas are reached by mangled name (`privc%`).
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Convergence.L18

open Lean Elab Term Meta in
/-- `privc% M D` elaborates to the private declaration `D` of module `M`. -/
elab "privc% " m:ident d:ident : term => do
  let n : Name := Name.append ((`_private ++ m.getId).num 0) d.getId
  mkConstWithFreshMVarLevels n

/-- Public copy of the private `Lemma4FreshTerminalHistory`
(FreshTerminalRun:12). -/
def PrimeTerminalHistory {n psi kappa : Nat} (k : Fin n)
    (G : GhostConfig n psi kappa) : Prop :=
  ∀ kind i z,
    ghostTokenAt kind G i = some z →
    FreshAt kind k z.lmeta →
    z.lmeta.moves < tokenTrajectoryMoves psi ∨
      HasFreshCompletion kind k G

/-- The prime ghost-run invariant. -/
def PrimeRunInv {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n)
    (t : Nat) (G : GhostConfig n psi kappa) : Prop :=
  L18RiskySweepPrefix2 ring root psi G.phys ∧
    GhostSound G ∧
    GhostIdsUniqueAt t G ∧
    (∀ k : Fin n, Lemma4FreshKinematics ring k G) ∧
    (∀ k : Fin n, PrimeTerminalHistory k G)

/-- Under `PreludeAgree`, the prime ghost step is the ordinary ghost step
with its physical part replaced by `pprimeStep`. -/
theorem ghostStepPrime_eq_withPhys {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e))) :
    ghostStepPrime hpsi ring t G e =
      { ghostStep hpsi ring t G e with phys := pprimeStep ring G.phys e } := by
  obtain ⟨hb, hw, hc, _⟩ := ghostStepPrime_bridge hpsi ring t G e hpre
  have hp : (ghostStepPrime hpsi ring t G e).phys = pprimeStep ring G.phys e := rfl
  generalize ghostStepPrime hpsi ring t G e = X at hb hw hc hp
  cases X
  simp only at hb hw hc hp
  subst hb hw hc hp
  rfl

/-- Ordinary one-step fresh kinematics (private, RunFacts:1578). -/
theorem pri_freshKinematics_step {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (t : Nat) (G : GhostConfig n psi kappa)
    (e : Fin n) (h : Lemma4FreshKinematics ring k G) :
    Lemma4FreshKinematics ring k (ghostStep hpsi ring t G e) :=
  (privc% Leader.PPL.TokenCompletion.RunFacts PPL.lemma4FreshKinematics_step)
    hpsi ring k t G e h

/-- Ordinary one-step terminal history (private, FreshTerminalRun:933). -/
theorem pri_terminalHistory_step {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (t : Nat) (G : GhostConfig n psi kappa)
    (e : Fin n) (h : PrimeTerminalHistory k G) :
    PrimeTerminalHistory k (ghostStep hpsi ring t G e) :=
  (privc% Leader.PPL.TokenCompletion.FreshTerminalRun PPL.terminalHistory_step)
    hpsi ring k t G e h

/-- One prime ghost step preserves `PrimeRunInv`. -/
theorem primeRunInv_step {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hlt : psi < n) (ring : DirectedRing n) (root : Fin n) (t : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (hI : PrimeRunInv ring root t G) :
    PrimeRunInv ring root (t + 1) (ghostStepPrime hpsi ring t G e) := by
  obtain ⟨hpref, hsound, huniq, hkin, hhist⟩ := hI
  have hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e)) :=
    preludeAgree_of_CDLAt hpsi ring root G.phys e hpref.1
  have hn2 : 2 ≤ n := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact l18GappedRiskyInsertedStepRow_proved hn3 hpsi hlt ring root psi
      G.phys e (Nat.le_refl psi) hpref
  · exact ghostSound_ghostStepPrime_of_preludeAgree hpsi ring t G e hsound hpre
  · exact ghostIdsUnique_step_prime hpsi hn2 ring t G e huniq
  · intro k
    rw [ghostStepPrime_eq_withPhys hpsi ring t G e hpre]
    exact pri_freshKinematics_step hpsi ring k t G e (hkin k)
  · intro k
    rw [ghostStepPrime_eq_withPhys hpsi ring t G e hpre]
    exact pri_terminalHistory_step hpsi ring k t G e (hhist k)

/-- The invariant holds at the initial ghost of any configuration with the
risky-sweep prefix at `psi`. -/
theorem primeRunInv_initial {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (root : Fin n) (C0 : Config n psi kappa)
    (h0 : L18RiskySweepPrefix2 ring root psi C0) :
    PrimeRunInv ring root 0 (initialGhost C0) := by
  refine ⟨h0, ?_, ghostIdsUnique_initial C0, ?_, ?_⟩
  · exact lemma4CoverageGhostRunSound_proved hpsi ring C0 []
  · intro k kind i z howner hfresh
    rcases hfresh with ⟨t, hborn, _hsite⟩
    have hU := (ghostIdsUnique_initial C0).2 kind i z kind t howner hborn
    omega
  · intro k kind i z howner hfresh
    rcases hfresh with ⟨t, hborn, _hsite⟩
    have hU := (ghostIdsUnique_initial C0).2 kind i z kind t howner hborn
    omega

/-- The invariant along a prime ghost run. -/
theorem primeRunInv_run {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hlt : psi < n) (ring : DirectedRing n) (root : Fin n) :
    ∀ (t : Nat) (G : GhostConfig n psi kappa) (s : DetSchedule n),
      PrimeRunInv ring root t G →
      PrimeRunInv ring root (t + s.length) (ghostRunPrime hpsi ring t G s) := by
  intro t G s hI
  induction s generalizing t G with
  | nil => exact hI
  | cons e es ih =>
      have h := ih (t + 1) (ghostStepPrime hpsi ring t G e)
        (primeRunInv_step hn3 hpsi hlt ring root t G e hI)
      simp only [List.length_cons]
      rw [show t + (es.length + 1) = t + 1 + es.length by omega]
      exact h

/-- The invariant along a prime run from an initial ghost. -/
theorem primeRunInv_of_run {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hlt : psi < n) (ring : DirectedRing n) (root : Fin n)
    (C0 : Config n psi kappa) (h0 : L18RiskySweepPrefix2 ring root psi C0)
    (pre : DetSchedule n) :
    PrimeRunInv ring root pre.length (ghostRunPrime hpsi ring 0 (initialGhost C0) pre) := by
  have h := primeRunInv_run hn3 hpsi hlt ring root 0 (initialGhost C0) pre
    (primeRunInv_initial hpsi ring root C0 h0)
  simpa using h

/-- Terminal provenance from the invariant (as in
`lemma4FreshTerminalProvenance_run`). -/
theorem primeRunInv_provenance {n psi kappa : Nat} {ring : DirectedRing n}
    {root : Fin n} {t : Nat} {G : GhostConfig n psi kappa}
    (hI : PrimeRunInv ring root t G) (k : Fin n) :
    Lemma4FreshTerminalProvenance k G := by
  intro kind i z howner hnoCompletion hfresh
  rcases hI.2.2.2.2 k kind i z howner hfresh with hyoung | hcomplete
  · exact hyoung
  · exact False.elim (hnoCompletion hcomplete)

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.primeRunInv_step
#print axioms PPL.Lemma4Generic.primeRunInv_of_run
#print axioms PPL.Lemma4Generic.primeRunInv_provenance

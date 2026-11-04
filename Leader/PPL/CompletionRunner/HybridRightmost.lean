import Leader.PPL.CompletionRunner.HybridServiceGeometry
import Leader.PPL.TokenCompletion.StepPropsClosed
import Leader.PPL.TokenCompletion.RightmostResponderLiteral
import Leader.PPL.TokenCompletion.RightmostResponderSelectedPair
import Leader.PPL.TokenCompletion.OffPairLiteral
import Leader.PPL.TokenCompletion.RightmostResponder
import Leader.PPL.TokenCompletion.RightmostInitiatorStateLocal

/-!
# Step-parametric Lemma 4: `RightmostProgressStep` for the hybrid runner

The ordinary producer (`lemma4RightmostProgressStep_closed`, RightmostRows:361,
through `lemma4RightmostProgressStep`, Rightmost:197, and the three run-history
adapters RightmostInitiatorAged:250, RightmostResponder:173 and :249) consumes
its run hypothesis only through four facts about the pre-state:

* `GhostSound G`, `GhostIdsUniqueAt step G`, `Lemma4FreshKinematics ring k G`,
* `Lemma4FreshTerminalProvenance k G` (initiator branch only).

The three state-local literal leaves take exactly these facts and a free
clock: `Lemma4RightmostInitiatorLiteralCasesAged` (closed from the terminal
and survival residuals), `Lemma4RightmostResponderLiteralCases` (from the
selected-pair cases) and `Lemma4RightmostOffPairLiteralCases`.

1. `ordRightmost_ofFacts`: the ordinary assembly for an arbitrary `G` with the
   four facts (no run hypothesis), by re-running Rightmost:197 and
   RightmostRows:231-358 on the literal leaves.
2. `primeRightmost_ofFacts`: the same outcome for `ghostStepPrime` through the
   bridge (`rmOut_transfer`: the outcome reads the post-state through the ghost
   maps, the completion log, `ValidToken` and `lemma4TokenProgress` only).
3. `hybrid_rightmostProgressStep : RightmostProgressStep hybridRunner`, with
   the four facts from `HybridInv`.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Convergence.L18

/-- The rightmost-progress outcome for a pre-state `G` and a post-state `G'`
(the body of `RightmostProgressStep`). -/
def RmOut {n psi kappa : Nat} (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (G G' : GhostConfig n psi kappa) (e : Fin n) (x : Fin (2 * psi))
    (z : GhostToken n psi) : Prop :=
  let i := shiftRight ring k x.val
  (¬FreshAt kind k z.lmeta ∧
      ∀ j z',
        ghostTokenAt kind G' j = some z' ->
        z'.lmeta.id ≠ z.lmeta.id) ∨
    HasFreshCompletion kind k G' ∨
    ∃ y z',
      Lemma4RightmostAt ring k kind G' y z' ∧
        z'.lmeta.id = z.lmeta.id ∧
        (FreshAt kind k z.lmeta ->
          FreshAt kind k z'.lmeta) ∧
        lemma4TokenProgress
            kind (G.phys i) z.value <=
          lemma4TokenProgress
            kind
            (G'.phys (shiftRight ring k y.val))
            z'.value ∧
        (e = lemma4ServiceEdge ring kind G i z ->
          lemma4TokenProgress
              kind
              (G'.phys (shiftRight ring k y.val))
              z'.value =
            lemma4TokenProgress
              kind (G.phys i) z.value + 1)

/-- Terminal provenance from terminal history. -/
theorem provenance_of_history {n psi kappa : Nat} {k : Fin n}
    {G : GhostConfig n psi kappa} (h : PrimeTerminalHistory k G) :
    Lemma4FreshTerminalProvenance k G := by
  intro kind i z howner hnoCompletion hfresh
  rcases h kind i z howner hfresh with hyoung | hcomplete
  · exact hyoung
  · exact False.elim (hnoCompletion hcomplete)

/-! ## 1. Ordinary assembly without the run hypothesis -/

theorem ordRightmost_ofFacts {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (x : Fin (2 * psi))
    (z : GhostToken n psi) (hsound : GhostSound G)
    (huniq : GhostIdsUniqueAt step G) (hkin : Lemma4FreshKinematics ring k G)
    (hage : Lemma4FreshTerminalProvenance k G)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStep hpsi ring step G e).phys)
    (hcov : Lemma4GhostCoveredWindow ring k kind G)
    (hright : Lemma4RightmostAt ring k kind G x z) :
    RmOut ring k kind G (ghostStep hpsi ring step G e) e x z := by
  have initLit : Lemma4RightmostInitiatorLiteralCasesAged :=
    lemma4RightmostInitiatorLiteralCasesAged_of_noPriorRow
      (lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_stateLocalResiduals
        lemma4RightmostInitiatorTerminalStateLocalResidual_proved
        lemma4RightmostInitiatorSurvivalStateLocalResidual_proved)
  have respLit : Lemma4RightmostResponderLiteralCases :=
    lemma4RightmostResponderLiteralCases_of_selectedPairCases
      lemma4RightmostResponderSelectedPairCases_proved
  have offLit : Lemma4RightmostOffPairLiteralCases :=
    lemma4RightmostOffPairLiteralCases_proved
  have hownOther : ∀ j, j ≠ e → j ≠ ring.rightNeighbor e →
      ghostTokenAt kind (ghostStep hpsi ring step G e) j = ghostTokenAt kind G j :=
    fun j hje hjr =>
      (privc% Leader.PPL.TokenCompletion.CoverageRows
        PPL.coverageRowsGhostStepOwnerOther) hpsi ring step G e j kind hje hjr
  have hphysOther : ∀ j, j ≠ e → j ≠ ring.rightNeighbor e →
      (ghostStep hpsi ring step G e).phys j = G.phys j :=
    fun j hje hjr =>
      (privc% Leader.PPL.TokenCompletion.CoverageRows
        PPL.coverageRowsGhostStepPhysOther) hpsi ring step G e j hje hjr
  by_cases hie : e = shiftRight ring k x.val
  · have hageZ := hage kind (shiftRight ring k x.val) z hright.1
    exact initLit hpsi ring k kind step G e x z hCd hCd' hcov hsound huniq hkin
      hageZ hright hie
  · by_cases hir : ring.rightNeighbor e = shiftRight ring k x.val
    · exact respLit hpsi ring k kind step G e x z hCd hCd' hcov hsound huniq hkin
        hright hir
    · have hie' : shiftRight ring k x.val ≠ e := fun h => hie h.symm
      have hir' : shiftRight ring k x.val ≠ ring.rightNeighbor e := fun h => hir h.symm
      have hphys := hphysOther _ hie' hir'
      have hR' : Lemma4RightmostAt ring k kind (ghostStep hpsi ring step G e) x z := by
        refine ⟨(hownOther _ hie' hir').trans hright.1, ?_, ?_⟩
        · have hv := hright.2.1
          unfold ValidToken at hv ⊢
          rw [hphys]
          exact hv
        · intro y hxy
          by_cases hje : shiftRight ring k y.val = e
          · exact offLit hpsi ring k kind step G e x z hCd hCd' hcov hsound huniq hkin
              hright hie hir y hxy (Or.inl hje)
          · by_cases hjr : shiftRight ring k y.val = ring.rightNeighbor e
            · exact offLit hpsi ring k kind step G e x z hCd hCd' hcov hsound huniq hkin
                hright hie hir y hxy (Or.inr hjr)
            · rw [hownOther _ hje hjr]
              exact hright.2.2 y hxy
      refine Or.inr (Or.inr ⟨x, z, hR', rfl, id, ?_, ?_⟩)
      · rw [hphys]
        exact Nat.le_refl _
      · intro hservice
        exfalso
        unfold lemma4ServiceEdge at hservice
        by_cases hpos : 0 < decodeOffset psi (tokenCode z.value)
        · rw [if_pos hpos] at hservice
          exact hie hservice
        · rw [if_neg hpos] at hservice
          apply hir
          rw [hservice]
          exact (privc% Leader.PPL.TokenCompletion.Rightmost
            PPL.lemma4RightNeighborLeftNeighbor) ring _

/-! ## 2. Transfer to the prime step -/

theorem rmOut_transfer {n psi kappa : Nat} {ring : DirectedRing n} {k : Fin n}
    {kind : TokenKind} {G Go Gp : GhostConfig n psi kappa} {e : Fin n}
    {x : Fin (2 * psi)} {z : GhostToken n psi}
    (hown : ∀ j, ghostTokenAt kind Gp j = ghostTokenAt kind Go j)
    (hag : ∀ j, PhysAgree (Gp.phys j) (Go.phys j))
    (hcomp : Gp.completed = Go.completed)
    (h : RmOut ring k kind G Go e x z) : RmOut ring k kind G Gp e x z := by
  have hF := hasFreshCompletion_of_completed kind k hcomp
  have hP : ∀ j v, lemma4TokenProgress kind (Gp.phys j) v =
      lemma4TokenProgress kind (Go.phys j) v :=
    fun j v => progress_of_dist kind (hag j).2.2.1 v
  unfold RmOut at h ⊢
  dsimp only at h ⊢
  rcases h with ⟨hnf, hgone⟩ | hdone | ⟨y, z', hR, hid, hfr, hle, hsvc⟩
  · exact Or.inl ⟨hnf, fun j z' hj => hgone j z' ((hown j).symm.trans hj)⟩
  · exact Or.inr (Or.inl (hF.2 hdone))
  · refine Or.inr (Or.inr ⟨y, z', rightmostAt_transfer hown hag y z' hR, hid, hfr, ?_, ?_⟩)
    · rw [hP]
      exact hle
    · intro hedge
      rw [hP]
      exact hsvc hedge

theorem primeRightmost_ofFacts {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (x : Fin (2 * psi))
    (z : GhostToken n psi) (hsound : GhostSound G)
    (huniq : GhostIdsUniqueAt step G) (hkin : Lemma4FreshKinematics ring k G)
    (hage : Lemma4FreshTerminalProvenance k G)
    (hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e)))
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStepPrime hpsi ring step G e).phys)
    (hcov : Lemma4GhostCoveredWindow ring k kind G)
    (hright : Lemma4RightmostAt ring k kind G x z) :
    RmOut ring k kind G (ghostStepPrime hpsi ring step G e) e x z := by
  obtain ⟨hown, hag⟩ := prime_ordinary_views hpsi ring step G e hpre kind
  have hcomp := prime_ordinary_views' hpsi ring step G e hpre
  have hCdO : Cd ring k kind (ghostStep hpsi ring step G e).phys :=
    cd_of_physAgree hag hCd'
  exact rmOut_transfer hown hag hcomp
    (ordRightmost_ofFacts hpsi ring k kind step G e x z hsound huniq hkin hage
      hCd hCdO hcov hright)

/-! ## 3. The hybrid runner -/

theorem hybrid_rightmostProgressStep : RightmostProgressStep hybridRunner := by
  intro n psi kappa hpsi ring k kind C0 pre G e x z hrun hCd hCd' hcov hright
  have hI := hybridInv_of_hrun hrun
  have hn2 := two_le_n_of_cd hpsi ring k kind G.phys hCd
  have hage := provenance_of_history (hI.2.2.2 k)
  show RmOut ring k kind G (hybridRunner.gstep hpsi ring pre.length G e) e x z
  rw [hybridRunner_gstep] at hCd' ⊢
  by_cases hg : PrimeGood ring G.phys
  · rw [hybridGStep_good hpsi ring pre.length G e hg] at hCd' ⊢
    exact primeRightmost_ofFacts hpsi ring k kind pre.length G e x z hI.1 (hI.2.1 hn2)
      (hI.2.2.1 k) hage (preludeAgree_of_good hpsi ring G.phys e hg) hCd hCd' hcov hright
  · rw [hybridGStep_bad hpsi ring pre.length G e hg] at hCd' ⊢
    exact ordRightmost_ofFacts hpsi ring k kind pre.length G e x z hI.1 (hI.2.1 hn2)
      (hI.2.2.1 k) hage hCd hCd' hcov hright

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.ordRightmost_ofFacts
#print axioms PPL.Lemma4Generic.primeRightmost_ofFacts
#print axioms PPL.Lemma4Generic.hybrid_rightmostProgressStep

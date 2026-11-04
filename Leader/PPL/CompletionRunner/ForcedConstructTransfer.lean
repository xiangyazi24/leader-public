import Leader.PPL.CompletionRunner.ForcedConstructRunInvariant
import Leader.PPL.TokenCompletion.CoverageLeaves
import Leader.PPL.TokenCompletion.CoverageTouched
import Leader.PPL.TokenCompletion.CoverageOrigin
import Leader.PPL.TokenCompletion.SweepOldOwnerInteracted

/-!
# Step-parametric Lemma 4: prime step Props from the ordinary rows

The two cheapest ordinary step producers consume their run hypothesis only
through `GhostSound G` (coverage step) or `GhostSound G` and
`GhostIdsUniqueAt step G` (old-owner progress step); their rows take an
arbitrary `G` and a free clock `step`.  So:

1. the ordinary assembly is re-run for an arbitrary `G` carrying those facts
   (`ordCoverage_ofSound`, `ordOldOwner_ofSound`; no run hypothesis);
2. the conclusion, which reads the post-state only through the ghost maps,
   `ValidToken` (token and `dist`) and `lemma4TokenProgress` (`dist`), is
   carried to `ghostStepPrime` by the one-step bridge under `PreludeAgree`
   (`primeCoverage_ofSound`, `primeOldOwner_ofSound`);
3. along a prime run from a configuration with
   `L18RiskySweepPrefix2 ring root psi C0` (and `3 ≤ n`, `psi < n`) the
   needed facts and `PreludeAgree` come from `PrimeRunInv`
   (`prime_coverageStep_scoped`, `prime_oldOwnerProgressStep_scoped`).

The scoped statements are the generic `CoverageStep primeRunner` (second
clause) and `OldOwnerProgressStep primeRunner` with the extra hypotheses
`3 ≤ n`, `psi < n` and `L18RiskySweepPrefix2 ring root psi C0`
(`primeRunner.run` / `.gstep` are `ghostRunPrime` / `ghostStepPrime` by `rfl`).
The first clause of `CoverageStep` (initial ghost) is runner-independent.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Convergence.L18

/-! ## 1. Reading the post-state through bridged fields -/

theorem physAgree_tokenAt {psi kappa : Nat} {a b : State psi kappa}
    (h : PhysAgree a b) (kind : TokenKind) : tokenAt kind a = tokenAt kind b := by
  cases kind
  · exact h.1
  · exact h.2.1

/-- `Cd` reads only `dist` and `last`. -/
theorem cd_of_physAgree {n psi kappa : Nat} {ring : DirectedRing n} {k : Fin n}
    {kind : TokenKind} {C C' : Config n psi kappa}
    (h : ∀ i, PhysAgree (C i) (C' i)) (hC : Cd ring k kind C) :
    Cd ring k kind C' := by
  intro x
  have hx := hC x
  dsimp only at hx ⊢
  rw [← (h _).2.2.1, ← (h _).2.2.2]
  exact hx

/-- `ValidToken` reads only the token and `dist`. -/
theorem validToken_of_physAgree {n psi kappa : Nat} {C C' : Config n psi kappa}
    (h : ∀ i, PhysAgree (C i) (C' i)) (kind : TokenKind) (i : Fin n) :
    ValidToken kind C i ↔ ValidToken kind C' i :=
  validToken_congr kind C C' i (physAgree_tokenAt (h i) kind) (h i).2.2.1

/-- `lemma4TokenProgress` reads the state only through `dist`. -/
theorem progress_of_dist {psi kappa : Nat} (kind : TokenKind)
    {a b : State psi kappa} (hd : a.dist = b.dist) (v : TokenData psi) :
    lemma4TokenProgress kind a v = lemma4TokenProgress kind b v := by
  unfold lemma4TokenProgress lemma4TokenStage tokenTargetCoordinate
  rw [hd]

/-- Under `PreludeAgree`: equal ghost maps and `PhysAgree` physical parts,
in the form used below. -/
theorem prime_ordinary_views {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e)))
    (kind : TokenKind) :
    (∀ j, ghostTokenAt kind (ghostStepPrime hpsi ring t G e) j =
        ghostTokenAt kind (ghostStep hpsi ring t G e) j) ∧
      (∀ j, PhysAgree ((ghostStepPrime hpsi ring t G e).phys j)
        ((ghostStep hpsi ring t G e).phys j)) := by
  obtain ⟨hb, hw, _, hph⟩ := ghostStepPrime_bridge hpsi ring t G e hpre
  refine ⟨?_, hph⟩
  intro j
  cases kind
  · show (ghostStepPrime hpsi ring t G e).black j = (ghostStep hpsi ring t G e).black j
    rw [hb]
  · show (ghostStepPrime hpsi ring t G e).white j = (ghostStep hpsi ring t G e).white j
    rw [hw]

/-! ## 2. Coverage step -/

/-- The ordinary coverage-step assembly (`lemma4CoverageStep_of_sound_rows`,
CoverageRows:525) for an arbitrary sound `G` and clock `step`. -/
theorem ordCoverage_ofSound {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (hsound : GhostSound G)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStep hpsi ring step G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G) :
    Lemma4GhostCoveredWindow ring k kind (ghostStep hpsi ring step G e) ∧
      ∀ i z,
        Lemma4InWindow ring k psi i →
        ghostTokenAt kind (ghostStep hpsi ring step G e) i = some z →
        FreshAt kind k z.lmeta ∨
          ∃ j z0,
            Lemma4InWindow ring k psi j ∧
            ghostTokenAt kind G j = some z0 ∧
            z.lmeta.id = z0.lmeta.id := by
  have htouched : Lemma4CoverageTouchedCoverageSound :=
    lemma4CoverageTouchedCoverageSound_proved
  have horigin : Lemma4CoverageTouchedOrigin :=
    lemma4CoverageTouchedOrigin_of_endpoint_rows
    lemma4CoverageOriginInitiatorRow_proved lemma4CoverageOriginResponderRow_proved
  have hphysOther : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e →
      (ghostStep hpsi ring step G e).phys i = G.phys i :=
    fun i hie hir =>
      (privc% Leader.PPL.TokenCompletion.CoverageRows
        PPL.coverageRowsGhostStepPhysOther) hpsi ring step G e i hie hir
  have hownOther : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e →
      ghostTokenAt kind (ghostStep hpsi ring step G e) i = ghostTokenAt kind G i :=
    fun i hie hir =>
      (privc% Leader.PPL.TokenCompletion.CoverageRows
        PPL.coverageRowsGhostStepOwnerOther) hpsi ring step G e i kind hie hir
  constructor
  · intro i hiwin hvalid
    by_cases hie : i = e
    · exact htouched hpsi ring k kind step G e i hCd hCd' hcovered hsound
        (Or.inl hie) hiwin hvalid
    · by_cases hir : i = ring.rightNeighbor e
      · exact htouched hpsi ring k kind step G e i hCd hCd' hcovered hsound
          (Or.inr hir) hiwin hvalid
      · have hvalid0 : ValidToken kind G.phys i := by
          unfold ValidToken at hvalid ⊢
          rw [hphysOther i hie hir] at hvalid
          exact hvalid
        obtain ⟨z, hz⟩ := hcovered i hiwin hvalid0
        exact ⟨z, (hownOther i hie hir).trans hz⟩
  · intro i z hiwin howner
    by_cases hie : i = e
    · exact horigin hpsi ring k kind step G e i z hCd hCd' (Or.inl hie) hiwin howner
    · by_cases hir : i = ring.rightNeighbor e
      · exact horigin hpsi ring k kind step G e i z hCd hCd' (Or.inr hir) hiwin howner
      · exact Or.inr ⟨i, z, hiwin, (hownOther i hie hir).symm.trans howner, rfl⟩

/-- Prime coverage step, for an arbitrary sound `G` whose selected pair
satisfies `PreludeAgree`. -/
theorem primeCoverage_ofSound {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (hsound : GhostSound G)
    (hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e)))
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStepPrime hpsi ring step G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G) :
    Lemma4GhostCoveredWindow ring k kind (ghostStepPrime hpsi ring step G e) ∧
      ∀ i z,
        Lemma4InWindow ring k psi i →
        ghostTokenAt kind (ghostStepPrime hpsi ring step G e) i = some z →
        FreshAt kind k z.lmeta ∨
          ∃ j z0,
            Lemma4InWindow ring k psi j ∧
            ghostTokenAt kind G j = some z0 ∧
            z.lmeta.id = z0.lmeta.id := by
  obtain ⟨hown, hag⟩ := prime_ordinary_views hpsi ring step G e hpre kind
  have hCdO : Cd ring k kind (ghostStep hpsi ring step G e).phys :=
    cd_of_physAgree hag hCd'
  obtain ⟨h1, h2⟩ := ordCoverage_ofSound hpsi ring k kind step G e hsound hCd hCdO hcovered
  constructor
  · intro i hiwin hvalid
    obtain ⟨z, hz⟩ := h1 i hiwin ((validToken_of_physAgree hag kind i).1 hvalid)
    exact ⟨z, (hown i).trans hz⟩
  · intro i z hiwin howner
    exact h2 i z hiwin ((hown i).symm.trans howner)

/-- Scoped prime `CoverageStep` (second clause of `CoverageStep primeRunner`)
along prime runs from an `L18RiskySweepPrefix2 … psi` configuration. -/
theorem prime_coverageStep_scoped {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hlt : psi < n) (ring : DirectedRing n) (root k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa) (h0 : L18RiskySweepPrefix2 ring root psi C0)
    (pre : DetSchedule n) (G : GhostConfig n psi kappa) (e : Fin n)
    (hrun : G = primeRunner.run hpsi ring 0 (initialGhost C0) pre)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (primeRunner.gstep hpsi ring pre.length G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G) :
    let G' := primeRunner.gstep hpsi ring pre.length G e
    Lemma4GhostCoveredWindow ring k kind G' ∧
      ∀ i z,
        Lemma4InWindow ring k psi i →
        ghostTokenAt kind G' i = some z →
        FreshAt kind k z.lmeta ∨
          ∃ j z0,
            Lemma4InWindow ring k psi j ∧
            ghostTokenAt kind G j = some z0 ∧
            z.lmeta.id = z0.lmeta.id := by
  have hI : PrimeRunInv ring root pre.length G := by
    rw [hrun]
    exact primeRunInv_of_run hn3 hpsi hlt ring root C0 h0 pre
  exact primeCoverage_ofSound hpsi ring k kind pre.length G e hI.2.1
    (preludeAgree_of_CDLAt hpsi ring root G.phys e hI.1.1) hCd hCd' hcovered

/-! ## 3. Old-owner progress step -/

/-- The ordinary old-owner assembly (`lemma4SweepOldOwnerProgressStep_of_rows`,
SweepOldOwnerRows:342) for an arbitrary `G` with soundness and ID uniqueness
at clock `step`. -/
theorem ordOldOwner_ofSound {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (hsound : GhostSound G)
    (huniq : GhostIdsUniqueAt step G)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStep hpsi ring step G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G)
    (i : Fin n) (z : GhostToken n psi) (hwin : Lemma4InWindow ring k psi i)
    (howner : ghostTokenAt kind G i = some z) (hnonfresh : ¬ FreshAt kind k z.lmeta) :
    Lemma4SweepOldOwnerOutcome hpsi ring k kind step G e i z := by
  by_cases hie : i = e
  · subst i
    exact lemma4SweepOldOwnerInitiatorRow_proved hpsi ring k kind step G e z
      hCd hCd' hcovered hsound huniq hwin howner hnonfresh
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      exact lemma4SweepOldOwnerResponderRow_proved hpsi ring k kind step G e z
        hCd hCd' hcovered hsound huniq hwin howner hnonfresh
    · exact lemma4SweepOldOwnerFrameRow_proved hpsi ring k kind step G e i z
        hCd hCd' hcovered hsound huniq hwin howner hnonfresh hie hir

/-- Prime old-owner progress step, for an arbitrary `G` with soundness,
ID uniqueness and `PreludeAgree` on the selected pair. -/
theorem primeOldOwner_ofSound {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (hsound : GhostSound G)
    (huniq : GhostIdsUniqueAt step G)
    (hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e)))
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStepPrime hpsi ring step G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G)
    (i : Fin n) (z : GhostToken n psi) (hwin : Lemma4InWindow ring k psi i)
    (howner : ghostTokenAt kind G i = some z) (hnonfresh : ¬ FreshAt kind k z.lmeta) :
    let G' := ghostStepPrime hpsi ring step G e
    (∀ (j : Fin n) (z' : GhostToken n psi),
        ghostTokenAt kind G' j = some z' →
        z'.lmeta.id ≠ z.lmeta.id) ∨
      ∃ j : Fin n, ∃ z' : GhostToken n psi,
        Lemma4InWindow ring k psi j ∧
          ghostTokenAt kind G' j = some z' ∧
          z'.lmeta.id = z.lmeta.id ∧
          ValidToken kind G'.phys j ∧
          lemma4TokenProgress kind (G.phys i) z.value ≤
            lemma4TokenProgress kind (G'.phys j) z'.value ∧
          (e = lemma4ServiceEdge ring kind G i z →
            lemma4TokenProgress kind (G'.phys j) z'.value =
              lemma4TokenProgress kind (G.phys i) z.value + 1) := by
  obtain ⟨hown, hag⟩ := prime_ordinary_views hpsi ring step G e hpre kind
  have hCdO : Cd ring k kind (ghostStep hpsi ring step G e).phys :=
    cd_of_physAgree hag hCd'
  have hO := ordOldOwner_ofSound hpsi ring k kind step G e hsound huniq hCd hCdO
    hcovered i z hwin howner hnonfresh
  unfold Lemma4SweepOldOwnerOutcome at hO
  have hP : ∀ j v, lemma4TokenProgress kind ((ghostStepPrime hpsi ring step G e).phys j) v =
      lemma4TokenProgress kind ((ghostStep hpsi ring step G e).phys j) v :=
    fun j v => progress_of_dist kind (hag j).2.2.1 v
  dsimp only
  rcases hO with hgone | ⟨j, z', hjwin, hjown, hid, hvalid, hle, hserv⟩
  · left
    intro j z' hj
    exact hgone j z' ((hown j).symm.trans hj)
  · right
    refine ⟨j, z', hjwin, (hown j).trans hjown, hid,
      (validToken_of_physAgree hag kind j).2 hvalid, ?_, ?_⟩
    · rw [hP]
      exact hle
    · intro hedge
      rw [hP]
      exact hserv hedge

/-- Scoped prime `OldOwnerProgressStep` (`OldOwnerProgressStep primeRunner`
body) along prime runs from an `L18RiskySweepPrefix2 … psi` configuration. -/
theorem prime_oldOwnerProgressStep_scoped {n psi kappa : Nat} (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi) (hlt : psi < n) (ring : DirectedRing n) (root k : Fin n)
    (kind : TokenKind) (C0 : Config n psi kappa)
    (h0 : L18RiskySweepPrefix2 ring root psi C0)
    (pre : DetSchedule n) (G : GhostConfig n psi kappa) (e : Fin n)
    (hrun : G = primeRunner.run hpsi ring 0 (initialGhost C0) pre)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (primeRunner.gstep hpsi ring pre.length G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G)
    (i : Fin n) (z : GhostToken n psi) (hwin : Lemma4InWindow ring k psi i)
    (howner : ghostTokenAt kind G i = some z) (hnonfresh : ¬ FreshAt kind k z.lmeta) :
    let G' := primeRunner.gstep hpsi ring pre.length G e
    (∀ (j : Fin n) (z' : GhostToken n psi),
        ghostTokenAt kind G' j = some z' →
        z'.lmeta.id ≠ z.lmeta.id) ∨
      ∃ j : Fin n, ∃ z' : GhostToken n psi,
        Lemma4InWindow ring k psi j ∧
          ghostTokenAt kind G' j = some z' ∧
          z'.lmeta.id = z.lmeta.id ∧
          ValidToken kind G'.phys j ∧
          lemma4TokenProgress kind (G.phys i) z.value ≤
            lemma4TokenProgress kind (G'.phys j) z'.value ∧
          (e = lemma4ServiceEdge ring kind G i z →
            lemma4TokenProgress kind (G'.phys j) z'.value =
              lemma4TokenProgress kind (G.phys i) z.value + 1) := by
  have hI : PrimeRunInv ring root pre.length G := by
    rw [hrun]
    exact primeRunInv_of_run hn3 hpsi hlt ring root C0 h0 pre
  exact primeOldOwner_ofSound hpsi ring k kind pre.length G e hI.2.1 hI.2.2.1
    (preludeAgree_of_CDLAt hpsi ring root G.phys e hI.1.1) hCd hCd' hcovered
    i z hwin howner hnonfresh

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.primeCoverage_ofSound
#print axioms PPL.Lemma4Generic.prime_coverageStep_scoped
#print axioms PPL.Lemma4Generic.primeOldOwner_ofSound
#print axioms PPL.Lemma4Generic.prime_oldOwnerProgressStep_scoped

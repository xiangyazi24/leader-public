import Leader.PPL.ReachCPB.MismatchHistFreshGeomLiteralCounterexample

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
Truth audit.

The selected-live row is false on arbitrary GhostConfig values.
The witness is deliberately lineage-coherent. Its only noncanonical feature
is historical: a live lineage is already at the terminal move count while its
ID has no entry in completed.

At psi = 2 the pre-token has:
  q = 1 = psi - 1,
  c = -1,
  moves = 5 = tokenTrajectoryMoves 2.

The literal responder c = -1 turn keeps the lineage live, advances moves to 6,
and changes the offset to +psi = +2. The post macro-stage equations therefore
force q = 2, contradicting the selected-live target q < psi.
-/

private theorem q19975Hpsi : 2 <= 2 := by
  omega

private def q19975Ring : DirectedRing 4 :=
  ⟨by decide⟩

private def q19975E0 : Fin 4 :=
  ⟨0, by decide⟩

private def q19975E2 : Fin 4 :=
  ⟨2, by decide⟩

private def q19975E3 : Fin 4 :=
  ⟨3, by decide⟩

/-- c = 1 - psi = -1 at psi = 2, with the q=1 payload (bit,carry)=(0,0). -/
private def q19975TokenNegOne : PPL.TokenData 2 :=
  ((PPL.offsetNegPsiPlusOneCode 2 q19975Hpsi,
      (0 : Fin 2)),
    (0 : Fin 2))

/--
Frozen epoch IDs:
  source k+0 = false,
  source k+1 = false,
  target b+0 = true,
  target b+1 = false.

Thus the target segment already contains the first two bits of source+1.
The selected physical pair is e=2 -> 3, with distances 1 -> 2, so Algorithm 2
does not create a leader and the black c=-1 responder is locally valid.
-/
private def q19975State
    (i : Fin 4) : PPL.State 2 1 :=
  {
    leader := false
    id := if i = q19975E2 then true else false
    dist :=
      if i = q19975E2 then
        (1 : Fin 4)
      else if i = q19975E3 then
        (2 : Fin 4)
      else
        (0 : Fin 4)
    last := false
    tokenB :=
      if i = q19975E3 then
        some q19975TokenNegOne
      else
        none
    tokenW := none
    mode := true
    clock := (1 : Fin 2)
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false
  }

private def q19975Cepoch : Config 4 2 1 :=
  q19975State

private def q19975Z : PPL.GhostToken 4 2 :=
  {
    value := q19975TokenNegOne
    lmeta :=
      {
        id := .born .black 0
        birthSite := q19975E0
        birthStep := 0
        moves := 5
      }
  }

private def q19975G : PPL.GhostConfig 4 2 1 :=
  {
    phys := q19975Cepoch
    black := fun i =>
      if i = q19975E3 then
        some q19975Z
      else
        none
    white := fun _ => none
    completed := []
  }

/-- The c=-1 turn sees left/source id=true and old carry=0. -/
private def q19975TokenPost : PPL.TokenData 2 :=
  ((PPL.offsetPsiCode 2 q19975Hpsi,
      (1 : Fin 2)),
    (0 : Fin 2))

private def q19975ZPost : PPL.GhostToken 4 2 :=
  {
    value := q19975TokenPost
    lmeta :=
      {
        id := .born .black 0
        birthSite := q19975E0
        birthStep := 0
        moves := 6
      }
  }

private def q19975GPost : PPL.GhostConfig 4 2 1 :=
  PPL.ghostStep
    q19975Hpsi q19975Ring 1
    q19975G q19975E2

private theorem q19975_decode_old :
    PPL.decodeOffset 2
        (PPL.tokenCode q19975TokenNegOne) =
      (-1 : Int) := by
  simpa [q19975TokenNegOne, PPL.tokenCode] using
    (PPL.decodeOffset_negPsiPlusOne 2 q19975Hpsi)

private theorem q19975_decode_post :
    PPL.decodeOffset 2
        (PPL.tokenCode q19975TokenPost) =
      (2 : Int) := by
  simpa [q19975TokenPost, PPL.tokenCode] using
    (PPL.decodeOffset_psi 2 q19975Hpsi)

private theorem q19975_owner_shape
    {i : Fin 4}
    {z : PPL.GhostToken 4 2}
    (h :
      PPL.ghostTokenAt .black q19975G i =
        some z) :
    And (i = q19975E3) (z = q19975Z) := by
  by_cases hi : i = q19975E3
  · subst i
    have hz : q19975Z = z := by
      simpa [q19975G, PPL.ghostTokenAt] using h
    exact And.intro rfl hz.symm
  · simp [q19975G, PPL.ghostTokenAt, hi] at h

private theorem q19975_geometry :
    Lemma16PostEpochFreshBorderGeometry
      q19975Ring q19975E2 q19975E0 2 := by
  unfold Lemma16PostEpochFreshBorderGeometry
  decide

private theorem q19975_ready :
    DetectReadyCapped q19975Ring q19975G.phys := by
  unfold DetectReadyCapped DetectReady
  refine And.intro ?_ ?_
  · refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
    · exact
        @of_decide_eq_true _
          (instDecidableAllLivePeaceful _ _) rfl
    · intro i
      revert i; decide
    · decide
    · decide
  · intro i
    revert i; decide

/--
The sole pre-owner satisfies the exact q=1 macro-stage equations.

Its payload is the q=1 source-add-one payload. The target prefix at q=1 is
the already-correct bit at b, and the negative-half latch records the q=1 bit
at b+1.
-/
private theorem q19975_stateInvariant :
    Lemma16PostEpochFreshStateInvariant
      q19975Ring q19975Cepoch 0
      q19975E2 q19975E0 .black q19975G := by
  unfold Lemma16PostEpochFreshStateInvariant
  refine And.intro ?_ ?_
  · intro i
    rfl
  · unfold Lemma16PostEpochFreshLiveInvariant
    intro i z t howner hid _hsite _hepoch _hprior
    rcases q19975_owner_shape howner with
      ⟨hi, hz⟩
    subst i
    subst z

    have ht : t = 0 := by
      change
        PPL.LineageId.born .black 0 =
          PPL.LineageId.born .black t
        at hid
      cases hid
      rfl
    subst t

    refine
      ⟨1, by decide, ?_, ?_, ?_, ?_⟩

    · unfold Lemma16FreshMacroStageAt
      dsimp only
      rw [show q19975Z.value = q19975TokenNegOne from rfl, q19975_decode_old]
      refine
        ⟨3, by decide, Or.inr ?_⟩
      refine And.intro (by omega) ?_
      refine And.intro (by decide) ?_
      refine And.intro (by omega) ?_
      decide

    · unfold PPL.payloadCorrect
      decide

    · unfold Lemma16TargetPrefix
      intro x hx
      have hx0 : x = 0 := by
        omega
      subst x
      decide

    · intro _hneg
      decide

private theorem q19975_post_owner :
    PPL.ghostTokenAt .black q19975GPost q19975E2 =
      some q19975ZPost := by
  decide

private theorem q19975_post_completed :
    q19975GPost.completed = [] := by
  decide

private theorem q19975_post_leaderless :
    forall i : Fin 4,
      (q19975GPost.phys i).leader = false := by
  decide

private theorem q19975_post_not_cpb :
    Not (PPL.CPB q19975Ring q19975GPost.phys) := by
  intro hcpb
  unfold PPL.CPB PPL.CPBCore at hcpb
  rcases hcpb.1 with ⟨i, hi⟩
  have hf := q19975_post_leaderless i
  dsimp only at hi; rw [hf] at hi
  cases hi

private theorem q19975_post_noPrior :
    Lemma16NoPriorCompletionId
      q19975GPost q19975ZPost.lmeta.id := by
  unfold Lemma16NoPriorCompletionId
  intro m hm
  rw [q19975_post_completed] at hm
  have hf : False := by
    simpa using hm
  exact hf.elim

/--
The requested selected-live row is false.

The counterexample is already lineage-coherent:
  slot kind       = black,
  ID kind         = black,
  ID timestamp    = 0,
  birthStep       = 0.
Thus adding Lemma16GhostLineageCoherent does not remove this witness.
-/
theorem
    lemma16PostEpochFreshSelectedLiveStepGeom_refuted :
    Not Lemma16PostEpochFreshSelectedLiveStepGeom := by
  intro hrow
  unfold
    Lemma16PostEpochFreshSelectedLiveStepGeom
    at hrow

  have hlocal :=
    hrow
      (n := 4) (psi := 2) (kappa := 1)
      q19975Hpsi
      (by decide : 3 <= 4)
      q19975Ring
      q19975Cepoch
      0
      q19975E2
      q19975E0
      .black
      1
      q19975G
      q19975E2
      q19975_geometry
      q19975_ready
      q19975_stateInvariant

  dsimp only at hlocal

  have hout :=
    hlocal
      q19975_post_not_cpb
      q19975E2
      q19975ZPost
      0
      (Or.inl rfl)
      q19975_post_owner
      rfl
      rfl
      (by omega)
      q19975_post_noPrior

  rcases hout with
    ⟨q, hq, hrest⟩
  have hstage := hrest.1

  unfold Lemma16FreshMacroStageAt at hstage
  dsimp only at hstage
  rw [show q19975ZPost.value = q19975TokenPost from rfl, q19975_decode_post] at hstage

  rcases hstage with
    ⟨x, _hx, hpos | hneg⟩

  · have hmoves := hpos.2.2.2
    have hmoves6 :
        q19975ZPost.lmeta.moves = 6 := by
      rfl
    rw [hmoves6] at hmoves
    change 6 = q * 3 at hmoves
    omega

  · have hc : (2 : Int) < 0 :=
      hneg.1
    omega

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshSelectedLiveStepGeom_refuted

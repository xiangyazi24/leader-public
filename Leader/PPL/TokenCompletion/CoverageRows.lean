import Leader.PPL.TokenCompletion.Coverage


namespace PPL


set_option autoImplicit false
set_option Elab.async false


/-!
# Lemma 4 coverage rows: truth audit


The literal residual `Lemma4CoverageTouchedCoverage` is false.


Its precondition `Lemma4GhostCoveredWindow` only says that a valid physical
token has *some* ghost owner.  It does not say that the owner's `value`
matches that physical token.  The literal ghost row begins with `liveShadow`,
which deletes a mismatched owner.


The closed psi=2 witness below keeps C_0 before and after edge 1 -> 2.  The
physical black token at u_2 has offset +1 and stays valid.  Its only pre ghost
owner deliberately carries offset +2.  Therefore pre coverage holds, but
`liveShadow` deletes the ghost and the post physical token is uncovered.


Consequently there can be no theorem
`lemma4CoverageTouchedCoverage_proved : Lemma4CoverageTouchedCoverage`, and
the existing `lemma4CoverageStep` cannot be closed through that false
residual.  The corrected touched-coverage row needs at least `GhostSound G`
(or the corresponding selected-color value-match premise).


The origin row is not refuted by this witness.  At the end of the file it is
split exactly into its initiator and responder endpoint rows, and the repaired
full-step interface is stated with the missing ghost-run soundness premise.
-/


/-! ## 1. Concrete mismatch-owner counterexample -/


private theorem coverageRowsHpsi : 2 <= 2 := by
  omega


private def coverageRowsRing : DirectedRing 4 :=
  ⟨by omega⟩


private def coverageRowsE0 : Fin 4 :=
  ⟨0, by omega⟩


private def coverageRowsE1 : Fin 4 :=
  ⟨1, by omega⟩


private def coverageRowsE2 : Fin 4 :=
  ⟨2, by omega⟩


private def coverageRowsE3 : Fin 4 :=
  ⟨3, by omega⟩


private def coverageRowsK : Fin 4 :=
  coverageRowsE0


private def coverageRowsPhysicalToken : TokenData 2 :=
  ((offsetOneCode 2 coverageRowsHpsi, (0 : Fin 2)),
    (0 : Fin 2))


/-- Deliberately different from the physical +1 token. -/
private def coverageRowsGhostValue : TokenData 2 :=
  ((offsetPsiCode 2 coverageRowsHpsi, (0 : Fin 2)),
    (0 : Fin 2))


private def coverageRowsBadGhostToken : GhostToken 4 2 where
  value := coverageRowsGhostValue
  lmeta :=
    { id := .initial .black coverageRowsE2
      birthSite := coverageRowsE2
      birthStep := 0
      moves := 0 }


private def coverageRowsState (i : Fin 4) : State 2 32 :=
  { leader := false
    id := false
    dist := ⟨i.val, i.isLt⟩
    last := false
    tokenB :=
      if i = coverageRowsE2 then
        some coverageRowsPhysicalToken
      else
        none
    tokenW := none
    mode := false
    clock := (0 : Fin 33)
    signalR := (0 : Fin 33)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }


private def coverageRowsC : Config 4 2 32 :=
  coverageRowsState


private def coverageRowsG : GhostConfig 4 2 32 :=
  { phys := coverageRowsC
    black := fun i =>
      if i = coverageRowsE2 then
        some coverageRowsBadGhostToken
      else
        none
    white := fun _ => none
    completed := [] }


private theorem coverageRowsFin4Cases (i : Fin 4) :
    Or
      (i = coverageRowsE0)
      (Or
        (i = coverageRowsE1)
        (Or
          (i = coverageRowsE2)
          (i = coverageRowsE3))) := by
  rcases i with ⟨v, hv⟩
  rcases v with _ | v
  · exact Or.inl rfl
  · rcases v with _ | v
    · exact Or.inr (Or.inl rfl)
    · rcases v with _ | v
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases v with _ | v
        · exact Or.inr (Or.inr (Or.inr rfl))
        · omega


private theorem coverageRowsCd :
    Cd coverageRowsRing coverageRowsK .black coverageRowsC := by
  intro x
  dsimp only
  have hx : x.val < 4 := x.isLt
  simp [coverageRowsC, coverageRowsState,
    coverageRowsRing, coverageRowsK,
    shiftRight, tokenD', coverageRowsE0, Nat.mod_eq_of_lt hx]


private theorem coverageRowsCovered :
    Lemma4GhostCoveredWindow
      coverageRowsRing coverageRowsK .black coverageRowsG := by
  intro i _hiwin hvalid
  by_cases hi : i = coverageRowsE2
  · subst i
    refine ⟨coverageRowsBadGhostToken, ?_⟩
    simp [coverageRowsG, ghostTokenAt]
  · have htok :
        tokenAt .black (coverageRowsG.phys i) = none := by
      simp [coverageRowsG, coverageRowsC,
        coverageRowsState, tokenAt, hi]
    unfold ValidToken at hvalid
    rw [htok] at hvalid
    exact False.elim hvalid


private theorem coverageRowsRightNeighbor :
    coverageRowsRing.rightNeighbor coverageRowsE1 =
      coverageRowsE2 := by
  decide


private theorem coverageRowsE2InWindow :
    Lemma4InWindow
      coverageRowsRing coverageRowsK 2 coverageRowsE2 := by
  refine ⟨(2 : Fin 4), ?_⟩
  decide


/--
The literal full physical step keeps the canonical C_0 dist/last geometry.
This is a closed finite computation; clock/hits may change, but C_d does not
mention them.
-/
private theorem coverageRowsCdPost :
    Cd coverageRowsRing coverageRowsK .black
      (ghostStep coverageRowsHpsi coverageRowsRing 0
        coverageRowsG coverageRowsE1).phys := by
  intro x
  rcases coverageRowsFin4Cases x with
    hx | hx | hx | hx
  · subst x
    set_option maxHeartbeats 8000000 in
      decide
  · subst x
    set_option maxHeartbeats 8000000 in
      decide
  · subst x
    set_option maxHeartbeats 8000000 in
      decide
  · subst x
    set_option maxHeartbeats 8000000 in
      decide


/-- The physical +1 token at u_2 survives and remains Definition-3 valid. -/
private theorem coverageRowsPostValid :
    ValidToken .black
      (ghostStep coverageRowsHpsi coverageRowsRing 0
        coverageRowsG coverageRowsE1).phys
      coverageRowsE2 := by
  set_option maxHeartbeats 8000000 in
    decide


/--
The mismatched offset-+2 owner is deleted by liveShadow, while no replacement
black owner is born on edge u_1 -> u_2.
-/
private theorem coverageRowsPostOwnerNone :
    ghostTokenAt .black
        (ghostStep coverageRowsHpsi coverageRowsRing 0
          coverageRowsG coverageRowsE1)
        coverageRowsE2 =
      none := by
  set_option maxHeartbeats 8000000 in
    decide


theorem lemma4CoverageTouchedCoverage_false :
    ¬ Lemma4CoverageTouchedCoverage := by
  intro hrow
  have howner :=
    hrow
      (n := 4) (psi := 2) (kappa := 32)
      coverageRowsHpsi
      coverageRowsRing
      coverageRowsK
      .black
      0
      coverageRowsG
      coverageRowsE1
      coverageRowsE2
      coverageRowsCd
      coverageRowsCdPost
      coverageRowsCovered
      (Or.inr coverageRowsRightNeighbor.symm)
      coverageRowsE2InWindow
      coverageRowsPostValid
  rcases howner with ⟨z, hz⟩
  rw [coverageRowsPostOwnerNone] at hz
  cases hz


/-! ## 2. Corrected coverage residual -/


/--
The missing premise in the false residual.  GhostSound supplies both
selected-color value agreement and local validity for every live owner.
-/
def Lemma4CoverageTouchedCoverageSound : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n),
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    GhostSound G ->
    Or (i = e) (i = ring.rightNeighbor e) ->
    Lemma4InWindow ring k psi i ->
    ValidToken kind
      (ghostStep hpsi ring step G e).phys i ->
    exists z : GhostToken n psi,
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      some z


/--
Exact run-level producer needed to obtain the new GhostSound premise from the
actual `G = ghostRun ... (initialGhost C0) pre` hypothesis in
Lemma4CoverageStep.
-/
def Lemma4CoverageGhostRunSound : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n),
    GhostSound
      (ghostRun hpsi ring 0 (initialGhost C0) pre)


/-! ## 3. Exact endpoint split of the still-unrefuted origin row -/


def Lemma4CoverageOriginInitiatorRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys ->
    Lemma4InWindow ring k psi e ->
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) e =
      some z ->
    Or
      (FreshAt kind k z.lmeta)
      (exists j z0,
        And
          (Lemma4InWindow ring k psi j)
          (And
            (ghostTokenAt kind G j = some z0)
            (z.lmeta.id = z0.lmeta.id)))


def Lemma4CoverageOriginResponderRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys ->
    Lemma4InWindow ring k psi
      (ring.rightNeighbor e) ->
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (ring.rightNeighbor e) =
      some z ->
    Or
      (FreshAt kind k z.lmeta)
      (exists j z0,
        And
          (Lemma4InWindow ring k psi j)
          (And
            (ghostTokenAt kind G j = some z0)
            (z.lmeta.id = z0.lmeta.id)))


theorem lemma4CoverageTouchedOrigin_of_endpoint_rows
    (hleft : Lemma4CoverageOriginInitiatorRow)
    (hright : Lemma4CoverageOriginResponderRow) :
    Lemma4CoverageTouchedOrigin := by
  intro n psi kappa hpsi ring k kind step G e i z
  intro hCd hCd' htouched hiwin howner
  rcases htouched with hie | hir
  · subst i
    exact
      hleft hpsi ring k kind step G e z
        hCd hCd' hiwin howner
  · subst i
    exact
      hright hpsi ring k kind step G e z
        hCd hCd' hiwin howner


/-! ## 4. Untouched facts and repaired full-step assembly -/


private theorem coverageRowsGhostStepPhysOther
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    (ghostStep hpsi ring step G e).phys i =
      G.phys i := by
  change
    (if i = e then _
      else if i = ring.rightNeighbor e then _
      else G.phys i) =
      G.phys i
  rw [if_neg hie, if_neg hir]


private theorem coverageRowsGhostStepOwnerOther
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (kind : TokenKind)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      ghostTokenAt kind G i := by
  cases kind with
  | black =>
      change
        (if i = e then _
          else if i = ring.rightNeighbor e then _
          else G.black i) =
        G.black i
      rw [if_neg hie, if_neg hir]
  | white =>
      change
        (if i = e then _
          else if i = ring.rightNeighbor e then _
          else G.white i) =
        G.white i
      rw [if_neg hie, if_neg hir]


/-! Copy of the private initial-ownership mirror from TokenCorrectnessLemma4Coverage
(upstream is accepted and not appended to). -/

private def rowsCopyLocalValid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  Or
    (And (0 < c)
      (And (((psi : Nat) : Int) <= target)
        (target <= (((2 * psi - 1 : Nat)) : Int))))
    (And (c < 0)
      (And (1 <= target)
        (target <= (((psi - 1 : Nat)) : Int))))

private instance instDecidableRowsCopyLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (rowsCopyLocalValid kind q t) := by
  unfold rowsCopyLocalValid
  infer_instance

private noncomputable def rowsCopyInitialOwned
    {n psi kappa : Nat}
    (kind : TokenKind) (C : Config n psi kappa)
    (i : Fin n) : Option (GhostToken n psi) := by
  classical
  exact
    match tokenAt kind (C i) with
    | none => none
    | some t =>
        if rowsCopyLocalValid kind (C i) t then
          some
            { value := t
              lmeta :=
                { id := .initial kind i
                  birthSite := i
                  birthStep := 0
                  moves := 0 } }
        else
          none

private theorem rowsCopy_ghostTokenAt_initial
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (kind : TokenKind) (i : Fin n) :
    ghostTokenAt kind (initialGhost C) i =
      rowsCopyInitialOwned kind C i := by
  cases kind <;> rfl

private theorem rowsCopyInitialGhostCovered
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (C : Config n psi kappa) :
    Lemma4GhostCoveredWindow ring k kind (initialGhost C) := by
  classical
  intro i _hwin hvalid
  change ValidToken kind C i at hvalid
  unfold ValidToken at hvalid
  cases ht : tokenAt kind (C i) with
  | none =>
      rw [ht] at hvalid
      exact False.elim hvalid
  | some t =>
      rw [ht] at hvalid
      dsimp only at hvalid
      have hlocal :
          rowsCopyLocalValid kind (C i) t := by
        exact hvalid
      let z : GhostToken n psi :=
        { value := t
          lmeta :=
            { id := .initial kind i
              birthSite := i
              birthStep := 0
              moves := 0 } }
      refine ⟨z, ?_⟩
      rw [rowsCopy_ghostTokenAt_initial]
      simp [rowsCopyInitialOwned, ht, hlocal, z]

/--
This is the sound replacement for the old assembly interface.  It uses the
actual ghost-run premise to obtain GhostSound, then uses the corrected touched
coverage row.  The origin row is unchanged.
-/
theorem lemma4CoverageStep_of_sound_rows
    (hrunSound : Lemma4CoverageGhostRunSound)
    (htouched : Lemma4CoverageTouchedCoverageSound)
    (horigin : Lemma4CoverageTouchedOrigin) :
    Lemma4CoverageStep := by
  intro n psi kappa hpsi ring k kind
  constructor
  · intro C _hCd
    exact rowsCopyInitialGhostCovered ring k kind C
  · intro C0 pre G e hrun
    intro hCd hCd' hcovered
    have hsound : GhostSound G := by
      rw [hrun]
      exact hrunSound hpsi ring C0 pre
    dsimp only
    constructor
    · intro i hiwin hvalid
      by_cases hie : i = e
      · exact
          htouched
            hpsi ring k kind pre.length
            G e i hCd hCd' hcovered hsound
            (Or.inl hie) hiwin hvalid
      · by_cases hir :
          i = ring.rightNeighbor e
        · exact
            htouched
              hpsi ring k kind pre.length
              G e i hCd hCd' hcovered hsound
              (Or.inr hir) hiwin hvalid
        · have hphys :=
            coverageRowsGhostStepPhysOther
              hpsi ring pre.length G e i
              hie hir
          have hvalid0 :
              ValidToken kind G.phys i := by
            unfold ValidToken at hvalid ⊢
            rw [hphys] at hvalid
            exact hvalid
          obtain ⟨z, hz⟩ :=
            hcovered i hiwin hvalid0
          refine ⟨z, ?_⟩
          rw [
            coverageRowsGhostStepOwnerOther
              hpsi ring pre.length
              G e i kind hie hir]
          exact hz
    · intro i z hiwin howner
      by_cases hie : i = e
      · exact
          horigin
            hpsi ring k kind pre.length
            G e i z hCd hCd'
            (Or.inl hie) hiwin howner
      · by_cases hir :
          i = ring.rightNeighbor e
        · exact
            horigin
              hpsi ring k kind pre.length
              G e i z hCd hCd'
              (Or.inr hir) hiwin howner
        · have howner0 :
              ghostTokenAt kind G i = some z := by
            rw [
              ← coverageRowsGhostStepOwnerOther
                hpsi ring pre.length
                G e i kind hie hir]
            exact howner
          exact
            Or.inr
              ⟨i, z, hiwin, howner0, rfl⟩


/--
If the two exact endpoint-origin rows are discharged, this is the corrected
remaining interface.  It deliberately does not manufacture the false
Lemma4CoverageTouchedCoverage premise.
-/
theorem lemma4CoverageStep_of_repaired_endpoint_rows
    (hrunSound : Lemma4CoverageGhostRunSound)
    (htouched : Lemma4CoverageTouchedCoverageSound)
    (hleft : Lemma4CoverageOriginInitiatorRow)
    (hright : Lemma4CoverageOriginResponderRow) :
    Lemma4CoverageStep :=
  lemma4CoverageStep_of_sound_rows
    hrunSound htouched
    (lemma4CoverageTouchedOrigin_of_endpoint_rows
      hleft hright)


end PPL


#print axioms PPL.lemma4CoverageTouchedCoverage_false
#print axioms PPL.lemma4CoverageTouchedOrigin_of_endpoint_rows
#print axioms PPL.lemma4CoverageStep_of_sound_rows
#print axioms PPL.lemma4CoverageStep_of_repaired_endpoint_rows

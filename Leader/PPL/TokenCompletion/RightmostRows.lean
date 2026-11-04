import Leader.PPL.TokenCompletion.Rightmost


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
# Lemma 4 rightmost rows: bounded local reduction


Truth audit against the literal selected-colour row:


* `Lemma4RightmostInteractedRow` is true. If the tracked rightmost owner
  is the responder, a collision deletes the left contender. If it is the
  initiator, a live selected-colour responder to its right would, by
  ghost coverage, already have an owner and contradict rightmostness.
* `Lemma4RightmostNoOvertakeOffPair` is true. Away from the selected
  pair the tracked owner and its physical state are unchanged. A new
  owner to its right can therefore only occur at one of the two selected
  endpoints; the literal selected-colour row rules that out by C_d,
  coverage, and the same collision/birth ordering.


The public files still hide the selected-colour `ghostMoveToken` value row.
Within this bounded round the global bookkeeping is closed below and the
remaining work is isolated as three strictly local branch Props:


* initiator-owned interacted pair;
* responder-owned interacted pair;
* endpoint creation/overtake on an otherwise off-pair interaction.


None of the three residuals contains a schedule induction or probability
statement. They are exactly one selected-colour Algorithm-3 row.
-/


private def rightmostRowsOutcome
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi) : Prop :=
  let i := shiftRight ring k x.val
  let G' := ghostStep hpsi ring pre.length G e
  Or
    (And
      (Not (FreshAt kind k z.lmeta))
      (forall j z',
        ghostTokenAt kind G' j = some z' ->
        z'.lmeta.id ≠ z.lmeta.id))
    (Or
      (HasFreshCompletion kind k G')
      (Exists fun y : Fin (2 * psi) =>
        Exists fun z' : GhostToken n psi =>
          And
            (Lemma4RightmostAt ring k kind G' y z')
            (And
              (z'.lmeta.id = z.lmeta.id)
              (And
                (FreshAt kind k z.lmeta ->
                  FreshAt kind k z'.lmeta)
                (And
                  (lemma4TokenProgress
                      kind (G.phys i) z.value <=
                    lemma4TokenProgress
                      kind
                      (G'.phys
                        (shiftRight ring k y.val))
                      z'.value)
                  (e =
                      lemma4ServiceEdge
                        ring kind G i z ->
                    lemma4TokenProgress
                        kind
                        (G'.phys
                          (shiftRight ring k y.val))
                        z'.value =
                      lemma4TokenProgress
                        kind (G.phys i) z.value +
                        1))))))


def Lemma4RightmostInitiatorBranch : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    G =
        ghostRun hpsi ring 0
          (initialGhost C0) pre ->
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring pre.length G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    Lemma4RightmostAt ring k kind G x z ->
    e = shiftRight ring k x.val ->
    rightmostRowsOutcome
      hpsi ring k kind pre G e x z


def Lemma4RightmostResponderBranch : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    G =
        ghostRun hpsi ring 0
          (initialGhost C0) pre ->
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring pre.length G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    Lemma4RightmostAt ring k kind G x z ->
    ring.rightNeighbor e =
      shiftRight ring k x.val ->
    rightmostRowsOutcome
      hpsi ring k kind pre G e x z


def Lemma4RightmostOffPairEndpointNoOvertake : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    G =
        ghostRun hpsi ring 0
          (initialGhost C0) pre ->
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring pre.length G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    Lemma4RightmostAt ring k kind G x z ->
    e ≠ shiftRight ring k x.val ->
    ring.rightNeighbor e ≠
      shiftRight ring k x.val ->
    forall y : Fin (2 * psi),
      x.val < y.val ->
      Or
          (shiftRight ring k y.val = e)
          (shiftRight ring k y.val =
            ring.rightNeighbor e) ->
      ghostTokenAt kind
          (ghostStep hpsi ring pre.length G e)
          (shiftRight ring k y.val) =
        none


private theorem rightmostRowsGhostOffPair
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
      simp [hie, hir]
  | white =>
      change
        (if i = e then _
          else if i = ring.rightNeighbor e then _
          else G.white i) =
        G.white i
      simp [hie, hir]


private theorem rightmostRowsPhysOffPair
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
    PopulationProtocol.step
        (protocol psi kappa)
        ring G.phys e i =
      G.phys i
  simp [PopulationProtocol.step, hie, hir]


theorem lemma4RightmostInteractedRow_proved
    (hInitiator : Lemma4RightmostInitiatorBranch)
    (hResponder : Lemma4RightmostResponderBranch) :
    Lemma4RightmostInteractedRow := by
  unfold Lemma4RightmostInteractedRow
  intro n psi kappa hpsi
  intro ring k kind C0 pre G e x z
  intro hrun hCd hCd' hcover hright
  dsimp only
  intro hinteract
  change
    rightmostRowsOutcome
      hpsi ring k kind pre G e x z
  rcases hinteract with he | hr
  · exact
      hInitiator
        hpsi ring k kind C0 pre G e x z
        hrun hCd hCd' hcover hright he
  · exact
      hResponder
        hpsi ring k kind C0 pre G e x z
        hrun hCd hCd' hcover hright hr


theorem lemma4RightmostNoOvertakeOffPair_proved
    (hEndpoint :
      Lemma4RightmostOffPairEndpointNoOvertake) :
    Lemma4RightmostNoOvertakeOffPair := by
  unfold Lemma4RightmostNoOvertakeOffPair
  intro n psi kappa hpsi
  intro ring k kind C0 pre G e x z
  intro hrun hCd hCd' hcover hright
  dsimp only
  intro hie hir


  let i : Fin n :=
    shiftRight ring k x.val
  let G' : GhostConfig n psi kappa :=
    ghostStep hpsi ring pre.length G e


  change
    And
      (ghostTokenAt kind G' i = some z)
      (And
        (ValidToken kind G'.phys i)
        (forall y : Fin (2 * psi),
          x.val < y.val ->
          ghostTokenAt kind G'
              (shiftRight ring k y.val) =
            none))


  have hright' :
      And
        (ghostTokenAt kind G i = some z)
        (And
          (ValidToken kind G.phys i)
          (forall y : Fin (2 * psi),
            x.val < y.val ->
            ghostTokenAt kind G
                (shiftRight ring k y.val) =
              none)) := by
    simpa [i, Lemma4RightmostAt] using hright


  have howner :
      ghostTokenAt kind G' i = some z := by
    have hs :=
      rightmostRowsGhostOffPair
        hpsi ring pre.length G e i kind
        (fun hq => hie (by simpa [i] using hq.symm))
        (fun hq => hir (by simpa [i] using hq.symm))
    rw [hs]
    exact hright'.1


  have hstate :
      G'.phys i = G.phys i := by
    exact
      rightmostRowsPhysOffPair
        hpsi ring pre.length G e i
        (fun hq => hie (by simpa [i] using hq.symm))
        (fun hq => hir (by simpa [i] using hq.symm))


  have hvalid :
      ValidToken kind G'.phys i := by
    unfold ValidToken at hright' ⊢
    rw [hstate]
    exact hright'.2.1


  refine And.intro howner
    (And.intro hvalid ?_)
  intro y hxy


  let j : Fin n :=
    shiftRight ring k y.val


  by_cases hje : j = e
  · exact
      hEndpoint
        hpsi ring k kind C0 pre G e x z
        hrun hCd hCd' hcover hright
        hie hir y hxy (Or.inl hje)


  · by_cases hjr :
      j = ring.rightNeighbor e
    · exact
        hEndpoint
          hpsi ring k kind C0 pre G e x z
          hrun hCd hCd' hcover hright
          hie hir y hxy (Or.inr hjr)


    · have hs :=
        rightmostRowsGhostOffPair
          hpsi ring pre.length G e j kind
          hje hjr
      change
        ghostTokenAt kind G' j = none
      rw [hs]
      exact hright'.2.2 y hxy


theorem lemma4RightmostProgressStep_closed
    (hInitiator : Lemma4RightmostInitiatorBranch)
    (hResponder : Lemma4RightmostResponderBranch)
    (hEndpoint :
      Lemma4RightmostOffPairEndpointNoOvertake) :
    Lemma4RightmostProgressStep :=
  lemma4RightmostProgressStep
    (lemma4RightmostInteractedRow_proved
      hInitiator hResponder)
    (lemma4RightmostNoOvertakeOffPair_proved
      hEndpoint)


end PPL


#print axioms PPL.lemma4RightmostInteractedRow_proved
#print axioms PPL.lemma4RightmostNoOvertakeOffPair_proved
#print axioms PPL.lemma4RightmostProgressStep_closed



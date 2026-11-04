import Leader.PPL.TokenCorrectness.PersistenceFrame


namespace PPL


set_option autoImplicit false
set_option Elab.async false


/-!
# Remark 2 interacted-pair row


Truth audit against the literal selected-colour Algorithm-3 row at dd22a24b.


There are exactly four old-owner/new-owner placements on the interacting pair.


1. old=e, new=e:
   the tracked initiator survives in place.  No bump can return an initiator
   lineage to the initiator in the same selected-colour row, so this is the
   unchanged/stay case.


2. old=e, new=rightNeighbor e:
   this is the positive direction.  A surviving tracked lineage is either
   the c >= 2 ordinary move or the c = 1 turn.  The turn may write the
   responder identifier, but sourceIota equality is an explicit premise.


3. old=rightNeighbor e, new=e:
   this is the negative direction.  A surviving tracked lineage is either
   the c <= -2 ordinary move or the c = -1 turn.  The c = -1 branch is
   exactly the exceptional branch already exposed by Remark2SurvivorFrame.


4. old=rightNeighbor e, new=rightNeighbor e:
   the tracked responder survives in place.


Collision/fresh-birth audit:
* if the tracked lineage starts at e, a same-colour collision deletes that
  left lineage, so there is no same-ID post survivor to consider;
* if the tracked lineage starts at the responder, the left contender is the
  one deleted, after which the tracked responder follows the negative row;
* a tracked token at e blocks a fresh birth there because the birth guard
  requires an empty selected-colour slot;
* when the tracked token is at the responder, a fresh left birth has the new
  id .born kind step and cannot alias the tracked old id because
  GhostIdsBefore step G is part of GhostIdsUniqueAt.


Hence Remark2InteractedPairRow is TRUE.  The only remaining low-level work is
the two directional selected-token rows below.  All non-selected fields and
the c = -1 semantic arithmetic are already public.
-/


/-! ## Public TransitionFacts/carry adapters -/


theorem remark2Row_moveToken_initiator_fields
    {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (l r : State psi kappa) :
    eraseKindToken kind (moveToken hpsi kind l r).1 =
      eraseKindToken kind l := by
  exact moveToken_initiator_fields hpsi kind l r


theorem remark2Row_moveToken_responder_fields
    {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (l r : State psi kappa) :
    Or
      (eraseKindTokenId kind (moveToken hpsi kind l r).2 =
        eraseKindTokenId kind r)
      (eraseKindTokenId kind (moveToken hpsi kind l r).2 =
        eraseKindTokenId kind (birthFields r)) := by
  exact moveToken_responder_fields hpsi kind l r


theorem remark2Row_moveToken_view4_cases
    {psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (l r : State psi kappa) :
    And
      (PPL.Elim.view4 (moveToken hpsi kind l r).1 =
        PPL.Elim.view4 l)
      (Or
        (PPL.Elim.view4 (moveToken hpsi kind l r).2 =
          PPL.Elim.view4 r)
        (PPL.Elim.view4 (moveToken hpsi kind l r).2 =
          (⟨true, (2 : Fin 3), true, false⟩ :
            PPL.Elim.Cell4))) := by
  exact moveToken_view4_cases hpsi kind l r


/-- The exceptional left-turn row is already semantically closed.
This adapter is useful when the literal selected-row split exposes
the c = -1 certificate. -/
theorem remark2Row_negTurn_correct
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (e i : Fin n) (kind : TokenKind)
    (t : TokenData psi)
    (hstep :
      C' =
        PopulationProtocol.step
          (protocol psi kappa) ring C e)
    (hri : ring.rightNeighbor e = i)
    (htok : tokenAt kind (C i) = some t)
    (hcneg :
      decodeOffset psi (tokenCode t) = -1)
    (hpost :
      tokenAt kind (C' e) =
        some
          (remark2NegTurnValue
            hpsi (C e).id t))
    (hvalid : ValidToken kind C i)
    (hwork :
      WorkingFor ring root C i kind seg.val)
    (hcorr :
      CorrectToken ring root C i kind seg.val)
    (hC : CDLAt ring root C)
    (hC' : CDLAt ring root C')
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val) :
    CorrectToken ring root C' e kind seg.val := by
  exact
    remark2NegTurnCarry_proved
      hpsi ring root seg
      C C' e i kind t
      hstep hri htok hcneg hpost
      hvalid hwork hcorr hC hC' hsrc


/-! ## Two remaining selected-token rows


These are deliberately directional.  They start after the public
moveToken_view4_cases split has ruled out hidden non-token writes.


The right row contains:
* initiator stay;
* c >= 2 ordinary right move;
* c = 1 right turn;
* impossible collision/fresh-alias branches.


The left row contains:
* responder stay;
* c <= -2 ordinary left move;
* c = -1 exceptional turn;
* the collision case where the left contender is deleted and the tracked
  responder continues through the negative row.
-/


def Remark2RightSelectedRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (step : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (z : GhostToken n psi),
    G.phys = C ->
    GhostSound G ->
    GhostIdsUniqueAt step G ->
    ghostTokenAt kind G e = some z ->
    ValidToken kind C e ->
    WorkingFor ring root C e kind seg.val ->
    CorrectToken ring root C e kind seg.val ->
    CDLAt ring root C ->
    CDLAt ring root
      (PopulationProtocol.step
        (protocol psi kappa) ring C e) ->
    forall (j : Fin n) (z' : GhostToken n psi),
      sourceIota ring root C seg.val =
        sourceIota ring root
          (PopulationProtocol.step
            (protocol psi kappa) ring C e)
          seg.val ->
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) j =
          some z' ->
      z'.lmeta.id = z.lmeta.id ->
      Or (j = e) (j = ring.rightNeighbor e) ->
      CorrectToken ring root
        (PopulationProtocol.step
          (protocol psi kappa) ring C e)
        j kind seg.val


def Remark2LeftSelectedRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (step : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (z : GhostToken n psi),
    G.phys = C ->
    GhostSound G ->
    GhostIdsUniqueAt step G ->
    ghostTokenAt kind G (ring.rightNeighbor e) =
      some z ->
    ValidToken kind C (ring.rightNeighbor e) ->
    WorkingFor ring root C
      (ring.rightNeighbor e) kind seg.val ->
    CorrectToken ring root C
      (ring.rightNeighbor e) kind seg.val ->
    CDLAt ring root C ->
    CDLAt ring root
      (PopulationProtocol.step
        (protocol psi kappa) ring C e) ->
    forall (j : Fin n) (z' : GhostToken n psi),
      sourceIota ring root C seg.val =
        sourceIota ring root
          (PopulationProtocol.step
            (protocol psi kappa) ring C e)
          seg.val ->
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) j =
          some z' ->
      z'.lmeta.id = z.lmeta.id ->
      Or (j = e) (j = ring.rightNeighbor e) ->
      Or
        (CorrectToken ring root
          (PopulationProtocol.step
            (protocol psi kappa) ring C e)
          j kind seg.val)
        (And (j = e)
          (And
            (tokenAt kind
              (C (ring.rightNeighbor e)) =
                some z.value)
            (And
              (decodeOffset psi
                (tokenCode z.value) = -1)
              (And
                (tokenAt kind
                  ((PopulationProtocol.step
                    (protocol psi kappa)
                    ring C e) e) =
                      some z'.value)
                (z'.value =
                  remark2NegTurnValue
                    hpsi (C e).id
                    z.value)))))


/-! ## Four-placement assembly -/


section DirectionRows




/-- Once the two directional selected-token rows are supplied, the exact
interacted-pair residual closes by the four possible placements. -/
theorem remark2InteractedPairRow
    (hRight : Remark2RightSelectedRow)
    (hLeft : Remark2LeftSelectedRow) :
    Remark2InteractedPairRow := by
  unfold Remark2InteractedPairRow
  intro n psi kappa hpsi hn3
  intro ring root seg step C e G kind i z
  intro hphys hG huniq howner
  intro hvalid hwork hcorr hC hC'
  intro j z' hsrc hpost hid hi hj


  rcases hi with hie | hir
  · subst i
    exact
      Or.inl
        (hRight hpsi hn3 ring root seg
          step C e G kind z
          hphys hG huniq howner
          hvalid hwork hcorr hC hC'
          j z' hsrc hpost hid hj)


  · subst i
    have hshape :=
      hLeft hpsi hn3 ring root seg
        step C e G kind z
        hphys hG huniq howner
        hvalid hwork hcorr hC hC'
        j z' hsrc hpost hid hj
    rcases hshape with hcorrect | hneg
    · exact Or.inl hcorrect
    · rcases hneg with
        ⟨hje, htok0, hcneg, htok1, hzval⟩
      exact
        Or.inr
          ⟨hje, rfl, htok0,
            hcneg, htok1, hzval⟩


/-- Plus the closed line-29 carry then gives the repaired one-step
Remark 2 theorem. -/
theorem remark2_one_step_unique_closed
    (hRight : Remark2RightSelectedRow)
    (hLeft : Remark2LeftSelectedRow) :
    remark2_one_step_unique :=
  remark2_one_step_unique_proved
    (remark2InteractedPairRow hRight hLeft)


end DirectionRows


#print axioms PPL.remark2Row_moveToken_view4_cases
#print axioms PPL.remark2Row_negTurn_correct
#print axioms PPL.remark2InteractedPairRow
#print axioms PPL.remark2_one_step_unique_closed


end PPL

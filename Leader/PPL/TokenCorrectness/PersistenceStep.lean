import Leader.PPL.TokenCorrectness.Persistence
import Leader.PPL.TransitionFacts

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-!
# Remark 2 one-step assembly

The carry recurrence at Algorithm 3 line 29 is isolated as
Remark2NegTurnCarry.

One further local fact is exposed as Remark2SurvivorFrame.  This is not a new
paper hypothesis: it is the selected-token/provenance frame left implicit by
the public TransitionFacts interface.  Those field theorems intentionally
erase the selected token (and, on the responder, the identifier), so they do
not themselves identify the post-step value of a surviving tracked lineage.

Remark2SurvivorFrame is exactly the six-case split:
* off-pair unchanged;
* same-site survivor;
* ordinary positive move;
* c = 1 positive turn;
* ordinary negative move;
* c = -1 negative turn.

All cases except the last already conclude CorrectToken.  The last exposes the
literal line-29 value, which Remark2NegTurnCarry discharges.
-/

private def remark2BitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def remark2MkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

/-- The literal value written by Algorithm 3 line 29.
The source bit is the initiator identifier read by that line. -/
def remark2NegTurnValue {psi : Nat}
    (hpsi : 2 <= psi) (sourceBit : Bool)
    (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    remark2MkToken (offsetPsiCode psi hpsi)
      (remark2BitToFin (!sourceBit))
      (remark2BitToFin sourceBit)
  else
    remark2MkToken (offsetPsiCode psi hpsi)
      (remark2BitToFin sourceBit) (0 : Fin 2)

/--
The single semantic microlemma for the c = -1 return turn.

The old selected-color token is at the responder i = rightNeighbor e and has
offset -1.  The post configuration contains at e exactly the value written by
line 29.  Under rooted C_DL before and after, unchanged sourceIota, and the
usual valid/working/correct premises, that new occurrence is CorrectToken for
the same interior segment.
-/
def Remark2NegTurnCarry : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (e i : Fin n) (kind : TokenKind)
    (t : TokenData psi),
    C' = PopulationProtocol.step (protocol psi kappa) ring C e ->
    ring.rightNeighbor e = i ->
    tokenAt kind (C i) = some t ->
    decodeOffset psi (tokenCode t) = -1 ->
    tokenAt kind (C' e) =
      some (remark2NegTurnValue hpsi (C e).id t) ->
    ValidToken kind C i ->
    WorkingFor ring root C i kind seg.val ->
    CorrectToken ring root C i kind seg.val ->
    CDLAt ring root C ->
    CDLAt ring root C' ->
    sourceIota ring root C seg.val =
      sourceIota ring root C' seg.val ->
    CorrectToken ring root C' e kind seg.val

/--
The remaining mechanical selected-lineage frame.

Assume the source segment did not change and choose any post-step live owner
with the tracked pre-step lineage ID.  Uniqueness/freshness plus the literal
MoveToken rows imply exactly one of two outcomes:

1. this survivor is already a CorrectToken for the same segment; or
2. it is precisely the c = -1 responder-to-initiator turn, with the literal
   line-29 value exposed.

The intended proof is the six-case split.  GhostIdsUnique excludes a
different old owner; GhostIdsBefore excludes a same-step fresh birth alias.
moveToken_initiator_fields, moveToken_responder_fields, and
moveToken_view4_cases provide the non-selected field frames.  The selected
token-value row is obtained by the definitionally mirrored r2 move in
TokenCorrectnessRemark2.
-/
def Remark2SurvivorFrame : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (step : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (G : GhostConfig n psi kappa) (kind : TokenKind)
    (i : Fin n) (z : GhostToken n psi),
    G.phys = C ->
    GhostSound G ->
    GhostIdsUniqueAt step G ->
    ghostTokenAt kind G i = some z ->
    ValidToken kind C i ->
    WorkingFor ring root C i kind seg.val ->
    CorrectToken ring root C i kind seg.val ->
    CDLAt ring root C ->
    CDLAt ring root
      (PopulationProtocol.step (protocol psi kappa) ring C e) ->
    forall (j : Fin n) (z' : GhostToken n psi),
      sourceIota ring root C seg.val =
          sourceIota ring root
            (PopulationProtocol.step
              (protocol psi kappa) ring C e) seg.val ->
      ghostTokenAt kind
          (ghostStep hpsi ring step G e) j = some z' ->
      z'.lmeta.id = z.lmeta.id ->
      CorrectToken ring root
          (PopulationProtocol.step
            (protocol psi kappa) ring C e)
          j kind seg.val \/
        (j = e /\
          ring.rightNeighbor e = i /\
          tokenAt kind (C i) = some z.value /\
          decodeOffset psi (tokenCode z.value) = -1 /\
          tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa) ring C e) e) =
            some z'.value /\
          z'.value =
            remark2NegTurnValue hpsi (C e).id z.value)

private theorem remark2GhostStepPhys
    {n psi kappa : Nat}
    (hpsi : 2 <= psi) (ring : DirectedRing n)
    (step : Nat) (G : GhostConfig n psi kappa)
    (e : Fin n) :
    (ghostStep hpsi ring step G e).phys =
      PopulationProtocol.step
        (protocol psi kappa) ring G.phys e := by
  rfl

/--
Assembly of the repaired Remark 2 from the carry microlemma plus the one
mechanical survivor frame.

The second premise is the only additional named Prop needed in this bounded
round.  In particular no extra correctness law, probability law, or protocol
invariant is introduced.
-/
theorem remark2_one_step_unique_of_negTurn
    (hturn : Remark2NegTurnCarry)
    (hframe : Remark2SurvivorFrame) :
    remark2_one_step_unique := by
  unfold remark2_one_step_unique
  intro n psi kappa hpsi hn3
  intro ring root seg step C e G kind i z
  intro hphys hG huniq howner hvalid hwork hcorr hC hC'

  dsimp only

  by_cases hsource :
      sourceIota ring root C seg.val ≠
        sourceIota ring root
          (PopulationProtocol.step
            (protocol psi kappa) ring C e) seg.val
  · exact Or.inl hsource
  · right
    have hsrc :
        sourceIota ring root C seg.val =
          sourceIota ring root
            (PopulationProtocol.step
              (protocol psi kappa) ring C e) seg.val := by
      exact Classical.not_not.mp hsource

    by_cases hdeleted :
        LineageDeleted kind z.lmeta.id
          (ghostStep hpsi ring step G e)
    · exact Or.inl hdeleted
    · right

      have hlive :
          LiveLineage kind z.lmeta.id
            (ghostStep hpsi ring step G e) := by
        unfold LineageDeleted at hdeleted
        exact Classical.not_not.mp hdeleted

      rcases hlive with ⟨j, z', hpost, hid⟩

      have hshape :=
        hframe hpsi hn3 ring root seg step C e G kind i z
          hphys hG huniq howner hvalid hwork hcorr hC hC'
          j z' hsrc hpost hid

      rcases hshape with hcorrect | hneg
      · unfold CorrectDescendant
        refine ⟨j, z', hpost, hid, ?_⟩
        rw [remark2GhostStepPhys hpsi ring step G e, hphys]
        exact hcorrect

      · rcases hneg with
          ⟨hje, hri, htok0, hcneg, htok1, hzval⟩
        subst j

        have htok1' :
            tokenAt kind
                ((PopulationProtocol.step
                  (protocol psi kappa) ring C e) e) =
              some
                (remark2NegTurnValue
                  hpsi (C e).id z.value) := by
          rw [← hzval]
          exact htok1

        have hcorrectTurn :
            CorrectToken ring root
              (PopulationProtocol.step
                (protocol psi kappa) ring C e)
              e kind seg.val := by
          exact
            hturn hpsi ring root seg
              C
              (PopulationProtocol.step
                (protocol psi kappa) ring C e)
              e i kind z.value
              rfl hri htok0 hcneg htok1'
              hvalid hwork hcorr hC hC' hsrc

        unfold CorrectDescendant
        refine ⟨e, z', hpost, hid, ?_⟩
        rw [remark2GhostStepPhys hpsi ring step G e, hphys]
        exact hcorrectTurn

end PPL

#print axioms PPL.remark2_one_step_unique_of_negTurn

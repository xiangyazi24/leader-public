import Leader.PPL.TokenCorrectness.PersistencePairRow

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-!
# Remark 2 left selected row

Truth audit.

For an old selected-colour owner at the responder, a same-colour collision
deletes the left contender (Algorithm 3 lines 16--17), not the responder.
After that deletion the tracked responder either stays, takes the ordinary
c <= -2 left move, or takes the c = -1 turn.  A fresh left birth has id
.born kind step; GhostIdsBefore, contained in GhostIdsUniqueAt, prevents it
from aliasing the tracked old lineage.  Thus the target Prop is true.

This bounded file closes the semantic transport and isolates only the literal
selected-shadow shape as Remark2LeftSelectedShape.
-/

/-! ## Public TransitionFacts package -/

/-- The three public MoveToken projections needed for the remaining literal
shadow-row split. -/
theorem remark2LeftSelected_physicalFacts
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    And
      (eraseKindToken kind
          (moveToken hpsi kind l r).1 =
        eraseKindToken kind l)
      (And
        (Or
          (eraseKindTokenId kind
              (moveToken hpsi kind l r).2 =
            eraseKindTokenId kind r)
          (eraseKindTokenId kind
              (moveToken hpsi kind l r).2 =
            eraseKindTokenId kind (birthFields r)))
        (And
          (PPL.Elim.view4
              (moveToken hpsi kind l r).1 =
            PPL.Elim.view4 l)
          (Or
            (PPL.Elim.view4
                (moveToken hpsi kind l r).2 =
              PPL.Elim.view4 r)
            (PPL.Elim.view4
                (moveToken hpsi kind l r).2 =
              (⟨true, (2 : Fin 3), true, false⟩ :
                PPL.Elim.Cell4))))) := by
  refine And.intro
    (remark2Row_moveToken_initiator_fields
      hpsi kind l r) ?_
  refine And.intro
    (remark2Row_moveToken_responder_fields
      hpsi kind l r) ?_
  exact remark2Row_moveToken_view4_cases
    hpsi kind l r

/-! ## Source-Iota transport -/

private def leftSourceIotaBit
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg : Nat)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg)
    (x : Fin psi) :
    (C
        (shiftRight ring
          (sourceStart psi ring root seg)
          x.val)).id =
      (C'
        (shiftRight ring
          (sourceStart psi ring root seg)
          x.val)).id := by
  exact congrFun hsrc x

private def leftFirstZeroAuxSourceCongr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg fuel j : Nat)
    (hbound : j + fuel <= psi)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg) :
    firstZeroAux ring C
        (sourceStart psi ring root seg)
        fuel j =
      firstZeroAux ring C'
        (sourceStart psi ring root seg)
        fuel j := by
  induction fuel generalizing j with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold firstZeroAux
      have hj : j < psi := by
        omega
      let x : Fin psi := ⟨j, hj⟩
      have hb :=
        leftSourceIotaBit
          ring root C C' seg hsrc x
      change
        (C
          (shiftRight ring
            (sourceStart psi ring root seg)
            j)).id =
        (C'
          (shiftRight ring
            (sourceStart psi ring root seg)
            j)).id at hb
      rw [hb]
      split
      · rfl
      · exact
          ih (j := j + 1)
            (by omega)

private def leftFirstZeroSourceCongr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg : Nat)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg) :
    firstZeroBit ring C
        (sourceStart psi ring root seg) =
      firstZeroBit ring C'
        (sourceStart psi ring root seg) := by
  unfold firstZeroBit
  exact
    leftFirstZeroAuxSourceCongr
      ring root C C' seg psi 0
      (by omega) hsrc

private def leftPayloadCorrectValueCongr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (seg x : Nat)
    (hx : x < psi)
    (t t' : TokenData psi)
    (hsrc :
      sourceIota ring root C seg =
        sourceIota ring root C' seg)
    (hbit :
      tokenBitBool t' = tokenBitBool t)
    (hcarry :
      tokenCarryBool t' = tokenCarryBool t) :
    Iff
      (payloadCorrect ring C
        (sourceStart psi ring root seg) x t)
      (payloadCorrect ring C'
        (sourceStart psi ring root seg) x t') := by
  unfold payloadCorrect
  have hj :=
    leftFirstZeroSourceCongr
      ring root C C' seg hsrc
  let ix : Fin psi := ⟨x, hx⟩
  have hb :=
    leftSourceIotaBit
      ring root C C' seg hsrc ix
  change
    (C
      (shiftRight ring
        (sourceStart psi ring root seg)
        x)).id =
      (C'
        (shiftRight ring
          (sourceStart psi ring root seg)
          x)).id at hb
  rw [hj, hb, hbit, hcarry]

private def leftCorrectSameOccurrence
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (i : Fin n)
    (kind : TokenKind)
    (t : TokenData psi)
    (ht : tokenAt kind (C i) = some t)
    (ht' : tokenAt kind (C' i) = some t)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hcorr :
      CorrectToken ring root C i kind seg.val) :
    CorrectToken ring root C' i kind seg.val := by
  unfold CorrectToken at hcorr ⊢
  rw [ht] at hcorr
  rw [ht']
  dsimp only at hcorr ⊢
  rcases hcorr with
    ⟨hparity, hrest⟩
  refine ⟨hparity, ?_⟩
  by_cases hpos :
      0 < decodeOffset psi (tokenCode t)
  · rw [if_pos hpos] at hrest ⊢
    rcases hrest with
      ⟨hrel, hx, hpay⟩
    exact
      ⟨hrel, hx,
        (leftPayloadCorrectValueCongr
          ring root C C' seg.val _
          hx t t hsrc rfl rfl).mp hpay⟩
  · rw [if_neg hpos] at hrest ⊢
    rcases hrest with
      ⟨hneg, hrel, hx, hpay⟩
    exact
      ⟨hneg, hrel, hx,
        (leftPayloadCorrectValueCongr
          ring root C C' seg.val _
          hx t t hsrc rfl rfl).mp hpay⟩

private def leftCorrectNegativeInvariant
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C C' : Config n psi kappa)
    (i j : Fin n)
    (kind : TokenKind)
    (t t' : TokenData psi)
    (ht : tokenAt kind (C i) = some t)
    (ht' : tokenAt kind (C' j) = some t')
    (hcOld :
      decodeOffset psi (tokenCode t) < 0)
    (hcNew :
      decodeOffset psi (tokenCode t') < 0)
    (htarget :
      tokenTargetSite ring j t' =
        tokenTargetSite ring i t)
    (hbit :
      tokenBitBool t' = tokenBitBool t)
    (hcarry :
      tokenCarryBool t' = tokenCarryBool t)
    (hsrc :
      sourceIota ring root C seg.val =
        sourceIota ring root C' seg.val)
    (hcorr :
      CorrectToken ring root C i kind seg.val) :
    CorrectToken ring root C' j kind seg.val := by
  unfold CorrectToken at hcorr ⊢
  rw [ht] at hcorr
  rw [ht']
  dsimp only at hcorr ⊢
  have hOldNotPos :
      Not (0 < decodeOffset psi (tokenCode t)) := by
    omega
  have hNewNotPos :
      Not (0 < decodeOffset psi (tokenCode t')) := by
    omega
  rw [if_neg hOldNotPos] at hcorr
  rw [if_neg hNewNotPos]
  rw [htarget]
  rcases hcorr with
    ⟨hparity, _hcOld, hrel, hx, hpay⟩
  exact
    ⟨hparity, hcNew, hrel, hx,
      (leftPayloadCorrectValueCongr
        ring root C C' seg.val _
        hx t t' hsrc hbit hcarry).mp hpay⟩

private def leftGhostSoundToken
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (i : Fin n)
    (z : GhostToken n psi)
    (hphys : G.phys = C)
    (hG : GhostSound G)
    (howner :
      ghostTokenAt kind G i = some z) :
    tokenAt kind (C i) = some z.value := by
  cases kind with
  | black =>
      have hs := hG.1 i z howner
      rw [hphys] at hs
      exact hs.1
  | white =>
      have hs := hG.2 i z howner
      rw [hphys] at hs
      exact hs.1

/-! ## Smallest remaining row obligation -/

/--
Pure selected-shadow shape of the responder-owned row.

This deliberately omits every paper-semantic premise: no root/segment,
ValidToken, WorkingFor, CorrectToken, CDLAt, or sourceIota.  It says only
that a same-ID post owner on the interacted pair is one of:

* responder stay with the same physical token value;
* an ordinary negative move preserving physical target and payload/carry;
* the literal c = -1 line-29 turn.

The remaining proof is the finite branch split over ghostStep /
the selected ghostMoveToken mirror.  GhostIdsUniqueAt excludes the only
spurious sources: a pre-left duplicate ID and a same-step fresh birth.
-/
def Remark2LeftSelectedShape : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (step : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (G : GhostConfig n psi kappa)
    (kind : TokenKind)
    (z : GhostToken n psi),
    G.phys = C ->
    GhostSound G ->
    GhostIdsUniqueAt step G ->
    ghostTokenAt kind G
      (ring.rightNeighbor e) = some z ->
    forall (j : Fin n)
      (z' : GhostToken n psi),
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) j =
          some z' ->
      z'.lmeta.id = z.lmeta.id ->
      Or (j = e)
        (j = ring.rightNeighbor e) ->
      Or
        (And
          (j = ring.rightNeighbor e)
          (And
            (z'.value = z.value)
            (tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa)
                ring C e)
                (ring.rightNeighbor e)) =
              some z.value)))
        (Or
          (And
            (j = e)
            (And
              (tokenAt kind
                ((PopulationProtocol.step
                  (protocol psi kappa)
                  ring C e) e) =
                some z'.value)
              (And
                (decodeOffset psi
                  (tokenCode z.value) < 0)
                (And
                  (decodeOffset psi
                    (tokenCode z'.value) < 0)
                  (And
                    (tokenTargetSite ring e
                        z'.value =
                      tokenTargetSite ring
                        (ring.rightNeighbor e)
                        z.value)
                    (And
                      (tokenBitBool z'.value =
                        tokenBitBool z.value)
                      (tokenCarryBool z'.value =
                        tokenCarryBool z.value)))))))
          (And
            (j = e)
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

/-- All paper-semantic work is closed once the literal selected-shadow shape
above is supplied.  The c = -1 branch is discharged by the public carry
adapter, rather than left as an extra assumption. -/
theorem remark2LeftSelectedRow_of_shape
    (hshape : Remark2LeftSelectedShape) :
    Remark2LeftSelectedRow := by
  unfold Remark2LeftSelectedRow
  intro n psi kappa hpsi hn3
  intro ring root seg step C e G kind z
  intro hphys hG huniq howner
  intro hvalid hwork hcorr hC hC'
  intro j z' hsrc hpost hid hj

  have htok0 :
      tokenAt kind
        (C (ring.rightNeighbor e)) =
          some z.value :=
    leftGhostSoundToken
      C G kind (ring.rightNeighbor e) z
      hphys hG howner

  have hs :=
    hshape hpsi hn3 ring step C e
      G kind z hphys hG huniq howner
      j z' hpost hid hj

  rcases hs with hstay | hrest
  · rcases hstay with
      ⟨hjr, _hzval, htok1⟩
    subst j
    exact
      Or.inl
        (leftCorrectSameOccurrence
          ring root seg C
          (PopulationProtocol.step
            (protocol psi kappa) ring C e)
          (ring.rightNeighbor e)
          kind z.value
          htok0 htok1 hsrc hcorr)

  · rcases hrest with hord | hturn
    · rcases hord with
        ⟨hje, htok1, hcOld, hcNew,
          htarget, hbit, hcarry⟩
      subst j
      exact
        Or.inl
          (leftCorrectNegativeInvariant
            ring root seg C
            (PopulationProtocol.step
              (protocol psi kappa) ring C e)
            (ring.rightNeighbor e) e
            kind z.value z'.value
            htok0 htok1
            hcOld hcNew htarget
            hbit hcarry hsrc hcorr)

    · rcases hturn with
        ⟨hje, hcneg, htok1, hzval⟩
      subst j
      have hpostTurn :
          tokenAt kind
              ((PopulationProtocol.step
                (protocol psi kappa)
                ring C e) e) =
            some
              (remark2NegTurnValue
                hpsi (C e).id z.value) := by
        rw [← hzval]
        exact htok1
      exact
        Or.inl
          (remark2Row_negTurn_correct
            hpsi ring root seg
            C
            (PopulationProtocol.step
              (protocol psi kappa) ring C e)
            e (ring.rightNeighbor e)
            kind z.value
            rfl rfl htok0 hcneg hpostTurn
            hvalid hwork hcorr hC hC' hsrc)

#print axioms PPL.remark2LeftSelected_physicalFacts
#print axioms PPL.remark2LeftSelectedRow_of_shape

end PPL

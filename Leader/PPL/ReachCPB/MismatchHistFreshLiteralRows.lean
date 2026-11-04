import Leader.PPL.ReachCPB.MismatchHistFreshLiteral
import Leader.PPL.TokenCompletion.GhostStepMirror


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL
open PPL.Probability


/-!
Reduction.

The target is true, but the remaining literal proof mixes two logically
different jobs:

* reconstruct which old/new selected endpoint owner produced one post owner;
* transport the macro-stage/payload/prefix/latch invariant through the
  corresponding offset branch.

The data types below expose only the information needed by the second job.
They deliberately contain no canonical-run premise, no schedule induction,
and no bad-border/completion conclusion.

There are four residual Props:

1. `Lemma16AgedSelectedOwnerCaseRow`: pure selected-pair owner provenance;
2. `Lemma16AgedOrdinaryOwnerRow`: birth/stay/c>=2/c<=-2 transport;
3. `Lemma16AgedC1OwnerRow`: the +1 right turn and negative latch;
4. `Lemma16AgedNegOneOwnerRow`: the -1 turn, q increment, payload recurrence.

The adapter at the bottom is kernel-cheap.
-/


/-! -------------------------------------------------------------------------
    Exact post-live goal, factored only to shorten the residual signatures
------------------------------------------------------------------------- -/


def Lemma16AgedLiveGoal
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (b k i : Fin n)
    (z : GhostToken n psi) : Prop :=
  Exists fun q : Nat =>
    And (q < psi)
      (And
        (Lemma16FreshMacroStageAt
          ring k i z q)
        (And
          (payloadCorrect
            ring Cepoch k q z.value)
          (And
            (Lemma16TargetPrefix
              ring Cepoch b k q)
            (decodeOffset psi
                  (tokenCode z.value) < 0 ->
              (Cepoch
                  (shiftRight ring b q)).id =
                lemma16ExpectedAddOneBit
                  ring Cepoch k q))))


/-! -------------------------------------------------------------------------
    Owner-case data returned by the pure ghost selected-pair case tree
------------------------------------------------------------------------- -/


/--
A surviving birth cannot remain at the initiator: the freshly created token
starts at c=psi and, because psi>=2, immediately takes the ordinary positive
right move.  Thus a surviving current-step birth is at the responder, has
moves=1 and c=psi-1, with the literal birth bit/carry copied from the
initiator ID.
-/
structure Lemma16AgedBirthData
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  hsite :
    i = ring.rightNeighbor e
  hid :
    z.lmeta.id = .born kind step
  hbirthSite :
    z.lmeta.birthSite = e
  hbirthStep :
    z.lmeta.birthStep = step
  hmoves :
    z.lmeta.moves = 1
  hoffset :
    decodeOffset psi (tokenCode z.value) =
      (((psi - 1 : Nat) : Int))
  hbit :
    tokenBitBool z.value = !(G.phys e).id
  hcarry :
    tokenCarryBool z.value = (G.phys e).id


/--
Inactive-last, unselected-responder, and collision-survivor cases all have
the same semantic shape: the post owner is literally an old endpoint owner
with unchanged ghost token and unchanged site.
-/
structure Lemma16AgedStayData
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  site : Fin n
  source : GhostToken n psi
  hpair :
    Or (site = e)
      (site = ring.rightNeighbor e)
  hsite :
    i = site
  howner :
    ghostTokenAt kind G site = some source
  hsame :
    z = source


/--
Ordinary positive service.  The old initiator moves right, metadata advances
once, c decreases by one, and payload/carry are transported literally.
-/
structure Lemma16AgedRightOrdinaryData
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  source : GhostToken n psi
  howner :
    ghostTokenAt kind G e = some source
  hsite :
    i = ring.rightNeighbor e
  hmeta :
    z.lmeta = ghostStepLineageAdvance source.lmeta
  hbit :
    tokenBitBool z.value =
      tokenBitBool source.value
  hcarry :
    tokenCarryBool z.value =
      tokenCarryBool source.value
  hpositive :
    (2 : Int) <=
      decodeOffset psi (tokenCode source.value)
  hoffset :
    decodeOffset psi (tokenCode z.value) =
      decodeOffset psi (tokenCode source.value) - 1


/--
Ordinary negative service.  The old responder moves left, metadata advances
once, c increases by one, and payload/carry are transported literally.
-/
structure Lemma16AgedLeftOrdinaryData
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  source : GhostToken n psi
  howner :
    ghostTokenAt kind G
        (ring.rightNeighbor e) =
      some source
  hsite :
    i = e
  hmeta :
    z.lmeta = ghostStepLineageAdvance source.lmeta
  hbit :
    tokenBitBool z.value =
      tokenBitBool source.value
  hcarry :
    tokenCarryBool z.value =
      tokenCarryBool source.value
  hnegative :
    decodeOffset psi (tokenCode source.value) <=
      (-2 : Int)
  hoffset :
    decodeOffset psi (tokenCode z.value) =
      decodeOffset psi (tokenCode source.value) + 1


inductive Lemma16AgedOrdinaryData
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  | birth :
      Lemma16AgedBirthData
        ring kind step G e i z ->
      Lemma16AgedOrdinaryData
        ring kind step G e i z
  | stay :
      Lemma16AgedStayData
        ring kind G e i z ->
      Lemma16AgedOrdinaryData
        ring kind step G e i z
  | right :
      Lemma16AgedRightOrdinaryData
        ring kind G e i z ->
      Lemma16AgedOrdinaryData
        ring kind step G e i z
  | left :
      Lemma16AgedLeftOrdinaryData
        ring kind G e i z ->
      Lemma16AgedOrdinaryData
        ring kind step G e i z


/--
The c=+1 initiator branch.  Metadata advances, the owner moves to the
responder, the payload is unchanged, and the signed offset turns to 1-psi.
The semantic row below derives the new negative latch from border geometry
and the non-CPB hypothesis.
-/
structure Lemma16AgedC1Data
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  source : GhostToken n psi
  howner :
    ghostTokenAt kind G e = some source
  hsite :
    i = ring.rightNeighbor e
  hmeta :
    z.lmeta = ghostStepLineageAdvance source.lmeta
  hbit :
    tokenBitBool z.value =
      tokenBitBool source.value
  hcarry :
    tokenCarryBool z.value =
      tokenCarryBool source.value
  hsourceOffset :
    decodeOffset psi (tokenCode source.value) =
      (1 : Int)
  hpostOffset :
    decodeOffset psi (tokenCode z.value) =
      (1 : Int) - (((psi : Nat) : Int))


/--
The c=-1 responder turn.  The selected responder moves left to the initiator,
metadata advances, and the offset resets to +psi.  The payload fields are
the literal line-29 carry recurrence, with the source bit read from the left
endpoint.  Under LastReady/Detect that endpoint ID is the frozen Cepoch bit.
-/
structure Lemma16AgedNegOneData
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  source : GhostToken n psi
  howner :
    ghostTokenAt kind G
        (ring.rightNeighbor e) =
      some source
  hsite :
    i = e
  hmeta :
    z.lmeta = ghostStepLineageAdvance source.lmeta
  hsourceOffset :
    decodeOffset psi (tokenCode source.value) =
      (-1 : Int)
  hpostOffset :
    decodeOffset psi (tokenCode z.value) =
      (((psi : Nat) : Int))
  hpayload :
    if tokenCarryBool source.value = true then
      And
        (tokenBitBool z.value = !(G.phys e).id)
        (tokenCarryBool z.value = (G.phys e).id)
    else
      And
        (tokenBitBool z.value = (G.phys e).id)
        (tokenCarryBool z.value = false)


inductive Lemma16AgedSelectedOwnerCase
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Type where
  | ordinary :
      Lemma16AgedOrdinaryData
        ring kind step G e i z ->
      Lemma16AgedSelectedOwnerCase
        ring kind step G e i z
  | c1 :
      Lemma16AgedC1Data
        ring kind G e i z ->
      Lemma16AgedSelectedOwnerCase
        ring kind step G e i z
  | negOne :
      Lemma16AgedNegOneData
        ring kind G e i z ->
      Lemma16AgedSelectedOwnerCase
        ring kind step G e i z


/-! -------------------------------------------------------------------------
    Four strictly smaller residual Props
------------------------------------------------------------------------- -/


/--
Pure owner-provenance row.

Truth argument.  Copy the selected-colour `ghostMoveToken` mirror from
`TokenCorrectnessLemma4SweepInitiatorRows.lean`.  `liveShadow` first removes
stale/invalid old owners.  With last inactive the surviving owner is a stay.
With last active, freshen can contribute only the current-step birth; if it
survives collision, c=psi>=2 immediately moves it right once, giving the
`birth` constructor.  Otherwise collision deletes the left contender and
the remaining six offset tests give exactly stay, c>=2 right, c=1 right,
c<=-2 left, or c=-1 left.  LastReady is used only to identify the birth/turn
source ID bit with `G.phys e.id`; there is no payload-prefix or age argument.
-/
def Lemma16AgedSelectedOwnerCaseRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    LastReadyCapped ring G.phys ->
    forall (i : Fin n)
      (z : GhostToken n psi),
      Or (i = e)
        (i = ring.rightNeighbor e) ->
      ghostTokenAt kind
          (ghostStep hpsi ring step G e) i =
        some z ->
      Nonempty
        (Lemma16AgedSelectedOwnerCase
          ring kind step G e i z)


/--
Birth/stay/ordinary-transport semantic row.

Truth argument.  Post no-prior implies pre no-prior because completed is
A stay therefore applies the old live invariant verbatim.
For c>=2 and c<=-2, one move changes the site and signed offset by the same
one edge, advances metadata.moves by one, and keeps q, payload and prefix;
a negative ordinary move keeps the already-established latch as well.
A surviving current-step birth has birthSite=e=k, q=0, x=1, moves=1 and
c=psi-1.  Its literal (!id,id) payload is exactly payloadCorrect at bit zero;
the prefix is empty and the post offset is positive, so the latch is vacuous.
Only the frozen-ID half of the state invariant is needed for the birth bit.
-/
def Lemma16AgedOrdinaryOwnerRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G ->
    forall (i : Fin n)
      (z : GhostToken n psi)
      (t : Nat),
      z.lmeta.id = .born kind t ->
      z.lmeta.birthSite = k ->
      epoch <= t ->
      Lemma16NoPriorCompletionId
        (ghostStep hpsi ring step G e)
        z.lmeta.id ->
      Lemma16AgedOrdinaryData
        ring kind step G e i z ->
      Lemma16AgedLiveGoal
        ring Cepoch b k i z


/--
c=+1 semantic row.

Truth argument.  Post no-prior again gives pre no-prior, so the old initiator
has some q<psi with the pre payload/prefix invariant.  Its c=1 macro-stage
equation and
`lemma16FreshMacroStage_c1_responder_of_borderGeometry`
identify the actual responder with `shiftRight ring b q`.  LastReady is
DetectReady plus the distance/last conditions, and
`lemma16MismatchHistFrozenIdStep` freezes IDs.  If the token bit disagreed
with that responder ID, the c=1 Detect comparison would create a leader and
the capped Detect persistence/peaceful row would put the post state in CPB,
contrary to hnot.  Hence the bit matches; after the literal turn to 1-psi
this equality is exactly the new negative latch.  Payload and prefix are
unchanged and q stays fixed.
-/
def Lemma16AgedC1OwnerRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi ->
    LastReadyCapped ring G.phys ->
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G ->
    Not
      (CPB ring
        (ghostStep hpsi ring step G e).phys) ->
    forall (i : Fin n)
      (z : GhostToken n psi)
      (t : Nat),
      z.lmeta.id = .born kind t ->
      z.lmeta.birthSite = k ->
      epoch <= t ->
      Lemma16NoPriorCompletionId
        (ghostStep hpsi ring step G e)
        z.lmeta.id ->
      Lemma16AgedC1Data
        ring kind G e i z ->
      Lemma16AgedLiveGoal
        ring Cepoch b k i z


/--
c=-1 semantic row.

Truth argument.  The source responder satisfies the pre live invariant at
some q<psi.  Post no-prior implies pre no-prior, so the age premise applies.
At c=-1 the pre trajectory formula is
  moves = q*(2*psi-1) + (2*psi-2).
If q+1=psi, this is >= tokenTrajectoryMoves psi (equal at psi=2 and strictly
larger for psi>2), contradicting the strict age bound.  Thus q+1<psi.
The old negative latch supplies the new target-prefix entry x=q.  The
line-29 carry update in `Lemma16AgedNegOneData.hpayload` is exactly the
firstZeroBit add-one recurrence for payloadCorrect at q+1.  The new offset is
+psi, so the post latch implication is vacuous.  Metadata/site equations give
the q+1 macro-stage directly.
-/
def Lemma16AgedNegOneOwnerRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G ->
    Lemma16FreshNoPriorTerminalAge
      kind k G ->
    forall (i : Fin n)
      (z : GhostToken n psi)
      (t : Nat),
      z.lmeta.id = .born kind t ->
      z.lmeta.birthSite = k ->
      epoch <= t ->
      Lemma16NoPriorCompletionId
        (ghostStep hpsi ring step G e)
        z.lmeta.id ->
      Lemma16AgedNegOneData
        ring kind G e i z ->
      Lemma16AgedLiveGoal
        ring Cepoch b k i z


/-! -------------------------------------------------------------------------
    Exact adapter back to the earlier target
------------------------------------------------------------------------- -/


theorem
    lemma16PostEpochFreshSelectedLiveLiteralAgedRow_of_localRows
    (hcases : Lemma16AgedSelectedOwnerCaseRow)
    (hordinary : Lemma16AgedOrdinaryOwnerRow)
    (hc1 : Lemma16AgedC1OwnerRow)
    (hnegOne : Lemma16AgedNegOneOwnerRow) :
    Lemma16PostEpochFreshSelectedLiveLiteralAgedRow := by
  unfold Lemma16AgedSelectedOwnerCaseRow at hcases
  unfold Lemma16AgedOrdinaryOwnerRow at hordinary
  unfold Lemma16AgedC1OwnerRow at hc1
  unfold Lemma16AgedNegOneOwnerRow at hnegOne
  unfold Lemma16PostEpochFreshSelectedLiveLiteralAgedRow

  intro n psi kappa
  intro hpsi hn3 ring Cepoch epoch b k kind
  intro step G e
  intro hgeom hready hinv hage
  dsimp only
  intro hnot
  intro i z t
  intro hpair howner hid hsite hepoch hprior

  rcases
      hcases
        hpsi hn3 ring kind step G e
        hready i z hpair howner with
    ⟨hcase⟩

  cases hcase with
  | ordinary hord =>
      exact
        hordinary
          hpsi ring Cepoch epoch b k kind
          step G e
          hinv
          i z t
          hid hsite hepoch hprior
          hord

  | c1 hturn =>
      exact
        hc1
          hpsi hn3 ring Cepoch epoch b k kind
          step G e
          hgeom hready hinv hnot
          i z t
          hid hsite hepoch hprior
          hturn

  | negOne hturn =>
      exact
        hnegOne
          hpsi ring Cepoch epoch b k kind
          step G e
          hinv hage
          i z t
          hid hsite hepoch hprior
          hturn


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshSelectedLiveLiteralAgedRow_of_localRows

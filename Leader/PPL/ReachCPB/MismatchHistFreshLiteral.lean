import Leader.PPL.ReachCPB.MismatchHistFreshAge

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
The canonical history seam is now closed by
`lemma16FreshNoPriorTerminalAgeCanon_proved`.  What remains is a single
state-local selected-pair row.  It has no scheduler induction and no canonical
run provenance: `G` and `step` are arbitrary, while the already-proved age
hypothesis rules out the extra lap.

Literal `ghostMoveToken` branch inventory for a post live fresh owner with no
prior completion:

* inactive-last / live-shadow stay: same macro stage q < psi; payload, prefix,
  and the negative latch are unchanged;
* fresh left birth: q = 0 < psi; `payloadCorrect ... 0` is the birth payload,
  the target prefix is vacuous, and the negative-latch antecedent is false;
* collision: the left contender is deleted, so a surviving old responder is
  handled by the negative branches below;
* initiator c >= 2: moves right with c-1 at the same q; bit/carry, payload,
  prefix, and any already-required latch are transported unchanged;
* initiator c = 1: moves right and turns to c = 1-psi at the same q.
  `lemma16FreshMacroStage_c1_responder_of_borderGeometry` identifies the
  responder as `shiftRight ring b q`; the mismatch alternative creates a
  leader, so under the non-CPB hypothesis the matching branch supplies the
  negative-half latch.  Payload and prefix are unchanged;
* responder c <= -2: moves left with c+1 at the same q; bit/carry, payload,
  prefix, and latch are unchanged;
* responder c = -1: turns to +psi and advances q to q+1.  The aged premise
  excludes the terminal/extra-lap case and gives q+1 < psi.  The old negative
  latch supplies the new target-prefix entry x=q; the payload is the add-one
  recurrence; the post token is positive, so its latch clause is vacuous.

Thus the exact remaining proof object is the finite selected-colour literal
row below.
-/

/--
The LastReady distance premise already contains the exact adjacent-border
distance used by the c=1 geometry branch.
-/
theorem lemma16AgedRow_borderDistance_eq
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (b : Fin n)
    (hready : LastReadyCapped ring C)
    (hb : PPL.IsBorder C b) :
    PPL.nextBorderDistance ring C b = psi ∧
      PPL.prevBorderDistance ring C b = psi := by
  exact
    lemma16DistReady_nextBorderDistance_eq
      hpsi ring C b hready.1 hb

/--
Exact remaining finite branch row.

Compared with
`Lemma16PostEpochFreshSelectedLiveStepGeomLastCanonAged`, all canonical-run
structure has been removed.  The hypotheses are precisely the state-local
facts available immediately before one selected interaction, including the
per-lineage age bound.  Proving this Prop is only the literal
`ghostMoveToken` split listed above.
-/
def Lemma16PostEpochFreshSelectedLiveLiteralAgedRow : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi ->
    LastReadyCapped ring G.phys ->
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G ->
    Lemma16FreshNoPriorTerminalAge
      kind k G ->
    let G' :=
      PPL.ghostStep hpsi ring step G e
    ¬ PPL.CPB ring G'.phys ->
    forall (i : Fin n)
      (z : PPL.GhostToken n psi)
      (t : Nat),
      (i = e ∨
        i = ring.rightNeighbor e) ->
      PPL.ghostTokenAt kind G' i =
        some z ->
      z.lmeta.id = .born kind t ->
      z.lmeta.birthSite = k ->
      epoch <= t ->
      Lemma16NoPriorCompletionId
        G' z.lmeta.id ->
      exists q : Nat,
        q < psi ∧
          Lemma16FreshMacroStageAt
            ring k i z q ∧
          PPL.payloadCorrect
            ring Cepoch k q z.value ∧
          Lemma16TargetPrefix
            ring Cepoch b k q ∧
          (PPL.decodeOffset psi
              (PPL.tokenCode z.value) < 0 ->
            (Cepoch
                (PPL.shiftRight ring b q)).id =
              lemma16ExpectedAddOneBit
                ring Cepoch k q)

/--
The canonical target is a direct specialization of the finite aged literal
row.  No history theorem remains here.
-/
theorem
    lemma16PostEpochFreshSelectedLiveStepGeomLastCanonAged_of_literalAged
    (hliteral :
      Lemma16PostEpochFreshSelectedLiveLiteralAgedRow) :
    Lemma16PostEpochFreshSelectedLiveStepGeomLastCanonAged := by
  unfold
    Lemma16PostEpochFreshSelectedLiveLiteralAgedRow
    at hliteral
  unfold
    Lemma16PostEpochFreshSelectedLiveStepGeomLastCanonAged
  intro n psi kappa hpsi hn3
  intro ring Cepoch epoch b k kind
  intro C0 pre e
  dsimp only
  intro hgeom hready hinv hage
  try dsimp only
  intro hnot i z t
  intro hpair howner hid hsite hepoch hprior
  exact
    hliteral
      hpsi hn3 ring Cepoch epoch b k kind
      pre.length
      (PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre)
      e
      hgeom hready hinv hage
      hnot
      i z t
      hpair howner hid hsite hepoch hprior

/--
Once the one finite literal row above is supplied, the requested global
canonical live row follows from the landed canonical age theorem and the
existing selected-pair/off-pair adapter.
-/
theorem
    lemma16PostEpochFreshLiveStepGeomLastCanon_of_literalAged
    (hliteral :
      Lemma16PostEpochFreshSelectedLiveLiteralAgedRow) :
    Lemma16PostEpochFreshLiveStepGeomLastCanon := by
  exact
    lemma16PostEpochFreshLiveStepGeomLastCanon_of_selectedAged
      lemma16FreshNoPriorTerminalAgeCanon_proved
      (lemma16PostEpochFreshSelectedLiveStepGeomLastCanonAged_of_literalAged
        hliteral)

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16AgedRow_borderDistance_eq
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshSelectedLiveStepGeomLastCanonAged_of_literalAged
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshLiveStepGeomLastCanon_of_literalAged

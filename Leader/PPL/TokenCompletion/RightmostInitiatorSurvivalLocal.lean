import Leader.PPL.TokenCompletion.RightmostInitiatorStateLocal
import Leader.PPL.TokenCompletion.SweepInitiatorSameId

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
Truth check.

The residual is TRUE state-locally; dropping run history and global
GhostIdsUniqueAt does not create an alias counterexample.

Reason.  From Cd with psi >= 2 one gets 2 * psi <= n, so the C_d window is
embedded without wrap aliasing.  A GhostSound rightmost owner cannot sit at
window coordinate 2 * psi - 1: at that coordinate every legal signed offset
in [-psi+1,-1] union [1,psi] has its Definition-3 target on the wrong side.
Hence its responder is the genuine next in-window site.  Rightmostness says
that site has no ghost owner; coverage plus GhostSound therefore rules out a
valid selected-color physical responder there.  Conversely the tracked
initiator stays live through the selected-input token/dist frame, so line 12
cannot erase it and the birth guard cannot replace it by an unrelated
current-step owner.  Thus any same-ID selected output is the tracked lineage:
c < 0 stays left; c = 1 and c >= 2 move right.  No global ID uniqueness is
used.  The post-rightmost and progress facts are then local endpoint/frame
bookkeeping.

The direct proof is the same explicit selected-pair tree already compiled in
TokenCorrectnessLemma4SweepInitiatorRows.lean, but its useful helpers are
private.  The reduction below isolates the three strictly smaller offset
leaves.  Each leaf fixes the only remaining movement class; there is no
history, uniqueness, or kinematics premise in any leaf.
-/

/-- Exact conclusion of the state-local survivor row, factored for the
three fixed-offset leaves below. -/
def Lemma4RightmostInitiatorSurvivalStateLocalConclusion
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi) : Prop :=
  let i := shiftRight ring k x.val
  let G' := ghostStep hpsi ring step G e
  ∃ y : Fin (2 * psi), ∃ z' : GhostToken n psi,
    Lemma4RightmostAt ring k kind G' y z' ∧
    z'.lmeta.id = z.lmeta.id ∧
    (FreshAt kind k z.lmeta →
      FreshAt kind k z'.lmeta) ∧
    lemma4TokenProgress kind
        (G.phys i) z.value ≤
      lemma4TokenProgress kind
        (G'.phys (shiftRight ring k y.val))
        z'.value ∧
    (e = lemma4ServiceEdge ring kind G i z →
      lemma4TokenProgress kind
          (G'.phys (shiftRight ring k y.val))
          z'.value =
        lemma4TokenProgress kind
            (G.phys i) z.value +
          1)

/--
Arrival leaf, c = 1.

Truth argument: source-live plus empty-live-responder rules out collision and
birth substitution.  Same-ID survival therefore forces the right bump of z.
The bump advances exactly z.lmeta, preserves FreshAt, and its new offset is
1 - psi.  Pre/post C_d give adjacent canonical distances, so the arrival
stage is unchanged and lemma4TokenProgress increases by one.  Every larger
window coordinate is an untouched pre-step coordinate, hence empty by the
pre-step rightmost hypothesis.
-/
def Lemma4RightmostInitiatorSurvivalArrivalLocalRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    Lemma4RightmostAt ring k kind G x z →
    e = shiftRight ring k x.val →
    ((∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id) ∨
      (∃ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR ∧
        zR.lmeta.id = z.lmeta.id)) →
    decodeOffset psi (tokenCode z.value) = 1 →
    Lemma4RightmostInitiatorSurvivalStateLocalConclusion
      hpsi ring k kind step G e x z

/--
Ordinary positive leaf, c >= 2.

Truth argument: as above, the tracked source is the only live selected-color
carrier entering the selected move.  Same-ID survival forces the responder
bump.  Its offset is c-1, target coordinate is unchanged under the adjacent
C_d distance increment, and the standard positive progress formula gives
exactly +1.  The responder is coordinate x+1 and all farther coordinates are
literal ghostStep frames of sites that were empty by rightmostness.
-/
def Lemma4RightmostInitiatorSurvivalRightMoveLocalRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    Lemma4RightmostAt ring k kind G x z →
    e = shiftRight ring k x.val →
    ((∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id) ∨
      (∃ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR ∧
        zR.lmeta.id = z.lmeta.id)) →
    2 ≤ decodeOffset psi (tokenCode z.value) →
    Lemma4RightmostInitiatorSurvivalStateLocalConclusion
      hpsi ring k kind step G e x z

/--
Negative leaf, c < 0.

Truth argument: the initiator is not serviced by edge e.  With no live
responder, the selected-color move is a stay and same-ID survival is exactly
z on the left endpoint.  Pre/post C_d give the same selected-site distance,
so validity and progress are unchanged.  Since the service edge for a
negative token is ring.leftNeighbor e, the exact-service implication is
vacuous.  The responder output is empty and every farther coordinate is an
off-pair frame of a pre-step empty coordinate, so z remains rightmost.
-/
def Lemma4RightmostInitiatorSurvivalTurnLocalRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    Lemma4RightmostAt ring k kind G x z →
    e = shiftRight ring k x.val →
    ((∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id) ∨
      (∃ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR ∧
        zR.lmeta.id = z.lmeta.id)) →
    decodeOffset psi (tokenCode z.value) < 0 →
    Lemma4RightmostInitiatorSurvivalStateLocalConclusion
      hpsi ring k kind step G e x z

/--
Kernel-trivial assembly from the three finite selected-pair leaves.

This is a strict reduction: every remaining premise is a one-offset-class
one-step Prop, whereas the requested residual quantifies over all legal
offsets.  lemma4SweepInitiatorOffsetCases is unconditional and partitions
exactly c = 1, c >= 2, c < 0.
-/
theorem lemma4RightmostInitiatorSurvivalStateLocalResidual_of_localRows
    (hArrival :
      Lemma4RightmostInitiatorSurvivalArrivalLocalRow)
    (hRightMove :
      Lemma4RightmostInitiatorSurvivalRightMoveLocalRow)
    (hTurn :
      Lemma4RightmostInitiatorSurvivalTurnLocalRow) :
    Lemma4RightmostInitiatorSurvivalStateLocalResidual := by
  unfold Lemma4RightmostInitiatorSurvivalStateLocalResidual
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound
  intro hright htrack hsame
  change
    Lemma4RightmostInitiatorSurvivalStateLocalConclusion
      hpsi ring k kind step G e x z
  rcases
      lemma4SweepInitiatorOffsetCases
        hpsi z.value with
    h1 | h2 | hneg
  · exact
      hArrival
        hpsi ring k kind step G e x z
        hCd hCd' hcovered hsound
        hright htrack hsame h1
  · exact
      hRightMove
        hpsi ring k kind step G e x z
        hCd hCd' hcovered hsound
        hright htrack hsame h2
  · exact
      hTurn
        hpsi ring k kind step G e x z
        hCd hCd' hcovered hsound
        hright htrack hsame hneg

end PPL

#print axioms PPL.lemma4RightmostInitiatorSurvivalStateLocalResidual_of_localRows

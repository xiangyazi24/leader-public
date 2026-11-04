import Leader.Wu.Birth.ControlledWrap

namespace BirthB1ControlledWrapGeneral

open PPLL
open BirthB1ControlledWrap
open BirthB1RightDrainProducer
open Q11632RightDrainCollar
open BirthShortDoneTerminalB1EntranceR2

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthB1ControlledWrap.FC n psi kappa tau

/-- The absorption theorem at the correct quantifier: the current state is
    already a certified moving-pair state. -/
def ControlledWrapAbsorptionFromInvariantStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen echoPos resetK : Nat),
    ControlledWrapInvariant hpsi ring initial current a
      corridorLen echoPos resetK ->
    exists finish : List (Fin n),
      WordSupported ring a corridorLen finish /\
      (let D := currentRun hpsi h2 ring current finish
       HasLeaderAlong hpsi h2 ring current finish \/
        (LeaderlessAlong hpsi h2 ring current finish /\
          AlignedAlong hpsi h2 ring current finish a /\
          CorridorTerminated ring D a corridorLen /\
          ThreeSiteSanitized hpsi ring D a))

/-- Exact no-birth handoff that the maximal right-drain producer has to expose.
    The existing `RightDrainProducer`/`ResetFrontTrace` does not yet prove this
    stronger endpoint contract in general n. -/
def RightDrainControlledWrapEntryStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi) (_hn : 4 <= n)
    (ring : DirectedRing n) : Prop :=
  forall (C : FC n psi kappa tau) (a : Fin n),
    BirthShortDoneTerminalFirstHit.Leaderless C ->
    TripleLabels hpsi ring C a ->
    exists corridorLen : Nat, exists pre : List (Fin n),
      0 < corridorLen /\
      2 + corridorLen + 1 = n /\
      (let drain := rightDrainWord ring a corridorLen
       let w := pre ++ drain
       let frontier := currentRun hpsi h2 ring C w
       WordSupported ring a corridorLen w /\
        (HasLeaderAlong hpsi h2 ring C w \/
          (LeaderlessAlong hpsi h2 ring C w /\
            AlignedAlong hpsi h2 ring C w a /\
            ControlledWrapInvariant hpsi ring frontier frontier a
              corridorLen 2 corridorLen)))

/-- Literal-host gates needed by the deterministic induction choice:
    move echo while it is positive; then move reset while it is short of the
    maximal boundary; finally execute the closing collision. -/
def ControlledWrapGateReady
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (current : FC n psi kappa tau)
    (a : Fin n) (corridorLen echoPos resetK : Nat) : Prop :=
  (0 < echoPos ->
    let e := echoTransportEdge ring a echoPos
    PreparedOrdinaryOpen hpsi
        (current e) (current (ring.rightNeighbor e)) /\
      BirthShortDoneTerminalPassiveR4.RowPreCap2
        hpsi h2 kappa ring current e) /\
  (echoPos = 0 -> resetK < corridorLen ->
    let e := drainSite ring a resetK
    PreparedOrdinaryOpen hpsi
      (current e) (current (ring.rightNeighbor e))) /\
  (echoPos = 0 -> resetK = corridorLen ->
    let e := drainSite ring a corridorLen
    PreparedOrdinaryOpen hpsi
        (current e) (current (ring.rightNeighbor e)) /\
      BirthShortDoneTerminalPassiveR4.RowPreCap2
        hpsi h2 kappa ring current e)

/-- One reverse-echo consumer step, upgraded with the strict rank drop. -/
theorem echo_step_ranked
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hstep : ControlledWrapEchoConsumerStepStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (initial current : FC n psi kappa tau) (a : Fin n)
    (corridorLen echoPos resetK : Nat)
    (hinv : ControlledWrapInvariant hpsi ring initial current a
      corridorLen echoPos resetK)
    (hpos : 0 < echoPos)
    (hopen :
      PreparedOrdinaryOpen hpsi
        (current (echoTransportEdge ring a echoPos))
        (current (ring.rightNeighbor
          (echoTransportEdge ring a echoPos))))
    (hpre : BirthShortDoneTerminalPassiveR4.RowPreCap2
      hpsi h2 kappa ring current (echoTransportEdge ring a echoPos)) :
    let e := echoTransportEdge ring a echoPos
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D \/
      (ControlledWrapInvariant hpsi ring initial D a
          corridorLen (echoPos - 1) resetK /\
        controlledWrapPairDistance corridorLen (echoPos - 1) resetK <
          controlledWrapPairDistance corridorLen echoPos resetK) := by
  dsimp only
  have hs := hstep initial current a corridorLen echoPos resetK
    hinv hpos hopen hpre
  rcases hs with hs | hs
  · exact Or.inl hs
  · exact Or.inr
      ⟨hs, controlledWrapPairDistance_echo_step hpos⟩

/-- One clockwise reset consumer step, upgraded with the strict rank drop. -/
theorem reset_step_ranked
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hstep : ControlledWrapResetConsumerStepStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (initial current : FC n psi kappa tau) (a : Fin n)
    (corridorLen echoPos resetK : Nat)
    (hinv : ControlledWrapInvariant hpsi ring initial current a
      corridorLen echoPos resetK)
    (hk : resetK < corridorLen)
    (hopen :
      PreparedOrdinaryOpen hpsi
        (current (drainSite ring a resetK))
        (current (ring.rightNeighbor (drainSite ring a resetK)))) :
    let e := drainSite ring a resetK
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D \/
      (ControlledWrapInvariant hpsi ring initial D a
          corridorLen echoPos (resetK + 1) /\
        controlledWrapPairDistance corridorLen echoPos (resetK + 1) <
          controlledWrapPairDistance corridorLen echoPos resetK) := by
  dsimp only
  have hs := hstep initial current a corridorLen echoPos resetK
    hinv hk hopen
  rcases hs with hs | hs
  · exact Or.inl hs
  · exact Or.inr
      ⟨hs, controlledWrapPairDistance_reset_step hk⟩

/-- Distance-zero closing row: the no-birth branch has the exact requested
    terminal sanitation, including the ruler labels. -/
theorem collision_step_finishes
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hstep : ControlledWrapCollisionConsumerStepStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (initial current : FC n psi kappa tau) (a : Fin n)
    (corridorLen : Nat)
    (hinv : ControlledWrapInvariant hpsi ring initial current a
      corridorLen 0 corridorLen)
    (hopen :
      PreparedOrdinaryOpen hpsi
        (current (drainSite ring a corridorLen))
        (current (ring.rightNeighbor (drainSite ring a corridorLen))))
    (hpre : BirthShortDoneTerminalPassiveR4.RowPreCap2
      hpsi h2 kappa ring current (drainSite ring a corridorLen)) :
    let e := drainSite ring a corridorLen
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D \/
      (BirthShortDoneTerminalFirstHit.Leaderless D /\
        TripleLabels hpsi ring D a /\
        CorridorTerminated ring D a corridorLen /\
        ThreeSiteSanitized hpsi ring D a) := by
  exact hstep initial current a corridorLen hinv hopen hpre

/-- Exact strong-induction assembly theorem still to prove.  The deterministic
    branch choice is echo first, then reset, then collision.  Invariant closure
    supplies `Leaderless` and `TripleLabels` at every no-birth prefix; maximal
    geometry supplies support of each chosen edge. -/
def ControlledWrapStrongInductionStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ControlledWrapEchoConsumerStepStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring ->
  ControlledWrapResetConsumerStepStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring ->
  ControlledWrapCollisionConsumerStepStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring ->
  (forall (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen echoPos resetK : Nat),
    ControlledWrapInvariant hpsi ring initial current a
      corridorLen echoPos resetK ->
    ControlledWrapGateReady hpsi h2 ring current a
      corridorLen echoPos resetK) ->
  ControlledWrapAbsorptionFromInvariantStatement
    (kappa := kappa) (tau := tau) hpsi h2 ring

end BirthB1ControlledWrapGeneral

#print axioms BirthB1ControlledWrapGeneral.echo_step_ranked
#print axioms BirthB1ControlledWrapGeneral.reset_step_ranked
#print axioms BirthB1ControlledWrapGeneral.collision_step_finishes

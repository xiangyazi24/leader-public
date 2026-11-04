import Leader.PPL.ReachCPB.ForcingCapped
import Leader.PPL.ReachCPB.ModeCapped
import Leader.PPL.ReachCPB.MismatchCapped


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
# Lemma 16 mismatch completion: historical domain repair


The universal one-step carrier in ReachCPBMismatchCapped is too large:
it allows C0 to be arbitrary and the current LastReadyCapped/bad-border
window to be established only after a fresh lineage has already captured
source bits.


The actual Lemma-16 consumer is narrower.  Its mismatch phase starts from an
already LastReadyCapped configuration C and restarts the proof-only ghost as
initialGhost C.  The definitions below make that epoch visible.


A bare lower bound 0 <= birthStep is intentionally separated out first.  It is
vacuous and therefore cannot repair the old statement; the theorem
lemma16MismatchCompletionStepSpec_of_birthOnly below formalizes that fact.
-/


/-- The birthStep-only premise suggested by the counterexample diagnosis,
without tying the epoch to a configuration where the Detect window holds. -/
def Lemma16MismatchBirthOnlyHistory
    {n psi kappa : Nat}
    (kind : PPL.TokenKind)
    (k : Fin n)
    (G : PPL.GhostConfig n psi kappa) : Prop :=
  forall (i : Fin n) (z : PPL.GhostToken n psi) (t : Nat),
    PPL.ghostTokenAt kind G i = some z ->
    z.lmeta.id = .born kind t ->
    z.lmeta.birthSite = k ->
    0 <= z.lmeta.birthStep


theorem lemma16MismatchBirthOnlyHistory_trivial
    {n psi kappa : Nat}
    (kind : PPL.TokenKind)
    (k : Fin n)
    (G : PPL.GhostConfig n psi kappa) :
    Lemma16MismatchBirthOnlyHistory kind k G := by
  intro i z t howner hid hsite
  exact Nat.zero_le _


/-- Same old one-step shape plus only the vacuous birthStep lower bound.
This is included to record precisely why birthStep alone is not a repair. -/
def Lemma16MismatchCompletionStepSpecBirthOnly : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    Lemma16MismatchBirthOnlyHistory kind k G ->
    LastReadyCapped ring G.phys ->
    Lemma16BadBorderWitness ring G.phys b k kind ->
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
    Or
      (PPL.CPB ring G'.phys)
      (And
        (LastReadyCapped ring G'.phys)
        (And
          (Lemma16BadBorderWitness ring G'.phys b k kind)
          (forall m : PPL.LineageMeta n,
            m ∈ G'.completed ->
            PPL.FreshCompletion (psi := psi) kind k m ->
            m ∈ G.completed)))


/-- BirthStep-only implies the old false universal carrier, because its added
premise is true for every canonical or noncanonical ghost.  Consequently any
counterexample to Lemma16MismatchCompletionStepSpec is automatically a
counterexample to the birthStep-only variant. -/
theorem lemma16MismatchCompletionStepSpec_of_birthOnly
    (h : Lemma16MismatchCompletionStepSpecBirthOnly) :
    Lemma16MismatchCompletionStepSpec := by
  unfold Lemma16MismatchCompletionStepSpec
  intro n psi kappa hpsi hn3 ring C0 pre b k kind e
  dsimp only
  intro hready hbad
  exact
    h hpsi hn3 ring C0 pre b k kind e
      (lemma16MismatchBirthOnlyHistory_trivial
        kind k
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre))
      hready hbad


/-!
The actual historical premise.


epoch is a prefix length of the canonical ghost run.  At that prefix the
capped Detect/Last window must already hold.  Every live selected-colour
lineage born at the bad predecessor border k must have birthStep at or after
that epoch.  Initial lineages are deliberately irrelevant: FreshCompletion
requires a .born lineage.


The current endpoint hypotheses in the step spec still give LastReadyCapped
at pre.length.  Between the epoch and that endpoint, the existing capped
Detect persistence plus CPB closedness is the intended source-freeze
argument.
-/
def Lemma16MismatchLineageHistory
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (k : Fin n)
    (kind : PPL.TokenKind) : Prop :=
  exists epoch : Nat,
    And
      (epoch <= pre.length)
      (And
        (LastReadyCapped ring
          (PPL.ghostRun hpsi ring 0
            (PPL.initialGhost C0)
            (pre.take epoch)).phys)
        (forall (i : Fin n) (z : PPL.GhostToken n psi) (t : Nat),
          PPL.ghostTokenAt kind
              (PPL.ghostRun hpsi ring 0
                (PPL.initialGhost C0) pre) i =
            some z ->
          z.lmeta.id = .born kind t ->
          z.lmeta.birthSite = k ->
          epoch <= z.lmeta.birthStep))


/-- The actual Lemma-16 mismatch phase has a canonical history witness at
epoch zero, because it restarts initialGhost at an already LastReadyCapped
configuration.  This is the historical-premise producer missing from the
universal old step interface. -/
theorem lemma16MismatchLineageHistory_of_startReady
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (k : Fin n)
    (kind : PPL.TokenKind)
    (hstart : LastReadyCapped ring C0) :
    Lemma16MismatchLineageHistory
      hpsi ring C0 pre k kind := by
  refine ⟨0, Nat.zero_le _, ?_, ?_⟩
  · simpa [PPL.ghostRun] using
      (show LastReadyCapped ring (PPL.initialGhost C0).phys from hstart)
  · intro i z t howner hid hsite
    exact Nat.zero_le _


def Lemma16MismatchLineageHistoryProducer : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (k : Fin n)
    (kind : PPL.TokenKind),
    LastReadyCapped ring C0 ->
      Lemma16MismatchLineageHistory
        hpsi ring C0 pre k kind


theorem lemma16MismatchLineageHistoryProducer_proved :
    Lemma16MismatchLineageHistoryProducer := by
  intro n psi kappa hpsi ring C0 pre k kind hstart
  exact
    lemma16MismatchLineageHistory_of_startReady
      hpsi ring C0 pre k kind hstart


/-- Corrected one-step interface.  The transition conclusion is unchanged;
the sole semantic change is the explicit historical premise. -/
def Lemma16MismatchCompletionStepSpecHist : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    Lemma16MismatchLineageHistory
        hpsi ring C0 pre k kind ->
    LastReadyCapped ring G.phys ->
    Lemma16BadBorderWitness ring G.phys b k kind ->
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
    Or
      (PPL.CPB ring G'.phys)
      (And
        (LastReadyCapped ring G'.phys)
        (And
          (Lemma16BadBorderWitness ring G'.phys b k kind)
          (forall m : PPL.LineageMeta n,
            m ∈ G'.completed ->
            PPL.FreshCompletion (psi := psi) kind k m ->
            m ∈ G.completed)))


/-- Sanity adapter: the old unrestricted step theorem, if it existed, would
immediately imply the historical one. -/
theorem lemma16MismatchCompletionStepSpecHist_of_unrestricted
    (h : Lemma16MismatchCompletionStepSpec) :
    Lemma16MismatchCompletionStepSpecHist := by
  unfold Lemma16MismatchCompletionStepSpecHist
  intro n psi kappa hpsi hn3 ring C0 pre b k kind e
  dsimp only
  intro hhistory hready hbad
  exact h hpsi hn3 ring C0 pre b k kind e hready hbad


/-!
Phase-level bridge required by the assembly.


ReachCPBMismatchCapped currently proves this bridge privately for the old
unrestricted step spec.  The replacement proof should replay exactly that
suffix induction, but at every recursive prefix obtain
Lemma16MismatchLineageHistory from the phase-start LastReadyCapped witness
using the producer above before invoking the Hist step.
-/
def Lemma16MismatchCompletionHistToWitness : Prop :=
  Lemma16MismatchLineageHistoryProducer ->
  Lemma16MismatchCompletionStepSpecHist ->
  Lemma16MismatchWitnessCappedSpec


/-- New top-level assembly shape.  No existing file is edited: once the
historical mismatch phase bridge is supplied, all other capped Lemma-16
producers are exactly the current ones. -/
theorem lemma16_wordBound_of_steps_hist
    (hDetect : Lemma16DetectPersistenceCappedStepSpec)
    (hDist : Lemma16DistForcingCappedStepSpec)
    (hLast : Lemma16LastForcingCappedStepSpec)
    (hMode : ModeScrubOneStepSpec)
    (hMismatch : Lemma16MismatchCompletionStepSpecHist)
    (hMismatchPhase : Lemma16MismatchCompletionHistToWitness)
    (hGeometry : Lemma16CdGeometryPairStepSpec)
    (h15 : Lemma16BulletSweepNatBound)
    (hcore : PPL.lemma4_deterministic_core)
    {n psi kappa modeC : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= modeC)
    (hkappa : kappa = 8 * modeC * psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= lemma16K n)
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    Lemma16WordBound ring C := by
  exact
    lemma16_wordBound_capped
      h15
      (lemma16DetectPersistenceCapped hDetect)
      (lemma16ModeCappedReachCount hMode)
      (lemma16DistForcingCapped hDist)
      (lemma16LastForcingCapped hLast)
      (hMismatchPhase
        lemma16MismatchLineageHistoryProducer_proved
        hMismatch)
      (lemma16CdTraceUntilSuccess_proved hGeometry)
      hcore hn3 hpsi hc hkappa hnpow hpsiK ring C


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16MismatchBirthOnlyHistory_trivial
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchCompletionStepSpec_of_birthOnly
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchLineageHistory_of_startReady
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchLineageHistoryProducer_proved
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchCompletionStepSpecHist_of_unrestricted
#print axioms PPL.Convergence.ReachCPB.lemma16_wordBound_of_steps_hist



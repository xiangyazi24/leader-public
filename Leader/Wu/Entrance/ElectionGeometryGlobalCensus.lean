import Leader.Wu.Coherence.LabelPreservation
import Leader.Wu.Coherence.CarrierSimulationComponents
import Leader.Wu.Entrance.AdmissionCollarClear

set_option autoImplicit false
set_option Elab.async false

namespace ElectionGeometryGlobalCensus

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open R2CoherenceV31 R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31FinalSimulation5 R2CoherenceV31FinalSimulation
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi kappa tau : Nat}

/-- A V3.1 edge is a remaining repairable barrier when it is not already
root-entering/successor and its responder is still a follower. -/
def RepairableBarrierAtV31
    (ring : DirectedRing n) (C : FC n psi kappa tau) (i : Fin n) : Prop :=
  passiveEdgeOKV3 (C i) (C (ring.rightNeighbor i)) = false ∧
    (raw (C (ring.rightNeighbor i))).leader = false

/-- Weak ring-wide geometry of the physical barrier-moving phase. -/
def BarrierTolerantGeometryV31
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  ∀ i : Fin n,
    passiveEdgeOKV3 (C i) (C (ring.rightNeighbor i)) = true ∨
      RepairableBarrierAtV31 ring C i

/-- Election geometry is exactly the barrier-tolerant profile after all
repairable barriers have disappeared. -/
theorem electionGeometry_of_barrierTolerant_noRepairable
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hTol : BarrierTolerantGeometryV31 ring C)
    (hNo : ∀ i : Fin n, ¬ RepairableBarrierAtV31 ring C i) :
    ElectionGeometryV31 ring C := by
  intro i
  rcases hTol i with hGood | hBarrier
  · exact hGood
  · exact (hNo i hBarrier).elim

/-- V3.1 preserves the good/bad status of every label edge because it never
changes labels. In particular it cannot consume a remaining barrier. -/
theorem passiveEdgeOKV3_step_eq
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e i : Fin n) :
    passiveEdgeOKV3
        (stepV3 hpsi h2 ring C e i)
        (stepV3 hpsi h2 ring C e (ring.rightNeighbor i)) =
      passiveEdgeOKV3 (C i) (C (ring.rightNeighbor i)) := by
  have hLab := stepV3_labels_eq_or_held hpsi h2 ring C e
  unfold passiveEdgeOKV3 at *
  unfold atRootB successorB
  rw [hLab i, hLab (ring.rightNeighbor i)]

/-- Hence a barrier present when V3.1 starts is still a barrier after one
V3.1 scheduler letter. -/
theorem barrier_persists_one_stepV31
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e i : Fin n)
    (hBad : passiveEdgeOKV3 (C i) (C (ring.rightNeighbor i)) = false) :
    passiveEdgeOKV3
        (stepV3 hpsi h2 ring C e i)
        (stepV3 hpsi h2 ring C e (ring.rightNeighbor i)) = false := by
  rw [passiveEdgeOKV3_step_eq hpsi h2 ring C e i]
  exact hBad

/-- Producer theorem that should replace the current admitted geometry leaf.
It says the physical producer has finished moving all barriers before the
final open/leaderless V3.1 handoff. -/
def FinalAdmissionAllBarriersDischargedV31
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi kappa tau,
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C → FinalAllOpen C →
      BarrierTolerantGeometryV31 ring (liftFinalV31 C) ∧
      (∀ i : Fin n,
        ¬ RepairableBarrierAtV31 ring (liftFinalV31 C) i)

/-- The producer theorem discharges the existing C1 geometry residual with no
change to the V3.1 mission payload. -/
theorem c1ElectionGeometry_of_allBarriersDischarged
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (h : FinalAdmissionAllBarriersDischargedV31
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31AdmittedElectionGeometryResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C hA hL hOpen
  rcases h C hA hL hOpen with ⟨hTol, hNo⟩
  exact electionGeometry_of_barrierTolerant_noRepairable
    ring (liftFinalV31 C) hTol hNo

end ElectionGeometryGlobalCensus

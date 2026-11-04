import Leader.Wu.Entrance.BarrierDischargeStatement
import Leader.Wu.Entrance.PassiveInputNeutralProjection
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe


set_option autoImplicit false
set_option Elab.async false


namespace BarrierDischargeTruth


open R2CoherenceV31 R2CoherenceV31Closure
open R2CoherenceV31FinalSimulation
open R2CoherenceV31FinalSimulation5
open BarrierDischargeCensus
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open B9ControllerRecovery
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceTableV10g
open B9FullCarrierHost
open B9SpliceV10ePhysicalHoldNoBirth
open Q11593SpliceControllerDesign


variable {n psi kappa tau : Nat}


private theorem modularMismatch_of_badEdge
    (hpsi : 0 < psi)
    (l r : R2CoherenceV31.Cell psi kappa tau)
    (hbad : passiveEdgeOKV3 l r = false) :
    (raw r).label ≠
      ⟨((raw l).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  intro hmod
  have hv := congrArg Fin.val hmod
  by_cases hr0 : (raw r).label.val = 0
  · have hgood : passiveEdgeOKV3 l r = true := by
      simp [passiveEdgeOKV3, atRootB, hr0]
    rw [hgood] at hbad
    cases hbad
  · have hle : (raw l).label.val + 1 ≤ psi :=
      Nat.succ_le_of_lt (raw l).label.isLt
    have hlt : (raw l).label.val + 1 < psi := by
      refine Classical.byContradiction ?_
      intro hn
      have heq : (raw l).label.val + 1 = psi := by
        omega
      have hz : (raw r).label.val = 0 := by
        simpa [heq] using hv
      exact hr0 hz
    have hs : (raw r).label.val = (raw l).label.val + 1 := by
      simpa [Nat.mod_eq_of_lt hlt] using hv
    have hgood : passiveEdgeOKV3 l r = true := by
      simp [passiveEdgeOKV3, successorB, hs]
    rw [hgood] at hbad
    cases hbad


private theorem noPairCovered_of_neutral
    (l r : FinalCandidateR2C.Cell psi kappa tau)
    (hl : NeutralController l) (hr : NeutralController r) :
    ¬ PairCovered (oldCell l) (oldCell r) := by
  rcases hl with ⟨hlRole, hlPending, hlTicket⟩
  rcases hr with ⟨hrRole, hrPending, hrTicket⟩
  simp [PairCovered, Pending, oldCell, B9FullCarrierHost.toOld,
    B9SpliceControllerR1Table.role, HostFenceShapeV7,
    ReservedFrontHoldGuard, PendingOwnerHoldShapeV7,
    hlRole, hlPending, hlTicket, hrRole, hrPending, hrTicket]


private theorem badEdge_impossible_of_admitted
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := kappa) (τ := tau) hpsi h2)
    (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C)
    (hL : FinalLeaderless C)
    (hbad : passiveEdgeOKV3
      (liftFinalV31 C e)
      (liftFinalV31 C (ring.rightNeighbor e)) = false) : False := by
  let j := ring.rightNeighbor e
  have hNeutral := concreteB7PassiveInputOuterNeutral_of_selector
    hpsi h2 ring hS C hA hL
  have hmod := modularMismatch_of_badEdge hpsi
    (liftFinalV31 C e) (liftFinalV31 C j) (by simpa [j] using hbad)
  change
    ((oldConfig C) j).carrier.splice.base.core.core.label ≠
      ⟨(((oldConfig C) e).carrier.splice.base.core.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ at hmod
  have hle :
      ((oldConfig C) e).carrier.splice.base.core.core.leader = false := by
    change outputFinal (C e) = false
    exact hL e
  have hlr :
      ((oldConfig C) j).carrier.splice.base.core.core.leader = false := by
    change outputFinal (C j) = false
    exact hL j
  have hDanger : PreparedDangerAt hpsi ring
      (B9SpliceControllerR1TableV6.projectV6 (oldConfig C)) e :=
    (B9SpliceV10ePhysicalHoldNoBirth.danger_iff_physical
      hpsi ring (oldConfig C) e).2 ⟨hle, hlr, by simpa [j] using hmod⟩
  have hLocal : LocalDanger hpsi (oldCell (C e)) (oldCell (C j)) := by
    change LocalDanger hpsi ((oldConfig C) e) ((oldConfig C) j)
    change PreparedDangerAt hpsi ring
      (B9SpliceControllerR1TableV6.projectV6 (oldConfig C)) e
    exact hDanger
  have hNoCover : ¬ PairCovered (oldCell (C e)) (oldCell (C j)) :=
    noPairCovered_of_neutral (C e) (C j) (hNeutral e) (hNeutral j)
  have hHole : FinalHole hpsi (C e) (C j) := by
    change Hole hpsi (oldCell (C e)) (oldCell (C j))
    exact ⟨hLocal, hNoCover⟩
  have hNoGarbage := (hA.2.2.2 e).1
  apply hNoGarbage
  change Garbage hpsi (oldCell (C e)) (oldCell (C j))
  exact Or.inr hHole


theorem concreteAdmissionBadEdgeForcesRelabelV31_holds
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := kappa) (τ := tau) hpsi h2) :
    ConcreteAdmissionBadEdgeForcesRelabelV31
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C e hA hL hbad
  exact (badEdge_impossible_of_admitted
    hpsi h2 ring hS C e hA hL hbad).elim


theorem c1ElectionGeometry_of_admitted
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := kappa) (τ := tau) hpsi h2) :
    C1FinalV31AdmittedElectionGeometryResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  exact c1Geometry_of_badEdgeForcesRelabel hpsi h2 ring
    (concreteAdmissionBadEdgeForcesRelabelV31_holds
      (kappa := kappa) (tau := tau) hpsi h2 ring hS)



end BarrierDischargeTruth

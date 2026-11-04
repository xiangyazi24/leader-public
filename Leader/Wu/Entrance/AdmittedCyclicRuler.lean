import Leader.Wu.Entrance.AdmittedElectionGeometry
import Leader.Wu.Entrance.CyclicRulerRootSpacing
import Leader.Wu.Coherence.ReachableSoundParametric

set_option autoImplicit false
set_option Elab.async false

namespace BarrierDischargeTruth2

open R2CoherenceV31 R2CoherenceV31Closure
open R2CoherenceV31FinalSimulation
open R2CoherenceV31FinalSimulation4
open R2CoherenceV31FinalSimulation5
open R2CoherenceV31ReachableRootSpacing
open BarrierDischargeTruth
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open B9ControllerRecovery
open B9SpliceControllerR1Table B9SpliceControllerR1TableV6
open CFinalJ2Ruler
open Q11593SpliceControllerDesign
open B9SpliceControllerR1TableV7
open B9SpliceControllerR1TableV2
open B9SpliceTableV10g

variable {n psi kappa tau : Nat}

/-- Generic form of CFinalJ2Ruler.CyclicRulerV31. -/
def AdmittedCyclicRulerV31
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n psi kappa tau) : Prop :=
  forall a : Fin n,
    (raw (C (ring.rightNeighbor a))).label =
      ⟨((raw (C a)).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩

private theorem noPairCovered_of_neutral2
    (l r : FinalCandidateR2C.Cell psi kappa tau)
    (hl : NeutralController l) (hr : NeutralController r) :
    ¬ PairCovered (oldCell l) (oldCell r) := by
  rcases hl with ⟨hlRole, hlPending, hlTicket⟩
  rcases hr with ⟨hrRole, hrPending, hrTicket⟩
  simp [PairCovered, Pending, oldCell, B9FullCarrierHost.toOld,
    B9SpliceControllerR1Table.role, HostFenceShapeV7,
    ReservedFrontHoldGuard, PendingOwnerHoldShapeV7,
    hlRole, hlPending, hlTicket, hrRole, hrPending, hrTicket]

theorem admittedCyclicRuler_of_noGarbage
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := kappa) (τ := tau) hpsi h2)
    (C : FinalCandidateR2C.Config n psi kappa tau)
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C)
    (hL : FinalLeaderless C) :
    AdmittedCyclicRulerV31 hpsi ring (liftFinalV31 C) := by
  intro a
  apply Fin.ext
  refine Classical.byContradiction ?_
  intro hne
  have hNeutral := concreteB7PassiveInputOuterNeutral_of_selector
    hpsi h2 ring hS C hA hL
  have hPhys :
      ((oldConfig C) a).carrier.splice.base.core.core.leader = false ∧
      ((oldConfig C) (ring.rightNeighbor a)).carrier.splice.base.core.core.leader = false ∧
      ((oldConfig C) (ring.rightNeighbor a)).carrier.splice.base.core.core.label ≠
        ⟨(((oldConfig C) a).carrier.splice.base.core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · change outputFinal (C a) = false
      exact hL a
    · change outputFinal (C (ring.rightNeighbor a)) = false
      exact hL (ring.rightNeighbor a)
    · intro heq
      apply hne
      exact congrArg Fin.val heq
  have hDanger : PreparedDangerAt hpsi ring
      (B9SpliceControllerR1TableV6.projectV6 (oldConfig C)) a :=
    (B9SpliceV10ePhysicalHoldNoBirth.danger_iff_physical
      hpsi ring (oldConfig C) a).2 hPhys
  have hLocal : LocalDanger hpsi
      (oldCell (C a)) (oldCell (C (ring.rightNeighbor a))) := by
    change LocalDanger hpsi
      ((oldConfig C) a) ((oldConfig C) (ring.rightNeighbor a))
    -- `preparedR1 hpsi c` is definitionally `prepared hpsi c.splice`, so the two
    -- danger interfaces are the same proposition at different abstraction
    -- levels.  Change to the prepared-level proposition rather than trying to
    -- reconcile them with a simp set, as the sibling theorem in
    -- `BarrierDischargeTruth` already does.
    change PreparedDangerAt hpsi ring
      (B9SpliceControllerR1TableV6.projectV6 (oldConfig C)) a
    exact hDanger
  have hNoCover :
      ¬ PairCovered (oldCell (C a))
        (oldCell (C (ring.rightNeighbor a))) :=
    noPairCovered_of_neutral2
      (C a) (C (ring.rightNeighbor a))
      (hNeutral a) (hNeutral (ring.rightNeighbor a))
  have hHole : FinalHole hpsi (C a) (C (ring.rightNeighbor a)) := by
    change Hole hpsi (oldCell (C a)) (oldCell (C (ring.rightNeighbor a)))
    exact ⟨hLocal, hNoCover⟩
  have hNG := (hA.2.2.2 a).1
  apply hNG
  change Garbage hpsi (oldCell (C a)) (oldCell (C (ring.rightNeighbor a)))
  exact Or.inr hHole

/-- Pure arithmetic bridge.  This is the reverse direction missing from
CFinalJ2Ruler: a full modular cyclic ruler fixes every computed ψ-window. -/
def CyclicRulerImpliesRootSpacingV31
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  forall C : R2CoherenceV31.FC n psi kappa tau,
    AdmittedCyclicRulerV31 hpsi ring C -> RootSpacingV31 ring C

theorem admittedLabelProfile_of_noGarbage
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := kappa) (τ := tau) hpsi h2)
    (hArithmetic : CyclicRulerImpliesRootSpacingV31
      (kappa := kappa) (tau := tau) hpsi ring) :
    C1FinalV31AdmittedLabelProfileResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C hA hL _hOpen
  exact hArithmetic (liftFinalV31 C)
    (admittedCyclicRuler_of_noGarbage
      hpsi h2 ring hS C hA hL)

/-- Exact remaining entrance-state leaf.  With open/none controls there is no
PrefixDead escape, so every live `.equal` must be intrinsically fresh. -/
def C1FinalV31AdmittedEqualFreshResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  forall C : FinalCandidateR2C.Config n psi kappa tau,
    ConcreteB7AdmittedPassive hpsi h2 ring C ->
    FinalLeaderless C -> FinalAllOpen C ->
    forall i : Fin n,
      (raw (liftFinalV31 C i)).state = .equal ->
      forall k : Fin ((raw (liftFinalV31 C i)).label.val + 1),
        R2Coherence.freshComponent
          (eraseCellV3
            (liftFinalV31 C
              (R2Coherence.prefixPos ring (eraseCfgV3 (liftFinalV31 C))
                i k.val))) k.val

/-- Equal-prefix freshness is sufficient for the admitted coherence residual.
The proof deliberately chooses the freshness disjunct; no PrefixDead witness
can be manufactured from the openInit controller. -/
theorem admittedCoherentPrefixes_of_equalFresh
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hFresh : C1FinalV31AdmittedEqualFreshResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31AdmittedCoherentPrefixesResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C hA hL hOpen i
  unfold R2Coherence.FreshEqualPrefix
  intro heq
  right
  exact hFresh C hA hL hOpen i heq



theorem c1FinalV31AdmittedClosedResidual_of_admission
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := kappa) (τ := tau) hpsi h2)
    (hFresh : C1FinalV31AdmittedEqualFreshResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hPhase : C1FinalV31AdmittedReachablePhaseResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31AdmittedClosedResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  exact c1FinalV31AdmittedClosedResidual_of_components
    (kappa := kappa) (tau := tau) hpsi h2 ring
    (BarrierDischargeTruth.c1ElectionGeometry_of_admitted
      (kappa := kappa) (tau := tau) hpsi h2 ring hS)
    (admittedCoherentPrefixes_of_equalFresh
      (kappa := kappa) (tau := tau) hpsi h2 ring hFresh)
    hPhase




end BarrierDischargeTruth2

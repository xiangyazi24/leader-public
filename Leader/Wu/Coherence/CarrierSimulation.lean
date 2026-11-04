import Leader.Wu.Coherence.CarrierViewGate
import Leader.Wu.Entrance.PassiveWord


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace R2CoherenceV31FinalSimulation


open BirthLeaderlessBirthMassRenewal
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C


variable {n psi kappa tau : Nat}


/-- Proof-side erasure of a V3.1 configuration. -/
def eraseFinalV31
    (Q : R2CoherenceV31.FC n psi kappa tau) :
    R2Coherence.FC n psi kappa tau :=
  R2CoherenceV31.eraseCfgV3 Q


/-- Canonical final-state lift used by the installed C1 gate. -/
def liftFinalV31
    (C : FinalCandidateR2C.Config n psi kappa tau) :
    R2CoherenceV31.FC n psi kappa tau :=
  R2CoherenceV31MissionGate.finalV31View C


/-- On the final admission side the old R2C controls are open/none, so
canonical V3.1 lift followed by erasure recovers the R2C physical view. -/
theorem eraseFinalV31_liftFinalV31_of_allOpen
    (C : FinalCandidateR2C.Config n psi kappa tau)
    (hOpen : FinalAllOpen C) :
    eraseFinalV31 (liftFinalV31 C) = physicalConfig C := by
  funext i
  rcases hOpen i with ⟨hm, ht⟩
  change
    (⟨(C i).phys.phys, ⟨.open, .none⟩⟩ :
      R2Coherence.Cell psi kappa tau) = (C i).phys
  cases hcell : (C i).phys with
  | mk p ctl =>
      cases hctl : ctl with
      | mk m t =>
          simp only [hcell, hctl] at hm ht ⊢
          cases hm
          cases ht
          rfl


/-- FIRST MISMATCH: passive final admission does not currently prove that
V3.1's CHECK-ready sanitizer is the identity on the served R2 endpoints. -/
def C1FinalV31SanitizeReadyResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    let D := R2Coherence.project (physicalConfig C)
    R2CoherenceBranches.sanitizeReadyPhys (D e) = D e ∧
      R2CoherenceBranches.sanitizeReadyPhys
        (D (ring.rightNeighbor e)) = D (ring.rightNeighbor e)


/-- Exact one-letter upgrade still missing after the first mismatch above.
This is intentionally a named residual, not an asserted theorem. -/
def C1FinalV31OneStepSimulationResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    liftFinalV31
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e) =
      R2CoherenceV31.stepV3 hpsi h2 ring (liftFinalV31 C) e


/-- The other clause already built into `C1FinalV31SimulationObligation`:
the current final state must have a V3.1 trace from the mission entrance. -/
def C1FinalV31EntranceReachabilityResidual
    (BirthEntrance : R2CoherenceV31.FC n psi kappa tau → Prop)
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi kappa tau,
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C →
    FinalAllOpen C →
    ∃ Q : R2CoherenceV31.FC n psi kappa tau,
      ∃ pre : List (Fin n),
        BirthEntrance Q ∧
          liftFinalV31 C =
            pre.foldl (R2CoherenceV31.stepV3 hpsi h2 ring) Q



private theorem liftFinalV31_foldl_of_stepSimulation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := kappa) (τ := tau) hpsi h2 ring)
    (hStep : C1FinalV31OneStepSimulationResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (C : FinalCandidateR2C.Config n psi kappa tau)
    (w : List (Fin n))
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C)
    (hAlive : AliveAlong
      (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
      FinalLeaderless C w) :
    liftFinalV31
        (w.foldl
          (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring) C) =
      w.foldl (R2CoherenceV31.stepV3 hpsi h2 ring)
        (liftFinalV31 C) := by
  induction w generalizing C with
  | nil => rfl
  | cons e rest ih =>
      have hCur : FinalLeaderless C := hAlive.1
      have hTail : AliveAlong
          (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
          FinalLeaderless
          (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e)
          rest := hAlive.2
      have hNextL : FinalLeaderless
          (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e) :=
        aliveAlong_good hTail
      have hNext := hClosed C e hA hCur
      have hA' : ConcreteB7AdmittedPassive hpsi h2 ring
          (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e) := by
        rcases hNext with hLeader | hAdm
        · rcases hLeader with ⟨i, hi⟩
          have hz := hNextL i
          rw [hz] at hi
          cases hi
        · exact hAdm
      have hRest := ih
        (C := stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e)
        hA' hTail
      have hOne := hStep C e hA
      simp only [List.foldl_cons]
      rw [hRest, hOne]


/-- Pure wiring: entrance reachability plus passive closure plus the exact
one-letter residual imply the installed full-word C1 simulation obligation. -/
theorem c1FinalV31SimulationObligation_of_stepSimulation
    (BirthEntrance : R2CoherenceV31.FC n psi kappa tau → Prop)
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hReach : C1FinalV31EntranceReachabilityResidual
      (kappa := kappa) (tau := tau) BirthEntrance hpsi h2 ring)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := kappa) (τ := tau) hpsi h2 ring)
    (hStep : C1FinalV31OneStepSimulationResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    R2CoherenceV31MissionGate.C1FinalV31SimulationObligation
      BirthEntrance hpsi h2 ring := by
  intro C w hA hLeaderless hOpen hAlive
  rcases hReach C hA hLeaderless hOpen with
    ⟨Q, pre, hBirth, hStart⟩
  refine ⟨Q, pre, hBirth, ?_, ?_⟩
  · simpa only [liftFinalV31] using hStart
  · have hWord := liftFinalV31_foldl_of_stepSimulation
      hpsi h2 ring hClosed hStep C w hA hAlive
    simpa only [liftFinalV31] using hWord


end R2CoherenceV31FinalSimulation

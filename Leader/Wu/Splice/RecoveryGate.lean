import Leader.Wu.Entrance.ComposedRow
import Leader.Wu.Entrance.ConcretePort
import Leader.Wu.Entrance.PassiveAdmission
import Leader.Wu.Splice.ControllerRecoveryMass
import Leader.Wu.Splice.RiskControllerProjection
import Leader.Wu.Splice.RiskLeafIdentification

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9RecoveryGate

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi kappa tau : Nat}

/-- The C2 source lane after producer retirement: writer-passive and leaderless. -/
def C2PassiveLeaderless (C : Config n psi kappa tau) : Prop :=
  FinalNoProducer C ∧ FinalWriterPassive C ∧ FinalLeaderless C

/-- The accepted old-carrier recovery inequality, specialized to the R1 host. -/
def C2OldRecoveryMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n psi kappa tau) : Prop :=
  let host := B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2
  let H := B9ControllerRecovery.RecoveryB n
  let Q := B9ControllerRecovery.RecoveryQ n
  Q * avoidCount (B9ControllerRecovery.stepRecover host hpsi ring)
      (fun _ : B9SpliceTableHost.Config n psi kappa tau => True)
      (B9ControllerRecovery.RecoveryTarget hpsi ring) C H ≤
    (Q - 1) * n ^ H

/-- J3's desired result: the same recovery mass on the frozen final step. -/
def C2FinalRecoveryMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Prop :=
  let H := B9ControllerRecovery.RecoveryB n
  let Q := B9ControllerRecovery.RecoveryQ n
  Q * avoidCount
      (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
      (fun _ : Config n psi kappa tau => True)
      (FinalRecoveryTarget hpsi ring) C H ≤
    (Q - 1) * n ^ H

/-- B7 failure currency at the C2 constants. -/
def C2FinalAliveMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Prop :=
  let H := B9ControllerRecovery.RecoveryB n
  let Q := B9ControllerRecovery.RecoveryQ n
  Q * aliveCount
      (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
      FinalLeaderless C H ≤
    (Q - 1) * n ^ H

/-- The literally matching `B7ComposedMassObligation` currency. -/
def C2FinalHasLeaderAvoidMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Prop :=
  let H := B9ControllerRecovery.RecoveryB n
  let Q := B9ControllerRecovery.RecoveryQ n
  Q * avoidCount
      (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
      (fun _ : Config n psi kappa tau => True) HasLeader C H ≤
    (Q - 1) * n ^ H

/-- Public local copy of the target bridge that is private on the broken
`FullRowPortFaithful` path. -/
theorem finalRecoveryTarget_iff_oldConfig
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) :
    FinalRecoveryTarget hpsi ring C ↔
      B9ControllerRecovery.RecoveryTarget hpsi ring
        (FinalCandidateR2C.FinalCandidateR2C.oldConfig C) := by
  constructor
  · rintro (hS | hN)
    · exact Or.inl hS
    · right
      intro i
      exact hN i
  · rintro (hS | hN)
    · exact Or.inl hS
    · right
      intro i
      exact hN i

/-- `stepConcrete` is `stepFinal` at `concretePort`, so the compiled final B7
currency theorem applies verbatim. -/
theorem stepConcrete_aliveCount_eq_avoidCount_hasLeader
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (T : Nat) :
    aliveCount
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
        FinalLeaderless C T =
      avoidCount
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
        (fun _ : Config n psi kappa tau => True) HasLeader C T := by
  simpa only [stepConcrete] using
    (aliveCount_finalLeaderless_eq_avoidCount_hasLeader
      hpsi h2 (concretePort (κ := kappa) (τ := tau) hpsi h2)
      ring C T)

/-- Direct packaging of the accepted Q=RecoveryQ, H=RecoveryB theorem. -/
theorem accepted_old_recovery_mass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n psi kappa tau) :
    C2OldRecoveryMass hpsi h2 ring C := by
  unfold C2OldRecoveryMass
  dsimp only
  exact B9ControllerRecovery.recovery_first_hit_mass
    (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
    hpsi ring C


/-- J3 from the census: transport old `stepRecover` mass to the exact final
`stepConcrete` recovery event.  The two currently-open risk refinements are
part of the seam rather than silently assumed. -/
def C2J3OldToFinalRecoveryMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀
    (hHold : B9RiskRefinement2C.HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2) hpsi)
    (hCompletion : B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause)
    (C : Config n psi kappa tau),
    C2PassiveLeaderless C →
    C2OldRecoveryMass hpsi h2 ring
      (FinalCandidateR2C.FinalCandidateR2C.oldConfig C) →
    C2FinalRecoveryMass hpsi h2 ring C

/-- J4 from the census: recovery success must land/drain into the passive B7
lane strongly enough that the calibrated recovery mass becomes leaderless
failure mass without changing H or Q.  This is deliberately a mass statement,
not the false state-level identification of the two targets. -/
def C2J4RecoveryToB7Mass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : Config n psi kappa tau,
    C2PassiveLeaderless C →
    C2FinalRecoveryMass hpsi h2 ring C →
    C2FinalAliveMass hpsi h2 ring C

/-- Exact outstanding C2 assembly seam J3 ∧ J4. -/
def C2RecoveryJ3J4Join
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  C2J3OldToFinalRecoveryMass
      (kappa := kappa) (tau := tau) hpsi h2 ring ∧
    C2J4RecoveryToB7Mass
      (kappa := kappa) (tau := tau) hpsi h2 ring

/-- C2 on the final carrier.  It records both open risk-refinement hypotheses,
the recovery first-hit inequality on `stepConcrete`, and the same inequality in
the two equivalent B7 failure currencies. -/
def C2RecoveryGate
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  B9RiskRefinement2C.HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2) hpsi ∧
    B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause ∧
    ∀ C : Config n psi kappa tau,
      C2PassiveLeaderless C →
      C2FinalRecoveryMass hpsi h2 ring C ∧
        C2FinalAliveMass hpsi h2 ring C ∧
        C2FinalHasLeaderAvoidMass hpsi h2 ring C

/-- The accepted old mass closes everything except the explicitly named J3/J4
join.  The final equality is the compiled B7 currency bridge. -/
theorem c2RecoveryGate_of_mass_and_refinement
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hHold : B9RiskRefinement2C.HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2) hpsi)
    (hCompletion : B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause)
    (hJoin : C2RecoveryJ3J4Join
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C2RecoveryGate (kappa := kappa) (tau := tau) hpsi h2 ring := by
  refine ⟨hHold, hCompletion, ?_⟩
  intro C hPassive
  have hOld :
      C2OldRecoveryMass hpsi h2 ring
        (FinalCandidateR2C.FinalCandidateR2C.oldConfig C) :=
    accepted_old_recovery_mass hpsi h2 ring
      (FinalCandidateR2C.FinalCandidateR2C.oldConfig C)
  have hRecovery : C2FinalRecoveryMass hpsi h2 ring C :=
    hJoin.1 hHold hCompletion C hPassive hOld
  have hAlive : C2FinalAliveMass hpsi h2 ring C :=
    hJoin.2 C hPassive hRecovery
  refine ⟨hRecovery, hAlive, ?_⟩
  unfold C2FinalAliveMass at hAlive
  unfold C2FinalHasLeaderAvoidMass
  dsimp only at hAlive ⊢
  rw [← stepConcrete_aliveCount_eq_avoidCount_hasLeader
    hpsi h2 ring C (B9ControllerRecovery.RecoveryB n)]
  exact hAlive

end B9RecoveryGate

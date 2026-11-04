import Leader.Wu.Coherence.CarrierSimulation


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace R2CoherenceV31FinalSimulation2


open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open R2CoherenceV31FinalSimulation
open B9Host B9FullCarrierHost


variable {n psi kappa tau : Nat}


def finalR2View
    (C : FinalCandidateR2C.Config n psi kappa tau) :
    R2.FC n psi kappa tau :=
  R2Coherence.project (physicalConfig C)


/-- The sanitizer residual makes the two proposals identical. -/
theorem proposalV3_lift_eq_r2_of_sanitize
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hSan : C1FinalV31SanitizeReadyResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C) :
    let D := finalR2View C
    R2CoherenceV31.proposalV3 hpsi (by decide : 0 < 2) h2
        (liftFinalV31 C e) (liftFinalV31 C (ring.rightNeighbor e)) =
      R2.row hpsi (by decide : 0 < 2) h2
        (D e) (D (ring.rightNeighbor e)) := by
  have hs := hSan C e hA
  dsimp only at hs
  change R2.row hpsi (by decide : 0 < 2) h2
      (R2CoherenceBranches.sanitizeReadyPhys
        ((R2Coherence.project (physicalConfig C)) e))
      (R2CoherenceBranches.sanitizeReadyPhys
        ((R2Coherence.project (physicalConfig C))
          (ring.rightNeighbor e))) =
    R2.row hpsi (by decide : 0 < 2) h2
      ((R2Coherence.project (physicalConfig C)) e)
      ((R2Coherence.project (physicalConfig C)) (ring.rightNeighbor e))
  rw [hs.1, hs.2]


/-- FIRST NEW PER-ARM MISMATCH after the sanitizer seam. -/
def C1FinalV31PathStableResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    let D := finalR2View C
    let q := R2.row hpsi (by decide : 0 < 2) h2
      (D e) (D (ring.rightNeighbor e))
    R2CoherenceV31.pairPathChangesV3
      (D e) (D (ring.rightNeighbor e)) q.1 q.2 = false


/-- Exact local wrapper seam.  On lifted open/none controls this says the V3.1
service is the same bare-R2 service as the final physical projection. -/
def C1FinalV31OpenArmResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    R2CoherenceV31.stepV3 hpsi h2 ring (liftFinalV31 C) e =
      R2CoherenceV31Entrance.openInitV31
        (R2.step hpsi h2 ring (finalR2View C) e)



private theorem rightNeighbor_ne_of_two
    (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem physicalConfig_stepConcrete_of_passive_admitted_local
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C) :
    physicalConfig
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e) =
      R2Coherence.step hpsi h2 ring (physicalConfig C) e := by
  classical
  have hs := rightNeighbor_ne_of_two ring hn e
  have hedge := hA.2.2.2 e
  have hg := hedge.1
  have ha :
      (concretePort (κ := kappa) (τ := tau) hpsi h2).action
          (C e) (C (ring.rightNeighbor e)) = .host := by
    simpa only [concretePort, concretePortLocal] using hedge.2.1
  have hf : FinalCandidateR2C.FinalCandidateR2C.finalAction hpsi h2
      (concretePort (κ := kappa) (τ := tau) hpsi h2)
      (C e) (C (ring.rightNeighbor e)) =
        FinalCandidateR2C.FinalCandidateR2C.FinalAction.host := by
    unfold FinalCandidateR2C.FinalCandidateR2C.finalAction
    rw [if_neg hg, ha]
  have hrow : rowFinal hpsi h2
      (concretePort (κ := kappa) (τ := tau) hpsi h2)
      (C e) (C (ring.rightNeighbor e)) =
      (concretePort (κ := kappa) (τ := tau) hpsi h2).row
        (C e) (C (ring.rightNeighbor e)) := by
    unfold rowFinal
    rw [hf]
  have hstep :
      stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e =
        B9FullCarrierHost.writeAtP ring C e
          ((concretePort (κ := kappa) (τ := tau) hpsi h2).row
            (C e) (C (ring.rightNeighbor e))) := by
    unfold stepConcrete stepFinal
    rw [if_neg hs, hrow]
  have hp :=
    (concretePort (κ := kappa) (τ := tau) hpsi h2).physical_spec
      (C e) (C (ring.rightNeighbor e))
  simp only [ha] at hp
  calc
    physicalConfig
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e) =
      physicalConfig
        (B9FullCarrierHost.writeAtP ring C e
          ((concretePort (κ := kappa) (τ := tau) hpsi h2).row
            (C e) (C (ring.rightNeighbor e)))) :=
      congrArg (fun D : FinalCandidateR2C.Config n psi kappa tau =>
        physicalConfig D) hstep
    _ = B9Host.hostStep
        (hostR2C (κ := kappa) (τ := tau) hpsi h2)
        ring (physicalConfig C) e := by
      funext i
      change
        (B9FullCarrierHost.writeAtP ring C e
          ((concretePort (κ := kappa) (τ := tau) hpsi h2).row
            (C e) (C (ring.rightNeighbor e))) i).phys =
        B9Host.hostStep
          (hostR2C (κ := kappa) (τ := tau) hpsi h2)
          ring (physicalConfig C) e i
      by_cases hi : i = e
      · subst i
        rw [B9Host.hostStep_left]
        simp only [B9FullCarrierHost.writeAtP, if_pos rfl]
        exact hp.1
      · by_cases hj : i = ring.rightNeighbor e
        · subst i
          rw [B9Host.hostStep_right
            (hostR2C (κ := kappa) (τ := tau) hpsi h2)
            ring (physicalConfig C) e hs]
          simp only [B9FullCarrierHost.writeAtP,
            if_neg hs, if_pos rfl]
          exact hp.2
        · rw [B9Host.hostStep_other
            (hostR2C (κ := kappa) (τ := tau) hpsi h2)
            ring (physicalConfig C) e i hi hj]
          simp only [B9FullCarrierHost.writeAtP,
            if_neg hi, if_neg hj]
          rfl
    _ = R2Coherence.step hpsi h2 ring (physicalConfig C) e := by
      rfl

private theorem finalR2View_stepConcrete_of_passive_admitted
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C) :
    finalR2View
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e) =
      R2.step hpsi h2 ring (finalR2View C) e := by
  have hphys := physicalConfig_stepConcrete_of_passive_admitted_local
    hpsi h2 ring hn C e hA
  have hOpen : R2Coherence.AllOpen (physicalConfig C) := by
    intro i
    exact hA.2.2.1 i
  have hNo : R2Coherence.NoHazardAt hpsi h2 ring (physicalConfig C) e := by
    exact (hA.2.2.2 e).2.2
  change R2Coherence.project
      (physicalConfig
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e)) =
    R2.step hpsi h2 ring (R2Coherence.project (physicalConfig C)) e
  rw [hphys]
  exact R2Coherence.project_step_of_open_no_write
    hpsi h2 ring (physicalConfig C) e hOpen hNo


/-- Everything outside the V3.1 open-arm mismatch is now wired. -/
theorem c1FinalV31OneStepSimulationResidual_of_openArm
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hArm : C1FinalV31OpenArmResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31OneStepSimulationResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C e hA
  have hR2 := finalR2View_stepConcrete_of_passive_admitted
    hpsi h2 ring hn C e hA
  have hV3 := hArm C e hA
  change R2CoherenceV31Entrance.openInitV31
      (finalR2View
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring C e)) =
    R2CoherenceV31.stepV3 hpsi h2 ring (liftFinalV31 C) e
  rw [hR2]
  exact hV3.symm


end R2CoherenceV31FinalSimulation2

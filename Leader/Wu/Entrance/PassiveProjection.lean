import Leader.Wu.Entrance.CapProgressStatement

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open B9Host B9FullCarrierHost
open WriterProducerRepair
open BirthLeaderlessBirthMassRenewal

variable {n ψ κ τ : Nat}

/-- The two endpoints of a scheduled edge are distinct once `2 ≤ n`.
Local copy because the corresponding B7 helper is private. -/
private theorem b4_rightNeighbor_ne_of_two
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

/-- Passive admission still forces the literal concrete service to be exactly
one physical R2C HOST step.  The `.depart`-tolerant writer conjunct is not
used: the proof needs only no-garbage and HOST on this edge, plus the frozen
port's `physical_spec`.

`concretePortLocal` and `concretePort` are definitionally the same frozen
`fullRowPort`; the former occurs in `ConcreteB7AdmittedPassive`, while the
latter occurs in `stepConcrete`. -/
private theorem physicalConfig_stepConcrete_of_passive_admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : Config n ψ κ τ) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hψ h2 ring C) :
    physicalConfig
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) =
      R2Coherence.step hψ h2 ring (physicalConfig C) e := by
  classical
  have hs := b4_rightNeighbor_ne_of_two ring hn e
  have hedge := hA.2.2.2 e
  have hg := hedge.1
  have ha :
      (concretePort (κ := κ) (τ := τ) hψ h2).action
          (C e) (C (ring.rightNeighbor e)) = .host := by
    simpa only [concretePort, concretePortLocal] using hedge.2.1
  have hf : finalAction hψ h2
      (concretePort (κ := κ) (τ := τ) hψ h2)
      (C e) (C (ring.rightNeighbor e)) = .host := by
    unfold finalAction
    rw [if_neg hg, ha]
  have hrow : rowFinal hψ h2
      (concretePort (κ := κ) (τ := τ) hψ h2)
      (C e) (C (ring.rightNeighbor e)) =
      (concretePort (κ := κ) (τ := τ) hψ h2).row
        (C e) (C (ring.rightNeighbor e)) := by
    unfold rowFinal
    rw [hf]
  have hstep :
      stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e =
        B9FullCarrierHost.writeAtP ring C e
          ((concretePort (κ := κ) (τ := τ) hψ h2).row
            (C e) (C (ring.rightNeighbor e))) := by
    unfold stepConcrete stepFinal
    rw [if_neg hs, hrow]
  have hp :=
    (concretePort (κ := κ) (τ := τ) hψ h2).physical_spec
      (C e) (C (ring.rightNeighbor e))
  simp only [ha] at hp
  calc
    physicalConfig
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) =
      physicalConfig
        (B9FullCarrierHost.writeAtP ring C e
          ((concretePort (κ := κ) (τ := τ) hψ h2).row
            (C e) (C (ring.rightNeighbor e)))) :=
      congrArg (fun D : Config n ψ κ τ => physicalConfig D) hstep
    _ = B9Host.hostStep
        (hostR2C (κ := κ) (τ := τ) hψ h2)
        ring (physicalConfig C) e := by
      funext i
      change
        (B9FullCarrierHost.writeAtP ring C e
          ((concretePort (κ := κ) (τ := τ) hψ h2).row
            (C e) (C (ring.rightNeighbor e))) i).phys =
        B9Host.hostStep
          (hostR2C (κ := κ) (τ := τ) hψ h2)
          ring (physicalConfig C) e i
      by_cases hi : i = e
      · subst i
        rw [B9Host.hostStep_left]
        simp only [B9FullCarrierHost.writeAtP, if_pos rfl]
        exact hp.1
      · by_cases hj : i = ring.rightNeighbor e
        · subst i
          rw [B9Host.hostStep_right
            (hostR2C (κ := κ) (τ := τ) hψ h2)
            ring (physicalConfig C) e hs]
          simp only [B9FullCarrierHost.writeAtP,
            if_neg hs, if_pos rfl]
          exact hp.2
        · rw [B9Host.hostStep_other
            (hostR2C (κ := κ) (τ := τ) hψ h2)
            ring (physicalConfig C) e i hi hj]
          simp only [B9FullCarrierHost.writeAtP,
            if_neg hi, if_neg hj]
          rfl
    _ = R2Coherence.step hψ h2 ring (physicalConfig C) e := by
      rfl

/-- One literal scheduler letter projects from the frozen concrete final
carrier to the bare R1 `step1` under the repaired writer-passive admission.

The `.depart` tolerance is harmless here: `FinalWriterPassive` is not used by
this theorem.  The physical agreement consumes the unchanged no-producer,
all-open, proposal-no-write and leaderless facts. -/
theorem stepConcrete_base_eq_step1_of_passive_admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : Config n ψ κ τ) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hψ h2 ring C)
    (hL : FinalLeaderless C) :
    finalBase
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) =
      BirthCheckPermitRepairLeaf.step1 hψ h2 ring
        (finalBase C) e := by
  have hphys := physicalConfig_stepConcrete_of_passive_admitted
    hψ h2 ring hn C e hA
  have hOpen : R2Coherence.AllOpen (physicalConfig C) := by
    intro i
    exact hA.2.2.1 i
  have hNo :
      R2Coherence.NoHazardAt hψ h2 ring (physicalConfig C) e := by
    exact (hA.2.2.2 e).2.2
  have hLead :
      R2.Leaderless (R2Coherence.project (physicalConfig C)) := by
    intro i
    change outputFinal (C i) = false
    exact hL i
  have hProd :
      R2.NoProducer (R2Coherence.project (physicalConfig C)) := by
    intro i
    exact hA.1 i
  have hAgree := R2Coherence.leaderless_agreement
    hψ h2 ring hR2 (physicalConfig C) e
    hOpen hNo hLead hProd
  change R2Coherence.baseProject
      (physicalConfig
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)) =
    BirthCheckPermitRepairLeaf.step1 hψ h2 ring
      (R2Coherence.baseProject (physicalConfig C)) e
  rw [hphys]
  exact hAgree

/-- B4-useful one-letter form: after the passive concrete-to-R1 projection,
the existing checked no-equal bridge identifies R1 with the terminal
consumer `currentStep2` on the same literal scheduler letter. -/
theorem stepConcrete_base_eq_currentStep2_of_passive_admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : Config n ψ κ τ) (e : Fin n)
    (hA : ConcreteB7AdmittedPassive hψ h2 ring C)
    (hL : FinalLeaderless C)
    (hNo : BirthCheckPermitRepairAgree.NoEqualOutcome hψ h2
      ((finalBase C) e)
      ((finalBase C) (ring.rightNeighbor e))) :
    finalBase
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) =
      BirthPhaseWait2BlockProgress.currentStep2
        hψ h2 ring (finalBase C) e := by
  calc
    finalBase
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) =
      BirthCheckPermitRepairLeaf.step1 hψ h2 ring
        (finalBase C) e :=
      stepConcrete_base_eq_step1_of_passive_admitted
        hψ h2 ring hn hR2 C e hA hL
    _ = BirthPhaseWait2BlockProgress.currentStep2
        hψ h2 ring (finalBase C) e :=
      BirthCheckPermitRepairAgree.step1_eq
        hψ h2 ring (finalBase C) e hNo

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C



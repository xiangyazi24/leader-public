import Leader.Wu.Entrance.ExpiryCutSafeAlong
import Leader.Wu.Entrance.ComposedRow

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6EntranceK2Gate

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open B6EntranceEnvelopeFrame B6EntranceEnvelopeWord
open B6EntranceAdmissionV3 B6EntranceAdmissionR1
open B6EntranceExpiryWord B6EntranceK2ChainCollar
open B4PassiveResetEcho
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi : Nat}
variable {ring : DirectedRing n}

private theorem aliveAlong_end
    {S : Type} {m : Nat}
    (step : S → Fin m → S) (Good : S → Prop)
    (x : S) (u : List (Fin m))
    (h : AliveAlong step Good x u) :
    Good (u.foldl step x) := by
  induction u generalizing x with
  | nil =>
      exact h
  | cons e rest ih =>
      simpa only [List.foldl_cons] using
        (ih (x := step x e) h.2)

theorem runConcrete_base_eq_runR1_of_passive_admitted
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi))
    (u : List (Fin n))
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C)
    (hAlive : AliveAlong
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C u) :
    finalBase
        (u.foldl
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring) C) =
      u.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring)
        (finalBase C) := by
  induction u generalizing C with
  | nil => rfl
  | cons e rest ih =>
      have hAliveCons :
          FinalLeaderless C ∧
            AliveAlong
              (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
              FinalLeaderless
              (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e)
              rest := hAlive
      have hstep := stepConcrete_base_eq_step1_of_passive_admitted
        hpsi h2 ring hn hR2 C e hA hAliveCons.1
      have hAliveRest := hAliveCons.2
      have hLnext :
          FinalLeaderless
            (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e) :=
        aliveAlong_good hAliveRest
      have hnext := hClosed C e hA hAliveCons.1
      have hA' :
          ConcreteB7AdmittedPassive hpsi h2 ring
            (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e) := by
        rcases hnext with hLead | hAdm
        · rcases hLead with ⟨i, hi⟩
          have hf := hLnext i
          rw [hf] at hi
          cases hi
        · exact hAdm
      have htail := ih
        (C := stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e)
        hA' hAliveRest
      rw [List.foldl_cons, List.foldl_cons]
      calc
        finalBase
            (rest.foldl
              (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
              (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e)) =
          rest.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring)
            (finalBase
              (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e)) :=
          htail
        _ = rest.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring)
            (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring
              (finalBase C) e) := by
          rw [hstep]


private theorem runHost_r1_eq_runStep1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (u : List (Fin n))
    (C : PConfig n (Phys psi psi (16 * psi))) :
    runHost
        (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring u C =
      u.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring) C := by
  induction u generalizing C with
  | nil => rfl
  | cons e rest ih =>
      change
        runHost
            (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
            ring rest
            (B9Host.hostStep
              (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
              ring C e) =
          rest.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring)
            (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e)
      rw [B9Host.hostStep_r1_eq_step1
        (kappa := psi) (tau := 16 * psi) hpsi h2 ring C e]
      exact ih (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e)


def C4K2EnvelopeGate
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi)))
    (b : EntranceBudgets)
    (hlaws :
      EntranceHostLawsV3b hpsi h2
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        (fun q : Phys psi psi (16 * psi) => q) ring WP b) : Prop :=
  ∀ (X : Workspace ring psi)
    (C0 : FinalCandidateR2C.Config n psi psi (16 * psi))
    (lineage : List (Fin n)),
    ConcreteB7AdmittedPassive hpsi h2 ring C0 →
    AliveAlong
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless C0 lineage →
    FinalResetEchoClear C0 →
    WriterAt WP X
      (finalBase
        (lineage.foldl
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring) C0)) →
    (∀ D : PConfig n (Phys psi psi (16 * psi)),
      TrafficAtEnv (fun q : Phys psi psi (16 * psi) => q) WP X D →
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring D
        (k2DrainWord ring X)) →
    ∃ u : List (Fin n),
      InternalWord X.env.I u ∧ u.length ≤ b.traffic.L ∧
      ∃ w : List (Fin n),
        InternalWord X.env.I w ∧ w.length ≤ b.expiry.L ∧
        HostExit
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          (fun q : Phys psi psi (16 * psi) => q) ring X.env.I
          (fun E =>
            let K :=
              runHost
                (B9Host.r1Host
                  (kappa := psi) (tau := 16 * psi) hpsi h2)
                ring (k2DrainWord ring X) E
            TrafficAtEnv
                (fun q : Phys psi psi (16 * psi) => q) WP X K ∧
              ExpiryAtEnv
                (fun q : Phys psi psi (16 * psi) => q) WP X K)
          (runHost
            (B9Host.r1Host
              (kappa := psi) (tau := 16 * psi) hpsi h2)
            ring (u ++ w)
            (finalBase
              (lineage.foldl
                (stepConcrete
                  (κ := psi) (τ := 16 * psi) hpsi h2 ring) C0)))


theorem c4K2EnvelopeGate_of_passive_lineage
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 2 ≤ n)
    (ring : DirectedRing n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi)))
    (b : EntranceBudgets)
    (hlaws :
      EntranceHostLawsV3b hpsi h2
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        (fun q : Phys psi psi (16 * psi) => q) ring WP b) :
    C4K2EnvelopeGate hpsi h2 ring WP b hlaws := by
  unfold C4K2EnvelopeGate
  intro X C0 lineage hA hAlive hClear0 hWriter hDrain
  let F : FinalCandidateR2C.Config n psi psi (16 * psi) :=
    lineage.foldl
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring) C0
  let E : PConfig n (Phys psi psi (16 * psi)) :=
    runHost
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      ring lineage (finalBase C0)
  have hWord :
      finalBase F =
        lineage.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring)
          (finalBase C0) := by
    dsimp only [F]
    exact runConcrete_base_eq_runR1_of_passive_admitted
      hpsi h2 ring hn hClosed hR2 C0 lineage hA hAlive
  have hRun :
      E = lineage.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring)
        (finalBase C0) := by
    dsimp only [E]
    exact runHost_r1_eq_runStep1 hpsi h2 ring lineage (finalBase C0)
  have hBase : finalBase F = E := hWord.trans hRun.symm
  have hLF : FinalLeaderless F := by
    dsimp only [F]
    exact aliveAlong_end
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C0 lineage hAlive
  have hClearF : FinalResetEchoClear F := by
    dsimp only [F]
    exact B4PassiveResetEcho.finalResetEchoClear_passiveWord
      (ring := ring) hpsi h2 hn hClosed hR2 C0 lineage hA hAlive hClear0
  have hLE :
      HostLeaderless (fun q : Phys psi psi (16 * psi) => q) E := by
    change BirthShortDoneTerminalFirstHit.Leaderless E
    rw [← hBase]
    intro i
    change FinalCandidateR2C.FinalCandidateR2C.outputFinal (F i) = false
    exact hLF i
  have hWriterE : WriterAt WP X E := by
    rw [← hBase]
    simpa only [F] using hWriter
  have hExit :=
    B6EntranceK2ChainCollar.k2_chain_of_lawsV3b_of_resetEchoClear_no_expiryCut
      (ring := ring) hpsi h2 WP b hlaws X E F hBase
      hLE hWriterE hClearF hDrain
  rcases hExit with ⟨u, huI, huL, w, hwI, hwL, hHost⟩
  refine ⟨u, huI, huL, w, hwI, hwL, ?_⟩
  rw [← hBase] at hHost
  simpa only [F] using hHost


def C4K2EnvelopeUniformMassObligation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (C0 : FinalCandidateR2C.Config n psi psi (16 * psi))
    (lineage : List (Fin n)),
    ConcreteB7AdmittedPassive hpsi h2 ring C0 →
    FinalResetEchoClear C0 →
    AliveAlong
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless C0 lineage →
    let C :=
      lineage.foldl
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring) C0
    let H := 256 * n ^ 2
    8 * avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
        HasLeader C H ≤
      (8 - 1) * n ^ H


end B6EntranceK2Gate

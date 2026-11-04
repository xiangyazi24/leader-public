import Leader.Wu.Coherence.CarrierSimulationOpenArm

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace R2CoherenceV31FinalSimulation3

open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open R2CoherenceV31FinalSimulation
open R2CoherenceV31FinalSimulation2

variable {n psi kappa tau : Nat}

/-- Exact CHECK-ready field absent from `ConcreteB7AdmittedPassive`. -/
def C1FinalV31ReadyAlignedAdmission
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ (C : FinalCandidateR2C.Config n psi kappa tau) (i : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    R2CoherenceBranches.ReadyAlignedCell ((physicalConfig C) i)

/-- The existing sanitizer residual follows immediately from the missing
CHECK-ready alignment field. -/
theorem c1FinalV31SanitizeReadyResidual_of_readyAlignedAdmission
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hReady : C1FinalV31ReadyAlignedAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31SanitizeReadyResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C e hA
  dsimp only
  constructor
  · apply R2CoherenceBranches.sanitizeReadyPhys_eq_self
    have h := hReady C e hA
    simpa [R2CoherenceBranches.ReadyAlignedCell,
      R2Coherence.raw, R2Coherence.project] using h
  · apply R2CoherenceBranches.sanitizeReadyPhys_eq_self
    have h := hReady C (ring.rightNeighbor e) hA
    simpa [R2CoherenceBranches.ReadyAlignedCell,
      R2Coherence.raw, R2Coherence.project] using h

/-- Exact R2-boundary arm that V3.1 newly treats as hazardous: the ordinary
R2 service changes at least one endpoint's main comparison path. -/
def R2MainPathMutationArm
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : R2.Cell psi kappa tau) : Prop :=
  let q := R2.row hpsi (by decide : 0 < 2) h2 l r
  q.1.base.core.core.path ≠ l.base.core.core.path ∨
    q.2.base.core.core.path ≠ r.base.core.core.path

/-- Exact strengthening needed on passive admission to exclude the preceding
arm.  This is deliberately about the main `path`, not writer `path3`. -/
def C1FinalV31MainPathFrameAdmission
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    let D := finalR2View C
    let q := R2.row hpsi (by decide : 0 < 2) h2
      (D e) (D (ring.rightNeighbor e))
    q.1.base.core.core.path = (D e).base.core.core.path ∧
      q.2.base.core.core.path =
        (D (ring.rightNeighbor e)).base.core.core.path

/-- The installed V3.1 path residual is exactly the Boolean form of the frame
above. -/
theorem c1FinalV31PathStableResidual_of_mainPathFrameAdmission
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hFrame : C1FinalV31MainPathFrameAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31PathStableResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C e hA
  have h := hFrame C e hA
  dsimp only at h ⊢
  rcases h with ⟨hL, hR⟩
  simp [R2CoherenceV31.pairPathChangesV3,
    R2CoherenceV31.pathChangedV3, hL, hR]

/-- Local open/open calculation.  Old admission supplies bit/label silence;
the two new seams supply sanitizer identity and main-path silence. -/
private theorem rowV3_openInit_of_sanitize_noWrite_path
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : R2Coherence.Cell psi kappa tau)
    (hSanL : R2CoherenceBranches.sanitizeReadyPhys l.phys = l.phys)
    (hSanR : R2CoherenceBranches.sanitizeReadyPhys r.phys = r.phys)
    (hNo : R2Coherence.ProposalNoWrite
      hpsi (by decide : 0 < 2) h2 l r)
    (hPath : R2CoherenceV31.pairPathChangesV3 l.phys r.phys
      (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).1
      (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).2 = false) :
    R2CoherenceV31.rowV3 hpsi (by decide : 0 < 2) h2
        ⟨l.phys, ⟨.open, .none⟩⟩ ⟨r.phys, ⟨.open, .none⟩⟩ =
      (⟨(R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).1,
          ⟨.open, .none⟩⟩,
       ⟨(R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).2,
          ⟨.open, .none⟩⟩) := by
  have hNo' := hNo
  change
    R2Coherence.pairWrites l.phys r.phys
        (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).1
        (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).2 = false ∧
    R2Coherence.pairRelabels l.phys r.phys
        (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).1
        (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).2 = false at hNo'
  have hHaz :
      R2CoherenceV31.pairHazardV3 l.phys r.phys
        (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).1
        (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).2 = false := by
    simp [R2CoherenceV31.pairHazardV3, R2Coherence.pairHazard,
      hNo'.1, hNo'.2, hPath]
  simp [R2CoherenceV31.rowV3, R2CoherenceV31.ordinaryStageV3,
    R2CoherenceV31.openStageV3, R2CoherenceV31.proposalV3,
    R2CoherenceV31.install, hSanL, hSanR, hHaz]

/-- Strongest valid `of_admission` assembly on current main: passive admission
plus the two fields it does not presently contain. -/
theorem c1FinalV31OpenArmResidual_of_admission
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hReady : C1FinalV31ReadyAlignedAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hFrame : C1FinalV31MainPathFrameAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31OpenArmResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C e hA
  have hSanR :=
    c1FinalV31SanitizeReadyResidual_of_readyAlignedAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring hReady
  have hSan := hSanR C e hA
  dsimp only at hSan
  have hPathR :=
    c1FinalV31PathStableResidual_of_mainPathFrameAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring hFrame
  have hPath := hPathR C e hA
  dsimp only at hPath
  have hNo := (hA.2.2.2 e).2.2
  have hrow := rowV3_openInit_of_sanitize_noWrite_path
    hpsi h2 (C e).phys (C (ring.rightNeighbor e)).phys
    hSan.1 hSan.2 hNo hPath
  funext i
  by_cases hi : i = e
  · subst i
    simpa [R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
      PopulationProtocol.step, R2.step, R2.protocol,
      liftFinalV31, R2CoherenceV31MissionGate.finalV31View,
      R2CoherenceV31Entrance.openInitV31, finalR2View,
      R2Coherence.project, physicalConfig] using congrArg Prod.fst hrow
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
        PopulationProtocol.step, R2.step, R2.protocol, hi,
        liftFinalV31, R2CoherenceV31MissionGate.finalV31View,
        R2CoherenceV31Entrance.openInitV31, finalR2View,
        R2Coherence.project, physicalConfig] using congrArg Prod.snd hrow
    · simp [R2CoherenceV31.stepV3, R2CoherenceV31.protocolV3,
        PopulationProtocol.step, R2.step, R2.protocol, hi, hj,
        liftFinalV31, R2CoherenceV31MissionGate.finalV31View,
        R2CoherenceV31Entrance.openInitV31, finalR2View,
        R2Coherence.project, physicalConfig]

/-- Installed reduction now closes the one-step residual once the two
missing admission fields are supplied. -/
theorem c1FinalV31OneStepSimulationResidual_of_admission
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hReady : C1FinalV31ReadyAlignedAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hFrame : C1FinalV31MainPathFrameAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31OneStepSimulationResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  apply c1FinalV31OneStepSimulationResidual_of_openArm hpsi h2 ring hn
  exact c1FinalV31OpenArmResidual_of_admission
    (kappa := kappa) (tau := tau) hpsi h2 ring hReady hFrame

end R2CoherenceV31FinalSimulation3

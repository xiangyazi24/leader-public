import Leader.Wu.Splice.OrdinaryHostBirthSafe
import Leader.Wu.Splice.OrdinaryLeftLeaderFrame

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV8BirthCaseAdapterLabelGen

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
open PPLLWallSweepPreCheckResetContracts PPLLWallSweepNormalResetContract
  PPLLCompleteMultiLeaderCleanup PPLLPpsiLeaderCreationSchedule
open BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthShortDoneCuts
  BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
  BirthSigMoveDisposalRepair BirthArrivalCaptureRepair
  BirthSingleUseReleaseRepair BirthTossCheckPreservationRepair
  BirthCheckCongestGuardRepair K2BirthDispatcher K2BirthDispatcherDone
  K2BirthLeaderNormalize ExpiringK2Projection BirthStationaryWrite
open B9SpliceV8LeftLeaderOpaqueBridge

variable {psi width kappa : Nat}

def rawLabels (q : AgentState psi × AgentState psi) : Fin psi × Fin psi :=
  (q.1.label, q.2.label)

def authLabels
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Fin psi × Fin psi :=
  (q.1.core.label, q.2.core.label)

private theorem waitEntry_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AgentState psi) :
    rawLabels (waitWidthEntry hpsi hwidth hle cap l r) = (l.label, r.label) := by
  apply Prod.ext <;> simp [rawLabels, waitWidthEntry, waitSaturatedPrepare,
    terminalInactiveClear, waitWidthCarry, waitWidthReset, waitWidthFinish]

private theorem genAfterWait_labels (hpsi : 0 < psi) (l r : AgentState psi) :
    rawLabels (genCleanAfterWait hpsi l r) = (l.label, r.label) := by
  let q0 := genSigSaturatedStart hpsi l r
  let q1 := genCleanEmit hpsi q0.1 q0.2
  let q2 := genCleanPropagate hpsi q1.1 q1.2
  have h0 : rawLabels q0 = (l.label, r.label) := by
    unfold q0 rawLabels genSigSaturatedStart
    repeat (first | rfl | split <;> try dsimp only)
  have h1 : rawLabels q1 = rawLabels q0 := by
    unfold q1 rawLabels genCleanEmit
    repeat (first | rfl | split <;> try dsimp only)
  have h2 : rawLabels q2 = rawLabels q1 := by
    unfold q2 rawLabels genCleanPropagate
    repeat (first | rfl | split <;> try dsimp only)
  have h3 : rawLabels (genSigSaturatedFinish hpsi q2.1 q2.2) = rawLabels q2 := by
    unfold rawLabels genSigSaturatedFinish
    repeat (first | rfl | split <;> try dsimp only)
  change rawLabels (genSigSaturatedFinish hpsi q2.1 q2.2) = (l.label, r.label)
  exact h3.trans (h2.trans (h1.trans h0))

private theorem genEntry_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AgentState psi) :
    rawLabels (genCleanEntryWidth hpsi hwidth hle cap l r) = (l.label, r.label) := by
  let w := waitWidthEntry hpsi hwidth hle cap l r
  exact (genAfterWait_labels hpsi w.1 w.2).trans
    (waitEntry_labels hpsi hwidth hle cap l r)

theorem generation_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    authLabels (generationBeforeMoveEntryWidth hpsi hwidth hle cap l r) =
      authLabels (authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let p := authorizedPPsiLeaderResetProbeWall hpsi l r
  let g := authorizedGenCleanEntryWidth hpsi hwidth hle cap p.1 p.2
  let c := authorizedCleanSig hpsi g.1 g.2
  have hg : authLabels g = authLabels p := by
    change rawLabels (genCleanEntryWidth hpsi hwidth hle cap p.1.core p.2.core) =
      (p.1.core.label, p.2.core.label)
    exact genEntry_labels hpsi hwidth hle cap p.1.core p.2.core
  have hc : authLabels c = authLabels g := by
    change rawLabels (cleanSig hpsi g.1.core g.2.core) =
      (g.1.core.label, g.2.core.label)
    exact Prod.ext (PPLLVerify.cleanSig_labels_eq hpsi g.1.core g.2.core).1
      (PPLLVerify.cleanSig_labels_eq hpsi g.1.core g.2.core).2
  have he : authLabels (authorizedEliminateSig hpsi c.1 c.2) = authLabels c := by
    change rawLabels (eliminateSig hpsi c.1.core c.2.core) =
      (c.1.core.label, c.2.core.label)
    exact Prod.ext (PPLLVerify.eliminateSig_labels_eq hpsi c.1.core c.2.core).1
      (PPLLVerify.eliminateSig_labels_eq hpsi c.1.core c.2.core).2
  have hs : generationBeforeMoveEntryWidth hpsi hwidth hle cap l r =
      authorizedEliminateSig hpsi c.1 c.2 :=
    generation_eq_stages hpsi hwidth hle cap l r
  exact (congrArg authLabels hs).trans (he.trans (hc.trans hg))

end B9SpliceV8BirthCaseAdapterLabelGen

#print axioms B9SpliceV8BirthCaseAdapterLabelGen.generation_labels

import Leader.Wu.Entrance.PreWriterFramesCheck

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV8LeftLeaderOpaqueBridge

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair
open BirthGenerationControlRepair BirthGenerationDone
  BirthTossCheckPreservationRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneCuts BirthShortDoneTerminalHost
open K2BirthDispatcher

variable {psi width kappa : Nat}

theorem generation_eq_stages
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    let p := authorizedPPsiLeaderResetProbeWall hpsi l r
    let g := authorizedGenCleanEntryWidth hpsi hwidth hle kappa p.1 p.2
    let c := authorizedCleanSig hpsi g.1 g.2
    generationBeforeMoveEntryWidth hpsi hwidth hle kappa l r =
      authorizedEliminateSig hpsi c.1 c.2 := by
  unfold generationBeforeMoveEntryWidth
  rfl

theorem doneBefore_eq_stages
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    let g := generationBeforeMoveEntryWidth hpsi hwidth hle kappa l r
    let m := authorizedDoneMove hpsi g.1 g.2
    doneBeforeCheckEntryWidth hpsi hwidth hle kappa l r =
      sanitizeAuthorizedPair hpsi (preCheckResetWall m.1 m.2) := by
  unfold doneBeforeCheckEntryWidth
  rfl

theorem doneThrough_eq_stages
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    let d := doneBeforeCheckEntryWidth hpsi hwidth hle kappa l r
    doneThroughCheckEntryWidth hpsi hwidth hle kappa l r =
      preserveDoneCheck hpsi d.1 d.2 := by
  unfold doneThroughCheckEntryWidth
  rfl

theorem ordinary_eq_stages
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    let c := doneThroughCheckEntryWidth hpsi hwidth hle kappa l r
    let q := afterCheckMetadataWidth hpsi hwidth hle c.1 c.2
    doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa l r =
      markLeaderBirth (authBirth l r q) q := by
  unfold doneOrdinaryMetadataEntryWidth
  rfl

end B9SpliceV8LeftLeaderOpaqueBridge

#print axioms B9SpliceV8LeftLeaderOpaqueBridge.generation_eq_stages
#print axioms B9SpliceV8LeftLeaderOpaqueBridge.ordinary_eq_stages

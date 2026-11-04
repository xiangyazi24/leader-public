import Leader.Wu.Entrance.ExpiryCutWord
import Leader.Wu.Elimination.MultiLeaderCleanupPhysicalBridge


set_option autoImplicit false
set_option Elab.async false


namespace B6EntranceExpiryWord


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open PPLLRepair PPLLDomain PPLLAuthorizedComparisonRepair
open PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthSigMoveDisposalRepair BirthGenerationDone
open BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair
open BirthShortDoneTerminalEntryCut BirthShortDoneCuts
open BirthStationaryWrite
open R1CandidateKernel
open PPLLCompleteMultiLeaderCleanup.PhysicalBridge


variable {n psi kappa tau : Nat}
variable {ring : DirectedRing n}


private theorem leftIdle_of_authQuiet
    (u : AuthorizedAgentState psi) (h : AuthQuiet u) :
    CleanupLeftTailIdle u := by
  rcases h with ⟨⟨hs, hp, _hp2, _hp4, _hp5, _hP, hcarry⟩, hpermit⟩
  exact ⟨hs, hp, hcarry, hpermit⟩


private theorem rightIdle_of_authQuiet
    (u : AuthorizedAgentState psi) (h : AuthQuiet u) :
    CleanupRightTailIdle u := by
  rcases h with ⟨⟨hs, hp, _hp2, _hp4, _hp5, _hP, _hcarry⟩, hpermit⟩
  exact ⟨hs, hp, hpermit⟩


private theorem prepareExpiringDisposal_eq_of_authQuiet
    (hpsi : 0 < psi) (u : Phys psi kappa tau)
    (hu : AuthQuiet u.core.erase) :
    prepareExpiringDisposal hpsi u = u := by
  have hp2 : u.core.erase.core.path2 = none := hu.1.2.2.1
  have hclear : pendingTerminalDisposal hpsi u.core.erase.core = false := by
    simp [pendingTerminalDisposal, hp2]
  -- PUBLIC: Leader/Wu/Birth/SigMoveDisposalRepair.lean:166-176.
  unfold prepareExpiringDisposal
  rw [prepareBoundedDisposal_eq_of_clear hpsi u.core hclear]


private theorem prepared_eq_of_authQuiet
    (hpsi : 0 < psi) (u : Phys psi kappa tau)
    (hu : AuthQuiet u.core.erase) :
    prepared hpsi u = u.core.erase := by
  unfold prepared
  rw [prepareExpiringDisposal_eq_of_authQuiet hpsi u hu]
  unfold normalizeDeletion
  simp [hu.1.1]


private theorem prepared_deletionActive_false
    (hpsi : 0 < psi) (u : Phys psi kappa tau)
    (hu : AuthQuiet u.core.erase) :
    deletionActive (prepared hpsi u) = false := by
  rw [prepared_eq_of_authQuiet hpsi u hu]
  rcases hu with ⟨⟨hs, hp, _hp2, _hp4, _hp5, _hP, _hcarry⟩, _⟩
  simp [deletionActive, pathPresent, hs, hp]


private theorem checkOutput_eq_checkInput_of_quiet
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Phys psi kappa tau)
    (hq : AuthQuiet (checkInput hpsi h2 l r).1 ∧
      AuthQuiet (checkInput hpsi h2 l r).2) :
    checkOutput hpsi h2 l r = checkInput hpsi h2 l r := by
  let q := checkInput hpsi h2 l r
  change AuthQuiet q.1 ∧ AuthQuiet q.2 at hq
  have hsL : q.1.core.state = .none := hq.1.1.1
  have hsR : q.2.core.state = .none := hq.2.1.1
  have hdoneL : q.1.core.state ≠ .done := by simp [hsL]
  have hdoneR : q.2.core.state ≠ .done := by simp [hsR]
  have htossL : q.1.core.state ≠ .toss := by simp [hsL]
  have htossR : q.2.core.state ≠ .toss := by simp [hsR]
  have hcongL : q.1.core.state ≠ .congest := by simp [hsL]
  have hcongR : q.2.core.state ≠ .congest := by simp [hsR]
  -- PUBLIC: Leader/Wu/Elimination/MultiLeaderCleanupPhysicalBridge.lean:211-222.
  have hcheck : authorizedCheckSig hpsi q.1 q.2 = q :=
    authorizedCheckSig_pair_eq_of_cleanup_idle hpsi q
      (leftIdle_of_authQuiet q.1 hq.1)
      (rightIdle_of_authQuiet q.2 hq.2)
  -- PUBLIC: Leader/Wu/Birth/GenerationDone.lean:40-44.
  have hdone := preserveDoneCheck_of_no_done hpsi q.1 q.2 hdoneL hdoneR
  -- PUBLIC: Leader/Wu/Birth/TossCheckPreservationRepair.lean:37-41.
  have htoss := preserveTossCheck_of_no_toss hpsi q.1 q.2 htossL htossR
  -- PUBLIC: Leader/Wu/Birth/CheckCongestGuardRepair.lean:39-43.
  have hcong := congestGuardCheck_of_clear hpsi q.1 q.2 hcongL hcongR
  have hguard : preserveDoneCheck hpsi q.1 q.2 = q := by
    calc
      preserveDoneCheck hpsi q.1 q.2 = preserveTossCheck hpsi q.1 q.2 := hdone
      _ = congestGuardCheck hpsi q.1 q.2 := htoss
      _ = authorizedCheckSig hpsi q.1 q.2 := hcong
      _ = q := hcheck
  change preserveDoneCheck hpsi q.1 q.2 = q
  exact hguard


private theorem permitFix_eq_of_authQuiet
    (u : AuthorizedAgentState psi) (hu : AuthQuiet u) :
    BirthCheckPermitRepair.permitFix u = u := by
  -- PUBLIC: Leader/Wu/Birth/CheckPermitRepair.lean:42-44.
  apply BirthCheckPermitRepair.permitFix_of_ne
  simpa [hu.1.1]


private theorem suppressWidth_neutral_of_neutral
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : AgentState psi)
    (hL : ComparisonNeutral l) (hR : ComparisonNeutral r) :
    let q := BirthShortWait.suppressSigResetKillWidth
      hpsi (by decide : 0 < 2) h2 l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 := by
  rcases hL with ⟨hLs, hLp, hLp2, hLp4, hLp5, hLP, hLCarry⟩
  rcases hR with ⟨hRs, hRp, hRp2, hRp4, hRp5, hRP, hRCarry⟩
  simp [BirthShortWait.suppressSigResetKillWidth, BirthShortWait.suppressPrefix,
    BirthShortWait.shortCountReset, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish, ComparisonNeutral,
    hLs, hLp, hLp2, hLp4, hLp5, hLP, hLCarry,
    hRs, hRp, hRp2, hRp4, hRp5, hRP, hRCarry]


private theorem authorizedSuppressWidth_authQuiet
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : AuthorizedAgentState psi)
    (hL : AuthQuiet l) (hR : AuthQuiet r) :
    let q := authorizedSuppressWidth hpsi (by decide : 0 < 2) h2 l r
    AuthQuiet q.1 ∧ AuthQuiet q.2 := by
  have hnL : ComparisonNeutral l.core := by
    simpa [RawQuiet, ComparisonNeutral] using hL.1
  have hnR : ComparisonNeutral r.core := by
    simpa [RawQuiet, ComparisonNeutral] using hR.1
  let raw := BirthShortWait.suppressSigResetKillWidth
    hpsi (by decide : 0 < 2) h2 l.core r.core
  have hn := suppressWidth_neutral_of_neutral hpsi h2 l.core r.core hnL hnR
  change AuthQuiet ⟨raw.1, reconcilePermit l raw.1⟩ ∧
    AuthQuiet ⟨raw.2, reconcilePermit r raw.2⟩
  constructor
  · change RawQuiet raw.1 ∧ reconcilePermit l raw.1 = false
    have hq : RawQuiet raw.1 := by
      simpa [RawQuiet, ComparisonNeutral] using hn.1
    refine ⟨hq, ?_⟩
    have hpath : raw.1.path = .bot := hq.2.1
    unfold reconcilePermit
    split
    · simp only [normalizePermit, hpath]
    · rfl
  · change RawQuiet raw.2 ∧ reconcilePermit r raw.2 = false
    have hq : RawQuiet raw.2 := by
      simpa [RawQuiet, ComparisonNeutral] using hn.2
    refine ⟨hq, ?_⟩
    have hpath : raw.2.path = .bot := hq.2.1
    unfold reconcilePermit
    split
    · simp only [normalizePermit, hpath]
    · rfl

private theorem beforeWriteWidth_authQuiet
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : AuthorizedAgentState psi)
    (hL : AuthQuiet l) (hR : AuthQuiet r) :
    let q := beforeWriteWidth hpsi (by decide : 0 < 2) h2 l r
    AuthQuiet q.1 ∧ AuthQuiet q.2 := by
  -- PUBLIC: Leader/Wu/Elimination/MultiLeaderCleanupPhysicalBridge.lean:224-239.
  have hd := authorizedDisappear_eq_of_cleanup_idle hpsi l r
    (leftIdle_of_authQuiet l hL) (rightIdle_of_authQuiet r hR)
  -- PUBLIC: Leader/Wu/Elimination/MultiLeaderCleanupPhysicalBridge.lean:241-251.
  have hc := authorizedCompareSigActionOne_eq_of_cleanup_idle hpsi l r
    (leftIdle_of_authQuiet l hL)
  unfold beforeWriteWidth
  dsimp only
  rw [hd]
  dsimp only
  rw [hc]
  exact authorizedSuppressWidth_authQuiet hpsi h2 l r hL hR


/-- Public-only prefix result: the actual stationary-writer input is quiet. -/
theorem writerInput_authQuiet_of_quiet_inputs
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Phys psi kappa tau)
    (hq : AuthQuiet (checkInput hpsi h2 l r).1 ∧
      AuthQuiet (checkInput hpsi h2 l r).2) :
    AuthQuiet (writerInput hpsi h2 l r).1 ∧
      AuthQuiet (writerInput hpsi h2 l r).2 := by
  have hcEq := checkOutput_eq_checkInput_of_quiet hpsi h2 l r hq
  let c := checkOutput hpsi h2 l r
  have hcq : AuthQuiet c.1 ∧ AuthQuiet c.2 := by
    dsimp only [c]
    rw [hcEq]
    exact hq
  have hfix : BirthCheckPermitRepair.permitFix c.1 = c.1 :=
    permitFix_eq_of_authQuiet c.1 hcq.1
  change
    AuthQuiet (beforeWriteWidth hpsi (by decide : 0 < 2) h2
      (BirthCheckPermitRepair.permitFix c.1) c.2).1 ∧
    AuthQuiet (beforeWriteWidth hpsi (by decide : 0 < 2) h2
      (BirthCheckPermitRepair.permitFix c.1) c.2).2
  rw [hfix]
  exact beforeWriteWidth_authQuiet hpsi h2 c.1 c.2 hcq.1 hcq.2


/-- STOP HERE under the public-only rule.


PUBLIC coverage:
* `stationaryPersistentRaw_frame`,
  Leader/Wu/WriteSeq/StationaryWritePersistent.lean:159-168, frames the `swPair`
  projection; `stationaryPersistentRaw_comparison` at :187-189 therefore
  covers `state/path/path2/p_carry`.
* `stationaryPersistentAuthorizedRow_permits`,
  Leader/Wu/WriteSeq/StationaryWritePersistentFinite.lean:259-267, covers
  `path0Crossed`.


MISSING public coverage: `AuthQuiet` also requires `path4 = none`,
`path5 = none`, and `p = false`.


The first unavailable cleanup-aux proof components in the existing stack are
PRIVATE `PPLLWallSweepNormalResetContract.cleanupAuxPair_writeSeqThroughPrepare`
at Leader/Wu/WallSweep/NormalResetContract.lean:2438 and PRIVATE
`cleanupAuxPair_writeSeqAfterPrepare` at :2601.  Moreover the current
stationary-persistent row uses the transport variants, and there is no public
`cleanupAuxPair` frame for that row.  Per the task instruction, do not unfold
the writer to reconstruct those private proofs here. -/
def R1ExpiryCutQuietWriterResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Phys psi kappa tau) : Prop :=
  let w := writerInput hpsi h2 l r
  let z := stationaryPersistentAuthorizedRow hpsi w.1 w.2
  AuthQuiet z.1 ∧ AuthQuiet z.2


/- The requested theorem
`r1ExpiryCutQuiet_of_quiet_inputs` resumes exactly after the residual above;
marking, bounded reification and `deletionPriorityExpireOne` are downstream of
this stopped writer boundary and are intentionally not crossed here. -/


end B6EntranceExpiryWord

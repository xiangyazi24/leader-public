import Leader.Wu.Birth.GenerationDone

/-!
# Preserve the current backward-generation acknowledgement phase

The complete finite candidate uses the exact source GEN/CLEAN/ELIMINATE
prefix, the two done corrections, and the frozen single-use-release suffix,
entry-disposal priority, expiry and newborn signal initialization.
-/

set_option autoImplicit false

namespace BirthGenerationDone

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepNormalResetContract
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair
  BirthDisposalRouteInvariant BirthMismatchDisposalProducer BirthArrivalCaptureRepair
  BirthGenerationControlRepair BirthTossCheckPreservationRepair BirthSingleUseReleaseRepair

variable {psi kappa tau : Nat}

def doneBeforeCheck (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let b := generationBeforeMove hpsi kappa l r
  let q := authorizedDoneMove hpsi b.1 b.2
  sanitizeAuthorizedPair hpsi (preCheckResetWall q.1 q.2)

attribute [local irreducible] generationBeforeMove authorizedDoneMove

theorem doneBeforeCheck_inProtocolDomain (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := doneBeforeCheck hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let b := generationBeforeMove hpsi kappa l r
  have hb := generationBeforeMove_inProtocolDomain hpsi kappa l r hl hr
  have hm := authorizedDoneMove_inProtocolDomain hpsi b.1 b.2 hb.1 hb.2
  let m := authorizedDoneMove hpsi b.1 b.2
  have hw := preCheckResetWall_inProtocolDomain m.1 m.2 hm.1 hm.2
  exact ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi _ hw.1,
    sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi _ hw.2⟩

def doneGuardedAuthorizedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then (l0, r0)
  else
    let beforeCheck := doneBeforeCheck hpsi kappa l0 r0
    let afterCheck := preserveDoneCheck hpsi beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born (actionOneAfterCheckSuffix hpsi afterCheck.1 afterCheck.2)

attribute [local irreducible] doneBeforeCheck actionOneAfterCheckSuffix

theorem doneGuardedAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := doneGuardedAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold doneGuardedAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let b := doneBeforeCheck hpsi kappa l0 r0
      have hb := doneBeforeCheck_inProtocolDomain hpsi kappa l0 r0 hl0 hr0
      let c := preserveDoneCheck hpsi b.1 b.2
      have hc := preserveDoneCheck_inProtocolDomain hpsi b.1 b.2 hb.1 hb.2
      exact markLeaderBirth_inProtocolDomain _ _
        (actionOneAfterCheckSuffix_inProtocolDomain hpsi kappa c.1 c.2 hc.1 hc.2)

def doneGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa × AuthorizedBoundedAgentState psi kappa :=
  let q := doneGuardedAuthorizedTransition hpsi kappa l.erase r.erase
  let hq := doneGuardedAuthorizedTransition_inProtocolDomain hpsi kappa
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem erase_doneGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := doneGuardedBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) = doneGuardedAuthorizedTransition hpsi kappa l.erase r.erase := by
  unfold doneGuardedBoundedTransition
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

/-- The complete finite host with held GEN acknowledgements and single-use release, using the
established disposal input, expiry rule and leader-signal initialization. -/
def doneFullTransition (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := doneGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  initializeFollowerPairBirthSignals l0 r0
    (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)

private theorem doneGuarded_eq_of_active (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (ha : deletionActive (normalizeDeletion l) = true ∨
      deletionActive (normalizeDeletion r) = true) :
    doneGuardedAuthorizedTransition hpsi kappa l r =
      singleUseGuardedAuthorizedTransition hpsi kappa l r := by
  unfold doneGuardedAuthorizedTransition singleUseGuardedAuthorizedTransition
  dsimp only
  by_cases hr : deletionActive (normalizeDeletion r) = true
  · simp only [hr, ↓reduceIte]
  · have hl : deletionActive (normalizeDeletion l) = true := ha.resolve_right hr
    simp only [hr, hl, ↓reduceIte]

attribute [local irreducible] singleUseGuardedBoundedTransition

/-- Pre-existing disposal has the identical complete successor, so holding
GEN acknowledgements does not alter the already proved action-four deletion service. -/
theorem doneFull_eq_singleUseFull_of_due
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (ha : DisposalDue hpsi l.core.erase ∨ DisposalDue hpsi r.core.erase) :
    doneFullTransition hpsi kappa tau l r = singleUseFullTransition hpsi kappa tau l r := by
  have hactive : deletionActive (preparedInput hpsi l.core.erase) = true ∨
      deletionActive (preparedInput hpsi r.core.erase) = true :=
    ha.imp (prepared_due_active hpsi l.core.erase) (prepared_due_active hpsi r.core.erase)
  have hr : doneGuardedAuthorizedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core).erase
      (prepareBoundedDisposal hpsi r.core).erase =
      singleUseGuardedAuthorizedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core).erase
        (prepareBoundedDisposal hpsi r.core).erase := by
    rw [erase_prepareBoundedDisposal, erase_prepareBoundedDisposal]
    exact doneGuarded_eq_of_active hpsi kappa _ _ hactive
  have hb : doneGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) =
      singleUseGuardedBoundedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) := by
    unfold doneGuardedBoundedTransition singleUseGuardedBoundedTransition
    dsimp only
    simp only [hr]
  unfold doneFullTransition singleUseFullTransition
  dsimp only [prepareExpiringDisposal]
  rw [hb]

/-- No done at the actual Step1 cut gives the same full pre-CHECK computation
as frozen 25, including GEN, control consumption, reset and sanitization. -/
theorem doneBeforeCheck_eq_singleUse (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hm : let g := generationBeforeMove hpsi kappa l r
      (sigMoveLeaderPreclear hpsi g.1.core g.2.core).1.state ≠ .done) :
    doneBeforeCheck hpsi kappa l r = singleUseBeforeCheck hpsi kappa l r := by
  unfold doneBeforeCheck singleUseBeforeCheck
  dsimp only
  rw [authorizedDoneMove_eq_singleUse hpsi _ _ hm]

/-- Whole ordinary-row equality is stated at the actual computed cuts.
Merely having no done in the raw input would be insufficient: GEN can write
one during the same interaction. No changed-stage output equality is assumed. -/
theorem doneGuarded_eq_singleUse_of_no_done_cuts (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hm : let g := generationBeforeMove hpsi kappa (normalizeDeletion l) (normalizeDeletion r)
      (sigMoveLeaderPreclear hpsi g.1.core g.2.core).1.state ≠ .done)
    (hl : (singleUseBeforeCheck hpsi kappa (normalizeDeletion l) (normalizeDeletion r)).1.core.state ≠ .done)
    (hr : (singleUseBeforeCheck hpsi kappa (normalizeDeletion l) (normalizeDeletion r)).2.core.state ≠ .done) :
    doneGuardedAuthorizedTransition hpsi kappa l r =
      singleUseGuardedAuthorizedTransition hpsi kappa l r := by
  unfold doneGuardedAuthorizedTransition singleUseGuardedAuthorizedTransition
  dsimp only
  by_cases hd : deletionActive (normalizeDeletion r) = true
  · simp only [hd, ↓reduceIte]
  · by_cases he : deletionActive (normalizeDeletion l) = true
    · simp only [hd, he, ↓reduceIte]
    · simp only [hd, he, doneBeforeCheck_eq_singleUse hpsi kappa _ _ hm,
        preserveDoneCheck_of_no_done hpsi _ _ hl hr]

/-- The same computed-cut criterion lifts through finite reification, both
expiry calls and final newborn initialization, with the unchanged physical
carrier and exact complete successor equality. -/
theorem doneFull_eq_singleUse_of_no_done_cuts (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hm : let g := generationBeforeMove hpsi kappa (preparedInput hpsi l.core.erase) (preparedInput hpsi r.core.erase)
      (sigMoveLeaderPreclear hpsi g.1.core g.2.core).1.state ≠ .done)
    (hl : (singleUseBeforeCheck hpsi kappa (preparedInput hpsi l.core.erase)
      (preparedInput hpsi r.core.erase)).1.core.state ≠ .done)
    (hr : (singleUseBeforeCheck hpsi kappa (preparedInput hpsi l.core.erase)
      (preparedInput hpsi r.core.erase)).2.core.state ≠ .done) :
    doneFullTransition hpsi kappa tau l r = singleUseFullTransition hpsi kappa tau l r := by
  have he : doneGuardedAuthorizedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core).erase (prepareBoundedDisposal hpsi r.core).erase =
      singleUseGuardedAuthorizedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core).erase (prepareBoundedDisposal hpsi r.core).erase := by
    rw [erase_prepareBoundedDisposal, erase_prepareBoundedDisposal]
    exact doneGuarded_eq_singleUse_of_no_done_cuts hpsi kappa _ _ hm hl hr
  have hb : doneGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) =
      singleUseGuardedBoundedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) := by
    unfold doneGuardedBoundedTransition singleUseGuardedBoundedTransition
    dsimp only
    simp only [he]
  unfold doneFullTransition singleUseFullTransition
  dsimp only [prepareExpiringDisposal]
  rw [hb]

end BirthGenerationDone

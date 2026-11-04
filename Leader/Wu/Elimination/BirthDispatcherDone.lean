import Leader.Wu.Elimination.BirthDispatcher
import Leader.Wu.Birth.GenerationDoneHost

/-!
# DONE-aware metadata adapter for the finite mixed birth dispatcher

Only the two already accepted DONE-sensitive cuts replace the frozen ordinary
prefix: `doneBeforeCheck` and `preserveDoneCheck`.  The mixed dispatcher's
post-CHECK metadata suffix, stationary persistent writer, disposal priority,
finite reification, one expiry call per endpoint, newborn initialization and
collision/K2 tail remain the existing implementations.
-/

namespace K2BirthDispatcherDone

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol PPLLNoCheckBirthLeaderFrames
  BirthArrivalCaptureRepair BirthGenerationControlRepair
  BirthSingleUseReleaseRepair BirthTossCheckPreservationRepair
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair K2OutputSafety

open K2BirthDispatcher BirthGenerationDone ExpiringK2Projection

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ τ n : Nat}

attribute [local irreducible]
  generationBeforeMove authorizedDoneMove authorizedPPsiLeaderResetProbeWall
  singleUseControlTail doneCaptureSigMove doneBeforeCheck preserveDoneCheck
  afterCheckMetadata

/-! ## Source-derived four-field frames for the DONE movement cut -/

private theorem doneStep2_signal (l r : AgentState ψ) :
    signalPair (sigMoveStep2 l r) = signalPair (l, r) := by
  unfold sigMoveStep2
  repeat (first | rfl | split)

private theorem doneStep3_signal (l r : AgentState ψ) :
    signalPair (sigMoveStep3 l r) = signalPair (l, r) := by
  unfold sigMoveStep3
  repeat (first | rfl | split)

private theorem doneStep4_signal (l r : AgentState ψ) :
    signalPair (sigMoveStep4 l r) = signalPair (l, r) := by
  unfold sigMoveStep4
  repeat (first | rfl | split)

private theorem doneStep5_signal (l r : AgentState ψ) :
    signalPair (sigMoveStep5 l r) = signalPair (l, r) := by
  unfold sigMoveStep5
  repeat (first | rfl | split)

private theorem holdDoneStep1_signal (l r : AgentState ψ) :
    signalPair (holdDoneStep1 l r) = signalPair (l, r) := by
  unfold holdDoneStep1
  split
  · rfl
  · exact captureStep1_signal l r

private theorem doneControlTransfers_signal (l r : AgentState ψ) :
    signalPair (controlTransfers l r) = signalPair (l, r) := by
  unfold controlTransfers
  dsimp only
  rw [doneStep5_signal, doneStep4_signal, doneStep3_signal, doneStep2_signal]

private theorem doneTransfers_signal (l r : AgentState ψ) :
    signalPair (doneTransfers l r) = signalPair (l, r) := by
  unfold doneTransfers
  dsimp only
  rw [doneControlTransfers_signal, holdDoneStep1_signal]

private theorem donePreclear_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (sigMoveLeaderPreclear hψ l r) = signalPair (l, r) := by
  unfold sigMoveLeaderPreclear clearIfLeader
  repeat (first | rfl | split)

private theorem doneLeaderWall_signal (l r : AgentState ψ) :
    signalPair (comparisonLeaderWall l r) = signalPair (l, r) := by
  unfold comparisonLeaderWall
  repeat (first | rfl | split)

private theorem doneApplyControl_signal (hψ : 0 < ψ) (u : AgentState ψ) :
    signalView (sigMoveApplyControl hψ u) = signalView u := by
  cases hp : u.path2 with
  | none =>
      simp only [sigMoveApplyControl, hp]
  | some p =>
      by_cases h1 :
        u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧
          (p.action = 3 ∨ p.action = 4)
      <;> by_cases h2 :
        u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ p.action = 5
      <;> by_cases h3 :
        u.label = (⟨0, hψ⟩ : Fin ψ) ∧ p.action = 6
      <;> simp [sigMoveApplyControl, hp, h1, h2, h3, signalView]

private theorem doneClearRelease_signal (hψ : 0 < ψ) (u : AgentState ψ) :
    signalView (clearTerminalRelease hψ u) = signalView u := by
  unfold clearTerminalRelease
  repeat (first | rfl | split)

private theorem doneOldControlTail_signal (hψ : 0 < ψ)
    (l r : AgentState ψ) :
    signalPair (sigMoveControlTail hψ l r) = signalPair (l, r) := by
  unfold sigMoveControlTail
  dsimp only
  split
  · split <;>
      exact Prod.ext (doneApplyControl_signal hψ l)
        (doneApplyControl_signal hψ r)
  · exact Prod.ext (doneApplyControl_signal hψ l)
      (doneApplyControl_signal hψ r)

private theorem doneSingleUseControlTail_signal (hψ : 0 < ψ)
    (l r : AgentState ψ) :
    signalPair (singleUseControlTail hψ l r) = signalPair (l, r) := by
  calc
    signalPair (singleUseControlTail hψ l r) =
        signalPair
          (clearTerminalRelease hψ (sigMoveControlTail hψ l r).1,
            clearTerminalRelease hψ (sigMoveControlTail hψ l r).2) := by
      exact congrArg signalPair (singleUseControlTail_eq_clear hψ l r)
    _ = signalPair (sigMoveControlTail hψ l r) := by
      unfold signalPair
      exact Prod.ext
        (doneClearRelease_signal hψ (sigMoveControlTail hψ l r).1)
        (doneClearRelease_signal hψ (sigMoveControlTail hψ l r).2)
    _ = signalPair (l, r) := doneOldControlTail_signal hψ l r

/-- Holding current `done` changes only the payload-transfer decision.  The
four K2 fields are exactly those of the movement input. -/
theorem doneCaptureSigMove_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (doneCaptureSigMove hψ l r) = signalPair (l, r) := by
  unfold doneCaptureSigMove
  dsimp only
  rw [doneSingleUseControlTail_signal, doneLeaderWall_signal,
    doneTransfers_signal, donePreclear_signal]

/-- Permit reconciliation uses the DONE-aware movement output but cannot alter
leader/shield/bullet/signal_B. -/
theorem authorizedDoneMove_signal (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    authSignalPair (authorizedDoneMove hψ l r) = authSignalPair (l, r) := by
  change signalPair
      ((authorizedDoneMove hψ l r).1.core,
        (authorizedDoneMove hψ l r).2.core) =
    signalPair (l.core, r.core)
  rw [authorizedDoneMove_core]
  exact doneCaptureSigMove_signal hψ l.core r.core

/-- The accepted DONE-aware pre-CHECK cut has the same K2 observation as the
actual GEN/WAIT probe-label prefix. -/
theorem doneBeforeCheck_signal (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authSignalPair (doneBeforeCheck hψ κ l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hψ l r) := by
  let b := generationBeforeMove hψ κ l r
  let q := authorizedDoneMove hψ b.1 b.2
  unfold doneBeforeCheck
  exact (authSignalPair_of_peace
      (sanitizePreCheckResetWall_peaceViewPair hψ q)).trans
    ((authorizedDoneMove_signal hψ b.1 b.2).trans
      (generationBeforeMove_signal hψ κ l r))

private theorem doneBeforeCheck_singleUse_signal (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authSignalPair (doneBeforeCheck hψ κ l r) =
      authSignalPair (singleUseBeforeCheck hψ κ l r) :=
  (doneBeforeCheck_signal hψ κ l r).trans
    (beforeCheck_signal hψ κ l r).symm

theorem doneBeforeCheck_bullets (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneBeforeCheck hψ κ l r) =
      authorizedBulletFieldPair (l, r) := by
  exact (authBullets_of_signal
      (doneBeforeCheck_singleUse_signal hψ κ l r)).trans
    (beforeCheck_bullets hψ κ l r)

/-- No preservation premise is carried: old-leader preservation is derived
from the actual DONE pre-CHECK computation and the source probe-label row. -/
theorem doneBeforeCheck_leaders (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true → (doneBeforeCheck hψ κ l r).1.core.leader = true) ∧
    (r.core.leader = true → (doneBeforeCheck hψ κ l r).2.core.leader = true) := by
  have hs := doneBeforeCheck_singleUse_signal hψ κ l r
  have ho := beforeCheck_leaders hψ κ l r
  exact ⟨
    fun hl =>
      (congrArg (fun q : AgentState 1 × AgentState 1 => q.1.leader) hs).trans
        (ho.1 hl),
    fun hr =>
      (congrArg (fun q : AgentState 1 × AgentState 1 => q.2.leader) hs).trans
        (ho.2 hr)⟩

/-- `preserveDoneCheck` either returns its inputs literally or executes the
already accepted toss-preserving CHECK. -/
theorem preserveDoneCheck_bullets (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (preserveDoneCheck hψ l r) =
      authorizedBulletFieldPair (l, r) := by
  by_cases hd : l.core.state = .done ∨ r.core.state = .done
  · rw [preserveDoneCheck_of_done hψ l r hd]
  · have hl : l.core.state ≠ .done := fun h => hd (Or.inl h)
    have hr : r.core.state ≠ .done := fun h => hd (Or.inr h)
    rw [preserveDoneCheck_of_no_done hψ l r hl hr]
    exact preserveCheck_bullets hψ l r

theorem preserveDoneCheck_leaders (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true → (preserveDoneCheck hψ l r).1.core.leader = true) ∧
    (r.core.leader = true → (preserveDoneCheck hψ l r).2.core.leader = true) := by
  by_cases hd : l.core.state = .done ∨ r.core.state = .done
  · rw [preserveDoneCheck_of_done hψ l r hd]
    exact ⟨id, id⟩
  · have hl : l.core.state ≠ .done := fun h => hd (Or.inl h)
    have hr : r.core.state ≠ .done := fun h => hd (Or.inr h)
    rw [preserveDoneCheck_of_no_done hψ l r hl hr]
    exact preserveCheck_leaders hψ l r

/-! ## DONE-aware ordinary metadata, retaining the mixed stationary writer -/

def doneThroughCheck (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let b := doneBeforeCheck hψ κ l r
  preserveDoneCheck hψ b.1 b.2

attribute [local irreducible] doneThroughCheck

theorem doneThroughCheck_bullets (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneThroughCheck hψ κ l r) =
      authorizedBulletFieldPair (l, r) := by
  unfold doneThroughCheck
  dsimp only
  exact (preserveDoneCheck_bullets hψ
      (doneBeforeCheck hψ κ l r).1 (doneBeforeCheck hψ κ l r).2).trans
    (doneBeforeCheck_bullets hψ κ l r)

theorem doneThroughCheck_leaders (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true → (doneThroughCheck hψ κ l r).1.core.leader = true) ∧
    (r.core.leader = true → (doneThroughCheck hψ κ l r).2.core.leader = true) := by
  unfold doneThroughCheck
  dsimp only
  have hb := doneBeforeCheck_leaders hψ κ l r
  have hc := preserveDoneCheck_leaders hψ
    (doneBeforeCheck hψ κ l r).1 (doneBeforeCheck hψ κ l r).2
  exact ⟨hc.1 ∘ hb.1, hc.2 ∘ hb.2⟩

theorem doneThroughCheck_domain (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneThroughCheck hψ κ l r).1.core.inProtocolDomain κ ∧
      (doneThroughCheck hψ κ l r).2.core.inProtocolDomain κ := by
  unfold doneThroughCheck
  dsimp only
  have hb := doneBeforeCheck_inProtocolDomain hψ κ l r hl hr
  exact preserveDoneCheck_inProtocolDomain hψ
    (doneBeforeCheck hψ κ l r).1 (doneBeforeCheck hψ κ l r).2 hb.1 hb.2

/-- This is the mixed dispatcher's existing post-CHECK metadata, including the
stationary persistent writer, applied to the DONE-aware CHECK result. -/
def doneOrdinaryMetadata (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let c := doneThroughCheck hψ κ l r
  let q := afterCheckMetadata hψ c.1 c.2
  markLeaderBirth (authBirth l r q) q

attribute [local irreducible] doneOrdinaryMetadata

theorem doneOrdinaryMetadata_signal (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authSignalPair (doneOrdinaryMetadata hψ κ l r) =
      authSignalPair (doneThroughCheck hψ κ l r) := by
  let c := doneThroughCheck hψ κ l r
  let q := afterCheckMetadata hψ c.1 c.2
  unfold doneOrdinaryMetadata
  exact (markBirth_signal (authBirth l r q) q).trans
    (afterCheckMetadata_signal hψ c.1 c.2)

theorem doneOrdinaryMetadata_bullets (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneOrdinaryMetadata hψ κ l r) =
      authorizedBulletFieldPair (l, r) :=
  (authBullets_of_signal (doneOrdinaryMetadata_signal hψ κ l r)).trans
    (doneThroughCheck_bullets hψ κ l r)

theorem doneOrdinaryMetadata_leaders (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneOrdinaryMetadata hψ κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneOrdinaryMetadata hψ κ l r).2.core.leader = true) := by
  have hs := doneOrdinaryMetadata_signal hψ κ l r
  have hc := doneThroughCheck_leaders hψ κ l r
  exact ⟨
    fun hl => (congrArg (fun q => q.1.leader) hs).trans (hc.1 hl),
    fun hr => (congrArg (fun q => q.2.leader) hs).trans (hc.2 hr)⟩

theorem doneOrdinaryMetadata_domain (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneOrdinaryMetadata hψ κ l r).1.core.inProtocolDomain κ ∧
      (doneOrdinaryMetadata hψ κ l r).2.core.inProtocolDomain κ := by
  let c := doneThroughCheck hψ κ l r
  have hc := doneThroughCheck_domain hψ l r hl hr
  have hw := afterCheckMetadata_domain hψ c.1 c.2 hc.1 hc.2
  unfold doneOrdinaryMetadata
  exact markLeaderBirth_inProtocolDomain _ _ hw

/-- Same responder-delete / initiator-wait / ordinary branch order as the
mixed dispatcher.  Only the ordinary branch is DONE-aware. -/
def doneMetadataAuthorized (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hψ l0 r0
  else if deletionActive l0 then (l0, r0)
  else doneOrdinaryMetadata hψ κ l0 r0

attribute [local irreducible] doneMetadataAuthorized


/-- Explicit coverage certificate for the unchanged disposal priority. -/
theorem doneMetadataAuthorized_right_priority (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = true) :
    doneMetadataAuthorized hψ κ l r =
      authorizedEliminateSig hψ (normalizeDeletion l) (normalizeDeletion r) := by
  unfold doneMetadataAuthorized
  simp only [hr, if_true]

theorem doneMetadataAuthorized_left_priority (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = true) :
    doneMetadataAuthorized hψ κ l r =
      (normalizeDeletion l, normalizeDeletion r) := by
  unfold doneMetadataAuthorized
  simp only [hr, Bool.false_eq_true, if_false, hl, if_true]

theorem doneMetadataAuthorized_ordinary (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = false) :
    doneMetadataAuthorized hψ κ l r =
      doneOrdinaryMetadata hψ κ (normalizeDeletion l) (normalizeDeletion r) := by
  unfold doneMetadataAuthorized
  simp only [hr, Bool.false_eq_true, if_false, hl]

theorem doneMetadataAuthorized_branch_coverage (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (deletionActive (normalizeDeletion r) = true ∧
      doneMetadataAuthorized hψ κ l r =
        authorizedEliminateSig hψ (normalizeDeletion l) (normalizeDeletion r)) ∨
    (deletionActive (normalizeDeletion r) = false ∧
      deletionActive (normalizeDeletion l) = true ∧
      doneMetadataAuthorized hψ κ l r =
        (normalizeDeletion l, normalizeDeletion r)) ∨
    (deletionActive (normalizeDeletion r) = false ∧
      deletionActive (normalizeDeletion l) = false ∧
      doneMetadataAuthorized hψ κ l r =
        doneOrdinaryMetadata hψ κ (normalizeDeletion l) (normalizeDeletion r)) := by
  cases hr : deletionActive (normalizeDeletion r) with
  | true =>
      exact Or.inl ⟨rfl,
        doneMetadataAuthorized_right_priority hψ κ l r hr⟩
  | false =>
      cases hl : deletionActive (normalizeDeletion l) with
      | true =>
          exact Or.inr (Or.inl ⟨rfl, rfl,
            doneMetadataAuthorized_left_priority hψ κ l r hr hl⟩)
      | false =>
          exact Or.inr (Or.inr ⟨rfl, rfl,
            doneMetadataAuthorized_ordinary hψ κ l r hr hl⟩)

/-- Source-derived bullet preservation on every metadata priority branch. -/
theorem doneMetadataAuthorized_bullets (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneMetadataAuthorized hψ κ l r) =
      authorizedBulletFieldPair (l, r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have h0 := authBullets_of_signal (normalize_pair_signal l r)
  cases hr : deletionActive (normalizeDeletion r) with
  | true =>
      rw [doneMetadataAuthorized_right_priority hψ κ l r hr]
      exact (authBullets_of_signal (eliminate_signal hψ l0 r0)).trans h0
  | false =>
      cases hl : deletionActive (normalizeDeletion l) with
      | true =>
          rw [doneMetadataAuthorized_left_priority hψ κ l r hr hl]
          exact h0
      | false =>
          rw [doneMetadataAuthorized_ordinary hψ κ l r hr hl]
          exact (doneOrdinaryMetadata_bullets hψ κ l0 r0).trans h0

/-- No metadata branch deletes an old leader.  Collision/K2 remains the only
physical leader-deletion stage in this combined row. -/
theorem doneMetadataAuthorized_leaders (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneMetadataAuthorized hψ κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneMetadataAuthorized hψ κ l r).2.core.leader = true) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 : l0.core.leader = l.core.leader :=
    congrArg (fun u : AgentState 1 => u.leader) (normalize_signal l)
  have hr0 : r0.core.leader = r.core.leader :=
    congrArg (fun u : AgentState 1 => u.leader) (normalize_signal r)
  cases hdR : deletionActive (normalizeDeletion r) with
  | true =>
      rw [doneMetadataAuthorized_right_priority hψ κ l r hdR]
      have he := eliminate_signal hψ l0 r0
      exact ⟨
        fun hl => (congrArg (fun q => q.1.leader) he).trans (hl0.trans hl),
        fun hr => (congrArg (fun q => q.2.leader) he).trans (hr0.trans hr)⟩
  | false =>
      cases hdL : deletionActive (normalizeDeletion l) with
      | true =>
          rw [doneMetadataAuthorized_left_priority hψ κ l r hdR hdL]
          exact ⟨fun hl => hl0.trans hl, fun hr => hr0.trans hr⟩
      | false =>
          rw [doneMetadataAuthorized_ordinary hψ κ l r hdR hdL]
          have he := doneOrdinaryMetadata_leaders hψ κ l0 r0
          exact ⟨fun hl => he.1 (hl0.trans hl),
            fun hr => he.2 (hr0.trans hr)⟩

/-- Domain closure follows the actual branch implementation; no output-domain
assumption is introduced. -/
theorem doneMetadataAuthorized_domain (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneMetadataAuthorized hψ κ l r).1.core.inProtocolDomain κ ∧
      (doneMetadataAuthorized hψ κ l r).2.core.inProtocolDomain κ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  cases hdR : deletionActive (normalizeDeletion r) with
  | true =>
      rw [doneMetadataAuthorized_right_priority hψ κ l r hdR]
      exact authorizedReconcile_inProtocolDomain (eliminateSig hψ) l0 r0
        (eliminateSig_inProtocolDomain hψ l0.core r0.core hl0 hr0)
  | false =>
      cases hdL : deletionActive (normalizeDeletion l) with
      | true =>
          rw [doneMetadataAuthorized_left_priority hψ κ l r hdR hdL]
          exact ⟨hl0, hr0⟩
      | false =>
          rw [doneMetadataAuthorized_ordinary hψ κ l r hdR hdL]
          exact doneOrdinaryMetadata_domain hψ l0 r0 hl0 hr0

/-! ## Existing finite reification and one-expiry-per-role shell -/

def doneMetadataBounded (hψ : 0 < ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := doneMetadataAuthorized hψ κ l.erase r.erase
  let hq := doneMetadataAuthorized_domain hψ l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

attribute [local irreducible] doneMetadataBounded

theorem doneMetadataBounded_erase (hψ : 0 < ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    ((doneMetadataBounded hψ l r).1.erase,
      (doneMetadataBounded hψ l r).2.erase) =
      doneMetadataAuthorized hψ κ l.erase r.erase := by
  unfold doneMetadataBounded
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

/-- Entry disposal, DONE-aware metadata and exactly one priority-expiry call
for each endpoint role. -/
def doneMetadata (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := doneMetadataBounded hψ l0.core r0.core
  (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩,
    deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)

attribute [local irreducible] doneMetadata

/-- Exact observed erasure through bounded conversion and both real expiry
calls. -/
theorem doneMetadata_observation (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (doneMetadata hψ l r).1,
      observeCell (doneMetadata hψ l r).2) =
      authSignalPair (doneMetadataAuthorized hψ κ
        (prepareExpiringDisposal hψ l).core.erase
        (prepareExpiringDisposal hψ r).core.erase) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := doneMetadataBounded hψ l0.core r0.core
  have he := congrArg authSignalPair
    (doneMetadataBounded_erase hψ l0.core r0.core)
  have hx :
      (observeCell (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩),
        observeCell (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)) =
      (observeCell (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ),
        observeCell (⟨q.2, r0.stall⟩ : ExpiringAgentState ψ κ τ)) :=
    Prod.ext (priority_expiry_observation l0 (⟨q.1, l0.stall⟩))
      (priority_expiry_observation r0 (⟨q.2, r0.stall⟩))
  unfold doneMetadata
  exact hx.trans he

/-- The actual expiring metadata preserves every old leader, including through
entry-disposal preparation, bounded reification and timer expiry. -/
theorem doneMetadata_existing_leaders (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (l.core.core.leader = true →
      (doneMetadata hψ l r).1.core.core.leader = true) ∧
    (r.core.core.leader = true →
      (doneMetadata hψ l r).2.core.core.leader = true) := by
  have hs := doneMetadataAuthorized_leaders hψ κ
    (prepareExpiringDisposal hψ l).core.erase
    (prepareExpiringDisposal hψ r).core.erase
  have he := doneMetadata_observation hψ l r
  have hl := congrArg AgentState.leader (prepareExpiring_signal hψ l)
  have hr := congrArg AgentState.leader (prepareExpiring_signal hψ r)
  exact ⟨fun h => (congrArg (fun q => q.1.leader) he).trans (hs.1 (hl.trans h)),
    fun h => (congrArg (fun q => q.2.leader) he).trans (hs.2 (hr.trans h))⟩

/-- The three actual bullet fields are unchanged by the complete metadata
adapter.  These are physical endpoint equalities, not a post-state assumption. -/
theorem doneMetadata_bullets (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    ((doneMetadata hψ l r).1.core.core.shield = l.core.core.shield ∧
      (doneMetadata hψ l r).1.core.core.bullet = l.core.core.bullet ∧
      (doneMetadata hψ l r).1.core.core.signal_B = l.core.core.signal_B) ∧
    ((doneMetadata hψ l r).2.core.core.shield = r.core.core.shield ∧
      (doneMetadata hψ l r).2.core.core.bullet = r.core.core.bullet ∧
      (doneMetadata hψ l r).2.core.core.signal_B = r.core.core.signal_B) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  have he := doneMetadata_observation hψ l r
  have hb := doneMetadataAuthorized_bullets hψ κ l0.core.erase r0.core.erase
  have hpL := prepareExpiring_signal hψ l
  have hpR := prepareExpiring_signal hψ r

  have eLs := congrArg (fun q : AgentState 1 × AgentState 1 => q.1.shield) he
  have eLb := congrArg (fun q : AgentState 1 × AgentState 1 => q.1.bullet) he
  have eLz := congrArg (fun q : AgentState 1 × AgentState 1 => q.1.signal_B) he
  have eRs := congrArg (fun q : AgentState 1 × AgentState 1 => q.2.shield) he
  have eRb := congrArg (fun q : AgentState 1 × AgentState 1 => q.2.bullet) he
  have eRz := congrArg (fun q : AgentState 1 × AgentState 1 => q.2.signal_B) he

  have bLs := congrArg (fun q => q.1.shield) hb
  have bLb := congrArg (fun q => q.1.bullet) hb
  have bLz := congrArg (fun q => q.1.signal_B) hb
  have bRs := congrArg (fun q => q.2.shield) hb
  have bRb := congrArg (fun q => q.2.bullet) hb
  have bRz := congrArg (fun q => q.2.signal_B) hb

  have pLs := congrArg AgentState.shield hpL
  have pLb := congrArg AgentState.bullet hpL
  have pLz := congrArg AgentState.signal_B hpL
  have pRs := congrArg AgentState.shield hpR
  have pRb := congrArg AgentState.bullet hpR
  have pRz := congrArg AgentState.signal_B hpR

  change (doneMetadata hψ l r).1.core.core.shield =
    (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).1.core.shield at eLs
  change (doneMetadata hψ l r).1.core.core.bullet =
    (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).1.core.bullet at eLb
  change (doneMetadata hψ l r).1.core.core.signal_B =
    (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).1.core.signal_B at eLz
  change (doneMetadata hψ l r).2.core.core.shield =
    (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).2.core.shield at eRs
  change (doneMetadata hψ l r).2.core.core.bullet =
    (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).2.core.bullet at eRb
  change (doneMetadata hψ l r).2.core.core.signal_B =
    (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).2.core.signal_B at eRz

  change (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).1.core.shield =
    l0.core.core.shield at bLs
  change (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).1.core.bullet =
    l0.core.core.bullet at bLb
  change (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).1.core.signal_B =
    l0.core.core.signal_B at bLz
  change (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).2.core.shield =
    r0.core.core.shield at bRs
  change (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).2.core.bullet =
    r0.core.core.bullet at bRb
  change (doneMetadataAuthorized hψ κ l0.core.erase r0.core.erase).2.core.signal_B =
    r0.core.core.signal_B at bRz

  change l0.core.core.shield = l.core.core.shield at pLs
  change l0.core.core.bullet = l.core.core.bullet at pLb
  change l0.core.core.signal_B = l.core.core.signal_B at pLz
  change r0.core.core.shield = r.core.core.shield at pRs
  change r0.core.core.bullet = r.core.core.bullet at pRb
  change r0.core.core.signal_B = r.core.core.signal_B at pRz

  constructor
  · exact ⟨eLs.trans (bLs.trans pLs), eLb.trans (bLb.trans pLb),
      eLz.trans (bLz.trans pLz)⟩
  · exact ⟨eRs.trans (bRs.trans pRs), eRb.trans (bRb.trans pRb),
      eRz.trans (bRz.trans pRz)⟩

/-- The source-derived raw-domain proof is what licenses reification above;
after reification/expiry the actual result remains in the same finite carrier. -/
theorem doneMetadata_domain (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (doneMetadata hψ l r).1.core.core.erase.inProtocolDomain κ ∧
      (doneMetadata hψ l r).2.core.core.erase.inProtocolDomain κ :=
  ⟨(doneMetadata hψ l r).1.core.core.erase_inProtocolDomain,
    (doneMetadata hψ l r).2.core.core.erase_inProtocolDomain⟩

/-! ## The unchanged newborn plus collision/K2 tail -/

def doneBirthEvent (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) : Bool :=
  let q := doneMetadata hψ l r
  newborn l q.1 || newborn r q.2

/-- No metadata priority returns early: every branch reaches the existing
newborn initialization and actual collision/K2 stage inside `finalPhysical`. -/
def doneRow (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := doneMetadata hψ l r
  finalPhysical hψ l r q.1 q.2

attribute [local irreducible] doneRow

theorem doneRow_metadata_frame (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    putSignals (doneRow hψ l r).1 (observeCell (doneMetadata hψ l r).1) =
        (doneMetadata hψ l r).1 ∧
      putSignals (doneRow hψ l r).2 (observeCell (doneMetadata hψ l r).2) =
        (doneMetadata hψ l r).2 := by
  unfold doneRow
  exact finalPhysical_frame hψ l r _ _

theorem doneRow_metadata_nonK2 (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    nonK2 (doneRow hψ l r).1 = nonK2 (doneMetadata hψ l r).1 ∧
      nonK2 (doneRow hψ l r).2 = nonK2 (doneMetadata hψ l r).2 := by
  unfold doneRow
  exact finalPhysical_nonK2 hψ l r _ _

/-- The only timer calls in this combined row are the two calls inside
`doneMetadata`, once per endpoint role. -/
theorem doneRow_timers_once (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := doneMetadataBounded hψ l0.core r0.core
    (doneRow hψ l r).1.stall =
        (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩).stall ∧
      (doneRow hψ l r).2.stall =
        (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩).stall := by
  have h := doneRow_metadata_frame hψ l r
  unfold doneMetadata at h
  have hl := congrArg ExpiringAgentState.stall h.1
  have hr := congrArg ExpiringAgentState.stall h.2
  exact ⟨hl, hr⟩

theorem doneRow_domain (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (doneRow hψ l r).1.core.core.erase.inProtocolDomain κ ∧
      (doneRow hψ l r).2.core.core.erase.inProtocolDomain κ :=
  ⟨(doneRow hψ l r).1.core.core.erase_inProtocolDomain,
    (doneRow hψ l r).2.core.core.erase_inProtocolDomain⟩

#print axioms K2BirthDispatcherDone.doneCaptureSigMove_signal
#print axioms K2BirthDispatcherDone.doneBeforeCheck_signal
#print axioms K2BirthDispatcherDone.doneBeforeCheck_bullets
#print axioms K2BirthDispatcherDone.doneBeforeCheck_leaders
#print axioms K2BirthDispatcherDone.preserveDoneCheck_bullets
#print axioms K2BirthDispatcherDone.preserveDoneCheck_leaders
#print axioms K2BirthDispatcherDone.doneThroughCheck_domain
#print axioms K2BirthDispatcherDone.doneOrdinaryMetadata_domain
#print axioms K2BirthDispatcherDone.doneMetadataAuthorized_branch_coverage
#print axioms K2BirthDispatcherDone.doneMetadataAuthorized_bullets
#print axioms K2BirthDispatcherDone.doneMetadataAuthorized_leaders
#print axioms K2BirthDispatcherDone.doneMetadataAuthorized_domain
#print axioms K2BirthDispatcherDone.doneMetadataBounded_erase
#print axioms K2BirthDispatcherDone.doneMetadata_observation
#print axioms K2BirthDispatcherDone.doneMetadata_existing_leaders
#print axioms K2BirthDispatcherDone.doneMetadata_bullets
#print axioms K2BirthDispatcherDone.doneRow_metadata_frame
#print axioms K2BirthDispatcherDone.doneRow_metadata_nonK2
#print axioms K2BirthDispatcherDone.doneRow_timers_once
#print axioms K2BirthDispatcherDone.doneRow_domain

end K2BirthDispatcherDone

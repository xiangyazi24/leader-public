import Leader.Wu.Birth.ShortDoneTerminalEntryCut
import Leader.Wu.Elimination.BirthDispatcherDoneNormalize


/-!
# Terminal-entry WAIT on the real DONE host


The ordinary DONE branch starts from `doneThroughCheckEntryWidth`; the existing
post-CHECK `afterCheckMetadataWidth` is unchanged.  The responder-delete /
initiator-wait / ordinary priority, birth marking, finite reification, disposal
preparation, two role-local expiry calls, endpoint normalization and one
`finalPhysical` tail are the existing ones.
-/


namespace BirthShortDoneTerminalHost


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol PPLLNoCheckBirthLeaderFrames
  BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitDomainWitness BirthStationaryWrite K2OutputSafety
  PPLLTerminalEqualSupportRepair BirthSigMoveDisposalRepair


open K2BirthDispatcher K2BirthDispatcherDone ExpiringK2Projection
  K2BirthLeaderNormalize BirthShortDoneCuts BirthShortDoneTerminalEntryCut


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


variable {ψ width κ τ : Nat}


/-! ## Repaired ordinary and authorized metadata host -/


/-- The repaired CHECK output is the first line of ordinary metadata.  The
post-CHECK SUPPRESS/stationary-WRITE helper is exactly the frozen width helper. -/
def doneOrdinaryMetadataEntryWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let c := doneThroughCheckEntryWidth hψ hwidth hle κ l r
  let q := afterCheckMetadataWidth hψ hwidth hle c.1 c.2
  markLeaderBirth (authBirth l r q) q


theorem doneOrdinaryMetadataEntryWidth_domain
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  have hc := doneThroughCheckEntryWidth_domain hψ hwidth hle l r hl hr
  unfold doneOrdinaryMetadataEntryWidth
  generalize doneThroughCheckEntryWidth hψ hwidth hle κ l r = c at *
  have hw := afterCheckMetadataWidth_domain (κ := κ) hψ hwidth hle c.1 c.2 hc.1 hc.2
  exact markLeaderBirth_inProtocolDomain _ _ hw


theorem doneOrdinaryMetadataEntryWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneOrdinaryMetadataEntryWidth hψ hψ (Nat.le_refl ψ) κ l r =
      K2BirthDispatcherDone.doneOrdinaryMetadata hψ κ l r := by
  let cS := doneThroughCheckEntryWidth hψ hψ (Nat.le_refl ψ) κ l r
  let cO := K2BirthDispatcherDone.doneThroughCheck hψ κ l r
  have hc : cS = cO := doneThroughCheckEntryWidth_full hψ κ l r
  have hq :
      afterCheckMetadataWidth hψ hψ (Nat.le_refl ψ) cS.1 cS.2 =
        afterCheckMetadata hψ cO.1 cO.2 := by
    calc
      afterCheckMetadataWidth hψ hψ (Nat.le_refl ψ) cS.1 cS.2 =
          afterCheckMetadata hψ cS.1 cS.2 :=
        afterCheckMetadataWidth_full hψ cS.1 cS.2
      _ = afterCheckMetadata hψ cO.1 cO.2 :=
        congrArg
          (fun c : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
            afterCheckMetadata hψ c.1 c.2) hc
  let finish :
      (AuthorizedAgentState ψ × AuthorizedAgentState ψ) →
        (AuthorizedAgentState ψ × AuthorizedAgentState ψ) := fun q =>
    markLeaderBirth (authBirth l r q) q
  change
    finish (afterCheckMetadataWidth hψ hψ (Nat.le_refl ψ) cS.1 cS.2) =
      finish (afterCheckMetadata hψ cO.1 cO.2)
  exact congrArg finish hq


/-- Exact accepted responder-delete / initiator-wait / ordinary priority. -/
def doneMetadataAuthorizedEntryWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hψ l0 r0
  else if deletionActive l0 then (l0, r0)
  else doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l0 r0


theorem doneMetadataAuthorizedEntryWidth_domain
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  unfold doneMetadataAuthorizedEntryWidth
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hψ) l0 r0
      (eliminateSig_inProtocolDomain hψ l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · exact doneOrdinaryMetadataEntryWidth_domain
        hψ hwidth hle l0 r0 hl0 hr0


theorem doneMetadataAuthorizedEntryWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneMetadataAuthorizedEntryWidth hψ hψ (Nat.le_refl ψ) κ l r =
      K2BirthDispatcherDone.doneMetadataAuthorized hψ κ l r := by
  unfold doneMetadataAuthorizedEntryWidth
    K2BirthDispatcherDone.doneMetadataAuthorized
  dsimp only
  split
  · rfl
  · split
    · rfl
    · exact doneOrdinaryMetadataEntryWidth_full hψ κ _ _


/-! ## The actual finite and expiring consumers -/


/-- Reification uses the new authorized host's actual domain proof. -/
def doneMetadataBoundedEntryWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l.erase r.erase
  let hq := doneMetadataAuthorizedEntryWidth_domain hψ hwidth hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)


/-- This is the concrete bridge from the finite carrier back to the repaired
raw authorized host; the terminal-entry cut is therefore not detached. -/
theorem doneMetadataBoundedEntryWidth_erase
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    ((doneMetadataBoundedEntryWidth hψ hwidth hle l r).1.erase,
      (doneMetadataBoundedEntryWidth hψ hwidth hle l r).2.erase) =
      doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l.erase r.erase := by
  unfold doneMetadataBoundedEntryWidth
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]


theorem doneMetadataBoundedEntryWidth_full (hψ : 0 < ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    doneMetadataBoundedEntryWidth hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDispatcherDone.doneMetadataBounded hψ l r := by
  unfold doneMetadataBoundedEntryWidth K2BirthDispatcherDone.doneMetadataBounded
  dsimp only
  simp only [doneMetadataAuthorizedEntryWidth_full hψ κ]


/-- Same disposal preparation and exactly one priority-expiry call per role. -/
def doneMetadataEntryWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core
  (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩,
    deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)


theorem doneMetadataEntryWidth_full (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    doneMetadataEntryWidth hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDispatcherDone.doneMetadata hψ l r := by
  unfold doneMetadataEntryWidth K2BirthDispatcherDone.doneMetadata
  dsimp only
  rw [doneMetadataBoundedEntryWidth_full (κ := κ) hψ]


theorem doneMetadataEntryWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    (doneMetadataEntryWidth hψ hwidth hle l r).1.core.core.erase.inProtocolDomain κ ∧
      (doneMetadataEntryWidth hψ hwidth hle l r).2.core.core.erase.inProtocolDomain κ :=
  ⟨(doneMetadataEntryWidth hψ hwidth hle l r).1.core.core.erase_inProtocolDomain,
    (doneMetadataEntryWidth hψ hwidth hle l r).2.core.core.erase_inProtocolDomain⟩


/-! ## Existing current-leader normalization and the single physical tail -/


/-- No new state or K2 wrapper: normalize only the two computed endpoints. -/
def metadata (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := doneMetadataEntryWidth hψ hwidth hle l r
  (K2BirthLeaderNormalize.normalizeLeader hψ q.1,
    K2BirthLeaderNormalize.normalizeLeader hψ q.2)


theorem metadata_full (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    metadata hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDoneNormalize.metadata hψ l r := by
  unfold metadata K2BirthDoneNormalize.metadata
  dsimp only
  rw [doneMetadataEntryWidth_full hψ l r]


/-- Exactly one existing `finalPhysical`, with original endpoints first. -/
def row (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := metadata hψ hwidth hle l r
  K2BirthDispatcher.finalPhysical hψ l r q.1 q.2


theorem row_full (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    row hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDoneNormalize.row hψ l r := by
  unfold row K2BirthDoneNormalize.row
  rw [metadata_full hψ l r]


/-- Concrete executable witness for the real physical host: the row is fed by
this module's bounded host, exactly two expiry calls, normalization of those two
results, and one final physical call. -/
theorem row_real_host_witness (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core
    let eL := deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩
    let eR := deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩
    row hψ hwidth hle l r =
      K2BirthDispatcher.finalPhysical hψ l r
        (K2BirthLeaderNormalize.normalizeLeader hψ eL)
        (K2BirthLeaderNormalize.normalizeLeader hψ eR) := by
  unfold row metadata doneMetadataEntryWidth
  rfl


/-- The unique physical tail changes only its K2 signals relative to the
normalized computed metadata; this is the non-detached physical attachment. -/
theorem row_metadata_frame (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    putSignals (row hψ hwidth hle l r).1
        (observeCell (metadata hψ hwidth hle l r).1) =
        (metadata hψ hwidth hle l r).1 ∧
      putSignals (row hψ hwidth hle l r).2
        (observeCell (metadata hψ hwidth hle l r).2) =
        (metadata hψ hwidth hle l r).2 := by
  unfold row
  dsimp only
  exact K2BirthDispatcher.finalPhysical_frame hψ l r _ _


theorem row_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    (row hψ hwidth hle l r).1.core.core.erase.inProtocolDomain κ ∧
      (row hψ hwidth hle l r).2.core.core.erase.inProtocolDomain κ :=
  ⟨(row hψ hwidth hle l r).1.core.core.erase_inProtocolDomain,
    (row hψ hwidth hle l r).2.core.core.erase_inProtocolDomain⟩


#print axioms BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth_domain
#print axioms BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth_full
#print axioms BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth_domain
#print axioms BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth_full
#print axioms BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth_erase
#print axioms BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth_full
#print axioms BirthShortDoneTerminalHost.doneMetadataEntryWidth_full
#print axioms BirthShortDoneTerminalHost.doneMetadataEntryWidth_domain
#print axioms BirthShortDoneTerminalHost.metadata_full
#print axioms BirthShortDoneTerminalHost.row_full
#print axioms BirthShortDoneTerminalHost.row_real_host_witness
#print axioms BirthShortDoneTerminalHost.row_metadata_frame
#print axioms BirthShortDoneTerminalHost.row_domain


end BirthShortDoneTerminalHost

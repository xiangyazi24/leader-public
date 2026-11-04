import Leader.Wu.Birth.ShortDoneCuts
import Leader.Wu.Elimination.BirthDispatcherDoneNormalize

/-!
# Short-width DONE dispatcher with current-leader normalization

The only changed metadata calls are those already frozen in
`BirthShortDoneCuts.doneMetadataWidth`.  Each computed endpoint is then passed
through the existing `normalizeLeader`, followed by exactly one existing
`finalPhysical` call whose first two arguments are the original endpoints.
Thus newborn detection remains the real old/computed leader-bit test.
-/

namespace BirthShortDoneDispatcher

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  LDSinkBoundedKernel LDSinkKernelC LDSinkTwoGapEpochSuccessor
  ExpiringK2Projection K2OutputSafety

open K2BirthDispatcher K2BirthDispatcherDone K2BirthLeaderNormalize
  BirthShortDoneCuts

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ width κ τ n : Nat}

/-! ## Exact full-width bridge, derived from the frozen definitions -/

theorem doneMetadataBoundedWidth_full (hψ : 0 < ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    BirthShortDoneCuts.doneMetadataBoundedWidth
        hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDispatcherDone.doneMetadataBounded hψ l r := by
  unfold BirthShortDoneCuts.doneMetadataBoundedWidth
    K2BirthDispatcherDone.doneMetadataBounded
  dsimp only
  simp only [BirthShortDoneCuts.doneMetadataAuthorizedWidth_full hψ κ]

theorem doneMetadataWidth_full (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    BirthShortDoneCuts.doneMetadataWidth hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDispatcherDone.doneMetadata hψ l r := by
  unfold BirthShortDoneCuts.doneMetadataWidth
    K2BirthDispatcherDone.doneMetadata
  dsimp only
  rw [doneMetadataBoundedWidth_full (κ := κ) hψ]

/-! ## Width-parametric normalized metadata and the one physical tail -/

/-- Short-width DONE metadata/expiry, then endpoint-local current-leader
normalization. -/
def metadata (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r
  (K2BirthLeaderNormalize.normalizeLeader hψ q.1,
    K2BirthLeaderNormalize.normalizeLeader hψ q.2)

/-- The actual birth bit compares the ORIGINAL endpoints with the normalized
computed endpoints. -/
def birthEvent (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) : Bool :=
  let q := metadata hψ hwidth hle l r
  K2BirthDispatcher.newborn l q.1 || K2BirthDispatcher.newborn r q.2

/-- Exactly one existing physical tail, with ORIGINAL endpoints first. -/
def row (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := metadata hψ hwidth hle l r
  K2BirthDispatcher.finalPhysical hψ l r q.1 q.2

attribute [local irreducible] metadata birthEvent row

theorem metadata_full (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    metadata hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDoneNormalize.metadata hψ l r := by
  unfold metadata K2BirthDoneNormalize.metadata
  dsimp only
  rw [doneMetadataWidth_full hψ l r]

theorem birthEvent_full (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    birthEvent hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDoneNormalize.birthEvent hψ l r := by
  unfold birthEvent K2BirthDoneNormalize.birthEvent
  rw [metadata_full hψ l r]

/-- Exact requested full-width regression: the complete executable row is the
published DONE-normalize row at width = psi. -/
theorem row_full (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    row hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDoneNormalize.row hψ l r := by
  unfold row K2BirthDoneNormalize.row
  rw [metadata_full hψ l r]

/-- Restoring the pre-normalization label recovers the complete short-width
metadata record, including authorization and timer. -/
theorem metadata_field_frame (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    K2BirthLeaderNormalize.putLabel (metadata hψ hwidth hle l r).1
        (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.core.core.label =
        (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1 ∧
      K2BirthLeaderNormalize.putLabel (metadata hψ hwidth hle l r).2
        (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.core.core.label =
        (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2 := by
  unfold metadata
  dsimp only
  exact ⟨K2BirthLeaderNormalize.normalizeLeader_field_frame hψ _,
    K2BirthLeaderNormalize.normalizeLeader_field_frame hψ _⟩

/-- Normalization is invisible to the exact four-field K2 observation. -/
theorem metadata_observation_raw (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (metadata hψ hwidth hle l r).1,
      observeCell (metadata hψ hwidth hle l r).2) =
    (observeCell (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1,
      observeCell (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2) := by
  unfold metadata
  dsimp only
  rw [K2BirthLeaderNormalize.normalizeLeader_observation,
    K2BirthLeaderNormalize.normalizeLeader_observation]

/-- Existing leaders survive the actual short-width metadata/expiry computation. -/
theorem raw_existing_leaders (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    (l.core.core.leader = true →
      (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.core.core.leader = true) ∧
    (r.core.core.leader = true →
      (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.core.core.leader = true) := by
  have hs := BirthShortDoneCuts.doneMetadataAuthorizedWidth_leaders
    hψ hwidth hle κ
    (prepareExpiringDisposal hψ l).core.erase
    (prepareExpiringDisposal hψ r).core.erase
  have he := BirthShortDoneCuts.doneMetadataWidth_observation
    hψ hwidth hle l r
  have hl := congrArg AgentState.leader (prepareExpiring_signal hψ l)
  have hr := congrArg AgentState.leader (prepareExpiring_signal hψ r)
  exact ⟨
    fun h => (congrArg (fun q => q.1.leader) he).trans (hs.1 (hl.trans h)),
    fun h => (congrArg (fun q => q.2.leader) he).trans (hs.2 (hr.trans h))⟩

/-- The actual short-width metadata/expiry computation preserves the three
non-leader K2 fields endpointwise. -/
theorem raw_bullets (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    ((BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.core.core.shield =
        l.core.core.shield ∧
      (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.core.core.bullet =
        l.core.core.bullet ∧
      (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.core.core.signal_B =
        l.core.core.signal_B) ∧
    ((BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.core.core.shield =
        r.core.core.shield ∧
      (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.core.core.bullet =
        r.core.core.bullet ∧
      (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.core.core.signal_B =
        r.core.core.signal_B) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  have he := BirthShortDoneCuts.doneMetadataWidth_observation hψ hwidth hle l r
  have hb := BirthShortDoneCuts.doneMetadataAuthorizedWidth_bullets
    hψ hwidth hle κ l0.core.erase r0.core.erase
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
  change (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.core.core.shield =
    (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).1.core.shield at eLs
  change (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.core.core.bullet =
    (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).1.core.bullet at eLb
  change (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.core.core.signal_B =
    (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).1.core.signal_B at eLz
  change (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.core.core.shield =
    (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).2.core.shield at eRs
  change (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.core.core.bullet =
    (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).2.core.bullet at eRb
  change (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.core.core.signal_B =
    (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).2.core.signal_B at eRz
  change (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).1.core.shield = l0.core.core.shield at bLs
  change (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).1.core.bullet = l0.core.core.bullet at bLb
  change (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).1.core.signal_B = l0.core.core.signal_B at bLz
  change (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).2.core.shield = r0.core.core.shield at bRs
  change (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).2.core.bullet = r0.core.core.bullet at bRb
  change (BirthShortDoneCuts.doneMetadataAuthorizedWidth hψ hwidth hle κ l0.core.erase r0.core.erase).2.core.signal_B = r0.core.core.signal_B at bRz
  change l0.core.core.shield = l.core.core.shield at pLs
  change l0.core.core.bullet = l.core.core.bullet at pLb
  change l0.core.core.signal_B = l.core.core.signal_B at pLz
  change r0.core.core.shield = r.core.core.shield at pRs
  change r0.core.core.bullet = r.core.core.bullet at pRb
  change r0.core.core.signal_B = r.core.core.signal_B at pRz
  exact ⟨
    ⟨eLs.trans (bLs.trans pLs), eLb.trans (bLb.trans pLb),
      eLz.trans (bLz.trans pLz)⟩,
    ⟨eRs.trans (bRs.trans pRs), eRb.trans (bRb.trans pRb),
      eRz.trans (bRz.trans pRz)⟩⟩

private theorem raw_signal_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ)
    (hn : birthEvent hψ hwidth hle l r = false) :
    (observeCell (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1,
      observeCell (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2) =
      (observeCell l, observeCell r) := by
  have hnb :
      K2BirthDispatcher.newborn l (metadata hψ hwidth hle l r).1 = false ∧
      K2BirthDispatcher.newborn r (metadata hψ hwidth hle l r).2 = false := by
    simpa only [birthEvent, Bool.or_eq_false_iff] using hn
  have hrawL :
      K2BirthDispatcher.newborn l
        (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1 = false := by
    have h := hnb.1
    unfold metadata at h
    dsimp only at h
    simpa only [K2BirthLeaderNormalize.newborn_normalize] using h
  have hrawR :
      K2BirthDispatcher.newborn r
        (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2 = false := by
    have h := hnb.2
    unfold metadata at h
    dsimp only at h
    simpa only [K2BirthLeaderNormalize.newborn_normalize] using h
  have hp := raw_existing_leaders hψ hwidth hle l r
  have hb := raw_bullets hψ hwidth hle l r
  have hleadL :
      (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.core.core.leader =
        l.core.core.leader := by
    cases hl : l.core.core.leader with
    | false => simpa [K2BirthDispatcher.newborn, hl] using hrawL
    | true => simpa [hl] using (hp.1 hl)
  have hleadR :
      (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.core.core.leader =
        r.core.core.leader := by
    cases hr : r.core.core.leader with
    | false => simpa [K2BirthDispatcher.newborn, hr] using hrawR
    | true => simpa [hr] using (hp.2 hr)
  apply Prod.ext
  · unfold ExpiringK2Projection.observeCell K2OutputSafety.signalView
    apply congrArg PPLLNoCheckBirthConditionTwoProtocol.PeaceView.toState
    apply PPLLNoCheckBirthConditionTwoPhysical.PeaceView.ext
    · exact hleadL
    · rfl
    · exact hb.1.1
    · exact hb.1.2.1
    · exact hb.1.2.2
  · unfold ExpiringK2Projection.observeCell K2OutputSafety.signalView
    apply congrArg PPLLNoCheckBirthConditionTwoProtocol.PeaceView.toState
    apply PPLLNoCheckBirthConditionTwoPhysical.PeaceView.ext
    · exact hleadR
    · rfl
    · exact hb.2.1
    · exact hb.2.2.1
    · exact hb.2.2.2

/-- The actual NEW no-birth Boolean gives exact four-field equality before the
one physical collision/K2 tail. -/
theorem metadata_signal_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ)
    (hn : birthEvent hψ hwidth hle l r = false) :
    (observeCell (metadata hψ hwidth hle l r).1,
      observeCell (metadata hψ hwidth hle l r).2) =
      (observeCell l, observeCell r) :=
  (metadata_observation_raw hψ hwidth hle l r).trans
    (raw_signal_of_no_birth hψ hwidth hle l r hn)

/-- The one physical tail frames the normalized computed metadata. -/
theorem row_metadata_frame (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    putSignals (row hψ hwidth hle l r).1
        (observeCell (metadata hψ hwidth hle l r).1) =
        (metadata hψ hwidth hle l r).1 ∧
      putSignals (row hψ hwidth hle l r).2
        (observeCell (metadata hψ hwidth hle l r).2) =
        (metadata hψ hwidth hle l r).2 := by
  unfold row
  dsimp only
  exact K2BirthDispatcher.finalPhysical_frame hψ l r _ _

/-- Actual computed no-birth gives exactly the frozen collision/K2 observation. -/
theorem observe_row_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ)
    (hn : birthEvent hψ hwidth hle l r = false) :
    (observeCell (row hψ hwidth hle l r).1,
      observeCell (row hψ hwidth hle l r).2) =
      K2BirthDispatcher.shadowRow (observeCell l) (observeCell r) := by
  have hnorm :
      K2BirthDispatcher.newborn l (metadata hψ hwidth hle l r).1 = false ∧
      K2BirthDispatcher.newborn r (metadata hψ hwidth hle l r).2 = false := by
    simpa only [birthEvent, Bool.or_eq_false_iff] using hn
  unfold row
  dsimp only
  rw [K2BirthDispatcher.finalPhysical_of_no_birth hψ l r _ _
    hnorm.1 hnorm.2]
  exact (K2BirthDispatcher.observe_collisionRow hψ _ _).trans
    (congrArg (fun q : AgentState 1 × AgentState 1 =>
      K2BirthDispatcher.shadowRow q.1 q.2)
      (metadata_signal_of_no_birth hψ hwidth hle l r hn))

/-- The only expiry calls are exactly the two calls already inside the frozen
short-width DONE metadata computation, once per endpoint role. -/
theorem row_timers_once (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := BirthShortDoneCuts.doneMetadataBoundedWidth
      hψ hwidth hle l0.core r0.core
    (row hψ hwidth hle l r).1.stall =
        (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩).stall ∧
      (row hψ hwidth hle l r).2.stall =
        (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩).stall := by
  have hf := row_metadata_frame hψ hwidth hle l r
  have hL := congrArg ExpiringAgentState.stall hf.1
  have hR := congrArg ExpiringAgentState.stall hf.2
  change (row hψ hwidth hle l r).1.stall =
    (metadata hψ hwidth hle l r).1.stall at hL
  change (row hψ hwidth hle l r).2.stall =
    (metadata hψ hwidth hle l r).2.stall at hR
  have hm := metadata_field_frame hψ hwidth hle l r
  have mL := congrArg ExpiringAgentState.stall hm.1
  have mR := congrArg ExpiringAgentState.stall hm.2
  change (metadata hψ hwidth hle l r).1.stall =
    (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).1.stall at mL
  change (metadata hψ hwidth hle l r).2.stall =
    (BirthShortDoneCuts.doneMetadataWidth hψ hwidth hle l r).2.stall at mR
  unfold BirthShortDoneCuts.doneMetadataWidth at mL mR
  exact ⟨hL.trans mL, hR.trans mR⟩

/-- Same finite expiring carrier; no new physical field is introduced. -/
theorem row_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    (row hψ hwidth hle l r).1.core.core.erase.inProtocolDomain κ ∧
      (row hψ hwidth hle l r).2.core.core.erase.inProtocolDomain κ :=
  ⟨(row hψ hwidth hle l r).1.core.core.erase_inProtocolDomain,
    (row hψ hwidth hle l r).2.core.core.erase_inProtocolDomain⟩

/-! ## Actual scheduler composition and same-word observation -/

def protocol (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := Bool
  transition := row hψ hwidth hle
  output := fun q => q.core.core.leader

def step (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (e : Fin n) : Fin n → ExpiringAgentState ψ κ τ :=
  (protocol hψ hwidth hle κ τ).step ring C e

/-- Exactly the existing exhaustive carrier and bound. -/
def stateCertificate (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ τ : Nat) :
    ExhaustiveList (protocol hψ hwidth hle κ τ).Q :=
  K2BirthDispatcher.stateCertificate hψ κ τ

theorem finite_state_bound (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ τ : Nat) :
    Function.Injective (stateCertificate hψ hwidth hle κ τ).decode ∧
    Function.Surjective (stateCertificate hψ hwidth hle κ τ).decode ∧
    (stateCertificate hψ hwidth hle κ τ).values.length ≤
      ExpiringK2Projection.localBound ψ κ τ :=
  K2BirthDispatcher.finite_state_bound hψ κ τ

theorem observe_step_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hn : birthEvent hψ hwidth hle (C e) (C (ring.rightNeighbor e)) = false) :
    ExpiringK2Projection.observe (step hψ hwidth hle ring C e) =
      K2BirthDispatcher.shadowStep ring (ExpiringK2Projection.observe C) e := by
  have hq := observe_row_of_no_birth hψ hwidth hle
    (C e) (C (ring.rightNeighbor e)) hn
  funext i
  simp only [ExpiringK2Projection.observe, step, PopulationProtocol.step,
    protocol, K2BirthDispatcher.shadowStep, updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

/-- The sole scheduler-word no-birth premise, evaluated recursively on the
ACTUAL NEW successors. -/
def NoBirthAlong (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : List (Fin n) → Prop
  | [] => True
  | e :: es =>
      birthEvent hψ hwidth hle (C e) (C (ring.rightNeighbor e)) = false ∧
      NoBirthAlong hψ hwidth hle ring
        (step hψ hwidth hle ring C e) es

theorem NoBirthAlong.take (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ hwidth hle ring C es) (t : Nat) :
    NoBirthAlong hψ hwidth hle ring C (es.take t) := by
  induction t generalizing C es with
  | zero => trivial
  | succ t ih =>
    cases es with
    | nil => trivial
    | cons e es => exact ⟨hn.1, ih _ _ hn.2⟩

theorem observe_run_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ hwidth hle ring C es) :
    ExpiringK2Projection.observe
        (run (step hψ hwidth hle ring) C es) =
      run (K2BirthDispatcher.shadowStep ring)
        (ExpiringK2Projection.observe C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simpa only [run,
      observe_step_of_no_birth hψ hwidth hle ring C e hn.1] using
      ih (step hψ hwidth hle ring C e) hn.2

/-- Every prefix of the SAME scheduler word has the exact four-field
observation of the frozen shadow system. -/
theorem observe_all_prefixes_of_no_birth (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width <= ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ hwidth hle ring C es) (t : Nat) :
    ExpiringK2Projection.observe
        (run (step hψ hwidth hle ring) C (es.take t)) =
      run (K2BirthDispatcher.shadowStep ring)
        (ExpiringK2Projection.observe C) (es.take t) :=
  observe_run_of_no_birth hψ hwidth hle ring C _
    (NoBirthAlong.take hψ hwidth hle ring C es hn t)

/-- Direct same-word comparison to the frozen AdjacentLeaderElimination system. -/
theorem same_word_adjacent_all_prefixes (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width <= ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (D : Fin n → StateBoundUnifiedCell.UCell ψ κ) (es : List (Fin n))
    (h0 : ExpiringK2Projection.observe C = LabelFreeElimination.observe D)
    (hn : NoBirthAlong hψ hwidth hle ring C es) (t : Nat) :
    ExpiringK2Projection.observe
        (run (step hψ hwidth hle ring) C (es.take t)) =
      LabelFreeElimination.observe
        (run (AdjacentLeaderElimination.step hψ ring) D (es.take t)) := by
  rw [observe_all_prefixes_of_no_birth hψ hwidth hle ring C es hn t,
    K2BirthDispatcher.adjacent_observe_run hψ ring D (es.take t), h0]

/-- Unscheduled sites retain their entire raw records. -/
theorem step_other (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    step hψ hwidth hle ring C e i = C i := by
  simp only [step, PopulationProtocol.step, protocol, if_neg hi, if_neg hj]

/-- Self-edge aliasing keeps the population protocol's real left-output
priority; no responder copy or second physical call is inserted. -/
theorem step_alias (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (ha : ring.rightNeighbor e = e) :
    step hψ hwidth hle ring C e e =
      (row hψ hwidth hle (C e) (C e)).1 := by
  simp only [step, PopulationProtocol.step, protocol, ha, if_true]

#print axioms BirthShortDoneDispatcher.doneMetadataBoundedWidth_full
#print axioms BirthShortDoneDispatcher.doneMetadataWidth_full
#print axioms BirthShortDoneDispatcher.metadata_full
#print axioms BirthShortDoneDispatcher.birthEvent_full
#print axioms BirthShortDoneDispatcher.row_full
#print axioms BirthShortDoneDispatcher.metadata_field_frame
#print axioms BirthShortDoneDispatcher.metadata_observation_raw
#print axioms BirthShortDoneDispatcher.raw_existing_leaders
#print axioms BirthShortDoneDispatcher.raw_bullets
#print axioms BirthShortDoneDispatcher.metadata_signal_of_no_birth
#print axioms BirthShortDoneDispatcher.row_metadata_frame
#print axioms BirthShortDoneDispatcher.observe_row_of_no_birth
#print axioms BirthShortDoneDispatcher.row_timers_once
#print axioms BirthShortDoneDispatcher.row_domain
#print axioms BirthShortDoneDispatcher.finite_state_bound
#print axioms BirthShortDoneDispatcher.observe_step_of_no_birth
#print axioms BirthShortDoneDispatcher.NoBirthAlong.take
#print axioms BirthShortDoneDispatcher.observe_run_of_no_birth
#print axioms BirthShortDoneDispatcher.observe_all_prefixes_of_no_birth
#print axioms BirthShortDoneDispatcher.same_word_adjacent_all_prefixes
#print axioms BirthShortDoneDispatcher.step_other
#print axioms BirthShortDoneDispatcher.step_alias

end BirthShortDoneDispatcher

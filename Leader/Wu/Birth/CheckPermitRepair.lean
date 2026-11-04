import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Birth.WaitPassiveHost

/-! # R1: a CHECK outcome `equal` consumes the crossing permit

Separately named candidate repair of the width-two terminal consumer (`BirthShortDoneTerminalHost.row`).  At
psi >= 3 the consumer overwrites an aligned crossed CHECK train: CHECK writes `equal` on labels 0 and 1, then the
permit-authorized CMP_UPDATE fresh start rewrites both to `congest` (`B6CheckClobberConsumer`), so a single train
never completes CHECK and leaderless births need a lock wave of two adjacent trains.  R1 changes exactly one
thing in the ordinary DONE branch: between the CHECK stage (`doneThroughCheckEntryWidth`) and the post-CHECK
stages (`afterCheckMetadataWidth`), an initiator whose CHECK outcome is `equal` loses its crossing permit.  Every
other stage, the reification, both expiry calls, leader normalization and the final physical tail are the
consumer's.

* `ordinary_eq_of_not_equal`: when the CHECK outcome of the initiator is not `equal`, the repaired ordinary branch
  is the consumer's (so R1 agrees with the consumer on every such row).
* `crossed_row_keeps_equal`, `crossed_chain_births`: at psi = 3, kappa = 3, tau = 48 the aligned crossed train
  keeps `equal` and the next internal row creates the leader. -/

namespace BirthCheckPermitRepair

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
open BirthShortDoneTerminalHost BirthWaitPassive

set_option autoImplicit false

variable {ψ width κ τ : Nat}

/-- The only new assignment: an `equal` CHECK outcome consumes the crossing permit. -/
def permitFix (c : AuthorizedAgentState ψ) : AuthorizedAgentState ψ :=
  if c.core.state = .equal then ⟨c.core, false⟩ else c

theorem permitFix_of_ne (c : AuthorizedAgentState ψ) (h : c.core.state ≠ .equal) : permitFix c = c := by
  simp [permitFix, h]

theorem permitFix_core (c : AuthorizedAgentState ψ) : (permitFix c).core = c.core := by
  unfold permitFix; split <;> rfl

def ordinary (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let c := doneThroughCheckEntryWidth hψ hwidth hle κ l r
  let q := afterCheckMetadataWidth hψ hwidth hle (permitFix c.1) c.2
  markLeaderBirth (authBirth l r q) q

theorem ordinary_eq_of_not_equal (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (h : (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core.state ≠ .equal) :
    ordinary hψ hwidth hle κ l r = doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r := by
  unfold ordinary doneOrdinaryMetadataEntryWidth
  simp only [permitFix_of_ne _ h]

theorem ordinary_domain (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (ordinary hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (ordinary hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  have hc := doneThroughCheckEntryWidth_domain hψ hwidth hle l r hl hr
  unfold ordinary
  generalize doneThroughCheckEntryWidth hψ hwidth hle κ l r = c at *
  have hc1 : (permitFix c.1).core.inProtocolDomain κ := by rw [permitFix_core]; exact hc.1
  have hw := afterCheckMetadataWidth_domain (κ := κ) hψ hwidth hle (permitFix c.1) c.2 hc1 hc.2
  exact markLeaderBirth_inProtocolDomain _ _ hw

/-- Responder-delete / initiator-wait / ordinary priority, unchanged except for the ordinary branch. -/
def authorized (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hψ l0 r0
  else if deletionActive l0 then (l0, r0)
  else ordinary hψ hwidth hle κ l0 r0

theorem authorized_domain (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (authorized hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (authorized hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  unfold authorized
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hψ) l0 r0
      (eliminateSig_inProtocolDomain hψ l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · exact ordinary_domain hψ hwidth hle l0 r0 hl0 hr0

def bounded (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := authorized hψ hwidth hle κ l.erase r.erase
  let hq := authorized_domain hψ hwidth hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

def expiring (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := bounded hψ hwidth hle l0.core r0.core
  (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩, deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)

/-- The R1 row: the consumer's normalization and single final physical tail on the repaired metadata. -/
def row (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := expiring hψ hwidth hle l r
  K2BirthDispatcher.finalPhysical hψ l r (normalizeLeader hψ q.1) (normalizeLeader hψ q.2)

/-- The R1 consumer as a population protocol with the consumer's state type and output. -/
def protocol (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := Bool
  transition := row hψ hwidth hle
  output := fun q => q.core.core.leader

/-! ## Concrete certificate at the parameter witness psi = 3, kappa = 3, tau = 48 -/

def regsB (lab : Fin 3) (b : Bool) : Registers 3 :=
  { label := lab, h := false, carry := false, reset := false, count := 0, wait := true,
    bit := b, phase := false, writer := .none }

def withPath (lab : Fin 3) (b : Bool) : AgentState 3 :=
  { cell (regsB lab b) with path := .some lab.val (if b then 1 else 0) }

theorem dom_path (lab : Fin 3) (b : Bool) : (withPath lab b).inProtocolDomain 3 := by
  have h := lab.isLt
  cases b <;> simp [withPath, cell, regsB, AgentState.inProtocolDomain, h]

def tok (lab : Fin 3) (b crossed : Bool) : ExpiringAgentState 3 3 48 :=
  ⟨⟨BoundedAgentState.ofDomain (withPath lab b) (dom_path lab b), crossed⟩, Fin.last 48⟩

/-- The crossed aligned pair keeps `equal` under R1 (the consumer leaves it in `congest`). -/
theorem crossed_row_keeps_equal :
    let q := row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      (tok 0 true true) (tok 1 false false)
    q.1.core.core.state = .equal ∧ q.2.core.core.state = .equal := by
  decide +kernel

/-- The next internal row of the crossed aligned train creates the leader at label 2. -/
theorem crossed_chain_births :
    let q := row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      (tok 0 true true) (tok 1 false false)
    let q' := row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      q.2 (tok 2 true false)
    q'.2.core.core.leader = true := by
  decide +kernel

end BirthCheckPermitRepair

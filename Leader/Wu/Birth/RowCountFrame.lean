import Leader.Wu.Birth.ShortDoneTerminalHost

set_option autoImplicit false

namespace BirthB1RowCountFrame

open BirthShortDoneTerminalHost BirthSigMoveDisposalRepair ExpiringK2Projection K2BirthDispatcher K2BirthLeaderNormalize PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair PPLLPathStallComparisonRepair

variable {ψ κ τ : Nat}

/-- The physical count read through the erase projection (the `rawAt` path). -/
def countE (q : ExpiringAgentState ψ κ τ) : Nat := q.core.erase.core.count

theorem putSignals_count (q : ExpiringAgentState ψ κ τ) (v : AgentState 1) :
    countE (putSignals q v) = countE q := rfl

theorem putLabel_count (q : ExpiringAgentState ψ κ τ) (a : Fin ψ) :
    countE (putLabel q a) = countE q := rfl

theorem normalizeLeader_count (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    countE (normalizeLeader hψ q) = countE q := by
  unfold normalizeLeader
  split <;> rfl

theorem nonK2_count (q : ExpiringAgentState ψ κ τ) : countE (nonK2 q) = countE q := rfl

theorem finalPhysical_count (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    countE (finalPhysical hψ oldL oldR metaL metaR).1 = countE metaL ∧
      countE (finalPhysical hψ oldL oldR metaL metaR).2 = countE metaR := by
  have hf := finalPhysical_nonK2 hψ oldL oldR metaL metaR
  constructor
  · have h := congrArg countE hf.1
    rwa [nonK2_count, nonK2_count] at h
  · have h := congrArg countE hf.2
    rwa [nonK2_count, nonK2_count] at h

theorem clearComparisonCarrier_count (s : AuthorizedBoundedAgentState ψ κ) :
    (clearComparisonCarrier s).erase.core.count = s.erase.core.count := rfl

theorem pathExpireOne_count (τ : Nat) (old out : ExpiringAgentState ψ κ τ) :
    countE (pathExpireOne τ old out) = countE out := by
  unfold pathExpireOne
  split
  · rfl
  · split
    · exact clearComparisonCarrier_count out.core
    · rfl

theorem deletionPriorityExpireOne_count (τ : Nat) (old out : ExpiringAgentState ψ κ τ) :
    countE (deletionPriorityExpireOne τ old out) = countE out := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · exact pathExpireOne_count τ old out

theorem markComparisonForDeletion_count (u : AuthorizedAgentState ψ) :
    (markComparisonForDeletion u).core.count = u.core.count := by
  unfold markComparisonForDeletion
  split <;> rfl

theorem prepareDisposal_count (hψ : ψ > 0) (u : AuthorizedAgentState ψ) :
    (prepareDisposal hψ u).core.count = u.core.count := by
  unfold prepareDisposal
  split
  · exact markComparisonForDeletion_count u
  · rfl

theorem prepareExpiringDisposal_count (hψ : ψ > 0) (u : ExpiringAgentState ψ κ τ) :
    countE (prepareExpiringDisposal hψ u) = countE u := by
  show (prepareBoundedDisposal hψ u.core).erase.core.count = u.core.erase.core.count
  rw [erase_prepareBoundedDisposal]
  exact prepareDisposal_count hψ u.core.erase

/-- The physical row's counts are the inner authorized metadata's counts. -/
theorem row_count_eq (hψ : 0 < ψ) {width : Nat} (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let m := doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l0.core.erase r0.core.erase
    countE (row hψ hwidth hle l r).1 = m.1.core.count ∧
      countE (row hψ hwidth hle l r).2 = m.2.core.count := by
  intro l0 r0 m
  rw [row_real_host_witness hψ hwidth hle l r]
  have hq := doneMetadataBoundedEntryWidth_erase hψ hwidth hle l0.core r0.core
  have hq1 := congrArg Prod.fst hq
  have hq2 := congrArg Prod.snd hq
  simp only at hq1 hq2
  constructor
  · rw [(finalPhysical_count hψ l r _ _).1, normalizeLeader_count, deletionPriorityExpireOne_count]
    show (doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core).1.erase.core.count = m.1.core.count
    rw [hq1]
  · rw [(finalPhysical_count hψ l r _ _).2, normalizeLeader_count, deletionPriorityExpireOne_count]
    show (doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core).2.erase.core.count = m.2.core.count
    rw [hq2]

theorem prepare_count_eq (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    (prepareExpiringDisposal hψ u).core.erase.core.count = countE u :=
  prepareExpiringDisposal_count hψ u

theorem markComparisonForDeletion_leader (u : AuthorizedAgentState ψ) :
    (markComparisonForDeletion u).core.leader = u.core.leader := by
  unfold markComparisonForDeletion
  split <;> rfl

theorem markComparisonForDeletion_reset (u : AuthorizedAgentState ψ) :
    (markComparisonForDeletion u).core.reset_cmd = u.core.reset_cmd := by
  unfold markComparisonForDeletion
  split <;> rfl

theorem prepareDisposal_leader (hψ : ψ > 0) (u : AuthorizedAgentState ψ) :
    (prepareDisposal hψ u).core.leader = u.core.leader := by
  unfold prepareDisposal
  split
  · exact markComparisonForDeletion_leader u
  · rfl

theorem prepareDisposal_reset (hψ : ψ > 0) (u : AuthorizedAgentState ψ) :
    (prepareDisposal hψ u).core.reset_cmd = u.core.reset_cmd := by
  unfold prepareDisposal
  split
  · exact markComparisonForDeletion_reset u
  · rfl

theorem prepare_leader_eq (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    (prepareExpiringDisposal hψ u).core.erase.core.leader = u.core.erase.core.leader := by
  show (prepareBoundedDisposal hψ u.core).erase.core.leader = u.core.erase.core.leader
  rw [erase_prepareBoundedDisposal]
  exact prepareDisposal_leader hψ u.core.erase

theorem prepare_reset_eq (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    (prepareExpiringDisposal hψ u).core.erase.core.reset_cmd = u.core.erase.core.reset_cmd := by
  show (prepareBoundedDisposal hψ u.core).erase.core.reset_cmd = u.core.erase.core.reset_cmd
  rw [erase_prepareBoundedDisposal]
  exact prepareDisposal_reset hψ u.core.erase

end BirthB1RowCountFrame

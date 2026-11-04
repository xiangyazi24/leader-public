import Leader.Wu.Elimination.BirthDispatcherMetadata
import Leader.Wu.Elimination.BirthDispatcherCollision

/-! A concrete finite mixed candidate on the existing expiring carrier.
All metadata priority branches reach the same final collision/K2 stage.
The observation theorem is conditional on the computed absence of birth in
this row; no source of a birth-free interval is asserted here. -/

namespace K2BirthDispatcher

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  ExpiringK2Projection K2OutputSafety

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ τ n : Nat}

/-- Reify the actual metadata outputs, including their actual permit bits. -/
def metadataBounded (hψ : 0 < ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := metadataAuthorized hψ κ l.erase r.erase
  let hq := metadataAuthorized_domain hψ l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem metadataBounded_erase (hψ : 0 < ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    ((metadataBounded hψ l r).1.erase, (metadataBounded hψ l r).2.erase) =
      metadataAuthorized hψ κ l.erase r.erase := by
  unfold metadataBounded
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

/-- Entry disposal, actual metadata priorities and exactly one priority-expiry
call per endpoint role, also on the responder-delete and initiator-wait branches. -/
def metadata (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := metadataBounded hψ l0.core r0.core
  (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩,
    deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)

/-- Executable local event test on the complete computed metadata output. -/
def birthEvent (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) : Bool :=
  let q := metadata hψ l r
  newborn l q.1 || newborn r q.2

/-- The complete concrete row. There is no priority return before the final
physical stage, and no call to the old Algorithm 15 in the metadata stage. -/
def row (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := metadata hψ l r
  finalPhysical hψ l r q.1 q.2

attribute [local irreducible] metadataAuthorized metadataBounded metadata row

/-- Exact erasure through real reification and expiry, including stale
comparison erasure by expiry; only the four physical fields are observed. -/
theorem metadata_observation (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (metadata hψ l r).1, observeCell (metadata hψ l r).2) =
      authSignalPair (metadataAuthorized hψ κ
        (prepareExpiringDisposal hψ l).core.erase (prepareExpiringDisposal hψ r).core.erase) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := metadataBounded hψ l0.core r0.core
  have he := congrArg authSignalPair (metadataBounded_erase hψ l0.core r0.core)
  have hx :
      (observeCell (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩),
        observeCell (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)) =
      (observeCell (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ),
        observeCell (⟨q.2, r0.stall⟩ : ExpiringAgentState ψ κ τ)) :=
    Prod.ext (priority_expiry_observation l0 (⟨q.1, l0.stall⟩))
      (priority_expiry_observation r0 (⟨q.2, r0.stall⟩))
  unfold metadata
  exact hx.trans he

/-- The full metadata event is exactly its raw computed event. Disposal,
bounded conversion and timer expiration cannot manufacture or hide a birth. -/
theorem birthEvent_eq_raw (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    birthEvent hψ l r = authBirth
      (prepareExpiringDisposal hψ l).core.erase (prepareExpiringDisposal hψ r).core.erase
      (metadataAuthorized hψ κ
        (prepareExpiringDisposal hψ l).core.erase (prepareExpiringDisposal hψ r).core.erase) := by
  have hl := congrArg AgentState.leader (prepareExpiring_signal hψ l)
  have hr := congrArg AgentState.leader (prepareExpiring_signal hψ r)
  have h := congrArg (fun q : AgentState 1 × AgentState 1 =>
    (!l.core.core.leader && q.1.leader) || (!r.core.core.leader && q.2.leader))
    (metadata_observation hψ l r)
  change (prepareExpiringDisposal hψ l).core.core.leader = l.core.core.leader at hl
  change (prepareExpiringDisposal hψ r).core.core.leader = r.core.core.leader at hr
  unfold birthEvent newborn authBirth endpointLeaderBorn
  change _ = ((! (prepareExpiringDisposal hψ l).core.core.leader && _) ||
    (! (prepareExpiringDisposal hψ r).core.core.leader && _))
  rw [hl, hr]
  exact h

/-- Headline metadata frame: its only hypothesis is the actual no-birth
Boolean, with all four endpoint fields derived from the concrete source. -/
theorem metadata_signal_of_no_birth (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hn : birthEvent hψ l r = false) :
    (observeCell (metadata hψ l r).1, observeCell (metadata hψ l r).2) =
      (observeCell l, observeCell r) := by
  have hn0 := (birthEvent_eq_raw hψ l r).symm.trans hn
  exact (metadata_observation hψ l r).trans
    ((metadataAuthorized_signal_of_no_birth hψ κ _ _ hn0).trans
      (Prod.ext (prepareExpiring_signal hψ l) (prepareExpiring_signal hψ r)))

theorem metadata_existing_leaders (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (l.core.core.leader = true → (metadata hψ l r).1.core.core.leader = true) ∧
    (r.core.core.leader = true → (metadata hψ l r).2.core.core.leader = true) := by
  have hs := metadataAuthorized_leaders hψ κ
    (prepareExpiringDisposal hψ l).core.erase (prepareExpiringDisposal hψ r).core.erase
  have he := metadata_observation hψ l r
  have hl := congrArg AgentState.leader (prepareExpiring_signal hψ l)
  have hr := congrArg AgentState.leader (prepareExpiring_signal hψ r)
  exact ⟨fun h => (congrArg (fun q => q.1.leader) he).trans (hs.1 (hl.trans h)),
    fun h => (congrArg (fun q => q.2.leader) he).trans (hs.2 (hr.trans h))⟩

/-- One actual adjacent-collision/K2 row on the same endpoint observations.
No initial readiness, ordering, controller or timer hypothesis is present. -/
theorem observe_row_of_no_birth (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hn : birthEvent hψ l r = false) :
    (observeCell (row hψ l r).1, observeCell (row hψ l r).2) =
      shadowRow (observeCell l) (observeCell r) := by
  have hn' : newborn l (metadata hψ l r).1 = false ∧
      newborn r (metadata hψ l r).2 = false := by
    simpa only [birthEvent, Bool.or_eq_false_iff] using hn
  unfold row
  rw [finalPhysical_of_no_birth hψ l r _ _ hn'.1 hn'.2]
  exact (observe_collisionRow hψ _ _).trans
    (congrArg (fun q : AgentState 1 × AgentState 1 => shadowRow q.1 q.2)
      (metadata_signal_of_no_birth hψ l r hn))

/-- The physical tail retains all computed metadata fields, not the input
metadata. This covers real comparison cleanup, permits and elapsed timers. -/
theorem row_metadata_frame (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    putSignals (row hψ l r).1 (observeCell (metadata hψ l r).1) = (metadata hψ l r).1 ∧
      putSignals (row hψ l r).2 (observeCell (metadata hψ l r).2) = (metadata hψ l r).2 := by
  unfold row
  exact finalPhysical_frame hψ l r _ _

theorem row_metadata_nonK2 (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    nonK2 (row hψ l r).1 = nonK2 (metadata hψ l r).1 ∧
      nonK2 (row hψ l r).2 = nonK2 (metadata hψ l r).2 := by
  unfold row
  exact finalPhysical_nonK2 hψ l r _ _

/-- The only timer calls in the complete raw row occur here, once per role.
If the two physical endpoints alias, the global update keeps the left role. -/
theorem row_timers_once (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := metadataBounded hψ l0.core r0.core
    (row hψ l r).1.stall = (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩).stall ∧
      (row hψ l r).2.stall = (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩).stall := by
  have h := row_metadata_frame hψ l r
  unfold metadata at h
  have hl := congrArg ExpiringAgentState.stall h.1
  have hr := congrArg ExpiringAgentState.stall h.2
  exact ⟨hl, hr⟩

/-- Unconditional range closure on the actual bounded expiring carrier. -/
theorem row_domain (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (row hψ l r).1.core.core.erase.inProtocolDomain κ ∧
      (row hψ l r).2.core.core.erase.inProtocolDomain κ :=
  ⟨(row hψ l r).1.core.core.erase_inProtocolDomain,
    (row hψ l r).2.core.core.erase_inProtocolDomain⟩

def protocol (hψ : 0 < ψ) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := Bool
  transition := row hψ
  output := fun q => q.core.core.leader

def step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n) : Fin n → ExpiringAgentState ψ κ τ :=
  (protocol hψ κ τ).step ring C e

def stateCertificate (hψ : 0 < ψ) (κ τ : Nat) : ExhaustiveList (protocol hψ κ τ).Q :=
  expiringAgentState ψ κ τ

theorem finite_state_bound (hψ : 0 < ψ) (κ τ : Nat) :
    Function.Injective (stateCertificate hψ κ τ).decode ∧
    Function.Surjective (stateCertificate hψ κ τ).decode ∧
    (stateCertificate hψ κ τ).values.length ≤ ExpiringK2Projection.localBound ψ κ τ :=
  ⟨(finite_bijection ψ κ τ).1, (finite_bijection ψ κ τ).2, state_bound ψ κ τ⟩

#print axioms metadataBounded_erase
#print axioms metadata_signal_of_no_birth
#print axioms observe_row_of_no_birth
#print axioms row_metadata_nonK2
#print axioms row_timers_once
#print axioms finite_state_bound

end K2BirthDispatcher

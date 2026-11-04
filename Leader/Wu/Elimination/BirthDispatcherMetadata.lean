import Leader.Wu.Elimination.BirthDispatcherMetadataSuffix
import Leader.Wu.WriteSeq.StationaryWritePersistentFinite

/-! The concrete unbounded presentation of the metadata row. The separately
owned stationary persistent writer is used literally. No Algorithm 15 occurs
in this module's executable row. Bounded reification and expiry follow in the
complete dispatcher module. -/

namespace K2BirthDispatcher

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthLeaderFrames
  BirthStationaryWrite BirthSingleUseReleaseRepair BirthTossCheckPreservationRepair
  K2OutputSafety

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ : Nat}

attribute [local irreducible] stationaryPersistentRaw singleUseBeforeCheck preserveTossCheck

/-- Actual DISAPPEAR, action-one COMPARE, SUPPRESS and the stationary
persistent comparison/transport writer; the old Algorithm 15 is omitted. -/
def afterCheckMetadata (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := beforeWrite hψ l r
  stationaryPersistentAuthorizedRow hψ q.1 q.2

theorem stationaryWriter_signal (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (stationaryPersistentAuthorizedRow hψ l r) =
      authSignalPair (l, r) :=
  signalPair_of_fields
    (Prod.ext (stationaryPersistentRaw_leaders hψ l.core r.core).1
      (stationaryPersistentRaw_leaders hψ l.core r.core).2)
    (stationaryPersistentRaw_bullets hψ l.core r.core)

/-- The actual writer has no follower/leader migration on any input. -/
theorem stationaryWriter_no_migration (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (stationaryPersistentAuthorizedRow hψ l r).1.core.leader = l.core.leader ∧
      (stationaryPersistentAuthorizedRow hψ l r).2.core.leader = r.core.leader :=
  stationaryPersistentRaw_leaders hψ l.core r.core

theorem afterCheckMetadata_signal (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (afterCheckMetadata hψ l r) = authSignalPair (l, r) := by
  let q := beforeWrite hψ l r
  exact (stationaryWriter_signal hψ q.1 q.2).trans (beforeWrite_signal hψ l r)

/-- The only birth event used by metadata cleanup is computed from its
actual endpoint input and output leader bits. It is not a state register. -/
def authBirth (l r : AuthorizedAgentState ψ)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) : Bool :=
  endpointLeaderBorn l q.1 || endpointLeaderBorn r q.2

def ordinaryMetadata (hψ : 0 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let c := throughCheck hψ κ l r
  let q := afterCheckMetadata hψ c.1 c.2
  markLeaderBirth (authBirth l r q) q

/-- The old wrapper's actual responder-deletion / initiator-wait / ordinary
priority order. These branches concern metadata only; the complete row adds
the physical tail after every one of them. -/
def metadataAuthorized (hψ : 0 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hψ l0 r0
  else if deletionActive l0 then (l0, r0)
  else ordinaryMetadata hψ κ l0 r0

attribute [local irreducible] throughCheck beforeWrite afterCheckMetadata
  ordinaryMetadata metadataAuthorized

theorem ordinaryMetadata_signal (hψ : 0 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (ordinaryMetadata hψ κ l r) =
      authSignalPair (throughCheck hψ κ l r) := by
  let c := throughCheck hψ κ l r
  let q := afterCheckMetadata hψ c.1 c.2
  unfold ordinaryMetadata
  exact (markBirth_signal (authBirth l r q) q).trans (afterCheckMetadata_signal hψ c.1 c.2)

theorem ordinaryMetadata_bullets (hψ : 0 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (ordinaryMetadata hψ κ l r) =
      authorizedBulletFieldPair (l, r) :=
  (authBullets_of_signal (ordinaryMetadata_signal hψ κ l r)).trans
    (throughCheck_bullets hψ κ l r)

theorem ordinaryMetadata_leaders (hψ : 0 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true → (ordinaryMetadata hψ κ l r).1.core.leader = true) ∧
    (r.core.leader = true → (ordinaryMetadata hψ κ l r).2.core.leader = true) := by
  have h := ordinaryMetadata_signal hψ κ l r
  have hc := throughCheck_leaders hψ κ l r
  exact ⟨fun hl => (congrArg (fun q => q.1.leader) h).trans (hc.1 hl),
    fun hr => (congrArg (fun q => q.2.leader) h).trans (hc.2 hr)⟩

theorem metadataAuthorized_right_priority (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (hr : deletionActive (normalizeDeletion r) = true) :
    metadataAuthorized hψ κ l r =
      authorizedEliminateSig hψ (normalizeDeletion l) (normalizeDeletion r) := by
  unfold metadataAuthorized
  simp only [hr, if_true]

theorem metadataAuthorized_left_priority (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = true) :
    metadataAuthorized hψ κ l r = (normalizeDeletion l, normalizeDeletion r) := by
  unfold metadataAuthorized
  simp only [hr, Bool.false_eq_true, if_false, hl, if_true]

theorem metadataAuthorized_ordinary (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = false) :
    metadataAuthorized hψ κ l r =
      ordinaryMetadata hψ κ (normalizeDeletion l) (normalizeDeletion r) := by
  unfold metadataAuthorized
  simp only [hr, Bool.false_eq_true, if_false, hl]

theorem metadataAuthorized_branch_coverage (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (deletionActive (normalizeDeletion r) = true ∧
      metadataAuthorized hψ κ l r =
        authorizedEliminateSig hψ (normalizeDeletion l) (normalizeDeletion r)) ∨
    (deletionActive (normalizeDeletion r) = false ∧
      deletionActive (normalizeDeletion l) = true ∧
      metadataAuthorized hψ κ l r = (normalizeDeletion l, normalizeDeletion r)) ∨
    (deletionActive (normalizeDeletion r) = false ∧
      deletionActive (normalizeDeletion l) = false ∧
      metadataAuthorized hψ κ l r =
        ordinaryMetadata hψ κ (normalizeDeletion l) (normalizeDeletion r)) := by
  cases hr : deletionActive (normalizeDeletion r) with
  | true => exact Or.inl ⟨rfl, metadataAuthorized_right_priority hψ κ l r hr⟩
  | false =>
    cases hl : deletionActive (normalizeDeletion l) with
    | true => exact Or.inr (Or.inl ⟨rfl, rfl, metadataAuthorized_left_priority hψ κ l r hr hl⟩)
    | false => exact Or.inr (Or.inr ⟨rfl, rfl, metadataAuthorized_ordinary hψ κ l r hr hl⟩)

theorem normalize_pair_signal (l r : AuthorizedAgentState ψ) :
    authSignalPair (normalizeDeletion l, normalizeDeletion r) = authSignalPair (l, r) :=
  Prod.ext (normalize_signal l) (normalize_signal r)

/-- Metadata never changes the three bullet fields, on every priority branch. -/
theorem metadataAuthorized_bullets (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (metadataAuthorized hψ κ l r) =
      authorizedBulletFieldPair (l, r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have h0 := authBullets_of_signal (normalize_pair_signal l r)
  unfold metadataAuthorized
  dsimp only
  split
  · exact (authBullets_of_signal (eliminate_signal hψ l0 r0)).trans h0
  · split
    · exact h0
    · exact (ordinaryMetadata_bullets hψ κ l0 r0).trans h0

/-- Every pre-existing leader survives metadata. Physical deletion belongs
exclusively to the final collision/K2 stage. -/
theorem metadataAuthorized_leaders (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true → (metadataAuthorized hψ κ l r).1.core.leader = true) ∧
    (r.core.leader = true → (metadataAuthorized hψ κ l r).2.core.leader = true) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 : l0.core.leader = l.core.leader :=
    congrArg (fun u : AgentState 1 => u.leader) (normalize_signal l)
  have hr0 : r0.core.leader = r.core.leader :=
    congrArg (fun u : AgentState 1 => u.leader) (normalize_signal r)
  unfold metadataAuthorized
  dsimp only
  split
  · have he := eliminate_signal hψ l0 r0
    exact ⟨fun hl => (congrArg (fun q => q.1.leader) he).trans (hl0.trans hl),
      fun hr => (congrArg (fun q => q.2.leader) he).trans (hr0.trans hr)⟩
  · split
    · exact ⟨fun hl => hl0.trans hl, fun hr => hr0.trans hr⟩
    · have he := ordinaryMetadata_leaders hψ κ l0 r0
      exact ⟨fun hl => he.1 (hl0.trans hl), fun hr => he.2 (hr0.trans hr)⟩

/-- A Boolean lemma on the actual input/output bits: no birth, together
with source-derived preservation of old leaders, gives bit equality. -/
theorem leader_eq_of_no_birth (a b : Bool) (hs : a = true → b = true)
    (hn : (!a && b) = false) : b = a := by
  cases a <;> cases b <;> simp_all

/-- No post-state frame is assumed: the sole additional hypothesis is the
computed metadata birth test, and the frames are derived from the real stages. -/
theorem metadataAuthorized_signal_of_no_birth (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hn : authBirth l r (metadataAuthorized hψ κ l r) = false) :
    authSignalPair (metadataAuthorized hψ κ l r) = authSignalPair (l, r) := by
  have hs := metadataAuthorized_leaders hψ κ l r
  have hn' : (!l.core.leader && (metadataAuthorized hψ κ l r).1.core.leader) = false ∧
      (!r.core.leader && (metadataAuthorized hψ κ l r).2.core.leader) = false := by
    simpa only [authBirth, endpointLeaderBorn, Bool.or_eq_false_iff] using hn
  exact signalPair_of_fields
    (Prod.ext (leader_eq_of_no_birth _ _ hs.1 hn'.1) (leader_eq_of_no_birth _ _ hs.2 hn'.2))
    (metadataAuthorized_bullets hψ κ l r)

theorem afterCheckMetadata_domain (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (afterCheckMetadata hψ l r).1.core.inProtocolDomain κ ∧
      (afterCheckMetadata hψ l r).2.core.inProtocolDomain κ := by
  have h := beforeWrite_domain hψ l r hl hr
  unfold afterCheckMetadata
  exact stationaryPersistentAuthorizedRow_domain hψ _ _ h.1 h.2

theorem ordinaryMetadata_domain (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (ordinaryMetadata hψ κ l r).1.core.inProtocolDomain κ ∧
      (ordinaryMetadata hψ κ l r).2.core.inProtocolDomain κ := by
  have hc := throughCheck_domain hψ l r hl hr
  have hw := afterCheckMetadata_domain hψ _ _ hc.1 hc.2
  unfold ordinaryMetadata
  exact markLeaderBirth_inProtocolDomain _ _ hw

theorem metadataAuthorized_domain (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (metadataAuthorized hψ κ l r).1.core.inProtocolDomain κ ∧
      (metadataAuthorized hψ κ l r).2.core.inProtocolDomain κ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  unfold metadataAuthorized
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hψ) l0 r0
      (eliminateSig_inProtocolDomain hψ l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · exact ordinaryMetadata_domain hψ l0 r0 hl0 hr0

private theorem two_endpoint_birth_chain (a b c d e f : Bool)
    (hac : a = true → c = true) (hbd : b = true → d = true)
    (hce : c = true → e = true) (hdf : d = true → f = true) :
    ((!a && c) || (!b && d) || (!c && e) || (!d && f)) =
      ((!a && e) || (!b && f)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> simp_all

/-- Input/output event detection agrees exactly with the old source's
before-or-at-CHECK detector on this new stationary metadata suffix. -/
theorem ordinary_cleanup_event_exact (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    let b := singleUseBeforeCheck hψ κ l r
    let c := preserveTossCheck hψ b.1 b.2
    authBirth l r (afterCheckMetadata hψ c.1 c.2) =
      leaderBirthBeforeOrAtCheck l r b c := by
  let b := singleUseBeforeCheck hψ κ l r
  let c := preserveTossCheck hψ b.1 b.2
  have hb := beforeCheck_leaders hψ κ l r
  have hc := preserveCheck_leaders hψ b.1 b.2
  have hw := afterCheckMetadata_signal hψ c.1 c.2
  have he := congrArg (fun q : AgentState 1 × AgentState 1 =>
    (!l.core.leader && q.1.leader) || (!r.core.leader && q.2.leader)) hw
  exact he.trans (two_endpoint_birth_chain _ _ _ _ _ _ hb.1 hb.2 hc.1 hc.2).symm

#print axioms stationaryWriter_signal
#print axioms stationaryWriter_no_migration
#print axioms ordinary_cleanup_event_exact
#print axioms metadataAuthorized_branch_coverage
#print axioms metadataAuthorized_bullets
#print axioms metadataAuthorized_leaders
#print axioms metadataAuthorized_signal_of_no_birth
#print axioms metadataAuthorized_domain

end K2BirthDispatcher

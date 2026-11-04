import Leader.Wu.Splice.CheckCleanupReleasedSafe

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9CheckCapstoneCanonical

open PPLL PPLLRepair PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
open PPLLTerminalEqualSupportRepair PPLLWriteIncrementGate
open PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
open PPLLWallSweepRestartableProtected PPLLWallSweepSchedule
open PPLLWallSweepEchoDrain
open B9CheckCleanupReleasedSafe
open PPLLWallSweepRepair PPLLWriteSeqPersistenceRegression PPLLWriteSeqRelocation

variable {n psi kappa tau : Nat}

private theorem markComparisonForDeletion_canonical
    (u : AuthorizedAgentState psi) (hu : AuthorizationCanonical u) :
    AuthorizationCanonical (markComparisonForDeletion u) := by
  unfold markComparisonForDeletion
  split
  · exact hu
  · intro h
    cases h

private theorem markLeaderBirth_canonical
    (born : Bool) (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hq : AuthorizationCanonical q.1 ∧ AuthorizationCanonical q.2) :
    AuthorizationCanonical (markLeaderBirth born q).1 ∧
      AuthorizationCanonical (markLeaderBirth born q).2 := by
  unfold markLeaderBirth
  split
  · exact ⟨markComparisonForDeletion_canonical q.1 hq.1,
      markComparisonForDeletion_canonical q.2 hq.2⟩
  · exact hq

private theorem wallSweepAuthorized_canonical_of_open
    (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let q := wallSweepAuthorizedTransition hpsi kappa l r
    AuthorizationCanonical q.1 ∧ AuthorizationCanonical q.2 := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hnormal :
      wallSweepAuthorizedTransition hpsi kappa l r =
        markLeaderBirth born
          (wallSweepAuthorizedAfterCheckSuffix
            hpsi afterCheck.1 afterCheck.2) := by
    simpa [l0, r0, beforeRaw, beforeCheck, afterCheck, born] using
      (wallSweepAuthorizedTransition_eq_normal_of_priority_open
        hpsi kappa l r hopen)
  have htail :
      AuthorizationCanonical
          (wallSweepAuthorizedAfterCheckSuffix
            hpsi afterCheck.1 afterCheck.2).1 ∧
        AuthorizationCanonical
          (wallSweepAuthorizedAfterCheckSuffix
            hpsi afterCheck.1 afterCheck.2).2 := by
    unfold wallSweepAuthorizedAfterCheckSuffix
    dsimp only
    exact authorizedReconcile_canonical
      (writeSeqIncrementGate hpsi) _ _
  rw [hnormal]
  exact markLeaderBirth_canonical born _ htail

private theorem deletionPriorityExpireOne_canonical
    (old out : ExpiringAgentState psi kappa tau)
    (hout : AuthorizationCanonical out.core.erase) :
    AuthorizationCanonical
      (deletionPriorityExpireOne tau old out).core.erase := by
  unfold deletionPriorityExpireOne
  split
  · exact hout
  · unfold pathExpireOne
    split
    · exact hout
    · split
      · simp [AuthorizationCanonical, clearComparisonCarrier,
          AuthorizedBoundedAgentState.erase]
      · exact hout

private theorem wallSweepPathStall_canonical_of_open
    (hpsi : 0 < psi) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    AuthorizationCanonical q.1.core.erase ∧
      AuthorizationCanonical q.2.core.erase := by
  let b := wallSweepBoundedTransition hpsi kappa l.core r.core
  have herase :
      (b.1.erase, b.2.erase) =
        wallSweepAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase := by
    simpa [b] using
      (erase_wallSweepBoundedTransition hpsi kappa l.core r.core)
  have ha := wallSweepAuthorized_canonical_of_open hpsi kappa
    l.core.erase r.core.erase (by
      simpa [WallPriorityOpen] using hopen)
  have hL : b.1.erase =
      (wallSweepAuthorizedTransition hpsi kappa l.core.erase r.core.erase).1 :=
    congrArg Prod.fst herase
  have hR : b.2.erase =
      (wallSweepAuthorizedTransition hpsi kappa l.core.erase r.core.erase).2 :=
    congrArg Prod.snd herase
  have hbL : AuthorizationCanonical b.1.erase := by
    rw [hL]
    exact ha.1
  have hbR : AuthorizationCanonical b.2.erase := by
    rw [hR]
    exact ha.2
  let lOut : ExpiringAgentState psi kappa tau := ⟨b.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨b.2, r.stall⟩
  change AuthorizationCanonical
      (deletionPriorityExpireOne tau l lOut).core.erase ∧
    AuthorizationCanonical
      (deletionPriorityExpireOne tau r rOut).core.erase
  exact ⟨deletionPriorityExpireOne_canonical l lOut hbL,
    deletionPriorityExpireOne_canonical r rOut hbR⟩

private theorem protectedWallStep_endpoints_canonical
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 1 < n)
    (C D : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n) (segment : DetSchedule n)
    (hstep : ProtectedWallStep hpsi kappa tau ring C e segment D) :
    AuthorizationCanonical (D e).core.erase ∧
      AuthorizationCanonical (D (ring.rightNeighbor e)).core.erase := by
  rcases hstep with
    ⟨drain, C0, _, _, _, _, hnoActive, _, _, hD⟩
  subst D
  have hopen := WallPriorityOpen.of_noActiveDeletion
    C0 hnoActive ring e
  have hc := wallSweepPathStall_canonical_of_open hpsi
    (C0 e) (C0 (ring.rightNeighbor e)) hopen
  have hne := rightNeighbor_ne_self_of_one_lt ring hn e
  constructor
  · simpa [localStep] using hc.1
  · simpa [localStep, hne] using hc.2

private theorem protectedWallStep_off
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : Fin n → ExpiringAgentState psi kappa tau)
    (e i : Fin n) (segment : DetSchedule n)
    (hstep : ProtectedWallStep hpsi kappa tau ring C e segment D)
    (hnoActive : NoActiveDeletion C)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    D i = C i := by
  rcases hstep with
    ⟨drain, C0, _, hC0, _, hempty, _, _, _, hD⟩
  have hd : drain = [] := hempty hnoActive
  subst drain
  simp [runLocalSchedule] at hC0
  subst C0
  subst D
  simp [localStep, hi, hj]

/-- `ProtectedResetSweepState` plus the missing authorization invariant. -/
structure CanonicalProtectedResetSweepState (hpsi : 0 < psi)
    (ring : DirectedRing n) (leader start : Fin n)
    (initial current : Fin n → ExpiringAgentState psi kappa tau)
    (steps : Nat) : Prop where
  base : ProtectedResetSweepState hpsi ring leader start initial current steps
  token_canonical : AuthorizationCanonical
    (current (groupOffset ring start steps)).core.erase
  visited_canonical : ∀ k, k < steps → AuthorizationCanonical
    (current (groupOffset ring start k)).core.erase

theorem canonicalProtectedResetSweepState_zero
    (hpsi : 0 < psi) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hreset : (C (ring.rightNeighbor leader)).core.erase.core.reset_cmd = true)
    (hneutral : ComparisonNeutral
      (C (ring.rightNeighbor leader)).core.erase.core)
    (hanchor : ProtectedLeaderAt hpsi C leader)
    (hcanonical : AuthorizationCanonical
      (C (ring.rightNeighbor leader)).core.erase) :
    CanonicalProtectedResetSweepState hpsi ring leader
      (ring.rightNeighbor leader) C C 0 := by
  refine ⟨protectedResetSweepState_zero hpsi ring hn leader C
    hnoActive hreset hneutral hanchor, ?_, ?_⟩
  · simpa [groupOffset, Nat.mod_eq_of_lt
      (ring.rightNeighbor leader).isLt] using hcanonical
  · intro k hk
    omega

theorem CanonicalProtectedResetSweepState.step
    {steps : Nat} (hpsi : 0 < psi)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (initial current D : Fin n → ExpiringAgentState psi kappa tau)
    (segment : DetSchedule n)
    (hstate : CanonicalProtectedResetSweepState hpsi ring leader
      (ring.rightNeighbor leader) initial current steps)
    (hnext : steps + 1 < n)
    (hecho : ∀ i, (initial i).core.erase.core.echo = false)
    (hstep : ProtectedWallStep hpsi kappa tau ring current
      (groupOffset ring (ring.rightNeighbor leader) steps) segment D) :
    CanonicalProtectedResetSweepState hpsi ring leader
      (ring.rightNeighbor leader) initial D (steps + 1) := by
  have hbase := ProtectedResetSweepState.step hpsi ring hn leader
    initial current D segment hstate.base hnext hecho hstep
  let start := ring.rightNeighbor leader
  let e := groupOffset ring start steps
  have hpair := protectedWallStep_endpoints_canonical
    hpsi ring hn current D e segment hstep
  have hneighbor : ring.rightNeighbor e =
      groupOffset ring start (steps + 1) := by
    simpa [e] using rightNeighbor_groupOffset ring start steps
  refine ⟨hbase, ?_, ?_⟩
  · rw [← hneighbor]
    exact hpair.2
  · intro k hk
    by_cases hks : k = steps
    · subst k
      simpa [e] using hpair.1
    · have hkold : k < steps := by omega
      have hke : groupOffset ring start k ≠ e := by
        change groupOffset ring start k ≠ groupOffset ring start steps
        apply groupOffset_ne_of_lt ring start <;> omega
      have hkj :
          groupOffset ring start k ≠ ring.rightNeighbor e := by
        rw [hneighbor]
        apply groupOffset_ne_of_lt ring start <;> omega
      rw [protectedWallStep_off hpsi ring current D e
        (groupOffset ring start k) segment hstep
        hstate.base.noActive hke hkj]
      exact hstate.visited_canonical k hkold

/-- Exact next endpoint theorem: the existing capstone facts, now retaining
structural authorization canonicality at every physical site. -/
def CleanupCapstoneCanonicalStatement : Prop :=
  ∀ (n psi kappa tau : Nat) (hpsi : 0 < psi)
      (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
      (C : Fin n → ExpiringAgentState psi kappa tau),
    ProtectedLeaderAt hpsi C leader →
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      RestartableWallExecution hpsi kappa tau ring C
        (leaderDrainReseedResetSweep ring leader) actual D ∧
      actual.length ≤
        (2 * n - 1) * (n + 1) + comparisonPathCount C ∧
      (D leader).core.erase.core.leader = true ∧
      (∀ i, ComparisonNeutral (D i).core.erase.core) ∧
      CleanupEndpointAuthorizationCanonical D

end B9CheckCapstoneCanonical

#print axioms B9CheckCapstoneCanonical.canonicalProtectedResetSweepState_zero
#print axioms B9CheckCapstoneCanonical.CanonicalProtectedResetSweepState.step

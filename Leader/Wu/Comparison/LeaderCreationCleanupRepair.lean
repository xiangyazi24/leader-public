import Leader.Wu.Comparison.PathStallRepair
import Leader.Wu.Comparison.ExpiringPersistenceDiagnosis

/-!
# Physical cleanup of comparison material after leader creation

T19 isolates a source-zero lifecycle omitted by the printed stable-sequence
argument.  A comparison carrier can create a leader in its source group, remain
present, move to an equal-ID follower group, and create another leader.  The
positive-source ruler theorem cannot apply because the source is group zero.

This file gives a separately named research repair.  It reuses the physical
`eliminate_signal` state as a priority deletion wave.  A transition-local event
observes follower-to-leader creation in the prefix through SIGMOVE or at CHECK,
then marks all present final endpoint paths after the unchanged suffix runs.
Because observation occurs before WRITE_SEQ, ordinary migration of an input
leader is excluded while a newborn moved in the same call remains detected.
While a marked component is
the initiator it waits; when it is the responder, Algorithm 9 alone propagates
the deletion left and clears that component.  Returning immediately from these
priority branches prevents SIGMOVE, CHECK, or COMPARE from reviving the marker.
No proof ghost guards execution and no new local-state field is introduced.
-/

namespace PPLLLeaderCreationCleanupRepair

open PPLL PPLLResearchFormulation PPLLRepair PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLExpiringPersistenceDiagnosis

/-- Whether a physical comparison path is present. -/
def pathPresent (u : AuthorizedAgentState ψ) : Bool :=
  match u.core.path with
  | .bot => false
  | .some _ _ => true

/-- A deletion marker is meaningful only while attached to a path component. -/
def deletionActive (u : AuthorizedAgentState ψ) : Bool :=
  decide (u.core.state = .eliminate_signal) && pathPresent u

/-- Remove an arbitrary orphan deletion state that has no path to delete. -/
def normalizeDeletion (u : AuthorizedAgentState ψ) : AuthorizedAgentState ψ :=
  if u.core.state = .eliminate_signal && !pathPresent u then
    ⟨{ u.core with state := .none }, false⟩
  else u

/-- Mark one present comparison component for priority deletion.  Permission is
consumed because a deleting carrier must never start another comparison wave. -/
def markComparisonForDeletion
    (u : AuthorizedAgentState ψ) : AuthorizedAgentState ψ :=
  match u.core.path with
  | .bot => u
  | .some _ _ => ⟨{ u.core with state := .eliminate_signal }, false⟩

/-- Whether one endpoint changes from follower to leader across a named stage. -/
def endpointLeaderBorn (before after : AuthorizedAgentState ψ) : Bool :=
  !before.core.leader && after.core.leader

/-- Executable transition-local birth event before or at CHECK.  The first two
clauses detect P'_ψ creation anywhere in the prefix through SIGMOVE; the last
two detect Algorithm-11 creation itself.  WRITE_SEQ has not run at either
boundary, so ordinary migration is not mistaken for birth. -/
def leaderBirthBeforeOrAtCheck
    (inputL inputR : AuthorizedAgentState ψ)
    (beforeCheck afterCheck : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    Bool :=
  endpointLeaderBorn inputL beforeCheck.1 ||
    endpointLeaderBorn inputR beforeCheck.2 ||
    endpointLeaderBorn beforeCheck.1 afterCheck.1 ||
    endpointLeaderBorn beforeCheck.2 afterCheck.2

/-- Execute the unchanged authorized suffix after CHECK.  Factoring this suffix
lets the repair observe a real birth event without storing a new state bit. -/
def authorizedAfterCheckSuffix (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := authorizedDisappear hψ l r
  let q := authorizedCompareSig hψ q.1 q.2
  let q := authorizedReconcile (suppressSig hψ) q.1 q.2
  let q := authorizedReconcile (eliminateLeadersNoCollision hψ) q.1 q.2
  authorizedReconcile (writeSeq hψ) q.1 q.2

/-- The staged factorization is definitionally the existing authorized repair;
only the newly exposed birth event changes the cleanup wrapper. -/
theorem authorizedAfterCheckSuffix_staged_eq (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    let beforeCheck := authorizedBeforeCheck hψ κ l r
    let afterCheck := authorizedCheckSig hψ beforeCheck.1 beforeCheck.2
    authorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2 =
      ppllAuthorizedRepair hψ κ l r := by
  rfl

/-- Mark every present final endpoint path when an earlier physical stage in
this same interaction actually created a leader. -/
def markLeaderBirth (born : Bool)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  if born then
    (markComparisonForDeletion q.1, markComparisonForDeletion q.2)
  else q

/-- Authorized comparison transition with source-zero residual cleanup.

Deletion has top priority.  A responder marker executes only Algorithm 9 and
returns; an initiator marker waits until it appears as a responder to its left
neighbor.  Otherwise the existing authorized repair runs, and a local leader
birth marks every endpoint path component for deletion. -/
def leaderCleanupAuthorizedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let l := normalizeDeletion l
  let r := normalizeDeletion r
  if deletionActive r then
    authorizedEliminateSig hψ l r
  else if deletionActive l then
    (l, r)
  else
    let beforeCheck := authorizedBeforeCheck hψ κ l r
    let afterCheck := authorizedCheckSig hψ beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l r beforeCheck afterCheck
    markLeaderBirth born
      (authorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2)

/-! ## Local deletion and domain contracts -/

/-- A present marked responder takes the deletion branch exactly. -/
theorem leaderCleanup_of_responder_deletion (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hnl : normalizeDeletion l = l) (hnr : normalizeDeletion r = r)
    (hr : deletionActive r = true) :
    leaderCleanupAuthorizedTransition hψ κ l r =
      authorizedEliminateSig hψ l r := by
  simp [leaderCleanupAuthorizedTransition, hnl, hnr, hr]

/-- A marked initiator cannot move, CHECK, or COMPARE while waiting to be
consumed from its left. -/
theorem leaderCleanup_initiator_waits (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hnl : normalizeDeletion l = l) (hnr : normalizeDeletion r = r)
    (hr : deletionActive r = false) (hl : deletionActive l = true) :
    leaderCleanupAuthorizedTransition hψ κ l r = (l, r) := by
  simp [leaderCleanupAuthorizedTransition, hnl, hnr, hr, hl]

/-- In the absence of a deletion marker or observed pre-CHECK birth, cleanup
is exactly the underlying authorized repair.  This is a conditional agreement
contract, not a claim that arbitrary configurations satisfy its premises. -/
theorem leaderCleanup_eq_authorized_of_inactive (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hnl : normalizeDeletion l = l) (hnr : normalizeDeletion r = r)
    (hr : deletionActive r = false) (hl : deletionActive l = false)
    (hbirth :
      let beforeCheck := authorizedBeforeCheck hψ κ l r
      let afterCheck := authorizedCheckSig hψ beforeCheck.1 beforeCheck.2
      leaderBirthBeforeOrAtCheck l r beforeCheck afterCheck = false) :
    leaderCleanupAuthorizedTransition hψ κ l r =
      ppllAuthorizedRepair hψ κ l r := by
  simp [leaderCleanupAuthorizedTransition, hnl, hnr, hr, hl,
    markLeaderBirth, hbirth, authorizedAfterCheckSuffix,
    ppllAuthorizedRepair, authorizedBeforeSuppress]

/-- A path-attached state is unchanged by orphan normalization. -/
theorem normalizeDeletion_eq_of_path_present (u : AuthorizedAgentState ψ)
    (hp : u.core.path ≠ .bot) : normalizeDeletion u = u := by
  cases hpath : u.core.path with
  | bot => exact (hp hpath).elim
  | some label bit => simp [normalizeDeletion, pathPresent, hpath]

/-- A path-attached elimination state enables the priority branch. -/
theorem deletionActive_eq_true (u : AuthorizedAgentState ψ)
    (hs : u.core.state = .eliminate_signal) (hp : u.core.path ≠ .bot) :
    deletionActive u = true := by
  cases hpath : u.core.path with
  | bot => exact (hp hpath).elim
  | some label bit => simp [deletionActive, pathPresent, hs, hpath]

/-- Every active responder marker is cleared in one predecessor interaction,
even when the left endpoint is arbitrary garbage. -/
theorem leaderCleanup_deletion_clears_responder (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hrpath : r.core.path ≠ .bot)
    (hrstate : r.core.state = .eliminate_signal) :
    let q := leaderCleanupAuthorizedTransition hψ κ l r
    q.2.core.state = .none ∧ q.2.core.path = .bot := by
  have hnr := normalizeDeletion_eq_of_path_present r hrpath
  have hdel := deletionActive_eq_true r hrstate hrpath
  change
    let q := leaderCleanupAuthorizedTransition hψ κ l r
    q.2.core.state = .none ∧ q.2.core.path = .bot
  unfold leaderCleanupAuthorizedTransition
  dsimp only
  rw [hnr]
  simp [hdel, authorizedEliminateSig, authorizedReconcile, eliminateSig,
    hrstate]

/-- One predecessor interaction propagates deletion left and clears the marked
responder.  This is the local induction step for a ψ-component source signal. -/
theorem leaderCleanup_deletion_propagates_left (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hlpath : l.core.path ≠ .bot) (hrpath : r.core.path ≠ .bot)
    (hrstate : r.core.state = .eliminate_signal)
    (hlnonterminal : l.core.label ≠ ⟨ψ - 1, by omega⟩) :
    let q := leaderCleanupAuthorizedTransition hψ κ l r
    q.1.core.state = .eliminate_signal ∧
      q.2.core.state = .none ∧ q.2.core.path = .bot := by
  have hnl := normalizeDeletion_eq_of_path_present l hlpath
  have hnr := normalizeDeletion_eq_of_path_present r hrpath
  have hdel := deletionActive_eq_true r hrstate hrpath
  rw [leaderCleanup_of_responder_deletion hψ κ l r hnl hnr hdel]
  simp [authorizedEliminateSig, authorizedReconcile, eliminateSig,
    hrstate, hlnonterminal]

/-- At the source boundary, a terminal predecessor clears the label-zero marker
without propagating deletion into the preceding group. -/
theorem leaderCleanup_deletion_stops_at_terminal (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hlpath : l.core.path ≠ .bot) (hrpath : r.core.path ≠ .bot)
    (hrstate : r.core.state = .eliminate_signal)
    (hlterminal : l.core.label = ⟨ψ - 1, by omega⟩) :
    let q := leaderCleanupAuthorizedTransition hψ κ l r
    q.1.core.state = l.core.state ∧ q.1.core.path = l.core.path ∧
      q.2.core.state = .none ∧ q.2.core.path = .bot := by
  have hnl := normalizeDeletion_eq_of_path_present l hlpath
  have hnr := normalizeDeletion_eq_of_path_present r hrpath
  have hdel := deletionActive_eq_true r hrstate hrpath
  rw [leaderCleanup_of_responder_deletion hψ κ l r hnl hnr hdel]
  simp [authorizedEliminateSig, authorizedReconcile, eliminateSig,
    hrstate, hlterminal]

/-- Marking and orphan normalization preserve Algorithm 1's numeric domain. -/
theorem cleanup_helpers_inProtocolDomain (u : AuthorizedAgentState ψ)
    (hu : u.core.inProtocolDomain κ) :
    (normalizeDeletion u).core.inProtocolDomain κ ∧
      (markComparisonForDeletion u).core.inProtocolDomain κ := by
  constructor
  · unfold normalizeDeletion
    split <;> simpa [AgentState.inProtocolDomain] using hu
  · unfold markComparisonForDeletion
    cases hp : u.core.path with
    | bot => exact hu
    | some label bit =>
        simpa [AgentState.inProtocolDomain, hp] using hu

/-- Leader-birth postprocessing preserves the domain whenever the underlying
transition output lies in it. -/
theorem markLeaderBirth_inProtocolDomain
    (born : Bool) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (hq : q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ) :
    let out := markLeaderBirth born q
    out.1.core.inProtocolDomain κ ∧ out.2.core.inProtocolDomain κ := by
  unfold markLeaderBirth
  split
  · exact ⟨(cleanup_helpers_inProtocolDomain q.1 hq.1).2,
      (cleanup_helpers_inProtocolDomain q.2 hq.2).2⟩
  · exact hq

attribute [local irreducible] ppllAuthorizedRepair

/-- The complete cleanup transition remains inside all declared numeric ranges. -/
theorem leaderCleanupAuthorizedTransition_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := leaderCleanupAuthorizedTransition hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain κ at hl0
  change r0.core.inProtocolDomain κ at hr0
  unfold leaderCleanupAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hψ) l0 r0
      (eliminateSig_inProtocolDomain hψ l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let beforeCheck := authorizedBeforeCheck hψ κ l0 r0
      let afterCheck := authorizedCheckSig hψ beforeCheck.1 beforeCheck.2
      let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
      let q := authorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2
      have hqBase := ppllAuthorizedRepair_inProtocolDomain
        hψ κ l0 r0 hl0 hr0
      have hstaged := authorizedAfterCheckSuffix_staged_eq hψ κ l0 r0
      change q = ppllAuthorizedRepair hψ κ l0 r0 at hstaged
      have hq : q.1.core.inProtocolDomain κ ∧
          q.2.core.inProtocolDomain κ := by
        rw [hstaged]
        exact hqBase
      exact markLeaderBirth_inProtocolDomain born q hq

attribute [local semireducible] ppllAuthorizedRepair

/-! ## Finite carrier and path-stall composition -/

/-- Total finite transition on the existing authorized bounded carrier.  The
repair adds no state value; it only changes transition priority. -/
def leaderCleanupBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := leaderCleanupAuthorizedTransition hψ κ l.erase r.erase
  let hq := leaderCleanupAuthorizedTransition_inProtocolDomain hψ κ
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

/-- Finite cleanup execution erases exactly to the audit transition. -/
theorem erase_leaderCleanupBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q := leaderCleanupBoundedTransition hψ κ l r
    (q.1.erase, q.2.erase) =
      leaderCleanupAuthorizedTransition hψ κ l.erase r.erase := by
  let q := leaderCleanupAuthorizedTransition hψ κ l.erase r.erase
  let hq := leaderCleanupAuthorizedTransition_inProtocolDomain hψ κ
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = (q.1, q.2)
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Active deletion is a physical priority phase, not ordinary comparison
stall.  Preserve and refresh its finite wait budget until the component is
scheduled as a responder; all other outputs use path-only expiration. -/
def deletionPriorityExpireOne (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ) : ExpiringAgentState ψ κ τ :=
  if deletionActive out.core.erase then
    ⟨out.core, freshStall τ⟩
  else pathExpireOne τ old out

/-- An active marked output survives timer accounting exactly. -/
theorem deletionPriorityExpireOne_of_active (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hactive : deletionActive out.core.erase = true) :
    deletionPriorityExpireOne τ old out = ⟨out.core, freshStall τ⟩ := by
  simp [deletionPriorityExpireOne, hactive]

/-- Compose source-zero deletion with the stricter path-only stall timer. -/
def leaderCleanupPathStallTransition (hψ : ψ > 0) (κ τ : Nat)
    (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := leaderCleanupBoundedTransition hψ κ l.core r.core
  let lOut : ExpiringAgentState ψ κ τ := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState ψ κ τ := ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne τ l lOut,
    deletionPriorityExpireOne τ r rOut)

/-- The combined cleanup protocol uses exactly the existing expiration carrier;
this certificate introduces no extra multiplicative state factor. -/
def leaderCleanupStateCertificate (ψ κ τ : Nat) :
    ExhaustiveList (ExpiringAgentState ψ κ τ) :=
  expiringAgentState ψ κ τ

/-- Cleanup reuses the duplicate-free expiration certificate exactly. -/
theorem leaderCleanupStateCertificate_values_nodup (ψ κ τ : Nat) :
    (leaderCleanupStateCertificate ψ κ τ).values.Nodup :=
  expiringAgentState_values_nodup ψ κ τ

/-- Cleanup changes no carrier type and has the exact semantic cardinality of
authorization plus path-stall expiration. -/
theorem leaderCleanupStateCertificate_values_length (ψ κ τ : Nat) :
    (leaderCleanupStateCertificate ψ κ τ).values.length =
      (2 * (PPLLFinite.boundedAgentState ψ κ).values.length) * (τ + 1) := by
  exact expiringAgentState_values_length ψ κ τ

/-- Packaged finite physical protocol for the combined cleanup experiment. -/
def leaderCleanupPathStallProtocol (hψ : ψ > 0) (κ τ : Nat) :
    PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := LeaderOutput
  transition := leaderCleanupPathStallTransition hψ κ τ
  output := fun s => if s.core.core.leader then .leader else .follower

/-! ## T19 regression on the n=4 recovery trace -/

/-- Recovery under expiration plus source-zero cleanup. -/
def cleanupRecoveryAfter : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule recoveryRing
    (leaderCleanupPathStallTransition (by omega) 0 0)
    recoveryConfig [1, 0, 3, 0]

/-- First checkpoint of the old T19 continuation. -/
def cleanupOldBadAfter1 : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (leaderCleanupPathStallTransition (by omega) 0 0)
    cleanupRecoveryAfter 1

/-- Second checkpoint of the old T19 continuation. -/
def cleanupOldBadAfter2 : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (leaderCleanupPathStallTransition (by omega) 0 0)
    cleanupOldBadAfter1 0

/-- Third checkpoint of the old T19 continuation. -/
def cleanupOldBadAfter3 : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (leaderCleanupPathStallTransition (by omega) 0 0)
    cleanupOldBadAfter2 2

/-- Fourth checkpoint of the old T19 continuation. -/
def cleanupOldBadAfter4 : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (leaderCleanupPathStallTransition (by omega) 0 0)
    cleanupOldBadAfter3 1

/-- Replay endpoint after the fifth edge of the old T19 continuation. -/
def cleanupOldBadFuture : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (leaderCleanupPathStallTransition (by omega) 0 0)
    cleanupOldBadAfter4 2

/-- Physical leader-output vector used to check every named replay prefix. -/
def cleanupLeaderVector (C : Fin 4 → ExpiringAgentState 2 0 0) : List Bool :=
  List.ofFn (fun i : Fin 4 => (C i).core.core.leader)

/-- Every prefix of the formerly bad five-edge replay retains exactly the
output vector `[leader,follower,follower,follower]`.  This is still only one
named continuation family, not Definition-1 safety. -/
theorem cleanup_old_bad_continuation_prefixwise_preserves_outputs :
    cleanupLeaderVector cleanupRecoveryAfter = [true, false, false, false] ∧
      cleanupLeaderVector cleanupOldBadAfter1 = [true, false, false, false] ∧
      cleanupLeaderVector cleanupOldBadAfter2 = [true, false, false, false] ∧
      cleanupLeaderVector cleanupOldBadAfter3 = [true, false, false, false] ∧
      cleanupLeaderVector cleanupOldBadAfter4 = [true, false, false, false] ∧
      cleanupLeaderVector cleanupOldBadFuture = [true, false, false, false] := by
  decide

/-- The recovery schedule still creates one leader and places both residual
source components into the priority deletion lifecycle.  Active deletion is
preserved even at zero path-stall budget. -/
theorem cleanup_recovery_creates_and_marks_leader_source :
    (cleanupRecoveryAfter 0).core.core.leader = true ∧
      (cleanupRecoveryAfter 1).core.core.leader = false ∧
      (cleanupRecoveryAfter 0).core.core.path = .some 0 0 ∧
      (cleanupRecoveryAfter 0).core.core.state = .eliminate_signal ∧
      (cleanupRecoveryAfter 1).core.core.path = .some 1 0 ∧
      (cleanupRecoveryAfter 1).core.core.state = .eliminate_signal := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The old T19 continuation no longer creates the leader at position two.
It consumes the terminal source component while the label-zero source component
remains physically marked, waiting for its predecessor edge. -/
theorem cleanup_old_bad_continuation_preserves_outputs :
    (cleanupOldBadFuture 0).core.core.leader = true ∧
      (cleanupOldBadFuture 1).core.core.leader = false ∧
      (cleanupOldBadFuture 2).core.core.leader = false ∧
      (cleanupOldBadFuture 3).core.core.leader = false ∧
      (cleanupOldBadFuture 0).core.core.path = .some 0 0 ∧
      (cleanupOldBadFuture 0).core.core.state = .eliminate_signal ∧
      (cleanupOldBadFuture 1).core.core.path = .bot ∧
      (cleanupOldBadFuture 2).core.core.path = .bot ∧
      (cleanupOldBadFuture 3).core.core.path = .bot := by
  decide

/-- One final predecessor interaction closes the deletion lifecycle left by the
old five-edge replay. -/
def cleanupAfterFinalDeletion : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule recoveryRing
    (leaderCleanupPathStallTransition (by omega) 0 0)
    cleanupOldBadFuture [3]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- After the predecessor edge, the unique output remains and all four physical
comparison paths are absent. -/
theorem cleanup_final_deletion_preserves_outputs_and_clears_paths :
    (cleanupAfterFinalDeletion 0).core.core.leader = true ∧
      (cleanupAfterFinalDeletion 1).core.core.leader = false ∧
      (cleanupAfterFinalDeletion 2).core.core.leader = false ∧
      (cleanupAfterFinalDeletion 3).core.core.leader = false ∧
      (cleanupAfterFinalDeletion 0).core.core.path = .bot ∧
      (cleanupAfterFinalDeletion 1).core.core.path = .bot ∧
      (cleanupAfterFinalDeletion 2).core.core.path = .bot ∧
      (cleanupAfterFinalDeletion 3).core.core.path = .bot := by
  decide

end PPLLLeaderCreationCleanupRepair

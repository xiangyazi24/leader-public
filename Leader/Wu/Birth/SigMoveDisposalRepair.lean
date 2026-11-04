import Leader.Wu.Birth.CheckParametricWait

set_option autoImplicit false

namespace BirthSigMoveDisposalRepair

open PPLL PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepPreCheckResetRepair BirthCheckCongestGuardRepair

variable {psi kappa tau : Nat}

/-! SIGMOVE transfers `path` before applying terminal action three/four.  A
pending disposal can therefore be left at an empty sender while its carrier
escapes.  This separately named repair converts that already-present physical
command to the existing deletion-priority phase at interaction entry.  A
marked initiator waits with its carrier; as a responder it is deleted and the
deletion propagates to the preceding component.  No new field is introduced.

The complete guarded host then runs unchanged.  In particular this preserves
the ordinary WAIT/GEN/full-signal comparison word when there is no pending
terminal disposal.  No claim of global protocol correctness is made here. -/

/-- Exactly the terminal action-three/action-four branch of the original
SIGMOVE control application, detected before any payload transfer. -/
def pendingTerminalDisposal (hpsi : psi > 0) (u : AgentState psi) : Bool :=
  match u.path2 with
  | none => false
  | some p2 => decide (u.label = ⟨psi - 1, by omega⟩ ∧
      (p2.action = 3 ∨ p2.action = 4))

/-- The new detector is tied to the actual source SIGMOVE assignment. -/
theorem pendingDisposal_is_original_control (hpsi : psi > 0)
    (u : AgentState psi) (h : pendingTerminalDisposal hpsi u = true) :
    (sigMoveApplyControl hpsi u).state = .eliminate_signal := by
  cases hp : u.path2 with
  | none => simp [pendingTerminalDisposal, hp] at h
  | some p2 =>
      simp only [pendingTerminalDisposal, hp, decide_eq_true_eq] at h
      rcases h with ⟨hl, ha | ha⟩ <;>
        simp [sigMoveApplyControl, hp, hl, ha]

/-- Convert a pending disposal to the existing meaningful deletion marker.
An empty carrier is unchanged, as in `markComparisonForDeletion`. -/
def prepareDisposal (hpsi : psi > 0) (u : AuthorizedAgentState psi) :
    AuthorizedAgentState psi :=
  if pendingTerminalDisposal hpsi u.core then markComparisonForDeletion u else u

theorem prepareDisposal_eq_of_clear (hpsi : psi > 0)
    (u : AuthorizedAgentState psi) (h : pendingTerminalDisposal hpsi u.core = false) :
    prepareDisposal hpsi u = u := by
  simp [prepareDisposal, h]

/-- Marking changes neither the carrier payload nor its location. -/
theorem prepareDisposal_path (hpsi : psi > 0) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.path = u.core.path := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

/-- A present pending carrier becomes an active deletion component before
the old host can reach SIGMOVE or CHECK. -/
theorem prepareDisposal_pending (hpsi : psi > 0) (u : AuthorizedAgentState psi)
    (hpending : pendingTerminalDisposal hpsi u.core = true)
    (hpath : u.core.path ≠ .bot) :
    (prepareDisposal hpsi u).core.state = .eliminate_signal ∧
      (prepareDisposal hpsi u).path0Crossed = false := by
  unfold prepareDisposal
  simp only [hpending, ↓reduceIte]
  cases hp : u.core.path with
  | bot => exact (hpath hp).elim
  | some label bit => simp [markComparisonForDeletion, hp]

/-- The preparatory operation uses an already domain-closed existing marker. -/
theorem prepareDisposal_inProtocolDomain (hpsi : psi > 0)
    (u : AuthorizedAgentState psi) (hu : u.core.inProtocolDomain kappa) :
    (prepareDisposal hpsi u).core.inProtocolDomain kappa := by
  unfold prepareDisposal
  split
  · exact (cleanup_helpers_inProtocolDomain u hu).2
  · exact hu

/-- The repaired authorized transition runs the unchanged guarded host after
making its already-present disposal controls effective. -/
def disposalAuthorizedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  guardedAuthorizedTransition hpsi kappa
    (prepareDisposal hpsi l) (prepareDisposal hpsi r)

theorem disposalAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := disposalAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa :=
  guardedAuthorizedTransition_inProtocolDomain hpsi kappa _ _
    (prepareDisposal_inProtocolDomain hpsi l hl)
    (prepareDisposal_inProtocolDomain hpsi r hr)

private theorem normalizeDeletion_path (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.path = u.core.path := by
  unfold normalizeDeletion
  split <;> rfl

attribute [local irreducible]
  PPLLWallSweepFinite.wallSweepResetProbeAuthorizedBeforeCheck
  wallSweepLeaderSinkAfterCheckSuffix

/-- An initiator carrying pending terminal disposal cannot transfer its
payload into an empty responder.  The payload stays attached to the active
deletion marker, ready for the predecessor interaction that removes it. -/
theorem pending_source_cannot_transfer
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hpending : pendingTerminalDisposal hpsi l.core = true)
    (hlpath : l.core.path ≠ .bot) (hrpath : r.core.path = .bot) :
    let q := disposalAuthorizedTransition hpsi kappa l r
    q.1.core.path = l.core.path ∧
      q.1.core.state = .eliminate_signal ∧ q.2.core.path = .bot := by
  let l0 := prepareDisposal hpsi l
  let r0 := prepareDisposal hpsi r
  have hlState : l0.core.state = .eliminate_signal :=
    (prepareDisposal_pending hpsi l hpending hlpath).1
  have hlPath : l0.core.path = l.core.path := prepareDisposal_path hpsi l
  have hlPresent : l0.core.path ≠ .bot := by simpa only [hlPath] using hlpath
  have hnl := normalizeDeletion_eq_of_path_present l0 hlPresent
  have hlActive := deletionActive_eq_true l0 hlState hlPresent
  have hrPath : (normalizeDeletion r0).core.path = .bot :=
    (normalizeDeletion_path r0).trans ((prepareDisposal_path hpsi r).trans hrpath)
  have hrInactive : deletionActive (normalizeDeletion r0) = false := by
    simp [deletionActive, pathPresent, hrPath]
  change
    let q := guardedAuthorizedTransition hpsi kappa l0 r0
    q.1.core.path = l.core.path ∧ q.1.core.state = .eliminate_signal ∧
      q.2.core.path = .bot
  unfold guardedAuthorizedTransition
  dsimp only
  rw [hnl]
  simp only [hrInactive, Bool.false_eq_true, ↓reduceIte, hlActive]
  exact ⟨hlPath, hlState, hrPath⟩

/-- Exact finite reification of the preparatory marker, with the original
authorized bounded carrier and no additional register. -/
def prepareBoundedDisposal (hpsi : psi > 0)
    (u : AuthorizedBoundedAgentState psi kappa) : AuthorizedBoundedAgentState psi kappa :=
  let q := prepareDisposal hpsi u.erase
  let hq := prepareDisposal_inProtocolDomain hpsi u.erase u.core.erase_inProtocolDomain
  ⟨BoundedAgentState.ofDomain q.core hq, q.path0Crossed⟩

theorem erase_prepareBoundedDisposal (hpsi : psi > 0)
    (u : AuthorizedBoundedAgentState psi kappa) :
    (prepareBoundedDisposal hpsi u).erase = prepareDisposal hpsi u.erase := by
  let q := prepareDisposal hpsi u.erase
  let hq := prepareDisposal_inProtocolDomain hpsi u.erase u.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.core hq).erase,
    q.path0Crossed⟩ : AuthorizedAgentState psi) = q
  rw [BoundedAgentState.erase_ofDomain]

def prepareExpiringDisposal (hpsi : psi > 0)
    (u : ExpiringAgentState psi kappa tau) : ExpiringAgentState psi kappa tau :=
  ⟨prepareBoundedDisposal hpsi u.core, u.stall⟩

/-- The complete finite repair retains every original stage, including
expiry and birth-signal initialization, after the early disposal marker. -/
def disposalFullTransition (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  guardedFullTransition hpsi kappa tau
    (prepareExpiringDisposal hpsi l) (prepareExpiringDisposal hpsi r)

theorem prepareBoundedDisposal_eq_of_clear (hpsi : psi > 0)
    (u : AuthorizedBoundedAgentState psi kappa)
    (h : pendingTerminalDisposal hpsi u.erase.core = false) :
    prepareBoundedDisposal hpsi u = u := by
  unfold prepareBoundedDisposal
  simp only [prepareDisposal_eq_of_clear hpsi u.erase h]
  cases u with
  | mk core permit =>
      simp only [AuthorizedBoundedAgentState.erase]
      rw [BoundedAgentState.ofDomain_erase]

/-- If neither endpoint has the pending source disposal command, the entire
new transition is exactly the previous guarded full host. -/
theorem disposalFullTransition_eq_of_clear
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : pendingTerminalDisposal hpsi l.core.erase.core = false)
    (hr : pendingTerminalDisposal hpsi r.core.erase.core = false) :
    disposalFullTransition hpsi kappa tau l r =
      guardedFullTransition hpsi kappa tau l r := by
  unfold disposalFullTransition prepareExpiringDisposal
  rw [prepareBoundedDisposal_eq_of_clear hpsi l.core hl,
    prepareBoundedDisposal_eq_of_clear hpsi r.core hr]

/-- The base finite pair erases exactly to the repaired authorized pair. -/
theorem erase_disposal_base (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := guardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l) (prepareBoundedDisposal hpsi r)
    (q.1.erase, q.2.erase) = disposalAuthorizedTransition hpsi kappa l.erase r.erase := by
  dsimp only
  rw [erase_guardedBoundedTransition, erase_prepareBoundedDisposal,
    erase_prepareBoundedDisposal]
  rfl

private theorem expiry_preserves_absence
    (old out : ExpiringAgentState psi kappa tau)
    (h : out.core.erase.core.path = .bot) :
    (deletionPriorityExpireOne tau old out).core.erase.core.path = .bot := by
  unfold deletionPriorityExpireOne PPLLPathStallComparisonRepair.pathExpireOne
  split
  · exact h
  · split
    · exact h
    · split
      · rfl
      · exact h

private theorem clearLeaderSignal_path
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.path = u.core.erase.core.path := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

private theorem clearLeaderSignal_state
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.state = u.core.erase.core.state := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

attribute [local irreducible] guardedBoundedTransition

/-- The no-escape property holds for the actual complete finite transition,
for every parameter value and arbitrary other input fields.  Expiry keeps the
active left deletion carrier and cannot create a path at the empty right. -/
theorem pending_source_cannot_escape_full
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hpending : pendingTerminalDisposal hpsi l.core.erase.core = true)
    (hlpath : l.core.erase.core.path ≠ .bot)
    (hrpath : r.core.erase.core.path = .bot) :
    let q := disposalFullTransition hpsi kappa tau l r
    q.1.core.erase.core.path = l.core.erase.core.path ∧
      q.1.core.erase.core.state = .eliminate_signal ∧
      q.2.core.erase.core.path = .bot := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := guardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  have he := erase_disposal_base hpsi kappa l.core r.core
  have hf := pending_source_cannot_transfer hpsi kappa l.core.erase r.core.erase
    hpending hlpath hrpath
  rw [← he] at hf
  change q.1.erase.core.path = l.core.erase.core.path ∧
    q.1.erase.core.state = .eliminate_signal ∧ q.2.erase.core.path = .bot at hf
  have hlPresent : lOut.core.erase.core.path ≠ .bot := by
    simpa only [lOut, hf.1] using hlpath
  have hactive := deletionActive_eq_true lOut.core.erase hf.2.1 hlPresent
  have hleft := deletionPriorityExpireOne_of_active tau l0 lOut hactive
  have hright := expiry_preserves_absence r0 rOut hf.2.2
  change
    let z := initializeFollowerPairBirthSignals l0 r0
      (deletionPriorityExpireOne tau l0 lOut,
        deletionPriorityExpireOne tau r0 rOut)
    z.1.core.erase.core.path = l.core.erase.core.path ∧
      z.1.core.erase.core.state = .eliminate_signal ∧ z.2.core.erase.core.path = .bot
  unfold initializeFollowerPairBirthSignals
  split
  · simp only [clearLeaderSignal_path, clearLeaderSignal_state]
    rw [hleft]
    exact hf.imp (fun h => h) (fun h => ⟨h.1, hright⟩)
  · rw [hleft]
    exact hf.imp (fun h => h) (fun h => ⟨h.1, hright⟩)

attribute [local semireducible]
  guardedBoundedTransition
  PPLLWallSweepFinite.wallSweepResetProbeAuthorizedBeforeCheck
  wallSweepLeaderSinkAfterCheckSuffix

/-! ## Complete-host positive and negative regressions -/

open BirthFullHostRulerCounterexample BirthFullHostWaitedRulerCounterexample

/-- The independent audit's eighteen-edge complete-signal escape word. -/
def disposalRegressionWord : DetSchedule 8 :=
  List.replicate 8 0 ++ [1, 2, 0, 1, 2, 3, 2, 4, 3, 4]

def disposalRegressionPrefix (t : Nat) : Fin 8 → Local :=
  runLocalSchedule ringEight (disposalFullTransition (by omega) 2 16)
    waitedInitial (disposalRegressionWord.take t)

private theorem get_ofFn {Q : Type} (C : Fin 8 → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

private def cachedRun {Q : Type} (T : Q → Q → Q × Q) :
    DetSchedule 8 → Vector Q 8 → Vector Q 8
  | [], C => C
  | e :: rest, C => cachedRun T rest (Vector.ofFn (localStep ringEight T C.get e))

private theorem cachedRun_correct {Q : Type} (T : Q → Q → Q × Q)
    (C : Fin 8 → Q) (word : DetSchedule 8) :
    (cachedRun T word (Vector.ofFn C)).get = runLocalSchedule ringEight T C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [cachedRun, get_ofFn, runLocalSchedule]
      exact ih _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The observed mismatching terminal payload now stays at three, attached
to deletion, instead of escaping to four.  The next predecessor interaction
deletes it and marks the preceding component. -/
theorem actual_disposal_blocks_escape :
    (disposalRegressionPrefix 13 3).core.erase.core.path2 = some ⟨0, 0, 0, 3⟩ ∧
      (disposalRegressionPrefix 14 3).core.core.path = .some 1 0 ∧
      (disposalRegressionPrefix 14 3).core.core.state = .eliminate_signal ∧
      (disposalRegressionPrefix 14 4).core.core.path = .bot ∧
      (disposalRegressionPrefix 15 3).core.core.path = .bot ∧
      (disposalRegressionPrefix 15 2).core.core.state = .eliminate_signal := by
  unfold disposalRegressionPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Every prefix of the complete-signal counterexample now retains exactly
leader six.  This is a finite regression, not arbitrary-schedule safety. -/
theorem disposal_blocks_eighteen_step_birth :
    ∀ t : Fin 19, ∀ i : Fin 8,
      (disposalRegressionPrefix t.val i).core.core.leader = true ↔ i = 6 := by
  unfold disposalRegressionPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The earlier mixed-component forty-two-edge regression remains blocked
after the disposal repair is composed with the existing congestion guard. -/
theorem disposal_blocks_forty_two_step_birth :
    ∀ t : Fin 43, ∀ i : Fin 8,
      (runLocalSchedule ringEight (disposalFullTransition (by omega) 2 16)
        waitedInitial (waitedSchedule.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The complete repaired host still executes ordinary WAIT/GEN and accepts
a complete legitimate equal signal in the original thirteen-edge word. -/
theorem disposal_preserves_thirteen_step_birth :
    let C := runLocalSchedule ringEight
      (disposalFullTransition (by omega) 2 16) equalInitial equalSchedule
    (∀ i : Fin 8, (C i).core.core.leader = true ↔ i = 2) ∧
      (C 2).core.core.label = 0 ∧ (C 2).core.core.signal_B = 0 := by
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- All four two-bit source words remain live with the fresh-budget initial
family.  The repair does not require a chosen all-zero payload. -/
theorem disposal_accepts_all_two_bit_words (a b : Bool) :
    let C := runLocalSchedule ringEight
      (disposalFullTransition (by omega) 2 16)
      (BirthCheckParametricWait.familyInitial 16 a b) equalSchedule
    (∀ i : Fin 8, (C i).core.core.leader = true ↔ i = 2) ∧
      (C 2).core.core.label = 0 ∧ (C 2).core.core.signal_B = 0 := by
  cases a <;> cases b <;>
    simp only [← cachedRun_correct] <;> decide

end BirthSigMoveDisposalRepair

#print axioms BirthSigMoveDisposalRepair.pendingDisposal_is_original_control
#print axioms BirthSigMoveDisposalRepair.disposalAuthorizedTransition_inProtocolDomain
#print axioms BirthSigMoveDisposalRepair.pending_source_cannot_transfer
#print axioms BirthSigMoveDisposalRepair.erase_prepareBoundedDisposal
#print axioms BirthSigMoveDisposalRepair.disposalFullTransition_eq_of_clear
#print axioms BirthSigMoveDisposalRepair.pending_source_cannot_escape_full
#print axioms BirthSigMoveDisposalRepair.actual_disposal_blocks_escape
#print axioms BirthSigMoveDisposalRepair.disposal_blocks_eighteen_step_birth
#print axioms BirthSigMoveDisposalRepair.disposal_blocks_forty_two_step_birth
#print axioms BirthSigMoveDisposalRepair.disposal_preserves_thirteen_step_birth
#print axioms BirthSigMoveDisposalRepair.disposal_accepts_all_two_bit_words

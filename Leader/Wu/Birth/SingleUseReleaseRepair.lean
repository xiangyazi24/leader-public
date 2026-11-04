import Leader.Wu.Birth.TossReleaseLifecycleWitnesses

set_option autoImplicit false

namespace BirthSingleUseReleaseRepair

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepNormalResetContract
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair
  BirthDisposalRouteInvariant BirthMismatchDisposalProducer BirthArrivalCaptureRepair
  BirthGenerationControlRepair BirthTossCheckPreservationRepair

variable {psi kappa tau : Nat}

/-! A terminal action five has completed its effect once it sets depart.
Its token is consumed at that execution, while the current depart state and
the ensuing backward departure propagation are retained.  Nonterminal
action five and every other action keep their original behavior.

The executable authorized adapter uses a post-control token projection.
The exact source-row and control-tail equalities below show that this is the
same operation as clearing path2 inside the terminal action-five assignment,
before any CHECK or later source can run.  No new protocol field is added. -/

/-- Clear a terminal action-five token.  In the host this projection is
applied only after the original control tail has interpreted the token. -/
def clearTerminalRelease (hpsi : psi > 0) (u : AgentState psi) : AgentState psi :=
  match u.path2 with
  | some p =>
      if u.label = ⟨psi - 1, by omega⟩ ∧ p.action = 5 then
        { u with path2 := none }
      else u
  | none => u

@[simp] theorem clearTerminalRelease_state (hpsi : psi > 0) (u : AgentState psi) :
    (clearTerminalRelease hpsi u).state = u.state := by
  unfold clearTerminalRelease
  split
  · split <;> rfl
  · rfl

@[simp] theorem clearTerminalRelease_label (hpsi : psi > 0) (u : AgentState psi) :
    (clearTerminalRelease hpsi u).label = u.label := by
  unfold clearTerminalRelease
  split
  · split <;> rfl
  · rfl

@[simp] theorem clearTerminalRelease_path (hpsi : psi > 0) (u : AgentState psi) :
    (clearTerminalRelease hpsi u).path = u.path := by
  unfold clearTerminalRelease
  split
  · split <;> rfl
  · rfl

private theorem clearTerminalRelease_set_state (hpsi : psi > 0)
    (u : AgentState psi) (s : MainState) :
    clearTerminalRelease hpsi { u with state := s } =
      { clearTerminalRelease hpsi u with state := s } := by
  cases hp : u.path2
  · simp [clearTerminalRelease, hp]
  · rename_i p
    by_cases h : u.label = ⟨psi - 1, by omega⟩ ∧ p.action = 5
    all_goals simp [clearTerminalRelease, hp, h]

/-- All unrelated endpoint registers are exactly the old registers. -/
theorem clearTerminalRelease_only_control (hpsi : psi > 0) (u : AgentState psi) :
    { clearTerminalRelease hpsi u with path2 := u.path2 } = u := by
  unfold clearTerminalRelease
  split
  · split <;> rfl
  · rfl

/-- Nonterminal release still travels toward its intended terminal. -/
theorem clearTerminalRelease_nonterminal (hpsi : psi > 0) (u : AgentState psi)
    (hl : u.label ≠ ⟨psi - 1, by omega⟩) : clearTerminalRelease hpsi u = u := by
  cases hp : u.path2 <;> simp [clearTerminalRelease, hp, hl]

/-- No other opcode is removed by the token projection. -/
theorem clearTerminalRelease_other_action (hpsi : psi > 0) (u : AgentState psi)
    (p : Path2Info) (hp : u.path2 = some p) (ha : p.action ≠ 5) :
    clearTerminalRelease hpsi u = u := by
  simp [clearTerminalRelease, hp, ha]

private theorem clearTerminalRelease_terminal_no_five (hpsi : psi > 0)
    (u : AgentState psi) (p : Path2Info)
    (hl : u.label = ⟨psi - 1, by omega⟩)
    (hp : (clearTerminalRelease hpsi u).path2 = some p) : p.action ≠ 5 := by
  cases hu : u.path2 with
  | none => simp [clearTerminalRelease, hu] at hp
  | some q =>
      by_cases hq : q.action = 5
      · simp [clearTerminalRelease, hu, hl, hq] at hp
      · have heq : some q = some p := by
          simpa [clearTerminalRelease, hu, hl, hq] using hp
        cases Option.some.inj heq
        exact hq

/-- The source assignment differs precisely at the already executed
terminal action-five row; action three, four and six remain untouched. -/
def singleUseApplyControl (hpsi : psi > 0) (u : AgentState psi) : AgentState psi :=
  match u.path2 with
  | some p =>
    let u := if u.label = (⟨psi - 1, by omega⟩ : Fin psi) ∧
        (p.action = 3 ∨ p.action = 4) then
      { u with state := .eliminate_signal } else u
    let u := if u.label = (⟨psi - 1, by omega⟩ : Fin psi) ∧ p.action = 5 then
      { u with state := .depart, path2 := none } else u
    if u.label = (⟨0, hpsi⟩ : Fin psi) ∧ p.action = 6 then
      { u with state := .toss } else u
  | none => u

/-- The post-control implementation equals the source assignment exactly,
including psi one and arbitrary raw token data. -/
theorem singleUseApplyControl_eq_clear (hpsi : psi > 0) (u : AgentState psi) :
    singleUseApplyControl hpsi u = clearTerminalRelease hpsi (sigMoveApplyControl hpsi u) := by
  cases hp : u.path2
  · simp [singleUseApplyControl, sigMoveApplyControl, clearTerminalRelease, hp]
  · rename_i p
    by_cases ht : u.label = ⟨psi - 1, by omega⟩
    all_goals by_cases h5 : p.action = 5
    all_goals by_cases h34 : p.action = 3 ∨ p.action = 4
    all_goals by_cases hz : u.label = ⟨0, hpsi⟩
    all_goals by_cases h6 : p.action = 6
    all_goals simp_all [singleUseApplyControl, sigMoveApplyControl, clearTerminalRelease]

/-- Applying action five at a terminal retains its complete current
departure effect and removes the token which would repeat that effect. -/
theorem singleUseApplyControl_release (hpsi : psi > 0) (u : AgentState psi)
    (p : Path2Info) (hp : u.path2 = some p) (ha : p.action = 5)
    (hl : u.label = ⟨psi - 1, by omega⟩) :
    singleUseApplyControl hpsi u = { u with state := .depart, path2 := none } := by
  simp [singleUseApplyControl, hp, ha, hl]

def singleUseControlTail (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let l := singleUseApplyControl hpsi l
  let r := singleUseApplyControl hpsi r
  let l := if r.state = .depart then
    if l.label.val < psi - 1 ∧ l.state = .CHECK_ready then
      { l with state := .depart }
    else l
  else l
  (l, r)

/-- Consumption commutes with the original backward departure propagation.
The executable projection therefore performs no late state correction. -/
theorem singleUseControlTail_eq_clear (hpsi : psi > 0) (l r : AgentState psi) :
    let old := sigMoveControlTail hpsi l r
    singleUseControlTail hpsi l r =
      (clearTerminalRelease hpsi old.1, clearTerminalRelease hpsi old.2) := by
  unfold singleUseControlTail sigMoveControlTail
  rw [singleUseApplyControl_eq_clear, singleUseApplyControl_eq_clear]
  dsimp only
  simp only [clearTerminalRelease_state, clearTerminalRelease_label]
  split
  · split
    · simp only [clearTerminalRelease_set_state, clearTerminalRelease_label]
    · rfl
  · rfl

/-- The entire old control tail's state, payload and label outputs survive,
including the departure propagated to a ready predecessor. -/
theorem singleUseControlTail_preserves_departure (hpsi : psi > 0)
    (l r : AgentState psi) :
    let q := singleUseControlTail hpsi l r
    let old := sigMoveControlTail hpsi l r
    q.1.state = old.1.state ∧ q.2.state = old.2.state ∧
      q.1.path = old.1.path ∧ q.2.path = old.2.path ∧
      q.1.label = old.1.label ∧ q.2.label = old.2.label := by
  rw [singleUseControlTail_eq_clear]
  simp

private theorem clearTerminalRelease_inProtocolDomain (hpsi : psi > 0)
    (u : AgentState psi) (hu : u.inProtocolDomain kappa) :
    (clearTerminalRelease hpsi u).inProtocolDomain kappa := by
  unfold clearTerminalRelease
  split
  · split
    · rw [inProtocolDomain_iff_path2_frame]
      exact ⟨True.intro, ((inProtocolDomain_iff_path2_frame u).1 hu).2⟩
    · exact hu
  · exact hu

/-- The same preclear, captured transfers and leader wall precede the
source-shaped single-use control tail. -/
def singleUseCaptureSigMove (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let p := sigMoveLeaderPreclear hpsi l r
  let moved := captureTransfers p.1 p.2
  let wall := comparisonLeaderWall moved.1 moved.2
  singleUseControlTail hpsi wall.1 wall.2

theorem singleUseCaptureSigMove_eq_clear (hpsi : psi > 0) (l r : AgentState psi) :
    let old := captureSigMoveLeaderWall hpsi l r
    singleUseCaptureSigMove hpsi l r =
      (clearTerminalRelease hpsi old.1, clearTerminalRelease hpsi old.2) := by
  unfold singleUseCaptureSigMove captureSigMoveLeaderWall
  exact singleUseControlTail_eq_clear hpsi _ _

/-- The actual full captured SIGMOVE leaves no reusable action five at a
terminal endpoint.  Later production of a new five is a separate event. -/
theorem singleUseCaptureSigMove_terminal_no_five (hpsi : psi > 0)
    (l r : AgentState psi) :
    let q := singleUseCaptureSigMove hpsi l r
    (∀ p : Path2Info, q.1.label = ⟨psi - 1, by omega⟩ →
      q.1.path2 = some p → p.action ≠ 5) ∧
    (∀ p : Path2Info, q.2.label = ⟨psi - 1, by omega⟩ →
      q.2.path2 = some p → p.action ≠ 5) := by
  rw [singleUseCaptureSigMove_eq_clear]
  constructor <;> intro p hl hp
  all_goals simp only [clearTerminalRelease_label] at hl
  all_goals exact clearTerminalRelease_terminal_no_five hpsi _ p hl hp

/-- Existing authorization is computed from the unchanged movement and
labels.  Only the consumed control is projected from the returned cores. -/
def authorizedSingleUseReleaseMove (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := authorizedCaptureSigMove hpsi l r
  (⟨clearTerminalRelease hpsi q.1.core, q.1.path0Crossed⟩,
    ⟨clearTerminalRelease hpsi q.2.core, q.2.path0Crossed⟩)

/-- The actual authorized adapter executes the source-shaped replacement
inside the control tail, with no intervening CHECK or other writer. -/
theorem authorizedSingleUseReleaseMove_core (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    let q := authorizedSingleUseReleaseMove hpsi l r
    (q.1.core, q.2.core) = singleUseCaptureSigMove hpsi l.core r.core := by
  rw [singleUseCaptureSigMove_eq_clear]
  exact congrArg (fun q : AgentState psi × AgentState psi =>
    (clearTerminalRelease hpsi q.1, clearTerminalRelease hpsi q.2))
    (authorizedCaptureSigMove_core hpsi l r)

theorem authorizedSingleUseReleaseMove_inProtocolDomain (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := authorizedSingleUseReleaseMove hpsi l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  have h := authorizedCaptureSigMove_inProtocolDomain hpsi l r hl hr
  exact ⟨clearTerminalRelease_inProtocolDomain hpsi _ h.1,
    clearTerminalRelease_inProtocolDomain hpsi _ h.2⟩

/-- The prior freshly acquired state guarantee is retained by token
consumption, for the actual current Step1 movement event. -/
theorem singleUseCaptureSigMove_moved_not_equal (hpsi : psi > 0)
    (l r : AgentState psi)
    (hm :
      let b := sigMoveLeaderPreclear hpsi l r
      pathMovedRight b.1 b.2 (sigMoveStep1 b.1 b.2).1 (sigMoveStep1 b.1 b.2).2 = true) :
    let q := singleUseCaptureSigMove hpsi l r
    q.1.state ≠ .equal ∧ q.2.state ≠ .equal := by
  rw [singleUseCaptureSigMove_eq_clear]
  simp only [clearTerminalRelease_state]
  exact captureSigMoveLeaderWall_moved_not_equal hpsi l r hm

/-! Complete finite integration.  The repaired generation prefix and the
toss-preserving CHECK are unchanged; the sole new boundary is the consumed
terminal release between SIGMOVE control execution and CHECK. -/

def singleUseBeforeCheck (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let b := generationBeforeMove hpsi kappa l r
  let q := authorizedSingleUseReleaseMove hpsi b.1 b.2
  sanitizeAuthorizedPair hpsi (preCheckResetWall q.1 q.2)

attribute [local irreducible] generationBeforeMove authorizedSingleUseReleaseMove

theorem singleUseBeforeCheck_inProtocolDomain (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := singleUseBeforeCheck hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let b := generationBeforeMove hpsi kappa l r
  have hb := generationBeforeMove_inProtocolDomain hpsi kappa l r hl hr
  have hm := authorizedSingleUseReleaseMove_inProtocolDomain hpsi b.1 b.2 hb.1 hb.2
  let m := authorizedSingleUseReleaseMove hpsi b.1 b.2
  have hw := preCheckResetWall_inProtocolDomain m.1 m.2 hm.1 hm.2
  exact ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi _ hw.1,
    sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi _ hw.2⟩

def singleUseGuardedAuthorizedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then (l0, r0)
  else
    let beforeCheck := singleUseBeforeCheck hpsi kappa l0 r0
    let afterCheck := preserveTossCheck hpsi beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born (actionOneAfterCheckSuffix hpsi afterCheck.1 afterCheck.2)

attribute [local irreducible] singleUseBeforeCheck actionOneAfterCheckSuffix

theorem singleUseGuardedAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := singleUseGuardedAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold singleUseGuardedAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let b := singleUseBeforeCheck hpsi kappa l0 r0
      have hb := singleUseBeforeCheck_inProtocolDomain hpsi kappa l0 r0 hl0 hr0
      let c := preserveTossCheck hpsi b.1 b.2
      have hc := preserveTossCheck_inProtocolDomain hpsi b.1 b.2 hb.1 hb.2
      exact markLeaderBirth_inProtocolDomain _ _
        (actionOneAfterCheckSuffix_inProtocolDomain hpsi kappa c.1 c.2 hc.1 hc.2)

def singleUseGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa × AuthorizedBoundedAgentState psi kappa :=
  let q := singleUseGuardedAuthorizedTransition hpsi kappa l.erase r.erase
  let hq := singleUseGuardedAuthorizedTransition_inProtocolDomain hpsi kappa
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem erase_singleUseGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := singleUseGuardedBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) = singleUseGuardedAuthorizedTransition hpsi kappa l.erase r.erase := by
  unfold singleUseGuardedBoundedTransition
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

/-- The complete finite host with single-use terminal release, using the
established disposal input, expiry rule and leader-signal initialization. -/
def singleUseFullTransition (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := singleUseGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  initializeFollowerPairBirthSignals l0 r0
    (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)

private theorem singleUseGuarded_eq_of_active (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (ha : deletionActive (normalizeDeletion l) = true ∨
      deletionActive (normalizeDeletion r) = true) :
    singleUseGuardedAuthorizedTransition hpsi kappa l r =
      tossGuardedAuthorizedTransition hpsi kappa l r := by
  unfold singleUseGuardedAuthorizedTransition tossGuardedAuthorizedTransition
  dsimp only
  by_cases hr : deletionActive (normalizeDeletion r) = true
  · simp only [hr, ↓reduceIte]
  · have hl : deletionActive (normalizeDeletion l) = true := ha.resolve_right hr
    simp only [hr, hl, ↓reduceIte]

attribute [local irreducible] tossGuardedBoundedTransition

/-- Pre-existing disposal has the identical complete successor, so consuming
action five does not alter the already proved action-four deletion service. -/
theorem singleUseFull_eq_tossFull_of_due
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (ha : DisposalDue hpsi l.core.erase ∨ DisposalDue hpsi r.core.erase) :
    singleUseFullTransition hpsi kappa tau l r = tossFullTransition hpsi kappa tau l r := by
  have hactive : deletionActive (preparedInput hpsi l.core.erase) = true ∨
      deletionActive (preparedInput hpsi r.core.erase) = true :=
    ha.imp (prepared_due_active hpsi l.core.erase) (prepared_due_active hpsi r.core.erase)
  have hr : singleUseGuardedAuthorizedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core).erase
      (prepareBoundedDisposal hpsi r.core).erase =
      tossGuardedAuthorizedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core).erase
        (prepareBoundedDisposal hpsi r.core).erase := by
    rw [erase_prepareBoundedDisposal, erase_prepareBoundedDisposal]
    exact singleUseGuarded_eq_of_active hpsi kappa _ _ hactive
  have hb : singleUseGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) =
      tossGuardedBoundedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) := by
    unfold singleUseGuardedBoundedTransition tossGuardedBoundedTransition
    dsimp only
    simp only [hr]
  unfold singleUseFullTransition tossFullTransition
  dsimp only [prepareExpiringDisposal]
  rw [hb]

#print axioms clearTerminalRelease_only_control
#print axioms clearTerminalRelease_nonterminal
#print axioms clearTerminalRelease_other_action
#print axioms singleUseApplyControl_eq_clear
#print axioms singleUseApplyControl_release
#print axioms singleUseControlTail_eq_clear
#print axioms singleUseControlTail_preserves_departure
#print axioms singleUseCaptureSigMove_eq_clear
#print axioms singleUseCaptureSigMove_terminal_no_five
#print axioms authorizedSingleUseReleaseMove_core
#print axioms authorizedSingleUseReleaseMove_inProtocolDomain
#print axioms singleUseCaptureSigMove_moved_not_equal
#print axioms singleUseBeforeCheck_inProtocolDomain
#print axioms singleUseGuardedAuthorizedTransition_inProtocolDomain
#print axioms erase_singleUseGuardedBoundedTransition
#print axioms singleUseFull_eq_tossFull_of_due

end BirthSingleUseReleaseRepair

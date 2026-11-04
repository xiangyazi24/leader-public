import Leader.Wu.Birth.DisposalRouteInvariant
import Leader.Wu.Elimination.MultiLeaderCleanup

set_option autoImplicit false

namespace BirthMismatchDisposalProducer

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLWallSweepNormalResetContract
  PPLLTerminalEqualSupportRepair PPLLCompleteMultiLeaderCleanup
  PPLLComparisonHistory PPLLWriteIncrementGate
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair
  BirthDisposalRouteInvariant

variable {psi kappa tau : Nat}

/-! CHECK's larger/less results are action-four/action-six commands.  The
retained raw COMPARE reinterprets every position-zero token, including these
fresh commands.  The existing action-one candidate is integrated here into
the exact COMPARE slot of the entry-disposal host.  All other prefix, CHECK,
reset, leader-sink, WRITE, expiry, and birth-signal stages are retained.

This is a separately named transition on the same finite state carrier.
The general producer below analyzes the actual post-CHECK suffix and expiry;
a raw CHECK result alone is not treated as a complete-host postcondition. -/

/-- The old raw row changes a fresh larger command to the opposite moving
action in the same interaction, before the next entry hook can inspect it. -/
theorem raw_compare_reverses_larger (hpsi : psi > 0) (r : AgentState psi)
    (hp : r.path2 = some ⟨0, 0, 0, 4⟩) (hb : r.bit = true) :
    (compareBitUpdateR hpsi r).path2 = some ⟨0, 0, 0, 3⟩ := by
  simp [compareBitUpdateR, hp, hb]

/-- Replace only the existing authorized COMPARE call, retaining the literal
DISAPPEAR, reset-kill, leader sink, and gated WRITE sequence. -/
def actionOneAfterCheckSuffix (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile (suppressSigResetKill hpsi) q1.1 q1.2
  authorizedPostSuppressLeaderSink hpsi q2.1 q2.2

/-- The substituted row already has a domain theorem in the cleanup module;
all remaining suffix stages use their existing domain proofs. -/
theorem actionOneAfterCheckSuffix_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := actionOneAfterCheckSuffix hpsi l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let q0 := authorizedDisappear hpsi l r
  have h0 := authorizedReconcile_inProtocolDomain (disappear hpsi) l r
    (disappear_inProtocolDomain hpsi l.core r.core hl hr)
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  have h1 := authorizedCompareSigActionOne_inProtocolDomain hpsi q0.1 q0.2 h0.1 h0.2
  let q2 := authorizedReconcile (suppressSigResetKill hpsi) q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain (suppressSigResetKill hpsi) q1.1 q1.2
    (suppressSigResetKill_inProtocolDomain hpsi q1.1.core q1.2.core h1.1 h1.2)
  exact authorizedPostSuppressLeaderSink_inProtocolDomain hpsi q2.1 q2.2 h2.1 h2.2

/-- The guarded authorized host with exactly the COMPARE-slot substitution.
Deletion remains the first branch and suppresses the entire ordinary tail. -/
def actionOneGuardedAuthorizedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then (l0, r0)
  else
    let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l0 r0
    let afterCheck := congestGuardCheck hpsi beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born (actionOneAfterCheckSuffix hpsi afterCheck.1 afterCheck.2)

attribute [local irreducible]
  wallSweepResetProbeAuthorizedBeforeCheck wallSweepLeaderSinkAfterCheckSuffix
  actionOneAfterCheckSuffix

theorem actionOneGuardedAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := actionOneGuardedAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold actionOneGuardedAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let q0 := wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l0 r0
      have h0 := wallSweepResetProbeAuthorizedBeforeCheck_inProtocolDomain
        hpsi kappa l0 r0 hl0 hr0
      let qR := preCheckResetWall q0.1 q0.2
      have hR := preCheckResetWall_inProtocolDomain q0.1 q0.2 h0.1 h0.2
      let q1 := sanitizeAuthorizedPair hpsi qR
      have h1 : q1.1.core.inProtocolDomain kappa ∧ q1.2.core.inProtocolDomain kappa :=
        ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.1 hR.1,
          sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.2 hR.2⟩
      let q2 := congestGuardCheck hpsi q1.1 q1.2
      have h2 := congestGuardCheck_inProtocolDomain hpsi q1.1 q1.2 h1.1 h1.2
      exact markLeaderBirth_inProtocolDomain _ _
        (actionOneAfterCheckSuffix_inProtocolDomain hpsi kappa q2.1 q2.2 h2.1 h2.2)

/-- Entry disposal is composed with the new authorized host at the same
physical boundary as in the frozen disposal repair. -/
def actionOneDisposalAuthorizedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  actionOneGuardedAuthorizedTransition hpsi kappa
    (prepareDisposal hpsi l) (prepareDisposal hpsi r)

theorem actionOneDisposalAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := actionOneDisposalAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa :=
  actionOneGuardedAuthorizedTransition_inProtocolDomain hpsi kappa _ _
    (prepareDisposal_inProtocolDomain hpsi l hl)
    (prepareDisposal_inProtocolDomain hpsi r hr)

/-- Exact reification into the original authorized bounded carrier. -/
def actionOneGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa × AuthorizedBoundedAgentState psi kappa :=
  let q := actionOneGuardedAuthorizedTransition hpsi kappa l.erase r.erase
  let hq := actionOneGuardedAuthorizedTransition_inProtocolDomain hpsi kappa
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem erase_actionOneGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := actionOneGuardedBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) = actionOneGuardedAuthorizedTransition hpsi kappa l.erase r.erase := by
  unfold actionOneGuardedBoundedTransition
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

/-- The complete named host changes only the COMPARE row.  Prepared inputs
are still passed to the original deletion-priority expiry and final
follower-pair birth-signal initialization. -/
def actionOneFullTransition (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := actionOneGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  initializeFollowerPairBirthSignals l0 r0
    (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)

theorem erase_actionOne_disposal_base (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := actionOneGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l) (prepareBoundedDisposal hpsi r)
    (q.1.erase, q.2.erase) =
      actionOneDisposalAuthorizedTransition hpsi kappa l.erase r.erase := by
  dsimp only
  rw [erase_actionOneGuardedBoundedTransition, erase_prepareBoundedDisposal,
    erase_prepareBoundedDisposal]
  rfl

/-! ## Actual suffix contracts -/

/-- Current fields needed to follow a payload through the comparison tail.
The tuple is only a proof projection of the existing physical state. -/
def anchorView (u : AgentState psi) : Bool × Bool × Fin psi × PathInfo :=
  (u.leader, u.reset_cmd, u.label, u.path)

private theorem disappear_anchor (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    anchorView (authorizedDisappear hpsi l r).1.core = anchorView l.core ∧
      anchorView (authorizedDisappear hpsi l r).2.core = anchorView r.core := by
  have hstartR (a b : AgentState psi) :
      anchorView (disappearStartR hpsi a b).1 = anchorView a ∧
        anchorView (disappearStartR hpsi a b).2 = anchorView b := by
    unfold disappearStartR
    split <;> exact ⟨rfl, rfl⟩
  have hstartL (a b : AgentState psi) :
      anchorView (disappearStartL hpsi a b).1 = anchorView a ∧
        anchorView (disappearStartL hpsi a b).2 = anchorView b := by
    unfold disappearStartL
    split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have hcarry (a b : AgentState psi) :
      anchorView (disappearCarry hpsi a b).1 = anchorView a ∧
        anchorView (disappearCarry hpsi a b).2 = anchorView b := by
    unfold disappearCarry
    split
    · split
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  let q0 := disappearStartR hpsi l.core r.core
  let q1 := disappearStartL hpsi q0.1 q0.2
  have h0 := hstartR l.core r.core
  have h1 := hstartL q0.1 q0.2
  have h2 := hcarry q1.1 q1.2
  exact ⟨h2.1.trans (h1.1.trans h0.1), h2.2.trans (h1.2.trans h0.2)⟩

private theorem disappear_right_path2 (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) (hr : r.core.state ≠ .toss) :
    (authorizedDisappear hpsi l r).2.core.path2 = r.core.path2 := by
  have hstart : disappearStartR hpsi l.core r.core = (l.core, r.core) := by
    simp [disappearStartR, hr]
  have hleft : (disappearStartL hpsi l.core r.core).2 = r.core := by
    unfold disappearStartL
    split
    · split <;> rfl
    · rfl
  have hcarry (a b : AgentState psi) :
      (disappearCarry hpsi a b).2.path2 = b.path2 := by
    unfold disappearCarry
    split
    · split
      · split <;> rfl
      · rfl
    · rfl
  change (disappear hpsi l.core r.core).2.path2 = r.core.path2
  rw [disappear_eq_staged]
  unfold disappearStaged
  rw [hstart]
  exact (hcarry _ _).trans (congrArg AgentState.path2 hleft)

private theorem cmpReturn_anchor (hpsi : psi > 0) (l r : AgentState psi) :
    anchorView (cmpUpdateReturnPriority hpsi l r).1 = anchorView l ∧
      anchorView (cmpUpdateReturnPriority hpsi l r).2 = anchorView r := by
  unfold cmpUpdateReturnPriority
  repeat (first | exact ⟨rfl, rfl⟩ | split)

private theorem cmpSet_anchor (hpsi : psi > 0) (u : AgentState psi) :
    anchorView (cmpUpdateSetPath2 hpsi u) = anchorView u := by
  cases hp : u.path with
  | bot => simp [cmpUpdateSetPath2, hp]
  | some label bit =>
      simp only [cmpUpdateSetPath2, hp]
      split <;> simp [anchorView, hp]

private theorem cmpUpdate_anchor (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    anchorView (authorizedCmpUpdate hpsi l r).1.core = anchorView l.core ∧
      anchorView (authorizedCmpUpdate hpsi l r).2.core = anchorView r.core := by
  let lc := if freshComparisonStart hpsi l && !comparisonActive l.core.state then
    { l.core with state := .congest } else l.core
  have hlc : anchorView lc = anchorView l.core := by
    unfold lc
    split <;> rfl
  have hp := cmpReturn_anchor hpsi lc r.core
  have hs := cmpSet_anchor hpsi (cmpUpdateReturnPriority hpsi lc r.core).1
  exact ⟨hs.trans (hp.1.trans hlc), hp.2⟩

private theorem compareL_anchor (hpsi : psi > 0) (u : AgentState psi) :
    anchorView (compareBitUpdateL hpsi u) = anchorView u := by
  cases hp2 : u.path2 <;> cases hp : u.path <;>
    simp only [compareBitUpdateL, hp2, hp]
  all_goals first | rfl | split <;> simp [anchorView, hp]

private theorem compareR_anchor (hpsi : psi > 0) (u : AgentState psi) :
    anchorView (compareBitUpdateRActionOne hpsi u) = anchorView u := by
  cases hp : u.path2 with
  | none => simp [compareBitUpdateRActionOne, hp]
  | some p2 =>
      simp only [compareBitUpdateRActionOne, hp]
      repeat (first | rfl | split)

private theorem dispatchActionOne_anchor (hpsi : psi > 0) (l r : AgentState psi) :
    anchorView (compareSigDispatchActionOne hpsi l r).1 = anchorView l ∧
      anchorView (compareSigDispatchActionOne hpsi l r).2 = anchorView r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [compareSigDispatchActionOne, hl, hr, compareBitActionOne]
  · exact ⟨True.intro, True.intro⟩
  all_goals exact ⟨compareL_anchor hpsi l, compareR_anchor hpsi r⟩

private theorem compareActionOne_anchor (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    anchorView (authorizedCompareSigActionOne hpsi l r).1.core = anchorView l.core ∧
      anchorView (authorizedCompareSigActionOne hpsi l r).2.core = anchorView r.core := by
  have hinit : anchorView (compareSigInit l.core) = anchorView l.core := by
    unfold compareSigInit
    split <;> rfl
  let l0 : AuthorizedAgentState psi :=
    ⟨compareSigInit l.core, normalizePermit (compareSigInit l.core) l.path0Crossed⟩
  have hu := cmpUpdate_anchor hpsi l0 r
  have hd := dispatchActionOne_anchor hpsi
    (authorizedCmpUpdate hpsi l0 r).1.core (authorizedCmpUpdate hpsi l0 r).2.core
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact ⟨hinit, rfl⟩
  · split
    · exact ⟨hinit, rfl⟩
    · exact ⟨hd.1.trans (hu.1.trans hinit), hd.2.trans hu.2⟩

private theorem cmpUpdate_right_path2 (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    (authorizedCmpUpdate hpsi l r).2.core.path2 = r.core.path2 := by
  have hraw (a b : AgentState psi) : (cmpUpdateReturnPriority hpsi a b).2.path2 = b.path2 := by
    unfold cmpUpdateReturnPriority
    repeat (first | rfl | split)
  exact hraw _ r.core

private theorem dispatchActionOne_right_result (hpsi : psi > 0)
    (l r : AgentState psi) (p2 : Path2Info)
    (hp : r.path2 = some p2) (ha : p2.action = 4 ∨ p2.action = 6) :
    (compareSigDispatchActionOne hpsi l r).2 = r := by
  cases hl : l.path2 <;>
    simp only [compareSigDispatchActionOne, hl, hp, compareBitActionOne]
  all_goals exact compareBitUpdateRActionOne_preserves_check_result hpsi r hp ha

/-- The actual action-one authorized COMPARE preserves a right-hand CHECK
result, including the intervening CMP_UPDATE and dispatch conditions. -/
theorem compareActionOne_preserves_right_result (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) (p2 : Path2Info)
    (hp : r.core.path2 = some p2) (ha : p2.action = 4 ∨ p2.action = 6) :
    (authorizedCompareSigActionOne hpsi l r).2.core.path2 = some p2 := by
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact hp
  · split
    · exact hp
    · rw [dispatchActionOne_right_result hpsi _ _ p2
        ((cmpUpdate_right_path2 hpsi _ r).trans hp) ha]
      exact (cmpUpdate_right_path2 hpsi _ r).trans hp

private theorem suppress_no_reset_comparison (hpsi : psi > 0)
    (l r : AgentState psi) (hlleader : l.leader = false)
    (hlreset : l.reset_cmd = false) (hrreset : r.reset_cmd = false) :
    comparisonTrackedPair (suppressSigResetKill hpsi l r) =
      comparisonTrackedPair (l, r) := by
  unfold suppressSigResetKill suppressSigStart
  simp only [hlleader, Bool.false_eq_true, ↓reduceIte]
  unfold resetKillComparison suppressSigMoveReset
  simp only [hlreset, hrreset, Bool.false_eq_true, ↓reduceIte]
  unfold suppressSigTerminal
  simp only [hrreset, Bool.false_eq_true, and_false, ↓reduceIte]
  unfold suppressSigEcho suppressSigFinish comparisonTrackedPair ComparisonTrackedView.ofState
  repeat (first | rfl | split)

attribute [local irreducible] eliminateLeadersNoCollisionLeaderSink
  writeSeqIncrementGate authorizedPostSuppressLeaderSink

private theorem postSuppress_comparison (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    authorizedComparisonTrackedPair (authorizedPostSuppressLeaderSink hpsi l r) =
      authorizedComparisonTrackedPair (l, r) := by
  unfold authorizedPostSuppressLeaderSink
  let q := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
  have hq := eliminateLeadersNoCollisionLeaderSink_comparisonTracked_frame
    hpsi l.core r.core
  have hw := writeSeqIncrementGate_comparisonTracked_pair hpsi q.1 q.2
  exact hw.trans (Prod.ext hq.1 hq.2)

attribute [local semireducible] actionOneAfterCheckSuffix

/-- A fresh right-hand CHECK command survives DISAPPEAR, action-one COMPARE,
reset suppression, the leader sink, and gated WRITE.  The hypotheses are
current physical reset/leader fields and the actual result command.  No
writer-neutrality or future preservation hypothesis is needed. -/
theorem actionOne_suffix_preserves_right_result
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) (p2 : Path2Info)
    (hp : r.core.path2 = some p2) (ha : p2.action = 4 ∨ p2.action = 6)
    (hrstate : r.core.state ≠ .toss) (hlleader : l.core.leader = false)
    (hlreset : l.core.reset_cmd = false) (hrreset : r.core.reset_cmd = false) :
    let q := actionOneAfterCheckSuffix hpsi l r
    q.2.core.path = r.core.path ∧ q.2.core.path2 = some p2 ∧
      q.2.core.label = r.core.label := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedPostSuppressLeaderSink hpsi q2.1 q2.2
  have hv0 := disappear_anchor hpsi l r
  have hv1 := compareActionOne_anchor hpsi q0.1 q0.2
  have hlv := hv1.1.trans hv0.1
  have hrv := hv1.2.trans hv0.2
  have hlleader1 : q1.1.core.leader = false :=
    (congrArg Prod.fst hlv).trans hlleader
  have hlreset1 : q1.1.core.reset_cmd = false :=
    (congrArg (fun x : Bool × Bool × Fin psi × PathInfo => x.2.1) hlv).trans hlreset
  have hrreset1 : q1.2.core.reset_cmd = false :=
    (congrArg (fun x : Bool × Bool × Fin psi × PathInfo => x.2.1) hrv).trans hrreset
  have hrpath1 : q1.2.core.path = r.core.path :=
    congrArg (fun x : Bool × Bool × Fin psi × PathInfo => x.2.2.2) hrv
  have hrlabel1 : q1.2.core.label = r.core.label :=
    congrArg (fun x : Bool × Bool × Fin psi × PathInfo => x.2.2.1) hrv
  have hrp20 : q0.2.core.path2 = some p2 :=
    (disappear_right_path2 hpsi l r hrstate).trans hp
  have hrp21 := compareActionOne_preserves_right_result hpsi q0.1 q0.2 p2 hrp20 ha
  have hs := suppress_no_reset_comparison hpsi q1.1.core q1.2.core
    hlleader1 hlreset1 hrreset1
  have hsright : ComparisonTrackedView.ofState q2.2.core =
      ComparisonTrackedView.ofState q1.2.core := congrArg Prod.snd hs
  have hw := postSuppress_comparison hpsi q2.1 q2.2
  have hwright : ComparisonTrackedView.ofState q3.2.core =
      ComparisonTrackedView.ofState q2.2.core := congrArg Prod.snd hw
  have hright := hwright.trans hsright
  have hpath := (congrArg ComparisonTrackedView.path hright).trans hrpath1
  have hp2 := (congrArg ComparisonTrackedView.path2 hright).trans hrp21
  have hlabel := (authorizedPostSuppressLeaderSink_labels_eq hpsi q2.1 q2.2).2.trans
    ((suppressSigResetKill_right_label_eq hpsi q1.1.core q1.2.core).trans hrlabel1)
  exact ⟨hpath, hp2, hlabel⟩

/-- Exact normalized prepared input of the existing deletion-priority host. -/
def preparedInput (hpsi : psi > 0) (u : AuthorizedAgentState psi) :
    AuthorizedAgentState psi := normalizeDeletion (prepareDisposal hpsi u)

/-- The actual sanitized boundary immediately before CHECK in the new host.
It is computed from the current pair by the retained source prefix. -/
def actualCheckInput (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa
    (preparedInput hpsi l) (preparedInput hpsi r)

/-- The actual guarded CHECK result on that computed boundary. -/
def actualCheckOutput (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := actualCheckInput hpsi kappa l r
  congestGuardCheck hpsi q.1 q.2

private theorem mark_right_fields (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (markLeaderBirth born q).2.core.path = q.2.core.path ∧
      (markLeaderBirth born q).2.core.path2 = q.2.core.path2 ∧
      (markLeaderBirth born q).2.core.label = q.2.core.label := by
  unfold markLeaderBirth
  split
  · change (markComparisonForDeletion q.2).core.path = q.2.core.path ∧
      (markComparisonForDeletion q.2).core.path2 = q.2.core.path2 ∧
      (markComparisonForDeletion q.2).core.label = q.2.core.label
    unfold markComparisonForDeletion
    split <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

attribute [local irreducible] actionOneAfterCheckSuffix actualCheckInput actualCheckOutput

/-- A directional CHECK command survives the entire authorized interaction,
including the actual suffix and final birth marking.  The CHECK boundary is
computed from this same input pair, and only its current field facts appear
as hypotheses. -/
theorem actual_checked_command_survives_authorized
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (p2 : Path2Info)
    (hlinactive : deletionActive (preparedInput hpsi l) = false)
    (hrinactive : deletionActive (preparedInput hpsi r) = false)
    (hp : (actualCheckOutput hpsi kappa l r).2.core.path2 = some p2)
    (ha : p2.action = 4 ∨ p2.action = 6)
    (hrstate : (actualCheckOutput hpsi kappa l r).2.core.state ≠ .toss)
    (hlleader : (actualCheckOutput hpsi kappa l r).1.core.leader = false)
    (hlreset : (actualCheckOutput hpsi kappa l r).1.core.reset_cmd = false)
    (hrreset : (actualCheckOutput hpsi kappa l r).2.core.reset_cmd = false) :
    let q := actionOneDisposalAuthorizedTransition hpsi kappa l r
    q.2.core.path = (actualCheckOutput hpsi kappa l r).2.core.path ∧
      q.2.core.path2 = some p2 ∧
      q.2.core.label = (actualCheckOutput hpsi kappa l r).2.core.label := by
  let c := actualCheckOutput hpsi kappa l r
  have hs := actionOne_suffix_preserves_right_result hpsi c.1 c.2 p2 hp ha
    hrstate hlleader hlreset hrreset
  let before := actualCheckInput hpsi kappa l r
  let born := leaderBirthBeforeOrAtCheck (preparedInput hpsi l)
    (preparedInput hpsi r) before c
  have hm := mark_right_fields born (actionOneAfterCheckSuffix hpsi c.1 c.2)
  have he : actionOneDisposalAuthorizedTransition hpsi kappa l r =
      markLeaderBirth born (actionOneAfterCheckSuffix hpsi c.1 c.2) := by
    unfold actionOneDisposalAuthorizedTransition actionOneGuardedAuthorizedTransition
    change (if deletionActive (preparedInput hpsi r) then _ else
      if deletionActive (preparedInput hpsi l) then _ else _) = _
    simp only [hrinactive, hlinactive, Bool.false_eq_true, ↓reduceIte]
    unfold born c before actualCheckOutput actualCheckInput preparedInput
    rfl
  rw [he]
  exact ⟨hm.1.trans hs.1, hm.2.1.trans hs.2.1, hm.2.2.trans hs.2.2⟩

private theorem expiry_core_or_lost (old out : ExpiringAgentState psi kappa tau) :
    (deletionPriorityExpireOne tau old out).core = out.core ∨
      (deletionPriorityExpireOne tau old out).core.erase.core.path = .bot := by
  unfold deletionPriorityExpireOne PPLLPathStallComparisonRepair.pathExpireOne
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl

private theorem signal_right_fields (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau) :
    (initializeFollowerPairBirthSignals l r q).2.core.erase.core.path =
        q.2.core.erase.core.path ∧
      (initializeFollowerPairBirthSignals l r q).2.core.erase.core.path2 =
        q.2.core.erase.core.path2 ∧
      (initializeFollowerPairBirthSignals l r q).2.core.erase.core.label =
        q.2.core.erase.core.label := by
  unfold initializeFollowerPairBirthSignals
  split
  · change (clearExpiringLeaderSignal q.2).core.erase.core.path = q.2.core.erase.core.path ∧
      (clearExpiringLeaderSignal q.2).core.erase.core.path2 = q.2.core.erase.core.path2 ∧
      (clearExpiringLeaderSignal q.2).core.erase.core.label = q.2.core.erase.core.label
    unfold clearExpiringLeaderSignal
    split <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

attribute [local irreducible] actionOneGuardedBoundedTransition

/-- The actual complete finite successor retains the checked directional
command with the same right payload and label, or expiry has removed that
payload.  This holds for every timer bound and every initial timer value. -/
theorem actual_checked_command_full_or_lost
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (p2 : Path2Info)
    (hlinactive : deletionActive (preparedInput hpsi l.core.erase) = false)
    (hrinactive : deletionActive (preparedInput hpsi r.core.erase) = false)
    (hp : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.path2 = some p2)
    (ha : p2.action = 4 ∨ p2.action = 6)
    (hrstate : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.state ≠ .toss)
    (hlleader : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).1.core.leader = false)
    (hlreset : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).1.core.reset_cmd = false)
    (hrreset : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.reset_cmd = false) :
    let q := actionOneFullTransition hpsi kappa tau l r
    (q.2.core.erase.core.path =
        (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.path ∧
      q.2.core.erase.core.path2 = some p2 ∧
      q.2.core.erase.core.label =
        (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.label) ∨
      q.2.core.erase.core.path = .bot := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := actionOneGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  have hf := actual_checked_command_survives_authorized hpsi kappa l.core.erase r.core.erase
    p2 hlinactive hrinactive hp ha hrstate hlleader hlreset hrreset
  rw [← erase_actionOne_disposal_base hpsi kappa l.core r.core] at hf
  have hs := signal_right_fields l0 r0
    (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)
  rcases expiry_core_or_lost r0 rOut with he | he
  · have hp' := hs.1
    have hp2' := hs.2.1
    have hl' := hs.2.2
    rw [he] at hp' hp2' hl'
    exact Or.inl ⟨hp'.trans hf.1, hp2'.trans hf.2.1, hl'.trans hf.2.2⟩
  · exact Or.inr (hs.1.trans he)

/-- Positive current right-end credit rules out the expiry alternative in
the preceding complete-host theorem; no lower bound on the global timer
parameter is silently supplied. -/
theorem actual_checked_command_full_of_positive
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) (p2 : Path2Info)
    (hlinactive : deletionActive (preparedInput hpsi l.core.erase) = false)
    (hrinactive : deletionActive (preparedInput hpsi r.core.erase) = false)
    (hp : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.path2 = some p2)
    (ha : p2.action = 4 ∨ p2.action = 6)
    (hrstate : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.state ≠ .toss)
    (hlleader : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).1.core.leader = false)
    (hlreset : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).1.core.reset_cmd = false)
    (hrreset : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.reset_cmd = false)
    (hpositive : 0 < r.stall.val) :
    let q := actionOneFullTransition hpsi kappa tau l r
    q.2.core.erase.core.path =
        (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.path ∧
      q.2.core.erase.core.path2 = some p2 ∧
      q.2.core.erase.core.label =
        (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.label := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := actionOneGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  have hf := actual_checked_command_survives_authorized hpsi kappa l.core.erase r.core.erase
    p2 hlinactive hrinactive hp ha hrstate hlleader hlreset hrreset
  rw [← erase_actionOne_disposal_base hpsi kappa l.core r.core] at hf
  have hs := signal_right_fields l0 r0
    (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)
  have he := BirthCheckParametricWait.expiry_core_of_positive r0 rOut hpositive
  have hp' := hs.1
  have hp2' := hs.2.1
  have hl' := hs.2.2
  rw [he] at hp' hp2' hl'
  exact ⟨hp'.trans hf.1, hp2'.trans hf.2.1, hl'.trans hf.2.2⟩

private theorem ready_anchor (u : AgentState psi) :
    anchorView (checkSigSetReady u) = anchorView u := by
  cases hp : u.path with
  | bot => simp [checkSigSetReady, hp]
  | some label bit =>
      simp only [checkSigSetReady, hp]
      split <;> simp [anchorView, hp]

private theorem checkL_anchor (hpsi : psi > 0) (u : AgentState psi) :
    anchorView (checkSigCheckL hpsi u) = anchorView u := by
  cases hp : u.path with
  | bot => simp [checkSigCheckL, hp]
  | some label bit =>
      cases label with
      | zero =>
          simp only [checkSigCheckL, hp]
          split <;> simp [anchorView, hp]
      | succ label => simp [checkSigCheckL, hp]

private theorem setReady_of_ready (u : AgentState psi) (hs : u.state = .CHECK_ready) :
    checkSigSetReady u = u := by
  have hu : { u with state := MainState.CHECK_ready } = u := by
    cases u
    cases hs
    rfl
  unfold checkSigSetReady
  split
  · split
    · exact hu
    · rfl
  · rfl

/-- A real ready responder with resident bit one and payload bit zero is
checked as larger when the current left CHECK prefix is equal.  The prefix
condition is executable on this input agent and covers both a retained equal
prefix and the same-call label-zero comparison. -/
theorem guarded_check_right_larger (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hlclear : l.core.state ≠ .congest)
    (hlprefix : (checkSigCheckL hpsi (checkSigSetReady l.core)).state = .equal)
    (hllabel : l.core.label.val < psi - 1)
    (hrstate : r.core.state = .CHECK_ready)
    (hrpath : r.core.path = .some r.core.label.val 0)
    (hrbit : r.core.bit = true) :
    let q := congestGuardCheck hpsi l r
    anchorView q.1.core = anchorView l.core ∧
      q.2.core = { r.core with state := .larger, path2 := some ⟨0, 0, 0, 4⟩ } := by
  let lc := checkSigCheckL hpsi (checkSigSetReady l.core)
  have hv := (checkL_anchor hpsi (checkSigSetReady l.core)).trans (ready_anchor l.core)
  have hlc : lc.label.val < psi - 1 := by
    have he := congrArg (fun x : Bool × Bool × Fin psi × PathInfo => x.2.2.1) hv
    change lc.label = l.core.label at he
    simpa only [he] using hllabel
  have hlresult : checkSigSetResult lc = lc := by
    simp [checkSigSetResult, show lc.state = .equal from hlprefix]
  have hrcheck : checkSigCheckR hpsi lc r.core = { r.core with state := .larger } := by
    simp [checkSigCheckR, hrpath, hlc, show lc.state = .equal from hlprefix,
      hrstate, checkBit, hrbit]
  unfold congestGuardCheck
  rw [if_neg (by simp [hlclear, hrstate])]
  change anchorView (checkSig hpsi l.core r.core).1 = anchorView l.core ∧
    (checkSig hpsi l.core r.core).2 = _
  rw [checkSig_eq_staged]
  unfold checkSigStaged
  rw [setReady_of_ready r.core hrstate]
  change anchorView (checkSigSetResult lc) = anchorView l.core ∧
    checkSigSetLeader hpsi (checkSigSetResult (checkSigCheckR hpsi lc r.core)) = _
  rw [hlresult, hrcheck]
  exact ⟨hv, by simp [checkSigSetResult, checkSigSetLeader]⟩

/-- General actual-input producer: the unchanged physical prefix presents
a ready larger mismatch to CHECK, and the complete repaired successor keeps
action four attached to that component or removes the component by expiry.
In particular, the statement includes COMPARE, reset, WRITE, finite
reification, both endpoint expiries, and birth-signal initialization. -/
theorem actual_ready_larger_full_or_lost
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (hlinactive : deletionActive (preparedInput hpsi l.core.erase) = false)
    (hrinactive : deletionActive (preparedInput hpsi r.core.erase) = false)
    (hlclear : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.state ≠ .congest)
    (hlprefix : (checkSigCheckL hpsi (checkSigSetReady
      (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core)).state = .equal)
    (hllabel : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.label.val < psi - 1)
    (hrstate : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.state = .CHECK_ready)
    (hrpath : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.path =
      .some (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label.val 0)
    (hrbit : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.bit = true)
    (hlleader : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.leader = false)
    (hlreset : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.reset_cmd = false)
    (hrreset : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.reset_cmd = false) :
    let q := actionOneFullTransition hpsi kappa tau l r
    (q.2.core.erase.core.path =
        (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.path ∧
      q.2.core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      q.2.core.erase.core.label =
        (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label) ∨
      q.2.core.erase.core.path = .bot := by
  let b := actualCheckInput hpsi kappa l.core.erase r.core.erase
  have hc := guarded_check_right_larger hpsi b.1 b.2 hlclear hlprefix hllabel
    hrstate hrpath hrbit
  have hfields :
      anchorView (actualCheckOutput hpsi kappa l.core.erase r.core.erase).1.core =
        anchorView b.1.core ∧
      (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core =
        { b.2.core with state := .larger, path2 := some ⟨0, 0, 0, 4⟩ } := by
    simpa only [actualCheckOutput, b] using hc
  have hp : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.path2 =
      some ⟨0, 0, 0, 4⟩ := by rw [hfields.2]
  have hs : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.state ≠ .toss := by
    rw [hfields.2]
    change MainState.larger ≠ .toss
    decide
  have hl := (congrArg Prod.fst hfields.1).trans hlleader
  have hlr := (congrArg (fun x : Bool × Bool × Fin psi × PathInfo => x.2.1)
    hfields.1).trans hlreset
  have hrr : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.reset_cmd =
      false := by rw [hfields.2]; exact hrreset
  have h := actual_checked_command_full_or_lost hpsi kappa tau l r
    ⟨0, 0, 0, 4⟩ hlinactive hrinactive hp (Or.inl rfl) hs hl hlr hrr
  simpa only [hfields.2] using h

/-- The ready terminal mismatch produces the exact `DisposalDue` entry used
by the checked deletion route.  Every hypothesis concerns current input or
its actual pre-CHECK computation; the positive stall is a current finite
register fact.  No post-CHECK or future route premise is assumed. -/
theorem actual_ready_terminal_larger_produces_disposal
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (hlinactive : deletionActive (preparedInput hpsi l.core.erase) = false)
    (hrinactive : deletionActive (preparedInput hpsi r.core.erase) = false)
    (hlclear : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.state ≠ .congest)
    (hlprefix : (checkSigCheckL hpsi (checkSigSetReady
      (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core)).state = .equal)
    (hllabel : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.label.val < psi - 1)
    (hrstate : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.state = .CHECK_ready)
    (hrpath : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.path =
      .some (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label.val 0)
    (hrbit : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.bit = true)
    (hlleader : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.leader = false)
    (hlreset : (actualCheckInput hpsi kappa l.core.erase r.core.erase).1.core.reset_cmd = false)
    (hrreset : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.reset_cmd = false)
    (hrterminal : (actualCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label =
      ⟨psi - 1, by omega⟩)
    (hpositive : 0 < r.stall.val) :
    DisposalDue hpsi (actionOneFullTransition hpsi kappa tau l r).2.core.erase := by
  let b := actualCheckInput hpsi kappa l.core.erase r.core.erase
  have hc := guarded_check_right_larger hpsi b.1 b.2 hlclear hlprefix hllabel
    hrstate hrpath hrbit
  have hfields :
      anchorView (actualCheckOutput hpsi kappa l.core.erase r.core.erase).1.core =
        anchorView b.1.core ∧
      (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core =
        { b.2.core with state := .larger, path2 := some ⟨0, 0, 0, 4⟩ } := by
    simpa only [actualCheckOutput, b] using hc
  have hp : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.path2 =
      some ⟨0, 0, 0, 4⟩ := by rw [hfields.2]
  have hs : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.state ≠ .toss := by
    rw [hfields.2]
    change MainState.larger ≠ .toss
    decide
  have hl := (congrArg Prod.fst hfields.1).trans hlleader
  have hlr := (congrArg (fun x : Bool × Bool × Fin psi × PathInfo => x.2.1)
    hfields.1).trans hlreset
  have hrr : (actualCheckOutput hpsi kappa l.core.erase r.core.erase).2.core.reset_cmd =
      false := by rw [hfields.2]; exact hrreset
  have h := actual_checked_command_full_of_positive hpsi kappa tau l r
    ⟨0, 0, 0, 4⟩ hlinactive hrinactive hp (Or.inl rfl) hs hl hlr hrr hpositive
  have hpath : (actionOneFullTransition hpsi kappa tau l r).2.core.erase.core.path =
      .some b.2.core.label.val 0 := by
    rw [h.1, hfields.2]
    exact hrpath
  have hlabel : (actionOneFullTransition hpsi kappa tau l r).2.core.erase.core.label =
      ⟨psi - 1, by omega⟩ := by
    rw [h.2.2, hfields.2]
    exact hrterminal
  refine ⟨?_, Or.inr ?_⟩
  · rw [hpath]
    intro he
    cases he
  · simp only [pendingTerminalDisposal, h.2.1, hlabel]
    decide

/-- An existing disposal remains active after the exact preparatory and
orphan-normalization operations, independently of all other fields. -/
theorem prepared_due_active (hpsi : psi > 0) (u : AuthorizedAgentState psi)
    (hu : DisposalDue hpsi u) : deletionActive (preparedInput hpsi u) = true := by
  have hp : (prepareDisposal hpsi u).core.path ≠ .bot := by
    simpa only [prepareDisposal_path] using hu.1
  have hs : (prepareDisposal hpsi u).core.state = .eliminate_signal := by
    rcases hu.2 with hs | hc
    · by_cases hc : pendingTerminalDisposal hpsi u.core = true
      · exact (prepareDisposal_pending hpsi u hc hu.1).1
      · simpa only [prepareDisposal, hc, Bool.false_eq_true, ↓reduceIte] using hs
    · exact (prepareDisposal_pending hpsi u hc hu.1).1
  unfold preparedInput
  rw [normalizeDeletion_eq_of_path_present _ hp]
  exact deletionActive_eq_true _ hs hp

private theorem guarded_eq_of_active (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (ha : deletionActive (normalizeDeletion l) = true ∨
      deletionActive (normalizeDeletion r) = true) :
    actionOneGuardedAuthorizedTransition hpsi kappa l r =
      guardedAuthorizedTransition hpsi kappa l r := by
  unfold actionOneGuardedAuthorizedTransition guardedAuthorizedTransition
  dsimp only
  by_cases hr : deletionActive (normalizeDeletion r) = true
  · simp only [hr, ↓reduceIte]
  · have hl : deletionActive (normalizeDeletion l) = true := ha.resolve_right hr
    simp only [hr, hl, ↓reduceIte]

attribute [local irreducible] guardedBoundedTransition

/-- The new complete host is exactly the frozen disposal host on every pair
already carrying disposal.  Thus the action-one integration preserves the
established pinning and predecessor-deletion rows, including timer behavior. -/
theorem actionOneFull_eq_disposalFull_of_due
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (ha : DisposalDue hpsi l.core.erase ∨ DisposalDue hpsi r.core.erase) :
    actionOneFullTransition hpsi kappa tau l r =
      disposalFullTransition hpsi kappa tau l r := by
  have hactive : deletionActive (preparedInput hpsi l.core.erase) = true ∨
      deletionActive (preparedInput hpsi r.core.erase) = true :=
    ha.imp (prepared_due_active hpsi l.core.erase) (prepared_due_active hpsi r.core.erase)
  have hr : actionOneGuardedAuthorizedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core).erase
      (prepareBoundedDisposal hpsi r.core).erase =
      guardedAuthorizedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core).erase
        (prepareBoundedDisposal hpsi r.core).erase := by
    rw [erase_prepareBoundedDisposal, erase_prepareBoundedDisposal]
    exact guarded_eq_of_active hpsi kappa _ _ hactive
  have hb : actionOneGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) =
      guardedBoundedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) := by
    unfold actionOneGuardedBoundedTransition guardedBoundedTransition
    dsimp only
    simp only [hr]
  unfold actionOneFullTransition disposalFullTransition guardedFullTransition
    guardedPathStallTransition
  dsimp only [prepareExpiringDisposal]
  rw [hb]

end BirthMismatchDisposalProducer

#print axioms BirthMismatchDisposalProducer.raw_compare_reverses_larger
#print axioms BirthMismatchDisposalProducer.actionOneDisposalAuthorizedTransition_inProtocolDomain
#print axioms BirthMismatchDisposalProducer.erase_actionOneGuardedBoundedTransition
#print axioms BirthMismatchDisposalProducer.erase_actionOne_disposal_base
#print axioms BirthMismatchDisposalProducer.compareActionOne_preserves_right_result
#print axioms BirthMismatchDisposalProducer.actionOne_suffix_preserves_right_result
#print axioms BirthMismatchDisposalProducer.actual_checked_command_full_or_lost
#print axioms BirthMismatchDisposalProducer.actual_checked_command_full_of_positive
#print axioms BirthMismatchDisposalProducer.guarded_check_right_larger
#print axioms BirthMismatchDisposalProducer.actual_ready_larger_full_or_lost
#print axioms BirthMismatchDisposalProducer.actual_ready_terminal_larger_produces_disposal
#print axioms BirthMismatchDisposalProducer.actionOneFull_eq_disposalFull_of_due

namespace BirthMismatchDisposalProducer


open PPLL PPLLAuthorizedComparisonRepair
  PPLLCompleteMultiLeaderCleanup


variable {psi : Nat}


/-- Public export of the existing proof projection for action-one COMPARE. -/
theorem compareActionOne_anchor_public (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    anchorView (authorizedCompareSigActionOne hpsi l r).1.core =
        anchorView l.core ∧
      anchorView (authorizedCompareSigActionOne hpsi l r).2.core =
        anchorView r.core := by
  exact compareActionOne_anchor hpsi l r


end BirthMismatchDisposalProducer

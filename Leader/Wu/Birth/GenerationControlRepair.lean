import Leader.Wu.Birth.SourceActionFiveCounterexample

set_option autoImplicit false

namespace BirthGenerationControlRepair

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepNormalResetContract
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair
  BirthDisposalRouteInvariant BirthMismatchDisposalProducer BirthArrivalCaptureRepair

variable {psi kappa tau : Nat}

/-! Every actual GENSIG payload writer starts a new comparison component.
It must therefore clear that endpoint's previous path2 control at the same
write.  The two changes below cover terminal emission and backward generation.
They do not clear controls during WAIT, ordinary transport, or DISAPPEAR.

The event predicates are computed from the current pair at the actual source
cuts.  They are proof observables, not added protocol fields.  The separately
named complete host retains the current capture, disposal, expiry, CHECK and
action-one COMPARE stages on the existing finite carrier. -/

/-- The terminal payload writer also discards the replaced episode's control. -/
def genCleanEmit (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let r :=
    if r.label = ⟨psi - 1, by omega⟩ ∧ r.state = .produce then
      { r with
        state := .done
        path := .some r.label.val (if r.bit then 1 else 0)
        path2 := none }
    else r
  (l, r)

/-- The backward payload writer clears only the newly written endpoint. -/
def genCleanPropagate (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  if l.label ≠ ⟨psi - 1, by omega⟩ ∧ l.state = .produce ∧ r.state = .done then
    ({ l with
       state := .done
       path := .some l.label.val (if l.bit then 1 else 0)
       path2 := none },
     { r with state := .depart })
  else (l, r)

/-- The unchanged source initialization and finish surround the two writers. -/
def genCleanAfterWait (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let q := genSigSaturatedStart hpsi l r
  let q := genCleanEmit hpsi q.1 q.2
  let q := genCleanPropagate hpsi q.1 q.2
  genSigSaturatedFinish hpsi q.1 q.2

def genClean (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let q := waitSaturated hpsi kappa l r
  genCleanAfterWait hpsi q.1 q.2

/-- A proof projection that replaces precisely path2 when its writer fires. -/
def resetControlOn (fires : Bool) (u : AgentState psi) : AgentState psi :=
  if fires then { u with path2 := none } else u

/-- Current source-writer predicates after production-state initialization;
the first component records backward generation and the second emission. -/
def writesAfterStart (hpsi : psi > 0) (l r : AgentState psi) : Bool × Bool :=
  let emitted := genSigSaturatedEmit hpsi l r
  (decide (l.label ≠ ⟨psi - 1, by omega⟩ ∧ l.state = .produce ∧
      emitted.2.state = .done),
   decide (r.label = ⟨psi - 1, by omega⟩ ∧ r.state = .produce))

/-- The two actual source events, computed solely from the current input
through WAIT and source initialization. -/
def generationWrites (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    Bool × Bool :=
  let w := waitSaturated hpsi kappa l r
  let s := genSigSaturatedStart hpsi w.1 w.2
  writesAfterStart hpsi s.1 s.2

private theorem genClean_tail_exact (hpsi : psi > 0) (l r : AgentState psi) :
    let n2 := genCleanEmit hpsi l r
    let n3 := genCleanPropagate hpsi n2.1 n2.2
    let old2 := genSigSaturatedEmit hpsi l r
    let old3 := genSigSaturatedPropagate hpsi old2.1 old2.2
    let old := genSigSaturatedFinish hpsi old3.1 old3.2
    let writes := writesAfterStart hpsi l r
    genSigSaturatedFinish hpsi n3.1 n3.2 =
      (resetControlOn writes.1 old.1, resetControlOn writes.2 old.2) := by
  by_cases heLabel : r.label = ⟨psi - 1, by omega⟩
  all_goals by_cases heState : r.state = .produce
  all_goals by_cases hpLabel : l.label = ⟨psi - 1, by omega⟩
  all_goals by_cases hpState : l.state = .produce
  all_goals by_cases hr : r.state = .done
  all_goals by_cases hz : l.label = ⟨0, hpsi⟩
  all_goals by_cases hl : l.state = .done
  all_goals simp_all [genCleanEmit, genCleanPropagate, genSigSaturatedEmit,
    genSigSaturatedPropagate, genSigSaturatedFinish, writesAfterStart, resetControlOn]

/-- Exact whole-GENSIG comparison with the previous source: every field
agrees, except path2 is empty exactly at an actual payload-writing endpoint. -/
theorem genClean_exact (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    let old := genSigSaturated hpsi kappa l r
    let writes := generationWrites hpsi kappa l r
    genClean hpsi kappa l r =
      (resetControlOn writes.1 old.1, resetControlOn writes.2 old.2) := by
  unfold genClean genCleanAfterWait genSigSaturated genSigSaturatedAfterWait generationWrites
  exact genClean_tail_exact hpsi _ _

/-- Both newly generated endpoints have empty control at the actual GENSIG
output.  No future route or membership invariant is a hypothesis. -/
theorem genClean_written_control_empty (hpsi : psi > 0) (kappa : Nat)
    (l r : AgentState psi) :
    ((generationWrites hpsi kappa l r).1 = true →
      (genClean hpsi kappa l r).1.path2 = none) ∧
    ((generationWrites hpsi kappa l r).2 = true →
      (genClean hpsi kappa l r).2.path2 = none) := by
  rw [genClean_exact]
  constructor <;> intro h <;> simp [resetControlOn, h]

/-- A call with no actual payload writer preserves every old GENSIG field,
including a genuine release token emitted by an earlier DISAPPEAR event. -/
theorem genClean_eq_of_no_write (hpsi : psi > 0) (kappa : Nat)
    (l r : AgentState psi)
    (hl : (generationWrites hpsi kappa l r).1 = false)
    (hr : (generationWrites hpsi kappa l r).2 = false) :
    genClean hpsi kappa l r = genSigSaturated hpsi kappa l r := by
  rw [genClean_exact]
  simp [resetControlOn, hl, hr]

private theorem resetControlOn_inProtocolDomain (fires : Bool) (u : AgentState psi)
    (hu : u.inProtocolDomain kappa) :
    (resetControlOn fires u).inProtocolDomain kappa := by
  cases fires
  · exact hu
  · rw [inProtocolDomain_iff_path2_frame]
    exact ⟨True.intro, ((inProtocolDomain_iff_path2_frame u).1 hu).2⟩

/-- Clearing a control introduces no state-range enlargement, for arbitrary
positive psi and every kappa. -/
theorem genClean_inProtocolDomain (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := genClean hpsi kappa l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have h := genSigSaturated_inProtocolDomain hpsi l r hl hr
  rw [genClean_exact]
  exact ⟨resetControlOn_inProtocolDomain _ _ h.1,
    resetControlOn_inProtocolDomain _ _ h.2⟩

/-- Each terminal writer has the original payload, the original done state,
and no old control; the non-writing initiator is exactly unchanged. -/
theorem genCleanEmit_writer (hpsi : psi > 0) (l r : AgentState psi)
    (hl : r.label = ⟨psi - 1, by omega⟩) (hs : r.state = .produce) :
    genCleanEmit hpsi l r =
      (l, { r with
        state := .done
        path := .some r.label.val (if r.bit then 1 else 0)
        path2 := none }) := by
  simp [genCleanEmit, hl, hs]

/-- The nonterminal writer clears its own old control while retaining the
already generated responder's control exactly. -/
theorem genCleanPropagate_writer (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.label ≠ ⟨psi - 1, by omega⟩) (hs : l.state = .produce)
    (hr : r.state = .done) :
    genCleanPropagate hpsi l r =
      ({ l with
        state := .done
        path := .some l.label.val (if l.bit then 1 else 0)
        path2 := none },
       { r with state := .depart }) := by
  simp [genCleanPropagate, hl, hs, hr]

/-! The complete finite host changes only the GENSIG writer used in the
ordinary prefix.  Entry deletion still preempts that prefix completely. -/

def authorizedGenClean (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  authorizedReconcile (genClean hpsi kappa) l r

/-- The actual authorized source cut has empty control at either endpoint
whose current GENSIG writer fires. -/
theorem authorizedGenClean_written_control_empty (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    ((generationWrites hpsi kappa l.core r.core).1 = true →
      (authorizedGenClean hpsi kappa l r).1.core.path2 = none) ∧
    ((generationWrites hpsi kappa l.core r.core).2 = true →
      (authorizedGenClean hpsi kappa l r).2.core.path2 = none) :=
  genClean_written_control_empty hpsi kappa l.core r.core

def generationBeforeMove (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenClean hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  authorizedEliminateSig hpsi q2.1 q2.2

theorem generationBeforeMove_inProtocolDomain (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := generationBeforeMove hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  have h0 := authorizedPPsiLeaderResetProbeWall_inProtocolDomain hpsi l r hl hr
  let q1 := authorizedGenClean hpsi kappa q0.1 q0.2
  have h1 := authorizedReconcile_inProtocolDomain (genClean hpsi kappa) q0.1 q0.2
    (genClean_inProtocolDomain hpsi q0.1.core q0.2.core h0.1 h0.2)
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain (cleanSig hpsi) q1.1 q1.2
    (cleanSig_inProtocolDomain hpsi q1.1.core q1.2.core h1.1 h1.2)
  exact authorizedReconcile_inProtocolDomain (eliminateSig hpsi) q2.1 q2.2
    (eliminateSig_inProtocolDomain hpsi q2.1.core q2.2.core h2.1 h2.2)

def generationBeforeCheck (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let b := generationBeforeMove hpsi kappa l r
  let q := authorizedCaptureSigMove hpsi b.1 b.2
  sanitizeAuthorizedPair hpsi (preCheckResetWall q.1 q.2)

attribute [local irreducible] generationBeforeMove authorizedCaptureSigMove

theorem generationBeforeCheck_inProtocolDomain (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := generationBeforeCheck hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let b := generationBeforeMove hpsi kappa l r
  have hb := generationBeforeMove_inProtocolDomain hpsi kappa l r hl hr
  have hm := authorizedCaptureSigMove_inProtocolDomain hpsi b.1 b.2 hb.1 hb.2
  let m := authorizedCaptureSigMove hpsi b.1 b.2
  have hw := preCheckResetWall_inProtocolDomain m.1 m.2 hm.1 hm.2
  exact ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi _ hw.1,
    sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi _ hw.2⟩

def generationGuardedAuthorizedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then (l0, r0)
  else
    let beforeCheck := generationBeforeCheck hpsi kappa l0 r0
    let afterCheck := congestGuardCheck hpsi beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born (actionOneAfterCheckSuffix hpsi afterCheck.1 afterCheck.2)

attribute [local irreducible] generationBeforeCheck actionOneAfterCheckSuffix

theorem generationGuardedAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := generationGuardedAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold generationGuardedAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let b := generationBeforeCheck hpsi kappa l0 r0
      have hb := generationBeforeCheck_inProtocolDomain hpsi kappa l0 r0 hl0 hr0
      let c := congestGuardCheck hpsi b.1 b.2
      have hc := congestGuardCheck_inProtocolDomain hpsi b.1 b.2 hb.1 hb.2
      exact markLeaderBirth_inProtocolDomain _ _
        (actionOneAfterCheckSuffix_inProtocolDomain hpsi kappa c.1 c.2 hc.1 hc.2)

/-- Reification on the same bounded state carrier. -/
def generationGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa × AuthorizedBoundedAgentState psi kappa :=
  let q := generationGuardedAuthorizedTransition hpsi kappa l.erase r.erase
  let hq := generationGuardedAuthorizedTransition_inProtocolDomain hpsi kappa
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem erase_generationGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := generationGuardedBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) =
      generationGuardedAuthorizedTransition hpsi kappa l.erase r.erase := by
  unfold generationGuardedBoundedTransition
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

/-- The full current finite host with source-control reset at both GENSIG
writers.  Prepared disposal, expiry and birth-signal initialization are the
same operations on the same inputs as in the captured-arrival host. -/
def generationFullTransition (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := generationGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  initializeFollowerPairBirthSignals l0 r0
    (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)

private theorem generationGuarded_eq_of_active (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (ha : deletionActive (normalizeDeletion l) = true ∨
      deletionActive (normalizeDeletion r) = true) :
    generationGuardedAuthorizedTransition hpsi kappa l r =
      arrivalGuardedAuthorizedTransition hpsi kappa l r := by
  unfold generationGuardedAuthorizedTransition arrivalGuardedAuthorizedTransition
  dsimp only
  by_cases hr : deletionActive (normalizeDeletion r) = true
  · simp only [hr, ↓reduceIte]
  · have hl : deletionActive (normalizeDeletion l) = true := ha.resolve_right hr
    simp only [hr, hl, ↓reduceIte]

attribute [local irreducible] arrivalGuardedBoundedTransition

/-- Every actual disposal input has exactly the previous complete finite
successor, hence keeps the proved pinning and incoming-deletion contracts. -/
theorem generationFull_eq_arrivalFull_of_due
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (ha : DisposalDue hpsi l.core.erase ∨ DisposalDue hpsi r.core.erase) :
    generationFullTransition hpsi kappa tau l r =
      arrivalFullTransition hpsi kappa tau l r := by
  have hactive : deletionActive (preparedInput hpsi l.core.erase) = true ∨
      deletionActive (preparedInput hpsi r.core.erase) = true :=
    ha.imp (prepared_due_active hpsi l.core.erase) (prepared_due_active hpsi r.core.erase)
  have hr : generationGuardedAuthorizedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core).erase
      (prepareBoundedDisposal hpsi r.core).erase =
      arrivalGuardedAuthorizedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core).erase
        (prepareBoundedDisposal hpsi r.core).erase := by
    rw [erase_prepareBoundedDisposal, erase_prepareBoundedDisposal]
    exact generationGuarded_eq_of_active hpsi kappa _ _ hactive
  have hb : generationGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) =
      arrivalGuardedBoundedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) := by
    unfold generationGuardedBoundedTransition arrivalGuardedBoundedTransition
    dsimp only
    simp only [hr]
  unfold generationFullTransition arrivalFullTransition
  dsimp only [prepareExpiringDisposal]
  rw [hb]

private theorem generationBeforeMove_eq_of_no_write
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hw : let p := authorizedPPsiLeaderResetProbeWall hpsi l r
      generationWrites hpsi kappa p.1.core p.2.core = (false, false)) :
    generationBeforeMove hpsi kappa l r = arrivalBeforeMove hpsi kappa l r := by
  let p := authorizedPPsiLeaderResetProbeWall hpsi l r
  have heq := genClean_eq_of_no_write hpsi kappa p.1.core p.2.core
    (congrArg Prod.fst hw) (congrArg Prod.snd hw)
  unfold generationBeforeMove arrivalBeforeMove authorizedGenClean authorizedGenSig
    authorizedReconcile
  dsimp only
  rw [heq]

private theorem generationGuarded_eq_of_no_write
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hw :
      let p := authorizedPPsiLeaderResetProbeWall hpsi
        (normalizeDeletion l) (normalizeDeletion r)
      generationWrites hpsi kappa p.1.core p.2.core = (false, false)) :
    generationGuardedAuthorizedTransition hpsi kappa l r =
      arrivalGuardedAuthorizedTransition hpsi kappa l r := by
  have hb : generationBeforeCheck hpsi kappa (normalizeDeletion l) (normalizeDeletion r) =
      arrivalBeforeCheck hpsi kappa (normalizeDeletion l) (normalizeDeletion r) := by
    unfold generationBeforeCheck arrivalBeforeCheck
    rw [generationBeforeMove_eq_of_no_write hpsi kappa _ _ hw]
  unfold generationGuardedAuthorizedTransition arrivalGuardedAuthorizedTransition
  dsimp only
  split
  · rfl
  · split
    · rfl
    · rw [hb]

/-- A computable absence of source writers gives equality of the complete
pair successor, not just the raw GENSIG row.  In particular ordinary
DISAPPEAR creation and transport of new action five remain unchanged. -/
theorem generationFull_eq_arrivalFull_of_no_write
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (hw :
      let p := authorizedPPsiLeaderResetProbeWall hpsi
        (preparedInput hpsi l.core.erase) (preparedInput hpsi r.core.erase)
      generationWrites hpsi kappa p.1.core p.2.core = (false, false)) :
    generationFullTransition hpsi kappa tau l r =
      arrivalFullTransition hpsi kappa tau l r := by
  have hr : generationGuardedAuthorizedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core).erase
      (prepareBoundedDisposal hpsi r.core).erase =
      arrivalGuardedAuthorizedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core).erase
        (prepareBoundedDisposal hpsi r.core).erase := by
    rw [erase_prepareBoundedDisposal, erase_prepareBoundedDisposal]
    exact generationGuarded_eq_of_no_write hpsi kappa _ _ hw
  have hb : generationGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) =
      arrivalGuardedBoundedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) := by
    unfold generationGuardedBoundedTransition arrivalGuardedBoundedTransition
    dsimp only
    simp only [hr]
  unfold generationFullTransition arrivalFullTransition
  dsimp only [prepareExpiringDisposal]
  rw [hb]

#print axioms genClean_exact
#print axioms genClean_written_control_empty
#print axioms genClean_eq_of_no_write
#print axioms genClean_inProtocolDomain
#print axioms genCleanEmit_writer
#print axioms genCleanPropagate_writer
#print axioms authorizedGenClean_written_control_empty
#print axioms generationBeforeMove_inProtocolDomain
#print axioms generationBeforeCheck_inProtocolDomain
#print axioms generationGuardedAuthorizedTransition_inProtocolDomain
#print axioms erase_generationGuardedBoundedTransition
#print axioms generationFull_eq_arrivalFull_of_due
#print axioms generationFull_eq_arrivalFull_of_no_write

end BirthGenerationControlRepair

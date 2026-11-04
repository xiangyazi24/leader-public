import Leader.Wu.Birth.TossCheckRearmCounterexample

set_option autoImplicit false

namespace BirthTossCheckPreservationRepair

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair
  BirthDisposalRouteInvariant BirthMismatchDisposalProducer
  BirthArrivalCaptureRepair BirthGenerationControlRepair

variable {psi kappa tau : Nat}

/-! A current toss is an input to the following DISAPPEAR stage.  CHECK must
not overwrite it with ready before that consumer.  The extra guard below
protects precisely toss.  It does not restore receiver-old state: incoming
payload acquisition still uses captured Step1, and both GENSIG writers still
clear replaced source controls.  All other prefix and suffix stages retain
their order in the source-reset finite host. -/

/-- Preserve the current lottery input until the immediately following
DISAPPEAR stage; otherwise execute the existing congest-guarded CHECK. -/
def preserveTossCheck (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  if l.core.state = .toss ∨ r.core.state = .toss then (l, r)
  else congestGuardCheck hpsi l r

/-- The protected decision is a current input state, not a promised future
lottery event.  CHECK leaves the whole pair unchanged in this row. -/
theorem preserveTossCheck_of_toss (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (ht : l.core.state = .toss ∨ r.core.state = .toss) :
    preserveTossCheck hpsi l r = (l, r) := by
  simp [preserveTossCheck, ht]

/-- Every pair with no current toss executes exactly the existing CHECK. -/
theorem preserveTossCheck_of_no_toss (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.state ≠ .toss) (hr : r.core.state ≠ .toss) :
    preserveTossCheck hpsi l r = congestGuardCheck hpsi l r := by
  simp [preserveTossCheck, hl, hr]

theorem preserveTossCheck_inProtocolDomain (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := preserveTossCheck hpsi l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  unfold preserveTossCheck
  split
  · exact ⟨hl, hr⟩
  · exact congestGuardCheck_inProtocolDomain hpsi l r hl hr

/-- For arbitrary positive psi, the actual consecutive CHECK/DISAPPEAR
stages turn a label-zero responder toss into a newly assigned action five.
The payload survives this producer; no old control or route invariant is
assumed, and the initiator may have arbitrary lottery registers. -/
theorem preserved_toss_reaches_disappear_producer (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hr : r.core.state = .toss) (hlabel : r.core.label = ⟨0, hpsi⟩) :
    let c := preserveTossCheck hpsi l r
    let d := authorizedDisappear hpsi c.1 c.2
    d.2.core.state = .toss_done ∧ d.2.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      d.2.core.path = r.core.path := by
  rw [preserveTossCheck_of_toss hpsi l r (Or.inr hr)]
  unfold authorizedDisappear authorizedReconcile disappear
  dsimp only
  simp only [hr, hlabel, and_self, ↓reduceIte]
  repeat (first | rfl | split)
  all_goals simp_all

def tossGuardedAuthorizedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then (l0, r0)
  else
    let beforeCheck := generationBeforeCheck hpsi kappa l0 r0
    let afterCheck := preserveTossCheck hpsi beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born (actionOneAfterCheckSuffix hpsi afterCheck.1 afterCheck.2)

attribute [local irreducible] generationBeforeCheck actionOneAfterCheckSuffix

theorem tossGuardedAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    let q := tossGuardedAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold tossGuardedAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let b := generationBeforeCheck hpsi kappa l0 r0
      have hb := generationBeforeCheck_inProtocolDomain hpsi kappa l0 r0 hl0 hr0
      let c := preserveTossCheck hpsi b.1 b.2
      have hc := preserveTossCheck_inProtocolDomain hpsi b.1 b.2 hb.1 hb.2
      exact markLeaderBirth_inProtocolDomain _ _
        (actionOneAfterCheckSuffix_inProtocolDomain hpsi kappa c.1 c.2 hc.1 hc.2)

def tossGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa × AuthorizedBoundedAgentState psi kappa :=
  let q := tossGuardedAuthorizedTransition hpsi kappa l.erase r.erase
  let hq := tossGuardedAuthorizedTransition_inProtocolDomain hpsi kappa
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem erase_tossGuardedBoundedTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := tossGuardedBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) = tossGuardedAuthorizedTransition hpsi kappa l.erase r.erase := by
  unfold tossGuardedBoundedTransition
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

/-- The complete source-reset host with precisely the toss CHECK guard.
Disposal entry, expiry and final leader-signal initialization are unchanged. -/
def tossFullTransition (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := tossGuardedBoundedTransition hpsi kappa l0.core r0.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  initializeFollowerPairBirthSignals l0 r0
    (deletionPriorityExpireOne tau l0 lOut, deletionPriorityExpireOne tau r0 rOut)

private theorem tossGuarded_eq_of_active (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (ha : deletionActive (normalizeDeletion l) = true ∨
      deletionActive (normalizeDeletion r) = true) :
    tossGuardedAuthorizedTransition hpsi kappa l r =
      generationGuardedAuthorizedTransition hpsi kappa l r := by
  unfold tossGuardedAuthorizedTransition generationGuardedAuthorizedTransition
  dsimp only
  by_cases hr : deletionActive (normalizeDeletion r) = true
  · simp only [hr, ↓reduceIte]
  · have hl : deletionActive (normalizeDeletion l) = true := ha.resolve_right hr
    simp only [hr, hl, ↓reduceIte]

attribute [local irreducible] generationGuardedBoundedTransition

/-- An actual disposal input retains exactly its prior full pair successor. -/
theorem tossFull_eq_generationFull_of_due
    (hpsi : psi > 0) (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (ha : DisposalDue hpsi l.core.erase ∨ DisposalDue hpsi r.core.erase) :
    tossFullTransition hpsi kappa tau l r = generationFullTransition hpsi kappa tau l r := by
  have hactive : deletionActive (preparedInput hpsi l.core.erase) = true ∨
      deletionActive (preparedInput hpsi r.core.erase) = true :=
    ha.imp (prepared_due_active hpsi l.core.erase) (prepared_due_active hpsi r.core.erase)
  have hr : tossGuardedAuthorizedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core).erase
      (prepareBoundedDisposal hpsi r.core).erase =
      generationGuardedAuthorizedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core).erase
        (prepareBoundedDisposal hpsi r.core).erase := by
    rw [erase_prepareBoundedDisposal, erase_prepareBoundedDisposal]
    exact tossGuarded_eq_of_active hpsi kappa _ _ hactive
  have hb : tossGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) =
      generationGuardedBoundedTransition hpsi kappa
        (prepareBoundedDisposal hpsi l.core) (prepareBoundedDisposal hpsi r.core) := by
    unfold tossGuardedBoundedTransition generationGuardedBoundedTransition
    dsimp only
    simp only [hr]
  unfold tossFullTransition generationFullTransition
  dsimp only [prepareExpiringDisposal]
  rw [hb]

#print axioms preserveTossCheck_of_toss
#print axioms preserveTossCheck_of_no_toss
#print axioms preserveTossCheck_inProtocolDomain
#print axioms preserved_toss_reaches_disappear_producer
#print axioms tossGuardedAuthorizedTransition_inProtocolDomain
#print axioms erase_tossGuardedBoundedTransition
#print axioms tossFull_eq_generationFull_of_due

end BirthTossCheckPreservationRepair

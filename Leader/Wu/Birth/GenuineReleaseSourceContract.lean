import Leader.Wu.Birth.ReleaseTerminalInvariant
import Leader.Wu.Birth.SingleUseReleaseWitnesses

set_option autoImplicit false

namespace BirthGenuineReleaseSourceContract

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLWallSweepNormalResetContract
  PPLLCompleteMultiLeaderCleanup PPLLComparisonHistory PPLLWriteIncrementGate
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair
  BirthMismatchDisposalProducer BirthGenerationControlRepair
  BirthTossCheckPreservationRepair BirthSingleUseReleaseRepair
  BirthSingleUseReleaseWitnesses BirthReleaseTerminalInvariant BirthArrivalCaptureWitnesses

variable {psi kappa tau : Nat}

/-! A source contract at an actual full-host boundary.  A responder toss at
zero, serviced by an empty predecessor, produces a new five which survives
the entire comparison, reset, WRITE, birth-marking and expiry suffix under
current reset/follower and positive-credit conditions.  This is the same
producer reached by the already checked real GEN/less/toss history.

The contract distinguishes the release writer from payload identity.  It
does not require a common GEN epoch, and a retained path value alone is not
claimed to prove membership in an unchanged source group. -/

private theorem disappear_anchor (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    anchorView (authorizedDisappear hpsi l r).1.core = anchorView l.core ∧
      anchorView (authorizedDisappear hpsi l r).2.core = anchorView r.core := by
  have hsR (a b : AgentState psi) :
      anchorView (disappearStartR hpsi a b).1 = anchorView a ∧
        anchorView (disappearStartR hpsi a b).2 = anchorView b := by
    unfold disappearStartR
    split <;> exact ⟨rfl, rfl⟩
  have hsL (a b : AgentState psi) :
      anchorView (disappearStartL hpsi a b).1 = anchorView a ∧
        anchorView (disappearStartL hpsi a b).2 = anchorView b := by
    unfold disappearStartL
    split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have hc (a b : AgentState psi) :
      anchorView (disappearCarry hpsi a b).1 = anchorView a ∧
        anchorView (disappearCarry hpsi a b).2 = anchorView b := by
    unfold disappearCarry
    repeat (first | exact ⟨rfl, rfl⟩ | split)
  let q0 := disappearStartR hpsi l.core r.core
  let q1 := disappearStartL hpsi q0.1 q0.2
  have h0 := hsR l.core r.core
  have h1 := hsL q0.1 q0.2
  have h2 := hc q1.1 q1.2
  exact ⟨h2.1.trans (h1.1.trans h0.1), h2.2.trans (h1.2.trans h0.2)⟩

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

attribute [local irreducible] eliminateLeadersNoCollisionLeaderSink writeSeqIncrementGate

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

/-- At an empty-predecessor service edge, the normal toss producer keeps its
payload and newly written five through the complete actual post-CHECK
suffix.  COMPARE's empty-left dispatch is proved from the current path;
WRITE and leader elimination use their checked comparison frames. -/
theorem actual_toss_suffix_produces_release (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hlempty : l.core.path = .bot) (hrtoss : r.core.state = .toss)
    (hrzero : r.core.label = ⟨0, hpsi⟩) (hlleader : l.core.leader = false)
    (hlreset : l.core.reset_cmd = false) (hrreset : r.core.reset_cmd = false) :
    let c := preserveTossCheck hpsi l r
    let q := actionOneAfterCheckSuffix hpsi c.1 c.2
    q.2.core.state = .toss_done ∧ q.2.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      q.2.core.path = r.core.path ∧ q.2.core.label = ⟨0, hpsi⟩ := by
  rw [preserveTossCheck_of_toss hpsi l r (Or.inr hrtoss)]
  let d := authorizedDisappear hpsi l r
  have hd := preserved_toss_reaches_disappear_producer hpsi l r hrtoss hrzero
  rw [preserveTossCheck_of_toss hpsi l r (Or.inr hrtoss)] at hd
  have ha := disappear_anchor hpsi l r
  have hdlp : d.1.core.path = .bot :=
    (congrArg (fun a : Bool × Bool × Fin psi × PathInfo => a.2.2.2) ha.1).trans hlempty
  have hdll : d.1.core.leader = false := (congrArg Prod.fst ha.1).trans hlleader
  have hdlr : d.1.core.reset_cmd = false :=
    (congrArg (fun a : Bool × Bool × Fin psi × PathInfo => a.2.1) ha.1).trans hlreset
  have hdrr : d.2.core.reset_cmd = false :=
    (congrArg (fun a : Bool × Bool × Fin psi × PathInfo => a.2.1) ha.2).trans hrreset
  have hdrz : d.2.core.label = ⟨0, hpsi⟩ :=
    (congrArg (fun a : Bool × Bool × Fin psi × PathInfo => a.2.2.1) ha.2).trans hrzero
  let a := authorizedCompareSigActionOne hpsi d.1 d.2
  have har : a.2 = d.2 := by
    simp [a, authorizedCompareSigActionOne, compareSigInit, hdlp]
  have hall : a.1.core.leader = false := by
    simpa [a, authorizedCompareSigActionOne, compareSigInit, hdlp] using hdll
  have halr : a.1.core.reset_cmd = false := by
    simpa [a, authorizedCompareSigActionOne, compareSigInit, hdlp] using hdlr
  have harr : a.2.core.reset_cmd = false := by rw [har]; exact hdrr
  let s := authorizedReconcile (suppressSigResetKill hpsi) a.1 a.2
  let q := authorizedPostSuppressLeaderSink hpsi s.1 s.2
  have hs := suppress_no_reset_comparison hpsi a.1.core a.2.core hall halr harr
  have hsR : ComparisonTrackedView.ofState s.2.core =
      ComparisonTrackedView.ofState a.2.core := congrArg Prod.snd hs
  have hw := postSuppress_comparison hpsi s.1 s.2
  have hwR : ComparisonTrackedView.ofState q.2.core =
      ComparisonTrackedView.ofState s.2.core := congrArg Prod.snd hw
  have hframe := hwR.trans hsR
  rw [har] at hframe
  have hstate := (congrArg ComparisonTrackedView.state hframe).trans hd.1
  have hp2 := (congrArg ComparisonTrackedView.path2 hframe).trans hd.2.1
  have hp := (congrArg ComparisonTrackedView.path hframe).trans hd.2.2
  have hlabel := (authorizedPostSuppressLeaderSink_labels_eq hpsi s.1 s.2).2.trans
    ((suppressSigResetKill_right_label_eq hpsi a.1.core a.2.core).trans
      ((congrArg (fun u : AuthorizedAgentState psi => u.core.label) har).trans hdrz))
  exact ⟨hstate, hp2, hp, hlabel⟩

/-- The actual CHECK input, evaluated from the same current finite pair
after entry disposal and the complete single-use pre-CHECK pipeline. -/
def releaseCheckInput (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : AuthorizedAgentState psi × AuthorizedAgentState psi :=
  singleUseBeforeCheck hpsi kappa (preparedInput hpsi l) (preparedInput hpsi r)

attribute [local irreducible] releaseCheckInput singleUseBeforeCheck actionOneAfterCheckSuffix

private theorem authorized_toss_producer (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlinactive : deletionActive (preparedInput hpsi l) = false)
    (hrinactive : deletionActive (preparedInput hpsi r) = false)
    (hlempty : (releaseCheckInput hpsi kappa l r).1.core.path = .bot)
    (hrtoss : (releaseCheckInput hpsi kappa l r).2.core.state = .toss)
    (hrzero : (releaseCheckInput hpsi kappa l r).2.core.label = ⟨0, hpsi⟩)
    (hlleader : (releaseCheckInput hpsi kappa l r).1.core.leader = false)
    (hrleader : (releaseCheckInput hpsi kappa l r).2.core.leader = false)
    (hlreset : (releaseCheckInput hpsi kappa l r).1.core.reset_cmd = false)
    (hrreset : (releaseCheckInput hpsi kappa l r).2.core.reset_cmd = false) :
    let q := singleUseGuardedAuthorizedTransition hpsi kappa
      (prepareDisposal hpsi l) (prepareDisposal hpsi r)
    q.2.core.state = .toss_done ∧ q.2.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      q.2.core.path = (releaseCheckInput hpsi kappa l r).2.core.path ∧
      q.2.core.label = ⟨0, hpsi⟩ := by
  let b := releaseCheckInput hpsi kappa l r
  have hbL : b.1.core.leader = false := hlleader
  have hbR : b.2.core.leader = false := hrleader
  have hc : preserveTossCheck hpsi b.1 b.2 = b :=
    preserveTossCheck_of_toss hpsi b.1 b.2 (Or.inr hrtoss)
  have hb : leaderBirthBeforeOrAtCheck (preparedInput hpsi l)
      (preparedInput hpsi r) b b = false := by
    simp [leaderBirthBeforeOrAtCheck, endpointLeaderBorn, hbL, hbR]
  have hs := actual_toss_suffix_produces_release hpsi b.1 b.2 hlempty hrtoss hrzero
    hlleader hlreset hrreset
  rw [hc] at hs
  have he : singleUseGuardedAuthorizedTransition hpsi kappa
      (prepareDisposal hpsi l) (prepareDisposal hpsi r) =
      actionOneAfterCheckSuffix hpsi b.1 b.2 := by
    unfold singleUseGuardedAuthorizedTransition
    change (if deletionActive (preparedInput hpsi r) then _ else
      if deletionActive (preparedInput hpsi l) then _ else _) = _
    simp only [hlinactive, hrinactive, Bool.false_eq_true, ↓reduceIte]
    have hbdef : singleUseBeforeCheck hpsi kappa
        (normalizeDeletion (prepareDisposal hpsi l))
        (normalizeDeletion (prepareDisposal hpsi r)) = b := by
      unfold b releaseCheckInput preparedInput
      rfl
    rw [hbdef, hc]
    unfold preparedInput at hb
    rw [hb]
    rfl
  rw [he]
  exact hs

private theorem erase_prepared_singleUse (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := singleUseGuardedBoundedTransition hpsi kappa
      (prepareBoundedDisposal hpsi l) (prepareBoundedDisposal hpsi r)
    (q.1.erase, q.2.erase) = singleUseGuardedAuthorizedTransition hpsi kappa
      (prepareDisposal hpsi l.erase) (prepareDisposal hpsi r.erase) := by
  dsimp only
  rw [erase_singleUseGuardedBoundedTransition, erase_prepareBoundedDisposal,
    erase_prepareBoundedDisposal]

private theorem signal_right_fields (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau) :
    (initializeFollowerPairBirthSignals l r q).2.core.erase.core.state =
        q.2.core.erase.core.state ∧
      (initializeFollowerPairBirthSignals l r q).2.core.erase.core.path2 =
        q.2.core.erase.core.path2 ∧
      (initializeFollowerPairBirthSignals l r q).2.core.erase.core.path =
        q.2.core.erase.core.path ∧
      (initializeFollowerPairBirthSignals l r q).2.core.erase.core.label =
        q.2.core.erase.core.label := by
  unfold initializeFollowerPairBirthSignals
  split
  · change (clearExpiringLeaderSignal q.2).core.erase.core.state = q.2.core.erase.core.state ∧
      (clearExpiringLeaderSignal q.2).core.erase.core.path2 = q.2.core.erase.core.path2 ∧
      (clearExpiringLeaderSignal q.2).core.erase.core.path = q.2.core.erase.core.path ∧
      (clearExpiringLeaderSignal q.2).core.erase.core.label = q.2.core.erase.core.label
    unfold clearExpiringLeaderSignal
    split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

attribute [local irreducible] singleUseGuardedBoundedTransition

/-- A computed current toss cut produces an actual full finite successor
with a new five, the same resident payload, and toss_done at physical zero.
Positive current responder credit is the explicit condition that excludes
same-interaction path expiry; no bound is silently placed on tau. -/
theorem actual_toss_produces_full_release (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hlinactive : deletionActive (preparedInput hpsi l.core.erase) = false)
    (hrinactive : deletionActive (preparedInput hpsi r.core.erase) = false)
    (hlempty : (releaseCheckInput hpsi kappa l.core.erase r.core.erase).1.core.path = .bot)
    (hrtoss : (releaseCheckInput hpsi kappa l.core.erase r.core.erase).2.core.state = .toss)
    (hrzero : (releaseCheckInput hpsi kappa l.core.erase r.core.erase).2.core.label = ⟨0, hpsi⟩)
    (hlleader : (releaseCheckInput hpsi kappa l.core.erase r.core.erase).1.core.leader = false)
    (hrleader : (releaseCheckInput hpsi kappa l.core.erase r.core.erase).2.core.leader = false)
    (hlreset : (releaseCheckInput hpsi kappa l.core.erase r.core.erase).1.core.reset_cmd = false)
    (hrreset : (releaseCheckInput hpsi kappa l.core.erase r.core.erase).2.core.reset_cmd = false)
    (hcredit : 0 < r.stall.val) :
    let q := singleUseFullTransition hpsi kappa tau l r
    q.2.core.erase.core.state = .toss_done ∧
      q.2.core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      q.2.core.erase.core.path =
        (releaseCheckInput hpsi kappa l.core.erase r.core.erase).2.core.path ∧
      q.2.core.erase.core.label = ⟨0, hpsi⟩ := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let q := singleUseGuardedBoundedTransition hpsi kappa l0.core r0.core
  let a : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let b : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  have hf := authorized_toss_producer hpsi kappa l.core.erase r.core.erase
    hlinactive hrinactive hlempty hrtoss hrzero hlleader hrleader hlreset hrreset
  rw [← erase_prepared_singleUse hpsi kappa l.core r.core] at hf
  have hs := signal_right_fields l0 r0
    (deletionPriorityExpireOne tau l0 a, deletionPriorityExpireOne tau r0 b)
  have he := BirthCheckParametricWait.expiry_core_of_positive r0 b hcredit
  have hstate := hs.1
  have hp2 := hs.2.1
  have hp := hs.2.2.1
  have hlabel := hs.2.2.2
  rw [he] at hstate hp2 hp hlabel
  exact ⟨hstate.trans hf.1, hp2.trans hf.2.1, hp.trans hf.2.2.1,
    hlabel.trans hf.2.2.2⟩

attribute [local semireducible] singleUseGuardedBoundedTransition releaseCheckInput
  singleUseBeforeCheck actionOneAfterCheckSuffix eliminateLeadersNoCollisionLeaderSink
  writeSeqIncrementGate

private theorem get_ofFn {n : Nat} {Q : Type} (C : Fin n → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

private def cachedRun {n : Nat} {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q) :
    DetSchedule n → Vector Q n → Vector Q n
  | [], C => C
  | e :: rest, C => cachedRun ring T rest (Vector.ofFn (localStep ring T C.get e))

private theorem cachedRun_correct {n : Nat} {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (C : Fin n → Q) (word : DetSchedule n) :
    (cachedRun ring T word (Vector.ofFn C)).get = runLocalSchedule ring T C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [cachedRun, get_ofFn, runLocalSchedule]
      exact ih _

/-- The real incoming producer edge after the already checked proper-ruler
GEN/less/toss prefix; neither input is manually reseeded. -/
def genuineLeft : ExpiringAgentState 2 2 16 := singleUseLifecyclePrefix 14 7
def genuineRight : ExpiringAgentState 2 2 16 := singleUseLifecyclePrefix 14 8

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Every executable premise of the general producer holds on the real
history.  Its source bits were actually generated, and the earlier CHECK
really read less before the control became toss. -/
theorem genuine_history_supplies_producer :
    (singleUseLifecyclePrefix 8 6).core.core.path = .some 0 1 ∧
      (singleUseLifecyclePrefix 8 7).core.core.path = .some 1 0 ∧
      (let b := releaseCheckInput hTwo 2
        (singleUseLifecyclePrefix 12 8).core.erase (singleUseLifecyclePrefix 12 9).core.erase
       (preserveTossCheck hTwo b.1 b.2).1.core.state = .less) ∧
      deletionActive (preparedInput hTwo genuineLeft.core.erase) = false ∧
      deletionActive (preparedInput hTwo genuineRight.core.erase) = false ∧
      (releaseCheckInput hTwo 2 genuineLeft.core.erase genuineRight.core.erase).1.core.path = .bot ∧
      (releaseCheckInput hTwo 2 genuineLeft.core.erase genuineRight.core.erase).2.core.state = .toss ∧
      (releaseCheckInput hTwo 2 genuineLeft.core.erase genuineRight.core.erase).2.core.label = 0 ∧
      (releaseCheckInput hTwo 2 genuineLeft.core.erase genuineRight.core.erase).1.core.leader = false ∧
      (releaseCheckInput hTwo 2 genuineLeft.core.erase genuineRight.core.erase).2.core.leader = false ∧
      (releaseCheckInput hTwo 2 genuineLeft.core.erase genuineRight.core.erase).1.core.reset_cmd = false ∧
      (releaseCheckInput hTwo 2 genuineLeft.core.erase genuineRight.core.erase).2.core.reset_cmd = false ∧
      0 < genuineRight.stall.val ∧
      (releaseCheckInput hTwo 2 genuineLeft.core.erase genuineRight.core.erase).2.core.path = .some 0 1 := by
  unfold genuineLeft genuineRight releaseCheckInput singleUseLifecyclePrefix
  simp only [← cachedRun_correct]
  decide

/-- The new-five output of the actual normal history is obtained by applying
the general complete-host producer, not by replacing its missing suffix
with a raw DISAPPEAR conclusion. -/
theorem genuine_history_uses_general_producer :
    let q := singleUseFullTransition hTwo 2 16 genuineLeft genuineRight
    q.2.core.erase.core.state = .toss_done ∧
      q.2.core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      q.2.core.erase.core.path = .some 0 1 ∧ q.2.core.erase.core.label = 0 := by
  rcases genuine_history_supplies_producer with
    ⟨_, _, _, hli, hri, hle, hrt, hrz, hll, hrl, hlr, hrr, hcredit, hp⟩
  have h := actual_toss_produces_full_release hTwo 2 16 genuineLeft genuineRight
    hli hri hle hrt hrz hll hrl hlr hrr hcredit
  exact ⟨h.1, h.2.1, h.2.2.1.trans hp, h.2.2.2⟩

#print axioms actual_toss_suffix_produces_release
#print axioms actual_toss_produces_full_release
#print axioms genuine_history_supplies_producer
#print axioms genuine_history_uses_general_producer

end BirthGenuineReleaseSourceContract

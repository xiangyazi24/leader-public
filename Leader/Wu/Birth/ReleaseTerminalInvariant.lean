import Leader.Wu.Birth.SingleUseReleaseRepair

set_option autoImplicit false

namespace BirthReleaseTerminalInvariant

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepNormalResetContract
  PPLLCompleteMultiLeaderCleanup PPLLComparisonHistory PPLLWriteIncrementGate
  PPLLPathStallComparisonRepair
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair
  BirthMismatchDisposalProducer BirthGenerationControlRepair
  BirthTossCheckPreservationRepair BirthSingleUseReleaseRepair

variable {psi kappa tau : Nat}

attribute [local irreducible] generationBeforeMove authorizedSingleUseReleaseMove
  eliminateLeadersNoCollisionLeaderSink writeSeqIncrementGate

/-! A current-state invariant for release control on the complete single-use
host.  For psi greater than one, a new DISAPPEAR five originates at a
nonterminal zero.  SIGMOVE consumes five on its first terminal application;
the remaining actual stages cannot recreate a terminal five.  This result
tracks physical location and opcode only.  It asserts neither equality of
GEN epochs nor attachment to an unchanged source ID. -/

/-- No reusable action five is resident at a physical terminal.  The
predicate refers only to current counted fields, with no history field. -/
def NoTerminalFive (u : AgentState psi) : Prop :=
  ∀ p : Path2Info, u.path2 = some p → p.action = 5 → u.label.val ≠ psi - 1

private theorem noFive_of_fields (u v : AgentState psi) (hu : NoTerminalFive u)
    (hl : v.label = u.label) (hp : v.path2 = u.path2) : NoTerminalFive v := by
  intro p hpath ha
  rw [hl]
  exact hu p (hp.symm.trans hpath) ha

private theorem noFive_none (u : AgentState psi) (hp : u.path2 = none) :
    NoTerminalFive u := by
  simp [NoTerminalFive, hp]

private theorem noFive_set_other (u : AgentState psi) (p : Path2Info)
    (ha : p.action ≠ 5) : NoTerminalFive { u with path2 := some p } := by
  simpa [NoTerminalFive] using fun h : p.action = 5 => False.elim (ha h)

private theorem clear_noFive (u : AgentState psi) :
    NoTerminalFive (clearComparisonSignal u) :=
  noFive_none _ rfl

private theorem ready_noFive (u : AgentState psi) (hu : NoTerminalFive u) :
    NoTerminalFive (checkSigSetReady u) := by
  unfold checkSigSetReady
  split
  · split <;> exact hu
  · exact hu

private theorem checkL_noFive (hpsi : psi > 0) (u : AgentState psi)
    (hu : NoTerminalFive u) : NoTerminalFive (checkSigCheckL hpsi u) := by
  unfold checkSigCheckL
  split
  · split <;> exact hu
  · exact hu

private theorem checkR_noFive (hpsi : psi > 0) (l r : AgentState psi)
    (hr : NoTerminalFive r) : NoTerminalFive (checkSigCheckR hpsi l r) := by
  unfold checkSigCheckR
  split
  · split
    · split <;> exact hr
    · exact hr
  · exact hr

private theorem result_noFive (u : AgentState psi) (hu : NoTerminalFive u) :
    NoTerminalFive (checkSigSetResult u) := by
  unfold checkSigSetResult
  split
  · dsimp only
    split
    · exact noFive_set_other _ _ (by decide)
    · exact noFive_set_other _ _ (by decide)
  · dsimp only
    split
    · exact noFive_set_other _ _ (by decide)
    · exact hu

private theorem check_noFive (hpsi : psi > 0) (l r : AgentState psi)
    (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := checkSig hpsi l r
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  rw [checkSig_eq_staged]
  have hl' := result_noFive _ (checkL_noFive hpsi _ (ready_noFive l hl))
  have hr' := result_noFive _ (checkR_noFive hpsi
    (checkSigCheckL hpsi (checkSigSetReady l)) _ (ready_noFive r hr))
  unfold checkSigStaged checkSigSetLeader
  dsimp only
  split <;> exact ⟨hl', hr'⟩

private theorem preserveCheck_noFive (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) (hl : NoTerminalFive l.core)
    (hr : NoTerminalFive r.core) :
    let q := preserveTossCheck hpsi l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  unfold preserveTossCheck
  split
  · exact ⟨hl, hr⟩
  · unfold congestGuardCheck
    split
    · exact ⟨hl, hr⟩
    · exact check_noFive hpsi l.core r.core hl hr

private theorem disappearStartR_noFive (hpsi : psi > 0) (hlarge : 1 < psi)
    (l r : AgentState psi) (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := disappearStartR hpsi l r
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  unfold disappearStartR
  split
  · rename_i h
    refine ⟨hl, ?_⟩
    intro p hp ha
    have hz := congrArg Fin.val h.2
    dsimp only at hz ⊢
    omega
  · exact ⟨hl, hr⟩

private theorem disappearStartL_noFive (hpsi : psi > 0)
    (l r : AgentState psi) (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := disappearStartL hpsi l r
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  unfold disappearStartL
  split
  · split <;> exact ⟨hl, hr⟩
  · exact ⟨hl, hr⟩

private theorem disappearCarry_noFive (hpsi : psi > 0)
    (l r : AgentState psi) (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := disappearCarry hpsi l r
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  unfold disappearCarry
  repeat (first | exact ⟨hl, hr⟩ | split)

/-- The only new-five producer is harmless for this invariant exactly when
its physical zero differs from the terminal; no payload-presence or
cohort premise is needed. -/
theorem disappear_no_terminal_five (hpsi : psi > 0) (hlarge : 1 < psi)
    (l r : AuthorizedAgentState psi) (hl : NoTerminalFive l.core)
    (hr : NoTerminalFive r.core) :
    let q := authorizedDisappear hpsi l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  change NoTerminalFive (disappear hpsi l.core r.core).1 ∧
    NoTerminalFive (disappear hpsi l.core r.core).2
  rw [disappear_eq_staged]
  have h0 := disappearStartR_noFive hpsi hlarge l.core r.core hl hr
  have h1 := disappearStartL_noFive hpsi _ _ h0.1 h0.2
  exact disappearCarry_noFive hpsi _ _ h1.1 h1.2

private theorem cmpReturn_noFive (hpsi : psi > 0) (l r : AgentState psi)
    (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := cmpUpdateReturnPriority hpsi l r
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  unfold cmpUpdateReturnPriority
  repeat (first | exact ⟨hl, hr⟩ | split)

private theorem cmpSet_noFive (hpsi : psi > 0) (u : AgentState psi)
    (hu : NoTerminalFive u) : NoTerminalFive (cmpUpdateSetPath2 hpsi u) := by
  unfold cmpUpdateSetPath2
  split
  · split
    · exact noFive_set_other _ _ (by simp)
    · exact hu
  · exact hu

private theorem cmpUpdate_noFive (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : NoTerminalFive l.core) (hr : NoTerminalFive r.core) :
    let q := authorizedCmpUpdate hpsi l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  let lc := if freshComparisonStart hpsi l && !comparisonActive l.core.state then
    { l.core with state := .congest } else l.core
  have hc : NoTerminalFive lc := by unfold lc; split <;> exact hl
  have h := cmpReturn_noFive hpsi lc r.core hc hr
  exact ⟨cmpSet_noFive hpsi _ h.1, h.2⟩

private theorem compareL_noFive (hpsi : psi > 0) (u : AgentState psi)
    (hu : NoTerminalFive u) : NoTerminalFive (compareBitUpdateL hpsi u) := by
  unfold compareBitUpdateL
  split
  · split
    · exact noFive_set_other _ _ (by simp)
    · exact hu
  · exact hu

private theorem compareR_noFive (hpsi : psi > 0) (u : AgentState psi)
    (hu : NoTerminalFive u) : NoTerminalFive (compareBitUpdateRActionOne hpsi u) := by
  cases hp : u.path2 with
  | none => simpa [compareBitUpdateRActionOne, hp] using hu
  | some p =>
      by_cases hg : p.position = 0 ∧ p.action = 1
      · by_cases hgt : (if u.bit then 1 else 0) > p.bit
        · simp only [compareBitUpdateRActionOne, hp, hg, hgt, ↓reduceIte]
          exact noFive_set_other _ _ (by simp)
        · by_cases hlt : (if u.bit then 1 else 0) < p.bit
          · simp only [compareBitUpdateRActionOne, hp, hg, hgt, hlt, ↓reduceIte]
            exact noFive_set_other _ _ (by simp)
          · by_cases ht : u.label = ⟨psi - 1, by omega⟩
            all_goals simp [NoTerminalFive, compareBitUpdateRActionOne, hp, hg, hgt, hlt, ht]
      · simpa [compareBitUpdateRActionOne, hp, hg] using hu

private theorem dispatch_noFive (hpsi : psi > 0) (l r : AgentState psi)
    (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := compareSigDispatchActionOne hpsi l r
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  unfold compareSigDispatchActionOne
  split
  · exact ⟨compareL_noFive hpsi l hl, compareR_noFive hpsi r hr⟩
  · exact ⟨compareL_noFive hpsi l hl, compareR_noFive hpsi r hr⟩
  · exact ⟨hl, hr⟩

private theorem compare_noFive (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : NoTerminalFive l.core) (hr : NoTerminalFive r.core) :
    let q := authorizedCompareSigActionOne hpsi l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  have hi : NoTerminalFive (compareSigInit l.core) := by
    unfold compareSigInit
    split <;> exact hl
  let l0 : AuthorizedAgentState psi :=
    ⟨compareSigInit l.core, normalizePermit (compareSigInit l.core) l.path0Crossed⟩
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact ⟨hi, hr⟩
  · split
    · exact ⟨hi, hr⟩
    · have h := cmpUpdate_noFive hpsi l0 r hi hr
      exact dispatch_noFive hpsi _ _ h.1 h.2

private theorem resetKill_noFive (u : AgentState psi) (hu : NoTerminalFive u) :
    NoTerminalFive (resetKillComparison u) := by
  unfold resetKillComparison
  split
  · exact clear_noFive u
  · exact hu

private theorem suppressStart_noFive (l r : AgentState psi)
    (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := suppressSigStart l r
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  unfold suppressSigStart
  split <;> exact ⟨hl, hr⟩

private theorem suppressMove_noFive (l r : AgentState psi)
    (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := suppressSigMoveReset l r
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  unfold suppressSigMoveReset
  split <;> exact ⟨hl, hr⟩

private theorem suppressEnd_noFive (hpsi : psi > 0) (l r : AgentState psi)
    (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := suppressSigTerminal hpsi l r
    let q := suppressSigEcho q.1 q.2
    let q := suppressSigFinish q.1 q.2
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  have ht (a b : AgentState psi) (ha : NoTerminalFive a) (hb : NoTerminalFive b) :
      let q := suppressSigTerminal hpsi a b
      NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
    unfold suppressSigTerminal
    split <;> exact ⟨ha, hb⟩
  have he (a b : AgentState psi) (ha : NoTerminalFive a) (hb : NoTerminalFive b) :
      let q := suppressSigEcho a b
      NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
    unfold suppressSigEcho
    repeat (first | exact ⟨ha, hb⟩ | split)
  have hf (a b : AgentState psi) (ha : NoTerminalFive a) (hb : NoTerminalFive b) :
      let q := suppressSigFinish a b
      NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
    unfold suppressSigFinish
    split <;> exact ⟨ha, hb⟩
  have h0 := ht l r hl hr
  have h1 := he _ _ h0.1 h0.2
  exact hf _ _ h1.1 h1.2

private theorem suppress_noFive (hpsi : psi > 0) (l r : AgentState psi)
    (hl : NoTerminalFive l) (hr : NoTerminalFive r) :
    let q := suppressSigResetKill hpsi l r
    NoTerminalFive q.1 ∧ NoTerminalFive q.2 := by
  have h0 := suppressStart_noFive l r hl hr
  have h1 := suppressMove_noFive _ _
    (resetKill_noFive _ h0.1) (resetKill_noFive _ h0.2)
  exact suppressEnd_noFive hpsi _ _
    (resetKill_noFive _ h1.1) (resetKill_noFive _ h1.2)

private theorem postSuppress_noFive (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) (hl : NoTerminalFive l.core)
    (hr : NoTerminalFive r.core) :
    let q := authorizedPostSuppressLeaderSink hpsi l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  let a := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
  have ha := eliminateLeadersNoCollisionLeaderSink_comparisonTracked_frame
    hpsi l.core r.core
  have hw := writeSeqIncrementGate_comparisonTracked_pair hpsi a.1 a.2
  have haf : comparisonTrackedPair (a.1, a.2) = comparisonTrackedPair (l.core, r.core) :=
    Prod.ext ha.1 ha.2
  have hf := hw.trans haf
  have hlp := congrArg (fun p : ComparisonTrackedView psi × ComparisonTrackedView psi =>
    p.1.path2) hf
  have hrp := congrArg (fun p : ComparisonTrackedView psi × ComparisonTrackedView psi =>
    p.2.path2) hf
  have hlabel := authorizedPostSuppressLeaderSink_labels_eq hpsi l r
  exact ⟨noFive_of_fields _ _ hl hlabel.1 hlp,
    noFive_of_fields _ _ hr hlabel.2 hrp⟩

/-- DISAPPEAR, guarded COMPARE, reset deletion, leader elimination, and
gated WRITE preserve the terminal-control invariant.  This includes all
reset and write branches, without assuming a future writer-free interval. -/
theorem actual_suffix_no_terminal_five (hpsi : psi > 0) (hlarge : 1 < psi)
    (l r : AuthorizedAgentState psi) (hl : NoTerminalFive l.core)
    (hr : NoTerminalFive r.core) :
    let q := actionOneAfterCheckSuffix hpsi l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  have h0 := disappear_no_terminal_five hpsi hlarge l r hl hr
  have h1 := compare_noFive hpsi _ _ h0.1 h0.2
  have h2 := suppress_noFive hpsi _ _ h1.1 h1.2
  exact postSuppress_noFive hpsi _ _ h2.1 h2.2

private theorem preWall_noFive (l r : AuthorizedAgentState psi)
    (hl : NoTerminalFive l.core) (hr : NoTerminalFive r.core) :
    let q := preCheckResetWall l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  unfold preCheckResetWall
  dsimp only
  constructor
  · split
    · exact clear_noFive l.core
    · exact hl
  · split
    · exact clear_noFive r.core
    · exact hr

private theorem sanitize_noFive (hpsi : psi > 0) (u : AuthorizedAgentState psi)
    (hu : NoTerminalFive u.core) :
    NoTerminalFive (sanitizeAuthorizedTerminalEqual hpsi u).core := by
  unfold sanitizeAuthorizedTerminalEqual
  split <;> exact hu

/-- Every ordinary execution establishes the invariant at its actual
pre-CHECK boundary, even from arbitrary old endpoint controls. -/
theorem beforeCheck_no_terminal_five (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let q := singleUseBeforeCheck hpsi kappa l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  let g := generationBeforeMove hpsi kappa l r
  let m := authorizedSingleUseReleaseMove hpsi g.1 g.2
  have hm : NoTerminalFive m.1.core ∧ NoTerminalFive m.2.core := by
    have hc := authorizedSingleUseReleaseMove_core hpsi g.1 g.2
    have hf := singleUseCaptureSigMove_terminal_no_five hpsi g.1.core g.2.core
    rw [← hc] at hf
    constructor
    · intro p hp ha ht
      exact hf.1 p (Fin.ext ht) hp ha
    · intro p hp ha ht
      exact hf.2 p (Fin.ext ht) hp ha
  have hw := preWall_noFive m.1 m.2 hm.1 hm.2
  exact ⟨sanitize_noFive hpsi _ hw.1, sanitize_noFive hpsi _ hw.2⟩

private theorem mark_noFive (u : AuthorizedAgentState psi)
    (hu : NoTerminalFive u.core) : NoTerminalFive (markComparisonForDeletion u).core := by
  unfold markComparisonForDeletion
  split <;> exact hu

private theorem markBirth_noFive (b : Bool) (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hq : NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core) :
    NoTerminalFive (markLeaderBirth b q).1.core ∧
      NoTerminalFive (markLeaderBirth b q).2.core := by
  unfold markLeaderBirth
  split
  · exact ⟨mark_noFive _ hq.1, mark_noFive _ hq.2⟩
  · exact hq

private theorem normalize_noFive (u : AuthorizedAgentState psi)
    (hu : NoTerminalFive u.core) : NoTerminalFive (normalizeDeletion u).core := by
  unfold normalizeDeletion
  split <;> exact hu

private theorem prepare_noFive (hpsi : psi > 0) (u : AuthorizedAgentState psi)
    (hu : NoTerminalFive u.core) : NoTerminalFive (prepareDisposal hpsi u).core := by
  unfold prepareDisposal
  split
  · exact mark_noFive u hu
  · exact hu

private theorem eliminate_noFive (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : NoTerminalFive l.core) (hr : NoTerminalFive r.core) :
    let q := authorizedEliminateSig hpsi l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  change NoTerminalFive (eliminateSig hpsi l.core r.core).1 ∧
    NoTerminalFive (eliminateSig hpsi l.core r.core).2
  unfold eliminateSig
  split
  · split <;> exact ⟨hl, hr⟩
  · exact ⟨hl, hr⟩

attribute [local irreducible] singleUseBeforeCheck actionOneAfterCheckSuffix

private theorem ordinary_noFive (hpsi : psi > 0) (hlarge : 1 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let b := singleUseBeforeCheck hpsi kappa l r
    let c := preserveTossCheck hpsi b.1 b.2
    let out := actionOneAfterCheckSuffix hpsi c.1 c.2
    NoTerminalFive out.1.core ∧ NoTerminalFive out.2.core := by
  let b := singleUseBeforeCheck hpsi kappa l r
  let c := preserveTossCheck hpsi b.1 b.2
  have hb := beforeCheck_no_terminal_five hpsi kappa l r
  have hc := preserveCheck_noFive hpsi b.1 b.2 hb.1 hb.2
  exact actual_suffix_no_terminal_five hpsi hlarge c.1 c.2 hc.1 hc.2

/-- The ordinary branch establishes the invariant from arbitrary old
controls.  Its hypotheses describe the current deletion dispatch only. -/
theorem ordinary_guarded_establishes_no_terminal_five
    (hpsi : psi > 0) (hlarge : 1 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : deletionActive (normalizeDeletion l) = false)
    (hr : deletionActive (normalizeDeletion r) = false) :
    let q := singleUseGuardedAuthorizedTransition hpsi kappa l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  unfold singleUseGuardedAuthorizedTransition
  simp only [hl, hr, Bool.false_eq_true, ↓reduceIte]
  exact markBirth_noFive _ _
    (ordinary_noFive hpsi hlarge kappa (normalizeDeletion l) (normalizeDeletion r))

/-- Priority deletion either retains or deletes an old control.  Combined
with the actual ordinary branch, this proves closure of the authorized
transition for every current register assignment. -/
theorem guarded_preserves_no_terminal_five
    (hpsi : psi > 0) (hlarge : 1 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (hl : NoTerminalFive l.core)
    (hr : NoTerminalFive r.core) :
    let q := singleUseGuardedAuthorizedTransition hpsi kappa l r
    NoTerminalFive q.1.core ∧ NoTerminalFive q.2.core := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := normalize_noFive l hl
  have hr0 := normalize_noFive r hr
  unfold singleUseGuardedAuthorizedTransition
  dsimp only
  split
  · exact eliminate_noFive hpsi l0 r0 hl0 hr0
  · split
    · exact ⟨hl0, hr0⟩
    · exact markBirth_noFive _ _ (ordinary_noFive hpsi hlarge kappa l0 r0)

private theorem bounded_noFive (hpsi : psi > 0) (hlarge : 1 < psi) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) (hl : NoTerminalFive l.erase.core)
    (hr : NoTerminalFive r.erase.core) :
    let q := singleUseGuardedBoundedTransition hpsi kappa l r
    NoTerminalFive q.1.erase.core ∧ NoTerminalFive q.2.erase.core := by
  have h := guarded_preserves_no_terminal_five hpsi hlarge kappa l.erase r.erase hl hr
  have he := erase_singleUseGuardedBoundedTransition hpsi kappa l r
  have hl' := congrArg (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
    NoTerminalFive q.1.core) he
  have hr' := congrArg (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
    NoTerminalFive q.2.core) he
  exact ⟨hl'.mpr h.1, hr'.mpr h.2⟩

private theorem expiry_noFive (tau : Nat) (old out : ExpiringAgentState psi kappa tau)
    (ho : NoTerminalFive out.core.erase.core) :
    NoTerminalFive (deletionPriorityExpireOne tau old out).core.erase.core := by
  unfold deletionPriorityExpireOne
  split
  · exact ho
  · unfold pathExpireOne
    split
    · exact ho
    · split
      · exact noFive_none _ rfl
      · exact ho

private theorem birthSignals_noFive (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau)
    (hq : NoTerminalFive q.1.core.erase.core ∧ NoTerminalFive q.2.core.erase.core) :
    NoTerminalFive (initializeFollowerPairBirthSignals l r q).1.core.erase.core ∧
      NoTerminalFive (initializeFollowerPairBirthSignals l r q).2.core.erase.core := by
  have hf (u : ExpiringAgentState psi kappa tau) (hu : NoTerminalFive u.core.erase.core) :
      NoTerminalFive (clearExpiringLeaderSignal u).core.erase.core := by
    unfold clearExpiringLeaderSignal
    split <;> exact hu
  unfold initializeFollowerPairBirthSignals
  split
  · exact ⟨hf _ hq.1, hf _ hq.2⟩
  · exact hq

/-- The exact finite host preserves absence of terminal five, including
entry disposal, every ordinary suffix, path-only expiry for arbitrary tau,
and post-birth signal initialization.  No additional state or future route
assumption appears in the transition or in this invariant. -/
theorem full_preserves_no_terminal_five
    (hpsi : psi > 0) (hlarge : 1 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : NoTerminalFive l.core.erase.core) (hr : NoTerminalFive r.core.erase.core) :
    let q := singleUseFullTransition hpsi kappa tau l r
    NoTerminalFive q.1.core.erase.core ∧ NoTerminalFive q.2.core.erase.core := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  have hl0 : NoTerminalFive l0.core.erase.core := by
    change NoTerminalFive (prepareBoundedDisposal hpsi l.core).erase.core
    rw [erase_prepareBoundedDisposal]
    exact prepare_noFive hpsi l.core.erase hl
  have hr0 : NoTerminalFive r0.core.erase.core := by
    change NoTerminalFive (prepareBoundedDisposal hpsi r.core).erase.core
    rw [erase_prepareBoundedDisposal]
    exact prepare_noFive hpsi r.core.erase hr
  let q := singleUseGuardedBoundedTransition hpsi kappa l0.core r0.core
  have hq := bounded_noFive hpsi hlarge kappa l0.core r0.core hl0 hr0
  let a : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let b : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  exact birthSignals_noFive l0 r0 _
    ⟨expiry_noFive tau l0 a hq.1, expiry_noFive tau r0 b hq.2⟩

/-- Every finite asynchronous execution preserves the current-state
invariant once it holds.  The schedule is arbitrary, so this is not a
bounded-word regression or a claimed probabilistic time bound. -/
theorem run_preserves_no_terminal_five {n : Nat} (ring : DirectedRing n)
    (hpsi : psi > 0) (hlarge : 1 < psi) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hC : ∀ i, NoTerminalFive (C i).core.erase.core) (word : DetSchedule n) :
    ∀ i, NoTerminalFive
      (runLocalSchedule ring (singleUseFullTransition hpsi kappa tau) C word i).core.erase.core := by
  induction word generalizing C with
  | nil => exact hC
  | cons e rest ih =>
      apply ih
      intro i
      have h := full_preserves_no_terminal_five hpsi hlarge kappa tau
        (C e) (C (ring.rightNeighbor e)) (hC e) (hC (ring.rightNeighbor e))
      unfold localStep
      split
      · exact h.1
      · split
        · exact h.2
        · exact hC i

/-- Empty initial control gives a concrete, unrestricted producer for the
invariant, without imposing equality of source groups or GEN events. -/
theorem empty_control_run_no_terminal_five {n : Nat} (ring : DirectedRing n)
    (hpsi : psi > 0) (hlarge : 1 < psi) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hC : ∀ i, (C i).core.erase.core.path2 = none) (word : DetSchedule n) :
    ∀ i, NoTerminalFive
      (runLocalSchedule ring (singleUseFullTransition hpsi kappa tau) C word i).core.erase.core :=
  run_preserves_no_terminal_five ring hpsi hlarge kappa tau C
    (fun i => noFive_none _ (hC i)) word

#print axioms disappear_no_terminal_five
#print axioms actual_suffix_no_terminal_five
#print axioms beforeCheck_no_terminal_five
#print axioms ordinary_guarded_establishes_no_terminal_five
#print axioms guarded_preserves_no_terminal_five
#print axioms full_preserves_no_terminal_five
#print axioms run_preserves_no_terminal_five
#print axioms empty_control_run_no_terminal_five

end BirthReleaseTerminalInvariant

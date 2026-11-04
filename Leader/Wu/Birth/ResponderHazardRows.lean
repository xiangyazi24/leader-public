import Leader.Wu.Birth.MismatchDisposalProducer
import Leader.Wu.Comparison.HistoryStages

/-! Actual right-path writers for the old action-one host. Path erasure and
GEN assignment are distinguished from comparison-state/permission changes. -/

set_option autoImplicit false

namespace BirthResponderHazardRows

open PPLL PPLLRepair PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLTerminalEqualSupportRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLWallSweepNormalResetContract PPLLCompleteMultiLeaderCleanup
  PPLLComparisonHistory PPLLWriteIncrementGate
  BirthCheckCongestGuardRepair BirthMismatchDisposalProducer

variable {psi : Nat}

def ClearsOrKeeps (old out : PathInfo) : Prop := out = .bot ∨ out = old

theorem ClearsOrKeeps.retains {old out : PathInfo} (h : ClearsOrKeeps old out)
    (hp : out ≠ .bot) : out = old := h.resolve_left hp

theorem ClearsOrKeeps.trans {a b c : PathInfo} (hbc : ClearsOrKeeps b c)
    (hab : ClearsOrKeeps a b) : ClearsOrKeeps a c := by
  rcases hbc with hc | hc
  · exact Or.inl hc
  · rcases hab with hb | hb
    · exact Or.inl (hc.trans hb)
    · exact Or.inr (hc.trans hb)

theorem ppsi_right_path (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (authorizedPPsiLeaderResetProbeWall hpsi l r).2.core.path = r.core.path := by
  let l0 := if l.core.leader = true then { l.core with probe := false } else l.core
  let r0 := if r.core.leader = true ∨ l.core.leader = true ∨ l.core.reset_cmd = true then
    { r.core with probe := false } else r.core
  have hh := congrArg ComparisonTrackedView.path (pPsi_comparisonTracked_frame hpsi l0 r0).2
  change (pPsi hpsi l0 r0).2.path = r.core.path
  exact hh.trans (by dsimp only [r0]; split <;> rfl)

theorem wait_right_path (hpsi : 0 < psi) (kappa : Nat) (l r : AgentState psi) :
    (waitSaturated hpsi kappa l r).2.path = r.path := by
  simp [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry, waitSaturatedReset, waitSaturatedFinish]

theorem gen_start_right_path (hpsi : 0 < psi) (l r : AgentState psi) :
    (genSigSaturatedStart hpsi l r).2.path = r.path := by
  simp [genSigSaturatedStart]

theorem gen_propagate_right_path (hpsi : 0 < psi) (l r : AgentState psi) :
    (genSigSaturatedPropagate hpsi l r).2.path = r.path := by
  unfold genSigSaturatedPropagate
  split <;> rfl

/-- The actual right GEN assignment guard, sampled after WAIT and Start. -/
def rightGenWrite (hpsi : 0 < psi) (kappa : Nat) (l r : AuthorizedAgentState psi) : Bool :=
  let w := waitSaturated hpsi kappa l.core r.core
  let s := genSigSaturatedStart hpsi w.1 w.2
  decide (s.2.label = ⟨psi - 1, by omega⟩ ∧ s.2.state = .produce)

theorem gen_right_path_of_no_write (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (hw : rightGenWrite hpsi kappa l r = false) :
    (authorizedGenSig hpsi kappa l r).2.core.path = r.core.path := by
  let w := waitSaturated hpsi kappa l.core r.core
  let s := genSigSaturatedStart hpsi w.1 w.2
  have hg : ¬ (s.2.label = ⟨psi - 1, by omega⟩ ∧ s.2.state = .produce) := by
    exact of_decide_eq_false hw
  have he : genSigSaturatedEmit hpsi s.1 s.2 = s := by
    simp only [genSigSaturatedEmit, hg, if_false]
  change (genSigSaturatedFinish hpsi
    (genSigSaturatedPropagate hpsi (genSigSaturatedEmit hpsi s.1 s.2).1
      (genSigSaturatedEmit hpsi s.1 s.2).2).1
    (genSigSaturatedPropagate hpsi (genSigSaturatedEmit hpsi s.1 s.2).1
      (genSigSaturatedEmit hpsi s.1 s.2).2).2).2.path = r.core.path
  rw [he]
  change (genSigSaturatedPropagate hpsi s.1 s.2).2.path = r.core.path
  exact (gen_propagate_right_path hpsi s.1 s.2).trans
    ((gen_start_right_path hpsi w.1 w.2).trans (wait_right_path hpsi kappa l.core r.core))

theorem clean_right (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    ClearsOrKeeps r.core.path (authorizedCleanSig hpsi l r).2.core.path :=
  (cleanSig_comparison_frame hpsi l.core r.core).2.1

theorem eliminate_right (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    ClearsOrKeeps r.core.path (authorizedEliminateSig hpsi l r).2.core.path := by
  change ClearsOrKeeps r.core.path (eliminateSig hpsi l.core r.core).2.path
  unfold eliminateSig
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem preclear_right (hpsi : 0 < psi) (l r : AgentState psi) :
    ClearsOrKeeps r.path (sigMoveLeaderPreclear hpsi l r).2.path := by
  change ClearsOrKeeps r.path (clearIfLeader r).path
  unfold clearIfLeader
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem move2_right_path (l r : AgentState psi) :
    (sigMoveStep2 l r).2.path = r.path := by
  unfold sigMoveStep2
  repeat' (first | rfl | split)

private theorem move3_right_path (l r : AgentState psi) :
    (sigMoveStep3 l r).2.path = r.path := by
  unfold sigMoveStep3
  repeat' (first | rfl | split)

private theorem move4_right_path (l r : AgentState psi) :
    (sigMoveStep4 l r).2.path = r.path := by
  unfold sigMoveStep4
  repeat' (first | rfl | split)

private theorem move5_right_path (l r : AgentState psi) :
    (sigMoveStep5 l r).2.path = r.path := by
  unfold sigMoveStep5
  repeat' (first | rfl | split)

attribute [local irreducible] sigMoveStep2 sigMoveStep3 sigMoveStep4 sigMoveStep5

theorem transfers_right_of_present (l r : AgentState psi) (hr : r.path ≠ .bot) :
    (sigMoveTransfers l r).2.path = r.path := by
  have he : sigMoveStep1 l r = (l, r) := by
    cases hlp : l.path <;> cases hrp : r.path <;> simp_all [sigMoveStep1]
  unfold sigMoveTransfers
  rw [move5_right_path, move4_right_path, move3_right_path, move2_right_path, he]

theorem wall_right (l r : AgentState psi) :
    ClearsOrKeeps r.path (comparisonLeaderWall l r).2.path := by
  change ClearsOrKeeps r.path (if r.leader then clearComparisonSignal r else r).path
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem control_right_path (hpsi : 0 < psi) (l r : AgentState psi) :
    (sigMoveControlTail hpsi l r).2.path = r.path := by
  change (sigMoveApplyControl hpsi r).path = r.path
  cases hp : r.path2 <;> simp [sigMoveApplyControl, hp]

theorem reset_right (l r : AuthorizedAgentState psi) :
    ClearsOrKeeps r.core.path (preCheckResetWall l r).2.core.path := by
  change ClearsOrKeeps r.core.path
    (if (l.core.leader = true ∨ l.core.reset_cmd = true) ∨ r.core.reset_cmd = true then
      clearAuthorizedComparison r else r).core.path
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sanitize_right_path (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (sanitizeAuthorizedPair hpsi (l, r)).2.core.path = r.core.path := by
  change (sanitizeAuthorizedTerminalEqual hpsi r).core.path = r.core.path
  unfold sanitizeAuthorizedTerminalEqual
  split <;> rfl

private theorem ready_path (u : AgentState psi) : (checkSigSetReady u).path = u.path := by
  unfold checkSigSetReady
  repeat' (first | rfl | split)

private theorem check_left_path (hpsi : 0 < psi) (u : AgentState psi) :
    (checkSigCheckL hpsi u).path = u.path := by
  unfold checkSigCheckL
  repeat' (first | rfl | split)

private theorem check_right_path (hpsi : 0 < psi) (l r : AgentState psi) :
    (checkSigCheckR hpsi l r).path = r.path := by
  unfold checkSigCheckR
  repeat' (first | rfl | split)

private theorem result_path (u : AgentState psi) : (checkSigSetResult u).path = u.path := by
  simp [checkSigSetResult]

private theorem leader_path (hpsi : 0 < psi) (u : AgentState psi) :
    (checkSigSetLeader hpsi u).path = u.path := by
  unfold checkSigSetLeader
  split <;> rfl

theorem check_right_path_eq (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (congestGuardCheck hpsi l r).2.core.path = r.core.path := by
  unfold congestGuardCheck
  split
  · rfl
  · change (checkSig hpsi l.core r.core).2.path = r.core.path
    change (checkSigSetLeader hpsi
      (checkSigSetResult (checkSigCheckR hpsi
        (checkSigCheckL hpsi (checkSigSetReady l.core)) (checkSigSetReady r.core)))).path = r.core.path
    rw [leader_path, result_path, check_right_path, ready_path]

private theorem disappear_startR_path (hpsi : 0 < psi) (l r : AgentState psi) :
    (disappearStartR hpsi l r).2.path = r.path := by
  unfold disappearStartR
  repeat' (first | rfl | split)

private theorem disappear_startL_path (hpsi : 0 < psi) (l r : AgentState psi) :
    (disappearStartL hpsi l r).2.path = r.path := by
  unfold disappearStartL
  repeat' (first | rfl | split)

private theorem disappear_carry_path (hpsi : 0 < psi) (l r : AgentState psi) :
    (disappearCarry hpsi l r).2.path = r.path := by
  unfold disappearCarry
  repeat' (first | rfl | split)

attribute [local irreducible] disappearStartR disappearStartL disappearCarry

theorem disappear_right_path (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (authorizedDisappear hpsi l r).2.core.path = r.core.path := by
  change (disappear hpsi l.core r.core).2.path = r.core.path
  rw [disappear_eq_staged]
  unfold disappearStaged
  rw [disappear_carry_path, disappear_startL_path, disappear_startR_path]

private theorem cmpReturn_right_path (hpsi : 0 < psi) (l r : AgentState psi) :
    (cmpUpdateReturnPriority hpsi l r).2.path = r.path := by
  unfold cmpUpdateReturnPriority
  repeat' (first | rfl | split)

private theorem cmpUpdate_right_path (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (authorizedCmpUpdate hpsi l r).2.core.path = r.core.path := by
  exact cmpReturn_right_path hpsi _ _

private theorem cmpAction_right_path (hpsi : 0 < psi) (r : AgentState psi) :
    (compareBitUpdateRActionOne hpsi r).path = r.path := by
  cases hp : r.path2 <;> simp [compareBitUpdateRActionOne, hp]

private theorem cmpDispatch_right_path (hpsi : 0 < psi) (l r : AgentState psi) :
    (compareSigDispatchActionOne hpsi l r).2.path = r.path := by
  unfold compareSigDispatchActionOne
  split
  · exact cmpAction_right_path hpsi r
  · exact cmpAction_right_path hpsi r
  · rfl

theorem compare_right_path (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (authorizedCompareSigActionOne hpsi l r).2.core.path = r.core.path := by
  let l0 : AuthorizedAgentState psi :=
    ⟨compareSigInit l.core, normalizePermit (compareSigInit l.core) l.path0Crossed⟩
  change (match l0.core.path with
    | .bot => (l0, r)
    | .some _ _ => match r.core.path with
      | .bot => (l0, r)
      | .some _ _ =>
        let q := authorizedCmpUpdate hpsi l0 r
        let out := compareSigDispatchActionOne hpsi q.1.core q.2.core
        (⟨out.1, normalizePermit out.1 q.1.path0Crossed⟩,
         ⟨out.2, normalizePermit out.2 q.2.path0Crossed⟩)).2.core.path = r.core.path
  split
  · rfl
  · split
    · rfl
    · exact (cmpDispatch_right_path hpsi _ _).trans (cmpUpdate_right_path hpsi l0 r)

private theorem suppress_start_right (l r : AgentState psi) :
    (suppressSigStart l r).2.path = r.path := by
  unfold suppressSigStart
  split <;> rfl

private theorem suppress_move_right (l r : AgentState psi) :
    (suppressSigMoveReset l r).2.path = r.path := by
  unfold suppressSigMoveReset
  split <;> rfl

private theorem suppress_terminal_right (hpsi : 0 < psi) (l r : AgentState psi) :
    (suppressSigTerminal hpsi l r).2.path = r.path := by
  unfold suppressSigTerminal
  split <;> rfl

private theorem suppress_echo_right (l r : AgentState psi) :
    (suppressSigEcho l r).2.path = r.path := by
  unfold suppressSigEcho
  repeat' (first | rfl | split)

private theorem suppress_finish_right (l r : AgentState psi) :
    (suppressSigFinish l r).2.path = r.path := rfl

private theorem reset_kill_right (r : AgentState psi) :
    ClearsOrKeeps r.path (resetKillComparison r).path := by
  unfold resetKillComparison
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

attribute [local irreducible] suppressSigStart suppressSigMoveReset
  suppressSigTerminal suppressSigEcho suppressSigFinish resetKillComparison

theorem suppress_right (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    ClearsOrKeeps r.core.path (authorizedReconcile (suppressSigResetKill hpsi) l r).2.core.path := by
  change ClearsOrKeeps r.core.path (suppressSigResetKill hpsi l.core r.core).2.path
  unfold suppressSigResetKill
  rw [suppress_finish_right, suppress_echo_right, suppress_terminal_right]
  apply ClearsOrKeeps.trans (reset_kill_right _)
  rw [suppress_move_right]
  apply ClearsOrKeeps.trans (reset_kill_right _)
  exact Or.inr (suppress_start_right l.core r.core)

attribute [local irreducible] eliminateLeadersNoCollisionLeaderSink writeSeqIncrementGate

theorem post_right_path (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (authorizedPostSuppressLeaderSink hpsi l r).2.core.path = r.core.path := by
  let q := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
  have hl := (eliminateLeadersNoCollisionLeaderSink_comparisonTracked_frame hpsi l.core r.core).2
  have hw := congrArg Prod.snd (writeSeqIncrementGate_comparisonTracked_pair hpsi q.1 q.2)
  exact congrArg ComparisonTrackedView.path (hw.trans hl)

theorem mark_right_path (born : Bool) (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (markLeaderBirth born q).2.core.path = q.2.core.path := by
  unfold markLeaderBirth
  split
  · change (markComparisonForDeletion q.2).core.path = q.2.core.path
    unfold markComparisonForDeletion
    split <;> rfl
  · rfl

theorem post_right_canonical (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    AuthorizationCanonical (authorizedPostSuppressLeaderSink hpsi l r).2 :=
  (authorizedReconcile_canonical (writeSeqIncrementGate hpsi) _ _).2

theorem mark_right_canonical (born : Bool) (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hc : AuthorizationCanonical q.2) : AuthorizationCanonical (markLeaderBirth born q).2 := by
  unfold markLeaderBirth
  split
  · change AuthorizationCanonical (markComparisonForDeletion q.2)
    unfold markComparisonForDeletion
    split
    · exact hc
    · intro h
      cases h
  · exact hc

/-- Identical numeric payloads can still be a real assignment event. -/
theorem equal_value_emit_is_write (l r : AgentState 2) :
    let old := { r with label := (1 : Fin 2), state := .produce, path := .some 1 0, bit := false }
    old.path ≠ .bot ∧ old.label = (1 : Fin 2) ∧ old.state = .produce ∧
      (genSigSaturatedEmit (by decide) l old).2.path = old.path := by
  simp [genSigSaturatedEmit]

end BirthResponderHazardRows

#print axioms BirthResponderHazardRows.gen_right_path_of_no_write
#print axioms BirthResponderHazardRows.transfers_right_of_present
#print axioms BirthResponderHazardRows.compare_right_path
#print axioms BirthResponderHazardRows.suppress_right
#print axioms BirthResponderHazardRows.post_right_canonical
#print axioms BirthResponderHazardRows.equal_value_emit_is_write

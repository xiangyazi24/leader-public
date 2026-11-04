import Leader.Wu.Comparison.ExpiringK2ProjectionInvariants
import Leader.Wu.Comparison.ExpiringK2ProjectionFinite
import Leader.Wu.Birth.GenerationControlRepair

/-!
# Frozen-host boundary audit and a nontrivial expiring-carrier execution

The audited complete old host is BirthGenerationControlRepair at source SHA256
3c2e2271bd2c5004ad700342b507f51de5e512e15c9b5374cfd6174ab7c353c9.
No new toss/rearm host is imported. The examples distinguish that complete
host from the replacement stage; they are not global birth counterexamples.
-/

namespace ExpiringK2Projection

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthConditionTwoWriteFrames
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
  PPLLNoCheckBirthLeaderFrames PPLLWriteIncrementGate
  K2OutputSafety LDSinkBoundedKernel BirthGenerationControlRepair

set_option autoImplicit false

variable {ψ κ τ : Nat}

def encodeOutput : Bool → LeaderOutput
  | false => .follower
  | true => .leader

/-- The old host's LeaderOutput encoding is exactly the same physical bit
used by the replacement protocol's Bool output. -/
theorem old_output_encoding (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    (expiringProtocol hψ κ τ).output q =
      encodeOutput ((ExpiringK2Projection.protocol hψ κ τ).output q) := by
  cases h : q.core.core.leader <;> simp [expiringProtocol, protocol, encodeOutput, h]

private def observedPair (q : AgentState ψ × AgentState ψ) :
    AgentState 1 × AgentState 1 := (signalView q.1, signalView q.2)

private theorem signal_of_peace {u v : AgentState ψ}
    (h : PeaceView.ofState u = PeaceView.ofState v) :
    signalView u = signalView v :=
  congrArg (fun p : PeaceView ψ => PeaceView.toState
    (ψ := 1) ⟨p.leader, 0, p.shield, p.bullet, p.signal_B⟩) h

private theorem observed_of_peace {q p : AgentState ψ × AgentState ψ}
    (h : peaceViewPair q = peaceViewPair p) : observedPair q = observedPair p :=
  Prod.ext (signal_of_peace (congrArg Prod.fst h))
    (signal_of_peace (congrArg Prod.snd h))

/-- The real suppression stage can erase comparison state and reset count,
but it changes none of the four K2 fields. -/
theorem suppression_observation (hψ : 0 < ψ) (l r : AgentState ψ) :
    (signalView (suppressSigResetKill hψ l r).1,
      signalView (suppressSigResetKill hψ l r).2) =
      (signalView l, signalView r) :=
  observed_of_peace (suppressSigResetKill_peaceViewPair hψ l r)

private theorem resetControl_signal (b : Bool) (u : AgentState ψ) :
    signalView (resetControlOn b u) = signalView u := by
  cases b <;> rfl

private theorem observed_of_fields {q p : AgentState ψ × AgentState ψ}
    (hl : leaderPair q = leaderPair p)
    (hb : bulletFieldPair q = bulletFieldPair p) : observedPair q = observedPair p := by
  have h : ∀ (a b : AgentState ψ), a.leader = b.leader →
      BulletFields.ofState a = BulletFields.ofState b → signalView a = signalView b := by
    intro a b hleader hfields
    have hshield := congrArg BulletFields.shield hfields
    have hbullet := congrArg BulletFields.bullet hfields
    have hsignal := congrArg BulletFields.signal_B hfields
    change a.shield = b.shield at hshield
    change a.bullet = b.bullet at hbullet
    change a.signal_B = b.signal_B at hsignal
    simp only [signalView, hleader, hshield, hbullet, hsignal]
  exact Prod.ext (h _ _ (congrArg Prod.fst hl) (congrArg Prod.fst hb))
    (h _ _ (congrArg Prod.snd hl) (congrArg Prod.snd hb))

/-- The frozen host's new GENSIG writers clear old path2 controls; their
complete WAIT/GEN execution still frames the four K2 fields exactly. -/
theorem generation_observation (hψ : 0 < ψ) (κ : Nat) (l r : AgentState ψ) :
    (signalView (genClean hψ κ l r).1, signalView (genClean hψ κ l r).2) =
      (signalView l, signalView r) := by
  rw [genClean_exact]
  simp only [resetControl_signal]
  exact observed_of_fields (genSigSaturated_leaders hψ κ l r)
    (genSigSaturated_bulletFieldPair hψ κ l r)

/-- Expiry preserves the computed output's signal observation, including
the branch which really deletes stale comparison controls and the permit. -/
theorem path_expiry_observation (old out : ExpiringAgentState ψ κ τ) :
    observeCell (pathExpireOne τ old out) = observeCell out := by
  unfold pathExpireOne
  split
  · rfl
  · split <;> rfl

theorem priority_expiry_observation (old out : ExpiringAgentState ψ κ τ) :
    observeCell (deletionPriorityExpireOne τ old out) = observeCell out := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · exact path_expiry_observation old out

/-- CHECK and the probe prefix frame shield/bullet/signal_B, but their
leader bit is deliberately absent from this conclusion: both can give birth. -/
theorem birth_stage_bullet_frames (hψ : 0 < ψ) (l r : AgentState ψ) :
    bulletFieldPair (pPsiLeaderResetProbeWall hψ l r) = bulletFieldPair (l, r) ∧
      bulletFieldPair (checkSig hψ l r) = bulletFieldPair (l, r) :=
  ⟨pPsiLeaderResetProbeWall_bulletFieldPair hψ l r,
    checkSig_bulletFieldPair hψ l r⟩

/-- WRITE keeps the three bullet fields, but moves a nonzero-label
responder leader. This is a physical migration, not a ghost retagging. -/
theorem write_migration (hψ : 0 < ψ) (l r : AgentState ψ)
    (hr : r.leader = true ∧ r.label ≠ ⟨0, hψ⟩) :
    (writeSeqIncrementGate hψ l r).1.leader = true ∧
    (writeSeqIncrementGate hψ l r).2.leader = false ∧
    bulletFieldPair (writeSeqIncrementGate hψ l r) = bulletFieldPair (l, r) :=
  ⟨writeSeqIncrementGate_initiator_true_of_nonzero_responder_leader hψ l r hr,
    writeSeqIncrementGate_responder_false_of_nonzero_leader hψ l r hr,
    writeSeqIncrementGate_bulletFieldPair hψ l r⟩

namespace Example

theorem ring5 : DirectedRing 5 := ⟨by decide⟩

/-- All non-K2 controls are real stored fields, with stale terminal action 6,
live comparison/cleaning/write payloads, WAIT=true, full count, and permission.
The leader that will be deleted has stall zero on entry and on output. -/
def staleSeed (i : Fin 5) : ExpiringAgentState 2 2 3 :=
  ⟨⟨{ boundedCanonical (ψ := 2) (by decide) 2 i with
    label := 1
    leader := decide (i = 0 ∨ i = 2)
    shield := decide (i = 0)
    signal_B := 0
    bullet := if i = 4 then 2 else 0
    probe := true
    phase := true
    bit := true
    wait := true
    count := 2
    state := .compare2
    path := .some 1 1
    path2 := some ⟨1, 1, 2, 5⟩
    path3 := some ⟨1, 1, 1⟩
    path4 := some (.clean, 1)
    path5 := some (.normal 1, 1)
    p := true
    p_carry := true
    reset := true
    carry := true
    h_field := true
    reset_cmd := true
    echo := true
    write_state := .ready
    write := .increment_group
    last := true
    last_set := true
    last_unset := true
    b_carry := true
    gen_ws := true
    ws_echo := true
    signal_ws := true }, true⟩,
    if i = 2 then 0 else 3⟩

theorem stale_observation :
    observe staleSeed = LabelFreeElimination.observe
      LabelFreeElimination.NondivisibleExample.seed5 := rfl

theorem stale_domain : SignalGlobal ring5 staleSeed ∧ PeacefulGlobal ring5 staleSeed := by
  constructor
  · unfold SignalGlobal
    rw [stale_observation]
    exact LabelFreeElimination.NondivisibleExample.seed5_global
  · unfold PeacefulGlobal
    rw [stale_observation]
    exact K2PeacefulGlobal.seed5_peaceful

theorem stale_deletion :
    ¬ 2 ∣ 5 ∧ count staleSeed = 2 ∧
    count (run (step (by decide) ring5) staleSeed [3, 2]) = 1 ∧
    (run (step (by decide) ring5) staleSeed [3, 2] 2).core.core.leader = false := by
  decide

/-- Kernel evaluation of real stored output controls, not their observation. -/
theorem stale_controls_retained :
    let u := run (step (by decide) ring5) staleSeed [3, 2] 2
    u.core.core.state = .compare2 ∧
    u.core.core.path2 = some ⟨1, 1, 2, 5⟩ ∧
    u.core.core.wait = true ∧ u.core.core.count = 2 ∧
    u.core.path0Crossed = true ∧ u.stall = 0 ∧ u.core.core.label = 1 := by
  decide

/-- A real expiry call would delete this stale comparison and permit.
The replacement K2 row has not quietly inserted such a call. -/
theorem actual_expiry_clears_stale :
    let u := pathExpireOne 3 (staleSeed 2) (staleSeed 2)
    u.core.core.state = .none ∧ u.core.core.path = .bot ∧
    u.core.core.path2 = none ∧ u.core.path0Crossed = false ∧ u.stall = 3 := by
  decide

theorem stale_complete_frame (es : List (Fin 5)) (i : Fin 5) :
    nonK2 (run (step (by decide) ring5) staleSeed es i) = nonK2 (staleSeed i) :=
  run_nonK2 (by decide) ring5 staleSeed es i

/-- A clean, aligned, unexpired pair for the frozen complete-host audit. -/
def hostLeft : ExpiringAgentState 2 2 3 :=
  ⟨⟨{ boundedCanonical (n := 2) (by decide) 2 0 with
    leader := true, label := 0, shield := true, bullet := 0,
    signal_B := 0, wait := true }, false⟩, 3⟩

def hostRight : ExpiringAgentState 2 2 3 :=
  ⟨⟨{ boundedCanonical (n := 2) (by decide) 2 1 with
    leader := false, label := 1, shield := false, bullet := 2,
    signal_B := 0, wait := true }, false⟩, 3⟩

theorem host_pair_clean :
    hostLeft.core.core.state = .none ∧ hostRight.core.core.state = .none ∧
    hostLeft.core.core.path = .bot ∧ hostRight.core.core.path = .bot ∧
    hostLeft.core.core.path2 = none ∧ hostRight.core.core.path2 = none ∧
    hostLeft.core.core.wait = true ∧ hostRight.core.core.wait = true ∧
    hostLeft.core.core.count = 0 ∧ hostRight.core.core.count = 0 ∧
    hostLeft.core.path0Crossed = false ∧ hostRight.core.path0Crossed = false ∧
    hostLeft.stall = 3 ∧ hostRight.stall = 3 := by
  decide

/-- The complete old host retains this protected incoming live bullet;
actual K2 absorbs it. Thus replacing a stage is necessary: the old whole
host is not observation-equivalent to K2, even on this clean aligned pair. -/
theorem complete_old_host_differs :
    (generationFullTransition (by decide) 2 3 hostLeft hostRight).2.core.core.bullet = 2 ∧
    (row (by decide) hostLeft hostRight).2.core.core.bullet = 0 := by
  decide

def probeLeft : ExpiringAgentState 2 2 3 :=
  { hostLeft with core := { hostLeft.core with core :=
    { hostLeft.core.core with leader := false, label := 1, shield := false } } }

def probeRight : ExpiringAgentState 2 2 3 :=
  { hostRight with core := { hostRight.core with core :=
    { hostRight.core.core with probe := true, bullet := 0 } } }

/-- Actual P-prime birth survives all remaining stages of the frozen host.
This only exhibits a surrounding-stage writer; no arbitrary-state progress
or repair counterexample is claimed. -/
theorem complete_old_host_birth :
    probeLeft.core.core.leader = false ∧ probeRight.core.core.leader = false ∧
    (generationFullTransition (by decide) 2 3 probeLeft probeRight).2.core.core.leader = true ∧
    (row (by decide) probeLeft probeRight).2.core.core.leader = false := by
  decide

/-- The entry domain permits nonzero physical leader labels. Consequently
its premises cannot silently justify WRITE's responder-zero frame. -/
theorem domain_allows_write_migration :
    let q := writeSeqIncrementGate (by decide)
      (staleSeed 4).core.core.erase (staleSeed 0).core.core.erase
    q.1.leader = true ∧ q.2.leader = false ∧
      q.1.shield = false ∧ q.1.bullet = 2 := by
  decide

end Example
end ExpiringK2Projection

#print axioms ExpiringK2Projection.generation_observation
#print axioms ExpiringK2Projection.suppression_observation
#print axioms ExpiringK2Projection.priority_expiry_observation
#print axioms ExpiringK2Projection.write_migration
#print axioms ExpiringK2Projection.Example.stale_domain
#print axioms ExpiringK2Projection.Example.stale_deletion
#print axioms ExpiringK2Projection.Example.stale_complete_frame
#print axioms ExpiringK2Projection.Example.complete_old_host_differs
#print axioms ExpiringK2Projection.Example.complete_old_host_birth
#print axioms ExpiringK2Projection.Example.domain_allows_write_migration

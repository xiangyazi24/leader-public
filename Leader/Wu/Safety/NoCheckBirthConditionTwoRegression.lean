import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol

/-!
# Necessary nontrivial-ring boundary for corrected condition 2

The positive finite theorem assumes `1 < n`.  This file proves that the
assumption cannot simply be dropped: on the singleton self-edge, the exact
no-CHECK-birth protocol fires a live bullet, while the inclusive offset-zero
label-successor clause asks label zero to equal label one.

The physical computation is not brute-forced monolithically.  Exact normal-
branch refinement first reduces it to the isolated five-field Algorithm-15
kernel; only that one concrete terminal kernel state is evaluated.
-/

namespace PPLLNoCheckBirthConditionTwoRegression

open PPLL PPLLRepair PPLLFinite PPLLCounterexample
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthRepair PPLLNoCheckBirthPhysicalConditionOne
  PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthConditionTwoGlobal
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol

private def noCheckLoneCore : AgentState 2 :=
  { state2 0 true with signal_B := 1, shield := true }

private theorem noCheckLoneCore_inProtocolDomain :
    noCheckLoneCore.inProtocolDomain 10 := by
  simp [noCheckLoneCore, state2, AgentState.inProtocolDomain]

/-- The paper-safe singleton core in the exact finite no-CHECK-birth carrier;
its authorization bit and zero-width stall timer are explicit physical state. -/
def noCheckLoneConfig : Fin 1 → ExpiringAgentState 2 10 0 := fun _ =>
  ⟨⟨BoundedAgentState.ofDomain noCheckLoneCore
      noCheckLoneCore_inProtocolDomain, false⟩, 0⟩

/-- Its exact packaged successor on the singleton self-edge. -/
def noCheckLoneSuccessor : Fin 1 → ExpiringAgentState 2 10 0 :=
  (noCheckBirthProtocol (by omega) 10 0).step
    ringOne noCheckLoneConfig 0

/-- Erasure of the finite start is exactly the existing paper-safe singleton
configuration used by the source-level small-ring regression. -/
theorem erase_noCheckLoneConfig :
    eraseExpiringConfig noCheckLoneConfig = loneLeaderConfig := by
  funext i
  have hi : i = 0 := by
    apply Fin.ext
    omega
  subst i
  rfl

private theorem noCheckLoneConfig_paperSafe :
    PaperSafeConfig (by omega : 2 > 0) ringOne
      (eraseExpiringConfig noCheckLoneConfig) := by
  rw [erase_noCheckLoneConfig]
  exact loneLeaderConfig_paper_safe

private theorem noCheckLone_noDeletion :
    ¬deletionActive
      (normalizeDeletion (noCheckLoneConfig 0).core.erase) := by
  decide

/-- The isolated kernel's single concrete update fires a live bullet and keeps
its leader, shield, zero absence signal, and physical label.  This is the small
terminal computation remaining after the structural physical refinement. -/
private theorem noCheckLoneKernel_fields :
    let D := noCollisionStep (by omega : 2 > 0) ringOne
      (eraseExpiringConfig noCheckLoneConfig) 0
    (D 0).bullet = 2 ∧ (D 0).leader = true ∧
      (D 0).shield = true ∧ (D 0).signal_B = 0 ∧
      (D 0).label = 0 := by
  decide

/-- Exact normal-branch refinement transfers the isolated-kernel fields to the
actual bounded authorization/timer protocol; no full-transition enumeration is
used. -/
theorem noCheck_lone_successor_fields :
    (eraseExpiringState (noCheckLoneSuccessor 0)).bullet = 2 ∧
      (eraseExpiringState (noCheckLoneSuccessor 0)).leader = true ∧
      (eraseExpiringState (noCheckLoneSuccessor 0)).shield = true ∧
      (eraseExpiringState (noCheckLoneSuccessor 0)).signal_B = 0 ∧
      (eraseExpiringState (noCheckLoneSuccessor 0)).label = 0 := by
  have hv :=
    noCheckBirthProtocol_step_peaceView_eq_noCollisionStep_of_normal
      (by omega : 2 > 0) 10 0 ringOne noCheckLoneConfig
      noCheckLoneConfig_paperSafe 0 noCheckLone_noDeletion
      noCheckLone_noDeletion 0
  have hb := congrArg PeaceView.bullet hv
  have hl := congrArg PeaceView.leader hv
  have hs := congrArg PeaceView.shield hv
  have hg := congrArg PeaceView.signal_B hv
  have ha := congrArg PeaceView.label hv
  exact ⟨hb.trans noCheckLoneKernel_fields.1,
    hl.trans noCheckLoneKernel_fields.2.1,
    hs.trans noCheckLoneKernel_fields.2.2.1,
    hg.trans noCheckLoneKernel_fields.2.2.2.1,
    ha.trans noCheckLoneKernel_fields.2.2.2.2⟩

/-- At `n=1, ψ=2`, the inclusive successor-label clause asks the singleton
label zero to equal its own successor one. -/
theorem noCheck_lone_successor_not_peaceful :
    ¬isPeacefulBullet (by omega : 2 > 0) ringOne
      (eraseExpiringConfig noCheckLoneSuccessor) 0 := by
  intro hp
  obtain ⟨_, d, hd, _, _, _, hlabels⟩ := hp
  have hd0 : d = 0 := by omega
  subst d
  have hl := hlabels 0 (by omega)
  dsimp only at hl
  have hm : (⟨((0 : Fin 1).val + 0) % 1, by omega⟩ : Fin 1) = 0 := by
    apply Fin.ext
    omega
  have hm' : (⟨((0 : Fin 1).val + 0 + 1) % 1, by omega⟩ : Fin 1) = 0 := by
    apply Fin.ext
    omega
  have hmval := congrArg
    (fun x : Fin 1 =>
      (eraseExpiringConfig noCheckLoneSuccessor x).label.val) hm
  have hmval' := congrArg
    (fun x : Fin 1 =>
      (eraseExpiringConfig noCheckLoneSuccessor x).label.val) hm'
  have hzero := noCheck_lone_successor_fields.2.2.2.2
  have hzv := congrArg Fin.val hzero
  have hv := congrArg Fin.val hl
  dsimp only at hmval hmval' hzv hv
  omega

/-- Exact finite condition 2 is false at `n=1`; the positive preservation
theorem therefore has a necessary nontrivial-ring hypothesis. -/
theorem noCheck_lone_successor_not_noNonPeaceful :
    ¬noNonPeacefulBullet (by omega : 2 > 0) ringOne
      (eraseExpiringConfig noCheckLoneSuccessor) := by
  intro h
  apply noCheck_lone_successor_not_peaceful
  exact h 0 noCheck_lone_successor_fields.1

end PPLLNoCheckBirthConditionTwoRegression

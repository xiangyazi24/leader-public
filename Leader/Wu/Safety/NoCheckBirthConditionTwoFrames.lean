import Leader.Wu.Safety.NoCheckBirthConditionTwoGlobal

/-!
# Bullet-field frames outside Algorithm 15

`isPeacefulBullet` depends on shield, bullet, and `signal_B` in addition to
leaders and labels.  Algorithm 15 is their sole writer.  This module proves that
fact compositionally for the repaired source prefix and later wrapper stages;
no appeal is made to comments or metadata.
-/

namespace PPLLNoCheckBirthConditionTwoFrames

open PPLL PPLLRepair PPLLVerify PPLLNoCheckBirthRepair
  PPLLNoCheckBirthLeaderFrames PPLLNoCheckBirthBoundaryFrames
  PPLLAuthorizedComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLTerminalEqualSupportRepair
  PPLLNoCheckBirthPhysicalConditionOne

/-- The three non-geometric fields carried by one peaceful-bullet endpoint. -/
structure BulletFields (ψ : Nat) where
  shield : Bool
  bullet : Fin 3
  signal_B : Fin 2
  deriving DecidableEq

/-- Field projection used by the condition-2 refinement. -/
def BulletFields.ofState (u : AgentState ψ) : BulletFields ψ :=
  ⟨u.shield, u.bullet, u.signal_B⟩

/-- Project both interacting endpoints. -/
def bulletFieldPair (q : AgentState ψ × AgentState ψ) :
    BulletFields ψ × BulletFields ψ :=
  (BulletFields.ofState q.1, BulletFields.ofState q.2)

theorem BulletFields.ext (a b : BulletFields ψ)
    (h1 : a.shield = b.shield) (h2 : a.bullet = b.bullet)
    (h3 : a.signal_B = b.signal_B) : a = b := by
  cases a
  cases b
  simp_all

theorem pPsi_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (pPsi hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState pPsi
    try dsimp only []
    repeat (first | rfl | split)

private theorem waitSaturatedPrepare_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (waitSaturatedPrepare hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState waitSaturatedPrepare
    try dsimp only []
    repeat (first | rfl | split)

private theorem waitSaturatedCarry_bulletFieldPair (hψ : ψ > 0)
    (κ : Nat) (l r : AgentState ψ) :
    bulletFieldPair (waitSaturatedCarry hψ κ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState waitSaturatedCarry
    try dsimp only []
    repeat (first | rfl | split)

private theorem waitSaturatedReset_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (waitSaturatedReset hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState waitSaturatedReset
    try dsimp only []
    repeat (first | rfl | split)

private theorem waitSaturatedFinish_bulletFieldPair (hψ : ψ > 0)
    (κ : Nat) (l r : AgentState ψ) :
    bulletFieldPair (waitSaturatedFinish hψ κ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState waitSaturatedFinish
    try dsimp only []
    repeat (first | rfl | split)

private theorem waitSaturated_bulletFieldPair (hψ : ψ > 0)
    (κ : Nat) (l r : AgentState ψ) :
    bulletFieldPair (waitSaturated hψ κ l r) = bulletFieldPair (l, r) := by
  let q0 := waitSaturatedPrepare hψ l r
  let q1 := waitSaturatedCarry hψ κ q0.1 q0.2
  let q2 := waitSaturatedReset hψ q1.1 q1.2
  exact (waitSaturatedFinish_bulletFieldPair hψ κ q2.1 q2.2).trans
    ((waitSaturatedReset_bulletFieldPair hψ q1.1 q1.2).trans
      ((waitSaturatedCarry_bulletFieldPair hψ κ q0.1 q0.2).trans
        (waitSaturatedPrepare_bulletFieldPair hψ l r)))

private theorem genSigSaturatedStart_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (genSigSaturatedStart hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState genSigSaturatedStart
    try dsimp only []
    repeat (first | rfl | split)

private theorem genSigSaturatedEmit_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (genSigSaturatedEmit hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState genSigSaturatedEmit
    try dsimp only []
    repeat (first | rfl | split)

private theorem genSigSaturatedPropagate_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (genSigSaturatedPropagate hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState genSigSaturatedPropagate
    try dsimp only []
    repeat (first | rfl | split)

private theorem genSigSaturatedFinish_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (genSigSaturatedFinish hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState genSigSaturatedFinish
    try dsimp only []
    repeat (first | rfl | split)

private theorem genSigSaturatedAfterWait_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (genSigSaturatedAfterWait hψ l r) =
      bulletFieldPair (l, r) := by
  let q0 := genSigSaturatedStart hψ l r
  let q1 := genSigSaturatedEmit hψ q0.1 q0.2
  let q2 := genSigSaturatedPropagate hψ q1.1 q1.2
  exact (genSigSaturatedFinish_bulletFieldPair hψ q2.1 q2.2).trans
    ((genSigSaturatedPropagate_bulletFieldPair hψ q1.1 q1.2).trans
      ((genSigSaturatedEmit_bulletFieldPair hψ q0.1 q0.2).trans
        (genSigSaturatedStart_bulletFieldPair hψ l r)))

theorem genSigSaturated_bulletFieldPair (hψ : ψ > 0)
    (κ : Nat) (l r : AgentState ψ) :
    bulletFieldPair (genSigSaturated hψ κ l r) = bulletFieldPair (l, r) := by
  let q := waitSaturated hψ κ l r
  exact (genSigSaturatedAfterWait_bulletFieldPair hψ q.1 q.2).trans
    (waitSaturated_bulletFieldPair hψ κ l r)

private theorem cleanSigGenConnect_bulletFields (u : AgentState ψ) :
    BulletFields.ofState (cleanSigGenConnect u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState cleanSigGenConnect
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigCleanApply_bulletFields (u : AgentState ψ) :
    BulletFields.ofState (cleanSigCleanApply u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState cleanSigCleanApply
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigStep3_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (cleanSigStep3 l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState cleanSigStep3
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigStep4_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (cleanSigStep4 l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState cleanSigStep4
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigStep5_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (cleanSigStep5 hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState cleanSigStep5
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigStep6_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (cleanSigStep6 hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState cleanSigStep6
    try dsimp only []
    repeat (first | rfl | split)

theorem cleanSig_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (cleanSig hψ l r) = bulletFieldPair (l, r) := by
  let q0 := (cleanSigGenConnect l, cleanSigGenConnect r)
  let q1 := cleanSigStep3 q0.1 q0.2
  let q2 := cleanSigStep4 q1.1 q1.2
  let q3 := cleanSigStep5 hψ q2.1 q2.2
  let q4 := cleanSigStep6 hψ q3.1 q3.2
  change bulletFieldPair (cleanSigCleanApply q4.1,
    cleanSigCleanApply q4.2) = bulletFieldPair (l, r)
  have hfinal : bulletFieldPair (cleanSigCleanApply q4.1,
      cleanSigCleanApply q4.2) = bulletFieldPair q4 := by
    apply Prod.ext
    · exact cleanSigCleanApply_bulletFields q4.1
    · exact cleanSigCleanApply_bulletFields q4.2
  exact hfinal.trans ((cleanSigStep6_bulletFieldPair hψ q3.1 q3.2).trans
    ((cleanSigStep5_bulletFieldPair hψ q2.1 q2.2).trans
      ((cleanSigStep4_bulletFieldPair q1.1 q1.2).trans
        ((cleanSigStep3_bulletFieldPair q0.1 q0.2).trans
          (Prod.ext (cleanSigGenConnect_bulletFields l)
            (cleanSigGenConnect_bulletFields r))))))

/-- Algorithm 9 changes only comparison/deletion controls and therefore
frames every bullet field at both endpoints. -/
theorem eliminateSig_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (eliminateSig hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState eliminateSig
    try dsimp only []
    repeat (first | rfl | split)

theorem sigMoveStep1_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (sigMoveStep1 l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState sigMoveStep1
    try dsimp only []
    repeat (first | rfl | split)

theorem sigMoveStep2_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (sigMoveStep2 l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState sigMoveStep2
    try dsimp only []
    repeat (first | rfl | split)

theorem sigMoveStep3_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (sigMoveStep3 l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState sigMoveStep3
    try dsimp only []
    repeat (first | rfl | split)

theorem sigMoveStep4_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (sigMoveStep4 l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState sigMoveStep4
    try dsimp only []
    repeat (first | rfl | split)

theorem sigMoveStep5_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (sigMoveStep5 l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState sigMoveStep5
    try dsimp only []
    repeat (first | rfl | split)

theorem sigMoveApplyControl_bulletFields (hψ : ψ > 0)
    (u : AgentState ψ) :
    BulletFields.ofState (sigMoveApplyControl hψ u) =
      BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState sigMoveApplyControl
    try dsimp only []
    repeat (first | rfl | split)

theorem sigMove_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (sigMove hψ l r) = bulletFieldPair (l, r) := by
  let q0 := sigMoveStep1 l r
  let q1 := sigMoveStep2 q0.1 q0.2
  let q2 := sigMoveStep3 q1.1 q1.2
  let q3 := sigMoveStep4 q2.1 q2.2
  let q4 := sigMoveStep5 q3.1 q3.2
  let q5 := (sigMoveApplyControl hψ q4.1,
    sigMoveApplyControl hψ q4.2)
  let l5 := if q5.2.state = MainState.depart then
    if q5.1.label.val < ψ - 1 ∧ q5.1.state = MainState.CHECK_ready then
      { q5.1 with state := MainState.depart }
    else q5.1
  else q5.1
  let q6 := (l5, q5.2)
  change bulletFieldPair q6 = bulletFieldPair (l, r)
  have hfinal : bulletFieldPair q6 = bulletFieldPair q5 := by
    apply Prod.ext
    · apply BulletFields.ext
      all_goals
        unfold q6 l5 bulletFieldPair BulletFields.ofState
        try dsimp only []
        repeat (first | rfl | split)
    · rfl
  have hcontrol : bulletFieldPair q5 = bulletFieldPair q4 :=
    Prod.ext (sigMoveApplyControl_bulletFields hψ q4.1)
      (sigMoveApplyControl_bulletFields hψ q4.2)
  exact hfinal.trans (hcontrol.trans
    ((sigMoveStep5_bulletFieldPair q3.1 q3.2).trans
      ((sigMoveStep4_bulletFieldPair q2.1 q2.2).trans
        ((sigMoveStep3_bulletFieldPair q1.1 q1.2).trans
          ((sigMoveStep2_bulletFieldPair q0.1 q0.2).trans
            (sigMoveStep1_bulletFieldPair l r))))))

private theorem checkSigSetReady_bulletFields (u : AgentState ψ) :
    BulletFields.ofState (checkSigSetReady u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState checkSigSetReady
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSigCheckL_bulletFields (hψ : ψ > 0)
    (u : AgentState ψ) :
    BulletFields.ofState (checkSigCheckL hψ u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState checkSigCheckL
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSigCheckR_bulletFields (hψ : ψ > 0)
    (l r : AgentState ψ) :
    BulletFields.ofState (checkSigCheckR hψ l r) =
      BulletFields.ofState r := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState checkSigCheckR
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSigSetResult_bulletFields (u : AgentState ψ) :
    BulletFields.ofState (checkSigSetResult u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState checkSigSetResult
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSigSetLeader_bulletFields (hψ : ψ > 0)
    (u : AgentState ψ) :
    BulletFields.ofState (checkSigSetLeader hψ u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState checkSigSetLeader
    try dsimp only []
    repeat (first | rfl | split)

theorem checkSig_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (checkSig hψ l r) = bulletFieldPair (l, r) := by
  let l0 := checkSigSetReady l
  let r0 := checkSigSetReady r
  let l1 := checkSigCheckL hψ l0
  let r1 := checkSigCheckR hψ l1 r0
  let l2 := checkSigSetResult l1
  let r2 := checkSigSetResult r1
  rw [checkSig_eq_staged]
  change bulletFieldPair (l2, checkSigSetLeader hψ r2) =
    bulletFieldPair (l, r)
  exact Prod.ext
    ((checkSigSetResult_bulletFields l1).trans
      ((checkSigCheckL_bulletFields hψ l0).trans
        (checkSigSetReady_bulletFields l)))
    ((checkSigSetLeader_bulletFields hψ r2).trans
      ((checkSigSetResult_bulletFields r1).trans
        ((checkSigCheckR_bulletFields hψ l1 r0).trans
          (checkSigSetReady_bulletFields r))))

private theorem disappearStartR_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (disappearStartR hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState disappearStartR
    try dsimp only []
    repeat (first | rfl | split)

private theorem disappearStartL_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (disappearStartL hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState disappearStartL
    try dsimp only []
    repeat (first | rfl | split)

private theorem disappearCarry_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (disappearCarry hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState disappearCarry
    try dsimp only []
    repeat (first | rfl | split)

theorem disappear_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (disappear hψ l r) = bulletFieldPair (l, r) := by
  let q0 := disappearStartR hψ l r
  let q1 := disappearStartL hψ q0.1 q0.2
  rw [disappear_eq_staged]
  exact (disappearCarry_bulletFieldPair hψ q1.1 q1.2).trans
    ((disappearStartL_bulletFieldPair hψ q0.1 q0.2).trans
      (disappearStartR_bulletFieldPair hψ l r))

private theorem suppressSigStart_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (suppressSigStart l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState suppressSigStart
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigMoveReset_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (suppressSigMoveReset l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState suppressSigMoveReset
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigTerminal_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (suppressSigTerminal hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState suppressSigTerminal
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigEcho_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (suppressSigEcho l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState suppressSigEcho
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigFinish_bulletFieldPair (l r : AgentState ψ) :
    bulletFieldPair (suppressSigFinish l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState suppressSigFinish
    try dsimp only []
    repeat (first | rfl | split)

theorem suppressSig_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (suppressSig hψ l r) = bulletFieldPair (l, r) := by
  let q0 := suppressSigStart l r
  let q1 := suppressSigMoveReset q0.1 q0.2
  let q2 := suppressSigTerminal hψ q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  rw [suppressSig_eq_staged]
  exact (suppressSigFinish_bulletFieldPair q3.1 q3.2).trans
    ((suppressSigEcho_bulletFieldPair q2.1 q2.2).trans
      ((suppressSigTerminal_bulletFieldPair hψ q1.1 q1.2).trans
        ((suppressSigMoveReset_bulletFieldPair q0.1 q0.2).trans
          (suppressSigStart_bulletFieldPair l r))))

set_option maxHeartbeats 2000000 in
/-- The complete source prefix through SIGMOVE frames all three bullet fields
at both endpoints. -/
theorem noCheckBirthCoreBeforeCheck_bulletFieldPair
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    bulletFieldPair (noCheckBirthCoreBeforeCheck hψ κ l r) =
      bulletFieldPair (l, r) := by
  let q0 := pPsi hψ l r
  let q1 := genSigSaturated hψ κ q0.1 q0.2
  let q2 := cleanSig hψ q1.1 q1.2
  let q3 := eliminateSig hψ q2.1 q2.2
  change bulletFieldPair (sigMove hψ q3.1 q3.2) = bulletFieldPair (l, r)
  exact (sigMove_bulletFieldPair hψ q3.1 q3.2).trans
    ((eliminateSig_bulletFieldPair hψ q2.1 q2.2).trans
      ((cleanSig_bulletFieldPair hψ q1.1 q1.2).trans
        ((genSigSaturated_bulletFieldPair hψ κ q0.1 q0.2).trans
          (pPsi_bulletFieldPair hψ l r))))

/-- Project the bullet fields of an authorized pair's physical cores. -/
def authorizedBulletFieldPair
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    BulletFields ψ × BulletFields ψ :=
  bulletFieldPair (q.1.core, q.2.core)

private theorem compareSigInit_bulletFields (u : AgentState ψ) :
    BulletFields.ofState (compareSigInit u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState compareSigInit
    try dsimp only []
    repeat (first | rfl | split)

private theorem cmpUpdateReturnPriority_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (cmpUpdateReturnPriority hψ l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState cmpUpdateReturnPriority
    try dsimp only []
    repeat (first | rfl | split)

private theorem cmpUpdateSetPath2_bulletFields (hψ : ψ > 0)
    (u : AgentState ψ) :
    BulletFields.ofState (cmpUpdateSetPath2 hψ u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState cmpUpdateSetPath2
    try dsimp only []
    repeat (first | rfl | split)

private theorem compareSigDispatch_bulletFieldPair (hψ : ψ > 0)
    (l r : AgentState ψ) :
    bulletFieldPair (compareSigDispatch hψ l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold bulletFieldPair BulletFields.ofState compareSigDispatch compareBit
      compareBitUpdateL compareBitUpdateR
    try dsimp only []
    repeat (first | rfl | split)

private theorem authorizedCmpUpdate_bulletFieldPair (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (authorizedCmpUpdate hψ l r) =
      authorizedBulletFieldPair (l, r) := by
  let allowed := freshComparisonStart hψ l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := MainState.congest }
  else l.core
  let q := cmpUpdateReturnPriority hψ lCore r.core
  change bulletFieldPair (cmpUpdateSetPath2 hψ q.1, q.2) =
    bulletFieldPair (l.core, r.core)
  have hlCore : BulletFields.ofState lCore = BulletFields.ofState l.core := by
    apply BulletFields.ext
    all_goals
      unfold lCore BulletFields.ofState
      try dsimp only []
      repeat (first | rfl | split)
  have hreturn := cmpUpdateReturnPriority_bulletFieldPair hψ lCore r.core
  have hreturnL : BulletFields.ofState q.1 =
      BulletFields.ofState lCore := congrArg Prod.fst hreturn
  have hreturnR : BulletFields.ofState q.2 =
      BulletFields.ofState r.core := congrArg Prod.snd hreturn
  exact Prod.ext
    ((cmpUpdateSetPath2_bulletFields hψ q.1).trans
      (hreturnL.trans hlCore)) hreturnR

/-- Authorized comparison changes only comparison/path controls and permission;
it frames all bullet fields. -/
theorem authorizedCompareSig_bulletFieldPair (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (authorizedCompareSig hψ l r) =
      authorizedBulletFieldPair (l, r) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState ψ :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hl0 : BulletFields.ofState l0.core =
      BulletFields.ofState l.core := compareSigInit_bulletFields l.core
  unfold authorizedCompareSig
  dsimp only
  split
  · exact Prod.ext hl0 rfl
  · split
    · exact Prod.ext hl0 rfl
    · rename_i hpathL hpathR
      let q := authorizedCmpUpdate hψ l0 r
      let out := compareSigDispatch hψ q.1.core q.2.core
      have hq := authorizedCmpUpdate_bulletFieldPair hψ l0 r
      have hout := compareSigDispatch_bulletFieldPair hψ q.1.core q.2.core
      exact hout.trans (hq.trans (Prod.ext hl0 rfl))

/-- Deletion-state normalization frames shield, bullet, and `signal_B`; this
allows arbitrary malformed deletion controls without changing condition 2. -/
theorem normalizeDeletion_bulletFields
    (u : AuthorizedAgentState ψ) :
    BulletFields.ofState (normalizeDeletion u).core =
      BulletFields.ofState u.core := by
  apply BulletFields.ext
  all_goals
    unfold normalizeDeletion BulletFields.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem authorizedBeforeCheck_bulletFieldPair
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (authorizedBeforeCheck hψ κ l r) =
      authorizedBulletFieldPair (l, r) := by
  have hcores := authorizedBeforeCheck_cores_eq hψ κ l r
  have hphysical := congrArg bulletFieldPair hcores
  exact hphysical.trans
    (noCheckBirthCoreBeforeCheck_bulletFieldPair hψ κ l.core r.core)

private theorem sanitizeAuthorizedPair_bulletFieldPair
    (hψ : ψ > 0)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (sanitizeAuthorizedPair hψ q) =
      authorizedBulletFieldPair q := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold sanitizeAuthorizedPair sanitizeAuthorizedTerminalEqual
      authorizedBulletFieldPair bulletFieldPair BulletFields.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem authorizedCheckNoBirth_bulletFieldPair
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (authorizedCheckNoBirth hψ l r) =
      authorizedBulletFieldPair (l, r) := by
  unfold authorizedCheckNoBirth restoreAuthorizedLeader authorizedCheckSig
    authorizedReconcile authorizedBulletFieldPair
  dsimp only
  exact checkSig_bulletFieldPair hψ l.core r.core

private theorem authorizedDisappear_bulletFieldPair
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (authorizedDisappear hψ l r) =
      authorizedBulletFieldPair (l, r) := by
  exact disappear_bulletFieldPair hψ l.core r.core

private theorem authorizedSuppressSig_bulletFieldPair
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair
        (authorizedReconcile (suppressSig hψ) l r) =
      authorizedBulletFieldPair (l, r) := by
  exact suppressSig_bulletFieldPair hψ l.core r.core

/-- Authorized normal prefix stopped immediately before Algorithm 15, now with
all bullet fields exposed. -/
def conditionTwoAuthorizedBeforeEliminate (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  noCheckBirthAuthorizedBeforeEliminate hψ κ l r

attribute [local irreducible]
  authorizedBeforeCheck sanitizeAuthorizedPair authorizedCheckNoBirth
  authorizedDisappear authorizedCompareSig

/-- Every pre-Algorithm-15 authorized stage frames shield, bullet, and
`signal_B` at both endpoints. -/
theorem conditionTwoAuthorizedBeforeEliminate_bulletFieldPair
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair
        (conditionTwoAuthorizedBeforeEliminate hψ κ l r) =
      authorizedBulletFieldPair (l, r) := by
  let q0 := authorizedBeforeCheck hψ κ l r
  let q1 := sanitizeAuthorizedPair hψ q0
  let q2 := authorizedCheckNoBirth hψ q1.1 q1.2
  let q3 := authorizedDisappear hψ q2.1 q2.2
  let q4 := authorizedCompareSig hψ q3.1 q3.2
  change authorizedBulletFieldPair
      (authorizedReconcile (suppressSig hψ) q4.1 q4.2) = _
  exact (authorizedSuppressSig_bulletFieldPair hψ q4.1 q4.2).trans
    ((authorizedCompareSig_bulletFieldPair hψ q3.1 q3.2).trans
      ((authorizedDisappear_bulletFieldPair hψ q2.1 q2.2).trans
        ((authorizedCheckNoBirth_bulletFieldPair hψ q1.1 q1.2).trans
          ((sanitizeAuthorizedPair_bulletFieldPair hψ q0).trans
            (authorizedBeforeCheck_bulletFieldPair hψ κ l r)))))

private def authorizedLabelPair
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) : Fin ψ × Fin ψ :=
  (q.1.core.label, q.2.core.label)

private theorem cmpUpdateReturnPriority_labels (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cmpUpdateReturnPriority hψ l r).1.label = l.label ∧
      (cmpUpdateReturnPriority hψ l r).2.label = r.label := by
  unfold cmpUpdateReturnPriority
  repeat (first | constructor | rfl | split)

private theorem cmpUpdateSetPath2_label (hψ : ψ > 0)
    (u : AgentState ψ) : (cmpUpdateSetPath2 hψ u).label = u.label := by
  unfold cmpUpdateSetPath2
  repeat (first | rfl | split)

private theorem authorizedCmpUpdate_labels (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    authorizedLabelPair (authorizedCmpUpdate hψ l r) =
      authorizedLabelPair (l, r) := by
  let allowed := freshComparisonStart hψ l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := MainState.congest }
  else l.core
  let q := cmpUpdateReturnPriority hψ lCore r.core
  have hreturn := cmpUpdateReturnPriority_labels hψ lCore r.core
  apply Prod.ext
  · exact (cmpUpdateSetPath2_label hψ q.1).trans
      (hreturn.1.trans (by
        unfold lCore
        split <;> rfl))
  · exact hreturn.2

/-- Authorized comparison frames both labels. -/
theorem authorizedCompareSig_labels (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    authorizedLabelPair (authorizedCompareSig hψ l r) =
      authorizedLabelPair (l, r) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState ψ :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hl0 : l0.core.label = l.core.label := by
    unfold l0 lCore compareSigInit
    split <;> rfl
  unfold authorizedCompareSig
  dsimp only
  split
  · exact Prod.ext hl0 rfl
  · split
    · exact Prod.ext hl0 rfl
    · let q := authorizedCmpUpdate hψ l0 r
      let out := compareSigDispatch hψ q.1.core q.2.core
      have hq := authorizedCmpUpdate_labels hψ l0 r
      have hout := compareSigDispatch_labels_eq hψ q.1.core q.2.core
      exact (Prod.ext hout.1 hout.2).trans (hq.trans (Prod.ext hl0 rfl))

/-- The complete authorized pre-Algorithm-15 boundary frames the initiator
label. -/
theorem conditionTwoAuthorizedBeforeEliminate_left_label
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (conditionTwoAuthorizedBeforeEliminate hψ κ l r).1.core.label =
      l.core.label := by
  let q0 := authorizedBeforeCheck hψ κ l r
  let q1 := sanitizeAuthorizedPair hψ q0
  let q2 := authorizedCheckNoBirth hψ q1.1 q1.2
  let q3 := authorizedDisappear hψ q2.1 q2.2
  let q4 := authorizedCompareSig hψ q3.1 q3.2
  have hbefore := authorizedBeforeCheck_cores_eq hψ κ l r
  have hbeforeLabel := congrArg (fun q => q.1.label) hbefore
  have hsourceLabels := noCheckBirthCoreBeforeCheck_labels hψ κ l.core r.core
  have hsourceLeft := congrArg Prod.fst hsourceLabels
  unfold labelPair at hsourceLeft
  dsimp only at hsourceLeft
  have h0 : q0.1.core.label = (pPsi hψ l.core r.core).1.label :=
    hbeforeLabel.trans hsourceLeft
  have h1 : q1.1.core.label = q0.1.core.label := by
    unfold q1 sanitizeAuthorizedPair sanitizeAuthorizedTerminalEqual
    dsimp only
    split <;> rfl
  have h2 : q2.1.core.label = q1.1.core.label := by
    unfold q2 authorizedCheckNoBirth restoreAuthorizedLeader authorizedCheckSig
      authorizedReconcile
    dsimp only
    exact (checkSig_labels_eq hψ q1.1.core q1.2.core).1
  have h3 : q3.1.core.label = q2.1.core.label := by
    unfold q3 authorizedDisappear authorizedReconcile
    exact (disappear_labels_eq hψ q2.1.core q2.2.core).1
  have h4 : q4.1.core.label = q3.1.core.label := by
    unfold q4
    exact congrArg Prod.fst (authorizedCompareSig_labels hψ q3.1 q3.2)
  change (authorizedReconcile (suppressSig hψ) q4.1 q4.2).1.core.label = _
  exact (suppressSig_labels_eq hψ q4.1.core q4.2.core).1.trans
    (h4.trans (h3.trans (h2.trans (h1.trans (h0.trans
      (pPsi_initiator_label_eq hψ l.core r.core))))))

end PPLLNoCheckBirthConditionTwoFrames

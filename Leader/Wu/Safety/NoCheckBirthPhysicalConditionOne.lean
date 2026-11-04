import Leader.Wu.Safety.NoCheckBirthConditionOne

/-!
# Finite physical lift of corrected condition 1

This module lifts the source-level no-CHECK-birth leader accounting through the
actual finite repair transition.  The proof is branch-aware: it covers deletion
normalization and both deletion-priority branches, terminal-equality sanitation,
authorized comparison, Algorithm 15 and gated WRITE, leader-birth marking,
bounded reification, comparison-carrier clearing, and path-stall expiration.

Only the erased `AgentState` configuration is assumed output-safe.  Authorization
bits and stall timers remain arbitrary.  The result is one-step unique-leader
preservation for `noCheckBirthProtocol`; it is not yet preservation of paper
conditions 2--5 or a full closedness/convergence theorem.
-/

namespace PPLLNoCheckBirthPhysicalConditionOne

open PPLL PPLLRepair PPLLVerify PPLLResearchFormulation
  PPLLNoCheckBirthRepair
  PPLLNoCheckBirthLeaderFrames PPLLNoCheckBirthBoundaryFrames
  PPLLNoCheckBirthConditionOne
  PPLLAuthorizedComparisonRepair PPLLCombinedLocalRepair
  PPLLLeaderCreationCleanupRepair PPLLTerminalEqualSupportRepair
  PPLLWriteIncrementGate PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair

private abbrev authorizedCorePair (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    AgentState ψ × AgentState ψ := (q.1.core, q.2.core)

private theorem authorizedReconcile_cores_eq
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) :
    authorizedCorePair (authorizedReconcile f l r) = f l.core r.core := by
  rfl

private theorem authorizedReconcile_left_core
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) :
    (authorizedReconcile f l r).1.core = (f l.core r.core).1 := by
  rfl

private theorem authorizedReconcile_right_core
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) :
    (authorizedReconcile f l r).2.core = (f l.core r.core).2 := by
  rfl

private theorem authorizedPPsi_cores_eq
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedCorePair (authorizedPPsi hψ l r) = pPsi hψ l.core r.core := by
  rfl

private theorem authorizedSigMove_cores_eq
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedCorePair (authorizedSigMove hψ l r) = sigMove hψ l.core r.core := by
  by_cases hm : pathMovedRight l.core r.core
      (sigMove hψ l.core r.core).1 (sigMove hψ l.core r.core).2 = true
  · simp [authorizedSigMove, hm, authorizedCorePair]
  · simp [authorizedSigMove, hm, authorizedCorePair]

private theorem authorizedBeforeCheck_eq_staged
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBeforeCheck hψ κ l r =
      let a0 := authorizedPPsi hψ l r
      let a1 := authorizedGenSig hψ κ a0.1 a0.2
      let a2 := authorizedCleanSig hψ a1.1 a1.2
      let a3 := authorizedEliminateSig hψ a2.1 a2.2
      authorizedSigMove hψ a3.1 a3.2 := by
  rfl

private theorem noCheckBirthCoreBeforeCheck_eq_staged
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    noCheckBirthCoreBeforeCheck hψ κ l r =
      let q0 := pPsi hψ l r
      let q1 := genSigSaturated hψ κ q0.1 q0.2
      let q2 := cleanSig hψ q1.1 q1.2
      let q3 := eliminateSig hψ q2.1 q2.2
      sigMove hψ q3.1 q3.2 := by
  rfl

attribute [local irreducible]
  pPsi genSigSaturated cleanSig eliminateSig sigMove

/-- Erasing executable authorization through the pre-CHECK prefix gives the
factored no-CHECK-birth audit prefix exactly. -/
theorem authorizedBeforeCheck_cores_eq
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedCorePair (authorizedBeforeCheck hψ κ l r) =
      noCheckBirthCoreBeforeCheck hψ κ l.core r.core := by
  rw [authorizedBeforeCheck_eq_staged,
    noCheckBirthCoreBeforeCheck_eq_staged]
  let a0 := authorizedPPsi hψ l r
  let a1 := authorizedGenSig hψ κ a0.1 a0.2
  let a2 := authorizedCleanSig hψ a1.1 a1.2
  let a3 := authorizedEliminateSig hψ a2.1 a2.2
  let q0 := pPsi hψ l.core r.core
  let q1 := genSigSaturated hψ κ q0.1 q0.2
  let q2 := cleanSig hψ q1.1 q1.2
  let q3 := eliminateSig hψ q2.1 q2.2
  have h0 := authorizedPPsi_cores_eq hψ l r
  have h0L : a0.1.core = q0.1 := congrArg Prod.fst h0
  have h0R : a0.2.core = q0.2 := congrArg Prod.snd h0
  have h1L : a1.1.core = q1.1 := by
    change (authorizedReconcile (genSigSaturated hψ κ) a0.1 a0.2).1.core = q1.1
    rw [authorizedReconcile_left_core, h0L, h0R]
  have h1R : a1.2.core = q1.2 := by
    change (authorizedReconcile (genSigSaturated hψ κ) a0.1 a0.2).2.core = q1.2
    rw [authorizedReconcile_right_core, h0L, h0R]
  have h2L : a2.1.core = q2.1 := by
    change (authorizedReconcile (cleanSig hψ) a1.1 a1.2).1.core = q2.1
    rw [authorizedReconcile_left_core, h1L, h1R]
  have h2R : a2.2.core = q2.2 := by
    change (authorizedReconcile (cleanSig hψ) a1.1 a1.2).2.core = q2.2
    rw [authorizedReconcile_right_core, h1L, h1R]
  have h3L : a3.1.core = q3.1 := by
    change (authorizedReconcile (eliminateSig hψ) a2.1 a2.2).1.core = q3.1
    rw [authorizedReconcile_left_core, h2L, h2R]
  have h3R : a3.2.core = q3.2 := by
    change (authorizedReconcile (eliminateSig hψ) a2.1 a2.2).2.core = q3.2
    rw [authorizedReconcile_right_core, h2L, h2R]
  have h4 := authorizedSigMove_cores_eq hψ a3.1 a3.2
  have h4L : (authorizedSigMove hψ a3.1 a3.2).1.core =
      (sigMove hψ q3.1 q3.2).1 := by
    rw [show (authorizedSigMove hψ a3.1 a3.2).1.core =
      (sigMove hψ a3.1.core a3.2.core).1 from congrArg Prod.fst h4,
      h3L, h3R]
  have h4R : (authorizedSigMove hψ a3.1 a3.2).2.core =
      (sigMove hψ q3.1 q3.2).2 := by
    rw [show (authorizedSigMove hψ a3.1 a3.2).2.core =
      (sigMove hψ a3.1.core a3.2.core).2 from congrArg Prod.snd h4,
      h3L, h3R]
  exact Prod.ext h4L h4R

/-- The five endpoint fields needed at the Algorithm-15 boundary. -/
abbrev BoundaryProjection (ψ : Nat) :=
  Bool × Bool × Fin ψ × Bool × Fin 3

/-- Project an audit pair to the exact five fields needed by condition-1
leader accounting at the Algorithm-15 boundary. -/
def boundaryProjection
    (q : AgentState ψ × AgentState ψ) : BoundaryProjection ψ :=
  (q.1.leader, q.2.leader, q.2.label, q.1.shield, q.2.bullet)

/-- Apply the condition-1 boundary projection after erasing authorization. -/
def authorizedBoundaryProjection
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    BoundaryProjection ψ := boundaryProjection (q.1.core, q.2.core)

private theorem boundaryProjection_eq_of_fields
    {q : AgentState ψ × AgentState ψ} {l r : AgentState ψ}
    (hleaders : q.1.leader = l.leader ∧ q.2.leader = r.leader)
    (hrLabel : q.2.label = r.label)
    (hkill : q.1.shield = l.shield ∧ q.2.bullet = r.bullet) :
    boundaryProjection q = boundaryProjection (l, r) := by
  unfold boundaryProjection
  rw [hleaders.1, hleaders.2, hrLabel, hkill.1, hkill.2]

private theorem cmpUpdateReturnPriority_boundary
    (hψ : ψ > 0) (l r : AgentState ψ) :
    boundaryProjection (cmpUpdateReturnPriority hψ l r) =
      boundaryProjection (l, r) := by
  unfold boundaryProjection cmpUpdateReturnPriority
  repeat (first | constructor | rfl | split)

private theorem cmpUpdateSetPath2_left_fields
    (hψ : ψ > 0) (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).leader = l.leader ∧
      (cmpUpdateSetPath2 hψ l).shield = l.shield := by
  unfold cmpUpdateSetPath2
  repeat (first | constructor | rfl | split)

private theorem compareSigDispatch_boundary
    (hψ : ψ > 0) (l r : AgentState ψ) :
    boundaryProjection (compareSigDispatch hψ l r) =
      boundaryProjection (l, r) :=
  boundaryProjection_eq_of_fields
    (compareSigDispatch_leaders_eq hψ l r)
    (compareSigDispatch_labels_eq hψ l r).2
    (compareSigDispatch_kill_fields_eq hψ l r)

private theorem authorizedCmpUpdate_boundary
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedBoundaryProjection (authorizedCmpUpdate hψ l r) =
      authorizedBoundaryProjection (l, r) := by
  let allowed := freshComparisonStart hψ l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := .congest } else l.core
  let q := cmpUpdateReturnPriority hψ lCore r.core
  let lOut := cmpUpdateSetPath2 hψ q.1
  have hlCoreLeader : lCore.leader = l.core.leader := by
    dsimp [lCore]
    split <;> rfl
  have hlCoreShield : lCore.shield = l.core.shield := by
    dsimp [lCore]
    split <;> rfl
  have hq := cmpUpdateReturnPriority_boundary hψ lCore r.core
  have hqLLeader : q.1.leader = lCore.leader :=
    congrArg (fun v => v.1) hq
  have hqRLeader : q.2.leader = r.core.leader :=
    congrArg (fun v => v.2.1) hq
  have hqRLabel : q.2.label = r.core.label :=
    congrArg (fun v => v.2.2.1) hq
  have hqLShield : q.1.shield = lCore.shield :=
    congrArg (fun v => v.2.2.2.1) hq
  have hqRBullet : q.2.bullet = r.core.bullet :=
    congrArg (fun v => v.2.2.2.2) hq
  have hlOut := cmpUpdateSetPath2_left_fields hψ q.1
  change boundaryProjection (lOut, q.2) = boundaryProjection (l.core, r.core)
  apply boundaryProjection_eq_of_fields
  · exact ⟨hlOut.1.trans (hqLLeader.trans hlCoreLeader), hqRLeader⟩
  · exact hqRLabel
  · exact ⟨hlOut.2.trans (hqLShield.trans hlCoreShield), hqRBullet⟩

private theorem compareSigInit_left_fields (l : AgentState ψ) :
    (compareSigInit l).leader = l.leader ∧
      (compareSigInit l).shield = l.shield := by
  unfold compareSigInit
  split <;> exact ⟨rfl, rfl⟩

private theorem authorizedCompareSig_boundary
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedBoundaryProjection (authorizedCompareSig hψ l r) =
      authorizedBoundaryProjection (l, r) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState ψ :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hl0 := compareSigInit_left_fields l.core
  unfold authorizedCompareSig
  dsimp only
  split
  · apply boundaryProjection_eq_of_fields
    · exact ⟨hl0.1, rfl⟩
    · rfl
    · exact ⟨hl0.2, rfl⟩
  · split
    · apply boundaryProjection_eq_of_fields
      · exact ⟨hl0.1, rfl⟩
      · rfl
      · exact ⟨hl0.2, rfl⟩
    · let q := authorizedCmpUpdate hψ l0 r
      let out := compareSigDispatch hψ q.1.core q.2.core
      have hq := authorizedCmpUpdate_boundary hψ l0 r
      have hout := compareSigDispatch_boundary hψ q.1.core q.2.core
      exact hout.trans (hq.trans (by
        apply boundaryProjection_eq_of_fields
        · exact ⟨hl0.1, rfl⟩
        · rfl
        · exact ⟨hl0.2, rfl⟩))

private theorem sanitizeAuthorizedPair_boundary
    (hψ : ψ > 0) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    authorizedBoundaryProjection (sanitizeAuthorizedPair hψ q) =
      authorizedBoundaryProjection q := by
  unfold authorizedBoundaryProjection boundaryProjection sanitizeAuthorizedPair
    sanitizeAuthorizedTerminalEqual
  dsimp only
  repeat (first | constructor | rfl | split)

private theorem authorizedCheckNoBirth_boundary
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedBoundaryProjection (authorizedCheckNoBirth hψ l r) =
      authorizedBoundaryProjection (l, r) := by
  unfold authorizedCheckNoBirth restoreAuthorizedLeader authorizedCheckSig
    authorizedReconcile authorizedBoundaryProjection
  dsimp only
  apply boundaryProjection_eq_of_fields
  · exact ⟨rfl, rfl⟩
  · exact (checkSig_labels_eq hψ l.core r.core).2
  · exact checkSig_kill_fields_eq hψ l.core r.core

private theorem authorizedReconcile_boundary
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ)
    (hframe : boundaryProjection (f l.core r.core) =
      boundaryProjection (l.core, r.core)) :
    authorizedBoundaryProjection (authorizedReconcile f l r) =
      authorizedBoundaryProjection (l, r) := by
  exact hframe

private theorem authorizedDisappear_boundary
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedBoundaryProjection (authorizedDisappear hψ l r) =
      authorizedBoundaryProjection (l, r) := by
  apply authorizedReconcile_boundary
  apply boundaryProjection_eq_of_fields
  · exact disappear_leaders_eq hψ l.core r.core
  · exact (disappear_labels_eq hψ l.core r.core).2
  · exact disappear_kill_fields_eq hψ l.core r.core

private theorem authorizedSuppressSig_boundary
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedBoundaryProjection
        (authorizedReconcile (suppressSig hψ) l r) =
      authorizedBoundaryProjection (l, r) := by
  apply authorizedReconcile_boundary
  apply boundaryProjection_eq_of_fields
  · exact suppressSig_leaders_eq hψ l.core r.core
  · exact (suppressSig_labels_eq hψ l.core r.core).2
  · exact suppressSig_kill_fields_eq hψ l.core r.core

/-- Authorized normal-branch prefix stopped immediately before Algorithm 15. -/
def noCheckBirthAuthorizedBeforeEliminate (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q0 := authorizedBeforeCheck hψ κ l r
  let q1 := sanitizeAuthorizedPair hψ q0
  let q2 := authorizedCheckNoBirth hψ q1.1 q1.2
  let q3 := authorizedDisappear hψ q2.1 q2.2
  let q4 := authorizedCompareSig hψ q3.1 q3.2
  authorizedReconcile (suppressSig hψ) q4.1 q4.2

private theorem noCheckBirthAuthorizedBeforeEliminate_eq_staged
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    noCheckBirthAuthorizedBeforeEliminate hψ κ l r =
      let q0 := authorizedBeforeCheck hψ κ l r
      let q1 := sanitizeAuthorizedPair hψ q0
      let q2 := authorizedCheckNoBirth hψ q1.1 q1.2
      let q3 := authorizedDisappear hψ q2.1 q2.2
      let q4 := authorizedCompareSig hψ q3.1 q3.2
      authorizedReconcile (suppressSig hψ) q4.1 q4.2 := by
  rfl

attribute [local irreducible]
  authorizedBeforeCheck sanitizeAuthorizedPair authorizedCheckNoBirth
  authorizedDisappear authorizedCompareSig

private theorem noCheckBirthAuthorizedBeforeEliminate_boundary_from_beforeCheck
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBoundaryProjection
        (noCheckBirthAuthorizedBeforeEliminate hψ κ l r) =
      authorizedBoundaryProjection (authorizedBeforeCheck hψ κ l r) := by
  rw [noCheckBirthAuthorizedBeforeEliminate_eq_staged]
  let q0 := authorizedBeforeCheck hψ κ l r
  let q1 := sanitizeAuthorizedPair hψ q0
  let q2 := authorizedCheckNoBirth hψ q1.1 q1.2
  let q3 := authorizedDisappear hψ q2.1 q2.2
  let q4 := authorizedCompareSig hψ q3.1 q3.2
  calc
    authorizedBoundaryProjection
        (authorizedReconcile (suppressSig hψ) q4.1 q4.2) =
      authorizedBoundaryProjection q4 :=
        authorizedSuppressSig_boundary hψ q4.1 q4.2
    _ = authorizedBoundaryProjection q3 :=
      authorizedCompareSig_boundary hψ q3.1 q3.2
    _ = authorizedBoundaryProjection q2 :=
      authorizedDisappear_boundary hψ q2.1 q2.2
    _ = authorizedBoundaryProjection q1 :=
      authorizedCheckNoBirth_boundary hψ q1.1 q1.2
    _ = authorizedBoundaryProjection q0 :=
      sanitizeAuthorizedPair_boundary hψ q0

private theorem boundaryProjection_eq
    {q q' : AgentState ψ × AgentState ψ}
    (hll : q.1.leader = q'.1.leader)
    (hrl : q.2.leader = q'.2.leader)
    (hrLabel : q.2.label = q'.2.label)
    (hlShield : q.1.shield = q'.1.shield)
    (hrBullet : q.2.bullet = q'.2.bullet) :
    boundaryProjection q = boundaryProjection q' := by
  unfold boundaryProjection
  rw [hll, hrl, hrLabel, hlShield, hrBullet]

private theorem noCheckBirthSourceBoundary_from_beforeCheck
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    boundaryProjection (noCheckBirthBeforeEliminate hψ κ l r) =
      boundaryProjection (noCheckBirthCoreBeforeCheck hψ κ l r) := by
  have hfullLeaders := noCheckBirthBeforeEliminate_leaders hψ κ l r
  have hpreLeaders := noCheckBirthCoreBeforeCheck_leaders hψ κ l r
  have hfullLabels := noCheckBirthBeforeEliminate_labels hψ κ l r
  have hpreLabels := noCheckBirthCoreBeforeCheck_labels hψ κ l r
  have hfullKill := noCheckBirthBeforeEliminate_kill_fields hψ κ l r
  have hpreKill := noCheckBirthCoreBeforeCheck_kill_fields hψ κ l r
  apply boundaryProjection_eq
  · exact (congrArg Prod.fst hfullLeaders).trans
      (congrArg Prod.fst hpreLeaders).symm
  · exact (congrArg Prod.snd hfullLeaders).trans
      (congrArg Prod.snd hpreLeaders).symm
  · exact (congrArg Prod.snd hfullLabels).trans
      (congrArg Prod.snd hpreLabels).symm
  · exact hfullKill.1.trans hpreKill.1.symm
  · exact hfullKill.2.trans hpreKill.2.symm

/-- The executable authorized pre-Algorithm-15 prefix refines the source-level
five-field boundary projection. -/
theorem noCheckBirthAuthorizedBeforeEliminate_boundary
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBoundaryProjection
        (noCheckBirthAuthorizedBeforeEliminate hψ κ l r) =
      boundaryProjection
        (noCheckBirthBeforeEliminate hψ κ l.core r.core) := by
  have hprefix :=
    noCheckBirthAuthorizedBeforeEliminate_boundary_from_beforeCheck
      hψ κ l r
  have hcore := authorizedBeforeCheck_cores_eq hψ κ l r
  have hsource := noCheckBirthSourceBoundary_from_beforeCheck
    hψ κ l.core r.core
  exact hprefix.trans ((congrArg boundaryProjection hcore).trans hsource.symm)

private theorem normalizeDeletion_core_frame
    (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.leader = u.core.leader ∧
      (normalizeDeletion u).core.label = u.core.label ∧
      (normalizeDeletion u).core.shield = u.core.shield ∧
      (normalizeDeletion u).core.bullet = u.core.bullet := by
  unfold normalizeDeletion
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

attribute [local irreducible] noCheckBirthBeforeEliminate

private theorem pPsi_normalizeDeletion_boundary
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    boundaryProjection
        (pPsi hψ (normalizeDeletion l).core (normalizeDeletion r).core) =
      boundaryProjection (pPsi hψ l.core r.core) := by
  unfold normalizeDeletion
  dsimp only
  repeat split
  all_goals
    unfold boundaryProjection pPsi
    dsimp only
    repeat (first | constructor | rfl | split)

/-- Deletion-state normalization leaves the source-level condition-1 boundary
projection unchanged. -/
theorem noCheckBirthSourceBoundary_normalizeDeletion
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    boundaryProjection
        (noCheckBirthBeforeEliminate hψ κ
          (normalizeDeletion l).core (normalizeDeletion r).core) =
      boundaryProjection
        (noCheckBirthBeforeEliminate hψ κ l.core r.core) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := normalizeDeletion_core_frame l
  have hr0 := normalizeDeletion_core_frame r
  have hp := pPsi_normalizeDeletion_boundary hψ l r
  have hnormLeaders := noCheckBirthBeforeEliminate_leaders
    hψ κ l0.core r0.core
  have horigLeaders := noCheckBirthBeforeEliminate_leaders
    hψ κ l.core r.core
  have hnormLabels := noCheckBirthBeforeEliminate_labels
    hψ κ l0.core r0.core
  have horigLabels := noCheckBirthBeforeEliminate_labels
    hψ κ l.core r.core
  have hnormKill := noCheckBirthBeforeEliminate_kill_fields
    hψ κ l0.core r0.core
  have horigKill := noCheckBirthBeforeEliminate_kill_fields
    hψ κ l.core r.core
  have hnormLL := congrArg Prod.fst hnormLeaders
  have hnormRL := congrArg Prod.snd hnormLeaders
  have horigLL := congrArg Prod.fst horigLeaders
  have horigRL := congrArg Prod.snd horigLeaders
  have hnormRLabel := congrArg Prod.snd hnormLabels
  have horigRLabel := congrArg Prod.snd horigLabels
  unfold leaderPair at hnormLL hnormRL horigLL horigRL
  unfold labelPair at hnormRLabel horigRLabel
  unfold boundaryProjection at hp
  dsimp only at hnormLL hnormRL horigLL horigRL hnormRLabel horigRLabel hp
  apply boundaryProjection_eq
  · exact hnormLL.trans
      ((congrArg (fun v => v.1) hp).trans horigLL.symm)
  · exact hnormRL.trans
      ((congrArg (fun v => v.2.1) hp).trans horigRL.symm)
  · exact hnormRLabel.trans
      ((congrArg (fun v => v.2.2.1) hp).trans horigRLabel.symm)
  · exact hnormKill.1.trans (hl0.2.2.1.trans horigKill.1.symm)
  · exact hnormKill.2.trans (hr0.2.2.2.trans horigKill.2.symm)

/-- Authorized Algorithm-15 and gated-WRITE suffix over an explicit boundary. -/
def noCheckBirthAuthorizedAfterBeforeEliminate (hψ : ψ > 0)
    (q0 : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q1 := authorizedReconcile
    (eliminateLeadersNoCollision hψ) q0.1 q0.2
  authorizedReconcile (writeSeqIncrementGate hψ) q1.1 q1.2

/-- Erasing authorization from Algorithm 15 plus gated WRITE gives the exact
source-level suffix on the supplied boundary. -/
theorem noCheckBirthAuthorizedAfterBeforeEliminate_cores_eq
    (hψ : ψ > 0)
    (q0 : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    authorizedCorePair
        (noCheckBirthAuthorizedAfterBeforeEliminate hψ q0) =
      noCheckBirthCoreAfterBeforeEliminate hψ
        (q0.1.core, q0.2.core) := by
  let q1 := authorizedReconcile
    (eliminateLeadersNoCollision hψ) q0.1 q0.2
  have h1 := authorizedReconcile_cores_eq
    (eliminateLeadersNoCollision hψ) q0.1 q0.2
  have h1L : q1.1.core =
      (eliminateLeadersNoCollision hψ q0.1.core q0.2.core).1 :=
    congrArg Prod.fst h1
  have h1R : q1.2.core =
      (eliminateLeadersNoCollision hψ q0.1.core q0.2.core).2 :=
    congrArg Prod.snd h1
  rw [noCheckBirthCoreAfterBeforeEliminate_eq]
  change authorizedCorePair
      (authorizedReconcile (writeSeqIncrementGate hψ) q1.1 q1.2) = _
  rw [authorizedReconcile_cores_eq, h1L, h1R]

private def authorizedLeaderPair
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) : Bool × Bool :=
  (q.1.core.leader, q.2.core.leader)

private theorem markLeaderBirth_leaders
    (born : Bool)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    authorizedLeaderPair (markLeaderBirth born q) =
      authorizedLeaderPair q := by
  unfold markLeaderBirth markComparisonForDeletion authorizedLeaderPair
  repeat (first | constructor | rfl | split)

/-- The exact normal branch, named so its wrapper layers remain opaque. -/
def noCheckBirthAuthorizedNormal (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let beforeRaw := authorizedBeforeCheck hψ κ l r
  let beforeCheck := sanitizeAuthorizedPair hψ beforeRaw
  let afterCheck := authorizedCheckNoBirth hψ beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l r beforeCheck afterCheck
  markLeaderBirth born
    (combinedAuthorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2)

/-- Factor the normal physical branch at the explicit pre-Algorithm-15
boundary, exposing the suffix used by branch-aware refinements. -/
theorem noCheckBirthAuthorizedNormal_eq_boundarySuffix
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    noCheckBirthAuthorizedNormal hψ κ l r =
      let beforeRaw := authorizedBeforeCheck hψ κ l r
      let beforeCheck := sanitizeAuthorizedPair hψ beforeRaw
      let afterCheck := authorizedCheckNoBirth hψ beforeCheck.1 beforeCheck.2
      let born := leaderBirthBeforeOrAtCheck l r beforeCheck afterCheck
      let boundary := noCheckBirthAuthorizedBeforeEliminate hψ κ l r
      let tail := noCheckBirthAuthorizedAfterBeforeEliminate hψ boundary
      markLeaderBirth born tail := by
  rfl

attribute [local irreducible]
  noCheckBirthAuthorizedNormal noCheckBirthAuthorizedBeforeEliminate
  noCheckBirthAuthorizedAfterBeforeEliminate
  noCheckBirthCoreAfterBeforeEliminate

private theorem noCheckBirthNormal_leaders_eq_coreSuffix
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    let q := noCheckBirthAuthorizedNormal hψ κ l r
    let boundary := noCheckBirthAuthorizedBeforeEliminate hψ κ l r
    leaderPair (q.1.core, q.2.core) =
      leaderPair (noCheckBirthCoreAfterBeforeEliminate hψ
        (boundary.1.core, boundary.2.core)) := by
  rw [noCheckBirthAuthorizedNormal_eq_boundarySuffix]
  let boundary := noCheckBirthAuthorizedBeforeEliminate hψ κ l r
  let tail := noCheckBirthAuthorizedAfterBeforeEliminate hψ boundary
  let beforeRaw := authorizedBeforeCheck hψ κ l r
  let beforeCheck := sanitizeAuthorizedPair hψ beforeRaw
  let afterCheck := authorizedCheckNoBirth hψ beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l r beforeCheck afterCheck
  have hmark := markLeaderBirth_leaders born tail
  have hcores := noCheckBirthAuthorizedAfterBeforeEliminate_cores_eq
    hψ boundary
  have hcoreLeaders := congrArg leaderPair hcores
  unfold authorizedLeaderPair at hmark
  unfold authorizedCorePair leaderPair at hcoreLeaders
  change authorizedLeaderPair (markLeaderBirth born tail) = _
  unfold authorizedLeaderPair
  exact hmark.trans hcoreLeaders

private theorem uniqueLeader_preserved_from_physical_boundary
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C)
    (hsource : NoCheckConditionOneBoundary hψ κ ring C)
    (e : Fin n) (boundary q : AgentState ψ × AgentState ψ)
    (hboundary : boundaryProjection boundary =
      boundaryProjection (noCheckBirthBeforeEliminate hψ κ
        (C e) (C (ring.rightNeighbor e))))
    (hq : leaderPair q = leaderPair
      (noCheckBirthCoreAfterBeforeEliminate hψ boundary)) :
    hasUniqueLeader n (updatePair C e (ring.rightNeighbor e) q) := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  let sourceBoundary := noCheckBirthBeforeEliminate hψ κ l r
  have hb := hboundary
  unfold boundaryProjection at hb
  have hbLL : boundary.1.leader = sourceBoundary.1.leader :=
    congrArg (fun v => v.1) hb
  have hbRL : boundary.2.leader = sourceBoundary.2.leader :=
    congrArg (fun v => v.2.1) hb
  have hbRLabel : boundary.2.label = sourceBoundary.2.label :=
    congrArg (fun v => v.2.2.1) hb
  have hbLShield : boundary.1.shield = sourceBoundary.1.shield :=
    congrArg (fun v => v.2.2.2.1) hb
  have hbRBullet : boundary.2.bullet = sourceBoundary.2.bullet :=
    congrArg (fun v => v.2.2.2.2) hb
  have hsourceLeaders := noCheckBirthBeforeEliminate_leaders hψ κ l r
  have hpre : leaderPair boundary = leaderPair (pPsi hψ l r) :=
    (Prod.ext hbLL hbRL).trans hsourceLeaders
  have hsuffix := noCheckBirthSuffix_origins_of_pPsi_boundary
    hψ l r boundary hpre
  have hpreL := congrArg Prod.fst hpre
  have hpreR := congrArg Prod.snd hpre
  have hqL := congrArg Prod.fst hq
  have hqR := congrArg Prod.snd hq
  unfold leaderPair at hpreL hpreR hqL hqR
  dsimp only at hpreL hpreR hqL hqR
  have horiginL : q.1.leader = true →
      (pPsi hψ l r).1.leader = true ∨
        (pPsi hψ l r).2.leader = true := by
    intro hout
    rw [hqL] at hout
    exact hsuffix.1 hout
  have horiginR : q.2.leader = true →
      (pPsi hψ l r).2.leader = true := by
    intro hout
    rw [hqR] at hout
    exact hsuffix.2 hout
  have hsurviveL : (C e).leader = true → q.1.leader = true := by
    intro hleft
    have hpLeft : (pPsi hψ l r).1.leader = true := by
      rw [pPsi_initiator_leader_eq hψ l r, hleft]
    have hbLeft : boundary.1.leader = true := by
      rw [hpreL]
      exact hpLeft
    have hpeace : ¬(boundary.2.bullet = ⟨2, by omega⟩ ∧
        boundary.1.shield = false) := by
      intro hbad
      apply hsource.initiator_no_kill e hleft
      exact ⟨hbRBullet.symm.trans hbad.1,
        hbLShield.symm.trans hbad.2⟩
    have hs := noCheckBirthCoreAfterBeforeEliminate_initiator_survives
      hψ boundary hbLeft hpeace
    rw [hqL]
    exact hs
  have hsurviveR : (C (ring.rightNeighbor e)).leader = true →
      q.2.leader = true := by
    intro hright
    have hpRight := pPsi_responder_leader_of_true hψ l r hright
    have hbRight : boundary.2.leader = true := by
      rw [hpreR]
      exact hpRight
    have hsourceLabel : sourceBoundary.2.label = r.label :=
      hsource.responder_label e
    have hrLabel := paperSafe_unique_leader_label_zero hψ ring C hSafe
      (ring.rightNeighbor e)
      (by simpa [AgentState.isLeader] using hright)
    have hbLabel : boundary.2.label = ⟨0, hψ⟩ :=
      hbRLabel.trans (hsourceLabel.trans hrLabel)
    have hs := noCheckBirthCoreAfterBeforeEliminate_responder_survives
      hψ boundary hbRight hbLabel
    rw [hqR]
    exact hs
  have hnoMigration : (C e).leader = false →
      (C (ring.rightNeighbor e)).leader = true → q.1.leader = false := by
    intro hleft hright
    have hpLeft : (pPsi hψ l r).1.leader = false := by
      rw [pPsi_initiator_leader_eq hψ l r, hleft]
    have hbLeft : boundary.1.leader = false := by
      rw [hpreL]
      exact hpLeft
    have hsourceLabel : sourceBoundary.2.label = r.label :=
      hsource.responder_label e
    have hrLabel := paperSafe_unique_leader_label_zero hψ ring C hSafe
      (ring.rightNeighbor e)
      (by simpa [AgentState.isLeader] using hright)
    have hbLabel : boundary.2.label = ⟨0, hψ⟩ :=
      hbRLabel.trans (hsourceLabel.trans hrLabel)
    have hn := noCheckBirthCoreAfterBeforeEliminate_no_zero_migration
      hψ boundary hbLeft hbLabel
    rw [hqL]
    exact hn
  exact uniqueLeader_preserved_from_noCheck_local_contracts
    hψ hn2 ring C hSafe e q horiginL horiginR
      hsurviveL hsurviveR hnoMigration

private theorem normalizedPair_leaders
    (l r : AuthorizedAgentState ψ) :
    authorizedLeaderPair (normalizeDeletion l, normalizeDeletion r) =
      leaderPair (l.core, r.core) := by
  have hl := normalizeDeletion_core_frame l
  have hr := normalizeDeletion_core_frame r
  exact Prod.ext hl.1 hr.1

private theorem authorizedReconcile_leaders
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ)
    (hframe : leaderPair (f l.core r.core) =
      leaderPair (l.core, r.core)) :
    authorizedLeaderPair (authorizedReconcile f l r) =
      authorizedLeaderPair (l, r) := by
  have hcores := authorizedReconcile_cores_eq f l r
  have hleaders := congrArg leaderPair hcores
  unfold authorizedCorePair leaderPair at hleaders
  dsimp only at hleaders
  unfold authorizedLeaderPair
  exact hleaders.trans hframe

private theorem authorizedEliminateSig_leaders
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    authorizedLeaderPair (authorizedEliminateSig hψ l r) =
      authorizedLeaderPair (l, r) := by
  apply authorizedReconcile_leaders
  have h := eliminateSig_leaders_eq hψ l.core r.core
  exact Prod.ext h.1 h.2

private theorem noCheckBirthAuthorizedTransition_eq_staged
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    noCheckBirthAuthorizedTransition hψ κ l r =
      let l0 := normalizeDeletion l
      let r0 := normalizeDeletion r
      if deletionActive r0 then
        authorizedEliminateSig hψ l0 r0
      else if deletionActive l0 then
        (l0, r0)
      else
        let beforeRaw := authorizedBeforeCheck hψ κ l0 r0
        let beforeCheck := sanitizeAuthorizedPair hψ beforeRaw
        let afterCheck := authorizedCheckNoBirth hψ
          beforeCheck.1 beforeCheck.2
        let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
        markLeaderBirth born
          (combinedAuthorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2) := by
  rfl

/-- In the responder-deletion branch, the exact authorized transition executes
only Algorithm 9 after deletion-state normalization. -/
theorem noCheckBirthAuthorizedTransition_of_responderDeletion
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r)) :
    noCheckBirthAuthorizedTransition hψ κ l r =
      authorizedEliminateSig hψ (normalizeDeletion l) (normalizeDeletion r) := by
  rw [noCheckBirthAuthorizedTransition_eq_staged]
  simp only [hr, if_true]

/-- If only the initiator carries an active deletion, priority semantics waits
and returns the normalized pair unchanged. -/
theorem noCheckBirthAuthorizedTransition_of_initiatorDeletion
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : ¬deletionActive (normalizeDeletion r))
    (hl : deletionActive (normalizeDeletion l)) :
    noCheckBirthAuthorizedTransition hψ κ l r =
      (normalizeDeletion l, normalizeDeletion r) := by
  rw [noCheckBirthAuthorizedTransition_eq_staged]
  simp [hr, hl]

/-- With no active deletion at either normalized endpoint, the exact
transition is the named normal branch used by the physical refinement. -/
theorem noCheckBirthAuthorizedTransition_of_normal
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : ¬deletionActive (normalizeDeletion r))
    (hl : ¬deletionActive (normalizeDeletion l)) :
    noCheckBirthAuthorizedTransition hψ κ l r =
      noCheckBirthAuthorizedNormal hψ κ
        (normalizeDeletion l) (normalizeDeletion r) := by
  rw [noCheckBirthAuthorizedTransition_eq_staged]
  simp [hr, hl]
  symm
  rw [noCheckBirthAuthorizedNormal]

private theorem uniqueLeader_preserved_of_pair_leaders_eq_input
    (hψ : ψ > 0) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C) (e : Fin n)
    (q : AgentState ψ × AgentState ψ)
    (hq : leaderPair q =
      leaderPair (C e, C (ring.rightNeighbor e))) :
    hasUniqueLeader n (updatePair C e (ring.rightNeighbor e) q) := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  have hqL := congrArg Prod.fst hq
  have hqR := congrArg Prod.snd hq
  unfold leaderPair at hqL hqR
  dsimp only at hqL hqR
  have horiginL : q.1.leader = true →
      (pPsi hψ l r).1.leader = true ∨
        (pPsi hψ l r).2.leader = true := by
    intro hout
    left
    rw [pPsi_initiator_leader_eq hψ l r, ← hqL]
    exact hout
  have horiginR : q.2.leader = true →
      (pPsi hψ l r).2.leader = true := by
    intro hout
    apply pPsi_responder_leader_of_true hψ l r
    rw [← hqR]
    exact hout
  have hsurviveL : (C e).leader = true → q.1.leader = true := by
    intro hleft
    rw [hqL]
    exact hleft
  have hsurviveR : (C (ring.rightNeighbor e)).leader = true →
      q.2.leader = true := by
    intro hright
    rw [hqR]
    exact hright
  have hnoMigration : (C e).leader = false →
      (C (ring.rightNeighbor e)).leader = true → q.1.leader = false := by
    intro hleft _
    rw [hqL]
    exact hleft
  exact uniqueLeader_preserved_from_noCheck_local_contracts
    hψ hn2 ring C hSafe e q horiginL horiginR
      hsurviveL hsurviveR hnoMigration

private theorem uniqueLeader_preserved_noCheckBirthAuthorizedTransition
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C)
    (hsource : NoCheckConditionOneBoundary hψ κ ring C)
    (e : Fin n) (permitL permitR : Bool) :
    let l : AuthorizedAgentState ψ := ⟨C e, permitL⟩
    let r : AuthorizedAgentState ψ :=
      ⟨C (ring.rightNeighbor e), permitR⟩
    let q := noCheckBirthAuthorizedTransition hψ κ l r
    hasUniqueLeader n (updatePair C e (ring.rightNeighbor e)
      (q.1.core, q.2.core)) := by
  let l : AuthorizedAgentState ψ := ⟨C e, permitL⟩
  let r : AuthorizedAgentState ψ :=
    ⟨C (ring.rightNeighbor e), permitR⟩
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  change hasUniqueLeader n (updatePair C e (ring.rightNeighbor e)
    ((noCheckBirthAuthorizedTransition hψ κ l r).1.core,
      (noCheckBirthAuthorizedTransition hψ κ l r).2.core))
  by_cases hr : deletionActive r0
  · rw [noCheckBirthAuthorizedTransition_of_responderDeletion
      hψ κ l r hr]
    apply uniqueLeader_preserved_of_pair_leaders_eq_input
      hψ hn2 ring C hSafe e
    have helim := authorizedEliminateSig_leaders hψ l0 r0
    have hnorm := normalizedPair_leaders l r
    change authorizedLeaderPair
        (authorizedEliminateSig hψ l0 r0) =
      leaderPair (l.core, r.core)
    exact helim.trans hnorm
  · by_cases hl : deletionActive l0
    · rw [noCheckBirthAuthorizedTransition_of_initiatorDeletion
        hψ κ l r hr hl]
      apply uniqueLeader_preserved_of_pair_leaders_eq_input
        hψ hn2 ring C hSafe e
      exact normalizedPair_leaders l r
    · rw [noCheckBirthAuthorizedTransition_of_normal hψ κ l r hr hl]
      let boundary := noCheckBirthAuthorizedBeforeEliminate hψ κ l0 r0
      have hphysical := noCheckBirthAuthorizedBeforeEliminate_boundary
        hψ κ l0 r0
      have hnormalize := noCheckBirthSourceBoundary_normalizeDeletion
        hψ κ l r
      have hboundary : boundaryProjection
          (boundary.1.core, boundary.2.core) =
        boundaryProjection (noCheckBirthBeforeEliminate hψ κ
          (C e) (C (ring.rightNeighbor e))) := by
        exact hphysical.trans hnormalize
      have hq := noCheckBirthNormal_leaders_eq_coreSuffix hψ κ l0 r0
      exact uniqueLeader_preserved_from_physical_boundary
        hψ κ hn2 ring C hSafe hsource e
        (boundary.1.core, boundary.2.core)
        ((noCheckBirthAuthorizedNormal hψ κ l0 r0).1.core,
          (noCheckBirthAuthorizedNormal hψ κ l0 r0).2.core)
        hboundary hq

/-- Erase every finite authorization, bounding, and timer wrapper. -/
def eraseExpiringState
    (s : ExpiringAgentState ψ κ τ) : AgentState ψ :=
  s.core.erase.core

/-- Pointwise erasure of a finite physical configuration. -/
def eraseExpiringConfig
    (C : Fin n → ExpiringAgentState ψ κ τ) : Fin n → AgentState ψ :=
  fun i => eraseExpiringState (C i)

private def eraseExpiringPair
    (q : ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ) :
    AgentState ψ × AgentState ψ :=
  (eraseExpiringState q.1, eraseExpiringState q.2)

private theorem deletionPriorityExpireOne_leader
    (τ : Nat) (old out : ExpiringAgentState ψ κ τ) :
    (eraseExpiringState (deletionPriorityExpireOne τ old out)).leader =
      (eraseExpiringState out).leader := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · unfold pathExpireOne
    split
    · rfl
    · split
      · unfold clearComparisonCarrier eraseExpiringState
        rfl
      · rfl

private theorem noCheckBirthPathStallTransition_leaders
    (hψ : ψ > 0) (κ τ : Nat)
    (l r : ExpiringAgentState ψ κ τ) :
    leaderPair (eraseExpiringPair
        (noCheckBirthPathStallTransition hψ κ τ l r)) =
      authorizedLeaderPair
        (noCheckBirthAuthorizedTransition hψ κ
          l.core.erase r.core.erase) := by
  let q := noCheckBirthBoundedTransition hψ κ l.core r.core
  let lOut : ExpiringAgentState ψ κ τ := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState ψ κ τ := ⟨q.2, r.stall⟩
  have hleft := deletionPriorityExpireOne_leader τ l lOut
  have hright := deletionPriorityExpireOne_leader τ r rOut
  have herase := erase_noCheckBirthBoundedTransition hψ κ l.core r.core
  have hleaders := congrArg authorizedLeaderPair herase
  have hexpire : leaderPair (eraseExpiringPair
        (noCheckBirthPathStallTransition hψ κ τ l r)) =
      authorizedLeaderPair (q.1.erase, q.2.erase) := by
    unfold eraseExpiringPair leaderPair authorizedLeaderPair
      noCheckBirthPathStallTransition
    dsimp only
    exact Prod.ext hleft hright
  exact hexpire.trans hleaders

private theorem hasUniqueLeader_of_leader_eq
    {C D : Fin n → AgentState ψ}
    (hleader : ∀ i, (D i).leader = (C i).leader)
    (hunique : hasUniqueLeader n C) : hasUniqueLeader n D := by
  obtain ⟨leaderPos, hleaderPos, honly⟩ := hunique
  refine ⟨leaderPos, ?_, ?_⟩
  · simpa [AgentState.isLeader, hleader leaderPos] using hleaderPos
  · intro i hi
    apply honly i
    simpa [AgentState.isLeader, hleader i] using hi

private theorem updatePair_leaders_eq_of_pair
    (C : Fin n → AgentState ψ) (i j : Fin n)
    (q q' : AgentState ψ × AgentState ψ)
    (hq : leaderPair q' = leaderPair q) :
    ∀ k, (updatePair C i j q' k).leader =
      (updatePair C i j q k).leader := by
  have hleft := congrArg Prod.fst hq
  have hright := congrArg Prod.snd hq
  unfold leaderPair at hleft hright
  dsimp only at hleft hright
  intro k
  simp only [updatePair]
  split
  · exact hleft
  · split
    · exact hright
    · rfl

private theorem eraseExpiringConfig_protocol_step
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n) :
    eraseExpiringConfig
        ((noCheckBirthProtocol hψ κ τ).step ring C e) =
      updatePair (eraseExpiringConfig C) e (ring.rightNeighbor e)
        (eraseExpiringPair
          (noCheckBirthPathStallTransition hψ κ τ
            (C e) (C (ring.rightNeighbor e)))) := by
  funext k
  by_cases hke : k = e
  · simp [PopulationProtocol.step, noCheckBirthProtocol, updatePair,
      eraseExpiringConfig, eraseExpiringPair, hke]
  · by_cases hkr : k = ring.rightNeighbor e
    · have hre : ring.rightNeighbor e ≠ e := by
        intro hre
        apply hke
        exact hkr.trans hre
      simp [PopulationProtocol.step, noCheckBirthProtocol, updatePair,
        eraseExpiringConfig, eraseExpiringPair, hkr, hre]
    · simp [PopulationProtocol.step, noCheckBirthProtocol, updatePair,
        eraseExpiringConfig, hke, hkr]

/-- **Finite physical corrected condition 1.**  From an output-safe erased
configuration, one exact step of the bounded authorization/deletion/timer
protocol preserves exactly one leader, for arbitrary authorization bits and
stall timers. -/
theorem uniqueLeader_preserved_noCheckBirthProtocol
    (hψ : ψ > 0) (κ τ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hSafe : OutputSafeConfig hψ ring (eraseExpiringConfig C))
    (e : Fin n) :
    hasUniqueLeader n (eraseExpiringConfig
      ((noCheckBirthProtocol hψ κ τ).step ring C e)) := by
  let raw := eraseExpiringConfig C
  let l := C e
  let r := C (ring.rightNeighbor e)
  let auditOut := noCheckBirthAuthorizedTransition hψ κ
    l.core.erase r.core.erase
  let physicalOut := noCheckBirthPathStallTransition hψ κ τ l r
  have hpeace := noCheckPeaceBoundary_of_paperSafe
    hψ κ ring raw hSafe
  have hsource := noCheckConditionOneBoundary_of_peace
    hψ κ ring raw hSafe hpeace
  have haudit := uniqueLeader_preserved_noCheckBirthAuthorizedTransition
    hψ κ hn2 ring raw hSafe hsource e
      l.core.path0Crossed r.core.path0Crossed
  have hpair := noCheckBirthPathStallTransition_leaders
    hψ κ τ l r
  have hpairRaw : leaderPair (eraseExpiringPair physicalOut) =
      leaderPair (auditOut.1.core, auditOut.2.core) := by
    exact hpair
  have hphysical : hasUniqueLeader n
      (updatePair raw e (ring.rightNeighbor e)
        (eraseExpiringPair physicalOut)) :=
    hasUniqueLeader_of_leader_eq
      (updatePair_leaders_eq_of_pair raw e (ring.rightNeighbor e)
        (auditOut.1.core, auditOut.2.core)
        (eraseExpiringPair physicalOut) hpairRaw)
      haudit
  rw [eraseExpiringConfig_protocol_step hψ κ τ ring C e]
  exact hphysical

/-- Protocol-output form of finite corrected condition 1.  The actual packaged
finite transition has exactly one endpoint emitting `LeaderOutput.leader`. -/
theorem uniqueLeaderOutput_preserved_noCheckBirthProtocol
    (hψ : ψ > 0) (κ τ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hSafe : OutputSafeConfig hψ ring (eraseExpiringConfig C))
    (e : Fin n) :
    UniqueLeaderOutput (noCheckBirthProtocol hψ κ τ) n
      ((noCheckBirthProtocol hψ κ τ).step ring C e) isLeaderOutput := by
  have hunique := uniqueLeader_preserved_noCheckBirthProtocol
    hψ κ τ hn2 ring C hSafe e
  obtain ⟨leaderPos, hleader, honly⟩ := hunique
  refine ⟨leaderPos, ?_, ?_⟩
  · change isLeaderOutput
      (if (eraseExpiringState
        ((noCheckBirthProtocol hψ κ τ).step ring C e leaderPos)).leader
        then LeaderOutput.leader else LeaderOutput.follower) = true
    change (eraseExpiringState
      ((noCheckBirthProtocol hψ κ τ).step ring C e leaderPos)).leader = true
      at hleader
    simp [hleader, isLeaderOutput]
  · intro i hi
    apply honly i
    change isLeaderOutput
      (if (eraseExpiringState
        ((noCheckBirthProtocol hψ κ τ).step ring C e i)).leader
        then LeaderOutput.leader else LeaderOutput.follower) = true at hi
    change (eraseExpiringState
      ((noCheckBirthProtocol hψ κ τ).step ring C e i)).leader = true
    cases h : (eraseExpiringState
        ((noCheckBirthProtocol hψ κ τ).step ring C e i)).leader
    · simp [h, isLeaderOutput] at hi
    · rfl

end PPLLNoCheckBirthPhysicalConditionOne

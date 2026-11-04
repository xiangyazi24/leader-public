import Leader.Wu.WallSweep.FiniteCleanup
import Leader.Wu.Comparison.HistoryIntegrated
import Leader.Wu.Safety.NoCheckBirthConditionTwoWriteFrames
import Leader.Wu.Safety.NoCheckBirthConditionTwoKernel
import Leader.Wu.Safety.NoCheckBirthConditionTwoPhysical
import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol
import Leader.Wu.WallSweep.StageFrames

/-!
# Ordinary wall-sweep reset contract

The reset sweep is established for the isolated repaired Algorithm 14.  This
module transports that local result through the ordinary, priority-open suffix
of the finite wall transition.  The WRITE proof is deliberately split between
the existing four-field comparison-history view and the five additional fields
needed by the cleanup handoff; no complete Algorithms 16--20 term is unfolded.
-/

namespace PPLLWallSweepNormalResetContract

variable {psi kappa tau : Nat}

open PPLL PPLLRepair PPLLComparisonHistory PPLLWriteIncrementGate
  PPLLAuthorizedComparisonRepair PPLLVerify PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLTerminalEqualSupportRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepEchoDrain PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthBoundaryFrames PPLLNoCheckBirthConditionTwoKernel
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoWriteFrames
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol

/-! ## Finite `PeaceView` wrapper -/

/-- Deletion-priority refresh and path-stall expiration only alter comparison
and timer fields, so the five Algorithm-15 fields equal the bounded base
output exactly. -/
theorem deletionPriorityExpireOne_peaceView_frame
    (old out : ExpiringAgentState psi kappa tau) :
    PeaceView.ofState
        (deletionPriorityExpireOne tau old out).core.erase.core =
      PeaceView.ofState out.core.erase.core := by
  apply PeaceView.ext
  all_goals
    unfold deletionPriorityExpireOne pathExpireOne clearComparisonCarrier
      PeaceView.ofState AuthorizedBoundedAgentState.erase
      BoundedAgentState.erase
    try dsimp only []
    repeat (first | rfl | split)

/-- Exact bounded reification and outer expiration are transparent on
`PeaceView`; all remaining full-wall reasoning may stay at the authorized
transition. -/
theorem wallSweepPathStall_peaceView_eq_authorized
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    (PeaceView.ofState q.1.core.erase.core,
      PeaceView.ofState q.2.core.erase.core) =
      authorizedPeaceViewPair
        (wallSweepAuthorizedTransition hpsi kappa
          l.core.erase r.core.erase) := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hl := deletionPriorityExpireOne_peaceView_frame l lBase
  have hr := deletionPriorityExpireOne_peaceView_frame r rBase
  have he := erase_wallSweepBoundedTransition hpsi kappa l.core r.core
  change
    (PeaceView.ofState
        (deletionPriorityExpireOne tau l lBase).core.erase.core,
      PeaceView.ofState
        (deletionPriorityExpireOne tau r rBase).core.erase.core) = _
  calc
    _ = (PeaceView.ofState bounded.1.erase.core,
        PeaceView.ofState bounded.2.erase.core) := Prod.ext hl hr
    _ = authorizedPeaceViewPair (bounded.1.erase, bounded.2.erase) := rfl
    _ = authorizedPeaceViewPair
        (wallSweepAuthorizedTransition hpsi kappa
          l.core.erase r.core.erase) :=
      congrArg authorizedPeaceViewPair he

def PeaceViewConfigFrame
    (C D : Fin n → ExpiringAgentState psi kappa tau) : Prop :=
  ∀ i, PeaceView.ofState (D i).core.erase.core =
    PeaceView.ofState (C i).core.erase.core

theorem PeaceViewConfigFrame.refl
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    PeaceViewConfigFrame C C := fun _ => rfl

theorem PeaceViewConfigFrame.trans
    {A B C : Fin n → ExpiringAgentState psi kappa tau}
    (hAB : PeaceViewConfigFrame A B) (hBC : PeaceViewConfigFrame B C) :
    PeaceViewConfigFrame A C := fun i => (hBC i).trans (hAB i)

/-- Reconstruct a `PeaceView` pair equality from the three factored physical
projections.  Keeping this adapter public avoids repeated record-field
expansion in edge-local repair proofs. -/
theorem peaceViewPair_eq_of_frames
    {a b : AgentState psi × AgentState psi}
    (hleaders : leaderPair a = leaderPair b)
    (hlabels : labelPair a = labelPair b)
    (hbullets : bulletFieldPair a = bulletFieldPair b) :
    peaceViewPair a = peaceViewPair b := by
  have hleaderL := congrArg Prod.fst hleaders
  have hleaderR := congrArg Prod.snd hleaders
  have hlabelL := congrArg Prod.fst hlabels
  have hlabelR := congrArg Prod.snd hlabels
  have hbulletL := congrArg Prod.fst hbullets
  have hbulletR := congrArg Prod.snd hbullets
  apply Prod.ext <;> apply PeaceView.ext
  · exact hleaderL
  · exact hlabelL
  · exact congrArg BulletFields.shield hbulletL
  · exact congrArg BulletFields.bullet hbulletL
  · exact congrArg BulletFields.signal_B hbulletL
  · exact hleaderR
  · exact hlabelR
  · exact congrArg BulletFields.shield hbulletR
  · exact congrArg BulletFields.bullet hbulletR
  · exact congrArg BulletFields.signal_B hbulletR

private theorem genSigSaturated_peaceViewPair
    (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    peaceViewPair (genSigSaturated hpsi kappa l r) =
      peaceViewPair (l, r) :=
  peaceViewPair_eq_of_frames
    (genSigSaturated_leaders hpsi kappa l r)
    (genSigSaturated_labels hpsi kappa l r)
    (genSigSaturated_bulletFieldPair hpsi kappa l r)

private theorem cleanSig_peaceViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
  peaceViewPair (cleanSig hpsi l r) = peaceViewPair (l, r) :=
  peaceViewPair_eq_of_frames
    (Prod.ext (PPLLVerify.cleanSig_leaders_eq hpsi l r).1
      (PPLLVerify.cleanSig_leaders_eq hpsi l r).2)
    (Prod.ext (PPLLVerify.cleanSig_labels_eq hpsi l r).1
      (PPLLVerify.cleanSig_labels_eq hpsi l r).2)
    (cleanSig_bulletFieldPair hpsi l r)

private theorem eliminateSig_peaceViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
  peaceViewPair (eliminateSig hpsi l r) = peaceViewPair (l, r) :=
  peaceViewPair_eq_of_frames
    (Prod.ext (PPLLVerify.eliminateSig_leaders_eq hpsi l r).1
      (PPLLVerify.eliminateSig_leaders_eq hpsi l r).2)
    (Prod.ext (PPLLVerify.eliminateSig_labels_eq hpsi l r).1
      (PPLLVerify.eliminateSig_labels_eq hpsi l r).2)
    (eliminateSig_bulletFieldPair hpsi l r)

private theorem disappear_peaceViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
  peaceViewPair (disappear hpsi l r) = peaceViewPair (l, r) :=
  peaceViewPair_eq_of_frames
    (Prod.ext (PPLLVerify.disappear_leaders_eq hpsi l r).1
      (PPLLVerify.disappear_leaders_eq hpsi l r).2)
    (Prod.ext (PPLLVerify.disappear_labels_eq hpsi l r).1
    (PPLLVerify.disappear_labels_eq hpsi l r).2)
    (disappear_bulletFieldPair hpsi l r)

private theorem comparisonLeaderWall_bulletFieldPair
    (l r : AgentState psi) :
    bulletFieldPair (comparisonLeaderWall l r) = bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold comparisonLeaderWall clearComparisonSignal bulletFieldPair
      BulletFields.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveLeaderPreclear_bulletFieldPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    bulletFieldPair (sigMoveLeaderPreclear hpsi l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold sigMoveLeaderPreclear clearIfLeader clearComparisonSignal
      bulletFieldPair BulletFields.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveTransfers_bulletFieldPair
    (l r : AgentState psi) :
    bulletFieldPair (sigMoveTransfers l r) = bulletFieldPair (l, r) := by
  let q0 := sigMoveStep1 l r
  let q1 := sigMoveStep2 q0.1 q0.2
  let q2 := sigMoveStep3 q1.1 q1.2
  let q3 := sigMoveStep4 q2.1 q2.2
  change bulletFieldPair (sigMoveStep5 q3.1 q3.2) = bulletFieldPair (l, r)
  exact (sigMoveStep5_bulletFieldPair q3.1 q3.2).trans
    ((sigMoveStep4_bulletFieldPair q2.1 q2.2).trans
      ((sigMoveStep3_bulletFieldPair q1.1 q1.2).trans
        ((sigMoveStep2_bulletFieldPair q0.1 q0.2).trans
          (sigMoveStep1_bulletFieldPair l r))))

private theorem sigMoveLeaderBeforeControl_bulletFieldPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    bulletFieldPair (sigMoveLeaderBeforeControl hpsi l r) =
      bulletFieldPair (l, r) := by
  let q0 := sigMoveLeaderPreclear hpsi l r
  let moved := sigMoveTransfers q0.1 q0.2
  change bulletFieldPair (comparisonLeaderWall moved.1 moved.2) =
    bulletFieldPair (l, r)
  exact (comparisonLeaderWall_bulletFieldPair moved.1 moved.2).trans
    ((sigMoveTransfers_bulletFieldPair q0.1 q0.2).trans
      (sigMoveLeaderPreclear_bulletFieldPair hpsi l r))

private theorem sigMoveControlTail_bulletFieldPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    bulletFieldPair (sigMoveControlTail hpsi l r) = bulletFieldPair (l, r) := by
  let q := (sigMoveApplyControl hpsi l, sigMoveApplyControl hpsi r)
  let l' := if q.2.state = MainState.depart then
    if q.1.label.val < psi - 1 ∧ q.1.state = MainState.CHECK_ready then
      { q.1 with state := MainState.depart }
    else q.1
  else q.1
  change bulletFieldPair (l', q.2) = bulletFieldPair (l, r)
  have htail : bulletFieldPair (l', q.2) = bulletFieldPair q := by
    apply Prod.ext
    · apply BulletFields.ext
      all_goals
        unfold l' bulletFieldPair BulletFields.ofState
        try dsimp only []
        repeat (first | rfl | split)
    · rfl
  exact htail.trans (Prod.ext
    (sigMoveApplyControl_bulletFields hpsi l)
    (sigMoveApplyControl_bulletFields hpsi r))

theorem sigMoveLeaderWall_bulletFieldPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    bulletFieldPair (sigMoveLeaderWall hpsi l r) = bulletFieldPair (l, r) := by
  let q := sigMoveLeaderBeforeControl hpsi l r
  change bulletFieldPair (sigMoveControlTail hpsi q.1 q.2) =
    bulletFieldPair (l, r)
  exact (sigMoveControlTail_bulletFieldPair hpsi q.1 q.2).trans
    (sigMoveLeaderBeforeControl_bulletFieldPair hpsi l r)

private theorem sigMoveLeaderWall_peaceViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    peaceViewPair (sigMoveLeaderWall hpsi l r) = peaceViewPair (l, r) :=
  peaceViewPair_eq_of_frames
    (Prod.ext (sigMoveLeaderWall_leaders_eq hpsi l r).1
      (sigMoveLeaderWall_leaders_eq hpsi l r).2)
    (Prod.ext (sigMoveLeaderWall_labels_eq hpsi l r).1
      (sigMoveLeaderWall_labels_eq hpsi l r).2)
    (sigMoveLeaderWall_bulletFieldPair hpsi l r)

private theorem pPsiLeaderProbeWall_bulletFieldPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    bulletFieldPair (pPsiLeaderProbeWall hpsi l r) = bulletFieldPair (l, r) := by
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true then
    { r with probe := false }
  else r
  change bulletFieldPair (pPsi hpsi l0 r0) = bulletFieldPair (l, r)
  exact (pPsi_bulletFieldPair hpsi l0 r0).trans (by
    apply Prod.ext <;> apply BulletFields.ext
    all_goals
      unfold l0 r0 bulletFieldPair BulletFields.ofState
      try dsimp only []
      repeat (first | rfl | split))

/-- The reset-aware probe guard changes only probe/control fields before
literal P-prime, so it frames the complete bullet-field pair exactly. -/
theorem pPsiLeaderResetProbeWall_bulletFieldPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    bulletFieldPair (pPsiLeaderResetProbeWall hpsi l r) =
      bulletFieldPair (l, r) := by
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true ∨
      l.reset_cmd = true then
    { r with probe := false }
  else r
  change bulletFieldPair (pPsi hpsi l0 r0) = bulletFieldPair (l, r)
  exact (pPsi_bulletFieldPair hpsi l0 r0).trans (by
    apply Prod.ext <;> apply BulletFields.ext
    all_goals
      unfold l0 r0 bulletFieldPair BulletFields.ofState
      try dsimp only []
      repeat (first | rfl | split))

private theorem pPsiLeaderProbeWall_peaceViewPair_of_responder_frame
    (hpsi : psi > 0) (l r : AgentState psi)
    (hrespLeader : (pPsiLeaderProbeWall hpsi l r).2.leader = r.leader)
    (hrespLabel : (pPsiLeaderProbeWall hpsi l r).2.label = r.label) :
    peaceViewPair (pPsiLeaderProbeWall hpsi l r) = peaceViewPair (l, r) := by
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true then
    { r with probe := false }
  else r
  have hleftLeader : (pPsiLeaderProbeWall hpsi l r).1.leader = l.leader := by
    change (pPsi hpsi l0 r0).1.leader = l.leader
    exact (pPsi_initiator_leader_eq hpsi l0 r0).trans (by
      unfold l0
      split <;> rfl)
  have hleftLabel : (pPsiLeaderProbeWall hpsi l r).1.label = l.label := by
    change (pPsi hpsi l0 r0).1.label = l.label
    exact (pPsi_initiator_label_eq hpsi l0 r0).trans (by
      unfold l0
      split <;> rfl)
  exact peaceViewPair_eq_of_frames
    (Prod.ext hleftLeader hrespLeader)
    (Prod.ext hleftLabel hrespLabel)
    (pPsiLeaderProbeWall_bulletFieldPair hpsi l r)

theorem pPsiLeaderProbeWall_responder_frame_of_aligned
    (hpsi : psi > 0) (l r : AgentState psi)
    (halign : r.label =
      ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    (pPsiLeaderProbeWall hpsi l r).2.leader = r.leader ∧
      (pPsiLeaderProbeWall hpsi l r).2.label = r.label := by
  unfold pPsiLeaderProbeWall
  dsimp only
  split <;> split <;> simp [pPsi, halign]

/-- A barrier covered by an existing responder leader is also a physical
frame for that responder.  Unlike the aligned case, Algorithm 2 may update the
initiator probe/phase controls, but it cannot create, remove, or relabel the
leader that blocks the barrier. -/
theorem pPsiLeaderProbeWall_responder_frame_of_responder_leader
    (hpsi : psi > 0) (l r : AgentState psi)
    (hrLeader : r.leader = true) :
    (pPsiLeaderProbeWall hpsi l r).2.leader = r.leader ∧
      (pPsiLeaderProbeWall hpsi l r).2.label = r.label := by
  unfold pPsiLeaderProbeWall
  dsimp only
  simp [hrLeader, pPsi]

theorem normalizeDeletion_peaceView
    (u : AuthorizedAgentState psi) :
    PeaceView.ofState (normalizeDeletion u).core = PeaceView.ofState u.core := by
  apply PeaceView.ext
  all_goals
    unfold normalizeDeletion PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem authorizedGenSig_peaceViewPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedGenSig hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  exact genSigSaturated_peaceViewPair hpsi kappa l.core r.core

private theorem authorizedCleanSig_peaceViewPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedCleanSig hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  exact cleanSig_peaceViewPair hpsi l.core r.core

private theorem authorizedEliminateSig_peaceViewPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedEliminateSig hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  exact eliminateSig_peaceViewPair hpsi l.core r.core

private theorem authorizedSigMoveLeaderWall_peaceViewPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedSigMoveLeaderWall hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  have hcore := authorizedSigMoveLeaderWall_core hpsi l r
  exact (congrArg peaceViewPair hcore).trans
    (sigMoveLeaderWall_peaceViewPair hpsi l.core r.core)

theorem wallSweepAuthorizedBeforeCheck_peaceView_of_ppsi_frame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrespLeader :
      (authorizedPPsiLeaderProbeWall hpsi l r).2.core.leader = r.core.leader)
    (hrespLabel :
      (authorizedPPsiLeaderProbeWall hpsi l r).2.core.label = r.core.label) :
    authorizedPeaceViewPair (wallSweepAuthorizedBeforeCheck hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  let q0 := authorizedPPsiLeaderProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  let q4 := authorizedSigMoveLeaderWall hpsi q3.1 q3.2
  have h0 : authorizedPeaceViewPair q0 = authorizedPeaceViewPair (l, r) := by
    change peaceViewPair (pPsiLeaderProbeWall hpsi l.core r.core) =
      peaceViewPair (l.core, r.core)
    exact pPsiLeaderProbeWall_peaceViewPair_of_responder_frame
      hpsi l.core r.core hrespLeader hrespLabel
  have h1 : authorizedPeaceViewPair q1 = authorizedPeaceViewPair q0 := by
    exact authorizedGenSig_peaceViewPair hpsi kappa q0.1 q0.2
  have h2 : authorizedPeaceViewPair q2 = authorizedPeaceViewPair q1 := by
    exact authorizedCleanSig_peaceViewPair hpsi q1.1 q1.2
  have h3 : authorizedPeaceViewPair q3 = authorizedPeaceViewPair q2 := by
    exact authorizedEliminateSig_peaceViewPair hpsi q2.1 q2.2
  have h4 : authorizedPeaceViewPair q4 = authorizedPeaceViewPair q3 := by
    exact authorizedSigMoveLeaderWall_peaceViewPair hpsi q3.1 q3.2
  change authorizedPeaceViewPair q4 = authorizedPeaceViewPair (l, r)
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

/-! Stage bullet frames at variables.  The prefix theorems below rewrite the
prefix into its stages and generalize each stage output, so every step is a
syntactic instance of one of these (chaining them through `let`-bound stage
outputs made the elaborator reduce the composed prefix: 455 s and 338 s). -/

private theorem authorizedPPsiLeaderProbeWall_bulletFieldPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedPPsiLeaderProbeWall hpsi l r) =
      authorizedBulletFieldPair (l, r) :=
  pPsiLeaderProbeWall_bulletFieldPair hpsi l.core r.core

private theorem authorizedPPsiLeaderResetProbeWall_bulletFieldPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedPPsiLeaderResetProbeWall hpsi l r) =
      authorizedBulletFieldPair (l, r) :=
  pPsiLeaderResetProbeWall_bulletFieldPair hpsi l.core r.core

private theorem authorizedGenSig_bulletFieldPair
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedGenSig hpsi kappa l r) =
      authorizedBulletFieldPair (l, r) :=
  (congrArg bulletFieldPair
    (PPLLWallSweepStageFrames.authorizedReconcile_core_pair
      (genSigSaturated hpsi kappa) l r)).trans
    (genSigSaturated_bulletFieldPair hpsi kappa l.core r.core)

private theorem authorizedCleanSig_bulletFieldPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedCleanSig hpsi l r) =
      authorizedBulletFieldPair (l, r) :=
  (congrArg bulletFieldPair
    (PPLLWallSweepStageFrames.authorizedReconcile_core_pair
      (cleanSig hpsi) l r)).trans
    (cleanSig_bulletFieldPair hpsi l.core r.core)

private theorem authorizedEliminateSig_bulletFieldPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedEliminateSig hpsi l r) =
      authorizedBulletFieldPair (l, r) :=
  (congrArg bulletFieldPair
    (PPLLWallSweepStageFrames.authorizedReconcile_core_pair
      (eliminateSig hpsi) l r)).trans
    (eliminateSig_bulletFieldPair hpsi l.core r.core)

private theorem authorizedSigMoveLeaderWall_bulletFieldPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedSigMoveLeaderWall hpsi l r) =
      authorizedBulletFieldPair (l, r) :=
  (congrArg bulletFieldPair (authorizedSigMoveLeaderWall_core hpsi l r)).trans
    (sigMoveLeaderWall_bulletFieldPair hpsi l.core r.core)

/-- The four stages after P-prime frame all bullet fields. -/
private theorem afterPPrime_bulletFieldPair
    (hpsi : psi > 0) (kappa : Nat)
    (q0 : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedBulletFieldPair
        (authorizedSigMoveLeaderWall hpsi
          (authorizedEliminateSig hpsi
            (authorizedCleanSig hpsi
              (authorizedGenSig hpsi kappa q0.1 q0.2).1
              (authorizedGenSig hpsi kappa q0.1 q0.2).2).1
            (authorizedCleanSig hpsi
              (authorizedGenSig hpsi kappa q0.1 q0.2).1
              (authorizedGenSig hpsi kappa q0.1 q0.2).2).2).1
          (authorizedEliminateSig hpsi
            (authorizedCleanSig hpsi
              (authorizedGenSig hpsi kappa q0.1 q0.2).1
              (authorizedGenSig hpsi kappa q0.1 q0.2).2).1
            (authorizedCleanSig hpsi
              (authorizedGenSig hpsi kappa q0.1 q0.2).1
              (authorizedGenSig hpsi kappa q0.1 q0.2).2).2).2) =
      authorizedBulletFieldPair q0 := by
  have h1 := authorizedGenSig_bulletFieldPair hpsi kappa q0.1 q0.2
  revert h1
  generalize authorizedGenSig hpsi kappa q0.1 q0.2 = q1
  intro h1
  have h2 := authorizedCleanSig_bulletFieldPair hpsi q1.1 q1.2
  revert h2
  generalize authorizedCleanSig hpsi q1.1 q1.2 = q2
  intro h2
  have h3 := authorizedEliminateSig_bulletFieldPair hpsi q2.1 q2.2
  revert h3
  generalize authorizedEliminateSig hpsi q2.1 q2.2 = q3
  intro h3
  exact (authorizedSigMoveLeaderWall_bulletFieldPair hpsi q3.1 q3.2).trans
    (h3.trans (h2.trans h1))

/-- The complete wall prefix through SIGMOVE frames all bullet fields,
independently of whether P-prime changes the responder leader or label. -/
theorem wallSweepAuthorizedBeforeCheck_bulletFieldPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair
        (wallSweepAuthorizedBeforeCheck hpsi kappa l r) =
      authorizedBulletFieldPair (l, r) := by
  rw [PPLLWallSweepStageFrames.wallSweepAuthorizedBeforeCheck_stages]
  exact (afterPPrime_bulletFieldPair hpsi kappa
      (authorizedPPsiLeaderProbeWall hpsi l r)).trans
    (authorizedPPsiLeaderProbeWall_bulletFieldPair hpsi l r)

/-- Replacing the first P-prime stage by its reset-aware probe guard does not
change any shield, bullet, or overwriting-signal field through SIGMOVE. -/
theorem wallSweepResetProbeAuthorizedBeforeCheck_bulletFieldPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair
        (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r) =
      authorizedBulletFieldPair (l, r) := by
  rw [PPLLWallSweepStageFrames.wallSweepResetProbeAuthorizedBeforeCheck_stages]
  exact (afterPPrime_bulletFieldPair hpsi kappa
      (authorizedPPsiLeaderResetProbeWall hpsi l r)).trans
    (authorizedPPsiLeaderResetProbeWall_bulletFieldPair hpsi l r)

/-- Authorized CHECK exposes the raw CHECK bullet-field frame without asking
downstream proofs to unfold a concrete, potentially large prefix term. -/
theorem authorizedCheckSig_bulletFieldPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedCheckSig hpsi l r) =
      authorizedBulletFieldPair (l, r) := by
  exact checkSig_bulletFieldPair hpsi l.core r.core

theorem sanitizeAuthorizedPair_peaceViewPair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPeaceViewPair (sanitizeAuthorizedPair hpsi q) =
      authorizedPeaceViewPair q := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold sanitizeAuthorizedPair sanitizeAuthorizedTerminalEqual
      authorizedPeaceViewPair peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem markLeaderBirth_peaceViewPair
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPeaceViewPair (markLeaderBirth born q) =
      authorizedPeaceViewPair q := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold markLeaderBirth markComparisonForDeletion
      authorizedPeaceViewPair peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

theorem authorizedCheckSig_peaceViewPair_of_responder_frame
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hresp : (authorizedCheckSig hpsi l r).2.core.leader = r.core.leader) :
    authorizedPeaceViewPair (authorizedCheckSig hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  exact peaceViewPair_eq_of_frames
    (Prod.ext (checkSig_initiator_leader_eq hpsi l.core r.core) hresp)
    (Prod.ext (checkSig_labels_eq hpsi l.core r.core).1
      (checkSig_labels_eq hpsi l.core r.core).2)
    (checkSig_bulletFieldPair hpsi l.core r.core)

private theorem authorizedDisappear_peaceViewPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedDisappear hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  exact disappear_peaceViewPair hpsi l.core r.core

private theorem authorizedCompareSig_peaceViewPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedCompareSig hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  exact peaceViewPair_eq_of_frames
    (Prod.ext (authorizedCompareSig_leaders_eq hpsi l r).1
      (authorizedCompareSig_leaders_eq hpsi l r).2)
    (authorizedCompareSig_labels hpsi l r)
    (authorizedCompareSig_bulletFieldPair hpsi l r)

private theorem resetKillComparison_peaceView (u : AgentState psi) :
    PeaceView.ofState (resetKillComparison u) = PeaceView.ofState u := by
  apply PeaceView.ext
  all_goals
    unfold resetKillComparison clearComparisonSignal PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigStart_peaceViewPair (l r : AgentState psi) :
    peaceViewPair (suppressSigStart l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigStart peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigMoveReset_peaceViewPair (l r : AgentState psi) :
    peaceViewPair (suppressSigMoveReset l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigMoveReset peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigTerminal_peaceViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    peaceViewPair (suppressSigTerminal hpsi l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigTerminal peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigEcho_peaceViewPair (l r : AgentState psi) :
    peaceViewPair (suppressSigEcho l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigEcho peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigFinish_peaceViewPair (l r : AgentState psi) :
    peaceViewPair (suppressSigFinish l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigFinish peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

theorem suppressSigResetKill_peaceViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    peaceViewPair (suppressSigResetKill hpsi l r) = peaceViewPair (l, r) := by
  let q0 := suppressSigStart l r
  let q0' := (resetKillComparison q0.1, resetKillComparison q0.2)
  let q1 := suppressSigMoveReset q0'.1 q0'.2
  let q1' := (resetKillComparison q1.1, resetKillComparison q1.2)
  let q2 := suppressSigTerminal hpsi q1'.1 q1'.2
  let q3 := suppressSigEcho q2.1 q2.2
  change peaceViewPair (suppressSigFinish q3.1 q3.2) = peaceViewPair (l, r)
  have h0 : peaceViewPair q0' = peaceViewPair q0 :=
    Prod.ext (resetKillComparison_peaceView q0.1)
      (resetKillComparison_peaceView q0.2)
  have h1 : peaceViewPair q1' = peaceViewPair q1 :=
    Prod.ext (resetKillComparison_peaceView q1.1)
      (resetKillComparison_peaceView q1.2)
  exact (suppressSigFinish_peaceViewPair q3.1 q3.2).trans
    ((suppressSigEcho_peaceViewPair q2.1 q2.2).trans
      ((suppressSigTerminal_peaceViewPair hpsi q1'.1 q1'.2).trans
        (h1.trans
          ((suppressSigMoveReset_peaceViewPair q0'.1 q0'.2).trans
            (h0.trans (suppressSigStart_peaceViewPair l r))))))

theorem authorizedSuppressSigResetKill_peaceViewPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair
        (authorizedReconcile (suppressSigResetKill hpsi) l r) =
      authorizedPeaceViewPair (l, r) := by
  exact suppressSigResetKill_peaceViewPair hpsi l.core r.core

/-! ## Structured gated-WRITE frames -/

/-- The cleanup fields not already covered by `ComparisonTrackedView`. -/
structure CleanupAuxView (psi : Nat) where
  path4 : Option (Int × Nat)
  path5 : Option (Int × Nat)
  p : Bool
  resetCmd : Bool
  echo : Bool
  deriving DecidableEq, Repr

namespace CleanupAuxView

/-- Extract the five cleanup controls outside the comparison-history view. -/
def ofState (u : AgentState psi) : CleanupAuxView psi :=
  ⟨u.path4, u.path5, u.p, u.reset_cmd, u.echo⟩

end CleanupAuxView

/-- Pair projection used to compose the five-field WRITE frames. -/
def cleanupAuxPair (q : AgentState psi × AgentState psi) :
    CleanupAuxView psi × CleanupAuxView psi :=
  (CleanupAuxView.ofState q.1, CleanupAuxView.ofState q.2)

/-- The two control bits that must reach repaired Algorithm 14 unchanged. -/
def resetEchoView (u : AgentState psi) : Bool × Bool :=
  (u.reset_cmd, u.echo)

/-- Reset/echo projection of both interacting endpoints. -/
def resetEchoPair (q : AgentState psi × AgentState psi) :
    (Bool × Bool) × (Bool × Bool) :=
  (resetEchoView q.1, resetEchoView q.2)

/-- Reset/echo projection after erasing authorization. -/
def authorizedResetEchoPair
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (Bool × Bool) × (Bool × Bool) :=
  resetEchoPair (q.1.core, q.2.core)

/-- Proof-only anchor used when the designated leader is the initiator. -/
def InitiatorAnchor (u : AgentState psi) : Prop :=
  u.leader = true ∧ u.shield = true

/-- Proof-only anchor used when the designated leader is the responder. -/
def ResponderZeroAnchor (hpsi : psi > 0) (u : AgentState psi) : Prop :=
  u.leader = true ∧ u.label = ⟨0, hpsi⟩

/-- Initiator anchor lifted to an authorized interaction pair. -/
def authorizedInitiatorAnchor
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop :=
  InitiatorAnchor q.1.core

/-- Responder-zero anchor lifted to an authorized interaction pair. -/
def authorizedResponderZeroAnchor (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop :=
  ResponderZeroAnchor hpsi q.2.core

/-- Responder leader conclusion lifted to an authorized pair. -/
def authorizedResponderLeader
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop :=
  q.2.core.leader = true

def authorizedResponderEchoFalse
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop :=
  q.2.core.echo = false

def authorizedInitiatorEchoFalse
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop :=
  q.1.core.echo = false

def authorizedLeaderReseedResult
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop :=
  q.1.core.echo = false ∧ q.2.core.echo = false ∧
    q.2.core.reset_cmd = true

def authorizedBothNeutral
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop :=
  ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core

/-- Exact comparison/reset/echo effect of an interaction sourced by an
existing initiator leader.  The responder receives reset exactly when its
input echo is absent; in either case both output echoes are consumed. -/
def AuthorizedLeaderSourceCleanup
    (input output : AuthorizedAgentState psi ×
      AuthorizedAgentState psi) : Prop :=
  ComparisonNeutral output.1.core ∧
    ComparisonNeutral output.2.core ∧
    output.1.core.reset_cmd = false ∧
    output.2.core.reset_cmd = !input.2.core.echo ∧
    output.1.core.echo = false ∧
    output.2.core.echo = false

theorem AuthorizedLeaderSourceCleanup.of_pair_eq
    {input a b : AuthorizedAgentState psi ×
      AuthorizedAgentState psi}
    (hab : a = b) (hb : AuthorizedLeaderSourceCleanup input b) :
    AuthorizedLeaderSourceCleanup input a := by
  rw [hab]
  exact hb

def authorizedInitiatorLabel
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Fin psi :=
  q.1.core.label

theorem authorizedResetEchoPair_eq_trans
    {a b c : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : authorizedResetEchoPair a = authorizedResetEchoPair b)
    (hbc : authorizedResetEchoPair b = authorizedResetEchoPair c) :
    authorizedResetEchoPair a = authorizedResetEchoPair c :=
  hab.trans hbc

theorem authorizedResetEchoPair_eta
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedResetEchoPair (q.1, q.2) = authorizedResetEchoPair q := by
  cases q
  rfl

/-! ## Ordinary-prefix reset/echo frames -/

private theorem resetEchoPair_pPsi (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (pPsi hpsi l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView pPsi
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_pPsiLeaderProbeWall (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (pPsiLeaderProbeWall hpsi l r) = resetEchoPair (l, r) := by
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true then
    { r with probe := false } else r
  have hprep : resetEchoPair (l0, r0) = resetEchoPair (l, r) := by
    apply Prod.ext <;> apply Prod.ext
    all_goals
      unfold resetEchoPair resetEchoView l0 r0
      repeat (first | rfl | split)
  change resetEchoPair (pPsi hpsi l0 r0) = resetEchoPair (l, r)
  exact (resetEchoPair_pPsi hpsi l0 r0).trans hprep

private theorem resetEchoPair_pPsiLeaderResetProbeWall
    (hpsi : psi > 0) (l r : AgentState psi) :
    resetEchoPair (pPsiLeaderResetProbeWall hpsi l r) =
      resetEchoPair (l, r) := by
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true ∨
      l.reset_cmd = true then { r with probe := false } else r
  have hprep : resetEchoPair (l0, r0) = resetEchoPair (l, r) := by
    apply Prod.ext <;> apply Prod.ext
    all_goals
      unfold resetEchoPair resetEchoView l0 r0
      repeat (first | rfl | split)
  change resetEchoPair (pPsi hpsi l0 r0) = resetEchoPair (l, r)
  exact (resetEchoPair_pPsi hpsi l0 r0).trans hprep

private theorem resetEchoPair_waitPrepare (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (waitSaturatedPrepare hpsi l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView waitSaturatedPrepare
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_waitCarry (hpsi : psi > 0) (kappa : Nat)
    (l r : AgentState psi) :
    resetEchoPair (waitSaturatedCarry hpsi kappa l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView waitSaturatedCarry
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_waitReset (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (waitSaturatedReset hpsi l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView waitSaturatedReset
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_waitFinish (hpsi : psi > 0) (kappa : Nat)
    (l r : AgentState psi) :
    resetEchoPair (waitSaturatedFinish hpsi kappa l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView waitSaturatedFinish
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_waitSaturated (hpsi : psi > 0) (kappa : Nat)
    (l r : AgentState psi) :
    resetEchoPair (waitSaturated hpsi kappa l r) = resetEchoPair (l, r) := by
  let q0 := waitSaturatedPrepare hpsi l r
  let q1 := waitSaturatedCarry hpsi kappa q0.1 q0.2
  let q2 := waitSaturatedReset hpsi q1.1 q1.2
  exact (resetEchoPair_waitFinish hpsi kappa q2.1 q2.2).trans
    ((resetEchoPair_waitReset hpsi q1.1 q1.2).trans
      ((resetEchoPair_waitCarry hpsi kappa q0.1 q0.2).trans
        (resetEchoPair_waitPrepare hpsi l r)))

private theorem resetEchoPair_genStart (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (genSigSaturatedStart hpsi l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView genSigSaturatedStart
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_genEmit (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (genSigSaturatedEmit hpsi l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView genSigSaturatedEmit
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_genPropagate (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (genSigSaturatedPropagate hpsi l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView genSigSaturatedPropagate
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_genFinish (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (genSigSaturatedFinish hpsi l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView genSigSaturatedFinish
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_genAfterWait (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (genSigSaturatedAfterWait hpsi l r) =
      resetEchoPair (l, r) := by
  let q0 := genSigSaturatedStart hpsi l r
  let q1 := genSigSaturatedEmit hpsi q0.1 q0.2
  let q2 := genSigSaturatedPropagate hpsi q1.1 q1.2
  exact (resetEchoPair_genFinish hpsi q2.1 q2.2).trans
    ((resetEchoPair_genPropagate hpsi q1.1 q1.2).trans
      ((resetEchoPair_genEmit hpsi q0.1 q0.2).trans
        (resetEchoPair_genStart hpsi l r)))

private theorem resetEchoPair_genSigSaturated
    (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    resetEchoPair (genSigSaturated hpsi kappa l r) =
      resetEchoPair (l, r) := by
  let q := waitSaturated hpsi kappa l r
  exact (resetEchoPair_genAfterWait hpsi q.1 q.2).trans
    (resetEchoPair_waitSaturated hpsi kappa l r)

private theorem resetEcho_cleanSigGenConnect (u : AgentState psi) :
    resetEchoView (cleanSigGenConnect u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView cleanSigGenConnect
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEcho_cleanSigCleanApply (u : AgentState psi) :
    resetEchoView (cleanSigCleanApply u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView cleanSigCleanApply
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_cleanSigStep3 (l r : AgentState psi) :
    resetEchoPair (cleanSigStep3 l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView cleanSigStep3
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_cleanSigStep4 (l r : AgentState psi) :
    resetEchoPair (cleanSigStep4 l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView cleanSigStep4
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_cleanSigStep5 (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (cleanSigStep5 hpsi l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView cleanSigStep5
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_cleanSigStep6 (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (cleanSigStep6 hpsi l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView cleanSigStep6
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_cleanSig (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (cleanSig hpsi l r) = resetEchoPair (l, r) := by
  let q0 := (cleanSigGenConnect l, cleanSigGenConnect r)
  let q1 := cleanSigStep3 q0.1 q0.2
  let q2 := cleanSigStep4 q1.1 q1.2
  let q3 := cleanSigStep5 hpsi q2.1 q2.2
  let q4 := cleanSigStep6 hpsi q3.1 q3.2
  change resetEchoPair (cleanSigCleanApply q4.1,
    cleanSigCleanApply q4.2) = resetEchoPair (l, r)
  have hfinal : resetEchoPair (cleanSigCleanApply q4.1,
      cleanSigCleanApply q4.2) = resetEchoPair q4 :=
    Prod.ext (resetEcho_cleanSigCleanApply q4.1)
      (resetEcho_cleanSigCleanApply q4.2)
  exact hfinal.trans ((resetEchoPair_cleanSigStep6 hpsi q3.1 q3.2).trans
    ((resetEchoPair_cleanSigStep5 hpsi q2.1 q2.2).trans
      ((resetEchoPair_cleanSigStep4 q1.1 q1.2).trans
        ((resetEchoPair_cleanSigStep3 q0.1 q0.2).trans
          (Prod.ext (resetEcho_cleanSigGenConnect l)
            (resetEcho_cleanSigGenConnect r))))))

private theorem resetEchoPair_eliminateSig (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (eliminateSig hpsi l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView eliminateSig
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_sigMoveStep1 (l r : AgentState psi) :
    resetEchoPair (sigMoveStep1 l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView sigMoveStep1
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_sigMoveStep2 (l r : AgentState psi) :
    resetEchoPair (sigMoveStep2 l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView sigMoveStep2
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_sigMoveStep3 (l r : AgentState psi) :
    resetEchoPair (sigMoveStep3 l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView sigMoveStep3
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_sigMoveStep4 (l r : AgentState psi) :
    resetEchoPair (sigMoveStep4 l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView sigMoveStep4
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_sigMoveStep5 (l r : AgentState psi) :
    resetEchoPair (sigMoveStep5 l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView sigMoveStep5
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_sigMoveTransfers (l r : AgentState psi) :
    resetEchoPair (sigMoveTransfers l r) = resetEchoPair (l, r) := by
  let q0 := sigMoveStep1 l r
  let q1 := sigMoveStep2 q0.1 q0.2
  let q2 := sigMoveStep3 q1.1 q1.2
  let q3 := sigMoveStep4 q2.1 q2.2
  exact (resetEchoPair_sigMoveStep5 q3.1 q3.2).trans
    ((resetEchoPair_sigMoveStep4 q2.1 q2.2).trans
      ((resetEchoPair_sigMoveStep3 q1.1 q1.2).trans
        ((resetEchoPair_sigMoveStep2 q0.1 q0.2).trans
          (resetEchoPair_sigMoveStep1 l r))))

private theorem resetEcho_sigMoveApplyControl (hpsi : psi > 0)
    (u : AgentState psi) :
    resetEchoView (sigMoveApplyControl hpsi u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView sigMoveApplyControl
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_sigMoveControlTail (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (sigMoveControlTail hpsi l r) = resetEchoPair (l, r) := by
  let l0 := sigMoveApplyControl hpsi l
  let r0 := sigMoveApplyControl hpsi r
  let l1 := if r0.state = .depart then
    if l0.label.val < psi - 1 ∧ l0.state = .CHECK_ready then
      { l0 with state := .depart }
    else l0
  else l0
  have hl1 : resetEchoView l1 = resetEchoView l0 := by
    apply Prod.ext
    all_goals
      unfold l1 resetEchoView
      repeat (first | rfl | split)
  change resetEchoPair (l1, r0) = resetEchoPair (l, r)
  exact Prod.ext
    (hl1.trans (resetEcho_sigMoveApplyControl hpsi l))
    (resetEcho_sigMoveApplyControl hpsi r)

private theorem resetEcho_clearComparisonSignal (u : AgentState psi) :
    resetEchoView (clearComparisonSignal u) = resetEchoView u := by
  rfl

private theorem resetEcho_clearIfLeader (u : AgentState psi) :
    resetEchoView (clearIfLeader u) = resetEchoView u := by
  unfold clearIfLeader
  split
  · exact resetEcho_clearComparisonSignal u
  · rfl

private theorem resetEchoPair_comparisonLeaderWall (l r : AgentState psi) :
    resetEchoPair (comparisonLeaderWall l r) = resetEchoPair (l, r) := by
  let l0 := if l.leader ∨ r.leader then clearComparisonSignal l else l
  let r0 := if r.leader then clearComparisonSignal r else r
  have hl0 : resetEchoView l0 = resetEchoView l := by
    unfold l0
    split
    · exact resetEcho_clearComparisonSignal l
    · rfl
  have hr0 : resetEchoView r0 = resetEchoView r := by
    unfold r0
    split
    · exact resetEcho_clearComparisonSignal r
    · rfl
  change resetEchoPair (l0, r0) = resetEchoPair (l, r)
  exact Prod.ext hl0 hr0

private theorem resetEchoPair_sigMoveLeaderPreclear (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (sigMoveLeaderPreclear hpsi l r) =
      resetEchoPair (l, r) := by
  let l0 := if l.leader = true ∨ incompleteLeftLeaderBoundary hpsi l r then
    clearComparisonSignal l else l
  let r0 := clearIfLeader r
  have hl0 : resetEchoView l0 = resetEchoView l := by
    unfold l0
    split
    · exact resetEcho_clearComparisonSignal l
    · rfl
  change resetEchoPair (l0, r0) = resetEchoPair (l, r)
  exact Prod.ext hl0 (resetEcho_clearIfLeader r)

private theorem resetEchoPair_sigMoveLeaderBeforeControl (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (sigMoveLeaderBeforeControl hpsi l r) =
      resetEchoPair (l, r) := by
  let q0 := sigMoveLeaderPreclear hpsi l r
  let q1 := sigMoveTransfers q0.1 q0.2
  change resetEchoPair (comparisonLeaderWall q1.1 q1.2) =
    resetEchoPair (l, r)
  exact (resetEchoPair_comparisonLeaderWall q1.1 q1.2).trans
    ((resetEchoPair_sigMoveTransfers q0.1 q0.2).trans
      (resetEchoPair_sigMoveLeaderPreclear hpsi l r))

private theorem resetEchoPair_sigMoveLeaderWall (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (sigMoveLeaderWall hpsi l r) = resetEchoPair (l, r) := by
  let q := sigMoveLeaderBeforeControl hpsi l r
  change resetEchoPair (sigMoveControlTail hpsi q.1 q.2) =
    resetEchoPair (l, r)
  exact (resetEchoPair_sigMoveControlTail hpsi q.1 q.2).trans
    (resetEchoPair_sigMoveLeaderBeforeControl hpsi l r)

private theorem authorizedReconcile_resetEchoPair
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hf : resetEchoPair (f l.core r.core) =
      resetEchoPair (l.core, r.core)) :
    authorizedResetEchoPair (authorizedReconcile f l r) =
      authorizedResetEchoPair (l, r) := by
  change resetEchoPair (f l.core r.core) = resetEchoPair (l.core, r.core)
  exact hf

private theorem authorizedPPsiLeaderProbeWall_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedPPsiLeaderProbeWall hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  change resetEchoPair (pPsiLeaderProbeWall hpsi l.core r.core) =
    resetEchoPair (l.core, r.core)
  exact resetEchoPair_pPsiLeaderProbeWall hpsi l.core r.core

private theorem authorizedPPsiLeaderResetProbeWall_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair
        (authorizedPPsiLeaderResetProbeWall hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  change resetEchoPair
      (pPsiLeaderResetProbeWall hpsi l.core r.core) =
    resetEchoPair (l.core, r.core)
  exact resetEchoPair_pPsiLeaderResetProbeWall hpsi l.core r.core

private theorem authorizedGenSig_resetEchoPair
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedGenSig hpsi kappa l r) =
      authorizedResetEchoPair (l, r) := by
  exact authorizedReconcile_resetEchoPair (genSigSaturated hpsi kappa) l r
    (resetEchoPair_genSigSaturated hpsi kappa l.core r.core)

private theorem authorizedCleanSig_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedCleanSig hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  exact authorizedReconcile_resetEchoPair (cleanSig hpsi) l r
    (resetEchoPair_cleanSig hpsi l.core r.core)

private theorem authorizedEliminateSig_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedEliminateSig hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  exact authorizedReconcile_resetEchoPair (eliminateSig hpsi) l r
    (resetEchoPair_eliminateSig hpsi l.core r.core)

private theorem authorizedSigMoveLeaderWall_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedSigMoveLeaderWall hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  have hcore := authorizedSigMoveLeaderWall_core hpsi l r
  have hview := congrArg resetEchoPair hcore
  exact hview.trans (resetEchoPair_sigMoveLeaderWall hpsi l.core r.core)

theorem wallSweepAuthorizedBeforeCheck_resetEchoPair
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (wallSweepAuthorizedBeforeCheck hpsi kappa l r) =
      authorizedResetEchoPair (l, r) := by
  let q0 := authorizedPPsiLeaderProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  change authorizedResetEchoPair
    (authorizedSigMoveLeaderWall hpsi q3.1 q3.2) = _
  exact (authorizedSigMoveLeaderWall_resetEchoPair hpsi q3.1 q3.2).trans
    ((authorizedEliminateSig_resetEchoPair hpsi q2.1 q2.2).trans
      ((authorizedCleanSig_resetEchoPair hpsi q1.1 q1.2).trans
        ((authorizedGenSig_resetEchoPair hpsi kappa q0.1 q0.2).trans
          (authorizedPPsiLeaderProbeWall_resetEchoPair hpsi l r))))

/-- Replacing only the initial probe guard by its reset-aware form still
frames the complete reset/echo pair through the pre-CHECK prefix. -/
theorem wallSweepResetProbeAuthorizedBeforeCheck_resetEchoPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair
        (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r) =
      authorizedResetEchoPair (l, r) := by
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  change authorizedResetEchoPair
    (authorizedSigMoveLeaderWall hpsi q3.1 q3.2) = _
  exact (authorizedSigMoveLeaderWall_resetEchoPair hpsi q3.1 q3.2).trans
    ((authorizedEliminateSig_resetEchoPair hpsi q2.1 q2.2).trans
      ((authorizedCleanSig_resetEchoPair hpsi q1.1 q1.2).trans
        ((authorizedGenSig_resetEchoPair hpsi kappa q0.1 q0.2).trans
          (authorizedPPsiLeaderResetProbeWall_resetEchoPair hpsi l r))))

private theorem normalizeDeletion_resetEcho
    (u : AuthorizedAgentState psi) :
    resetEchoView (normalizeDeletion u).core = resetEchoView u.core := by
  apply Prod.ext
  all_goals
    unfold normalizeDeletion resetEchoView
    repeat (first | rfl | split)

theorem normalizeDeletionPair_resetEcho
    (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (normalizeDeletion l, normalizeDeletion r) =
      authorizedResetEchoPair (l, r) :=
  Prod.ext (normalizeDeletion_resetEcho l) (normalizeDeletion_resetEcho r)

private theorem sanitizeAuthorizedTerminalEqual_resetEcho
    (hpsi : psi > 0) (u : AuthorizedAgentState psi) :
    resetEchoView (sanitizeAuthorizedTerminalEqual hpsi u).core =
      resetEchoView u.core := by
  apply Prod.ext
  all_goals
    unfold sanitizeAuthorizedTerminalEqual resetEchoView
    split <;> rfl

theorem sanitizeAuthorizedPair_resetEchoPair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedResetEchoPair (sanitizeAuthorizedPair hpsi q) =
      authorizedResetEchoPair q :=
  Prod.ext (sanitizeAuthorizedTerminalEqual_resetEcho hpsi q.1)
    (sanitizeAuthorizedTerminalEqual_resetEcho hpsi q.2)

private theorem resetEcho_checkSigSetReady (u : AgentState psi) :
    resetEchoView (checkSigSetReady u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView checkSigSetReady
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEcho_checkSigCheckL (hpsi : psi > 0)
    (u : AgentState psi) :
    resetEchoView (checkSigCheckL hpsi u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView checkSigCheckL
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEcho_checkSigCheckR (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoView (checkSigCheckR hpsi l r) = resetEchoView r := by
  apply Prod.ext
  all_goals
    unfold resetEchoView checkSigCheckR
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEcho_checkSigSetResult (u : AgentState psi) :
    resetEchoView (checkSigSetResult u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView checkSigSetResult
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEcho_checkSigSetLeader (hpsi : psi > 0)
    (u : AgentState psi) :
    resetEchoView (checkSigSetLeader hpsi u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView checkSigSetLeader
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_checkSig (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (checkSig hpsi l r) = resetEchoPair (l, r) := by
  let l0 := checkSigSetReady l
  let r0 := checkSigSetReady r
  let l1 := checkSigCheckL hpsi l0
  let r1 := checkSigCheckR hpsi l1 r0
  let l2 := checkSigSetResult l1
  let r2 := checkSigSetResult r1
  rw [checkSig_eq_staged]
  change resetEchoPair (l2, checkSigSetLeader hpsi r2) =
    resetEchoPair (l, r)
  exact Prod.ext
    ((resetEcho_checkSigSetResult l1).trans
      ((resetEcho_checkSigCheckL hpsi l0).trans
        (resetEcho_checkSigSetReady l)))
    ((resetEcho_checkSigSetLeader hpsi r2).trans
      ((resetEcho_checkSigSetResult r1).trans
        ((resetEcho_checkSigCheckR hpsi l1 r0).trans
          (resetEcho_checkSigSetReady r))))

theorem authorizedCheckSig_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedCheckSig hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  exact authorizedReconcile_resetEchoPair (checkSig hpsi) l r
    (resetEchoPair_checkSig hpsi l.core r.core)

private theorem resetEchoPair_disappearStartR (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (disappearStartR hpsi l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView disappearStartR
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_disappearStartL (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (disappearStartL hpsi l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView disappearStartL
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_disappearCarry (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (disappearCarry hpsi l r) = resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView disappearCarry
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_disappear (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (disappear hpsi l r) = resetEchoPair (l, r) := by
  let q0 := disappearStartR hpsi l r
  let q1 := disappearStartL hpsi q0.1 q0.2
  rw [disappear_eq_staged]
  exact (resetEchoPair_disappearCarry hpsi q1.1 q1.2).trans
    ((resetEchoPair_disappearStartL hpsi q0.1 q0.2).trans
      (resetEchoPair_disappearStartR hpsi l r))

theorem authorizedDisappear_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedDisappear hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  exact authorizedReconcile_resetEchoPair (disappear hpsi) l r
    (resetEchoPair_disappear hpsi l.core r.core)

private theorem resetEcho_compareSigInit (u : AgentState psi) :
    resetEchoView (compareSigInit u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView compareSigInit
    split <;> rfl

private theorem resetEchoPair_cmpUpdateReturnPriority (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (cmpUpdateReturnPriority hpsi l r) =
      resetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView cmpUpdateReturnPriority
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEcho_cmpUpdateSetPath2 (hpsi : psi > 0)
    (u : AgentState psi) :
    resetEchoView (cmpUpdateSetPath2 hpsi u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView cmpUpdateSetPath2
    try dsimp only []
    repeat (first | rfl | split)

private theorem authorizedCmpUpdate_resetEchoPair (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedCmpUpdate hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  let allowed := freshComparisonStart hpsi l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := .congest } else l.core
  let q := cmpUpdateReturnPriority hpsi lCore r.core
  have hlCore : resetEchoView lCore = resetEchoView l.core := by
    unfold lCore
    split <;> rfl
  have hq := resetEchoPair_cmpUpdateReturnPriority hpsi lCore r.core
  have hqL := congrArg Prod.fst hq
  have hqR := congrArg Prod.snd hq
  change resetEchoPair (cmpUpdateSetPath2 hpsi q.1, q.2) =
    resetEchoPair (l.core, r.core)
  exact Prod.ext
    ((resetEcho_cmpUpdateSetPath2 hpsi q.1).trans (hqL.trans hlCore)) hqR

private theorem resetEcho_compareBitUpdateL (hpsi : psi > 0)
    (u : AgentState psi) :
    resetEchoView (compareBitUpdateL hpsi u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView compareBitUpdateL
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEcho_compareBitUpdateR (hpsi : psi > 0)
    (u : AgentState psi) :
    resetEchoView (compareBitUpdateR hpsi u) = resetEchoView u := by
  apply Prod.ext
  all_goals
    unfold resetEchoView compareBitUpdateR
    try dsimp only []
    repeat (first | rfl | split)

private theorem resetEchoPair_compareBit (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (compareBit hpsi l r) = resetEchoPair (l, r) := by
  change (resetEchoView (compareBitUpdateL hpsi l),
    resetEchoView (compareBitUpdateR hpsi r)) =
    (resetEchoView l, resetEchoView r)
  exact Prod.ext (resetEcho_compareBitUpdateL hpsi l)
    (resetEcho_compareBitUpdateR hpsi r)

private theorem resetEchoPair_compareSigDispatch (hpsi : psi > 0)
    (l r : AgentState psi) :
    resetEchoPair (compareSigDispatch hpsi l r) = resetEchoPair (l, r) := by
  unfold compareSigDispatch
  repeat (first | exact resetEchoPair_compareBit hpsi l r | rfl | split)

theorem authorizedCompareSig_resetEchoPair (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedCompareSig hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hinit : resetEchoView lCore = resetEchoView l.core :=
    resetEcho_compareSigInit l.core
  unfold authorizedCompareSig
  dsimp only
  split
  · exact Prod.ext hinit rfl
  · split
    · exact Prod.ext hinit rfl
    · let q := authorizedCmpUpdate hpsi l0 r
      have hq := authorizedCmpUpdate_resetEchoPair hpsi l0 r
      have hout := resetEchoPair_compareSigDispatch hpsi q.1.core q.2.core
      exact hout.trans (hq.trans (Prod.ext hinit rfl))

/-- The ordinary physical/authorized prefix stopped immediately before
repaired Algorithm 14. -/
def wallSweepAuthorizedNormalBeforeSuppress
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let q0 := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let q1 := sanitizeAuthorizedPair hpsi q0
  let q2 := authorizedCheckSig hpsi q1.1 q1.2
  let q3 := authorizedDisappear hpsi q2.1 q2.2
  authorizedCompareSig hpsi q3.1 q3.2

/-- Exact named-stage expansion of the ordinary prefix. -/
theorem wallSweepAuthorizedNormalBeforeSuppress_eq_staged
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r =
      let l0 := normalizeDeletion l
      let r0 := normalizeDeletion r
      let q0 := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
      let q1 := sanitizeAuthorizedPair hpsi q0
      let q2 := authorizedCheckSig hpsi q1.1 q1.2
      let q3 := authorizedDisappear hpsi q2.1 q2.2
      authorizedCompareSig hpsi q3.1 q3.2 := by
  rfl

/-- The complete ordinary branch up to repaired Algorithm 14 frames reset and
echo, including the real CHECK leader-birth stage. -/
theorem wallSweepAuthorizedNormalBeforeSuppress_resetEchoPair
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair
        (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r) =
      authorizedResetEchoPair (l, r) := by
  unfold wallSweepAuthorizedNormalBeforeSuppress
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let q0 := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let q1 := sanitizeAuthorizedPair hpsi q0
  let q2 := authorizedCheckSig hpsi q1.1 q1.2
  let q3 := authorizedDisappear hpsi q2.1 q2.2
  let q4 := authorizedCompareSig hpsi q3.1 q3.2
  have hn := normalizeDeletionPair_resetEcho l r
  have h0 := wallSweepAuthorizedBeforeCheck_resetEchoPair hpsi kappa l0 r0
  have h1 := sanitizeAuthorizedPair_resetEchoPair hpsi q0
  have h2 := authorizedCheckSig_resetEchoPair hpsi q1.1 q1.2
  have h3 := authorizedDisappear_resetEchoPair hpsi q2.1 q2.2
  have h4 := authorizedCompareSig_resetEchoPair hpsi q3.1 q3.2
  change authorizedResetEchoPair q4 = authorizedResetEchoPair (l, r)
  have h4' : authorizedResetEchoPair q4 = authorizedResetEchoPair q3 :=
    authorizedResetEchoPair_eq_trans h4 (authorizedResetEchoPair_eta q3)
  have h3' : authorizedResetEchoPair q3 = authorizedResetEchoPair q2 :=
    authorizedResetEchoPair_eq_trans h3 (authorizedResetEchoPair_eta q2)
  have h2' : authorizedResetEchoPair q2 = authorizedResetEchoPair q1 :=
    authorizedResetEchoPair_eq_trans h2 (authorizedResetEchoPair_eta q1)
  have h1' : authorizedResetEchoPair q1 = authorizedResetEchoPair q0 :=
    h1
  have h43 := authorizedResetEchoPair_eq_trans h4' h3'
  have h42 := authorizedResetEchoPair_eq_trans h43 h2'
  have h41 := authorizedResetEchoPair_eq_trans h42 h1'
  have h40 := authorizedResetEchoPair_eq_trans h41 h0
  exact authorizedResetEchoPair_eq_trans h40 hn

/-! ## Anchors through the ordinary prefix -/

private theorem initiatorAnchor_of_authorizedPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : authorizedInitiatorAnchor b) :
    authorizedInitiatorAnchor a := by
  rw [hab]
  exact hb

private theorem responderZeroAnchor_of_authorizedPair_eq
    (hpsi : psi > 0)
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : authorizedResponderZeroAnchor hpsi b) :
    authorizedResponderZeroAnchor hpsi a := by
  rw [hab]
  exact hb

private theorem responderLeader_of_authorizedPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : authorizedResponderLeader b) :
    authorizedResponderLeader a := by
  rw [hab]
  exact hb

theorem responderEchoFalse_of_authorizedPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : authorizedResponderEchoFalse b) :
    authorizedResponderEchoFalse a := by
  rw [hab]
  exact hb

theorem initiatorEchoFalse_of_authorizedPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : authorizedInitiatorEchoFalse b) :
    authorizedInitiatorEchoFalse a := by
  rw [hab]
  exact hb

theorem leaderReseedResult_of_authorizedPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : authorizedLeaderReseedResult b) :
    authorizedLeaderReseedResult a := by
  rw [hab]
  exact hb

theorem bothNeutral_of_authorizedPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : authorizedBothNeutral b) :
    authorizedBothNeutral a := by
  rw [hab]
  exact hb

theorem initiatorLabel_eq_of_authorizedPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) :
    authorizedInitiatorLabel a = authorizedInitiatorLabel b :=
  congrArg authorizedInitiatorLabel hab

private theorem normalizeDeletion_initiator_anchor
    (u : AuthorizedAgentState psi) (h : InitiatorAnchor u.core) :
    InitiatorAnchor (normalizeDeletion u).core := by
  unfold InitiatorAnchor at h ⊢
  unfold normalizeDeletion
  split <;> exact h

private theorem normalizeDeletion_responder_zero_anchor
    (hpsi : psi > 0) (u : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi u.core) :
    ResponderZeroAnchor hpsi (normalizeDeletion u).core := by
  unfold ResponderZeroAnchor at h ⊢
  unfold normalizeDeletion
  split <;> exact h

private theorem authorizedPPsiLeaderProbeWall_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    InitiatorAnchor (authorizedPPsiLeaderProbeWall hpsi l r).1.core := by
  let l0 := if l.core.leader = true then
    { l.core with probe := false } else l.core
  let r0 := if r.core.leader = true ∨ l.core.leader = true then
    { r.core with probe := false } else r.core
  have hl0 : InitiatorAnchor l0 := by
    unfold InitiatorAnchor l0
    split <;> exact h
  have hleader := PPLLVerify.pPsi_initiator_leader_eq hpsi l0 r0
  have hshield := (PPLLVerify.pPsi_kill_fields_eq hpsi l0 r0).1
  change InitiatorAnchor (pPsi hpsi l0 r0).1
  exact ⟨hleader.trans hl0.1, hshield.trans hl0.2⟩

private theorem authorizedPPsiLeaderProbeWall_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi
      (authorizedPPsiLeaderProbeWall hpsi l r).2.core := by
  let l0 := if l.core.leader = true then
    { l.core with probe := false } else l.core
  let r0 := if r.core.leader = true ∨ l.core.leader = true then
    { r.core with probe := false } else r.core
  have hr0 : ResponderZeroAnchor hpsi r0 := by
    unfold ResponderZeroAnchor r0
    split <;> exact h
  change ResponderZeroAnchor hpsi (pPsi hpsi l0 r0).2
  exact ⟨PPLLVerify.pPsi_responder_leader_of_true
      hpsi l0 r0 hr0.1,
    (PPLLVerify.pPsi_responder_label_of_leader_zero
      hpsi l0 r0 hr0.1 hr0.2).trans hr0.2⟩

private theorem authorizedGenSig_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    InitiatorAnchor (authorizedGenSig hpsi kappa l r).1.core := by
  have hleaders := PPLLNoCheckBirthLeaderFrames.genSigSaturated_leaders
    hpsi kappa l.core r.core
  have hleader := congrArg Prod.fst hleaders
  have hkill := PPLLNoCheckBirthBoundaryFrames.genSigSaturated_kill
    hpsi kappa l.core r.core
  have hshield := congrArg Prod.fst hkill
  change InitiatorAnchor (genSigSaturated hpsi kappa l.core r.core).1
  exact ⟨hleader.trans h.1, hshield.trans h.2⟩

private theorem authorizedGenSig_responder_zero_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi (authorizedGenSig hpsi kappa l r).2.core := by
  have hleaders := PPLLNoCheckBirthLeaderFrames.genSigSaturated_leaders
    hpsi kappa l.core r.core
  have hleader := congrArg Prod.snd hleaders
  have hlabels := PPLLNoCheckBirthBoundaryFrames.genSigSaturated_labels
    hpsi kappa l.core r.core
  have hlabel := congrArg Prod.snd hlabels
  change ResponderZeroAnchor hpsi
    (genSigSaturated hpsi kappa l.core r.core).2
  exact ⟨hleader.trans h.1, hlabel.trans h.2⟩

private theorem authorizedCleanSig_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    InitiatorAnchor (authorizedCleanSig hpsi l r).1.core := by
  change InitiatorAnchor (cleanSig hpsi l.core r.core).1
  exact ⟨(PPLLVerify.cleanSig_leaders_eq hpsi l.core r.core).1.trans h.1,
    (PPLLVerify.cleanSig_kill_fields_eq hpsi l.core r.core).1.trans h.2⟩

private theorem authorizedCleanSig_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi (authorizedCleanSig hpsi l r).2.core := by
  change ResponderZeroAnchor hpsi (cleanSig hpsi l.core r.core).2
  exact ⟨(PPLLVerify.cleanSig_leaders_eq hpsi l.core r.core).2.trans h.1,
    (PPLLVerify.cleanSig_labels_eq hpsi l.core r.core).2.trans h.2⟩

private theorem authorizedEliminateSig_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    InitiatorAnchor (authorizedEliminateSig hpsi l r).1.core := by
  change InitiatorAnchor (eliminateSig hpsi l.core r.core).1
  exact ⟨(PPLLVerify.eliminateSig_leaders_eq hpsi l.core r.core).1.trans h.1,
    (PPLLVerify.eliminateSig_kill_fields_eq hpsi l.core r.core).1.trans h.2⟩

private theorem authorizedEliminateSig_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi (authorizedEliminateSig hpsi l r).2.core := by
  change ResponderZeroAnchor hpsi (eliminateSig hpsi l.core r.core).2
  exact ⟨(PPLLVerify.eliminateSig_leaders_eq hpsi l.core r.core).2.trans h.1,
    (PPLLVerify.eliminateSig_labels_eq hpsi l.core r.core).2.trans h.2⟩

private theorem authorizedSigMoveLeaderWall_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    InitiatorAnchor (authorizedSigMoveLeaderWall hpsi l r).1.core := by
  have hcore := authorizedSigMoveLeaderWall_core hpsi l r
  have hleft : (authorizedSigMoveLeaderWall hpsi l r).1.core =
      (sigMoveLeaderWall hpsi l.core r.core).1 := by
    simpa using congrArg Prod.fst hcore
  rw [hleft]
  exact ⟨(sigMoveLeaderWall_leaders_eq hpsi l.core r.core).1.trans h.1,
    (sigMoveLeaderWall_left_shield_eq hpsi l.core r.core).trans h.2⟩

private theorem authorizedSigMoveLeaderWall_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi
      (authorizedSigMoveLeaderWall hpsi l r).2.core := by
  have hcore := authorizedSigMoveLeaderWall_core hpsi l r
  have hright : (authorizedSigMoveLeaderWall hpsi l r).2.core =
      (sigMoveLeaderWall hpsi l.core r.core).2 := by
    simpa using congrArg Prod.snd hcore
  rw [hright]
  exact ⟨(sigMoveLeaderWall_leaders_eq hpsi l.core r.core).2.trans h.1,
    (sigMoveLeaderWall_labels_eq hpsi l.core r.core).2.trans h.2⟩

theorem wallSweepAuthorizedBeforeCheck_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    InitiatorAnchor
      (wallSweepAuthorizedBeforeCheck hpsi kappa l r).1.core := by
  rw [PPLLWallSweepStageFrames.wallSweepAuthorizedBeforeCheck_stages]
  exact authorizedSigMoveLeaderWall_initiator_anchor hpsi _ _
    (authorizedEliminateSig_initiator_anchor hpsi _ _
      (authorizedCleanSig_initiator_anchor hpsi _ _
        (authorizedGenSig_initiator_anchor hpsi kappa _ _
          (authorizedPPsiLeaderProbeWall_initiator_anchor hpsi l r h))))

theorem wallSweepAuthorizedBeforeCheck_responder_zero_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi
      (wallSweepAuthorizedBeforeCheck hpsi kappa l r).2.core := by
  rw [PPLLWallSweepStageFrames.wallSweepAuthorizedBeforeCheck_stages]
  exact authorizedSigMoveLeaderWall_responder_zero_anchor hpsi _ _
    (authorizedEliminateSig_responder_zero_anchor hpsi _ _
      (authorizedCleanSig_responder_zero_anchor hpsi _ _
        (authorizedGenSig_responder_zero_anchor hpsi kappa _ _
          (authorizedPPsiLeaderProbeWall_responder_zero_anchor hpsi l r h))))

private theorem sanitizeAuthorizedPair_initiator_anchor
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : InitiatorAnchor q.1.core) :
    InitiatorAnchor (sanitizeAuthorizedPair hpsi q).1.core := by
  change InitiatorAnchor (sanitizeAuthorizedTerminalEqual hpsi q.1).core
  unfold sanitizeAuthorizedTerminalEqual
  split <;> exact h

private theorem sanitizeAuthorizedPair_responder_zero_anchor
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi q.2.core) :
    ResponderZeroAnchor hpsi (sanitizeAuthorizedPair hpsi q).2.core := by
  change ResponderZeroAnchor hpsi
    (sanitizeAuthorizedTerminalEqual hpsi q.2).core
  unfold sanitizeAuthorizedTerminalEqual
  split <;> exact h

private theorem authorizedCheckSig_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    InitiatorAnchor (authorizedCheckSig hpsi l r).1.core := by
  change InitiatorAnchor (checkSig hpsi l.core r.core).1
  exact ⟨(PPLLVerify.checkSig_initiator_leader_eq
      hpsi l.core r.core).trans h.1,
    (PPLLVerify.checkSig_kill_fields_eq hpsi l.core r.core).1.trans h.2⟩

private theorem authorizedCheckSig_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi (authorizedCheckSig hpsi l r).2.core := by
  change ResponderZeroAnchor hpsi (checkSig hpsi l.core r.core).2
  exact ⟨PPLLVerify.checkSig_responder_leader_of_true
      hpsi l.core r.core h.1,
    (PPLLVerify.checkSig_labels_eq hpsi l.core r.core).2.trans h.2⟩

private theorem authorizedDisappear_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    InitiatorAnchor (authorizedDisappear hpsi l r).1.core := by
  change InitiatorAnchor (disappear hpsi l.core r.core).1
  exact ⟨(PPLLVerify.disappear_leaders_eq hpsi l.core r.core).1.trans h.1,
    (PPLLVerify.disappear_kill_fields_eq hpsi l.core r.core).1.trans h.2⟩

private theorem authorizedDisappear_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi (authorizedDisappear hpsi l r).2.core := by
  change ResponderZeroAnchor hpsi (disappear hpsi l.core r.core).2
  exact ⟨(PPLLVerify.disappear_leaders_eq hpsi l.core r.core).2.trans h.1,
    (PPLLVerify.disappear_labels_eq hpsi l.core r.core).2.trans h.2⟩

private theorem authorizedCompareSig_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    InitiatorAnchor (authorizedCompareSig hpsi l r).1.core := by
  have hleaders := authorizedCompareSig_leaders_eq hpsi l r
  have hbullet := authorizedCompareSig_bulletFieldPair hpsi l r
  have hleft := congrArg Prod.fst hbullet
  have hshield := congrArg BulletFields.shield hleft
  exact ⟨hleaders.1.trans h.1, hshield.trans h.2⟩

private theorem authorizedCompareSig_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi (authorizedCompareSig hpsi l r).2.core := by
  have hleaders := authorizedCompareSig_leaders_eq hpsi l r
  have hlabels := authorizedCompareSig_labels hpsi l r
  have hright := congrArg Prod.snd hlabels
  exact ⟨hleaders.2.trans h.1, hright.trans h.2⟩

/-- Named normalized boundary before the wall-aware pre-CHECK prefix. -/
def wallSweepNormalBeforeCheckStage (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  wallSweepAuthorizedBeforeCheck hpsi kappa
    (normalizeDeletion l) (normalizeDeletion r)

theorem wallSweepNormalBeforeCheckStage_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    wallSweepNormalBeforeCheckStage hpsi kappa l r =
      wallSweepAuthorizedBeforeCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r) := by
  rfl

/-- Named terminal-equality sanitation boundary. -/
def wallSweepNormalSanitizedStage (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  sanitizeAuthorizedPair hpsi (wallSweepNormalBeforeCheckStage hpsi kappa l r)

theorem wallSweepNormalSanitizedStage_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    wallSweepNormalSanitizedStage hpsi kappa l r =
      sanitizeAuthorizedPair hpsi
        (wallSweepNormalBeforeCheckStage hpsi kappa l r) := by
  rfl

/-- Named real-CHECK boundary. -/
def wallSweepNormalCheckedStage (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := wallSweepNormalSanitizedStage hpsi kappa l r
  authorizedCheckSig hpsi q.1 q.2

theorem wallSweepNormalCheckedStage_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let q := wallSweepNormalSanitizedStage hpsi kappa l r
    wallSweepNormalCheckedStage hpsi kappa l r =
      authorizedCheckSig hpsi q.1 q.2 := by
  rfl

/-- Named DISAPPEAR boundary. -/
def wallSweepNormalDisappearedStage (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := wallSweepNormalCheckedStage hpsi kappa l r
  authorizedDisappear hpsi q.1 q.2

theorem wallSweepNormalDisappearedStage_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let q := wallSweepNormalCheckedStage hpsi kappa l r
    wallSweepNormalDisappearedStage hpsi kappa l r =
      authorizedDisappear hpsi q.1 q.2 := by
  rfl

/-- The existing normal prefix is exactly COMPARE after the named boundaries. -/
theorem wallSweepAuthorizedNormalBeforeSuppress_eq_anchorStages
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r =
      authorizedCompareSig hpsi
        (wallSweepNormalDisappearedStage hpsi kappa l r).1
        (wallSweepNormalDisappearedStage hpsi kappa l r).2 := by
  rfl

section WallPeacePrefix

attribute [local irreducible]
  wallSweepNormalBeforeCheckStage wallSweepNormalSanitizedStage
  wallSweepNormalCheckedStage wallSweepNormalDisappearedStage
  wallSweepAuthorizedNormalBeforeSuppress

/-- Exact stage-local obligations for refining a priority-open wall edge to
the isolated Algorithm-15 `PeaceView`.  This is proof-only phase data. -/
structure WallPeaceEdgeFrame (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : Prop where
  ppsi_responder_frame :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let q := authorizedPPsiLeaderProbeWall hpsi l0 r0
    q.2.core.leader = r.core.leader ∧ q.2.core.label = r.core.label
  check_responder_frame :
    let before := wallSweepNormalSanitizedStage hpsi kappa l r
    let after := wallSweepNormalCheckedStage hpsi kappa l r
    after.2.core.leader = before.2.core.leader
  responder_zero : r.core.leader = true →
    r.core.label = ⟨0, hpsi⟩

/-- Stable successor labels discharge the wall P'_psi clause; callers need
only supply the exact real-CHECK frame and responder-zero WRITE premise. -/
theorem WallPeaceEdgeFrame.of_aligned_check_frame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hcheck :
      let before := wallSweepNormalSanitizedStage hpsi kappa l r
      let after := wallSweepNormalCheckedStage hpsi kappa l r
      after.2.core.leader = before.2.core.leader)
    (hzero : r.core.leader = true → r.core.label = ⟨0, hpsi⟩) :
    WallPeaceEdgeFrame hpsi kappa l r := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hlLabel := congrArg PeaceView.label (normalizeDeletion_peaceView l)
  have hrLabel := congrArg PeaceView.label (normalizeDeletion_peaceView r)
  change l0.core.label = l.core.label at hlLabel
  change r0.core.label = r.core.label at hrLabel
  have halign0 : r0.core.label =
      ⟨(l0.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    rw [hrLabel, hlLabel]
    exact halign
  have hppsi := pPsiLeaderProbeWall_responder_frame_of_aligned
    hpsi l0.core r0.core halign0
  refine ⟨?_, hcheck, hzero⟩
  change
    (authorizedPPsiLeaderProbeWall hpsi l0 r0).2.core.leader = r.core.leader ∧
      (authorizedPPsiLeaderProbeWall hpsi l0 r0).2.core.label = r.core.label
  exact ⟨hppsi.1.trans (by
      have h := congrArg PeaceView.leader (normalizeDeletion_peaceView r)
      exact h),
    hppsi.2.trans hrLabel⟩

/-- The complete authorized prefix through COMPARE has the input `PeaceView`
under exactly the P'_psi and CHECK leader/label obligations. -/
theorem wallSweepAuthorizedNormalBeforeSuppress_peaceView_of_frame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hframe : WallPeaceEdgeFrame hpsi kappa l r) :
    authorizedPeaceViewPair
        (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let before := wallSweepNormalBeforeCheckStage hpsi kappa l r
  let sanitized := wallSweepNormalSanitizedStage hpsi kappa l r
  let checked := wallSweepNormalCheckedStage hpsi kappa l r
  let disappeared := wallSweepNormalDisappearedStage hpsi kappa l r
  have hnorm : authorizedPeaceViewPair (l0, r0) =
      authorizedPeaceViewPair (l, r) :=
    Prod.ext (normalizeDeletion_peaceView l) (normalizeDeletion_peaceView r)
  have hppsi := hframe.ppsi_responder_frame
  change
    (authorizedPPsiLeaderProbeWall hpsi l0 r0).2.core.leader = r.core.leader ∧
      (authorizedPPsiLeaderProbeWall hpsi l0 r0).2.core.label = r.core.label
      at hppsi
  have hbefore : authorizedPeaceViewPair before =
      authorizedPeaceViewPair (l, r) := by
    have hraw := wallSweepAuthorizedBeforeCheck_peaceView_of_ppsi_frame
      hpsi kappa l0 r0
      (hppsi.1.trans (by
        have h := congrArg PeaceView.leader (normalizeDeletion_peaceView r)
        exact h.symm))
      (hppsi.2.trans (by
        have h := congrArg PeaceView.label (normalizeDeletion_peaceView r)
        exact h.symm))
    have hstage := congrArg authorizedPeaceViewPair
      (wallSweepNormalBeforeCheckStage_eq hpsi kappa l r)
    exact hstage.trans (hraw.trans hnorm)
  have hsanitized : authorizedPeaceViewPair sanitized =
      authorizedPeaceViewPair (l, r) := by
    have hstage := congrArg authorizedPeaceViewPair
      (wallSweepNormalSanitizedStage_eq hpsi kappa l r)
    exact hstage.trans
      ((sanitizeAuthorizedPair_peaceViewPair hpsi before).trans hbefore)
  have hcheckFrame := hframe.check_responder_frame
  change checked.2.core.leader = sanitized.2.core.leader at hcheckFrame
  have hcheckedEq := wallSweepNormalCheckedStage_eq hpsi kappa l r
  have hcheckedLeader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) hcheckedEq
  have hcheckRaw :
      (authorizedCheckSig hpsi sanitized.1 sanitized.2).2.core.leader =
        sanitized.2.core.leader := hcheckedLeader.symm.trans hcheckFrame
  have hchecked : authorizedPeaceViewPair checked =
      authorizedPeaceViewPair (l, r) := by
    have hstage := congrArg authorizedPeaceViewPair hcheckedEq
    exact hstage.trans
      ((authorizedCheckSig_peaceViewPair_of_responder_frame
        hpsi sanitized.1 sanitized.2 hcheckRaw).trans hsanitized)
  have hdisappeared : authorizedPeaceViewPair disappeared =
      authorizedPeaceViewPair (l, r) := by
    have hstage := congrArg authorizedPeaceViewPair
      (wallSweepNormalDisappearedStage_eq hpsi kappa l r)
    exact hstage.trans
      ((authorizedDisappear_peaceViewPair hpsi checked.1 checked.2).trans
        hchecked)
  have hout := congrArg authorizedPeaceViewPair
    (wallSweepAuthorizedNormalBeforeSuppress_eq_anchorStages
      hpsi kappa l r)
  exact hout.trans ((authorizedCompareSig_peaceViewPair
    hpsi disappeared.1 disappeared.2).trans hdisappeared)

end WallPeacePrefix

private theorem wallSweepNormalBeforeCheckStage_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepNormalBeforeCheckStage hpsi kappa l r) := by
  exact initiatorAnchor_of_authorizedPair_eq
    (wallSweepNormalBeforeCheckStage_eq hpsi kappa l r)
      (wallSweepAuthorizedBeforeCheck_initiator_anchor hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r)
          (normalizeDeletion_initiator_anchor l h))

private theorem wallSweepNormalBeforeCheckStage_responder_zero_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepNormalBeforeCheckStage hpsi kappa l r) := by
  exact responderZeroAnchor_of_authorizedPair_eq hpsi
    (wallSweepNormalBeforeCheckStage_eq hpsi kappa l r)
      (wallSweepAuthorizedBeforeCheck_responder_zero_anchor hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r)
          (normalizeDeletion_responder_zero_anchor hpsi r h))

private theorem wallSweepNormalSanitizedStage_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepNormalSanitizedStage hpsi kappa l r) := by
  exact initiatorAnchor_of_authorizedPair_eq
    (wallSweepNormalSanitizedStage_eq hpsi kappa l r)
      (sanitizeAuthorizedPair_initiator_anchor hpsi
        (wallSweepNormalBeforeCheckStage hpsi kappa l r)
          (wallSweepNormalBeforeCheckStage_initiator_anchor hpsi kappa l r h))

private theorem wallSweepNormalSanitizedStage_responder_zero_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepNormalSanitizedStage hpsi kappa l r) := by
  exact responderZeroAnchor_of_authorizedPair_eq hpsi
    (wallSweepNormalSanitizedStage_eq hpsi kappa l r)
      (sanitizeAuthorizedPair_responder_zero_anchor hpsi
        (wallSweepNormalBeforeCheckStage hpsi kappa l r)
          (wallSweepNormalBeforeCheckStage_responder_zero_anchor
            hpsi kappa l r h))

private theorem wallSweepNormalCheckedStage_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepNormalCheckedStage hpsi kappa l r) := by
  let q := wallSweepNormalSanitizedStage hpsi kappa l r
  exact initiatorAnchor_of_authorizedPair_eq
    (wallSweepNormalCheckedStage_eq hpsi kappa l r)
      (authorizedCheckSig_initiator_anchor hpsi q.1 q.2
        (wallSweepNormalSanitizedStage_initiator_anchor hpsi kappa l r h))

private theorem wallSweepNormalCheckedStage_responder_zero_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepNormalCheckedStage hpsi kappa l r) := by
  let q := wallSweepNormalSanitizedStage hpsi kappa l r
  exact responderZeroAnchor_of_authorizedPair_eq hpsi
    (wallSweepNormalCheckedStage_eq hpsi kappa l r)
      (authorizedCheckSig_responder_zero_anchor hpsi q.1 q.2
        (wallSweepNormalSanitizedStage_responder_zero_anchor hpsi kappa l r h))

private theorem wallSweepNormalDisappearedStage_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepNormalDisappearedStage hpsi kappa l r) := by
  let q := wallSweepNormalCheckedStage hpsi kappa l r
  exact initiatorAnchor_of_authorizedPair_eq
    (wallSweepNormalDisappearedStage_eq hpsi kappa l r)
      (authorizedDisappear_initiator_anchor hpsi q.1 q.2
        (wallSweepNormalCheckedStage_initiator_anchor hpsi kappa l r h))

private theorem wallSweepNormalDisappearedStage_responder_zero_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepNormalDisappearedStage hpsi kappa l r) := by
  let q := wallSweepNormalCheckedStage hpsi kappa l r
  exact responderZeroAnchor_of_authorizedPair_eq hpsi
    (wallSweepNormalDisappearedStage_eq hpsi kappa l r)
      (authorizedDisappear_responder_zero_anchor hpsi q.1 q.2
        (wallSweepNormalCheckedStage_responder_zero_anchor hpsi kappa l r h))

/-- The ordinary prefix through real CHECK and repaired COMPARE preserves a
shielded initiator leader. -/
theorem wallSweepAuthorizedNormalBeforeSuppress_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r) := by
  apply initiatorAnchor_of_authorizedPair_eq
    (wallSweepAuthorizedNormalBeforeSuppress_eq_anchorStages
      hpsi kappa l r)
  exact authorizedCompareSig_initiator_anchor hpsi
    (wallSweepNormalDisappearedStage hpsi kappa l r).1
    (wallSweepNormalDisappearedStage hpsi kappa l r).2
      (wallSweepNormalDisappearedStage_initiator_anchor hpsi kappa l r h)

/-- The ordinary prefix preserves an existing responder leader hosted at
label zero. -/
theorem wallSweepAuthorizedNormalBeforeSuppress_responder_zero_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r) := by
  apply responderZeroAnchor_of_authorizedPair_eq hpsi
    (wallSweepAuthorizedNormalBeforeSuppress_eq_anchorStages
      hpsi kappa l r)
  exact authorizedCompareSig_responder_zero_anchor hpsi
    (wallSweepNormalDisappearedStage hpsi kappa l r).1
    (wallSweepNormalDisappearedStage hpsi kappa l r).2
      (wallSweepNormalDisappearedStage_responder_zero_anchor
        hpsi kappa l r h)

private theorem normalizeDeletion_label_eq (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl

private theorem authorizedPPsiLeaderProbeWall_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedPPsiLeaderProbeWall hpsi l r).1.core.label = l.core.label := by
  let l0 := if l.core.leader = true then
    { l.core with probe := false } else l.core
  let r0 := if r.core.leader = true ∨ l.core.leader = true then
    { r.core with probe := false } else r.core
  have hl0 : l0.label = l.core.label := by
    unfold l0
    split <;> rfl
  change (pPsi hpsi l0 r0).1.label = l.core.label
  exact (PPLLVerify.pPsi_initiator_label_eq hpsi l0 r0).trans hl0

private theorem authorizedGenSig_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (authorizedGenSig hpsi kappa l r).1.core.label = l.core.label := by
  have hlabels := PPLLNoCheckBirthBoundaryFrames.genSigSaturated_labels
    hpsi kappa l.core r.core
  exact congrArg Prod.fst hlabels

private theorem authorizedCleanSig_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCleanSig hpsi l r).1.core.label = l.core.label :=
  (PPLLVerify.cleanSig_labels_eq hpsi l.core r.core).1

private theorem authorizedEliminateSig_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedEliminateSig hpsi l r).1.core.label = l.core.label :=
  (PPLLVerify.eliminateSig_labels_eq hpsi l.core r.core).1

private theorem authorizedSigMoveLeaderWall_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedSigMoveLeaderWall hpsi l r).1.core.label = l.core.label := by
  have hcore := authorizedSigMoveLeaderWall_core hpsi l r
  have hL := congrArg Prod.fst hcore
  have hlabel := (sigMoveLeaderWall_labels_eq hpsi l.core r.core).1
  have hc := congrArg AgentState.label hL
  exact hc.trans hlabel

theorem wallSweepAuthorizedBeforeCheck_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (wallSweepAuthorizedBeforeCheck hpsi kappa l r).1.core.label =
      l.core.label := by
  rw [PPLLWallSweepStageFrames.wallSweepAuthorizedBeforeCheck_stages]
  exact (authorizedSigMoveLeaderWall_initiator_label_eq hpsi _ _).trans
    ((authorizedEliminateSig_initiator_label_eq hpsi _ _).trans
      ((authorizedCleanSig_initiator_label_eq hpsi _ _).trans
        ((authorizedGenSig_initiator_label_eq hpsi kappa _ _).trans
          (authorizedPPsiLeaderProbeWall_initiator_label_eq hpsi l r))))

private theorem sanitizeAuthorizedPair_initiator_label_eq
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (sanitizeAuthorizedPair hpsi q).1.core.label = q.1.core.label := by
  change (sanitizeAuthorizedTerminalEqual hpsi q.1).core.label = q.1.core.label
  unfold sanitizeAuthorizedTerminalEqual
  split <;> rfl

private theorem sanitizeAuthorizedPair_initiatorLabel_frame
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedInitiatorLabel (sanitizeAuthorizedPair hpsi q) =
      authorizedInitiatorLabel q :=
  sanitizeAuthorizedPair_initiator_label_eq hpsi q

private theorem authorizedCheckSig_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCheckSig hpsi l r).1.core.label = l.core.label :=
  (PPLLVerify.checkSig_labels_eq hpsi l.core r.core).1

private theorem authorizedCheckSig_initiatorLabel_frame
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedInitiatorLabel (authorizedCheckSig hpsi q.1 q.2) =
      authorizedInitiatorLabel q :=
  authorizedCheckSig_initiator_label_eq hpsi q.1 q.2

private theorem authorizedDisappear_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedDisappear hpsi l r).1.core.label = l.core.label :=
  (PPLLVerify.disappear_labels_eq hpsi l.core r.core).1

private theorem authorizedDisappear_initiatorLabel_frame
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedInitiatorLabel (authorizedDisappear hpsi q.1 q.2) =
      authorizedInitiatorLabel q :=
  authorizedDisappear_initiator_label_eq hpsi q.1 q.2

private theorem authorizedCompareSig_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCompareSig hpsi l r).1.core.label = l.core.label := by
  have hlabels := authorizedCompareSig_labels hpsi l r
  have hL := congrArg Prod.fst hlabels
  exact hL

private theorem authorizedCompareSig_initiatorLabel_frame
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedInitiatorLabel (authorizedCompareSig hpsi q.1 q.2) =
      authorizedInitiatorLabel q :=
  authorizedCompareSig_initiator_label_eq hpsi q.1 q.2

private theorem wallSweepNormalBeforeCheckStage_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel
      (wallSweepNormalBeforeCheckStage hpsi kappa l r) = l.core.label := by
  rw [wallSweepNormalBeforeCheckStage_eq]
  exact (wallSweepAuthorizedBeforeCheck_initiator_label_eq hpsi kappa
    (normalizeDeletion l) (normalizeDeletion r)).trans
      (normalizeDeletion_label_eq l)

private theorem wallSweepNormalSanitizedStage_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel
      (wallSweepNormalSanitizedStage hpsi kappa l r) = l.core.label := by
  rw [wallSweepNormalSanitizedStage_eq]
  exact (sanitizeAuthorizedPair_initiatorLabel_frame hpsi
    (wallSweepNormalBeforeCheckStage hpsi kappa l r)).trans
      (wallSweepNormalBeforeCheckStage_initiator_label_eq hpsi kappa l r)

private theorem wallSweepNormalCheckedStage_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel
      (wallSweepNormalCheckedStage hpsi kappa l r) = l.core.label := by
  let q := wallSweepNormalSanitizedStage hpsi kappa l r
  rw [wallSweepNormalCheckedStage_eq]
  exact (authorizedCheckSig_initiatorLabel_frame hpsi q).trans
    (wallSweepNormalSanitizedStage_initiator_label_eq hpsi kappa l r)

private theorem wallSweepNormalDisappearedStage_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel
      (wallSweepNormalDisappearedStage hpsi kappa l r) = l.core.label := by
  let q := wallSweepNormalCheckedStage hpsi kappa l r
  rw [wallSweepNormalDisappearedStage_eq]
  exact (authorizedDisappear_initiatorLabel_frame hpsi q).trans
    (wallSweepNormalCheckedStage_initiator_label_eq hpsi kappa l r)

theorem wallSweepAuthorizedNormalBeforeSuppress_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel
      (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r) =
      l.core.label := by
  rw [wallSweepAuthorizedNormalBeforeSuppress_eq_anchorStages]
  exact (authorizedCompareSig_initiatorLabel_frame hpsi
    (wallSweepNormalDisappearedStage hpsi kappa l r)).trans
      (wallSweepNormalDisappearedStage_initiator_label_eq hpsi kappa l r)

private theorem cleanupAuxPair_groupInfoStart (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (groupInfoStart hpsi l r) = cleanupAuxPair (l, r) := by
  simp [groupInfoStart, cleanupAuxPair, CleanupAuxView.ofState]

private theorem cleanupAuxPair_groupInfoSet (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (groupInfoSet hpsi l r) = cleanupAuxPair (l, r) := by
  unfold groupInfoSet cleanupAuxPair
  repeat (first | rfl | split)

private theorem cleanupAuxPair_groupInfoUnset (l r : AgentState psi) :
    cleanupAuxPair (groupInfoUnset l r) = cleanupAuxPair (l, r) := by
  unfold groupInfoUnset cleanupAuxPair
  repeat (first | rfl | split)

private theorem cleanupAuxPair_groupInfo (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (groupInfo hpsi l r) = cleanupAuxPair (l, r) := by
  rw [groupInfo_eq_staged]
  let q0 := groupInfoStart hpsi l r
  let q1 := groupInfoSet hpsi q0.1 q0.2
  exact (cleanupAuxPair_groupInfoUnset q1.1 q1.2).trans
    ((cleanupAuxPair_groupInfoSet hpsi q0.1 q0.2).trans
      (cleanupAuxPair_groupInfoStart hpsi l r))

private theorem cleanupAuxPair_gensigStart (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (gensigWriteseqStart hpsi l r) =
      cleanupAuxPair (l, r) := by
  simp [gensigWriteseqStart, cleanupAuxPair, CleanupAuxView.ofState]

private theorem cleanupAuxPair_gensigEmit (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (gensigWriteseqEmit hpsi l r) =
      cleanupAuxPair (l, r) := by
  simp [gensigWriteseqEmit, cleanupAuxPair, CleanupAuxView.ofState]

private theorem cleanupAuxPair_gensigPropagate (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (gensigWriteseqPropagate hpsi l r) =
      cleanupAuxPair (l, r) := by
  simp [gensigWriteseqPropagate, cleanupAuxPair, CleanupAuxView.ofState]

private theorem cleanupAuxPair_gensigFinish (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (gensigWriteseqFinish hpsi l r) =
      cleanupAuxPair (l, r) := by
  unfold gensigWriteseqFinish cleanupAuxPair
  split <;> rfl

private theorem cleanupAuxPair_gensigWriteseq (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (gensigWriteseq hpsi l r) = cleanupAuxPair (l, r) := by
  rw [gensigWriteseq_eq_staged]
  let q0 := gensigWriteseqStart hpsi l r
  let q1 := gensigWriteseqEmit hpsi q0.1 q0.2
  let q2 := gensigWriteseqPropagate hpsi q1.1 q1.2
  exact (cleanupAuxPair_gensigFinish hpsi q2.1 q2.2).trans
    ((cleanupAuxPair_gensigPropagate hpsi q1.1 q1.2).trans
      ((cleanupAuxPair_gensigEmit hpsi q0.1 q0.2).trans
        (cleanupAuxPair_gensigStart hpsi l r)))

private theorem cleanupAuxPair_writeSeqLeaderMove (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeSeqLeaderMove hpsi l r) = cleanupAuxPair (l, r) := by
  unfold writeSeqLeaderMove cleanupAuxPair
  split <;> rfl

private theorem cleanupAuxPair_writeSeqGenerate (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeSeqGenerate hpsi l r) = cleanupAuxPair (l, r) := by
  unfold writeSeqGenerate
  split
  · exact cleanupAuxPair_gensigWriteseq hpsi l r
  · rfl

private theorem cleanupAux_writeSeqSetWriteReady (u : AgentState psi) :
    CleanupAuxView.ofState (writeSeqSetWriteReady u) =
      CleanupAuxView.ofState u := by
  unfold writeSeqSetWriteReady
  cases u.path3 <;> repeat (first | rfl | split)

private theorem cleanupAux_writeSeqCheckBit (u : AgentState psi) :
    CleanupAuxView.ofState (writeSeqCheckBit u) = CleanupAuxView.ofState u := by
  unfold writeSeqCheckBit
  cases u.path3 <;> rfl

private theorem cleanupAux_writeSeqSetWriteAct (u : AgentState psi) :
    CleanupAuxView.ofState (writeSeqSetWriteAct u) =
      CleanupAuxView.ofState u := by
  unfold writeSeqSetWriteAct
  dsimp only
  repeat (first | rfl | split)

private theorem cleanupAux_writeSeqFinalR (u : AgentState psi) :
    CleanupAuxView.ofState (writeSeqFinalR u) = CleanupAuxView.ofState u := by
  unfold writeSeqFinalR
  cases u.path3 <;> repeat (first | rfl | split)

private theorem cleanupAuxPair_writeSeqReady (l r : AgentState psi) :
    cleanupAuxPair (writeSeqReady l r) = cleanupAuxPair (l, r) := by
  unfold writeSeqReady cleanupAuxPair
  rw [cleanupAux_writeSeqSetWriteReady, cleanupAux_writeSeqSetWriteReady]

private theorem cleanupAuxPair_writeSeqCompare (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeSeqCompare hpsi l r) = cleanupAuxPair (l, r) := by
  let r0 := if r.label = ⟨0, hpsi⟩ ∧ r.write_state = .ready then
    writeSeqCheckBit r else r
  let r1 := if l.label.val < psi - 1 ∧ l.write_state = .equal ∧
      r0.write_state = .ready then writeSeqCheckBit r0 else r0
  have h0 : CleanupAuxView.ofState r0 = CleanupAuxView.ofState r := by
    dsimp only [r0]
    split
    · exact cleanupAux_writeSeqCheckBit r
    · rfl
  have h1 : CleanupAuxView.ofState r1 = CleanupAuxView.ofState r0 := by
    dsimp only [r1]
    split
    · exact cleanupAux_writeSeqCheckBit r0
    · rfl
  change cleanupAuxPair (l, r1) = cleanupAuxPair (l, r)
  unfold cleanupAuxPair
  rw [h1, h0]

private theorem cleanupAuxPair_writeSeqCommands (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeSeqCommands hpsi l r) = cleanupAuxPair (l, r) := by
  let l0 := writeSeqSetWriteAct l
  let r0 := writeSeqSetWriteAct r
  let r1 := if r0.label = ⟨psi - 1, by omega⟩ ∧
      r0.write_state = .equal then writeSeqFinalR r0 else r0
  have hl0 := cleanupAux_writeSeqSetWriteAct l
  have hr0 := cleanupAux_writeSeqSetWriteAct r
  have hr1 : CleanupAuxView.ofState r1 = CleanupAuxView.ofState r0 := by
    dsimp only [r1]
    split
    · exact cleanupAux_writeSeqFinalR r0
    · rfl
  change cleanupAuxPair (l0, r1) = cleanupAuxPair (l, r)
  unfold cleanupAuxPair
  rw [hl0, hr1, hr0]

private theorem cleanupAuxPair_writeSeqPrepare (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeSeqPrepare hpsi l r) = cleanupAuxPair (l, r) := by
  let q0 := writeSeqReady l r
  let q1 := writeSeqCompare hpsi q0.1 q0.2
  exact (cleanupAuxPair_writeSeqCommands hpsi q1.1 q1.2).trans
    ((cleanupAuxPair_writeSeqCompare hpsi q0.1 q0.2).trans
      (cleanupAuxPair_writeSeqReady l r))

private theorem cleanupAuxPair_writeSeqThroughPrepare (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeSeqThroughPrepare hpsi l r) =
      cleanupAuxPair (l, r) := by
  let q0 := writeSeqLeaderMove hpsi l r
  let q1 := groupInfo hpsi q0.1 q0.2
  let q2 := writeSeqGenerate hpsi q1.1 q1.2
  exact (cleanupAuxPair_writeSeqPrepare hpsi q2.1 q2.2).trans
    ((cleanupAuxPair_writeSeqGenerate hpsi q1.1 q1.2).trans
      ((cleanupAuxPair_groupInfo hpsi q0.1 q0.2).trans
        (cleanupAuxPair_writeSeqLeaderMove hpsi l r)))

private theorem cleanupAux_gatePreparedIncrement (u : AgentState psi) :
    CleanupAuxView.ofState (gatePreparedIncrement u) =
      CleanupAuxView.ofState u := by
  unfold gatePreparedIncrement clearIncrementAction
  repeat (first | rfl | split)

private theorem cleanupAux_writeActionActivate (hpsi : psi > 0)
    (u : AgentState psi) :
    CleanupAuxView.ofState (writeActionActivate hpsi u) =
      CleanupAuxView.ofState u := by
  unfold writeActionActivate
  split <;> rfl

private theorem cleanupAux_writeActionApplyOverwrite (u : AgentState psi) :
    CleanupAuxView.ofState (writeActionApplyOverwrite u) =
      CleanupAuxView.ofState u := by
  unfold writeActionApplyOverwrite
  cases u.path3 <;> rfl

private theorem cleanupAux_writeActionApplyMoveFlip (u : AgentState psi) :
    CleanupAuxView.ofState (writeActionApplyMoveFlip u) =
      CleanupAuxView.ofState u := by
  unfold writeActionApplyMoveFlip
  cases u.path3 <;> rfl

private theorem cleanupAuxPair_writeActionExecute (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeActionExecute hpsi l r) = cleanupAuxPair (l, r) := by
  by_cases hrun : l.label < r.label ∨ r.label = ⟨0, hpsi⟩
  · let r0 := if r.write_state = .overwrite then
      writeActionApplyOverwrite r else r
    let r1 := if r0.write_state = .move_flip then
      writeActionApplyMoveFlip r0 else r0
    let r2 := if r1.write_state = .increment_group then
      if r1.bit = true then { r1 with bit := false }
      else { r1 with bit := true, write_state := .depart }
      else r1
    let l0 := if r2.label ≠ ⟨0, hpsi⟩ then
      { l with write_state := r2.write_state } else l
    have hr0 : CleanupAuxView.ofState r0 = CleanupAuxView.ofState r := by
      dsimp only [r0]
      split
      · exact cleanupAux_writeActionApplyOverwrite r
      · rfl
    have hr1 : CleanupAuxView.ofState r1 = CleanupAuxView.ofState r0 := by
      dsimp only [r1]
      split
      · exact cleanupAux_writeActionApplyMoveFlip r0
      · rfl
    have hr2 : CleanupAuxView.ofState r2 = CleanupAuxView.ofState r1 := by
      dsimp only [r2]
      repeat (first | rfl | split)
    have hl0 : CleanupAuxView.ofState l0 = CleanupAuxView.ofState l := by
      dsimp only [l0]
      split <;> rfl
    unfold writeActionExecute
    rw [if_pos hrun]
    change cleanupAuxPair (l0, { r2 with write_state := .depart }) =
      cleanupAuxPair (l, r)
    unfold cleanupAuxPair
    rw [hl0]
    change (_, CleanupAuxView.ofState r2) = _
    rw [hr2, hr1, hr0]
  · unfold writeActionExecute
    rw [if_neg hrun]

private theorem cleanupAuxPair_writeAction (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeAction hpsi l r) = cleanupAuxPair (l, r) := by
  rw [writeAction_eq_staged]
  let l0 := writeActionActivate hpsi l
  let r0 := writeActionActivate hpsi r
  have hq := cleanupAuxPair_writeActionExecute hpsi l0 r0
  have hbase : cleanupAuxPair (l0, r0) = cleanupAuxPair (l, r) := by
    unfold cleanupAuxPair
    rw [cleanupAux_writeActionActivate hpsi l,
      cleanupAux_writeActionActivate hpsi r]
  exact hq.trans hbase

private theorem cleanupAuxPair_moveWsigStart (l r : AgentState psi) :
    cleanupAuxPair (moveWsigStart l r) = cleanupAuxPair (l, r) := by
  unfold moveWsigStart moveWsigCheckGenWs cleanupAuxPair
  repeat (first | rfl | split)

private theorem cleanupAux_moveWsigCheckLast (u : AgentState psi) :
    CleanupAuxView.ofState (moveWsigCheckLast u) = CleanupAuxView.ofState u := by
  unfold moveWsigCheckLast
  cases u.path3 <;> repeat (first | rfl | split)

private theorem cleanupAuxPair_moveWsigTransfer (l r : AgentState psi) :
    cleanupAuxPair (moveWsigTransfer l r) = cleanupAuxPair (l, r) := by
  cases hlpath : l.path3 with
  | none => simp [moveWsigTransfer, hlpath, cleanupAuxPair,
      CleanupAuxView.ofState]
  | some p3 =>
      cases hrpath : r.path3 with
      | some p3r => simp [moveWsigTransfer, hlpath, hrpath, cleanupAuxPair,
          CleanupAuxView.ofState]
      | none =>
          by_cases hdepart : l.write_state = .depart
          · by_cases hecho : r.ws_echo = false
            · simp [moveWsigTransfer, hlpath, hrpath, hdepart, hecho,
                cleanupAuxPair, CleanupAuxView.ofState]
            · simp [moveWsigTransfer, hlpath, hrpath, hdepart, hecho,
                cleanupAuxPair, CleanupAuxView.ofState]
          · simp [moveWsigTransfer, hlpath, hrpath, hdepart]

private theorem cleanupAuxPair_moveWsigMoveWrite (l r : AgentState psi) :
    cleanupAuxPair (moveWsigMoveWrite l r) = cleanupAuxPair (l, r) := by
  unfold moveWsigMoveWrite cleanupAuxPair
  split <;> rfl

private theorem cleanupAuxPair_moveWsigLeaderSignal (l r : AgentState psi) :
    cleanupAuxPair (moveWsigLeaderSignal l r) = cleanupAuxPair (l, r) := by
  unfold moveWsigLeaderSignal cleanupAuxPair
  split <;> rfl

private theorem cleanupAuxPair_moveWsigSignalMove (l r : AgentState psi) :
    cleanupAuxPair (moveWsigSignalMove l r) = cleanupAuxPair (l, r) := by
  unfold moveWsigSignalMove cleanupAuxPair
  repeat (first | rfl | split)

private theorem cleanupAuxPair_moveWsigEchoMove (l r : AgentState psi) :
    cleanupAuxPair (moveWsigEchoMove l r) = cleanupAuxPair (l, r) := by
  unfold moveWsigEchoMove cleanupAuxPair
  repeat (first | rfl | split)

private theorem cleanupAuxPair_moveWsigFinish (l r : AgentState psi) :
    cleanupAuxPair (moveWsigFinish l r) = cleanupAuxPair (l, r) := by
  let q0 := moveWsigMoveWrite l r
  let q1 := moveWsigLeaderSignal q0.1 q0.2
  let q2 := moveWsigSignalMove q1.1 q1.2
  exact (cleanupAuxPair_moveWsigEchoMove q2.1 q2.2).trans
    ((cleanupAuxPair_moveWsigSignalMove q1.1 q1.2).trans
      ((cleanupAuxPair_moveWsigLeaderSignal q0.1 q0.2).trans
        (cleanupAuxPair_moveWsigMoveWrite l r)))

private theorem cleanupAuxPair_moveWsig (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (moveWsig hpsi l r) = cleanupAuxPair (l, r) := by
  rw [moveWsig_eq_staged]
  let q0 := moveWsigStart l r
  let l1 := moveWsigCheckLast q0.1
  let q1 := moveWsigTransfer l1 q0.2
  have hcheck : cleanupAuxPair (l1, q0.2) = cleanupAuxPair q0 := by
    unfold cleanupAuxPair
    rw [cleanupAux_moveWsigCheckLast q0.1]
  exact (cleanupAuxPair_moveWsigFinish q1.1 q1.2).trans
    ((cleanupAuxPair_moveWsigTransfer l1 q0.2).trans
      (hcheck.trans (cleanupAuxPair_moveWsigStart l r)))

private theorem cleanupAuxPair_writeSeqAfterPrepare (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeSeqAfterPrepare hpsi l r) =
      cleanupAuxPair (l, r) := by
  let q := writeAction hpsi l r
  exact (cleanupAuxPair_moveWsig hpsi q.1 q.2).trans
    (cleanupAuxPair_writeAction hpsi l r)

/-- The gated WRITE sequence frames the five cleanup controls not represented
by `ComparisonTrackedView`. -/
theorem writeSeqIncrementGate_cleanupAux_frame (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (writeSeqIncrementGate hpsi l r) =
      cleanupAuxPair (l, r) := by
  let q := writeSeqThroughPrepare hpsi l r
  let qg := (gatePreparedIncrement q.1, gatePreparedIncrement q.2)
  change cleanupAuxPair (writeSeqAfterPrepare hpsi qg.1 qg.2) = _
  have hgate : cleanupAuxPair qg = cleanupAuxPair q := by
    unfold cleanupAuxPair qg
    rw [cleanupAux_gatePreparedIncrement q.1,
      cleanupAux_gatePreparedIncrement q.2]
  exact (cleanupAuxPair_writeSeqAfterPrepare hpsi qg.1 qg.2).trans
    (hgate.trans (cleanupAuxPair_writeSeqThroughPrepare hpsi l r))

private theorem comparisonTracked_gatePreparedIncrement (u : AgentState psi) :
    ComparisonTrackedView.ofState (gatePreparedIncrement u) =
      ComparisonTrackedView.ofState u := by
  unfold gatePreparedIncrement clearIncrementAction
    ComparisonTrackedView.ofState
  repeat (first | rfl | split)

/-- The same gated WRITE sequence reuses the existing factored proof for the
four comparison-history fields.  The pair form avoids unfolding the complete
WRITE result merely to repackage its two projections as a conjunction. -/
theorem writeSeqIncrementGate_comparisonTracked_pair (hpsi : psi > 0)
    (l r : AgentState psi) :
    comparisonTrackedPair (writeSeqIncrementGate hpsi l r) =
      comparisonTrackedPair (l, r) := by
  let q := writeSeqThroughPrepare hpsi l r
  let qg := (gatePreparedIncrement q.1, gatePreparedIncrement q.2)
  have hprefix := writeSeqThroughPrepare_comparisonTracked_pair hpsi l r
  have hgate : comparisonTrackedPair qg = comparisonTrackedPair q := by
    unfold comparisonTrackedPair qg
    rw [comparisonTracked_gatePreparedIncrement q.1,
      comparisonTracked_gatePreparedIncrement q.2]
  have hsuffix := writeSeqAfterPrepare_comparisonTracked_pair
    hpsi qg.1 qg.2
  change comparisonTrackedPair (writeSeqAfterPrepare hpsi qg.1 qg.2) = _
  exact hsuffix.trans (hgate.trans hprefix)

/-! ## Post-suppression transport -/

private theorem cleanupAuxPair_eliminateFire (hpsi : psi > 0)
    (l r : AgentState psi) :
    cleanupAuxPair (eliminateLeadersNoCollisionFire hpsi l r) =
      cleanupAuxPair (l, r) := by
  unfold eliminateLeadersNoCollisionFire cleanupAuxPair
  repeat (first | rfl | split)

private theorem cleanupAuxPair_eliminateMove (nextLabel : Fin psi)
    (l r : AgentState psi) :
    cleanupAuxPair (eliminateLeadersNoCollisionMove nextLabel l r) =
      cleanupAuxPair (l, r) := by
  unfold eliminateLeadersNoCollisionMove cleanupAuxPair
  repeat (first | rfl | split)

private theorem cleanupAuxPair_eliminateSignal (nextLabel : Fin psi)
    (l r : AgentState psi) :
    cleanupAuxPair (eliminateLeadersNoCollisionSignal nextLabel l r) =
      cleanupAuxPair (l, r) := by
  unfold eliminateLeadersNoCollisionSignal cleanupAuxPair
  repeat (first | rfl | split)

private theorem cleanupAuxPair_eliminateSignalLeaderSink
    (nextLabel : Fin psi) (l r : AgentState psi) :
    cleanupAuxPair
        (eliminateLeadersNoCollisionSignalLeaderSink nextLabel l r) =
      cleanupAuxPair (l, r) := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink cleanupAuxPair
  repeat (first | rfl | split)

private theorem eliminateLeadersNoCollision_cleanupAux_pair
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (eliminateLeadersNoCollision hpsi l r) =
      cleanupAuxPair (l, r) := by
  rw [eliminateLeadersNoCollision_eq_staged]
  let nextLabel : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let q0 := eliminateLeadersNoCollisionFire hpsi l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  exact (cleanupAuxPair_eliminateSignal nextLabel q1.1 q1.2).trans
    ((cleanupAuxPair_eliminateMove nextLabel q0.1 q0.2).trans
      (cleanupAuxPair_eliminateFire hpsi l r))

private theorem eliminateLeadersNoCollisionLeaderSink_cleanupAux_pair
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (eliminateLeadersNoCollisionLeaderSink hpsi l r) =
      cleanupAuxPair (l, r) := by
  let nextLabel : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let q0 := eliminateLeadersNoCollisionFire hpsi l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  exact (cleanupAuxPair_eliminateSignalLeaderSink
    nextLabel q1.1 q1.2).trans
      ((cleanupAuxPair_eliminateMove nextLabel q0.1 q0.2).trans
        (cleanupAuxPair_eliminateFire hpsi l r))

/-- Equality of the two structured projections transports comparison
neutrality.  This is the only place the two views are reassembled into the
seven-field predicate used by the wall sweep. -/
private theorem neutral_of_tracked_aux_eq {old out : AgentState psi}
    (htracked : ComparisonTrackedView.ofState out =
      ComparisonTrackedView.ofState old)
    (haux : CleanupAuxView.ofState out = CleanupAuxView.ofState old)
    (hold : ComparisonNeutral old) : ComparisonNeutral out := by
  have hs := congrArg ComparisonTrackedView.state htracked
  have hpath := congrArg ComparisonTrackedView.path htracked
  have hpath2 := congrArg ComparisonTrackedView.path2 htracked
  have hpCarry := congrArg ComparisonTrackedView.pCarry htracked
  have hpath4 := congrArg CleanupAuxView.path4 haux
  have hpath5 := congrArg CleanupAuxView.path5 haux
  have hp := congrArg CleanupAuxView.p haux
  change out.state = old.state at hs
  change out.path = old.path at hpath
  change out.path2 = old.path2 at hpath2
  change out.p_carry = old.p_carry at hpCarry
  change out.path4 = old.path4 at hpath4
  change out.path5 = old.path5 at hpath5
  change out.p = old.p at hp
  exact ⟨hs.trans hold.1,
    hpath.trans hold.2.1,
    hpath2.trans hold.2.2.1,
    hpath4.trans hold.2.2.2.1,
    hpath5.trans hold.2.2.2.2.1,
    hp.trans hold.2.2.2.2.2.1,
    hpCarry.trans hold.2.2.2.2.2.2⟩

private theorem resetCmd_of_cleanupAux_eq {old out : AgentState psi}
    (haux : CleanupAuxView.ofState out = CleanupAuxView.ofState old) :
    out.reset_cmd = old.reset_cmd := by
  have h := congrArg CleanupAuxView.resetCmd haux
  change out.reset_cmd = old.reset_cmd at h
  exact h

private theorem echo_of_cleanupAux_eq {old out : AgentState psi}
    (haux : CleanupAuxView.ofState out = CleanupAuxView.ofState old) :
    out.echo = old.echo := by
  have h := congrArg CleanupAuxView.echo haux
  change out.echo = old.echo at h
  exact h

/-- Comparison-history projection after erasing the authorization wrapper. -/
def authorizedComparisonTrackedPair
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :=
  comparisonTrackedPair (q.1.core, q.2.core)

/-- Remaining cleanup projection after erasing the authorization wrapper. -/
def authorizedCleanupAuxPair
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :=
  cleanupAuxPair (q.1.core, q.2.core)

private theorem authorizedReconcile_comparisonTrackedPair
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    authorizedComparisonTrackedPair (authorizedReconcile f l r) =
      comparisonTrackedPair (f l.core r.core) := by
  rfl

private theorem authorizedReconcile_cleanupAuxPair
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    authorizedCleanupAuxPair (authorizedReconcile f l r) =
      cleanupAuxPair (f l.core r.core) := by
  rfl

/-- The ordinary suffix strictly after repaired Algorithm 14. -/
def authorizedPostSuppress (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := authorizedReconcile (eliminateLeadersNoCollision hpsi) l r
  authorizedReconcile (writeSeqIncrementGate hpsi) q.1 q.2

/-- Post-suppression suffix for the separately named rooted leader-sink
repair.  Only Algorithm 15 differs from `authorizedPostSuppress`; gated WRITE
is unchanged. -/
def authorizedPostSuppressLeaderSink (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  authorizedReconcile (writeSeqIncrementGate hpsi) q.1 q.2

/-- Authorization reconciliation exposes exactly the raw bullet fields. -/
theorem authorizedReconcile_bulletFieldPair
    (f : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedReconcile f l r) =
      bulletFieldPair (f l.core r.core) := by
  rfl

/-- Authorization reconciliation changes no physical leader bit.  Keeping
this as a generic projection theorem avoids unfolding a large raw transition
when a later proof only needs its leader fields. -/
theorem authorizedReconcile_leaders
    (f : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).1.core.leader =
        (f l.core r.core).1.leader ∧
      (authorizedReconcile f l r).2.core.leader =
        (f l.core r.core).2.leader := by
  exact ⟨rfl, rfl⟩

/-- Every leader after the rooted Algorithm-15/WRITE suffix originates in
one of its input leader bits; a responder output leader originates only at
the input responder.  This packages the two staged origin arguments without
unfolding the suffix at downstream call sites. -/
theorem authorizedPostSuppressLeaderSink_leader_origins
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    let q := authorizedPostSuppressLeaderSink hpsi l r
    (q.1.core.leader = true →
        l.core.leader = true ∨ r.core.leader = true) ∧
      (q.2.core.leader = true → r.core.leader = true) := by
  let q0 := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  let q1 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q0.1 q0.2
  have hstage : authorizedPostSuppressLeaderSink hpsi l r = q1 := by
    rfl
  have hq0Left : q0.1.core.leader = true → l.core.leader = true := by
    intro hout
    have hnew := (authorizedReconcile_leaders
      (eliminateLeadersNoCollisionLeaderSink hpsi) l r).1.symm.trans hout
    have hold := (eliminateLeadersNoCollisionLeaderSink_leaders_eq
      hpsi l.core r.core).1.symm.trans hnew
    exact eliminateLeadersNoCollision_initiator_origin
      hpsi l.core r.core hold
  have hq0Right : q0.2.core.leader = true → r.core.leader = true := by
    intro hout
    have hnew := (authorizedReconcile_leaders
      (eliminateLeadersNoCollisionLeaderSink hpsi) l r).2.symm.trans hout
    have hold := (eliminateLeadersNoCollisionLeaderSink_leaders_eq
      hpsi l.core r.core).2.symm.trans hnew
    exact (eliminateLeadersNoCollision_responder_leader_eq
      hpsi l.core r.core).symm.trans hold
  constructor
  · intro hout
    have hq1 := (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.leader) hstage).symm.trans hout
    have hraw := (authorizedReconcile_leaders
      (writeSeqIncrementGate hpsi) q0.1 q0.2).1.symm.trans hq1
    rcases writeSeqIncrementGate_initiator_origin
        hpsi q0.1.core q0.2.core hraw with hleft | hright
    · exact .inl (hq0Left hleft)
    · exact .inr (hq0Right hright)
  · intro hout
    have hq1 := (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.leader) hstage).symm.trans hout
    have hraw := (authorizedReconcile_leaders
      (writeSeqIncrementGate hpsi) q0.1 q0.2).2.symm.trans hq1
    exact hq0Right
      (writeSeqIncrementGate_responder_origin
        hpsi q0.1.core q0.2.core hraw)

/-- The rooted Algorithm-15/WRITE suffix preserves both endpoint bullet
fields exactly after Algorithm 15. -/
theorem authorizedPostSuppressLeaderSink_bulletFieldPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair
        (authorizedPostSuppressLeaderSink hpsi l r) =
      bulletFieldPair
        (eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core) := by
  let beforeWrite := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  have hstage : authorizedPostSuppressLeaderSink hpsi l r =
      authorizedReconcile (writeSeqIncrementGate hpsi)
        beforeWrite.1 beforeWrite.2 := by
    rfl
  rw [hstage]
  exact (authorizedReconcile_bulletFieldPair
    (writeSeqIncrementGate hpsi) beforeWrite.1 beforeWrite.2).trans
      ((writeSeqIncrementGate_bulletFieldPair
        hpsi beforeWrite.1.core beforeWrite.2.core).trans
          (authorizedReconcile_bulletFieldPair
            (eliminateLeadersNoCollisionLeaderSink hpsi) l r))

/-- The rooted leader-sink suffix is exactly the established suffix whenever
its responder is a follower.  Thus the repair changes only edges entering an
existing leader. -/
theorem authorizedPostSuppressLeaderSink_eq_of_responder_follower
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hrFollower : r.core.leader = false) :
    authorizedPostSuppressLeaderSink hpsi l r =
      authorizedPostSuppress hpsi l r := by
  unfold authorizedPostSuppressLeaderSink authorizedPostSuppress
  simp only [authorizedReconcile]
  rw [eliminateLeadersNoCollisionLeaderSink_eq_of_responder_follower
    hpsi l.core r.core hrFollower]

/-- Exact physical trace of a leader-killing live hit after the complete
authorized Algorithm-15/WRITE suffix. -/
structure AuthorizedInitiatorLeaderLiveHit
    (l r : AuthorizedAgentState psi)
    (out : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  sourceSignalZero : l.core.signal_B = ⟨0, by omega⟩
  sourceUnshielded : l.core.shield = false
  responderLive : r.core.bullet = ⟨2, by omega⟩
  outputInitiatorFollower : out.1.core.leader = false
  outputInitiatorBullet : out.1.core.bullet = l.core.bullet
  outputResponderFollower : out.2.core.leader = false
  outputResponderDummy : out.2.core.bullet = ⟨1, by omega⟩

/-- Staged lift of a leader-killing live hit through authorization and gated
WRITE.  Naming both boundaries keeps the proof independent of the large
surrounding transition term. -/
theorem authorizedLeaderSinkPostSuppress_live_hit_of_stages
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (beforeWrite out :
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hbeforeLeft : beforeWrite.1.core.leader =
      (eliminateLeadersNoCollisionLeaderSink
        hpsi l.core r.core).1.leader)
    (hbeforeRight : beforeWrite.2.core.leader =
      (eliminateLeadersNoCollisionLeaderSink
        hpsi l.core r.core).2.leader)
    (hbeforeLeftBullet : beforeWrite.1.core.bullet =
      (eliminateLeadersNoCollisionLeaderSink
        hpsi l.core r.core).1.bullet)
    (hbeforeRightBullet : beforeWrite.2.core.bullet =
      (eliminateLeadersNoCollisionLeaderSink
        hpsi l.core r.core).2.bullet)
    (houtLeft : out.1.core.leader =
      (writeSeqIncrementGate hpsi
        beforeWrite.1.core beforeWrite.2.core).1.leader)
    (houtRight : out.2.core.leader =
      (writeSeqIncrementGate hpsi
        beforeWrite.1.core beforeWrite.2.core).2.leader)
    (houtLeftBullet : out.1.core.bullet =
      (writeSeqIncrementGate hpsi
        beforeWrite.1.core beforeWrite.2.core).1.bullet)
    (houtRightBullet : out.2.core.bullet =
      (writeSeqIncrementGate hpsi
        beforeWrite.1.core beforeWrite.2.core).2.bullet)
    (hl : l.core.leader = true) (hr : r.core.leader = false)
    (hout : out.1.core.leader = false) :
    AuthorizedInitiatorLeaderLiveHit l r out := by
  let raw := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
  have hkernel :=
    noCollisionLeaderSink_initiator_leader_survives_or_live_hit
      hpsi l.core r.core hl hr
  change (raw.1.leader = true ∧ raw.2.leader = false) ∨
    InitiatorLeaderLiveHit l.core r.core raw at hkernel
  change beforeWrite.1.core.leader = raw.1.leader at hbeforeLeft
  change beforeWrite.2.core.leader = raw.2.leader at hbeforeRight
  change beforeWrite.1.core.bullet = raw.1.bullet at hbeforeLeftBullet
  change beforeWrite.2.core.bullet = raw.2.bullet at hbeforeRightBullet
  rcases hkernel with hsurvives | hhit
  · have hbeforeLeader : beforeWrite.1.core.leader = true :=
      hbeforeLeft.trans hsurvives.1
    have hwriteLeader := writeSeqIncrementGate_initiator_survives
      hpsi beforeWrite.1.core beforeWrite.2.core hbeforeLeader
    have hbad : (false : Bool) = true :=
      hout.symm.trans (houtLeft.trans hwriteLeader)
    simp at hbad
  · have hbeforeRightFollower : beforeWrite.2.core.leader = false :=
      hbeforeRight.trans hhit.outputResponderFollower
    have hwriteRight :
        (writeSeqIncrementGate hpsi
          beforeWrite.1.core beforeWrite.2.core).2.leader = false := by
      cases hw : (writeSeqIncrementGate hpsi
        beforeWrite.1.core beforeWrite.2.core).2.leader
      · rfl
      · have horigin := writeSeqIncrementGate_responder_origin
          hpsi beforeWrite.1.core beforeWrite.2.core hw
        have hbad : (false : Bool) = true :=
          hbeforeRightFollower.symm.trans horigin
        simp at hbad
    have hrightBullet := writeSeqIncrementGate_responder_bullet_eq
      hpsi beforeWrite.1.core beforeWrite.2.core
    have hleftBullet := writeSeqIncrementGate_initiator_bullet_eq
      hpsi beforeWrite.1.core beforeWrite.2.core
    have hbeforeRightDummy : beforeWrite.2.core.bullet =
        ⟨1, by omega⟩ := by
      exact hbeforeRightBullet.trans hhit.outputResponderDummy
    exact {
      sourceSignalZero := hhit.sourceSignalZero
      sourceUnshielded := hhit.sourceUnshielded
      responderLive := hhit.responderLive
      outputInitiatorFollower := hout
      outputInitiatorBullet := houtLeftBullet.trans
        (hleftBullet.trans (hbeforeLeftBullet.trans
          hhit.outputInitiatorBullet))
      outputResponderFollower := houtRight.trans hwriteRight
      outputResponderDummy := houtRightBullet.trans
        (hrightBullet.trans hbeforeRightDummy) }

/-- The rooted leader-sink suffix is closed on the unchanged numeric carrier. -/
theorem authorizedPostSuppressLeaderSink_inProtocolDomain
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := authorizedPostSuppressLeaderSink hpsi l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let q0 := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  have h0 := authorizedReconcile_inProtocolDomain
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
    (PPLLDomain.eliminateLeadersNoCollisionLeaderSink_inProtocolDomain
      hpsi l.core r.core hl hr)
  exact authorizedReconcile_inProtocolDomain
    (writeSeqIncrementGate hpsi) q0.1 q0.2
    (writeSeqIncrementGate_inProtocolDomain
      hpsi q0.1.core q0.2.core h0.1 h0.2)

/-- Named Algorithm-15 boundary used by anchor proofs. -/
def authorizedPostSuppressAfterEliminate (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  authorizedReconcile (eliminateLeadersNoCollision hpsi) l r

/-- Named gated-WRITE boundary used by anchor proofs. -/
def authorizedPostSuppressAfterWrite (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := authorizedPostSuppressAfterEliminate hpsi l r
  authorizedReconcile (writeSeqIncrementGate hpsi) q.1 q.2

theorem authorizedPostSuppressAfterEliminate_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPostSuppressAfterEliminate hpsi l r =
      authorizedReconcile (eliminateLeadersNoCollision hpsi) l r := by
  rfl

theorem authorizedPostSuppressAfterWrite_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    let q := authorizedPostSuppressAfterEliminate hpsi l r
    authorizedPostSuppressAfterWrite hpsi l r =
      authorizedReconcile (writeSeqIncrementGate hpsi) q.1 q.2 := by
  rfl

theorem authorizedPostSuppress_eq_afterWrite
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPostSuppress hpsi l r =
      authorizedPostSuppressAfterWrite hpsi l r := by
  rfl

attribute [local irreducible] writeSeqIncrementGate

/-- After Algorithm 15, gated WRITE preserves the complete `PeaceView` when
any responder leader is already at label zero. -/
theorem authorizedPostSuppress_peaceView_eq_noCollision
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hzero :
      let q := eliminateLeadersNoCollision hpsi l.core r.core
      q.2.leader = true → q.2.label = ⟨0, hpsi⟩) :
    authorizedPeaceViewPair (authorizedPostSuppress hpsi l r) =
      peaceViewPair
        (eliminateLeadersNoCollision hpsi l.core r.core) := by
  let q := eliminateLeadersNoCollision hpsi l.core r.core
  have hleaders := writeSeqIncrementGate_leaders_of_responder_zero
    hpsi q.1 q.2 hzero
  have hlabels := writeSeqIncrementGate_labels hpsi q.1 q.2
  have hbullets := writeSeqIncrementGate_bulletFieldPair hpsi q.1 q.2
  have hbLS := congrArg (fun v => v.1.shield) hbullets
  have hbLB := congrArg (fun v => v.1.bullet) hbullets
  have hbLG := congrArg (fun v => v.1.signal_B) hbullets
  have hbRS := congrArg (fun v => v.2.shield) hbullets
  have hbRB := congrArg (fun v => v.2.bullet) hbullets
  have hbRG := congrArg (fun v => v.2.signal_B) hbullets
  unfold bulletFieldPair BulletFields.ofState at hbLS hbLB hbLG hbRS hbRB hbRG
  dsimp only at hbLS hbLB hbLG hbRS hbRB hbRG
  have hwrite : peaceViewPair (writeSeqIncrementGate hpsi q.1 q.2) =
      peaceViewPair q := by
    apply Prod.ext <;> apply PeaceView.ext
    · exact hleaders.1
    · exact hlabels.1
    · exact hbLS
    · exact hbLB
    · exact hbLG
    · exact hleaders.2
    · exact hlabels.2
    · exact hbRS
    · exact hbRB
    · exact hbRG
  calc
    authorizedPeaceViewPair (authorizedPostSuppress hpsi l r) =
        authorizedPeaceViewPair
          (authorizedPostSuppressAfterWrite hpsi l r) :=
      congrArg authorizedPeaceViewPair
        (authorizedPostSuppress_eq_afterWrite hpsi l r)
    _ = peaceViewPair (writeSeqIncrementGate hpsi q.1 q.2) := rfl
    _ = peaceViewPair q := hwrite

/-- Gated WRITE also preserves the complete `PeaceView` of the rooted
leader-sink Algorithm 15 whenever a responder leader is hosted at label zero. -/
theorem authorizedPostSuppressLeaderSink_peaceView_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hzero :
      let q := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
      q.2.leader = true → q.2.label = ⟨0, hpsi⟩) :
    authorizedPeaceViewPair
        (authorizedPostSuppressLeaderSink hpsi l r) =
      peaceViewPair
        (eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core) := by
  let q := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
  have hleaders := writeSeqIncrementGate_leaders_of_responder_zero
    hpsi q.1 q.2 hzero
  have hlabels := writeSeqIncrementGate_labels hpsi q.1 q.2
  have hbullets := writeSeqIncrementGate_bulletFieldPair hpsi q.1 q.2
  have hbLS := congrArg (fun v => v.1.shield) hbullets
  have hbLB := congrArg (fun v => v.1.bullet) hbullets
  have hbLG := congrArg (fun v => v.1.signal_B) hbullets
  have hbRS := congrArg (fun v => v.2.shield) hbullets
  have hbRB := congrArg (fun v => v.2.bullet) hbullets
  have hbRG := congrArg (fun v => v.2.signal_B) hbullets
  unfold bulletFieldPair BulletFields.ofState at hbLS hbLB hbLG hbRS hbRB hbRG
  dsimp only at hbLS hbLB hbLG hbRS hbRB hbRG
  have hwrite : peaceViewPair (writeSeqIncrementGate hpsi q.1 q.2) =
      peaceViewPair q := by
    apply Prod.ext <;> apply PeaceView.ext
    · exact hleaders.1
    · exact hlabels.1
    · exact hbLS
    · exact hbLB
    · exact hbLG
    · exact hleaders.2
    · exact hlabels.2
    · exact hbRS
    · exact hbRB
    · exact hbRG
  change peaceViewPair (writeSeqIncrementGate hpsi q.1 q.2) =
    peaceViewPair q
  exact hwrite

/-- If an initiating leader survives the rooted Algorithm-15/WRITE suffix
against a follower responder, the output pair is collision-safe for replay:
any surviving responder live bullet is covered by the leader shield.  The
proof uses the suffix `PeaceView` contract instead of unfolding WRITE. -/
theorem authorizedPostSuppressLeaderSink_survivor_safe
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false)
    (houtLeader :
      (authorizedPostSuppressLeaderSink hpsi l r).1.core.leader = true) :
    (authorizedPostSuppressLeaderSink hpsi l r).2.core.bullet =
        ⟨2, by omega⟩ →
      (authorizedPostSuppressLeaderSink hpsi l r).1.core.shield = true := by
  let raw := eliminateLeadersNoCollisionLeaderSink
    hpsi l.core r.core
  have hrawRight : raw.2.leader = false :=
    (eliminateLeadersNoCollisionLeaderSink_leaders_eq
      hpsi l.core r.core).2.trans
        ((eliminateLeadersNoCollision_responder_leader_eq
          hpsi l.core r.core).trans hrFollower)
  have hzero : raw.2.leader = true → raw.2.label = ⟨0, hpsi⟩ := by
    intro hleader
    rw [hrawRight] at hleader
    contradiction
  have hview := authorizedPostSuppressLeaderSink_peaceView_eq
    hpsi l r hzero
  have hleftLeader := congrArg (fun q => q.1.leader) hview
  have hleftShield := congrArg (fun q => q.1.shield) hview
  have hrightBullet := congrArg (fun q => q.2.bullet) hview
  change (authorizedPostSuppressLeaderSink
    hpsi l r).1.core.leader = raw.1.leader at hleftLeader
  change (authorizedPostSuppressLeaderSink
    hpsi l r).1.core.shield = raw.1.shield at hleftShield
  change (authorizedPostSuppressLeaderSink
    hpsi l r).2.core.bullet = raw.2.bullet at hrightBullet
  have hrawLeft : raw.1.leader = true :=
    hleftLeader.symm.trans houtLeader
  have hsafe := noCollisionLeaderSink_survivor_safe
    hpsi l.core r.core hlLeader hrFollower hrawLeft
  intro houtBullet
  exact hleftShield.trans
    (hsafe (hrightBullet.symm.trans houtBullet))

/-- A live follower responder remains live through the rooted
Algorithm-15/WRITE suffix whenever the initiating leader survives. -/
theorem authorizedPostSuppressLeaderSink_survivor_preserves_responder_live
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false)
    (hrLive : r.core.bullet = ⟨2, by omega⟩)
    (houtLeader :
      (authorizedPostSuppressLeaderSink hpsi l r).1.core.leader = true) :
    (authorizedPostSuppressLeaderSink hpsi l r).2.core.bullet =
      ⟨2, by omega⟩ := by
  let raw := eliminateLeadersNoCollisionLeaderSink
    hpsi l.core r.core
  have hrawRight : raw.2.leader = false :=
    (eliminateLeadersNoCollisionLeaderSink_leaders_eq
      hpsi l.core r.core).2.trans
        ((eliminateLeadersNoCollision_responder_leader_eq
          hpsi l.core r.core).trans hrFollower)
  have hzero : raw.2.leader = true → raw.2.label = ⟨0, hpsi⟩ := by
    intro hleader
    rw [hrawRight] at hleader
    contradiction
  have hview := authorizedPostSuppressLeaderSink_peaceView_eq
    hpsi l r hzero
  have hleftLeader := congrArg (fun q => q.1.leader) hview
  have hrightBullet := congrArg (fun q => q.2.bullet) hview
  change (authorizedPostSuppressLeaderSink
    hpsi l r).1.core.leader = raw.1.leader at hleftLeader
  change (authorizedPostSuppressLeaderSink
    hpsi l r).2.core.bullet = raw.2.bullet at hrightBullet
  have hrawLeft : raw.1.leader = true :=
    hleftLeader.symm.trans houtLeader
  have hrawLive :=
    noCollisionLeaderSink_survivor_preserves_responder_live
      hpsi l.core r.core hlLeader hrFollower hrLive hrawLeft
  exact hrightBullet.trans hrawLive

/-- The exact ordinary boundary immediately after repaired Algorithm 14. -/
def wallSweepAuthorizedNormalAfterSuppress (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r
  authorizedReconcile (suppressSigResetKill hpsi) pre.1 pre.2

/-- The entire ordinary suffix, named from the original edge inputs through
the repaired suppress stage and post-suppression boundary. -/
def wallSweepAuthorizedNormalTail (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  authorizedPostSuppress hpsi q.1 q.2

theorem wallSweepAuthorizedNormalTail_eq_postSuppress
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let q := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
    wallSweepAuthorizedNormalTail hpsi kappa l r =
      authorizedPostSuppress hpsi q.1 q.2 := by
  rfl

/-- The named normal tail is definitionally the existing post-CHECK suffix on
the actual ordinary-branch CHECK output. -/
theorem wallSweepAuthorizedNormalTail_eq_afterCheckSuffix
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
    let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
    let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
    wallSweepAuthorizedNormalTail hpsi kappa l r =
      wallSweepAuthorizedAfterCheckSuffix hpsi afterCheck.1 afterCheck.2 := by
  rfl

/-- Exact authorized stage at the named post-Algorithm-14 boundary. -/
theorem wallSweepAuthorizedNormalAfterSuppress_eq_reconcile
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r
    wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r =
      authorizedReconcile (suppressSigResetKill hpsi) pre.1 pre.2 := by
  rfl

/-- Exact named-stage expansion of Algorithm 15 followed by gated WRITE. -/
theorem authorizedPostSuppress_eq_staged
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPostSuppress hpsi l r =
      let q := authorizedReconcile (eliminateLeadersNoCollision hpsi) l r
      authorizedReconcile (writeSeqIncrementGate hpsi) q.1 q.2 := by
  rfl

section WallPeaceTail

attribute [local irreducible]
  wallSweepAuthorizedNormalBeforeSuppress
  wallSweepAuthorizedNormalAfterSuppress wallSweepAuthorizedNormalTail

/-- Repaired Algorithm 14 preserves the prefix `PeaceView`. -/
theorem wallSweepAuthorizedNormalAfterSuppress_peaceView_of_frame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hframe : WallPeaceEdgeFrame hpsi kappa l r) :
    authorizedPeaceViewPair
        (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  let pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r
  have hpre := wallSweepAuthorizedNormalBeforeSuppress_peaceView_of_frame
    hpsi kappa l r hframe
  have hsuppress : authorizedPeaceViewPair
      (authorizedReconcile (suppressSigResetKill hpsi) pre.1 pre.2) =
      authorizedPeaceViewPair pre :=
    authorizedSuppressSigResetKill_peaceViewPair hpsi pre.1 pre.2
  have hstage := congrArg authorizedPeaceViewPair
    (wallSweepAuthorizedNormalAfterSuppress_eq_reconcile hpsi kappa l r)
  exact hstage.trans (hsuppress.trans hpre)

/-- The complete authorized ordinary tail has exactly the isolated
Algorithm-15 `PeaceView` on the raw edge inputs. -/
theorem wallSweepAuthorizedNormalTail_peaceView_eq_noCollision
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hframe : WallPeaceEdgeFrame hpsi kappa l r) :
    authorizedPeaceViewPair
        (wallSweepAuthorizedNormalTail hpsi kappa l r) =
      peaceViewPair (eliminateLeadersNoCollision hpsi l.core r.core) := by
  let q := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  have hq := wallSweepAuthorizedNormalAfterSuppress_peaceView_of_frame
    hpsi kappa l r hframe
  have hqL := congrArg Prod.fst hq
  have hqR := congrArg Prod.snd hq
  have hzero :
      let out := eliminateLeadersNoCollision hpsi q.1.core q.2.core
      out.2.leader = true → out.2.label = ⟨0, hpsi⟩ := by
    dsimp only
    intro hout
    have hqLeader : q.2.core.leader = true := by
      exact (eliminateLeadersNoCollision_responder_leader_eq
        hpsi q.1.core q.2.core).symm.trans hout
    have hrLeader : r.core.leader = true := by
      exact (congrArg PeaceView.leader hqR).symm.trans hqLeader
    have hrZero := hframe.responder_zero hrLeader
    exact (noCollision_labels hpsi q.1.core q.2.core).2.trans
      ((congrArg PeaceView.label hqR).trans hrZero)
  have hsuffix := authorizedPostSuppress_peaceView_eq_noCollision
    hpsi q.1 q.2 hzero
  have hkernel := noCollision_congr hpsi q.1.core q.2.core l.core r.core
    hqL hqR
  have hstage := congrArg authorizedPeaceViewPair
    (wallSweepAuthorizedNormalTail_eq_postSuppress hpsi kappa l r)
  exact hstage.trans (hsuffix.trans hkernel)

end WallPeaceTail

private theorem postSuppress_comparisonTracked_pair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedComparisonTrackedPair (authorizedPostSuppress hpsi l r) =
      authorizedComparisonTrackedPair (l, r) := by
  unfold authorizedPostSuppress
  let q0 := authorizedReconcile (eliminateLeadersNoCollision hpsi) l r
  have h0c := eliminateLeadersNoCollision_comparisonTracked_frame
    hpsi l.core r.core
  have h0raw : comparisonTrackedPair
      (eliminateLeadersNoCollision hpsi l.core r.core) =
      comparisonTrackedPair (l.core, r.core) := Prod.ext h0c.1 h0c.2
  have h0 : authorizedComparisonTrackedPair q0 =
      authorizedComparisonTrackedPair (l, r) :=
    (authorizedReconcile_comparisonTrackedPair
      (eliminateLeadersNoCollision hpsi) l r).trans h0raw
  let q1 := authorizedReconcile (writeSeqIncrementGate hpsi) q0.1 q0.2
  have h1raw := writeSeqIncrementGate_comparisonTracked_pair
    hpsi q0.1.core q0.2.core
  have h1 : authorizedComparisonTrackedPair q1 =
      authorizedComparisonTrackedPair q0 :=
    (authorizedReconcile_comparisonTrackedPair
      (writeSeqIncrementGate hpsi) q0.1 q0.2).trans h1raw
  exact h1.trans h0

/-- Algorithm 15 and gated WRITE frame every cleanup auxiliary field. -/
theorem postSuppress_cleanupAux_pair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedCleanupAuxPair (authorizedPostSuppress hpsi l r) =
      authorizedCleanupAuxPair (l, r) := by
  unfold authorizedPostSuppress
  let q0 := authorizedReconcile (eliminateLeadersNoCollision hpsi) l r
  have h0raw := eliminateLeadersNoCollision_cleanupAux_pair
    hpsi l.core r.core
  have h0 : authorizedCleanupAuxPair q0 =
      authorizedCleanupAuxPair (l, r) :=
    (authorizedReconcile_cleanupAuxPair
      (eliminateLeadersNoCollision hpsi) l r).trans h0raw
  let q1 := authorizedReconcile (writeSeqIncrementGate hpsi) q0.1 q0.2
  have h1raw := writeSeqIncrementGate_cleanupAux_frame
    hpsi q0.1.core q0.2.core
  have h1 : authorizedCleanupAuxPair q1 = authorizedCleanupAuxPair q0 :=
    (authorizedReconcile_cleanupAuxPair
      (writeSeqIncrementGate hpsi) q0.1 q0.2).trans h1raw
  exact h1.trans h0

/-- Algorithm 15 and gated WRITE frame reset and echo at both endpoints. -/
theorem authorizedPostSuppress_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedPostSuppress hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  have haux := postSuppress_cleanupAux_pair hpsi l r
  have hL := congrArg Prod.fst haux
  have hR := congrArg Prod.snd haux
  have hLReset := congrArg CleanupAuxView.resetCmd hL
  have hLEcho := congrArg CleanupAuxView.echo hL
  have hRReset := congrArg CleanupAuxView.resetCmd hR
  have hREcho := congrArg CleanupAuxView.echo hR
  apply Prod.ext
  · exact Prod.ext hLReset hLEcho
  · exact Prod.ext hRReset hREcho

private theorem postSuppressLeaderSink_comparisonTracked_pair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedComparisonTrackedPair
        (authorizedPostSuppressLeaderSink hpsi l r) =
      authorizedComparisonTrackedPair (l, r) := by
  unfold authorizedPostSuppressLeaderSink
  let q0 := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  have h0c :=
    eliminateLeadersNoCollisionLeaderSink_comparisonTracked_frame
      hpsi l.core r.core
  have h0raw : comparisonTrackedPair
      (eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core) =
      comparisonTrackedPair (l.core, r.core) := Prod.ext h0c.1 h0c.2
  have h0 : authorizedComparisonTrackedPair q0 =
      authorizedComparisonTrackedPair (l, r) :=
    (authorizedReconcile_comparisonTrackedPair
      (eliminateLeadersNoCollisionLeaderSink hpsi) l r).trans h0raw
  let q1 := authorizedReconcile (writeSeqIncrementGate hpsi) q0.1 q0.2
  have h1raw := writeSeqIncrementGate_comparisonTracked_pair
    hpsi q0.1.core q0.2.core
  have h1 : authorizedComparisonTrackedPair q1 =
      authorizedComparisonTrackedPair q0 :=
    (authorizedReconcile_comparisonTrackedPair
      (writeSeqIncrementGate hpsi) q0.1 q0.2).trans h1raw
  exact h1.trans h0

/-- The rooted leader-sink suffix frames every comparison-neutrality auxiliary
field, including reset and echo. -/
theorem postSuppressLeaderSink_cleanupAux_pair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedCleanupAuxPair
        (authorizedPostSuppressLeaderSink hpsi l r) =
      authorizedCleanupAuxPair (l, r) := by
  unfold authorizedPostSuppressLeaderSink
  let q0 := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  have h0raw := eliminateLeadersNoCollisionLeaderSink_cleanupAux_pair
    hpsi l.core r.core
  have h0 : authorizedCleanupAuxPair q0 =
      authorizedCleanupAuxPair (l, r) :=
    (authorizedReconcile_cleanupAuxPair
      (eliminateLeadersNoCollisionLeaderSink hpsi) l r).trans h0raw
  let q1 := authorizedReconcile (writeSeqIncrementGate hpsi) q0.1 q0.2
  have h1raw := writeSeqIncrementGate_cleanupAux_frame
    hpsi q0.1.core q0.2.core
  have h1 : authorizedCleanupAuxPair q1 = authorizedCleanupAuxPair q0 :=
    (authorizedReconcile_cleanupAuxPair
      (writeSeqIncrementGate hpsi) q0.1 q0.2).trans h1raw
  exact h1.trans h0

/-- The rooted leader-sink suffix leaves reset and echo unchanged at both
endpoints. -/
theorem authorizedPostSuppressLeaderSink_resetEchoPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair
        (authorizedPostSuppressLeaderSink hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  have haux := postSuppressLeaderSink_cleanupAux_pair hpsi l r
  have hL := congrArg Prod.fst haux
  have hR := congrArg Prod.snd haux
  apply Prod.ext
  · exact Prod.ext (congrArg CleanupAuxView.resetCmd hL)
      (congrArg CleanupAuxView.echo hL)
  · exact Prod.ext (congrArg CleanupAuxView.resetCmd hR)
      (congrArg CleanupAuxView.echo hR)

/-- The rooted Algorithm-15/WRITE suffix frames both physical labels.  This
pair theorem is independent of leader survival and lets downstream reset
normalization proofs keep the suffix opaque. -/
theorem authorizedPostSuppressLeaderSink_labels_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    let q := authorizedPostSuppressLeaderSink hpsi l r
    q.1.core.label = l.core.label ∧
      q.2.core.label = r.core.label := by
  let q0 := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  let q1 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q0.1 q0.2
  have h0 : q0.1.core.label = l.core.label ∧
      q0.2.core.label = r.core.label := by
    exact ⟨(eliminateLeadersNoCollisionLeaderSink_labels_eq
        hpsi l.core r.core).1.trans
          (noCollision_labels hpsi l.core r.core).1,
      (eliminateLeadersNoCollisionLeaderSink_labels_eq
        hpsi l.core r.core).2.trans
          (noCollision_labels hpsi l.core r.core).2⟩
  have hwrite := writeSeqIncrementGate_labels
    hpsi q0.1.core q0.2.core
  change q1.1.core.label = l.core.label ∧
    q1.2.core.label = r.core.label
  exact ⟨hwrite.1.trans h0.1, hwrite.2.trans h0.2⟩

/-- The rooted Algorithm-15/WRITE suffix atomically migrates an existing
nonzero-label responder leader to the initiator.  Algorithm 15 frames the
leader bits, gated WRITE performs the source migration, and both labels stay
on their physical hosts. -/
theorem authorizedPostSuppressLeaderSink_nonzero_responder_migrates
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true)
    (hrNonzero : r.core.label ≠ ⟨0, hpsi⟩) :
    let out := authorizedPostSuppressLeaderSink hpsi l r
    out.1.core.leader = true ∧
      out.2.core.leader = false ∧
      out.1.core.label = l.core.label ∧
      out.2.core.label = r.core.label := by
  let beforeWrite := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  let out := authorizedReconcile
    (writeSeqIncrementGate hpsi) beforeWrite.1 beforeWrite.2
  have hbeforeLeader : beforeWrite.2.core.leader = true := by
    change (eliminateLeadersNoCollisionLeaderSink
      hpsi l.core r.core).2.leader = true
    exact (eliminateLeadersNoCollisionLeaderSink_leaders_eq
      hpsi l.core r.core).2.trans
        ((eliminateLeadersNoCollision_responder_leader_eq
          hpsi l.core r.core).trans hrLeader)
  have hbeforeLabel : beforeWrite.2.core.label = r.core.label := by
    change (eliminateLeadersNoCollisionLeaderSink
      hpsi l.core r.core).2.label = r.core.label
    exact (eliminateLeadersNoCollisionLeaderSink_labels_eq
      hpsi l.core r.core).2.trans
        (noCollision_labels hpsi l.core r.core).2
  have hbeforeNonzero : beforeWrite.2.core.label ≠ ⟨0, hpsi⟩ := by
    intro hzero
    exact hrNonzero (hbeforeLabel.symm.trans hzero)
  have hmigrate : beforeWrite.2.core.leader = true ∧
      beforeWrite.2.core.label ≠ ⟨0, hpsi⟩ :=
    ⟨hbeforeLeader, hbeforeNonzero⟩
  have hleft :=
    writeSeqIncrementGate_initiator_true_of_nonzero_responder_leader
      hpsi beforeWrite.1.core beforeWrite.2.core hmigrate
  have hright :=
    writeSeqIncrementGate_responder_false_of_nonzero_leader
      hpsi beforeWrite.1.core beforeWrite.2.core hmigrate
  have hlabels := authorizedPostSuppressLeaderSink_labels_eq hpsi l r
  change out.1.core.leader = true ∧
    out.2.core.leader = false ∧
    out.1.core.label = l.core.label ∧
    out.2.core.label = r.core.label
  exact ⟨hleft, hright, hlabels.1, hlabels.2⟩

/-- Neutral comparison endpoints remain neutral through the rooted leader-sink
Algorithm 15 and unchanged gated WRITE suffix. -/
theorem authorizedPostSuppressLeaderSink_neutral
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hL : ComparisonNeutral l.core) (hR : ComparisonNeutral r.core) :
    let q := authorizedPostSuppressLeaderSink hpsi l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core := by
  let q := authorizedPostSuppressLeaderSink hpsi l r
  have htracked := postSuppressLeaderSink_comparisonTracked_pair hpsi l r
  have haux := postSuppressLeaderSink_cleanupAux_pair hpsi l r
  change authorizedComparisonTrackedPair q = _ at htracked
  change authorizedCleanupAuxPair q = _ at haux
  exact ⟨neutral_of_tracked_aux_eq
      (congrArg Prod.fst htracked) (congrArg Prod.fst haux) hL,
    neutral_of_tracked_aux_eq
      (congrArg Prod.snd htracked) (congrArg Prod.snd haux) hR⟩

/-! The two pair frames above are the only declarations below this point that
need the implementation of the post-suppression suffix. -/
attribute [local irreducible] authorizedPostSuppress

/-- Reassemble the two abstract pair projections into the physical handoff.
Keeping `before` and `after` abstract prevents elaboration from reopening
Algorithm 15 or WRITE while endpoint projections are extracted. -/
private theorem normalResetHandoff_of_pair_projection_eq
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hTracked : authorizedComparisonTrackedPair after =
      authorizedComparisonTrackedPair before)
    (hAux : authorizedCleanupAuxPair after = authorizedCleanupAuxPair before)
    (hNeutralL : ComparisonNeutral before.1.core)
    (hNeutralR : ComparisonNeutral before.2.core) :
    ComparisonNeutral after.1.core ∧ ComparisonNeutral after.2.core ∧
      after.1.core.reset_cmd = before.1.core.reset_cmd ∧
      after.2.core.reset_cmd = before.2.core.reset_cmd ∧
      after.1.core.echo = before.1.core.echo ∧
      after.2.core.echo = before.2.core.echo := by
  have hTrackedL := congrArg Prod.fst hTracked
  have hTrackedR := congrArg Prod.snd hTracked
  have hAuxL := congrArg Prod.fst hAux
  have hAuxR := congrArg Prod.snd hAux
  simp only [authorizedComparisonTrackedPair, comparisonTrackedPair] at hTrackedL hTrackedR
  simp only [authorizedCleanupAuxPair, cleanupAuxPair] at hAuxL hAuxR
  exact ⟨neutral_of_tracked_aux_eq hTrackedL hAuxL hNeutralL,
    neutral_of_tracked_aux_eq hTrackedR hAuxR hNeutralR,
    resetCmd_of_cleanupAux_eq hAuxL,
    resetCmd_of_cleanupAux_eq hAuxR,
    echo_of_cleanupAux_eq hAuxL,
    echo_of_cleanupAux_eq hAuxR⟩

/-- Algorithm 15 plus gated WRITE preserve the exact comparison/reset/echo
handoff produced by repaired Algorithm 14. -/
theorem postSuppress_normalReset_handoff
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hNeutralL : ComparisonNeutral l.core)
    (hNeutralR : ComparisonNeutral r.core) :
    let q := authorizedPostSuppress hpsi l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.core.reset_cmd = l.core.reset_cmd ∧
      q.2.core.reset_cmd = r.core.reset_cmd ∧
      q.1.core.echo = l.core.echo ∧ q.2.core.echo = r.core.echo := by
  exact normalResetHandoff_of_pair_projection_eq
    (before := (l, r))
    (after := authorizedPostSuppress hpsi l r)
    (postSuppress_comparisonTracked_pair hpsi l r)
    (postSuppress_cleanupAux_pair hpsi l r)
    hNeutralL hNeutralR

/-! ## Anchors through suppress and the ordinary tail -/

private theorem suppressSigResetKill_left_shield_eq
    (hpsi : psi > 0) (l r : AgentState psi) :
    (suppressSigResetKill hpsi l r).1.shield = l.shield := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish]

private theorem resetKillComparison_label_eq (u : AgentState psi) :
    (resetKillComparison u).label = u.label := by
  unfold resetKillComparison
  split <;> rfl

theorem suppressSigResetKill_right_label_eq
    (hpsi : psi > 0) (l r : AgentState psi) :
    (suppressSigResetKill hpsi l r).2.label = r.label := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison_label_eq, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish]

theorem suppressSigResetKill_left_label_eq
    (hpsi : psi > 0) (l r : AgentState psi) :
    (suppressSigResetKill hpsi l r).1.label = l.label := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison_label_eq, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish]

theorem suppressSigResetKill_initiator_anchor
    (hpsi : psi > 0) (l r : AgentState psi)
    (h : InitiatorAnchor l) :
    InitiatorAnchor (suppressSigResetKill hpsi l r).1 := by
  exact ⟨(suppressSigResetKill_leaders_eq hpsi l r).1.trans h.1,
    (suppressSigResetKill_left_shield_eq hpsi l r).trans h.2⟩

theorem suppressSigResetKill_responder_zero_anchor
    (hpsi : psi > 0) (l r : AgentState psi)
    (h : ResponderZeroAnchor hpsi r) :
    ResponderZeroAnchor hpsi (suppressSigResetKill hpsi l r).2 := by
  exact ⟨(suppressSigResetKill_leaders_eq hpsi l r).2.trans h.1,
    (suppressSigResetKill_right_label_eq hpsi l r).trans h.2⟩

theorem suppressSigResetKill_leader_reseed_neutral
    (hpsi : psi > 0) (l r : AgentState psi)
    (hleader : l.leader = true) (hrEcho : r.echo = false) :
    let q := suppressSigResetKill hpsi l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, ComparisonNeutral,
    suppressSigTerminal, suppressSigEcho, suppressSigFinish,
    hleader, hrEcho]

private theorem authorizedReconcile_initiator_anchor_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : InitiatorAnchor (f l.core r.core).1) :
    authorizedInitiatorAnchor (authorizedReconcile f l r) := by
  exact hraw

private theorem authorizedReconcile_responder_zero_anchor_of_raw
    (hpsi : psi > 0)
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : ResponderZeroAnchor hpsi (f l.core r.core).2) :
    authorizedResponderZeroAnchor hpsi (authorizedReconcile f l r) := by
  exact hraw

private theorem authorizedReconcile_initiator_label_eq_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : (f l.core r.core).1.label = l.core.label) :
    authorizedInitiatorLabel (authorizedReconcile f l r) = l.core.label := by
  exact hraw

theorem authorizedReconcile_initiatorLabel_frame_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (before : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hraw : (f before.1.core before.2.core).1.label =
      before.1.core.label) :
    authorizedInitiatorLabel
        (authorizedReconcile f before.1 before.2) =
      authorizedInitiatorLabel before := by
  exact hraw

theorem afterSuppress_initiator_anchor_of_eq
    (hpsi : psi > 0)
    {pre out : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hout : out = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2)
    (hpre : authorizedInitiatorAnchor pre) :
    authorizedInitiatorAnchor out := by
  exact initiatorAnchor_of_authorizedPair_eq hout
    (authorizedReconcile_initiator_anchor_of_raw
      (suppressSigResetKill hpsi) pre.1 pre.2
        (suppressSigResetKill_initiator_anchor
          hpsi pre.1.core pre.2.core hpre))

theorem afterSuppress_responder_zero_anchor_of_eq
    (hpsi : psi > 0)
    {pre out : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hout : out = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2)
    (hpre : authorizedResponderZeroAnchor hpsi pre) :
    authorizedResponderZeroAnchor hpsi out := by
  exact responderZeroAnchor_of_authorizedPair_eq hpsi hout
    (authorizedReconcile_responder_zero_anchor_of_raw hpsi
      (suppressSigResetKill hpsi) pre.1 pre.2
        (suppressSigResetKill_responder_zero_anchor
          hpsi pre.1.core pre.2.core hpre))

theorem wallSweepAuthorizedNormalAfterSuppress_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r) := by
  exact afterSuppress_initiator_anchor_of_eq hpsi
    (pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r)
    (out := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r)
    (wallSweepAuthorizedNormalAfterSuppress_eq_reconcile hpsi kappa l r)
    (wallSweepAuthorizedNormalBeforeSuppress_initiator_anchor
      hpsi kappa l r h)

theorem wallSweepAuthorizedNormalAfterSuppress_responder_zero_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r) := by
  exact afterSuppress_responder_zero_anchor_of_eq hpsi
    (pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r)
    (out := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r)
    (wallSweepAuthorizedNormalAfterSuppress_eq_reconcile hpsi kappa l r)
    (wallSweepAuthorizedNormalBeforeSuppress_responder_zero_anchor
      hpsi kappa l r h)

theorem wallSweepAuthorizedNormalAfterSuppress_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel
      (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r) =
      l.core.label := by
  let pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r
  have heq := initiatorLabel_eq_of_authorizedPair_eq
    (wallSweepAuthorizedNormalAfterSuppress_eq_reconcile hpsi kappa l r)
  have hrec := authorizedReconcile_initiatorLabel_frame_of_raw
    (suppressSigResetKill hpsi) pre
      (suppressSigResetKill_left_label_eq hpsi pre.1.core pre.2.core)
  exact heq.trans (hrec.trans
    (wallSweepAuthorizedNormalBeforeSuppress_initiator_label_eq
      hpsi kappa l r))

private theorem noCollision_left_shield_true
    (hpsi : psi > 0) (l r : AgentState psi)
    (hleader : l.leader = true) (hshield : l.shield = true) :
    (eliminateLeadersNoCollision hpsi l r).1.shield = true := by
  by_cases hzero : l.signal_B = ⟨0, by omega⟩
  · exact (noCollision_left_shield_of_signal_zero
      hpsi l r hzero).trans hshield
  · have hval0 : l.signal_B.val ≠ 0 := by
      intro hv
      apply hzero
      apply Fin.ext
      simpa using hv
    have hval1 : l.signal_B.val = 1 := by
      have hlt := l.signal_B.isLt
      omega
    have hone : l.signal_B = ⟨1, by omega⟩ := by
      apply Fin.ext
      exact hval1
    exact (noCollision_left_fire_fields hpsi l r hleader hone).1

private theorem eliminateLeadersNoCollision_initiator_anchor
    (hpsi : psi > 0) (l r : AgentState psi)
    (h : InitiatorAnchor l) :
    InitiatorAnchor (eliminateLeadersNoCollision hpsi l r).1 := by
  have hpeace :
      ¬(r.bullet = ⟨2, by omega⟩ ∧ l.shield = false) := by
    rintro ⟨_, hfalse⟩
    rw [h.2] at hfalse
    simp at hfalse
  exact ⟨eliminateLeadersNoCollision_initiator_survives
      hpsi l r h.1 hpeace,
    noCollision_left_shield_true hpsi l r h.1 h.2⟩

private theorem eliminateLeadersNoCollision_responder_zero_anchor
    (hpsi : psi > 0) (l r : AgentState psi)
    (h : ResponderZeroAnchor hpsi r) :
    ResponderZeroAnchor hpsi (eliminateLeadersNoCollision hpsi l r).2 := by
  exact ⟨(eliminateLeadersNoCollision_responder_leader_eq
      hpsi l r).trans h.1,
    (noCollision_labels hpsi l r).2.trans h.2⟩

/-- The rooted signal-sink guard changes neither component of a responder
leader's zero anchor. -/
private theorem eliminateLeadersNoCollisionLeaderSink_responder_zero_anchor
    (hpsi : psi > 0) (l r : AgentState psi)
    (h : ResponderZeroAnchor hpsi r) :
    ResponderZeroAnchor hpsi
      (eliminateLeadersNoCollisionLeaderSink hpsi l r).2 := by
  have hleaders := eliminateLeadersNoCollisionLeaderSink_leaders_eq
    hpsi l r
  have hlabels := eliminateLeadersNoCollisionLeaderSink_labels_eq
    hpsi l r
  exact ⟨hleaders.2.trans
      ((eliminateLeadersNoCollision_responder_leader_eq
        hpsi l r).trans h.1),
    hlabels.2.trans ((noCollision_labels hpsi l r).2.trans h.2)⟩

private theorem writeSeqIncrementGate_left_shield_eq
    (hpsi : psi > 0) (l r : AgentState psi) :
    (writeSeqIncrementGate hpsi l r).1.shield = l.shield := by
  have hpair := writeSeqIncrementGate_bulletFieldPair hpsi l r
  have hshield := congrArg (fun p => p.1.shield) hpair
  simpa only [bulletFieldPair, BulletFields.ofState] using hshield

private theorem writeSeqIncrementGate_initiator_anchor
    (hpsi : psi > 0) (l r : AgentState psi)
    (h : InitiatorAnchor l) :
    InitiatorAnchor (writeSeqIncrementGate hpsi l r).1 := by
  exact ⟨writeSeqIncrementGate_initiator_survives hpsi l r h.1,
    (writeSeqIncrementGate_left_shield_eq hpsi l r).trans h.2⟩

private theorem authorizedReconcile_responder_leader_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : (f l.core r.core).2.leader = true) :
    (authorizedReconcile f l r).2.core.leader = true := by
  exact hraw

private theorem writeReconcile_responder_zero_survives
    (hpsi : psi > 0)
    (before : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hbefore : authorizedResponderZeroAnchor hpsi before) :
    authorizedResponderLeader (authorizedReconcile
      (writeSeqIncrementGate hpsi) before.1 before.2) := by
  exact authorizedReconcile_responder_leader_of_raw
    (writeSeqIncrementGate hpsi) before.1 before.2
      (writeSeqIncrementGate_responder_zero_survives
        hpsi before.1.core before.2.core hbefore.1 hbefore.2)

/-- Gated WRITE preserves both components of an existing responder-zero
anchor, not merely the responder leader bit. -/
private theorem writeReconcile_responder_zero_anchor
    (hpsi : psi > 0)
    (before : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hbefore : authorizedResponderZeroAnchor hpsi before) :
    authorizedResponderZeroAnchor hpsi (authorizedReconcile
      (writeSeqIncrementGate hpsi) before.1 before.2) := by
  apply authorizedReconcile_responder_zero_anchor_of_raw hpsi
  exact ⟨writeSeqIncrementGate_responder_zero_survives
      hpsi before.1.core before.2.core hbefore.1 hbefore.2,
    (writeSeqIncrementGate_labels
      hpsi before.1.core before.2.core).2.trans hbefore.2⟩

private theorem postSuppressAfterEliminate_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (authorizedPostSuppressAfterEliminate hpsi l r) := by
  exact initiatorAnchor_of_authorizedPair_eq
    (authorizedPostSuppressAfterEliminate_eq hpsi l r)
      (authorizedReconcile_initiator_anchor_of_raw
        (eliminateLeadersNoCollision hpsi) l r
          (eliminateLeadersNoCollision_initiator_anchor
            hpsi l.core r.core h))

private theorem postSuppressAfterEliminate_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (authorizedPostSuppressAfterEliminate hpsi l r) := by
  exact responderZeroAnchor_of_authorizedPair_eq hpsi
    (authorizedPostSuppressAfterEliminate_eq hpsi l r)
      (authorizedReconcile_responder_zero_anchor_of_raw hpsi
        (eliminateLeadersNoCollision hpsi) l r
          (eliminateLeadersNoCollision_responder_zero_anchor
            hpsi l.core r.core h))

private theorem postSuppressAfterEliminate_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel
      (authorizedPostSuppressAfterEliminate hpsi l r) = l.core.label := by
  have heq := initiatorLabel_eq_of_authorizedPair_eq
    (authorizedPostSuppressAfterEliminate_eq hpsi l r)
  have hrec := authorizedReconcile_initiator_label_eq_of_raw
    (eliminateLeadersNoCollision hpsi) l r
      (noCollision_labels hpsi l.core r.core).1
  exact heq.trans hrec

private theorem postSuppressAfterWrite_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (authorizedPostSuppressAfterWrite hpsi l r) := by
  let q := authorizedPostSuppressAfterEliminate hpsi l r
  exact initiatorAnchor_of_authorizedPair_eq
    (authorizedPostSuppressAfterWrite_eq hpsi l r)
      (authorizedReconcile_initiator_anchor_of_raw
        (writeSeqIncrementGate hpsi) q.1 q.2
          (writeSeqIncrementGate_initiator_anchor hpsi q.1.core q.2.core
            (postSuppressAfterEliminate_initiator_anchor hpsi l r h)))

private theorem postSuppressAfterWrite_responder_zero_survives
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderLeader
      (authorizedPostSuppressAfterWrite hpsi l r) := by
  let q := authorizedPostSuppressAfterEliminate hpsi l r
  have hq := postSuppressAfterEliminate_responder_zero_anchor hpsi l r h
  exact responderLeader_of_authorizedPair_eq
    (authorizedPostSuppressAfterWrite_eq hpsi l r)
      (writeReconcile_responder_zero_survives hpsi q hq)

private theorem postSuppressAfterWrite_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel
      (authorizedPostSuppressAfterWrite hpsi l r) = l.core.label := by
  let q := authorizedPostSuppressAfterEliminate hpsi l r
  have heq := initiatorLabel_eq_of_authorizedPair_eq
    (authorizedPostSuppressAfterWrite_eq hpsi l r)
  have hrec := authorizedReconcile_initiator_label_eq_of_raw
    (writeSeqIncrementGate hpsi) q.1 q.2
      (writeSeqIncrementGate_labels hpsi q.1.core q.2.core).1
  exact heq.trans (hrec.trans
    (postSuppressAfterEliminate_initiator_label_eq hpsi l r))

theorem authorizedPostSuppress_initiator_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor (authorizedPostSuppress hpsi l r) := by
  exact initiatorAnchor_of_authorizedPair_eq
    (authorizedPostSuppress_eq_afterWrite hpsi l r)
      (postSuppressAfterWrite_initiator_anchor hpsi l r h)

theorem authorizedPostSuppress_responder_zero_survives
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderLeader (authorizedPostSuppress hpsi l r) := by
  exact responderLeader_of_authorizedPair_eq
    (authorizedPostSuppress_eq_afterWrite hpsi l r)
      (postSuppressAfterWrite_responder_zero_survives hpsi l r h)

/-- The rooted leader-sink suffix preserves a label-zero responder leader.
This is the exact first-birth survival contract needed by the P-prime lift. -/
theorem authorizedPostSuppressLeaderSink_responder_zero_survives
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderLeader
      (authorizedPostSuppressLeaderSink hpsi l r) := by
  let q := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  have hq : authorizedResponderZeroAnchor hpsi q :=
    authorizedReconcile_responder_zero_anchor_of_raw hpsi
      (eliminateLeadersNoCollisionLeaderSink hpsi) l r
        (eliminateLeadersNoCollisionLeaderSink_responder_zero_anchor
          hpsi l.core r.core h)
  change authorizedResponderLeader
    (authorizedReconcile (writeSeqIncrementGate hpsi) q.1 q.2)
  exact writeReconcile_responder_zero_survives hpsi q hq

/-- The rooted leader-sink suffix preserves the complete label-zero
responder anchor.  This sharper form is used to retain the first P-prime
birth's root label through the full repaired interaction. -/
theorem authorizedPostSuppressLeaderSink_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (authorizedPostSuppressLeaderSink hpsi l r) := by
  let q := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  have hq : authorizedResponderZeroAnchor hpsi q :=
    authorizedReconcile_responder_zero_anchor_of_raw hpsi
      (eliminateLeadersNoCollisionLeaderSink hpsi) l r
        (eliminateLeadersNoCollisionLeaderSink_responder_zero_anchor
          hpsi l.core r.core h)
  change authorizedResponderZeroAnchor hpsi
    (authorizedReconcile (writeSeqIncrementGate hpsi) q.1 q.2)
  exact writeReconcile_responder_zero_anchor hpsi q hq

/-- A label-zero responder leader carrying the positive absence signal remains
at the responder through gated WRITE, while Algorithm 15 clears its shield.
This is the authorized duplicate-leader certification step; it does not itself
provide the live bullet that will later remove the unshielded leader. -/
theorem
    authorizedPostSuppressLeaderSink_responder_zero_signal_one_unshielded
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hrSignal : r.core.signal_B = ⟨1, by omega⟩) :
    let out := authorizedPostSuppressLeaderSink hpsi l r
    out.2.core.leader = true ∧
      out.2.core.label = ⟨0, hpsi⟩ ∧
      out.2.core.shield = false := by
  let raw := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
  have hanchor :=
    authorizedPostSuppressLeaderSink_responder_zero_anchor
      hpsi l r ⟨hrLeader, hrZero⟩
  have hraw :=
    eliminateLeadersNoCollisionLeaderSink_responder_signal_one_unshielded
      hpsi l.core r.core hrLeader hrSignal
  change raw.2.leader = true ∧ raw.2.shield = false at hraw
  have hfields := authorizedPostSuppressLeaderSink_bulletFieldPair
    hpsi l r
  have hshield := congrArg (fun q => q.2.shield) hfields
  unfold authorizedBulletFieldPair bulletFieldPair
    BulletFields.ofState at hshield
  dsimp only at hshield
  exact ⟨hanchor.1, hanchor.2, hshield.trans hraw.2⟩

/-- Any responder leader that remains after the rooted leader-sink
Algorithm-15/WRITE suffix is at label zero.  A nonzero responder leader would
be migrated to the initiator by WRITE and hence could not remain the
responder. -/
theorem authorizedPostSuppressLeaderSink_responder_leader_zero
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    let out := authorizedPostSuppressLeaderSink hpsi l r
    out.2.core.leader = true → out.2.core.label = ⟨0, hpsi⟩ := by
  let q := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  let out := authorizedReconcile
    (writeSeqIncrementGate hpsi) q.1 q.2
  change out.2.core.leader = true → out.2.core.label = ⟨0, hpsi⟩
  intro hout
  have hrawOut :
      (writeSeqIncrementGate hpsi q.1.core q.2.core).2.leader = true :=
    hout
  have horigin : q.2.core.leader = true :=
    writeSeqIncrementGate_responder_origin
      hpsi q.1.core q.2.core hrawOut
  have hzero : q.2.core.label = ⟨0, hpsi⟩ := by
    apply Classical.byContradiction
    intro hne
    have hfalse := writeSeqIncrementGate_responder_false_of_nonzero_leader
      hpsi q.1.core q.2.core ⟨horigin, hne⟩
    have hbad : (false : Bool) = true := hfalse.symm.trans hrawOut
    simp at hbad
  exact (writeSeqIncrementGate_labels
    hpsi q.1.core q.2.core).2.trans hzero

/-- If the rooted leader-sink Algorithm-15/WRITE suffix creates an initiator
leader from a follower initiator, it does so by migrating a nonzero-labelled
responder leader.  The certificate is stated at the suffix input boundary,
before Algorithm 15 and WRITE alter the leader's location. -/
theorem authorizedPostSuppressLeaderSink_new_initiator_origin
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) :
    let out := authorizedPostSuppressLeaderSink hpsi l r
    out.1.core.leader = true →
      r.core.leader = true ∧ r.core.label ≠ ⟨0, hpsi⟩ := by
  let q := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  let out := authorizedReconcile
    (writeSeqIncrementGate hpsi) q.1 q.2
  change out.1.core.leader = true →
    r.core.leader = true ∧ r.core.label ≠ ⟨0, hpsi⟩
  intro hout
  have hqLeft : q.1.core.leader = false := by
    cases hq : q.1.core.leader
    · rfl
    · have hrawSink :
          (eliminateLeadersNoCollisionLeaderSink
            hpsi l.core r.core).1.leader = true := hq
      have hrawOld :
          (eliminateLeadersNoCollision hpsi l.core r.core).1.leader = true :=
        (eliminateLeadersNoCollisionLeaderSink_leaders_eq
          hpsi l.core r.core).1.symm.trans hrawSink
      have horigin := eliminateLeadersNoCollision_initiator_origin
        hpsi l.core r.core hrawOld
      rw [hl] at horigin
      contradiction
  have hrawOut :
      (writeSeqIncrementGate hpsi q.1.core q.2.core).1.leader = true :=
    hout
  have hmigrate := writeSeqIncrementGate_new_initiator_requires_responder
    hpsi q.1.core q.2.core hrawOut hqLeft
  have hrawResponderLeader :
      (eliminateLeadersNoCollisionLeaderSink
        hpsi l.core r.core).2.leader = true := hmigrate.1
  have hrawResponderLabel :
      (eliminateLeadersNoCollisionLeaderSink
        hpsi l.core r.core).2.label ≠ ⟨0, hpsi⟩ := hmigrate.2
  have hleaderFrame :
      (eliminateLeadersNoCollisionLeaderSink
        hpsi l.core r.core).2.leader = r.core.leader :=
    (eliminateLeadersNoCollisionLeaderSink_leaders_eq
      hpsi l.core r.core).2.trans
        (eliminateLeadersNoCollision_responder_leader_eq
          hpsi l.core r.core)
  have hlabelFrame :
      (eliminateLeadersNoCollisionLeaderSink
        hpsi l.core r.core).2.label = r.core.label :=
    (eliminateLeadersNoCollisionLeaderSink_labels_eq
      hpsi l.core r.core).2.trans
        (noCollision_labels hpsi l.core r.core).2
  exact ⟨hleaderFrame.symm.trans hrawResponderLeader, by
    intro hrZero
    exact hrawResponderLabel (hlabelFrame.trans hrZero)⟩

/-- The same migration certificate exposed at the exact pre-WRITE boundary.
It also records that gated WRITE consumes the responder leader while framing
its label. -/
theorem authorizedPostSuppressLeaderSink_new_initiator_migration
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false)
    (hout : (authorizedPostSuppressLeaderSink
      hpsi l r).1.core.leader = true) :
    let beforeWrite := authorizedReconcile
      (eliminateLeadersNoCollisionLeaderSink hpsi) l r
    let out := authorizedPostSuppressLeaderSink hpsi l r
    beforeWrite.1.core.leader = false ∧
      beforeWrite.2.core.leader = true ∧
      beforeWrite.2.core.label ≠ ⟨0, hpsi⟩ ∧
      out.2.core.leader = false ∧
      out.2.core.label = beforeWrite.2.core.label := by
  let beforeWrite := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  let out := authorizedPostSuppressLeaderSink hpsi l r
  have hbeforeWriteLeft : beforeWrite.1.core.leader = false := by
    cases hleft : beforeWrite.1.core.leader
    · rfl
    · have hsink :
          (eliminateLeadersNoCollisionLeaderSink
            hpsi l.core r.core).1.leader = true := by
        simpa only [beforeWrite, authorizedReconcile] using hleft
      have hold :
          (eliminateLeadersNoCollision
            hpsi l.core r.core).1.leader = true :=
        (eliminateLeadersNoCollisionLeaderSink_leaders_eq
          hpsi l.core r.core).1.symm.trans hsink
      have horigin := eliminateLeadersNoCollision_initiator_origin
        hpsi l.core r.core hold
      rw [hl] at horigin
      contradiction
  have hwriteLeft :
      (writeSeqIncrementGate hpsi
        beforeWrite.1.core beforeWrite.2.core).1.leader = true := by
    simpa only [out, beforeWrite, authorizedPostSuppressLeaderSink,
      authorizedReconcile] using hout
  have hmigrate := writeSeqIncrementGate_new_initiator_requires_responder
    hpsi beforeWrite.1.core beforeWrite.2.core hwriteLeft hbeforeWriteLeft
  have hrightFalse :=
    writeSeqIncrementGate_responder_false_of_nonzero_leader
      hpsi beforeWrite.1.core beforeWrite.2.core hmigrate
  have hlabels := writeSeqIncrementGate_labels
    hpsi beforeWrite.1.core beforeWrite.2.core
  change beforeWrite.1.core.leader = false ∧
    beforeWrite.2.core.leader = true ∧
    beforeWrite.2.core.label ≠ ⟨0, hpsi⟩ ∧
    out.2.core.leader = false ∧
    out.2.core.label = beforeWrite.2.core.label
  exact ⟨hbeforeWriteLeft, hmigrate.1, hmigrate.2,
    hrightFalse, hlabels.2⟩

theorem authorizedPostSuppress_initiator_label_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel (authorizedPostSuppress hpsi l r) =
      l.core.label := by
  exact (initiatorLabel_eq_of_authorizedPair_eq
    (authorizedPostSuppress_eq_afterWrite hpsi l r)).trans
      (postSuppressAfterWrite_initiator_label_eq hpsi l r)

theorem normalTail_initiator_anchor_of_eq
    (hpsi : psi > 0)
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (heq : after = authorizedPostSuppress hpsi before.1 before.2)
    (hbefore : authorizedInitiatorAnchor before) :
    authorizedInitiatorAnchor after := by
  rw [heq]
  exact authorizedPostSuppress_initiator_anchor
    hpsi before.1 before.2 hbefore

theorem normalTail_responder_survives_of_eq
    (hpsi : psi > 0)
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (heq : after = authorizedPostSuppress hpsi before.1 before.2)
    (hbefore : authorizedResponderZeroAnchor hpsi before) :
    authorizedResponderLeader after := by
  exact responderLeader_of_authorizedPair_eq heq
    (authorizedPostSuppress_responder_zero_survives
      hpsi before.1 before.2 hbefore)

theorem wallSweepAuthorizedNormalTail_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepAuthorizedNormalTail hpsi kappa l r) := by
  exact normalTail_initiator_anchor_of_eq hpsi
    (before := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r)
    (after := wallSweepAuthorizedNormalTail hpsi kappa l r)
    (wallSweepAuthorizedNormalTail_eq_postSuppress hpsi kappa l r)
    (wallSweepAuthorizedNormalAfterSuppress_initiator_anchor
      hpsi kappa l r h)

theorem wallSweepAuthorizedNormalTail_responder_zero_survives
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderLeader
      (wallSweepAuthorizedNormalTail hpsi kappa l r) := by
  exact normalTail_responder_survives_of_eq hpsi
    (before := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r)
    (after := wallSweepAuthorizedNormalTail hpsi kappa l r)
    (wallSweepAuthorizedNormalTail_eq_postSuppress hpsi kappa l r)
    (wallSweepAuthorizedNormalAfterSuppress_responder_zero_anchor
      hpsi kappa l r h)

theorem wallSweepAuthorizedNormalTail_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedInitiatorLabel
      (wallSweepAuthorizedNormalTail hpsi kappa l r) = l.core.label := by
  let q := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  exact (initiatorLabel_eq_of_authorizedPair_eq
    (wallSweepAuthorizedNormalTail_eq_postSuppress hpsi kappa l r)).trans
      ((authorizedPostSuppress_initiator_label_eq hpsi q.1 q.2).trans
        (wallSweepAuthorizedNormalAfterSuppress_initiator_label_eq
          hpsi kappa l r))

/-! ## Anchors through all priority branches -/

private theorem markComparisonForDeletion_initiator_anchor
    (u : AuthorizedAgentState psi) (h : InitiatorAnchor u.core) :
    InitiatorAnchor (markComparisonForDeletion u).core := by
  unfold markComparisonForDeletion
  cases u.core.path <;> exact h

private theorem markComparisonForDeletion_leader
    (u : AuthorizedAgentState psi) (h : u.core.leader = true) :
    (markComparisonForDeletion u).core.leader = true := by
  unfold markComparisonForDeletion
  cases u.core.path <;> exact h

private theorem markComparisonForDeletion_label_eq
    (u : AuthorizedAgentState psi) :
    (markComparisonForDeletion u).core.label = u.core.label := by
  unfold markComparisonForDeletion
  cases u.core.path <;> rfl

private theorem markLeaderBirth_initiator_anchor
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedInitiatorAnchor q) :
    authorizedInitiatorAnchor (markLeaderBirth born q) := by
  unfold markLeaderBirth
  split
  · exact markComparisonForDeletion_initiator_anchor q.1 h
  · exact h

private theorem markLeaderBirth_responder_leader
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedResponderLeader q) :
    authorizedResponderLeader (markLeaderBirth born q) := by
  unfold markLeaderBirth
  split
  · exact markComparisonForDeletion_leader q.2 h
  · exact h

private theorem markLeaderBirth_initiator_label_eq
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedInitiatorLabel (markLeaderBirth born q) =
      authorizedInitiatorLabel q := by
  unfold markLeaderBirth
  split
  · exact markComparisonForDeletion_label_eq q.1
  · rfl

private theorem wallSweep_of_responderDeletion
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = true) :
    wallSweepAuthorizedTransition hpsi kappa l r =
      authorizedEliminateSig hpsi
        (normalizeDeletion l) (normalizeDeletion r) := by
  simp [wallSweepAuthorizedTransition, hr]

private theorem wallSweep_of_initiatorDeletion
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = true) :
    wallSweepAuthorizedTransition hpsi kappa l r =
      (normalizeDeletion l, normalizeDeletion r) := by
  simp [wallSweepAuthorizedTransition, hr, hl]

/-- Priority openness exposes birth marking of exactly the named normal tail. -/
theorem wallSweepAuthorizedTransition_eq_marked_normalTail_of_priority_open
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
    let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
    let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    wallSweepAuthorizedTransition hpsi kappa l r =
      markLeaderBirth born (wallSweepAuthorizedNormalTail hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hnormal := wallSweepAuthorizedTransition_eq_normal_of_priority_open
    hpsi kappa l r hopen
  have htail := wallSweepAuthorizedNormalTail_eq_afterCheckSuffix
    hpsi kappa l r
  change wallSweepAuthorizedNormalTail hpsi kappa l r =
    wallSweepAuthorizedAfterCheckSuffix hpsi afterCheck.1 afterCheck.2 at htail
  exact hnormal.trans (congrArg (markLeaderBirth born) htail.symm)

/-- One priority-open authorized wall call refines exactly to the isolated
Algorithm-15 `PeaceView` under the three stage-local wall obligations. -/
theorem wallSweepAuthorized_priority_open_peaceView_eq_noCollision
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l r) :
    authorizedPeaceViewPair (wallSweepAuthorizedTransition hpsi kappa l r) =
      peaceViewPair (eliminateLeadersNoCollision hpsi l.core r.core) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hstage := congrArg authorizedPeaceViewPair
    (wallSweepAuthorizedTransition_eq_marked_normalTail_of_priority_open
      hpsi kappa l r hopen)
  have hmark := markLeaderBirth_peaceViewPair born
    (wallSweepAuthorizedNormalTail hpsi kappa l r)
  have htail := wallSweepAuthorizedNormalTail_peaceView_eq_noCollision
    hpsi kappa l r hframe
  exact hstage.trans (hmark.trans htail)

/-- One priority-open complete finite wall edge has exactly the `PeaceView` of
the isolated Algorithm-15 kernel on its erased input pair. -/
theorem wallSweepPathStall_priority_open_peaceView_eq_noCollision
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l.core.erase r.core.erase) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    (PeaceView.ofState q.1.core.erase.core,
      PeaceView.ofState q.2.core.erase.core) =
      peaceViewPair (eliminateLeadersNoCollision hpsi
        l.core.erase.core r.core.erase.core) := by
  have hfinite := wallSweepPathStall_peaceView_eq_authorized hpsi l r
  have hauth := wallSweepAuthorized_priority_open_peaceView_eq_noCollision
    hpsi kappa l.core.erase r.core.erase hopen hframe
  exact hfinite.trans hauth

/-- Once the returned absence signal reaches a label-zero leader, one
priority-open full-wall edge fires its shield and preserves the leader. -/
theorem wallSweepPathStall_priority_open_leader_fire_anchor
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l.core.erase r.core.erase)
    (hleader : l.core.erase.core.leader = true)
    (hlabel : l.core.erase.core.label = ⟨0, hpsi⟩)
    (hsignal : l.core.erase.core.signal_B = ⟨1, by omega⟩) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    q.1.core.erase.core.leader = true ∧
      q.1.core.erase.core.shield = true ∧
      q.1.core.erase.core.label = ⟨0, hpsi⟩ ∧
      q.1.core.erase.core.signal_B = ⟨0, by omega⟩ := by
  let raw := eliminateLeadersNoCollision hpsi
    l.core.erase.core r.core.erase.core
  have hview := wallSweepPathStall_priority_open_peaceView_eq_noCollision
    hpsi l r hopen hframe
  have hleft := congrArg Prod.fst hview
  have hrawLeader := noCollision_left_fire_leader hpsi
    l.core.erase.core r.core.erase.core hleader hsignal
  have hrawFields := noCollision_left_fire_fields hpsi
    l.core.erase.core r.core.erase.core hleader hsignal
  have hrawLabel := (noCollision_labels hpsi
    l.core.erase.core r.core.erase.core).1.trans hlabel
  exact ⟨(congrArg PeaceView.leader hleft).trans hrawLeader,
    (congrArg PeaceView.shield hleft).trans hrawFields.1,
    (congrArg PeaceView.label hleft).trans hrawLabel,
    (congrArg PeaceView.signal_B hleft).trans hrawFields.2⟩

/-- On an admissible stable edge, the complete finite wall call propagates an
absence signal exactly as Algorithm 15 does. -/
theorem wallSweepPathStall_priority_open_signal_propagates
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l.core.erase r.core.erase)
    (halign : r.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hrBullet : r.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrSignal : r.core.erase.core.signal_B = ⟨0, by omega⟩)
    (hsource : l.core.erase.core.leader = true ∨
      l.core.erase.core.signal_B = ⟨1, by omega⟩) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    q.2.core.erase.core.signal_B = ⟨1, by omega⟩ := by
  have hview := wallSweepPathStall_priority_open_peaceView_eq_noCollision
    hpsi l r hopen hframe
  have hright := congrArg Prod.snd hview
  have hraw := noCollision_right_signal_one_of_aligned_source hpsi
    l.core.erase.core r.core.erase.core halign hrBullet hrSignal hsource
  exact (congrArg PeaceView.signal_B hright).trans hraw

/-- Before the terminal fire, a full-wall propagation edge frames every other
shield-circuit field when both endpoint bullets are absent. -/
theorem wallSweepPathStall_priority_open_idle_propagation_frame
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l.core.erase r.core.erase)
    (hnoFire : l.core.erase.core.leader = false ∨
      l.core.erase.core.signal_B = ⟨0, by omega⟩)
    (hlBullet : l.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrSignal : r.core.erase.core.signal_B = ⟨0, by omega⟩) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    q.1.core.erase.core.leader = l.core.erase.core.leader ∧
      q.2.core.erase.core.leader = r.core.erase.core.leader ∧
      q.1.core.erase.core.label = l.core.erase.core.label ∧
      q.2.core.erase.core.label = r.core.erase.core.label ∧
      q.1.core.erase.core.shield = l.core.erase.core.shield ∧
      q.2.core.erase.core.shield = r.core.erase.core.shield ∧
      q.1.core.erase.core.bullet = ⟨0, by omega⟩ ∧
      q.2.core.erase.core.bullet = ⟨0, by omega⟩ ∧
      q.1.core.erase.core.signal_B = l.core.erase.core.signal_B := by
  have hview := wallSweepPathStall_priority_open_peaceView_eq_noCollision
    hpsi l r hopen hframe
  have hleft := congrArg Prod.fst hview
  have hright := congrArg Prod.snd hview
  have hraw := noCollision_idle_propagation_frame hpsi
    l.core.erase.core r.core.erase.core hnoFire hlBullet hrBullet hrSignal
  rcases hraw with ⟨hLL, hRL, hLLabel, hRLabel, hLS, hRS,
    hLB, hRB, hLSignal⟩
  exact ⟨(congrArg PeaceView.leader hleft).trans hLL,
    (congrArg PeaceView.leader hright).trans hRL,
    (congrArg PeaceView.label hleft).trans hLLabel,
    (congrArg PeaceView.label hright).trans hRLabel,
    (congrArg PeaceView.shield hleft).trans hLS,
    (congrArg PeaceView.shield hright).trans hRS,
    (congrArg PeaceView.bullet hleft).trans hLB,
    (congrArg PeaceView.bullet hright).trans hRB,
    (congrArg PeaceView.signal_B hleft).trans hLSignal⟩

/-- A T19 active-responder interrupt changes comparison controls only; the
complete finite wall call frames the entire `PeaceView` of both endpoints. -/
theorem wallSweepPathStall_active_responder_peaceView_frame
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hr : deletionActive r.core.erase = true) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    (PeaceView.ofState q.1.core.erase.core,
      PeaceView.ofState q.2.core.erase.core) =
      (PeaceView.ofState l.core.erase.core,
        PeaceView.ofState r.core.erase.core) := by
  let al := l.core.erase
  let ar := r.core.erase
  change deletionActive ar = true at hr
  have hrpath : ar.core.path ≠ .bot := by
    cases hpath : ar.core.path with
    | bot => simp [deletionActive, pathPresent, hpath] at hr
    | some label bit => simp
  have hnr := normalizeDeletion_eq_of_path_present ar hrpath
  let al0 := normalizeDeletion al
  have hbranch : wallSweepAuthorizedTransition hpsi kappa al ar =
      authorizedEliminateSig hpsi al0 ar := by
    simp [wallSweepAuthorizedTransition, al0, hnr, hr]
  have hauth : authorizedPeaceViewPair
      (wallSweepAuthorizedTransition hpsi kappa al ar) =
      authorizedPeaceViewPair (al, ar) := by
    rw [hbranch]
    exact (authorizedEliminateSig_peaceViewPair hpsi al0 ar).trans
      (Prod.ext (normalizeDeletion_peaceView al) rfl)
  exact (wallSweepPathStall_peaceView_eq_authorized hpsi l r).trans hauth

theorem wallSweepPathStall_active_edge_peaceView_frame
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPathStallTransition hpsi kappa tau) C e
    PeaceViewConfigFrame C D := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let q := wallSweepPathStallTransition hpsi kappa tau (C e) (C j)
  have hpair := wallSweepPathStall_active_responder_peaceView_frame
    hpsi (C e) (C j) hactive
  let D := localStep ring
    (wallSweepPathStallTransition hpsi kappa tau) C e
  have hleft : D e = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  change PeaceViewConfigFrame C D
  intro i
  by_cases hie : i = e
  · subst i
    rw [hleft]
    exact congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      rw [hright]
      exact congrArg Prod.snd hpair
    · have hsame : D i = C i := by
        simp [D, localStep, hie, hij, j]
      rw [hsame]

/-- The canonical T19 deletion drain preserves the complete `PeaceView` in
addition to its reset/echo and shield frames. -/
theorem exists_wallSweepDeletionDrain_peaceFrame
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → schedule = []) ∧
      let D := runLocalSchedule ring
        (wallSweepPathStallTransition hpsi kappa tau) C schedule
      NoActiveDeletion D ∧ ResetEchoConfigFrame C D ∧
        ShieldConfigFrame C D ∧ PeaceViewConfigFrame C D := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : NoActiveDeletion C
      · exact ⟨[], by simp, fun _ => rfl, hnone,
          fun i => ResetEchoFrame.refl (C i), ShieldConfigFrame.refl C,
          PeaceViewConfigFrame.refl C⟩
      · have hexists : ∃ j : Fin n,
            deletionActive (C j).core.erase = true := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi : deletionActive (C i).core.erase with
          | false => rfl
          | true => exact False.elim (hnot ⟨i, hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j :=
          rightNeighbor_leftNeighbor_wall ring j
        let C1 := localStep ring
          (wallSweepPathStallTransition hpsi kappa tau) C e
        have hstep := wallSweepPathStall_active_edge_decreases
          hpsi ring hn C e (by simpa [hneighbor] using hj)
        change comparisonPathCount C1 < comparisonPathCount C ∧
          ResetEchoConfigFrame C C1 at hstep
        have hshield := wallSweepPathStall_active_edge_shield_frame
          hpsi ring hn C e (by simpa [hneighbor] using hj)
        change ShieldConfigFrame C C1 at hshield
        have hpeace := wallSweepPathStall_active_edge_peaceView_frame
          hpsi ring hn C e (by simpa [hneighbor] using hj)
        change PeaceViewConfigFrame C C1 at hpeace
        have hlt : comparisonPathCount C1 < k := by
          rw [← hk]
          exact hstep.1
        obtain ⟨tail, htailLength, htailEmpty, htailNoActive,
          htailFrame, htailShield, htailPeace⟩ :=
          ih (comparisonPathCount C1) hlt C1 rfl
        refine ⟨e :: tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro hC
          exact (hnone hC).elim
        · exact htailNoActive
        · exact hstep.2.trans htailFrame
        · exact hshield.trans htailShield
        · exact hpeace.trans htailPeace

theorem wallSweepAuthorized_priority_open_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    authorizedInitiatorLabel
      (wallSweepAuthorizedTransition hpsi kappa l r) = l.core.label := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have heq := initiatorLabel_eq_of_authorizedPair_eq
    (wallSweepAuthorizedTransition_eq_marked_normalTail_of_priority_open
      hpsi kappa l r hopen)
  exact heq.trans ((markLeaderBirth_initiator_label_eq born
    (wallSweepAuthorizedNormalTail hpsi kappa l r)).trans
      (wallSweepAuthorizedNormalTail_initiator_label_eq hpsi kappa l r))

/-- A shielded initiator leader survives every priority branch of the complete
authorized wall transition. -/
theorem wallSweepAuthorizedTransition_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := normalizeDeletion_initiator_anchor l h
  by_cases hrD : deletionActive r0 = true
  · exact initiatorAnchor_of_authorizedPair_eq
      (wallSweep_of_responderDeletion hpsi kappa l r hrD)
        (authorizedEliminateSig_initiator_anchor hpsi l0 r0 hl0)
  · have hr0 : deletionActive r0 = false := by
      cases hv : deletionActive r0 <;> simp_all
    by_cases hlD : deletionActive l0 = true
    · exact initiatorAnchor_of_authorizedPair_eq
        (wallSweep_of_initiatorDeletion hpsi kappa l r hr0 hlD) hl0
    · have hlInactive : deletionActive l0 = false := by
        cases hv : deletionActive l0 <;> simp_all
      have hopen : AuthorizedPriorityOpen l r := by
        change deletionActive l0 = false ∧ deletionActive r0 = false
        exact ⟨hlInactive, hr0⟩
      let tail := wallSweepAuthorizedNormalTail hpsi kappa l r
      let born := leaderBirthBeforeOrAtCheck l0 r0
        (sanitizeAuthorizedPair hpsi
          (wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0))
        (authorizedCheckSig hpsi
          (sanitizeAuthorizedPair hpsi
            (wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0)).1
          (sanitizeAuthorizedPair hpsi
            (wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0)).2)
      exact initiatorAnchor_of_authorizedPair_eq
        (wallSweepAuthorizedTransition_eq_marked_normalTail_of_priority_open
          hpsi kappa l r hopen)
        (markLeaderBirth_initiator_anchor born tail
          (wallSweepAuthorizedNormalTail_initiator_anchor hpsi kappa l r h))

/-- A label-zero responder leader survives every priority branch of the
complete authorized wall transition. -/
theorem wallSweepAuthorizedTransition_responder_zero_survives
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderLeader
      (wallSweepAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hrAnchor := normalizeDeletion_responder_zero_anchor hpsi r h
  by_cases hrD : deletionActive r0 = true
  · have hbranch := authorizedEliminateSig_responder_zero_anchor
      hpsi l0 r0 hrAnchor
    exact responderLeader_of_authorizedPair_eq
      (wallSweep_of_responderDeletion hpsi kappa l r hrD) hbranch.1
  · have hr0 : deletionActive r0 = false := by
      cases hv : deletionActive r0 <;> simp_all
    by_cases hlD : deletionActive l0 = true
    · exact responderLeader_of_authorizedPair_eq
        (wallSweep_of_initiatorDeletion hpsi kappa l r hr0 hlD) hrAnchor.1
    · have hlInactive : deletionActive l0 = false := by
        cases hv : deletionActive l0 <;> simp_all
      have hopen : AuthorizedPriorityOpen l r := by
        change deletionActive l0 = false ∧ deletionActive r0 = false
        exact ⟨hlInactive, hr0⟩
      let tail := wallSweepAuthorizedNormalTail hpsi kappa l r
      let born := leaderBirthBeforeOrAtCheck l0 r0
        (sanitizeAuthorizedPair hpsi
          (wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0))
        (authorizedCheckSig hpsi
          (sanitizeAuthorizedPair hpsi
            (wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0)).1
          (sanitizeAuthorizedPair hpsi
            (wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0)).2)
      exact responderLeader_of_authorizedPair_eq
        (wallSweepAuthorizedTransition_eq_marked_normalTail_of_priority_open
          hpsi kappa l r hopen)
        (markLeaderBirth_responder_leader born tail
          (wallSweepAuthorizedNormalTail_responder_zero_survives
            hpsi kappa l r h))

/-! ## Bounded and path-stall anchor lifts -/

def boundedInitiatorAnchor
    (q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa) : Prop :=
  InitiatorAnchor q.1.erase.core

def boundedResponderLeader
    (q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa) : Prop :=
  q.2.erase.core.leader = true

def boundedInitiatorLabel
    (q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa) : Fin psi :=
  q.1.erase.core.label

def expiringInitiatorAnchor
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop :=
  InitiatorAnchor q.1.core.erase.core

def expiringResponderLeader
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop :=
  q.2.core.erase.core.leader = true

def expiringInitiatorLabel
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Fin psi :=
  q.1.core.erase.core.label

private theorem boundedInitiatorAnchor_of_pair_eq
    {a b : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa}
    (hab : a = b) (hb : boundedInitiatorAnchor b) :
    boundedInitiatorAnchor a := by
  rw [hab]
  exact hb

private theorem boundedResponderLeader_of_pair_eq
    {a b : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa}
    (hab : a = b) (hb : boundedResponderLeader b) :
    boundedResponderLeader a := by
  rw [hab]
  exact hb

private theorem boundedInitiatorLabel_eq_of_pair_eq
    {a b : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa}
    (hab : a = b) : boundedInitiatorLabel a = boundedInitiatorLabel b :=
  congrArg boundedInitiatorLabel hab

private theorem expiringInitiatorAnchor_of_pair_eq
    {a b : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau}
    (hab : a = b) (hb : expiringInitiatorAnchor b) :
    expiringInitiatorAnchor a := by
  rw [hab]
  exact hb

private theorem expiringResponderLeader_of_pair_eq
    {a b : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau}
    (hab : a = b) (hb : expiringResponderLeader b) :
    expiringResponderLeader a := by
  rw [hab]
  exact hb

private theorem expiringInitiatorLabel_eq_of_pair_eq
    {a b : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau}
    (hab : a = b) : expiringInitiatorLabel a = expiringInitiatorLabel b :=
  congrArg expiringInitiatorLabel hab

theorem wallSweepBoundedTransition_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (h : InitiatorAnchor l.erase.core) :
    boundedInitiatorAnchor (wallSweepBoundedTransition hpsi kappa l r) := by
  let q := wallSweepBoundedTransition hpsi kappa l r
  have ha := wallSweepAuthorizedTransition_initiator_anchor
    hpsi kappa l.erase r.erase h
  have he := erase_wallSweepBoundedTransition hpsi kappa l r
  have hL := congrArg Prod.fst he
  change q.1.erase =
    (wallSweepAuthorizedTransition hpsi kappa l.erase r.erase).1 at hL
  unfold boundedInitiatorAnchor
  rw [hL]
  exact ha

theorem wallSweepBoundedTransition_responder_zero_survives
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (h : ResponderZeroAnchor hpsi r.erase.core) :
    boundedResponderLeader (wallSweepBoundedTransition hpsi kappa l r) := by
  let q := wallSweepBoundedTransition hpsi kappa l r
  have ha := wallSweepAuthorizedTransition_responder_zero_survives
    hpsi kappa l.erase r.erase h
  have he := erase_wallSweepBoundedTransition hpsi kappa l r
  have hR := congrArg Prod.snd he
  change q.2.erase =
    (wallSweepAuthorizedTransition hpsi kappa l.erase r.erase).2 at hR
  unfold boundedResponderLeader
  rw [hR]
  exact ha

theorem wallSweepBounded_priority_open_initiator_label_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hopen : AuthorizedPriorityOpen l.erase r.erase) :
    boundedInitiatorLabel (wallSweepBoundedTransition hpsi kappa l r) =
      l.erase.core.label := by
  let q := wallSweepBoundedTransition hpsi kappa l r
  have ha := wallSweepAuthorized_priority_open_initiator_label_eq
    hpsi kappa l.erase r.erase hopen
  have he := erase_wallSweepBoundedTransition hpsi kappa l r
  have hL := congrArg Prod.fst he
  change q.1.erase =
    (wallSweepAuthorizedTransition hpsi kappa l.erase r.erase).1 at hL
  unfold boundedInitiatorLabel
  rw [hL]
  exact ha

private theorem deletionPriorityExpireOne_shield
    (old out : ExpiringAgentState psi kappa tau) :
    (deletionPriorityExpireOne tau old out).core.erase.core.shield =
      out.core.erase.core.shield := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · unfold pathExpireOne
    split
    · rfl
    · split
      · unfold clearComparisonCarrier
        rfl
      · rfl

private theorem deletionPriorityExpireOne_initiator_anchor
    (old out : ExpiringAgentState psi kappa tau)
    (h : InitiatorAnchor out.core.erase.core) :
    InitiatorAnchor
      (deletionPriorityExpireOne tau old out).core.erase.core := by
  have hf := deletionPriorityExpireOne_path_frame old out
  exact ⟨hf.2.1.trans h.1,
    (deletionPriorityExpireOne_shield old out).trans h.2⟩

theorem wallSweepPathStallTransition_eq_expiryStages
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
    let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
    let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
    wallSweepPathStallTransition hpsi kappa tau l r =
      (deletionPriorityExpireOne tau l lBase,
        deletionPriorityExpireOne tau r rBase) := by
  rfl

theorem wallSweepPathStallTransition_initiator_anchor
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (h : InitiatorAnchor l.core.erase.core) :
    expiringInitiatorAnchor
      (wallSweepPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hbase := wallSweepBoundedTransition_initiator_anchor
    hpsi kappa l.core r.core h
  have hfinal := deletionPriorityExpireOne_initiator_anchor l lBase hbase
  exact expiringInitiatorAnchor_of_pair_eq
    (wallSweepPathStallTransition_eq_expiryStages hpsi kappa tau l r)
      hfinal

theorem wallSweepPathStallTransition_responder_zero_survives
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (h : ResponderZeroAnchor hpsi r.core.erase.core) :
    expiringResponderLeader
      (wallSweepPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hbase := wallSweepBoundedTransition_responder_zero_survives
    hpsi kappa l.core r.core h
  have hf := deletionPriorityExpireOne_path_frame r rBase
  have hfinal : (deletionPriorityExpireOne tau r rBase).core.erase.core.leader =
      true := hf.2.1.trans hbase
  exact expiringResponderLeader_of_pair_eq
    (wallSweepPathStallTransition_eq_expiryStages hpsi kappa tau l r)
      hfinal

theorem wallSweepPathStall_priority_open_initiator_label_eq
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r) :
    expiringInitiatorLabel
      (wallSweepPathStallTransition hpsi kappa tau l r) =
      l.core.erase.core.label := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hbase := wallSweepBounded_priority_open_initiator_label_eq
    hpsi kappa l.core r.core hopen
  have hf := deletionPriorityExpireOne_path_frame l lBase
  have hfinal :
      (deletionPriorityExpireOne tau l lBase).core.erase.core.label =
        l.core.erase.core.label := hf.2.2.1.trans hbase
  exact (expiringInitiatorLabel_eq_of_pair_eq
    (wallSweepPathStallTransition_eq_expiryStages
      hpsi kappa tau l r)).trans hfinal

theorem resetEcho_fields_of_pair_eq
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair after = authorizedResetEchoPair before) :
    after.1.core.reset_cmd = before.1.core.reset_cmd ∧
      after.1.core.echo = before.1.core.echo ∧
      after.2.core.reset_cmd = before.2.core.reset_cmd ∧
      after.2.core.echo = before.2.core.echo := by
  have hL := congrArg Prod.fst h
  have hR := congrArg Prod.snd h
  simp only [authorizedResetEchoPair, resetEchoPair, resetEchoView] at hL hR
  exact ⟨congrArg Prod.fst hL, congrArg Prod.snd hL,
    congrArg Prod.fst hR, congrArg Prod.snd hR⟩

/-- The rooted leader-sink Algorithm-15/WRITE suffix preserves an established
leader-source comparison/reset/echo cleanup certificate. -/
theorem authorizedPostSuppressLeaderSink_leader_source_cleanup
    (hpsi : psi > 0)
    (input before : AuthorizedAgentState psi ×
      AuthorizedAgentState psi)
    (h : AuthorizedLeaderSourceCleanup input before) :
    AuthorizedLeaderSourceCleanup input
      (authorizedPostSuppressLeaderSink hpsi before.1 before.2) := by
  have hneutral := authorizedPostSuppressLeaderSink_neutral
    hpsi before.1 before.2 h.1 h.2.1
  have hframe := resetEcho_fields_of_pair_eq
    (authorizedPostSuppressLeaderSink_resetEchoPair
      hpsi before.1 before.2)
  exact ⟨hneutral.1, hneutral.2,
    hframe.1.trans h.2.2.1,
    hframe.2.2.1.trans h.2.2.2.1,
    hframe.2.1.trans h.2.2.2.2.1,
    hframe.2.2.2.trans h.2.2.2.2.2⟩

private theorem authorizedReconcile_reset_handoff_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw :
      let q := f l.core r.core
      ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 ∧
        q.1.reset_cmd = false ∧ q.2.reset_cmd = true) :
    let q := authorizedReconcile f l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.core.reset_cmd = false ∧ q.2.core.reset_cmd = true := by
  exact hraw

/-- Repaired Algorithm 14 realizes the handoff at the named authorized
post-suppression boundary. -/
theorem wallSweepAuthorizedNormalAfterSuppress_reset_handoff
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true)
    (hrEcho : r.core.echo = false) :
    let q := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.core.reset_cmd = false ∧ q.2.core.reset_cmd = true := by
  have hpre := wallSweepAuthorizedNormalBeforeSuppress_resetEchoPair
    hpsi kappa l r
  have hfields := resetEcho_fields_of_pair_eq hpre
  have hpreReset :
      (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r).1.core.reset_cmd =
        true :=
    hfields.1.trans hlReset
  have hpreEcho :
      (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r).2.core.echo =
        false :=
    hfields.2.2.2.trans hrEcho
  have hraw := suppressSigResetKill_handoff hpsi
    (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r).1.core
    (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r).2.core
      hpreReset hpreEcho
  have hauth := authorizedReconcile_reset_handoff_of_raw
    (suppressSigResetKill hpsi)
    (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r).1
    (wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r).2 hraw
  change ComparisonNeutral
      (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r).1.core ∧
    ComparisonNeutral
      (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r).2.core ∧
    (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r).1.core.reset_cmd =
      false ∧
    (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r).2.core.reset_cmd =
      true
  exact hauth

private theorem resetHandoff_of_post_frame
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hbefore : ComparisonNeutral before.1.core ∧
      ComparisonNeutral before.2.core ∧
      before.1.core.reset_cmd = false ∧
      before.2.core.reset_cmd = true)
    (hpost : ComparisonNeutral after.1.core ∧
      ComparisonNeutral after.2.core ∧
      after.1.core.reset_cmd = before.1.core.reset_cmd ∧
      after.2.core.reset_cmd = before.2.core.reset_cmd ∧
      after.1.core.echo = before.1.core.echo ∧
      after.2.core.echo = before.2.core.echo) :
    ComparisonNeutral after.1.core ∧ ComparisonNeutral after.2.core ∧
      after.1.core.reset_cmd = false ∧
      after.2.core.reset_cmd = true :=
  ⟨hpost.1, hpost.2.1,
    hpost.2.2.1.trans hbefore.2.2.1,
    hpost.2.2.2.1.trans hbefore.2.2.2⟩

private theorem markComparisonForDeletion_eq_of_neutral
    (u : AuthorizedAgentState psi) (hu : ComparisonNeutral u.core) :
    markComparisonForDeletion u = u := by
  simp [markComparisonForDeletion, hu.2.1]

/-- Birth marking remains enabled, but is inert after reset cleanup because
there is no physical comparison path left to mark. -/
private theorem markLeaderBirth_eq_of_neutral (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hL : ComparisonNeutral q.1.core) (hR : ComparisonNeutral q.2.core) :
    markLeaderBirth born q = q := by
  unfold markLeaderBirth
  split
  · rw [markComparisonForDeletion_eq_of_neutral q.1 hL,
      markComparisonForDeletion_eq_of_neutral q.2 hR]
  · rfl

/-- The named ordinary tail realizes the reset handoff.  This statement does
not need priority openness because it starts at the ordinary branch itself. -/
theorem wallSweepAuthorizedNormalTail_reset_handoff
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true)
    (hrEcho : r.core.echo = false) :
    let tail := wallSweepAuthorizedNormalTail hpsi kappa l r
    ComparisonNeutral tail.1.core ∧ ComparisonNeutral tail.2.core ∧
      tail.1.core.reset_cmd = false ∧
      tail.2.core.reset_cmd = true := by
  let q2 := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  let tail := wallSweepAuthorizedNormalTail hpsi kappa l r
  have hs := wallSweepAuthorizedNormalAfterSuppress_reset_handoff
    hpsi kappa l r hlReset hrEcho
  have hpost := postSuppress_normalReset_handoff
    hpsi q2.1 q2.2 hs.1 hs.2.1
  let post := authorizedPostSuppress hpsi q2.1 q2.2
  change ComparisonNeutral post.1.core ∧ ComparisonNeutral post.2.core ∧
    post.1.core.reset_cmd = q2.1.core.reset_cmd ∧
    post.2.core.reset_cmd = q2.2.core.reset_cmd ∧
    post.1.core.echo = q2.1.core.echo ∧
    post.2.core.echo = q2.2.core.echo at hpost
  have htailPost := wallSweepAuthorizedNormalTail_eq_postSuppress
    hpsi kappa l r
  change tail = post at htailPost
  have htail : ComparisonNeutral tail.1.core ∧
      ComparisonNeutral tail.2.core ∧
      tail.1.core.reset_cmd = false ∧
      tail.2.core.reset_cmd = true := by
    rw [htailPost]
    exact resetHandoff_of_post_frame hs hpost
  exact htail

/-- On a priority-open call, neutral output makes the birth-marking wrapper
inert and the complete transition is exactly the named ordinary tail. -/
theorem wallSweepAuthorizedTransition_eq_normalTail_of_priority_open
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hL : ComparisonNeutral
      (wallSweepAuthorizedNormalTail hpsi kappa l r).1.core)
    (hR : ComparisonNeutral
      (wallSweepAuthorizedNormalTail hpsi kappa l r).2.core) :
    wallSweepAuthorizedTransition hpsi kappa l r =
      wallSweepAuthorizedNormalTail hpsi kappa l r := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepAuthorizedNormalTail hpsi kappa l r
  have hnormal := wallSweepAuthorizedTransition_eq_normal_of_priority_open
    hpsi kappa l r hopen
  have htailSuffix := wallSweepAuthorizedNormalTail_eq_afterCheckSuffix
    hpsi kappa l r
  change tail = wallSweepAuthorizedAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2 at htailSuffix
  have hnormal' : wallSweepAuthorizedTransition hpsi kappa l r =
      markLeaderBirth born tail := by
    exact hnormal.trans (congrArg (markLeaderBirth born) htailSuffix.symm)
  exact hnormal'.trans (markLeaderBirth_eq_of_neutral born tail hL hR)

/-- A priority-open authorized wall call realizes the exact repaired reset
handoff through the complete ordinary transition.  CHECK birth is not disabled
or assumed absent. -/
theorem wallSweepAuthorized_priority_open_reset_handoff
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlReset : l.core.reset_cmd = true)
    (hrEcho : r.core.echo = false) :
    let q := wallSweepAuthorizedTransition hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.core.reset_cmd = false ∧ q.2.core.reset_cmd = true := by
  have htail := wallSweepAuthorizedNormalTail_reset_handoff
    hpsi kappa l r hlReset hrEcho
  have hout := wallSweepAuthorizedTransition_eq_normalTail_of_priority_open
    hpsi kappa l r hopen htail.1 htail.2.1
  rw [hout]
  exact htail

/-! ## Finite/path-stall lift -/

/-- A neutral bounded base output remains neutral through the outer
deletion/path-stall expiry, and its reset command is framed exactly. -/
private theorem deletionPriorityExpireOne_neutral_reset_frame
    (old out : ExpiringAgentState psi kappa tau)
    (hneutral : ComparisonNeutral out.core.erase.core) :
    let q := deletionPriorityExpireOne tau old out
    ComparisonNeutral q.core.erase.core ∧
      q.core.erase.core.reset_cmd = out.core.erase.core.reset_cmd := by
  have hframe := deletionPriorityExpireOne_path_frame old out
  rcases hframe with ⟨_, _, _, hreset, _, _⟩
  refine ⟨?_, hreset⟩
  unfold deletionPriorityExpireOne
  split
  · exact hneutral
  · unfold pathExpireOne
    split
    · exact hneutral
    · split
      · simp [ComparisonNeutral, clearComparisonCarrier,
          AuthorizedBoundedAgentState.erase, BoundedAgentState.erase]
        rfl
      · exact hneutral

/-- One priority-open full finite wall call realizes the repaired reset
handoff through bounded reification and the outer path-stall policy. -/
theorem wallSweepPathStall_priority_open_reset_handoff
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrEcho : r.core.erase.core.echo = false) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    ComparisonNeutral q.1.core.erase.core ∧
      ComparisonNeutral q.2.core.erase.core ∧
      q.1.core.erase.core.reset_cmd = false ∧
      q.2.core.erase.core.reset_cmd = true := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  let lFinal : ExpiringAgentState psi kappa tau :=
    deletionPriorityExpireOne tau l lBase
  let rFinal : ExpiringAgentState psi kappa tau :=
    deletionPriorityExpireOne tau r rBase
  have htransition :
      wallSweepPathStallTransition hpsi kappa tau l r =
        (lFinal, rFinal) := by
    rfl
  have hopenAuth : AuthorizedPriorityOpen l.core.erase r.core.erase := by
    simpa only [WallPriorityOpen] using hopen
  have hauth := wallSweepAuthorized_priority_open_reset_handoff
    hpsi kappa l.core.erase r.core.erase hopenAuth hlReset hrEcho
  rcases hauth with ⟨haLNeutral, haRNeutral, haLReset, haRReset⟩
  have herase := erase_wallSweepBoundedTransition hpsi kappa l.core r.core
  have hleftErase := congrArg Prod.fst herase
  have hrightErase := congrArg Prod.snd herase
  change bounded.1.erase =
      (wallSweepAuthorizedTransition
        hpsi kappa l.core.erase r.core.erase).1 at hleftErase
  change bounded.2.erase =
      (wallSweepAuthorizedTransition
        hpsi kappa l.core.erase r.core.erase).2 at hrightErase
  have hLBaseNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hleftErase]
    exact haLNeutral
  have hRBaseNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hrightErase]
    exact haRNeutral
  have hLBaseReset : lBase.core.erase.core.reset_cmd = false := by
    change bounded.1.erase.core.reset_cmd = false
    rw [hleftErase]
    exact haLReset
  have hRBaseReset : rBase.core.erase.core.reset_cmd = true := by
    change bounded.2.erase.core.reset_cmd = true
    rw [hrightErase]
    exact haRReset
  have hLFinal :=
    deletionPriorityExpireOne_neutral_reset_frame l lBase hLBaseNeutral
  have hRFinal :=
    deletionPriorityExpireOne_neutral_reset_frame r rBase hRBaseNeutral
  change ComparisonNeutral lFinal.core.erase.core ∧
    lFinal.core.erase.core.reset_cmd = lBase.core.erase.core.reset_cmd at hLFinal
  change ComparisonNeutral rFinal.core.erase.core ∧
    rFinal.core.erase.core.reset_cmd = rBase.core.erase.core.reset_cmd at hRFinal
  rw [htransition]
  exact ⟨hLFinal.1, hRFinal.1,
    hLFinal.2.trans hLBaseReset,
    hRFinal.2.trans hRBaseReset⟩

/-! ## Full-wall echo drain and leader reseed projections -/

private theorem authorizedReconcile_responder_echo_false_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : (f l.core r.core).2.echo = false) :
    authorizedResponderEchoFalse (authorizedReconcile f l r) := by
  exact hraw

private theorem authorizedReconcile_initiator_echo_false_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : (f l.core r.core).1.echo = false) :
    authorizedInitiatorEchoFalse (authorizedReconcile f l r) := by
  exact hraw

private theorem authorizedReconcile_leader_reseed_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : (f l.core r.core).1.echo = false ∧
      (f l.core r.core).2.echo = false ∧
      (f l.core r.core).2.reset_cmd = true) :
    authorizedLeaderReseedResult (authorizedReconcile f l r) := by
  exact hraw

private theorem authorizedReconcile_both_neutral_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : ComparisonNeutral (f l.core r.core).1 ∧
      ComparisonNeutral (f l.core r.core).2) :
    authorizedBothNeutral (authorizedReconcile f l r) := by
  exact hraw

theorem wallSweepAuthorizedNormalAfterSuppress_responder_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedResponderEchoFalse
      (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r) := by
  let pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r
  exact responderEchoFalse_of_authorizedPair_eq
    (wallSweepAuthorizedNormalAfterSuppress_eq_reconcile hpsi kappa l r)
      (authorizedReconcile_responder_echo_false_of_raw
        (suppressSigResetKill hpsi) pre.1 pre.2
          (suppressSigResetKill_responder_echo_false
            hpsi pre.1.core pre.2.core))

theorem afterSuppress_initiator_echo_false_of_eq
    (hpsi : psi > 0)
    {pre out : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hpreAnchor : authorizedInitiatorAnchor pre)
    (hout : out = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2) :
    authorizedInitiatorEchoFalse out := by
  exact initiatorEchoFalse_of_authorizedPair_eq hout
    (authorizedReconcile_initiator_echo_false_of_raw
      (suppressSigResetKill hpsi) pre.1 pre.2
        (suppressSigResetKill_leader_echo_false
          hpsi pre.1.core pre.2.core hpreAnchor.1))

theorem wallSweepAuthorizedNormalAfterSuppress_initiator_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core) :
    authorizedInitiatorEchoFalse
      (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r) := by
  exact afterSuppress_initiator_echo_false_of_eq hpsi
    (pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r)
    (out := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r)
    (wallSweepAuthorizedNormalBeforeSuppress_initiator_anchor
      hpsi kappa l r hanchor)
    (wallSweepAuthorizedNormalAfterSuppress_eq_reconcile hpsi kappa l r)

theorem afterSuppress_leader_reseed_of_eq
    (hpsi : psi > 0)
    {input pre out : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hpreAnchor : authorizedInitiatorAnchor pre)
    (hpreFrame : authorizedResetEchoPair pre = authorizedResetEchoPair input)
    (hout : out = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2)
    (hrEcho : input.2.core.echo = false) :
    authorizedLeaderReseedResult out := by
  have hfields := resetEcho_fields_of_pair_eq hpreFrame
  have hpreEcho : pre.2.core.echo = false :=
    hfields.2.2.2.trans hrEcho
  have hraw := suppressSigResetKill_leader_reseed
    hpsi pre.1.core pre.2.core hpreAnchor.1 hpreEcho
  exact leaderReseedResult_of_authorizedPair_eq hout
    (authorizedReconcile_leader_reseed_of_raw
      (suppressSigResetKill hpsi) pre.1 pre.2 hraw)

theorem afterSuppress_leader_reseed_neutral_of_eq
    (hpsi : psi > 0)
    {input pre out : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hpreAnchor : authorizedInitiatorAnchor pre)
    (hpreFrame : authorizedResetEchoPair pre = authorizedResetEchoPair input)
    (hout : out = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2)
    (hrEcho : input.2.core.echo = false) :
    authorizedBothNeutral out := by
  have hfields := resetEcho_fields_of_pair_eq hpreFrame
  have hpreEcho : pre.2.core.echo = false :=
    hfields.2.2.2.trans hrEcho
  have hraw := suppressSigResetKill_leader_reseed_neutral
    hpsi pre.1.core pre.2.core hpreAnchor.1 hpreEcho
  exact bothNeutral_of_authorizedPair_eq hout
    (authorizedReconcile_both_neutral_of_raw
      (suppressSigResetKill hpsi) pre.1 pre.2 hraw)

theorem wallSweepAuthorizedNormalAfterSuppress_leader_reseed
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedLeaderReseedResult
      (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r) := by
  exact afterSuppress_leader_reseed_of_eq hpsi
    (input := (l, r))
    (pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r)
    (out := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r)
    (wallSweepAuthorizedNormalBeforeSuppress_initiator_anchor
      hpsi kappa l r hanchor)
    (wallSweepAuthorizedNormalBeforeSuppress_resetEchoPair hpsi kappa l r)
    (wallSweepAuthorizedNormalAfterSuppress_eq_reconcile hpsi kappa l r)
    hrEcho

theorem wallSweepAuthorizedNormalAfterSuppress_leader_reseed_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedBothNeutral
      (wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r) := by
  exact afterSuppress_leader_reseed_neutral_of_eq hpsi
    (input := (l, r))
    (pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r)
    (out := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r)
    (wallSweepAuthorizedNormalBeforeSuppress_initiator_anchor
      hpsi kappa l r hanchor)
    (wallSweepAuthorizedNormalBeforeSuppress_resetEchoPair hpsi kappa l r)
    (wallSweepAuthorizedNormalAfterSuppress_eq_reconcile hpsi kappa l r)
    hrEcho

theorem authorizedPostSuppress_responder_echo_false
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : r.core.echo = false) :
    authorizedResponderEchoFalse (authorizedPostSuppress hpsi l r) := by
  have hframe := authorizedPostSuppress_resetEchoPair hpsi l r
  have hfields := resetEcho_fields_of_pair_eq hframe
  exact hfields.2.2.2.trans h

theorem authorizedPostSuppress_initiator_echo_false
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : l.core.echo = false) :
    authorizedInitiatorEchoFalse (authorizedPostSuppress hpsi l r) := by
  have hframe := authorizedPostSuppress_resetEchoPair hpsi l r
  have hfields := resetEcho_fields_of_pair_eq hframe
  exact hfields.2.1.trans h

theorem authorizedPostSuppress_leader_reseed
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : l.core.echo = false ∧ r.core.echo = false ∧
      r.core.reset_cmd = true) :
    authorizedLeaderReseedResult (authorizedPostSuppress hpsi l r) := by
  have hframe := authorizedPostSuppress_resetEchoPair hpsi l r
  have hfields := resetEcho_fields_of_pair_eq hframe
  exact ⟨hfields.2.1.trans h.1,
    hfields.2.2.2.trans h.2.1,
    hfields.2.2.1.trans h.2.2⟩

theorem wallSweepAuthorizedNormalTail_responder_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedResponderEchoFalse
      (wallSweepAuthorizedNormalTail hpsi kappa l r) := by
  let q := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  exact responderEchoFalse_of_authorizedPair_eq
    (wallSweepAuthorizedNormalTail_eq_postSuppress hpsi kappa l r)
      (authorizedPostSuppress_responder_echo_false hpsi q.1 q.2
        (wallSweepAuthorizedNormalAfterSuppress_responder_echo_false
          hpsi kappa l r))

theorem wallSweepAuthorizedNormalTail_initiator_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core) :
    authorizedInitiatorEchoFalse
      (wallSweepAuthorizedNormalTail hpsi kappa l r) := by
  let q := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  exact initiatorEchoFalse_of_authorizedPair_eq
    (wallSweepAuthorizedNormalTail_eq_postSuppress hpsi kappa l r)
      (authorizedPostSuppress_initiator_echo_false hpsi q.1 q.2
        (wallSweepAuthorizedNormalAfterSuppress_initiator_echo_false
          hpsi kappa l r hanchor))

theorem wallSweepAuthorizedNormalTail_leader_reseed
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedLeaderReseedResult
      (wallSweepAuthorizedNormalTail hpsi kappa l r) := by
  let q := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  exact leaderReseedResult_of_authorizedPair_eq
    (wallSweepAuthorizedNormalTail_eq_postSuppress hpsi kappa l r)
      (authorizedPostSuppress_leader_reseed hpsi q.1 q.2
      (wallSweepAuthorizedNormalAfterSuppress_leader_reseed
          hpsi kappa l r hanchor hrEcho))

theorem authorizedPostSuppress_both_neutral
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ComparisonNeutral l.core ∧ ComparisonNeutral r.core) :
    authorizedBothNeutral (authorizedPostSuppress hpsi l r) := by
  have hpost := postSuppress_normalReset_handoff hpsi l r h.1 h.2
  exact ⟨hpost.1, hpost.2.1⟩

theorem wallSweepAuthorizedNormalTail_leader_reseed_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedBothNeutral
      (wallSweepAuthorizedNormalTail hpsi kappa l r) := by
  let q := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  exact bothNeutral_of_authorizedPair_eq
    (wallSweepAuthorizedNormalTail_eq_postSuppress hpsi kappa l r)
      (authorizedPostSuppress_both_neutral hpsi q.1 q.2
        (wallSweepAuthorizedNormalAfterSuppress_leader_reseed_neutral
          hpsi kappa l r hanchor hrEcho))

theorem wallSweepAuthorized_priority_open_leader_reseed_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedBothNeutral
      (wallSweepAuthorizedTransition hpsi kappa l r) := by
  have htail := wallSweepAuthorizedNormalTail_leader_reseed_neutral
    hpsi kappa l r hanchor hrEcho
  have heq := wallSweepAuthorizedTransition_eq_normalTail_of_priority_open
    hpsi kappa l r hopen htail.1 htail.2
  exact bothNeutral_of_authorizedPair_eq heq htail

private theorem markComparisonForDeletion_reset_echo
    (u : AuthorizedAgentState psi) :
    (markComparisonForDeletion u).core.reset_cmd = u.core.reset_cmd ∧
      (markComparisonForDeletion u).core.echo = u.core.echo := by
  unfold markComparisonForDeletion
  cases u.core.path <;> exact ⟨rfl, rfl⟩

theorem markLeaderBirth_responder_echo_false
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedResponderEchoFalse q) :
    authorizedResponderEchoFalse (markLeaderBirth born q) := by
  unfold markLeaderBirth
  split
  · exact (markComparisonForDeletion_reset_echo q.2).2.trans h
  · exact h

theorem markLeaderBirth_initiator_echo_false
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedInitiatorEchoFalse q) :
    authorizedInitiatorEchoFalse (markLeaderBirth born q) := by
  unfold markLeaderBirth
  split
  · exact (markComparisonForDeletion_reset_echo q.1).2.trans h
  · exact h

theorem markLeaderBirth_leader_reseed
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedLeaderReseedResult q) :
    authorizedLeaderReseedResult (markLeaderBirth born q) := by
  unfold markLeaderBirth
  split
  · exact ⟨(markComparisonForDeletion_reset_echo q.1).2.trans h.1,
      (markComparisonForDeletion_reset_echo q.2).2.trans h.2.1,
      (markComparisonForDeletion_reset_echo q.2).1.trans h.2.2⟩
  · exact h

theorem wallSweepAuthorized_priority_open_responder_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    authorizedResponderEchoFalse
      (wallSweepAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  exact responderEchoFalse_of_authorizedPair_eq
    (wallSweepAuthorizedTransition_eq_marked_normalTail_of_priority_open
      hpsi kappa l r hopen)
    (markLeaderBirth_responder_echo_false born
      (wallSweepAuthorizedNormalTail hpsi kappa l r)
        (wallSweepAuthorizedNormalTail_responder_echo_false hpsi kappa l r))

theorem wallSweepAuthorized_priority_open_initiator_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core) :
    authorizedInitiatorEchoFalse
      (wallSweepAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  exact initiatorEchoFalse_of_authorizedPair_eq
    (wallSweepAuthorizedTransition_eq_marked_normalTail_of_priority_open
      hpsi kappa l r hopen)
    (markLeaderBirth_initiator_echo_false born
      (wallSweepAuthorizedNormalTail hpsi kappa l r)
        (wallSweepAuthorizedNormalTail_initiator_echo_false
          hpsi kappa l r hanchor))

theorem wallSweepAuthorized_priority_open_leader_reseed
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedLeaderReseedResult
      (wallSweepAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeRaw
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  exact leaderReseedResult_of_authorizedPair_eq
    (wallSweepAuthorizedTransition_eq_marked_normalTail_of_priority_open
      hpsi kappa l r hopen)
    (markLeaderBirth_leader_reseed born
      (wallSweepAuthorizedNormalTail hpsi kappa l r)
        (wallSweepAuthorizedNormalTail_leader_reseed
          hpsi kappa l r hanchor hrEcho))

def boundedResponderEchoFalse
    (q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa) : Prop :=
  q.2.erase.core.echo = false

def boundedInitiatorEchoFalse
    (q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa) : Prop :=
  q.1.erase.core.echo = false

def boundedLeaderReseedResult
    (q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa) : Prop :=
  q.1.erase.core.echo = false ∧ q.2.erase.core.echo = false ∧
    q.2.erase.core.reset_cmd = true

def boundedBothNeutral
    (q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa) : Prop :=
  ComparisonNeutral q.1.erase.core ∧ ComparisonNeutral q.2.erase.core

def expiringResponderEchoFalse
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop :=
  q.2.core.erase.core.echo = false

def expiringInitiatorEchoFalse
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop :=
  q.1.core.erase.core.echo = false

def expiringLeaderReseedResult
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop :=
  q.1.core.erase.core.echo = false ∧
    q.2.core.erase.core.echo = false ∧
    q.2.core.erase.core.reset_cmd = true

def expiringBothNeutral
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop :=
  ComparisonNeutral q.1.core.erase.core ∧
    ComparisonNeutral q.2.core.erase.core

private theorem boundedResponderEchoFalse_of_pair_eq
    {a b : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa}
    (hab : a = b) (hb : boundedResponderEchoFalse b) :
    boundedResponderEchoFalse a := by
  rw [hab]
  exact hb

private theorem boundedInitiatorEchoFalse_of_pair_eq
    {a b : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa}
    (hab : a = b) (hb : boundedInitiatorEchoFalse b) :
    boundedInitiatorEchoFalse a := by
  rw [hab]
  exact hb

private theorem boundedLeaderReseedResult_of_pair_eq
    {a b : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa}
    (hab : a = b) (hb : boundedLeaderReseedResult b) :
    boundedLeaderReseedResult a := by
  rw [hab]
  exact hb

private theorem boundedBothNeutral_of_pair_eq
    {a b : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa}
    (hab : a = b) (hb : boundedBothNeutral b) :
    boundedBothNeutral a := by
  rw [hab]
  exact hb

private theorem expiringResponderEchoFalse_of_pair_eq
    {a b : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau}
    (hab : a = b) (hb : expiringResponderEchoFalse b) :
    expiringResponderEchoFalse a := by
  rw [hab]
  exact hb

private theorem expiringInitiatorEchoFalse_of_pair_eq
    {a b : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau}
    (hab : a = b) (hb : expiringInitiatorEchoFalse b) :
    expiringInitiatorEchoFalse a := by
  rw [hab]
  exact hb

private theorem expiringLeaderReseedResult_of_pair_eq
    {a b : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau}
    (hab : a = b) (hb : expiringLeaderReseedResult b) :
    expiringLeaderReseedResult a := by
  rw [hab]
  exact hb

private theorem expiringBothNeutral_of_pair_eq
    {a b : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau}
    (hab : a = b) (hb : expiringBothNeutral b) :
    expiringBothNeutral a := by
  rw [hab]
  exact hb

theorem wallSweepBounded_priority_open_responder_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hopen : AuthorizedPriorityOpen l.erase r.erase) :
    boundedResponderEchoFalse (wallSweepBoundedTransition hpsi kappa l r) := by
  let q := wallSweepBoundedTransition hpsi kappa l r
  have ha := wallSweepAuthorized_priority_open_responder_echo_false
    hpsi kappa l.erase r.erase hopen
  have he := erase_wallSweepBoundedTransition hpsi kappa l r
  have hR := congrArg Prod.snd he
  change q.2.erase =
    (wallSweepAuthorizedTransition hpsi kappa l.erase r.erase).2 at hR
  unfold boundedResponderEchoFalse
  rw [hR]
  exact ha

theorem wallSweepBounded_priority_open_initiator_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hopen : AuthorizedPriorityOpen l.erase r.erase)
    (hanchor : InitiatorAnchor l.erase.core) :
    boundedInitiatorEchoFalse (wallSweepBoundedTransition hpsi kappa l r) := by
  let q := wallSweepBoundedTransition hpsi kappa l r
  have ha := wallSweepAuthorized_priority_open_initiator_echo_false
    hpsi kappa l.erase r.erase hopen hanchor
  have he := erase_wallSweepBoundedTransition hpsi kappa l r
  have hL := congrArg Prod.fst he
  change q.1.erase =
    (wallSweepAuthorizedTransition hpsi kappa l.erase r.erase).1 at hL
  unfold boundedInitiatorEchoFalse
  rw [hL]
  exact ha

theorem wallSweepBounded_priority_open_leader_reseed
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hopen : AuthorizedPriorityOpen l.erase r.erase)
    (hanchor : InitiatorAnchor l.erase.core)
    (hrEcho : r.erase.core.echo = false) :
    boundedLeaderReseedResult (wallSweepBoundedTransition hpsi kappa l r) := by
  let q := wallSweepBoundedTransition hpsi kappa l r
  have ha := wallSweepAuthorized_priority_open_leader_reseed
    hpsi kappa l.erase r.erase hopen hanchor hrEcho
  have he := erase_wallSweepBoundedTransition hpsi kappa l r
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change q.1.erase =
    (wallSweepAuthorizedTransition hpsi kappa l.erase r.erase).1 at hL
  change q.2.erase =
    (wallSweepAuthorizedTransition hpsi kappa l.erase r.erase).2 at hR
  unfold boundedLeaderReseedResult
  rw [hL, hR]
  exact ha

theorem wallSweepBounded_priority_open_leader_reseed_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hopen : AuthorizedPriorityOpen l.erase r.erase)
    (hanchor : InitiatorAnchor l.erase.core)
    (hrEcho : r.erase.core.echo = false) :
    boundedBothNeutral (wallSweepBoundedTransition hpsi kappa l r) := by
  let q := wallSweepBoundedTransition hpsi kappa l r
  have ha := wallSweepAuthorized_priority_open_leader_reseed_neutral
    hpsi kappa l.erase r.erase hopen hanchor hrEcho
  have he := erase_wallSweepBoundedTransition hpsi kappa l r
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change q.1.erase =
    (wallSweepAuthorizedTransition hpsi kappa l.erase r.erase).1 at hL
  change q.2.erase =
    (wallSweepAuthorizedTransition hpsi kappa l.erase r.erase).2 at hR
  unfold boundedBothNeutral
  rw [hL, hR]
  exact ha

theorem wallSweepPathStall_priority_open_responder_echo_false
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r) :
    expiringResponderEchoFalse
      (wallSweepPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hbase := wallSweepBounded_priority_open_responder_echo_false
    hpsi kappa l.core r.core hopen
  have hf := deletionPriorityExpireOne_path_frame r rBase
  have hfinal : (deletionPriorityExpireOne tau r rBase).core.erase.core.echo =
      false := hf.2.2.2.2.1.trans hbase
  exact expiringResponderEchoFalse_of_pair_eq
    (wallSweepPathStallTransition_eq_expiryStages hpsi kappa tau l r) hfinal

theorem wallSweepPathStall_priority_open_initiator_echo_false
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core.erase.core) :
    expiringInitiatorEchoFalse
      (wallSweepPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hbase := wallSweepBounded_priority_open_initiator_echo_false
    hpsi kappa l.core r.core hopen hanchor
  have hf := deletionPriorityExpireOne_path_frame l lBase
  have hfinal :
      (deletionPriorityExpireOne tau l lBase).core.erase.core.echo = false :=
    hf.2.2.2.2.1.trans hbase
  exact expiringInitiatorEchoFalse_of_pair_eq
    (wallSweepPathStallTransition_eq_expiryStages hpsi kappa tau l r) hfinal

theorem wallSweepPathStall_priority_open_leader_reseed
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core.erase.core)
    (hrEcho : r.core.erase.core.echo = false) :
    expiringLeaderReseedResult
      (wallSweepPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hbase := wallSweepBounded_priority_open_leader_reseed
    hpsi kappa l.core r.core hopen hanchor hrEcho
  have hLf := deletionPriorityExpireOne_path_frame l lBase
  have hRf := deletionPriorityExpireOne_path_frame r rBase
  have hfinal :
      (deletionPriorityExpireOne tau l lBase).core.erase.core.echo = false ∧
      (deletionPriorityExpireOne tau r rBase).core.erase.core.echo = false ∧
      (deletionPriorityExpireOne tau r rBase).core.erase.core.reset_cmd = true :=
    ⟨hLf.2.2.2.2.1.trans hbase.1,
      hRf.2.2.2.2.1.trans hbase.2.1,
      hRf.2.2.2.1.trans hbase.2.2⟩
  exact expiringLeaderReseedResult_of_pair_eq
    (wallSweepPathStallTransition_eq_expiryStages hpsi kappa tau l r) hfinal

theorem wallSweepPathStall_priority_open_leader_reseed_neutral
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core.erase.core)
    (hrEcho : r.core.erase.core.echo = false) :
    expiringBothNeutral
      (wallSweepPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hbase := wallSweepBounded_priority_open_leader_reseed_neutral
    hpsi kappa l.core r.core hopen hanchor hrEcho
  have hLf := deletionPriorityExpireOne_neutral_reset_frame
    l lBase hbase.1
  have hRf := deletionPriorityExpireOne_neutral_reset_frame
    r rBase hbase.2
  have hfinal :
      ComparisonNeutral
        (deletionPriorityExpireOne tau l lBase).core.erase.core ∧
      ComparisonNeutral
        (deletionPriorityExpireOne tau r rBase).core.erase.core :=
    ⟨hLf.1, hRf.1⟩
  exact expiringBothNeutral_of_pair_eq
    (wallSweepPathStallTransition_eq_expiryStages hpsi kappa tau l r) hfinal

end PPLLWallSweepNormalResetContract

namespace PPLLWallSweepNormalResetContract

open PPLL PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair

variable {psi : Nat}

private theorem q13750_cleanupAux_clearIncrementAction
    (u : AgentState psi) :
    CleanupAuxView.ofState (clearIncrementAction u) =
      CleanupAuxView.ofState u := by
  unfold clearIncrementAction CleanupAuxView.ofState
  repeat (first | rfl | split)

/-- `clearInputIncrementPair`, WriteSeqPersistenceRepair.lean:151-155. -/
theorem clearInputIncrementPair_cleanupAux_frame
    (l r : AgentState psi) :
    cleanupAuxPair (clearInputIncrementPair l r) = cleanupAuxPair (l, r) := by
  unfold clearInputIncrementPair cleanupAuxPair
  rw [q13750_cleanupAux_clearIncrementAction l,
    q13750_cleanupAux_clearIncrementAction r]

/-- `groupInfo`; private factor `cleanupAuxPair_groupInfo`,
WallSweepNormalResetContract.lean:2302. -/
theorem groupInfo_cleanupAux_frame
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (groupInfo hpsi l r) = cleanupAuxPair (l, r) :=
  cleanupAuxPair_groupInfo hpsi l r

/-- `writeSeqGenerate`; private factor near
WallSweepNormalResetContract.lean:2350. -/
theorem writeSeqGenerate_cleanupAux_frame
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (writeSeqGenerate hpsi l r) = cleanupAuxPair (l, r) :=
  cleanupAuxPair_writeSeqGenerate hpsi l r

private theorem q13750_cleanupAux_writeSeqSetWriteReadyTransport
    (u : AgentState psi) :
    CleanupAuxView.ofState (writeSeqSetWriteReadyTransport u) =
      CleanupAuxView.ofState u := by
  unfold writeSeqSetWriteReadyTransport CleanupAuxView.ofState
  cases u.path3 <;> repeat (first | rfl | split)

/-- `writeSeqPrepareTransport`, WriteSeqPersistenceRepair.lean:144-149.
The compare/command factors are the private factors already proved above. -/
theorem writeSeqPrepareTransport_cleanupAux_frame
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (writeSeqPrepareTransport hpsi l r) =
      cleanupAuxPair (l, r) := by
  let q0 := writeSeqReadyTransport l r
  let q1 := writeSeqCompare hpsi q0.1 q0.2
  have hready : cleanupAuxPair q0 = cleanupAuxPair (l, r) := by
    unfold q0 writeSeqReadyTransport cleanupAuxPair
    rw [q13750_cleanupAux_writeSeqSetWriteReadyTransport l,
      q13750_cleanupAux_writeSeqSetWriteReadyTransport r]
  change cleanupAuxPair (writeSeqCommands hpsi q1.1 q1.2) =
    cleanupAuxPair (l, r)
  exact (cleanupAuxPair_writeSeqCommands hpsi q1.1 q1.2).trans
    ((cleanupAuxPair_writeSeqCompare hpsi q0.1 q0.2).trans hready)

/-- `gatePreparedIncrement`, private factor immediately after the ordinary
prepare factor in WallSweepNormalResetContract.lean:2440ff. -/
theorem gatePreparedIncrementPair_cleanupAux_frame
    (l r : AgentState psi) :
    cleanupAuxPair
        (gatePreparedIncrement l, gatePreparedIncrement r) =
      cleanupAuxPair (l, r) := by
  unfold cleanupAuxPair
  rw [cleanupAux_gatePreparedIncrement l,
    cleanupAux_gatePreparedIncrement r]

private theorem q13750_cleanupAux_writeActionActivateNonempty
    (hpsi : psi > 0) (u : AgentState psi) :
    CleanupAuxView.ofState (writeActionActivateNonempty hpsi u) =
      CleanupAuxView.ofState u := by
  unfold writeActionActivateNonempty CleanupAuxView.ofState
  repeat (first | rfl | split)

private theorem q13750_cleanupAux_writeActionApplyIncrementAndFlip
    (u : AgentState psi) :
    CleanupAuxView.ofState (writeActionApplyIncrementAndFlip u) =
      CleanupAuxView.ofState u := by
  cases hpath : u.path3 <;>
    simp [writeActionApplyIncrementAndFlip, hpath, CleanupAuxView.ofState]

private theorem q13750_cleanupAux_writeActionPropagateState
    (u : AgentState psi) (s : WriteState) :
    CleanupAuxView.ofState (writeActionPropagateState u s) =
      CleanupAuxView.ofState u := by
  cases s <;> rfl

private theorem q13750_cleanupAux_ite
    (p : Prop) [Decidable p] (u v : AgentState psi) :
    CleanupAuxView.ofState (if p then u else v) =
      if p then CleanupAuxView.ofState u else CleanupAuxView.ofState v := by
  split <;> rfl

private theorem q13750_cleanupAux_setWriteState
    (u : AgentState psi) (s : WriteState) :
    CleanupAuxView.ofState { u with write_state := s } =
      CleanupAuxView.ofState u := rfl

private theorem q13750_writeActionExecutePreservingDepart_cleanupAux
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (writeActionExecutePreservingDepart hpsi l r) =
      cleanupAuxPair (l, r) := by
  unfold writeActionExecutePreservingDepart
  split
  · simp only [cleanupAuxPair, q13750_cleanupAux_ite,
      q13750_cleanupAux_setWriteState,
      cleanupAux_writeActionApplyOverwrite,
      cleanupAux_writeActionApplyMoveFlip,
      q13750_cleanupAux_writeActionApplyIncrementAndFlip,
      q13750_cleanupAux_writeActionPropagateState, ite_self]
  · rfl

private theorem q13750_writeActionExecutePreservingComparison_cleanupAux
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (writeActionExecutePreservingComparison hpsi l r) =
      cleanupAuxPair (l, r) := by
  unfold writeActionExecutePreservingComparison
  split
  · rfl
  · exact q13750_writeActionExecutePreservingDepart_cleanupAux hpsi l r

/-- `writeActionPreservingComparison`, WriteSeqPersistenceRepair.lean:290-294. -/
theorem writeActionPreservingComparison_cleanupAux_frame
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (writeActionPreservingComparison hpsi l r) =
      cleanupAuxPair (l, r) := by
  change cleanupAuxPair
      (writeActionExecutePreservingComparison hpsi
        (writeActionActivateNonempty hpsi l)
        (writeActionActivateNonempty hpsi r)) = cleanupAuxPair (l, r)
  exact
    (q13750_writeActionExecutePreservingComparison_cleanupAux hpsi
      (writeActionActivateNonempty hpsi l)
      (writeActionActivateNonempty hpsi r)).trans
      (by
        unfold cleanupAuxPair
        rw [q13750_cleanupAux_writeActionActivateNonempty hpsi l,
          q13750_cleanupAux_writeActionActivateNonempty hpsi r])

private theorem q13750_moveWsigTransferStopAligned_cleanupAux
    (l r : AgentState psi) :
    cleanupAuxPair (moveWsigTransferStopAligned l r) =
      cleanupAuxPair (l, r) := by
  cases hl : l.path3 with
  | none =>
      simp [moveWsigTransferStopAligned, hl, cleanupAuxPair,
        CleanupAuxView.ofState]
  | some p3 =>
      cases hr : r.path3 with
      | some p3r =>
          simp [moveWsigTransferStopAligned, hl, hr, cleanupAuxPair,
            CleanupAuxView.ofState]
      | none =>
          by_cases hd : l.write_state = .depart
          · by_cases he : r.ws_echo = false
            · simp [moveWsigTransferStopAligned, hl, hr, hd, he,
                cleanupAuxPair, CleanupAuxView.ofState]
            · simp [moveWsigTransferStopAligned, hl, hr, hd, he,
                cleanupAuxPair, CleanupAuxView.ofState]
          · simp [moveWsigTransferStopAligned, hl, hr, hd,
              cleanupAuxPair, CleanupAuxView.ofState]

private theorem q13750_moveWsigMoveWritePreservingNonempty_cleanupAux
    (l r : AgentState psi) :
    cleanupAuxPair (moveWsigMoveWritePreservingNonempty l r) =
      cleanupAuxPair (l, r) := by
  unfold moveWsigMoveWritePreservingNonempty cleanupAuxPair
  split <;> rfl

private theorem q13750_moveWsigFinishPreservingCommand_cleanupAux
    (l r : AgentState psi) :
    cleanupAuxPair (moveWsigFinishPreservingCommand l r) =
      cleanupAuxPair (l, r) := by
  let q0 := moveWsigMoveWritePreservingNonempty l r
  let q1 := moveWsigLeaderSignal q0.1 q0.2
  let q2 := moveWsigSignalMove q1.1 q1.2
  change cleanupAuxPair (moveWsigEchoMove q2.1 q2.2) = cleanupAuxPair (l, r)
  exact (cleanupAuxPair_moveWsigEchoMove q2.1 q2.2).trans
    ((cleanupAuxPair_moveWsigSignalMove q1.1 q1.2).trans
      ((cleanupAuxPair_moveWsigLeaderSignal q0.1 q0.2).trans
        (q13750_moveWsigMoveWritePreservingNonempty_cleanupAux l r)))

/-- `moveWsigStopAligned`, WriteSeqPersistenceRepair.lean:397-403. -/
theorem moveWsigStopAligned_cleanupAux_frame
    (hpsi : psi > 0) (l r : AgentState psi) :
    cleanupAuxPair (moveWsigStopAligned hpsi l r) =
      cleanupAuxPair (l, r) := by
  let q0 := moveWsigStart l r
  let q1 := (moveWsigCheckLast q0.1, q0.2)
  let q2 := moveWsigTransferStopAligned q1.1 q1.2
  have hcheck : cleanupAuxPair q1 = cleanupAuxPair q0 := by
    unfold q1 cleanupAuxPair
    rw [cleanupAux_moveWsigCheckLast q0.1]
  change cleanupAuxPair (moveWsigFinishPreservingCommand q2.1 q2.2) =
    cleanupAuxPair (l, r)
  exact (q13750_moveWsigFinishPreservingCommand_cleanupAux q2.1 q2.2).trans
    ((q13750_moveWsigTransferStopAligned_cleanupAux q1.1 q1.2).trans
      (hcheck.trans (cleanupAuxPair_moveWsigStart l r)))

end PPLLWallSweepNormalResetContract

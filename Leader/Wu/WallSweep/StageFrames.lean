import Leader.Wu.WallSweep.FiniteIntegration
import Leader.Wu.Safety.NoCheckBirthLeaderFrames
import Leader.Wu.Safety.NoCheckBirthBoundaryFrames

/-!
# Stage frames of the authorized pre-CHECK prefix, stated at variables

The pre-CHECK prefixes `wallSweepAuthorizedBeforeCheck` and
`wallSweepResetProbeAuthorizedBeforeCheck` are four authorized stages after a
P-prime stage.  Proofs about the composed prefix that chain whole-stage facts
through `let`-bound stage outputs make the elaborator unify a stage output with
a differently shaped term; it then reduces the composed protocol (`whnf`
through every earlier stage's `if` conditions), which cost minutes per theorem.

This module gives each stage's leader and label frame for one stage applied to
variables, and the definitional unfolding of each prefix into its stages.  A
caller rewrites the prefix with `_stages`, generalizes the stage outputs one at
a time, and applies the stage lemmas by syntactic matching.
-/

namespace PPLLWallSweepStageFrames

open PPLL PPLLRepair PPLLAuthorizedComparisonRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthBoundaryFrames

variable {psi : Nat}

/-! ## Readers at variables -/

theorem leaders_of_leaderPair_eq {p : AgentState psi × AgentState psi}
    {a b : Bool} (h : leaderPair p = (a, b)) :
    p.1.leader = a ∧ p.2.leader = b :=
  ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem labels_of_labelPair_eq {p : AgentState psi × AgentState psi}
    {a b : Fin psi} (h : labelPair p = (a, b)) :
    p.1.label = a ∧ p.2.label = b :=
  ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Authorization reconciliation keeps the raw cores (at a variable stage). -/
theorem authorizedReconcile_core_pair
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    ((authorizedReconcile f l r).1.core, (authorizedReconcile f l r).2.core) =
      f l.core r.core :=
  rfl

theorem authorizedReconcile_leaders_eq
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).1.core.leader = (f l.core r.core).1.leader ∧
      (authorizedReconcile f l r).2.core.leader = (f l.core r.core).2.leader :=
  ⟨rfl, rfl⟩

theorem authorizedReconcile_labels_eq
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).1.core.label = (f l.core r.core).1.label ∧
      (authorizedReconcile f l r).2.core.label = (f l.core r.core).2.label :=
  ⟨rfl, rfl⟩

/-! ## One stage at variables -/

theorem authorizedGenSig_leaders_eq
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    (authorizedGenSig hpsi kappa l r).1.core.leader = l.core.leader ∧
      (authorizedGenSig hpsi kappa l r).2.core.leader = r.core.leader := by
  have hraw := leaders_of_leaderPair_eq
    (genSigSaturated_leaders hpsi kappa l.core r.core)
  have hrec := authorizedReconcile_leaders_eq (genSigSaturated hpsi kappa) l r
  exact ⟨hrec.1.trans hraw.1, hrec.2.trans hraw.2⟩

theorem authorizedGenSig_labels_eq
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    (authorizedGenSig hpsi kappa l r).1.core.label = l.core.label ∧
      (authorizedGenSig hpsi kappa l r).2.core.label = r.core.label := by
  have hraw := labels_of_labelPair_eq
    (genSigSaturated_labels hpsi kappa l.core r.core)
  have hrec := authorizedReconcile_labels_eq (genSigSaturated hpsi kappa) l r
  exact ⟨hrec.1.trans hraw.1, hrec.2.trans hraw.2⟩

theorem authorizedCleanSig_leaders_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCleanSig hpsi l r).1.core.leader = l.core.leader ∧
      (authorizedCleanSig hpsi l r).2.core.leader = r.core.leader := by
  have hraw := PPLLVerify.cleanSig_leaders_eq hpsi l.core r.core
  have hrec := authorizedReconcile_leaders_eq (cleanSig hpsi) l r
  exact ⟨hrec.1.trans hraw.1, hrec.2.trans hraw.2⟩

theorem authorizedCleanSig_labels_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCleanSig hpsi l r).1.core.label = l.core.label ∧
      (authorizedCleanSig hpsi l r).2.core.label = r.core.label := by
  have hraw := PPLLVerify.cleanSig_labels_eq hpsi l.core r.core
  have hrec := authorizedReconcile_labels_eq (cleanSig hpsi) l r
  exact ⟨hrec.1.trans hraw.1, hrec.2.trans hraw.2⟩

theorem authorizedEliminateSig_leaders_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedEliminateSig hpsi l r).1.core.leader = l.core.leader ∧
      (authorizedEliminateSig hpsi l r).2.core.leader = r.core.leader := by
  have hraw := PPLLVerify.eliminateSig_leaders_eq hpsi l.core r.core
  have hrec := authorizedReconcile_leaders_eq (eliminateSig hpsi) l r
  exact ⟨hrec.1.trans hraw.1, hrec.2.trans hraw.2⟩

theorem authorizedEliminateSig_labels_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedEliminateSig hpsi l r).1.core.label = l.core.label ∧
      (authorizedEliminateSig hpsi l r).2.core.label = r.core.label := by
  have hraw := PPLLVerify.eliminateSig_labels_eq hpsi l.core r.core
  have hrec := authorizedReconcile_labels_eq (eliminateSig hpsi) l r
  exact ⟨hrec.1.trans hraw.1, hrec.2.trans hraw.2⟩

theorem authorizedCheckSig_labels_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCheckSig hpsi l r).1.core.label = l.core.label ∧
      (authorizedCheckSig hpsi l r).2.core.label = r.core.label := by
  have hraw := PPLLVerify.checkSig_labels_eq hpsi l.core r.core
  have hrec := authorizedReconcile_labels_eq (checkSig hpsi) l r
  exact ⟨hrec.1.trans hraw.1, hrec.2.trans hraw.2⟩

theorem authorizedSigMoveLeaderWall_leaders_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedSigMoveLeaderWall hpsi l r).1.core.leader = l.core.leader ∧
      (authorizedSigMoveLeaderWall hpsi l r).2.core.leader =
        r.core.leader := by
  have hcore := authorizedSigMoveLeaderWall_core hpsi l r
  have hraw := sigMoveLeaderWall_leaders_eq hpsi l.core r.core
  exact ⟨(congrArg (fun q : AgentState psi × AgentState psi => q.1.leader)
      hcore).trans hraw.1,
    (congrArg (fun q : AgentState psi × AgentState psi => q.2.leader)
      hcore).trans hraw.2⟩

theorem authorizedSigMoveLeaderWall_labels_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedSigMoveLeaderWall hpsi l r).1.core.label = l.core.label ∧
      (authorizedSigMoveLeaderWall hpsi l r).2.core.label =
        r.core.label := by
  have hcore := authorizedSigMoveLeaderWall_core hpsi l r
  have hraw := sigMoveLeaderWall_labels_eq hpsi l.core r.core
  exact ⟨(congrArg (fun q : AgentState psi × AgentState psi => q.1.label)
      hcore).trans hraw.1,
    (congrArg (fun q : AgentState psi × AgentState psi => q.2.label)
      hcore).trans hraw.2⟩

/-! ## The prefixes are their stages, by definition -/

theorem wallSweepAuthorizedBeforeCheck_stages
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    wallSweepAuthorizedBeforeCheck hpsi kappa l r =
      authorizedSigMoveLeaderWall hpsi
        (authorizedEliminateSig hpsi
          (authorizedCleanSig hpsi
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderProbeWall hpsi l r).1
              (authorizedPPsiLeaderProbeWall hpsi l r).2).1
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderProbeWall hpsi l r).1
              (authorizedPPsiLeaderProbeWall hpsi l r).2).2).1
          (authorizedCleanSig hpsi
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderProbeWall hpsi l r).1
              (authorizedPPsiLeaderProbeWall hpsi l r).2).1
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderProbeWall hpsi l r).1
              (authorizedPPsiLeaderProbeWall hpsi l r).2).2).2).1
        (authorizedEliminateSig hpsi
          (authorizedCleanSig hpsi
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderProbeWall hpsi l r).1
              (authorizedPPsiLeaderProbeWall hpsi l r).2).1
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderProbeWall hpsi l r).1
              (authorizedPPsiLeaderProbeWall hpsi l r).2).2).1
          (authorizedCleanSig hpsi
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderProbeWall hpsi l r).1
              (authorizedPPsiLeaderProbeWall hpsi l r).2).1
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderProbeWall hpsi l r).1
              (authorizedPPsiLeaderProbeWall hpsi l r).2).2).2).2 :=
  rfl

theorem wallSweepResetProbeAuthorizedBeforeCheck_stages
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r =
      authorizedSigMoveLeaderWall hpsi
        (authorizedEliminateSig hpsi
          (authorizedCleanSig hpsi
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderResetProbeWall hpsi l r).1
              (authorizedPPsiLeaderResetProbeWall hpsi l r).2).1
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderResetProbeWall hpsi l r).1
              (authorizedPPsiLeaderResetProbeWall hpsi l r).2).2).1
          (authorizedCleanSig hpsi
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderResetProbeWall hpsi l r).1
              (authorizedPPsiLeaderResetProbeWall hpsi l r).2).1
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderResetProbeWall hpsi l r).1
              (authorizedPPsiLeaderResetProbeWall hpsi l r).2).2).2).1
        (authorizedEliminateSig hpsi
          (authorizedCleanSig hpsi
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderResetProbeWall hpsi l r).1
              (authorizedPPsiLeaderResetProbeWall hpsi l r).2).1
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderResetProbeWall hpsi l r).1
              (authorizedPPsiLeaderResetProbeWall hpsi l r).2).2).1
          (authorizedCleanSig hpsi
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderResetProbeWall hpsi l r).1
              (authorizedPPsiLeaderResetProbeWall hpsi l r).2).1
            (authorizedGenSig hpsi kappa
              (authorizedPPsiLeaderResetProbeWall hpsi l r).1
              (authorizedPPsiLeaderResetProbeWall hpsi l r).2).2).2).2 :=
  rfl

end PPLLWallSweepStageFrames

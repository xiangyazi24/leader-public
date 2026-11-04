import Leader.Wu.Birth.ResponderHazardRows

/-!
# Physical stage events in the old action-one responder

The trace is computed from the actual calls. The recorded events are a GEN
assignment or a literal empty path at a physical clearing boundary. A change
of an arbitrary projection is never declared an event. This is a residence
observer; global source/cohort semantics are a separate obligation.
-/

set_option autoImplicit false

namespace BirthResponderHazardTrace

open PPLL PPLLRepair PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLTerminalEqualSupportRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLWallSweepNormalResetContract PPLLCompleteMultiLeaderCleanup
  BirthCheckCongestGuardRepair BirthMismatchDisposalProducer
  BirthResponderHazardRows

variable {psi : Nat}

abbrev APair (psi : Nat) := AuthorizedAgentState psi × AuthorizedAgentState psi
abbrev RPair (psi : Nat) := AgentState psi × AgentState psi

/-- Values only: no caller-supplied success, preservation, or loss field. -/
structure OrdinaryTrace (psi : Nat) where
  ppsi : APair psi
  gen : APair psi
  clean : APair psi
  eliminate : APair psi
  movePre : RPair psi
  moved : RPair psi
  moveWall : RPair psi
  move : APair psi
  reset : APair psi
  sanitized : APair psi
  checked : APair psi
  disappeared : APair psi
  compared : APair psi
  suppressed : APair psi
  post : APair psi
  output : APair psi
  genWrite : Bool

def ordinaryTrace (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : OrdinaryTrace psi :=
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  let m0 := sigMoveLeaderPreclear hpsi q3.1.core q3.2.core
  let m1 := sigMoveTransfers m0.1 m0.2
  let m2 := comparisonLeaderWall m1.1 m1.2
  let q4 := authorizedSigMoveLeaderWall hpsi q3.1 q3.2
  let qR := preCheckResetWall q4.1 q4.2
  let q5 := sanitizeAuthorizedPair hpsi qR
  let q6 := congestGuardCheck hpsi q5.1 q5.2
  let q7 := authorizedDisappear hpsi q6.1 q6.2
  let q8 := authorizedCompareSigActionOne hpsi q7.1 q7.2
  let q9 := authorizedReconcile (suppressSigResetKill hpsi) q8.1 q8.2
  let q10 := authorizedPostSuppressLeaderSink hpsi q9.1 q9.2
  let born := leaderBirthBeforeOrAtCheck l r q5 q6
  let q11 := markLeaderBirth born q10
  ⟨q0, q1, q2, q3, m0, m1, m2, q4, qR, q5, q6, q7, q8, q9, q10, q11,
    rightGenWrite hpsi kappa q0.1 q0.2⟩

/-- Every listed element is the right path at an actual clearing boundary.
In particular, the pre-SIGMOVE empty slot is observed before a refill. -/
def clearingPaths (t : OrdinaryTrace psi) : List PathInfo :=
  [t.clean.2.core.path, t.eliminate.2.core.path, t.movePre.2.path,
    t.moveWall.2.path, t.reset.2.core.path, t.suppressed.2.core.path]

def StageEvent (t : OrdinaryTrace psi) : Prop :=
  t.genWrite = true ∨ .bot ∈ clearingPaths t

instance stageEventDecidable (t : OrdinaryTrace psi) : Decidable (StageEvent t) := by
  unfold StageEvent
  infer_instance

/-- Erasure into the exact ordinary branch, including the actual birth marker. -/
theorem ordinary_output_eq (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (ordinaryTrace hpsi kappa l r).output =
      let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r
      let afterCheck := congestGuardCheck hpsi beforeCheck.1 beforeCheck.2
      markLeaderBirth (leaderBirthBeforeOrAtCheck l r beforeCheck afterCheck)
        (actionOneAfterCheckSuffix hpsi afterCheck.1 afterCheck.2) := by
  rfl

attribute [local irreducible] authorizedPPsiLeaderResetProbeWall authorizedGenSig
  authorizedCleanSig authorizedEliminateSig sigMoveLeaderPreclear sigMoveTransfers
  comparisonLeaderWall sigMoveControlTail authorizedSigMoveLeaderWall
  preCheckResetWall sanitizeAuthorizedPair congestGuardCheck authorizedDisappear
  authorizedCompareSigActionOne suppressSigResetKill authorizedPostSuppressLeaderSink
  markLeaderBirth

/-- This preservation statement is derived from physical row effects. Its
premise excludes only explicit GEN assignments and actual path clearing. -/
theorem no_stage_event_path (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (he : ¬ StageEvent (ordinaryTrace hpsi kappa l r)) :
    (ordinaryTrace hpsi kappa l r).output.2.core.path = r.core.path := by
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  let m0 := sigMoveLeaderPreclear hpsi q3.1.core q3.2.core
  let m1 := sigMoveTransfers m0.1 m0.2
  let m2 := comparisonLeaderWall m1.1 m1.2
  let q4 := authorizedSigMoveLeaderWall hpsi q3.1 q3.2
  let qR := preCheckResetWall q4.1 q4.2
  let q5 := sanitizeAuthorizedPair hpsi qR
  let q6 := congestGuardCheck hpsi q5.1 q5.2
  let q7 := authorizedDisappear hpsi q6.1 q6.2
  let q8 := authorizedCompareSigActionOne hpsi q7.1 q7.2
  let q9 := authorizedReconcile (suppressSigResetKill hpsi) q8.1 q8.2
  let q10 := authorizedPostSuppressLeaderSink hpsi q9.1 q9.2
  have hgen : rightGenWrite hpsi kappa q0.1 q0.2 = false := by
    cases hw : rightGenWrite hpsi kappa q0.1 q0.2
    · rfl
    · exact (he (Or.inl hw)).elim
  have hn : ∀ p ∈ [q2.2.core.path, q3.2.core.path, m0.2.path, m2.2.path,
      qR.2.core.path, q9.2.core.path], p ≠ .bot := by
    intro p hp hb
    exact he (Or.inr (hb ▸ hp))
  have h0 : q0.2.core.path = r.core.path := ppsi_right_path hpsi l r
  have h1 : q1.2.core.path = q0.2.core.path := gen_right_path_of_no_write hpsi kappa _ _ hgen
  have h2 : q2.2.core.path = q1.2.core.path :=
    (clean_right hpsi _ _).retains (hn _ (by simp [q2, q3, m0, m2, qR, q9]))
  have h3 : q3.2.core.path = q2.2.core.path :=
    (eliminate_right hpsi _ _).retains (hn _ (by simp [q2, q3, m0, m2, qR, q9]))
  have hm0 : m0.2.path = q3.2.core.path :=
    (preclear_right hpsi _ _).retains (hn _ (by simp [q2, q3, m0, m2, qR, q9]))
  have hm1 : m1.2.path = m0.2.path := transfers_right_of_present _ _ (hn _ (by simp [q2, q3, m0, m2, qR, q9]))
  have hm2 : m2.2.path = m1.2.path := (wall_right _ _).retains (hn _ (by simp [q2, q3, m0, m2, qR, q9]))
  have h4 : q4.2.core.path = m2.2.path := by
    have hc := congrArg Prod.snd (authorizedSigMoveLeaderWall_core hpsi q3.1 q3.2)
    exact (congrArg AgentState.path hc).trans (control_right_path hpsi m2.1 m2.2)
  have hR : qR.2.core.path = q4.2.core.path := (reset_right _ _).retains (hn _ (by simp [q2, q3, m0, m2, qR, q9]))
  have h5 : q5.2.core.path = qR.2.core.path := sanitize_right_path hpsi _ _
  have h6 : q6.2.core.path = q5.2.core.path := check_right_path_eq hpsi _ _
  have h7 : q7.2.core.path = q6.2.core.path := disappear_right_path hpsi _ _
  have h8 : q8.2.core.path = q7.2.core.path := compare_right_path hpsi _ _
  have h9 : q9.2.core.path = q8.2.core.path := (suppress_right hpsi _ _).retains (hn _ (by simp [q2, q3, m0, m2, qR, q9]))
  have h10 : q10.2.core.path = q9.2.core.path := post_right_path hpsi _ _
  exact (mark_right_path _ _).trans
    (h10.trans (h9.trans (h8.trans (h7.trans (h6.trans (h5.trans
      (hR.trans (h4.trans (hm2.trans (hm1.trans (hm0.trans
        (h3.trans (h2.trans (h1.trans h0))))))))))))))

theorem ordinary_output_canonical (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizationCanonical (ordinaryTrace hpsi kappa l r).output.2 :=
  mark_right_canonical _ _ (post_right_canonical hpsi _ _)

/-- Normalization of the actual ordinary suffix forbids a permission-only
refresh on a retained nonzero payload. No fixed-left premise is used. -/
theorem no_stage_event_nonzero (hpsi : 0 < psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (j bit : Nat)
    (hp : r.core.path = .some j bit) (hj : j ≠ 0)
    (he : ¬ StageEvent (ordinaryTrace hpsi kappa l r)) :
    (ordinaryTrace hpsi kappa l r).output.2.core.path = .some j bit ∧
      (ordinaryTrace hpsi kappa l r).output.2.path0Crossed = false := by
  have hout := (no_stage_event_path hpsi kappa l r he).trans hp
  refine ⟨hout, ?_⟩
  cases hb : (ordinaryTrace hpsi kappa l r).output.2.path0Crossed
  · rfl
  · obtain ⟨b, hh⟩ := ordinary_output_canonical hpsi kappa l r hb
    rw [hout] at hh
    cases hh
    exact (hj rfl).elim

end BirthResponderHazardTrace

#print axioms BirthResponderHazardTrace.ordinary_output_eq
#print axioms BirthResponderHazardTrace.no_stage_event_path
#print axioms BirthResponderHazardTrace.no_stage_event_nonzero

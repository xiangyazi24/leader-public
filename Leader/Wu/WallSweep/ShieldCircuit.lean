import Leader.Wu.WallSweep.NormalResetContract

/-!
# Clockwise absence-signal shield circuit

This module isolates the spatial induction behind the source Algorithm-15
shield mechanism.  A unique label-zero leader seeds the absence signal, the
signal advances clockwise through every other agent, and the returned signal
then triggers the leader's shield.  The physical wall refinement supplies the
same local transition later; this section first proves the exact isolated
kernel geometry without finite enumeration.
-/

namespace PPLLWallSweepShieldCircuit

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLWallSweepNormalResetContract
  PPLLLeaderCreationCleanupRepair PPLLTerminalEqualSupportRepair
  PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepEchoDrain PPLLWallSweepFiniteCleanup
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
  PPLLWriteSeqRelocation PPLLWallSweepSchedule
  PPLLWriteSeqPersistenceRegression
  PPLLNoCheckBirthConditionTwoKernel

variable {n psi kappa tau : Nat}

/-! ## Exact CHECK admissibility for the wall refinement -/

/-- A pre-CHECK responder is safe from a new CHECK birth when it is already a
leader, is not at the terminal label, has no carrier or stale equality, or is
in the non-ready `depart` state.  This is the small stage-local predicate
actually needed by the shield circuit; it does not disable CHECK. -/
def CheckResponderSafe (hpsi : psi > 0) (u : AgentState psi) : Prop :=
  u.leader = true ∨
    u.label ≠ ⟨psi - 1, by omega⟩ ∨
    (u.path = .bot ∧ u.state ≠ .equal) ∨ u.state = .depart

/-- CHECK frames the responder leader bit on the exact safe shapes occurring
along a neutral absence-signal sweep. -/
theorem checkSig_responder_leader_eq_of_safe
    (hpsi : psi > 0) (l r : AgentState psi)
    (hsafe : CheckResponderSafe hpsi r) :
    (checkSig hpsi l r).2.leader = r.leader := by
  rcases hsafe with hleader | hlabel | hpath | hstate
  · exact (PPLLVerify.checkSig_responder_leader_of_true
      hpsi l r hleader).trans hleader.symm
  · by_cases hrleader : r.leader = true
    · exact (PPLLVerify.checkSig_responder_leader_of_true
        hpsi l r hrleader).trans hrleader.symm
    · have hrfalse : r.leader = false := by
        cases h : r.leader <;> simp_all
      cases hout : (checkSig hpsi l r).2.leader with
      | false => exact hrfalse.symm
      | true =>
          have hterminal :=
            PPLLVerify.checkSig_new_responder_leader_requires_terminal_equal
              hpsi l r hout hrfalse
          have hlabelEq := (PPLLVerify.checkSig_labels_eq hpsi l r).2
          exact False.elim (hlabel (hlabelEq.symm.trans hterminal.1))
  · rcases hpath with ⟨hpath, hstate⟩
    simp [checkSig, checkSigSetReady, checkSigCheckR,
      checkSigSetResult, hpath, hstate]
  · cases hpath : r.path <;>
      simp [checkSig, checkSigSetReady, checkSigCheckR,
        checkSigSetResult, hpath, hstate]

/-- Stable labels plus the exact sanitized CHECK-safe shape construct the
complete wall-edge refinement frame.  The remaining responder-zero premise is
the independent WRITE-migration obligation carried by the circuit invariant. -/
theorem WallPeaceEdgeFrame.of_aligned_check_safe
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsafe : CheckResponderSafe hpsi
      (wallSweepNormalSanitizedStage hpsi kappa l r).2.core)
    (hzero : r.core.leader = true →
      r.core.label = ⟨0, hpsi⟩) :
    WallPeaceEdgeFrame hpsi kappa l r := by
  apply WallPeaceEdgeFrame.of_aligned_check_frame
    hpsi kappa l r halign
  · change
      (checkSig hpsi
        (wallSweepNormalSanitizedStage hpsi kappa l r).1.core
        (wallSweepNormalSanitizedStage hpsi kappa l r).2.core).2.leader =
      (wallSweepNormalSanitizedStage hpsi kappa l r).2.core.leader
    exact checkSig_responder_leader_eq_of_safe hpsi _ _ hsafe
  · exact hzero

/-! ### Neutral-input producer for CHECK safety

The proof follows only the three controls that can feed CHECK: the physical
path, the comparison state, and `path2`.  It factors WAIT, GENSIG, CLEAN,
ELIMINATE_SIG, and the leader-aware SIGMOVE instead of expanding the full
agent record or enumerating finite states. -/

/-- Shape emitted by GENSIG from comparison-neutral endpoints and preserved
through CLEAN and ELIMINATE_SIG.  Either both paths remain absent or the
responder is a departing fresh terminal component; no `path2` control exists. -/
private def FreshPairShape (l r : AgentState psi) : Prop :=
  ((l.path = .bot ∧ r.path = .bot) ∨ r.state = .depart) ∧
    l.path2 = none ∧ r.path2 = none

/-- Responder shape immediately before sanitation: an existing leader, no
physical carrier, or a departing fresh component. -/
private def PreCheckResponderShape (u : AgentState psi) : Prop :=
  u.leader = true ∨ u.path = .bot ∨ u.state = .depart

private theorem pPsiLeaderProbeWall_neutral_of_aligned_neutral
    (hpsi : psi > 0)
    (l r : AgentState psi)
    (halign : r.label =
      ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hl : ComparisonNeutral l)
    (hr : ComparisonNeutral r) :
    let q := pPsiLeaderProbeWall hpsi l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 := by
  unfold pPsiLeaderProbeWall
  dsimp only
  split <;> simp_all [ComparisonNeutral, pPsi]

private theorem waitSaturated_neutral
    (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi)
    (hl : ComparisonNeutral l) (hr : ComparisonNeutral r) :
    let q := waitSaturated hpsi kappa l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 := by
  simpa [ComparisonNeutral, waitSaturated, waitSaturatedPrepare,
    waitSaturatedCarry, waitSaturatedReset, waitSaturatedFinish,
    hl, hr] using And.intro hl hr

private theorem genSigSaturatedAfterWait_responder_shape_of_neutral
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : ComparisonNeutral l) (hr : ComparisonNeutral r) :
    let q := genSigSaturatedAfterWait hpsi l r
    FreshPairShape q.1 q.2 := by
  rcases hl with ⟨hlState, hlPath, hlPath2, hlPath4, hlPath5, hlP, hlCarry⟩
  rcases hr with ⟨hrState, hrPath, hrPath2, hrPath4, hrPath5, hrP, hrCarry⟩
  by_cases hone : psi = 1
  · subst psi
    have hlzero : l.label = ⟨0, by omega⟩ := Subsingleton.elim _ _
    have hrzero : r.label = ⟨0, by omega⟩ := Subsingleton.elim _ _
    simp [FreshPairShape, genSigSaturatedAfterWait, genSigSaturatedStart,
      genSigSaturatedEmit, genSigSaturatedPropagate,
      genSigSaturatedFinish, hlState, hlPath, hrState, hrPath,
      hlPath2, hrPath2, hlzero, hrzero]
  · have hzeroNeTerminal :
        (⟨0, hpsi⟩ : Fin psi) ≠ ⟨psi - 1, by omega⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    have hpred : psi - 1 ≠ 0 := by omega
    by_cases hstart :
        l.leader = false ∧ l.label = ⟨0, hpsi⟩ ∧ l.wait = false
    · by_cases hrzero : r.label = ⟨0, hpsi⟩
      · simp [FreshPairShape, genSigSaturatedAfterWait, genSigSaturatedStart,
          genSigSaturatedEmit, genSigSaturatedPropagate,
          genSigSaturatedFinish, hlPath, hrState, hrPath,
          hlPath2, hrPath2, hstart, hrzero]
      · by_cases hrterminal : r.label = ⟨psi - 1, by omega⟩
        · simp [FreshPairShape, genSigSaturatedAfterWait, genSigSaturatedStart,
            genSigSaturatedEmit, genSigSaturatedPropagate,
            genSigSaturatedFinish, hlPath, hrPath,
            hlPath2, hrPath2, hstart, hrterminal,
            hzeroNeTerminal, hpred]
        · simp [FreshPairShape, genSigSaturatedAfterWait, genSigSaturatedStart,
            genSigSaturatedEmit, genSigSaturatedPropagate,
            genSigSaturatedFinish, hlPath, hrPath,
            hlPath2, hrPath2, hstart, hrzero, hrterminal]
    · simp [FreshPairShape, genSigSaturatedAfterWait, genSigSaturatedStart,
        genSigSaturatedEmit, genSigSaturatedPropagate,
        genSigSaturatedFinish, hlState, hlPath, hrState, hrPath,
        hlPath2, hrPath2, hstart]

private theorem genSigSaturated_responder_shape_of_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AgentState psi)
    (hl : ComparisonNeutral l)
    (hr : ComparisonNeutral r) :
    let q := genSigSaturated hpsi kappa l r
    FreshPairShape q.1 q.2 := by
  let q0 := waitSaturated hpsi kappa l r
  have hq0 := waitSaturated_neutral hpsi kappa l r hl hr
  change ComparisonNeutral q0.1 ∧ ComparisonNeutral q0.2 at hq0
  exact genSigSaturatedAfterWait_responder_shape_of_neutral
    hpsi q0.1 q0.2 hq0.1 hq0.2

private def statePair (q : AgentState psi × AgentState psi) :=
  (q.1.state, q.2.state)

private def pathPair (q : AgentState psi × AgentState psi) :=
  (q.1.path, q.2.path)

private def path2Pair (q : AgentState psi × AgentState psi) :=
  (q.1.path2, q.2.path2)

private theorem statePair_genConnect (l r : AgentState psi) :
    statePair (cleanSigGenConnect l, cleanSigGenConnect r) =
      statePair (l, r) := by
  unfold statePair cleanSigGenConnect
  repeat (first | constructor | rfl | split)

private theorem pathPair_genConnect (l r : AgentState psi) :
    pathPair (cleanSigGenConnect l, cleanSigGenConnect r) =
      pathPair (l, r) := by
  unfold pathPair cleanSigGenConnect
  repeat (first | constructor | rfl | split)

private theorem path2Pair_genConnect (l r : AgentState psi) :
    path2Pair (cleanSigGenConnect l, cleanSigGenConnect r) =
      path2Pair (l, r) := by
  unfold path2Pair cleanSigGenConnect
  repeat (first | constructor | rfl | split)

private theorem statePair_step3 (l r : AgentState psi) :
    statePair (cleanSigStep3 l r) = statePair (l, r) := by
  unfold statePair cleanSigStep3
  repeat (first | constructor | rfl | split)

private theorem pathPair_step3 (l r : AgentState psi) :
    pathPair (cleanSigStep3 l r) = pathPair (l, r) := by
  unfold pathPair cleanSigStep3
  repeat (first | constructor | rfl | split)

private theorem path2Pair_step3 (l r : AgentState psi) :
    path2Pair (cleanSigStep3 l r) = path2Pair (l, r) := by
  unfold path2Pair cleanSigStep3
  repeat (first | constructor | rfl | split)

private theorem statePair_step4 (l r : AgentState psi) :
    statePair (cleanSigStep4 l r) = statePair (l, r) := by
  unfold statePair cleanSigStep4
  repeat (first | constructor | rfl | split)

private theorem pathPair_step4 (l r : AgentState psi) :
    pathPair (cleanSigStep4 l r) = pathPair (l, r) := by
  unfold pathPair cleanSigStep4
  repeat (first | constructor | rfl | split)

private theorem path2Pair_step4 (l r : AgentState psi) :
    path2Pair (cleanSigStep4 l r) = path2Pair (l, r) := by
  unfold path2Pair cleanSigStep4
  repeat (first | constructor | rfl | split)

private theorem statePair_step5 (hpsi : psi > 0)
    (l r : AgentState psi) :
    statePair (cleanSigStep5 hpsi l r) = statePair (l, r) := by
  unfold statePair cleanSigStep5
  repeat (first | constructor | rfl | split)

private theorem pathPair_step5 (hpsi : psi > 0)
    (l r : AgentState psi) :
    pathPair (cleanSigStep5 hpsi l r) = pathPair (l, r) := by
  unfold pathPair cleanSigStep5
  repeat (first | constructor | rfl | split)

private theorem path2Pair_step5 (hpsi : psi > 0)
    (l r : AgentState psi) :
    path2Pair (cleanSigStep5 hpsi l r) = path2Pair (l, r) := by
  unfold path2Pair cleanSigStep5
  repeat (first | constructor | rfl | split)

private theorem statePair_step6 (hpsi : psi > 0)
    (l r : AgentState psi) :
    statePair (cleanSigStep6 hpsi l r) = statePair (l, r) := by
  unfold statePair cleanSigStep6
  repeat (first | constructor | rfl | split)

private theorem pathPair_step6 (hpsi : psi > 0)
    (l r : AgentState psi) :
    pathPair (cleanSigStep6 hpsi l r) = pathPair (l, r) := by
  unfold pathPair cleanSigStep6
  repeat (first | constructor | rfl | split)

private theorem path2Pair_step6 (hpsi : psi > 0)
    (l r : AgentState psi) :
    path2Pair (cleanSigStep6 hpsi l r) = path2Pair (l, r) := by
  unfold path2Pair cleanSigStep6
  repeat (first | constructor | rfl | split)

private theorem cleanApply_state (u : AgentState psi) :
    (cleanSigCleanApply u).state = u.state := by
  cases hpath : u.path with
  | bot => simp [cleanSigCleanApply, hpath]
  | some label bit =>
      cases h4 : u.path4 <;> cases h5 : u.path5 <;>
        simp [cleanSigCleanApply, hpath, h4, h5]

private theorem cleanApply_path2 (u : AgentState psi) :
    (cleanSigCleanApply u).path2 = u.path2 := by
  cases hpath : u.path with
  | bot => simp [cleanSigCleanApply, hpath]
  | some label bit =>
      cases h4 : u.path4 <;> cases h5 : u.path5 <;>
        simp [cleanSigCleanApply, hpath, h4, h5]

private theorem statePair_cleanApply (l r : AgentState psi) :
    statePair (cleanSigCleanApply l, cleanSigCleanApply r) =
      statePair (l, r) := by
  exact Prod.ext (cleanApply_state l) (cleanApply_state r)

private theorem path2Pair_cleanApply (l r : AgentState psi) :
    path2Pair (cleanSigCleanApply l, cleanSigCleanApply r) =
      path2Pair (l, r) := by
  exact Prod.ext (cleanApply_path2 l) (cleanApply_path2 r)

private theorem pathPair_cleanApply_of_bot (l r : AgentState psi)
    (hl : l.path = .bot) (hr : r.path = .bot) :
    pathPair (cleanSigCleanApply l, cleanSigCleanApply r) =
      (.bot, .bot) := by
  simp [pathPair, cleanSigCleanApply, hl, hr]

private theorem cleanSig_statePair_eq (hpsi : psi > 0)
    (l r : AgentState psi) :
    statePair (cleanSig hpsi l r) = statePair (l, r) := by
  let q0 := (cleanSigGenConnect l, cleanSigGenConnect r)
  let q1 := cleanSigStep3 q0.1 q0.2
  let q2 := cleanSigStep4 q1.1 q1.2
  let q3 := cleanSigStep5 hpsi q2.1 q2.2
  let q4 := cleanSigStep6 hpsi q3.1 q3.2
  exact (statePair_cleanApply q4.1 q4.2).trans
    ((statePair_step6 hpsi q3.1 q3.2).trans
      ((statePair_step5 hpsi q2.1 q2.2).trans
        ((statePair_step4 q1.1 q1.2).trans
          ((statePair_step3 q0.1 q0.2).trans
            (statePair_genConnect l r)))))

private theorem cleanSig_pathPair_bot (hpsi : psi > 0)
    (l r : AgentState psi) (hl : l.path = .bot) (hr : r.path = .bot) :
    pathPair (cleanSig hpsi l r) = (.bot, .bot) := by
  let q0 := (cleanSigGenConnect l, cleanSigGenConnect r)
  let q1 := cleanSigStep3 q0.1 q0.2
  let q2 := cleanSigStep4 q1.1 q1.2
  let q3 := cleanSigStep5 hpsi q2.1 q2.2
  let q4 := cleanSigStep6 hpsi q3.1 q3.2
  have hq0 : pathPair q0 = (.bot, .bot) :=
    (pathPair_genConnect l r).trans (by simp [pathPair, hl, hr])
  have hq1 : pathPair q1 = (.bot, .bot) :=
    (pathPair_step3 q0.1 q0.2).trans hq0
  have hq2 : pathPair q2 = (.bot, .bot) :=
    (pathPair_step4 q1.1 q1.2).trans hq1
  have hq3 : pathPair q3 = (.bot, .bot) :=
    (pathPair_step5 hpsi q2.1 q2.2).trans hq2
  have hq4 : pathPair q4 = (.bot, .bot) :=
    (pathPair_step6 hpsi q3.1 q3.2).trans hq3
  have hq4L := congrArg Prod.fst hq4
  have hq4R := congrArg Prod.snd hq4
  exact pathPair_cleanApply_of_bot q4.1 q4.2 hq4L hq4R

private theorem cleanSig_path2Pair_eq (hpsi : psi > 0)
    (l r : AgentState psi) :
    path2Pair (cleanSig hpsi l r) = path2Pair (l, r) := by
  let q0 := (cleanSigGenConnect l, cleanSigGenConnect r)
  let q1 := cleanSigStep3 q0.1 q0.2
  let q2 := cleanSigStep4 q1.1 q1.2
  let q3 := cleanSigStep5 hpsi q2.1 q2.2
  let q4 := cleanSigStep6 hpsi q3.1 q3.2
  exact (path2Pair_cleanApply q4.1 q4.2).trans
    ((path2Pair_step6 hpsi q3.1 q3.2).trans
      ((path2Pair_step5 hpsi q2.1 q2.2).trans
        ((path2Pair_step4 q1.1 q1.2).trans
          ((path2Pair_step3 q0.1 q0.2).trans
            (path2Pair_genConnect l r)))))

private theorem cleanSig_preserves_freshPairShape
    (hpsi : psi > 0) (l r : AgentState psi)
    (h : FreshPairShape l r) :
    let q := cleanSig hpsi l r
    FreshPairShape q.1 q.2 := by
  have hstates := cleanSig_statePair_eq hpsi l r
  have hpath2 := cleanSig_path2Pair_eq hpsi l r
  rcases h with ⟨hshape, hlp2, hrp2⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases hshape with hbot | hdepart
    · rcases hbot with ⟨hlbot, hrbot⟩
      have hpaths := cleanSig_pathPair_bot hpsi l r hlbot hrbot
      left
      exact ⟨congrArg Prod.fst hpaths, congrArg Prod.snd hpaths⟩
    · right
      exact (congrArg Prod.snd hstates).trans hdepart
  · exact (congrArg Prod.fst hpath2).trans hlp2
  · exact (congrArg Prod.snd hpath2).trans hrp2

private theorem eliminateSig_preserves_freshPairShape
    (hpsi : psi > 0) (l r : AgentState psi)
    (h : FreshPairShape l r) :
    let q := eliminateSig hpsi l r
    FreshPairShape q.1 q.2 := by
  rcases h with ⟨hshape, hlp2, hrp2⟩
  rcases hshape with hbot | hdepart
  · rcases hbot with ⟨hlbot, hrbot⟩
    simp [FreshPairShape, eliminateSig, hlbot, hrbot, hlp2, hrp2]
  · simp [FreshPairShape, eliminateSig, hdepart, hlp2, hrp2]

private theorem path2Pair_sigMoveStep1 (l r : AgentState psi) :
    path2Pair (sigMoveStep1 l r) = path2Pair (l, r) := by
  unfold path2Pair sigMoveStep1
  repeat (first | constructor | rfl | split)

private theorem sigMoveTransfers_eq_step1_of_path2_none
    (l r : AgentState psi)
    (hlp2 : l.path2 = none) (hrp2 : r.path2 = none) :
    sigMoveTransfers l r = sigMoveStep1 l r := by
  let q0 := sigMoveStep1 l r
  have hp2 := path2Pair_sigMoveStep1 l r
  have hq0L : q0.1.path2 = none :=
    (congrArg Prod.fst hp2).trans hlp2
  have hq0R : q0.2.path2 = none :=
    (congrArg Prod.snd hp2).trans hrp2
  simp [sigMoveTransfers, q0, sigMoveStep2, sigMoveStep3,
    sigMoveStep4, sigMoveStep5, hq0L, hq0R]

private theorem sigMoveStep1_responder_state_eq
    (l r : AgentState psi) :
    (sigMoveStep1 l r).2.state = r.state := by
  unfold sigMoveStep1
  repeat (first | rfl | split)

private theorem sigMoveStep1_responder_leader_eq
    (l r : AgentState psi) :
    (sigMoveStep1 l r).2.leader = r.leader := by
  unfold sigMoveStep1
  repeat (first | rfl | split)

private theorem sigMoveStep1_responder_path_bot
    (l r : AgentState psi)
    (hl : l.path = .bot) (hr : r.path = .bot) :
    (sigMoveStep1 l r).2.path = .bot := by
  simp [sigMoveStep1, hl, hr]

private theorem sigMoveLeaderWall_responder_eq_of_follower_no_controls
    (hpsi : psi > 0) (l r : AgentState psi)
    (hrleader : r.leader = false)
    (hlp2 : l.path2 = none) (hrp2 : r.path2 = none) :
    (sigMoveLeaderWall hpsi l r).2 =
      (sigMoveStep1 (sigMoveLeaderPreclear hpsi l r).1 r).2 := by
  let pre := sigMoveLeaderPreclear hpsi l r
  have hpreR : pre.2 = r := by
    simp [pre, sigMoveLeaderPreclear, clearIfLeader, hrleader]
  have hpreL2 : pre.1.path2 = none := by
    simp [pre, sigMoveLeaderPreclear, clearIfLeader,
      incompleteLeftLeaderBoundary, clearComparisonSignal,
      hrleader, hlp2]
  have hpreR2 : pre.2.path2 = none := by rw [hpreR]; exact hrp2
  let moved := sigMoveTransfers pre.1 pre.2
  have hmoved : moved = sigMoveStep1 pre.1 pre.2 :=
    sigMoveTransfers_eq_step1_of_path2_none pre.1 pre.2 hpreL2 hpreR2
  have hmovedRLeader : moved.2.leader = false := by
    rw [hmoved]
    exact (sigMoveStep1_responder_leader_eq pre.1 pre.2).trans
      (by rw [hpreR]; exact hrleader)
  have hmovedR2 : moved.2.path2 = none := by
    rw [hmoved]
    exact (congrArg Prod.snd (path2Pair_sigMoveStep1 pre.1 pre.2)).trans
      hpreR2
  let walled := comparisonLeaderWall moved.1 moved.2
  have hwalledR : walled.2 = moved.2 := by
    simp [walled, comparisonLeaderWall, hmovedRLeader]
  change (sigMoveControlTail hpsi walled.1 walled.2).2 =
    (sigMoveStep1 pre.1 r).2
  rw [hwalledR]
  have hmovedR : moved.2 = (sigMoveStep1 pre.1 r).2 := by
    rw [hmoved, hpreR]
  have hstepR2 : (sigMoveStep1 pre.1 r).2.path2 = none := by
    rw [← hmovedR]
    exact hmovedR2
  simp [sigMoveControlTail, sigMoveApplyControl, hstepR2, hmovedR]

private theorem sigMoveLeaderWall_preCheck_shape_of_fresh
    (hpsi : psi > 0) (l r : AgentState psi)
    (h : FreshPairShape l r) :
    let q := sigMoveLeaderWall hpsi l r
    PreCheckResponderShape q.2 := by
  rcases h with ⟨hshape, hlp2, hrp2⟩
  by_cases hrleader : r.leader = true
  · left
    exact (sigMoveLeaderWall_leaders_eq hpsi l r).2.trans hrleader
  · rcases hshape with hbot | hdepart
    · rcases hbot with ⟨hlbot, hrbot⟩
      right
      left
      rw [sigMoveLeaderWall_responder_eq_of_follower_no_controls
        hpsi l r (by simpa using hrleader) hlp2 hrp2]
      apply sigMoveStep1_responder_path_bot
      · simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary,
          clearComparisonSignal, hrleader, hlbot]
      · exact hrbot
    · right
      right
      rw [sigMoveLeaderWall_responder_eq_of_follower_no_controls
        hpsi l r (by simpa using hrleader) hlp2 hrp2]
      exact (sigMoveStep1_responder_state_eq
        (sigMoveLeaderPreclear hpsi l r).1 r).trans hdepart

/-- From comparison-neutral inputs on a stable edge, the entire raw wall prefix
reaches CHECK with a responder shape on which CHECK cannot create leadership. -/
private theorem wallSweepBeforeCheck_responder_shape_of_aligned_neutral
    (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi)
    (halign : r.label =
      ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hl : ComparisonNeutral l) (hr : ComparisonNeutral r) :
    let q := wallSweepBeforeCheck hpsi kappa l r
    PreCheckResponderShape q.2 := by
  let q0 := pPsiLeaderProbeWall hpsi l r
  have hq0 := pPsiLeaderProbeWall_neutral_of_aligned_neutral
    hpsi l r halign hl hr
  change ComparisonNeutral q0.1 ∧ ComparisonNeutral q0.2 at hq0
  let q1 := genSigSaturated hpsi kappa q0.1 q0.2
  have hq1 := genSigSaturated_responder_shape_of_neutral
    hpsi kappa q0.1 q0.2 hq0.1 hq0.2
  change FreshPairShape q1.1 q1.2 at hq1
  let q2 := cleanSig hpsi q1.1 q1.2
  have hq2 := cleanSig_preserves_freshPairShape
    hpsi q1.1 q1.2 hq1
  change FreshPairShape q2.1 q2.2 at hq2
  let q3 := eliminateSig hpsi q2.1 q2.2
  have hq3 := eliminateSig_preserves_freshPairShape
    hpsi q2.1 q2.2 hq2
  change FreshPairShape q3.1 q3.2 at hq3
  exact sigMoveLeaderWall_preCheck_shape_of_fresh
    hpsi q3.1 q3.2 hq3

private theorem sanitizeAuthorizedTerminalEqual_check_safe_of_shape
    (hpsi : psi > 0) (u : AuthorizedAgentState psi)
    (h : PreCheckResponderShape u.core) :
    CheckResponderSafe hpsi (sanitizeAuthorizedTerminalEqual hpsi u).core := by
  have hframe :
      (sanitizeAuthorizedTerminalEqual hpsi u).core.leader = u.core.leader ∧
      (sanitizeAuthorizedTerminalEqual hpsi u).core.label = u.core.label ∧
      (sanitizeAuthorizedTerminalEqual hpsi u).core.path = u.core.path := by
    unfold sanitizeAuthorizedTerminalEqual
    split <;> exact ⟨rfl, rfl, rfl⟩
  rcases h with hleader | hpath | hdepart
  · left
    exact hframe.1.trans hleader
  · by_cases hlabel : u.core.label = ⟨psi - 1, by omega⟩
    · right
      right
      left
      refine ⟨?_, ?_⟩
      · exact hframe.2.2.trans hpath
      · by_cases hstate : u.core.state = .equal
        · simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual,
            equalLocallySupported, hpath, hlabel, hstate]
        · simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual,
            equalLocallySupported, hpath, hlabel, hstate]
    · right
      left
      exact fun hout => hlabel (hframe.2.1.symm.trans hout)
  · right
    right
    right
    simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual,
      hdepart]

private def authorizedCorePair
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :=
  (q.1.core, q.2.core)

/- Stage-wise core pairs.  Each authorized stage has the raw stage as its
core pair; rewriting the staged prefix with these from the outside in keeps
every step a syntactic instance, instead of unfolding all five stages at once
and splitting the composed SIGMOVE guard (206 s). -/
private theorem authorizedPPsiLeaderProbeWall_corePair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedCorePair (authorizedPPsiLeaderProbeWall hpsi l r) =
      pPsiLeaderProbeWall hpsi l.core r.core :=
  rfl

private theorem authorizedGenSig_corePair
    (hpsi : psi > 0) (kappa : Nat)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedCorePair (authorizedGenSig hpsi kappa q.1 q.2) =
      genSigSaturated hpsi kappa (authorizedCorePair q).1
        (authorizedCorePair q).2 :=
  PPLLWallSweepStageFrames.authorizedReconcile_core_pair
    (genSigSaturated hpsi kappa) q.1 q.2

private theorem authorizedCleanSig_corePair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedCorePair (authorizedCleanSig hpsi q.1 q.2) =
      cleanSig hpsi (authorizedCorePair q).1 (authorizedCorePair q).2 :=
  PPLLWallSweepStageFrames.authorizedReconcile_core_pair
    (cleanSig hpsi) q.1 q.2

private theorem authorizedEliminateSig_corePair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedCorePair (authorizedEliminateSig hpsi q.1 q.2) =
      eliminateSig hpsi (authorizedCorePair q).1 (authorizedCorePair q).2 :=
  PPLLWallSweepStageFrames.authorizedReconcile_core_pair
    (eliminateSig hpsi) q.1 q.2

private theorem authorizedSigMoveLeaderWall_corePair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedCorePair (authorizedSigMoveLeaderWall hpsi q.1 q.2) =
      sigMoveLeaderWall hpsi (authorizedCorePair q).1
        (authorizedCorePair q).2 :=
  authorizedSigMoveLeaderWall_core hpsi q.1 q.2

private theorem wallSweepAuthorizedBeforeCheck_cores_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedCorePair (wallSweepAuthorizedBeforeCheck hpsi kappa l r) =
      wallSweepBeforeCheck hpsi kappa l.core r.core := by
  rw [PPLLWallSweepStageFrames.wallSweepAuthorizedBeforeCheck_stages,
    authorizedSigMoveLeaderWall_corePair, authorizedEliminateSig_corePair,
    authorizedCleanSig_corePair, authorizedGenSig_corePair,
    authorizedPPsiLeaderProbeWall_corePair]
  rfl

private theorem wallSweepAuthorizedBeforeCheck_right_core_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (wallSweepAuthorizedBeforeCheck hpsi kappa l r).2.core =
      (wallSweepBeforeCheck hpsi kappa l.core r.core).2 := by
  have h := wallSweepAuthorizedBeforeCheck_cores_eq hpsi kappa l r
  revert h
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = q
  generalize wallSweepBeforeCheck hpsi kappa l.core r.core = p
  intro h
  exact congrArg Prod.snd h

private theorem normalizeDeletion_eq_of_neutral
    (u : AuthorizedAgentState psi) (h : ComparisonNeutral u.core) :
    normalizeDeletion u = u := by
  simp [normalizeDeletion, pathPresent, h.1, h.2.1]

/-- Comparison neutrality and stable labels produce the exact CHECK-safety
premise required by `WallPeaceEdgeFrame`; no no-birth hypothesis is assumed. -/
theorem wallSweepNormalSanitizedStage_check_safe_of_aligned_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hl : ComparisonNeutral l.core) (hr : ComparisonNeutral r.core) :
    CheckResponderSafe hpsi
      (wallSweepNormalSanitizedStage hpsi kappa l r).2.core := by
  have hnl := normalizeDeletion_eq_of_neutral l hl
  have hnr := normalizeDeletion_eq_of_neutral r hr
  let before := wallSweepAuthorizedBeforeCheck hpsi kappa l r
  have hraw := wallSweepBeforeCheck_responder_shape_of_aligned_neutral
    hpsi kappa l.core r.core halign hl hr
  change PreCheckResponderShape
    (wallSweepBeforeCheck hpsi kappa l.core r.core).2 at hraw
  have hbefore : PreCheckResponderShape before.2.core := by
    exact (wallSweepAuthorizedBeforeCheck_right_core_eq
      hpsi kappa l r).symm ▸ hraw
  have hsafe := sanitizeAuthorizedTerminalEqual_check_safe_of_shape
    hpsi before.2 hbefore
  simpa [wallSweepNormalSanitizedStage,
    wallSweepNormalBeforeCheckStage, sanitizeAuthorizedPair,
    hnl, hnr, before] using hsafe

/-- On a stable edge whose two inputs are comparison-neutral, the real CHECK
frame is automatic.  Thus the full `WallPeaceEdgeFrame` requires only the
independent fact that any input responder leader is hosted at label zero. -/
theorem WallPeaceEdgeFrame.of_aligned_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hl : ComparisonNeutral l.core) (hr : ComparisonNeutral r.core)
    (hzero : r.core.leader = true →
      r.core.label = ⟨0, hpsi⟩) :
    WallPeaceEdgeFrame hpsi kappa l r := by
  exact WallPeaceEdgeFrame.of_aligned_check_safe hpsi kappa l r halign
    (wallSweepNormalSanitizedStage_check_safe_of_aligned_neutral
      hpsi kappa l r halign hl hr) hzero

/-! ### First full-wall edge: leader seed and neutral reset handoff -/

private theorem suppressSigResetKill_leader_seed_neutral
    (hpsi : psi > 0) (l r : AgentState psi)
    (hleader : l.leader = true) :
    let q := suppressSigResetKill hpsi l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, ComparisonNeutral,
    suppressSigTerminal, suppressSigEcho, suppressSigFinish,
    hleader]

private theorem deletionPriorityExpireOne_neutral
    (old out : ExpiringAgentState psi kappa tau)
    (hneutral : ComparisonNeutral out.core.erase.core) :
    ComparisonNeutral
      (deletionPriorityExpireOne tau old out).core.erase.core := by
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

private theorem afterSuppress_leader_seed_handoff_of_eq
    (hpsi : psi > 0)
    {pre after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hpreLeader : pre.1.core.leader = true)
    (hpreEcho : pre.2.core.echo = false)
    (hout : after = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2) :
    ComparisonNeutral after.1.core ∧ ComparisonNeutral after.2.core ∧
      after.1.core.echo = false ∧ after.2.core.echo = false ∧
      after.2.core.reset_cmd = true := by
  have hneutral := suppressSigResetKill_leader_seed_neutral
    hpsi pre.1.core pre.2.core hpreLeader
  have hseed := suppressSigResetKill_leader_reseed
    hpsi pre.1.core pre.2.core hpreLeader hpreEcho
  rw [hout]
  exact ⟨hneutral.1, hneutral.2, hseed.1, hseed.2.1, hseed.2.2⟩

private theorem postSuppress_leader_seed_handoff_of_eq
    (hpsi : psi > 0)
    {after post : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hafter : ComparisonNeutral after.1.core ∧
      ComparisonNeutral after.2.core ∧
      after.1.core.echo = false ∧ after.2.core.echo = false ∧
      after.2.core.reset_cmd = true)
    (hout : post = authorizedPostSuppress hpsi after.1 after.2) :
    ComparisonNeutral post.1.core ∧ ComparisonNeutral post.2.core ∧
      post.1.core.echo = false ∧ post.2.core.echo = false ∧
      post.2.core.reset_cmd = true := by
  have hpost := postSuppress_normalReset_handoff
    hpsi after.1 after.2 hafter.1 hafter.2.1
  rw [hout]
  exact ⟨hpost.1, hpost.2.1,
    hpost.2.2.2.2.1.trans hafter.2.2.1,
    hpost.2.2.2.2.2.trans hafter.2.2.2.1,
    hpost.2.2.2.1.trans hafter.2.2.2.2⟩

private theorem initiator_leader_of_peaceViewPair_eq
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hview : authorizedPeaceViewPair after =
      authorizedPeaceViewPair before)
    (hleader : before.1.core.leader = true) :
    after.1.core.leader = true := by
  have hleft := congrArg Prod.fst hview
  exact (congrArg PeaceView.leader hleft).trans hleader

private theorem responder_echo_false_of_resetEchoPair_eq
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hview : authorizedResetEchoPair after =
      authorizedResetEchoPair before)
    (hecho : before.2.core.echo = false) :
    after.2.core.echo = false := by
  have hright := congrArg Prod.snd hview
  have heq := congrArg Prod.snd hright
  change after.2.core.echo = before.2.core.echo at heq
  exact heq.trans hecho

/-- An admissible neutral edge initiated by the unshielded leader already has
enough structure to seed the reset sweep.  Repaired Algorithm 14 clears both
comparison carriers, consumes both echoes, and places reset on the responder;
Algorithm 15 and gated WRITE preserve that handoff. -/
theorem wallSweepAuthorizedNormalTail_leader_seed_handoff
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hframe : WallPeaceEdgeFrame hpsi kappa l r)
    (hleader : l.core.leader = true)
    (hrEcho : r.core.echo = false) :
    let tail := wallSweepAuthorizedNormalTail hpsi kappa l r
    ComparisonNeutral tail.1.core ∧ ComparisonNeutral tail.2.core ∧
      tail.1.core.echo = false ∧ tail.2.core.echo = false ∧
      tail.2.core.reset_cmd = true := by
  let pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r
  have hview := wallSweepAuthorizedNormalBeforeSuppress_peaceView_of_frame
    hpsi kappa l r hframe
  have hpreLeader : pre.1.core.leader = true :=
    initiator_leader_of_peaceViewPair_eq hview hleader
  have hresetEcho := wallSweepAuthorizedNormalBeforeSuppress_resetEchoPair
    hpsi kappa l r
  have hpreEcho : pre.2.core.echo = false :=
    responder_echo_false_of_resetEchoPair_eq hresetEcho hrEcho
  let after := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  have hafterEq := wallSweepAuthorizedNormalAfterSuppress_eq_reconcile
    hpsi kappa l r
  change after = authorizedReconcile
    (suppressSigResetKill hpsi) pre.1 pre.2 at hafterEq
  have hafter := afterSuppress_leader_seed_handoff_of_eq
    hpsi hpreLeader hpreEcho hafterEq
  have htailEq := wallSweepAuthorizedNormalTail_eq_postSuppress
    hpsi kappa l r
  change wallSweepAuthorizedNormalTail hpsi kappa l r =
    authorizedPostSuppress hpsi after.1 after.2 at htailEq
  exact postSuppress_leader_seed_handoff_of_eq hpsi hafter htailEq

/-- Birth marking is inert on the neutral leader-seed output, so the complete
priority-open authorized transition realizes the same reset handoff. -/
theorem wallSweepAuthorized_priority_open_leader_seed_handoff
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l r)
    (hleader : l.core.leader = true)
    (hrEcho : r.core.echo = false) :
    let q := wallSweepAuthorizedTransition hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.core.echo = false ∧ q.2.core.echo = false ∧
      q.2.core.reset_cmd = true := by
  have htail := wallSweepAuthorizedNormalTail_leader_seed_handoff
    hpsi kappa l r hframe hleader hrEcho
  have heq := wallSweepAuthorizedTransition_eq_normalTail_of_priority_open
    hpsi kappa l r hopen htail.1 htail.2.1
  rw [heq]
  exact htail

/-- The leader-seed handoff survives bounded reification and path-stall
expiry.  This is the first actual complete-wall edge of the shield circuit. -/
theorem wallSweepPathStall_priority_open_leader_seed_handoff
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l.core.erase r.core.erase)
    (hleader : l.core.erase.core.leader = true)
    (hrEcho : r.core.erase.core.echo = false) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    ComparisonNeutral q.1.core.erase.core ∧
      ComparisonNeutral q.2.core.erase.core ∧
      q.1.core.erase.core.echo = false ∧
      q.2.core.erase.core.echo = false ∧
      q.2.core.erase.core.reset_cmd = true := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hauth := wallSweepAuthorized_priority_open_leader_seed_handoff
    hpsi kappa l.core.erase r.core.erase hopen hframe hleader hrEcho
  have herase := erase_wallSweepBoundedTransition hpsi kappa l.core r.core
  have hleft := congrArg Prod.fst herase
  have hright := congrArg Prod.snd herase
  change bounded.1.erase =
    (wallSweepAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hleft
  change bounded.2.erase =
    (wallSweepAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hright
  have hLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hleft]
    exact hauth.1
  have hRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hright]
    exact hauth.2.1
  have hLEcho : lBase.core.erase.core.echo = false := by
    change bounded.1.erase.core.echo = false
    rw [hleft]
    exact hauth.2.2.1
  have hREcho : rBase.core.erase.core.echo = false := by
    change bounded.2.erase.core.echo = false
    rw [hright]
    exact hauth.2.2.2.1
  have hRReset : rBase.core.erase.core.reset_cmd = true := by
    change bounded.2.erase.core.reset_cmd = true
    rw [hright]
    exact hauth.2.2.2.2
  have hLn := deletionPriorityExpireOne_neutral l lBase hLNeutral
  have hRn := deletionPriorityExpireOne_neutral r rBase hRNeutral
  have hLf := deletionPriorityExpireOne_path_frame l lBase
  have hRf := deletionPriorityExpireOne_path_frame r rBase
  change
    ComparisonNeutral (deletionPriorityExpireOne tau l lBase).core.erase.core ∧
      ComparisonNeutral (deletionPriorityExpireOne tau r rBase).core.erase.core ∧
      (deletionPriorityExpireOne tau l lBase).core.erase.core.echo = false ∧
      (deletionPriorityExpireOne tau r rBase).core.erase.core.echo = false ∧
      (deletionPriorityExpireOne tau r rBase).core.erase.core.reset_cmd = true
  exact ⟨hLn, hRn,
    hLf.2.2.2.2.1.trans hLEcho,
    hRf.2.2.2.2.1.trans hREcho,
    hRf.2.2.2.1.trans hRReset⟩

private theorem afterSuppress_leader_neutral_of_eq
    (hpsi : psi > 0)
    {pre after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hpreLeader : pre.1.core.leader = true)
    (hout : after = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2) :
    ComparisonNeutral after.1.core ∧ ComparisonNeutral after.2.core := by
  have hneutral := suppressSigResetKill_leader_seed_neutral
    hpsi pre.1.core pre.2.core hpreLeader
  rw [hout]
  exact hneutral

private theorem postSuppress_neutral_of_eq
    (hpsi : psi > 0)
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hbefore : ComparisonNeutral before.1.core ∧
      ComparisonNeutral before.2.core)
    (hout : after = authorizedPostSuppress hpsi before.1 before.2) :
    ComparisonNeutral after.1.core ∧ ComparisonNeutral after.2.core := by
  have hpost := postSuppress_normalReset_handoff
    hpsi before.1 before.2 hbefore.1 hbefore.2
  rw [hout]
  exact ⟨hpost.1, hpost.2.1⟩

/-- A priority-open full-wall call initiated by a leader has neutral comparison
output even when the responder echo cancels the reset token. -/
theorem wallSweepAuthorized_priority_open_leader_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l r)
    (hleader : l.core.leader = true) :
    let q := wallSweepAuthorizedTransition hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core := by
  let pre := wallSweepAuthorizedNormalBeforeSuppress hpsi kappa l r
  have hview := wallSweepAuthorizedNormalBeforeSuppress_peaceView_of_frame
    hpsi kappa l r hframe
  have hpreLeader : pre.1.core.leader = true :=
    initiator_leader_of_peaceViewPair_eq hview hleader
  let after := wallSweepAuthorizedNormalAfterSuppress hpsi kappa l r
  have hafterEq := wallSweepAuthorizedNormalAfterSuppress_eq_reconcile
    hpsi kappa l r
  change after = authorizedReconcile
    (suppressSigResetKill hpsi) pre.1 pre.2 at hafterEq
  have hafter := afterSuppress_leader_neutral_of_eq
    hpsi hpreLeader hafterEq
  let tail := wallSweepAuthorizedNormalTail hpsi kappa l r
  have htailEq := wallSweepAuthorizedNormalTail_eq_postSuppress
    hpsi kappa l r
  change tail = authorizedPostSuppress hpsi after.1 after.2 at htailEq
  have htail := postSuppress_neutral_of_eq hpsi hafter htailEq
  have hout := wallSweepAuthorizedTransition_eq_normalTail_of_priority_open
    hpsi kappa l r hopen htail.1 htail.2
  rw [hout]
  exact htail

/-- Bounded reification and expiry preserve the neutral leader-edge output. -/
theorem wallSweepPathStall_priority_open_leader_neutral
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l.core.erase r.core.erase)
    (hleader : l.core.erase.core.leader = true) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    ComparisonNeutral q.1.core.erase.core ∧
      ComparisonNeutral q.2.core.erase.core := by
  let bounded := wallSweepBoundedTransition hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hauth := wallSweepAuthorized_priority_open_leader_neutral
    hpsi kappa l.core.erase r.core.erase hopen hframe hleader
  have herase := erase_wallSweepBoundedTransition hpsi kappa l.core r.core
  have hleft := congrArg Prod.fst herase
  have hright := congrArg Prod.snd herase
  change bounded.1.erase =
    (wallSweepAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hleft
  change bounded.2.erase =
    (wallSweepAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hright
  have hLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hleft]
    exact hauth.1
  have hRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hright]
    exact hauth.2
  change
    ComparisonNeutral (deletionPriorityExpireOne tau l lBase).core.erase.core ∧
      ComparisonNeutral (deletionPriorityExpireOne tau r rBase).core.erase.core
  exact ⟨deletionPriorityExpireOne_neutral l lBase hLNeutral,
    deletionPriorityExpireOne_neutral r rBase hRNeutral⟩

/-- The final returned-signal edge both establishes the protected anchor and
leaves its two comparison endpoints neutral. -/
theorem wallSweepPathStall_priority_open_leader_fire_neutral_anchor
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hframe : WallPeaceEdgeFrame hpsi kappa l.core.erase r.core.erase)
    (hleader : l.core.erase.core.leader = true)
    (hlabel : l.core.erase.core.label = ⟨0, hpsi⟩)
    (hsignal : l.core.erase.core.signal_B = ⟨1, by omega⟩) :
    let q := wallSweepPathStallTransition hpsi kappa tau l r
    ComparisonNeutral q.1.core.erase.core ∧
      ComparisonNeutral q.2.core.erase.core ∧
      q.1.core.erase.core.leader = true ∧
      q.1.core.erase.core.shield = true ∧
      q.1.core.erase.core.label = ⟨0, hpsi⟩ ∧
      q.1.core.erase.core.signal_B = ⟨0, by omega⟩ := by
  have hneutral := wallSweepPathStall_priority_open_leader_neutral
    hpsi l r hopen hframe hleader
  have hanchor := wallSweepPathStall_priority_open_leader_fire_anchor
    hpsi l r hopen hframe hleader hlabel hsignal
  exact ⟨hneutral.1, hneutral.2, hanchor.1, hanchor.2.1,
    hanchor.2.2.1, hanchor.2.2.2⟩

/-- State after `steps` clockwise propagation edges.  Positive offsets already
visited carry the signal, offsets strictly ahead are zero, and the leader
receives the signal exactly after the full revolution. -/
structure ShieldPropagationState (hpsi : psi > 0)
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → AgentState psi) (steps : Nat) : Prop where
  steps_le : steps ≤ n
  stable_labels : ∀ i,
    (C (ring.rightNeighbor i)).label =
      ⟨((C i).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  leader_alive : (C leader).leader = true
  leader_zero : (C leader).label = ⟨0, hpsi⟩
  unique_leader : ∀ i, i ≠ leader → (C i).leader = false
  bullets_zero : ∀ i, (C i).bullet = ⟨0, by omega⟩
  visited_signal : ∀ k, 0 < k → k ≤ steps → k < n →
    (C (groupOffset ring leader k)).signal_B = ⟨1, by omega⟩
  ahead_zero : ∀ k, steps < k → k < n →
    (C (groupOffset ring leader k)).signal_B = ⟨0, by omega⟩
  leader_signal_zero : steps < n →
    (C leader).signal_B = ⟨0, by omega⟩
  leader_signal_one : steps = n →
    (C leader).signal_B = ⟨1, by omega⟩

theorem shieldPropagationState_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → AgentState psi)
    (hstable : ∀ i,
      (C (ring.rightNeighbor i)).label =
        ⟨((C i).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hleader : (C leader).leader = true)
    (hzero : (C leader).label = ⟨0, hpsi⟩)
    (hunique : ∀ i, i ≠ leader → (C i).leader = false)
    (hbullets : ∀ i, (C i).bullet = ⟨0, by omega⟩)
    (hsignals : ∀ i, (C i).signal_B = ⟨0, by omega⟩) :
    ShieldPropagationState hpsi ring leader C 0 := by
  refine ⟨by omega, hstable, hleader, hzero, hunique, hbullets,
    ?_, ?_, ?_, ?_⟩
  · intro k hk
    omega
  · intro k _ hk
    exact hsignals _
  · intro _
    exact hsignals leader
  · intro h
    have hn := ring.hn
    omega

private theorem groupOffset_zero_eq
    (ring : DirectedRing n) (leader : Fin n) :
    groupOffset ring leader 0 = leader := by
  apply Fin.ext
  simp [groupOffset, Nat.mod_eq_of_lt leader.isLt]

private theorem groupOffset_n_eq
    (ring : DirectedRing n) (leader : Fin n) :
    groupOffset ring leader n = leader := by
  apply Fin.ext
  simp [groupOffset, Nat.add_mod_right, Nat.mod_eq_of_lt leader.isLt]

/-! ## One isolated propagation edge -/

theorem ShieldPropagationState.step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → AgentState psi) (steps : Nat)
    (hstate : ShieldPropagationState hpsi ring leader C steps)
    (hnext : steps + 1 ≤ n) :
    let e := groupOffset ring leader steps
    let D := localStep ring (eliminateLeadersNoCollision hpsi) C e
    ShieldPropagationState hpsi ring leader D (steps + 1) := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  have hsteps : steps < n := by omega
  have heBound : steps < n := hsteps
  have hneighbor : ring.rightNeighbor e = j := by
    exact rightNeighbor_groupOffset ring leader steps
  have hene : e ≠ j := by
    rw [← hneighbor]
    exact Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn e)
  have heLeader : steps = 0 → e = leader := by
    intro hs
    subst steps
    apply Fin.ext
    simp [e, groupOffset, Nat.mod_eq_of_lt leader.isLt]
  have heNotLeader : 0 < steps → e ≠ leader := by
    intro hs
    intro heq
    have hne := groupOffset_ne_of_lt ring leader hsteps
      (by omega : 0 < n) (by omega : steps ≠ 0)
    exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjLeader : steps + 1 = n → j = leader := by
    intro hs
    change groupOffset ring leader (steps + 1) = leader
    rw [hs]
    exact groupOffset_n_eq ring leader
  have hjBound : steps + 1 < n → steps + 1 < n := fun h => h
  have hsource : (C e).leader = true ∨
      (C e).signal_B = ⟨1, by omega⟩ := by
    by_cases hs : steps = 0
    · left
      rw [heLeader hs]
      exact hstate.leader_alive
    · right
      exact hstate.visited_signal steps (by omega) (by omega) hsteps
  have hjSignal : (C j).signal_B = ⟨0, by omega⟩ := by
    by_cases hlast : steps + 1 = n
    · rw [hjLeader hlast]
      exact hstate.leader_signal_zero hsteps
    · exact hstate.ahead_zero (steps + 1) (by omega) (by omega)
  have hnoFire : (C e).leader = false ∨
      (C e).signal_B = ⟨0, by omega⟩ := by
    by_cases hs : steps = 0
    · right
      rw [heLeader hs]
      exact hstate.leader_signal_zero hsteps
    · left
      exact hstate.unique_leader e (heNotLeader (by omega))
  have hlocal := noCollision_idle_propagation_frame hpsi
    (C e) (C j) hnoFire (hstate.bullets_zero e)
      (hstate.bullets_zero j) hjSignal
  have hprop := noCollision_right_signal_one_of_aligned_source hpsi
    (C e) (C j) (by simpa [hneighbor] using hstate.stable_labels e)
      (hstate.bullets_zero j) hjSignal hsource
  let q := eliminateLeadersNoCollision hpsi (C e) (C j)
  let D := localStep ring (eliminateLeadersNoCollision hpsi) C e
  have hleft : D e = q.1 := by
    simp [D, q, localStep, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, localStep, hneighbor, Ne.symm hene]
  rcases hlocal with ⟨hLL, hRL, hLLabel, hRLabel, hLS, hRS,
    hLB, hRB, hLSignal⟩
  have hleaderAt : ∀ i, (D i).leader = (C i).leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hLL
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hRL
      · simp [D, localStep, hie, hneighbor, hij]
  have hlabelAt : ∀ i, (D i).label = (C i).label := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hLLabel
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hRLabel
      · simp [D, localStep, hie, hneighbor, hij]
  have hbulletAt : ∀ i, (D i).bullet = ⟨0, by omega⟩ := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hLB
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hRB
      · have hsame : D i = C i := by
          simp [D, localStep, hie, hneighbor, hij]
        rw [hsame]
        exact hstate.bullets_zero i
  have hsignalOther : ∀ i, i ≠ j → (D i).signal_B = (C i).signal_B := by
    intro i hij
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hLSignal
    · simp [D, localStep, hie, hneighbor, hij]
  refine ⟨hnext, ?_, ?_, ?_, ?_, hbulletAt, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hlabelAt, hlabelAt]
    exact hstate.stable_labels i
  · rw [hleaderAt]
    exact hstate.leader_alive
  · rw [hlabelAt]
    exact hstate.leader_zero
  · intro i hi
    rw [hleaderAt]
    exact hstate.unique_leader i hi
  · intro k hkPos hkVisited hkBound
    by_cases hk : k = steps + 1
    · subst k
      change (D j).signal_B = ⟨1, by omega⟩
      rw [hright]
      exact hprop
    · have hkj : groupOffset ring leader k ≠ j := by
        by_cases hlast : steps + 1 = n
        · rw [hjLeader hlast]
          have hne := groupOffset_ne_of_lt ring leader hkBound
            (by omega : 0 < n) (by omega : k ≠ 0)
          exact fun heq => hne
            (heq.trans (groupOffset_zero_eq ring leader).symm)
        · apply groupOffset_ne_of_lt ring leader hkBound
            (by omega : steps + 1 < n)
          exact hk
      rw [hsignalOther _ hkj]
      exact hstate.visited_signal k hkPos (by omega) hkBound
  · intro k hkAhead hkBound
    have hkj : groupOffset ring leader k ≠ j := by
      apply groupOffset_ne_of_lt ring leader hkBound
        (by omega : steps + 1 < n)
      omega
    rw [hsignalOther _ hkj]
    exact hstate.ahead_zero k (by omega) hkBound
  · intro hbefore
    have hjNotLeader : j ≠ leader := by
      have hjn := groupOffset_ne_of_lt ring leader
        (by omega : steps + 1 < n) (by omega : 0 < n)
        (by omega : steps + 1 ≠ 0)
      exact fun hj => hjn (hj.trans (groupOffset_zero_eq ring leader).symm)
    rw [hsignalOther leader (Ne.symm hjNotLeader)]
    exact hstate.leader_signal_zero hsteps
  · intro hdone
    have hjEq : j = leader := hjLeader hdone
    change (D leader).signal_B = ⟨1, by omega⟩
    rw [← hjEq, hright]
    exact hprop

private theorem runLocalSchedule_append
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (a b : DetSchedule n) :
    runLocalSchedule ring T C (a ++ b) =
      runLocalSchedule ring T (runLocalSchedule ring T C a) b := by
  induction a generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih _

theorem shieldPropagationSchedule_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → AgentState psi)
    (hstable : ∀ i,
      (C (ring.rightNeighbor i)).label =
        ⟨((C i).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hleader : (C leader).leader = true)
    (hzero : (C leader).label = ⟨0, hpsi⟩)
    (hunique : ∀ i, i ≠ leader → (C i).leader = false)
    (hbullets : ∀ i, (C i).bullet = ⟨0, by omega⟩)
    (hsignals : ∀ i, (C i).signal_B = ⟨0, by omega⟩)
    (steps : Nat) (hsteps : steps ≤ n) :
    let D := runLocalSchedule ring (eliminateLeadersNoCollision hpsi) C
      (resetSweepSchedule ring leader steps)
    ShieldPropagationState hpsi ring leader D steps := by
  induction steps with
  | zero =>
      exact shieldPropagationState_zero hpsi ring leader C hstable
        hleader hzero hunique hbullets hsignals
  | succ steps ih =>
      have hprev : steps ≤ n := by omega
      let C0 := runLocalSchedule ring (eliminateLeadersNoCollision hpsi) C
        (resetSweepSchedule ring leader steps)
      have hstate : ShieldPropagationState hpsi ring leader C0 steps :=
        ih hprev
      have hstep := hstate.step hpsi ring hn leader C0 steps hsteps
      rw [resetSweepSchedule, runLocalSchedule_append]
      exact hstep

/-- The clockwise kernel circuit returns the absence signal to the leader and
the final leader edge installs its shield. -/
theorem shieldCircuit_establishes_anchor
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → AgentState psi)
    (hstable : ∀ i,
      (C (ring.rightNeighbor i)).label =
        ⟨((C i).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hleader : (C leader).leader = true)
    (hzero : (C leader).label = ⟨0, hpsi⟩)
    (hunique : ∀ i, i ≠ leader → (C i).leader = false)
    (hbullets : ∀ i, (C i).bullet = ⟨0, by omega⟩)
    (hsignals : ∀ i, (C i).signal_B = ⟨0, by omega⟩) :
    let word := resetSweepSchedule ring leader n ++ [leader]
    let D := runLocalSchedule ring (eliminateLeadersNoCollision hpsi) C word
    (D leader).leader = true ∧ (D leader).shield = true ∧
      (D leader).label = ⟨0, hpsi⟩ ∧
      (D leader).signal_B = ⟨0, by omega⟩ := by
  let C0 := runLocalSchedule ring (eliminateLeadersNoCollision hpsi) C
    (resetSweepSchedule ring leader n)
  have hstate := shieldPropagationSchedule_reaches hpsi ring hn leader C
    hstable hleader hzero hunique hbullets hsignals n (by omega)
  change ShieldPropagationState hpsi ring leader C0 n at hstate
  have hsignal := hstate.leader_signal_one rfl
  let q := eliminateLeadersNoCollision hpsi (C0 leader)
    (C0 (ring.rightNeighbor leader))
  have hfireLeader := noCollision_left_fire_leader hpsi
    (C0 leader) (C0 (ring.rightNeighbor leader))
    hstate.leader_alive hsignal
  have hfireFields := noCollision_left_fire_fields hpsi
    (C0 leader) (C0 (ring.rightNeighbor leader))
    hstate.leader_alive hsignal
  have hlabel := (noCollision_labels hpsi
    (C0 leader) (C0 (ring.rightNeighbor leader))).1.trans hstate.leader_zero
  dsimp only
  rw [runLocalSchedule_append]
  change
    (localStep ring (eliminateLeadersNoCollision hpsi) C0 leader leader).leader =
      true ∧
    (localStep ring (eliminateLeadersNoCollision hpsi) C0 leader leader).shield =
      true ∧
    (localStep ring (eliminateLeadersNoCollision hpsi) C0 leader leader).label =
      ⟨0, hpsi⟩ ∧
    (localStep ring (eliminateLeadersNoCollision hpsi) C0 leader leader).signal_B =
      ⟨0, by omega⟩
  have hleft : localStep ring (eliminateLeadersNoCollision hpsi)
      C0 leader leader = q.1 := by
    simp [q, localStep]
  rw [hleft]
  exact ⟨hfireLeader, hfireFields.1, hlabel, hfireFields.2⟩

end PPLLWallSweepShieldCircuit

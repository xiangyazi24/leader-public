import Leader.Wu.Safety.NoCheckBirthLeaderFrames
import Leader.Wu.Safety.SignalCoherence

/-!
# Physical boundary frames for corrected condition 1

Only P'_ψ changes labels. This file proves that saturated WAIT/GENSIG and every
later pre-Algorithm-15 stage frame both labels, then uses OutputSafe's
no-free-barrier and unique label-zero leader facts to recover the responder
label. A second structural pass shows that the same prefix preserves exactly
the initiator shield and responder bullet inspected by ELIMINATE_LEADERS.
Together these are the physical boundary facts needed for old-leader survival.
-/

namespace PPLLNoCheckBirthBoundaryFrames

open PPLL PPLLRepair PPLLVerify PPLLNoCheckBirthLeaderFrames

/-- Pair projection for label-frame composition. -/
def labelPair (q : AgentState ψ × AgentState ψ) : Fin ψ × Fin ψ :=
  (q.1.label, q.2.label)

private theorem labelPair_eq_of_fields
    {q : AgentState ψ × AgentState ψ} {l r : AgentState ψ}
    (h : q.1.label = l.label ∧ q.2.label = r.label) :
    labelPair q = labelPair (l, r) :=
  Prod.ext h.1 h.2

private theorem waitSaturatedPrepare_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (waitSaturatedPrepare hψ l r) = (l.label, r.label) := by
  unfold labelPair waitSaturatedPrepare
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedCarry_labels
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    labelPair (waitSaturatedCarry hψ κ l r) = (l.label, r.label) := by
  unfold labelPair waitSaturatedCarry satCountSucc
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedReset_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (waitSaturatedReset hψ l r) = (l.label, r.label) := by
  unfold labelPair waitSaturatedReset
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedFinish_labels
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    labelPair (waitSaturatedFinish hψ κ l r) = (l.label, r.label) := by
  simp [labelPair, waitSaturatedFinish]

private theorem waitSaturated_labels
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    labelPair (waitSaturated hψ κ l r) = (l.label, r.label) := by
  let q0 := waitSaturatedPrepare hψ l r
  let q1 := waitSaturatedCarry hψ κ q0.1 q0.2
  let q2 := waitSaturatedReset hψ q1.1 q1.2
  calc
    labelPair (waitSaturated hψ κ l r) = labelPair q2 :=
      waitSaturatedFinish_labels hψ κ q2.1 q2.2
    _ = labelPair q1 := waitSaturatedReset_labels hψ q1.1 q1.2
    _ = labelPair q0 := waitSaturatedCarry_labels hψ κ q0.1 q0.2
    _ = (l.label, r.label) := waitSaturatedPrepare_labels hψ l r

private theorem genSigSaturatedStart_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (genSigSaturatedStart hψ l r) = (l.label, r.label) := by
  simp [labelPair, genSigSaturatedStart]

private theorem genSigSaturatedEmit_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (genSigSaturatedEmit hψ l r) = (l.label, r.label) := by
  simp [labelPair, genSigSaturatedEmit]

private theorem genSigSaturatedPropagate_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (genSigSaturatedPropagate hψ l r) = (l.label, r.label) := by
  simp [labelPair, genSigSaturatedPropagate]

private theorem genSigSaturatedFinish_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (genSigSaturatedFinish hψ l r) = (l.label, r.label) := by
  simp [labelPair, genSigSaturatedFinish]

private theorem genSigSaturatedAfterWait_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (genSigSaturatedAfterWait hψ l r) = (l.label, r.label) := by
  let q0 := genSigSaturatedStart hψ l r
  let q1 := genSigSaturatedEmit hψ q0.1 q0.2
  let q2 := genSigSaturatedPropagate hψ q1.1 q1.2
  calc
    labelPair (genSigSaturatedAfterWait hψ l r) = labelPair q2 :=
      genSigSaturatedFinish_labels hψ q2.1 q2.2
    _ = labelPair q1 := genSigSaturatedPropagate_labels hψ q1.1 q1.2
    _ = labelPair q0 := genSigSaturatedEmit_labels hψ q0.1 q0.2
    _ = (l.label, r.label) := genSigSaturatedStart_labels hψ l r

/-- Saturated GENSIG frames both labels. -/
theorem genSigSaturated_labels
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    labelPair (genSigSaturated hψ κ l r) = (l.label, r.label) := by
  let q := waitSaturated hψ κ l r
  calc
    labelPair (genSigSaturated hψ κ l r) = labelPair q :=
      genSigSaturatedAfterWait_labels hψ q.1 q.2
    _ = (l.label, r.label) := waitSaturated_labels hψ κ l r

private theorem noCheckBirthCoreAfterPPsi_labels
    (hψ : ψ > 0) (κ : Nat) (q0 : AgentState ψ × AgentState ψ) :
    labelPair (noCheckBirthCoreAfterPPsi hψ κ q0) = labelPair q0 := by
  let q1 := genSigSaturated hψ κ q0.1 q0.2
  let q2 := cleanSig hψ q1.1 q1.2
  let q3 := eliminateSig hψ q2.1 q2.2
  have hsig := labelPair_eq_of_fields (sigMove_labels_eq hψ q3.1 q3.2)
  have helim := labelPair_eq_of_fields (eliminateSig_labels_eq hψ q2.1 q2.2)
  have hclean := labelPair_eq_of_fields (cleanSig_labels_eq hψ q1.1 q1.2)
  have hgen := genSigSaturated_labels hψ κ q0.1 q0.2
  change labelPair (sigMove hψ q3.1 q3.2) = labelPair q0
  exact hsig.trans (helim.trans (hclean.trans hgen))

/-- The explicit pre-CHECK prefix frames exactly P'_ψ's label pair. -/
theorem noCheckBirthCoreBeforeCheck_labels
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    labelPair (noCheckBirthCoreBeforeCheck hψ κ l r) =
      labelPair (pPsi hψ l r) :=
  noCheckBirthCoreAfterPPsi_labels hψ κ (pPsi hψ l r)

private theorem checkSigNoBirthCore_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (checkSigNoBirthCore hψ l r) = (l.label, r.label) := by
  have h := checkSig_labels_eq hψ l r
  exact Prod.ext h.1 h.2

private theorem cmpUpdatePropagate_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (cmpUpdatePropagate hψ l r) = (l.label, r.label) := by
  unfold labelPair cmpUpdatePropagate
  repeat (first | constructor | rfl | split)

private theorem cmpUpdateSetPath2_label_eq
    (hψ : ψ > 0) (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).label = l.label := by
  unfold cmpUpdateSetPath2
  repeat (first | rfl | split)

private theorem cmpUpdateNoSourceRearm_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (cmpUpdateNoSourceRearm hψ l r) = (l.label, r.label) := by
  let l0 := if l.label = ⟨0, hψ⟩ ∧ l.state ≠ .depart then
    { l with state := .congest } else l
  let q := cmpUpdatePropagate hψ l0 r
  have hl0 : l0.label = l.label := by dsimp [l0]; split <;> rfl
  have hq := cmpUpdatePropagate_labels hψ l0 r
  have hql : q.1.label = l0.label := congrArg Prod.fst hq
  have hqr : q.2.label = r.label := congrArg Prod.snd hq
  change labelPair (cmpUpdateSetPath2 hψ q.1, q.2) = (l.label, r.label)
  unfold labelPair
  rw [cmpUpdateSetPath2_label_eq, hql, hqr, hl0]

private theorem compareSigInit_label_eq (l : AgentState ψ) :
    (compareSigInit l).label = l.label := by
  unfold compareSigInit
  split <;> rfl

private theorem compareSigNoSourceRearm_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    labelPair (compareSigNoSourceRearm hψ l r) = (l.label, r.label) := by
  unfold compareSigNoSourceRearm
  dsimp only
  split
  · exact Prod.ext (compareSigInit_label_eq l) rfl
  · split
    · let l0 := compareSigInit l
      let q := cmpUpdateNoSourceRearm hψ l0 r
      have hcmp := cmpUpdateNoSourceRearm_labels hψ l0 r
      have hdispatch := labelPair_eq_of_fields
        (compareSigDispatch_labels_eq hψ q.1 q.2)
      have hinit : labelPair (l0, r) = (l.label, r.label) :=
        Prod.ext (compareSigInit_label_eq l) rfl
      exact hdispatch.trans (hcmp.trans hinit)
    · exact Prod.ext (compareSigInit_label_eq l) rfl

private theorem noCheckBirthCoreAfterBeforeCheck_labels
    (hψ : ψ > 0) (q0 : AgentState ψ × AgentState ψ) :
    labelPair (noCheckBirthCoreAfterBeforeCheck hψ q0) = labelPair q0 := by
  let q1 := checkSigNoBirthCore hψ q0.1 q0.2
  let q2 := disappear hψ q1.1 q1.2
  let q3 := compareSigNoSourceRearm hψ q2.1 q2.2
  have h1 := checkSigNoBirthCore_labels hψ q0.1 q0.2
  have h2 := labelPair_eq_of_fields (disappear_labels_eq hψ q1.1 q1.2)
  have h3 := compareSigNoSourceRearm_labels hψ q2.1 q2.2
  have h4 := labelPair_eq_of_fields (suppressSig_labels_eq hψ q3.1 q3.2)
  change labelPair (suppressSig hψ q3.1 q3.2) = labelPair q0
  exact h4.trans (h3.trans (h2.trans h1))

/-- Every stage through SUPPRESS_SIG frames the P'_ψ label pair. -/
theorem noCheckBirthBeforeEliminate_labels
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    labelPair (noCheckBirthBeforeEliminate hψ κ l r) =
      labelPair (pPsi hψ l r) :=
  (noCheckBirthCoreAfterBeforeCheck_labels hψ
    (noCheckBirthCoreBeforeCheck hψ κ l r)).trans
      (noCheckBirthCoreBeforeCheck_labels hψ κ l r)

/-! ## Algorithm-15 kill-field framing

ELIMINATE_LEADERS can remove the initiator only by observing an unshielded live
bullet at the responder. The following paired projection avoids unfolding the
whole prefix and proves those two fields unchanged stage by stage.
-/

private def killPair {ψ : Nat} (q : AgentState ψ × AgentState ψ) :=
  (q.1.shield, q.2.bullet)

private theorem killPair_eq_of_fields
    {q : AgentState ψ × AgentState ψ} {l r : AgentState ψ}
    (h : q.1.shield = l.shield ∧ q.2.bullet = r.bullet) :
    killPair q = killPair (l, r) :=
  Prod.ext h.1 h.2

private theorem waitSaturatedPrepare_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (waitSaturatedPrepare hψ l r) = (l.shield, r.bullet) := by
  unfold killPair waitSaturatedPrepare
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedCarry_kill
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    killPair (waitSaturatedCarry hψ κ l r) = (l.shield, r.bullet) := by
  unfold killPair waitSaturatedCarry satCountSucc
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedReset_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (waitSaturatedReset hψ l r) = (l.shield, r.bullet) := by
  unfold killPair waitSaturatedReset
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedFinish_kill
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    killPair (waitSaturatedFinish hψ κ l r) = (l.shield, r.bullet) := by
  simp [killPair, waitSaturatedFinish]

private theorem waitSaturated_kill
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    killPair (waitSaturated hψ κ l r) = (l.shield, r.bullet) := by
  let q0 := waitSaturatedPrepare hψ l r
  let q1 := waitSaturatedCarry hψ κ q0.1 q0.2
  let q2 := waitSaturatedReset hψ q1.1 q1.2
  calc
    killPair (waitSaturated hψ κ l r) = killPair q2 :=
      waitSaturatedFinish_kill hψ κ q2.1 q2.2
    _ = killPair q1 := waitSaturatedReset_kill hψ q1.1 q1.2
    _ = killPair q0 := waitSaturatedCarry_kill hψ κ q0.1 q0.2
    _ = (l.shield, r.bullet) := waitSaturatedPrepare_kill hψ l r

private theorem genSigSaturatedStart_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (genSigSaturatedStart hψ l r) = (l.shield, r.bullet) := by
  simp [killPair, genSigSaturatedStart]

private theorem genSigSaturatedEmit_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (genSigSaturatedEmit hψ l r) = (l.shield, r.bullet) := by
  simp [killPair, genSigSaturatedEmit]

private theorem genSigSaturatedPropagate_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (genSigSaturatedPropagate hψ l r) = (l.shield, r.bullet) := by
  simp [killPair, genSigSaturatedPropagate]

private theorem genSigSaturatedFinish_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (genSigSaturatedFinish hψ l r) = (l.shield, r.bullet) := by
  simp [killPair, genSigSaturatedFinish]

private theorem genSigSaturatedAfterWait_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (genSigSaturatedAfterWait hψ l r) = (l.shield, r.bullet) := by
  let q0 := genSigSaturatedStart hψ l r
  let q1 := genSigSaturatedEmit hψ q0.1 q0.2
  let q2 := genSigSaturatedPropagate hψ q1.1 q1.2
  calc
    killPair (genSigSaturatedAfterWait hψ l r) = killPair q2 :=
      genSigSaturatedFinish_kill hψ q2.1 q2.2
    _ = killPair q1 := genSigSaturatedPropagate_kill hψ q1.1 q1.2
    _ = killPair q0 := genSigSaturatedEmit_kill hψ q0.1 q0.2
    _ = (l.shield, r.bullet) := genSigSaturatedStart_kill hψ l r

/-- Saturated GENSIG frames the initiator shield and responder bullet. -/
theorem genSigSaturated_kill
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    killPair (genSigSaturated hψ κ l r) = (l.shield, r.bullet) := by
  let q := waitSaturated hψ κ l r
  exact (genSigSaturatedAfterWait_kill hψ q.1 q.2).trans
    (waitSaturated_kill hψ κ l r)

private theorem noCheckBirthCoreAfterPPsi_kill
    (hψ : ψ > 0) (κ : Nat) (q0 : AgentState ψ × AgentState ψ) :
    killPair (noCheckBirthCoreAfterPPsi hψ κ q0) = killPair q0 := by
  let q1 := genSigSaturated hψ κ q0.1 q0.2
  let q2 := cleanSig hψ q1.1 q1.2
  let q3 := eliminateSig hψ q2.1 q2.2
  have hgen := genSigSaturated_kill hψ κ q0.1 q0.2
  have hclean := killPair_eq_of_fields
    (cleanSig_kill_fields_eq hψ q1.1 q1.2)
  have helim := killPair_eq_of_fields
    (eliminateSig_kill_fields_eq hψ q2.1 q2.2)
  have hsig := killPair_eq_of_fields
    (sigMove_kill_fields_eq hψ q3.1 q3.2)
  change killPair (sigMove hψ q3.1 q3.2) = killPair q0
  exact hsig.trans (helim.trans (hclean.trans hgen))

/-- The named pre-CHECK boundary is the P'_ψ output followed by the saturated
WAIT/GENSIG, CLEAN, ELIMINATE_SIG, and SIGMOVE prefix.  Exposing this shallow
identity lets downstream projection proofs rewrite the boundary without
normalizing the full transition term. -/
theorem noCheckBirthCoreBeforeCheck_eq_afterPPsi
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    noCheckBirthCoreBeforeCheck hψ κ l r =
      noCheckBirthCoreAfterPPsi hψ κ (pPsi hψ l r) := by
  rfl

set_option maxHeartbeats 4000000 in
/-- The saturated prefix through SIGMOVE preserves the initiator shield and
responder bullet inspected later by ELIMINATE_LEADERS. -/
theorem noCheckBirthCoreBeforeCheck_kill_fields
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    (noCheckBirthCoreBeforeCheck hψ κ l r).1.shield = l.shield ∧
      (noCheckBirthCoreBeforeCheck hψ κ l r).2.bullet = r.bullet := by
  rw [noCheckBirthCoreBeforeCheck_eq_afterPPsi]
  have hp := pPsi_kill_fields_eq hψ l r
  have hprefix := noCheckBirthCoreAfterPPsi_kill hψ κ (pPsi hψ l r)
  unfold killPair at hprefix
  exact ⟨(congrArg Prod.fst hprefix).trans hp.1,
    (congrArg Prod.snd hprefix).trans hp.2⟩

private theorem checkSigNoBirthCore_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (checkSigNoBirthCore hψ l r) = (l.shield, r.bullet) := by
  exact killPair_eq_of_fields (checkSig_kill_fields_eq hψ l r)

private theorem cmpUpdatePropagate_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (cmpUpdatePropagate hψ l r) = (l.shield, r.bullet) := by
  unfold killPair cmpUpdatePropagate
  repeat (first | constructor | rfl | split)

private theorem cmpUpdateSetPath2_shield
    (hψ : ψ > 0) (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).shield = l.shield := by
  unfold cmpUpdateSetPath2
  repeat (first | rfl | split)

private theorem cmpUpdateNoSourceRearm_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (cmpUpdateNoSourceRearm hψ l r) = (l.shield, r.bullet) := by
  let l0 := if l.label = ⟨0, hψ⟩ ∧ l.state ≠ .depart then
    { l with state := .congest } else l
  let q := cmpUpdatePropagate hψ l0 r
  have hl0 : l0.shield = l.shield := by dsimp [l0]; split <;> rfl
  have hq := cmpUpdatePropagate_kill hψ l0 r
  have hql : q.1.shield = l0.shield := congrArg Prod.fst hq
  have hqr : q.2.bullet = r.bullet := congrArg Prod.snd hq
  change killPair (cmpUpdateSetPath2 hψ q.1, q.2) = (l.shield, r.bullet)
  unfold killPair
  rw [cmpUpdateSetPath2_shield, hql, hqr, hl0]

private theorem compareSigInit_shield_eq (l : AgentState ψ) :
    (compareSigInit l).shield = l.shield := by
  unfold compareSigInit
  split <;> rfl

private theorem compareSigNoSourceRearm_kill
    (hψ : ψ > 0) (l r : AgentState ψ) :
    killPair (compareSigNoSourceRearm hψ l r) = (l.shield, r.bullet) := by
  unfold compareSigNoSourceRearm
  dsimp only
  split
  · exact Prod.ext (compareSigInit_shield_eq l) rfl
  · split
    · let l0 := compareSigInit l
      let q := cmpUpdateNoSourceRearm hψ l0 r
      have hcmp := cmpUpdateNoSourceRearm_kill hψ l0 r
      have hdispatch := killPair_eq_of_fields
        (compareSigDispatch_kill_fields_eq hψ q.1 q.2)
      have hinit : killPair (l0, r) = (l.shield, r.bullet) :=
        Prod.ext (compareSigInit_shield_eq l) rfl
      exact hdispatch.trans (hcmp.trans hinit)
    · exact Prod.ext (compareSigInit_shield_eq l) rfl

private theorem noCheckBirthCoreAfterBeforeCheck_kill
    (hψ : ψ > 0) (q0 : AgentState ψ × AgentState ψ) :
    killPair (noCheckBirthCoreAfterBeforeCheck hψ q0) = killPair q0 := by
  let q1 := checkSigNoBirthCore hψ q0.1 q0.2
  let q2 := disappear hψ q1.1 q1.2
  let q3 := compareSigNoSourceRearm hψ q2.1 q2.2
  have h1 := checkSigNoBirthCore_kill hψ q0.1 q0.2
  have h2 := killPair_eq_of_fields
    (disappear_kill_fields_eq hψ q1.1 q1.2)
  have h3 := compareSigNoSourceRearm_kill hψ q2.1 q2.2
  have h4 := killPair_eq_of_fields
    (suppressSig_kill_fields_eq hψ q3.1 q3.2)
  change killPair (suppressSig hψ q3.1 q3.2) = killPair q0
  exact h4.trans (h3.trans (h2.trans h1))

private theorem noCheckBirthBeforeEliminate_eq
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    noCheckBirthBeforeEliminate hψ κ l r =
      noCheckBirthCoreAfterBeforeCheck hψ
        (noCheckBirthCoreBeforeCheck hψ κ l r) := by
  rfl

attribute [local irreducible] noCheckBirthCoreAfterBeforeCheck

/-- The complete no-CHECK-birth prefix preserves exactly the shield and live
bullet fields later inspected by ELIMINATE_LEADERS. -/
theorem noCheckBirthBeforeEliminate_kill_fields
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    (noCheckBirthBeforeEliminate hψ κ l r).1.shield = l.shield ∧
      (noCheckBirthBeforeEliminate hψ κ l r).2.bullet = r.bullet := by
  rw [noCheckBirthBeforeEliminate_eq]
  have hp := killPair_eq_of_fields (pPsi_kill_fields_eq hψ l r)
  have hprefix := noCheckBirthCoreAfterPPsi_kill hψ κ (pPsi hψ l r)
  have hsuffix := noCheckBirthCoreAfterBeforeCheck_kill hψ
    (noCheckBirthCoreBeforeCheck hψ κ l r)
  have hall : killPair (noCheckBirthCoreAfterBeforeCheck hψ
      (noCheckBirthCoreBeforeCheck hψ κ l r)) =
      (l.shield, r.bullet) := hsuffix.trans (hprefix.trans hp)
  exact ⟨congrArg Prod.fst hall, congrArg Prod.snd hall⟩

attribute [local irreducible] noCheckBirthBeforeEliminate

/-- PaperSafe discharges the responder-label field of the corrected condition-1
boundary. -/
theorem noCheckConditionOne_responder_label
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e : Fin n) :
    (noCheckBirthBeforeEliminate hψ κ
      (C e) (C (ring.rightNeighbor e))).2.label =
        (C (ring.rightNeighbor e)).label := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  have hframe := noCheckBirthBeforeEliminate_labels hψ κ l r
  have hframeR : (noCheckBirthBeforeEliminate hψ κ l r).2.label =
      (pPsi hψ l r).2.label := congrArg Prod.snd hframe
  rw [hframeR]
  by_cases hb : isBarrier hψ l r
  · have hrLeaderProp := hSafe.no_free_barrier e hb
    have hrLeader : r.leader = true := by
      simpa [AgentState.isLeader] using hrLeaderProp
    have hrLabel : r.label = ⟨0, hψ⟩ :=
      paperSafe_unique_leader_label_zero hψ ring C hSafe
        (ring.rightNeighbor e) hrLeaderProp
    exact pPsi_responder_label_of_leader_zero hψ l r hrLeader hrLabel
  · exact pPsi_responder_label_of_nonbarrier hψ l r hb

end PPLLNoCheckBirthBoundaryFrames

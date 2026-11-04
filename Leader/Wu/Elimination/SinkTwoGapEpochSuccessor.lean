import Leader.Wu.Elimination.SinkTwoGapEpochKernel


open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
  LDSinkGapBlockedPreStep LDSinkGapCleanupBound LDTwoGapFrame
  LDSinkTwoGapEpochDefs LDSinkTwoGapEpochCost LDSinkTwoGapEpochLaws
  LDSinkTwoGapEpochKernel PPLLRepair FiniteUniformStoppingTree
open Classical


namespace LDSinkTwoGapEpochSuccessor


set_option autoImplicit false


variable {n ψ : Nat}


/-! ## Cellwise structural preservation -/


private theorem fire_leaders_epoch (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.leader = l.leader ∧
      (eliminateLeadersNoCollisionFire hψ l r).2.leader = r.leader := by
  constructor <;>
    (simp only [eliminateLeadersNoCollisionFire] <;>
      (repeat split <;> rfl))


private theorem move_left_follower_epoch (hψ : ψ > 0)
    (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = false) :
    (absorbProtectedMove hψ nl l r).1.leader = false := by
  unfold absorbProtectedMove
  try unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  repeat (first | exact hl | rfl | split)


private theorem move_right_leader_epoch (hψ : ψ > 0)
    (nl : Fin ψ) (l r : AgentState ψ) :
    (absorbProtectedMove hψ nl l r).2.leader = r.leader := by
  unfold absorbProtectedMove
  try unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  repeat (first | rfl | split)


private theorem signal_leaders_epoch (nl : Fin ψ)
    (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).1.leader = l.leader ∧
      (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.leader = r.leader := by
  constructor <;>
    (unfold eliminateLeadersNoCollisionSignalLeaderSink
     dsimp only
     repeat (first | rfl | split))


private theorem dummy_leaders_epoch
    (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).1.leader = q.1.leader ∧
      (dummyBulletSink q).2.leader = q.2.leader := by
  constructor <;>
    (unfold dummyBulletSink
     dsimp only
     repeat (first | rfl | split))


/-- The left cell of the C-kernel cannot create a leader: a follower remains a
follower.  This is the only direction needed for interior-gap preservation. -/
theorem kernelC_left_follower
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) :
    (sinkKernelC hψ l r).1.leader = false := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  have h0 := (fire_leaders_epoch hψ l r).1.trans hl
  have h1 := move_left_follower_epoch hψ nl q0.1 q0.2 h0
  have h2 := (signal_leaders_epoch nl q1.1 q1.2).1
  have h3 := (dummy_leaders_epoch q2).1
  change (dummyBulletSink q2).1.leader = false
  exact h3.trans (h2.trans h1)


/-- The responder's leader bit is framed exactly by the C-kernel. -/
theorem kernelC_right_leader_eq
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (sinkKernelC hψ l r).2.leader = r.leader := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  have h0 := (fire_leaders_epoch hψ l r).2
  have h1 := move_right_leader_epoch hψ nl q0.1 q0.2
  have h2 := (signal_leaders_epoch nl q1.1 q1.2).2
  have h3 := (dummy_leaders_epoch q2).2
  change (dummyBulletSink q2).2.leader = r.leader
  exact h3.trans (h2.trans (h1.trans h0))


/-- No cell which is already a follower can become a leader in one C-kernel
interaction. -/
theorem kernelC_no_leader_creation
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (l.leader = false → (sinkKernelC hψ l r).1.leader = false) ∧
      (r.leader = false → (sinkKernelC hψ l r).2.leader = false) := by
  constructor
  · exact kernelC_left_follower hψ l r
  · intro hr
    exact (kernelC_right_leader_eq hψ l r).trans hr


private theorem head_ne_epoch (F : GapFrame n) (e : Fin n) :
    F.ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  have hd := F.hd
  have hdn := F.hdn
  by_cases ha : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self] at hv
    omega


private theorem sinkStepC_at_left_epoch
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ F C e e =
      (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).1 := by
  simp [sinkStepC, updatePair]


private theorem sinkStepC_at_right_epoch
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ F C e (F.ring.rightNeighbor e) =
      (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).2 := by
  simp [sinkStepC, updatePair, head_ne_epoch F e]


/-- Pointwise leader non-creation for the whole-ring C step. -/
theorem sinkStepC_follower_preserved
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e v : Fin n)
    (hv : (C v).leader = false) :
    (sinkStepC hψ F C e v).leader = false := by
  by_cases hleft : v = e
  · subst v
    rw [sinkStepC_at_left_epoch]
    exact kernelC_left_follower hψ (C e) (C (F.ring.rightNeighbor e)) hv
  · by_cases hright : v = F.ring.rightNeighbor e
    · subst v
      rw [sinkStepC_at_right_epoch]
      exact (kernelC_right_leader_eq hψ
        (C e) (C (F.ring.rightNeighbor e))).trans hv
    · rw [sinkStepC_other hψ F C e v hleft hright]
      exact hv


/-- Labels are pointwise framed by the whole-ring C step. -/
theorem sinkStepC_label_eq
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e v : Fin n) :
    (sinkStepC hψ F C e v).label = (C v).label := by
  by_cases hleft : v = e
  · subst v
    rw [sinkStepC_at_left_epoch]
    exact (kernelC_labels hψ (C e) (C (F.ring.rightNeighbor e))).1
  · by_cases hright : v = F.ring.rightNeighbor e
    · subst v
      rw [sinkStepC_at_right_epoch]
      exact (kernelC_labels hψ (C e) (C (F.ring.rightNeighbor e))).2
    · rw [sinkStepC_other hψ F C e v hleft hright]


/-! ## Recovering the invariant after a CleanReady successor -/


/-- Non-deletion of both endpoints is exactly endpoint presence. -/
theorem gapEndpointsPresent_of_not_endpointDeleted
    (F : GapFrame n) (C : Fin n → AgentState ψ)
    (hn : ¬ EndpointDeleted F C) :
    GapEndpointsPresent F C := by
  constructor
  · by_cases h0 : (C (F.pos 0)).leader = true
    · exact h0
    · exact False.elim (hn (Or.inl (by simpa using h0)))
  · by_cases hd : (C (F.pos F.d)).leader = true
    · exact hd
    · exact False.elim (hn (Or.inr (by simpa using hd)))


/-- Interior followers survive one C step because the kernel never creates a
leader. -/
theorem gapInteriorFollowers_step
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInteriorFollowers F C) :
    GapInteriorFollowers F (sinkStepC hψ F C e) := by
  intro k hk hkd
  exact sinkStepC_follower_preserved hψ F C e (F.pos k)
    (hi k hk hkd)


/-- Label alignment survives because every individual label is framed. -/
theorem gapLabelAligned_step
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapLabelAligned hψ F C) :
    GapLabelAligned hψ F (sinkStepC hψ F C e) := by
  intro k hk
  have h1 := sinkStepC_label_eq hψ F C e (F.pos (k + 1))
  have h2 := sinkStepC_label_eq hψ F C e (F.pos k)
  have hk' := hi k hk
  have hnl : nextLabel hψ (sinkStepC hψ F C e (F.pos k))
      = nextLabel hψ (C (F.pos k)) := by
    apply Fin.ext
    show ((sinkStepC hψ F C e (F.pos k)).label.val + 1) % ψ
        = ((C (F.pos k)).label.val + 1) % ψ
    rw [h2]
  rw [h1, hnl]
  exact hk'


/-- The three non-signal pieces needed to turn a CleanReady successor back
into a full `GapInvariant`. -/
theorem gapShape_step_of_invariant_not_deleted
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInvariant hψ F C)
    (hn : ¬ EndpointDeleted F (sinkStepC hψ F C e)) :
    GapEndpointsPresent F (sinkStepC hψ F C e) ∧
      GapInteriorFollowers F (sinkStepC hψ F C e) ∧
      GapLabelAligned hψ F (sinkStepC hψ F C e) := by
  exact ⟨gapEndpointsPresent_of_not_endpointDeleted F _ hn,
    gapInteriorFollowers_step hψ F C e hi.2.1,
    gapLabelAligned_step hψ F C e hi.2.2.1⟩


/-- Strengthening of `sinkStepC_invariant_or_done'`: if the pre-state is a
non-done invariant and neither endpoint is deleted by the step, then the
successor is again invariant.  The only extra work over the existing theorem
is rebuilding the invariant in its `CleanReady` successor branch. -/
theorem gapInvariant_step_of_not_endpointDeleted
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInvariant hψ F C)
    (hn : ¬ GapDoneC F C)
    (hdel : ¬ EndpointDeleted F (sinkStepC hψ F C e)) :
    GapInvariant hψ F (sinkStepC hψ F C e) := by
  rcases sinkStepC_invariant_or_done' hψ F C e hi hn with hdone | hinv
  · change CleanReady F (sinkStepC hψ F C e) ∨
      EndpointDeleted F (sinkStepC hψ F C e) at hdone
    rcases hdone with hclean | hdeleted
    · have hshape := gapShape_step_of_invariant_not_deleted
        hψ F C e hi hdel
      exact gapInvariant_of_cleanReady_and_shape hψ F
        (sinkStepC hψ F C e)
        hshape.1 hshape.2.1 hshape.2.2 hclean
    · exact False.elim (hdel hdeleted)
  · exact hinv


/-! ## Correct stopping predicate for the three-leader frame -/


/-- Correct frame-level progress event: an endpoint of either adjacent gap has
been deleted.  Since the two gaps share `j`, this is exactly deletion of one of
`i`, `j`, or `k`.  This should replace the imported attack-only `Success` in the
upstream epoch definition if successor closure is required for arbitrary raw
scheduler edges. -/
def FrameSuccess (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  EndpointDeleted F.recovery C ∨ EndpointDeleted F.attack C


/-- Imported attack-only success is contained in the corrected frame success. -/
theorem Success_implies_FrameSuccess (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) :
    Success F C → FrameSuccess F C := by
  intro hs
  right
  simpa only [Success] using hs


/-- Under the corrected success predicate, non-success gives recovery endpoint
presence with no additional hypothesis. -/
theorem recovery_not_deleted_of_not_frameSuccess
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hs : ¬ FrameSuccess F C) :
    ¬ EndpointDeleted F.recovery C := by
  intro h
  exact hs (Or.inl h)


/-- Likewise for the attack gap. -/
theorem attack_not_deleted_of_not_frameSuccess
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hs : ¬ FrameSuccess F C) :
    ¬ EndpointDeleted F.attack C := by
  intro h
  exact hs (Or.inr h)


/-- Old attack-only `¬ Success` does guarantee that the shared recovery-right
endpoint `j` remains present, because it is the attack victim. -/
theorem recovery_right_present_of_not_success
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hs : ¬ Success F C) :
    (C (F.recovery.pos F.recovery.d)).leader = true := by
  have hatt : ¬ EndpointDeleted F.attack C := by
    simpa only [Success] using hs
  have hep := gapEndpointsPresent_of_not_endpointDeleted F.attack C hatt
  rw [F.shared]
  exact hep.1


/-- This is the sharp old-`Success` recovery API.  The only extra shape fact
needed is that the recovery-left endpoint `i` is still present. -/
theorem recovery_not_deleted_of_not_success_and_shape
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hs : ¬ Success F C)
    (hleft : (C (F.recovery.pos 0)).leader = true) :
    ¬ EndpointDeleted F.recovery C := by
  have hright := recovery_right_present_of_not_success F C hs
  intro hdel
  rcases hdel with hl | hr
  · rw [hleft] at hl
    cases hl
  · rw [hright] at hr
    cases hr


/-! ## Successor invariants -/


/-- Attack half of the requested successor closure under the existing
attack-only `Success`. -/
theorem attack_successorInvariant_of_not_success
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInvariant hψ F.attack C)
    (hn : ¬ GapDoneC F.attack C)
    (hs : ¬ Success F (sinkStepC hψ F.attack C e)) :
    GapInvariant hψ F.attack (sinkStepC hψ F.attack C e) := by
  have hdel : ¬ EndpointDeleted F.attack (sinkStepC hψ F.attack C e) := by
    simpa only [Success] using hs
  exact gapInvariant_step_of_not_endpointDeleted
    hψ F.attack C e hi hn hdel


/-- Recovery half, stated with exactly the post-step non-deletion fact it
requires.  The physical step is written through the attack frame to match
`epochStepConf`. -/
theorem recovery_successorInvariant_of_not_deleted
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInvariant hψ F.recovery C)
    (hn : ¬ GapDoneC F.recovery C)
    (hdel : ¬ EndpointDeleted F.recovery
      (sinkStepC hψ F.attack C e)) :
    GapInvariant hψ F.recovery (sinkStepC hψ F.attack C e) := by
  have hdel' : ¬ EndpointDeleted F.recovery
      (sinkStepC hψ F.recovery C e) := by
    rw [twoGap_sinkStepC_eq hψ F C e]
    exact hdel
  have hInv := gapInvariant_step_of_not_endpointDeleted
    hψ F.recovery C e hi hn hdel'
  rw [twoGap_sinkStepC_eq hψ F C e] at hInv
  exact hInv


/-- Fully closed two-gap successor invariants with the corrected three-leader
success predicate. -/
theorem successorInvariants_of_not_frameSuccess
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hRecovery : GapInvariant hψ F.recovery C)
    (hAttack : GapInvariant hψ F.attack C)
    (hnAttack : ¬ GapDoneC F.attack C)
    (hnRecovery : ¬ GapDoneC F.recovery C)
    (hs : ¬ FrameSuccess F (sinkStepC hψ F.attack C e)) :
    GapInvariant hψ F.recovery (sinkStepC hψ F.attack C e) ∧
      GapInvariant hψ F.attack (sinkStepC hψ F.attack C e) := by
  have hrecDel := recovery_not_deleted_of_not_frameSuccess F _ hs
  have hattDel := attack_not_deleted_of_not_frameSuccess F _ hs
  constructor
  · exact recovery_successorInvariant_of_not_deleted
      hψ F C e hRecovery hnRecovery hrecDel
  · exact gapInvariant_step_of_not_endpointDeleted
      hψ F.attack C e hAttack hnAttack hattDel


/-- The user's requested old-`Success` statement becomes provable once the
single missing post-step shape fact—presence of `i`—is supplied. -/
theorem successorInvariants_of_not_success_and_recoveryLeft
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hRecovery : GapInvariant hψ F.recovery C)
    (hAttack : GapInvariant hψ F.attack C)
    (hnAttack : ¬ GapDoneC F.attack C)
    (hnRecovery : ¬ GapDoneC F.recovery C)
    (hs : ¬ Success F (sinkStepC hψ F.attack C e))
    (hleft :
      (sinkStepC hψ F.attack C e (F.recovery.pos 0)).leader = true) :
    GapInvariant hψ F.recovery (sinkStepC hψ F.attack C e) ∧
      GapInvariant hψ F.attack (sinkStepC hψ F.attack C e) := by
  have hrecDel := recovery_not_deleted_of_not_success_and_shape
    F (sinkStepC hψ F.attack C e) hs hleft
  constructor
  · exact recovery_successorInvariant_of_not_deleted
      hψ F C e hRecovery hnRecovery hrecDel
  · exact attack_successorInvariant_of_not_success
      hψ F C e hAttack hnAttack hs


/-- Honest residue if the imported attack-only `Success` is retained.  This
field is not expected to hold for arbitrary raw scheduler edges: the leader
immediately to the left of the recovery gap may itself be deleted.  Prefer
changing the upstream epoch stop predicate to `FrameSuccess`. -/
structure OldSuccessRecoveryResidual (hψ : ψ > 0)
    (F : TwoGapFrame n) : Prop where
  recoveryLeftPresent :
    ∀ (C : Fin n → AgentState ψ) (e : Fin n),
      GapInvariant hψ F.recovery C →
      GapInvariant hψ F.attack C →
      ¬ GapDoneC F.attack C →
      ¬ GapDoneC F.recovery C →
      ¬ Success F (sinkStepC hψ F.attack C e) →
      (sinkStepC hψ F.attack C e (F.recovery.pos 0)).leader = true


/-- The old successor-invariant obligation follows from exactly the one honest
residual field above. -/
theorem successorInvariants_of_oldSuccessResidual
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : OldSuccessRecoveryResidual hψ F)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hRecovery : GapInvariant hψ F.recovery C)
    (hAttack : GapInvariant hψ F.attack C)
    (hnAttack : ¬ GapDoneC F.attack C)
    (hnRecovery : ¬ GapDoneC F.recovery C)
    (hs : ¬ Success F (sinkStepC hψ F.attack C e)) :
    GapInvariant hψ F.recovery (sinkStepC hψ F.attack C e) ∧
      GapInvariant hψ F.attack (sinkStepC hψ F.attack C e) := by
  exact successorInvariants_of_not_success_and_recoveryLeft
    hψ F C e hRecovery hAttack hnAttack hnRecovery hs
    (hR.recoveryLeftPresent C e hRecovery hAttack
      hnAttack hnRecovery hs)


/-- `epochStepConf` version of the fully closed corrected-success theorem. -/
theorem epoch_successorInvariants_of_not_frameSuccess
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F) (e : Fin n)
    (hRecovery : GapInvariant hψ F.recovery x.conf)
    (hAttack : GapInvariant hψ F.attack x.conf)
    (hnAttack : ¬ GapDoneC F.attack x.conf)
    (hnRecovery : ¬ GapDoneC F.recovery x.conf)
    (hs : ¬ FrameSuccess F (epochStepConf hψ F x e)) :
    GapInvariant hψ F.recovery (epochStepConf hψ F x e) ∧
      GapInvariant hψ F.attack (epochStepConf hψ F x e) := by
  simpa only [epochStepConf] using
    successorInvariants_of_not_frameSuccess hψ F x.conf e
      hRecovery hAttack hnAttack hnRecovery hs


/-! ## Active entrance, correctly stated -/


/-- `RoundActive` alone still does not imply `Entrance`.  With `Entrance` as
an explicit hypothesis, its exact decomposition is immediate. -/
theorem activeEntrance_components
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : RoundActive (ψ := ψ) F)
    (hE : Entrance hψ F x.1) :
    GapInvariant hψ F.recovery x.1.conf ∧
      GapInvariant hψ F.attack x.1.conf ∧
      ((x.1.conf (F.attack.pos F.attack.d)).signal_B = (1 : Fin 2) ∨
        x.1.phase = .transit ∨ x.1.phase = .parked) := by
  exact entrance_components hψ F x.1 hE


#print axioms LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
#print axioms LDSinkTwoGapEpochSuccessor.sinkStepC_follower_preserved
#print axioms LDSinkTwoGapEpochSuccessor.sinkStepC_label_eq
#print axioms LDSinkTwoGapEpochSuccessor.gapInvariant_step_of_not_endpointDeleted
#print axioms LDSinkTwoGapEpochSuccessor.recovery_not_deleted_of_not_success_and_shape
#print axioms LDSinkTwoGapEpochSuccessor.successorInvariants_of_not_frameSuccess
#print axioms LDSinkTwoGapEpochSuccessor.successorInvariants_of_oldSuccessResidual
#print axioms LDSinkTwoGapEpochSuccessor.epoch_successorInvariants_of_not_frameSuccess
#print axioms LDSinkTwoGapEpochSuccessor.activeEntrance_components


end LDSinkTwoGapEpochSuccessor

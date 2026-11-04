import Leader.Wu.WallSweep.PreCheckResetRepair

/-!
# Local contracts for the pre-CHECK reset wall

The pre-CHECK deletion changes comparison timing but leaves the existing
deletion-priority and reset/echo architecture intact.  This module proves the
field-level contracts needed to replay the arbitrary-ring cleanup schedule:
active deletion edges agree with the earlier full wall, while priority-open
edges preserve the designated anchor and implement echo drain, leader reseed,
and reset movement under the corrected CHECK order.
-/

namespace PPLLWallSweepPreCheckResetContracts

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLRepair PPLLWriteIncrementGate
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLTerminalEqualSupportRepair
  PPLLWallSweepNormalResetContract PPLLWallSweepEchoDrain
  PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoKernel
  PPLLNoCheckBirthConditionTwoPhysical

variable {psi kappa tau : Nat}

/-! ## Exact agreement on deletion-priority edges -/

private theorem normalizeDeletion_eq_of_active
    (u : AuthorizedAgentState psi) (h : deletionActive u = true) :
    normalizeDeletion u = u := by
  cases hp : u.core.path with
  | bot => simp [deletionActive, pathPresent, hp] at h
  | some label bit => simp [normalizeDeletion, pathPresent, hp]

/-- On an active responder the corrected transition selects the same isolated
Algorithm-9 branch as the earlier full wall; the new pre-CHECK stage is never
reached. -/
theorem wallSweepPreCheckResetAuthorized_eq_wallSweep_of_responder_active
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive r = true) :
    wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
      wallSweepAuthorizedTransition hpsi kappa l r := by
  have hnr := normalizeDeletion_eq_of_active r hr
  simp [wallSweepPreCheckResetAuthorizedTransition,
    wallSweepAuthorizedTransition, hnr, hr]

private theorem authorizedBounded_erase_injective :
    Function.Injective
      (@AuthorizedBoundedAgentState.erase psi kappa) := by
  intro a b h
  cases a with
  | mk ac ap =>
      cases b with
      | mk bc bp =>
          have hcoreErase : ac.erase = bc.erase :=
            congrArg (fun u : AuthorizedAgentState psi => u.core) h
          have hcore : ac = bc := by
            apply BoundedAgentState.eraseToDomain_bijective.1
            apply Subtype.ext
            exact hcoreErase
          have hpermit : ap = bp :=
            congrArg (fun u : AuthorizedAgentState psi => u.path0Crossed) h
          cases hcore
          cases hpermit
          rfl

/-- Exact active-responder agreement survives finite reification. -/
theorem wallSweepPreCheckResetBounded_eq_wallSweep_of_responder_active
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hr : deletionActive r.erase = true) :
    wallSweepPreCheckResetBoundedTransition hpsi kappa l r =
      wallSweepBoundedTransition hpsi kappa l r := by
  let qNew := wallSweepPreCheckResetBoundedTransition hpsi kappa l r
  let qOld := wallSweepBoundedTransition hpsi kappa l r
  have hNew := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l r
  have hOld := erase_wallSweepBoundedTransition hpsi kappa l r
  have hAuth :=
    wallSweepPreCheckResetAuthorized_eq_wallSweep_of_responder_active
      hpsi kappa l.erase r.erase hr
  change (qNew.1.erase, qNew.2.erase) =
    wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.erase r.erase at hNew
  change (qOld.1.erase, qOld.2.erase) =
    wallSweepAuthorizedTransition hpsi kappa l.erase r.erase at hOld
  have hErase : (qNew.1.erase, qNew.2.erase) =
      (qOld.1.erase, qOld.2.erase) :=
    hNew.trans (hAuth.trans hOld.symm)
  apply Prod.ext
  · exact authorizedBounded_erase_injective (congrArg Prod.fst hErase)
  · exact authorizedBounded_erase_injective (congrArg Prod.snd hErase)

/-- Exact active-responder agreement also survives path-stall expiry. -/
theorem wallSweepPreCheckResetPathStall_eq_wallSweep_of_responder_active
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hr : deletionActive r.core.erase = true) :
    wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r =
      wallSweepPathStallTransition hpsi kappa tau l r := by
  have hbase :=
    wallSweepPreCheckResetBounded_eq_wallSweep_of_responder_active
      hpsi kappa l.core r.core hr
  unfold wallSweepPreCheckResetPathStallTransition
    wallSweepPathStallTransition
  rw [hbase]

/-! ### Leader-sink agreement on deletion-priority edges -/

/-- The rooted leader-sink repair has the same isolated Algorithm-9 branch as
the established pre-CHECK-reset transition on an active responder. -/
theorem wallSweepPreCheckResetLeaderSinkAuthorized_eq_of_responder_active
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive r = true) :
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa l r =
      wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r := by
  have hnr := normalizeDeletion_eq_of_active r hr
  simp [wallSweepPreCheckResetLeaderSinkAuthorizedTransition,
    wallSweepPreCheckResetAuthorizedTransition, hnr, hr]

/-- Active-responder agreement survives finite reification. -/
theorem wallSweepPreCheckResetLeaderSinkBounded_eq_of_responder_active
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hr : deletionActive r.erase = true) :
    wallSweepPreCheckResetLeaderSinkBoundedTransition hpsi kappa l r =
      wallSweepPreCheckResetBoundedTransition hpsi kappa l r := by
  let qNew := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  let qOld := wallSweepPreCheckResetBoundedTransition hpsi kappa l r
  have hNew := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  have hOld := erase_wallSweepPreCheckResetBoundedTransition hpsi kappa l r
  have hAuth :=
    wallSweepPreCheckResetLeaderSinkAuthorized_eq_of_responder_active
      hpsi kappa l.erase r.erase hr
  change (qNew.1.erase, qNew.2.erase) =
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.erase r.erase at hNew
  change (qOld.1.erase, qOld.2.erase) =
    wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.erase r.erase at hOld
  have hErase : (qNew.1.erase, qNew.2.erase) =
      (qOld.1.erase, qOld.2.erase) :=
    hNew.trans (hAuth.trans hOld.symm)
  apply Prod.ext
  · exact authorizedBounded_erase_injective (congrArg Prod.fst hErase)
  · exact authorizedBounded_erase_injective (congrArg Prod.snd hErase)

/-- Active-responder agreement survives path-stall expiry. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_eq_of_responder_active
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hr : deletionActive r.core.erase = true) :
    wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r =
      wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r := by
  have hbase :=
    wallSweepPreCheckResetLeaderSinkBounded_eq_of_responder_active
      hpsi kappa l.core r.core hr
  unfold wallSweepPreCheckResetLeaderSinkPathStallTransition
    wallSweepPreCheckResetPathStallTransition
  rw [hbase]

/-! ### Reset-free agreement of the integrated P-prime guard -/

/-- Exact authorized agreement of the integrated reset-aware transition with
the established rooted transition on reset-free initiator edges. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_of_no_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = false) :
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r =
      wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r :=
  wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition_eq_of_no_reset
    hpsi kappa l r hlReset

/-- Exact reset-free agreement survives finite reification. -/
theorem wallSweepResetProbePreCheckResetLeaderSinkBounded_eq_of_no_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hlReset : l.erase.core.reset_cmd = false) :
    wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
        hpsi kappa l r =
      wallSweepPreCheckResetLeaderSinkBoundedTransition
        hpsi kappa l r := by
  let qNew := wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  let qOld := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  have hNew :=
    erase_wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l r
  have hOld := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  have hAuth :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_of_no_reset
      hpsi kappa l.erase r.erase hlReset
  change (qNew.1.erase, qNew.2.erase) =
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.erase r.erase at hNew
  change (qOld.1.erase, qOld.2.erase) =
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.erase r.erase at hOld
  have hErase : (qNew.1.erase, qNew.2.erase) =
      (qOld.1.erase, qOld.2.erase) :=
    hNew.trans (hAuth.trans hOld.symm)
  apply Prod.ext
  · exact authorizedBounded_erase_injective (congrArg Prod.fst hErase)
  · exact authorizedBounded_erase_injective (congrArg Prod.snd hErase)

/-- Exact reset-free agreement survives the path-stall/deletion-expiry
wrapper. -/
theorem wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_no_reset
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hlReset : l.core.erase.core.reset_cmd = false) :
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r =
      wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r := by
  have hbase :=
    wallSweepResetProbePreCheckResetLeaderSinkBounded_eq_of_no_reset
      hpsi kappa l.core r.core hlReset
  unfold wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    wallSweepPreCheckResetLeaderSinkPathStallTransition
  rw [hbase]

/-! ### Responder-leader agreement of the integrated P-prime guard -/

/-- The integrated authorized transition and the rooted transition coincide
when the responder is already a leader, including on the reset-carrying
closing edge. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_of_right_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r =
      wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r :=
  wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition_eq_of_right_leader
    hpsi kappa l r hrLeader

/-- The integrated and rooted authorized transitions also coincide when the
initiator is the existing leader. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_of_left_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r =
      wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r :=
  wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition_eq_of_left_leader
    hpsi kappa l r hlLeader

/-- Exact responder-leader agreement survives finite reification. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkBounded_eq_of_right_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hrLeader : r.erase.core.leader = true) :
    wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
        hpsi kappa l r =
      wallSweepPreCheckResetLeaderSinkBoundedTransition
        hpsi kappa l r := by
  let qNew := wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  let qOld := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  have hNew :=
    erase_wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l r
  have hOld := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  have hAuth :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_of_right_leader
      hpsi kappa l.erase r.erase hrLeader
  change (qNew.1.erase, qNew.2.erase) =
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.erase r.erase at hNew
  change (qOld.1.erase, qOld.2.erase) =
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.erase r.erase at hOld
  have hErase : (qNew.1.erase, qNew.2.erase) =
      (qOld.1.erase, qOld.2.erase) :=
    hNew.trans (hAuth.trans hOld.symm)
  apply Prod.ext
  · exact authorizedBounded_erase_injective (congrArg Prod.fst hErase)
  · exact authorizedBounded_erase_injective (congrArg Prod.snd hErase)

/-- Exact initiator-leader agreement survives finite reification. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkBounded_eq_of_left_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hlLeader : l.erase.core.leader = true) :
    wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
        hpsi kappa l r =
      wallSweepPreCheckResetLeaderSinkBoundedTransition
        hpsi kappa l r := by
  let qNew := wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  let qOld := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  have hNew :=
    erase_wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l r
  have hOld := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  have hAuth :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_of_left_leader
      hpsi kappa l.erase r.erase hlLeader
  change (qNew.1.erase, qNew.2.erase) =
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.erase r.erase at hNew
  change (qOld.1.erase, qOld.2.erase) =
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.erase r.erase at hOld
  have hErase : (qNew.1.erase, qNew.2.erase) =
      (qOld.1.erase, qOld.2.erase) :=
    hNew.trans (hAuth.trans hOld.symm)
  apply Prod.ext
  · exact authorizedBounded_erase_injective (congrArg Prod.fst hErase)
  · exact authorizedBounded_erase_injective (congrArg Prod.snd hErase)

/-- Exact responder-leader agreement survives path-stall and deletion expiry. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_right_leader
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hrLeader : r.core.erase.core.leader = true) :
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r =
      wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r := by
  have hbase :=
    wallSweepResetProbePreCheckResetLeaderSinkBounded_eq_of_right_leader
      hpsi kappa l.core r.core hrLeader
  unfold wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    wallSweepPreCheckResetLeaderSinkPathStallTransition
  rw [hbase]

/-- Exact initiator-leader agreement survives path-stall and deletion expiry. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hlLeader : l.core.erase.core.leader = true) :
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r =
      wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r := by
  have hbase :=
    wallSweepResetProbePreCheckResetLeaderSinkBounded_eq_of_left_leader
      hpsi kappa l.core r.core hlLeader
  unfold wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    wallSweepPreCheckResetLeaderSinkPathStallTransition
  rw [hbase]

/-! ## Anchor and label frame through the new prefix -/

theorem normalizeDeletion_initiator_anchor
    (u : AuthorizedAgentState psi) (h : InitiatorAnchor u.core) :
    InitiatorAnchor (normalizeDeletion u).core := by
  unfold InitiatorAnchor at h ⊢
  unfold normalizeDeletion
  split <;> exact h

theorem normalizeDeletion_responder_zero_anchor
    (hpsi : psi > 0) (u : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi u.core) :
    ResponderZeroAnchor hpsi (normalizeDeletion u).core := by
  unfold ResponderZeroAnchor at h ⊢
  unfold normalizeDeletion
  split <;> exact h

theorem normalizeDeletion_label_eq (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl

theorem normalizeDeletion_leader_eq (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl

theorem normalizeDeletion_probe_eq (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.probe = u.core.probe := by
  unfold normalizeDeletion
  split <;> rfl

theorem sanitizeAuthorizedTerminalEqual_leader_eq
    (hpsi : psi > 0) (u : AuthorizedAgentState psi) :
    (sanitizeAuthorizedTerminalEqual hpsi u).core.leader =
      u.core.leader := by
  unfold sanitizeAuthorizedTerminalEqual
  split <;> rfl

private theorem sanitizeAuthorizedTerminalEqual_label_eq
    (hpsi : psi > 0) (u : AuthorizedAgentState psi) :
    (sanitizeAuthorizedTerminalEqual hpsi u).core.label =
      u.core.label := by
  unfold sanitizeAuthorizedTerminalEqual
  split <;> rfl

theorem sanitizeAuthorizedPair_leaders_eq
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (sanitizeAuthorizedPair hpsi q).1.core.leader = q.1.core.leader ∧
      (sanitizeAuthorizedPair hpsi q).2.core.leader = q.2.core.leader :=
  ⟨sanitizeAuthorizedTerminalEqual_leader_eq hpsi q.1,
    sanitizeAuthorizedTerminalEqual_leader_eq hpsi q.2⟩

theorem sanitizeAuthorizedPair_labels_eq
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (sanitizeAuthorizedPair hpsi q).1.core.label = q.1.core.label ∧
      (sanitizeAuthorizedPair hpsi q).2.core.label = q.2.core.label :=
  ⟨sanitizeAuthorizedTerminalEqual_label_eq hpsi q.1,
    sanitizeAuthorizedTerminalEqual_label_eq hpsi q.2⟩

theorem authorizedDisappear_leaders_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedDisappear hpsi l r).1.core.leader = l.core.leader ∧
      (authorizedDisappear hpsi l r).2.core.leader = r.core.leader :=
  PPLLVerify.disappear_leaders_eq hpsi l.core r.core

theorem authorizedDisappear_labels_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedDisappear hpsi l r).1.core.label = l.core.label ∧
      (authorizedDisappear hpsi l r).2.core.label = r.core.label :=
  PPLLVerify.disappear_labels_eq hpsi l.core r.core

/-- Leader-birth accounting marks comparison paths but never changes either
physical leader bit. -/
theorem markLeaderBirth_leaders_eq
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (markLeaderBirth born q).1.core.leader = q.1.core.leader ∧
      (markLeaderBirth born q).2.core.leader = q.2.core.leader := by
  unfold markLeaderBirth markComparisonForDeletion
  repeat (first | constructor | rfl | split)

/-- Leader-birth accounting also frames both physical labels. -/
theorem markLeaderBirth_labels_eq
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (markLeaderBirth born q).1.core.label = q.1.core.label ∧
      (markLeaderBirth born q).2.core.label = q.2.core.label := by
  unfold markLeaderBirth markComparisonForDeletion
  repeat (first | constructor | rfl | split)

/-- Authorization reconciliation changes only the proof-only path permission;
both physical leader bits are exactly those of the raw stage. -/
theorem authorizedReconcile_leaders_eq
    (f : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).1.core.leader =
        (f l.core r.core).1.leader ∧
      (authorizedReconcile f l r).2.core.leader =
        (f l.core r.core).2.leader := by
  exact authorizedReconcile_leaders f l r

theorem normalizeDeletion_isBarrier_iff
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    isBarrier hpsi (normalizeDeletion l).core (normalizeDeletion r).core ↔
      isBarrier hpsi l.core r.core := by
  simp only [isBarrier, normalizeDeletion_label_eq]

theorem preCheckResetWall_initiator_anchor
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    InitiatorAnchor (preCheckResetWall l r).1.core := by
  have hview := congrArg Prod.fst (preCheckResetWall_peaceViewPair l r)
  exact ⟨(congrArg PeaceView.leader hview).trans h.1,
    (congrArg PeaceView.shield hview).trans h.2⟩

theorem preCheckResetWall_responder_zero_anchor
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    ResponderZeroAnchor hpsi (preCheckResetWall l r).2.core := by
  have hview := congrArg Prod.snd (preCheckResetWall_peaceViewPair l r)
  exact ⟨(congrArg PeaceView.leader hview).trans h.1,
    (congrArg PeaceView.label hview).trans h.2⟩

theorem preCheckResetWall_initiator_label_eq
    (l r : AuthorizedAgentState psi) :
    (preCheckResetWall l r).1.core.label = l.core.label := by
  have hview := congrArg Prod.fst (preCheckResetWall_peaceViewPair l r)
  exact congrArg PeaceView.label hview

/-- The wall-aware P-prime-psi stage never changes the initiator leader bit. -/
theorem authorizedPPsiLeaderProbeWall_initiator_leader_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedPPsiLeaderProbeWall hpsi l r).1.core.leader =
      l.core.leader := by
  simp [authorizedPPsiLeaderProbeWall, pPsiLeaderProbeWall,
    PPLLVerify.pPsi_initiator_leader_eq]

/-- A follower initiator carrying reset and a follower responder remain two
followers at the reset-aware P-prime boundary.  In particular, a resident
responder probe cannot use a stale barrier to create the first new leader. -/
theorem authorizedPPsiLeaderResetProbeWall_followers_of_reset_source
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let q := authorizedPPsiLeaderResetProbeWall hpsi l r
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  let qAuth := authorizedPPsiLeaderResetProbeWall hpsi l r
  let qRaw := pPsiLeaderResetProbeWall hpsi l.core r.core
  have hraw := pPsiLeaderResetProbeWall_source_follower_normalizes
    hpsi l.core r.core (.inr hlReset) hrFollower
  change qRaw.1.leader = l.core.leader ∧
      qRaw.2.leader = false ∧ _ at hraw
  have hcore := authorizedPPsiLeaderResetProbeWall_core hpsi l r
  change (qAuth.1.core, qAuth.2.core) = qRaw at hcore
  have hleft := congrArg
    (fun q : AgentState psi × AgentState psi => q.1.leader) hcore
  have hright := congrArg
    (fun q : AgentState psi × AgentState psi => q.2.leader) hcore
  change qAuth.1.core.leader = false ∧ qAuth.2.core.leader = false
  exact ⟨hleft.trans (hraw.1.trans hlFollower),
    hright.trans hraw.2.1⟩

/-! ### Prefix theorems through the stage frames

The four prefix theorems below rewrite the prefix into its stages
(`Leader.Wu.WallSweep.StageFrames`), generalize each stage output, and apply the
one-stage frames by syntactic matching.  Chaining whole-prefix facts through
`let`-bound stage outputs made the elaborator reduce the composed protocol
(`whnf` through every earlier stage's `if` conditions): 258 s and 634 s for the
two BeforeCheck theorems, and heartbeat timeouts for the two AfterCheck ones
once their raised limits were removed. -/

open PPLLWallSweepStageFrames (authorizedGenSig_leaders_eq
  authorizedGenSig_labels_eq authorizedCleanSig_leaders_eq
  authorizedCleanSig_labels_eq authorizedEliminateSig_leaders_eq
  authorizedEliminateSig_labels_eq authorizedSigMoveLeaderWall_leaders_eq
  authorizedSigMoveLeaderWall_labels_eq authorizedCheckSig_labels_eq
  wallSweepResetProbeAuthorizedBeforeCheck_stages)

/-- The later GENSIG/CLEAN/ELIMINATE/SIGMOVE stages frame the follower pair
produced by the reset-aware P-prime boundary. -/
theorem wallSweepResetProbeAuthorizedBeforeCheck_followers_of_reset_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let q := wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  have h0 : (authorizedPPsiLeaderResetProbeWall hpsi l r).1.core.leader = false ∧
      (authorizedPPsiLeaderResetProbeWall hpsi l r).2.core.leader = false :=
    authorizedPPsiLeaderResetProbeWall_followers_of_reset_source
      hpsi l r hlFollower hlReset hrFollower
  show (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).1.core.leader =
      false ∧
    (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).2.core.leader =
      false
  rw [wallSweepResetProbeAuthorizedBeforeCheck_stages]
  revert h0
  generalize authorizedPPsiLeaderResetProbeWall hpsi l r = q0
  intro h0
  have h1 := authorizedGenSig_leaders_eq hpsi kappa q0.1 q0.2
  revert h1
  generalize authorizedGenSig hpsi kappa q0.1 q0.2 = q1
  intro h1
  have h2 := authorizedCleanSig_leaders_eq hpsi q1.1 q1.2
  revert h2
  generalize authorizedCleanSig hpsi q1.1 q1.2 = q2
  intro h2
  have h3 := authorizedEliminateSig_leaders_eq hpsi q2.1 q2.2
  revert h3
  generalize authorizedEliminateSig hpsi q2.1 q2.2 = q3
  intro h3
  have h4 := authorizedSigMoveLeaderWall_leaders_eq hpsi q3.1 q3.2
  exact ⟨h4.1.trans (h3.1.trans (h2.1.trans (h1.1.trans h0.1))),
    h4.2.trans (h3.2.trans (h2.2.trans (h1.2.trans h0.2)))⟩

/-- A leader or reset source rewrites a follower responder to the exact
successor label at P'_psi, and every remaining pre-CHECK prefix stage frames
that newly established local alignment. -/
theorem wallSweepResetProbeAuthorizedBeforeCheck_source_follower_labels
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let q := wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r
    q.1.core.label = l.core.label ∧
      q.2.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  have hraw := pPsiLeaderResetProbeWall_source_follower_normalizes
    hpsi l.core r.core hsource hrFollower
  have hcore := authorizedPPsiLeaderResetProbeWall_core hpsi l r
  have h0 : (authorizedPPsiLeaderResetProbeWall hpsi l r).1.core.label =
        l.core.label ∧
      (authorizedPPsiLeaderResetProbeWall hpsi l r).2.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ :=
    ⟨(congrArg
        (fun q : AgentState psi × AgentState psi => q.1.label)
        hcore).trans hraw.2.2.1,
      (congrArg
        (fun q : AgentState psi × AgentState psi => q.2.label)
        hcore).trans hraw.2.2.2.1⟩
  show (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).1.core.label =
      l.core.label ∧
    (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).2.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  rw [wallSweepResetProbeAuthorizedBeforeCheck_stages]
  revert h0
  generalize authorizedPPsiLeaderResetProbeWall hpsi l r = q0
  intro h0
  have h1 := authorizedGenSig_labels_eq hpsi kappa q0.1 q0.2
  revert h1
  generalize authorizedGenSig hpsi kappa q0.1 q0.2 = q1
  intro h1
  have h2 := authorizedCleanSig_labels_eq hpsi q1.1 q1.2
  revert h2
  generalize authorizedCleanSig hpsi q1.1 q1.2 = q2
  intro h2
  have h3 := authorizedEliminateSig_labels_eq hpsi q2.1 q2.2
  revert h3
  generalize authorizedEliminateSig hpsi q2.1 q2.2 = q3
  intro h3
  have h4 := authorizedSigMoveLeaderWall_labels_eq hpsi q3.1 q3.2
  exact ⟨h4.1.trans (h3.1.trans (h2.1.trans (h1.1.trans h0.1))),
    h4.2.trans (h3.2.trans (h2.2.trans (h1.2.trans h0.2)))⟩

private theorem labels_of_authorizedPeaceViewPair_eq
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair q = authorizedPeaceViewPair p) :
    q.1.core.label = p.1.core.label ∧ q.2.core.label = p.2.core.label :=
  ⟨congrArg (fun v : PeaceView psi × PeaceView psi => v.1.label) h,
    congrArg (fun v : PeaceView psi × PeaceView psi => v.2.label) h⟩

/-- The real-CHECK output is CHECK after the sanitized pre-CHECK reset wall,
by definition. -/
private theorem wallSweepResetProbePreCheckResetAfterCheck_stages
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r =
      authorizedCheckSig hpsi
        (sanitizeAuthorizedPair hpsi (preCheckResetWall
          (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).1
          (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).2)).1
        (sanitizeAuthorizedPair hpsi (preCheckResetWall
          (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).1
          (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).2)).2 :=
  rfl

/-- The reset-aware pre-CHECK wall and real CHECK retain the follower pair:
the reset token is framed through the prefix, so both comparison carriers are
cleared before CHECK can perform a birth. -/
theorem
    wallSweepResetProbePreCheckResetAfterCheck_followers_of_reset_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let q := wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  have hfollowers :=
    wallSweepResetProbeAuthorizedBeforeCheck_followers_of_reset_source
      hpsi kappa l r hlFollower hlReset hrFollower
  have hframe := wallSweepResetProbeAuthorizedBeforeCheck_resetEchoPair
    hpsi kappa l r
  have hbeforeReset :
      (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).1.core.reset_cmd =
        true :=
    (resetEcho_fields_of_pair_eq hframe).1.trans hlReset
  show (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).1.core.leader =
      false ∧
    (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).2.core.leader =
      false
  rw [wallSweepResetProbePreCheckResetAfterCheck_stages]
  revert hfollowers hbeforeReset
  generalize wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r = q0
  intro hfollowers hbeforeReset
  have hcheck := preCheckResetWall_check_leaders_eq_of_send
    hpsi q0.1 q0.2 (.inr hbeforeReset)
  exact ⟨hcheck.1.trans hfollowers.1, hcheck.2.trans hfollowers.2⟩

/-- The pre-CHECK reset wall, sanitizer, and real CHECK frame the local
successor labels established by the reset-aware P'_psi prefix. -/
theorem
    wallSweepResetProbePreCheckResetAfterCheck_source_follower_labels
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let q := wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r
    q.1.core.label = l.core.label ∧
      q.2.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  have hraw :=
    wallSweepResetProbeAuthorizedBeforeCheck_source_follower_labels
      hpsi kappa l r hsource hrFollower
  show (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).1.core.label =
      l.core.label ∧
    (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).2.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  rw [wallSweepResetProbePreCheckResetAfterCheck_stages]
  revert hraw
  generalize wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r = q0
  intro hraw
  have hreset := labels_of_authorizedPeaceViewPair_eq
    (preCheckResetWall_peaceViewPair q0.1 q0.2)
  have hsanitize := sanitizeAuthorizedPair_labels_eq hpsi
    (preCheckResetWall q0.1 q0.2)
  have hcheck := authorizedCheckSig_labels_eq hpsi
    (sanitizeAuthorizedPair hpsi (preCheckResetWall q0.1 q0.2)).1
    (sanitizeAuthorizedPair hpsi (preCheckResetWall q0.1 q0.2)).2
  exact ⟨hcheck.1.trans
      (hsanitize.1.trans (hreset.1.trans hraw.1)),
    hcheck.2.trans
      (hsanitize.2.trans (hreset.2.trans hraw.2))⟩

/-- The reset-aware P'_psi prefix, pre-CHECK deletion wall, sanitizer, and
real CHECK frame the complete reset/echo pair. -/
theorem wallSweepResetProbePreCheckResetAfterCheck_resetEchoPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair
        (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r) =
      authorizedResetEchoPair (l, r) := by
  let q0 := wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r
  let qR := preCheckResetWall q0.1 q0.2
  let q1 := sanitizeAuthorizedPair hpsi qR
  let q2 := authorizedCheckSig hpsi q1.1 q1.2
  have h0 := wallSweepResetProbeAuthorizedBeforeCheck_resetEchoPair
    hpsi kappa l r
  have hR := preCheckResetWall_resetEchoPair q0.1 q0.2
  have h1 := sanitizeAuthorizedPair_resetEchoPair hpsi qR
  have h2 := authorizedCheckSig_resetEchoPair hpsi q1.1 q1.2
  change authorizedResetEchoPair q2 = authorizedResetEchoPair (l, r)
  have h2' : authorizedResetEchoPair q2 = authorizedResetEchoPair q1 :=
    authorizedResetEchoPair_eq_trans h2 (authorizedResetEchoPair_eta q1)
  have hR' : authorizedResetEchoPair qR = authorizedResetEchoPair q0 :=
    authorizedResetEchoPair_eq_trans hR (authorizedResetEchoPair_eta q0)
  exact authorizedResetEchoPair_eq_trans h2'
    (authorizedResetEchoPair_eq_trans h1
      (authorizedResetEchoPair_eq_trans hR' h0))

/-- The rooted Algorithm-15/WRITE suffix cannot create a leader from two
follower inputs.  Each possible output leader has an explicit input-leader
origin, and both origins are false here. -/
theorem authorizedPostSuppressLeaderSink_followers_of_followers
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hrFollower : r.core.leader = false) :
    let q := authorizedPostSuppressLeaderSink hpsi l r
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  let out := authorizedPostSuppressLeaderSink hpsi l r
  have horigin := authorizedPostSuppressLeaderSink_leader_origins hpsi l r
  change (out.1.core.leader = true →
      l.core.leader = true ∨ r.core.leader = true) ∧
    (out.2.core.leader = true → r.core.leader = true) at horigin
  constructor
  · rw [← Bool.not_eq_true]
    intro hout
    rcases horigin.1 hout with hleft | hright
    · have hbad : (false : Bool) = true :=
        hlFollower.symm.trans hleft
      simp at hbad
    · have hbad : (false : Bool) = true :=
        hrFollower.symm.trans hright
      simp at hbad
  · rw [← Bool.not_eq_true]
    intro hout
    have hbad : (false : Bool) = true :=
      hrFollower.symm.trans (horigin.2 hout)
    simp at hbad

/-- All post-CHECK stages of the rooted suffix preserve a follower pair. -/
theorem wallSweepLeaderSinkAfterCheckSuffix_followers_of_followers
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hrFollower : r.core.leader = false) :
    let q := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  let q0 := authorizedDisappear hpsi l r
  have h0 : q0.1.core.leader = false ∧ q0.2.core.leader = false :=
    ⟨(authorizedDisappear_leaders_eq hpsi l r).1.trans hlFollower,
      (authorizedDisappear_leaders_eq hpsi l r).2.trans hrFollower⟩
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  have h1 : q1.1.core.leader = false ∧ q1.2.core.leader = false :=
    ⟨(authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).1.trans h0.1,
      (authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).2.trans h0.2⟩
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  have hraw := suppressSigResetKill_leaders_eq
    hpsi q1.1.core q1.2.core
  have h2 : q2.1.core.leader = false ∧ q2.2.core.leader = false :=
    ⟨(authorizedReconcile_leaders_eq
        (suppressSigResetKill hpsi) q1.1 q1.2).1.trans
          (hraw.1.trans h1.1),
      (authorizedReconcile_leaders_eq
        (suppressSigResetKill hpsi) q1.1 q1.2).2.trans
          (hraw.2.trans h1.2)⟩
  have hpost := authorizedPostSuppressLeaderSink_followers_of_followers
    hpsi q2.1 q2.2 h2.1 h2.2
  let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
  let post := authorizedPostSuppressLeaderSink hpsi q2.1 q2.2
  have hstage : out = post := by rfl
  exact ⟨(congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.leader) hstage).trans hpost.1,
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.leader) hstage).trans hpost.2⟩

/-- DISAPPEAR, COMPARE, repaired Algorithm 14, rooted Algorithm 15, and gated
WRITE frame both labels of the real-CHECK output. -/
theorem wallSweepLeaderSinkAfterCheckSuffix_labels_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    let q := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
    q.1.core.label = l.core.label ∧
      q.2.core.label = r.core.label := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedPostSuppressLeaderSink hpsi q2.1 q2.2
  have h0 := authorizedDisappear_labels_eq hpsi l r
  have h1pair :=
    PPLLNoCheckBirthConditionTwoFrames.authorizedCompareSig_labels
      hpsi q0.1 q0.2
  have h1 : q1.1.core.label = q0.1.core.label ∧
      q1.2.core.label = q0.2.core.label :=
    ⟨congrArg Prod.fst h1pair, congrArg Prod.snd h1pair⟩
  have h2 : q2.1.core.label = q1.1.core.label ∧
      q2.2.core.label = q1.2.core.label :=
    ⟨suppressSigResetKill_left_label_eq hpsi q1.1.core q1.2.core,
      suppressSigResetKill_right_label_eq hpsi q1.1.core q1.2.core⟩
  have h3 := authorizedPostSuppressLeaderSink_labels_eq
    hpsi q2.1 q2.2
  change q3.1.core.label = l.core.label ∧
    q3.2.core.label = r.core.label
  exact ⟨h3.1.trans (h2.1.trans (h1.1.trans h0.1)),
    h3.2.trans (h2.2.trans (h1.2.trans h0.2))⟩

/-- The complete rooted post-CHECK suffix migrates an existing nonzero-label
responder leader to the initiator and leaves both labels on their physical
hosts.  Earlier suffix stages frame the responder leader and label; the final
gated WRITE performs the only migration. -/
theorem wallSweepLeaderSinkAfterCheckSuffix_nonzero_responder_migrates
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true)
    (hrNonzero : r.core.label ≠ ⟨0, hpsi⟩) :
    let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
    out.1.core.leader = true ∧
      out.2.core.leader = false ∧
      out.1.core.label = l.core.label ∧
      out.2.core.label = r.core.label := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let out := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
  have hq0Leader : q0.2.core.leader = true :=
    (authorizedDisappear_leaders_eq hpsi l r).2.trans hrLeader
  have hq1Leader : q1.2.core.leader = true :=
    (authorizedCompareSig_leaders_eq hpsi q0.1 q0.2).2.trans hq0Leader
  have hq2Leader : q2.2.core.leader = true :=
    (authorizedReconcile_leaders_eq
      (suppressSigResetKill hpsi) q1.1 q1.2).2.trans
        ((suppressSigResetKill_leaders_eq
          hpsi q1.1.core q1.2.core).2.trans hq1Leader)
  have hq0Label : q0.2.core.label = r.core.label :=
    (authorizedDisappear_labels_eq hpsi l r).2
  have hq1Label : q1.2.core.label = q0.2.core.label := by
    exact congrArg Prod.snd
      (PPLLNoCheckBirthConditionTwoFrames.authorizedCompareSig_labels
        hpsi q0.1 q0.2)
  have hq2Label : q2.2.core.label = r.core.label :=
    (suppressSigResetKill_right_label_eq
      hpsi q1.1.core q1.2.core).trans (hq1Label.trans hq0Label)
  have hq2Nonzero : q2.2.core.label ≠ ⟨0, hpsi⟩ := by
    intro hzero
    exact hrNonzero (hq2Label.symm.trans hzero)
  have hmigrate :=
    authorizedPostSuppressLeaderSink_nonzero_responder_migrates
      hpsi q2.1 q2.2 hq2Leader hq2Nonzero
  change out.1.core.leader = true ∧
    out.2.core.leader = false ∧
    out.1.core.label = q2.1.core.label ∧
    out.2.core.label = q2.2.core.label at hmigrate
  have hlabels := wallSweepLeaderSinkAfterCheckSuffix_labels_eq hpsi l r
  change out.1.core.leader = true ∧
    out.2.core.leader = false ∧
    out.1.core.label = l.core.label ∧
    out.2.core.label = r.core.label
  exact ⟨hmigrate.1, hmigrate.2.1, hlabels.1, hlabels.2⟩


end PPLLWallSweepPreCheckResetContracts

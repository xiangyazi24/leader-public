import Std
import Leader.Wu.Entrance.PassiveAdmission
import Leader.Wu.Splice.InstalledCarrier


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace ZZRecoveryPreempts


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9FullCarrierHost
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceTableV10g B9ControllerRecovery
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C


variable {ψ κ τ : Nat}


private theorem h3 : 0 < 3 := by omega
private theorem h23 : 2 ≤ 3 := by omega


/-! ## The cell, lifted neutrally. -/


def base : ExpiringAgentState 3 3 48 :=
  QuietPairCounterexample.quietBase 0


def r2 : R2.Cell 3 3 48 :=
  ⟨base, 0⟩


def inner : R2CoherenceV31.Cell 3 3 48 :=
  ⟨r2, ⟨.sealed, .none⟩⟩


/-- Both sites of the constant two-ring use this same cell. -/
def cell : ZZFinalCarrierV3.Cell 3 3 48 :=
  ⟨inner, .none, false, false⟩


def liftClosed : ZZFinalCarrierV3.Config 2 3 3 48 :=
  fun _ => cell


private def old : B9SpliceTableHost.Cell 3 3 48 :=
  ZZFinalCarrierV3.oldCellV3 cell


@[simp] private theorem old_role :
    B9SpliceControllerR1Table.role old.carrier = .none := by
  rfl


@[simp] private theorem old_pending :
    old.carrier.repairPending = false := by
  rfl


@[simp] private theorem old_ticket :
    old.acquireTicket = false := by
  rfl


@[simp] private theorem old_raw_leader :
    old.carrier.splice.base.core.core.leader = false := by
  decide +kernel


@[simp] private theorem old_raw_label :
    old.carrier.splice.base.core.core.label = (0 : Fin 3) := by
  decide +kernel


/-! ## Preparation frame, copied from the compiled ZZOrbitLiftClean proof. -/


private theorem normalizeDeletion_leader_local
    (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareDisposal_leader_local
    (hψ : 0 < ψ) (u : AuthorizedAgentState ψ) :
    (prepareDisposal hψ u).core.leader = u.core.leader := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl


private theorem normalizeDeletion_label_local
    (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareDisposal_label_local
    (hψ : 0 < ψ) (u : AuthorizedAgentState ψ) :
    (prepareDisposal hψ u).core.label = u.core.label := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl


private theorem preparedSplice_leader_local
    (hψ : 0 < ψ) (u : SpliceAgentState ψ κ τ) :
    (prepared hψ u).core.leader = u.base.core.core.leader := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hψ u.base.core]
  rw [normalizeDeletion_leader_local, prepareDisposal_leader_local]
  rfl


private theorem preparedSplice_label_local
    (hψ : 0 < ψ) (u : SpliceAgentState ψ κ τ) :
    (prepared hψ u).core.label = u.base.core.core.label := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hψ u.base.core]
  rw [normalizeDeletion_label_local, prepareDisposal_label_local]
  rfl


private theorem preparedR1_leader_local
    (hψ : 0 < ψ) (u : R1AgentStateV4 ψ κ τ) :
    (preparedR1 hψ u).core.leader =
      u.splice.base.core.core.leader := by
  simpa [preparedR1] using
    (preparedSplice_leader_local hψ u.splice)


private theorem preparedR1_label_local
    (hψ : 0 < ψ) (u : R1AgentStateV4 ψ κ τ) :
    (preparedR1 hψ u).core.label =
      u.splice.base.core.core.label := by
  simpa [preparedR1] using
    (preparedSplice_label_local hψ u.splice)


private theorem localDanger_iff_physical
    (hψ : 0 < ψ) (l r : B9SpliceTableHost.Cell ψ κ τ) :
    B9ControllerRecovery.LocalDanger hψ l r ↔
      l.carrier.splice.base.core.core.leader = false ∧
      r.carrier.splice.base.core.core.leader = false ∧
      r.carrier.splice.base.core.core.label ≠
        ⟨(l.carrier.splice.base.core.core.label.val + 1) % ψ,
          Nat.mod_lt _ hψ⟩ := by
  unfold B9ControllerRecovery.LocalDanger
    B9SpliceControllerR1Table.LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  simp only [preparedR1_leader_local, preparedR1_label_local]


/-! ## Positive LocalDanger. -/


private theorem pair_localDanger :
    B9ControllerRecovery.LocalDanger h3 old old := by
  rw [localDanger_iff_physical]
  refine ⟨old_raw_leader, old_raw_leader, ?_⟩
  intro h
  have hv := congrArg Fin.val h
  simp only [old_raw_label] at hv
  change 0 = 1 at hv
  omega


/-! ## Every PairCovered arm is false. -/


private theorem old_not_reservedFront :
    ¬ B9SpliceControllerR1TableV2.ReservedFrontHoldGuard old.carrier := by
  intro h
  have hr := h.1
  rw [old_role] at hr
  cases hr


private theorem old_not_pending :
    ¬ B9ControllerRecovery.Pending old := by
  intro h
  have hr := h.1
  rw [old_role] at hr
  cases hr


private theorem old_not_hostFence :
    ¬ B9SpliceControllerR1TableV7.HostFenceShapeV7 old := by
  intro h
  have ht := h.2.2
  rw [old_ticket] at ht
  cases ht


private theorem old_not_pendingOwnerHold :
    ¬ B9SpliceTableV10g.PendingOwnerHoldShapeV7 old old := by
  intro h
  have hr := h.1
  rw [old_role] at hr
  cases hr


private theorem pair_notCovered :
    ¬ B9ControllerRecovery.PairCovered old old := by
  intro h
  unfold B9ControllerRecovery.PairCovered at h
  rcases h with hMain | hOwner
  · rcases hMain with hCore | hFence
    · rcases hCore with hReserved | hRest
      · exact old_not_reservedFront hReserved
      · rcases hRest with hPending | hPredClear
        · exact old_not_pending hPending
        · have hr := hPredClear.1
          rw [old_role] at hr
          cases hr
    · exact old_not_hostFence hFence
  · exact old_not_pendingOwnerHold hOwner


/-- Requested positive hole theorem. -/
theorem pair_isHole :
    B9ControllerRecovery.Hole h3
      (ZZFinalCarrierV3.oldCellV3 cell)
      (ZZFinalCarrierV3.oldCellV3 cell) := by
  change B9ControllerRecovery.Hole h3 old old
  exact ⟨pair_localDanger, pair_notCovered⟩


/-- Requested Garbage proof: choose the Hole disjunct directly. -/
theorem pair_isGarbage :
    ZZFinalCarrierV3.FinalGarbageV3 h3 cell cell := by
  change B9ControllerRecovery.Garbage h3 old old
  exact Or.inr (by simpa [old] using pair_isHole)


/-! ## Recovery pre-empts the completed B9 port. -/


theorem finalAction_recovers :
    ZZFinalCarrierV3.finalActionV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      cell cell = .recovery := by
  classical
  unfold ZZFinalCarrierV3.finalActionV3
  rw [if_pos pair_isGarbage]


/-! The following three facts strengthen the requested result by showing that
recovery really reaches coverFinalV3, not an earlier scrub branch. -/


private theorem pair_not_badTicket :
    ¬ ZZFinalCarrierV3.FinalBadTicketV3 cell := by
  intro h
  change B9ControllerRecovery.BadTicket old at h
  have ht := h.1
  rw [old_ticket] at ht
  cases ht


private theorem pair_not_badBacking :
    ¬ ZZFinalCarrierV3.FinalBadBackingV3 cell cell := by
  intro h
  change B9ControllerRecovery.BadBacking old old at h
  exact old_not_pending h.1


private theorem pair_isFinalHole :
    ZZFinalCarrierV3.FinalHoleV3 h3 cell cell := by
  change B9ControllerRecovery.Hole h3 old old
  exact ⟨pair_localDanger, pair_notCovered⟩


theorem recoverPair_is_cover :
    ZZFinalCarrierV3.recoverPairV3 h3 cell cell =
      ZZFinalCarrierV3.coverFinalV3 cell cell := by
  classical
  unfold ZZFinalCarrierV3.recoverPairV3
  rw [if_neg pair_not_badTicket, if_neg pair_not_badTicket,
    if_neg pair_not_badBacking, if_pos pair_isFinalHole]


/-! Exact controller write of the recovery cover. -/
theorem coverFinalV3_write :
    (ZZFinalCarrierV3.coverFinalV3 cell cell).1.spliceRole =
        .predecessorArmed ∧
    (ZZFinalCarrierV3.coverFinalV3 cell cell).1.repairPending = true ∧
    (ZZFinalCarrierV3.coverFinalV3 cell cell).1.acquireTicket = false ∧
    (ZZFinalCarrierV3.coverFinalV3 cell cell).2.spliceRole = .front ∧
    (ZZFinalCarrierV3.coverFinalV3 cell cell).2.repairPending = true ∧
    (ZZFinalCarrierV3.coverFinalV3 cell cell).2.acquireTicket = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Requested movement theorem. -/
theorem coverFinalV3_moves :
    ZZFinalCarrierV3.coverFinalV3 cell cell ≠ (cell, cell) := by
  intro h
  have hr := congrArg
    (fun q : ZZFinalCarrierV3.Cell 3 3 48 ×
      ZZFinalCarrierV3.Cell 3 3 48 => q.1.spliceRole) h
  change SpliceRole.predecessorArmed = SpliceRole.none at hr
  cases hr


/-- Stronger capstone: the installed local final row really moves this pair. -/
theorem rowFinal_recovers :
    ZZFinalCarrierV3.rowFinalV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      cell cell = ZZFinalCarrierV3.coverFinalV3 cell cell := by
  unfold ZZFinalCarrierV3.rowFinalV3
  rw [finalAction_recovers]
  exact recoverPair_is_cover


theorem rowFinal_moves :
    ZZFinalCarrierV3.rowFinalV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      cell cell ≠ (cell, cell) := by
  rw [rowFinal_recovers]
  exact coverFinalV3_moves


#print axioms ZZRecoveryPreempts.pair_isHole
#print axioms ZZRecoveryPreempts.pair_isGarbage
#print axioms ZZRecoveryPreempts.finalAction_recovers
#print axioms ZZRecoveryPreempts.coverFinalV3_moves
#print axioms ZZRecoveryPreempts.rowFinal_moves


end ZZRecoveryPreempts

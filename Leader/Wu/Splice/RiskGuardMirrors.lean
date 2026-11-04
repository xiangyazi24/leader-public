import Leader.Wu.Splice.RiskAbstraction

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9RiskRefinement

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g
open B9Host B9SpliceTableHost B9RiskAbstraction

variable {psi kappa tau : Nat}

/-! The preparation cut preserves exactly the two physical coordinates used by
`LocalPreparedBarrier`.  This is the same small frame used in the existing B9
risk proofs; no row definition is opened here. -/

private theorem normalizeDeletion_leader_ref (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl

private theorem prepareDisposal_leader_ref
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.leader = u.core.leader := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

private theorem normalizeDeletion_label_ref (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl

private theorem prepareDisposal_label_ref
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.label = u.core.label := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

private theorem preparedR1_leader_ref
    (hpsi : 0 < psi) (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.leader = u.splice.base.core.core.leader := by
  unfold preparedR1 prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.splice.base.core]
  rw [normalizeDeletion_leader_ref, prepareDisposal_leader_ref]
  rfl

private theorem preparedR1_label_ref
    (hpsi : 0 < psi) (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.label = u.splice.base.core.core.label := by
  unfold preparedR1 prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.splice.base.core]
  rw [normalizeDeletion_label_ref, prepareDisposal_label_ref]
  rfl

private def RawLocalBarrier
    (l r : Phys psi kappa tau) : Prop :=
  B9Host.leader r = false ∧ ¬ B9Host.Aligned l r

/-- Source guard: `LocalPreparedBarrier`,
`Leader/Wu/Splice/MovingFrontTable.lean:93-99`.
This is support for the guard lemmas below, not a row/host expansion. -/
private theorem localPreparedBarrier_iff_raw
    (hpsi : 0 < psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    LocalPreparedBarrier hpsi l r ↔
      RawLocalBarrier l.splice.base r.splice.base := by
  change
    ((preparedR1 hpsi r).core.leader = false ∧
      isBarrier hpsi (preparedR1 hpsi l).core (preparedR1 hpsi r).core) ↔
      RawLocalBarrier l.splice.base r.splice.base
  unfold RawLocalBarrier B9Host.Aligned B9Host.leader B9Host.label
  unfold isBarrier
  simp only [preparedR1_leader_ref, preparedR1_label_ref]
  constructor
  · rintro ⟨hr, hne⟩
    refine ⟨hr, ?_⟩
    intro hv
    apply hne
    apply Fin.ext
    exact hv
  · rintro ⟨hr, hne⟩
    refine ⟨hr, ?_⟩
    intro hf
    apply hne
    exact congrArg Fin.val hf

private theorem decide_false_iff_not (P : Prop) [Decidable P] :
    decide P = false ↔ ¬ P := by
  by_cases h : P <;> simp [h]

/-! Public Prop-valued mirrors of the private Boolean selector vocabulary in
`B9RiskAbstraction`.  A Prop mirror is convenient because the concrete tables
also branch on Props. -/

def absReservedFront (c : AbsController) : Prop :=
  c.spliceRole = .front ∧ c.repairPending = true

def absHostFence (c : AbsController) : Prop :=
  c.spliceRole = .none ∧ c.repairPending = false ∧ c.acquireTicket = true

def absTargetClear (c : AbsController) : Prop :=
  c.spliceRole = .none ∧ c.repairPending = false

def absPendingPred (c : AbsController) : Prop :=
  c.spliceRole = .predecessorArmed ∧ c.repairPending = true

def absSettledPred (c : AbsController) : Prop :=
  c.spliceRole = .predecessorArmed ∧ c.repairPending = false

def absVictimPending (c : AbsController) : Prop :=
  c.spliceRole = .victimArmed ∧ c.repairPending = true

def absVictimClear (c : AbsController) : Prop :=
  c.spliceRole = .victimArmed ∧ c.repairPending = false

def absFrontClear (c : AbsController) : Prop :=
  c.spliceRole = .front ∧ c.repairPending = false

def absMalformedPending (c : AbsController) : Prop :=
  c.repairPending = true ∧
    c.spliceRole ≠ .predecessorArmed ∧
    c.spliceRole ≠ .front ∧
    c.spliceRole ≠ .victimArmed

def absGuardLdc (v : RiskView) : Prop :=
  v.inLeaderL = true ∧ v.hostLeaderL = false

def absGuardLocalBarrier (v : RiskView) : Prop :=
  v.inLeaderR = false ∧ v.alignedBefore = false

def absGuardMoveAcquireFront (v : RiskView) : Prop :=
  absReservedFront v.left ∧ v.inLeaderL = false ∧
  v.left.acquireTicket = true ∧ absReservedFront v.right ∧
  v.inLeaderR = false ∧ v.right.acquireTicket = false ∧
  ¬ absGuardLocalBarrier v

def absGuardArmA (v : RiskView) : Prop :=
  v.left.spliceRole = .none ∧ v.right.spliceRole = .none ∧
  v.left.repairPending = false ∧ v.right.repairPending = false ∧
  absGuardLdc v

def absGuardArmB (v : RiskView) : Prop :=
  v.left.spliceRole = .none ∧ v.left.repairPending = false ∧
  v.right.spliceRole = .victimArmed ∧ v.right.repairPending = false ∧
  v.inLeaderR = true

def absGuardDelete (v : RiskView) : Prop :=
  v.left.spliceRole = .front ∧ v.right.spliceRole = .front ∧
  v.left.repairPending = false ∧ v.right.repairPending = false ∧
  absGuardLdc v

def absGuardPendingHold (v : RiskView) : Prop :=
  v.left.spliceRole = .victimArmed ∧ v.right.spliceRole = .front ∧
  v.left.repairPending = false ∧ v.right.repairPending = false ∧
  absGuardLdc v

def absGuardPendingAbort (v : RiskView) : Prop :=
  v.left.spliceRole = .victimArmed ∧ v.right.spliceRole = .front ∧
  v.left.repairPending = false ∧ v.right.repairPending = false ∧
  v.inLeaderL = true ∧ ¬ absGuardLdc v

def absGuardMoveCommit (v : RiskView) : Prop :=
  absSettledPred v.left ∧ absPendingPred v.right ∧ v.inLeaderR = false

def absGuardMoveStop (v : RiskView) : Prop :=
  absSettledPred v.left ∧ absReservedFront v.right ∧
  ¬ absGuardLocalBarrier v

def absGuardMoveSeek (v : RiskView) : Prop :=
  absSettledPred v.left ∧ absReservedFront v.right ∧
  absGuardLocalBarrier v

def absGuardMoveSeekHold (v : RiskView) : Prop :=
  absSettledPred v.left ∧ absVictimPending v.right ∧ v.inLeaderR = false

def absGuardPendingOwnerAbort (v : RiskView) : Prop :=
  absPendingPred v.right ∧ ¬ absSettledPred v.left

def absGuardPendingOwnerHold (v : RiskView) : Prop :=
  absPendingPred v.left

def absGuardMoveAcquireLegacy (v : RiskView) : Prop :=
  absVictimPending v.left ∧ v.inLeaderL = false ∧
  absReservedFront v.right ∧ v.right.acquireTicket = false

def absGuardMoveAcquireAbort (v : RiskView) : Prop :=
  absVictimPending v.left ∧ v.inLeaderL = false ∧
  ¬ absReservedFront v.right

def absGuardOrphanReservedFront (v : RiskView) : Prop :=
  absReservedFront v.right ∧ v.left.spliceRole ≠ .predecessorArmed

def absGuardMarkedHold (v : RiskView) : Prop :=
  v.left.spliceRole ≠ .none ∨
    (v.right.spliceRole ≠ .none ∧
      (v.left.repairPending = true ∨ v.right.repairPending = true))

def absGuardRightStale (v : RiskView) : Prop :=
  v.left.spliceRole = .none ∧ v.left.repairPending = false ∧
  v.left.acquireTicket = false ∧
  v.right.spliceRole = .predecessorArmed ∧
  v.right.repairPending = false ∧ v.right.acquireTicket = false

def absGuardFenceBusy (v : RiskView) : Prop :=
  absHostFence v.left ∧ absGuardLocalBarrier v ∧ absReservedFront v.right

def absGuardFenceAdvance (v : RiskView) : Prop :=
  absHostFence v.left ∧ absGuardLocalBarrier v ∧ absTargetClear v.right

def absGuardOrphanVictim (v : RiskView) : Prop :=
  absVictimPending v.right ∧ ¬ absSettledPred v.left

def absGuardOwnedPendingVictim (v : RiskView) : Prop :=
  absSettledPred v.left ∧ absVictimPending v.right

def absGuardOwnerlessPendingPred (v : RiskView) : Prop :=
  v.left.spliceRole = .none ∧ absPendingPred v.right

def absGuardLeftScrub (v : RiskView) : Prop :=
  absVictimClear v.left ∨ absFrontClear v.left ∨ absMalformedPending v.left

def absGuardLeftPred (v : RiskView) : Prop :=
  v.left.spliceRole = .predecessorArmed

def absGuardLeftFront (v : RiskView) : Prop :=
  v.left.spliceRole = .front

def absGuardRightPred (v : RiskView) : Prop :=
  v.right.spliceRole = .predecessorArmed

def absGuardRightPending (v : RiskView) : Prop :=
  v.right.repairPending = true

def absGuardRow10dgStutters (v : RiskView) : Bool :=
  v.row10dgStutters

/-- `Leader/Wu/Splice/HostTable.lean:58-61`. -/
theorem guard_ldc_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    B9SpliceTableHost.ldc host l.carrier r.carrier =
      absGuardLdc (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardLdc B9RiskAbstraction.riskViewOf
  rfl

theorem guard_localPreparedBarrier_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    LocalPreparedBarrier hpsi l.carrier r.carrier =
      absGuardLocalBarrier (riskViewOf host hpsi l r) := by
  apply propext
  rw [localPreparedBarrier_iff_raw]
  unfold absGuardLocalBarrier B9RiskAbstraction.riskViewOf RawLocalBarrier
  change
    (B9Host.leader (B9SpliceTableHost.base r) = false ∧
      ¬ B9Host.Aligned (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)) ↔
    (B9Host.leader (B9SpliceTableHost.base r) = false ∧
      decide (B9Host.Aligned
        (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)) = false)
  constructor
  · rintro ⟨hr, hnot⟩
    refine ⟨hr, ?_⟩
    by_cases h : B9Host.Aligned
        (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)
    · exact False.elim (hnot h)
    · simp [h]
  · rintro ⟨hr, hdec⟩
    refine ⟨hr, ?_⟩
    by_cases h : B9Host.Aligned
        (B9SpliceTableHost.base l) (B9SpliceTableHost.base r)
    · simp [h] at hdec
    · exact h

/-- `ReservedFrontHoldGuard`, `Leader/Wu/Splice/ReservedFrontTable.lean:36-38`. -/
theorem guard_reservedFront_left_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    ReservedFrontHoldGuard l.carrier =
      absReservedFront (riskViewOf host hpsi l r).left := by
  apply propext
  unfold absReservedFront B9RiskAbstraction.riskViewOf
  rfl

/-- `ReservedFrontHoldGuard`, `Leader/Wu/Splice/ReservedFrontTable.lean:36-38`. -/
theorem guard_reservedFront_right_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    ReservedFrontHoldGuard r.carrier =
      absReservedFront (riskViewOf host hpsi l r).right := by
  apply propext
  unfold absReservedFront B9RiskAbstraction.riskViewOf
  rfl

/-- `HostFenceShapeV7`, `Leader/Wu/Splice/HostFenceTable.lean:30-34`. -/
theorem guard_hostFence_left_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    HostFenceShapeV7 l = absHostFence (riskViewOf host hpsi l r).left := by
  apply propext
  unfold absHostFence B9RiskAbstraction.riskViewOf
  rfl

/-- `HostFenceShapeV7`, `Leader/Wu/Splice/HostFenceTable.lean:30-34`. -/
theorem guard_hostFence_right_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    HostFenceShapeV7 r = absHostFence (riskViewOf host hpsi l r).right := by
  apply propext
  unfold absHostFence B9RiskAbstraction.riskViewOf
  rfl

/-- `HostFenceTargetClearV7`, `Leader/Wu/Splice/HostFenceTable.lean:270-273`. -/
theorem guard_hostFenceTargetClear_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    HostFenceTargetClearV7 r = absTargetClear (riskViewOf host hpsi l r).right := by
  apply propext
  unfold absTargetClear B9RiskAbstraction.riskViewOf
  rfl

theorem guard_moveAcquireFront_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MoveAcquireFrontGuardV6 hpsi l r =
      absGuardMoveAcquireFront (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardMoveAcquireFront
  rw [← guard_reservedFront_left_eq_abs host hpsi l r,
    ← guard_reservedFront_right_eq_abs host hpsi l r,
    ← guard_localPreparedBarrier_eq_abs host hpsi l r]
  change
    (ReservedFrontHoldGuard l.carrier ∧
      l.carrier.splice.base.core.core.leader = false ∧
      l.acquireTicket = true ∧
      ReservedFrontHoldGuard r.carrier ∧
      r.carrier.splice.base.core.core.leader = false ∧
      r.acquireTicket = false ∧
      ¬ LocalPreparedBarrier hpsi l.carrier r.carrier) ↔
    (ReservedFrontHoldGuard l.carrier ∧
      l.carrier.splice.base.core.core.leader = false ∧
      l.acquireTicket = true ∧
      ReservedFrontHoldGuard r.carrier ∧
      r.carrier.splice.base.core.core.leader = false ∧
      r.acquireTicket = false ∧
      ¬ LocalPreparedBarrier hpsi l.carrier r.carrier)
  rfl

/-- `ArmAGuardH`, `Leader/Wu/Splice/HostTable.lean:65-69`. -/
theorem guard_armA_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    B9SpliceTableHost.ArmAGuardH host l.carrier r.carrier =
      absGuardArmA (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardArmA absGuardLdc B9RiskAbstraction.riskViewOf
  rfl

/-- `ArmBGuard`, `Leader/Wu/Splice/MovingFrontTable.lean:151-157`. -/
theorem guard_armB_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    ArmBGuard l.carrier r.carrier =
      absGuardArmB (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardArmB B9RiskAbstraction.riskViewOf
  rfl

/-- `DeleteGuardH`, `Leader/Wu/Splice/HostTable.lean:72-76`. -/
theorem guard_delete_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    B9SpliceTableHost.DeleteGuardH host l.carrier r.carrier =
      absGuardDelete (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardDelete absGuardLdc B9RiskAbstraction.riskViewOf
  rfl

/-- `PendingHoldGuardH`, `Leader/Wu/Splice/HostTable.lean:79-83`. -/
theorem guard_pendingHold_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    B9SpliceTableHost.PendingHoldGuardH host l.carrier r.carrier =
      absGuardPendingHold (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardPendingHold absGuardLdc B9RiskAbstraction.riskViewOf
  rfl

/-- `PendingAbortGuardH`, `Leader/Wu/Splice/HostTable.lean:86-91`. -/
theorem guard_pendingAbort_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    B9SpliceTableHost.PendingAbortGuardH host l.carrier r.carrier =
      absGuardPendingAbort (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardPendingAbort absGuardLdc B9RiskAbstraction.riskViewOf
  rfl

theorem guard_moveCommit_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MoveCommitGuard l.carrier r.carrier =
      absGuardMoveCommit (riskViewOf host hpsi l r) := by
  apply propext
  unfold MoveCommitGuard absGuardMoveCommit absSettledPred absPendingPred
    B9RiskAbstraction.riskViewOf
  change
    (role l.carrier = .predecessorArmed ∧
      l.carrier.repairPending = false ∧
      role r.carrier = .predecessorArmed ∧
      r.carrier.repairPending = true ∧
      r.carrier.splice.base.core.core.leader = false) ↔
    ((role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false) ∧
      (role r.carrier = .predecessorArmed ∧
        r.carrier.repairPending = true) ∧
      r.carrier.splice.base.core.core.leader = false)
  constructor
  · rintro ⟨hlr, hlp, hrr, hrp, hlead⟩
    exact ⟨⟨hlr, hlp⟩, ⟨hrr, hrp⟩, hlead⟩
  · rintro ⟨⟨hlr, hlp⟩, ⟨hrr, hrp⟩, hlead⟩
    exact ⟨hlr, hlp, hrr, hrp, hlead⟩

theorem guard_moveStop_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MoveStopGuardV3 hpsi l.carrier r.carrier =
      absGuardMoveStop (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardMoveStop
  rw [← guard_reservedFront_right_eq_abs host hpsi l r,
    ← guard_localPreparedBarrier_eq_abs host hpsi l r]
  unfold MoveStopGuardV3 absSettledPred B9RiskAbstraction.riskViewOf
  change
    (role l.carrier = .predecessorArmed ∧
      l.carrier.repairPending = false ∧
      ReservedFrontHoldGuard r.carrier ∧
      ¬ LocalPreparedBarrier hpsi l.carrier r.carrier) ↔
    ((role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false) ∧
      ReservedFrontHoldGuard r.carrier ∧
      ¬ LocalPreparedBarrier hpsi l.carrier r.carrier)
  constructor
  · rintro ⟨hr, hp, hf, hb⟩
    exact ⟨⟨hr, hp⟩, hf, hb⟩
  · rintro ⟨⟨hr, hp⟩, hf, hb⟩
    exact ⟨hr, hp, hf, hb⟩

theorem guard_moveSeek_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MoveSeekGuardV3 hpsi l.carrier r.carrier =
      absGuardMoveSeek (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardMoveSeek
  rw [← guard_reservedFront_right_eq_abs host hpsi l r,
    ← guard_localPreparedBarrier_eq_abs host hpsi l r]
  unfold MoveSeekGuardV3 absSettledPred B9RiskAbstraction.riskViewOf
  change
    (role l.carrier = .predecessorArmed ∧
      l.carrier.repairPending = false ∧
      ReservedFrontHoldGuard r.carrier ∧
      LocalPreparedBarrier hpsi l.carrier r.carrier) ↔
    ((role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false) ∧
      ReservedFrontHoldGuard r.carrier ∧
      LocalPreparedBarrier hpsi l.carrier r.carrier)
  constructor
  · rintro ⟨hr, hp, hf, hb⟩
    exact ⟨⟨hr, hp⟩, hf, hb⟩
  · rintro ⟨⟨hr, hp⟩, hf, hb⟩
    exact ⟨hr, hp, hf, hb⟩

theorem guard_moveSeekHold_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MoveSeekHoldGuardV3 l.carrier r.carrier =
      absGuardMoveSeekHold (riskViewOf host hpsi l r) := by
  apply propext
  unfold MoveSeekHoldGuardV3 absGuardMoveSeekHold absSettledPred
    absVictimPending B9RiskAbstraction.riskViewOf
  change
    (role l.carrier = .predecessorArmed ∧
      l.carrier.repairPending = false ∧
      role r.carrier = .victimArmed ∧
      r.carrier.repairPending = true ∧
      r.carrier.splice.base.core.core.leader = false) ↔
    ((role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false) ∧
      (role r.carrier = .victimArmed ∧
        r.carrier.repairPending = true) ∧
      r.carrier.splice.base.core.core.leader = false)
  constructor
  · rintro ⟨hlr, hlp, hrr, hrp, hlead⟩
    exact ⟨⟨hlr, hlp⟩, ⟨hrr, hrp⟩, hlead⟩
  · rintro ⟨⟨hlr, hlp⟩, ⟨hrr, hrp⟩, hlead⟩
    exact ⟨hlr, hlp, hrr, hrp, hlead⟩

theorem guard_pendingOwnerAbort_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    PendingOwnerAbortGuardV3 l.carrier r.carrier =
      absGuardPendingOwnerAbort (riskViewOf host hpsi l r) := by
  apply propext
  unfold PendingOwnerAbortGuardV3 absGuardPendingOwnerAbort absPendingPred
    absSettledPred B9RiskAbstraction.riskViewOf
  change
    (role r.carrier = .predecessorArmed ∧
      r.carrier.repairPending = true ∧
      ¬ (role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false)) ↔
    ((role r.carrier = .predecessorArmed ∧
        r.carrier.repairPending = true) ∧
      ¬ (role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false))
  constructor
  · rintro ⟨hrr, hrp, hnot⟩
    exact ⟨⟨hrr, hrp⟩, hnot⟩
  · rintro ⟨⟨hrr, hrp⟩, hnot⟩
    exact ⟨hrr, hrp, hnot⟩

/-- Raw pending-owner HOLD test in `row7H`, `Leader/Wu/Splice/HostTable.lean:158-159`. -/
theorem guard_pendingOwnerHold_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) =
      absGuardPendingOwnerHold (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardPendingOwnerHold absPendingPred B9RiskAbstraction.riskViewOf
  rfl

theorem guard_moveAcquireLegacy_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MoveAcquireLegacyGuardV6 l r =
      absGuardMoveAcquireLegacy (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardMoveAcquireLegacy
  rw [← guard_reservedFront_right_eq_abs host hpsi l r]
  unfold MoveAcquireLegacyGuardV6 MoveAcquireGuardV3 absVictimPending
    B9RiskAbstraction.riskViewOf
  change
    ((role l.carrier = .victimArmed ∧
        l.carrier.repairPending = true ∧
        l.carrier.splice.base.core.core.leader = false ∧
        ReservedFrontHoldGuard r.carrier) ∧
      r.acquireTicket = false) ↔
    ((role l.carrier = .victimArmed ∧
        l.carrier.repairPending = true) ∧
      l.carrier.splice.base.core.core.leader = false ∧
      ReservedFrontHoldGuard r.carrier ∧
      r.acquireTicket = false)
  constructor
  · rintro ⟨⟨hlr, hlp, hlead, hrf⟩, ht⟩
    exact ⟨⟨hlr, hlp⟩, hlead, hrf, ht⟩
  · rintro ⟨⟨hlr, hlp⟩, hlead, hrf, ht⟩
    exact ⟨⟨hlr, hlp, hlead, hrf⟩, ht⟩

theorem guard_moveAcquireAbort_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MoveAcquireAbortGuardV3 l.carrier r.carrier =
      absGuardMoveAcquireAbort (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardMoveAcquireAbort
  rw [← guard_reservedFront_right_eq_abs host hpsi l r]
  unfold MoveAcquireAbortGuardV3 absVictimPending B9RiskAbstraction.riskViewOf
  change
    (role l.carrier = .victimArmed ∧
      l.carrier.repairPending = true ∧
      l.carrier.splice.base.core.core.leader = false ∧
      ¬ ReservedFrontHoldGuard r.carrier) ↔
    ((role l.carrier = .victimArmed ∧
        l.carrier.repairPending = true) ∧
      l.carrier.splice.base.core.core.leader = false ∧
      ¬ ReservedFrontHoldGuard r.carrier)
  constructor
  · rintro ⟨hlr, hlp, hlead, hnot⟩
    exact ⟨⟨hlr, hlp⟩, hlead, hnot⟩
  · rintro ⟨⟨hlr, hlp⟩, hlead, hnot⟩
    exact ⟨hlr, hlp, hlead, hnot⟩

/-- `OrphanReservedFrontGuardV3`, `Leader/Wu/Splice/MoveLeaseTable.lean:91-94`. -/
theorem guard_orphanReservedFront_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    OrphanReservedFrontGuardV3 l.carrier r.carrier =
      absGuardOrphanReservedFront (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardOrphanReservedFront absReservedFront
    B9RiskAbstraction.riskViewOf
  rfl

/-- `VictimRightScrubGuardV6`, `Leader/Wu/Splice/ProvenanceTicketTable.lean:346-349`. -/
theorem guard_victimRightScrub_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    VictimRightScrubGuardV6 r =
      absVictimClear (riskViewOf host hpsi l r).right := by
  apply propext
  unfold absVictimClear B9RiskAbstraction.riskViewOf
  rfl

/-- `VictimLeftScrubGuardV6`, `Leader/Wu/Splice/ProvenanceTicketTable.lean:351-353`. -/
theorem guard_victimLeftScrub_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    VictimLeftScrubGuardV6 l =
      absVictimClear (riskViewOf host hpsi l r).left := by
  apply propext
  unfold absVictimClear B9RiskAbstraction.riskViewOf
  rfl

/-- `FrontRightScrubGuardV6`, `Leader/Wu/Splice/ProvenanceTicketTable.lean:356-359`. -/
theorem guard_frontRightScrub_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    FrontRightScrubGuardV6 r =
      absFrontClear (riskViewOf host hpsi l r).right := by
  apply propext
  unfold absFrontClear B9RiskAbstraction.riskViewOf
  rfl

/-- `MalformedLeftPendingGuardV6`, `Leader/Wu/Splice/ProvenanceTicketTable.lean:361-366`. -/
theorem guard_malformedLeft_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MalformedLeftPendingGuardV6 l =
      absMalformedPending (riskViewOf host hpsi l r).left := by
  apply propext
  unfold absMalformedPending B9RiskAbstraction.riskViewOf
  rfl

/-- `MalformedRightPendingGuardV6`, `Leader/Wu/Splice/ProvenanceTicketTable.lean:368-373`. -/
theorem guard_malformedRight_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MalformedRightPendingGuardV6 r =
      absMalformedPending (riskViewOf host hpsi l r).right := by
  apply propext
  unfold absMalformedPending B9RiskAbstraction.riskViewOf
  rfl

/-- Raw predecessor-left scrub test in `row7H`, `Leader/Wu/Splice/HostTable.lean:169`. -/
theorem guard_leftPred_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (role l.carrier = .predecessorArmed) =
      absGuardLeftPred (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardLeftPred B9RiskAbstraction.riskViewOf
  rfl

/-- Raw left-front HOLD test in `row7H`, `Leader/Wu/Splice/HostTable.lean:170`. -/
theorem guard_leftFront_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (role l.carrier = .front) =
      absGuardLeftFront (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardLeftFront B9RiskAbstraction.riskViewOf
  rfl

/-- `MarkedHoldGuardV6`, `Leader/Wu/Splice/ProvenanceTicketTable.lean:375-379`. -/
theorem guard_markedHold_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MarkedHoldGuardV6 l r =
      absGuardMarkedHold (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardMarkedHold B9RiskAbstraction.riskViewOf
  rfl

/-- `RightStalePredecessorHoldGuardV8`, `Leader/Wu/Splice/StaleHoldTable.lean:28-36`. -/
theorem guard_rightStale_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    RightStalePredecessorHoldGuardV8 l r =
      absGuardRightStale (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardRightStale B9RiskAbstraction.riskViewOf
  rfl

theorem guard_fenceBusy_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    HostFenceBusyFrontGuardV9 hpsi l r =
      absGuardFenceBusy (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardFenceBusy
  rw [← guard_hostFence_left_eq_abs host hpsi l r,
    ← guard_localPreparedBarrier_eq_abs host hpsi l r,
    ← guard_reservedFront_right_eq_abs host hpsi l r]
  unfold HostFenceBusyFrontGuardV9
  rfl

theorem guard_fenceAdvance_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    HostFenceAdvanceGuardV10b hpsi l r =
      absGuardFenceAdvance (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardFenceAdvance
  rw [← guard_hostFence_left_eq_abs host hpsi l r,
    ← guard_localPreparedBarrier_eq_abs host hpsi l r,
    ← guard_hostFenceTargetClear_eq_abs host hpsi l r]
  unfold HostFenceAdvanceGuardV10b
  rfl

theorem guard_orphanVictim_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    OrphanVictimGuard l r =
      absGuardOrphanVictim (riskViewOf host hpsi l r) := by
  apply propext
  unfold OrphanVictimGuard absGuardOrphanVictim absVictimPending
    absSettledPred B9RiskAbstraction.riskViewOf
  change
    (role r.carrier = .victimArmed ∧
      r.carrier.repairPending = true ∧
      ¬ (role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false)) ↔
    ((role r.carrier = .victimArmed ∧
        r.carrier.repairPending = true) ∧
      ¬ (role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false))
  constructor
  · rintro ⟨hrr, hrp, hnot⟩
    exact ⟨⟨hrr, hrp⟩, hnot⟩
  · rintro ⟨⟨hrr, hrp⟩, hnot⟩
    exact ⟨hrr, hrp, hnot⟩

theorem guard_ownedPendingVictim_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    OwnedPendingVictimGuard l r =
      absGuardOwnedPendingVictim (riskViewOf host hpsi l r) := by
  apply propext
  unfold OwnedPendingVictimGuard absGuardOwnedPendingVictim absSettledPred
    absVictimPending B9RiskAbstraction.riskViewOf
  change
    (role l.carrier = .predecessorArmed ∧
      l.carrier.repairPending = false ∧
      role r.carrier = .victimArmed ∧
      r.carrier.repairPending = true) ↔
    ((role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = false) ∧
      (role r.carrier = .victimArmed ∧
        r.carrier.repairPending = true))
  constructor
  · rintro ⟨hlr, hlp, hrr, hrp⟩
    exact ⟨⟨hlr, hlp⟩, ⟨hrr, hrp⟩⟩
  · rintro ⟨⟨hlr, hlp⟩, ⟨hrr, hrp⟩⟩
    exact ⟨hlr, hlp, hrr, hrp⟩

/-- `OwnerlessPendingPredGuard`, `Leader/Wu/Splice/OrphanToFence.lean:250-252`. -/
theorem guard_ownerlessPendingPred_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    OwnerlessPendingPredGuard l r =
      absGuardOwnerlessPendingPred (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardOwnerlessPendingPred absPendingPred
    B9RiskAbstraction.riskViewOf
  rfl

/-- Exact full-state selector carried explicitly by `RiskView`;
concrete use: `Leader/Wu/Splice/HostTable.lean:225-229`. -/
theorem guard_row10dgStutters_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    decide (B9SpliceTableHost.row10dgH host hpsi l r = (l, r)) =
      absGuardRow10dgStutters (riskViewOf host hpsi l r) := by
  unfold absGuardRow10dgStutters B9RiskAbstraction.riskViewOf
  rfl

/-- Raw pending-predecessor HOLD test in `row10gH`,
`Leader/Wu/Splice/HostTable.lean:229`. -/
theorem guard_row10gPendingOwnerHold_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) =
      absGuardPendingOwnerHold (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardPendingOwnerHold absPendingPred B9RiskAbstraction.riskViewOf
  rfl

/-- `VictimRightScrubGuardV6`, concrete use `Leader/Wu/Splice/HostTable.lean:230`. -/
theorem guard_row10gVictimRight_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    VictimRightScrubGuardV6 r =
      absVictimClear (riskViewOf host hpsi l r).right :=
  guard_victimRightScrub_eq_abs host hpsi l r

/-- `FrontRightScrubGuardV6`, concrete use `Leader/Wu/Splice/HostTable.lean:231`. -/
theorem guard_row10gFrontRight_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    FrontRightScrubGuardV6 r =
      absFrontClear (riskViewOf host hpsi l r).right :=
  guard_frontRightScrub_eq_abs host hpsi l r

/-- `MalformedRightPendingGuardV6`, concrete use `Leader/Wu/Splice/HostTable.lean:232`. -/
theorem guard_row10gMalformedRight_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    MalformedRightPendingGuardV6 r =
      absMalformedPending (riskViewOf host hpsi l r).right :=
  guard_malformedRight_eq_abs host hpsi l r

/-- Raw right-predecessor selector, `Leader/Wu/Splice/HostTable.lean:233`. -/
theorem guard_rightPred_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (role r.carrier = .predecessorArmed) =
      absGuardRightPred (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardRightPred B9RiskAbstraction.riskViewOf
  rfl

/-- Raw right-pending selector, `Leader/Wu/Splice/HostTable.lean:234`. -/
theorem guard_rightPending_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (r.carrier.repairPending = true) =
      absGuardRightPending (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardRightPending B9RiskAbstraction.riskViewOf
  rfl

/-- `LeftScrubGuardV10e`, concrete use `Leader/Wu/Splice/HostTable.lean:236`. -/
theorem guard_leftScrub_eq_abs
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    LeftScrubGuardV10e l =
      absGuardLeftScrub (riskViewOf host hpsi l r) := by
  apply propext
  unfold absGuardLeftScrub absVictimClear absFrontClear absMalformedPending
    B9RiskAbstraction.riskViewOf
  rfl

/-! `ZeroRefreshOnlyGuardH`, `Leader/Wu/Splice/HostTable.lean:192-199`, has no
abstract selector theorem here on purpose.  The current abstraction defines
`absRow10c := absRow10b`; therefore a theorem claiming equality to an abstract
branch guard would be false as a statement about branch identity.  Its correct
obligation is `SameExceptStall` output equivalence in the next layer. -/

end B9RiskRefinement

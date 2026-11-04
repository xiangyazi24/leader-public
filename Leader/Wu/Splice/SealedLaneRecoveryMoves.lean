import Std
import Leader.Wu.Splice.InstalledRecoveryStep

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZV31SealedInstalled

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9FullCarrierHost
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceTableV10g B9ControllerRecovery
open R2CoherenceV31
open ZZFinalCarrierV3

variable {ψ κ τ : Nat}

private theorem h3 : 0 < 3 := by omega
private theorem h23 : 2 ≤ 3 := by omega
private theorem h02 : 0 < 2 := by omega

/-! ## Exact wait=false sealed witness -/

/-- Exact physical follower from the sealed-lane witness.
`wait` is explicitly false: this is not `QuietPairCounterexample.quietBase`. -/
def follower0Phys : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) (0 : Fin 3)
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      probe := false
      phase := false
      bit := false
      wait := false
      state := .none
      path := .bot
      reset := false
      carry := false
      count := 0
      label := 0
      h_field := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      signal_B := 0
      bullet := 0
      shield := false
      write_state := .none
      write := .none
      last := false
      last_set := false
      last_unset := false
      b_carry := false
      gen_ws := false
      ws_echo := false
      signal_ws := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

/-- V3.1 inner state: sealed and token-free. -/
def inner : R2CoherenceV31.Cell 3 3 48 :=
  ⟨follower0Phys, ⟨.sealed, .none⟩⟩

/-- Installed final cell: exact inner witness with neutral outer B9 control. -/
def cell : ZZFinalCarrierV3.Cell 3 3 48 :=
  ⟨inner, .none, false, false⟩

/-- Constant two-ring installed configuration. -/
def C : ZZFinalCarrierV3.Config 2 3 3 48 := fun _ => cell

def ring2 : DirectedRing 2 := ⟨by omega⟩

@[simp] theorem witness_wait_false :
    cell.phys.phys.base.core.core.wait = false := by rfl

@[simp] theorem witness_leader_false :
    cell.phys.phys.base.core.core.leader = false := by rfl

@[simp] theorem witness_label_zero :
    cell.phys.phys.base.core.core.label = (0 : Fin 3) := by rfl

@[simp] theorem witness_inner_control :
    cell.phys.ctl.mark = .sealed ∧ cell.phys.ctl.tok = .none := by
  exact ⟨rfl, rfl⟩

@[simp] theorem witness_outer_control :
    cell.spliceRole = .none ∧
      cell.repairPending = false ∧ cell.acquireTicket = false := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Requested adversarial recheck of the inner sealed lane -/

private def q00 : R2.Cell 3 3 48 × R2.Cell 3 3 48 :=
  sealedProposalV3 h3 h02 h23 inner inner

/-- Equal physical labels 0,0 are not a successor edge. -/
theorem successor00_false : successorB inner inner = false := by
  decide +kernel

/-- On the exact wait=false proposal, the sealed proposal is classified as a
relabel.  This is the inner row's explicit hold mechanism. -/
theorem q00_relabels :
    R2Coherence.pairRelabels inner.phys inner.phys q00.1 q00.2 = true := by
  decide +kernel

/-! ## Erased old B9 recovery view -/

private def old : B9SpliceTableHost.Cell 3 3 48 :=
  ZZFinalCarrierV3.oldCellV3 cell

@[simp] private theorem old_role :
    B9SpliceControllerR1Table.role old.carrier = .none := by rfl

@[simp] private theorem old_pending :
    old.carrier.repairPending = false := by rfl

@[simp] private theorem old_ticket :
    old.acquireTicket = false := by rfl

@[simp] private theorem old_raw_leader :
    old.carrier.splice.base.core.core.leader = false := by rfl

@[simp] private theorem old_raw_label :
    old.carrier.splice.base.core.core.label = (0 : Fin 3) := by rfl

@[simp] private theorem old_raw_wait :
    old.carrier.splice.base.core.core.wait = false := by rfl

/-! Preparation preserves the raw leader and label.  Consequently the wait
correction from `true` to `false` cannot change `LocalDanger`. -/

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

/-- Exact wait=false computation: both endpoints are followers and label 0 is
not the successor of label 0 modulo 3. -/
theorem pair_localDanger :
    B9ControllerRecovery.LocalDanger h3 old old := by
  rw [localDanger_iff_physical]
  refine ⟨old_raw_leader, old_raw_leader, ?_⟩
  intro h
  have hv := congrArg Fin.val h
  simp only [old_raw_label] at hv
  change 0 = 1 at hv
  omega

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

/-- Every protection arm is false for the outer `.none/false/false` pair. -/
theorem pair_notCovered :
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

private theorem old_not_badTicket :
    ¬ B9ControllerRecovery.BadTicket old := by
  intro h
  have ht := h.1
  rw [old_ticket] at ht
  cases ht

private theorem old_not_badBacking :
    ¬ B9ControllerRecovery.BadBacking old old := by
  intro h
  exact old_not_pending h.1

/-- Neither ticket scrub nor backing scrub is enabled. -/
theorem pair_not_scrubGarbage :
    ¬ B9ControllerRecovery.ScrubGarbage old old := by
  intro h
  rcases h with h | h | h
  · exact old_not_badTicket h
  · exact old_not_badTicket h
  · exact old_not_badBacking h

/-- The exact positive final guard is `Hole = LocalDanger ∧ ¬ PairCovered`. -/
theorem pair_isHole :
    ZZFinalCarrierV3.FinalHoleV3 h3 cell cell := by
  change B9ControllerRecovery.Hole h3 old old
  exact ⟨pair_localDanger, pair_notCovered⟩

/-- Therefore `FinalGarbageV3` is true solely through its Hole disjunct. -/
theorem pair_isGarbage :
    ZZFinalCarrierV3.FinalGarbageV3 h3 cell cell := by
  change B9ControllerRecovery.Garbage h3 old old
  exact Or.inr (by
    simpa [old, ZZFinalCarrierV3.FinalHoleV3] using pair_isHole)

/-- Full requested recovery census. -/
theorem finalGarbage_census :
    ¬ ZZFinalCarrierV3.FinalBadTicketV3 cell ∧
    ¬ ZZFinalCarrierV3.FinalBadTicketV3 cell ∧
    ¬ ZZFinalCarrierV3.FinalBadBackingV3 cell cell ∧
    ZZFinalCarrierV3.FinalHoleV3 h3 cell cell := by
  refine ⟨?_, ?_, ?_, pair_isHole⟩
  · change ¬ B9ControllerRecovery.BadTicket old
    exact old_not_badTicket
  · change ¬ B9ControllerRecovery.BadTicket old
    exact old_not_badTicket
  · change ¬ B9ControllerRecovery.BadBacking old old
    exact old_not_badBacking

/-! ## Installed final arbitration -/

/-- Recovery has absolute priority over the completed B9 port. -/
theorem finalAction_recovers :
    ZZFinalCarrierV3.finalActionV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      cell cell = .recovery :=
  ZZRecoveryJ3V3B.finalActionV3_eq_recovery_of_finalGarbage
    (κ := 3) (τ := 48) h3 h23
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23)
    cell cell pair_isGarbage

private theorem final_not_badTicket :
    ¬ ZZFinalCarrierV3.FinalBadTicketV3 cell := by
  change ¬ B9ControllerRecovery.BadTicket old
  exact old_not_badTicket

private theorem final_not_badBacking :
    ¬ ZZFinalCarrierV3.FinalBadBackingV3 cell cell := by
  change ¬ B9ControllerRecovery.BadBacking old old
  exact old_not_badBacking

/-- Since the three scrub guards are false and Hole is true, recovery is exactly
`coverFinalV3`: left becomes predecessor/pending, right front/pending. -/
theorem recoverPair_is_cover :
    ZZFinalCarrierV3.recoverPairV3 h3 cell cell =
      ZZFinalCarrierV3.coverFinalV3 cell cell := by
  classical
  unfold ZZFinalCarrierV3.recoverPairV3
  rw [if_neg final_not_badTicket, if_neg final_not_badTicket,
    if_neg final_not_badBacking, if_pos pair_isHole]

/-- Exact local installed result. -/
theorem rowFinal_recovers :
    ZZFinalCarrierV3.rowFinalV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      cell cell = ZZFinalCarrierV3.coverFinalV3 cell cell := by
  calc
    ZZFinalCarrierV3.rowFinalV3 h3 h23
        (ZZFinalCarrierV3.concretePortV3
          (κ := 3) (τ := 48) h3 h23)
        cell cell = ZZFinalCarrierV3.recoverPairV3 h3 cell cell :=
      ZZRecoveryJ3V3B.rowFinalV3_eq_recoverPairV3_of_finalGarbage
        (κ := 3) (τ := 48) h3 h23
        (ZZFinalCarrierV3.concretePortV3
          (κ := 3) (τ := 48) h3 h23)
        cell cell pair_isGarbage
    _ = ZZFinalCarrierV3.coverFinalV3 cell cell := recoverPair_is_cover

/-- Exact moved configuration after serving edge `e`. -/
def recoveredAt (e : Fin 2) : ZZFinalCarrierV3.Config 2 3 3 48 :=
  B9FullCarrierHost.writeAtP ring2 C e
    (ZZFinalCarrierV3.coverFinalV3 cell cell)

@[simp] theorem ring2_right0 :
    ring2.rightNeighbor (0 : Fin 2) = 1 := by rfl

@[simp] theorem ring2_right1 :
    ring2.rightNeighbor (1 : Fin 2) = 0 := by rfl

private theorem right0_ne :
    ring2.rightNeighbor (0 : Fin 2) ≠ (0 : Fin 2) := by
  simp

private theorem right1_ne :
    ring2.rightNeighbor (1 : Fin 2) ≠ (1 : Fin 2) := by
  simp

/-- Edge 0 writes predecessor/pending at site 0 and front/pending at site 1. -/
theorem recovered0_fields :
    (recoveredAt 0 0).spliceRole = .predecessorArmed ∧
    (recoveredAt 0 0).repairPending = true ∧
    (recoveredAt 0 0).acquireTicket = false ∧
    (recoveredAt 0 1).spliceRole = .front ∧
    (recoveredAt 0 1).repairPending = true ∧
    (recoveredAt 0 1).acquireTicket = false := by
  decide +kernel

/-- Edge 1 writes the same cover with the sites exchanged. -/
theorem recovered1_fields :
    (recoveredAt 1 1).spliceRole = .predecessorArmed ∧
    (recoveredAt 1 1).repairPending = true ∧
    (recoveredAt 1 1).acquireTicket = false ∧
    (recoveredAt 1 0).spliceRole = .front ∧
    (recoveredAt 1 0).repairPending = true ∧
    (recoveredAt 1 0).acquireTicket = false := by
  decide +kernel

/-- Exact installed step on edge 0. -/
theorem step0_eq_recovered :
    ZZFinalCarrierV3.stepConcreteV3
        (κ := 3) (τ := 48) h3 h23 ring2 C (0 : Fin 2) =
      recoveredAt 0 := by
  have hg : ZZFinalCarrierV3.FinalGarbageV3 h3
      (C 0) (C (ring2.rightNeighbor 0)) := by
    change ZZFinalCarrierV3.FinalGarbageV3 h3 cell cell
    exact pair_isGarbage
  rw [ZZRecoveryJ3V3B.stepConcreteV3_eq_recoveryStepV3_of_finalGarbage
    (κ := 3) (τ := 48) h3 h23 ring2 C (0 : Fin 2) hg]
  unfold ZZRecoveryJ3V3B.recoveryStepV3 recoveredAt
  rw [if_neg right0_ne]
  change B9FullCarrierHost.writeAtP ring2 C (0 : Fin 2)
      (ZZFinalCarrierV3.recoverPairV3 h3 cell cell) =
    B9FullCarrierHost.writeAtP ring2 C (0 : Fin 2)
      (ZZFinalCarrierV3.coverFinalV3 cell cell)
  rw [recoverPair_is_cover]

/-- Exact installed step on edge 1. -/
theorem step1_eq_recovered :
    ZZFinalCarrierV3.stepConcreteV3
        (κ := 3) (τ := 48) h3 h23 ring2 C (1 : Fin 2) =
      recoveredAt 1 := by
  have hg : ZZFinalCarrierV3.FinalGarbageV3 h3
      (C 1) (C (ring2.rightNeighbor 1)) := by
    change ZZFinalCarrierV3.FinalGarbageV3 h3 cell cell
    exact pair_isGarbage
  rw [ZZRecoveryJ3V3B.stepConcreteV3_eq_recoveryStepV3_of_finalGarbage
    (κ := 3) (τ := 48) h3 h23 ring2 C (1 : Fin 2) hg]
  unfold ZZRecoveryJ3V3B.recoveryStepV3 recoveredAt
  rw [if_neg right1_ne]
  change B9FullCarrierHost.writeAtP ring2 C (1 : Fin 2)
      (ZZFinalCarrierV3.recoverPairV3 h3 cell cell) =
    B9FullCarrierHost.writeAtP ring2 C (1 : Fin 2)
      (ZZFinalCarrierV3.coverFinalV3 cell cell)
  rw [recoverPair_is_cover]

/-- Edge 0 is not a fixed installed step. -/
theorem step0_moves :
    ZZFinalCarrierV3.stepConcreteV3
        (κ := 3) (τ := 48) h3 h23 ring2 C (0 : Fin 2) ≠ C := by
  rw [step0_eq_recovered]
  intro h
  have hr := congrArg
    (fun D : ZZFinalCarrierV3.Config 2 3 3 48 =>
      (D (0 : Fin 2)).spliceRole) h
  have hout := recovered0_fields.1
  have hin : (C (0 : Fin 2)).spliceRole = .none := rfl
  rw [hout, hin] at hr
  cases hr

/-- Edge 1 is not a fixed installed step. -/
theorem step1_moves :
    ZZFinalCarrierV3.stepConcreteV3
        (κ := 3) (τ := 48) h3 h23 ring2 C (1 : Fin 2) ≠ C := by
  rw [step1_eq_recovered]
  intro h
  have hr := congrArg
    (fun D : ZZFinalCarrierV3.Config 2 3 3 48 =>
      (D (1 : Fin 2)).spliceRole) h
  have hout := recovered1_fields.1
  have hin : (C (1 : Fin 2)).spliceRole = .none := rfl
  rw [hout, hin] at hr
  cases hr

/-- Verdict: the exact wait=false sealed-lane row fixed point is
recovery-moved on both directed services of the installed two-ring. -/
theorem installed_recovery_moves_both :
    ZZFinalCarrierV3.FinalGarbageV3 h3 cell cell ∧
    ZZFinalCarrierV3.stepConcreteV3
        (κ := 3) (τ := 48) h3 h23 ring2 C (0 : Fin 2) ≠ C ∧
    ZZFinalCarrierV3.stepConcreteV3
        (κ := 3) (τ := 48) h3 h23 ring2 C (1 : Fin 2) ≠ C := by
  exact ⟨pair_isGarbage, step0_moves, step1_moves⟩

#print axioms ZZV31SealedInstalled.witness_wait_false
#print axioms ZZV31SealedInstalled.successor00_false
#print axioms ZZV31SealedInstalled.q00_relabels
#print axioms ZZV31SealedInstalled.pair_localDanger
#print axioms ZZV31SealedInstalled.pair_notCovered
#print axioms ZZV31SealedInstalled.pair_not_scrubGarbage
#print axioms ZZV31SealedInstalled.pair_isHole
#print axioms ZZV31SealedInstalled.pair_isGarbage
#print axioms ZZV31SealedInstalled.finalGarbage_census
#print axioms ZZV31SealedInstalled.finalAction_recovers
#print axioms ZZV31SealedInstalled.recoverPair_is_cover
#print axioms ZZV31SealedInstalled.rowFinal_recovers
#print axioms ZZV31SealedInstalled.recovered0_fields
#print axioms ZZV31SealedInstalled.recovered1_fields
#print axioms ZZV31SealedInstalled.step0_eq_recovered
#print axioms ZZV31SealedInstalled.step1_eq_recovered
#print axioms ZZV31SealedInstalled.step0_moves
#print axioms ZZV31SealedInstalled.step1_moves
#print axioms ZZV31SealedInstalled.installed_recovery_moves_both

end ZZV31SealedInstalled

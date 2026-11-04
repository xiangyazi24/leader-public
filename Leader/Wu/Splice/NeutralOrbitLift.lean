import Leader.Wu.Splice.InstalledCarrier
import Leader.Wu.Coherence.FairCycleRingSix

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZOrbitLiftClean

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9FullCarrierHost
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceTableV10g B9ControllerRecovery

variable {ψ κ τ : Nat}

theorem h3 : 0 < 3 := by omega

def ring6 : DirectedRing 6 := ⟨by omega⟩

/-- Exact physical literal from `ZZV31FairCycleA.cleanPhys`. -/
private def cleanPhys (lab : Fin 3) : R2.Cell 3 3 48 :=
  let b : BoundedAgentState 3 3 :=
    { leader := false
      probe := false
      phase := false
      bit := false
      wait := true
      state := .none
      path := .bot
      reset := false
      carry := false
      count := 0
      label := lab
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
  ⟨⟨⟨b, false⟩,
      PPLLExpiringComparisonRepair.freshStall 48⟩, 0⟩

private def labAt (i : Fin 6) : Fin 3 :=
  ⟨i.val % 3, Nat.mod_lt _ h3⟩

private def ctlR : R2CoherenceV31.ControlV3 :=
  ⟨.releasing, .none⟩

private def ctlRs : R2CoherenceV31.ControlV3 :=
  ⟨.releasing, .scrubL⟩

private def cycleCtl (i : Fin 6) : R2CoherenceV31.ControlV3 :=
  if i.val % 3 = 2 then ctlRs else ctlR

/-- Exact six-cell V3.1 orbit state from `ZZV31FairCycleA.cycleC`. -/
private def cycleC : R2CoherenceV31.FC 6 3 3 48 :=
  fun i => ⟨cleanPhys (labAt i), cycleCtl i⟩

/--
Neutral outer-B9 lift of the compiled V3.1 orbit.

`ZZFinalCarrierV3.Cell` abbreviates `CellP (R2CoherenceV31.Cell ...)`, so
`phys` must be the whole `cycleC i`, not `(cycleC i).phys`.
-/
def liftC : Fin 6 → ZZFinalCarrierV3.Cell 3 3 48 :=
  fun i =>
    { phys := cycleC i
      spliceRole := .none
      repairPending := false
      acquireTicket := false }

@[simp] theorem ring6_right0 :
    ring6.rightNeighbor (0 : Fin 6) = 1 := by rfl

@[simp] theorem ring6_right1 :
    ring6.rightNeighbor (1 : Fin 6) = 2 := by rfl

@[simp] theorem ring6_right2 :
    ring6.rightNeighbor (2 : Fin 6) = 3 := by rfl

@[simp] theorem ring6_right3 :
    ring6.rightNeighbor (3 : Fin 6) = 4 := by rfl

@[simp] theorem ring6_right4 :
    ring6.rightNeighbor (4 : Fin 6) = 5 := by rfl

@[simp] theorem ring6_right5 :
    ring6.rightNeighbor (5 : Fin 6) = 0 := by rfl

/-- Core-only replacement for unavailable `fin_cases`. -/
private theorem fin6_cases (i : Fin 6) :
    i = (0 : Fin 6) ∨ i = 1 ∨ i = 2 ∨
      i = 3 ∨ i = 4 ∨ i = 5 := by
  have hi : i.val < 6 := i.isLt
  have hv :
      i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
        i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
    omega
  rcases hv with h | h | h | h | h | h
  · left
    apply Fin.ext
    omega
  · right; left
    apply Fin.ext
    omega
  · right; right; left
    apply Fin.ext
    omega
  · right; right; right; left
    apply Fin.ext
    omega
  · right; right; right; right; left
    apply Fin.ext
    omega
  · right; right; right; right; right
    apply Fin.ext
    omega

/-! Preparation preserves exactly the two physical fields needed by
`LocalDanger`.  These are the same compiled helper proofs used by the B9
physical-hold safety files. -/

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

/-- Pair-local recovery danger written only in raw physical leader/label data. -/
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

/-! Exact neutral outer fields after the `oldCellV3` projection. -/

@[simp] private theorem lift_old_role (i : Fin 6) :
    B9SpliceControllerR1Table.role
      (ZZFinalCarrierV3.oldCellV3 (liftC i)).carrier = .none := by
  rfl

@[simp] private theorem lift_old_pending (i : Fin 6) :
    (ZZFinalCarrierV3.oldCellV3 (liftC i)).carrier.repairPending =
      false := by
  rfl

@[simp] private theorem lift_old_ticket (i : Fin 6) :
    (ZZFinalCarrierV3.oldCellV3 (liftC i)).acquireTicket = false := by
  rfl

@[simp] private theorem lift_old_leader (i : Fin 6) :
    (ZZFinalCarrierV3.oldCellV3 (liftC i)).carrier.splice.base.core.core.leader =
      false := by
  rfl

@[simp] private theorem lift_old_label (i : Fin 6) :
    (ZZFinalCarrierV3.oldCellV3 (liftC i)).carrier.splice.base.core.core.label =
      labAt i := by
  rfl

/--
For neutral outer fields, all scrub disjuncts are false and `PairCovered` is
false, so final garbage is exactly the physical `LocalDanger` residual.
-/
private theorem lift_garbage_iff_localDanger (i j : Fin 6) :
    ZZFinalCarrierV3.FinalGarbageV3 h3 (liftC i) (liftC j) ↔
      B9ControllerRecovery.LocalDanger h3
        (ZZFinalCarrierV3.oldCellV3 (liftC i))
        (ZZFinalCarrierV3.oldCellV3 (liftC j)) := by
  simp [ZZFinalCarrierV3.FinalGarbageV3,
    B9ControllerRecovery.Garbage,
    B9ControllerRecovery.ScrubGarbage,
    B9ControllerRecovery.Hole,
    B9ControllerRecovery.PairCovered,
    B9ControllerRecovery.BadTicket,
    B9ControllerRecovery.BadBacking,
    B9ControllerRecovery.Pending,
    B9SpliceControllerR1TableV2.ReservedFrontHoldGuard,
    B9SpliceControllerR1TableV7.HostFenceShapeV7,
    B9SpliceTableV10g.PendingOwnerHoldShapeV7]

/-- Every one of the six physical edges is successor-labelled, including 5->0. -/
private theorem noLocalDanger_on_ring (i : Fin 6) :
    ¬ B9ControllerRecovery.LocalDanger h3
      (ZZFinalCarrierV3.oldCellV3 (liftC i))
      (ZZFinalCarrierV3.oldCellV3
        (liftC (ring6.rightNeighbor i))) := by
  rcases fin6_cases i with h | h | h | h | h | h
  · subst i
    simp [localDanger_iff_physical, labAt] <;> omega
  · subst i
    simp [localDanger_iff_physical, labAt] <;> omega
  · subst i
    simp [localDanger_iff_physical, labAt] <;> omega
  · subst i
    simp [localDanger_iff_physical, labAt] <;> omega
  · subst i
    simp [localDanger_iff_physical, labAt] <;> omega
  · subst i
    simp [localDanger_iff_physical, labAt] <;> omega

/-- The neutral lift of the complete six-cell V3.1 orbit is recovery-clean. -/
theorem cleanLift_noFinalGarbage :
    ∀ i : Fin 6,
      ¬ ZZFinalCarrierV3.FinalGarbageV3 h3
        (liftC i) (liftC (ring6.rightNeighbor i)) := by
  intro i hG
  exact noLocalDanger_on_ring i
    ((lift_garbage_iff_localDanger
      i (ring6.rightNeighbor i)).mp hG)

#print axioms ZZOrbitLiftClean.cleanLift_noFinalGarbage

end ZZOrbitLiftClean

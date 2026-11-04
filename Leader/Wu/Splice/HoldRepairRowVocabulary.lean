import Leader.Wu.Splice.HoldRepairStallRing
import Leader.Wu.Splice.PhysicalHoldHandoffFollowUp

set_option autoImplicit false
set_option Elab.async false

/-! # V10j: the first service of an edge, classified at row level

For a served pair `(l, r)` whose cells satisfy the V7 ticket shape, the V10j row either is physical (both bases
take the host row), strictly lowers the controller weight of the pair, is one of the stall shapes
`HoldShapeJ`, or is one of three follow-up cases (`SpecialJ`): the V10b handoff, the ownerless pending
predecessor behind a neutral unticketed cell, and ARM-B (`first_row_classified`). -/

namespace B9SpliceV10jRowProgress

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
  B9SpliceV10jHoldRing B9SpliceV10eRowPotential B9SpliceV10eHandoffFollowUp B9SpliceV10ePhysicalHoldNoBirth

variable {psi width kappa tau : Nat}

/-! ## Vocabulary -/

/-- Both bases take the host row of `(l, r)`. -/
def PhysRow (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) : Prop :=
  w.1.carrier.splice.base = (BirthShortDoneTerminalHost.row hpsi hwidth hle l.carrier.splice.base r.carrier.splice.base).1 ∧
  w.2.carrier.splice.base = (BirthShortDoneTerminalHost.row hpsi hwidth hle l.carrier.splice.base r.carrier.splice.base).2

/-- Controller weight of a pair. -/
def wsum (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) : Nat :=
  controllerWeightV6 w.1 + controllerWeightV6 w.2

/-- The three follow-up cases. -/
def SpecialJ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice ∧
  (HostFenceAdvanceGuardV10b hpsi l r ∨
   (role l.carrier = .none ∧ l.carrier.repairPending = false ∧ l.acquireTicket = false ∧
     role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true) ∨
   (ArmBGuard l.carrier r.carrier ∧ l.acquireTicket = false))

/-! ## Physical writes -/

theorem phys_hold (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    PhysRow hpsi hwidth hle l r (physicalHoldV6 hpsi hwidth hle l r) :=
  ⟨physicalHold_base_left hpsi hwidth hle l r, physicalHold_base_right hpsi hwidth hle l r⟩

theorem phys_fence (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    PhysRow hpsi hwidth hle l r
      ((physicalHoldV6 hpsi hwidth hle l r).1, fenceV6 (physicalHoldV6 hpsi hwidth hle l r).2) :=
  ⟨physicalHold_base_left hpsi hwidth hle l r, physicalHold_base_right hpsi hwidth hle l r⟩

theorem phys_ordinary (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    PhysRow hpsi hwidth hle l r (ordinaryHostWriteV7 hpsi hwidth hle l r) := by
  have hc := physicalHold_carriers_eq_ordinaryHost hpsi hwidth hle l r
  refine ⟨?_, ?_⟩
  · rw [← hc.1]; exact physicalHold_base_left hpsi hwidth hle l r
  · rw [← hc.2]; exact physicalHold_base_right hpsi hwidth hle l r

theorem phys_delete (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    PhysRow hpsi hwidth hle l r (deleteWriteV6 hpsi hwidth hle l r) := ⟨rfl, rfl⟩

/-! ## Weights -/

theorem weight_fence (u : R1AgentStateV6 psi kappa tau) : controllerWeightV6 (fenceV6 u) = 1 := rfl
theorem weight_settle (u : R1AgentStateV6 psi kappa tau) : controllerWeightV6 (settleV6 u) = 3 := rfl

theorem weight_pendingPred_ge (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .predecessorArmed)
    (h2 : u.carrier.repairPending = true) : 4 ≤ controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h1, h2]
  cases u.acquireTicket <;> decide

theorem weight_front_ge (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .front) :
    2 ≤ controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h1]
  cases u.carrier.repairPending <;> cases u.acquireTicket <;> decide

theorem weight_victim_ge (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .victimArmed) :
    2 ≤ controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h1]
  cases u.carrier.repairPending <;> cases u.acquireTicket <;> decide

theorem weight_none_pos (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .none)
    (h : u.carrier.repairPending = true ∨ u.acquireTicket = true) : 1 ≤ controllerWeightV6 u := by
  rcases h with hp | ht
  · exact weight_pos_of_pending u hp
  · exact weight_pos_of_ticket u ht

/-! ## Tickets forced by the ticket shape -/

theorem ticket_false_of_shape (u : R1AgentStateV6 psi kappa tau) (h : TicketShapeV7 u)
    (hnf : role u.carrier ≠ .front) (hnn : role u.carrier ≠ .none) : u.acquireTicket = false := by
  cases ht : u.acquireTicket
  · rfl
  · rcases h ht with hrf | hf
    · exact absurd hrf.1 hnf
    · exact absurd hf.1 hnn

theorem clearTicket_self (u : R1AgentStateV6 psi kappa tau) (h : u.acquireTicket = false) : clearTicketV6 u = u := by
  cases u with
  | mk c t =>
    simp only at h
    subst h
    rfl

theorem setTicket_self (u : R1AgentStateV6 psi kappa tau) (h : u.acquireTicket = true) : setTicketV6 u true = u := by
  cases u with
  | mk c t =>
    simp only at h
    subst h
    rfl

/-! ## Row equations -/

theorem rowV10j_of_notLDC (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hd : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice) :
    rowV10j hpsi hwidth hle l r = rowV10g hpsi hwidth hle l r := by
  rw [rowV10j.eq_1, if_neg hd]

theorem rowV10g_of_change (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (hq : rowV10dg hpsi hwidth hle l r ≠ (l, r)) :
    rowV10g hpsi hwidth hle l r = rowV10dg hpsi hwidth hle l r := by
  have hw := rowV10g.eq_1 hpsi hwidth hle l r
  dsimp only at hw
  rw [hw, if_neg hq]

theorem ordinaryHost_right_role (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    role (ordinaryHostWriteV7 hpsi hwidth hle l r).2.carrier = role r.carrier := by
  rw [← (physicalHold_carriers_eq_ordinaryHost hpsi hwidth hle l r).2]
  exact (physicalHold_role_frame hpsi hwidth hle l r).2.2.1

theorem notZeroRefresh_of_right_role (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (h : role (rowV10b hpsi hwidth hle l r).2.carrier ≠ role r.carrier) :
    ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r := by
  intro hz
  apply h
  have h1 := hz.1
  rw [h1]
  exact ordinaryHost_right_role hpsi hwidth hle l r

theorem notZeroRefresh_of_left_ticket (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (h : l.acquireTicket = true) :
    ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r := by
  intro hz
  have h1 := hz.2.2.2.1.2.2.2
  have h2 := hz.1
  have h3 : (ordinaryHostWriteV7 hpsi hwidth hle l r).1.acquireTicket = false := by
    unfold ordinaryHostWriteV7; dsimp only; split <;> rfl
  rw [h2, h3, h] at h1
  cases h1

end B9SpliceV10jRowProgress

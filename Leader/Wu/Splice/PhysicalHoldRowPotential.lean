import Leader.Wu.Splice.PhysicalHoldTable
import Leader.Wu.Splice.ZeroRefreshChain

set_option autoImplicit false

/-! # Potential facts for the inherited rows, as configuration steps

For the ring-global progress theorem every non-physical row must either drop
`controllerPotentialV6` or be one of the two follow-up classes.  This file proves the drops
for the inherited rows through one-index sum splitting. -/

namespace B9SpliceV10eRowPotential

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10d B9SpliceTableV10e

variable {n psi width kappa tau : Nat}

/-- One cell changes and its weight strictly drops. -/
theorem potential_drop_one (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (hother : ∀ i, i ≠ x → D i = C i)
    (hlt : controllerWeightV6 (D x) < controllerWeightV6 (C x)) :
    controllerPotentialV6 D < controllerPotentialV6 C := by
  have hs := ofFn_sum_split (fun i => controllerWeightV6 (D i)) (fun i => controllerWeightV6 (C i)) x
    (fun i hi => by rw [hother i hi]; exact Nat.le_refl _)
  unfold controllerPotentialV6
  omega

/-- Two cells change; the left weight does not rise and the right weight drops (or the
symmetric case), in total a strict drop. -/
theorem potential_drop_two (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau) (x y : Fin n)
    (hxy : x ≠ y)
    (hother : ∀ i, i ≠ x → i ≠ y → D i = C i)
    (hsum : controllerWeightV6 (D x) + controllerWeightV6 (D y) <
      controllerWeightV6 (C x) + controllerWeightV6 (C y)) :
    controllerPotentialV6 D < controllerPotentialV6 C := by
  -- intermediate configuration: D at x, C elsewhere
  let M : R1ConfigV6 n psi kappa tau := fun i => if i = x then D x else C i
  have hs1 := ofFn_sum_split (fun i => controllerWeightV6 (M i)) (fun i => controllerWeightV6 (C i)) x
    (fun i hi => by simp [M, hi])
  have hs2 := ofFn_sum_split (fun i => controllerWeightV6 (D i)) (fun i => controllerWeightV6 (M i)) y
    (fun i hi => by
      by_cases hix : i = x
      · subst hix; simp [M]
      · simp [M, hix, hother i hix hi])
  have hMx : controllerWeightV6 (M x) = controllerWeightV6 (D x) := by simp [M]
  have hMy : controllerWeightV6 (M y) = controllerWeightV6 (C y) := by simp [M, Ne.symm hxy]
  unfold controllerPotentialV6
  rw [hMx] at hs1
  rw [hMy] at hs2
  omega

/-! ## Cell weights -/

theorem weight_clear (u : R1AgentStateV6 psi kappa tau) : controllerWeightV6 (clearControlV6 u) = 0 := rfl

theorem weight_pos_of_role (u : R1AgentStateV6 psi kappa tau) (h : role u.carrier ≠ .none) :
    0 < controllerWeightV6 u := by
  unfold controllerWeightV6
  cases hr : role u.carrier <;> cases hp : u.carrier.repairPending <;> cases ht : u.acquireTicket <;>
    first | (exact absurd hr h) | decide

theorem weight_pos_of_pending (u : R1AgentStateV6 psi kappa tau) (h : u.carrier.repairPending = true) :
    0 < controllerWeightV6 u := by
  unfold controllerWeightV6
  cases hr : role u.carrier <;> rw [h] <;> cases ht : u.acquireTicket <;> decide

theorem weight_pos_of_ticket (u : R1AgentStateV6 psi kappa tau) (h : u.acquireTicket = true) :
    0 < controllerWeightV6 u := by
  unfold controllerWeightV6
  cases hr : role u.carrier <;> cases hp : u.carrier.repairPending <;> rw [h] <;> decide

theorem weight_clearControl_lt (u : R1AgentStateV6 psi kappa tau) (h : role u.carrier ≠ .none) :
    controllerWeightV6 (clearControlV6 u) < controllerWeightV6 u := by
  rw [weight_clear]; exact weight_pos_of_role u h

theorem weight_RFHG_ge (u : R1AgentStateV6 psi kappa tau) (h : ReservedFrontHoldGuard u.carrier) :
    6 ≤ controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h.1, h.2]
  cases u.acquireTicket <;> decide

theorem weight_RFHG_clearTicket (u : R1AgentStateV6 psi kappa tau) (h : ReservedFrontHoldGuard u.carrier) :
    controllerWeightV6 (clearTicketV6 u) = 8 := by
  unfold controllerWeightV6
  have h1 : role (clearTicketV6 u).carrier = .front := h.1
  have h2 : (clearTicketV6 u).carrier.repairPending = true := h.2
  have h3 : (clearTicketV6 u).acquireTicket = false := rfl
  rw [h1, h2, h3]

theorem weight_RFHG_setTicket (u : R1AgentStateV6 psi kappa tau) (h : ReservedFrontHoldGuard u.carrier) :
    controllerWeightV6 (setTicketV6 u true) = 6 := by
  unfold controllerWeightV6
  have h1 : role (setTicketV6 u true).carrier = .front := h.1
  have h2 : (setTicketV6 u true).carrier.repairPending = true := h.2
  have h3 : (setTicketV6 u true).acquireTicket = true := rfl
  rw [h1, h2, h3]

theorem weight_RFHG_unticketed (u : R1AgentStateV6 psi kappa tau) (h : ReservedFrontHoldGuard u.carrier)
    (ht : u.acquireTicket = false) : controllerWeightV6 u = 8 := by
  unfold controllerWeightV6
  rw [h.1, h.2, ht]

theorem weight_settledPred (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .predecessorArmed)
    (h2 : u.carrier.repairPending = false) : 3 ≤ controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h1, h2]
  cases u.acquireTicket <;> decide

theorem weight_pendingPred_ticketed (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .predecessorArmed)
    (h2 : u.carrier.repairPending = true) (h3 : u.acquireTicket = true) : controllerWeightV6 u = 5 := by
  unfold controllerWeightV6
  rw [h1, h2, h3]

theorem weight_pendingPred_clearTicket (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .predecessorArmed)
    (h2 : u.carrier.repairPending = true) : controllerWeightV6 (clearTicketV6 u) = 4 := by
  unfold controllerWeightV6
  have h1' : role (clearTicketV6 u).carrier = .predecessorArmed := h1
  have h2' : (clearTicketV6 u).carrier.repairPending = true := h2
  have h3 : (clearTicketV6 u).acquireTicket = false := rfl
  rw [h1', h2', h3]

theorem weight_pendingVictim_ticketed (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .victimArmed)
    (h2 : u.carrier.repairPending = true) (h3 : u.acquireTicket = true) : controllerWeightV6 u = 6 := by
  unfold controllerWeightV6
  rw [h1, h2, h3]

theorem weight_pendingVictim_clearTicket (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .victimArmed)
    (h2 : u.carrier.repairPending = true) : controllerWeightV6 (clearTicketV6 u) = 5 := by
  unfold controllerWeightV6
  have h1' : role (clearTicketV6 u).carrier = .victimArmed := h1
  have h2' : (clearTicketV6 u).carrier.repairPending = true := h2
  have h3 : (clearTicketV6 u).acquireTicket = false := rfl
  rw [h1', h2', h3]

theorem weight_pendingVictim_ge (u : R1AgentStateV6 psi kappa tau) (h1 : role u.carrier = .victimArmed)
    (h2 : u.carrier.repairPending = true) : 5 ≤ controllerWeightV6 u := by
  unfold controllerWeightV6
  rw [h1, h2]
  cases u.acquireTicket <;> decide

theorem weight_setControl_pred_pending (u : R1AgentStateV6 psi kappa tau) :
    controllerWeightV6 (setControlV6 u .predecessorArmed true) = 4 := rfl
theorem weight_setControl_pred_settled (u : R1AgentStateV6 psi kappa tau) :
    controllerWeightV6 (setControlV6 u .predecessorArmed false) = 3 := rfl
theorem weight_hostFence_clearTicket (u : R1AgentStateV6 psi kappa tau) (h : HostFenceShapeV7 u) :
    controllerWeightV6 (clearTicketV6 u) = 0 := by
  unfold controllerWeightV6
  have h1 : role (clearTicketV6 u).carrier = .none := h.1
  have h2 : (clearTicketV6 u).carrier.repairPending = false := h.2.1
  have h3 : (clearTicketV6 u).acquireTicket = false := rfl
  rw [h1, h2, h3]

theorem weight_hostFence (u : R1AgentStateV6 psi kappa tau) (h : HostFenceShapeV7 u) :
    controllerWeightV6 u = 1 := by
  unfold controllerWeightV6
  rw [h.1, h.2.1, h.2.2]

end B9SpliceV10eRowPotential

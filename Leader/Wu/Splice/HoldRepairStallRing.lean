import Leader.Wu.Splice.HoldRepairTable

set_option autoImplicit false

/-! # The V10j stall shapes cannot cover a ring

`HoldShapeJ l r` lists the three served-pair shapes on which a V10j edge can fail to make progress
(sampled: run/verification/b9-v10j-liveness-probe.txt): a pending predecessor on the left; a pending victim
facing a pending predecessor; a reserved front facing a controller-neutral unpending cell (neutral or host fence)
or a settled predecessor.  `ring_not_all_hold`: under the provenance clause of `SpliceSafeV7g` these shapes
cannot hold on every edge of a ring, since a pending predecessor is backed by a reserved front, a reserved front
in a stall shape faces a quiet cell, and no stall shape starts at a quiet cell. -/

namespace B9SpliceV10jHoldRing

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7

variable {n psi kappa tau : Nat}

/-- The three stall shapes of V10j. -/
def HoldShapeJ (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) ∨
  (role l.carrier = .victimArmed ∧ l.carrier.repairPending = true ∧
    role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true) ∨
  (ReservedFrontHoldGuard l.carrier ∧
    ((role r.carrier = .none ∧ r.carrier.repairPending = false) ∨
     (role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = false)))

/-- A quiet cell: controller-neutral and unpending, or a settled predecessor. -/
def QuietJ (u : R1AgentStateV6 psi kappa tau) : Prop :=
  (role u.carrier = .none ∧ u.carrier.repairPending = false) ∨
  (role u.carrier = .predecessorArmed ∧ u.carrier.repairPending = false)

theorem not_hold_of_quiet (u v : R1AgentStateV6 psi kappa tau) (hq : QuietJ u) : ¬ HoldShapeJ u v := by
  intro h
  rcases hq with ⟨hr, hp⟩ | ⟨hr, hp⟩
  · rcases h with h1 | h2 | h3
    · rw [hr] at h1; exact absurd h1.1 (by decide)
    · rw [hr] at h2; exact absurd h2.1 (by decide)
    · have := h3.1.1; rw [hr] at this; exact absurd this (by decide)
  · rcases h with h1 | h2 | h3
    · rw [hp] at h1; exact absurd h1.2 (by decide)
    · rw [hr] at h2; exact absurd h2.1 (by decide)
    · have := h3.1.1; rw [hr] at this; exact absurd this (by decide)

/-- From a reserved front, a stall shape reaches a quiet cell. -/
theorem quiet_after_front (u v : R1AgentStateV6 psi kappa tau) (hrf : ReservedFrontHoldGuard u.carrier)
    (h : HoldShapeJ u v) : QuietJ v := by
  rcases h with h1 | h2 | h3
  · have := hrf.1; rw [h1.1] at this; exact absurd this (by decide)
  · have := hrf.1; rw [h2.1] at this; exact absurd this (by decide)
  · exact h3.2

theorem ring_not_all_hold (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (hP : ProvenanceSafeV7 ring C) (e : Fin n) :
    ¬ ∀ x, HoldShapeJ (C x) (C (ring.rightNeighbor x)) := by
  intro hall
  -- a pending predecessor leads, through its backing front, to a quiet cell two steps on
  have from_pp : ∀ x, role (C x).carrier = .predecessorArmed → (C x).carrier.repairPending = true → False := by
    intro x hr hp
    have hb := hP.2 x hr hp
    have hq := quiet_after_front _ _ hb.1 (hall (ring.rightNeighbor x))
    exact not_hold_of_quiet _ _ hq (hall (ring.rightNeighbor (ring.rightNeighbor x)))
  rcases hall e with h1 | h2 | h3
  · exact from_pp e h1.1 h1.2
  · exact from_pp (ring.rightNeighbor e) h2.2.2.1 h2.2.2.2
  · exact not_hold_of_quiet _ _ h3.2 (hall (ring.rightNeighbor e))

end B9SpliceV10jHoldRing

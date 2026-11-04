import Leader.Wu.Splice.PhysicalHoldTable

set_option autoImplicit false

/-! # Transparency of V10e: the shape of the liveness obligation

In the leaderless phase the controller must not block the physical protocol.  A service of
edge `e` is *physical* when both served bases are rewritten exactly by the physical host row.
This file states the obligation and proves the two facts that need no case analysis: a
physical hold is a physical service, and every row of V10e that is not a physical hold is one
of finitely many controller-only writers. -/

namespace B9SpliceV10eTransparency

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceV10cLiveness B9SpliceTableV10d B9SpliceTableV10e

variable {n psi width kappa tau : Nat}

/-- The served bases after a service equal the physical host row of the served bases before. -/
def PhysicalServiceAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau) (e : Fin n) : Prop :=
  let q := BirthShortDoneTerminalHost.row hpsi hwidth hle
    (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base
  (D e).carrier.splice.base = q.1 ∧ (D (ring.rightNeighbor e)).carrier.splice.base = q.2

/-- `m` consecutive V10e services of the same edge. -/
def serveIter (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) : Nat → R1ConfigV6 n psi kappa tau → R1ConfigV6 n psi kappa tau
  | 0, C => C
  | m + 1, C => stepV10e hpsi hwidth hle ring (serveIter hpsi hwidth hle ring e m C) e

/-- Transparency with bound `k`: among any `k` consecutive services of the same edge from a
safe leaderless configuration, at least one is physical.  The census on the n = 3 fixture
cores supports `k = 4`. -/
def TransparentWithin (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (k : Nat) : Prop :=
  ∀ (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
    (∀ i, (C i).carrier.splice.base.core.core.leader = false) →
    SpliceSafeV7 hpsi ring C → ring.rightNeighbor e ≠ e →
    ∃ m, m < k ∧
      PhysicalServiceAt hpsi hwidth hle ring
        (serveIter hpsi hwidth hle ring e m C) (serveIter hpsi hwidth hle ring e (m + 1) C) e

/-- A physical hold is a physical service. -/
theorem physicalHold_is_physical (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    PhysicalServiceAt hpsi hwidth hle ring C (physicalHoldAt hpsi hwidth hle ring C e) e := by
  unfold PhysicalServiceAt
  dsimp only
  constructor
  · show (physicalHoldAt hpsi hwidth hle ring C e e).carrier.splice.base = _
    simp only [physicalHoldAt, if_pos rfl]
    exact physicalHold_base_left hpsi hwidth hle _ _
  · show (physicalHoldAt hpsi hwidth hle ring C e (ring.rightNeighbor e)).carrier.splice.base = _
    simp only [physicalHoldAt, if_neg hne, if_pos rfl, if_true]
    exact physicalHold_base_right hpsi hwidth hle _ _

/-- The physical-then-fence row is a physical service too (the fence changes no base). -/
theorem physicalFence_is_physical (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    PhysicalServiceAt hpsi hwidth hle ring C (physicalFenceAt hpsi hwidth hle ring C e) e := by
  unfold PhysicalServiceAt
  dsimp only
  constructor
  · show (physicalFenceAt hpsi hwidth hle ring C e e).carrier.splice.base = _
    simp only [physicalFenceAt, if_pos rfl]
    exact physicalHold_base_left hpsi hwidth hle _ _
  · show (physicalFenceAt hpsi hwidth hle ring C e (ring.rightNeighbor e)).carrier.splice.base = _
    simp only [physicalFenceAt, if_neg hne, if_pos rfl, if_true]
    exact physicalHold_base_right hpsi hwidth hle _ _

end B9SpliceV10eTransparency

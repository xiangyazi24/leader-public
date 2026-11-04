import Leader.Wu.Splice.PendingLeftHoldTable

set_option autoImplicit false

/-! # V10g candidate: with-leader repair of the DELETE no-go (definitions and first facts)

The with-leader DELETE no-go (LDR-BIRTH-B9-V10B-DELETE-BRANCH-NOGO) is exactly the served-edge clause of
danger coverage in `SpliceSafeV7`.  The repair candidate adds a fourth protected shape and two settle
repairs to V10f:

* `PendingOwnerHoldShapeV7 l r`: the left cell is a pending predecessor, the right cell is a reserved
  front, and both acquire tickets are false.  `SpliceSafeV7g` is `SpliceSafeV7` with this extra disjunct
  in the danger-coverage clause (`ProtectedSpliceEdgeV7g`); the provenance clause is unchanged.
* `rowV10dg` is `rowV10d` except that the ownerless-pending-predecessor row settles the right cell
  (`settleV6`) instead of clearing it.
* `rowV10g` is `rowV10f` on top of `rowV10dg`, except that the stutter branch "right pending predecessor
  behind a reserved front" settles the right cell instead of clearing it.

This file only fixes the objects the preservation proof must talk about; nothing here is the
preservation theorem.  First facts: `SpliceSafeV7` implies `SpliceSafeV7g`, the new rows agree with the
old ones outside the two repaired branches, and the V10f pending-left hold is kept. -/

namespace B9SpliceTableV10g

open Q11593SpliceControllerDesign
  B9SpliceControllerR1Table
  B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3
  B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7
  B9SpliceV10cLiveness
  B9OrphanToFence
  B9SpliceTableV10d
  B9SpliceTableV10e
  B9SpliceTableV10f

variable {n psi kappa tau width : Nat}

/-- The fourth protected shape: pending predecessor on the left, reserved front on the right, no tickets. -/
def PendingOwnerHoldShapeV7 (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true ∧
    ReservedFrontHoldGuard r.carrier ∧ l.acquireTicket = false ∧ r.acquireTicket = false

instance instDecPendingOwnerHoldShapeV7 (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (PendingOwnerHoldShapeV7 l r) := by
  unfold PendingOwnerHoldShapeV7 ReservedFrontHoldGuard; infer_instance

/-- Danger coverage with the fourth shape. -/
def ProtectedSpliceEdgeV7g (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) : Prop :=
  ProtectedSpliceEdgeV7 ring C e ∨ PendingOwnerHoldShapeV7 (C e) (C (ring.rightNeighbor e))

/-- The V10g invariant: extended danger coverage and the unchanged V7 provenance clause. -/
def SpliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) : Prop :=
  (∀ e, PreparedDangerAt hpsi ring (projectV6 C) e → ProtectedSpliceEdgeV7g ring C e) ∧
    ProvenanceSafeV7 ring C

theorem spliceSafeV7g_of_spliceSafeV7 (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (h : SpliceSafeV7 hpsi ring C) : SpliceSafeV7g hpsi ring C :=
  ⟨fun e he => Or.inl (h.1 e he), h.2⟩

/-- Under `ShapeClear` there is no pending predecessor, so the new disjunct never holds and the two
invariants coincide. -/
theorem not_pendingOwnerHold_of_shapeClear (C : R1ConfigV6 n psi kappa tau)
    (hSC : B9SpliceComposedEvents.ShapeClear C) (e j : Fin n) :
    ¬ PendingOwnerHoldShapeV7 (C e) (C j) := by
  intro h
  have := hSC.2 e h.1
  rw [h.2.1] at this
  exact Bool.noConfusion this

theorem spliceSafeV7_iff_V7g_of_shapeClear (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (hSC : B9SpliceComposedEvents.ShapeClear C) :
    SpliceSafeV7 hpsi ring C ↔ SpliceSafeV7g hpsi ring C := by
  constructor
  · exact spliceSafeV7g_of_spliceSafeV7 hpsi ring C
  · intro h
    refine ⟨fun e he => ?_, h.2⟩
    rcases h.1 e he with hp | hp
    · exact hp
    · exact absurd hp (not_pendingOwnerHold_of_shapeClear C hSC e _)

/-- `rowV10d` with repair (ii): the ownerless pending predecessor is settled, not cleared. -/
def rowV10dg (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if OrphanReservedFrontGuardV3 l.carrier r.carrier then (l, fenceV6 r)
  else if OrphanVictimGuard l r then (l, clearControlV6 r)
  else if OwnedPendingVictimGuard l r then (fenceV6 l, fenceV6 r)
  else if OwnerlessPendingPredGuard l r then (fenceV6 l, settleV6 r)
  else rowV10c hpsi hwidth hle l r

/-- V10g row: V10f's pending-left hold on top of `rowV10dg`, and repair (iii) in the stutter branch. -/
def rowV10g (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  let q := rowV10dg hpsi hwidth hle l r
  if q = (l, r) then
    if role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true then
      (l, r)
    else if VictimRightScrubGuardV6 r then (l, clearControlV6 r)
    else if FrontRightScrubGuardV6 r then (l, clearControlV6 r)
    else if MalformedRightPendingGuardV6 r then (l, clearControlV6 r)
    else if role r.carrier = .predecessorArmed then
      if r.carrier.repairPending then
        if ReservedFrontHoldGuard l.carrier then (l, settleV6 r)
        else if LeftScrubGuardV10e l then (clearControlV6 l, r)
        else (l, r)
      else
        let q' := physicalHoldV6 hpsi hwidth hle l r
        (q'.1, fenceV6 q'.2)
    else physicalHoldV6 hpsi hwidth hle l r
  else q

/-- Pointwise ring step using `rowV10g`, with the self-edge convention of `stepV10e`. -/
def stepV10g (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  if ring.rightNeighbor e = e then C
  else
    let w := rowV10g hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
    fun i =>
      if i = e then w.1
      else if i = ring.rightNeighbor e then w.2
      else C i

/-- Outside the ownerless-pending-predecessor branch, `rowV10dg` is `rowV10d`. -/
theorem rowV10dg_eq_rowV10d_of_not_ownerless (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (h : ¬ OwnerlessPendingPredGuard l r) :
    rowV10dg hpsi hwidth hle l r = rowV10d hpsi hwidth hle l r := by
  unfold rowV10dg rowV10d
  simp only [if_neg h]

/-- Under `ShapeClear` at the served pair there is no pending predecessor on either side, so V10g is V10e
on that pair. -/
theorem rowV10g_eq_rowV10e_of_no_pending_pred (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hl : role l.carrier = .predecessorArmed → l.carrier.repairPending = false)
    (hr : role r.carrier = .predecessorArmed → r.carrier.repairPending = false) :
    rowV10g hpsi hwidth hle l r = rowV10e hpsi hwidth hle l r := by
  have hown : ¬ OwnerlessPendingPredGuard l r := by
    rintro ⟨_, hrole, hpend⟩
    rw [hr hrole] at hpend
    exact Bool.noConfusion hpend
  have hleft : ¬ (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) := by
    rintro ⟨hrole, hpend⟩
    rw [hl hrole] at hpend
    exact Bool.noConfusion hpend
  unfold rowV10g rowV10e
  rw [rowV10dg_eq_rowV10d_of_not_ownerless hpsi hwidth hle l r hown]
  dsimp only
  by_cases hq : rowV10d hpsi hwidth hle l r = (l, r)
  · rw [if_pos hq, if_pos hq, if_neg hleft]
    by_cases hrole : role r.carrier = .predecessorArmed
    · have hpend := hr hrole
      simp [hrole, hpend]
    · simp [hrole]
  · rw [if_neg hq, if_neg hq]

/-- The V10f pending-left hold is kept. -/
theorem rowV10g_pendingLeft_hold (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hq : rowV10dg hpsi hwidth hle l r = (l, r))
    (hp : role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) :
    rowV10g hpsi hwidth hle l r = (l, r) := by
  unfold rowV10g
  simp only [hq, if_pos hp, if_true]

end B9SpliceTableV10g

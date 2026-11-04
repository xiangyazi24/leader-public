import Leader.Wu.Splice.CertifiedDeleteSafe

set_option autoImplicit false

/-! # Repair (iii) of V10g/V10h preserves `SpliceSafeV7g` (first row lifted with `local_preservation`)

`settleAt ring C e` settles the right served cell: `j := settleV6 (C j)` (predecessor, not pending, ticket
cleared), every other cell unchanged, the physical bases unchanged.  V10g/V10h use this write on the
stutter branch "right pending predecessor behind a left reserved front".  Theorem
`settleAt_preserves_spliceSafeV7g`: if `C` is `SpliceSafeV7g`, `C e` is a reserved front and `C j` a pending
predecessor, then `settleAt C e` is `SpliceSafeV7g`, in the presence of leaders as well.

The proof is an instance of `B9SpliceCertifiedDelete.local_preservation`: the incoming edge keeps both cells;
the served edge is protected by its left reserved front (V3 disjunct 1); the outgoing edge by V3 disjunct 3
(settled predecessor on the left, reserved front on the right), where the right cell is the reserved front
that backed the pending predecessor (or, on a ring of two, the unchanged left reserved front). -/

namespace B9SpliceSettleRepairSafe

open Q11593SpliceControllerDesign
  B9SpliceControllerR1Table
  B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3
  B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7
  B9OrphanToFence
  B9SpliceTableV10g
  B9SpliceCertifiedDelete

variable {n psi kappa tau : Nat}

def settleAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = ring.rightNeighbor e then settleV6 (C (ring.rightNeighbor e)) else C i

theorem settleAt_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    settleAt ring C e (ring.rightNeighbor e) = settleV6 (C (ring.rightNeighbor e)) := by
  simp [settleAt]

theorem settleAt_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h : i ≠ ring.rightNeighbor e) : settleAt ring C e i = C i := by
  simp [settleAt, h]

theorem settle_role (u : R1AgentStateV6 psi kappa tau) : role (settleV6 u).carrier = .predecessorArmed := rfl
theorem settle_pending (u : R1AgentStateV6 psi kappa tau) : (settleV6 u).carrier.repairPending = false := rfl
theorem settle_ticket (u : R1AgentStateV6 psi kappa tau) : (settleV6 u).acquireTicket = false := rfl
theorem settle_base (u : R1AgentStateV6 psi kappa tau) :
    (settleV6 u).carrier.splice.base = u.carrier.splice.base := rfl

theorem settleAt_base (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (settleAt ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  unfold settleAt
  split
  · rename_i h; subst h; rfl
  · rfl

theorem settleAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hRF : ReservedFrontHoldGuard (C e).carrier)
    (hjrole : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed)
    (hjpend : (C (ring.rightNeighbor e)).carrier.repairPending = true) :
    SpliceSafeV7g hpsi ring (settleAt ring C e) := by
  have hDe : settleAt ring C e e = C e := settleAt_other ring C e e (Ne.symm hself)
  have hDj := settleAt_j ring C e
  -- backing of the pending predecessor at j: its right neighbour is an unticketed reserved front
  have hback := hS.2.2 _ hjrole hjpend
  refine local_preservation hpsi ring C (settleAt ring C e) e hself
    (fun i _ hij => settleAt_other ring C e i hij) hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- incoming edge
    intro x hre hdx
    by_cases hxj : x = ring.rightNeighbor e
    · -- ring of two: the incoming edge starts at j; settled predecessor before the reserved front e
      subst hxj
      left; left
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      rw [hDj, hre, hDe]
      exact Or.inr (Or.inr ⟨settle_role _, settle_pending _, Or.inl hRF⟩)
    · have h1 : settleAt ring C e x = C x := settleAt_other ring C e x hxj
      have h2 : settleAt ring C e (ring.rightNeighbor x) = C (ring.rightNeighbor x) := by
        rw [hre]; exact hDe
      have hdC := (danger_congr hpsi ring C (settleAt ring C e) x (by rw [h1]) (by rw [h2])).1 hdx
      exact (protected_congr ring C (settleAt ring C e) x h1 h2).2 (hS.1 x hdC)
  · -- served edge: left reserved front
    intro _
    left; left
    unfold R1ProtectedSpliceEdgeV3 projectV6
    dsimp only
    rw [hDe]
    exact Or.inl hRF
  · -- outgoing edge: settled predecessor on the left, reserved front on the right
    intro _
    left; left
    unfold R1ProtectedSpliceEdgeV3 projectV6
    dsimp only
    rw [hDj]
    refine Or.inr (Or.inr ⟨settle_role _, settle_pending _, Or.inl ?_⟩)
    by_cases hs : ring.rightNeighbor (ring.rightNeighbor e) = ring.rightNeighbor e
    · exact absurd (rightNeighbor_inj ring hs) hself
    · rw [settleAt_other ring C e _ hs]
      exact hback.1
  · -- ticket shape at e: unchanged
    rw [hDe]; exact hS.2.1 e
  · -- ticket shape at j: cleared
    rw [hDj]; intro ht; exact absurd ht (by rw [settle_ticket]; decide)
  · -- backing for a pending predecessor entering e: e is unchanged and was its backing
    intro x hre _ hrole hpend
    have hb := hS.2.2 x hrole hpend
    rw [hre] at hb
    rw [hDe]
    exact hb
  · -- e is a reserved front, not a predecessor
    intro hrole _
    rw [hDe, hRF.1] at hrole
    exact absurd hrole (by decide)
  · -- j is settled
    intro _ hpend
    rw [hDj, settle_pending] at hpend
    exact absurd hpend (by decide)

/-- Repair (ii): the ownerless pending predecessor row writes `(fenceV6 l, settleV6 r)`.  It preserves
`SpliceSafeV7g` with or without leaders. -/
theorem fenceSettleAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hlnone : role (C e).carrier = .none)
    (hjrole : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed)
    (hjpend : (C (ring.rightNeighbor e)).carrier.repairPending = true) :
    SpliceSafeV7g hpsi ring (fenceSettleAt ring C e) := by
  have hDe : fenceSettleAt ring C e e = fenceV6 (C e) := fs_at_e ring C e
  have hDj := fs_at_j ring C e hself
  have hback := hS.2.2 _ hjrole hjpend
  -- the backing reserved front of j is not e (e is neutral)
  have hs_ne_e : ring.rightNeighbor (ring.rightNeighbor e) ≠ e := by
    intro h
    have := hback.1.1
    rw [h, hlnone] at this
    exact absurd this (by decide)
  have hs_ne_j : ring.rightNeighbor (ring.rightNeighbor e) ≠ ring.rightNeighbor e :=
    fun h => hself (rightNeighbor_inj ring h)
  refine local_preservation hpsi ring C (fenceSettleAt ring C e) e hself
    (fun i hie hij => fs_at_other ring C e i hie hij) hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- incoming edge: protection came from the unchanged left cell
    intro x hre hdx
    by_cases hxj : x = ring.rightNeighbor e
    · -- would make e the backing of j, impossible
      rw [hxj] at hre
      exact absurd hre hs_ne_e
    have hxe : x ≠ e := by
      intro h; rw [h] at hre; exact hself hre
    have h1 : fenceSettleAt ring C e x = C x := fs_at_other ring C e x hxe hxj
    have hdC := (fs_dangerAt_iff hpsi ring C e x).1 hdx
    rcases hS.1 x hdC with hv | hpoh
    · rcases hv with hv3 | hf
      · unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
        dsimp only at hv3
        rcases hv3 with h31 | h32 | h33
        · left; left
          unfold R1ProtectedSpliceEdgeV3 projectV6
          dsimp only
          rw [h1]
          exact Or.inl h31
        · have := h32.1
          rw [hre, hlnone] at this
          exact absurd this (by decide)
        · rcases h33.2.2 with hr1 | hr2 | hr3
          · have := hr1.1
            rw [hre, hlnone] at this
            exact absurd this (by decide)
          · have := hr2.1
            rw [hre, hlnone] at this
            exact absurd this (by decide)
          · have := hr3.1
            rw [hre, hlnone] at this
            exact absurd this (by decide)
      · left; right
        rw [h1]; exact hf
    · have := hpoh.2.2.1.1
      rw [hre, hlnone] at this
      exact absurd this (by decide)
  · -- served edge: left fence
    intro _
    left; right
    rw [hDe]; exact fence_shape _
  · -- outgoing edge: settled predecessor before the reserved front backing j
    intro _
    left; left
    unfold R1ProtectedSpliceEdgeV3 projectV6
    dsimp only
    rw [hDj, fs_at_other ring C e _ hs_ne_e hs_ne_j]
    exact Or.inr (Or.inr ⟨settle_role _, settle_pending _, Or.inl hback.1⟩)
  · -- ticket shape at e: a fence
    rw [hDe]; intro _; exact Or.inr (fence_shape _)
  · -- ticket shape at j: cleared
    rw [hDj]; intro ht; exact absurd ht (by rw [settle_ticket]; decide)
  · -- a pending predecessor entering e would need e to be a reserved front
    intro x hre _ hrole hpend
    have hb := hS.2.2 x hrole hpend
    rw [hre] at hb
    have := hb.1.1
    rw [hlnone] at this
    exact absurd this (by decide)
  · -- e is a fence
    intro hrole _
    rw [hDe] at hrole
    have hn : role (fenceV6 (C e)).carrier = .none := rfl
    rw [hn] at hrole
    exact absurd hrole (by decide)
  · -- j is settled
    intro _ hpend
    rw [hDj, settle_pending] at hpend
    exact absurd hpend (by decide)

end B9SpliceSettleRepairSafe

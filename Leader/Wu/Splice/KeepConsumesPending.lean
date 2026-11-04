import Leader.Wu.Splice.FullCarrierRows

set_option autoImplicit false
set_option Elab.async false

namespace ZZKeepConsumesPending

open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
open B9OrphanToFence

variable {psi kappa tau : Nat} {P : Type}

/--
Exact residual left by the fifth branch of `row10dgPlanP`:
a dg-level KEEP either sees a pending right endpoint in one of the four
new dg guards, or the KEEP was inherited from `row10cActionP`.
-/
theorem row10dg_keep_pendingR_or_row10c_keep
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P)
    (h : (row10dgPlanP laws host hpsi l r).action =
      PhysicalAction.keep) :
    (toOld laws r).carrier.repairPending = true ∨
      row10cActionP laws host hpsi l r = PhysicalAction.keep := by
  classical
  rw [B9FullCarrierRows.row10dgPlanP.eq_1] at h
  try dsimp only at h
  by_cases h1 : OrphanReservedFrontGuardV3
      (toOld laws l).carrier (toOld laws r).carrier
  · exact Or.inl h1.1.2
  · rw [if_neg h1] at h
    by_cases h2 : OrphanVictimGuard (toOld laws l) (toOld laws r)
    · exact Or.inl h2.2.1
    · rw [if_neg h2] at h
      by_cases h3 : OwnedPendingVictimGuard (toOld laws l) (toOld laws r)
      · exact Or.inl h3.2.2.2
      · rw [if_neg h3] at h
        by_cases h4 : OwnerlessPendingPredGuard
            (toOld laws l) (toOld laws r)
        · exact Or.inl h4.2.2
        · rw [if_neg h4] at h
          right
          simpa only [planFromRow] using h

/--
LEMMA A, restricted exactly to the four dg-specific KEEP branches.
`hLower` excludes the fifth/fallthrough branch being KEEP.
-/
theorem row10dg_keep_requires_pendingR
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P)
    (h : (row10dgPlanP laws host hpsi l r).action =
      PhysicalAction.keep)
    (hLower :
      row10cActionP laws host hpsi l r ≠ PhysicalAction.keep) :
    (toOld laws r).carrier.repairPending = true := by
  rcases row10dg_keep_pendingR_or_row10c_keep
      laws host hpsi l r h with hp | hc
  · exact hp
  · exact (hLower hc).elim

/--
LEMMA B, with the same exact restriction.
`RowPlan` stores the old-controller pair in field `out`, not `pair`.
-/
theorem row10dg_keep_clears_pendingR
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P)
    (h : (row10dgPlanP laws host hpsi l r).action =
      PhysicalAction.keep)
    (hLower :
      row10cActionP laws host hpsi l r ≠ PhysicalAction.keep) :
    ((row10dgPlanP laws host hpsi l r).out.2).carrier.repairPending =
      false := by
  classical
  rw [B9FullCarrierRows.row10dgPlanP.eq_1] at h ⊢
  try dsimp only at h
  try dsimp only
  by_cases h1 : OrphanReservedFrontGuardV3
      (toOld laws l).carrier (toOld laws r).carrier
  · rw [if_pos h1] at h ⊢
    rfl
  · rw [if_neg h1] at h ⊢
    by_cases h2 : OrphanVictimGuard (toOld laws l) (toOld laws r)
    · rw [if_pos h2] at h ⊢
      rfl
    · rw [if_neg h2] at h ⊢
      by_cases h3 : OwnedPendingVictimGuard (toOld laws l) (toOld laws r)
      · rw [if_pos h3] at h ⊢
        rfl
      · rw [if_neg h3] at h ⊢
        by_cases h4 : OwnerlessPendingPredGuard
            (toOld laws l) (toOld laws r)
        · rw [if_pos h4] at h ⊢
          rfl
        · rw [if_neg h4] at h ⊢
          have hc :
              row10cActionP laws host hpsi l r =
                PhysicalAction.keep := by
            simpa only [planFromRow] using h
          exact (hLower hc).elim

/-- The fifth branch genuinely has a KEEP constructor of its own. -/
theorem row10c_keep_of_zeroRefresh
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P)
    (hz : ZeroRefreshOnlyGuardP laws host hpsi l r) :
    row10cActionP laws host hpsi l r = PhysicalAction.keep := by
  unfold row10cActionP
  rw [B9FullCarrierRows.row10cPlanP.eq_1]
  try dsimp only
  simp only [hz, if_pos]

/--
A literal grep for `repairPending := true` is not a semantic write census:
the accepted V6 table also writes the bit through `setControlV6 ... true`.
-/
theorem moveAcquireFrontWriteV6_mints_pending
    (l r : R1AgentStateV6 psi kappa tau) :
    ((moveAcquireFrontWriteV6 l r).1).carrier.repairPending = true := by
  rfl

end ZZKeepConsumesPending

#print axioms ZZKeepConsumesPending.row10dg_keep_requires_pendingR
#print axioms ZZKeepConsumesPending.row10dg_keep_clears_pendingR

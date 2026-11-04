import Leader.Wu.Splice.PhysicalHoldTransparency
import Leader.Wu.Splice.PhysicalHoldLeaderlessSafe

set_option autoImplicit false

/-! # Ring-global progress for V10e: statement and the first structural lemmas

`GlobalProgressWithin k`: on every leaderless, safe, non-clear configuration there is an edge
whose next `k` services contain a physical service or end below the starting potential. -/

namespace B9SpliceV10eGlobalProgress

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10d B9SpliceTableV10e
  B9SpliceV10eTransparency

variable {n psi width kappa tau : Nat}

def GlobalProgressWithin (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (k : Nat) : Prop :=
  ∀ (C : R1ConfigV6 n psi kappa tau),
    (∀ i, (C i).carrier.splice.base.core.core.leader = false) →
    SpliceSafeV7 hpsi ring C → ¬ RolesClearV7 C →
    ∃ e : Fin n, ∃ m, m < k ∧
      (PhysicalServiceAt hpsi hwidth hle ring
          (serveIter hpsi hwidth hle ring e m C) (serveIter hpsi hwidth hle ring e (m + 1) C) e ∨
        controllerPotentialV6 (serveIter hpsi hwidth hle ring e (m + 1) C) < controllerPotentialV6 C)

/-! ## Ring predecessor -/

theorem rightNeighbor_leftNeighbor (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  show ((i.val + n - 1) % n + 1) % n = i.val
  have hn := ring.hn
  have hi := i.isLt
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have h1 : (i.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show n - 1 + 1 = n by omega, Nat.mod_self, h0]
  · have h1 : (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show i.val - 1 + 1 = i.val by omega]
    exact Nat.mod_eq_of_lt hi

/-! ## Lemma B: the edge into a pending victim drops the potential in one service -/

theorem edge_into_pending_victim_drops
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hv : role (C (ring.rightNeighbor e)).carrier = .victimArmed)
    (hp : (C (ring.rightNeighbor e)).carrier.repairPending = true) :
    controllerPotentialV6 (stepV10e hpsi hwidth hle ring C e) < controllerPotentialV6 C := by
  have hnf : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier := by
    intro ho
    have h0 := ho.1.1
    rw [hv] at h0
    cases h0
  by_cases hov : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))
  · have hchange : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) ≠ (C e, C (ring.rightNeighbor e)) := by
      intro h
      have h2 : role (rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).2.carrier = .none := by
        unfold rowV10d
        rw [if_neg hnf, if_pos hov]
        rfl
      rw [h] at h2
      simp only at h2
      rw [hv] at h2
      cases h2
    rw [stepV10e_of_change hpsi hwidth hle ring C e hne hchange]
    rw [stepV10d_of_orphanVictim hpsi hwidth hle ring C e hne hnf hov]
    have := orphanVictimClear_potential_drop ring C e hov
    omega
  · have hls : role (C e).carrier = .predecessorArmed ∧ (C e).carrier.repairPending = false :=
      Classical.byContradiction (fun hc => hov ⟨hv, hp, hc⟩)
    have howned : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e)) := ⟨hls.1, hls.2, hv, hp⟩
    have hchange : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) ≠ (C e, C (ring.rightNeighbor e)) := by
      intro h
      have h2 : role (rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).2.carrier = .none := by
        unfold rowV10d
        rw [if_neg hnf, if_neg hov, if_pos howned]
        rfl
      rw [h] at h2
      simp only at h2
      rw [hv] at h2
      cases h2
    rw [stepV10e_of_change hpsi hwidth hle ring C e hne hchange]
    rw [stepV10d_of_ownedVictim hpsi hwidth hle ring C e hne hnf hov howned]
    have := fenceFence_potential_drop ring C e hne howned
    omega

end B9SpliceV10eGlobalProgress

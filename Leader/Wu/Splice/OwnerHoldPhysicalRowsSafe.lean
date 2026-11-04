import Leader.Wu.Splice.OwnerHoldFollowerPairSafe
import Leader.Wu.Splice.OwnerHoldLeaderPairSafe
import Leader.Wu.Splice.PhysicalHoldFenceIdentity
import Leader.Wu.Splice.OwnerHoldMoveRowsSafe

set_option autoImplicit false
set_option Elab.async false

/-! # The physical rows of V10h preserve `SpliceSafeV7g` on every served pair

* `physicalHold_followers_preserves_spliceSafeV7g`: a pair of followers, by the birth / deletion-priority /
  open trichotomy of the physical row (`B9SpliceV10hPhysicalHoldFollowerV7g`);
* `physicalHold_preserves_spliceSafeV7g`: any pair on which the row does not delete a left leader
  (`¬ LeftDeletionCandidate`, the condition under which V10h reaches its physical rows), combining the
  follower case with `B9SpliceV10hPhysicalHoldLeaderSafe.physHoldAt_preserves_spliceSafeV7g_leader`;
* `settledPredFence_preserves_spliceSafeV7g`: fencing a settled predecessor, on every configuration;
* `physicalFence_preserves_spliceSafeV7g`: physical row then fence of a settled predecessor on the right;
* `ordinaryHost_preserves_spliceSafeV7g`: the V7 ordinary host row on an unticketed pair with a neutral right
  cell. -/

namespace B9SpliceV10hPhysicalRowsSafe

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceCertifiedDelete
  B9SpliceV10ePhysicalHoldNoBirth B9SpliceV10hPhysicalHoldFollowerV7g
  B9SpliceV10hPhysicalHoldLeaderSafe B9SpliceV10eFenceIdentity B9SpliceV10dRowsSafeV7g
  B9SpliceMoveRowsSafeV7g

variable {n psi width kappa tau : Nat}

theorem physicalHold_followers_preserves_spliceSafeV7g
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7g hpsi ring C)
    (hself : ring.rightNeighbor e ≠ e)
    (hrshape : (role (C (ring.rightNeighbor e)).carrier = .none ∧
        (C (ring.rightNeighbor e)).carrier.repairPending = false) ∨
      ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier)
    (hl : (C e).carrier.splice.base.core.core.leader = false)
    (hr : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false) :
    SpliceSafeV7g hpsi ring (physicalHoldAt hpsi hwidth hle ring C e) := by
  by_cases hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = true
  · exact physicalHold_birth_preserves_spliceSafeV7g hpsi hwidth hle ring C e hsafe hself hrshape hl hr hb
  · have hb' : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
        (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = false := by
      cases hh : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
        (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base
      · rfl
      · exact absurd hh hb
    by_cases hr0 : deletionActive (normalizeDeletion
        (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase) = true
    · exact physicalHold_deletion_preserves_spliceSafeV7g hpsi hwidth hle ring C e hsafe hself hl hr (Or.inl hr0)
    · have hr0' : deletionActive (normalizeDeletion
          (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase) = false := by
        cases hh : deletionActive (normalizeDeletion
          (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase)
        · rfl
        · exact absurd hh hr0
      by_cases hl0 : deletionActive (normalizeDeletion
          (prepareExpiringDisposal hpsi (C e).carrier.splice.base).core.erase) = true
      · exact physicalHold_deletion_preserves_spliceSafeV7g hpsi hwidth hle ring C e hsafe hself hl hr
          (Or.inr ⟨hr0', hl0⟩)
      · have hl0' : deletionActive (normalizeDeletion
            (prepareExpiringDisposal hpsi (C e).carrier.splice.base).core.erase) = false := by
          cases hh : deletionActive (normalizeDeletion
            (prepareExpiringDisposal hpsi (C e).carrier.splice.base).core.erase)
          · rfl
          · exact absurd hh hl0
        have hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hpsi
            (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base :=
          ⟨hr0', hl0'⟩
        exact physicalHold_no_birth_preserves_spliceSafeV7g hpsi hwidth hle ring C e hsafe hself hrshape
          hl hr hopen hb'

/-- Outside a left-leader deletion the row keeps a left leader. -/
theorem keep_of_not_candidate (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hno : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice) :
    l.carrier.splice.base.core.core.leader = true →
      (hostOut hpsi hwidth hle l r).1.core.core.leader = true := by
  intro hl
  cases hh : (hostOut hpsi hwidth hle l r).1.core.core.leader
  · exact absurd ⟨hl, hh⟩ hno
  · rfl

theorem physHoldAt_eq (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    physHoldAt hpsi hwidth hle ring C e = physicalHoldAt hpsi hwidth hle ring C e := rfl

theorem physicalHold_preserves_spliceSafeV7g
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7g hpsi ring C)
    (hself : ring.rightNeighbor e ≠ e)
    (hrshape : (role (C (ring.rightNeighbor e)).carrier = .none ∧
        (C (ring.rightNeighbor e)).carrier.repairPending = false) ∨
      ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier)
    (hno : ¬ LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice
      (C (ring.rightNeighbor e)).carrier.splice) :
    SpliceSafeV7g hpsi ring (physicalHoldAt hpsi hwidth hle ring C e) := by
  cases hl : (C e).carrier.splice.base.core.core.leader
  · cases hr : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader
    · exact physicalHold_followers_preserves_spliceSafeV7g hpsi hwidth hle ring C e hsafe hself hrshape hl hr
    · rw [← physHoldAt_eq]
      exact physHoldAt_preserves_spliceSafeV7g_leader hpsi hwidth hle ring C e hself hsafe (Or.inr hr)
        (keep_of_not_candidate hpsi hwidth hle _ _ hno) hrshape
  · rw [← physHoldAt_eq]
    exact physHoldAt_preserves_spliceSafeV7g_leader hpsi hwidth hle ring C e hself hsafe (Or.inl hl)
      (keep_of_not_candidate hpsi hwidth hle _ _ hno) hrshape

/-- Fencing a settled predecessor preserves `SpliceSafeV7g` on every configuration. -/
theorem settledPredFence_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hpred : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed)
    (hset : (C (ring.rightNeighbor e)).carrier.repairPending = false) :
    SpliceSafeV7g hpsi ring (orphanToFenceAt ring C e) := by
  classical
  let D := orphanToFenceAt ring C e
  have hDj : D (ring.rightNeighbor e) = fenceV6 (C (ring.rightNeighbor e)) := at_j ring C e
  have hDo : ∀ i, i ≠ ring.rightNeighbor e → D i = C i := fun i h => at_other ring C e i h
  have hDe : D e = C e := hDo e (Ne.symm hself)
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base := base_eq ring C e
  have hfence : HostFenceShapeV7 (D (ring.rightNeighbor e)) := by rw [hDj]; exact fence_shape _
  refine local_preservation hpsi ring C D e hself (fun i _ hij => hDo i hij) hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    by_cases hxj : x = ring.rightNeighbor e
    · left; right; rw [hxj]; exact hfence
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    exact (protected_congr ring C D x (hDo x hxj) (by rw [hre, hDe])).2 (hS.1 x hdC)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb e).1 hdx
    exact protection_from_left_of_right_settled ring C D e hDe hpred hset (hS.1 e hdC)
  · intro _
    left; right; exact hfence
  · rw [hDe]; exact hS.2.1 e
  · intro _; exact Or.inr hfence
  · intro x hre hxj hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    rw [hDe]; exact hbk
  · intro hrole hpend
    rw [hDe] at hrole hpend
    have hbk := hS.2.2 e hrole hpend
    exact absurd (hbk.1.1.symm.trans hpred) (by decide)
  · intro hrole _
    have := hfence.1
    rw [hrole] at this
    exact absurd this (by decide)

theorem physicalFence_preserves_spliceSafeV7g
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7g hpsi ring C)
    (hself : ring.rightNeighbor e ≠ e)
    (hpred : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed)
    (hset : (C (ring.rightNeighbor e)).carrier.repairPending = false)
    (hno : ¬ LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice
      (C (ring.rightNeighbor e)).carrier.splice) :
    SpliceSafeV7g hpsi ring (physicalFenceAt hpsi hwidth hle ring C e) := by
  rw [physicalFenceAt_eq_hold_of_fence hpsi hwidth hle ring C e hself]
  have hF := settledPredFence_preserves_spliceSafeV7g hpsi ring C e hself hsafe hpred hset
  have hCe : orphanToFenceAt ring C e e = C e := at_other ring C e e (Ne.symm hself)
  have hCj : orphanToFenceAt ring C e (ring.rightNeighbor e) = fenceV6 (C (ring.rightNeighbor e)) :=
    at_j ring C e
  refine physicalHold_preserves_spliceSafeV7g hpsi hwidth hle ring _ e hF hself ?_ ?_
  · left; rw [hCj]; exact ⟨rfl, rfl⟩
  · rw [hCe, hCj]; exact hno

/-- The V7 ordinary host row on an unticketed pair with a neutral right cell (no left-leader deletion). -/
theorem ordinaryHost_preserves_spliceSafeV7g
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7g hpsi ring C)
    (hself : ring.rightNeighbor e ≠ e)
    (hlt : (C e).acquireTicket = false) (hrt : (C (ring.rightNeighbor e)).acquireTicket = false)
    (hrneutral : role (C (ring.rightNeighbor e)).carrier = .none ∧
      (C (ring.rightNeighbor e)).carrier.repairPending = false)
    (hno : ¬ LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice
      (C (ring.rightNeighbor e)).carrier.splice) :
    SpliceSafeV7g hpsi ring (ordinaryAt hpsi hwidth hle ring C e) := by
  have hEq : ordinaryAt hpsi hwidth hle ring C e = physicalHoldAt hpsi hwidth hle ring C e := by
    unfold ordinaryAt physicalHoldAt
    rw [ordinaryHostWriteV7_eq_physicalHoldV6 hpsi hwidth hle _ _ hlt hrt]
  rw [hEq]
  exact physicalHold_preserves_spliceSafeV7g hpsi hwidth hle ring C e hsafe hself (Or.inl hrneutral) hno

end B9SpliceV10hPhysicalRowsSafe

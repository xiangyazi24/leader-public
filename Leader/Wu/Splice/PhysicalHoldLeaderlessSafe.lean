import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
import Leader.Wu.Splice.PhysicalHoldDeletionSafe
import Leader.Wu.Splice.PhysicalHoldBirthSafe
import Leader.Wu.Splice.ZeroRefreshLeaderlessSafe
import Leader.Wu.Splice.PhysicalHoldFenceIdentity
import Leader.Wu.Splice.FrontPendingPredClear
import Leader.Wu.Splice.CertFreeLeftSafe

set_option autoImplicit false
set_option Elab.async false

/-! # V10e whole-step safety for leaderless configurations, relative to V10c only

The physical-hold input of `stepV10e_preserves_spliceSafeV7` is discharged by the three
branch theorems (birth, deletion priority, no birth) through the propositional trichotomy of
the physical row, and the settled-predecessor fence input by fencing the predecessor first
(safe on any configuration) and then applying the physical hold to the fenced pair. -/

namespace B9SpliceV10eAssembly

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceV8LabelFrame B9OrphanToFence
  B9SpliceTableV10d B9SpliceTableV10e B9SpliceV10cLiveness B9SpliceV10ePhysicalHoldNoBirth
  B9SpliceV10ePhysicalHoldDeletion B9SpliceV10ePhysicalHoldBirth B9SpliceV10eFenceIdentity
  B9SpliceFrontPendingPredClear B9SpliceV10cRowCertFreeLeft

variable {n psi width kappa tau : Nat}

/-! ## C. Shape of the right endpoint at the physical branch -/

theorem rshape_of_stutter
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (h : rowV10d hpsi hwidth hle l r = (l, r))
    (h1 : ¬ VictimRightScrubGuardV6 r)
    (h2 : ¬ FrontRightScrubGuardV6 r)
    (h3 : ¬ MalformedRightPendingGuardV6 r)
    (h4 : ¬ role r.carrier = .predecessorArmed) :
    (role r.carrier = .none ∧ r.carrier.repairPending = false) ∨ ReservedFrontHoldGuard r.carrier := by
  cases hrole : role r.carrier with
  | none =>
      cases hpend : r.carrier.repairPending with
      | false => exact Or.inl ⟨rfl, rfl⟩
      | true =>
          exact absurd ⟨hpend, by rw [hrole]; decide, by rw [hrole]; decide, by rw [hrole]; decide⟩ h3
  | front =>
      cases hpend : r.carrier.repairPending with
      | false => exact absurd ⟨hrole, hpend⟩ h2
      | true => exact Or.inr ⟨hrole, hpend⟩
  | predecessorArmed => exact absurd hrole h4
  | victimArmed =>
      cases hpend : r.carrier.repairPending with
      | false => exact absurd ⟨hrole, hpend⟩ h1
      | true =>
          -- a pending victim never stutters under V10d
          exfalso
          have hnf : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := by
            intro ho
            have h0 := ho.1.1
            rw [hrole] at h0
            cases h0
          have hkey : role (rowV10d hpsi hwidth hle l r).2.carrier = .none := by
            by_cases hov : OrphanVictimGuard l r
            · have hrow : rowV10d hpsi hwidth hle l r = (l, clearControlV6 r) := by
                unfold rowV10d
                rw [if_neg hnf, if_pos hov]
              rw [hrow]
              rfl
            · have hls : role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = false :=
                Classical.byContradiction (fun hc => hov ⟨hrole, hpend, hc⟩)
              have howned : OwnedPendingVictimGuard l r := ⟨hls.1, hls.2, hrole, hpend⟩
              have hrow : rowV10d hpsi hwidth hle l r = (fenceV6 l, fenceV6 r) := by
                unfold rowV10d
                rw [if_neg hnf, if_neg hov, if_pos howned]
              rw [hrow]
              rfl
          rw [h] at hkey
          simp only at hkey
          rw [hrole] at hkey
          cases hkey

/-! ## D. The physical hold on a leaderless pair -/

theorem physicalHold_preserves_spliceSafeV7_leaderless
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hself : ring.rightNeighbor e ≠ e)
    (hrshape : (role (C (ring.rightNeighbor e)).carrier = .none ∧
        (C (ring.rightNeighbor e)).carrier.repairPending = false) ∨
      ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier)
    (hl : (C e).carrier.splice.base.core.core.leader = false)
    (hr : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false) :
    SpliceSafeV7 hpsi ring (physicalHoldAt hpsi hwidth hle ring C e) := by
  by_cases hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = true
  · exact physicalHold_birth_preserves_spliceSafeV7 hpsi hwidth hle ring C e hsafe hself hrshape hl hr hb
  · have hb' : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
        (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = false := by
      cases hh : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
        (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base
      · rfl
      · exact absurd hh hb
    by_cases hr0 : deletionActive (normalizeDeletion
        (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase) = true
    · exact physicalHold_deletion_preserves_spliceSafeV7 hpsi hwidth hle ring C e hsafe hself hl hr (Or.inl hr0)
    · have hr0' : deletionActive (normalizeDeletion
          (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase) = false := by
        cases hh : deletionActive (normalizeDeletion
          (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase)
        · rfl
        · exact absurd hh hr0
      by_cases hl0 : deletionActive (normalizeDeletion
          (prepareExpiringDisposal hpsi (C e).carrier.splice.base).core.erase) = true
      · exact physicalHold_deletion_preserves_spliceSafeV7 hpsi hwidth hle ring C e hsafe hself hl hr
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
        exact physicalHold_no_birth_preserves_spliceSafeV7 hpsi hwidth hle ring C e hsafe hself hrshape
          hl hr hopen hb'

/-- The V10e left-scrub guard yields a certificate-free left cell. -/
theorem certFreeLeft_of_leftScrub (l r : R1AgentStateV6 psi kappa tau)
    (h : LeftScrubGuardV10e l) : CertFreeLeftV7 l r := by
  rcases h with hv | hf | hm
  · exact victimLeftScrub_certFree l r hv
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hr; exact absurd hr.2 (by rw [hf.2]; decide)
    · intro hp; exact absurd hp.1 (by rw [hf.1]; decide)
    · intro hv; exact absurd hv.1 (by rw [hf.1]; decide)
    · intro hfe; exact absurd hfe.1 (by rw [hf.1]; decide)
    · intro hs; exact absurd hs.1 (by rw [hf.1]; decide)
  · exact malformedLeft_certFree l r hm

/-! ## E. V10e whole-step safety on leaderless configurations -/

/-- V10d whole-step safety with the V10c input given at the served configuration only. -/
theorem stepV10d_preserves_spliceSafeV7_at
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hV10c : SpliceSafeV7 hpsi ring (stepV10c hpsi hwidth hle ring C e))
    (hS : SpliceSafeV7 hpsi ring C) :
    SpliceSafeV7 hpsi ring (stepV10d hpsi hwidth hle ring C e) := by
  by_cases hne : ring.rightNeighbor e = e
  · rw [stepV10d_self hpsi hwidth hle ring C e hne]; exact hS
  by_cases h1 : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [stepV10d_of_orphanFront hpsi hwidth hle ring C e hne h1]
    exact orphanToFence_preserves_spliceSafeV7 hpsi ring C e hS h1
  by_cases h2 : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))
  · rw [stepV10d_of_orphanVictim hpsi hwidth hle ring C e hne h1 h2]
    exact orphanVictimClear_preserves_spliceSafeV7 hpsi ring C e hS h2
  by_cases h2b : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))
  · rw [stepV10d_of_ownedVictim hpsi hwidth hle ring C e hne h1 h2 h2b]
    exact fenceFence_preserves_spliceSafeV7 hpsi ring C e hne hS h2b
  by_cases h3 : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))
  · rw [stepV10d_of_ownerless hpsi hwidth hle ring C e hne h1 h2 h2b h3]
    exact fenceClear_preserves_spliceSafeV7 hpsi ring C e hne hS h3
  · rw [stepV10d_of_none hpsi hwidth hle ring C e hne h1 h2 h2b h3]
    exact hV10c

def Leaderless (C : R1ConfigV6 n psi kappa tau) : Prop :=
  ∀ i, (C i).carrier.splice.base.core.core.leader = false

theorem stepV10e_preserves_spliceSafeV7_leaderless
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hV10c : SpliceSafeV7 hpsi ring (stepV10c hpsi hwidth hle ring C e))
    (hlead : Leaderless C)
    (hS : SpliceSafeV7 hpsi ring C) :
    SpliceSafeV7 hpsi ring (stepV10e hpsi hwidth hle ring C e) := by
  by_cases hne : ring.rightNeighbor e = e
  · rw [stepV10e_self hpsi hwidth hle ring C e hne]; exact hS
  rcases Classical.em (rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e))) with h | h
  · by_cases h1 : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
    · rw [stepV10e_of_victimScrub hpsi hwidth hle ring C e hne h h1]
      refine certFreeClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨?_, ?_, ?_, ?_⟩
      · intro hf; exact absurd hf.1 (by rw [h1.1]; decide)
      · rw [h1.1]; decide
      · intro hv; exact absurd hv.2 (by rw [h1.2]; decide)
      · intro hf; exact absurd hf.1 (by rw [h1.1]; decide)
    by_cases h2 : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
    · rw [stepV10e_of_frontScrub hpsi hwidth hle ring C e hne h h1 h2]
      refine certFreeClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨?_, ?_, ?_, ?_⟩
      · intro hf; exact absurd hf.2 (by rw [h2.2]; decide)
      · rw [h2.1]; decide
      · intro hv; exact absurd hv.1 (by rw [h2.1]; decide)
      · intro hf; exact absurd hf.1 (by rw [h2.1]; decide)
    by_cases h3 : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
    · rw [stepV10e_of_malformedScrub hpsi hwidth hle ring C e hne h h1 h2 h3]
      refine certFreeClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨?_, ?_, ?_, ?_⟩
      · intro hf; exact h3.2.2.1 hf.1
      · exact h3.2.1
      · intro hv; exact h3.2.2.2 hv.1
      · intro hf; exact absurd hf.2.1 (by rw [h3.1]; decide)
    by_cases h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed
    · by_cases h5 : (C (ring.rightNeighbor e)).carrier.repairPending = true
      · by_cases h6 : ReservedFrontHoldGuard (C e).carrier
        · rw [stepV10e_of_frontOwnedPredClear hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6]
          exact frontOwnedPendingPredClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨h6, h4, h5⟩
        by_cases h7 : LeftScrubGuardV10e (C e)
        · rw [stepV10e_of_leftScrub hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6 h7]
          exact certFreeLeftClear_preserves_spliceSafeV7 hpsi ring C e hS
            (certFreeLeft_of_leftScrub (C e) (C (ring.rightNeighbor e)) h7)
        · rw [stepV10e_of_pendingPredHold hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6 h7]; exact hS
      · have h5' : (C (ring.rightNeighbor e)).carrier.repairPending = false := by
          cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
          · rfl
          · exact absurd hp h5
        rw [stepV10e_of_settledPredFence hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5']
        rw [physicalFenceAt_eq_hold_of_fence hpsi hwidth hle ring C e hne]
        have hS' := settledPredFence_preserves_spliceSafeV7 hpsi ring C e hS h4 h5'
        refine physicalHold_preserves_spliceSafeV7_leaderless hpsi hwidth hle ring _ e hS' hne ?_ ?_ ?_
        · left
          rw [at_j]
          exact ⟨rfl, rfl⟩
        · rw [at_other ring C e e (Ne.symm hne)]; exact hlead e
        · rw [at_j, fence_base]; exact hlead _
    · rw [stepV10e_of_physical hpsi hwidth hle ring C e hne h h1 h2 h3 h4]
      exact physicalHold_preserves_spliceSafeV7_leaderless hpsi hwidth hle ring C e hS hne
        (rshape_of_stutter hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) h h1 h2 h3 h4)
        (hlead e) (hlead _)
  · rw [stepV10e_of_change hpsi hwidth hle ring C e hne h]
    exact stepV10d_preserves_spliceSafeV7_at hpsi hwidth hle ring C e hV10c hS

/-- V10e whole-step safety on leaderless configurations, with no remaining input. -/
theorem stepV10e_preserves_spliceSafeV7_leaderless_final
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hlead : Leaderless C) (hS : SpliceSafeV7 hpsi ring C) :
    SpliceSafeV7 hpsi ring (stepV10e hpsi hwidth hle ring C e) :=
  stepV10e_preserves_spliceSafeV7_leaderless hpsi hwidth hle ring C e
    (B9SpliceV10cWholeStepLeaderless.stepV10c_preserves_spliceSafeV7_leaderless
      hpsi hwidth hle ring C e hlead hS)
    hlead hS

end B9SpliceV10eAssembly

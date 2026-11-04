import Leader.Wu.Entrance.PassiveInputNeutralProjection
import Leader.Wu.Splice.RiskHoldRepairSelector

set_option autoImplicit false
set_option Elab.async false

namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows B9SpliceTableHost
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e

variable {n ψ κ τ : Nat} {P : Type}

private theorem q13933_concrete_action_bridge
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ) :
    (concretePortLocal (κ := κ) (τ := τ) hψ h2).action l r =
      fullActionP
        (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
        (hostR2C (κ := κ) (τ := τ) hψ h2) hψ l r := by
  rfl

private theorem q13933_phys_projection_route
    (h : B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause) :
    B9RiskRefinementPhys3.R1ConcreteRowB9PhysicalProjectionObligation :=
  B9RiskRefinementPhys4.r1Host_concreteRowB9PhysicalProjection h

private theorem q13933_holdRepair_projection
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :
    B9RiskRefinement2C.HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := κ) (tau := τ) hψ h2) hψ :=
  B9RiskRefinement2D.r1Host_holdRepairControllerProjectionObligation hψ h2

section OpaqueSelector

attribute [local irreducible]
  B9FullCarrierRows.fullRowPort hostR2C

private theorem q13933_full_host_to_10g
    (laws : PhysCarrierLaws P ψ κ τ) (host : HostRow P)
    (hψ : 0 < ψ) (l r : CellP P)
    (hNo : ¬ ldc (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier)
    (ha : fullActionP laws host hψ l r = .host) :
    row10gActionP laws host hψ l r = .host := by
  unfold fullActionP at ha
  rw [B9FullCarrierRows.fullPlanP.eq_1] at ha
  try dsimp only at ha
  rw [if_neg hNo] at ha
  simpa only [planFromRow] using ha

private theorem q13933_nonstutter_host_to_row7
    (laws : PhysCarrierLaws P ψ κ τ) (host : HostRow P)
    (hψ : 0 < ψ) (l r : CellP P)
    (hq : row10dgP laws host hψ l r ≠ (l, r))
    (ha : row10gActionP laws host hψ l r = .host) :
    row7ActionP laws host hψ l r = .host := by
  classical
  unfold row10gActionP at ha
  rw [B9FullCarrierRows.row10gPlanP.eq_1] at ha
  try dsimp only at ha
  rw [if_neg hq] at ha
  have hdg : row10dgActionP laws host hψ l r = .host := by
    simpa only [planFromRow] using ha
  have hc : row10cActionP laws host hψ l r = .host := by
    unfold row10dgActionP at hdg
    rw [B9FullCarrierRows.row10dgPlanP.eq_1] at hdg
    try dsimp only at hdg
    by_cases h1 : OrphanReservedFrontGuardV3
        (toOld laws l).carrier (toOld laws r).carrier
    · rw [if_pos h1] at hdg
      cases hdg
    · rw [if_neg h1] at hdg
      by_cases h2 : OrphanVictimGuard (toOld laws l) (toOld laws r)
      · rw [if_pos h2] at hdg
        cases hdg
      · rw [if_neg h2] at hdg
        by_cases h3 : OwnedPendingVictimGuard (toOld laws l) (toOld laws r)
        · rw [if_pos h3] at hdg
          cases hdg
        · rw [if_neg h3] at hdg
          by_cases h4 : OwnerlessPendingPredGuard (toOld laws l) (toOld laws r)
          · rw [if_pos h4] at hdg
            cases hdg
          · rw [if_neg h4] at hdg
            simpa only [planFromRow] using hdg
  have hb : row10bActionP laws host hψ l r = .host := by
    unfold row10cActionP at hc
    rw [B9FullCarrierRows.row10cPlanP.eq_1] at hc
    try dsimp only at hc
    by_cases h : ZeroRefreshOnlyGuardP laws host hψ l r
    · rw [if_pos h] at hc
      cases hc
    · rw [if_neg h] at hc
      simpa only [planFromRow] using hc
  have h9 : row9ActionP laws host hψ l r = .host := by
    unfold row10bActionP at hb
    rw [B9FullCarrierRows.row10bPlanP.eq_1] at hb
    try dsimp only at hb
    by_cases h : HostFenceAdvanceGuardV10b hψ (toOld laws l) (toOld laws r)
    · rw [if_pos h] at hb
      cases hb
    · rw [if_neg h] at hb
      simpa only [planFromRow] using hb
  have h8 : row8ActionP laws host hψ l r = .host := by
    unfold row9ActionP at h9
    rw [B9FullCarrierRows.row9PlanP.eq_1] at h9
    try dsimp only at h9
    by_cases h : HostFenceBusyFrontGuardV9 hψ (toOld laws l) (toOld laws r)
    · rw [if_pos h] at h9
      cases h9
    · rw [if_neg h] at h9
      simpa only [planFromRow] using h9
  unfold row8ActionP at h8
  rw [B9FullCarrierRows.row8PlanP.eq_1] at h8
  try dsimp only at h8
  by_cases h : RightStalePredecessorHoldGuardV8 (toOld laws l) (toOld laws r)
  · rw [if_pos h] at h8
    cases h8
  · rw [if_neg h] at h8
    simpa only [planFromRow] using h8

private theorem q13933_row7_host_normal
    (laws : PhysCarrierLaws P ψ κ τ) (host : HostRow P)
    (hψ : 0 < ψ) (l r : CellP P)
    (hNo : ¬ ldc (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier)
    (ha : row7ActionP laws host hψ l r = .host) :
    l.spliceRole = .none ∧ l.repairPending = false ∧
      l.acquireTicket = false ∧ r.spliceRole ≠ .front := by
  classical
  rw [B9FullCarrierHost.row7ActionP.eq_1 laws host hψ l r] at ha
  try dsimp only at ha
  have hFL : ¬ HostFenceShapeV7 (toOld laws l) := by
    intro h
    rw [if_pos h] at ha
    by_cases hb : LocalPreparedBarrier hψ (toOld laws l).carrier (toOld laws r).carrier
    · rw [if_pos hb] at ha
      by_cases hc : HostFenceTargetClearV7 (toOld laws r)
      · rw [if_pos hc] at ha; cases ha
      · rw [if_neg hc] at ha; cases ha
    · rw [if_neg hb] at ha; cases ha
  rw [if_neg hFL] at ha
  have hFR0 : ¬ HostFenceShapeV7 (toOld laws r) := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hFR0] at ha
  have hMAF : ¬ MoveAcquireFrontGuardV6 hψ (toOld laws l) (toOld laws r) := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hMAF] at ha
  have hAA : ¬ ArmAGuardH (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hAA] at ha
  have hAB : ¬ ArmBGuard (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hAB] at ha
  have hDel : ¬ DeleteGuardH (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier := by
    intro h
    exact hNo h.2.2.2.2
  rw [if_neg hDel] at ha
  have hPH : ¬ PendingHoldGuardH (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hPH] at ha
  have hPA : ¬ PendingAbortGuardH (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hPA] at ha
  have hMC : ¬ MoveCommitGuard (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hMC] at ha
  have hMS : ¬ MoveStopGuardV3 hψ (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hMS] at ha
  have hSK : ¬ MoveSeekGuardV3 hψ (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hSK] at ha
  have hSKH : ¬ MoveSeekHoldGuardV3 (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hSKH] at ha
  have hPOA : ¬ PendingOwnerAbortGuardV3 (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hPOA] at ha
  have hPP : ¬ (role (toOld laws l).carrier = .predecessorArmed ∧
      (toOld laws l).carrier.repairPending = true) := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hPP] at ha
  have hMAL : ¬ MoveAcquireLegacyGuardV6 (toOld laws l) (toOld laws r) := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hMAL] at ha
  have hMAA : ¬ MoveAcquireAbortGuardV3 (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hMAA] at ha
  have hORF : ¬ OrphanReservedFrontGuardV3 (toOld laws l).carrier (toOld laws r).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hORF] at ha
  have hRF : ¬ ReservedFrontHoldGuard (toOld laws l).carrier := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hRF] at ha
  have hVR : ¬ VictimRightScrubGuardV6 (toOld laws r) := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hVR] at ha
  have hVL : ¬ VictimLeftScrubGuardV6 (toOld laws l) := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hVL] at ha
  have hFC : ¬ FrontRightScrubGuardV6 (toOld laws r) := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hFC] at ha
  have hML : ¬ MalformedLeftPendingGuardV6 (toOld laws l) := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hML] at ha
  have hMR : ¬ MalformedRightPendingGuardV6 (toOld laws r) := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hMR] at ha
  have hPred : ¬ role (toOld laws l).carrier = .predecessorArmed := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hPred] at ha
  have hFront : ¬ role (toOld laws l).carrier = .front := by
    intro h; rw [if_pos h] at ha; cases ha
  rw [if_neg hFront] at ha
  have hMH : ¬ MarkedHoldGuardV6 (toOld laws l) (toOld laws r) := by
    intro h; rw [if_pos h] at ha; cases ha
  have hl : l.spliceRole = .none := by
    by_cases h : l.spliceRole = .none
    · exact h
    exfalso
    apply hMH
    simp [B9SpliceControllerR1TableV6.MarkedHoldGuardV6,
      B9FullCarrierHost.toOld, B9SpliceControllerR1Table.role, h]
  have hp : l.repairPending = false := by
    cases h : l.repairPending with
    | false => rfl
    | true =>
        exfalso
        apply hML
        simp [B9SpliceControllerR1TableV6.MalformedLeftPendingGuardV6,
          B9FullCarrierHost.toOld, B9SpliceControllerR1Table.role, hl, h]
  have ht : l.acquireTicket = false := by
    cases h : l.acquireTicket with
    | false => rfl
    | true =>
        exfalso
        apply hFL
        simp [B9SpliceControllerR1TableV7.HostFenceShapeV7,
          B9FullCarrierHost.toOld, B9SpliceControllerR1Table.role, hl, hp, h]
  have hr : r.spliceRole ≠ .front := by
    intro hf
    cases h : r.repairPending with
    | false =>
        apply hFC
        simp [B9SpliceControllerR1TableV6.FrontRightScrubGuardV6,
          B9FullCarrierHost.toOld, B9SpliceControllerR1Table.role, hf, h]
    | true =>
        apply hMH
        simp [B9SpliceControllerR1TableV6.MarkedHoldGuardV6,
          B9FullCarrierHost.toOld, B9SpliceControllerR1Table.role, hf, h]
  exact ⟨hl, hp, ht, hr⟩


/-- First unclosed selector.  `row10gPlanP` deliberately turns a complete
lower-row stutter into an operational HOST service, so endpoint/physical
projection cannot recover these input-controller facts. -/
def ConcreteV10gHostStutterSelectorResidual
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : Prop :=
  ∀ (l r : Cell ψ κ τ),
    (¬ ldc
      (shadowHostAt
        (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
        (hostR2C (κ := κ) (τ := τ) hψ h2) l.phys r.phys)
      (toOld (carrierLaws (ψ := ψ) (κ := κ) (τ := τ)) l).carrier
      (toOld (carrierLaws (ψ := ψ) (κ := κ) (τ := τ)) r).carrier) →
    row10dgP
      (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
      (hostR2C (κ := κ) (τ := τ) hψ h2) hψ l r = (l, r) →
    row10gActionP
      (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
      (hostR2C (κ := κ) (τ := τ) hψ h2) hψ l r = .host →
      l.spliceRole ≠ .predecessorArmed ∧
      l.spliceRole ≠ .victimArmed ∧
      r.spliceRole ≠ .front ∧
      (l.spliceRole = .none →
        l.repairPending = false ∧ l.acquireTicket = false)

theorem concretePortHostSelectorResidual_of_v10gStutter
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (hS : ConcreteV10gHostStutterSelectorResidual
      (κ := κ) (τ := τ) hψ h2) :
    ConcretePortHostSelectorResidual
      (κ := κ) (τ := τ) hψ h2 := by
  intro l r hNo ha
  have haFull :
      fullActionP
        (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
        (hostR2C (κ := κ) (τ := τ) hψ h2) hψ l r = .host := by
    rw [← q13933_concrete_action_bridge hψ h2 l r]
    exact ha
  have h10 := q13933_full_host_to_10g
    (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
    (hostR2C (κ := κ) (τ := τ) hψ h2) hψ l r hNo haFull
  by_cases hq :
      row10dgP
        (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
        (hostR2C (κ := κ) (τ := τ) hψ h2) hψ l r = (l, r)
  · exact hS l r hNo hq h10
  · have h7 := q13933_nonstutter_host_to_row7
      (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
      (hostR2C (κ := κ) (τ := τ) hψ h2) hψ l r hq h10
    have hn := q13933_row7_host_normal
      (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
      (hostR2C (κ := κ) (τ := τ) hψ h2) hψ l r hNo h7
    rcases hn with ⟨hl, hp, ht, hr⟩
    refine ⟨?_, ?_, hr, ?_⟩
    · intro h; rw [hl] at h; cases h
    · intro h; rw [hl] at h; cases h
    · intro _; exact ⟨hp, ht⟩

theorem concreteB7PassiveInputOuterNeutral_of_v10gStutter
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hS : ConcreteV10gHostStutterSelectorResidual
      (κ := κ) (τ := τ) hψ h2) :
    ConcreteB7PassiveInputOuterNeutralObligation
      (κ := κ) (τ := τ) hψ h2 ring :=
  concreteB7PassiveInputOuterNeutral_of_selector hψ h2 ring
    (concretePortHostSelectorResidual_of_v10gStutter hψ h2 hS)



end OpaqueSelector
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C

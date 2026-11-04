import Leader.Wu.Entrance.AdmissionNoGarbage
import Leader.Wu.Splice.RiskHoldRepairSelector
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace CFinalJ2Edge2

open CFinalJ2Edge CFinalJ2Landing
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e

variable {n psi : Nat}

private theorem concrete_action_bridge
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi psi (16 * psi)) :
    (concretePortLocal (κ := psi) (τ := 16 * psi) hpsi h2).action l r =
      fullActionP
        (carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi))
        (hostR2C (κ := psi) (τ := 16 * psi) hpsi h2) hpsi l r := by
  rfl

private theorem no_ldc_of_leaderless_left
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi psi (16 * psi))
    (hL : outputFinal l = false) :
    ¬ B9SpliceTableHost.ldc
      (shadowHostAt
        (carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi))
        (hostR2C (κ := psi) (τ := 16 * psi) hpsi h2) l.phys r.phys)
      (toOld (carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi)) l).carrier
      (toOld (carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi)) r).carrier := by
  intro h
  have hl := h.1
  change outputFinal l = true at hl
  rw [hL] at hl
  cases hl

section OpaquePort
attribute [local irreducible] B9FullCarrierRows.fullRowPort hostR2C

private theorem row7_host_of_neutral
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi psi (16 * psi))
    (hNL : NeutralController l) (hNR : NeutralController r)
    (hNo : ¬ B9SpliceTableHost.ldc
      (shadowHostAt
        (carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi))
        (hostR2C (κ := psi) (τ := 16 * psi) hpsi h2) l.phys r.phys)
      (toOld (carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi)) l).carrier
      (toOld (carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi)) r).carrier) :
    row7ActionP
      (carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi))
      (hostR2C (κ := psi) (τ := 16 * psi) hpsi h2) hpsi l r = .host := by
  classical
  unfold NeutralController at hNL hNR
  rcases hNL with ⟨hlr, hlp, hlt⟩
  rcases hNR with ⟨hrr, hrp, hrt⟩
  let laws := carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi)
  let host := hostR2C (κ := psi) (τ := 16 * psi) hpsi h2
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  have hlr' : role lo.carrier = .none := by change l.spliceRole = .none; exact hlr
  have hlp' : lo.carrier.repairPending = false := by change l.repairPending = false; exact hlp
  have hlt' : lo.acquireTicket = false := by change l.acquireTicket = false; exact hlt
  have hrr' : role ro.carrier = .none := by change r.spliceRole = .none; exact hrr
  have hrp' : ro.carrier.repairPending = false := by change r.repairPending = false; exact hrp
  have hrt' : ro.acquireTicket = false := by change r.acquireTicket = false; exact hrt
  have hNo' : ¬ B9SpliceTableHost.ldc oh lo.carrier ro.carrier := by exact hNo
  have hfL : ¬ HostFenceShapeV7 lo := fun h => by
    have ht := h.2.2; rw [hlt'] at ht; cases ht
  have hfR : ¬ HostFenceShapeV7 ro := fun h => by
    have ht := h.2.2; rw [hrt'] at ht; cases ht
  have hRF : ¬ ReservedFrontHoldGuard ro.carrier := fun h => by
    have ht := h.1; rw [hrr'] at ht; cases ht
  have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi lo ro := fun h => hRF h.2.2.2.1
  have hA : ¬ B9SpliceTableHost.ArmAGuardH oh lo.carrier ro.carrier :=
    fun h => hNo' h.2.2.2.2
  have hB : ¬ ArmBGuard lo.carrier ro.carrier := fun h => by
    have ht := h.2.2.1; rw [hrr'] at ht; cases ht
  have hDel : ¬ B9SpliceTableHost.DeleteGuardH oh lo.carrier ro.carrier :=
    fun h => hNo' h.2.2.2.2
  have hPH : ¬ B9SpliceTableHost.PendingHoldGuardH oh lo.carrier ro.carrier :=
    fun h => hNo' h.2.2.2.2
  have hPA : ¬ B9SpliceTableHost.PendingAbortGuardH oh lo.carrier ro.carrier := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hMC : ¬ MoveCommitGuard lo.carrier ro.carrier := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hMS : ¬ MoveStopGuardV3 hpsi lo.carrier ro.carrier := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hSK : ¬ MoveSeekGuardV3 hpsi lo.carrier ro.carrier := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hSKH : ¬ MoveSeekHoldGuardV3 lo.carrier ro.carrier := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hPOA : ¬ PendingOwnerAbortGuardV3 lo.carrier ro.carrier := fun h => by
    have ht := h.1; rw [hrr'] at ht; cases ht
  have hPP : ¬ (role lo.carrier = .predecessorArmed ∧ lo.carrier.repairPending = true) :=
    fun h => by have ht := h.1; rw [hlr'] at ht; cases ht
  have hMAL : ¬ MoveAcquireLegacyGuardV6 lo ro := fun h => hRF h.1.2.2.2
  have hMAA : ¬ MoveAcquireAbortGuardV3 lo.carrier ro.carrier := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hORF : ¬ OrphanReservedFrontGuardV3 lo.carrier ro.carrier := fun h => hRF h.1
  have hRFH : ¬ ReservedFrontHoldGuard lo.carrier := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hVR : ¬ VictimRightScrubGuardV6 ro := fun h => by
    have ht := h.1; rw [hrr'] at ht; cases ht
  have hVL : ¬ VictimLeftScrubGuardV6 lo := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hFR : ¬ FrontRightScrubGuardV6 ro := fun h => by
    have ht := h.1; rw [hrr'] at ht; cases ht
  have hML : ¬ MalformedLeftPendingGuardV6 lo := fun h => by
    have ht := h.1; rw [hlp'] at ht; cases ht
  have hMR : ¬ MalformedRightPendingGuardV6 ro := fun h => by
    have ht := h.1; rw [hrp'] at ht; cases ht
  have hpl : ¬ role lo.carrier = .predecessorArmed := by
    intro h; rw [hlr'] at h; cases h
  have hlf : ¬ role lo.carrier = .front := by
    intro h; rw [hlr'] at h; cases h
  have hmk : ¬ MarkedHoldGuardV6 lo ro := by
    rintro (h | ⟨h, _⟩)
    · exact h hlr'
    · exact h hrr'
  change row7ActionP laws host hpsi l r = .host
  rw [B9FullCarrierHost.row7ActionP.eq_1 laws host hpsi l r]
  try dsimp only
  rw [if_neg hfL, if_neg hfR, if_neg hmaf, if_neg hA, if_neg hB,
    if_neg hDel, if_neg hPH, if_neg hPA, if_neg hMC, if_neg hMS,
    if_neg hSK, if_neg hSKH, if_neg hPOA, if_neg hPP, if_neg hMAL,
    if_neg hMAA, if_neg hORF, if_neg hRFH, if_neg hVR, if_neg hVL,
    if_neg hFR, if_neg hML, if_neg hMR, if_neg hpl, if_neg hlf, if_neg hmk]

theorem concretePort_action_host_of_neutral_leaderless
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi psi (16 * psi))
    (hL : outputFinal l = false)
    (hNL : NeutralController l) (hNR : NeutralController r) :
    (concretePortLocal (κ := psi) (τ := 16 * psi) hpsi h2).action l r = .host := by
  classical
  have hNo := no_ldc_of_leaderless_left hpsi h2 l r hL
  have h7 := row7_host_of_neutral hpsi h2 l r hNL hNR hNo
  unfold NeutralController at hNL hNR
  rcases hNL with ⟨hlr, hlp, hlt⟩
  rcases hNR with ⟨hrr, hrp, hrt⟩
  let laws := carrierLaws (ψ := psi) (κ := psi) (τ := 16 * psi)
  let host := hostR2C (κ := psi) (τ := 16 * psi) hpsi h2
  let lo := toOld laws l
  let ro := toOld laws r
  have hlr' : role lo.carrier = .none := by change l.spliceRole = .none; exact hlr
  have hlt' : lo.acquireTicket = false := by change l.acquireTicket = false; exact hlt
  have hrr' : role ro.carrier = .none := by change r.spliceRole = .none; exact hrr
  have hNo' : ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host l.phys r.phys) lo.carrier ro.carrier := by exact hNo
  have h7' : row7ActionP laws host hpsi l r = .host := by exact h7
  have hRF : ¬ ReservedFrontHoldGuard ro.carrier := fun h => by
    have ht := h.1; rw [hrr'] at ht; cases ht
  have hD1 : ¬ OrphanReservedFrontGuardV3 lo.carrier ro.carrier := fun h => hRF h.1
  have hD2 : ¬ OrphanVictimGuard lo ro := fun h => by
    have ht := h.1; rw [hrr'] at ht; cases ht
  have hD3 : ¬ OwnedPendingVictimGuard lo ro := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hD4 : ¬ OwnerlessPendingPredGuard lo ro := fun h => by
    have ht := h.2.1; rw [hrr'] at ht; cases ht
  have hSP8 : ¬ RightStalePredecessorHoldGuardV8 lo ro := fun h => by
    have ht := h.2.2.2.1; rw [hrr'] at ht; cases ht
  have hBF : ¬ HostFenceBusyFrontGuardV9 hpsi lo ro := fun h => by
    have ht := h.1.2.2; rw [hlt'] at ht; cases ht
  have hHO : ¬ HostFenceAdvanceGuardV10b hpsi lo ro := fun h => by
    have ht := h.1.2.2; rw [hlt'] at ht; cases ht
  rw [concrete_action_bridge hpsi h2 l r]
  change fullActionP laws host hpsi l r = .host
  unfold fullActionP
  rw [B9FullCarrierRows.fullPlanP.eq_1]
  try dsimp only
  rw [if_neg hNo']
  simp only [planFromRow]
  unfold row10gActionP
  rw [B9FullCarrierRows.row10gPlanP.eq_1]
  try dsimp only
  by_cases hq : row10dgP laws host hpsi l r = (l, r)
  · rw [if_pos hq]
    simp [B9FullCarrierHost.toOld, role, hlr, hlp, hlt, hrr, hrp, hrt,
      VictimRightScrubGuardV6, FrontRightScrubGuardV6,
      MalformedRightPendingGuardV6, ReservedFrontHoldGuard,
      LeftScrubGuardV10e]
  · rw [if_neg hq]
    simp only [planFromRow]
    have h8 : row8ActionP laws host hpsi l r = .host := by
      unfold row8ActionP
      rw [B9FullCarrierRows.row8PlanP.eq_1]
      try dsimp only
      rw [if_neg hSP8]
      simpa only [planFromRow] using h7'
    have h9 : row9ActionP laws host hpsi l r = .host := by
      unfold row9ActionP
      rw [B9FullCarrierRows.row9PlanP.eq_1]
      try dsimp only
      rw [if_neg hBF]
      simpa only [planFromRow] using h8
    have hb : row10bActionP laws host hpsi l r = .host := by
      unfold row10bActionP
      rw [B9FullCarrierRows.row10bPlanP.eq_1]
      try dsimp only
      rw [if_neg hHO]
      simpa only [planFromRow] using h9
    have hc : row10cActionP laws host hpsi l r = .host := by
      unfold row10cActionP
      rw [B9FullCarrierRows.row10cPlanP.eq_1]
      try dsimp only
      by_cases hz : ZeroRefreshOnlyGuardP laws host hpsi l r
      · have hcKeep : row10cActionP laws host hpsi l r = .keep := by
          unfold row10cActionP
          rw [B9FullCarrierRows.row10cPlanP.eq_1]
          try dsimp only
          rw [if_pos hz]
        have hcP : row10cP laws host hpsi l r = (l, r) := by
          unfold row10cP
          rw [B9FullCarrierRows.row10cPlanP.eq_1]
          try dsimp only
          rw [if_pos hz]
          simp only [runPlan, transportPair, B9FullCarrierHost.toOld,
            B9FullCarrierHost.ofOldWith, role]
        have hst : row10dgP laws host hpsi l r = (l, r) := by
          unfold row10dgP
          rw [B9FullCarrierRows.row10dgPlanP.eq_1]
          try dsimp only
          rw [if_neg hD1, if_neg hD2, if_neg hD3, if_neg hD4]
          rw [hcKeep, hcP]
          simp only [planFromRow, runPlan, transportPair,
            B9FullCarrierHost.toOld, B9FullCarrierHost.ofOldWith, role]
        exact (hq hst).elim
      · rw [if_neg hz]
        simpa only [planFromRow] using hb
    have hdg : row10dgActionP laws host hpsi l r = .host := by
      unfold row10dgActionP
      rw [B9FullCarrierRows.row10dgPlanP.eq_1]
      try dsimp only
      rw [if_neg hD1, if_neg hD2, if_neg hD3, if_neg hD4]
      simpa only [planFromRow] using hc
    exact hdg

/-- Exact missing ruler fact: unlike `ElectionGeometryV31`, this includes the
wrap edge entering label zero. -/
def FinalCyclicRuler
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi)) : Prop :=
  ∀ a : Fin n,
    ((oldConfig C) (ring.rightNeighbor a)).carrier.splice.base.core.core.label =
      ⟨(((oldConfig C) a).carrier.splice.base.core.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

/-- Producer-side fact still missing from the installed J2 stack. -/
def ConcreteB7PassiveCyclicRulerPostObligation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n psi psi (16 * psi)) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e
    FinalLeaderless D → FinalCyclicRuler hpsi ring D

theorem no_finalHole_of_cyclicRuler
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi psi (16 * psi))
    (hR : FinalCyclicRuler hpsi ring C) (a : Fin n) :
    ¬ FinalHole hpsi (C a) (C (ring.rightNeighbor a)) := by
  intro hH
  have hH' : B9ControllerRecovery.Hole hpsi
      ((oldConfig C) a) ((oldConfig C) (ring.rightNeighbor a)) := hH
  have hD : B9SpliceControllerR1Table.PreparedDangerAt hpsi ring
      (B9SpliceControllerR1TableV6.projectV6 (oldConfig C)) a := hH'.1
  have hp :=
    (B9SpliceV10ePhysicalHoldNoBirth.danger_iff_physical
      hpsi ring (oldConfig C) a).1 hD
  exact hp.2.2 (hR a)

theorem j2C1AdmissionHoleResidual_of_cyclicRulerPost
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hRuler : ConcreteB7PassiveCyclicRulerPostObligation hpsi h2 ring) :
    J2C1AdmissionHoleResidual hpsi h2 ring := by
  intro C e hA hL
  dsimp only
  intro hDL _hGeom _hPrefix _hNeutral a
  exact no_finalHole_of_cyclicRuler hpsi ring
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e)
    (hRuler C e hA hL hDL) a

theorem j2C1AdmissionHostActionResidual_closed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    J2C1AdmissionHostActionResidual hpsi h2 ring := by
  intro C e _hA _hL
  dsimp only
  intro hDL _hGeom _hPrefix hNeutral a
  exact concretePort_action_host_of_neutral_leaderless
    hpsi h2
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e a)
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e
      (ring.rightNeighbor a))
    (hDL a) (hNeutral a) (hNeutral (ring.rightNeighbor a))

end OpaquePort
end CFinalJ2Edge2

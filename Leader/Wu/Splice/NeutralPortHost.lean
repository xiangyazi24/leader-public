import Leader.Wu.Splice.NeutralOrbitLift

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZNeutralPortAction

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g
  B9SpliceTableV10j B9SpliceTableHost

variable {ψ κ τ : Nat} {P : Type}

/-- Both endpoints have the completely neutral outer B9 controller. -/
def AllNeutral (l r : CellP P) : Prop :=
  l.spliceRole = .none ∧
  l.repairPending = false ∧
  l.acquireTicket = false ∧
  r.spliceRole = .none ∧
  r.repairPending = false ∧
  r.acquireTicket = false

/-- Under neutral outer control and no top-level deletion candidate, every
V7 priority guard is false and the V7 action is HOST. -/
private theorem row7_action_host_of_neutral_of_not_ldc
    (laws : PhysCarrierLaws P ψ κ τ)
    (host : HostRow P) (hψ : 0 < ψ)
    (l r : CellP P)
    (hN : AllNeutral l r)
    (hNo : ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier) :
    row7ActionP laws host hψ l r = .host := by
  classical
  rcases hN with ⟨hlr, hlp, hlt, hrr, hrp, hrt⟩
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  have hlr' : role lo.carrier = .none := by
    change l.spliceRole = .none
    exact hlr
  have hlp' : lo.carrier.repairPending = false := by
    change l.repairPending = false
    exact hlp
  have hlt' : lo.acquireTicket = false := by
    change l.acquireTicket = false
    exact hlt
  have hrr' : role ro.carrier = .none := by
    change r.spliceRole = .none
    exact hrr
  have hrp' : ro.carrier.repairPending = false := by
    change r.repairPending = false
    exact hrp
  have hrt' : ro.acquireTicket = false := by
    change r.acquireTicket = false
    exact hrt
  have hNo' : ¬ B9SpliceTableHost.ldc oh lo.carrier ro.carrier := by
    simpa [oh, lo, ro] using hNo
  have hfL : ¬ HostFenceShapeV7 lo := fun h => by
    have ht := h.2.2
    rw [hlt'] at ht
    cases ht
  have hfR : ¬ HostFenceShapeV7 ro := fun h => by
    have ht := h.2.2
    rw [hrt'] at ht
    cases ht
  have hRF : ¬ ReservedFrontHoldGuard ro.carrier := fun h => by
    have ht := h.1
    rw [hrr'] at ht
    cases ht
  have hmaf : ¬ MoveAcquireFrontGuardV6 hψ lo ro :=
    fun h => hRF h.2.2.2.1
  have hA : ¬ B9SpliceTableHost.ArmAGuardH oh lo.carrier ro.carrier :=
    fun h => hNo' h.2.2.2.2
  have hB : ¬ ArmBGuard lo.carrier ro.carrier := fun h => by
    have ht := h.2.2.1
    rw [hrr'] at ht
    cases ht
  have hDel : ¬ B9SpliceTableHost.DeleteGuardH oh lo.carrier ro.carrier :=
    fun h => hNo' h.2.2.2.2
  have hPH : ¬ B9SpliceTableHost.PendingHoldGuardH oh lo.carrier ro.carrier :=
    fun h => hNo' h.2.2.2.2
  have hPA : ¬ B9SpliceTableHost.PendingAbortGuardH oh lo.carrier ro.carrier :=
    fun h => by
      have ht := h.1
      rw [hlr'] at ht
      cases ht
  have hMC : ¬ MoveCommitGuard lo.carrier ro.carrier := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hMS : ¬ MoveStopGuardV3 hψ lo.carrier ro.carrier := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hSK : ¬ MoveSeekGuardV3 hψ lo.carrier ro.carrier := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hSKH : ¬ MoveSeekHoldGuardV3 lo.carrier ro.carrier := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hPOA : ¬ PendingOwnerAbortGuardV3 lo.carrier ro.carrier := fun h => by
    have ht := h.1
    rw [hrr'] at ht
    cases ht
  have hPP : ¬ (role lo.carrier = .predecessorArmed ∧
      lo.carrier.repairPending = true) := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hMAL : ¬ MoveAcquireLegacyGuardV6 lo ro :=
    fun h => hRF h.1.2.2.2
  have hMAA : ¬ MoveAcquireAbortGuardV3 lo.carrier ro.carrier := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hORF : ¬ OrphanReservedFrontGuardV3 lo.carrier ro.carrier :=
    fun h => hRF h.1
  have hRFH : ¬ ReservedFrontHoldGuard lo.carrier := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hVR : ¬ VictimRightScrubGuardV6 ro := fun h => by
    have ht := h.1
    rw [hrr'] at ht
    cases ht
  have hVL : ¬ VictimLeftScrubGuardV6 lo := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hFR : ¬ FrontRightScrubGuardV6 ro := fun h => by
    have ht := h.1
    rw [hrr'] at ht
    cases ht
  have hML : ¬ MalformedLeftPendingGuardV6 lo := fun h => by
    have ht := h.1
    rw [hlp'] at ht
    cases ht
  have hMR : ¬ MalformedRightPendingGuardV6 ro := fun h => by
    have ht := h.1
    rw [hrp'] at ht
    cases ht
  have hpl : ¬ role lo.carrier = .predecessorArmed := by
    intro h
    rw [hlr'] at h
    cases h
  have hlf : ¬ role lo.carrier = .front := by
    intro h
    rw [hlr'] at h
    cases h
  have hmk : ¬ MarkedHoldGuardV6 lo ro := by
    rintro (h | ⟨h, _⟩)
    · exact h hlr'
    · exact h hrr'
  change row7ActionP laws host hψ l r = .host
  rw [B9FullCarrierHost.row7ActionP.eq_1 laws host hψ l r]
  try dsimp only
  rw [if_neg hfL, if_neg hfR, if_neg hmaf, if_neg hA, if_neg hB,
    if_neg hDel, if_neg hPH, if_neg hPA, if_neg hMC, if_neg hMS,
    if_neg hSK, if_neg hSKH, if_neg hPOA, if_neg hPP, if_neg hMAL,
    if_neg hMAA, if_neg hORF, if_neg hRFH, if_neg hVR, if_neg hVL,
    if_neg hFR, if_neg hML, if_neg hMR, if_neg hpl, if_neg hlf, if_neg hmk]

/-- Strong generic theorem: physical payloads are unrestricted.  The `ldc=true`
case is HOST at the top V10j DELETE branch; the `ldc=false` case reaches the
neutral V10g HOST branch. -/
theorem full_action_host_of_neutral
    (laws : PhysCarrierLaws P ψ κ τ)
    (host : HostRow P) (hψ : 0 < ψ)
    (l r : CellP P) (hN : AllNeutral l r) :
    fullActionP laws host hψ l r = .host := by
  classical
  rcases hN with ⟨hlr, hlp, hlt, hrr, hrp, hrt⟩
  have hN' : AllNeutral l r :=
    ⟨hlr, hlp, hlt, hrr, hrp, hrt⟩
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  have hlr' : role lo.carrier = .none := by
    change l.spliceRole = .none
    exact hlr
  have hlp' : lo.carrier.repairPending = false := by
    change l.repairPending = false
    exact hlp
  have hlt' : lo.acquireTicket = false := by
    change l.acquireTicket = false
    exact hlt
  have hrr' : role ro.carrier = .none := by
    change r.spliceRole = .none
    exact hrr
  have hrp' : ro.carrier.repairPending = false := by
    change r.repairPending = false
    exact hrp
  have hrt' : ro.acquireTicket = false := by
    change r.acquireTicket = false
    exact hrt
  have hRF_L : ¬ ReservedFrontHoldGuard lo.carrier := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hRF_R : ¬ ReservedFrontHoldGuard ro.carrier := fun h => by
    have ht := h.1
    rw [hrr'] at ht
    cases ht
  have hfL : ¬ HostFenceShapeV7 lo := fun h => by
    have ht := h.2.2
    rw [hlt'] at ht
    cases ht
  have hSP8 : ¬ RightStalePredecessorHoldGuardV8 lo ro := fun h => by
    have ht := h.2.2.2.1
    rw [hrr'] at ht
    cases ht
  have hBF : ¬ HostFenceBusyFrontGuardV9 hψ lo ro :=
    fun h => hfL h.1
  have hHO : ¬ HostFenceAdvanceGuardV10b hψ lo ro :=
    fun h => hfL h.1
  have hD1 : ¬ OrphanReservedFrontGuardV3 lo.carrier ro.carrier :=
    fun h => hRF_R h.1
  have hD2 : ¬ OrphanVictimGuard lo ro := fun h => by
    have ht := h.1
    rw [hrr'] at ht
    cases ht
  have hD3 : ¬ OwnedPendingVictimGuard lo ro := fun h => by
    have ht := h.1
    rw [hlr'] at ht
    cases ht
  have hD4 : ¬ OwnerlessPendingPredGuard lo ro := fun h => by
    have ht := h.2.1
    rw [hrr'] at ht
    cases ht
  by_cases hLdc : B9SpliceTableHost.ldc oh lo.carrier ro.carrier
  · unfold fullActionP
    rw [B9FullCarrierRows.fullPlanP.eq_1 laws host hψ l r]
    try dsimp only
    rw [if_pos hLdc, if_neg hRF_L]
  · have hNo : ¬ B9SpliceTableHost.ldc
        (shadowHostAt laws host l.phys r.phys)
        (toOld laws l).carrier (toOld laws r).carrier := by
      simpa [oh, lo, ro] using hLdc
    have h7 : row7ActionP laws host hψ l r = .host :=
      row7_action_host_of_neutral_of_not_ldc
        laws host hψ l r hN' hNo
    have h8 : row8ActionP laws host hψ l r = .host := by
      unfold row8ActionP
      rw [B9FullCarrierRows.row8PlanP.eq_1]
      try dsimp only
      rw [if_neg hSP8]
      simpa only [planFromRow] using h7
    have h9 : row9ActionP laws host hψ l r = .host := by
      unfold row9ActionP
      rw [B9FullCarrierRows.row9PlanP.eq_1]
      try dsimp only
      rw [if_neg hBF]
      simpa only [planFromRow] using h8
    have hb : row10bActionP laws host hψ l r = .host := by
      unfold row10bActionP
      rw [B9FullCarrierRows.row10bPlanP.eq_1]
      try dsimp only
      rw [if_neg hHO]
      simpa only [planFromRow] using h9
    change fullActionP laws host hψ l r = .host
    unfold fullActionP
    rw [B9FullCarrierRows.fullPlanP.eq_1]
    try dsimp only
    rw [if_neg hLdc]
    simp only [planFromRow]
    unfold row10gActionP
    rw [B9FullCarrierRows.row10gPlanP.eq_1]
    try dsimp only
    by_cases hq : row10dgP laws host hψ l r = (l, r)
    · rw [if_pos hq]
      simp [B9FullCarrierHost.toOld, role, hlr, hlp, hlt, hrr, hrp, hrt,
        VictimRightScrubGuardV6, FrontRightScrubGuardV6,
        MalformedRightPendingGuardV6, ReservedFrontHoldGuard,
        LeftScrubGuardV10e]
    · rw [if_neg hq]
      simp only [planFromRow]
      have hc : row10cActionP laws host hψ l r = .host := by
        unfold row10cActionP
        rw [B9FullCarrierRows.row10cPlanP.eq_1]
        try dsimp only
        by_cases hz : ZeroRefreshOnlyGuardP laws host hψ l r
        · have hcKeep : row10cActionP laws host hψ l r = .keep := by
            unfold row10cActionP
            rw [B9FullCarrierRows.row10cPlanP.eq_1]
            try dsimp only
            rw [if_pos hz]
          have hcP : row10cP laws host hψ l r = (l, r) := by
            unfold row10cP
            rw [B9FullCarrierRows.row10cPlanP.eq_1]
            try dsimp only
            rw [if_pos hz]
            simp only [runPlan, transportPair, B9FullCarrierHost.toOld,
              B9FullCarrierHost.ofOldWith, role]
          have hst : row10dgP laws host hψ l r = (l, r) := by
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
      have hdg : row10dgActionP laws host hψ l r = .host := by
        unfold row10dgActionP
        rw [B9FullCarrierRows.row10dgPlanP.eq_1]
        try dsimp only
        rw [if_neg hD1, if_neg hD2, if_neg hD3, if_neg hD4]
        simpa only [planFromRow] using hc
      exact hdg

/-- Requested V3.1 concrete-port specialization. -/
theorem port_action_host_of_neutral
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : ZZFinalCarrierV3.Cell ψ κ τ)
    (h : AllNeutral l r) :
    (ZZFinalCarrierV3.concretePortV3
      (κ := κ) (τ := τ) hψ h2).action l r = .host := by
  change fullActionP
    (ZZFinalCarrierV3.carrierLawsV3
      (ψ := ψ) (κ := κ) (τ := τ))
    (ZZFinalCarrierV3.hostR2CV3
      (κ := κ) (τ := τ) hψ h2)
    hψ l r = .host
  exact full_action_host_of_neutral
    (ZZFinalCarrierV3.carrierLawsV3
      (ψ := ψ) (κ := κ) (τ := τ))
    (ZZFinalCarrierV3.hostR2CV3
      (κ := κ) (τ := τ) hψ h2)
    hψ l r h

/-- Outer neutrality of every adjacent pair of the compiled six-ring lift. -/
theorem orbit_pair_allNeutral (e : Fin 6) :
    AllNeutral
      (ZZOrbitLiftClean.liftC e)
      (ZZOrbitLiftClean.liftC
        (ZZOrbitLiftClean.ring6.rightNeighbor e)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem h23 : 2 ≤ 3 := by omega

/-- One theorem covers all six orbit edges; no per-edge evaluation is needed. -/
theorem port_action_host (e : Fin 6) :
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) ZZOrbitLiftClean.h3 h23).action
      (ZZOrbitLiftClean.liftC e)
      (ZZOrbitLiftClean.liftC
        (ZZOrbitLiftClean.ring6.rightNeighbor e)) = .host := by
  exact port_action_host_of_neutral
    ZZOrbitLiftClean.h3 h23
    (ZZOrbitLiftClean.liftC e)
    (ZZOrbitLiftClean.liftC
      (ZZOrbitLiftClean.ring6.rightNeighbor e))
    (orbit_pair_allNeutral e)

/-- For the orbit, the compiled no-garbage theorem upgrades the port result to
the actual final dispatcher. -/
theorem final_action_host (e : Fin 6) :
    ZZFinalCarrierV3.finalActionV3
      ZZOrbitLiftClean.h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) ZZOrbitLiftClean.h3 h23)
      (ZZOrbitLiftClean.liftC e)
      (ZZOrbitLiftClean.liftC
        (ZZOrbitLiftClean.ring6.rightNeighbor e)) = .host := by
  unfold ZZFinalCarrierV3.finalActionV3
  rw [if_neg (ZZOrbitLiftClean.cleanLift_noFinalGarbage e)]
  rw [port_action_host e]

#print axioms ZZNeutralPortAction.full_action_host_of_neutral
#print axioms ZZNeutralPortAction.port_action_host_of_neutral
#print axioms ZZNeutralPortAction.port_action_host
#print axioms ZZNeutralPortAction.final_action_host

end ZZNeutralPortAction

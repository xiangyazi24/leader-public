import Leader.Wu.Splice.FullCarrierRows
import Leader.Wu.Splice.HostQuiescence
import Leader.Wu.Splice.NeutralOrbitLift


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace ZZNeutralGuardsFalse


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g
  B9SpliceTableHost


variable {psi kappa tau : Nat} {P : Type}


/-- Outer-B9 controller neutrality on the complete physical carrier. -/
def NeutralP (u : CellP P) : Prop :=
  u.spliceRole = .none /\
  u.repairPending = false /\
  u.acquireTicket = false


/-- Both endpoints have neutral outer-B9 controller fields. -/
def AllNeutral (l r : CellP P) : Prop :=
  NeutralP l /\ NeutralP r


private theorem neutral_fields
    (l r : CellP P) (hN : AllNeutral l r) :
    l.spliceRole = .none /\ l.repairPending = false /\
    l.acquireTicket = false /\
    r.spliceRole = .none /\ r.repairPending = false /\
    r.acquireTicket = false := by
  unfold AllNeutral NeutralP at hN
  exact ⟨hN.1.1, hN.1.2.1, hN.1.2.2,
    hN.2.1, hN.2.2.1, hN.2.2.2⟩


/-! ## V8/V9/V10b guards -/


theorem rightStalePredecessorHoldGuardV8_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ RightStalePredecessorHoldGuardV8 (toOld laws l) (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨_, _, _, hrr, _, _⟩
  intro h
  have ht := h.2.2.2.1
  change r.spliceRole = .predecessorArmed at ht
  rw [hrr] at ht
  cases ht


theorem hostFenceBusyFrontGuardV9_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (hpsi : 0 < psi) (l r : CellP P) (hN : AllNeutral l r) :
    ¬ HostFenceBusyFrontGuardV9 hpsi (toOld laws l) (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨_, _, hlt, _, _, _⟩
  intro h
  have ht := h.1.2.2
  change l.acquireTicket = true at ht
  rw [hlt] at ht
  cases ht


/-- `HostFenceTargetClearV7` itself is compatible with a neutral right cell. -/
theorem hostFenceTargetClearV7_of_neutral_right
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    HostFenceTargetClearV7 (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨_, _, _, hrr, hrp, _⟩
  constructor
  · change r.spliceRole = .none
    exact hrr
  · change r.repairPending = false
    exact hrp


theorem hostFenceAdvanceGuardV10b_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (hpsi : 0 < psi) (l r : CellP P) (hN : AllNeutral l r) :
    ¬ HostFenceAdvanceGuardV10b hpsi (toOld laws l) (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨_, _, hlt, _, _, _⟩
  intro h
  have ht := h.1.2.2
  change l.acquireTicket = true at ht
  rw [hlt] at ht
  cases ht


/-! ## Four direct row10dg KEEP guards -/


theorem orphanReservedFrontGuardV3_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ OrphanReservedFrontGuardV3
      (toOld laws l).carrier (toOld laws r).carrier := by
  rcases neutral_fields l r hN with ⟨_, _, _, hrr, _, _⟩
  intro h
  have ht := h.1.1
  change r.spliceRole = .front at ht
  rw [hrr] at ht
  cases ht


theorem orphanVictimGuard_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ OrphanVictimGuard (toOld laws l) (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨_, _, _, hrr, _, _⟩
  intro h
  have ht := h.1
  change r.spliceRole = .victimArmed at ht
  rw [hrr] at ht
  cases ht


theorem ownedPendingVictimGuard_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ OwnedPendingVictimGuard (toOld laws l) (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨hlr, _, _, _, _, _⟩
  intro h
  have ht := h.1
  change l.spliceRole = .predecessorArmed at ht
  rw [hlr] at ht
  cases ht


theorem ownerlessPendingPredGuard_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ OwnerlessPendingPredGuard (toOld laws l) (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨_, _, _, hrr, _, _⟩
  intro h
  have ht := h.2.1
  change r.spliceRole = .predecessorArmed at ht
  rw [hrr] at ht
  cases ht


/-! ## Zero-refresh: neutral alone is intentionally insufficient -/


theorem zeroRefreshOnlyGuardP_implies_zero_stalls
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P)
    (h : ZeroRefreshOnlyGuardP laws host hpsi l r) :
    (laws.stall l.phys).val = 0 /\ (laws.stall r.phys).val = 0 := by
  exact ⟨h.2.1, h.2.2.1⟩


/-- Honest replacement for the false unconditional neutral claim. -/
theorem zeroRefreshOnlyGuardP_false_of_left_stall_ne_zero
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (_hN : AllNeutral l r)
    (hstall : (laws.stall l.phys).val ≠ 0) :
    ¬ ZeroRefreshOnlyGuardP laws host hpsi l r := by
  intro h
  exact hstall h.2.1


/-! ## row10g hold/scrub guards -/


theorem row10g_left_pending_predecessor_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ (role (toOld laws l).carrier = .predecessorArmed /\
      (toOld laws l).carrier.repairPending = true) := by
  rcases neutral_fields l r hN with ⟨hlr, _, _, _, _, _⟩
  rintro ⟨h, _⟩
  change l.spliceRole = .predecessorArmed at h
  rw [hlr] at h
  cases h


theorem victimRightScrubGuardV6_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ VictimRightScrubGuardV6 (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨_, _, _, hrr, _, _⟩
  intro h
  have ht := h.1
  change r.spliceRole = .victimArmed at ht
  rw [hrr] at ht
  cases ht


theorem frontRightScrubGuardV6_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ FrontRightScrubGuardV6 (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨_, _, _, hrr, _, _⟩
  intro h
  have ht := h.1
  change r.spliceRole = .front at ht
  rw [hrr] at ht
  cases ht


theorem malformedRightPendingGuardV6_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ MalformedRightPendingGuardV6 (toOld laws r) := by
  rcases neutral_fields l r hN with ⟨_, _, _, _, hrp, _⟩
  intro h
  have ht := h.1
  change r.repairPending = true at ht
  rw [hrp] at ht
  cases ht


theorem row10g_right_predecessor_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ role (toOld laws r).carrier = .predecessorArmed := by
  rcases neutral_fields l r hN with ⟨_, _, _, hrr, _, _⟩
  intro h
  change r.spliceRole = .predecessorArmed at h
  rw [hrr] at h
  cases h


theorem reservedFrontHoldGuard_left_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ ReservedFrontHoldGuard (toOld laws l).carrier := by
  rcases neutral_fields l r hN with ⟨hlr, _, _, _, _, _⟩
  intro h
  have ht := h.1
  change l.spliceRole = .front at ht
  rw [hlr] at ht
  cases ht


theorem leftScrubGuardV10e_false
    (laws : PhysCarrierLaws P psi kappa tau)
    (l r : CellP P) (hN : AllNeutral l r) :
    ¬ LeftScrubGuardV10e (toOld laws l) := by
  rcases neutral_fields l r hN with ⟨hlr, hlp, _, _, _, _⟩
  rintro (hV | hF | hM)
  · have ht := hV.1
    change l.spliceRole = .victimArmed at ht
    rw [hlr] at ht
    cases ht
  · have ht := hF.1
    change l.spliceRole = .front at ht
    rw [hlr] at ht
    cases ht
  · have ht := hM.1
    change l.repairPending = true at ht
    rw [hlp] at ht
    cases ht


/-! ## Row-7 neutral classification below the V8/V9/V10 stack -/


private theorem row7Action_host_of_allNeutral_of_not_ldc
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r)
    (hNo : ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier) :
    row7ActionP laws host hpsi l r = .host := by
  classical
  rcases neutral_fields l r hN with
    ⟨hlr, hlp, hlt, hrr, hrp, hrt⟩
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  have hlr' : role lo.carrier = .none := by
    change l.spliceRole = .none; exact hlr
  have hlp' : lo.carrier.repairPending = false := by
    change l.repairPending = false; exact hlp
  have hlt' : lo.acquireTicket = false := by
    change l.acquireTicket = false; exact hlt
  have hrr' : role ro.carrier = .none := by
    change r.spliceRole = .none; exact hrr
  have hrp' : ro.carrier.repairPending = false := by
    change r.repairPending = false; exact hrp
  have hrt' : ro.acquireTicket = false := by
    change r.acquireTicket = false; exact hrt
  have hNo' : ¬ B9SpliceTableHost.ldc oh lo.carrier ro.carrier := by
    exact hNo
  have hfL : ¬ HostFenceShapeV7 lo := fun h => by
    have ht := h.2.2; rw [hlt'] at ht; cases ht
  have hfR : ¬ HostFenceShapeV7 ro := fun h => by
    have ht := h.2.2; rw [hrt'] at ht; cases ht
  have hRF : ¬ ReservedFrontHoldGuard ro.carrier := fun h => by
    have ht := h.1; rw [hrr'] at ht; cases ht
  have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi lo ro :=
    fun h => hRF h.2.2.2.1
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
  have hPP : ¬ (role lo.carrier = .predecessorArmed /\
      lo.carrier.repairPending = true) := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hMAL : ¬ MoveAcquireLegacyGuardV6 lo ro :=
    fun h => hRF h.1.2.2.2
  have hMAA : ¬ MoveAcquireAbortGuardV3 lo.carrier ro.carrier := fun h => by
    have ht := h.1; rw [hlr'] at ht; cases ht
  have hORF : ¬ OrphanReservedFrontGuardV3 lo.carrier ro.carrier :=
    fun h => hRF h.1
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
  rw [B9FullCarrierHost.row7ActionP.eq_1 laws host hpsi l r]
  try dsimp only
  rw [if_neg hfL, if_neg hfR, if_neg hmaf, if_neg hA, if_neg hB,
    if_neg hDel, if_neg hPH, if_neg hPA, if_neg hMC, if_neg hMS,
    if_neg hSK, if_neg hSKH, if_neg hPOA, if_neg hPP, if_neg hMAL,
    if_neg hMAA, if_neg hORF, if_neg hRFH, if_neg hVR, if_neg hVL,
    if_neg hFR, if_neg hML, if_neg hMR, if_neg hpl, if_neg hlf,
    if_neg hmk]


/-! ## Generic assembly -/


private theorem fullActionP_host_of_allNeutral_of_not_ldc
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r)
    (hNo : ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host l.phys r.phys)
      (toOld laws l).carrier (toOld laws r).carrier) :
    fullActionP laws host hpsi l r = .host := by
  classical
  rcases neutral_fields l r hN with
    ⟨hlr, hlp, hlt, hrr, hrp, hrt⟩
  let lo := toOld laws l
  let ro := toOld laws r
  have hlr' : role lo.carrier = .none := by
    change l.spliceRole = .none; exact hlr
  have hlt' : lo.acquireTicket = false := by
    change l.acquireTicket = false; exact hlt
  have hrr' : role ro.carrier = .none := by
    change r.spliceRole = .none; exact hrr
  have hNo' : ¬ B9SpliceTableHost.ldc
      (shadowHostAt laws host l.phys r.phys) lo.carrier ro.carrier := by
    exact hNo
  have h7 : row7ActionP laws host hpsi l r = .host :=
    row7Action_host_of_allNeutral_of_not_ldc laws host hpsi l r hN hNo
  have hD1 := orphanReservedFrontGuardV3_false laws l r hN
  have hD2 := orphanVictimGuard_false laws l r hN
  have hD3 := ownedPendingVictimGuard_false laws l r hN
  have hD4 := ownerlessPendingPredGuard_false laws l r hN
  have hSP8 := rightStalePredecessorHoldGuardV8_false laws l r hN
  have hBF := hostFenceBusyFrontGuardV9_false laws hpsi l r hN
  have hHO := hostFenceAdvanceGuardV10b_false laws hpsi l r hN
  have hLP := row10g_left_pending_predecessor_false laws l r hN
  have hVR := victimRightScrubGuardV6_false laws l r hN
  have hFR := frontRightScrubGuardV6_false laws l r hN
  have hMR := malformedRightPendingGuardV6_false laws l r hN
  have hRP := row10g_right_predecessor_false laws l r hN
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
    rw [if_neg hLP, if_neg hVR, if_neg hFR, if_neg hMR, if_neg hRP]
  · rw [if_neg hq]
    simp only [planFromRow]
    have h8 : row8ActionP laws host hpsi l r = .host := by
      unfold row8ActionP
      rw [B9FullCarrierRows.row8PlanP.eq_1]
      try dsimp only
      rw [if_neg hSP8]
      simpa only [planFromRow] using h7
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


/-- Strongest generic dispatch result: outer neutrality alone forces HOST. -/
theorem fullActionP_host_of_allNeutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r) :
    fullActionP laws host hpsi l r = .host := by
  classical
  let lo := toOld laws l
  let ro := toOld laws r
  let oh := shadowHostAt laws host l.phys r.phys
  have hRF : ¬ ReservedFrontHoldGuard lo.carrier := by
    simpa only [lo] using reservedFrontHoldGuard_left_false laws l r hN
  by_cases hdel : B9SpliceTableHost.ldc oh lo.carrier ro.carrier
  · unfold fullActionP
    rw [B9FullCarrierRows.fullPlanP.eq_1]
    try dsimp only
    rw [if_pos hdel, if_neg hRF]
  · exact fullActionP_host_of_allNeutral_of_not_ldc
      laws host hpsi l r hN hdel


/-- Packaging corollary for the actual full-row port. -/
theorem fullRowPort_action_host_of_allNeutral
    (laws : PhysCarrierLaws P psi kappa tau)
    (host : HostRow P) (hpsi : 0 < psi)
    (l r : CellP P) (hN : AllNeutral l r) :
    (fullRowPort laws host hpsi).action l r = .host := by
  exact fullActionP_host_of_allNeutral laws host hpsi l r hN


/-! ## The six adjacent pairs of the compiled orbit's neutral lift -/


private theorem h3 : 0 < 3 := ZZOrbitLiftClean.h3
private theorem h23 : 2 ≤ 3 := by omega


private def orbitLaws :
    PhysCarrierLaws (ZZFinalCarrierV3.P 3 3 48) 3 3 48 :=
  ZZFinalCarrierV3.carrierLawsV3


private def orbitHost : HostRow (ZZFinalCarrierV3.P 3 3 48) :=
  ZZFinalCarrierV3.hostR2CV3 h3 h23


private theorem liftC_neutral (i : Fin 6) :
    NeutralP (ZZOrbitLiftClean.liftC i) := by
  exact ⟨rfl, rfl, rfl⟩


theorem liftC_allNeutral (i : Fin 6) :
    AllNeutral
      (ZZOrbitLiftClean.liftC i)
      (ZZOrbitLiftClean.liftC (ZZOrbitLiftClean.ring6.rightNeighbor i)) := by
  exact ⟨liftC_neutral i,
    liftC_neutral (ZZOrbitLiftClean.ring6.rightNeighbor i)⟩


/-- The orbit also satisfies the stronger zero-refresh-false side condition:
its physical stall is the literal fresh value 48. -/
theorem liftC_zeroRefreshOnlyGuardP_false (i : Fin 6) :
    ¬ ZeroRefreshOnlyGuardP orbitLaws orbitHost h3
      (ZZOrbitLiftClean.liftC i)
      (ZZOrbitLiftClean.liftC (ZZOrbitLiftClean.ring6.rightNeighbor i)) := by
  apply zeroRefreshOnlyGuardP_false_of_left_stall_ne_zero
    orbitLaws orbitHost h3
    (ZZOrbitLiftClean.liftC i)
    (ZZOrbitLiftClean.liftC (ZZOrbitLiftClean.ring6.rightNeighbor i))
    (liftC_allNeutral i)
  change (48 : Nat) ≠ 0
  omega


theorem liftC_fullAction_host (i : Fin 6) :
    fullActionP orbitLaws orbitHost h3
      (ZZOrbitLiftClean.liftC i)
      (ZZOrbitLiftClean.liftC (ZZOrbitLiftClean.ring6.rightNeighbor i)) = .host := by
  exact fullActionP_host_of_allNeutral
    orbitLaws orbitHost h3 _ _ (liftC_allNeutral i)


theorem liftC_port_action_host (i : Fin 6) :
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action
      (ZZOrbitLiftClean.liftC i)
      (ZZOrbitLiftClean.liftC (ZZOrbitLiftClean.ring6.rightNeighbor i)) = .host := by
  change fullActionP orbitLaws orbitHost h3
      (ZZOrbitLiftClean.liftC i)
      (ZZOrbitLiftClean.liftC (ZZOrbitLiftClean.ring6.rightNeighbor i)) = .host
  exact liftC_fullAction_host i


/-- With the no-garbage theorem, the final wrapper also selects HOST. -/
theorem liftC_finalAction_host (i : Fin 6) :
    ZZFinalCarrierV3.finalActionV3 h3 h23
      (ZZFinalCarrierV3.concretePortV3
        (κ := 3) (τ := 48) h3 h23)
      (ZZOrbitLiftClean.liftC i)
      (ZZOrbitLiftClean.liftC (ZZOrbitLiftClean.ring6.rightNeighbor i)) = .host := by
  have hg := ZZOrbitLiftClean.cleanLift_noFinalGarbage i
  have ha := liftC_port_action_host i
  simp [ZZFinalCarrierV3.finalActionV3, hg, ha]


/-- Explicit six-edge form, including the wrap edge 5 -> 0. -/
theorem liftC_six_port_actions_host :
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action
        (ZZOrbitLiftClean.liftC 0) (ZZOrbitLiftClean.liftC 1) = .host /\
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action
        (ZZOrbitLiftClean.liftC 1) (ZZOrbitLiftClean.liftC 2) = .host /\
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action
        (ZZOrbitLiftClean.liftC 2) (ZZOrbitLiftClean.liftC 3) = .host /\
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action
        (ZZOrbitLiftClean.liftC 3) (ZZOrbitLiftClean.liftC 4) = .host /\
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action
        (ZZOrbitLiftClean.liftC 4) (ZZOrbitLiftClean.liftC 5) = .host /\
    (ZZFinalCarrierV3.concretePortV3
      (κ := 3) (τ := 48) h3 h23).action
        (ZZOrbitLiftClean.liftC 5) (ZZOrbitLiftClean.liftC 0) = .host := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (liftC_port_action_host (0 : Fin 6))
  · simpa using (liftC_port_action_host (1 : Fin 6))
  · simpa using (liftC_port_action_host (2 : Fin 6))
  · simpa using (liftC_port_action_host (3 : Fin 6))
  · simpa using (liftC_port_action_host (4 : Fin 6))
  · simpa using (liftC_port_action_host (5 : Fin 6))


#print axioms ZZNeutralGuardsFalse.fullActionP_host_of_allNeutral
#print axioms ZZNeutralGuardsFalse.liftC_port_action_host
#print axioms ZZNeutralGuardsFalse.liftC_finalAction_host


end ZZNeutralGuardsFalse

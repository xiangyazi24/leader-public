import Leader.Wu.Splice.TransactionLifetime


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceControllerR1TableV9


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8


variable {n psi width kappa tau : Nat}


/-- The V8 HOLD case that is safe to service immediately: the busy target is
itself the old reserved-front safety certificate. -/
def HostFenceBusyFrontGuardV9
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  HostFenceShapeV7 l /\
  LocalPreparedBarrier hpsi l.carrier r.carrier /\
  ReservedFrontHoldGuard r.carrier


private instance instDecidableHostFenceBusyFrontGuardV9
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceBusyFrontGuardV9 hpsi l r) := by
  unfold HostFenceBusyFrontGuardV9 HostFenceShapeV7
    ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance


/-- Repair only the physical barrier.  The left fence and the reserved-front
controller/ticket are retained literally. -/
def hostFenceBusyFrontRepairWriteV9
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  (l, { r with carrier := repairResponder hpsi l.carrier r.carrier })


/-- V9 is V8 plus one row above the old HOLD. -/
def rowV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if HostFenceBusyFrontGuardV9 hpsi l r then
    hostFenceBusyFrontRepairWriteV9 hpsi l r
  else rowV8 hpsi hwidth hle l r


def stepV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) : R1ConfigV6 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV9 hpsi hwidth hle (C e) (C j)
    fun i => if i = e then q.1 else if i = j then q.2 else C i


private theorem rightNeighbor_injectiveV9
    (ring : DirectedRing n) : Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv; omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv; omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv; omega
    · have hbeq : b.val + 1 = n := by omega
      omega


private theorem normalizeDeletion_labelV9 (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareDisposal_labelV9
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.label = u.core.label := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl


private theorem preparedR1_labelV9
    (hpsi : 0 < psi) (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.label = u.splice.base.core.core.label := by
  unfold preparedR1 prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.splice.base.core]
  rw [normalizeDeletion_labelV9, prepareDisposal_labelV9]
  rfl


private theorem repairResponder_no_localPreparedBarrierV9
    (hpsi : 0 < psi) (l r : R1AgentStateV4 psi kappa tau) :
    ¬ LocalPreparedBarrier hpsi l (repairResponder hpsi l r) := by
  intro h
  unfold LocalPreparedBarrier at h
  dsimp only at h
  unfold isBarrier at h
  apply h.2
  apply Fin.ext
  simp [preparedR1_labelV9, repairResponder]


private theorem localPreparedBarrier_of_dangerV9
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (h : PreparedDangerAt hpsi ring (projectV6 C) e) :
    LocalPreparedBarrier hpsi
      (C e).carrier (C (ring.rightNeighbor e)).carrier := by
  simpa [PreparedBarrierAt, LocalPreparedBarrier,
    projectSpliceConfig, projectV6, preparedR1] using h.2


/-- The new row preserves the existing V7 safety predicate. -/
theorem hostFenceBusyFrontRepair_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hg : HostFenceBusyFrontGuardV9 hpsi
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (stepV9 hpsi hwidth hle ring C e) := by
  by_cases hself : ring.rightNeighbor e = e
  · simpa [stepV9, hself] using hsafe
  · let j := ring.rightNeighbor e
    let D := stepV9 hpsi hwidth hle ring C e
    change SpliceSafeV7 hpsi ring D
    have hrow :
        rowV9 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
          (C e,
            { C (ring.rightNeighbor e) with
              carrier := repairResponder hpsi
                (C e).carrier (C (ring.rightNeighbor e)).carrier }) := by
      simp [rowV9, hg, hostFenceBusyFrontRepairWriteV9]
    have hE : D e = C e := by
      simp [D, stepV9, hself, hrow]
    have hJ : D j =
        { C j with
          carrier := repairResponder hpsi (C e).carrier (C j).carrier } := by
      simp [D, stepV9, j, hself, hrow]
    have hOffJ : ∀ i, i ≠ j -> D i = C i := by
      intro i hij
      by_cases hie : i = e
      · subst i
        exact hE
      · have hir : i ≠ ring.rightNeighbor e := by
          simpa only [j] using hij
        simp [D, stepV9, hself, hrow, hie, hir]
    rcases hg with ⟨hf, hbar, hfront⟩
    have hfrontJ : ReservedFrontHoldGuard (C j).carrier := by
      simpa only [j] using hfront
    have hrole : ∀ i, role (D i).carrier = role (C i).carrier := by
      intro i
      by_cases hij : i = j
      · subst i
        rw [hJ]
        simp [repairResponder, role, setPhysical, setRole, setControl,
          clearControl, setTicketV6, clearTicketV6,
          withCarrierClearTicketV6]
      · rw [hOffJ i hij]
    have hpending : ∀ i,
        (D i).carrier.repairPending = (C i).carrier.repairPending := by
      intro i
      by_cases hij : i = j
      · subst i
        rw [hJ]
        simp [repairResponder, setPhysical, setRole, setControl,
          clearControl, setTicketV6, clearTicketV6,
          withCarrierClearTicketV6]
      · rw [hOffJ i hij]
    have hticket : ∀ i, (D i).acquireTicket = (C i).acquireTicket := by
      intro i
      by_cases hij : i = j
      · subst i
        rw [hJ]
      · rw [hOffJ i hij]
    have hfrontD : ReservedFrontHoldGuard (D j).carrier := by
      unfold ReservedFrontHoldGuard at hfrontJ ⊢
      exact ⟨(hrole j).trans hfrontJ.1,
        (hpending j).trans hfrontJ.2⟩
    have hprot : ∀ x,
        R1ProtectedSpliceEdgeV3 ring (projectV6 D) x <->
          R1ProtectedSpliceEdgeV3 ring (projectV6 C) x := by
      intro x
      unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard projectV6
      dsimp only
      simp only [hrole x, hpending x,
        hrole (ring.rightNeighbor x), hpending (ring.rightNeighbor x)]
    have hDangerE :
        PreparedDangerAt hpsi ring (projectV6 D) e ->
          ProtectedSpliceEdgeV7 ring D e := by
      intro hd
      have hb := localPreparedBarrier_of_dangerV9
        (kappa := kappa) (tau := tau) hpsi ring D e hd
      change LocalPreparedBarrier hpsi (D e).carrier (D j).carrier at hb
      rw [hE, hJ] at hb
      change LocalPreparedBarrier hpsi (C e).carrier
        (repairResponder hpsi (C e).carrier (C j).carrier) at hb
      exact (repairResponder_no_localPreparedBarrierV9
        (kappa := kappa) (tau := tau)
        hpsi (C e).carrier (C j).carrier hb).elim
    have hDangerJ :
        PreparedDangerAt hpsi ring (projectV6 D) j ->
          ProtectedSpliceEdgeV7 ring D j := by
      intro _
      apply Or.inl
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      exact Or.inl hfrontD
    have hDangerIncoming :
        ∀ x, x ≠ e -> x ≠ j -> ring.rightNeighbor x = e ->
          PreparedDangerAt hpsi ring (projectV6 D) x ->
            ProtectedSpliceEdgeV7 ring D x := by
      intro x hxe hxj hin hd
      have hDx := hOffJ x hxj
      have hDr : D (ring.rightNeighbor x) = C (ring.rightNeighbor x) := by
        rw [hin]
        exact hE
      have hd0 : PreparedDangerAt hpsi ring (projectV6 C) x := by
        unfold PreparedDangerAt PreparedBarrierAt
          projectSpliceConfig projectV6 at hd ⊢
        dsimp only at hd ⊢
        rw [hDx, hDr] at hd
        exact hd
      rcases hsafe.1 x hd0 with hv3 | hfx
      · exact Or.inl ((hprot x).2 hv3)
      · apply Or.inr
        rw [hDx]
        exact hfx
    have hDangerDisjoint :
        ∀ x, x ≠ e -> x ≠ j -> ring.rightNeighbor x ≠ e ->
          PreparedDangerAt hpsi ring (projectV6 D) x ->
            ProtectedSpliceEdgeV7 ring D x := by
      intro x hxe hxj _ hd
      have hrxj : ring.rightNeighbor x ≠ j := by
        intro h
        apply hxe
        apply rightNeighbor_injectiveV9 ring
        simpa only [j] using h
      have hDx := hOffJ x hxj
      have hDr := hOffJ (ring.rightNeighbor x) hrxj
      have hd0 : PreparedDangerAt hpsi ring (projectV6 C) x := by
        unfold PreparedDangerAt PreparedBarrierAt
          projectSpliceConfig projectV6 at hd ⊢
        dsimp only at hd ⊢
        rw [hDx, hDr] at hd
        exact hd
      rcases hsafe.1 x hd0 with hv3 | hfx
      · exact Or.inl ((hprot x).2 hv3)
      · apply Or.inr
        rw [hDx]
        exact hfx
    constructor
    · intro x hd
      by_cases hxe : x = e
      · subst x
        exact hDangerE hd
      · by_cases hxj : x = j
        · subst x
          exact hDangerJ hd
        · by_cases hin : ring.rightNeighbor x = e
          · exact hDangerIncoming x hxe hxj hin hd
          · exact hDangerDisjoint x hxe hxj hin hd
    · rcases hsafe.2 with ⟨hticketSafe, hbackSafe⟩
      constructor
      · intro i
        unfold TicketShapeV7
        intro ht
        have htC : (C i).acquireTicket = true :=
          (hticket i).symm.trans ht
        rcases hticketSafe i htC with hres | hhost
        · left
          unfold ReservedFrontHoldGuard at hres ⊢
          exact ⟨(hrole i).trans hres.1,
            (hpending i).trans hres.2⟩
        · right
          unfold HostFenceShapeV7 at hhost ⊢
          exact ⟨(hrole i).trans hhost.1,
            (hpending i).trans hhost.2.1, ht⟩
      · intro i hr hp
        have hrC : role (C i).carrier = .predecessorArmed :=
          (hrole i).symm.trans hr
        have hpC : (C i).carrier.repairPending = true :=
          (hpending i).symm.trans hp
        have hb := hbackSafe i hrC hpC
        constructor
        · unfold ReservedFrontHoldGuard at hb ⊢
          exact ⟨(hrole (ring.rightNeighbor i)).trans hb.1.1,
            (hpending (ring.rightNeighbor i)).trans hb.1.2⟩
        · exact (hticket (ring.rightNeighbor i)).trans hb.2


private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩


/-- The literal fixed point now changes on edge zero. -/
theorem fenceLivelock2_progress_v9 :
    stepV9 hTwo hOne hOneTwo ring2 B9SpliceLifetime.fenceLivelock2
        (0 : Fin 2) (1 : Fin 2) !=
      B9SpliceLifetime.fenceLivelock2 (1 : Fin 2) := by
  decide


/-- One unit for an idle fence, one extra unit while it still faces a barrier. -/
def fenceDebtAtV9
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (i : Fin n) : Nat :=
  if HostFenceShapeV7 (C i) then
    if LocalPreparedBarrier hpsi
        (C i).carrier (C (ring.rightNeighbor i)).carrier then 2 else 1
  else 0


def fencePotentialV9
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Nat :=
  (List.ofFn (fun i : Fin n => fenceDebtAtV9 hpsi ring C i)).sum


/-- `2*n+1` makes any one-unit V6 drop dominate the entire fence term. -/
def compositeRankV9
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Nat :=
  (2 * n + 1) * controllerPotentialV6 C + fencePotentialV9 hpsi ring C


/-- Missing global strictness leaf. -/
def V9StrictRank
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  forall C : R1ConfigV6 n psi kappa tau, SpliceSafeV7 hpsi ring C ->
    forall e : Fin n,
      (exists i, stepV9 hpsi hwidth hle ring C e i != C i) ->
      compositeRankV9 hpsi ring (stepV9 hpsi hwidth hle ring C e) <
        compositeRankV9 hpsi ring C


/-- Missing global enabled-progress leaf. -/
def V9ProgressEnabled
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  forall C : R1ConfigV6 n psi kappa tau,
    SpliceSafeV7 hpsi ring C -> not (RolesClearV7 C) ->
      exists e i, stepV9 hpsi hwidth hle ring C e i != C i


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The q11703 fence ADVANCE now pays one fence unit although V6 is flat. -/
theorem q11703_first_advance_drops_composite_v9 :
    compositeRankV9 hTwo ring3 q11703Fence1V8 <
      compositeRankV9 hTwo ring3 q11703ArmedAfterV8 := by
  decide


/-- V9 adds no local coordinate. -/
def controllerStateFactorV9 : Nat := controllerStateFactorV8


theorem controllerStateFactorV9_eq : controllerStateFactorV9 = 16 := by
  simpa [controllerStateFactorV9] using controllerStateFactorV8_eq


end B9SpliceControllerR1TableV9


#print axioms B9SpliceControllerR1TableV9.hostFenceBusyFrontRepair_preserves_spliceSafeV7
#print axioms B9SpliceControllerR1TableV9.fenceLivelock2_progress_v9
#print axioms B9SpliceControllerR1TableV9.q11703_first_advance_drops_composite_v9
#print axioms B9SpliceControllerR1TableV9.controllerStateFactorV9_eq

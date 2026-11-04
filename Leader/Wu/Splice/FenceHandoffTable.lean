import Leader.Wu.Splice.BusyFrontTable

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceControllerR1TableV10b

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
open FiniteUniformStoppingTree

variable {n psi width kappa tau : Nat}

def HostFenceAdvanceGuardV10b
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  HostFenceShapeV7 l /\
  LocalPreparedBarrier hpsi l.carrier r.carrier /\
  HostFenceTargetClearV7 r

private instance instDecidableHostFenceAdvanceGuardV10b
    (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceAdvanceGuardV10b hpsi l r) := by
  unfold HostFenceAdvanceGuardV10b HostFenceShapeV7
    HostFenceTargetClearV7 LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

def hostFenceHandoffWriteV10b
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  (setControlV6 l .predecessorArmed false,
    setControlV6 r .front true)

def rowV10b
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if HostFenceAdvanceGuardV10b hpsi l r then
    hostFenceHandoffWriteV10b l r
  else rowV9 hpsi hwidth hle l r

def stepV10b
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) : R1ConfigV6 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV10b hpsi hwidth hle (C e) (C j)
    fun i => if i = e then q.1 else if i = j then q.2 else C i

def controllerStateFactorV10b : Nat := controllerStateFactorV9

theorem controllerStateFactorV10b_eq : controllerStateFactorV10b = 16 := by
  simpa [controllerStateFactorV10b] using controllerStateFactorV9_eq

private theorem normalizeDeletion_leader_local (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl

private theorem prepareDisposal_leader_local (hpsi : 0 < psi)
    (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.leader = u.core.leader := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

private theorem normalizeDeletion_label_local (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl

private theorem prepareDisposal_label_local (hpsi : 0 < psi)
    (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.label = u.core.label := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

private theorem preparedR1_leader_local (hpsi : 0 < psi)
    (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.leader = u.splice.base.core.core.leader := by
  unfold preparedR1 prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.splice.base.core]
  rw [normalizeDeletion_leader_local, prepareDisposal_leader_local]
  rfl

private theorem preparedR1_label_local (hpsi : 0 < psi)
    (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.label = u.splice.base.core.core.label := by
  unfold preparedR1 prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.splice.base.core]
  rw [normalizeDeletion_label_local, prepareDisposal_label_local]
  rfl

private theorem prepared_leader_local (hpsi : 0 < psi)
    (u : R1AgentStateV4 psi kappa tau) :
    (prepared hpsi u.splice).core.leader = u.splice.base.core.core.leader :=
  preparedR1_leader_local hpsi u

private theorem prepared_label_local (hpsi : 0 < psi)
    (u : R1AgentStateV4 psi kappa tau) :
    (prepared hpsi u.splice).core.label = u.splice.base.core.core.label :=
  preparedR1_label_local hpsi u

private theorem danger_iff_physical (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (x : Fin n) :
    PreparedDangerAt (kappa := kappa) (tau := tau)
        hpsi ring (projectV6 C) x <->
      (C x).carrier.splice.base.core.core.leader = false /\
      (C (ring.rightNeighbor x)).carrier.splice.base.core.core.leader = false /\
      (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label ≠
        ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6 projectSpliceConfig
  dsimp only
  unfold isBarrier
  simp only [preparedR1_label_local, preparedR1_leader_local,
    prepared_label_local, prepared_leader_local]

private theorem danger_congr_of_base
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1ConfigV6 n psi kappa tau)
    (hbase : forall i,
      (D i).carrier.splice.base = (C i).carrier.splice.base)
    (x : Fin n) :
    PreparedDangerAt (kappa := kappa) (tau := tau)
        hpsi ring (projectV6 D) x <->
      PreparedDangerAt (kappa := kappa) (tau := tau)
        hpsi ring (projectV6 C) x := by
  rw [danger_iff_physical hpsi ring D x,
    danger_iff_physical hpsi ring C x]
  rw [hbase x, hbase (ring.rightNeighbor x)]

theorem corrected_handoff_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7 (kappa := kappa) (tau := tau) hpsi ring C)
    (hg : HostFenceAdvanceGuardV10b (kappa := kappa) (tau := tau)
      hpsi (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 (kappa := kappa) (tau := tau) hpsi ring
      (stepV10b hpsi hwidth hle ring C e) := by
  let j := ring.rightNeighbor e
  by_cases hself : j = e
  · simpa [stepV10b, j, hself] using hsafe
  let D := stepV10b hpsi hwidth hle ring C e
  have hgJ : HostFenceAdvanceGuardV10b hpsi (C e) (C j) := by
    simpa only [j] using hg
  have hE : D e = setControlV6 (C e) .predecessorArmed false := by
    simp [D, stepV10b, j, hself, rowV10b, hgJ,
      hostFenceHandoffWriteV10b]
  have hJ : D j = setControlV6 (C j) .front true := by
    simp [D, stepV10b, j, hself, rowV10b, hgJ,
      hostFenceHandoffWriteV10b]
  have hOther : forall i, i ≠ e -> i ≠ j -> D i = C i := by
    intro i hie hij
    simp [D, stepV10b, j, hself, rowV10b, hgJ, hie, hij]
  have hbase : forall i,
      (D i).carrier.splice.base = (C i).carrier.splice.base := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [show D e = setControlV6 (C e) .predecessorArmed false from hE]
      rfl
    · by_cases hij : i = j
      · subst i
        rw [show D j = setControlV6 (C j) .front true from hJ]
        rfl
      · have hDi := hOther i hie hij
        rw [show D i = C i from hDi]
  have hdanger := danger_congr_of_base
    (kappa := kappa) (tau := tau) hpsi ring C D hbase
  constructor
  · intro x hd
    have hold := hsafe.1 x ((hdanger x).1 hd)
    by_cases hxe : x = e
    · subst x
      left
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      right
      right
      rw [show stepV10b hpsi hwidth hle ring C e e = setControlV6 (C e) .predecessorArmed false from hE]
      rw [show stepV10b hpsi hwidth hle ring C e (ring.rightNeighbor e) =
          setControlV6 (C j) .front true by simpa only [j] using hJ]
      simp [ReservedFrontHoldGuard, setControlV6,
        withCarrierClearTicketV6, setControl, setPhysical, role]
    · by_cases hxj : x = j
      · subst x
        left
        unfold R1ProtectedSpliceEdgeV3 projectV6
        dsimp only
        left
        rw [show stepV10b hpsi hwidth hle ring C e j = setControlV6 (C j) .front true from hJ]
        simp [ReservedFrontHoldGuard, setControlV6,
          withCarrierClearTicketV6, setControl, setPhysical, role]
      · by_cases hre : ring.rightNeighbor x = e
        · rcases hold with hv3 | hf
          · have hxres : ReservedFrontHoldGuard (C x).carrier := by
              unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
              dsimp only at hv3
              rw [hre] at hv3
              simpa [ReservedFrontHoldGuard,
                hgJ.1.1, hgJ.1.2.1] using hv3
            left
            unfold R1ProtectedSpliceEdgeV3 projectV6
            dsimp only
            left
            have hDx := hOther x hxe hxj
            rw [show stepV10b hpsi hwidth hle ring C e x = C x from hDx]
            exact hxres
          · right
            have hDx := hOther x hxe hxj
            rw [show stepV10b hpsi hwidth hle ring C e x = C x from hDx]
            exact hf
        · by_cases hrj : ring.rightNeighbor x = j
          · rcases hold with hv3 | hf
            · have hxres : ReservedFrontHoldGuard (C x).carrier := by
                unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
                dsimp only at hv3
                rw [hrj] at hv3
                simpa [ReservedFrontHoldGuard,
                  hgJ.2.2.1, hgJ.2.2.2] using hv3
              left
              unfold R1ProtectedSpliceEdgeV3 projectV6
              dsimp only
              left
              have hDx := hOther x hxe hxj
              rw [show stepV10b hpsi hwidth hle ring C e x = C x from hDx]
              exact hxres
            · right
              have hDx := hOther x hxe hxj
              rw [show stepV10b hpsi hwidth hle ring C e x = C x from hDx]
              exact hf
          · rcases hold with hv3 | hf
            · left
              unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3 ⊢
              dsimp only at hv3 ⊢
              have hDx := hOther x hxe hxj
              have hDr := hOther (ring.rightNeighbor x) hre hrj
              rw [show stepV10b hpsi hwidth hle ring C e x = C x from hDx,
                show stepV10b hpsi hwidth hle ring C e (ring.rightNeighbor x) =
                  C (ring.rightNeighbor x) from hDr]
              exact hv3
            · right
              have hDx := hOther x hxe hxj
              rw [show stepV10b hpsi hwidth hle ring C e x = C x from hDx]
              exact hf
  · constructor
    · intro i
      by_cases hie : i = e
      · subst i
        rw [show stepV10b hpsi hwidth hle ring C e e = setControlV6 (C e) .predecessorArmed false from hE]
        simp [TicketShapeV7, setControlV6,
          withCarrierClearTicketV6, setControl, setPhysical]
      · by_cases hij : i = j
        · subst i
          rw [show stepV10b hpsi hwidth hle ring C e j = setControlV6 (C j) .front true from hJ]
          simp [TicketShapeV7, setControlV6,
            withCarrierClearTicketV6, setControl, setPhysical]
        · have hDi := hOther i hie hij
          rw [show stepV10b hpsi hwidth hle ring C e i = C i from hDi]
          exact hsafe.2.1 i
    · intro i hr hp
      by_cases hie : i = e
      · subst i
        have hfalse : False := by
          have hp' := hp
          rw [show stepV10b hpsi hwidth hle ring C e e = setControlV6 (C e) .predecessorArmed false from hE]
            at hp'
          simpa [setControlV6, withCarrierClearTicketV6,
            setControl, setPhysical] using hp'
        exact hfalse.elim
      · by_cases hij : i = j
        · subst i
          have hfalse : False := by
            have hr' := hr
            rw [show stepV10b hpsi hwidth hle ring C e j = setControlV6 (C j) .front true from hJ] at hr'
            simpa [setControlV6, withCarrierClearTicketV6,
              setControl, setPhysical, role] using hr'
          exact hfalse.elim
        · have hDi := hOther i hie hij
          have hr0 : role (C i).carrier = .predecessorArmed := by
            rw [<- show stepV10b hpsi hwidth hle ring C e i = C i from hDi]
            exact hr
          have hp0 : (C i).carrier.repairPending = true := by
            rw [<- show stepV10b hpsi hwidth hle ring C e i = C i from hDi]
            exact hp
          have hb := hsafe.2.2 i hr0 hp0
          by_cases hre : ring.rightNeighbor i = e
          · have ht := hb.2
            rw [hre] at ht
            have hbad : (true : Bool) = false :=
              hgJ.1.2.2.symm.trans ht
            have hfalse : False := by simpa using hbad
            exact hfalse.elim
          · by_cases hrj : ring.rightNeighbor i = j
            · constructor
              · rw [hrj]
                rw [show stepV10b hpsi hwidth hle ring C e j = setControlV6 (C j) .front true from hJ]
                simp [ReservedFrontHoldGuard, setControlV6,
                  withCarrierClearTicketV6, setControl, setPhysical, role]
              · rw [hrj]
                rw [show stepV10b hpsi hwidth hle ring C e j = setControlV6 (C j) .front true from hJ]
                simp [setControlV6, withCarrierClearTicketV6,
                  setControl, setPhysical]
            · have hDr := hOther (ring.rightNeighbor i) hre hrj
              rw [show stepV10b hpsi hwidth hle ring C e (ring.rightNeighbor i) =
                C (ring.rightNeighbor i) from hDr]
              exact hb

private theorem handoff_rowV6_moveSeek
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hbar : LocalPreparedBarrier hpsi l.carrier r.carrier) :
    let q := hostFenceHandoffWriteV10b l r
    rowV6 hpsi hwidth hle q.1 q.2 = moveSeekWriteV6 q.1 q.2 := by
  dsimp only [hostFenceHandoffWriteV10b]
  let L := setControlV6 l .predecessorArmed false
  let R := setControlV6 r .front true
  change rowV6 hpsi hwidth hle L R = moveSeekWriteV6 L R
  have hb : LocalPreparedBarrier hpsi L.carrier R.carrier := by
    unfold LocalPreparedBarrier at hbar ⊢
    dsimp only at hbar ⊢
    unfold isBarrier at hbar ⊢
    simpa [L, R, setControlV6, withCarrierClearTicketV6,
      setControl, setPhysical, preparedR1_label_local,
      preparedR1_leader_local, prepared_label_local,
      prepared_leader_local] using hbar
  have hAcquire : ¬ MoveAcquireFrontGuardV6 hpsi L R := by
    simp [MoveAcquireFrontGuardV6, ReservedFrontHoldGuard, L, R,
      setControlV6, withCarrierClearTicketV6, setControl, setPhysical, role]
  have hA : ¬ ArmAGuard hpsi hwidth hle L.carrier R.carrier := by
    simp [ArmAGuard, L, R, setControlV6, withCarrierClearTicketV6,
      setControl, setPhysical, role]
  have hB : ¬ ArmBGuard L.carrier R.carrier := by
    simp [ArmBGuard, L, R, setControlV6, withCarrierClearTicketV6,
      setControl, setPhysical, role]
  have hD : ¬ DeleteGuard hpsi hwidth hle L.carrier R.carrier := by
    simp [DeleteGuard, L, R, setControlV6, withCarrierClearTicketV6,
      setControl, setPhysical, role]
  have hPH : ¬ PendingHoldGuard hpsi hwidth hle L.carrier R.carrier := by
    simp [PendingHoldGuard, L, R, setControlV6, withCarrierClearTicketV6,
      setControl, setPhysical, role]
  have hPA : ¬ PendingAbortGuard hpsi hwidth hle L.carrier R.carrier := by
    simp [PendingAbortGuard, L, R, setControlV6, withCarrierClearTicketV6,
      setControl, setPhysical, role]
  have hMC : ¬ MoveCommitGuard L.carrier R.carrier := by
    simp [MoveCommitGuard, L, R, setControlV6, withCarrierClearTicketV6,
      setControl, setPhysical, role]
  have hMS : ¬ MoveStopGuardV3 hpsi L.carrier R.carrier := by
    intro hs
    exact hs.2.2.2 hb
  have hSeek : MoveSeekGuardV3 hpsi L.carrier R.carrier := by
    refine ⟨?_, ?_, ?_, hb⟩
    · simp [L, setControlV6, withCarrierClearTicketV6, setControl, role]
    · simp [L, setControlV6, withCarrierClearTicketV6, setControl]
    · simp [ReservedFrontHoldGuard, R, setControlV6,
        withCarrierClearTicketV6, setControl, role]
  unfold rowV6
  rw [if_neg hAcquire, if_neg hA, if_neg hB, if_neg hD,
    if_neg hPH, if_neg hPA, if_neg hMC, if_neg hMS, if_pos hSeek]

private theorem ofFn_sum_lt_of_single_lt
    {m : Nat} (f g : Fin m -> Nat) (chosen : Fin m)
    (hle : forall i, f i <= g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction m with
  | zero => exact Fin.elim0 chosen
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hz : chosen = 0
      · subst chosen
        have ht := ofFn_sum_le (fun i : Fin m => f i.succ)
          (fun i => g i.succ) (fun i => hle i.succ)
        exact Nat.add_lt_add_of_lt_of_le hlt ht
      · have hz' : chosen.val ≠ 0 := fun h => hz (Fin.ext h)
        let p : Fin m := ⟨chosen.val - 1, by have := chosen.isLt; omega⟩
        have hs : p.succ = chosen := Fin.ext (by simp [p]; omega)
        have ht := ih (fun i : Fin m => f i.succ)
          (fun i => g i.succ) p (fun i => hle i.succ)
          (by simpa only [hs] using hlt)
        have hh := hle 0
        omega

theorem handoff_next_v6_service_drops
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hg : HostFenceAdvanceGuardV10b (kappa := kappa) (tau := tau)
      hpsi (C e) (C (ring.rightNeighbor e))) :
    let H := stepV10b hpsi hwidth hle ring C e
    controllerPotentialV6
        (stepV6 hpsi hwidth hle ring H e) < controllerPotentialV6 H := by
  let j := ring.rightNeighbor e
  let H := stepV10b hpsi hwidth hle ring C e
  change controllerPotentialV6 (stepV6 hpsi hwidth hle ring H e) <
    controllerPotentialV6 H
  have hne' : j ≠ e := by simpa only [j] using hne
  have hgJ : HostFenceAdvanceGuardV10b hpsi (C e) (C j) := by
    simpa only [j] using hg
  have hE : H e = setControlV6 (C e) .predecessorArmed false := by
    simp [H, stepV10b, j, hne', rowV10b, hgJ,
      hostFenceHandoffWriteV10b]
  have hJ : H j = setControlV6 (C j) .front true := by
    simp [H, stepV10b, j, hne', rowV10b, hgJ,
      hostFenceHandoffWriteV10b]
  have hrow : rowV6 hpsi hwidth hle (H e) (H j) =
      moveSeekWriteV6 (H e) (H j) := by
    rw [show H e = setControlV6 (C e) .predecessorArmed false from hE,
      show H j = setControlV6 (C j) .front true from hJ]
    exact handoff_rowV6_moveSeek hpsi hwidth hle (C e) (C j) hgJ.2.1
  let S := stepV6 hpsi hwidth hle ring H e
  have hSe : S e = H e := by
    simp [S, stepV6, j, hne', hrow, moveSeekWriteV6]
  have hSj : S j = setTicketV6 (H j) true := by
    simp [S, stepV6, j, hne', hrow, moveSeekWriteV6]
  have hSOther : forall i, i ≠ e -> i ≠ j -> S i = H i := by
    intro i hie hij
    simp [S, stepV6, j, hne', hrow, hie, hij]
  have hlt : controllerWeightV6 (S j) < controllerWeightV6 (H j) := by
    rw [show S j = setTicketV6 (H j) true from hSj]
    rw [show H j = setControlV6 (C j) .front true from hJ]
    simp [controllerWeightV6, setTicketV6, setControlV6,
      withCarrierClearTicketV6, setControl, setPhysical, role]
  have hleW : forall i, controllerWeightV6 (S i) <=
      controllerWeightV6 (H i) := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [show S e = H e from hSe]
      exact Nat.le_refl _
    · by_cases hij : i = j
      · subst i
        exact Nat.le_of_lt hlt
      · have hSi := hSOther i hie hij
        rw [show S i = H i from hSi]
        exact Nat.le_refl _
  unfold controllerPotentialV6
  exact ofFn_sum_lt_of_single_lt _ _ j hleW hlt

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private theorem hOneThree : 1 <= 3 := by decide
private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩

def q11866StartV10b : R1ConfigV6 2 3 0 0 := fun i =>
  if i = (0 : Fin 2) then
    setTicketV6 (clearControlV6
      (B9SpliceControllerR1TableV6.moveAcquireAbortStart2V6 i)) true
  else clearControlV6
    (B9SpliceControllerR1TableV6.moveAcquireAbortStart2V6 i)

private def zeroCell3 : R1AgentStateV6 2 1 1 :=
  clearControlV6 (q11703StartV7 (1 : Fin 3))
private def oneCell3 : R1AgentStateV6 2 1 1 :=
  clearControlV6 (q11703StartV7 (2 : Fin 3))

def q11874StartV10b : R1ConfigV6 3 2 1 1 := fun i =>
  if i = (0 : Fin 3) then setTicketV6 zeroCell3 true
  else if i = (1 : Fin 3) then zeroCell3 else oneCell3

def runV10bWord
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau -> List (Fin n) -> R1ConfigV6 n psi kappa tau
  | C, [] => C
  | C, e :: es => runV10bWord hpsi hwidth hle ring
      (stepV10b hpsi hwidth hle ring C e) es

private def cycle2Word : List (Fin 2) := [0, 1, 0, 1, 0, 1]
private def cycle3Word : List (Fin 3) := [0, 1, 2, 0, 1, 2]

theorem q11866_cycle_broken_v10b :
    exists i : Fin 2, runV10bWord hThree hOne hOneThree ring2
      q11866StartV10b cycle2Word i ≠ q11866StartV10b i := by
  decide

theorem q11874_cycle_broken_v10b :
    exists i : Fin 3, runV10bWord hTwo hOne hOneTwo ring3
      q11874StartV10b cycle3Word i ≠ q11874StartV10b i := by
  decide

def LiveAlongV10b
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau -> List (Fin n) -> Prop
  | C, [] => SpliceSafeV7 (kappa := kappa) (tau := tau) hpsi ring C
  | C, e :: es =>
      SpliceSafeV7 (kappa := kappa) (tau := tau) hpsi ring C /\
      (exists i, stepV10b hpsi hwidth hle ring C e i ≠ C i) /\
      LiveAlongV10b hpsi hwidth hle ring
        (stepV10b hpsi hwidth hle ring C e) es

def V10bWindowDrainOrEnd
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  3 <= n -> forall C es, es.length = n ->
    LiveAlongV10b (kappa := kappa) (tau := tau)
      hpsi hwidth hle ring C es ->
    (exists pre e post,
      es = pre ++ e :: post /\
      controllerPotentialV6
        (stepV10b hpsi hwidth hle ring
          (runV10bWord hpsi hwidth hle ring C pre) e) <
      controllerPotentialV6 (runV10bWord hpsi hwidth hle ring C pre)) \/
    (exists pre post,
      es = pre ++ post /\
      RolesClearV7 (runV10bWord hpsi hwidth hle ring C pre))

end B9SpliceControllerR1TableV10b

#print axioms B9SpliceControllerR1TableV10b.controllerStateFactorV10b_eq
#print axioms B9SpliceControllerR1TableV10b.corrected_handoff_preserves_spliceSafeV7
#print axioms B9SpliceControllerR1TableV10b.handoff_next_v6_service_drops
#print axioms B9SpliceControllerR1TableV10b.q11866_cycle_broken_v10b
#print axioms B9SpliceControllerR1TableV10b.q11874_cycle_broken_v10b
#print axioms B9SpliceControllerR1TableV10b.V10bWindowDrainOrEnd

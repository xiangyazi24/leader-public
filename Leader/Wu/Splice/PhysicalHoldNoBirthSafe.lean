import Leader.Wu.Splice.PhysicalHoldTable
import Leader.Wu.Splice.OrdinaryHostLabelFrame

set_option autoImplicit false
set_option Elab.async false

/-! # Physical hold, no-birth branch: SpliceSafeV7 is preserved with kept roles

Generalises `B9SpliceV8OrdinaryHost.ordinary_no_birth_preserves_spliceSafeV7` from a neutral
served pair to a pair whose controller fields are kept: the right endpoint is either a neutral
cell (any ticket) or a reserved front; the left endpoint is arbitrary. -/

namespace B9SpliceV10ePhysicalHoldNoBirth

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceV8LabelFrame B9SpliceTableV10e

variable {n psi width kappa tau : Nat}

/-! ## Local physical helpers (copies of the private V8 helpers) -/

private theorem normalizeDeletion_leader_local (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion; split <;> rfl

private theorem prepareDisposal_leader_local (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.leader = u.core.leader := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion; split <;> rfl
  · rfl

private theorem normalizeDeletion_label_local (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion; split <;> rfl

private theorem prepareDisposal_label_local (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.label = u.core.label := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion; split <;> rfl
  · rfl

private theorem preparedSplice_leader_local (hpsi : 0 < psi) (u : SpliceAgentState psi kappa tau) :
    (prepared hpsi u).core.leader = u.base.core.core.leader := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.base.core]
  rw [normalizeDeletion_leader_local, prepareDisposal_leader_local]
  rfl

private theorem preparedSplice_label_local (hpsi : 0 < psi) (u : SpliceAgentState psi kappa tau) :
    (prepared hpsi u).core.label = u.base.core.core.label := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.base.core]
  rw [normalizeDeletion_label_local, prepareDisposal_label_local]
  rfl

private theorem preparedR1_leader_local (hpsi : 0 < psi) (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.leader = u.splice.base.core.core.leader := by
  simpa [preparedR1] using (preparedSplice_leader_local hpsi u.splice)

theorem danger_iff_physical
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (x : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 C) x <->
      (C x).carrier.splice.base.core.core.leader = false /\
      (C (ring.rightNeighbor x)).carrier.splice.base.core.core.leader = false /\
      (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label ≠
        ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6 projectSpliceConfig
  dsimp only
  unfold isBarrier
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (preparedR1_leader_local hpsi (C x).carrier).symm.trans h.1
    · exact (preparedSplice_leader_local hpsi (C (ring.rightNeighbor x)).carrier.splice).symm.trans h.2.1
    · intro heq
      apply h.2.2
      calc
        (prepared hpsi (C (ring.rightNeighbor x)).carrier.splice).core.label =
            (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label :=
          preparedSplice_label_local hpsi (C (ring.rightNeighbor x)).carrier.splice
        _ = ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := heq
        _ = ⟨(((prepared hpsi (C x).carrier.splice).core.label).val + 1) % psi, Nat.mod_lt _ hpsi⟩ :=
          congrArg (fun a : Fin psi => (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
            (preparedSplice_label_local hpsi (C x).carrier.splice).symm
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (preparedR1_leader_local hpsi (C x).carrier).trans h.1
    · exact (preparedSplice_leader_local hpsi (C (ring.rightNeighbor x)).carrier.splice).trans h.2.1
    · intro heq
      apply h.2.2
      calc
        (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label =
            (prepared hpsi (C (ring.rightNeighbor x)).carrier.splice).core.label :=
          (preparedSplice_label_local hpsi (C (ring.rightNeighbor x)).carrier.splice).symm
        _ = ⟨(((prepared hpsi (C x).carrier.splice).core.label).val + 1) % psi, Nat.mod_lt _ hpsi⟩ := heq
        _ = ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ :=
          congrArg (fun a : Fin psi => (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
            (preparedSplice_label_local hpsi (C x).carrier.splice)

private theorem v3Protection_frame
    (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (hr : forall i, role (D i).carrier = role (C i).carrier)
    (hp : forall i, (D i).carrier.repairPending = (C i).carrier.repairPending) :
    R1ProtectedSpliceEdgeV3 ring (projectV6 D) x <-> R1ProtectedSpliceEdgeV3 ring (projectV6 C) x := by
  unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard projectV6
  dsimp only
  simp only [hr x, hp x, hr (ring.rightNeighbor x), hp (ring.rightNeighbor x)]

private theorem danger_congr_carrier_at
    (hpsi : 0 < psi) (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (hL : (D x).carrier = (C x).carrier)
    (hR : (D (ring.rightNeighbor x)).carrier = (C (ring.rightNeighbor x)).carrier) :
    PreparedDangerAt hpsi ring (projectV6 D) x <-> PreparedDangerAt hpsi ring (projectV6 C) x := by
  unfold PreparedDangerAt PreparedBarrierAt projectSpliceConfig projectV6
  dsimp only
  rw [hL, hR]

private theorem rightFollowerRelabelledV7_false_label
    (old out : R1AgentStateV4 psi kappa tau)
    (hrel : rightFollowerRelabelledV7 old out = false)
    (hr : role out = .none) (hp : out.repairPending = false)
    (hl : out.splice.base.core.core.leader = false) :
    out.splice.base.core.core.label = old.splice.base.core.core.label := by
  by_cases heq : out.splice.base.core.core.label = old.splice.base.core.core.label
  · exact heq
  · have ht : rightFollowerRelabelledV7 old out = true := by
      simp [rightFollowerRelabelledV7, hr, hp, hl, heq]
    have hbad : (false : Bool) = true := hrel.symm.trans ht
    cases hbad

private theorem rightFollowerRelabelledV7_true_role
    (old out : R1AgentStateV4 psi kappa tau)
    (hrel : rightFollowerRelabelledV7 old out = true) :
    role out = .none ∧ out.repairPending = false := by
  unfold rightFollowerRelabelledV7 at hrel
  have h := of_decide_eq_true hrel
  exact ⟨h.1, h.2.1⟩

/-! ## Frame of the physical hold at configuration level -/

section Frame

variable (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
  (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)

theorem physicalHoldAt_e :
    physicalHoldAt hpsi hwidth hle ring C e e =
      (physicalHoldV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1 := by
  simp [physicalHoldAt]

theorem physicalHoldAt_j (hself : ring.rightNeighbor e ≠ e) :
    physicalHoldAt hpsi hwidth hle ring C e (ring.rightNeighbor e) =
      (physicalHoldV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).2 := by
  simp [physicalHoldAt, hself]

theorem physicalHoldAt_other (i : Fin n) (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    physicalHoldAt hpsi hwidth hle ring C e i = C i := by
  simp [physicalHoldAt, hi, hj]

theorem physicalHold_role_frame (l r : R1AgentStateV6 psi kappa tau) :
    role (physicalHoldV6 hpsi hwidth hle l r).1.carrier = role l.carrier ∧
    (physicalHoldV6 hpsi hwidth hle l r).1.carrier.repairPending = l.carrier.repairPending ∧
    role (physicalHoldV6 hpsi hwidth hle l r).2.carrier = role r.carrier ∧
    (physicalHoldV6 hpsi hwidth hle l r).2.carrier.repairPending = r.carrier.repairPending := by
  simp only [physicalHoldV6]
  split <;> simp [ordinaryRow, setTicketV6, setPhysical, role]

theorem physicalHold_right_ticket (l r : R1AgentStateV6 psi kappa tau) :
    (physicalHoldV6 hpsi hwidth hle l r).2.acquireTicket =
      (if rightFollowerRelabelledV7 r.carrier (ordinaryRow hpsi hwidth hle l.carrier r.carrier).2
        then true else r.acquireTicket) := by
  simp only [physicalHoldV6]
  split <;> simp_all [setTicketV6]

end Frame

/-! ## The theorem -/

theorem physicalHold_no_birth_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hself : ring.rightNeighbor e ≠ e)
    (hrshape : (role (C (ring.rightNeighbor e)).carrier = .none ∧
        (C (ring.rightNeighbor e)).carrier.repairPending = false) ∨
      ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier)
    (hl : (C e).carrier.splice.base.core.core.leader = false)
    (hr : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hpsi
      (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base)
    (hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = false) :
    SpliceSafeV7 hpsi ring (physicalHoldAt hpsi hwidth hle ring C e) := by
  let j := ring.rightNeighbor e
  let D := physicalHoldAt hpsi hwidth hle ring C e
  let q := physicalHoldV6 hpsi hwidth hle (C e) (C j)
  let o := ordinaryRow hpsi hwidth hle (C e).carrier (C j).carrier
  have hDe : D e = q.1 := physicalHoldAt_e hpsi hwidth hle ring C e
  have hDj : D j = q.2 := physicalHoldAt_j hpsi hwidth hle ring C e hself
  have hDother : forall i, i ≠ e -> i ≠ j -> D i = C i :=
    fun i hi hj => physicalHoldAt_other hpsi hwidth hle ring C e i hi hj
  obtain ⟨hqLRole, hqLPend, hqRRole, hqRPend⟩ := physicalHold_role_frame hpsi hwidth hle (C e) (C j)
  have hqCarrierL : q.1.carrier = o.1 := physicalHold_left_carrier hpsi hwidth hle (C e) (C j)
  have hqCarrierR : q.2.carrier = o.2 := physicalHold_right_carrier hpsi hwidth hle (C e) (C j)
  have hqLTicket : q.1.acquireTicket = (C e).acquireTicket :=
    physicalHold_left_ticket hpsi hwidth hle (C e) (C j)
  have hqRTicket := physicalHold_right_ticket hpsi hwidth hle (C e) (C j)
  have hrole : forall i, role (D i).carrier = role (C i).carrier := by
    intro i
    by_cases hie : i = e
    · subst i; exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => role u.carrier) hDe).trans hqLRole
    · by_cases hij : i = j
      · subst i; exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => role u.carrier) hDj).trans hqRRole
      · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => role u.carrier) (hDother i hie hij)
  have hpending : forall i, (D i).carrier.repairPending = (C i).carrier.repairPending := by
    intro i
    by_cases hie : i = e
    · subst i; exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.repairPending) hDe).trans hqLPend
    · by_cases hij : i = j
      · subst i; exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.repairPending) hDj).trans hqRPend
      · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.repairPending) (hDother i hie hij)
  have htOffJ : forall i, i ≠ j -> (D i).acquireTicket = (C i).acquireTicket := by
    intro i hij
    by_cases hie : i = e
    · subst i; exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket) hDe).trans hqLTicket
    · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket) (hDother i hie hij)
  -- ticket at j: either newly set by the relabel rule (then the cell is neutral) or unchanged
  have htJ : (D j).acquireTicket = true ->
      ((role (C j).carrier = .none ∧ (C j).carrier.repairPending = false) ∨ (C j).acquireTicket = true) := by
    intro ht
    have ht' : q.2.acquireTicket = true :=
      (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket) hDj).symm.trans ht
    rw [hqRTicket] at ht'
    by_cases hrel : rightFollowerRelabelledV7 (C j).carrier o.2 = true
    · left
      have hro := rightFollowerRelabelledV7_true_role (C j).carrier o.2 hrel
      refine ⟨?_, ?_⟩
      · calc role (C j).carrier = role q.2.carrier := hqRRole.symm
          _ = role o.2 := congrArg role hqCarrierR
          _ = .none := hro.1
      · calc (C j).carrier.repairPending = q.2.carrier.repairPending := hqRPend.symm
          _ = o.2.repairPending := congrArg (fun u : R1AgentStateV4 psi kappa tau => u.repairPending) hqCarrierR
          _ = false := hro.2
    · right
      have hrel' : rightFollowerRelabelledV7 (C j).carrier o.2 = false := by
        cases hh : rightFollowerRelabelledV7 (C j).carrier o.2
        · rfl
        · exact absurd hh hrel
      have hrel'' : rightFollowerRelabelledV7 (C j).carrier
          (ordinaryRow hpsi hwidth hle (C e).carrier (C j).carrier).2 = false := by
        simpa only [o] using hrel'
      simpa [hrel''] using ht'
  have htJ' : (C j).acquireTicket = false -> ¬ rightFollowerRelabelledV7 (C j).carrier o.2 = true ->
      (D j).acquireTicket = false := by
    intro hc hrel
    have hrel' : rightFollowerRelabelledV7 (C j).carrier o.2 = false := by
      cases hh : rightFollowerRelabelledV7 (C j).carrier o.2
      · rfl
      · exact absurd hh hrel
    have hrel'' : rightFollowerRelabelledV7 (C j).carrier
        (ordinaryRow hpsi hwidth hle (C e).carrier (C j).carrier).2 = false := by
      simpa only [o] using hrel'
    rw [hDj, hqRTicket]
    simp [hrel'', hc]
  -- labels of the served pair
  have hlabels0 := BirthShortDoneTerminalOrdinaryLabelR1.ordinary_row_labels_of_no_birth
    hpsi hwidth hle (C e).carrier.splice.base (C j).carrier.splice.base hl hr hopen hb
  have hbaseL := physicalHold_base_left hpsi hwidth hle (C e) (C j)
  have hbaseR := physicalHold_base_right hpsi hwidth hle (C e) (C j)
  have hleftLabel : (D e).carrier.splice.base.core.core.label = (C e).carrier.splice.base.core.core.label := by
    rw [hDe]
    have := congrArg (fun b : ExpiringAgentState psi kappa tau => b.core.core.label) hbaseL
    exact this.trans hlabels0.1
  have haligned : (D j).carrier.splice.base.core.core.label =
      ⟨((D e).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    rw [hleftLabel, hDj]
    have := congrArg (fun b : ExpiringAgentState psi kappa tau => b.core.core.label) hbaseR
    exact this.trans hlabels0.2
  refine ⟨?_, ?_⟩
  · intro x hdx
    have hd := (danger_iff_physical hpsi ring D x).1 hdx
    by_cases hxe : x = e
    · subst x
      exact (hd.2.2 (by simpa only [j] using haligned)).elim
    by_cases hxj : x = j
    · subst x
      -- the responder's outgoing edge
      rcases hrshape with hneutral | hfront
      · by_cases ht : (D j).acquireTicket = true
        · right
          exact ⟨(hrole j).trans hneutral.1, (hpending j).trans hneutral.2, ht⟩
        · -- no ticket after the step: the cell was unticketed and not relabelled
          have htf : (D j).acquireTicket = false := by
            cases hh : (D j).acquireTicket
            · rfl
            · exact absurd hh ht
          have hCt : (C j).acquireTicket = false := by
            by_cases hc : (C j).acquireTicket = true
            · have : (D j).acquireTicket = true := by
                rw [hDj, hqRTicket]; split <;> simp [hc]
              exact absurd this ht
            · cases hh : (C j).acquireTicket
              · rfl
              · exact absurd hh hc
          have hrel : rightFollowerRelabelledV7 (C j).carrier o.2 = false := by
            cases hh : rightFollowerRelabelledV7 (C j).carrier o.2
            · rfl
            · have hh' : rightFollowerRelabelledV7 (C j).carrier
                  (ordinaryRow hpsi hwidth hle (C e).carrier (C j).carrier).2 = true := by
                simpa only [o] using hh
              have : (D j).acquireTicket = true := by
                rw [hDj, hqRTicket]; simp [hh']
              exact absurd this ht
          have hoRole : role o.2 = .none := by
            calc role o.2 = role q.2.carrier := (congrArg role hqCarrierR).symm
              _ = role (C j).carrier := hqRRole
              _ = .none := hneutral.1
          have hoPend : o.2.repairPending = false := by
            calc o.2.repairPending = q.2.carrier.repairPending :=
                  (congrArg (fun u : R1AgentStateV4 psi kappa tau => u.repairPending) hqCarrierR).symm
              _ = (C j).carrier.repairPending := hqRPend
              _ = false := hneutral.2
          have hoFollower : o.2.splice.base.core.core.leader = false := by
            calc o.2.splice.base.core.core.leader = q.2.carrier.splice.base.core.core.leader :=
                  (congrArg (fun u : R1AgentStateV4 psi kappa tau => u.splice.base.core.core.leader) hqCarrierR).symm
              _ = (D j).carrier.splice.base.core.core.leader :=
                  (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.splice.base.core.core.leader) hDj).symm
              _ = false := hd.1
          have hoLabel : o.2.splice.base.core.core.label = (C j).carrier.splice.base.core.core.label :=
            rightFollowerRelabelledV7_false_label (C j).carrier o.2 hrel hoRole hoPend hoFollower
          have hjLabel : (D j).carrier.splice.base.core.core.label = (C j).carrier.splice.base.core.core.label := by
            calc (D j).carrier.splice.base.core.core.label = q.2.carrier.splice.base.core.core.label :=
                  congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.splice.base.core.core.label) hDj
              _ = o.2.splice.base.core.core.label :=
                  congrArg (fun u : R1AgentStateV4 psi kappa tau => u.splice.base.core.core.label) hqCarrierR
              _ = (C j).carrier.splice.base.core.core.label := hoLabel
          let k := ring.rightNeighbor j
          have hkj : k ≠ j := by
            intro hh
            change ring.rightNeighbor j = j at hh
            have hrn : ring.rightNeighbor j = ring.rightNeighbor e := by
              calc ring.rightNeighbor j = j := hh
                _ = ring.rightNeighbor e := rfl
            have hjeq : j = e := B9OrphanToFence.rightNeighbor_inj ring hrn
            apply hself
            calc ring.rightNeighbor e = j := rfl
              _ = e := hjeq
          have hkLabel : (D k).carrier.splice.base.core.core.label = (C k).carrier.splice.base.core.core.label := by
            by_cases hke : k = e
            · simpa only [hke] using hleftLabel
            · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.splice.base.core.core.label)
                (hDother k hke (by simpa only [j] using hkj))
          have hkLeader : (C k).carrier.splice.base.core.core.leader = false := by
            by_cases hke : k = e
            · simpa only [hke] using hl
            · have hDk := hDother k hke (by simpa only [j] using hkj)
              have hDkLeader := congrArg
                (fun u : R1AgentStateV6 psi kappa tau => u.carrier.splice.base.core.core.leader) hDk
              exact hDkLeader.symm.trans (by simpa only [k] using hd.2.1)
          have hbar : (C k).carrier.splice.base.core.core.label ≠
              ⟨((C j).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
            intro hh
            apply hd.2.2
            calc (D k).carrier.splice.base.core.core.label = (C k).carrier.splice.base.core.core.label := hkLabel
              _ = ⟨((C j).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := hh
              _ = ⟨((D j).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ :=
                congrArg (fun a : Fin psi => (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi)) hjLabel.symm
          have hold := hsafe.1 j ((danger_iff_physical hpsi ring C j).2 ⟨hr, hkLeader, hbar⟩)
          change R1ProtectedSpliceEdgeV3 ring (projectV6 C) j \/ HostFenceShapeV7 (C j) at hold
          rcases hold with hv3 | hf
          · exact Or.inl ((v3Protection_frame ring C D j hrole hpending).2 hv3)
          · have hbad : (false : Bool) = true := hCt.symm.trans hf.2.2
            cases hbad
      · -- reserved front: its own certificate protects the outgoing edge
        left
        unfold R1ProtectedSpliceEdgeV3
        simp only [projectV6]
        left
        unfold ReservedFrontHoldGuard at hfront ⊢
        exact ⟨(hrole j).trans hfront.1, (hpending j).trans hfront.2⟩
    · let y := ring.rightNeighbor x
      have hyj : y ≠ j := by
        intro hh
        apply hxe
        apply B9OrphanToFence.rightNeighbor_inj ring
        simpa only [y, j] using hh
      have hDx : D x = C x := hDother x hxe (by simpa only [j] using hxj)
      by_cases hye : y = e
      · have hin : ring.rightNeighbor x = e := by simpa only [y] using hye
        have hxLeader : (C x).carrier.splice.base.core.core.leader = false := by
          have hxl := congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.splice.base.core.core.leader) hDx
          exact hxl.symm.trans hd.1
        have hyLeader : (C (ring.rightNeighbor x)).carrier.splice.base.core.core.leader = false := by
          rw [hin]; exact hl
        have hxLabel : (D x).carrier.splice.base.core.core.label = (C x).carrier.splice.base.core.core.label :=
          congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.splice.base.core.core.label) hDx
        have hbar : (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label ≠
            ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
          rw [hin]
          intro hh
          apply hd.2.2
          have hindex := congrArg (fun z : Fin n => (D z).carrier.splice.base.core.core.label) hin
          apply hindex.trans
          calc (D e).carrier.splice.base.core.core.label = (C e).carrier.splice.base.core.core.label := hleftLabel
            _ = ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := hh
            _ = ⟨((D x).carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ :=
              congrArg (fun a : Fin psi => (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi)) hxLabel.symm
        have hold := hsafe.1 x ((danger_iff_physical hpsi ring C x).2 ⟨hxLeader, hyLeader, hbar⟩)
        change R1ProtectedSpliceEdgeV3 ring (projectV6 C) x \/ HostFenceShapeV7 (C x) at hold
        rcases hold with hv3 | hf
        · exact Or.inl ((v3Protection_frame ring C D x hrole hpending).2 hv3)
        · exact Or.inr (cast (congrArg HostFenceShapeV7 hDx.symm) hf)
      · have hDy : D y = C y := hDother y hye (by simpa only [y, j] using hyj)
        have hL : (D x).carrier = (C x).carrier :=
          congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier) hDx
        have hR : (D (ring.rightNeighbor x)).carrier = (C (ring.rightNeighbor x)).carrier := by
          simpa only [y] using congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier) hDy
        have hd0 := (danger_congr_carrier_at hpsi ring C D x hL hR).1 hdx
        have hold := hsafe.1 x hd0
        unfold ProtectedSpliceEdgeV7 at hold ⊢
        rcases hold with hv3 | hf
        · exact Or.inl ((v3Protection_frame ring C D x hrole hpending).2 hv3)
        · exact Or.inr (cast (congrArg HostFenceShapeV7 hDx.symm) hf)
  · refine ⟨?_, ?_⟩
    · intro i
      unfold TicketShapeV7
      intro ht
      by_cases hij : i = j
      · subst i
        rcases htJ ht with hneutral | hCt
        · exact Or.inr ⟨(hrole j).trans hneutral.1, (hpending j).trans hneutral.2, ht⟩
        · rcases hsafe.2.1 j hCt with hres | hf
          · left
            unfold ReservedFrontHoldGuard at hres ⊢
            exact ⟨(hrole j).trans hres.1, (hpending j).trans hres.2⟩
          · right
            unfold HostFenceShapeV7 at hf ⊢
            exact ⟨(hrole j).trans hf.1, (hpending j).trans hf.2.1, ht⟩
      · have htC : (C i).acquireTicket = true := (htOffJ i hij).symm.trans ht
        rcases hsafe.2.1 i htC with hres | hf
        · left
          unfold ReservedFrontHoldGuard at hres ⊢
          exact ⟨(hrole i).trans hres.1, (hpending i).trans hres.2⟩
        · right
          unfold HostFenceShapeV7 at hf ⊢
          exact ⟨(hrole i).trans hf.1, (hpending i).trans hf.2.1, ht⟩
    · intro i hri hpi
      have hriC : role (C i).carrier = .predecessorArmed := (hrole i).symm.trans hri
      have hpiC : (C i).carrier.repairPending = true := (hpending i).symm.trans hpi
      have hold := hsafe.2.2 i hriC hpiC
      let y := ring.rightNeighbor i
      have hres : ReservedFrontHoldGuard (C y).carrier := by simpa only [y] using hold.1
      have hyTicketC : (C y).acquireTicket = false := by simpa only [y] using hold.2
      constructor
      · unfold ReservedFrontHoldGuard at hres ⊢
        exact ⟨(hrole y).trans hres.1, (hpending y).trans hres.2⟩
      · by_cases hyJ : y = j
        · -- the front is the responder: it is not neutral, so the relabel rule cannot ticket it
          have hfrontJ : role (C j).carrier = .front := by
            unfold ReservedFrontHoldGuard at hres
            simpa only [hyJ] using hres.1
          have hnotrel : ¬ rightFollowerRelabelledV7 (C j).carrier o.2 = true := by
            intro hrel
            have hro := rightFollowerRelabelledV7_true_role (C j).carrier o.2 hrel
            have : role (C j).carrier = .none := by
              calc role (C j).carrier = role q.2.carrier := hqRRole.symm
                _ = role o.2 := congrArg role hqCarrierR
                _ = .none := hro.1
            rw [hfrontJ] at this
            cases this
          have hCtJ : (C j).acquireTicket = false := by simpa only [hyJ] using hyTicketC
          have := htJ' hCtJ hnotrel
          simpa only [y, hyJ] using this
        · have ht := (htOffJ y hyJ).trans hyTicketC
          simpa only [y] using ht

end B9SpliceV10ePhysicalHoldNoBirth

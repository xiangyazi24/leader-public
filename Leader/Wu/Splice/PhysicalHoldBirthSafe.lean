import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
import Leader.Wu.Splice.OrdinaryHostBirthFollowerDischarged

set_option autoImplicit false
set_option Elab.async false

/-! # Physical hold, birth branch: SpliceSafeV7 is preserved with kept roles

The physical row creates a leader at one served endpoint.  Edges touching the new leader are
no longer dangers; the follower endpoint keeps its label (left) or is fenced / keeps its own
certificate (right).  Generalises `B9SpliceV8BirthCase.ordinary_birth_preserves_spliceSafeV7`
to arbitrary kept roles, with the served pair assumed leaderless before the step. -/

namespace B9SpliceV10ePhysicalHoldBirth

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open BirthShortDoneTerminalHost K2BirthLeaderNormalize
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceV8LabelFrame B9SpliceV8BirthCaseAdapter
  B9SpliceTableV10e B9SpliceV10ePhysicalHoldNoBirth

variable {n psi width kappa tau : Nat}

/-- A follower initiator keeps its label under the physical row (no controller hypothesis). -/
theorem left_follower_label_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (L R : ExpiringAgentState psi kappa tau) (hl : L.core.core.leader = false) :
    (BirthShortDoneTerminalHost.row hpsi hwidth hle L R).1.core.core.label = L.core.core.label := by
  let d := doneMetadataEntryWidth hpsi hwidth hle L R
  have hdfalse : d.1.core.core.leader = false :=
    (metadataEntry_left_leader (kappa := kappa) (tau := tau) hpsi hwidth hle L R).trans hl
  let m := BirthShortDoneTerminalHost.metadata hpsi hwidth hle L R
  have hnlabel : m.1.core.core.label = d.1.core.core.label := by
    change (normalizeLeader hpsi d.1).core.core.label = d.1.core.core.label
    unfold normalizeLeader
    rw [hdfalse]
    rfl
  have hrowlabel := hostRow_labels_metadata (kappa := kappa) (tau := tau) hpsi hwidth hle L R
  have hdlabel := metadataEntry_left_label (kappa := kappa) (tau := tau) hpsi hwidth hle L R
  exact hrowlabel.1.trans (hnlabel.trans hdlabel)

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

theorem physicalHold_birth_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hself : ring.rightNeighbor e ≠ e)
    (hrshape : (role (C (ring.rightNeighbor e)).carrier = .none ∧
        (C (ring.rightNeighbor e)).carrier.repairPending = false) ∨
      ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier)
    (hl : (C e).carrier.splice.base.core.core.leader = false)
    (hr : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false)
    (hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = true) :
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
  have hqCarrierR : q.2.carrier = o.2 := physicalHold_right_carrier hpsi hwidth hle (C e) (C j)
  have hqLTicket : q.1.acquireTicket = (C e).acquireTicket :=
    physicalHold_left_ticket hpsi hwidth hle (C e) (C j)
  have hqRTicket := physicalHold_right_ticket hpsi hwidth hle (C e) (C j)
  have hbaseL := physicalHold_base_left hpsi hwidth hle (C e) (C j)
  have hbaseR := physicalHold_base_right hpsi hwidth hle (C e) (C j)
  have hrJ : (C j).carrier.splice.base.core.core.leader = false := by simpa only [j] using hr
  have hbJ : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C j).carrier.splice.base = true := by simpa only [j] using hb
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
  -- the follower initiator keeps its label
  have hleftLabel : (D e).carrier.splice.base.core.core.label = (C e).carrier.splice.base.core.core.label := by
    rw [hDe]
    have := congrArg (fun b : ExpiringAgentState psi kappa tau => b.core.core.label) hbaseL
    exact this.trans (left_follower_label_frame hpsi hwidth hle
      (C e).carrier.splice.base (C j).carrier.splice.base hl)
  -- the birth
  have hbirth := BirthShortDoneTerminalBirthPhysical.birthEvent_true_row_has_physical_leader
    hpsi hwidth hle (C e).carrier.splice.base (C j).carrier.splice.base hbJ
  have hbirthD : (D e).carrier.splice.base.core.core.leader = true \/
      (D j).carrier.splice.base.core.core.leader = true := by
    rcases hbirth with hL | hR
    · left
      rw [hDe]
      have := congrArg (fun b : ExpiringAgentState psi kappa tau => b.core.core.leader) hbaseL
      exact this.trans hL
    · right
      rw [hDj]
      have := congrArg (fun b : ExpiringAgentState psi kappa tau => b.core.core.leader) hbaseR
      exact this.trans hR
  refine ⟨?_, ?_⟩
  · intro x hdx
    have hd := (danger_iff_physical hpsi ring D x).1 hdx
    by_cases hxe : x = e
    · subst x
      rcases hbirthD with hL | hR
      · exact absurd hd.1 (by rw [hL]; decide)
      · have hR0 : (D (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = true := by
          simpa only [j] using hR
        exact absurd hd.2.1 (by rw [hR0]; decide)
    by_cases hxj : x = j
    · subst x
      rcases hbirthD with hL | hR
      · -- birth on the left; the responder's outgoing edge
        rcases hrshape with hneutral | hfront
        · by_cases ht : (D j).acquireTicket = true
          · right
            exact ⟨(hrole j).trans hneutral.1, (hpending j).trans hneutral.2, ht⟩
          · have hCt : (C j).acquireTicket = false := by
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
            -- k = e is impossible here: e is the new leader but the danger needs k a follower
            have hke : k ≠ e := by
              intro hke
              have hkl : (D k).carrier.splice.base.core.core.leader = false := by
                simpa only [k] using hd.2.1
              rw [hke] at hkl
              exact absurd hkl (by rw [hL]; decide)
            have hDk : D k = C k := hDother k hke (by simpa only [j] using hkj)
            have hkLabel : (D k).carrier.splice.base.core.core.label = (C k).carrier.splice.base.core.core.label :=
              congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.splice.base.core.core.label) hDk
            have hkLeader : (C k).carrier.splice.base.core.core.leader = false := by
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
            have hold := hsafe.1 j ((danger_iff_physical hpsi ring C j).2 ⟨hrJ, hkLeader, hbar⟩)
            change R1ProtectedSpliceEdgeV3 ring (projectV6 C) j \/ HostFenceShapeV7 (C j) at hold
            rcases hold with hv3 | hf
            · exact Or.inl ((v3Protection_frame ring C D j hrole hpending).2 hv3)
            · have hbad : (false : Bool) = true := hCt.symm.trans hf.2.2
              cases hbad
        · left
          unfold R1ProtectedSpliceEdgeV3
          simp only [projectV6]
          left
          unfold ReservedFrontHoldGuard at hfront ⊢
          exact ⟨(hrole j).trans hfront.1, (hpending j).trans hfront.2⟩
      · exact absurd hd.1 (by rw [hR]; decide)
    · let y := ring.rightNeighbor x
      have hyj : y ≠ j := by
        intro hh
        apply hxe
        apply B9OrphanToFence.rightNeighbor_inj ring
        simpa only [y, j] using hh
      have hDx : D x = C x := hDother x hxe (by simpa only [j] using hxj)
      by_cases hye : y = e
      · have hin : ring.rightNeighbor x = e := by simpa only [y] using hye
        have hfE : (D e).carrier.splice.base.core.core.leader = false := by
          have hh := hd.2.1
          simpa only [hin] using hh
        rcases hbirthD with hL | hR
        · exact absurd hfE (by rw [hL]; decide)
        · have hxLeader : (C x).carrier.splice.base.core.core.leader = false := by
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
        · have hfrontJ : role (C j).carrier = .front := by
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

end B9SpliceV10ePhysicalHoldBirth

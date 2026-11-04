import Leader.Wu.Splice.OrdinaryHostLabelFrame


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceV8OrdinaryHost


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceV8LabelFrame


variable {n psi width kappa tau : Nat}


/-- Exact controller shape at the final V8 ordinary fallback. -/
def OrdinaryNeutralPairV8
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  role l.carrier = .none /\ l.carrier.repairPending = false /\
  l.acquireTicket = false /\
  role r.carrier = .none /\ r.carrier.repairPending = false /\
  r.acquireTicket = false


private theorem normalizeDeletion_leader_local
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareDisposal_leader_local
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.leader = u.core.leader := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl


private theorem normalizeDeletion_label_local
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareDisposal_label_local
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.label = u.core.label := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl


private theorem preparedSplice_leader_local
    (hpsi : 0 < psi) (u : SpliceAgentState psi kappa tau) :
    (prepared hpsi u).core.leader = u.base.core.core.leader := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.base.core]
  rw [normalizeDeletion_leader_local, prepareDisposal_leader_local]
  rfl


private theorem preparedSplice_label_local
    (hpsi : 0 < psi) (u : SpliceAgentState psi kappa tau) :
    (prepared hpsi u).core.label = u.base.core.core.label := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.base.core]
  rw [normalizeDeletion_label_local, prepareDisposal_label_local]
  rfl


private theorem preparedR1_leader_local
    (hpsi : 0 < psi) (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.leader =
      u.splice.base.core.core.leader := by
  simpa [preparedR1] using
    (preparedSplice_leader_local hpsi u.splice)


/-- Prepared danger is exactly the physical follower/follower label defect.
Use propositional inequality here; Boolean `!=` would make the last conjunct
non-functional and is what caused the old “Function expected” failures. -/
private theorem danger_iff_physical
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (x : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 C) x <->
      (C x).carrier.splice.base.core.core.leader = false /\
      (C (ring.rightNeighbor x)).carrier.splice.base.core.core.leader = false /\
      (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label ≠
        ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6 projectSpliceConfig
  dsimp only
  unfold isBarrier
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (preparedR1_leader_local hpsi (C x).carrier).symm.trans h.1
    · exact
        (preparedSplice_leader_local hpsi
          (C (ring.rightNeighbor x)).carrier.splice).symm.trans h.2.1
    · intro heq
      apply h.2.2
      calc
        (prepared hpsi
            (C (ring.rightNeighbor x)).carrier.splice).core.label =
            (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label :=
          preparedSplice_label_local hpsi
            (C (ring.rightNeighbor x)).carrier.splice
        _ = ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := heq
        _ = ⟨(((prepared hpsi (C x).carrier.splice).core.label).val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ :=
          congrArg
            (fun a : Fin psi =>
              (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
            (preparedSplice_label_local hpsi (C x).carrier.splice).symm
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (preparedR1_leader_local hpsi (C x).carrier).trans h.1
    · exact
        (preparedSplice_leader_local hpsi
          (C (ring.rightNeighbor x)).carrier.splice).trans h.2.1
    · intro heq
      apply h.2.2
      calc
        (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label =
            (prepared hpsi
              (C (ring.rightNeighbor x)).carrier.splice).core.label :=
          (preparedSplice_label_local hpsi
            (C (ring.rightNeighbor x)).carrier.splice).symm
        _ = ⟨(((prepared hpsi (C x).carrier.splice).core.label).val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := heq
        _ = ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ :=
          congrArg
            (fun a : Fin psi =>
              (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
            (preparedSplice_label_local hpsi (C x).carrier.splice)


private theorem rightNeighbor_injective (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega


private theorem v3Protection_frame
    (ring : DirectedRing n)
    (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (hr : forall i, role (D i).carrier = role (C i).carrier)
    (hp : forall i, (D i).carrier.repairPending =
      (C i).carrier.repairPending) :
    R1ProtectedSpliceEdgeV3 ring (projectV6 D) x <->
      R1ProtectedSpliceEdgeV3 ring (projectV6 C) x := by
  unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard projectV6
  dsimp only
  simp only [hr x, hp x, hr (ring.rightNeighbor x),
    hp (ring.rightNeighbor x)]


/-- Local copy of the compiled V7 carrier-congruence helper. -/
private theorem danger_congr_carrier_at
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (hL : (D x).carrier = (C x).carrier)
    (hR : (D (ring.rightNeighbor x)).carrier =
      (C (ring.rightNeighbor x)).carrier) :
    PreparedDangerAt hpsi ring (projectV6 D) x <->
      PreparedDangerAt hpsi ring (projectV6 C) x := by
  unfold PreparedDangerAt PreparedBarrierAt projectSpliceConfig projectV6
  dsimp only
  rw [hL, hR]


/-- The ordinary physical row frames all splice roles and repair-pending bits;
the left ticket is always cleared. -/
private theorem ordinaryHostWriteV7_controller_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    let q := ordinaryHostWriteV7 hpsi hwidth hle l r
    role q.1.carrier = role l.carrier /\
      q.1.carrier.repairPending = l.carrier.repairPending /\
      q.1.acquireTicket = false /\
      role q.2.carrier = role r.carrier /\
      q.2.carrier.repairPending = r.carrier.repairPending := by
  unfold ordinaryHostWriteV7
  dsimp only
  split <;>
    simp [ordinaryRow, withCarrierClearTicketV6, setTicketV6,
      setPhysical, role]


/-- Ticket arming never changes either V4 carrier. -/
private theorem ordinaryHostWriteV7_carrier_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    let o := ordinaryRow hpsi hwidth hle l.carrier r.carrier
    let q := ordinaryHostWriteV7 hpsi hwidth hle l r
    q.1.carrier = o.1 /\ q.2.carrier = o.2 := by
  unfold ordinaryHostWriteV7
  dsimp only
  split <;> exact ⟨rfl, rfl⟩


private theorem ordinaryHostWriteV7_right_ticket_of_relabel
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hrel : rightFollowerRelabelledV7 r.carrier
      (ordinaryRow hpsi hwidth hle l.carrier r.carrier).2 = true) :
    (ordinaryHostWriteV7 hpsi hwidth hle l r).2.acquireTicket = true := by
  unfold ordinaryHostWriteV7
  dsimp only
  rw [hrel]
  rfl


private theorem rightFollowerRelabelledV7_false_label
    (old out : R1AgentStateV4 psi kappa tau)
    (hrel : rightFollowerRelabelledV7 old out = false)
    (hr : role out = .none)
    (hp : out.repairPending = false)
    (hl : out.splice.base.core.core.leader = false) :
    out.splice.base.core.core.label = old.splice.base.core.core.label := by
  by_cases heq : out.splice.base.core.core.label =
      old.splice.base.core.core.label
  · exact heq
  · have ht : rightFollowerRelabelledV7 old out = true := by
      simp [rightFollowerRelabelledV7, hr, hp, hl, heq]
    have hbad : (false : Bool) = true := hrel.symm.trans ht
    cases hbad


/-- The complete ordinary, no-birth V8 branch.  `hneutral` is the controller
certificate supplied by reaching the final fallback after the V8 HOLD and all
V7 controller guards have failed. -/
theorem ordinary_no_birth_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hneutral : OrdinaryNeutralPairV8
      (C e) (C (ring.rightNeighbor e)))
    (hrow : rowV8 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) =
        ordinaryHostWriteV7 hpsi hwidth hle
          (C e) (C (ring.rightNeighbor e)))
    (hl : (C e).carrier.splice.base.core.core.leader = false)
    (hr : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hpsi
      (C e).carrier.splice.base
      (C (ring.rightNeighbor e)).carrier.splice.base)
    (hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base
      (C (ring.rightNeighbor e)).carrier.splice.base = false) :
    SpliceSafeV7 hpsi ring
      (stepV8 hpsi hwidth hle ring C e) := by
  by_cases hself : ring.rightNeighbor e = e
  · simpa [stepV8, hself] using hsafe
  let j := ring.rightNeighbor e
  let D := stepV8 hpsi hwidth hle ring C e
  let o := ordinaryRow hpsi hwidth hle (C e).carrier (C j).carrier
  let q := ordinaryHostWriteV7 hpsi hwidth hle (C e) (C j)
  rcases hneutral with ⟨heRole, hePend, heTicket,
    hjRole, hjPend, hjTicket⟩
  have hjRoleJ : role (C j).carrier = .none := by
    simpa only [j] using hjRole
  have hjPendJ : (C j).carrier.repairPending = false := by
    simpa only [j] using hjPend
  have hjTicketJ : (C j).acquireTicket = false := by
    simpa only [j] using hjTicket
  have hrJ : (C j).carrier.splice.base.core.core.leader = false := by
    simpa only [j] using hr
  have hopenJ : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hpsi
      (C e).carrier.splice.base (C j).carrier.splice.base := by
    simpa only [j] using hopen
  have hbJ : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C j).carrier.splice.base = false := by
    simpa only [j] using hb
  have hDe : D e = q.1 := by
    simp [D, j, q, stepV8, hself, hrow]
  have hDj : D j = q.2 := by
    simp [D, j, q, stepV8, hself, hrow]
  have hctrl := ordinaryHostWriteV7_controller_frame
    hpsi hwidth hle (C e) (C j)
  change role q.1.carrier = role (C e).carrier /\
      q.1.carrier.repairPending = (C e).carrier.repairPending /\
      q.1.acquireTicket = false /\
      role q.2.carrier = role (C j).carrier /\
      q.2.carrier.repairPending = (C j).carrier.repairPending at hctrl
  rcases hctrl with
    ⟨hqLRole, hqLPend, hqLTicket, hqRRole, hqRPend⟩
  have hcar := ordinaryHostWriteV7_carrier_frame
    hpsi hwidth hle (C e) (C j)
  change q.1.carrier = o.1 /\ q.2.carrier = o.2 at hcar
  rcases hcar with ⟨hqCarrierL, hqCarrierR⟩
  have hrole : forall i, role (D i).carrier = role (C i).carrier := by
    intro i
    by_cases hie : i = e
    · subst i
      exact (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
        role u.carrier) hDe).trans hqLRole
    · by_cases hij : i = j
      · subst i
        exact (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
          role u.carrier) hDj).trans hqRRole
      · exact congrArg
          (fun u : R1AgentStateV6 psi kappa tau => role u.carrier)
          (B9SpliceV8LabelFrame.stepV8_other
            hpsi hwidth hle ring C e i hie
              (by simpa only [j] using hij))
  have hpending : forall i, (D i).carrier.repairPending =
      (C i).carrier.repairPending := by
    intro i
    by_cases hie : i = e
    · subst i
      exact (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
        u.carrier.repairPending) hDe).trans hqLPend
    · by_cases hij : i = j
      · subst i
        exact (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
          u.carrier.repairPending) hDj).trans hqRPend
      · exact congrArg
          (fun u : R1AgentStateV6 psi kappa tau => u.carrier.repairPending)
          (B9SpliceV8LabelFrame.stepV8_other
            hpsi hwidth hle ring C e i hie
              (by simpa only [j] using hij))
  have htOffJ : forall i, i ≠ j ->
      (D i).acquireTicket = (C i).acquireTicket := by
    intro i hij
    by_cases hie : i = e
    · subst i
      exact (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
        u.acquireTicket) hDe).trans (hqLTicket.trans heTicket.symm)
    · exact congrArg
        (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket)
        (B9SpliceV8LabelFrame.stepV8_other
          hpsi hwidth hle ring C e i hie
            (by simpa only [j] using hij))
  have hlabels :=
    B9SpliceV8LabelFrame.ordinaryHostWriteV7_labels_of_no_birth
      hpsi hwidth hle (C e) (C j) hl hrJ hopenJ hbJ
  change
    q.1.carrier.splice.base.core.core.label =
        (C e).carrier.splice.base.core.core.label /\
      q.2.carrier.splice.base.core.core.label =
        ⟨((C e).carrier.splice.base.core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ at hlabels
  have hleftLabel : (D e).carrier.splice.base.core.core.label =
      (C e).carrier.splice.base.core.core.label :=
    (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
      u.carrier.splice.base.core.core.label) hDe).trans hlabels.1
  have haligned : (D j).carrier.splice.base.core.core.label =
      ⟨((D e).carrier.splice.base.core.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
    calc
      (D j).carrier.splice.base.core.core.label =
          q.2.carrier.splice.base.core.core.label :=
        congrArg (fun u : R1AgentStateV6 psi kappa tau =>
          u.carrier.splice.base.core.core.label) hDj
      _ = ⟨((C e).carrier.splice.base.core.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ := hlabels.2
      _ = ⟨((D e).carrier.splice.base.core.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ :=
        congrArg
          (fun a : Fin psi =>
            (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
          hleftLabel.symm
  refine ⟨?_, ?_⟩
  · intro x hdx
    have hd := (danger_iff_physical hpsi ring D x).1 hdx
    by_cases hxe : x = e
    · subst x
      exact (hd.2.2 (by simpa only [j] using haligned)).elim
    by_cases hxj : x = j
    · subst x
      cases hrel : rightFollowerRelabelledV7 (C j).carrier o.2 with
      | false =>
          have hoRole : role o.2 = .none := by
            calc
              role o.2 = role q.2.carrier :=
                (congrArg role hqCarrierR).symm
              _ = role (C j).carrier := hqRRole
              _ = .none := hjRoleJ
          have hoPend : o.2.repairPending = false := by
            calc
              o.2.repairPending = q.2.carrier.repairPending :=
                (congrArg (fun u : R1AgentStateV4 psi kappa tau =>
                  u.repairPending) hqCarrierR).symm
              _ = (C j).carrier.repairPending := hqRPend
              _ = false := hjPendJ
          have hoFollower : o.2.splice.base.core.core.leader = false := by
            calc
              o.2.splice.base.core.core.leader =
                  q.2.carrier.splice.base.core.core.leader :=
                (congrArg (fun u : R1AgentStateV4 psi kappa tau =>
                  u.splice.base.core.core.leader) hqCarrierR).symm
              _ = (D j).carrier.splice.base.core.core.leader :=
                (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
                  u.carrier.splice.base.core.core.leader) hDj).symm
              _ = false := hd.1
          have hoLabel : o.2.splice.base.core.core.label =
              (C j).carrier.splice.base.core.core.label :=
            rightFollowerRelabelledV7_false_label
              (C j).carrier o.2 hrel hoRole hoPend hoFollower
          have hjLabel : (D j).carrier.splice.base.core.core.label =
              (C j).carrier.splice.base.core.core.label := by
            calc
              (D j).carrier.splice.base.core.core.label =
                  q.2.carrier.splice.base.core.core.label :=
                congrArg (fun u : R1AgentStateV6 psi kappa tau =>
                  u.carrier.splice.base.core.core.label) hDj
              _ = o.2.splice.base.core.core.label :=
                congrArg (fun u : R1AgentStateV4 psi kappa tau =>
                  u.splice.base.core.core.label) hqCarrierR
              _ = (C j).carrier.splice.base.core.core.label := hoLabel
          let k := ring.rightNeighbor j
          have hkj : k ≠ j := by
            intro hh
            change ring.rightNeighbor j = j at hh
            have hrn : ring.rightNeighbor j = ring.rightNeighbor e := by
              calc
                ring.rightNeighbor j = j := hh
                _ = ring.rightNeighbor e := rfl
            have hjeq : j = e := rightNeighbor_injective ring hrn
            apply hself
            calc
              ring.rightNeighbor e = j := rfl
              _ = e := hjeq
          have hkLabel : (D k).carrier.splice.base.core.core.label =
              (C k).carrier.splice.base.core.core.label := by
            by_cases hke : k = e
            · simpa only [hke] using hleftLabel
            · exact congrArg
                (fun u : R1AgentStateV6 psi kappa tau =>
                  u.carrier.splice.base.core.core.label)
                (B9SpliceV8LabelFrame.stepV8_other
                  hpsi hwidth hle ring C e k hke
                    (by simpa only [j] using hkj))
          have hkLeader : (C k).carrier.splice.base.core.core.leader = false := by
            by_cases hke : k = e
            · simpa only [hke] using hl
            · have hDk := B9SpliceV8LabelFrame.stepV8_other
                hpsi hwidth hle ring C e k hke
                  (by simpa only [j] using hkj)
              have hDkLeader := congrArg
                (fun u : R1AgentStateV6 psi kappa tau =>
                  u.carrier.splice.base.core.core.leader) hDk
              exact hDkLeader.symm.trans (by simpa only [k] using hd.2.1)
          have hbar : (C k).carrier.splice.base.core.core.label ≠
              ⟨((C j).carrier.splice.base.core.core.label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ := by
            intro hh
            apply hd.2.2
            calc
              (D k).carrier.splice.base.core.core.label =
                  (C k).carrier.splice.base.core.core.label := hkLabel
              _ = ⟨((C j).carrier.splice.base.core.core.label.val + 1) % psi,
                    Nat.mod_lt _ hpsi⟩ := hh
              _ = ⟨((D j).carrier.splice.base.core.core.label.val + 1) % psi,
                    Nat.mod_lt _ hpsi⟩ :=
                congrArg
                  (fun a : Fin psi =>
                    (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
                  hjLabel.symm
          have hold := hsafe.1 j
            ((danger_iff_physical hpsi ring C j).2
              ⟨hrJ, hkLeader, hbar⟩)
          change R1ProtectedSpliceEdgeV3 ring (projectV6 C) j \/
            HostFenceShapeV7 (C j) at hold
          rcases hold with hv3 | hf
          · exact Or.inl
              ((v3Protection_frame ring C D j hrole hpending).2 hv3)
          · have hbad : (false : Bool) = true :=
              hjTicketJ.symm.trans hf.2.2
            cases hbad
      | true =>
          have hqt := ordinaryHostWriteV7_right_ticket_of_relabel
            hpsi hwidth hle (C e) (C j) (by simpa only [o] using hrel)
          change q.2.acquireTicket = true at hqt
          have hDt : (D j).acquireTicket = true :=
            (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
              u.acquireTicket) hDj).trans hqt
          exact Or.inr
            ⟨(hrole j).trans hjRoleJ,
              (hpending j).trans hjPendJ, hDt⟩
    · let y := ring.rightNeighbor x
      have hyj : y ≠ j := by
        intro hh
        apply hxe
        apply rightNeighbor_injective ring
        simpa only [y, j] using hh
      have hDx : D x = C x :=
        B9SpliceV8LabelFrame.stepV8_other
          hpsi hwidth hle ring C e x hxe
            (by simpa only [j] using hxj)
      by_cases hye : y = e
      · have hin : ring.rightNeighbor x = e := by
          simpa only [y] using hye
        have hframe :=
          B9SpliceV8LabelFrame.stepV8_incoming_edge_no_birth_label_frame
            hpsi hwidth hle ring C e x hself hin hxe
              (by simpa only [j] using hxj)
              hrow hl hr hopen hb
        change
          (D x).carrier.splice.base.core.core.label =
              (C x).carrier.splice.base.core.core.label /\
            (D e).carrier.splice.base.core.core.label =
              (C e).carrier.splice.base.core.core.label at hframe
        have hxLeader : (C x).carrier.splice.base.core.core.leader = false := by
          have hxl := congrArg
            (fun u : R1AgentStateV6 psi kappa tau =>
              u.carrier.splice.base.core.core.leader) hDx
          exact hxl.symm.trans hd.1
        have hyLeader :
            (C (ring.rightNeighbor x)).carrier.splice.base.core.core.leader =
              false := by
          rw [hin]
          exact hl
        have hbar :
            (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label ≠
              ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ := by
          rw [hin]
          intro hh
          apply hd.2.2
          have hindex := congrArg
            (fun z : Fin n =>
              (D z).carrier.splice.base.core.core.label) hin
          apply hindex.trans
          calc
            (D e).carrier.splice.base.core.core.label =
                (C e).carrier.splice.base.core.core.label := hframe.2
            _ = ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
                  Nat.mod_lt _ hpsi⟩ := hh
            _ = ⟨((D x).carrier.splice.base.core.core.label.val + 1) % psi,
                  Nat.mod_lt _ hpsi⟩ :=
              congrArg
                (fun a : Fin psi =>
                  (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
                hframe.1.symm
        have hold := hsafe.1 x
          ((danger_iff_physical hpsi ring C x).2
            ⟨hxLeader, hyLeader, hbar⟩)
        change R1ProtectedSpliceEdgeV3 ring (projectV6 C) x \/
          HostFenceShapeV7 (C x) at hold
        rcases hold with hv3 | hf
        · exact Or.inl
            ((v3Protection_frame ring C D x hrole hpending).2 hv3)
        · exact Or.inr (cast (congrArg HostFenceShapeV7 hDx.symm) hf)
      · have hDy : D y = C y :=
          B9SpliceV8LabelFrame.stepV8_other
            hpsi hwidth hle ring C e y hye
              (by simpa only [j] using hyj)
        have hL : (D x).carrier = (C x).carrier :=
          congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier) hDx
        have hR : (D (ring.rightNeighbor x)).carrier =
            (C (ring.rightNeighbor x)).carrier := by
          simpa only [y] using
            congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier) hDy
        have hd0 :=
          (danger_congr_carrier_at hpsi ring C D x hL hR).1 hdx
        have hold := hsafe.1 x hd0
        exact
          (B9SpliceV8LabelFrame.stepV8_disjoint_protection_iff
            hpsi hwidth hle ring C e x hxe
              (by simpa only [j] using hxj)
              (by simpa only [y] using hye)
              (by simpa only [y, j] using hyj)).2 hold
  · refine ⟨?_, ?_⟩
    · intro i
      unfold TicketShapeV7
      intro ht
      by_cases hij : i = j
      · subst i
        exact Or.inr
          ⟨(hrole j).trans hjRoleJ,
            (hpending j).trans hjPendJ, ht⟩
      · have htC : (C i).acquireTicket = true :=
          (htOffJ i hij).symm.trans ht
        rcases hsafe.2.1 i htC with hres | hf
        · left
          unfold ReservedFrontHoldGuard at hres ⊢
          exact ⟨(hrole i).trans hres.1,
            (hpending i).trans hres.2⟩
        · right
          unfold HostFenceShapeV7 at hf ⊢
          exact ⟨(hrole i).trans hf.1,
            (hpending i).trans hf.2.1, ht⟩
    · intro i hri hpi
      have hriC : role (C i).carrier = .predecessorArmed :=
        (hrole i).symm.trans hri
      have hpiC : (C i).carrier.repairPending = true :=
        (hpending i).symm.trans hpi
      have hold := hsafe.2.2 i hriC hpiC
      let y := ring.rightNeighbor i
      have hres : ReservedFrontHoldGuard (C y).carrier := by
        simpa only [y] using hold.1
      have hyTicketC : (C y).acquireTicket = false := by
        simpa only [y] using hold.2
      have hyJ : y ≠ j := by
        intro hy
        have hfrontJ : role (C j).carrier = .front := by
          unfold ReservedFrontHoldGuard at hres
          simpa only [hy] using hres.1
        have hbad : SpliceRole.none = SpliceRole.front :=
          hjRoleJ.symm.trans hfrontJ
        cases hbad
      constructor
      · unfold ReservedFrontHoldGuard at hres ⊢
        exact ⟨(hrole y).trans hres.1,
          (hpending y).trans hres.2⟩
      · have ht := (htOffJ y hyJ).trans hyTicketC
        simpa only [y] using ht


/-- Exact physical-birth branch still to compose with the controller frame. -/
def OrdinaryBirthBranchStatement
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
    SpliceSafeV7 hpsi ring C ->
    OrdinaryNeutralPairV8 (C e) (C (ring.rightNeighbor e)) ->
    rowV8 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
      ordinaryHostWriteV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) ->
    BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base
      (C (ring.rightNeighbor e)).carrier.splice.base = true ->
    SpliceSafeV7 hpsi ring (stepV8 hpsi hwidth hle ring C e)


/-- Exact two deletion-priority choices inside the physical host. -/
def OrdinaryDeletionPriorityBranchStatement
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
    SpliceSafeV7 hpsi ring C ->
    OrdinaryNeutralPairV8 (C e) (C (ring.rightNeighbor e)) ->
    rowV8 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
      ordinaryHostWriteV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) ->
    (let l := (C e).carrier.splice.base
     let r := (C (ring.rightNeighbor e)).carrier.splice.base
     let pl := prepareExpiringDisposal hpsi l
     let pr := prepareExpiringDisposal hpsi r
     let l0 := normalizeDeletion pl.core.erase
     let r0 := normalizeDeletion pr.core.erase
     deletionActive r0 = true \/
       (deletionActive r0 = false /\ deletionActive l0 = true)) ->
    SpliceSafeV7 hpsi ring (stepV8 hpsi hwidth hle ring C e)


end B9SpliceV8OrdinaryHost


#print axioms B9SpliceV8OrdinaryHost.ordinary_no_birth_preserves_spliceSafeV7

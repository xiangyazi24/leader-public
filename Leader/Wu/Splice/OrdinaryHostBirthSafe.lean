import Leader.Wu.Splice.OrdinaryHostDeletionSafe


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceV8BirthCase


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceV8LabelFrame
open B9SpliceV8OrdinaryHost


variable {n psi width kappa tau : Nat}


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
    PreparedDangerAt hpsi ring (projectV6 C) x <->
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


private theorem danger_back (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (hback : forall i,
      (D i).carrier.splice.base.core.core.leader = false ->
      (C i).carrier.splice.base.core.core.leader = false /\
      (D i).carrier.splice.base.core.core.label =
        (C i).carrier.splice.base.core.core.label)
    (hd : PreparedDangerAt hpsi ring (projectV6 D) x) :
    PreparedDangerAt hpsi ring (projectV6 C) x := by
  rcases (danger_iff_physical hpsi ring D x).1 hd with ⟨hl, hr, hb⟩
  rcases hback x hl with ⟨hl0, hll⟩
  rcases hback (ring.rightNeighbor x) hr with ⟨hr0, hlr⟩
  apply (danger_iff_physical hpsi ring C x).2
  refine ⟨hl0, hr0, ?_⟩
  intro heq
  apply hb
  calc
    (D (ring.rightNeighbor x)).carrier.splice.base.core.core.label =
        (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label := hlr
    _ = ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := heq
    _ = ⟨((D x).carrier.splice.base.core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ :=
      congrArg (fun a : Fin psi =>
        (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi)) hll.symm


private theorem rightNeighbor_injective_local
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


theorem ordinary_birth_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (hleft : forall (l r : R1AgentStateV6 psi kappa tau),
      OrdinaryNeutralPairV8 l r ->
      rowV8 hpsi hwidth hle l r = ordinaryHostWriteV7 hpsi hwidth hle l r ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle
        l.carrier.splice.base r.carrier.splice.base).1.core.core.leader = false ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle
        l.carrier.splice.base r.carrier.splice.base).1.core.core.label =
        l.carrier.splice.base.core.core.label) :
    OrdinaryBirthBranchStatement (kappa := kappa) (tau := tau)
      hpsi hwidth hle ring := by
  unfold OrdinaryBirthBranchStatement
  intro C e hsafe hneutral hrow hb
  by_cases hself : ring.rightNeighbor e = e
  · simpa [stepV8, hself] using hsafe
  let j := ring.rightNeighbor e
  let D := stepV8 hpsi hwidth hle ring C e
  let o := ordinaryRow hpsi hwidth hle (C e).carrier (C j).carrier
  let q := ordinaryHostWriteV7 hpsi hwidth hle (C e) (C j)
  have hneutralJ : OrdinaryNeutralPairV8 (C e) (C j) := by
    simpa only [j] using hneutral
  have hrowJ : rowV8 hpsi hwidth hle (C e) (C j) = q := by
    simpa only [j, q] using hrow
  have hbJ : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C j).carrier.splice.base = true := by
    simpa only [j] using hb
  rcases hneutralJ with ⟨heRole, hePend, heTicket, hjRole, hjPend, hjTicket⟩
  have hDe : D e = q.1 := by simp [D, j, q, stepV8, hself, hrow]
  have hDj : D j = q.2 := by simp [D, j, q, stepV8, hself, hrow]
  have hctrl : role q.1.carrier = role (C e).carrier /\
      q.1.carrier.repairPending = (C e).carrier.repairPending /\
      q.1.acquireTicket = false /\ role q.2.carrier = role (C j).carrier /\
      q.2.carrier.repairPending = (C j).carrier.repairPending := by
    unfold q ordinaryHostWriteV7
    dsimp only
    split <;>
      simp [ordinaryRow, withCarrierClearTicketV6, setTicketV6, setPhysical, role]
  rcases hctrl with ⟨hqLRole, hqLPend, hqLTicket, hqRRole, hqRPend⟩
  have hnoDel : ¬ LeftDeletionCandidate hpsi hwidth hle
      (C e).carrier.splice (C j).carrier.splice := by
    intro hd
    have hstale : ¬ RightStalePredecessorHoldGuardV8 (C e) (C j) := by
      intro hs
      exact (show SpliceRole.none ≠ SpliceRole.predecessorArmed by decide)
        (hjRole.symm.trans hs.2.2.2.1)
    have hfL : ¬ HostFenceShapeV7 (C e) := fun hf =>
      (show (false : Bool) ≠ true by decide) (heTicket.symm.trans hf.2.2)
    have hfR : ¬ HostFenceShapeV7 (C j) := fun hf =>
      (show (false : Bool) ≠ true by decide) (hjTicket.symm.trans hf.2.2)
    have hacq : ¬ MoveAcquireFrontGuardV6 hpsi (C e) (C j) := by
      intro ha
      exact (show SpliceRole.none ≠ SpliceRole.front by decide)
        (heRole.symm.trans ha.1.1)
    have harm : ArmAGuard hpsi hwidth hle (C e).carrier (C j).carrier :=
      ⟨heRole, hjRole, hePend, hjPend, hd⟩
    have hv : role (rowV8 hpsi hwidth hle (C e) (C j)).1.carrier =
        .victimArmed := by
      unfold rowV8
      rw [if_neg hstale]
      unfold rowV7
      rw [if_neg hfL, if_neg hfR, if_neg hacq, if_pos harm]
      rfl
    have heq := congrArg
      (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau =>
        role z.1.carrier) hrowJ
    have hn : role q.1.carrier = .none := hqLRole.trans heRole
    exact (show SpliceRole.victimArmed ≠ SpliceRole.none by decide)
      (hv.symm.trans (heq.trans hn))
  have hcar : q.1.carrier = o.1 /\ q.2.carrier = o.2 := by
    unfold q ordinaryHostWriteV7
    dsimp only
    split <;> exact ⟨rfl, rfl⟩
  have hbaseL := congrArg
    (fun u : R1AgentStateV4 psi kappa tau => u.splice.base) hcar.1
  have hbaseR := congrArg
    (fun u : R1AgentStateV4 psi kappa tau => u.splice.base) hcar.2
  change q.1.carrier.splice.base =
    (BirthShortDoneTerminalHost.row hpsi hwidth hle
      (C e).carrier.splice.base (C j).carrier.splice.base).1 at hbaseL
  change q.2.carrier.splice.base =
    (BirthShortDoneTerminalHost.row hpsi hwidth hle
      (C e).carrier.splice.base (C j).carrier.splice.base).2 at hbaseR
  have hleftBackLabel :
      (D e).carrier.splice.base.core.core.leader = false ->
      (C e).carrier.splice.base.core.core.leader = false /\
      (D e).carrier.splice.base.core.core.label =
        (C e).carrier.splice.base.core.core.label := by
    intro hout
    have hqf := (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
      u.carrier.splice.base.core.core.leader) hDe).symm.trans hout
    have hrf := (congrArg
      (fun u : ExpiringAgentState psi kappa tau => u.core.core.leader)
      hbaseL).symm.trans hqf
    have hold : (C e).carrier.splice.base.core.core.leader = false := by
      cases hl0 : (C e).carrier.splice.base.core.core.leader with
      | false => rfl
      | true => exact (hnoDel ⟨hl0, hrf⟩).elim
    have hlab := hleft (C e) (C j)
      ⟨heRole, hePend, heTicket, hjRole, hjPend, hjTicket⟩ hrowJ hrf
    exact ⟨hold, by
      calc
        (D e).carrier.splice.base.core.core.label =
            q.1.carrier.splice.base.core.core.label :=
          congrArg (fun u : R1AgentStateV6 psi kappa tau =>
            u.carrier.splice.base.core.core.label) hDe
        _ = (BirthShortDoneTerminalHost.row hpsi hwidth hle
              (C e).carrier.splice.base (C j).carrier.splice.base).1.core.core.label :=
          congrArg (fun u : ExpiringAgentState psi kappa tau => u.core.core.label) hbaseL
        _ = (C e).carrier.splice.base.core.core.label := hlab⟩
  have hrightBack : q.2.carrier.splice.base.core.core.leader = false ->
      (C j).carrier.splice.base.core.core.leader = false := by
    intro hout
    have hrf := (congrArg
      (fun u : ExpiringAgentState psi kappa tau => u.core.core.leader)
      hbaseR).symm.trans hout
    cases hr0 : (C j).carrier.splice.base.core.core.leader with
    | false => rfl
    | true =>
        have hs := B9LeaderLossCensus.host_right_existing_leader_survives
          hpsi hwidth hle (C e).carrier.splice.base (C j).carrier.splice.base hr0
        exact ((show (true : Bool) ≠ false by decide) (hs.symm.trans hrf)).elim
  have hrole : forall i, role (D i).carrier = role (C i).carrier := by
    intro i
    by_cases hie : i = e
    · subst i; exact (congrArg
        (fun u : R1AgentStateV6 psi kappa tau => role u.carrier) hDe).trans hqLRole
    · by_cases hij : i = j
      · subst i; exact (congrArg
          (fun u : R1AgentStateV6 psi kappa tau => role u.carrier) hDj).trans hqRRole
      · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => role u.carrier)
          (stepV8_other hpsi hwidth hle ring C e i hie
            (by simpa only [j] using hij))
  have hpending : forall i, (D i).carrier.repairPending =
      (C i).carrier.repairPending := by
    intro i
    by_cases hie : i = e
    · subst i; exact (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
        u.carrier.repairPending) hDe).trans hqLPend
    · by_cases hij : i = j
      · subst i; exact (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
          u.carrier.repairPending) hDj).trans hqRPend
      · exact congrArg (fun u : R1AgentStateV6 psi kappa tau =>
          u.carrier.repairPending)
          (stepV8_other hpsi hwidth hle ring C e i hie
            (by simpa only [j] using hij))
  have htOffJ : forall i, i ≠ j ->
      (D i).acquireTicket = (C i).acquireTicket := by
    intro i hij
    by_cases hie : i = e
    · subst i
      exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket)
        hDe).trans (hqLTicket.trans heTicket.symm)
    · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket)
        (stepV8_other hpsi hwidth hle ring C e i hie
          (by simpa only [j] using hij))
  have hprot : forall x,
      R1ProtectedSpliceEdgeV3 ring (projectV6 D) x <->
        R1ProtectedSpliceEdgeV3 ring (projectV6 C) x := by
    intro x
    unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard projectV6
    dsimp only
    simp only [hrole x, hpending x, hrole (ring.rightNeighbor x),
      hpending (ring.rightNeighbor x)]
  have hrightLabelNoRel : rightFollowerRelabelledV7 (C j).carrier o.2 = false ->
      (D j).carrier.splice.base.core.core.leader = false ->
      (C j).carrier.splice.base.core.core.leader = false /\
      (D j).carrier.splice.base.core.core.label =
        (C j).carrier.splice.base.core.core.label := by
    intro hrel hout
    have hqf := (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
      u.carrier.splice.base.core.core.leader) hDj).symm.trans hout
    have hold := hrightBack hqf
    have hoRole : role o.2 = .none :=
      (congrArg role hcar.2).symm.trans (hqRRole.trans hjRole)
    have hoPend : o.2.repairPending = false :=
      (congrArg (fun u : R1AgentStateV4 psi kappa tau => u.repairPending)
        hcar.2).symm.trans (hqRPend.trans hjPend)
    have hoFollower : o.2.splice.base.core.core.leader = false :=
      (congrArg (fun u : R1AgentStateV4 psi kappa tau =>
        u.splice.base.core.core.leader) hcar.2).symm.trans hqf
    have hoLabel : o.2.splice.base.core.core.label =
        (C j).carrier.splice.base.core.core.label := by
      by_cases heq : o.2.splice.base.core.core.label =
          (C j).carrier.splice.base.core.core.label
      · exact heq
      · have ht : rightFollowerRelabelledV7 (C j).carrier o.2 = true := by
          simp [rightFollowerRelabelledV7, hoRole, hoPend, hoFollower, heq]
        exact ((show (false : Bool) ≠ true by decide) (hrel.symm.trans ht)).elim
    exact ⟨hold, by
      calc
        (D j).carrier.splice.base.core.core.label =
            q.2.carrier.splice.base.core.core.label :=
          congrArg (fun u : R1AgentStateV6 psi kappa tau =>
            u.carrier.splice.base.core.core.label) hDj
        _ = o.2.splice.base.core.core.label :=
          congrArg (fun u : R1AgentStateV4 psi kappa tau =>
            u.splice.base.core.core.label) hcar.2
        _ = (C j).carrier.splice.base.core.core.label := hoLabel⟩
  have hbackNoRel : rightFollowerRelabelledV7 (C j).carrier o.2 = false ->
      forall i, (D i).carrier.splice.base.core.core.leader = false ->
        (C i).carrier.splice.base.core.core.leader = false /\
        (D i).carrier.splice.base.core.core.label =
          (C i).carrier.splice.base.core.core.label := by
    intro hrel i hi
    by_cases hie : i = e
    · subst i; exact hleftBackLabel hi
    · by_cases hij : i = j
      · subst i; exact hrightLabelNoRel hrel hi
      · have hx := stepV8_other hpsi hwidth hle ring C e i hie
          (by simpa only [j] using hij)
        exact ⟨(congrArg (fun u : R1AgentStateV6 psi kappa tau =>
          u.carrier.splice.base.core.core.leader) hx).symm.trans hi,
          congrArg (fun u : R1AgentStateV6 psi kappa tau =>
            u.carrier.splice.base.core.core.label) hx⟩
  have hbirth := BirthShortDoneTerminalBirthPhysical.birthEvent_true_row_has_physical_leader
    hpsi hwidth hle (C e).carrier.splice.base (C j).carrier.splice.base hbJ
  have hbirthD : (D e).carrier.splice.base.core.core.leader = true \/
      (D j).carrier.splice.base.core.core.leader = true := by
    rcases hbirth with hL | hR
    · left
      calc
        (D e).carrier.splice.base.core.core.leader =
            q.1.carrier.splice.base.core.core.leader :=
          congrArg (fun u : R1AgentStateV6 psi kappa tau =>
            u.carrier.splice.base.core.core.leader) hDe
        _ = (BirthShortDoneTerminalHost.row hpsi hwidth hle
              (C e).carrier.splice.base (C j).carrier.splice.base).1.core.core.leader :=
          congrArg (fun u : ExpiringAgentState psi kappa tau => u.core.core.leader) hbaseL
        _ = true := hL
    · right
      calc
        (D j).carrier.splice.base.core.core.leader =
            q.2.carrier.splice.base.core.core.leader :=
          congrArg (fun u : R1AgentStateV6 psi kappa tau =>
            u.carrier.splice.base.core.core.leader) hDj
        _ = (BirthShortDoneTerminalHost.row hpsi hwidth hle
              (C e).carrier.splice.base (C j).carrier.splice.base).2.core.core.leader :=
          congrArg (fun u : ExpiringAgentState psi kappa tau => u.core.core.leader) hbaseR
        _ = true := hR
  have hprotectOff : forall x, x ≠ e -> x ≠ j ->
      ProtectedSpliceEdgeV7 ring C x -> ProtectedSpliceEdgeV7 ring D x := by
    intro x hxe hxj hold
    rcases hold with hv3 | hf
    · exact Or.inl ((hprot x).2 hv3)
    · have hx := stepV8_other hpsi hwidth hle ring C e x hxe
        (by simpa only [j] using hxj)
      exact Or.inr (cast (congrArg HostFenceShapeV7 hx.symm) hf)
  have hDangerE : PreparedDangerAt hpsi ring (projectV6 D) e ->
      ProtectedSpliceEdgeV7 ring D e := by
    intro hd
    rcases (danger_iff_physical hpsi ring D e).1 hd with ⟨hfL, hfR, _⟩
    rcases hbirthD with hL | hR
    · exact (show (true : Bool) ≠ false by decide) (hL.symm.trans hfL) |>.elim
    · have hR0 : (D j).carrier.splice.base.core.core.leader = false := by
        simpa only [j] using hfR
      exact (show (true : Bool) ≠ false by decide) (hR.symm.trans hR0) |>.elim
  have hDangerJ : PreparedDangerAt hpsi ring (projectV6 D) j ->
      ProtectedSpliceEdgeV7 ring D j := by
    intro hd
    have hfJ := ((danger_iff_physical hpsi ring D j).1 hd).1
    rcases hbirthD with hL | hR
    · cases hrel : rightFollowerRelabelledV7 (C j).carrier o.2 with
      | false =>
          have hd0 := danger_back hpsi ring C D j (hbackNoRel hrel) hd
          rcases hsafe.1 j hd0 with hv3 | hf
          · exact Or.inl ((hprot j).2 hv3)
          · exact (show (false : Bool) ≠ true by decide)
              (hjTicket.symm.trans hf.2.2) |>.elim
      | true =>
          have hqt : q.2.acquireTicket = true := by
            unfold q ordinaryHostWriteV7
            dsimp only
            rw [show rightFollowerRelabelledV7 (C j).carrier
              (ordinaryRow hpsi hwidth hle (C e).carrier (C j).carrier).2 = true by
                simpa only [o] using hrel]
            rfl
          have hDt : (D j).acquireTicket = true :=
            (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket)
              hDj).trans hqt
          exact Or.inr ⟨(hrole j).trans hjRole,
            (hpending j).trans hjPend, hDt⟩
    · exact (show (true : Bool) ≠ false by decide) (hR.symm.trans hfJ) |>.elim
  have hDangerIncoming : forall x, x ≠ e -> x ≠ j ->
      ring.rightNeighbor x = e -> PreparedDangerAt hpsi ring (projectV6 D) x ->
      ProtectedSpliceEdgeV7 ring D x := by
    intro x hxe hxj hin hd
    have hfE : (D e).carrier.splice.base.core.core.leader = false := by
      have hh := ((danger_iff_physical hpsi ring D x).1 hd).2.1
      simpa only [hin] using hh
    rcases hbirthD with hL | hR
    · exact (show (true : Bool) ≠ false by decide) (hL.symm.trans hfE) |>.elim
    · cases hrel : rightFollowerRelabelledV7 (C j).carrier o.2 with
      | false =>
          exact hprotectOff x hxe hxj
            (hsafe.1 x (danger_back hpsi ring C D x (hbackNoRel hrel) hd))
      | true =>
          have ht : role o.2 = .none /\ o.2.repairPending = false /\
              o.2.splice.base.core.core.leader = false /\
              o.2.splice.base.core.core.label ≠
                (C j).carrier.splice.base.core.core.label := by
            simpa [rightFollowerRelabelledV7] using hrel
          have hDf : (D j).carrier.splice.base.core.core.leader = false := by
            calc
              (D j).carrier.splice.base.core.core.leader =
                  q.2.carrier.splice.base.core.core.leader :=
                congrArg (fun u : R1AgentStateV6 psi kappa tau =>
                  u.carrier.splice.base.core.core.leader) hDj
              _ = o.2.splice.base.core.core.leader :=
                congrArg (fun u : R1AgentStateV4 psi kappa tau =>
                  u.splice.base.core.core.leader) hcar.2
              _ = false := ht.2.2.1
          exact (show (true : Bool) ≠ false by decide) (hR.symm.trans hDf) |>.elim
  have hDangerDisjoint : forall x, x ≠ e -> x ≠ j ->
      ring.rightNeighbor x ≠ e -> PreparedDangerAt hpsi ring (projectV6 D) x ->
      ProtectedSpliceEdgeV7 ring D x := by
    intro x hxe hxj hye hd
    have hyj : ring.rightNeighbor x ≠ j := by
      intro hh
      apply hxe
      apply rightNeighbor_injective_local ring
      simpa only [j] using hh
    have hDx := stepV8_other hpsi hwidth hle ring C e x hxe
      (by simpa only [j] using hxj)
    have hDy := stepV8_other hpsi hwidth hle ring C e
      (ring.rightNeighbor x) hye hyj
    have hd0 : PreparedDangerAt hpsi ring (projectV6 C) x := by
      unfold PreparedDangerAt PreparedBarrierAt projectV6 projectSpliceConfig at hd ⊢
      dsimp only at hd ⊢
      rw [show D x = C x from hDx,
        show D (ring.rightNeighbor x) = C (ring.rightNeighbor x) from hDy] at hd
      exact hd
    exact (stepV8_disjoint_protection_iff hpsi hwidth hle ring C e x
      hxe (by simpa only [j] using hxj) hye hyj).2 (hsafe.1 x hd0)
  refine ⟨?_, ?_⟩
  · intro x hd
    by_cases hxe : x = e
    · subst x; exact hDangerE hd
    · by_cases hxj : x = j
      · subst x; exact hDangerJ hd
      · by_cases hin : ring.rightNeighbor x = e
        · exact hDangerIncoming x hxe hxj hin hd
        · exact hDangerDisjoint x hxe hxj hin hd
  · refine ⟨?_, ?_⟩
    · intro i
      unfold TicketShapeV7
      intro ht
      by_cases hij : i = j
      · subst i
        exact Or.inr ⟨(hrole j).trans hjRole,
          (hpending j).trans hjPend, ht⟩
      · have htC : (C i).acquireTicket = true := (htOffJ i hij).symm.trans ht
        rcases hsafe.2.1 i htC with hres | hf
        · left
          unfold ReservedFrontHoldGuard at hres ⊢
          exact ⟨(hrole i).trans hres.1, (hpending i).trans hres.2⟩
        · right
          unfold HostFenceShapeV7 at hf ⊢
          exact ⟨(hrole i).trans hf.1, (hpending i).trans hf.2.1, ht⟩
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
        exact (show SpliceRole.none ≠ SpliceRole.front by decide)
          (hjRole.symm.trans hfrontJ)
      constructor
      · unfold ReservedFrontHoldGuard at hres ⊢
        exact ⟨(hrole y).trans hres.1, (hpending y).trans hres.2⟩
      · have ht := (htOffJ y hyJ).trans hyTicketC
        simpa only [y] using ht


end B9SpliceV8BirthCase


#print axioms B9SpliceV8BirthCase.ordinary_birth_preserves_spliceSafeV7

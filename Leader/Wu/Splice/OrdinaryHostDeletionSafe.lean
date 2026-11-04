import Leader.Wu.Splice.OrdinaryHostNoBirthSafe
import Leader.Wu.Splice.LeaderLossCensus

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV8DeletionCase

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

private theorem preparedSplice_leader_local (hpsi : 0 < psi)
    (u : SpliceAgentState psi kappa tau) :
    (prepared hpsi u).core.leader = u.base.core.core.leader := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.base.core]
  rw [normalizeDeletion_leader_local, prepareDisposal_leader_local]
  rfl

private theorem preparedSplice_label_local (hpsi : 0 < psi)
    (u : SpliceAgentState psi kappa tau) :
    (prepared hpsi u).core.label = u.base.core.core.label := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.base.core]
  rw [normalizeDeletion_label_local, prepareDisposal_label_local]
  rfl

private theorem preparedR1_leader_local (hpsi : 0 < psi)
    (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.leader = u.splice.base.core.core.leader := by
  simpa [preparedR1] using preparedSplice_leader_local hpsi u.splice

private theorem danger_back (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (hback : forall i,
      (D i).carrier.splice.base.core.core.leader = false ->
      (C i).carrier.splice.base.core.core.leader = false /\
      (D i).carrier.splice.base.core.core.label =
        (C i).carrier.splice.base.core.core.label)
    (h : PreparedDangerAt hpsi ring (projectV6 D) x) :
    PreparedDangerAt hpsi ring (projectV6 C) x := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6 projectSpliceConfig at h ⊢
  dsimp only at h ⊢
  unfold isBarrier at h ⊢
  have hdL := (preparedR1_leader_local hpsi (D x).carrier).symm.trans h.1
  have hdR := (preparedSplice_leader_local hpsi
    (D (ring.rightNeighbor x)).carrier.splice).symm.trans h.2.1
  rcases hback x hdL with ⟨hcL, hlabelL⟩
  rcases hback (ring.rightNeighbor x) hdR with ⟨hcR, hlabelR⟩
  refine ⟨(preparedR1_leader_local hpsi (C x).carrier).trans hcL,
    (preparedSplice_leader_local hpsi
      (C (ring.rightNeighbor x)).carrier.splice).trans hcR, ?_⟩
  intro heq
  apply h.2.2
  calc
    (prepared hpsi (D (ring.rightNeighbor x)).carrier.splice).core.label =
        (D (ring.rightNeighbor x)).carrier.splice.base.core.core.label :=
      preparedSplice_label_local hpsi (D (ring.rightNeighbor x)).carrier.splice
    _ = (C (ring.rightNeighbor x)).carrier.splice.base.core.core.label := hlabelR
    _ = (prepared hpsi (C (ring.rightNeighbor x)).carrier.splice).core.label :=
      (preparedSplice_label_local hpsi
        (C (ring.rightNeighbor x)).carrier.splice).symm
    _ = ⟨(((prepared hpsi (C x).carrier.splice).core.label).val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := heq
    _ = ⟨((C x).carrier.splice.base.core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ :=
      congrArg (fun a : Fin psi =>
        (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
        (preparedSplice_label_local hpsi (C x).carrier.splice)
    _ = ⟨((D x).carrier.splice.base.core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ :=
      congrArg (fun a : Fin psi =>
        (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi)) hlabelL.symm
    _ = ⟨(((prepared hpsi (D x).carrier.splice).core.label).val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ :=
      congrArg (fun a : Fin psi =>
        (⟨(a.val + 1) % psi, Nat.mod_lt _ hpsi⟩ : Fin psi))
        (preparedSplice_label_local hpsi (D x).carrier.splice).symm

private theorem ordinary_controller_frame
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
    simp [ordinaryRow, withCarrierClearTicketV6, setTicketV6, setPhysical, role]

private theorem ordinary_carrier_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    let o := ordinaryRow hpsi hwidth hle l.carrier r.carrier
    let q := ordinaryHostWriteV7 hpsi hwidth hle l r
    q.1.carrier = o.1 /\ q.2.carrier = o.2 := by
  unfold ordinaryHostWriteV7
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

private theorem deletion_entry_leaders
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hdel :
      deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true \/
      (deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = false /\
       deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase) = true)) :
    let q := BirthShortDoneTerminalHost.doneMetadataEntryWidth hpsi hwidth hle l r
    q.1.core.core.leader = l.core.core.leader /\
      q.2.core.core.leader = r.core.core.leader := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let q := BirthShortDoneTerminalHost.doneMetadataEntryWidth hpsi hwidth hle l r
  have hauth :
      K2BirthDispatcher.authSignalPair
          (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
            hpsi hwidth hle kappa pl.core.erase pr.core.erase) =
        K2BirthDispatcher.authSignalPair (pl.core.erase, pr.core.erase) := by
    rcases hdel with hr | ⟨hr, hl⟩
    · have hr0 : deletionActive (normalizeDeletion pr.core.erase) = true := by
        simpa only [pr] using hr
      unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
      dsimp only
      rw [hr0]
      exact (K2BirthDispatcher.eliminate_signal hpsi
        (normalizeDeletion pl.core.erase) (normalizeDeletion pr.core.erase)).trans
        (K2BirthDispatcher.normalize_pair_signal pl.core.erase pr.core.erase)
    · have hr0 : deletionActive (normalizeDeletion pr.core.erase) = false := by
        simpa only [pr] using hr
      have hl0 : deletionActive (normalizeDeletion pl.core.erase) = true := by
        simpa only [pl] using hl
      unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
      dsimp only
      rw [hr0, hl0]
      exact K2BirthDispatcher.normalize_pair_signal pl.core.erase pr.core.erase
  have hentry := BirthShortDoneTerminalConsumer.doneMetadataEntryWidth_observation
    hpsi hwidth hle l r
  have hsignal :
      (ExpiringK2Projection.observeCell q.1,
        ExpiringK2Projection.observeCell q.2) =
      (ExpiringK2Projection.observeCell l,
        ExpiringK2Projection.observeCell r) := by
    calc
      (ExpiringK2Projection.observeCell q.1,
          ExpiringK2Projection.observeCell q.2) =
          K2BirthDispatcher.authSignalPair
            (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
              hpsi hwidth hle kappa pl.core.erase pr.core.erase) := by
        simpa only [q, pl, pr] using hentry
      _ = K2BirthDispatcher.authSignalPair (pl.core.erase, pr.core.erase) := hauth
      _ = (ExpiringK2Projection.observeCell pl,
          ExpiringK2Projection.observeCell pr) := rfl
      _ = (ExpiringK2Projection.observeCell l,
          ExpiringK2Projection.observeCell r) :=
        Prod.ext (K2BirthDispatcher.prepareExpiring_signal hpsi l)
          (K2BirthDispatcher.prepareExpiring_signal hpsi r)
  have hL := congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) hsignal
  have hR := congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) hsignal
  change q.1.core.core.leader = l.core.core.leader at hL
  change q.2.core.core.leader = r.core.core.leader at hR
  exact ⟨hL, hR⟩

private theorem deletion_old_follower_labels
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hdel :
      deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true \/
      (deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = false /\
       deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase) = true)) :
    (l.core.core.leader = false ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.label =
        l.core.core.label) /\
    (r.core.core.leader = false ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.label =
        r.core.core.label) := by
  let d := BirthShortDoneTerminalHost.doneMetadataEntryWidth hpsi hwidth hle l r
  have hleaders := deletion_entry_leaders hpsi hwidth hle l r hdel
  change d.1.core.core.leader = l.core.core.leader /\
    d.2.core.core.leader = r.core.core.leader at hleaders
  have hlabels : d.1.core.core.label = l.core.core.label /\
      d.2.core.core.label = r.core.core.label := by
    rcases hdel with hr | ⟨hr, hl⟩
    · exact B9SpliceV8LabelFrame.host_responder_deletion_label_frame
        hpsi hwidth hle l r hr
    · exact B9SpliceV8LabelFrame.host_initiator_deletion_label_frame
        hpsi hwidth hle l r hr hl
  have hrow := B9SpliceV8LabelFrame.hostRow_labels_metadata hpsi hwidth hle l r
  constructor
  · intro hl
    calc
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.label =
          (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1.core.core.label := hrow.1
      _ = d.1.core.core.label := by
        change (K2BirthLeaderNormalize.normalizeLeader hpsi d.1).core.core.label =
          d.1.core.core.label
        simp [K2BirthLeaderNormalize.normalizeLeader, hleaders.1.trans hl]
      _ = l.core.core.label := hlabels.1
  · intro hr
    calc
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.label =
          (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2.core.core.label := hrow.2
      _ = d.2.core.core.label := by
        change (K2BirthLeaderNormalize.normalizeLeader hpsi d.2).core.core.label =
          d.2.core.core.label
        simp [K2BirthLeaderNormalize.normalizeLeader, hleaders.2.trans hr]
      _ = r.core.core.label := hlabels.2

theorem ordinary_deletion_priority_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    OrdinaryDeletionPriorityBranchStatement (kappa := kappa) (tau := tau) hpsi hwidth hle ring := by
  unfold OrdinaryDeletionPriorityBranchStatement
  intro C e hsafe hneutral hrow hdel
  by_cases hself : ring.rightNeighbor e = e
  · simpa [stepV8, hself] using hsafe
  let j := ring.rightNeighbor e
  let D := stepV8 hpsi hwidth hle ring C e
  let o := ordinaryRow hpsi hwidth hle (C e).carrier (C j).carrier
  let q := ordinaryHostWriteV7 hpsi hwidth hle (C e) (C j)
  rcases hneutral with ⟨heRole, hePend, heTicket, hjRole, hjPend, hjTicket⟩
  have hjRoleJ : role (C j).carrier = .none := by simpa only [j] using hjRole
  have hjPendJ : (C j).carrier.repairPending = false := by simpa only [j] using hjPend
  have hjTicketJ : (C j).acquireTicket = false := by simpa only [j] using hjTicket
  dsimp only at hdel
  have hdelJ :
      deletionActive (normalizeDeletion
        (prepareExpiringDisposal hpsi (C j).carrier.splice.base).core.erase) = true \/
      (deletionActive (normalizeDeletion
        (prepareExpiringDisposal hpsi (C j).carrier.splice.base).core.erase) = false /\
       deletionActive (normalizeDeletion
        (prepareExpiringDisposal hpsi (C e).carrier.splice.base).core.erase) = true) := by
    simpa only [j] using hdel
  have hrowJ : rowV8 hpsi hwidth hle (C e) (C j) = q := by
    simpa only [j, q] using hrow
  have hDe : D e = q.1 := by simp [D, j, q, stepV8, hself, hrow]
  have hDj : D j = q.2 := by simp [D, j, q, stepV8, hself, hrow]
  have hctrl := ordinary_controller_frame hpsi hwidth hle (C e) (C j)
  change role q.1.carrier = role (C e).carrier /\
      q.1.carrier.repairPending = (C e).carrier.repairPending /\
      q.1.acquireTicket = false /\ role q.2.carrier = role (C j).carrier /\
      q.2.carrier.repairPending = (C j).carrier.repairPending at hctrl
  rcases hctrl with ⟨hqLRole, hqLPend, hqLTicket, hqRRole, hqRPend⟩
  have hnoDel : ¬ LeftDeletionCandidate hpsi hwidth hle
      (C e).carrier.splice (C j).carrier.splice := by
    intro hd
    have hstale : ¬ RightStalePredecessorHoldGuardV8 (C e) (C j) := by
      intro hs
      have hb : SpliceRole.none = SpliceRole.predecessorArmed :=
        hjRoleJ.symm.trans hs.2.2.2.1
      cases hb
    have hfL : ¬ HostFenceShapeV7 (C e) := by
      intro hf
      have hb : (false : Bool) = true := heTicket.symm.trans hf.2.2
      cases hb
    have hfR : ¬ HostFenceShapeV7 (C j) := by
      intro hf
      have hb : (false : Bool) = true := hjTicketJ.symm.trans hf.2.2
      cases hb
    have hacq : ¬ MoveAcquireFrontGuardV6 hpsi (C e) (C j) := by
      intro ha
      have hb : SpliceRole.none = SpliceRole.front := heRole.symm.trans ha.1.1
      cases hb
    have harm : ArmAGuard hpsi hwidth hle (C e).carrier (C j).carrier :=
      ⟨heRole, hjRoleJ, hePend, hjPendJ, hd⟩
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
    have hnone : role q.1.carrier = .none := hqLRole.trans heRole
    have hb : SpliceRole.victimArmed = SpliceRole.none := hv.symm.trans (heq.trans hnone)
    cases hb
  have hcar := ordinary_carrier_frame hpsi hwidth hle (C e) (C j)
  change q.1.carrier = o.1 /\ q.2.carrier = o.2 at hcar
  have hbaseL := congrArg (fun u : R1AgentStateV4 psi kappa tau => u.splice.base) hcar.1
  have hbaseR := congrArg (fun u : R1AgentStateV4 psi kappa tau => u.splice.base) hcar.2
  change q.1.carrier.splice.base =
    (BirthShortDoneTerminalHost.row hpsi hwidth hle
      (C e).carrier.splice.base (C j).carrier.splice.base).1 at hbaseL
  change q.2.carrier.splice.base =
    (BirthShortDoneTerminalHost.row hpsi hwidth hle
      (C e).carrier.splice.base (C j).carrier.splice.base).2 at hbaseR
  have hlabels := deletion_old_follower_labels hpsi hwidth hle
    (C e).carrier.splice.base (C j).carrier.splice.base hdelJ
  have hrel : rightFollowerRelabelledV7 (C j).carrier o.2 = false := by
    cases hh : rightFollowerRelabelledV7 (C j).carrier o.2 with
    | false => rfl
    | true =>
        have ht : role o.2 = .none /\ o.2.repairPending = false /\
            o.2.splice.base.core.core.leader = false /\
            o.2.splice.base.core.core.label ≠
              (C j).carrier.splice.base.core.core.label := by
          simpa [rightFollowerRelabelledV7] using hh
        have hjFollower : (C j).carrier.splice.base.core.core.leader = false := by
          cases hr0 : (C j).carrier.splice.base.core.core.leader with
          | false => rfl
          | true =>
              have hs := B9LeaderLossCensus.host_right_existing_leader_survives
                hpsi hwidth hle (C e).carrier.splice.base
                  (C j).carrier.splice.base hr0
              have hof :
                  (BirthShortDoneTerminalHost.row hpsi hwidth hle
                    (C e).carrier.splice.base
                    (C j).carrier.splice.base).2.core.core.leader = false := by
                simpa [o, ordinaryRow, setPhysical] using ht.2.2.1
              have hb : (true : Bool) = false := hs.symm.trans hof
              cases hb
        have heq : o.2.splice.base.core.core.label =
            (C j).carrier.splice.base.core.core.label := by
          simpa [o, ordinaryRow, setPhysical] using hlabels.2 hjFollower
        exact (ht.2.2.2 heq).elim
  have hqRTicket : q.2.acquireTicket = false := by
    unfold q ordinaryHostWriteV7
    dsimp only
    rw [hrel]
    rfl
  have hleftBack : q.1.carrier.splice.base.core.core.leader = false ->
      (C e).carrier.splice.base.core.core.leader = false := by
    intro hout
    cases hl0 : (C e).carrier.splice.base.core.core.leader with
    | false => rfl
    | true =>
        exfalso
        apply hnoDel
        exact ⟨hl0, (congrArg
          (fun u : ExpiringAgentState psi kappa tau => u.core.core.leader)
          hbaseL).symm.trans hout⟩
  have hrightBack : q.2.carrier.splice.base.core.core.leader = false ->
      (C j).carrier.splice.base.core.core.leader = false := by
    intro hout
    cases hr0 : (C j).carrier.splice.base.core.core.leader with
    | false => rfl
    | true =>
        have hs := B9LeaderLossCensus.host_right_existing_leader_survives
          hpsi hwidth hle (C e).carrier.splice.base (C j).carrier.splice.base hr0
        have hof := (congrArg
          (fun u : ExpiringAgentState psi kappa tau => u.core.core.leader)
          hbaseR).symm.trans hout
        have hb : (true : Bool) = false := hs.symm.trans hof
        cases hb
  have hrole : forall i, role (D i).carrier = role (C i).carrier := by
    intro i
    by_cases hie : i = e
    · subst i
      exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => role u.carrier) hDe).trans hqLRole
    · by_cases hij : i = j
      · subst i
        exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => role u.carrier) hDj).trans hqRRole
      · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => role u.carrier)
          (stepV8_other hpsi hwidth hle ring C e i hie (by simpa only [j] using hij))
  have hpending : forall i, (D i).carrier.repairPending = (C i).carrier.repairPending := by
    intro i
    by_cases hie : i = e
    · subst i
      exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.repairPending) hDe).trans hqLPend
    · by_cases hij : i = j
      · subst i
        exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.repairPending) hDj).trans hqRPend
      · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.repairPending)
          (stepV8_other hpsi hwidth hle ring C e i hie (by simpa only [j] using hij))
  have hticket : forall i, (D i).acquireTicket = (C i).acquireTicket := by
    intro i
    by_cases hie : i = e
    · subst i
      exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket) hDe).trans
        (hqLTicket.trans heTicket.symm)
    · by_cases hij : i = j
      · subst i
        exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket) hDj).trans
          (hqRTicket.trans hjTicketJ.symm)
      · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket)
          (stepV8_other hpsi hwidth hle ring C e i hie (by simpa only [j] using hij))
  have hback : forall i,
      (D i).carrier.splice.base.core.core.leader = false ->
      (C i).carrier.splice.base.core.core.leader = false /\
      (D i).carrier.splice.base.core.core.label =
        (C i).carrier.splice.base.core.core.label := by
    intro i hi
    by_cases hie : i = e
    · subst i
      have hqf := (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
        u.carrier.splice.base.core.core.leader) hDe).symm.trans hi
      have hold := hleftBack hqf
      refine ⟨hold, ?_⟩
      calc
        (D e).carrier.splice.base.core.core.label = q.1.carrier.splice.base.core.core.label :=
          congrArg (fun u : R1AgentStateV6 psi kappa tau =>
            u.carrier.splice.base.core.core.label) hDe
        _ = (BirthShortDoneTerminalHost.row hpsi hwidth hle
              (C e).carrier.splice.base (C j).carrier.splice.base).1.core.core.label :=
          congrArg (fun u : ExpiringAgentState psi kappa tau => u.core.core.label) hbaseL
        _ = (C e).carrier.splice.base.core.core.label := hlabels.1 hold
    · by_cases hij : i = j
      · subst i
        have hqf := (congrArg (fun u : R1AgentStateV6 psi kappa tau =>
          u.carrier.splice.base.core.core.leader) hDj).symm.trans hi
        have hold := hrightBack hqf
        refine ⟨hold, ?_⟩
        calc
          (D j).carrier.splice.base.core.core.label = q.2.carrier.splice.base.core.core.label :=
            congrArg (fun u : R1AgentStateV6 psi kappa tau =>
              u.carrier.splice.base.core.core.label) hDj
          _ = (BirthShortDoneTerminalHost.row hpsi hwidth hle
                (C e).carrier.splice.base (C j).carrier.splice.base).2.core.core.label :=
            congrArg (fun u : ExpiringAgentState psi kappa tau => u.core.core.label) hbaseR
          _ = (C j).carrier.splice.base.core.core.label := hlabels.2 hold
      · have hs := stepV8_other hpsi hwidth hle ring C e i hie
          (by simpa only [j] using hij)
        exact ⟨(congrArg (fun u : R1AgentStateV6 psi kappa tau =>
          u.carrier.splice.base.core.core.leader) hs).symm.trans hi,
          congrArg (fun u : R1AgentStateV6 psi kappa tau =>
            u.carrier.splice.base.core.core.label) hs⟩
  have hprot : forall x,
      ProtectedSpliceEdgeV7 ring D x <-> ProtectedSpliceEdgeV7 ring C x := by
    intro x
    unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 HostFenceShapeV7
      ReservedFrontHoldGuard projectV6
    dsimp only
    simp only [hrole x, hpending x, hticket x,
      hrole (ring.rightNeighbor x), hpending (ring.rightNeighbor x)]
  refine ⟨?_, ?_⟩
  · intro x hdx
    exact (hprot x).2 (hsafe.1 x (danger_back hpsi ring C D x hback hdx))
  · rcases hsafe.2 with ⟨htsafe, hpsafe⟩
    constructor
    · intro i
      unfold TicketShapeV7
      intro ht
      have htC : (C i).acquireTicket = true := (hticket i).symm.trans ht
      rcases htsafe i htC with hres | hf
      · left
        unfold ReservedFrontHoldGuard at hres ⊢
        exact ⟨(hrole i).trans hres.1, (hpending i).trans hres.2⟩
      · right
        unfold HostFenceShapeV7 at hf ⊢
        exact ⟨(hrole i).trans hf.1, (hpending i).trans hf.2.1, ht⟩
    · intro i hri hpi
      have hold := hpsafe i ((hrole i).symm.trans hri) ((hpending i).symm.trans hpi)
      constructor
      · unfold ReservedFrontHoldGuard at hold ⊢
        exact ⟨(hrole (ring.rightNeighbor i)).trans hold.1.1,
          (hpending (ring.rightNeighbor i)).trans hold.1.2⟩
      · exact (hticket (ring.rightNeighbor i)).trans hold.2

#print axioms B9SpliceV8DeletionCase.ordinary_deletion_priority_preserves_spliceSafeV7

end B9SpliceV8DeletionCase

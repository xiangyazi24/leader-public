import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
import Leader.Wu.Splice.OrdinaryHostDeletionSafe

set_option autoImplicit false
set_option Elab.async false

/-! # Physical hold, deletion-priority branch: SpliceSafeV7 is preserved with kept roles

On the two deletion-priority choices of the physical host the follower labels are unchanged
and no follower becomes a leader, so with every controller field kept the whole invariant
transports.  Generalises `B9SpliceV8DeletionCase.ordinary_deletion_priority_preserves_spliceSafeV7`
to arbitrary kept roles (the served pair is assumed leaderless). -/

namespace B9SpliceV10ePhysicalHoldDeletion

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceV8LabelFrame B9SpliceTableV10e
  B9SpliceV10ePhysicalHoldNoBirth

variable {n psi width kappa tau : Nat}

/-! ## Local copies of the private V8 deletion-case lemmas -/

private theorem deletion_entry_leaders
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hdel :
      deletionActive (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true \/
      (deletionActive (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = false /\
       deletionActive (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase) = true)) :
    let q := BirthShortDoneTerminalHost.doneMetadataEntryWidth hpsi hwidth hle l r
    q.1.core.core.leader = l.core.core.leader /\ q.2.core.core.leader = r.core.core.leader := by
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
  have hentry := BirthShortDoneTerminalConsumer.doneMetadataEntryWidth_observation hpsi hwidth hle l r
  have hsignal :
      (ExpiringK2Projection.observeCell q.1, ExpiringK2Projection.observeCell q.2) =
      (ExpiringK2Projection.observeCell l, ExpiringK2Projection.observeCell r) := by
    calc
      (ExpiringK2Projection.observeCell q.1, ExpiringK2Projection.observeCell q.2) =
          K2BirthDispatcher.authSignalPair
            (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
              hpsi hwidth hle kappa pl.core.erase pr.core.erase) := by
        simpa only [q, pl, pr] using hentry
      _ = K2BirthDispatcher.authSignalPair (pl.core.erase, pr.core.erase) := hauth
      _ = (ExpiringK2Projection.observeCell pl, ExpiringK2Projection.observeCell pr) := rfl
      _ = (ExpiringK2Projection.observeCell l, ExpiringK2Projection.observeCell r) :=
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
      deletionActive (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true \/
      (deletionActive (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = false /\
       deletionActive (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase) = true)) :
    (l.core.core.leader = false ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.label = l.core.core.label) /\
    (r.core.core.leader = false ->
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.label = r.core.core.label) := by
  let d := BirthShortDoneTerminalHost.doneMetadataEntryWidth hpsi hwidth hle l r
  have hleaders := deletion_entry_leaders hpsi hwidth hle l r hdel
  change d.1.core.core.leader = l.core.core.leader /\ d.2.core.core.leader = r.core.core.leader at hleaders
  have hlabels : d.1.core.core.label = l.core.core.label /\ d.2.core.core.label = r.core.core.label := by
    rcases hdel with hr | ⟨hr, hl⟩
    · exact B9SpliceV8LabelFrame.host_responder_deletion_label_frame hpsi hwidth hle l r hr
    · exact B9SpliceV8LabelFrame.host_initiator_deletion_label_frame hpsi hwidth hle l r hr hl
  have hrow := B9SpliceV8LabelFrame.hostRow_labels_metadata hpsi hwidth hle l r
  constructor
  · intro hl
    calc
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).1.core.core.label =
          (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).1.core.core.label := hrow.1
      _ = d.1.core.core.label := by
        change (K2BirthLeaderNormalize.normalizeLeader hpsi d.1).core.core.label = d.1.core.core.label
        simp [K2BirthLeaderNormalize.normalizeLeader, hleaders.1.trans hl]
      _ = l.core.core.label := hlabels.1
  · intro hr
    calc
      (BirthShortDoneTerminalHost.row hpsi hwidth hle l r).2.core.core.label =
          (BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r).2.core.core.label := hrow.2
      _ = d.2.core.core.label := by
        change (K2BirthLeaderNormalize.normalizeLeader hpsi d.2).core.core.label = d.2.core.core.label
        simp [K2BirthLeaderNormalize.normalizeLeader, hleaders.2.trans hr]
      _ = r.core.core.label := hlabels.2

/-! ## The theorem -/

theorem physicalHold_deletion_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7 hpsi ring C)
    (hself : ring.rightNeighbor e ≠ e)
    (hl : (C e).carrier.splice.base.core.core.leader = false)
    (hr : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false)
    (hdel :
      deletionActive (normalizeDeletion
        (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase) = true \/
      (deletionActive (normalizeDeletion
        (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase) = false /\
       deletionActive (normalizeDeletion
        (prepareExpiringDisposal hpsi (C e).carrier.splice.base).core.erase) = true)) :
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
  have hlabels := deletion_old_follower_labels hpsi hwidth hle
    (C e).carrier.splice.base (C j).carrier.splice.base (by simpa only [j] using hdel)
  have hrJ : (C j).carrier.splice.base.core.core.leader = false := by simpa only [j] using hr
  -- the responder keeps its label, so the relabel rule does not fire and its ticket is kept
  have hrel : rightFollowerRelabelledV7 (C j).carrier o.2 = false := by
    cases hh : rightFollowerRelabelledV7 (C j).carrier o.2 with
    | false => rfl
    | true =>
        have ht : role o.2 = .none /\ o.2.repairPending = false /\
            o.2.splice.base.core.core.leader = false /\
            o.2.splice.base.core.core.label ≠ (C j).carrier.splice.base.core.core.label := by
          simpa [rightFollowerRelabelledV7] using hh
        have heq : o.2.splice.base.core.core.label = (C j).carrier.splice.base.core.core.label := by
          have h1 : o.2.splice.base = (BirthShortDoneTerminalHost.row hpsi hwidth hle
              (C e).carrier.splice.base (C j).carrier.splice.base).2 := by
            simpa only [q] using hqCarrierR ▸ hbaseR
          rw [h1]
          exact hlabels.2 hrJ
        exact (ht.2.2.2 heq).elim
  have hrel' : rightFollowerRelabelledV7 (C j).carrier
      (ordinaryRow hpsi hwidth hle (C e).carrier (C j).carrier).2 = false := by
    simpa only [o] using hrel
  have hqRTicket' : q.2.acquireTicket = (C j).acquireTicket := by
    rw [hqRTicket]; simp [hrel']
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
  have hticket : forall i, (D i).acquireTicket = (C i).acquireTicket := by
    intro i
    by_cases hie : i = e
    · subst i; exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket) hDe).trans hqLTicket
    · by_cases hij : i = j
      · subst i; exact (congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket) hDj).trans hqRTicket'
      · exact congrArg (fun u : R1AgentStateV6 psi kappa tau => u.acquireTicket) (hDother i hie hij)
  have hback : forall i,
      (D i).carrier.splice.base.core.core.leader = false ->
      (C i).carrier.splice.base.core.core.leader = false /\
      (D i).carrier.splice.base.core.core.label = (C i).carrier.splice.base.core.core.label := by
    intro i _
    by_cases hie : i = e
    · subst i
      refine ⟨hl, ?_⟩
      rw [hDe]
      have := congrArg (fun b : ExpiringAgentState psi kappa tau => b.core.core.label) hbaseL
      exact this.trans (hlabels.1 hl)
    · by_cases hij : i = j
      · subst i
        refine ⟨hrJ, ?_⟩
        rw [hDj]
        have := congrArg (fun b : ExpiringAgentState psi kappa tau => b.core.core.label) hbaseR
        exact this.trans (hlabels.2 hrJ)
      · have hs := hDother i hie hij
        exact ⟨(congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.splice.base.core.core.leader) hs).symm.trans
          ‹(D i).carrier.splice.base.core.core.leader = false›,
          congrArg (fun u : R1AgentStateV6 psi kappa tau => u.carrier.splice.base.core.core.label) hs⟩
  have hdanger_back : forall x, PreparedDangerAt hpsi ring (projectV6 D) x ->
      PreparedDangerAt hpsi ring (projectV6 C) x := by
    intro x hdx
    have hd := (danger_iff_physical hpsi ring D x).1 hdx
    obtain ⟨hcL, hlabL⟩ := hback x hd.1
    obtain ⟨hcR, hlabR⟩ := hback (ring.rightNeighbor x) hd.2.1
    refine (danger_iff_physical hpsi ring C x).2 ⟨hcL, hcR, ?_⟩
    intro hh
    apply hd.2.2
    rw [hlabR, hlabL]
    exact hh
  have hprot : forall x, ProtectedSpliceEdgeV7 ring D x <-> ProtectedSpliceEdgeV7 ring C x := by
    intro x
    unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 HostFenceShapeV7 ReservedFrontHoldGuard projectV6
    dsimp only
    simp only [hrole x, hpending x, hticket x, hrole (ring.rightNeighbor x), hpending (ring.rightNeighbor x)]
  refine ⟨?_, ?_⟩
  · intro x hdx
    exact (hprot x).2 (hsafe.1 x (hdanger_back x hdx))
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
        exact ⟨(hrole (ring.rightNeighbor i)).trans hold.1.1, (hpending (ring.rightNeighbor i)).trans hold.1.2⟩
      · exact (hticket (ring.rightNeighbor i)).trans hold.2

end B9SpliceV10ePhysicalHoldDeletion

import Leader.Wu.Splice.PhysicalHoldDeletionSafe
import Leader.Wu.Splice.PhysicalHoldBirthSafe
import Leader.Wu.Splice.CertifiedDeleteSafe

set_option autoImplicit false
set_option Elab.async false

/-! # Physical hold on a follower pair preserves `SpliceSafeV7g`

The three branches of the physical row on a served pair of followers (birth, deletion priority, open
no-birth) restated for the extended invariant `SpliceSafeV7g`, with every controller field kept.  The proofs
are the V7 proofs (`B9SpliceV10ePhysicalHold{NoBirth,Deletion,Birth}`) with one change: the provenance
clause is proved first, an edge whose left cell is a pending predecessor is covered by the fourth shape
(`spliceSafeV7g_of_provenance_and_nonpending`), and at every other edge the old V7 coverage of the start
configuration is available (`nonpending_coverage_of_spliceSafeV7g`, the kept roles transport the
non-pending hypothesis).  The served pair is a pair of followers; leaders elsewhere on the ring are allowed. -/

namespace B9SpliceV10hPhysicalHoldFollowerV7g

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open BirthShortDoneTerminalHost K2BirthLeaderNormalize
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceV8LabelFrame B9SpliceV8BirthCaseAdapter
  B9SpliceTableV10e B9SpliceV10ePhysicalHoldNoBirth B9SpliceV10ePhysicalHoldBirth
  B9SpliceTableV10g B9SpliceCertifiedDelete

variable {n psi width kappa tau : Nat}

/-! ## Local copies of the private helpers -/

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

/-! ## The three branches -/

theorem physicalHold_no_birth_preserves_spliceSafeV7g
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7g hpsi ring C)
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
    SpliceSafeV7g hpsi ring (physicalHoldAt hpsi hwidth hle ring C e) := by
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
  have hprovD : ProvenanceSafeV7 ring D := by
    refine ⟨?_, ?_⟩
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
  refine spliceSafeV7g_of_provenance_and_nonpending hpsi ring D hprovD ?_
  · intro x hdx hnpD
    have hnpC : ¬ (role (C x).carrier = .predecessorArmed ∧ (C x).carrier.repairPending = true) :=
      fun h => hnpD ⟨(hrole x).trans h.1, (hpending x).trans h.2⟩
    have hsafeX : PreparedDangerAt hpsi ring (projectV6 C) x → ProtectedSpliceEdgeV7 ring C x :=
      fun hd => nonpending_coverage_of_spliceSafeV7g hpsi ring C hsafe x hd hnpC
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
          have hold := hsafeX ((danger_iff_physical hpsi ring C j).2 ⟨hr, hkLeader, hbar⟩)
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
        have hold := hsafeX ((danger_iff_physical hpsi ring C x).2 ⟨hxLeader, hyLeader, hbar⟩)
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
        have hold := hsafeX hd0
        unfold ProtectedSpliceEdgeV7 at hold ⊢
        rcases hold with hv3 | hf
        · exact Or.inl ((v3Protection_frame ring C D x hrole hpending).2 hv3)
        · exact Or.inr (cast (congrArg HostFenceShapeV7 hDx.symm) hf)

theorem physicalHold_deletion_preserves_spliceSafeV7g
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7g hpsi ring C)
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
    SpliceSafeV7g hpsi ring (physicalHoldAt hpsi hwidth hle ring C e) := by
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
  have hprovD : ProvenanceSafeV7 ring D := by
    rcases hsafe.2 with ⟨htsafe, hpsafe⟩
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
  refine spliceSafeV7g_of_provenance_and_nonpending hpsi ring D hprovD ?_
  · intro x hdx hnpD
    have hnpC : ¬ (role (C x).carrier = .predecessorArmed ∧ (C x).carrier.repairPending = true) :=
      fun h => hnpD ⟨(hrole x).trans h.1, (hpending x).trans h.2⟩
    have hsafeX : PreparedDangerAt hpsi ring (projectV6 C) x → ProtectedSpliceEdgeV7 ring C x :=
      fun hd => nonpending_coverage_of_spliceSafeV7g hpsi ring C hsafe x hd hnpC
    exact (hprot x).2 (hsafeX (hdanger_back x hdx))

theorem physicalHold_birth_preserves_spliceSafeV7g
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeV7g hpsi ring C)
    (hself : ring.rightNeighbor e ≠ e)
    (hrshape : (role (C (ring.rightNeighbor e)).carrier = .none ∧
        (C (ring.rightNeighbor e)).carrier.repairPending = false) ∨
      ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier)
    (hl : (C e).carrier.splice.base.core.core.leader = false)
    (hr : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false)
    (hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = true) :
    SpliceSafeV7g hpsi ring (physicalHoldAt hpsi hwidth hle ring C e) := by
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
  have hprovD : ProvenanceSafeV7 ring D := by
    refine ⟨?_, ?_⟩
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
  refine spliceSafeV7g_of_provenance_and_nonpending hpsi ring D hprovD ?_
  · intro x hdx hnpD
    have hnpC : ¬ (role (C x).carrier = .predecessorArmed ∧ (C x).carrier.repairPending = true) :=
      fun h => hnpD ⟨(hrole x).trans h.1, (hpending x).trans h.2⟩
    have hsafeX : PreparedDangerAt hpsi ring (projectV6 C) x → ProtectedSpliceEdgeV7 ring C x :=
      fun hd => nonpending_coverage_of_spliceSafeV7g hpsi ring C hsafe x hd hnpC
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
            have hold := hsafeX ((danger_iff_physical hpsi ring C j).2 ⟨hrJ, hkLeader, hbar⟩)
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
          have hold := hsafeX ((danger_iff_physical hpsi ring C x).2 ⟨hxLeader, hyLeader, hbar⟩)
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
        have hold := hsafeX hd0
        unfold ProtectedSpliceEdgeV7 at hold ⊢
        rcases hold with hv3 | hf
        · exact Or.inl ((v3Protection_frame ring C D x hrole hpending).2 hv3)
        · exact Or.inr (cast (congrArg HostFenceShapeV7 hDx.symm) hf)

end B9SpliceV10hPhysicalHoldFollowerV7g

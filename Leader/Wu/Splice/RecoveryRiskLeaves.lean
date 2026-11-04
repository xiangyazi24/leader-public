-- REPLACE Parts 1-2 completely, from the imports through immediately before
-- existing `abbrev RecoveryActive`.
import Leader.Wu.Splice.ControllerRecoveryMass
import Leader.Core.FiniteUniformStoppingTree
import Leader.Core.ModArith


set_option autoImplicit false
set_option Elab.async false


namespace B9ControllerRecovery


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair BirthShortDoneTerminalEntryCut
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10d B9SpliceTableV10e
  B9SpliceTableV10g B9SpliceTableV10j
open B9SpliceV10hControllerRowsSafe
open B9Host B9SpliceTableHost
open BirthTwoStageEscape FiniteUniformStoppingTree


variable {n psi kappa tau : Nat}


private theorem ind_mono_rate {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  classical
  by_cases hp : P
  · have hq : Q := h hp
    simp [ind, hp, hq]
  · simp [ind, hp]


private theorem ind_le_one_rate (P : Prop) : ind P ≤ 1 := by
  classical
  by_cases h : P <;> simp [ind, h]


/-- The two edge-local terms of the global recovery potential. -/
noncomputable def edgeRisk (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : Nat :=
  2 * ind (BadBacking l r) + ind (Hole hpsi l r)


noncomputable def edgeRiskScan (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) : Nat :=
  (List.ofFn (fun i : Fin n =>
    edgeRisk hpsi (C i) (C (ring.rightNeighbor i)))).sum


theorem edgeRiskScan_eq
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) :
    edgeRiskScan hpsi ring C =
      2 * backingFaults ring C + holes hpsi ring C := by
  unfold edgeRiskScan edgeRisk
  rw [FiniteUniformStoppingTree.ofFn_sum_add,
    FiniteUniformStoppingTree.ofFn_sum_mul_left]
  rw [backingFaults_eq_faultScan, holes_eq_faultScan]
  rfl


-- REPLACE recoveryPotential_eq_scans.
theorem recoveryPotential_eq_scans
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) :
    recoveryPotential hpsi ring C =
      3 * faultScan (fun i => BadTicket (C i)) + edgeRiskScan hpsi ring C := by
  rw [edgeRiskScan_eq, ← ticketFaults_eq_faultScan]
  unfold recoveryPotential
  omega


/-- The exact local contract needed to lift a non-garbage B9 fallback row to
one-step global potential monotonicity.  The `reverse` field is the n=2 alias. -/
structure PairRiskNoRaise
    (hpsi : 0 < psi)
    (l r l' r' : Cell psi kappa tau) : Prop where
  ticketL : ind (BadTicket l') ≤ ind (BadTicket l)
  ticketR : ind (BadTicket r') ≤ ind (BadTicket r)
  incoming : ∀ p, edgeRisk hpsi p l' ≤ edgeRisk hpsi p l
  served : edgeRisk hpsi l' r' ≤ edgeRisk hpsi l r
  outgoing : ∀ s, edgeRisk hpsi r' s ≤ edgeRisk hpsi r s
  reverse : edgeRisk hpsi r' l' ≤ edgeRisk hpsi r l


private theorem rn_injective_rate (ring : DirectedRing n) :
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


-- REPLACE ticketScan_writeAt_le.
private theorem ticketScan_writeAt_le
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (w : Cell psi kappa tau × Cell psi kappa tau)
    (hP : PairRiskNoRaise hpsi (C e) (C (ring.rightNeighbor e)) w.1 w.2) :
    faultScan (fun i => BadTicket (writeAt ring C e w i)) ≤
      faultScan (fun i => BadTicket (C i)) := by
  unfold faultScan
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro i
  change ind (BadTicket (writeAt ring C e w i)) ≤ ind (BadTicket (C i))
  by_cases hie : i = e
  · subst i
    simpa only [writeAt_e] using hP.ticketL
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa only [writeAt_j ring C e w hself] using hP.ticketR
    · rw [writeAt_other ring C e w i hie hij]
      exact Nat.le_refl _




-- REPLACE edgeRiskScan_writeAt_le.
private theorem edgeRiskScan_writeAt_le
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (w : Cell psi kappa tau × Cell psi kappa tau)
    (hP : PairRiskNoRaise hpsi (C e) (C (ring.rightNeighbor e)) w.1 w.2) :
    edgeRiskScan hpsi ring (writeAt ring C e w) ≤ edgeRiskScan hpsi ring C := by
  unfold edgeRiskScan
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro i
  change edgeRisk hpsi
      (writeAt ring C e w i)
      (writeAt ring C e w (ring.rightNeighbor i)) ≤
    edgeRisk hpsi (C i) (C (ring.rightNeighbor i))
  by_cases hie : i = e
  · subst i
    simpa only [writeAt_e, writeAt_j ring C e w hself] using hP.served
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      rw [writeAt_j ring C e w hself]
      by_cases hje : ring.rightNeighbor (ring.rightNeighbor e) = e
      · rw [hje, writeAt_e]
        exact hP.reverse
      · have hjj : ring.rightNeighbor (ring.rightNeighbor e) ≠
          ring.rightNeighbor e := by
          intro hh
          have heq : ring.rightNeighbor e = e :=
            rn_injective_rate ring (by simpa using hh)
          exact hself heq
        rw [writeAt_other ring C e w _ hje hjj]
        exact hP.outgoing (C (ring.rightNeighbor (ring.rightNeighbor e)))
    · rw [writeAt_other ring C e w i hie hij]
      by_cases hre : ring.rightNeighbor i = e
      · rw [hre, writeAt_e]
        exact hP.incoming (C i)
      · have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          exact hie (rn_injective_rate ring h)
        rw [writeAt_other ring C e w (ring.rightNeighbor i) hre hrj]
        exact Nat.le_refl _



-- CONTINUATION OF THE COMPLETE PARTS 1-2 REPLACEMENT.
theorem recoveryPotential_writeAt_le
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (w : Cell psi kappa tau × Cell psi kappa tau)
    (hP : PairRiskNoRaise hpsi (C e) (C (ring.rightNeighbor e)) w.1 w.2) :
    recoveryPotential hpsi ring (writeAt ring C e w) ≤
      recoveryPotential hpsi ring C := by
  rw [recoveryPotential_eq_scans, recoveryPotential_eq_scans]
  have hT := ticketScan_writeAt_le hpsi ring C e hself w hP
  have hE := edgeRiskScan_writeAt_le hpsi ring C e hself w hP
  omega


/-! Physical danger is exactly follower/follower misalignment. -/


private theorem normalizeDeletion_leader_rate (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareDisposal_leader_rate
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.leader = u.core.leader := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl


private theorem normalizeDeletion_label_rate (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareDisposal_label_rate
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.label = u.core.label := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl


private theorem preparedR1_leader_rate
    (hpsi : 0 < psi) (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.leader = u.splice.base.core.core.leader := by
  unfold preparedR1 prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.splice.base.core]
  rw [normalizeDeletion_leader_rate, prepareDisposal_leader_rate]
  rfl


private theorem preparedR1_label_rate
    (hpsi : 0 < psi) (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.label = u.splice.base.core.core.label := by
  unfold preparedR1 prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.splice.base.core]
  rw [normalizeDeletion_label_rate, prepareDisposal_label_rate]
  rfl


private def RawDanger (l r : Phys psi kappa tau) : Prop :=
  B9Host.leader l = false ∧ B9Host.leader r = false ∧
    ¬ B9Host.Aligned l r


-- REPLACE localDanger_iff_raw.
private theorem localDanger_iff_raw
    (hpsi : 0 < psi) (l r : Cell psi kappa tau) :
    LocalDanger hpsi l r ↔ RawDanger (base l) (base r) := by
  unfold LocalDanger LocalPreparedBarrier RawDanger B9Host.Aligned
  dsimp only
  unfold isBarrier B9Host.leader B9Host.label B9SpliceTableHost.base
  simp only [preparedR1_leader_rate, preparedR1_label_rate]
  constructor
  · rintro ⟨hl, hr, hne⟩
    refine ⟨hl, hr, ?_⟩
    intro hv
    apply hne
    apply Fin.ext
    exact hv
  · rintro ⟨hl, hr, hne⟩
    refine ⟨hl, hr, ?_⟩
    intro hf
    apply hne
    exact congrArg Fin.val hf


/-! ## Split non-garbage fallback census


The host table rows are kept opaque across layer boundaries.  A table layer is
opened only in the lemma for that layer.  The physical ordinary/hold leaves are
separate declarations, so their small finite leader/alignment census is never
multiplied by the controller guard tree. -/


section PairRiskCensus


attribute [local irreducible]
  B9SpliceTableHost.row7H B9SpliceTableHost.row8H
  B9SpliceTableHost.row9H B9SpliceTableHost.row10bH
  B9SpliceTableHost.row10cH B9SpliceTableHost.row10dgH
  B9SpliceTableHost.row10gH B9SpliceTableHost.rowB9


private theorem pairRisk_refl
    (hpsi : 0 < psi) (l r : Cell psi kappa tau) :
    PairRiskNoRaise hpsi l r l r := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, Nat.le_refl _, ?_, Nat.le_refl _⟩
  · intro p
    exact Nat.le_refl _
  · intro s
    exact Nat.le_refl _


/-- Guard-aware `ite`: branch hypotheses are retained for the leaf proof. -/
private theorem pairRisk_ite_on
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (P : Prop) [Decidable P]
    (a b : Cell psi kappa tau × Cell psi kappa tau)
    (ha : P → PairRiskNoRaise hpsi l r a.1 a.2)
    (hb : ¬ P → PairRiskNoRaise hpsi l r b.1 b.2) :
    PairRiskNoRaise hpsi l r
      (if P then a else b).1 (if P then a else b).2 := by
  by_cases h : P
  · simpa only [if_pos h] using ha h
  · simpa only [if_neg h] using hb h


private theorem edgeRisk_mono_rate
    (hpsi : 0 < psi)
    (l r l' r' : Cell psi kappa tau)
    (hB : BadBacking l' r' → BadBacking l r)
    (hH : Hole hpsi l' r' → Hole hpsi l r) :
    edgeRisk hpsi l' r' ≤ edgeRisk hpsi l r := by
  have hB' := ind_mono_rate hB
  have hH' := ind_mono_rate hH
  unfold edgeRisk
  omega

macro "risk_prepare" : tactic =>
  `(tactic|
    (refine ⟨ind_mono_rate ?_, ind_mono_rate ?_, ?_, ?_, ?_, ?_⟩
     all_goals try intro x
     all_goals try apply edgeRisk_mono_rate
     all_goals try intro h))





macro "risk_split_ite" : tactic =>
  `(tactic| (apply pairRisk_ite_on hpsi l r <;> intro))



macro "risk_simp" : tactic =>
  `(tactic|
    (simp_all [Garbage, ScrubGarbage, BadTicket, BadBacking, Pending,
      Hole, PairCovered, localDanger_iff_raw, RawDanger,
      B9Host.Aligned, B9Host.leader, B9Host.label,
      B9Host.LeftDeletionCandidate, B9SpliceTableHost.ldc,
      B9SpliceTableHost.base,
      HostFenceShapeV7, HostFenceTargetClearV7,
      ReservedFrontHoldGuard, PendingOwnerHoldShapeV7,
      RightStalePredecessorHoldGuardV8,
      HostFenceBusyFrontGuardV9, HostFenceAdvanceGuardV10b,
      MoveAcquireFrontGuardV6, B9SpliceTableHost.ArmAGuardH,
      ArmBGuard, B9SpliceTableHost.DeleteGuardH,
      B9SpliceTableHost.PendingHoldGuardH,
      B9SpliceTableHost.PendingAbortGuardH,
      MoveCommitGuard, MoveStopGuardV3, MoveSeekGuardV3,
      MoveSeekHoldGuardV3, PendingOwnerAbortGuardV3,
      MoveAcquireLegacyGuardV6, MoveAcquireAbortGuardV3,
      OrphanReservedFrontGuardV3, VictimRightScrubGuardV6,
      VictimLeftScrubGuardV6, FrontRightScrubGuardV6,
      MalformedLeftPendingGuardV6, MalformedRightPendingGuardV6,
      MarkedHoldGuardV6, OrphanVictimGuard, OwnedPendingVictimGuard,
      OwnerlessPendingPredGuard, LeftScrubGuardV10e,
      rightFollowerRelabelledV7,
      B9SpliceTableV10j.holdRepairV10j,
      B9SpliceTableHost.deleteWriteH, B9SpliceTableHost.physicalHoldH,
      B9SpliceTableHost.ordinaryHostWriteH, B9SpliceTableHost.ordinaryRowH,
      hostFenceLeftAdvanceWriteV7, hostFenceLeftHoldWriteV7,
      hostFenceLeftStopWriteV7, hostFenceRightHoldWriteV7,
      hostFenceBusyFrontRepairWriteV9, hostFenceHandoffWriteV10b,
      moveAcquireFrontWriteV6, armAWriteV6, armBWriteV6,
      pendingHoldWriteV6, pendingAbortWriteV6, moveCommitWriteV6,
      moveStopWriteV6, moveSeekWriteV6, moveSeekHoldWriteV6,
      pendingOwnerAbortWriteV6, pendingOwnerHoldWriteV6,
      moveAcquireLegacyWriteV6, moveAcquireAbortWriteV6,
      orphanReservedFrontWriteV6, reservedFrontHoldWriteV6,
      victimRightScrubWriteV6, victimLeftScrubWriteV6,
      frontRightScrubWriteV6, malformedLeftPendingWriteV6,
      malformedRightPendingWriteV6, predecessorLeftScrubWriteV6,
      leftFrontHoldWriteV6, markedHoldWriteV6,
      fenceV6, settleV6, clearControlV6, clearTicketV6,
      setControlV6, setTicketV6, withCarrierClearTicketV6,
      setControl, setPhysical, repairResponder, role]))



/-- Extra physical frame actually needed by the recovery-risk census.
`B9Host.SpliceLaws` does not imply this for an arbitrary host. -/
private def RightFollowerLabelLaw
    (host : HostRow (Phys psi kappa tau)) : Prop :=
  ∀ (l r : Phys psi kappa tau),
    B9Host.leader r = false →
      B9Host.label (host.row l r).2 = B9Host.label r


/-- Row-7 ordinary fallthrough has already passed both host-fence branches.
These two facts are essential because the ordinary writer clears tickets. -/
private structure OrdinaryLeafFallthrough
    (l r : Cell psi kappa tau) : Prop where
  noLeftFence : ¬ HostFenceShapeV7 l
  noRightFence : ¬ HostFenceShapeV7 r

private structure PhysicalHostRiskFacts
    (l r : Cell psi kappa tau)
    (p : Phys psi kappa tau × Phys psi kappa tau) : Prop where
  leftLeader :
    B9Host.leader (base l) = true →
      B9Host.leader p.1 = true
  leftFollowerLabel :
    B9Host.leader (base l) = false →
      B9Host.label p.1 = B9Host.label (base l)
  rightLeader :
    B9Host.leader (base r) = true →
      B9Host.leader p.2 = true
  rightFollowerLabel :
    B9Host.leader (base r) = false →
      B9Host.label p.2 = B9Host.label (base r)
  alignedFollowers :
    B9Host.leader (base l) = false →
    B9Host.leader (base r) = false →
    B9Host.leader p.1 = false →
    B9Host.leader p.2 = false →
    B9Host.Aligned (base l) (base r) →
      B9Host.Aligned p.1 p.2



private def ordinaryHostWriteFromPhysical
    (p : Phys psi kappa tau × Phys psi kappa tau)
    (l r : Cell psi kappa tau) :
    Cell psi kappa tau × Cell psi kappa tau :=
  let q := (setPhysical l.carrier p.1, setPhysical r.carrier p.2)
  let l' := withCarrierClearTicketV6 l q.1
  let r' := withCarrierClearTicketV6 r q.2
  if rightFollowerRelabelledV7 r.carrier q.2 then
    (l', setTicketV6 r' true)
  else
    (l', r')


private def physicalHoldFromPhysical
    (p : Phys psi kappa tau × Phys psi kappa tau)
    (l r : Cell psi kappa tau) :
    Cell psi kappa tau × Cell psi kappa tau :=
  let q := (setPhysical l.carrier p.1, setPhysical r.carrier p.2)
  let l' : Cell psi kappa tau := ⟨q.1, l.acquireTicket⟩
  let r' : Cell psi kappa tau := ⟨q.2, r.acquireTicket⟩
  if rightFollowerRelabelledV7 r.carrier q.2 then
    (l', setTicketV6 r' true)
  else
    (l', r')


private theorem ordinaryHostWriteH_eq_fromPhysical
    (host : HostRow (Phys psi kappa tau))
    (l r : Cell psi kappa tau) :
    B9SpliceTableHost.ordinaryHostWriteH host l r =
      ordinaryHostWriteFromPhysical
        (host.row (base l) (base r)) l r := by
  rfl


private theorem physicalHoldH_eq_fromPhysical
    (host : HostRow (Phys psi kappa tau))
    (l r : Cell psi kappa tau) :
    B9SpliceTableHost.physicalHoldH host l r =
      physicalHoldFromPhysical
        (host.row (base l) (base r)) l r := by
  rfl


private theorem physicalHostRiskFacts_of_spliceLaws
    (host : HostRow (Phys psi kappa tau))
    (hHost : B9Host.SpliceLaws host)
    (hRight : RightFollowerLabelLaw host)
    (l r : Cell psi kappa tau)
    (hNoDel : ¬ B9SpliceTableHost.ldc host l.carrier r.carrier) :
    PhysicalHostRiskFacts l r
      (host.row (base l) (base r)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hl
    have hNo :
        ¬ B9Host.LeftDeletionCandidate host (base l) (base r) := by
      simpa only [B9SpliceTableHost.ldc, B9SpliceTableHost.base] using hNoDel
    exact B9Host.left_leader_of_not_candidate
      host (base l) (base r) hNo hl
  · exact hHost.left_follower_label (base l) (base r)
  · exact hHost.right_leader (base l) (base r)
  · exact hRight (base l) (base r)
  · exact hHost.aligned_followers (base l) (base r)


private structure CellControllerFrame
    (u v : Cell psi kappa tau) : Prop where
  role_eq : role v.carrier = role u.carrier
  pending_eq : v.carrier.repairPending = u.carrier.repairPending
  ticket_eq : v.acquireTicket = u.acquireTicket

private theorem controllerFrame_refl
    (u : Cell psi kappa tau) : CellControllerFrame u u :=
  ⟨rfl, rfl, rfl⟩

private theorem badTicket_of_controllerFrame
    {u v : Cell psi kappa tau}
    (hF : CellControllerFrame u v) : BadTicket v → BadTicket u := by
  intro h
  simpa only [BadTicket, ReservedFrontHoldGuard, HostFenceShapeV7,
    hF.role_eq, hF.pending_eq, hF.ticket_eq] using h

private theorem badBacking_of_controllerFrames
    {l r l' r' : Cell psi kappa tau}
    (hL : CellControllerFrame l l') (hR : CellControllerFrame r r') :
    BadBacking l' r' → BadBacking l r := by
  intro h
  simpa only [BadBacking, Pending, ReservedFrontHoldGuard,
    hL.role_eq, hL.pending_eq,
    hR.role_eq, hR.pending_eq, hR.ticket_eq] using h

private theorem pairCovered_of_controllerFrames
    {l r l' r' : Cell psi kappa tau}
    (hL : CellControllerFrame l l') (hR : CellControllerFrame r r') :
    PairCovered l r → PairCovered l' r' := by
  intro h
  simpa only [PairCovered, Pending, ReservedFrontHoldGuard,
    HostFenceShapeV7, PendingOwnerHoldShapeV7,
    hL.role_eq, hL.pending_eq, hL.ticket_eq,
    hR.role_eq, hR.pending_eq, hR.ticket_eq] using h

private theorem hole_of_controllerFrames
    (hpsi : 0 < psi)
    {l r l' r' : Cell psi kappa tau}
    (hL : CellControllerFrame l l') (hR : CellControllerFrame r r')
    (hD : LocalDanger hpsi l' r' → LocalDanger hpsi l r) :
    Hole hpsi l' r' → Hole hpsi l r := by
  rintro ⟨hd, hn⟩
  refine ⟨hD hd, ?_⟩
  intro hc
  exact hn (pairCovered_of_controllerFrames hL hR hc)

private theorem pairRisk_of_controllerFrames
    (hpsi : 0 < psi)
    (l r l' r' : Cell psi kappa tau)
    (hL : CellControllerFrame l l') (hR : CellControllerFrame r r')
    (hIn : ∀ x, LocalDanger hpsi x l' → LocalDanger hpsi x l)
    (hServed : LocalDanger hpsi l' r' → LocalDanger hpsi l r)
    (hOut : ∀ x, LocalDanger hpsi r' x → LocalDanger hpsi r x)
    (hRev : LocalDanger hpsi r' l' → LocalDanger hpsi r l) :
    PairRiskNoRaise hpsi l r l' r' := by
  refine ⟨ind_mono_rate (badTicket_of_controllerFrame hL),
    ind_mono_rate (badTicket_of_controllerFrame hR), ?_, ?_, ?_, ?_⟩
  · intro x
    apply edgeRisk_mono_rate
    · exact badBacking_of_controllerFrames (controllerFrame_refl x) hL
    · exact hole_of_controllerFrames hpsi
        (controllerFrame_refl x) hL (hIn x)
  · apply edgeRisk_mono_rate
    · exact badBacking_of_controllerFrames hL hR
    · exact hole_of_controllerFrames hpsi hL hR hServed
  · intro x
    apply edgeRisk_mono_rate
    · exact badBacking_of_controllerFrames hR (controllerFrame_refl x)
    · exact hole_of_controllerFrames hpsi
        hR (controllerFrame_refl x) (hOut x)
  · apply edgeRisk_mono_rate
    · exact badBacking_of_controllerFrames hR hL
    · exact hole_of_controllerFrames hpsi hR hL hRev

private theorem oldLeftFollower_of_physicalFacts
    {l r : Cell psi kappa tau}
    {p : Phys psi kappa tau × Phys psi kappa tau}
    (hPhys : PhysicalHostRiskFacts l r p)
    (h : B9Host.leader p.1 = false) :
    B9Host.leader (base l) = false := by
  cases h0 : B9Host.leader (base l) with
  | false => rfl
  | true =>
      have hh := hPhys.leftLeader h0
      rw [h] at hh
      cases hh

private theorem oldRightFollower_of_physicalFacts
    {l r : Cell psi kappa tau}
    {p : Phys psi kappa tau × Phys psi kappa tau}
    (hPhys : PhysicalHostRiskFacts l r p)
    (h : B9Host.leader p.2 = false) :
    B9Host.leader (base r) = false := by
  cases h0 : B9Host.leader (base r) with
  | false => rfl
  | true =>
      have hh := hPhys.rightLeader h0
      rw [h] at hh
      cases hh

private theorem rawDanger_incoming_of_physicalFacts
    {l r : Cell psi kappa tau}
    {p : Phys psi kappa tau × Phys psi kappa tau}
    (hPhys : PhysicalHostRiskFacts l r p)
    (x : Phys psi kappa tau) :
    RawDanger x p.1 → RawDanger x (base l) := by
  rintro ⟨hx, hp, hna⟩
  have hl := oldLeftFollower_of_physicalFacts hPhys hp
  refine ⟨hx, hl, ?_⟩
  intro ha
  apply hna
  unfold B9Host.Aligned at ha ⊢
  rw [hPhys.leftFollowerLabel hl]
  exact ha

private theorem rawDanger_served_of_physicalFacts
    {l r : Cell psi kappa tau}
    {p : Phys psi kappa tau × Phys psi kappa tau}
    (hPhys : PhysicalHostRiskFacts l r p) :
    RawDanger p.1 p.2 → RawDanger (base l) (base r) := by
  rintro ⟨hpl, hpr, hna⟩
  have hl := oldLeftFollower_of_physicalFacts hPhys hpl
  have hr := oldRightFollower_of_physicalFacts hPhys hpr
  refine ⟨hl, hr, ?_⟩
  intro ha
  exact hna (hPhys.alignedFollowers hl hr hpl hpr ha)

private theorem rawDanger_outgoing_of_physicalFacts
    {l r : Cell psi kappa tau}
    {p : Phys psi kappa tau × Phys psi kappa tau}
    (hPhys : PhysicalHostRiskFacts l r p)
    (x : Phys psi kappa tau) :
    RawDanger p.2 x → RawDanger (base r) x := by
  rintro ⟨hp, hx, hna⟩
  have hr := oldRightFollower_of_physicalFacts hPhys hp
  refine ⟨hr, hx, ?_⟩
  intro ha
  apply hna
  unfold B9Host.Aligned at ha ⊢
  rw [hPhys.rightFollowerLabel hr]
  exact ha

private theorem rawDanger_reverse_of_physicalFacts
    {l r : Cell psi kappa tau}
    {p : Phys psi kappa tau × Phys psi kappa tau}
    (hPhys : PhysicalHostRiskFacts l r p) :
    RawDanger p.2 p.1 → RawDanger (base r) (base l) := by
  rintro ⟨hpr, hpl, hna⟩
  have hr := oldRightFollower_of_physicalFacts hPhys hpr
  have hl := oldLeftFollower_of_physicalFacts hPhys hpl
  refine ⟨hr, hl, ?_⟩
  intro ha
  apply hna
  unfold B9Host.Aligned at ha ⊢
  rw [hPhys.rightFollowerLabel hr, hPhys.leftFollowerLabel hl]
  exact ha

private theorem pairRisk_of_controllerFrames_physicalFacts
    (hpsi : 0 < psi)
    (l r l' r' : Cell psi kappa tau)
    (p : Phys psi kappa tau × Phys psi kappa tau)
    (hPhys : PhysicalHostRiskFacts l r p)
    (hL : CellControllerFrame l l') (hR : CellControllerFrame r r')
    (hBL : base l' = p.1) (hBR : base r' = p.2) :
    PairRiskNoRaise hpsi l r l' r' := by
  apply pairRisk_of_controllerFrames hpsi l r l' r' hL hR
  · intro x hd
    apply (localDanger_iff_raw hpsi x l).2
    have h := (localDanger_iff_raw hpsi x l').1 hd
    rw [hBL] at h
    exact rawDanger_incoming_of_physicalFacts hPhys (base x) h
  · intro hd
    apply (localDanger_iff_raw hpsi l r).2
    have h := (localDanger_iff_raw hpsi l' r').1 hd
    rw [hBL, hBR] at h
    exact rawDanger_served_of_physicalFacts hPhys h
  · intro x hd
    apply (localDanger_iff_raw hpsi r x).2
    have h := (localDanger_iff_raw hpsi r' x).1 hd
    rw [hBR] at h
    exact rawDanger_outgoing_of_physicalFacts hPhys (base x) h
  · intro hd
    apply (localDanger_iff_raw hpsi r l).2
    have h := (localDanger_iff_raw hpsi r' l').1 hd
    rw [hBR, hBL] at h
    exact rawDanger_reverse_of_physicalFacts hPhys h

private theorem rightFollowerRelabelled_false_of_physicalFacts
    (l r : Cell psi kappa tau)
    (p : Phys psi kappa tau × Phys psi kappa tau)
    (hPhys : PhysicalHostRiskFacts l r p) :
    rightFollowerRelabelledV7 r.carrier
      (setPhysical r.carrier p.2) = false := by
  unfold rightFollowerRelabelledV7
  simp only [decide_eq_false_iff_not]
  rintro ⟨_, _, hlead, hlabel⟩
  have hlead' : B9Host.leader p.2 = false := hlead
  have hlabel' : B9Host.label p.2 ≠ B9Host.label (base r) := hlabel
  cases hr : B9Host.leader (base r) with
  | false => exact hlabel' (hPhys.rightFollowerLabel hr)
  | true =>
      have ho := hPhys.rightLeader hr
      rw [hlead'] at ho
      cases ho

private theorem physicalHoldFromPhysical_frames
    (l r : Cell psi kappa tau)
    (p : Phys psi kappa tau × Phys psi kappa tau)
    (hPhys : PhysicalHostRiskFacts l r p) :
    let q := physicalHoldFromPhysical p l r
    CellControllerFrame l q.1 ∧
      CellControllerFrame r q.2 ∧
      base q.1 = p.1 ∧ base q.2 = p.2 := by
  have hrel := rightFollowerRelabelled_false_of_physicalFacts l r p hPhys
  unfold physicalHoldFromPhysical
  dsimp only
  rw [hrel]
  exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl⟩

private theorem pairRisk_trans
    (hpsi : 0 < psi)
    {l r a b c d : Cell psi kappa tau}
    (h₁ : PairRiskNoRaise hpsi l r a b)
    (h₂ : PairRiskNoRaise hpsi a b c d) :
    PairRiskNoRaise hpsi l r c d := by
  refine ⟨Nat.le_trans h₂.ticketL h₁.ticketL,
    Nat.le_trans h₂.ticketR h₁.ticketR, ?_, ?_, ?_, ?_⟩
  · intro x
    exact Nat.le_trans (h₂.incoming x) (h₁.incoming x)
  · exact Nat.le_trans h₂.served h₁.served
  · intro x
    exact Nat.le_trans (h₂.outgoing x) (h₁.outgoing x)
  · exact Nat.le_trans h₂.reverse h₁.reverse

private theorem hostFence_iff_controllerFrame
    {u v : Cell psi kappa tau} (hF : CellControllerFrame u v) :
    HostFenceShapeV7 v ↔ HostFenceShapeV7 u := by
  simp only [HostFenceShapeV7, hF.role_eq, hF.pending_eq, hF.ticket_eq]

private theorem clearTickets_pairRisk
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hL : ¬ HostFenceShapeV7 l) (hR : ¬ HostFenceShapeV7 r) :
    PairRiskNoRaise hpsi l r (clearTicketV6 l) (clearTicketV6 r) := by
  classical
  risk_prepare
  all_goals
    simp only [BadTicket, BadBacking, Pending, Hole, PairCovered,
      HostFenceShapeV7, ReservedFrontHoldGuard, PendingOwnerHoldShapeV7,
      localDanger_iff_raw, RawDanger, B9SpliceTableHost.base,
      carrier_clearTicketV6, ticket_clearTicketV6] at *
  all_goals simp_all

private theorem ordinaryHostWriteFromPhysical_eq_clear_hold
    (l r : Cell psi kappa tau)
    (p : Phys psi kappa tau × Phys psi kappa tau)
    (hPhys : PhysicalHostRiskFacts l r p) :
    ordinaryHostWriteFromPhysical p l r =
      (clearTicketV6 (physicalHoldFromPhysical p l r).1,
       clearTicketV6 (physicalHoldFromPhysical p l r).2) := by
  have hrel := rightFollowerRelabelled_false_of_physicalFacts l r p hPhys
  unfold ordinaryHostWriteFromPhysical physicalHoldFromPhysical
  dsimp only
  rw [hrel]
  rfl

private theorem base_setControl_rate
    (c : R1AgentState psi kappa tau) (r : SpliceRole) (p : Bool) :
    (setControl c r p).splice.base = c.splice.base := rfl

private theorem fenceRight_pairRisk
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hRole : role r.carrier = .predecessorArmed)
    (hPend : r.carrier.repairPending = false) :
    PairRiskNoRaise hpsi l r l (fenceV6 r) := by
  classical
  risk_prepare
  all_goals
    simp only [BadTicket, BadBacking, Pending, Hole, PairCovered,
      HostFenceShapeV7, ReservedFrontHoldGuard, PendingOwnerHoldShapeV7,
      localDanger_iff_raw, RawDanger, B9SpliceTableHost.base,
      fenceV6, carrier_setTicketV6, ticket_setTicketV6,
      role_setControlV6, pending_setControlV6,
      base_setControl_rate] at *
  all_goals simp_all
  all_goals
    try rename_i hx
    first
      | exact ⟨hx.1.2.1, hx.1.2.2⟩
      | (intro hNone
         cases hp : l.carrier.repairPending <;> simp_all)

private theorem ordinaryHost_pairRisk
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hNG : ¬ Garbage hpsi l r)
    (hFall : OrdinaryLeafFallthrough l r)
    (p : Phys psi kappa tau × Phys psi kappa tau)
    (hPhys : PhysicalHostRiskFacts l r p)
    (q : Cell psi kappa tau × Cell psi kappa tau)
    (hq : q = ordinaryHostWriteFromPhysical p l r) :
    PairRiskNoRaise hpsi l r q.1 q.2 := by
  subst q
  obtain ⟨hL, hR, hBL, hBR⟩ :=
    physicalHoldFromPhysical_frames l r p hPhys
  have hHold : PairRiskNoRaise hpsi l r
      (physicalHoldFromPhysical p l r).1
      (physicalHoldFromPhysical p l r).2 :=
    pairRisk_of_controllerFrames_physicalFacts hpsi l r
      (physicalHoldFromPhysical p l r).1
      (physicalHoldFromPhysical p l r).2
      p hPhys hL hR hBL hBR
  have hnL : ¬ HostFenceShapeV7 (physicalHoldFromPhysical p l r).1 := by
    intro h
    exact hFall.noLeftFence ((hostFence_iff_controllerFrame hL).mp h)
  have hnR : ¬ HostFenceShapeV7 (physicalHoldFromPhysical p l r).2 := by
    intro h
    exact hFall.noRightFence ((hostFence_iff_controllerFrame hR).mp h)
  have hClear := clearTickets_pairRisk hpsi
    (physicalHoldFromPhysical p l r).1
    (physicalHoldFromPhysical p l r).2 hnL hnR
  rw [ordinaryHostWriteFromPhysical_eq_clear_hold l r p hPhys]
  exact pairRisk_trans hpsi hHold hClear






private theorem physicalHold_pairRisk
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hNG : ¬ Garbage hpsi l r)
    (hOwner : ¬ (role l.carrier = .predecessorArmed ∧
      l.carrier.repairPending = true))
    (hVR : ¬ VictimRightScrubGuardV6 r)
    (hFR : ¬ FrontRightScrubGuardV6 r)
    (hMR : ¬ MalformedRightPendingGuardV6 r)
    (hRP : role r.carrier ≠ .predecessorArmed)
    (p : Phys psi kappa tau × Phys psi kappa tau)
    (hPhys : PhysicalHostRiskFacts l r p)
    (q : Cell psi kappa tau × Cell psi kappa tau)
    (hq : q = physicalHoldFromPhysical p l r) :
    PairRiskNoRaise hpsi l r q.1 q.2 := by
  subst q
  obtain ⟨hL, hR, hBL, hBR⟩ :=
    physicalHoldFromPhysical_frames l r p hPhys
  exact pairRisk_of_controllerFrames_physicalFacts hpsi l r
    (physicalHoldFromPhysical p l r).1
    (physicalHoldFromPhysical p l r).2
    p hPhys hL hR hBL hBR




-- CONTINUATION OF THE COMPLETE PARTS 1-2 REPLACEMENT.
private theorem physicalFence_pairRisk
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hNG : ¬ Garbage hpsi l r)
    (hOwner : ¬ (role l.carrier = .predecessorArmed ∧
      l.carrier.repairPending = true))
    (hVR : ¬ VictimRightScrubGuardV6 r)
    (hFR : ¬ FrontRightScrubGuardV6 r)
    (hMR : ¬ MalformedRightPendingGuardV6 r)
    (hRP : role r.carrier = .predecessorArmed)
    (hPend : ¬ r.carrier.repairPending = true)
    (p : Phys psi kappa tau × Phys psi kappa tau)
    (hPhys : PhysicalHostRiskFacts l r p)
    (q : Cell psi kappa tau × Cell psi kappa tau)
    (hq : q = physicalHoldFromPhysical p l r) :
    PairRiskNoRaise hpsi l r q.1 (fenceV6 q.2) := by
  subst q
  obtain ⟨hL, hR, hBL, hBR⟩ :=
    physicalHoldFromPhysical_frames l r p hPhys
  have hHold : PairRiskNoRaise hpsi l r
      (physicalHoldFromPhysical p l r).1
      (physicalHoldFromPhysical p l r).2 :=
    pairRisk_of_controllerFrames_physicalFacts hpsi l r
      (physicalHoldFromPhysical p l r).1
      (physicalHoldFromPhysical p l r).2
      p hPhys hL hR hBL hBR
  have hPend0 : r.carrier.repairPending = false := by
    cases hp : r.carrier.repairPending
    · rfl
    · exact False.elim (hPend hp)
  have hRole' :
      role (physicalHoldFromPhysical p l r).2.carrier = .predecessorArmed :=
    hR.role_eq.trans hRP
  have hPend' :
      (physicalHoldFromPhysical p l r).2.carrier.repairPending = false :=
    hR.pending_eq.trans hPend0
  have hFence := fenceRight_pairRisk hpsi
    (physicalHoldFromPhysical p l r).1
    (physicalHoldFromPhysical p l r).2 hRole' hPend'
  exact pairRisk_trans hpsi hHold hFence





/-- Top-level physical DELETE.  Its controller shape covers every new physical
hazard, so no whole host-tree expansion is needed. -/
private theorem delete_pairRisk
    (host : HostRow (Phys psi kappa tau))
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hDel : B9SpliceTableHost.ldc host l.carrier r.carrier)
    (hRF : ¬ ReservedFrontHoldGuard l.carrier)
    (hNG : ¬ Garbage hpsi l r) :
    PairRiskNoRaise hpsi l r
      (B9SpliceTableHost.deleteWriteH host l r).1
      (B9SpliceTableHost.deleteWriteH host l r).2 := by
  classical
  risk_prepare
  all_goals risk_simp <;> omega


macro "risk_finish_concrete_leaf" : tactic =>
  `(tactic|
    (risk_prepare
     all_goals try
       simp only [BadTicket, BadBacking, Pending, Hole, PairCovered,
         HostFenceShapeV7, ReservedFrontHoldGuard, PendingOwnerHoldShapeV7,
         localDanger_iff_raw, RawDanger, B9SpliceTableHost.base,
         VictimRightScrubGuardV6, FrontRightScrubGuardV6,
         MalformedRightPendingGuardV6,
         fenceV6, settleV6, clearControlV6,
         setTicketV6, setControlV6, withCarrierClearTicketV6,
         setControl, role] at *
     all_goals try simp only [ind, if_pos, if_neg] at *
     all_goals first
       | simp_all
       | omega))



private theorem holdRepair_pairRisk
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hRF : ReservedFrontHoldGuard l.carrier)
    (hNG : ¬ Garbage hpsi l r) :
    PairRiskNoRaise hpsi l r
      (B9SpliceTableV10j.holdRepairV10j l r).1
      (B9SpliceTableV10j.holdRepairV10j l r).2 := by
  classical
  have hw := B9SpliceTableV10j.holdRepairV10j.eq_1 l r
  rw [hw]
  by_cases h1 : ReservedFrontHoldGuard r.carrier
  · rw [if_pos h1]
    risk_finish_concrete_leaf
  · rw [if_neg h1]
    by_cases h2 : role r.carrier = .predecessorArmed ∧
        r.carrier.repairPending = true
    · rw [if_pos h2]
      risk_finish_concrete_leaf
    · rw [if_neg h2]
      by_cases h3 : role r.carrier = .victimArmed ∧
          r.carrier.repairPending = true
      · rw [if_pos h3]
        risk_finish_concrete_leaf
      · rw [if_neg h3]
        by_cases h4 : VictimRightScrubGuardV6 r ∨
            FrontRightScrubGuardV6 r ∨
            MalformedRightPendingGuardV6 r
        · rw [if_pos h4]
          rcases h4 with h4 | h4 | h4 <;> risk_finish_concrete_leaf
        · rw [if_neg h4]
          exact pairRisk_refl hpsi l r





/-- V10b handoff leaf. -/
private theorem handoff_pairRisk
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hG : HostFenceAdvanceGuardV10b hpsi l r)
    (hNG : ¬ Garbage hpsi l r) :
    PairRiskNoRaise hpsi l r
      (hostFenceHandoffWriteV10b l r).1
      (hostFenceHandoffWriteV10b l r).2 := by
  classical
  risk_prepare
  all_goals risk_simp <;> omega


/-- V9 busy-front repair leaf. -/
private theorem busyFront_pairRisk
    (hpsi : 0 < psi) (l r : Cell psi kappa tau)
    (hG : HostFenceBusyFrontGuardV9 hpsi l r)
    (hNG : ¬ Garbage hpsi l r) :
    PairRiskNoRaise hpsi l r
      (hostFenceBusyFrontRepairWriteV9 hpsi l r).1
      (hostFenceBusyFrontRepairWriteV9 hpsi l r).2 := by
  classical
  risk_prepare
  all_goals risk_simp <;> omega

end PairRiskCensus

end B9ControllerRecovery

import Leader.Wu.Safety.PermitRepairLegitKernel
import Leader.Wu.Birth.ShortDoneTerminalCheckInputSources
import Leader.Wu.Elimination.NearestPeaceful


namespace R1CandidateKernel


open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneCuts BirthShortDoneTerminalHost
  PPLLNoCheckBirthConditionTwoGeometry


set_option autoImplicit false
set_option synthInstance.maxSize 4096


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  Fin n → ExpiringAgentState psi kappa tau


abbrev AP (psi : Nat) :=
  AuthorizedAgentState psi × AuthorizedAgentState psi


def raw (u : ExpiringAgentState psi kappa tau) : AgentState psi :=
  u.core.core.erase


/-- One unrolled lap, not a strict-sub-lap second-leader segment.
The incoming root edge need not be successor-aligned. -/
def RootedLap (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (root : Fin n) : Prop :=
  (C root).core.core.leader = true ∧
  (∀ i : Fin n, (C i).core.core.leader = true → i = root) ∧
  (C root).core.core.label = ⟨0, hpsi⟩ ∧
  (∀ d : Fin n, (C (cwPos ring root d.val)).core.core.label =
    ⟨d.val % psi, Nat.mod_lt _ hpsi⟩) ∧
  (∀ e : Fin n, ring.rightNeighbor e ≠ root →
    (C (ring.rightNeighbor e)).core.core.label =
      ⟨((C e).core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) ∧
  (C root).core.core.shield = true ∧
  (C root).core.core.signal_B = 0


/-- Finite form of nearest-leader K2 support, with the endpoint included
in the zero-signal interval and excluded from the follower interval. -/
def SupportFinite (ring : DirectedRing n) (C : FC n psi kappa tau)
    (start d : Fin n) : Prop :=
  (C (cwPos ring start d.val)).core.core.leader = true ∧
  (C (cwPos ring start d.val)).core.core.shield = true ∧
  (∀ k : Fin n, k.val ≤ d.val →
    (C (cwPos ring start k.val)).core.core.signal_B = 0) ∧
  (∀ k : Fin n, k.val < d.val →
    (C (cwPos ring start k.val)).core.core.leader = false)


def K2PeacefulFinite (ring : DirectedRing n)
    (C : FC n psi kappa tau) : Prop :=
  ∀ i : Fin n, (C i).core.core.bullet = 2 →
    ∃ d : Fin n, SupportFinite ring C i d


/-- ID of a complete group in the unrolled lap. Group zero is excluded
from the positive-group peak condition below. -/
def lapID (ring : DirectedRing n) (C : FC n psi kappa tau)
    (root : Fin n) (g : Nat) : Nat :=
  groupID ring.hn (fun i => raw (C i)) (cwPos ring root (g * psi))


def PositivePeak (ring : DirectedRing n) (C : FC n psi kappa tau)
    (root : Fin n) : Prop :=
  ∀ a b : Fin n, 0 < a.val → a.val < b.val →
    (b.val + 1) * psi ≤ n →
    lapID ring C root a.val = lapID ring C root b.val →
    ∃ k : Fin n, a.val < k.val ∧ k.val < b.val ∧
      lapID ring C root a.val < lapID ring C root k.val


/-- The strong quiet branch: no comparison state, payload, control,
cleanup connector, or lottery residue. This does not freeze WAIT. -/
def RawQuiet (u : AgentState psi) : Prop :=
  u.state = .none ∧ u.path = .bot ∧ u.path2 = none ∧
  u.path4 = none ∧ u.path5 = none ∧ u.p = false ∧ u.p_carry = false


def AuthQuiet (u : AuthorizedAgentState psi) : Prop :=
  RawQuiet u.core ∧ u.path0Crossed = false


/-- L16: exclude already-present writers as well as fresh generation.
last/echo/carry flags are not silently declared immutable. -/
def WriterDormant (u : AgentState psi) : Prop :=
  u.path3 = none ∧ u.write_state = .none ∧
    u.write = .none ∧ u.gen_ws = false


def prepared (hpsi : 0 < psi)
    (u : ExpiringAgentState psi kappa tau) : AuthorizedAgentState psi :=
  normalizeDeletion (prepareExpiringDisposal hpsi u).core.erase


/-- These are actual ordinary-branch cuts, never synthetic records. -/
def checkInput (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : AP psi :=
  doneBeforeCheckEntryWidth hpsi (by decide : 0 < 2) h2 kappa
    (prepared hpsi l) (prepared hpsi r)


def checkOutput (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : AP psi :=
  doneThroughCheckEntryWidth hpsi (by decide : 0 < 2) h2 kappa
    (prepared hpsi l) (prepared hpsi r)


def writerInput (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : AP psi :=
  let c := checkOutput hpsi h2 l r
  beforeWriteWidth hpsi (by decide : 0 < 2) h2
    (BirthCheckPermitRepair.permitFix c.1) c.2


def checkedSuffix (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : AP psi :=
  let c := checkOutput hpsi h2 l r
  afterCheckMetadataWidth hpsi (by decide : 0 < 2) h2
    (BirthCheckPermitRepair.permitFix c.1) c.2


def PreparedRuler (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  (prepared hpsi r).core.leader = false →
    (prepared hpsi r).core.label =
      ⟨((prepared hpsi l).core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩


/-- No delayed action-3/4 disposal or active deletion in this branch.
There is deliberately no lower bound on the stall credit. -/
def LocalQuiet (hpsi : 0 < psi)
    (u : ExpiringAgentState psi kappa tau) : Prop :=
  AuthQuiet u.core.erase ∧ WriterDormant (raw u) ∧
  pendingTerminalDisposal hpsi (raw u) = false ∧
  deletionActive (prepared hpsi u) = false


/-- Literal class E, before permitFix. Not a final-output event. -/
def ClassE (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  deletionActive (prepared hpsi l) = false ∧
  deletionActive (prepared hpsi r) = false ∧
  (checkOutput hpsi h2 l r).1.core.state = .equal ∧
  (checkOutput hpsi h2 l r).1.path0Crossed = true


/-- Finite diagnostic obligations at the literal cuts. These are
current-state tests, NOT conclusions about a future scheduler word. -/
def EdgeSafe (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  PreparedRuler hpsi l r ∧
  AuthQuiet (checkInput hpsi h2 l r).1 ∧
  AuthQuiet (checkInput hpsi h2 l r).2 ∧
  (checkOutput hpsi h2 l r).1.core.state ≠ .equal ∧
  WriterDormant (writerInput hpsi h2 l r).1.core ∧
  WriterDormant (writerInput hpsi h2 l r).2.core ∧
  ((checkedSuffix hpsi h2 l r).1.core.bit =
      (writerInput hpsi h2 l r).1.core.bit ∧
    (checkedSuffix hpsi h2 l r).2.core.bit =
      (writerInput hpsi h2 l r).2.core.bit) ∧
  (let q := BirthCheckPermitRepair.expiring
      hpsi (by decide : 0 < 2) h2 l r
   AuthQuiet q.1.core.erase ∧ AuthQuiet q.2.core.erase)


def CandR1At (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (root : Fin n) : Prop :=
  RootedLap hpsi ring C root ∧ K2PeacefulFinite ring C ∧
  PositivePeak ring C root ∧ (∀ i : Fin n, LocalQuiet hpsi (C i)) ∧
  (∀ e : Fin n, EdgeSafe hpsi h2 (C e) (C (ring.rightNeighbor e)))


def CandR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  ∃ root : Fin n, CandR1At hpsi h2 ring C root


instance candR1AtDecidable (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (root : Fin n) :
    Decidable (CandR1At hpsi h2 ring C root) := by
  unfold CandR1At RootedLap K2PeacefulFinite SupportFinite PositivePeak
    LocalQuiet EdgeSafe PreparedRuler AuthQuiet RawQuiet WriterDormant
  infer_instance


instance candR1Decidable (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) :
    Decidable (CandR1 hpsi h2 ring C) := by
  unfold CandR1
  infer_instance
-- END PART 1
/-- Unlike equality of final leader counts, this equality is at the
actual normalized metadata cut used by the event. It is restricted to
the no-equal branch; no all-row/full-state agreement is claimed. -/
private theorem metadata_eq_of_no_equal
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (h : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r) :
    R1LegitKernel.metadataR1 hpsi h2 l r =
      BirthShortDoneTerminalHost.metadata hpsi (by decide : 0 < 2) h2 l r := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  have ha := BirthCheckPermitRepairAgree.authorized_eq
    hpsi h2 pl.core.erase pr.core.erase h
  have hb : BirthCheckPermitRepair.bounded
      hpsi (by decide : 0 < 2) h2 pl.core pr.core =
      doneMetadataBoundedEntryWidth
        hpsi (by decide : 0 < 2) h2 pl.core pr.core := by
    unfold BirthCheckPermitRepair.bounded doneMetadataBoundedEntryWidth
    dsimp only
    exact BirthCheckPermitRepairAgree.reify_congr ha
      (BirthCheckPermitRepair.authorized_domain
        hpsi (by decide : 0 < 2) h2 pl.core.erase pr.core.erase
        pl.core.core.erase_inProtocolDomain pr.core.core.erase_inProtocolDomain)
      (doneMetadataAuthorizedEntryWidth_domain
        hpsi (by decide : 0 < 2) h2 pl.core.erase pr.core.erase
        pl.core.core.erase_inProtocolDomain pr.core.core.erase_inProtocolDomain)
  have he : BirthCheckPermitRepair.expiring
      hpsi (by decide : 0 < 2) h2 l r =
      doneMetadataEntryWidth hpsi (by decide : 0 < 2) h2 l r := by
    unfold BirthCheckPermitRepair.expiring doneMetadataEntryWidth
    dsimp only
    rw [hb]
  unfold R1LegitKernel.metadataR1 BirthShortDoneTerminalHost.metadata
  rw [he]


private theorem event_eq_of_no_equal
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (h : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r) :
    R1LegitKernel.birthEventR1 hpsi h2 l r =
      BirthShortDoneTerminalObserver.birthEvent
        hpsi (by decide : 0 < 2) h2 l r := by
  unfold R1LegitKernel.birthEventR1 BirthShortDoneTerminalObserver.birthEvent
  rw [metadata_eq_of_no_equal hpsi h2 l r h]


/-- Keep the contradiction abstract: l and r are records, not row terms. -/
private theorem ruler_excludes_pprime
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi)
    (hRuler : r.core.leader = false →
      r.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    ¬ BirthShortDoneTerminalBirthSources.PPrimeBarrierBirthGuard hpsi l r := by
  intro hb
  exact hb.2.2.2.2 (hRuler hb.2.1)


/-- Eliminate CHECK input alternatives before substituting a computed cut. -/
private theorem quiet_right_excludes_check
    (hpsi : 0 < psi) (b : AP psi) (hq : AuthQuiet b.2) :
    ¬ BirthShortDoneTerminalCheckInputSources.ActualCheckBirthInput hpsi b := by
  intro hb
  have hf : BirthShortDoneTerminalCheckInputSources.CheckFollowerBirthInput
      hpsi b.1.core b.2.core := hb.2.2.2.2.2.2
  rcases hf.2.2 with heq | ⟨lab, bit, hpath, _⟩
  · have bad : MainState.none = MainState.equal := hq.1.1.symm.trans heq
    cases bad
  · have bad : PathInfo.bot = PathInfo.some lab bit :=
      hq.1.2.1.symm.trans hpath
    cases bad


section CutBoundaryProof


-- These attributes affect elaboration only and end with this section.
-- Explicit simp lists below unfold aliases, never execute a row stage.
attribute [local irreducible]
  prepared checkInput checkOutput
  BirthShortDoneTerminalEntryCut.doneBeforeCheckEntryWidth
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthCheckPermitRepair.expiring
  R1LegitKernel.birthEventR1
  BirthShortDoneTerminalObserver.birthEvent


/-- Source exclusion, rather than a stored no-birth-event field. -/
theorem edgeSafe_no_birth (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (h : EdgeSafe hpsi h2 l r) :
    R1LegitKernel.birthEventR1 hpsi h2 l r = false := by
  have hP : ¬ BirthShortDoneTerminalBirthSources.PPrimeBarrierBirthGuard
      hpsi (prepared hpsi l) (prepared hpsi r) :=
    ruler_excludes_pprime hpsi (prepared hpsi l) (prepared hpsi r) h.1
  have hQ : ¬ BirthShortDoneTerminalCheckInputSources.ActualCheckBirthInput
      hpsi (checkInput hpsi h2 l r) :=
    quiet_right_excludes_check hpsi (checkInput hpsi h2 l r) h.2.2.1
  have hn : BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2 l r = false := by
    apply BirthShortDoneTerminalCheckInputSources.birthEvent_false_of_no_input_sources
      hpsi (by decide : 0 < 2) h2 l r
    · simpa only [prepared] using hP
    · simpa only [checkInput, prepared] using hQ
  have hcut : BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r := by
    simpa only [BirthCheckPermitRepairAgree.NoEqualOutcome,
      BirthCheckPermitRepairAgree.AuthNoEqual, checkOutput, prepared]
      using h.2.2.2.1
  exact (event_eq_of_no_equal hpsi h2 l r hcut).trans hn


end CutBoundaryProof


/-- The current unique leader output is exactly the geometry projection. -/
theorem candR1_unique (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) :
    UniqueLeaderOutput (R1LegitKernel.protocolR1 hpsi h2 kappa tau)
      n C R1LegitKernel.isLeaderR1 := by
  rcases hC with ⟨root, hG, _, _, _, _⟩
  exact ⟨root, hG.1, hG.2.1⟩


/-- Every physical barrier is on an edge entering the root leader. -/
theorem candR1_no_free_barrier (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) :
    noFreeBarrier hpsi ring (fun i => raw (C i)) := by
  rcases hC with ⟨root, hG, _, _, _, _⟩
  unfold noFreeBarrier
  intro e
  dsimp only
  intro hb
  change (C (ring.rightNeighbor e)).core.core.leader = true
  by_cases hr : ring.rightNeighbor e = root
  · rw [hr]
    exact hG.1
  · exact (hb (hG.2.2.2.2.1 e hr)).elim


/-- The finite field really supplies the existing K2 predicate. -/
theorem candR1_nearest_peaceful (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) :
    K2PeacefulGlobal.NearestPeaceful ring (ExpiringK2Projection.observe C) := by
  rcases hC with ⟨_, _, hPeace, _, _, _⟩
  intro i hb
  obtain ⟨d, hl, hs, hz, hf⟩ := hPeace i hb
  refine ⟨d.val, ?_⟩
  refine {
    distance_lt := d.isLt
    target_leader := hl
    target_shield := hs
    signal_zero := ?_
    before_follower := ?_
  }
  · intro k hk
    exact hz ⟨k, Nat.lt_of_le_of_lt hk d.isLt⟩ hk
  · intro k hk
    exact hf ⟨k, Nat.lt_trans hk d.isLt⟩ hk


/-- Stronger than excluding a currently true permit at CHECK alone. -/
theorem candR1_not_classE (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e : Fin n) :
    ¬ ClassE hpsi h2 (C e) (C (ring.rightNeighbor e)) := by
  rcases hC with ⟨_, _, _, _, _, hRows⟩
  have hNE := (hRows e).2.2.2.1
  intro hE
  exact hNE hE.2.2.1


/-- The required single-row event exclusion on the actual R1 carrier. -/
theorem candR1_no_birth_row (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e : Fin n) :
    R1LegitKernel.birthEventR1 hpsi h2
      (C e) (C (ring.rightNeighbor e)) = false := by
  rcases hC with ⟨_, _, _, _, _, hRows⟩
  exact edgeSafe_no_birth hpsi h2 _ _ (hRows e)


/-- Apply the physical lemma in its valid direction: after establishing
no metadata birth, a newly observed leader was already a leader. -/
theorem candR1_no_new_leader (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e i : Fin n)
    (hi : (BirthCheckPermitRepairLeaf.step1
      hpsi h2 ring C e i).core.core.leader = true) :
    (C i).core.core.leader = true := by
  exact R1LegitKernel.step1_no_new_leader_of_no_birth
    hpsi h2 ring C e (candR1_no_birth_row hpsi h2 ring C hC e) i hi


/-- No claim about survival of the unique leader is hidden here. -/
theorem candR1_step_at_most_one (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e i j : Fin n)
    (hi : (BirthCheckPermitRepairLeaf.step1
      hpsi h2 ring C e i).core.core.leader = true)
    (hj : (BirthCheckPermitRepairLeaf.step1
      hpsi h2 ring C e j).core.core.leader = true) : i = j := by
  obtain ⟨root, _, honly⟩ := candR1_unique hpsi h2 ring C hC
  exact (honly i (candR1_no_new_leader hpsi h2 ring C hC e i hi)).trans
    (honly j (candR1_no_new_leader hpsi h2 ring C hC e j hj)).symm
-- END PART 2
/-- Executable candidate test; the proposition itself is decidable. -/
def candR1B (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Bool :=
  decide (CandR1 hpsi h2 ring C)


theorem candR1B_iff (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) :
    candR1B hpsi h2 ring C = true ↔ CandR1 hpsi h2 ring C := by
  simp only [candR1B, decide_eq_true_eq]


theorem witnessRing : DirectedRing 9 := ⟨by decide⟩


/-- Complete bounded records. Positive groups have IDs 000 and 001.
Stall zero exercises the actual zero-credit expiry branch. -/
def witness (i : Fin 9) : ExpiringAgentState 3 3 48 :=
  let b : BoundedAgentState 3 3 := {
    leader := decide (i.val = 0)
    probe := false
    phase := false
    bit := decide (i.val = 8)
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := decide (i.val = 0)
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false
  }
  ⟨⟨b, false⟩, 0⟩


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem witness_mem :
    CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
      witnessRing witness := by
  decide


theorem witness_bool :
    candR1B (by decide : 0 < 3) (by decide : 2 ≤ 3)
      witnessRing witness = true :=
  (candR1B_iff (by decide) (by decide) witnessRing witness).2 witness_mem


theorem witness_no_birth (e : Fin 9) :
    R1LegitKernel.birthEventR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
      (witness e) (witness (witnessRing.rightNeighbor e)) = false :=
  candR1_no_birth_row (by decide) (by decide)
    witnessRing witness witness_mem e


/- PLAN
Intended closure target, NOT a declaration proved by this file:
  candR1_closed :
    PopulationProtocol.ClosedPred
      (R1LegitKernel.protocolR1 hpsi h2 kappa tau) ring
      (CandR1 hpsi h2 ring)


This exact quiet candidate is intentionally falsifiable. A reachable row
which creates legitimate comparison/writer material may leave it, even
without changing the output. Then widen the structural predicate; do not
make closure a stored field or replace it by an all-futures definition.


Rule obligations for either this predicate or its live-route extension:
1. Disposal preparation and responder-delete/initiator-hold priorities:
   classify residual controls and permits on adjacent edges; derive the
   prepared ruler from the raw rooted ruler rather than retaining that
   redundant cut check. Do not silently bypass active disposal.
2. P-prime and normalizeLeader: retain the same root and all follower
   successor labels; allow the single closing defect entering the root.
   No psi-divides-n assumption and no second sub-lap leader witness.
3. WAIT/GEN: new carriers need real generation/source/bit coordinates.
   Current emptiness does not imply permanent emptiness or no new permits.
4. CLEAN/ELIMINATE/DONE: prove source-compatible joins, disposal of invalid
   remnants, and leader/reset-wall behavior under every scheduled edge.
5. CHECK/permitFix: preserve certificates for retained equal states even
   after consumption; block stale terminal equality as well as class E.
   A larger candidate should allow harmless equality with a justified
   route obstruction, not merely remove the checkOutput-not-equal test.
6. DISAPPEAR/COMPARE/SUPPRESS: preserve crossing/current-ID information,
   handle genuine new permits, and tolerate out-of-order reset/echo work.
7. WRITE: cover carried path3 and all active actions, not only the
   leader-guarded generator. Preserve PositivePeak and each live route's
   current/reference ID agreement, or dispose dependencies BEFORE the
   dangerous CHECK/write. Derive the stored one-row bit-frame test.
8. Expiry: prove the structural classification through the actual R1
   progress/decrement/zero-credit branches. Positive credit is not a
   permanent invariant. Derive the stored expiry-neutrality checks.
9. Final K2: combine the exact R1 no-birth observer with nearest-leader
   peacefulness to prove root survival and physical safety preservation;
   then reconstruct all other fields on the actual successor.
10. Final B9+R1: establish compatibility with its real stutter/relabel/
    physical services. Bare-host facts do not establish composed closure.


The old R1LegitKernel also carries literal label-sensitive OutputLegit.
NearestPeaceful at the singleton K2 observation does not silently imply
that old literal bullet clause on arbitrary physical labels. A transfer
to that particular kernel needs this additional bridge, or an explicitly
named physical-safe kernel. No CandR1-to-LegitR1 theorem is asserted here.


Nonvacuity of the finite quiet candidate is not an entrance theorem.
A useful terminal invariant must include the live-route cases that its
own GEN/WRITE stages produce and prove all of their joins and updates.
-/


end R1CandidateKernel


#print axioms R1CandidateKernel.edgeSafe_no_birth
#print axioms R1CandidateKernel.candR1_unique
#print axioms R1CandidateKernel.candR1_no_birth_row
#print axioms R1CandidateKernel.candR1_no_new_leader
#print axioms R1CandidateKernel.candR1_nearest_peaceful
#print axioms R1CandidateKernel.witness_mem
-- END PART 3

import Leader.Wu.WriteSeq.StationaryWrite
import Leader.Wu.WallSweep.Repair
import Leader.Wu.Elimination.SinkBoundedKernel

/-!
# Domain closure and actual authorized stationary WRITE

The bounded constructors use the established numeric domain and erasure maps.
Authorization is the existing fail-closed reconciliation applied to the real
stationary output. No post-hoc physical field restoration occurs.
-/

namespace BirthStationaryWrite

open PPLL PPLLRepair PPLLDomain PPLLWriteIncrementGate
open PPLLAuthorizedComparisonRepair PPLLWallSweepRepair
open PPLLComparisonHistory PPLLNoCheckBirthConditionTwoFrames

set_option autoImplicit false

variable {n ψ κ : Nat}

attribute [local irreducible] writeSeqIncrementGate

def swDomainPair (q : AgentState ψ × AgentState ψ) :=
  ((q.1.count, PayloadView.ofState q.1), (q.2.count, PayloadView.ofState q.2))

theorem swDomainOfFrame (q : AgentState ψ × AgentState ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ)
    (he : swDomainPair q = swDomainPair (l, r)) :
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hcl := congrArg (fun p => p.1.1) he
  have hpl := congrArg (fun p => p.1.2) he
  have hcr := congrArg (fun p => p.2.1) he
  have hpr := congrArg (fun p => p.2.2) he
  change q.1.count = l.count at hcl
  change PayloadView.ofState q.1 = PayloadView.ofState l at hpl
  change q.2.count = r.count at hcr
  change PayloadView.ofState q.2 = PayloadView.ofState r at hpr
  rw [inProtocolDomain_iff] at hl hr ⊢
  rw [inProtocolDomain_iff]
  exact ⟨⟨hcl ▸ hl.1, hpl ▸ hl.2⟩, ⟨hcr ▸ hr.1, hpr ▸ hr.2⟩⟩

private theorem swGroupStartDomainFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swDomainPair (groupInfoStart hψ l r) = swDomainPair (l, r) := by
  unfold swDomainPair PayloadView.ofState groupInfoStart
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swGroupSetDomainFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swDomainPair (groupInfoSet hψ l r) = swDomainPair (l, r) := by
  unfold swDomainPair PayloadView.ofState groupInfoSet
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem swGroupUnsetDomainFrame (l r : AgentState ψ) :
    swDomainPair (groupInfoUnset l r) = swDomainPair (l, r) := by
  unfold swDomainPair PayloadView.ofState groupInfoUnset
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swGroupDomainFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swDomainPair (groupInfo hψ l r) = swDomainPair (l, r) := by
  rw [groupInfo_eq_staged]
  let q0 := groupInfoStart hψ l r
  let q1 := groupInfoSet hψ q0.1 q0.2
  exact (swGroupUnsetDomainFrame q1.1 q1.2).trans
    ((swGroupSetDomainFrame hψ q0.1 q0.2).trans (swGroupStartDomainFrame hψ l r))


private theorem swReadyDomainFrame (l r : AgentState ψ) :
    swDomainPair (writeSeqReady l r) = swDomainPair (l, r) := by
  unfold swDomainPair PayloadView.ofState writeSeqReady writeSeqSetWriteReady
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

theorem swCompareDomainFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swDomainPair (writeSeqCompare hψ l r) = swDomainPair (l, r) := by
  unfold swDomainPair PayloadView.ofState writeSeqCompare writeSeqCheckBit
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

set_option maxHeartbeats 1000000 in
theorem swCommandsDomainFrame (hψ : 0 < ψ) (l r : AgentState ψ) :
    swDomainPair (writeSeqCommands hψ l r) = swDomainPair (l, r) := by
  unfold swDomainPair PayloadView.ofState writeSeqCommands writeSeqSetWriteAct writeSeqFinalR
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))


set_option maxHeartbeats 1000000 in
/-- Generation uses the checked public payload-domain theorem; enum-only
preparation stages preserve the actual count and complete payload view. -/
theorem swThroughPrepare_domain (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (swThroughPrepare hψ l r).1.inProtocolDomain κ ∧
      (swThroughPrepare hψ l r).2.inProtocolDomain κ := by
  let q0 := groupInfo hψ l r
  have h0 := swDomainOfFrame q0 l r hl hr (swGroupDomainFrame hψ l r)
  let q1 := writeSeqGenerate hψ q0.1 q0.2
  have h1 : q1.1.inProtocolDomain κ ∧ q1.2.inProtocolDomain κ := by
    dsimp only [q1, writeSeqGenerate]
    split
    · exact gensigWriteseq_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
    · exact h0
  let q2 := writeSeqReady q1.1 q1.2
  have h2 := swDomainOfFrame q2 q1.1 q1.2 h1.1 h1.2 (swReadyDomainFrame q1.1 q1.2)
  let q3 := writeSeqCompare hψ q2.1 q2.2
  have h3 := swDomainOfFrame q3 q2.1 q2.2 h2.1 h2.2 (swCompareDomainFrame hψ q2.1 q2.2)
  exact swDomainOfFrame (writeSeqCommands hψ q3.1 q3.2) q3.1 q3.2 h3.1 h3.2
    (swCommandsDomainFrame hψ q3.1 q3.2)


attribute [local irreducible] swThroughPrepare

/-- The actual new row is closed on the existing bounded numeric domain. -/
theorem stationaryRaw_domain (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (stationaryRaw hψ l r).1.inProtocolDomain κ ∧
      (stationaryRaw hψ l r).2.inProtocolDomain κ := by
  let q := swThroughPrepare hψ l r
  have hq := swThroughPrepare_domain hψ l r hl hr
  let lg := gatePreparedIncrement q.1
  let rg := gatePreparedIncrement q.2
  have hlg := gatePreparedIncrement_inProtocolDomain q.1 hq.1
  have hrg := gatePreparedIncrement_inProtocolDomain q.2 hq.2
  let w := writeAction hψ lg rg
  have hw := writeAction_inProtocolDomain hψ lg rg hlg hrg
  exact moveWsig_inProtocolDomain hψ w.1 w.2 hw.1 hw.2


attribute [local irreducible] stationaryRaw

/-- The existing finite carrier reifies this exact domain-closed raw row. -/
def boundedRow (hψ : 0 < ψ) (l r : BoundedAgentState ψ κ) :
    BoundedAgentState ψ κ × BoundedAgentState ψ κ :=
  let q := stationaryRaw hψ l.erase r.erase
  let hq := stationaryRaw_domain hψ l.erase r.erase l.erase_inProtocolDomain r.erase_inProtocolDomain
  (BoundedAgentState.ofDomain q.1 hq.1, BoundedAgentState.ofDomain q.2 hq.2)

theorem boundedRow_erase (hψ : 0 < ψ) (l r : BoundedAgentState ψ κ) :
    ((boundedRow hψ l r).1.erase, (boundedRow hψ l r).2.erase) =
      stationaryRaw hψ l.erase r.erase := by
  simp only [boundedRow, BoundedAgentState.erase_ofDomain]


/-- Actual authorization reconciliation, with the output path compared
against its own old endpoint exactly as in the host's existing adapter. -/
def authorizedRow (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (stationaryRaw hψ) l r

theorem authorizedRow_core (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    ((authorizedRow hψ l r).1.core, (authorizedRow hψ l r).2.core) =
      stationaryRaw hψ l.core r.core := rfl

theorem authorizedRow_domain (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (authorizedRow hψ l r).1.core.inProtocolDomain κ ∧
      (authorizedRow hψ l r).2.core.inProtocolDomain κ :=
  authorizedReconcile_inProtocolDomain (stationaryRaw hψ) l r (stationaryRaw_domain hψ l.core r.core hl hr)


/-- The old and new authorized outputs agree entirely whenever the actual
old migration guard is false, including their reconciled permissions. -/
theorem authorizedRow_eq_old (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hm : ¬ (r.core.leader = true ∧ r.core.label ≠ ⟨0, hψ⟩)) :
    authorizedRow hψ l r = authorizedReconcile (writeSeqIncrementGate hψ) l r := by
  unfold authorizedRow authorizedReconcile
  rw [stationaryRaw_eq_old hψ l.core r.core hm]

theorem authorizedRow_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    swPair ((authorizedRow hψ l r).1.core, (authorizedRow hψ l r).2.core) = swPair (l.core, r.core) :=
  stationaryRaw_frame hψ l.core r.core


/-- Arbitrary stale permissions are reconciled, rather than silently retained. -/
theorem authorizedRow_permits (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (authorizedRow hψ l r).1.path0Crossed = normalizePermit l.core l.path0Crossed ∧
      (authorizedRow hψ l r).2.path0Crossed = normalizePermit r.core r.path0Crossed := by
  have hf := stationaryRaw_comparison hψ l.core r.core
  have hl := congrArg (fun q => q.1.path) hf
  have hr := congrArg (fun q => q.2.path) hf
  change (stationaryRaw hψ l.core r.core).1.path = l.core.path at hl
  change (stationaryRaw hψ l.core r.core).2.path = r.core.path at hr
  simp only [authorizedRow, authorizedReconcile, reconcilePermit, hl, hr, if_true, normalizePermit, and_self]

theorem authorizedRow_canonical (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    AuthorizationCanonical (authorizedRow hψ l r).1 ∧
      AuthorizationCanonical (authorizedRow hψ l r).2 :=
  authorizedReconcile_canonical (stationaryRaw hψ) l r

/-- No new finite local field is introduced by the authorized row. -/
def authorizedBoundedRow (hψ : 0 < ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := authorizedRow hψ l.erase r.erase
  let hq := authorizedRow_domain hψ l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem authorizedBoundedRow_erase (hψ : 0 < ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    ((authorizedBoundedRow hψ l r).1.erase, (authorizedBoundedRow hψ l r).2.erase) =
      authorizedRow hψ l.erase r.erase := by
  simp only [authorizedBoundedRow, AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]


theorem authorizedBoundedRow_frame (hψ : 0 < ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    swPair ((authorizedBoundedRow hψ l r).1.core.erase, (authorizedBoundedRow hψ l r).2.core.erase) =
      swPair (l.core.erase, r.core.erase) := by
  have hh := congrArg (fun q => swPair (q.1.core, q.2.core)) (authorizedBoundedRow_erase hψ l r)
  exact hh.trans (authorizedRow_frame hψ l.erase r.erase)

/-- A finite protocol for this isolated writer component, on the existing
authorized carrier. The full birth/dispatcher transition is unchanged. -/
def swProtocol (hψ : 0 < ψ) (κ : Nat) : PopulationProtocol where
  Q := AuthorizedBoundedAgentState ψ κ
  Y := LeaderOutput
  transition := authorizedBoundedRow hψ
  output := fun u => AgentState.outputFn u.core.erase

def swStateCertificate (hψ : 0 < ψ) (κ : Nat) : ExhaustiveList (swProtocol hψ κ).Q :=
  authorizedBoundedAgentState ψ κ

theorem swCarrierUnchanged (hψ : 0 < ψ) (κ : Nat) :
    (swProtocol hψ κ).Q = AuthorizedBoundedAgentState ψ κ ∧
      (swStateCertificate hψ κ).values.length = (authorizedBoundedAgentState ψ κ).values.length :=
  ⟨rfl, rfl⟩

theorem swFiniteDecode (hψ : 0 < ψ) (κ : Nat) :
    Function.Surjective (swStateCertificate hψ κ).decode :=
  authorizedBoundedAgentState_decode_surjective ψ κ

/-- Raw audit protocols use the actual existing physical scheduler update. -/
def swRawProtocol (hψ : 0 < ψ) : PopulationProtocol where
  Q := AgentState ψ
  Y := LeaderOutput
  transition := stationaryRaw hψ
  output := AgentState.outputFn

def swOldRawProtocol (hψ : 0 < ψ) : PopulationProtocol where
  Q := AgentState ψ
  Y := LeaderOutput
  transition := writeSeqIncrementGate hψ
  output := AgentState.outputFn

theorem swRawStepFrame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e i : Fin n) :
    swView ((swRawProtocol hψ).step ring C e i) = swView (C i) := by
  have hf := stationaryRaw_frame hψ (C e) (C (ring.rightNeighbor e))
  unfold PopulationProtocol.step swRawProtocol
  by_cases hi : i = e
  · subst i
    simpa only [if_true, swPair] using congrArg Prod.fst hf
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa only [if_neg hi, if_true, swPair] using congrArg Prod.snd hf
    · simp only [if_neg hi, if_neg hj]


/-- Every physical position retains its original leader and protected fields
along every writer word, without a label-coherence premise. -/
theorem swRawRunFrame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (es : List (Fin n)) (i : Fin n) :
    swView (LDSinkBoundedKernel.run ((swRawProtocol hψ).step ring) C es i) = swView (C i) := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih => exact (ih _).trans (swRawStepFrame hψ ring C e i)

/-- A concrete sufficient no-migration domain, checked from current leader
bits and labels. The raw frame proves its closure under this component. -/
def swZeroLeaders (hψ : 0 < ψ) (C : Fin n → AgentState ψ) : Prop :=
  ∀ i, (C i).leader = true → (C i).label = ⟨0, hψ⟩

theorem swZeroLeaders_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : swZeroLeaders hψ C) (e : Fin n) :
    swZeroLeaders hψ ((swRawProtocol hψ).step ring C e) := by
  intro i hi
  have hf := swRawStepFrame hψ ring C e i
  have hl := congrArg Prod.fst hf
  have hb := congrArg (fun q => q.2.1) hf
  exact hb.trans (hC i (hl.symm.trans hi))

theorem swRawStepEqOld (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : swZeroLeaders hψ C) (e : Fin n) :
    (swRawProtocol hψ).step ring C e = (swOldRawProtocol hψ).step ring C e := by
  have hm : ¬ ((C (ring.rightNeighbor e)).leader = true ∧
      (C (ring.rightNeighbor e)).label ≠ ⟨0, hψ⟩) := fun hh => hh.2 (hC _ hh.1)
  exact congrArg (fun q : AgentState ψ × AgentState ψ =>
    let (l, r) := q
    fun i => if i = e then l else if i = ring.rightNeighbor e then r else C i)
    (stationaryRaw_eq_old hψ (C e) (C (ring.rightNeighbor e)) hm)

/-- Exact total-state word agreement on the produced no-migration domain;
the guard condition is preserved by the actual new row at every prefix. -/
theorem swRawRunEqOld (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : swZeroLeaders hψ C) (es : List (Fin n)) :
    LDSinkBoundedKernel.run ((swRawProtocol hψ).step ring) C es =
      LDSinkBoundedKernel.run ((swOldRawProtocol hψ).step ring) C es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    exact (ih ((swRawProtocol hψ).step ring C e) (swZeroLeaders_step hψ ring C hC e)).trans
      (congrArg (fun D : Fin n → AgentState ψ =>
        LDSinkBoundedKernel.run ((swOldRawProtocol hψ).step ring) D es)
        (swRawStepEqOld hψ ring C hC e))


/-- The existing reset/probe wall preserves the label of every existing
leader at either endpoint. Its reset clause clears probes, not leader labels. -/
theorem swLeaderResetWall_existing (hψ : 0 < ψ) (l r : AgentState ψ) :
    (l.leader = true → (pPsiLeaderResetProbeWall hψ l r).1.leader = true ∧
      (pPsiLeaderResetProbeWall hψ l r).1.label = l.label) ∧
    (r.leader = true → (pPsiLeaderResetProbeWall hψ l r).2.leader = true ∧
      (pPsiLeaderResetProbeWall hψ l r).2.label = r.label) := by
  constructor
  · intro hl
    unfold pPsiLeaderResetProbeWall pPsi
    simp only [hl, if_true, true_or]
    repeat (first | constructor | rfl | split)
  · intro hr
    unfold pPsiLeaderResetProbeWall pPsi
    simp only [hr, if_true, true_or]
    repeat (first | constructor | rfl | split)

/-- Incident reset/probe-wall interactions normalize an old leader to zero
exactly when its old label was already zero. -/
theorem swLeaderResetWall_zero_iff (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = true) :
    ((pPsiLeaderResetProbeWall hψ l r).1.label = ⟨0, hψ⟩ ↔ l.label = ⟨0, hψ⟩) ∧
      ((pPsiLeaderResetProbeWall hψ l r).2.label = ⟨0, hψ⟩ ↔ r.label = ⟨0, hψ⟩) := by
  rw [((swLeaderResetWall_existing hψ l r).1 hl).2,
    ((swLeaderResetWall_existing hψ l r).2 hr).2]
  exact ⟨Iff.rfl, Iff.rfl⟩

end BirthStationaryWrite

import Leader.Wu.WriteSeq.StationaryWritePersistent

/-!
# Finite authorized stationary persistent writer

Every numeric-domain premise is discharged for the actual successive stage
outputs. The adapter is the existing authorization reconciliation, and the
finite carrier is the existing authorized bounded state without a new field.
-/

namespace BirthStationaryWrite

open PPLL PPLLRepair PPLLDomain PPLLWriteIncrementGate
open PPLLWriteSeqPersistenceRepair PPLLAuthorizedComparisonRepair
open PPLLComparisonHistory PPLLNoCheckBirthConditionTwoFrames

set_option autoImplicit false

variable {n ψ κ : Nat}

theorem swPersistentPrepareDomain (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (writeSeqPrepareTransport hψ l r).1.inProtocolDomain κ ∧
      (writeSeqPrepareTransport hψ l r).2.inProtocolDomain κ := by
  let q0 := writeSeqReadyTransport l r
  let q1 := writeSeqCompare hψ q0.1 q0.2
  have h0 : q0.1.inProtocolDomain κ ∧ q0.2.inProtocolDomain κ :=
    ⟨transportReady_inProtocolDomain l hl, transportReady_inProtocolDomain r hr⟩
  have h1 := swDomainOfFrame q1 q0.1 q0.2 h0.1 h0.2 (swCompareDomainFrame hψ q0.1 q0.2)
  exact swDomainOfFrame (writeSeqCommands hψ q1.1 q1.2) q1.1 q1.2 h1.1 h1.2
    (swCommandsDomainFrame hψ q1.1 q1.2)

theorem swPersistentThroughPrepareDomain (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (swPersistentThroughPrepare hψ l r).1.inProtocolDomain κ ∧
      (swPersistentThroughPrepare hψ l r).2.inProtocolDomain κ := by
  let q0 := clearInputIncrementPair l r
  have h0 := clearInputIncrementPair_inProtocolDomain l r hl hr
  let q1 := groupInfo hψ q0.1 q0.2
  have h1 := swDomainOfFrame q1 q0.1 q0.2 h0.1 h0.2 (swGroupDomainFrame hψ q0.1 q0.2)
  let q2 := writeSeqGenerate hψ q1.1 q1.2
  have h2 : q2.1.inProtocolDomain κ ∧ q2.2.inProtocolDomain κ := by
    dsimp only [q2, writeSeqGenerate]
    split
    · exact gensigWriteseq_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
    · exact h1
  exact swPersistentPrepareDomain hψ q2.1 q2.2 h2.1 h2.2

attribute [local irreducible] swPersistentThroughPrepare

private theorem swPersistentOverwriteDomain (u : AgentState ψ)
    (hu : u.inProtocolDomain κ) :
    (writeActionApplyOverwrite u).inProtocolDomain κ := by
  cases hp : u.path3 with
  | none => simpa only [writeActionApplyOverwrite, hp] using hu
  | some p =>
    rcases hu with ⟨hc, h1, h2, h3, h4, h5⟩
    rw [hp] at h3
    change p.label < ψ ∧ p.bit ≤ 1 ∧ p.flag ≤ 1 at h3
    simp only [writeActionApplyOverwrite, hp]
    exact ⟨hc, h1, h2, ⟨h3.1, h3.2.1, Nat.sub_le 1 p.flag⟩, h4, h5⟩

private theorem swPersistentMoveFlipDomain (u : AgentState ψ)
    (hu : u.inProtocolDomain κ) :
    (writeActionApplyMoveFlip u).inProtocolDomain κ := by
  cases hp : u.path3 with
  | none => simpa only [writeActionApplyMoveFlip, hp] using hu
  | some p =>
    rcases hu with ⟨hc, h1, h2, h3, h4, h5⟩
    rw [hp] at h3
    change p.label < ψ ∧ p.bit ≤ 1 ∧ p.flag ≤ 1 at h3
    simp only [writeActionApplyMoveFlip, hp]
    exact ⟨hc, h1, h2, ⟨h3.1, h3.2.1, Nat.sub_le 1 p.flag⟩, h4, h5⟩

private theorem swPersistentActivateDomain (hψ : 0 < ψ) (u : AgentState ψ)
    (hu : u.inProtocolDomain κ) :
    (writeActionActivateNonempty hψ u).inProtocolDomain κ := by
  unfold writeActionActivateNonempty
  split <;> exact hu

private theorem swPersistentPropagateDomain (u : AgentState ψ) (s : WriteState)
    (hu : u.inProtocolDomain κ) :
    (writeActionPropagateState u s).inProtocolDomain κ := by
  cases s <;> exact hu

attribute [local irreducible] writeActionApplyOverwrite writeActionApplyMoveFlip
  writeActionApplyIncrementAndFlip writeActionPropagateState

private theorem swPersistentExecuteDomain (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (writeActionExecutePreservingDepart hψ l r).1.inProtocolDomain κ ∧
      (writeActionExecutePreservingDepart hψ l r).2.inProtocolDomain κ := by
  unfold writeActionExecutePreservingDepart
  split
  · let r0 := if r.write_state = .overwrite then writeActionApplyOverwrite r else r
    let r1 := if r0.write_state = .move_flip then writeActionApplyMoveFlip r0 else r0
    let r2 := if r1.write_state = .increment_group then writeActionApplyIncrementAndFlip r1 else r1
    let l0 := if r2.label ≠ ⟨0, hψ⟩ ∧ r2.write_state ≠ .none then
        writeActionPropagateState l r2.write_state else l
    have hr0 : r0.inProtocolDomain κ := by
      dsimp only [r0]
      split
      · exact swPersistentOverwriteDomain r hr
      · exact hr
    have hr1 : r1.inProtocolDomain κ := by
      dsimp only [r1]
      split
      · exact swPersistentMoveFlipDomain r0 hr0
      · exact hr0
    have hr2 : r2.inProtocolDomain κ := by
      dsimp only [r2]
      split
      · exact writeActionApplyIncrementAndFlip_inProtocolDomain r1 hr1
      · exact hr1
    have hl0 : l0.inProtocolDomain κ := by
      dsimp only [l0]
      split
      · exact swPersistentPropagateDomain l r2.write_state hl
      · exact hl
    change l0.inProtocolDomain κ ∧ ({ r2 with write_state := .depart }).inProtocolDomain κ
    exact ⟨hl0, hr2⟩
  · exact ⟨hl, hr⟩

theorem swPersistentActionDomain (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (writeActionPreservingComparison hψ l r).1.inProtocolDomain κ ∧
      (writeActionPreservingComparison hψ l r).2.inProtocolDomain κ := by
  let l0 := writeActionActivateNonempty hψ l
  let r0 := writeActionActivateNonempty hψ r
  have hl0 := swPersistentActivateDomain hψ l hl
  have hr0 := swPersistentActivateDomain hψ r hr
  change (writeActionExecutePreservingComparison hψ l0 r0).1.inProtocolDomain κ ∧
    (writeActionExecutePreservingComparison hψ l0 r0).2.inProtocolDomain κ
  unfold writeActionExecutePreservingComparison
  split
  · exact ⟨hl0, hr0⟩
  · exact swPersistentExecuteDomain hψ l0 r0 hl0 hr0

private theorem swPersistentCheckGenDomain (l r : AgentState ψ)
    (hr : r.inProtocolDomain κ) :
    (moveWsigCheckGenWs l r).inProtocolDomain κ := by
  unfold moveWsigCheckGenWs
  repeat (first | exact hr | split)

private theorem swPersistentMoveStartDomain (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (moveWsigStart l r).1.inProtocolDomain κ ∧
      (moveWsigStart l r).2.inProtocolDomain κ := by
  unfold moveWsigStart
  split
  · exact ⟨⟨hl.1, hl.2.1, hl.2.2.1, trivial, hl.2.2.2.2⟩,
      swPersistentCheckGenDomain l r hr⟩
  · exact ⟨hl, hr⟩

private theorem swPersistentMoveLastDomain (l : AgentState ψ)
    (hl : l.inProtocolDomain κ) : (moveWsigCheckLast l).inProtocolDomain κ := by
  cases hp : l.path3 with
  | none => simpa only [moveWsigCheckLast, hp] using hl
  | some p =>
    simp only [moveWsigCheckLast, hp]
    split
    · exact ⟨hl.1, hl.2.1, hl.2.2.1, trivial, hl.2.2.2.2⟩
    · exact hl

private theorem swPersistentMoveWriteDomain (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (moveWsigMoveWritePreservingNonempty l r).1.inProtocolDomain κ ∧
      (moveWsigMoveWritePreservingNonempty l r).2.inProtocolDomain κ := by
  unfold moveWsigMoveWritePreservingNonempty
  split <;> exact ⟨hl, hr⟩

private theorem swPersistentLeaderSignalDomain (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (moveWsigLeaderSignal l r).1.inProtocolDomain κ ∧
      (moveWsigLeaderSignal l r).2.inProtocolDomain κ := by
  unfold moveWsigLeaderSignal
  split <;> exact ⟨hl, hr⟩

private theorem swPersistentSignalMoveDomain (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (moveWsigSignalMove l r).1.inProtocolDomain κ ∧
      (moveWsigSignalMove l r).2.inProtocolDomain κ := by
  unfold moveWsigSignalMove
  repeat (first | exact ⟨hl, hr⟩ | split)

private theorem swPersistentEchoMoveDomain (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (moveWsigEchoMove l r).1.inProtocolDomain κ ∧
      (moveWsigEchoMove l r).2.inProtocolDomain κ := by
  unfold moveWsigEchoMove
  repeat (first | exact ⟨hl, hr⟩ | split)

theorem swPersistentMoveDomain (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (moveWsigStopAligned hψ l r).1.inProtocolDomain κ ∧
      (moveWsigStopAligned hψ l r).2.inProtocolDomain κ := by
  let q0 := moveWsigStart l r
  have h0 := swPersistentMoveStartDomain l r hl hr
  let q1 := (moveWsigCheckLast q0.1, q0.2)
  have h1 : q1.1.inProtocolDomain κ ∧ q1.2.inProtocolDomain κ :=
    ⟨swPersistentMoveLastDomain q0.1 h0.1, h0.2⟩
  let q2 := moveWsigTransferStopAligned q1.1 q1.2
  have h2 := moveWsigTransferStopAligned_inProtocolDomain q1.1 q1.2 h1.1 h1.2
  let q3 := moveWsigMoveWritePreservingNonempty q2.1 q2.2
  have h3 := swPersistentMoveWriteDomain q2.1 q2.2 h2.1 h2.2
  let q4 := moveWsigLeaderSignal q3.1 q3.2
  have h4 := swPersistentLeaderSignalDomain q3.1 q3.2 h3.1 h3.2
  let q5 := moveWsigSignalMove q4.1 q4.2
  have h5 := swPersistentSignalMoveDomain q4.1 q4.2 h4.1 h4.2
  exact swPersistentEchoMoveDomain q5.1 q5.2 h5.1 h5.2

/-- Actual range closure, with no post-state domain hypothesis. -/
theorem stationaryPersistentRaw_domain (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    (stationaryPersistentRaw hψ l r).1.inProtocolDomain κ ∧
      (stationaryPersistentRaw hψ l r).2.inProtocolDomain κ := by
  let q := swPersistentThroughPrepare hψ l r
  have hq := swPersistentThroughPrepareDomain hψ l r hl hr
  let lg := gatePreparedIncrement q.1
  let rg := gatePreparedIncrement q.2
  have hlg := gatePreparedIncrement_inProtocolDomain q.1 hq.1
  have hrg := gatePreparedIncrement_inProtocolDomain q.2 hq.2
  let w := writeActionPreservingComparison hψ lg rg
  have hw := swPersistentActionDomain hψ lg rg hlg hrg
  exact swPersistentMoveDomain hψ w.1 w.2 hw.1 hw.2

attribute [local irreducible] stationaryPersistentRaw

/-- Existing fail-closed authorization reconciliation on the real output. -/
def stationaryPersistentAuthorizedRow (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (stationaryPersistentRaw hψ) l r

theorem stationaryPersistentAuthorizedRow_core (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    ((stationaryPersistentAuthorizedRow hψ l r).1.core,
      (stationaryPersistentAuthorizedRow hψ l r).2.core) =
      stationaryPersistentRaw hψ l.core r.core := rfl

theorem stationaryPersistentAuthorizedRow_domain (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (stationaryPersistentAuthorizedRow hψ l r).1.core.inProtocolDomain κ ∧
      (stationaryPersistentAuthorizedRow hψ l r).2.core.inProtocolDomain κ :=
  authorizedReconcile_inProtocolDomain (stationaryPersistentRaw hψ) l r
    (stationaryPersistentRaw_domain hψ l.core r.core hl hr)

theorem stationaryPersistentAuthorizedRow_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    swPair ((stationaryPersistentAuthorizedRow hψ l r).1.core,
      (stationaryPersistentAuthorizedRow hψ l r).2.core) = swPair (l.core, r.core) :=
  stationaryPersistentRaw_frame hψ l.core r.core

theorem stationaryPersistentAuthorizedRow_eq_old (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hm : ¬ (r.core.leader = true ∧ r.core.label ≠ ⟨0, hψ⟩)) :
    stationaryPersistentAuthorizedRow hψ l r =
      authorizedReconcile (writeSeqPersistentComparisonTransportLifecycle hψ) l r := by
  unfold stationaryPersistentAuthorizedRow authorizedReconcile
  rw [stationaryPersistentRaw_eq_old hψ l.core r.core hm]

theorem stationaryPersistentAuthorizedRow_permits (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (stationaryPersistentAuthorizedRow hψ l r).1.path0Crossed = normalizePermit l.core l.path0Crossed ∧
      (stationaryPersistentAuthorizedRow hψ l r).2.path0Crossed = normalizePermit r.core r.path0Crossed := by
  have hf := stationaryPersistentRaw_comparison hψ l.core r.core
  have hl := congrArg (fun q => q.1.path) hf
  have hr := congrArg (fun q => q.2.path) hf
  change (stationaryPersistentRaw hψ l.core r.core).1.path = l.core.path at hl
  change (stationaryPersistentRaw hψ l.core r.core).2.path = r.core.path at hr
  simp only [stationaryPersistentAuthorizedRow, authorizedReconcile, reconcilePermit,
    hl, hr, if_true, normalizePermit, and_self]

theorem stationaryPersistentAuthorizedRow_canonical (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    AuthorizationCanonical (stationaryPersistentAuthorizedRow hψ l r).1 ∧
      AuthorizationCanonical (stationaryPersistentAuthorizedRow hψ l r).2 :=
  authorizedReconcile_canonical (stationaryPersistentRaw hψ) l r

def stationaryPersistentBoundedRow (hψ : 0 < ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := stationaryPersistentAuthorizedRow hψ l.erase r.erase
  let hq := stationaryPersistentAuthorizedRow_domain hψ l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem stationaryPersistentBoundedRow_erase (hψ : 0 < ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    ((stationaryPersistentBoundedRow hψ l r).1.erase,
      (stationaryPersistentBoundedRow hψ l r).2.erase) =
      stationaryPersistentAuthorizedRow hψ l.erase r.erase := by
  simp only [stationaryPersistentBoundedRow, AuthorizedBoundedAgentState.erase,
    BoundedAgentState.erase_ofDomain]

theorem stationaryPersistentBoundedRow_frame (hψ : 0 < ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    swPair ((stationaryPersistentBoundedRow hψ l r).1.core.erase,
      (stationaryPersistentBoundedRow hψ l r).2.core.erase) = swPair (l.core.erase, r.core.erase) := by
  have hh := congrArg (fun q => swPair (q.1.core, q.2.core)) (stationaryPersistentBoundedRow_erase hψ l r)
  exact hh.trans (stationaryPersistentAuthorizedRow_frame hψ l.erase r.erase)

def swPersistentProtocol (hψ : 0 < ψ) (κ : Nat) : PopulationProtocol where
  Q := AuthorizedBoundedAgentState ψ κ
  Y := LeaderOutput
  transition := stationaryPersistentBoundedRow hψ
  output := fun u => AgentState.outputFn u.core.erase

def swPersistentStateCertificate (hψ : 0 < ψ) (κ : Nat) : ExhaustiveList (swPersistentProtocol hψ κ).Q :=
  authorizedBoundedAgentState ψ κ

theorem swPersistentCarrierUnchanged (hψ : 0 < ψ) (κ : Nat) :
    (swPersistentProtocol hψ κ).Q = AuthorizedBoundedAgentState ψ κ ∧
      (swPersistentStateCertificate hψ κ).values.length = (authorizedBoundedAgentState ψ κ).values.length :=
  ⟨rfl, rfl⟩

theorem swPersistentFiniteDecode (hψ : 0 < ψ) (κ : Nat) :
    Function.Surjective (swPersistentStateCertificate hψ κ).decode :=
  authorizedBoundedAgentState_decode_surjective ψ κ

attribute [local irreducible] writeSeqPersistentComparisonTransportLifecycle

def swPersistentRawProtocol (hψ : 0 < ψ) : PopulationProtocol where
  Q := AgentState ψ
  Y := LeaderOutput
  transition := stationaryPersistentRaw hψ
  output := AgentState.outputFn

def swPersistentOldRawProtocol (hψ : 0 < ψ) : PopulationProtocol where
  Q := AgentState ψ
  Y := LeaderOutput
  transition := writeSeqPersistentComparisonTransportLifecycle hψ
  output := AgentState.outputFn

theorem swPersistentRawStepFrame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e i : Fin n) :
    swView ((swPersistentRawProtocol hψ).step ring C e i) = swView (C i) := by
  have hf := stationaryPersistentRaw_frame hψ (C e) (C (ring.rightNeighbor e))
  unfold PopulationProtocol.step swPersistentRawProtocol
  by_cases hi : i = e
  · subst i
    simpa only [if_true, swPair] using congrArg Prod.fst hf
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa only [if_neg hi, if_true, swPair] using congrArg Prod.snd hf
    · simp only [if_neg hi, if_neg hj]

/-- Physical positions retain every original leader bit for all writer words. -/
theorem swPersistentRawRunFrame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (es : List (Fin n)) (i : Fin n) :
    swView (LDSinkBoundedKernel.run ((swPersistentRawProtocol hψ).step ring) C es i) = swView (C i) := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih => exact (ih _).trans (swPersistentRawStepFrame hψ ring C e i)

theorem swPersistentZeroLeaders_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : swZeroLeaders hψ C) (e : Fin n) :
    swZeroLeaders hψ ((swPersistentRawProtocol hψ).step ring C e) := by
  intro i hi
  have hf := swPersistentRawStepFrame hψ ring C e i
  have hl := congrArg Prod.fst hf
  have hb := congrArg (fun q => q.2.1) hf
  exact hb.trans (hC i (hl.symm.trans hi))

theorem swPersistentRawStepEqOld (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : swZeroLeaders hψ C) (e : Fin n) :
    (swPersistentRawProtocol hψ).step ring C e = (swPersistentOldRawProtocol hψ).step ring C e := by
  have hm : ¬ ((C (ring.rightNeighbor e)).leader = true ∧
      (C (ring.rightNeighbor e)).label ≠ ⟨0, hψ⟩) := fun hh => hh.2 (hC _ hh.1)
  exact congrArg (fun q : AgentState ψ × AgentState ψ =>
    let (l, r) := q
    fun i => if i = e then l else if i = ring.rightNeighbor e then r else C i)
    (stationaryPersistentRaw_eq_old hψ (C e) (C (ring.rightNeighbor e)) hm)

/-- The no-migration premise is produced at every actual prefix by the frame. -/
theorem swPersistentRawRunEqOld (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : swZeroLeaders hψ C) (es : List (Fin n)) :
    LDSinkBoundedKernel.run ((swPersistentRawProtocol hψ).step ring) C es =
      LDSinkBoundedKernel.run ((swPersistentOldRawProtocol hψ).step ring) C es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    exact (ih ((swPersistentRawProtocol hψ).step ring C e)
      (swPersistentZeroLeaders_step hψ ring C hC e)).trans
      (congrArg (fun D : Fin n → AgentState ψ =>
        LDSinkBoundedKernel.run ((swPersistentOldRawProtocol hψ).step ring) D es)
        (swPersistentRawStepEqOld hψ ring C hC e))

end BirthStationaryWrite

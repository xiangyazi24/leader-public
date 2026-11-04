import Leader.Wu.Birth.CheckPermitRepair
import Leader.Wu.Entrance.PreWriterFramesCheck

/-!
# Two bit-silent modes for the stationary persistent R1 writer

Source: the formalization erratum `ERRATA.md`, item L16. Algorithm-19 WRITE_ACTION
can change an input bit from a present `path3` without a leader guard.
Thus follower status alone is not a bit-silence hypothesis.

`EmptyWriter` means exactly absence of `path3`. Dirty commands, writer
states, last-group flags and generation requests are permitted.
`BlockedWriter` is a pair-wide occupied/depart mode: both endpoints are
followers, both payloads are present, both command registers are empty,
and all three last-group flags are false. Neither payload contents nor
`gen_ws`, `signal_ws`, or `ws_echo` are constrained.

The actual post-SUPPRESS writer is
`BirthStationaryWrite.stationaryPersistentAuthorizedRow`, whose raw core
is `stationaryPersistentRaw`. The stationary variant omits leader
migration. Algorithm-18 generation tests the initiator's leader field;
therefore EmptyWriter silence needs only a follower initiator, even if
P-prime or CHECK has just created a responder leader.

No stage outside this writer creates or transports `path3`: the R1
prefix frames both bits and both payloads; preparation, birth marking,
reification, expiry, normalization, and the final physical tail frame
them as well. Inside the writer, Algorithm 20 can populate an empty
receiver from an already-present sender without any leader. That is
transport, not generation from an empty pair. The theorem below about
that assignment records this distinction explicitly.

The full-row EmptyWriter theorem includes the interaction that first
creates a leader. It does not assert that the output pair is leaderless,
or that the next interaction with a leader still satisfies its premise.
The BlockedWriter result is a writer-stage invariant, not a claim that
all earlier R1 stages preserve the BlockedWriter leader/last flags.
-/

set_option autoImplicit false
set_option Elab.async false

namespace B6WriterSilence

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
  PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  PPLLCompleteMultiLeaderCleanup PPLLNoCheckBirthConditionTwoPhysical
  BirthGenerationControlRepair BirthGenerationDone
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
  BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair
  BirthSigMoveDisposalRepair BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneCuts BirthStationaryWrite
  K2BirthDispatcher K2BirthDispatcherDone K2BirthLeaderNormalize
  ExpiringK2Projection

variable {ψ κ τ width : Nat}

/-- Payload absence only; in particular, `write` need not be `.none`. -/
def EmptyWriter (u : AgentState ψ) : Prop := u.path3 = none

/-- One endpoint of the occupied, action-free, retained-depart mode. -/
def BlockedCell (u : AgentState ψ) : Prop :=
  u.leader = false ∧ u.path3 ≠ none ∧ u.write = .none ∧
    u.write_state = .depart ∧ u.last = false ∧
    u.last_set = false ∧ u.last_unset = false

/-- Both payloads must be present: an empty receiver would permit transport. -/
def BlockedWriter (l r : AgentState ψ) : Prop :=
  BlockedCell l ∧ BlockedCell r

private abbrev BV := Bool × Option Path3Info

private def bv (u : AgentState ψ) : BV := (u.bit, u.path3)

private def pv (q : AgentState ψ × AgentState ψ) : BV × BV :=
  (bv q.1, bv q.2)

private def av
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) : BV × BV :=
  pv (q.1.core, q.2.core)

private def ev (u : ExpiringAgentState ψ κ τ) : BV :=
  bv u.core.erase.core

private def xv
    (q : ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ) : BV × BV :=
  (ev q.1, ev q.2)

private theorem empty_of_bv {u v : AgentState ψ}
    (h : bv u = bv v) (hv : EmptyWriter v) : EmptyWriter u :=
  (congrArg Prod.snd h).trans hv

private theorem unpack_empty (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ)
    (h : pv q = pv (l, r)) (hl : EmptyWriter l) (hr : EmptyWriter r) :
    EmptyWriter q.1 ∧ EmptyWriter q.2 ∧
      q.1.bit = l.bit ∧ q.2.bit = r.bit := by
  exact ⟨(congrArg (fun z : BV × BV => z.1.2) h).trans hl,
    (congrArg (fun z : BV × BV => z.2.2) h).trans hr,
    congrArg (fun z : BV × BV => z.1.1) h,
    congrArg (fun z : BV × BV => z.2.1) h⟩

private theorem reconcile_av
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, pv (f a b) = pv (a, b))
    (l r : AuthorizedAgentState ψ) :
    av (authorizedReconcile f l r) = av (l, r) :=
  hf l.core r.core

/-! ## EmptyWriter at the literal stationary writer -/

private theorem clear_bv (u : AgentState ψ) :
    bv (clearIncrementAction u) = bv u := by
  unfold clearIncrementAction
  split <;> rfl

private theorem clear_leader (u : AgentState ψ) :
    (clearIncrementAction u).leader = u.leader := by
  unfold clearIncrementAction
  split <;> rfl

private theorem clear_pair_pv (l r : AgentState ψ) :
    pv (clearInputIncrementPair l r) = pv (l, r) :=
  Prod.ext (clear_bv l) (clear_bv r)

private theorem gate_bv (u : AgentState ψ) :
    bv (gatePreparedIncrement u) = bv u := by
  unfold gatePreparedIncrement clearIncrementAction bv
  repeat (first | rfl | split)


private theorem group_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (groupInfo hψ l r) = pv (l, r) := by
  unfold groupInfo pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem group_left_leader (hψ : 0 < ψ) (l r : AgentState ψ) :
    (groupInfo hψ l r).1.leader = l.leader := by
  unfold groupInfo
  dsimp only
  repeat (first | rfl | split)

private theorem ready_bv (u : AgentState ψ) :
    bv (writeSeqSetWriteReadyTransport u) = bv u := by
  unfold writeSeqSetWriteReadyTransport bv
  repeat (first | rfl | split)


private theorem writer_compare_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (writeSeqCompare hψ l r) = pv (l, r) := by
  unfold writeSeqCompare writeSeqCheckBit pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem b6ws_bv_ite (P : Prop) [Decidable P]
    (u v : AgentState ψ) :
    bv (if P then u else v) = if P then bv u else bv v := by
  split <;> rfl


private theorem b6ws_bv_write (u : AgentState ψ) (a : WriteAction) :
    bv { u with write := a } = bv u := rfl


private theorem b6ws_bv_write_state (u : AgentState ψ) (s : WriteState) :
    bv { u with write_state := s } = bv u := rfl


private theorem b6ws_set_write_act_bv (u : AgentState ψ) :
    bv (writeSeqSetWriteAct u) = bv u := by
  by_cases hlarge : u.write_state = .larger
  · cases hp : u.path3 with
    | none =>
        simp [writeSeqSetWriteAct, hlarge, hp, bv]
    | some p =>
        by_cases hf : p.flag = 1
        · simp [writeSeqSetWriteAct, hlarge, hp, hf, bv]
        · simp [writeSeqSetWriteAct, hlarge, hp, hf, bv]
  · by_cases hless : u.write_state = .less
    · simp [writeSeqSetWriteAct, hlarge, hless, bv]
    · simp [writeSeqSetWriteAct, hlarge, hless, bv]



private theorem b6ws_final_r_bv (u : AgentState ψ) :
    bv (writeSeqFinalR u) = bv u := by
  cases hp : u.path3 with
  | none =>
      simp [writeSeqFinalR, hp, bv]
  | some p =>
      by_cases hf : p.flag = 1
      · simp [writeSeqFinalR, hp, hf, bv]
      · simp [writeSeqFinalR, hp, hf, bv]


section
attribute [local irreducible] writeSeqSetWriteAct writeSeqFinalR


private theorem commands_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (writeSeqCommands hψ l r) = pv (l, r) := by
  unfold writeSeqCommands pv
  dsimp only
  simp only [b6ws_set_write_act_bv, b6ws_bv_ite,
    b6ws_final_r_bv, ite_self]

end


section
attribute [local irreducible]
  writeSeqPrepareTransport writeSeqCompare writeSeqCommands


private theorem prepare_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (writeSeqPrepareTransport hψ l r) = pv (l, r) := by
  have hr : pv (writeSeqReadyTransport l r) = pv (l, r) :=
    Prod.ext (ready_bv l) (ready_bv r)
  simp only [writeSeqPrepareTransport]
  generalize writeSeqReadyTransport l r = q at hr ⊢
  have hc := writer_compare_pv hψ q.1 q.2
  generalize writeSeqCompare hψ q.1 q.2 = d at hc ⊢
  exact (commands_pv hψ d.1 d.2).trans (hc.trans hr)
end


private theorem through_prepare_pv (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = false) :
    pv (swPersistentThroughPrepare hψ l r) = pv (l, r) := by
  let c := clearInputIncrementPair l r
  let g := groupInfo hψ c.1 c.2
  have hgl : g.1.leader = false :=
    (group_left_leader hψ c.1 c.2).trans ((clear_leader l).trans hl)
  have hg : writeSeqGenerate hψ g.1 g.2 = (g.1, g.2) := by
    simp [writeSeqGenerate, hgl]
  change pv (writeSeqPrepareTransport hψ
    (writeSeqGenerate hψ g.1 g.2).1
    (writeSeqGenerate hψ g.1 g.2).2) = pv (l, r)
  rw [hg]
  exact (prepare_pv hψ g.1 g.2).trans
    ((group_pv hψ c.1 c.2).trans (clear_pair_pv l r))

private theorem activate_bv (hψ : 0 < ψ) (u : AgentState ψ) :
    bv (writeActionActivateNonempty hψ u) = bv u := by
  unfold writeActionActivateNonempty
  split <;> rfl

private theorem b6ws_overwrite_empty (u : AgentState ψ)
    (h : u.path3 = none) : writeActionApplyOverwrite u = u := by
  simp only [writeActionApplyOverwrite, h]


private theorem b6ws_move_flip_empty (u : AgentState ψ)
    (h : u.path3 = none) : writeActionApplyMoveFlip u = u := by
  simp only [writeActionApplyMoveFlip, h]


private theorem b6ws_increment_empty_bv (u : AgentState ψ)
    (h : u.path3 = none) :
    bv (writeActionApplyIncrementAndFlip u) = bv u := by
  simp only [writeActionApplyIncrementAndFlip, h, bv]


private theorem b6ws_propagate_bv (u : AgentState ψ) (s : WriteState) :
    bv (writeActionPropagateState u s) = bv u := by
  cases s <;> rfl

section
attribute [local irreducible]
  writeActionApplyOverwrite writeActionApplyMoveFlip
  writeActionApplyIncrementAndFlip writeActionPropagateState


private theorem execute_pv_empty (hψ : 0 < ψ) (l r : AgentState ψ)
    (hr : r.path3 = none) :
    pv (writeActionExecutePreservingDepart hψ l r) = pv (l, r) := by
  have ho := b6ws_overwrite_empty r hr
  have hm := b6ws_move_flip_empty r hr
  have hi := b6ws_increment_empty_bv r hr
  unfold writeActionExecutePreservingDepart
  split
  · simp only [ho, hm, ite_self, pv, b6ws_bv_ite,
      b6ws_bv_write_state, b6ws_propagate_bv, hi]
  · rfl
end


private theorem action_pv_empty (hψ : 0 < ψ) (l r : AgentState ψ)
    (hr : r.path3 = none) :
    pv (writeActionPreservingComparison hψ l r) = pv (l, r) := by
  let l0 := writeActionActivateNonempty hψ l
  let r0 := writeActionActivateNonempty hψ r
  have hr0 : r0.path3 = none := empty_of_bv (activate_bv hψ r) hr
  have he : pv (writeActionExecutePreservingComparison hψ l0 r0) =
      pv (l0, r0) := by
    unfold writeActionExecutePreservingComparison
    split
    · rfl
    · exact execute_pv_empty hψ l0 r0 hr0
  exact he.trans (Prod.ext (activate_bv hψ l) (activate_bv hψ r))

private theorem move_write_pv (l r : AgentState ψ) :
    pv (moveWsigMoveWritePreservingNonempty l r) = pv (l, r) := by
  unfold moveWsigMoveWritePreservingNonempty
  split <;> rfl

private theorem leader_signal_pv (l r : AgentState ψ) :
    pv (moveWsigLeaderSignal l r) = pv (l, r) := by
  unfold moveWsigLeaderSignal pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem signal_move_pv (l r : AgentState ψ) :
    pv (moveWsigSignalMove l r) = pv (l, r) := by
  unfold moveWsigSignalMove pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem echo_move_pv (l r : AgentState ψ) :
    pv (moveWsigEchoMove l r) = pv (l, r) := by
  unfold moveWsigEchoMove pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem finish_pv (l r : AgentState ψ) :
    pv (moveWsigFinishPreservingCommand l r) = pv (l, r) := by
  unfold moveWsigFinishPreservingCommand
  dsimp only
  rw [echo_move_pv, signal_move_pv, leader_signal_pv, move_write_pv]

private theorem move_start_pv_empty (l r : AgentState ψ)
    (hl : l.path3 = none) :
    pv (moveWsigStart l r) = pv (l, r) := by
  unfold moveWsigStart
  split
  · simp [moveWsigCheckGenWs, hl, pv, bv]
  · rfl

private theorem move_pv_empty (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.path3 = none) :
    pv (moveWsigStopAligned hψ l r) = pv (l, r) := by
  let s := moveWsigStart l r
  have hs : pv s = pv (l, r) := move_start_pv_empty l r hl
  have he : s.1.path3 = none := empty_of_bv (congrArg Prod.fst hs) hl
  have hc : moveWsigCheckLast s.1 = s.1 := by
    simp [moveWsigCheckLast, he]
  have ht : moveWsigTransferStopAligned s.1 s.2 = (s.1, s.2) := by
    simp [moveWsigTransferStopAligned, he]
  change pv (moveWsigFinishPreservingCommand
    (moveWsigTransferStopAligned (moveWsigCheckLast s.1) s.2).1
    (moveWsigTransferStopAligned (moveWsigCheckLast s.1) s.2).2) = pv (l, r)
  rw [hc, ht]
  exact (finish_pv s.1 s.2).trans hs

section
attribute [local irreducible]
  swPersistentThroughPrepare stationaryPersistentRaw
  writeSeqAfterPrepareComparisonTransport gatePreparedIncrement
  writeActionPreservingComparison moveWsigStopAligned

private theorem stationary_empty_pv (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = false) (hel : EmptyWriter l) (her : EmptyWriter r) :
    pv (stationaryPersistentRaw hψ l r) = pv (l, r) := by
  have hp := through_prepare_pv hψ l r hl
  simp only [stationaryPersistentRaw]
  generalize swPersistentThroughPrepare hψ l r = p at hp ⊢
  have hgl := gate_bv p.1
  have hgr := gate_bv p.2
  generalize gatePreparedIncrement p.1 = gl at hgl ⊢
  generalize gatePreparedIncrement p.2 = gr at hgr ⊢
  have hg0 : pv (gl, gr) = pv p := Prod.ext hgl hgr
  have hg : pv (gl, gr) = pv (l, r) := hg0.trans hp
  have egL : gl.path3 = none :=
    empty_of_bv (u := gl) (v := l)
      (congrArg (fun z : BV × BV => z.1) hg) hel
  have egR : gr.path3 = none :=
    empty_of_bv (u := gr) (v := r)
      (congrArg (fun z : BV × BV => z.2) hg) her
  have ha := action_pv_empty hψ gl gr egR
  simp only [writeSeqAfterPrepareComparisonTransport]
  generalize writeActionPreservingComparison hψ gl gr = a at ha ⊢
  have ea : a.1.path3 = none :=
    empty_of_bv (u := a.1) (v := gl)
      (congrArg (fun z : BV × BV => z.1) ha) egL
  exact (move_pv_empty hψ a.1 a.2 ea).trans (ha.trans hg)
end


/-- The responder may already be, or have just become, a leader. -/
theorem stationaryPersistentRaw_empty_of_left_follower
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = false) (hel : EmptyWriter l) (her : EmptyWriter r) :
    let q := stationaryPersistentRaw hψ l r
    EmptyWriter q.1 ∧ EmptyWriter q.2 ∧
      q.1.bit = l.bit ∧ q.2.bit = r.bit :=
  unpack_empty l r _ (stationary_empty_pv hψ l r hl hel her) hel her

section
attribute [local irreducible]
  stationaryPersistentRaw stationaryPersistentAuthorizedRow

private theorem b6ws_stationary_av (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    av (stationaryPersistentAuthorizedRow hψ l r) =
      pv (stationaryPersistentRaw hψ l.core r.core) := by
  have hc := stationaryPersistentAuthorizedRow_core hψ l r
  generalize stationaryPersistentRaw hψ l.core r.core = p at hc ⊢
  generalize stationaryPersistentAuthorizedRow hψ l r = q at hc ⊢
  exact congrArg (fun z : AgentState ψ × AgentState ψ => pv z) hc

private theorem b6ws_unpack_auth_empty
    (l r : AuthorizedAgentState ψ)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (h : av q = av (l, r))
    (hel : EmptyWriter l.core) (her : EmptyWriter r.core) :
    EmptyWriter q.1.core ∧ EmptyWriter q.2.core ∧
      q.1.core.bit = l.core.bit ∧ q.2.core.bit = r.core.bit :=
  unpack_empty l.core r.core (q.1.core, q.2.core) h hel her

theorem stationaryPersistentAuthorizedRow_empty_of_left_follower
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false)
    (hel : EmptyWriter l.core) (her : EmptyWriter r.core) :
    let q := stationaryPersistentAuthorizedRow hψ l r
    EmptyWriter q.1.core ∧ EmptyWriter q.2.core ∧
      q.1.core.bit = l.core.bit ∧ q.2.core.bit = r.core.bit := by
  have hv : av (stationaryPersistentAuthorizedRow hψ l r) = av (l, r) :=
    (b6ws_stationary_av hψ l r).trans
      (stationary_empty_pv hψ l.core r.core hl hel her)
  exact b6ws_unpack_auth_empty l r
    (stationaryPersistentAuthorizedRow hψ l r) hv hel her

theorem stationaryPersistentAuthorizedRow_empty
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false) (_hr : r.core.leader = false)
    (hel : EmptyWriter l.core) (her : EmptyWriter r.core) :
    let q := stationaryPersistentAuthorizedRow hψ l r
    EmptyWriter q.1.core ∧ EmptyWriter q.2.core ∧
      q.1.core.bit = l.core.bit ∧ q.2.core.bit = r.core.bit := by
  exact stationaryPersistentAuthorizedRow_empty_of_left_follower
    hψ l r hl hel her

theorem stationaryPersistentAuthorizedRow_empty_closed
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hel : EmptyWriter l.core) (her : EmptyWriter r.core) :
    let q := stationaryPersistentAuthorizedRow hψ l r
    q.1.core.leader = false ∧ q.2.core.leader = false ∧
      EmptyWriter q.1.core ∧ EmptyWriter q.2.core := by
  have he := stationaryPersistentAuthorizedRow_empty hψ l r hl hr hel her
  have hf := stationaryPersistentRaw_leaders hψ l.core r.core
  have hc := stationaryPersistentAuthorizedRow_core hψ l r
  generalize stationaryPersistentRaw hψ l.core r.core = p at hf hc
  generalize stationaryPersistentAuthorizedRow hψ l r = q at he hc ⊢
  have hL : q.1.core.leader = p.1.leader :=
    congrArg (fun z : AgentState ψ × AgentState ψ => z.1.leader) hc
  have hR : q.2.core.leader = p.2.leader :=
    congrArg (fun z : AgentState ψ × AgentState ψ => z.2.leader) hc
  exact ⟨hL.trans (hf.1.trans hl), hR.trans (hf.2.trans hr), he.1, he.2.1⟩
end




/-! ## BlockedWriter at the literal stationary writer -/

section
attribute [local irreducible]
  stationaryPersistentRaw swPersistentThroughPrepare
  writeSeqAfterPrepareComparisonTransport
  writeActionPreservingComparison moveWsigStopAligned

private theorem blocked_to_finish (hψ : 0 < ψ) (l r : AgentState ψ)
    (h : BlockedWriter l r) :
    stationaryPersistentRaw hψ l r = moveWsigFinishPreservingCommand l r := by
  rcases h with ⟨hL, hR⟩
  rcases hL with ⟨hll, hlp, hlw, hls, hla, hlset, hlunset⟩
  rcases hR with ⟨hrl, hrp, hrw, hrs, hra, hrset, hrunset⟩
  obtain ⟨pL, hpL⟩ : ∃ p : Path3Info, l.path3 = some p := by
    cases hp : l.path3 with
    | none => exact (hlp hp).elim
    | some p => exact ⟨p, rfl⟩
  obtain ⟨pR, hpR⟩ : ∃ p : Path3Info, r.path3 = some p := by
    cases hp : r.path3 with
    | none => exact (hrp hp).elim
    | some p => exact ⟨p, rfl⟩
  have hp : swPersistentThroughPrepare hψ l r = (l, r) := by
    simp [swPersistentThroughPrepare, clearInputIncrementPair,
      clearIncrementAction, groupInfo, writeSeqGenerate,
      writeSeqPrepareTransport, writeSeqReadyTransport,
      writeSeqSetWriteReadyTransport, writeSeqCompare,
      writeSeqCommands, writeSeqSetWriteAct,
      hll, hrl, hlw, hrw, hls, hrs, hla, hra,
      hlset, hlunset, hrset, hrunset, hpL, hpR]
  have hgl : gatePreparedIncrement l = l := by
    simp [gatePreparedIncrement, hlw]
  have hgr : gatePreparedIncrement r = r := by
    simp [gatePreparedIncrement, hrw]
  have hld : { l with write_state := .depart } = l :=
    (congrArg (fun s : WriteState => { l with write_state := s }) hls).symm
  have hrd : { r with write_state := .depart } = r :=
    (congrArg (fun s : WriteState => { r with write_state := s }) hrs).symm
  have hxl : writeActionActivateNonempty hψ l = l := by
    simp [writeActionActivateNonempty, hlw]
  have hxr : writeActionActivateNonempty hψ r = r := by
    simp [writeActionActivateNonempty, hrw]
  have hex : writeActionExecutePreservingDepart hψ l r = (l, r) := by
    unfold writeActionExecutePreservingDepart
    split
    · simp [hrs, writeActionPropagateState, hld, hrd]
    · rfl
  have ha : writeActionPreservingComparison hψ l r = (l, r) := by
    simp only [writeActionPreservingComparison, hxl, hxr]
    simp [writeActionExecutePreservingComparison, hrs, hex]
  simp only [stationaryPersistentRaw, hp, hgl, hgr,
    writeSeqAfterPrepareComparisonTransport, ha]
  simp [moveWsigStopAligned, moveWsigStart, hrl,
    moveWsigCheckLast, hpL, hla, moveWsigTransferStopAligned, hpR]
end


private theorem finish_blocked (l r : AgentState ψ)
    (h : BlockedWriter l r) :
    let q := moveWsigFinishPreservingCommand l r
    BlockedWriter q.1 q.2 ∧ q.1.bit = l.bit ∧ q.2.bit = r.bit := by
  have hw : l.write = .none := h.1.2.2.1
  unfold moveWsigFinishPreservingCommand
  rw [moveWsigMoveWritePreservingNonempty_of_empty l r hw]
  dsimp only
  unfold moveWsigLeaderSignal moveWsigSignalMove moveWsigEchoMove
  dsimp only
  repeat (first | exact ⟨h, rfl, rfl⟩ | split)

/-- Both occupied departures persist; only unobserved writer-signal fields
may change. Follower status is included in `BlockedWriter` itself. -/
theorem stationaryPersistentRaw_blocked (hψ : 0 < ψ)
    (l r : AgentState ψ) (h : BlockedWriter l r) :
    let q := stationaryPersistentRaw hψ l r
    BlockedWriter q.1 q.2 ∧ q.1.bit = l.bit ∧ q.2.bit = r.bit := by
  rw [blocked_to_finish hψ l r h]
  exact finish_blocked l r h

section
attribute [local irreducible]
  stationaryPersistentRaw stationaryPersistentAuthorizedRow

theorem stationaryPersistentAuthorizedRow_blocked (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) (h : BlockedWriter l.core r.core) :
    let q := stationaryPersistentAuthorizedRow hψ l r
    BlockedWriter q.1.core q.2.core ∧
      q.1.core.bit = l.core.bit ∧ q.2.core.bit = r.core.bit := by
  have hc := stationaryPersistentAuthorizedRow_core hψ l r
  have hb := stationaryPersistentRaw_blocked hψ l.core r.core h
  generalize stationaryPersistentRaw hψ l.core r.core = p at hc hb
  generalize stationaryPersistentAuthorizedRow hψ l r = q at hc ⊢
  have hL : q.1.core = p.1 :=
    congrArg (fun z : AgentState ψ × AgentState ψ => z.1) hc
  have hR : q.2.core = p.2 :=
    congrArg (fun z : AgentState ψ × AgentState ψ => z.2) hc
  change BlockedWriter q.1.core q.2.core ∧
    q.1.core.bit = l.core.bit ∧ q.2.core.bit = r.core.bit
  rw [hL, hR]
  exact hb
end


/-- Algorithm 20 has no leader premise for transporting an existing payload.
This assignment cannot fire from a pair of EmptyWriter endpoints. -/
theorem transfer_populates_receiver (l r : AgentState ψ) (p : Path3Info)
    (hl : l.path3 = some p) (hr : r.path3 = none)
    (hs : l.write_state = .depart) (he : r.ws_echo = false) :
    (moveWsigTransferStopAligned l r).2.path3 = some p := by
  simp [moveWsigTransferStopAligned, hl, hr, hs, he]

/-! ## Two-endpoint bit/path3 frames for the R1 prefix

The existing B6 pre-writer view contains only the responder's writer
fields. We use it below for its initiator-leader coordinate, but do not
misuse it as a two-endpoint bit/path3 frame. The following small frames
supply those additional coordinates directly from the source stages.
-/

private theorem pprime_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (pPsiLeaderResetProbeWall hψ l r) = pv (l, r) := by
  unfold pPsiLeaderResetProbeWall pPsi pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem pprime_av (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    av (authorizedPPsiLeaderResetProbeWall hψ l r) = av (l, r) :=
  (congrArg pv (authorizedPPsiLeaderResetProbeWall_core hψ l r)).trans
    (pprime_pv hψ l.core r.core)

private theorem wait_prepare_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (waitSaturatedPrepare hψ l r) = pv (l, r) := by
  unfold waitSaturatedPrepare pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem wait_clear_pv (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    pv (terminalInactiveClear hw hle l r) = pv (l, r) := by
  unfold terminalInactiveClear pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem wait_carry_pv (hw : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AgentState ψ) :
    pv (waitWidthCarry hw hle κ l r) = pv (l, r) := by
  unfold waitWidthCarry pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem wait_reset_pv (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    pv (waitWidthReset hw hle l r) = pv (l, r) := by
  unfold waitWidthReset pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem wait_finish_pv (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    pv (waitWidthFinish hψ hw hle κ l r) = pv (l, r) := by
  unfold waitWidthFinish pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem wait_entry_pv (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    pv (waitWidthEntry hψ hw hle κ l r) = pv (l, r) := by
  unfold waitWidthEntry
  dsimp only
  rw [wait_finish_pv, wait_reset_pv, wait_carry_pv,
    wait_clear_pv, wait_prepare_pv]

private theorem gen_start_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (genSigSaturatedStart hψ l r) = pv (l, r) := by
  unfold genSigSaturatedStart pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem gen_emit_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (genCleanEmit hψ l r) = pv (l, r) := by
  unfold genCleanEmit pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem gen_propagate_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (genCleanPropagate hψ l r) = pv (l, r) := by
  unfold genCleanPropagate pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem gen_finish_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (genSigSaturatedFinish hψ l r) = pv (l, r) := by
  unfold genSigSaturatedFinish pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem gen_after_wait_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (genCleanAfterWait hψ l r) = pv (l, r) := by
  unfold genCleanAfterWait
  dsimp only
  rw [gen_finish_pv, gen_propagate_pv, gen_emit_pv, gen_start_pv]

private theorem gen_entry_pv (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    pv (genCleanEntryWidth hψ hw hle κ l r) = pv (l, r) := by
  unfold genCleanEntryWidth
  dsimp only
  rw [gen_after_wait_pv, wait_entry_pv]

private theorem gen_entry_av (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    av (authorizedGenCleanEntryWidth hψ hw hle κ l r) = av (l, r) :=
  reconcile_av _ (gen_entry_pv hψ hw hle κ) l r

private theorem clean_connect_pv (l r : AgentState ψ) :
    pv (cleanSigGenConnect l, cleanSigGenConnect r) = pv (l, r) := by
  unfold cleanSigGenConnect pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem clean3_pv (l r : AgentState ψ) :
    pv (cleanSigStep3 l r) = pv (l, r) := by
  unfold cleanSigStep3 pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem clean4_pv (l r : AgentState ψ) :
    pv (cleanSigStep4 l r) = pv (l, r) := by
  unfold cleanSigStep4 pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem clean5_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (cleanSigStep5 hψ l r) = pv (l, r) := by
  unfold cleanSigStep5 pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem clean6_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (cleanSigStep6 hψ l r) = pv (l, r) := by
  unfold cleanSigStep6 pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem clean_apply_pv (l r : AgentState ψ) :
    pv (cleanSigCleanApply l, cleanSigCleanApply r) = pv (l, r) := by
  unfold cleanSigCleanApply pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem clean_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (cleanSig hψ l r) = pv (l, r) := by
  unfold cleanSig
  dsimp only
  rw [clean_apply_pv, clean6_pv, clean5_pv, clean4_pv,
    clean3_pv, clean_connect_pv]

private theorem clean_av (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    av (authorizedCleanSig hψ l r) = av (l, r) :=
  reconcile_av _ (clean_pv hψ) l r

private theorem eliminate_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (eliminateSig hψ l r) = pv (l, r) := by
  unfold eliminateSig pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem eliminate_av (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    av (authorizedEliminateSig hψ l r) = av (l, r) :=
  reconcile_av _ (eliminate_pv hψ) l r

private theorem preclear_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (sigMoveLeaderPreclear hψ l r) = pv (l, r) := by
  unfold sigMoveLeaderPreclear clearIfLeader clearComparisonSignal pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem capture_pv (l r : AgentState ψ) :
    pv (captureStep1 l r) = pv (l, r) := by
  unfold captureStep1 pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem hold_done_pv (l r : AgentState ψ) :
    pv (holdDoneStep1 l r) = pv (l, r) := by
  unfold holdDoneStep1
  split
  · rfl
  · exact capture_pv l r

private theorem sig2_pv (l r : AgentState ψ) :
    pv (sigMoveStep2 l r) = pv (l, r) := by
  unfold sigMoveStep2 pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem sig3_pv (l r : AgentState ψ) :
    pv (sigMoveStep3 l r) = pv (l, r) := by
  unfold sigMoveStep3 pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem sig4_pv (l r : AgentState ψ) :
    pv (sigMoveStep4 l r) = pv (l, r) := by
  unfold sigMoveStep4 pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem sig5_pv (l r : AgentState ψ) :
    pv (sigMoveStep5 l r) = pv (l, r) := by
  unfold sigMoveStep5 pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem controls_pv (l r : AgentState ψ) :
    pv (controlTransfers l r) = pv (l, r) := by
  unfold controlTransfers
  dsimp only
  rw [sig5_pv, sig4_pv, sig3_pv, sig2_pv]

private theorem done_transfers_pv (l r : AgentState ψ) :
    pv (doneTransfers l r) = pv (l, r) := by
  unfold doneTransfers
  dsimp only
  rw [controls_pv, hold_done_pv]

private theorem leader_wall_pv (l r : AgentState ψ) :
    pv (comparisonLeaderWall l r) = pv (l, r) := by
  unfold comparisonLeaderWall clearComparisonSignal pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem control_apply_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (singleUseApplyControl hψ l, singleUseApplyControl hψ r) = pv (l, r) := by
  unfold singleUseApplyControl pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem control_tail_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (singleUseControlTail hψ l r) = pv (l, r) := by
  unfold singleUseControlTail
  dsimp only
  split
  · split
    · simpa [pv, bv] using control_apply_pv hψ l r
    · exact control_apply_pv hψ l r
  · exact control_apply_pv hψ l r

private theorem done_move_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (doneCaptureSigMove hψ l r) = pv (l, r) := by
  unfold doneCaptureSigMove
  dsimp only
  rw [control_tail_pv, leader_wall_pv, done_transfers_pv, preclear_pv]

private theorem done_move_av (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    av (authorizedDoneMove hψ l r) = av (l, r) :=
  (congrArg pv (authorizedDoneMove_core hψ l r)).trans
    (done_move_pv hψ l.core r.core)

private theorem reset_sanitize_av (hψ : 0 < ψ)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    av (sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)) = av q := by
  unfold sanitizeAuthorizedPair sanitizeAuthorizedTerminalEqual
    preCheckResetWall clearAuthorizedComparison clearComparisonSignal av pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem check_ready_pv (l r : AgentState ψ) :
    pv (checkSigSetReady l, checkSigSetReady r) = pv (l, r) := by
  unfold checkSigSetReady pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem check_left_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (checkSigCheckL hψ l, r) = pv (l, r) := by
  unfold checkSigCheckL pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem check_right_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (l, checkSigCheckR hψ l r) = pv (l, r) := by
  unfold checkSigCheckR pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem check_result_pv (l r : AgentState ψ) :
    pv (checkSigSetResult l, checkSigSetResult r) = pv (l, r) := by
  unfold checkSigSetResult pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem check_leader_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (l, checkSigSetLeader hψ r) = pv (l, r) := by
  unfold checkSigSetLeader pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem check_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (checkSig hψ l r) = pv (l, r) := by
  rw [checkSig_eq_staged]
  unfold checkSigStaged
  dsimp only
  rw [check_leader_pv, check_result_pv, check_right_pv,
    check_left_pv, check_ready_pv]

private theorem done_check_av (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    av (preserveDoneCheck hψ l r) = av (l, r) := by
  unfold preserveDoneCheck
  split
  · rfl
  · unfold preserveTossCheck
    split
    · rfl
    · unfold congestGuardCheck
      split
      · rfl
      · exact reconcile_av _ (check_pv hψ) l r

private theorem through_check_av (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    av (doneThroughCheckEntryWidth hψ hw hle κ l r) = av (l, r) := by
  unfold doneThroughCheckEntryWidth doneBeforeCheckEntryWidth
  dsimp only
  rw [done_check_av, reset_sanitize_av, done_move_av]
  unfold generationBeforeMoveEntryWidth
  dsimp only
  rw [eliminate_av, clean_av, gen_entry_av, pprime_av]

private theorem disappear_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (disappear hψ l r) = pv (l, r) := by
  unfold disappear pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem disappear_av (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    av (authorizedDisappear hψ l r) = av (l, r) :=
  reconcile_av _ (disappear_pv hψ) l r

private theorem compare_init_bv (u : AgentState ψ) :
    bv (compareSigInit u) = bv u := by
  unfold compareSigInit bv
  repeat (first | rfl | split)


private theorem compare_set_bv (hψ : 0 < ψ) (u : AgentState ψ) :
    bv (cmpUpdateSetPath2 hψ u) = bv u := by
  unfold cmpUpdateSetPath2 bv
  repeat (first | rfl | split)


private theorem compare_return_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (cmpUpdateReturnPriority hψ l r) = pv (l, r) := by
  unfold cmpUpdateReturnPriority pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem compare_update_av (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    av (authorizedCmpUpdate hψ l r) = av (l, r) := by
  let lc := if freshComparisonStart hψ l && !comparisonActive l.core.state then
      { l.core with state := .congest } else l.core
  let q := cmpUpdateReturnPriority hψ lc r.core
  have hc : bv lc = bv l.core := by
    unfold lc
    split <;> rfl
  have ht : pv (cmpUpdateSetPath2 hψ q.1, q.2) = pv q :=
    Prod.ext (compare_set_bv hψ q.1) rfl
  change pv (cmpUpdateSetPath2 hψ q.1, q.2) = pv (l.core, r.core)
  exact ht.trans ((compare_return_pv hψ lc r.core).trans (Prod.ext hc rfl))

private theorem compare_left_bv (hψ : 0 < ψ) (u : AgentState ψ) :
    bv (compareBitUpdateL hψ u) = bv u := by
  unfold compareBitUpdateL bv
  repeat (first | rfl | split)


private theorem compare_right_bv (hψ : 0 < ψ) (u : AgentState ψ) :
    bv (compareBitUpdateRActionOne hψ u) = bv u := by
  simp only [compareBitUpdateRActionOne, compareBitUpdateR, bv]
  repeat (first | rfl | split)

private theorem compare_pair_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (compareBitActionOne hψ l r) = pv (l, r) :=
  Prod.ext (compare_left_bv hψ l) (compare_right_bv hψ r)

private theorem compare_dispatch_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (compareSigDispatchActionOne hψ l r) = pv (l, r) := by
  unfold compareSigDispatchActionOne
  repeat (first | exact compare_pair_pv hψ l r | rfl | split)

private theorem compare_av (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    av (authorizedCompareSigActionOne hψ l r) = av (l, r) := by
  let l0 : AuthorizedAgentState ψ :=
    ⟨compareSigInit l.core, normalizePermit (compareSigInit l.core) l.path0Crossed⟩
  have hi : av (l0, r) = av (l, r) :=
    Prod.ext (compare_init_bv l.core) rfl
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact hi
  · split
    · exact hi
    · let q := authorizedCmpUpdate hψ l0 r
      change pv (compareSigDispatchActionOne hψ q.1.core q.2.core) = av (l, r)
      exact (compare_dispatch_pv hψ q.1.core q.2.core).trans
        ((compare_update_av hψ l0 r).trans hi)

private theorem suppress_start_pv (l r : AgentState ψ) :
    pv (suppressSigStart l r) = pv (l, r) := by
  unfold suppressSigStart pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem reset_kill_pv (l r : AgentState ψ) :
    pv (resetKillComparison l, resetKillComparison r) = pv (l, r) := by
  unfold resetKillComparison clearComparisonSignal pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem suppress_move_pv (l r : AgentState ψ) :
    pv (suppressSigMoveReset l r) = pv (l, r) := by
  unfold suppressSigMoveReset pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem short_count_pv (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    pv (shortCountReset hw hle l r) = pv (l, r) := by
  unfold shortCountReset pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem suppress_terminal_pv (hψ : 0 < ψ) (l r : AgentState ψ) :
    pv (suppressSigTerminal hψ l r) = pv (l, r) := by
  unfold suppressSigTerminal pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem suppress_echo_pv (l r : AgentState ψ) :
    pv (suppressSigEcho l r) = pv (l, r) := by
  unfold suppressSigEcho pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem suppress_finish_pv (l r : AgentState ψ) :
    pv (suppressSigFinish l r) = pv (l, r) := by
  unfold suppressSigFinish pv bv
  dsimp only
  repeat (first | rfl | split)

private theorem suppress_prefix_pv (l r : AgentState ψ) :
    pv (suppressPrefix l r) = pv (l, r) := by
  unfold suppressPrefix
  dsimp only
  rw [reset_kill_pv, suppress_move_pv, reset_kill_pv, suppress_start_pv]

private theorem suppress_pv (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (l r : AgentState ψ) :
    pv (suppressSigResetKillWidth hψ hw hle l r) = pv (l, r) := by
  unfold suppressSigResetKillWidth
  dsimp only
  rw [suppress_finish_pv, suppress_echo_pv, suppress_terminal_pv,
    short_count_pv, suppress_prefix_pv]

private theorem suppress_av (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (l r : AuthorizedAgentState ψ) :
    av (authorizedSuppressWidth hψ hw hle l r) = av (l, r) :=
  reconcile_av _ (suppress_pv hψ hw hle) l r

private theorem before_write_av (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (l r : AuthorizedAgentState ψ) :
    av (beforeWriteWidth hψ hw hle l r) = av (l, r) := by
  unfold beforeWriteWidth
  dsimp only
  rw [suppress_av, compare_av, disappear_av]

/-- The actual R1 cut, including its permit consumption after CHECK.
This is not the older consumer's unmodified `rowPreWriterInput`. -/
def r1WriterInput (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let c := doneThroughCheckEntryWidth hψ hw hle κ l r
  beforeWriteWidth hψ hw hle (BirthCheckPermitRepair.permitFix c.1) c.2

section
attribute [local irreducible]
  r1WriterInput doneThroughCheckEntryWidth beforeWriteWidth
  BirthCheckPermitRepair.permitFix

private theorem r1_input_av (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    av (r1WriterInput hψ hw hle κ l r) = av (l, r) := by
  have hc := through_check_av hψ hw hle κ l r
  simp only [r1WriterInput]
  generalize doneThroughCheckEntryWidth hψ hw hle κ l r = q at hc ⊢
  have hf : av (BirthCheckPermitRepair.permitFix q.1, q.2) = av q := by
    change (bv (BirthCheckPermitRepair.permitFix q.1).core, bv q.2.core) =
      (bv q.1.core, bv q.2.core)
    exact Prod.ext
      (congrArg (fun u : AgentState ψ => bv u)
        (BirthCheckPermitRepair.permitFix_core q.1)) rfl
  exact (before_write_av hψ hw hle
    (BirthCheckPermitRepair.permitFix q.1) q.2).trans (hf.trans hc)

theorem r1WriterInput_fields (hψ : 0 < ψ) (hw : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    let q := r1WriterInput hψ hw hle κ l r
    q.1.core.bit = l.core.bit ∧ q.2.core.bit = r.core.bit ∧
      q.1.core.path3 = l.core.path3 ∧ q.2.core.path3 = r.core.path3 := by
  have h := r1_input_av hψ hw hle κ l r
  generalize r1WriterInput hψ hw hle κ l r = q at h ⊢
  exact ⟨congrArg (fun z : BV × BV => z.1.1) h,
    congrArg (fun z : BV × BV => z.2.1) h,
    congrArg (fun z : BV × BV => z.1.2) h,
    congrArg (fun z : BV × BV => z.2.2) h⟩

private theorem through_check_left_leader
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (doneThroughCheckEntryWidth hψ hw hle κ l r).1.core.leader =
      l.core.leader := by
  have hf : B6PreWriterFramesA.PreWriterFrame
      (doneThroughCheckEntryWidth hψ hw hle κ l r) =
      B6PreWriterFramesA.PreWriterFrame (l, r) := by
    unfold doneThroughCheckEntryWidth doneBeforeCheckEntryWidth
    simp only
    rw [B6PreWriterFramesC.preserveDoneCheck_frame hψ,
      B6PreWriterFramesC.resetSanitize_frame hψ,
      B6PreWriterFramesB.doneMove_frame hψ]
    unfold generationBeforeMoveEntryWidth
    simp only
    rw [B6PreWriterFramesB.eliminate_frame hψ,
      B6PreWriterFramesB.clean_frame hψ,
      B6PreWriterFramesA.genEntry_frame hψ hw hle κ,
      B6PreWriterFramesA.pprime_frame hψ]
  generalize doneThroughCheckEntryWidth hψ hw hle κ l r = q at hf ⊢
  exact congrArg B6PreWriterFramesA.PreWriterFrameView.leftLeader hf
end

-- Keep the existing before_write_left_leader declaration unchanged.




private theorem before_write_left_leader
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    (beforeWriteWidth hψ hw hle l r).1.core.leader = l.core.leader := by
  have hf : B6PreWriterFramesA.PreWriterFrame (beforeWriteWidth hψ hw hle l r) =
      B6PreWriterFramesA.PreWriterFrame (l, r) := by
    unfold beforeWriteWidth
    dsimp only
    rw [B6PreWriterFramesC.suppress_frame, B6PreWriterFramesC.compare_frame,
      B6PreWriterFramesC.disappear_frame]
  exact congrArg B6PreWriterFramesA.PreWriterFrameView.leftLeader hf

section
attribute [local irreducible]
  r1WriterInput doneThroughCheckEntryWidth beforeWriteWidth
  BirthCheckPermitRepair.permitFix

theorem r1WriterInput_left_leader
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (r1WriterInput hψ hw hle κ l r).1.core.leader = l.core.leader := by
  have hc := through_check_left_leader hψ hw hle κ l r
  simp only [r1WriterInput]
  generalize doneThroughCheckEntryWidth hψ hw hle κ l r = q at hc ⊢
  have hf : (BirthCheckPermitRepair.permitFix q.1).core.leader =
      q.1.core.leader :=
    congrArg (fun u : AgentState ψ => u.leader)
      (BirthCheckPermitRepair.permitFix_core q.1)
  exact (before_write_left_leader hψ hw hle
    (BirthCheckPermitRepair.permitFix q.1) q.2).trans (hf.trans hc)
end


/-! ## R1 priority, finite reification, expiry, and the physical tail -/

private theorem mark_av (born : Bool)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    av (markLeaderBirth born q) = av q := by
  unfold markLeaderBirth markComparisonForDeletion av pv bv
  dsimp only
  repeat (first | rfl | split)

section
attribute [local irreducible]
  r1WriterInput doneThroughCheckEntryWidth beforeWriteWidth
  afterCheckMetadataWidth stationaryPersistentRaw
  stationaryPersistentAuthorizedRow BirthCheckPermitRepair.permitFix
  BirthCheckPermitRepair.ordinary markLeaderBirth

private theorem b6ws_ordinary_writer_eq
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) :
    BirthCheckPermitRepair.ordinary hψ hw hle κ l r =
      (let p := r1WriterInput hψ hw hle κ l r
       let w := stationaryPersistentAuthorizedRow hψ p.1 p.2
       markLeaderBirth (authBirth l r w) w) := by
  simp only [BirthCheckPermitRepair.ordinary,
    afterCheckMetadataWidth, r1WriterInput]

private theorem ordinary_empty_av
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false)
    (hel : EmptyWriter l.core) (her : EmptyWriter r.core) :
    av (BirthCheckPermitRepair.ordinary hψ hw hle κ l r) = av (l, r) := by
  have hp := r1_input_av hψ hw hle κ l r
  have hlead := r1WriterInput_left_leader hψ hw hle κ l r
  rw [b6ws_ordinary_writer_eq hψ hw hle κ l r]
  generalize r1WriterInput hψ hw hle κ l r = p at hp hlead ⊢
  dsimp only
  have ep1 : EmptyWriter p.1.core :=
    empty_of_bv (u := p.1.core) (v := l.core)
      (congrArg (fun z : BV × BV => z.1) hp) hel
  have ep2 : EmptyWriter p.2.core :=
    empty_of_bv (u := p.2.core) (v := r.core)
      (congrArg (fun z : BV × BV => z.2) hp) her
  have hwv : av (stationaryPersistentAuthorizedRow hψ p.1 p.2) = av p :=
    (b6ws_stationary_av hψ p.1 p.2).trans
      (stationary_empty_pv hψ p.1.core p.2.core
        (hlead.trans hl) ep1 ep2)
  generalize stationaryPersistentAuthorizedRow hψ p.1 p.2 = w at hwv ⊢
  exact (mark_av (authBirth l r w) w).trans (hwv.trans hp)

end


private theorem normalize_deletion_view (u : AuthorizedAgentState ψ) :
    ((normalizeDeletion u).core.leader, bv (normalizeDeletion u).core) =
      (u.core.leader, bv u.core) := by
  unfold normalizeDeletion bv
  dsimp only
  repeat (first | rfl | split)

section
attribute [local irreducible]
  BirthCheckPermitRepair.authorized BirthCheckPermitRepair.ordinary
  normalizeDeletion authorizedEliminateSig

private theorem authorized_empty_av
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false)
    (hel : EmptyWriter l.core) (her : EmptyWriter r.core) :
    av (BirthCheckPermitRepair.authorized hψ hw hle κ l r) = av (l, r) := by
  have fl := normalize_deletion_view l
  have fr := normalize_deletion_view r
  simp only [BirthCheckPermitRepair.authorized]
  generalize normalizeDeletion l = l0 at fl ⊢
  generalize normalizeDeletion r = r0 at fr ⊢
  have hlb : bv l0.core = bv l.core :=
    congrArg (fun z : Bool × BV => z.2) fl
  have hrb : bv r0.core = bv r.core :=
    congrArg (fun z : Bool × BV => z.2) fr
  have hl0 : l0.core.leader = false :=
    (congrArg (fun z : Bool × BV => z.1) fl).trans hl
  have el0 : EmptyWriter l0.core :=
    empty_of_bv (u := l0.core) (v := l.core) hlb hel
  have er0 : EmptyWriter r0.core :=
    empty_of_bv (u := r0.core) (v := r.core) hrb her
  have hn : av (l0, r0) = av (l, r) := by
    change (bv l0.core, bv r0.core) = (bv l.core, bv r.core)
    exact Prod.ext hlb hrb
  split
  · exact (eliminate_av hψ l0 r0).trans hn
  · split
    · exact hn
    · exact (ordinary_empty_av hψ hw hle κ l0 r0 hl0 el0 er0).trans hn
end


private theorem bounded_erase
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    ((BirthCheckPermitRepair.bounded hψ hw hle l r).1.erase,
      (BirthCheckPermitRepair.bounded hψ hw hle l r).2.erase) =
      BirthCheckPermitRepair.authorized hψ hw hle κ l.erase r.erase := by
  simp only [BirthCheckPermitRepair.bounded,
    AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain] <;> rfl

private theorem disposal_view (hψ : 0 < ψ) (u : AuthorizedAgentState ψ) :
    ((prepareDisposal hψ u).core.leader, bv (prepareDisposal hψ u).core) =
      (u.core.leader, bv u.core) := by
  unfold prepareDisposal markComparisonForDeletion bv
  dsimp only
  repeat (first | rfl | split)

private theorem prepared_view (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    ((prepareExpiringDisposal hψ u).core.erase.core.leader,
      ev (prepareExpiringDisposal hψ u)) =
      (u.core.erase.core.leader, ev u) := by
  change ((prepareBoundedDisposal hψ u.core).erase.core.leader,
      bv (prepareBoundedDisposal hψ u.core).erase.core) =
    (u.core.erase.core.leader, bv u.core.erase.core)
  simpa only [erase_prepareBoundedDisposal] using disposal_view hψ u.core.erase

private theorem expiry_ev (old out : ExpiringAgentState ψ κ τ) :
    ev (deletionPriorityExpireOne τ old out) = ev out := by
  unfold deletionPriorityExpireOne pathExpireOne clearComparisonCarrier ev bv
  dsimp only
  repeat (first | rfl | split)

private theorem normalize_ev (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    ev (normalizeLeader hψ u) = ev u := by
  have h := congrArg (fun z : ExpiringAgentState ψ κ τ => ev z)
    (normalizeLeader_field_frame hψ u)
  change ev (normalizeLeader hψ u) = ev u at h
  exact h

private theorem final_xv (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    xv (K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR) =
      xv (metaL, metaR) := by
  have h := K2BirthDispatcher.finalPhysical_frame hψ oldL oldR metaL metaR
  have hl := congrArg (fun z : ExpiringAgentState ψ κ τ => ev z) h.1
  have hr := congrArg (fun z : ExpiringAgentState ψ κ τ => ev z) h.2
  change ev (K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).1 =
    ev metaL at hl
  change ev (K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).2 =
    ev metaR at hr
  exact Prod.ext hl hr

section
attribute [local irreducible]
  BirthCheckPermitRepair.expiring BirthCheckPermitRepair.bounded
  BirthCheckPermitRepair.authorized
  prepareExpiringDisposal deletionPriorityExpireOne

private theorem expiring_empty_xv
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.erase.core.leader = false)
    (hel : EmptyWriter l.core.erase.core)
    (her : EmptyWriter r.core.erase.core) :
    xv (BirthCheckPermitRepair.expiring hψ hw hle l r) = xv (l, r) := by
  have fl := prepared_view hψ l
  have fr := prepared_view hψ r
  simp only [BirthCheckPermitRepair.expiring]
  generalize prepareExpiringDisposal hψ l = l0 at fl ⊢
  generalize prepareExpiringDisposal hψ r = r0 at fr ⊢
  have hbl : ev l0 = ev l :=
    congrArg (fun z : Bool × BV => z.2) fl
  have hbr : ev r0 = ev r :=
    congrArg (fun z : Bool × BV => z.2) fr
  have hl0 : l0.core.erase.core.leader = false :=
    (congrArg (fun z : Bool × BV => z.1) fl).trans hl
  have el0 : EmptyWriter l0.core.erase.core :=
    empty_of_bv (u := l0.core.erase.core) (v := l.core.erase.core) hbl hel
  have er0 : EmptyWriter r0.core.erase.core :=
    empty_of_bv (u := r0.core.erase.core) (v := r.core.erase.core) hbr her
  have hc := bounded_erase hψ hw hle l0.core r0.core
  have ha := authorized_empty_av hψ hw hle κ
    l0.core.erase r0.core.erase hl0 el0 er0
  generalize BirthCheckPermitRepair.bounded hψ hw hle l0.core r0.core = q at hc ⊢
  have hb : av (q.1.erase, q.2.erase) = av (l0.core.erase, r0.core.erase) :=
    (congrArg (fun z : AuthorizedAgentState ψ × AuthorizedAgentState ψ => av z)
      hc).trans ha
  have hn : xv (l0, r0) = xv (l, r) := by
    change (ev l0, ev r0) = (ev l, ev r)
    exact Prod.ext hbl hbr
  have hbefore :
      (ev (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ),
       ev (⟨q.2, r0.stall⟩ : ExpiringAgentState ψ κ τ)) = xv (l0, r0) := hb
  have he :
      (ev (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩),
       ev (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)) =
      (ev (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ),
       ev (⟨q.2, r0.stall⟩ : ExpiringAgentState ψ κ τ)) :=
    Prod.ext
      (expiry_ev l0 (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ))
      (expiry_ev r0 (⟨q.2, r0.stall⟩ : ExpiringAgentState ψ κ τ))
  exact he.trans (hbefore.trans hn)
end


/-- Full R1 EmptyWriter/bit preservation. Only the input initiator must be a
follower; a responder birth anywhere in the prefix is allowed. -/
theorem row_empty_of_left_follower
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.erase.core.leader = false)
    (hel : EmptyWriter l.core.erase.core)
    (her : EmptyWriter r.core.erase.core) :
    let q := BirthCheckPermitRepair.row hψ hw hle l r
    EmptyWriter q.1.core.erase.core ∧ EmptyWriter q.2.core.erase.core ∧
      q.1.core.erase.core.bit = l.core.erase.core.bit ∧
      q.2.core.erase.core.bit = r.core.erase.core.bit := by
  let e := BirthCheckPermitRepair.expiring hψ hw hle l r
  let q := BirthCheckPermitRepair.row hψ hw hle l r
  have he : xv e = xv (l, r) := expiring_empty_xv hψ hw hle l r hl hel her
  have hn : xv (normalizeLeader hψ e.1, normalizeLeader hψ e.2) = xv e :=
    Prod.ext (normalize_ev hψ e.1) (normalize_ev hψ e.2)
  have hq : xv q = xv (l, r) :=
    (final_xv hψ l r (normalizeLeader hψ e.1) (normalizeLeader hψ e.2)).trans
      (hn.trans he)
  exact unpack_empty l.core.erase.core r.core.erase.core
    (q.1.core.erase.core, q.2.core.erase.core) hq hel her

/-- The requested leaderless-input R1 corollary. The resulting pair need not
remain leaderless, so this is not an assertion of closure after a birth. -/
theorem row_empty
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.erase.core.leader = false)
    (_hr : r.core.erase.core.leader = false)
    (hel : EmptyWriter l.core.erase.core)
    (her : EmptyWriter r.core.erase.core) :
    let q := BirthCheckPermitRepair.row hψ hw hle l r
    EmptyWriter q.1.core.erase.core ∧ EmptyWriter q.2.core.erase.core ∧
      q.1.core.erase.core.bit = l.core.erase.core.bit ∧
      q.2.core.erase.core.bit = r.core.erase.core.bit :=
  row_empty_of_left_follower hψ hw hle l r hl hel her

end B6WriterSilence

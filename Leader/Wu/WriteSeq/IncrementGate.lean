import Leader.Wu.Protocol.BoundedProtocol
import Leader.Wu.WriteSeq.CommandProvenance
import Leader.Wu.Safety.ConcreteProtocolProperties

/-!
# A zero-state-cost gate for unsupported increment commands

T8 starts Algorithm 19 with `write = increment_group` but no local `path3`.
This separately named research repair inserts a physical gate at the exact
Algorithm-16/19 boundary: after command preparation and immediately before
`writeAction`, an increment command survives only beside a present `path3`
whose flag is exactly zero.  Placing the gate after preparation also rejects a
malformed raw flag that `writeSeqFinalR` would otherwise interpret as an
increment in the same interaction.

The gate adds no state and reuses `BoundedAgentState`.  It is only local support,
not lineage authentication: an arbitrary initial state identical to a genuine
flag-zero prepared command is intentionally indistinguishable and remains
executable.  No `GroupIDBoundarySafe` or convergence claim is made here.
-/

namespace PPLLWriteIncrementGate

open PPLL PPLLRepair PPLLDomain

/-- Clear a pending increment action while preserving every other physical
field and every other write action. -/
def clearIncrementAction (u : AgentState ψ) : AgentState ψ :=
  if u.write = .increment_group then { u with write := .none } else u

/-- Fail-closed physical gate at the prepared-command boundary.  Only an exact
flag-zero `path3` supports `increment_group`; malformed raw flags are rejected. -/
def gatePreparedIncrement (u : AgentState ψ) : AgentState ψ :=
  if u.write = .increment_group then
    match u.path3 with
    | some p3 => if p3.flag = 0 then u else clearIncrementAction u
    | none => clearIncrementAction u
  else u

/-- Any increment surviving the gate has an explicit local flag-zero support.
This says nothing about where that support was generated. -/
theorem gatePreparedIncrement_supported (u : AgentState ψ)
    (hwrite : (gatePreparedIncrement u).write = .increment_group) :
    ∃ p3 : Path3Info,
      (gatePreparedIncrement u).path3 = some p3 ∧ p3.flag = 0 := by
  by_cases hw : u.write = .increment_group
  · cases hp : u.path3 with
    | none => simp [gatePreparedIncrement, clearIncrementAction, hw, hp] at hwrite
    | some p3 =>
        by_cases hf : p3.flag = 0
        · exact ⟨p3, by simp [gatePreparedIncrement, hw, hp, hf], hf⟩
        · simp [gatePreparedIncrement, clearIncrementAction, hw, hp, hf] at hwrite
  · simp [gatePreparedIncrement, hw] at hwrite

/-- The gate changes no field constrained by `AgentState.inProtocolDomain`. -/
theorem gatePreparedIncrement_inProtocolDomain (u : AgentState ψ)
    (hu : u.inProtocolDomain κ) :
    (gatePreparedIncrement u).inProtocolDomain κ := by
  have hc : (gatePreparedIncrement u).count = u.count := by
    by_cases hw : u.write = .increment_group
    · cases hp : u.path3 with
      | none => simp [gatePreparedIncrement, clearIncrementAction, hw, hp]
      | some p3 =>
          by_cases hf : p3.flag = 0 <;>
            simp [gatePreparedIncrement, clearIncrementAction, hw, hp, hf]
    · simp [gatePreparedIncrement, hw]
  have hp : PayloadView.ofState (gatePreparedIncrement u) =
      PayloadView.ofState u := by
    by_cases hw : u.write = .increment_group
    · cases hpath : u.path3 with
      | none =>
          simp [gatePreparedIncrement, clearIncrementAction, hw, hpath,
            PayloadView.ofState]
      | some p3 =>
          by_cases hf : p3.flag = 0 <;>
            simp [gatePreparedIncrement, clearIncrementAction, hw, hpath, hf,
              PayloadView.ofState]
    · simp [gatePreparedIncrement, hw]
  rw [inProtocolDomain_iff] at hu ⊢
  exact ⟨hc ▸ hu.1, hp ▸ hu.2⟩

/-- The prepared increment gate frames the leader output field. -/
theorem gatePreparedIncrement_leader_eq (u : AgentState ψ) :
    (gatePreparedIncrement u).leader = u.leader := by
  unfold gatePreparedIncrement clearIncrementAction
  repeat (first | rfl | split)

/-- Algorithm-16 gate: prepare commands exactly as before, sanitize both
endpoints, then execute Algorithms 19–20 unchanged. -/
def writeSeqIncrementGate (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := writeSeqThroughPrepare hψ l r
  writeSeqAfterPrepare hψ
    (gatePreparedIncrement q.1) (gatePreparedIncrement q.2)

/-- Exact factored boundary for the gated Algorithm-16 execution. -/
theorem writeSeqIncrementGate_eq_afterPrepare
    (hψ : ψ > 0) (l r : AgentState ψ) :
    writeSeqIncrementGate hψ l r = writeSeqAfterPrepare hψ
      (gatePreparedIncrement (writeSeqThroughPrepare hψ l r).1)
      (gatePreparedIncrement (writeSeqThroughPrepare hψ l r).2) := by
  rfl

private theorem writeSeqAfterPrepare_leaders_eq
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqAfterPrepare hψ l r).1.leader = l.leader ∧
      (writeSeqAfterPrepare hψ l r).2.leader = r.leader := by
  let q := writeAction hψ l r
  have h0 := PPLLVerify.writeAction_leaders_eq hψ l r
  have h1 := PPLLVerify.moveWsig_leaders_eq hψ q.1 q.2
  change (moveWsig hψ q.1 q.2).1.leader = l.leader ∧
    (moveWsig hψ q.1 q.2).2.leader = r.leader
  exact ⟨h1.1.trans h0.1, h1.2.trans h0.2⟩

/-- Prepared gating changes no leader behavior relative to ordinary WRITE_SEQ. -/
theorem writeSeqIncrementGate_leaders_eq_writeSeq
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqIncrementGate hψ l r).1.leader = (writeSeq hψ l r).1.leader ∧
      (writeSeqIncrementGate hψ l r).2.leader =
        (writeSeq hψ l r).2.leader := by
  have hgL := gatePreparedIncrement_leader_eq
    (writeSeqThroughPrepare hψ l r).1
  have hgR := gatePreparedIncrement_leader_eq
    (writeSeqThroughPrepare hψ l r).2
  have hgate := writeSeqAfterPrepare_leaders_eq hψ
    (gatePreparedIncrement (writeSeqThroughPrepare hψ l r).1)
    (gatePreparedIncrement (writeSeqThroughPrepare hψ l r).2)
  have hplain := writeSeqAfterPrepare_leaders_eq hψ
    (writeSeqThroughPrepare hψ l r).1
    (writeSeqThroughPrepare hψ l r).2
  rw [writeSeqIncrementGate_eq_afterPrepare, writeSeq_eq_afterPrepare]
  exact ⟨hgate.1.trans (hgL.trans hplain.1.symm),
    hgate.2.trans (hgR.trans hplain.2.symm)⟩

/-- Gating preserves an existing initiator leader. -/
theorem writeSeqIncrementGate_initiator_survives
    (hψ : ψ > 0) (l r : AgentState ψ) (hl : l.leader = true) :
    (writeSeqIncrementGate hψ l r).1.leader = true := by
  have heq := (writeSeqIncrementGate_leaders_eq_writeSeq hψ l r).1
  rw [heq]
  exact PPLLVerify.writeSeq_initiator_leader_of_true hψ l r hl

/-- Gating preserves a responder leader hosted at label zero. -/
theorem writeSeqIncrementGate_responder_zero_survives
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hr : r.leader = true) (hrLabel : r.label = ⟨0, hψ⟩) :
    (writeSeqIncrementGate hψ l r).2.leader = true := by
  have heq := (writeSeqIncrementGate_leaders_eq_writeSeq hψ l r).2
  rw [heq]
  exact PPLLVerify.writeSeq_responder_leader_of_label_zero
    hψ l r hr hrLabel

/-- A gated WRITE_SEQ responder leader must already be the input responder. -/
theorem writeSeqIncrementGate_responder_origin
    (hψ : ψ > 0) (l r : AgentState ψ)
    (h : (writeSeqIncrementGate hψ l r).2.leader = true) :
    r.leader = true := by
  have heq := (writeSeqIncrementGate_leaders_eq_writeSeq hψ l r).2
  have hw : (writeSeq hψ l r).2.leader = true := heq.symm.trans h
  exact PPLLVerify.writeSeq_responder_leader_was_leader hψ l r hw

/-- Prepared-increment gating preserves WRITE_SEQ's atomic responder clear on
a nonzero-label leader migration. -/
theorem writeSeqIncrementGate_responder_false_of_nonzero_leader
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hmigrate : r.leader = true ∧ r.label ≠ ⟨0, hψ⟩) :
    (writeSeqIncrementGate hψ l r).2.leader = false := by
  rw [(writeSeqIncrementGate_leaders_eq_writeSeq hψ l r).2]
  exact PPLLVerify.writeSeq_responder_false_of_nonzero_leader
    hψ l r hmigrate

/-- Gated WRITE_SEQ migrates every nonzero-label responder leader to the
initiator.  Together with the responder-clear theorem above, this is the
positive half of the source transition's atomic leader-migration contract. -/
theorem writeSeqIncrementGate_initiator_true_of_nonzero_responder_leader
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hmigrate : r.leader = true ∧ r.label ≠ ⟨0, hψ⟩) :
    (writeSeqIncrementGate hψ l r).1.leader = true := by
  rw [(writeSeqIncrementGate_leaders_eq_writeSeq hψ l r).1]
  exact PPLLVerify.writeSeq_initiator_true_of_nonzero_responder_leader
    hψ l r hmigrate

/-- If gating produces a new initiator leader, it came from a nonzero-label
responder leader exactly as in ordinary WRITE_SEQ. -/
theorem writeSeqIncrementGate_new_initiator_requires_responder
    (hψ : ψ > 0) (l r : AgentState ψ)
    (h : (writeSeqIncrementGate hψ l r).1.leader = true)
    (hl : l.leader = false) :
    r.leader = true ∧ r.label ≠ ⟨0, hψ⟩ := by
  have heq := (writeSeqIncrementGate_leaders_eq_writeSeq hψ l r).1
  have hw : (writeSeq hψ l r).1.leader = true := heq.symm.trans h
  exact PPLLVerify.writeSeq_new_initiator_requires_responder_leader
    hψ l r hw hl

/-- Gated WRITE_SEQ cannot duplicate a sole responder leader into a follower
initiator: its only new-left case simultaneously clears the responder. -/
theorem writeSeqIncrementGate_left_follower_not_both
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) :
    ¬ ((writeSeqIncrementGate hψ l r).1.leader = true ∧
      (writeSeqIncrementGate hψ l r).2.leader = true) := by
  rintro ⟨hleft, hright⟩
  have hmigrate := writeSeqIncrementGate_new_initiator_requires_responder
    hψ l r hleft hl
  have hrightFalse :=
    writeSeqIncrementGate_responder_false_of_nonzero_leader
      hψ l r hmigrate
  have hbad : (false : Bool) = true := hrightFalse.symm.trans hright
  simp at hbad

/-- A gated WRITE_SEQ initiator leader comes from one of the two input leaders. -/
theorem writeSeqIncrementGate_initiator_origin
    (hψ : ψ > 0) (l r : AgentState ψ)
    (h : (writeSeqIncrementGate hψ l r).1.leader = true) :
    l.leader = true ∨ r.leader = true := by
  by_cases hl : l.leader = true
  · exact .inl hl
  · right
    have hlf : l.leader = false := by
      cases hleq : l.leader
      · rfl
      · exact (hl hleq).elim
    have heq := (writeSeqIncrementGate_leaders_eq_writeSeq hψ l r).1
    have hw : (writeSeq hψ l r).1.leader = true := heq.symm.trans h
    exact (PPLLVerify.writeSeq_new_initiator_requires_responder_leader
      hψ l r hw hlf).1

private theorem writeSeqSetWriteReady_not_increment (u : AgentState ψ) :
    (writeSeqSetWriteReady u).write_state ≠ .increment_group := by
  cases hp : u.path3 with
  | none => simp [writeSeqSetWriteReady, hp]
  | some p3 =>
      simp only [writeSeqSetWriteReady, hp]
      split <;> simp

private theorem writeSeqCheckBit_not_increment (u : AgentState ψ)
    (hu : u.write_state ≠ .increment_group) :
    (writeSeqCheckBit u).write_state ≠ .increment_group := by
  cases hp : u.path3 with
  | none => simpa [writeSeqCheckBit, hp] using hu
  | some p3 =>
      simp only [writeSeqCheckBit, hp]
      change checkBitWS u.bit p3.bit ≠ .increment_group
      let b : Nat := if u.bit then 1 else 0
      by_cases heq : b = p3.bit
      · simp [checkBitWS, b, heq]
      · by_cases hgt : b > p3.bit
        · simp [checkBitWS, b, heq, hgt]
        · simp [checkBitWS, b, heq, hgt]

private theorem writeSeqCompare_not_increment (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hl : l.write_state ≠ .increment_group)
    (hr : r.write_state ≠ .increment_group) :
    let q := writeSeqCompare hψ l r
    q.1.write_state ≠ .increment_group ∧
      q.2.write_state ≠ .increment_group := by
  let r0 := if r.label = ⟨0, hψ⟩ ∧ r.write_state = .ready then
    writeSeqCheckBit r else r
  have hr0 : r0.write_state ≠ .increment_group := by
    dsimp only [r0]
    split
    · exact writeSeqCheckBit_not_increment r hr
    · exact hr
  let r1 := if l.label.val < ψ - 1 ∧ l.write_state = .equal ∧
      r0.write_state = .ready then writeSeqCheckBit r0 else r0
  have hr1 : r1.write_state ≠ .increment_group := by
    dsimp only [r1]
    split
    · exact writeSeqCheckBit_not_increment r0 hr0
    · exact hr0
  exact ⟨hl, hr1⟩

private theorem writeSeqCommands_writeState_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := writeSeqCommands hψ l r
    q.1.write_state = l.write_state ∧ q.2.write_state = r.write_state := by
  simp only [writeSeqCommands, writeSeqSetWriteAct, writeSeqFinalR]
  repeat (first | constructor | rfl | split)

private theorem writeSeqPrepare_no_increment_state (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := writeSeqPrepare hψ l r
    q.1.write_state ≠ .increment_group ∧
      q.2.write_state ≠ .increment_group := by
  let q0 := writeSeqReady l r
  have h0 : q0.1.write_state ≠ .increment_group ∧
      q0.2.write_state ≠ .increment_group :=
    ⟨writeSeqSetWriteReady_not_increment l,
      writeSeqSetWriteReady_not_increment r⟩
  let q1 := writeSeqCompare hψ q0.1 q0.2
  have h1 := writeSeqCompare_not_increment hψ q0.1 q0.2 h0.1 h0.2
  have hframe := writeSeqCommands_writeState_frame hψ q1.1 q1.2
  exact ⟨hframe.1 ▸ h1.1, hframe.2 ▸ h1.2⟩

/-- Algorithm-16 preparation removes arbitrary old `write_state=increment_group`
from both endpoints.  The prepared gate therefore needs to inspect only the
pending `write` action; this theorem does not apply to direct arbitrary inputs
to Algorithm 19. -/
theorem writeSeqThroughPrepare_no_increment_state (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := writeSeqThroughPrepare hψ l r
    q.1.write_state ≠ .increment_group ∧
      q.2.write_state ≠ .increment_group := by
  unfold writeSeqThroughPrepare
  dsimp only
  exact writeSeqPrepare_no_increment_state hψ _ _

/-- When neither prepared endpoint is changed by the gate, the write stage is
exactly Algorithm 16's old composition. -/
theorem writeSeqIncrementGate_eq_writeSeq_of_fixed (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hl : gatePreparedIncrement (writeSeqThroughPrepare hψ l r).1 =
      (writeSeqThroughPrepare hψ l r).1)
    (hr : gatePreparedIncrement (writeSeqThroughPrepare hψ l r).2 =
      (writeSeqThroughPrepare hψ l r).2) :
    writeSeqIncrementGate hψ l r = writeSeq hψ l r := by
  simp [writeSeqIncrementGate, writeSeq, hl, hr]

/-- Full repaired audit transition: Algorithms 1–15 retain the existing
saturated-WAIT/no-collision semantics; only the prepared write boundary changes. -/
def ppllWriteIncrementGate (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeWrite hψ κ l r
  writeSeqIncrementGate hψ q.1 q.2

/-! ## Numeric-domain closure

The existing prefix-domain theorem is private to `DomainClosure`.  The proof
below composes its public stage lemmas directly.  For Algorithm 16's enum-only
sub-stages, small count/payload frame lemmas expose why the numeric domain is
unchanged.
-/

private theorem domain_of_count_payload_eq (input output : AgentState ψ)
    (hin : input.inProtocolDomain κ)
    (hcount : output.count = input.count)
    (hpayload : PayloadView.ofState output = PayloadView.ofState input) :
    output.inProtocolDomain κ := by
  rw [inProtocolDomain_iff] at hin ⊢
  exact ⟨hcount ▸ hin.1, hpayload ▸ hin.2⟩

private theorem unchanged_pair_inProtocolDomain
    (q : AgentState ψ × AgentState ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ)
    (h : (q.1.count = l.count ∧
          PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧
          PayloadView.ofState q.2 = PayloadView.ofState r)) :
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ :=
  ⟨domain_of_count_payload_eq l q.1 hl h.1.1 h.1.2,
    domain_of_count_payload_eq r q.2 hr h.2.1 h.2.2⟩

private theorem writeSeqLeaderMove_count_payload (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := writeSeqLeaderMove hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [writeSeqLeaderMove]
  repeat (first | constructor | rfl | split)

private theorem groupInfoStart_count_payload (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := groupInfoStart hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [groupInfoStart]
  repeat (first | constructor | rfl | split)

private theorem groupInfoSet_count_payload (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := groupInfoSet hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [groupInfoSet]
  repeat (first | constructor | rfl | split)

private theorem groupInfoUnset_count_payload (l r : AgentState ψ) :
    let q := groupInfoUnset l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [groupInfoUnset]
  repeat (first | constructor | rfl | split)

private theorem groupInfo_public_inProtocolDomain (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := groupInfo hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  rw [groupInfo_eq_staged]
  let q0 := groupInfoStart hψ l r
  let q1 := groupInfoSet hψ q0.1 q0.2
  have h0 := unchanged_pair_inProtocolDomain q0 l r hl hr
    (groupInfoStart_count_payload hψ l r)
  have h1 := unchanged_pair_inProtocolDomain q1 q0.1 q0.2 h0.1 h0.2
    (groupInfoSet_count_payload hψ q0.1 q0.2)
  exact unchanged_pair_inProtocolDomain
    (groupInfoUnset q1.1 q1.2) q1.1 q1.2 h1.1 h1.2
    (groupInfoUnset_count_payload q1.1 q1.2)

private theorem writeSeqReady_count_payload (l r : AgentState ψ) :
    let q := writeSeqReady l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [writeSeqReady, writeSeqSetWriteReady]
  repeat (first | constructor | rfl | split)

private theorem writeSeqCompare_count_payload (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := writeSeqCompare hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [writeSeqCompare, writeSeqCheckBit]
  repeat (first | constructor | rfl | split)

private theorem writeSeqCommands_count_payload (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := writeSeqCommands hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [writeSeqCommands, writeSeqSetWriteAct, writeSeqFinalR]
  repeat (first | constructor | rfl | split)

private theorem writeSeqThroughPrepare_inProtocolDomain (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := writeSeqThroughPrepare hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := writeSeqLeaderMove hψ l r
  let q1 := groupInfo hψ q0.1 q0.2
  let q2 := writeSeqGenerate hψ q1.1 q1.2
  let q3 := writeSeqReady q2.1 q2.2
  let q4 := writeSeqCompare hψ q3.1 q3.2
  have h0 := unchanged_pair_inProtocolDomain q0 l r hl hr
    (writeSeqLeaderMove_count_payload hψ l r)
  have h1 := groupInfo_public_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  have h2 : q2.1.inProtocolDomain κ ∧ q2.2.inProtocolDomain κ := by
    change
      let q := writeSeqGenerate hψ q1.1 q1.2
      q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
    unfold writeSeqGenerate
    split
    · exact gensigWriteseq_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
    · exact h1
  have h3 := unchanged_pair_inProtocolDomain q3 q2.1 q2.2 h2.1 h2.2
    (writeSeqReady_count_payload q2.1 q2.2)
  have h4 := unchanged_pair_inProtocolDomain q4 q3.1 q3.2 h3.1 h3.2
    (writeSeqCompare_count_payload hψ q3.1 q3.2)
  change
    let q := writeSeqCommands hψ q4.1 q4.2
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
  exact unchanged_pair_inProtocolDomain
    (writeSeqCommands hψ q4.1 q4.2) q4.1 q4.2 h4.1 h4.2
    (writeSeqCommands_count_payload hψ q4.1 q4.2)

/-- The gated Algorithm-16 stage preserves every declared numeric range.
This public boundary theorem lets combined repairs reuse the prepared gate
without duplicating the long Algorithm-16 domain proof. -/
theorem writeSeqIncrementGate_inProtocolDomain
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := writeSeqIncrementGate hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := writeSeqThroughPrepare hψ l r
  have h0 := writeSeqThroughPrepare_inProtocolDomain hψ l r hl hr
  let lGate := gatePreparedIncrement q0.1
  let rGate := gatePreparedIncrement q0.2
  have hlGate := gatePreparedIncrement_inProtocolDomain q0.1 h0.1
  have hrGate := gatePreparedIncrement_inProtocolDomain q0.2 h0.2
  let q1 := writeAction hψ lGate rGate
  have h1 := writeAction_inProtocolDomain hψ lGate rGate hlGate hrGate
  exact moveWsig_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2

private theorem ppllSaturatedBeforeWrite_public_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := ppllSaturatedBeforeWrite hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := pPsi hψ l r
  let q1 := genSigSaturated hψ κ q0.1 q0.2
  let q2 := cleanSig hψ q1.1 q1.2
  let q3 := eliminateSig hψ q2.1 q2.2
  let q4 := sigMove hψ q3.1 q3.2
  let q5 := checkSig hψ q4.1 q4.2
  let q6 := disappear hψ q5.1 q5.2
  let q7 := compareSig hψ q6.1 q6.2
  let q8 := suppressSig hψ q7.1 q7.2
  have h0 := pPsi_inProtocolDomain hψ l r hl hr
  have h1 := genSigSaturated_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  have h2 := cleanSig_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
  have h3 := eliminateSig_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2
  have h4 := sigMove_inProtocolDomain hψ q3.1 q3.2 h3.1 h3.2
  have h5 := checkSig_inProtocolDomain hψ q4.1 q4.2 h4.1 h4.2
  have h6 := disappear_inProtocolDomain hψ q5.1 q5.2 h5.1 h5.2
  have h7 := compareSig_inProtocolDomain hψ q6.1 q6.2 h6.1 h6.2
  have h8 := suppressSig_inProtocolDomain hψ q7.1 q7.2 h7.1 h7.2
  exact eliminateLeadersNoCollision_inProtocolDomain
    hψ q8.1 q8.2 h8.1 h8.2

/-- The complete prepared-increment gate preserves every declared numeric
range, including on malformed raw inputs that already satisfy the range. -/
theorem ppllWriteIncrementGate_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := ppllWriteIncrementGate hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := ppllSaturatedBeforeWrite hψ κ l r
  have h0 := ppllSaturatedBeforeWrite_public_inProtocolDomain
    hψ κ l r hl hr
  let q1 := writeSeqThroughPrepare hψ q0.1 q0.2
  have h1 := writeSeqThroughPrepare_inProtocolDomain
    hψ q0.1 q0.2 h0.1 h0.2
  let lGate := gatePreparedIncrement q1.1
  let rGate := gatePreparedIncrement q1.2
  have hlGate := gatePreparedIncrement_inProtocolDomain q1.1 h1.1
  have hrGate := gatePreparedIncrement_inProtocolDomain q1.2 h1.2
  let q2 := writeAction hψ lGate rGate
  have h2 := writeAction_inProtocolDomain hψ lGate rGate hlGate hrGate
  exact moveWsig_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2

/-! ## Existing finite carrier and exact erasure -/

attribute [local irreducible] ppllWriteIncrementGate

/-- Total finite transition on the unchanged bounded carrier. -/
def boundedWriteIncrementGateTransition (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedAgentState ψ κ) :
    BoundedAgentState ψ κ × BoundedAgentState ψ κ :=
  let q := ppllWriteIncrementGate hψ κ l.erase r.erase
  let hq := ppllWriteIncrementGate_inProtocolDomain hψ κ l.erase r.erase
    l.erase_inProtocolDomain r.erase_inProtocolDomain
  (BoundedAgentState.ofDomain q.1 hq.1,
    BoundedAgentState.ofDomain q.2 hq.2)

/-- Finite execution erases exactly to the separately named write-gate audit
transition, not to the old transition on T8. -/
theorem erase_boundedWriteIncrementGateTransition
    (hψ : ψ > 0) (κ : Nat) (l r : BoundedAgentState ψ κ) :
    let q := boundedWriteIncrementGateTransition hψ κ l r
    (q.1.erase, q.2.erase) = ppllWriteIncrementGate hψ κ l.erase r.erase := by
  let q := ppllWriteIncrementGate hψ κ l.erase r.erase
  let hq := ppllWriteIncrementGate_inProtocolDomain hψ κ l.erase r.erase
    l.erase_inProtocolDomain r.erase_inProtocolDomain
  change ((BoundedAgentState.ofDomain q.1 hq.1).erase,
    (BoundedAgentState.ofDomain q.2 hq.2).erase) = q
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Packaged finite protocol for the local write gate. -/
def boundedWriteIncrementGateProtocol (hψ : ψ > 0) (κ : Nat) :
    PopulationProtocol where
  Q := BoundedAgentState ψ κ
  Y := LeaderOutput
  transition := boundedWriteIncrementGateTransition hψ κ
  output := fun s => AgentState.outputFn s.erase

/-- The gate adds no state: its certificate is definitionally the old bounded
state certificate. -/
def writeIncrementGateStateCertificate (ψ κ : Nat) :
    ExhaustiveList (BoundedAgentState ψ κ) :=
  PPLLFinite.boundedAgentState ψ κ

/-- Prepared increment gating reuses a duplicate-free certificate. -/
theorem writeIncrementGateStateCertificate_values_nodup (ψ κ : Nat) :
    (writeIncrementGateStateCertificate ψ κ).values.Nodup :=
  PPLLFinite.boundedAgentState_values_nodup ψ κ

/-- Prepared increment gating has exact semantic-cardinality factor one. -/
theorem writeIncrementGateStateCertificate_values_length (ψ κ : Nat) :
    (writeIncrementGateStateCertificate ψ κ).values.length =
      (PPLLFinite.boundedAgentState ψ κ).values.length := by
  rfl

/-- Every gated physical state retains the existing explicit finite index. -/
theorem writeIncrementGateState_decode_surjective (ψ κ : Nat) :
    Function.Surjective (writeIncrementGateStateCertificate ψ κ).decode :=
  (writeIncrementGateStateCertificate ψ κ).decode_surjective

end PPLLWriteIncrementGate

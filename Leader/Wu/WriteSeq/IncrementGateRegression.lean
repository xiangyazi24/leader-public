import Leader.Wu.WriteSeq.IncrementGate
import Leader.Wu.Safety.Counterexamples

/-!
# Hostile regressions for the prepared increment gate

These checks separate the exact T8 repair from claims it cannot support.  The
gate blocks an orphan command with no `path3`, including a malformed raw flag
that creates a fresh command during Algorithm-16 preparation.  It preserves a
flag-zero command genuinely produced by `writeSeqFinalR`—and therefore also
preserves an arbitrary forged local twin.  The latter is the explicit boundary
between local support and historical lineage.
-/

namespace PPLLWriteIncrementGateRegression

open PPLL PPLLRepair PPLLCounterexample PPLLWriteIncrementGate

/-! ## T8 and maximal local garbage -/

/-- Full gated interaction on T8's original orphan pair. -/
def t8WriteGatePair : AgentState 2 × AgentState 2 :=
  ppllWriteIncrementGate (by omega) 10
    (writeCounterConfig 2) (writeCounterConfig 3)

/-- The original unsupported terminal increment no longer flips its bit. -/
theorem write_gate_blocks_exact_t8 :
    t8WriteGatePair.2.bit = false := by
  decide

/-- Maximize the existing write-control surface while retaining T8's decisive
absence of `path3`. -/
def maximalWriteOrphan (u : AgentState 2) : AgentState 2 :=
  let u := { u with path3 := none }
  let u := { u with write_state := WriteState.increment_group }
  let u := { u with write := WriteAction.increment_group }
  let u := { u with last := true, last_set := true, last_unset := true }
  let u := { u with b_carry := true, gen_ws := true, ws_echo := true }
  { u with signal_ws := true }

/-- The gate itself clears the pending increment action; the full interaction
cannot reconstruct an executable increment from the remaining current garbage. -/
theorem write_gate_blocks_maximal_pathless_orphan :
    (gatePreparedIncrement
      (maximalWriteOrphan (writeCounterConfig 3))).write = .none ∧
    (ppllWriteIncrementGate (by omega) 10
      (maximalWriteOrphan (writeCounterConfig 2))
      (maximalWriteOrphan (writeCounterConfig 3))).2.bit = false := by
  decide

/-! ## Raw malformed flag -/

/-- Neutral raw one-label state used only to audit total behavior outside the
bounded physical value domain. -/
private def rawState1 : AgentState 1 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := true, state := .none, path := .bot, reset := false,
    carry := false, count := 0, label := 0, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := 0, bullet := 0, shield := true, write_state := .none,
    write := .none, last := false, last_set := false,
    last_unset := false, b_carry := false, gen_ws := false,
    ws_echo := false, signal_ws := false }

private def rawBadFlagRight : AgentState 1 :=
  { rawState1 with path3 := some ⟨0, 0, 2⟩ }

/-- The malformed flag is outside the physical domain. -/
theorem raw_bad_flag_outside_domain :
    ¬rawBadFlagRight.inProtocolDomain 10 := by
  simp [rawBadFlagRight, rawState1, AgentState.inProtocolDomain]

/-- Placement after preparation is essential: `writeSeqFinalR` may create an
increment from raw flag two, but the prepared gate removes it before Algorithm
19, so the bit remains zero. -/
theorem prepared_gate_blocks_fresh_raw_bad_flag_increment :
    (ppllWriteIncrementGate (by omega : 1 > 0) 10
      rawState1 rawBadFlagRight).2.bit = false := by
  decide

/-! ## Genuine command and unavoidable forged twin -/

/-- Terminal flag-zero comparison state from which Algorithm 16 creates the
intended increment action. -/
def genuineTerminalInput : AgentState 2 :=
  { state2 1 with path3 := some ⟨1, 0, 0⟩, write_state := .equal }

/-- Command obtained by calling the actual Algorithm-16 helper, not hand-forged. -/
def genuinePendingIncrement : AgentState 2 :=
  writeSeqFinalR genuineTerminalInput

/-- Execute Algorithm 19 on the supported prepared command. -/
def genuineIncrementAction : AgentState 2 × AgentState 2 :=
  writeAction (by omega : 2 > 0) (state2 0)
    (gatePreparedIncrement genuinePendingIncrement)

/-- The local gate is identity on the genuine flag-zero command and preserves
its intended zero-to-one binary increment. -/
theorem write_gate_preserves_genuine_terminal_increment :
    genuinePendingIncrement.write = .increment_group ∧
      gatePreparedIncrement genuinePendingIncrement = genuinePendingIncrement ∧
      genuineIncrementAction.2.bit = true := by
  decide

/-- Arbitrary initialization may forge the exact same local support pattern. -/
def forgedFlagZeroIncrement : AgentState 2 :=
  { state2 1 with path3 := some ⟨1, 0, 0⟩, write := .increment_group }

/-- Local support is not provenance: the forged flag-zero twin also passes and
can flip a bit.  This prevents any `GroupIDBoundarySafe` or lineage upgrade. -/
theorem write_gate_preserves_forged_flag_zero_twin :
    gatePreparedIncrement forgedFlagZeroIncrement = forgedFlagZeroIncrement ∧
      (writeAction (by omega : 2 > 0) (state2 0)
        (gatePreparedIncrement forgedFlagZeroIncrement)).2.bit = true := by
  decide

/-! ## Algorithm-20 orphan output and next-interaction revalidation -/

private def algorithm20ExportLeft : AgentState 2 :=
  { state2 0 with path3 := some ⟨0, 0, 0⟩, write := .increment_group }

private def algorithm20ExportRight : AgentState 2 := state2 1

private def algorithm20ExportAfter : AgentState 2 × AgentState 2 :=
  writeSeqAfterPrepare (by omega : 2 > 0)
    (gatePreparedIncrement algorithm20ExportLeft)
    (gatePreparedIncrement algorithm20ExportRight)

/-- Algorithm 20 can separate a supported command from its path after Algorithm
19, so local support is not an output invariant. -/
theorem algorithm20_can_export_increment_orphan :
    algorithm20ExportAfter.1.path3 = some ⟨0, 0, 0⟩ ∧
      algorithm20ExportAfter.1.write = .none ∧
      algorithm20ExportAfter.2.path3 = none ∧
      algorithm20ExportAfter.2.write = .increment_group := by
  decide

private def algorithm20OrphanNext : AgentState 2 × AgentState 2 :=
  writeSeqIncrementGate (by omega : 2 > 0)
    (state2 0) algorithm20ExportAfter.2

/-- The exported orphan may exist between interactions but cannot execute an
increment before the next prepared gate revalidates it. -/
theorem algorithm20_orphan_cannot_execute_before_next_gate :
    algorithm20ExportAfter.2.bit = false ∧
      algorithm20OrphanNext.2.bit = false := by
  decide

/-- Domain-valid ψ=1 flag-zero preparation supplies an end-to-end positive:
prepare, `writeSeqFinalR`, gate, and Algorithm 19 all occur in one write call. -/
private def rawGoodFlagRight : AgentState 1 :=
  { rawState1 with path3 := some ⟨0, 0, 0⟩ }

/-- The stricter gate rejects malformed nonzero flags but preserves the same-call
flag-zero increment at the full write-stage boundary. -/
theorem prepared_gate_preserves_same_interaction_flag_zero_increment :
    (writeSeqIncrementGate (by omega : 1 > 0)
      rawState1 rawGoodFlagRight).2.bit = true := by
  decide

/-! ## Exact finite T8 execution -/

/-- Reify T8 into the unchanged physical bounded carrier. -/
def finiteT8WriteConfig : Fin 4 → BoundedAgentState 2 10 := fun i =>
  BoundedAgentState.ofDomain (writeCounterConfig i)
    (writeCounterConfig_inProtocolDomain i)

/-- One finite gated interaction at T8's bad edge. -/
def finiteT8WriteAfter : Fin 4 → BoundedAgentState 2 10 :=
  PopulationProtocol.step
    (boundedWriteIncrementGateProtocol (by omega) 10)
    ring4 finiteT8WriteConfig 2

/-- The exact finite physical execution leaves the terminal follower bit
unchanged; this is not inferred only from the audit-level test. -/
theorem finite_write_gate_blocks_t8 :
    (finiteT8WriteConfig 3).bit = false ∧
      (finiteT8WriteAfter 3).bit = false := by
  decide

end PPLLWriteIncrementGateRegression

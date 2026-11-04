import Leader.Wu.Protocol.Repairs
import Leader.Wu.Safety.CorrectedFormulation
import Leader.Wu.Protocol.BoundedProtocol

set_option autoImplicit false

/-! # GAP11 kernel: does the escape word [0,1,0] produce a unique leader?
  Witness: n=3, ψ=2, κ=2.
  Agent 0: leader=true, label=0, all else default
  Agent 1: leader=true, label=0, all else default
  Agent 2: leader=false, label=1, path2=(0,0,0,3), all else default -/

open PPLL PPLLRepair PPLLResearchFormulation

private theorem hψ2 : 0 < 2 := by decide
private def ring3 : DirectedRing 3 := ⟨by omega⟩

-- ═══════════════════════════════════════════════
-- Unbounded carrier (AgentState 2)
-- ═══════════════════════════════════════════════

private def defA (lab : Fin 2) : AgentState 2 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := .none, path := .bot, reset := false, carry := false,
    count := 0, label := lab, h_field := false, path2 := none,
    path3 := none, path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := ⟨0, by decide⟩,
    bullet := ⟨0, by decide⟩, shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false, b_carry := false,
    gen_ws := false, ws_echo := false, signal_ws := false }

private def witnessU : Fin 3 → AgentState 2
  | ⟨0, _⟩ => { defA ⟨0, by decide⟩ with leader := true }
  | ⟨1, _⟩ => { defA ⟨0, by decide⟩ with leader := true }
  | ⟨2, _⟩ => { defA ⟨1, by decide⟩ with path2 := some ⟨0, 0, 0, 3⟩ }

private def TU := ppllSaturatedNoCollision hψ2 2

private def escW : DetSchedule 3 :=
  [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩]

private def afterU : Fin 3 → AgentState 2 :=
  runLocalSchedule ring3 TU witnessU escW

-- Agent 0 loses leader, agent 1 keeps it, agent 2 stays follower
set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem escU_a0 : (afterU ⟨0, by omega⟩).leader = false := by decide
set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem escU_a1 : (afterU ⟨1, by omega⟩).leader = true := by decide
set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem escU_a2 : (afterU ⟨2, by omega⟩).leader = false := by decide

-- ═══════════════════════════════════════════════
-- Bounded carrier (BoundedAgentState 2 2)
-- ═══════════════════════════════════════════════

private def defB (lab : Fin 2) : BoundedAgentState 2 2 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := .none, path := .bot, reset := false, carry := false,
    count := ⟨0, by omega⟩, label := lab, h_field := false, path2 := none,
    path3 := none, path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := ⟨0, by decide⟩,
    bullet := ⟨0, by decide⟩, shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false, b_carry := false,
    gen_ws := false, ws_echo := false, signal_ws := false }

private def witnessB : Fin 3 → BoundedAgentState 2 2
  | ⟨0, _⟩ => { defB ⟨0, by decide⟩ with leader := true }
  | ⟨1, _⟩ => { defB ⟨0, by decide⟩ with leader := true }
  | ⟨2, _⟩ => { defB ⟨1, by decide⟩ with
      path2 := some ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨2, by omega⟩⟩ }

private def TB := boundedTransition hψ2 2

private def afterB : Fin 3 → BoundedAgentState 2 2 :=
  runLocalSchedule ring3 TB witnessB escW

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem escB_a0 : (afterB ⟨0, by omega⟩).leader = false := by decide
set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem escB_a1 : (afterB ⟨1, by omega⟩).leader = true := by decide
set_option maxHeartbeats 80000000 in
set_option maxRecDepth 100000 in
theorem escB_a2 : (afterB ⟨2, by omega⟩).leader = false := by decide

#print axioms escU_a0
#print axioms escU_a1
#print axioms escB_a0
#print axioms escB_a1

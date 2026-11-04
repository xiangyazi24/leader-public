import Leader.Wu.Elimination.SinkStallWitness
import Leader.Wu.Protocol.Algorithm

open LDSinkGapCleanup LDSinkStallWitness

namespace LDLiteralKernelOnStall

set_option autoImplicit false

/-!
The literal Algorithm-15 kernel is PPLL.eliminateLeaders. This file calls
that imported definition directly; it does not copy or modify either kernel.

On edge (0,1), FIRE is inert and the shield blocks deletion. The literal
SIGNAL stage nevertheless seeds signal_B = 1 at the live-bullet follower.
The sink repair instead leaves that signal at zero.

The configuration inequality uses one field projection, not decidability
of equality on functions or on the entire AgentState record. The only
proof tactics used below are rfl and ordinary decide; congrArg is applied
as a proof term. This file has not been compiler-tested here.
-/

/-- Exact literal output: only the responder's absence signal changes. -/
theorem literal_edge0_pair :
    PPLL.eliminateLeaders (by decide : 1 > 0) (stall 0) (stall 1) =
      (stall 0, { (stall 1) with signal_B := (1 : Fin 2) }) := by
  rfl

/-- The literal transcription seeds signal one despite the live bullet. -/
theorem literal_edge0_signal :
    (PPLL.eliminateLeaders (by decide : 1 > 0)
      (stall 0) (stall 1)).2.signal_B = (1 : Fin 2) := by
  rfl

/-- In contrast, the imported sink repair clamps this signal to zero. -/
theorem repair_edge0_signal :
    (sinkKernel (by decide : 1 > 0)
      (stall 0) (stall 1)).2.signal_B = (0 : Fin 2) := by
  rfl

/-- The same signal change is present after the actual ring update. -/
theorem literal_edge0_step_signal :
    (updatePair stall 0 (rightNeighbor 0)
      (PPLL.eliminateLeaders (by decide : 1 > 0)
        (stall 0) (stall 1)) 1).signal_B = (1 : Fin 2) := by
  rfl

/-- Equality with stall would identify signal one with its original zero. -/
theorem literal_edge0_changes :
    updatePair stall 0 (rightNeighbor 0)
      (PPLL.eliminateLeaders (by decide : 1 > 0)
        (stall 0) (stall 1)) ≠ stall :=
  fun h =>
    (by decide : (1 : Fin 2) ≠ (0 : Fin 2))
      (congrArg (fun C : Fin 6 → AgentState 1 => (C 1).signal_B) h)

end LDLiteralKernelOnStall

#print axioms LDLiteralKernelOnStall.literal_edge0_pair
#print axioms LDLiteralKernelOnStall.literal_edge0_signal
#print axioms LDLiteralKernelOnStall.repair_edge0_signal
#print axioms LDLiteralKernelOnStall.literal_edge0_step_signal
#print axioms LDLiteralKernelOnStall.literal_edge0_changes

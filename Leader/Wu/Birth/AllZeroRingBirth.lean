import Leader.Wu.Birth.LeaderlessEscapeConsumeControl

set_option autoImplicit false
set_option Elab.async false

namespace ZZAllZeroBirth

open PPLL

private def ring2 : DirectedRing 2 := ⟨by decide⟩

/-- Full neutral cell; only `phaseValue` and the physical label vary. -/
private def allZeroCell (phaseValue : Bool) (lab : Fin 2) : AgentState 2 :=
  { leader := false, probe := false, phase := phaseValue, bit := false,
    wait := false, state := MainState.none, path := PathInfo.bot,
    reset := false, carry := false, count := 0, label := lab,
    h_field := false, path2 := none, path3 := none,
    path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := WriteState.none,
    write := WriteAction.none, last := false,
    last_set := false, last_unset := false, b_carry := false,
    gen_ws := false, ws_echo := false, signal_ws := false }

/-- All bits, leaders, probes, and phases are false; labels are the sites. -/
def allZeroCfg : Fin 2 → AgentState 2 :=
  fun i => allZeroCell false i

/-- The same all-zero-bit follower ring, with every phase bit true. -/
def allZeroPhaseTrueCfg : Fin 2 → AgentState 2 :=
  fun i => allZeroCell true i

abbrev Config := ZZRepairAll10Consume.protocolAll10Consume.Configuration 2

private def consumeStep (C : Config) (e : Fin 2) : Config :=
  ZZRepairAll10Consume.protocolAll10Consume.step ring2 C e

private def hasLeader (C : Config) : Bool :=
  (C (0 : Fin 2)).leader || (C (1 : Fin 2)).leader

/-- Check the current node and recursively enumerate both scheduled edges.
Thus depth `d` means every schedule of length at most `d`. -/
private def birthWithinAux : Nat → Config → Bool
  | 0, C => hasLeader C
  | d + 1, C =>
      hasLeader C ||
      birthWithinAux d (consumeStep C (0 : Fin 2)) ||
      birthWithinAux d (consumeStep C (1 : Fin 2))

def birthWithin (d : Nat) : Bool :=
  birthWithinAux d allZeroCfg

def birthWithinPhaseTrue (d : Nat) : Bool :=
  birthWithinAux d allZeroPhaseTrueCfg

/-- Kernel verdict for the all-false phase branch. -/
theorem allzero_births : birthWithin 6 = true := by
  decide +kernel

#print axioms ZZAllZeroBirth.allzero_births

/-- Kernel verdict for the all-true phase branch. -/
theorem allzero_phase_true_births : birthWithinPhaseTrue 6 = true := by
  decide +kernel

#print axioms ZZAllZeroBirth.allzero_phase_true_births

end ZZAllZeroBirth

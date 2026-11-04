import Leader.Wu.Birth.SpatialSourceSpliceFixture
import Leader.Wu.Birth.FiniteTraceCertificate

set_option autoImplicit false

/-!
# Spatial source splice trace, steps 0-7: GEN at edge ten

One-step rows of the 32-agent counterexample trace checked in `BirthSpatialSourceSpliceCertificate`; each row
states the transition output of one interaction. Steps are kept in trace order.
-/

/-! Step 0 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample
abbrev S := ExpiringAgentState 2 2 16
abbrev ring : DirectedRing 32 := ringThirtyTwo
def T : S → S → S × S := singleUseFullTransition twoPositive 2 16
def C00 : Vector S 32 := Vector.ofFn initial

def outL00 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def outR00 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def row00 : Row 32 S :=
  (⟨10, by decide⟩, outL00, outR00)
theorem row00_ok :
    T (C00.get row00.1)
      (C00.get (ring.rightNeighbor row00.1)) = row00.2 := by
  decide
def C01 : Vector S 32 := writeRow ring C00 row00
end BirthSpatialSourceSpliceCertificate

/-! Step 1 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL01 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def outR01 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def row01 : Row 32 S :=
  (⟨10, by decide⟩, outL01, outR01)
theorem row01_ok :
    T (C01.get row01.1)
      (C01.get (ring.rightNeighbor row01.1)) = row01.2 := by
  decide
def C02 : Vector S 32 := writeRow ring C01 row01
end BirthSpatialSourceSpliceCertificate

/-! Step 2 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL02 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def outR02 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def row02 : Row 32 S :=
  (⟨10, by decide⟩, outL02, outR02)
theorem row02_ok :
    T (C02.get row02.1)
      (C02.get (ring.rightNeighbor row02.1)) = row02.2 := by
  decide
def C03 : Vector S 32 := writeRow ring C02 row02
end BirthSpatialSourceSpliceCertificate

/-! Step 3 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL03 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 12 }

def outR03 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 1, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 12 }

def row03 : Row 32 S :=
  (⟨10, by decide⟩, outL03, outR03)
theorem row03_ok :
    T (C03.get row03.1)
      (C03.get (ring.rightNeighbor row03.1)) = row03.2 := by
  decide
def C04 : Vector S 32 := writeRow ring C03 row03
end BirthSpatialSourceSpliceCertificate

/-! Step 4 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL04 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 11 }

def outR04 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 1, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 11 }

def row04 : Row 32 S :=
  (⟨10, by decide⟩, outL04, outR04)
theorem row04_ok :
    T (C04.get row04.1)
      (C04.get (ring.rightNeighbor row04.1)) = row04.2 := by
  decide
def C05 : Vector S 32 := writeRow ring C04 row04
end BirthSpatialSourceSpliceCertificate

/-! Step 5 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL05 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 10 }

def outR05 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 1, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 10 }

def row05 : Row 32 S :=
  (⟨10, by decide⟩, outL05, outR05)
theorem row05_ok :
    T (C05.get row05.1)
      (C05.get (ring.rightNeighbor row05.1)) = row05.2 := by
  decide
def C06 : Vector S 32 := writeRow ring C05 row05
end BirthSpatialSourceSpliceCertificate

/-! Step 6 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL06 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 9 }

def outR06 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 1, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 9 }

def row06 : Row 32 S :=
  (⟨10, by decide⟩, outL06, outR06)
theorem row06_ok :
    T (C06.get row06.1)
      (C06.get (ring.rightNeighbor row06.1)) = row06.2 := by
  decide
def C07 : Vector S 32 := writeRow ring C06 row06
end BirthSpatialSourceSpliceCertificate

/-! Step 7 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL07 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR07 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 2, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row07 : Row 32 S :=
  (⟨10, by decide⟩, outL07, outR07)
theorem row07_ok :
    T (C07.get row07.1)
      (C07.get (ring.rightNeighbor row07.1)) = row07.2 := by
  decide
def C08 : Vector S 32 := writeRow ring C07 row07
end BirthSpatialSourceSpliceCertificate

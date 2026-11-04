import Leader.Wu.Birth.SpatialSourceSpliceGenTen

set_option autoImplicit false

/-!
# Spatial source splice trace, steps 8-15: GEN at edge six

One-step rows of the 32-agent counterexample trace checked in `BirthSpatialSourceSpliceCertificate`; each row
states the transition output of one interaction. Steps are kept in trace order.
-/

/-! Step 8 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL08 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def outR08 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def row08 : Row 32 S :=
  (⟨6, by decide⟩, outL08, outR08)
theorem row08_ok :
    T (C08.get row08.1)
      (C08.get (ring.rightNeighbor row08.1)) = row08.2 := by
  decide
def C09 : Vector S 32 := writeRow ring C08 row08
end BirthSpatialSourceSpliceCertificate

/-! Step 9 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL09 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def outR09 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def row09 : Row 32 S :=
  (⟨6, by decide⟩, outL09, outR09)
theorem row09_ok :
    T (C09.get row09.1)
      (C09.get (ring.rightNeighbor row09.1)) = row09.2 := by
  decide
def C10 : Vector S 32 := writeRow ring C09 row09
end BirthSpatialSourceSpliceCertificate

/-! Step 10 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL10 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def outR10 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def row10 : Row 32 S :=
  (⟨6, by decide⟩, outL10, outR10)
theorem row10_ok :
    T (C10.get row10.1)
      (C10.get (ring.rightNeighbor row10.1)) = row10.2 := by
  decide
def C11 : Vector S 32 := writeRow ring C10 row10
end BirthSpatialSourceSpliceCertificate

/-! Step 11 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL11 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 12 }

def outR11 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 1, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 12 }

def row11 : Row 32 S :=
  (⟨6, by decide⟩, outL11, outR11)
theorem row11_ok :
    T (C11.get row11.1)
      (C11.get (ring.rightNeighbor row11.1)) = row11.2 := by
  decide
def C12 : Vector S 32 := writeRow ring C11 row11
end BirthSpatialSourceSpliceCertificate

/-! Step 12 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL12 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 11 }

def outR12 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 1, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 11 }

def row12 : Row 32 S :=
  (⟨6, by decide⟩, outL12, outR12)
theorem row12_ok :
    T (C12.get row12.1)
      (C12.get (ring.rightNeighbor row12.1)) = row12.2 := by
  decide
def C13 : Vector S 32 := writeRow ring C12 row12
end BirthSpatialSourceSpliceCertificate

/-! Step 13 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL13 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 10 }

def outR13 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 1, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 10 }

def row13 : Row 32 S :=
  (⟨6, by decide⟩, outL13, outR13)
theorem row13_ok :
    T (C13.get row13.1)
      (C13.get (ring.rightNeighbor row13.1)) = row13.2 := by
  decide
def C14 : Vector S 32 := writeRow ring C13 row13
end BirthSpatialSourceSpliceCertificate

/-! Step 14 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL14 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 9 }

def outR14 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 1, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 9 }

def row14 : Row 32 S :=
  (⟨6, by decide⟩, outL14, outR14)
theorem row14_ok :
    T (C14.get row14.1)
      (C14.get (ring.rightNeighbor row14.1)) = row14.2 := by
  decide
def C15 : Vector S 32 := writeRow ring C14 row14
end BirthSpatialSourceSpliceCertificate

/-! Step 15 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL15 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR15 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 2, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row15 : Row 32 S :=
  (⟨6, by decide⟩, outL15, outR15)
theorem row15_ok :
    T (C15.get row15.1)
      (C15.get (ring.rightNeighbor row15.1)) = row15.2 := by
  decide
def C16 : Vector S 32 := writeRow ring C15 row15
end BirthSpatialSourceSpliceCertificate

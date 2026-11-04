import Leader.Wu.Birth.SpatialSourceSpliceGenSix

set_option autoImplicit false

/-!
# Spatial source splice trace, steps 16-23: the six is compared

One-step rows of the 32-agent counterexample trace checked in `BirthSpatialSourceSpliceCertificate`; each row
states the transition output of one interaction. Steps are kept in trace order.
-/

/-! Step 16 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL16 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 2, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR16 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.some 1 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row16 : Row 32 S :=
  (⟨7, by decide⟩, outL16, outR16)
theorem row16_ok :
    T (C16.get row16.1)
      (C16.get (ring.rightNeighbor row16.1)) = row16.2 := by
  decide
def C17 : Vector S 32 := writeRow ring C16 row16
end BirthSpatialSourceSpliceCertificate

/-! Step 17 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL17 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := false, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR17 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 2, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 0), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row17 : Row 32 S :=
  (⟨6, by decide⟩, outL17, outR17)
theorem row17_ok :
    T (C17.get row17.1)
      (C17.get (ring.rightNeighbor row17.1)) = row17.2 := by
  decide
def C18 : Vector S 32 := writeRow ring C17 row17
end BirthSpatialSourceSpliceCertificate

/-! Step 18 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL18 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR18 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.CHECK_ready, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row18 : Row 32 S :=
  (⟨8, by decide⟩, outL18, outR18)
theorem row18_ok :
    T (C18.get row18.1)
      (C18.get (ring.rightNeighbor row18.1)) = row18.2 := by
  decide
def C19 : Vector S 32 := writeRow ring C18 row18
end BirthSpatialSourceSpliceCertificate

/-! Step 19 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL19 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 2, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR19 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.CHECK_ready, path := BoundedPathInfo.some 0 1, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := true }, stall := 16 }

def row19 : Row 32 S :=
  (⟨7, by decide⟩, outL19, outR19)
theorem row19_ok :
    T (C19.get row19.1)
      (C19.get (ring.rightNeighbor row19.1)) = row19.2 := by
  decide
def C20 : Vector S 32 := writeRow ring C19 row19
end BirthSpatialSourceSpliceCertificate

/-! Step 20 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL20 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.congest, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR20 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.congest, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def row20 : Row 32 S :=
  (⟨8, by decide⟩, outL20, outR20)
theorem row20_ok :
    T (C20.get row20.1)
      (C20.get (ring.rightNeighbor row20.1)) = row20.2 := by
  decide
def C21 : Vector S 32 := writeRow ring C20 row20
end BirthSpatialSourceSpliceCertificate

/-! Step 21 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL21 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.toss, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := true, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def outR21 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.congest, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def row21 : Row 32 S :=
  (⟨8, by decide⟩, outL21, outR21)
theorem row21_ok :
    T (C21.get row21.1)
      (C21.get (ring.rightNeighbor row21.1)) = row21.2 := by
  decide
def C22 : Vector S 32 := writeRow ring C21 row21
end BirthSpatialSourceSpliceCertificate

/-! Step 22 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL22 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 2, label := 1, h_field := false, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def outR22 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.toss_done, path := BoundedPathInfo.some 0 1, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := some { label := 0, bit := 0, position := 0, action := 4 }, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def row22 : Row 32 S :=
  (⟨7, by decide⟩, outL22, outR22)
theorem row22_ok :
    T (C22.get row22.1)
      (C22.get (ring.rightNeighbor row22.1)) = row22.2 := by
  decide
def C23 : Vector S 32 := writeRow ring C22 row22
end BirthSpatialSourceSpliceCertificate

/-! Step 23 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL23 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.less, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def outR23 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def row23 : Row 32 S :=
  (⟨8, by decide⟩, outL23, outR23)
theorem row23_ok :
    T (C23.get row23.1)
      (C23.get (ring.rightNeighbor row23.1)) = row23.2 := by
  decide
def C24 : Vector S 32 := writeRow ring C23 row23
end BirthSpatialSourceSpliceCertificate

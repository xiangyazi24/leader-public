import Leader.Wu.Birth.SpatialSourceSpliceExpiry

set_option autoImplicit false

/-!
# Spatial source splice trace, steps 41-59: the survivors compare

One-step rows of the 32-agent counterexample trace checked in `BirthSpatialSourceSpliceCertificate`; each row
states the transition output of one interaction. Steps are kept in trace order.
-/

/-! Step 41 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL41 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := true, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR41 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 0), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row41 : Row 32 S :=
  (⟨8, by decide⟩, outL41, outR41)
theorem row41_ok :
    T (C41.get row41.1)
      (C41.get (ring.rightNeighbor row41.1)) = row41.2 := by
  decide
def C42 : Vector S 32 := writeRow ring C41 row41
end BirthSpatialSourceSpliceCertificate

/-! Step 42 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL42 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR42 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.CHECK_ready, path := BoundedPathInfo.some 0 1, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := true }, stall := 16 }

def row42 : Row 32 S :=
  (⟨9, by decide⟩, outL42, outR42)
theorem row42_ok :
    T (C42.get row42.1)
      (C42.get (ring.rightNeighbor row42.1)) = row42.2 := by
  decide
def C43 : Vector S 32 := writeRow ring C42 row42
end BirthSpatialSourceSpliceCertificate

/-! Step 43 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL43 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := false, state := MainState.congest, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR43 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.congest, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 2, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def row43 : Row 32 S :=
  (⟨10, by decide⟩, outL43, outR43)
theorem row43_ok :
    T (C43.get row43.1)
      (C43.get (ring.rightNeighbor row43.1)) = row43.2 := by
  decide
def C44 : Vector S 32 := writeRow ring C43 row43
end BirthSpatialSourceSpliceCertificate

/-! Step 44 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL44 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := false, state := MainState.congest, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def outR44 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.congest, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 2, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def row44 : Row 32 S :=
  (⟨10, by decide⟩, outL44, outR44)
theorem row44_ok :
    T (C44.get row44.1)
      (C44.get (ring.rightNeighbor row44.1)) = row44.2 := by
  decide
def C45 : Vector S 32 := writeRow ring C44 row44
end BirthSpatialSourceSpliceCertificate

/-! Step 45 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL45 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def outR45 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := false, state := MainState.congest, path := BoundedPathInfo.some 0 1, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def row45 : Row 32 S :=
  (⟨9, by decide⟩, outL45, outR45)
theorem row45_ok :
    T (C45.get row45.1)
      (C45.get (ring.rightNeighbor row45.1)) = row45.2 := by
  decide
def C46 : Vector S 32 := writeRow ring C45 row45
end BirthSpatialSourceSpliceCertificate

/-! Step 46 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL46 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := false, state := MainState.congest, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def outR46 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.congest, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 2, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def row46 : Row 32 S :=
  (⟨10, by decide⟩, outL46, outR46)
theorem row46_ok :
    T (C46.get row46.1)
      (C46.get (ring.rightNeighbor row46.1)) = row46.2 := by
  decide
def C47 : Vector S 32 := writeRow ring C46 row46
end BirthSpatialSourceSpliceCertificate

/-! Step 47 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL47 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 2, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR47 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.some 1 1, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row47 : Row 32 S :=
  (⟨11, by decide⟩, outL47, outR47)
theorem row47_ok :
    T (C47.get row47.1)
      (C47.get (ring.rightNeighbor row47.1)) = row47.2 := by
  decide
def C48 : Vector S 32 := writeRow ring C47 row47
end BirthSpatialSourceSpliceCertificate

/-! Step 48 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL48 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := false, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR48 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 2, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 0), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row48 : Row 32 S :=
  (⟨10, by decide⟩, outL48, outR48)
theorem row48_ok :
    T (C48.get row48.1)
      (C48.get (ring.rightNeighbor row48.1)) = row48.2 := by
  decide
def C49 : Vector S 32 := writeRow ring C48 row48
end BirthSpatialSourceSpliceCertificate

/-! Step 49 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL49 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR49 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.CHECK_ready, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row49 : Row 32 S :=
  (⟨12, by decide⟩, outL49, outR49)
theorem row49_ok :
    T (C49.get row49.1)
      (C49.get (ring.rightNeighbor row49.1)) = row49.2 := by
  decide
def C50 : Vector S 32 := writeRow ring C49 row49
end BirthSpatialSourceSpliceCertificate

/-! Step 50 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL50 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 2, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR50 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.CHECK_ready, path := BoundedPathInfo.some 0 1, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := true }, stall := 16 }

def row50 : Row 32 S :=
  (⟨11, by decide⟩, outL50, outR50)
theorem row50_ok :
    T (C50.get row50.1)
      (C50.get (ring.rightNeighbor row50.1)) = row50.2 := by
  decide
def C51 : Vector S 32 := writeRow ring C50 row50
end BirthSpatialSourceSpliceCertificate

/-! Step 51 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL51 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.congest, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR51 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.congest, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def row51 : Row 32 S :=
  (⟨12, by decide⟩, outL51, outR51)
theorem row51_ok :
    T (C51.get row51.1)
      (C51.get (ring.rightNeighbor row51.1)) = row51.2 := by
  decide
def C52 : Vector S 32 := writeRow ring C51 row51
end BirthSpatialSourceSpliceCertificate

/-! Step 52 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL52 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.toss, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := true, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def outR52 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.congest, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def row52 : Row 32 S :=
  (⟨12, by decide⟩, outL52, outR52)
theorem row52_ok :
    T (C52.get row52.1)
      (C52.get (ring.rightNeighbor row52.1)) = row52.2 := by
  decide
def C53 : Vector S 32 := writeRow ring C52 row52
end BirthSpatialSourceSpliceCertificate

/-! Step 53 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL53 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 2, label := 1, h_field := true, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def outR53 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.toss_done, path := BoundedPathInfo.some 0 1, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := some { label := 0, bit := 0, position := 0, action := 4 }, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def row53 : Row 32 S :=
  (⟨11, by decide⟩, outL53, outR53)
theorem row53_ok :
    T (C53.get row53.1)
      (C53.get (ring.rightNeighbor row53.1)) = row53.2 := by
  decide
def C54 : Vector S 32 := writeRow ring C53 row53
end BirthSpatialSourceSpliceCertificate

/-! Step 54 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL54 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.less, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def outR54 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def row54 : Row 32 S :=
  (⟨12, by decide⟩, outL54, outR54)
theorem row54_ok :
    T (C54.get row54.1)
      (C54.get (ring.rightNeighbor row54.1)) = row54.2 := by
  decide
def C55 : Vector S 32 := writeRow ring C54 row54
end BirthSpatialSourceSpliceCertificate

/-! Step 55 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL55 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR55 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.some 1 1, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row55 : Row 32 S :=
  (⟨13, by decide⟩, outL55, outR55)
theorem row55_ok :
    T (C55.get row55.1)
      (C55.get (ring.rightNeighbor row55.1)) = row55.2 := by
  decide
def C56 : Vector S 32 := writeRow ring C55 row55
end BirthSpatialSourceSpliceCertificate

/-! Step 56 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL56 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := false, path2 := some { label := 0, bit := 0, position := 0, action := 5 }, path3 := none, path4 := none, path5 := none, p := true, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR56 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 0), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row56 : Row 32 S :=
  (⟨12, by decide⟩, outL56, outR56)
theorem row56_ok :
    T (C56.get row56.1)
      (C56.get (ring.rightNeighbor row56.1)) = row56.2 := by
  decide
def C57 : Vector S 32 := writeRow ring C56 row56
end BirthSpatialSourceSpliceCertificate

/-! Step 57 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL57 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR57 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.CHECK_ready, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row57 : Row 32 S :=
  (⟨14, by decide⟩, outL57, outR57)
theorem row57_ok :
    T (C57.get row57.1)
      (C57.get (ring.rightNeighbor row57.1)) = row57.2 := by
  decide
def C58 : Vector S 32 := writeRow ring C57 row57
end BirthSpatialSourceSpliceCertificate

/-! Step 58 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL58 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR58 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.CHECK_ready, path := BoundedPathInfo.some 0 1, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := true }, stall := 16 }

def row58 : Row 32 S :=
  (⟨13, by decide⟩, outL58, outR58)
theorem row58_ok :
    T (C58.get row58.1)
      (C58.get (ring.rightNeighbor row58.1)) = row58.2 := by
  decide
def C59 : Vector S 32 := writeRow ring C58 row58
end BirthSpatialSourceSpliceCertificate

/-! Step 59 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL59 : S := { core := { core := { leader := true, probe := false, phase := false, bit := true, wait := true, state := MainState.eliminate_signal, path := BoundedPathInfo.some 0 1, reset := false, carry := false, count := 0, label := 0, h_field := true, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR59 : S := { core := { core := { leader := false, probe := false, phase := false, bit := true, wait := true, state := MainState.eliminate_signal, path := BoundedPathInfo.some 1 1, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row59 : Row 32 S :=
  (⟨14, by decide⟩, outL59, outR59)
theorem row59_ok :
    T (C59.get row59.1)
      (C59.get (ring.rightNeighbor row59.1)) = row59.2 := by
  decide
def C60 : Vector S 32 := writeRow ring C59 row59
end BirthSpatialSourceSpliceCertificate

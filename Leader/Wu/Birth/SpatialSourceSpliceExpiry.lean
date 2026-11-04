import Leader.Wu.Birth.SpatialSourceSpliceSixCompare

set_option autoImplicit false

/-!
# Spatial source splice trace, steps 24-40: the zero bits expire

One-step rows of the 32-agent counterexample trace checked in `BirthSpatialSourceSpliceCertificate`; each row
states the transition output of one interaction. Steps are kept in trace order.
-/

/-! Step 24 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL24 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 12 }

def outR24 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def row24 : Row 32 S :=
  (⟨9, by decide⟩, outL24, outR24)
theorem row24_ok :
    T (C24.get row24.1)
      (C24.get (ring.rightNeighbor row24.1)) = row24.2 := by
  decide
def C25 : Vector S 32 := writeRow ring C24 row24
end BirthSpatialSourceSpliceCertificate

/-! Step 25 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL25 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 11 }

def outR25 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def row25 : Row 32 S :=
  (⟨9, by decide⟩, outL25, outR25)
theorem row25_ok :
    T (C25.get row25.1)
      (C25.get (ring.rightNeighbor row25.1)) = row25.2 := by
  decide
def C26 : Vector S 32 := writeRow ring C25 row25
end BirthSpatialSourceSpliceCertificate

/-! Step 26 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL26 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 10 }

def outR26 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def row26 : Row 32 S :=
  (⟨9, by decide⟩, outL26, outR26)
theorem row26_ok :
    T (C26.get row26.1)
      (C26.get (ring.rightNeighbor row26.1)) = row26.2 := by
  decide
def C27 : Vector S 32 := writeRow ring C26 row26
end BirthSpatialSourceSpliceCertificate

/-! Step 27 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL27 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 9 }

def outR27 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 12 }

def row27 : Row 32 S :=
  (⟨9, by decide⟩, outL27, outR27)
theorem row27_ok :
    T (C27.get row27.1)
      (C27.get (ring.rightNeighbor row27.1)) = row27.2 := by
  decide
def C28 : Vector S 32 := writeRow ring C27 row27
end BirthSpatialSourceSpliceCertificate

/-! Step 28 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL28 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 8 }

def outR28 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 11 }

def row28 : Row 32 S :=
  (⟨9, by decide⟩, outL28, outR28)
theorem row28_ok :
    T (C28.get row28.1)
      (C28.get (ring.rightNeighbor row28.1)) = row28.2 := by
  decide
def C29 : Vector S 32 := writeRow ring C28 row28
end BirthSpatialSourceSpliceCertificate

/-! Step 29 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL29 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 7 }

def outR29 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 10 }

def row29 : Row 32 S :=
  (⟨9, by decide⟩, outL29, outR29)
theorem row29_ok :
    T (C29.get row29.1)
      (C29.get (ring.rightNeighbor row29.1)) = row29.2 := by
  decide
def C30 : Vector S 32 := writeRow ring C29 row29
end BirthSpatialSourceSpliceCertificate

/-! Step 30 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL30 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 6 }

def outR30 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 9 }

def row30 : Row 32 S :=
  (⟨9, by decide⟩, outL30, outR30)
theorem row30_ok :
    T (C30.get row30.1)
      (C30.get (ring.rightNeighbor row30.1)) = row30.2 := by
  decide
def C31 : Vector S 32 := writeRow ring C30 row30
end BirthSpatialSourceSpliceCertificate

/-! Step 31 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL31 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 5 }

def outR31 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 8 }

def row31 : Row 32 S :=
  (⟨9, by decide⟩, outL31, outR31)
theorem row31_ok :
    T (C31.get row31.1)
      (C31.get (ring.rightNeighbor row31.1)) = row31.2 := by
  decide
def C32 : Vector S 32 := writeRow ring C31 row31
end BirthSpatialSourceSpliceCertificate

/-! Step 32 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL32 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 4 }

def outR32 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 7 }

def row32 : Row 32 S :=
  (⟨9, by decide⟩, outL32, outR32)
theorem row32_ok :
    T (C32.get row32.1)
      (C32.get (ring.rightNeighbor row32.1)) = row32.2 := by
  decide
def C33 : Vector S 32 := writeRow ring C32 row32
end BirthSpatialSourceSpliceCertificate

/-! Step 33 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL33 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 3 }

def outR33 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 6 }

def row33 : Row 32 S :=
  (⟨9, by decide⟩, outL33, outR33)
theorem row33_ok :
    T (C33.get row33.1)
      (C33.get (ring.rightNeighbor row33.1)) = row33.2 := by
  decide
def C34 : Vector S 32 := writeRow ring C33 row33
end BirthSpatialSourceSpliceCertificate

/-! Step 34 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL34 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 2 }

def outR34 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 5 }

def row34 : Row 32 S :=
  (⟨9, by decide⟩, outL34, outR34)
theorem row34_ok :
    T (C34.get row34.1)
      (C34.get (ring.rightNeighbor row34.1)) = row34.2 := by
  decide
def C35 : Vector S 32 := writeRow ring C34 row34
end BirthSpatialSourceSpliceCertificate

/-! Step 35 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL35 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 1 }

def outR35 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 4 }

def row35 : Row 32 S :=
  (⟨9, by decide⟩, outL35, outR35)
theorem row35_ok :
    T (C35.get row35.1)
      (C35.get (ring.rightNeighbor row35.1)) = row35.2 := by
  decide
def C36 : Vector S 32 := writeRow ring C35 row35
end BirthSpatialSourceSpliceCertificate

/-! Step 36 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL36 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 1 0, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := some (CleaningLabel.normal 1, 1), path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 0 }

def outR36 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 3 }

def row36 : Row 32 S :=
  (⟨9, by decide⟩, outL36, outR36)
theorem row36_ok :
    T (C36.get row36.1)
      (C36.get (ring.rightNeighbor row36.1)) = row36.2 := by
  decide
def C37 : Vector S 32 := writeRow ring C36 row36
end BirthSpatialSourceSpliceCertificate

/-! Step 37 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL37 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def outR37 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 2 }

def row37 : Row 32 S :=
  (⟨9, by decide⟩, outL37, outR37)
theorem row37_ok :
    T (C37.get row37.1)
      (C37.get (ring.rightNeighbor row37.1)) = row37.2 := by
  decide
def C38 : Vector S 32 := writeRow ring C37 row37
end BirthSpatialSourceSpliceCertificate

/-! Step 38 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL38 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 15 }

def outR38 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 1 }

def row38 : Row 32 S :=
  (⟨9, by decide⟩, outL38, outR38)
theorem row38_ok :
    T (C38.get row38.1)
      (C38.get (ring.rightNeighbor row38.1)) = row38.2 := by
  decide
def C39 : Vector S 32 := writeRow ring C38 row38
end BirthSpatialSourceSpliceCertificate

/-! Step 39 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL39 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 14 }

def outR39 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.depart, path := BoundedPathInfo.some 0 0, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := some (CleaningLabel.normal 0, 1), p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 0 }

def row39 : Row 32 S :=
  (⟨9, by decide⟩, outL39, outR39)
theorem row39_ok :
    T (C39.get row39.1)
      (C39.get (ring.rightNeighbor row39.1)) = row39.2 := by
  decide
def C40 : Vector S 32 := writeRow ring C39 row39
end BirthSpatialSourceSpliceCertificate

/-! Step 40 of the 60-step trace. -/
namespace BirthSpatialSourceSpliceCertificate
open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  BirthSingleUseReleaseRepair BirthFiniteTraceCertificate
  BirthSpatialSourceSpliceCounterexample

def outL40 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := false, carry := false, count := 0, label := 1, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.none, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 13 }

def outR40 : S := { core := { core := { leader := false, probe := false, phase := false, bit := false, wait := true, state := MainState.none, path := BoundedPathInfo.bot, reset := true, carry := false, count := 0, label := 0, h_field := false, path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false, reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false, write_state := WriteState.depart, write := WriteAction.none, last := false, last_set := false, last_unset := false, b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }, path0Crossed := false }, stall := 16 }

def row40 : Row 32 S :=
  (⟨9, by decide⟩, outL40, outR40)
theorem row40_ok :
    T (C40.get row40.1)
      (C40.get (ring.rightNeighbor row40.1)) = row40.2 := by
  decide
def C41 : Vector S 32 := writeRow ring C40 row40
end BirthSpatialSourceSpliceCertificate

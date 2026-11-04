import Leader.Wu.RaceEntrance.ColourCoupling
import Leader.Wu.RaceEntrance.Transit

set_option autoImplicit false
-- The row certificates are checked one after another in the kernel either way; elaborated in
-- parallel they held 4.3 GB at once (6.0 GB with elaborator `decide`), sequentially 0.7 GB.
set_option Elab.async false

open PPLLRepair LDSinkKernelC LDSinkGapCleanup LDSinkProtectedAbsorption
open LDTwoGapFrame LDSinkTwoGapNoResetKernel FiniteUniformStoppingTree

namespace LDSinkTwoGapRaceEntranceReverseRace.Certificate

/-- Fixed values of the existing state fields for the finite physical witness. -/
def atom (ld sh : Bool) (bt : Fin 3) (sb : Fin 2) : AgentState 1 where
  leader := ld
  probe := false
  phase := false
  bit := false
  wait := true
  state := MainState.none
  path := PathInfo.bot
  reset := false
  carry := false
  count := 0
  label := 0
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := sb
  bullet := bt
  shield := sh
  write_state := WriteState.none
  write := WriteAction.none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

/-- Decode only concrete state data, not a replacement transition rule. -/
def cell (u : Nat) : AgentState 1 :=
  atom (decide (u % 2 = 1)) (decide (u / 12 = 1))
    ⟨u / 4 % 3, Nat.mod_lt _ (by decide)⟩ ⟨u / 2 % 2, Nat.mod_lt _ (by decide)⟩

abbrev Config := Fin 7 → AgentState 1

def frame : TwoGapFrame 7 where
  recovery := ⟨⟨by decide⟩, 0, 2, by decide, by decide⟩
  attack := ⟨⟨by decide⟩, 2, 3, by decide, by decide⟩
  shared := by decide
  length_lt := by decide

def physicalStep (C : Config) (e : Fin 7) : Config :=
  sinkStepC (by decide) frame.attack C e

/-- Stop at the first live arrival or tagged deletion. A protected live
arrival with all three leaders present is recorded separately as success. -/
def auditStep (C : Config) (e : Fin 7) : StopNode Config :=
  let D := physicalStep C e
  if (D 0).leader = false ∨ (D 2).leader = false ∨ (D 5).leader = false then .failure
  else if (D 3).bullet = (2 : Fin 3) then
    if (D 2).shield = true then .success else .failure
  else .active D

/-- The seed is clean on both actual gaps. -/
def seed : Config := fun i =>
  if i = 0 then cell 13 else if i = 2 ∨ i = 5 then cell 3 else cell 0

def initial : Config := physicalStep (physicalStep seed 2) 5

/-- Finite extensional comparison, used only to check exact actual rows. -/
def nodeEq (x y : StopNode Config) : Prop :=
  match x, y with
  | .success, .success => True
  | .failure, .failure => True
  | .active C, .active D => ∀ i : Fin 7, C i = D i
  | _, _ => False

instance (x y : StopNode Config) : Decidable (nodeEq x y) := by
  cases x <;> cases y <;> unfold nodeEq <;> infer_instance

theorem nodeEq_eq (x y : StopNode Config) (h : nodeEq x y) : x = y := by
  cases x <;> cases y <;> simp only [nodeEq] at h
  all_goals first | rfl | exact h.elim | exact congrArg StopNode.active (funext h)

def stateData : Array (Array Nat) := #[
  #[13,0,21,2,0,21,2],
  #[13,2,21,2,0,21,2],
  #[13,8,13,2,0,21,2],
  #[13,0,21,2,2,21,2],
  #[13,0,21,2,8,13,2],
  #[15,0,21,2,0,21,2],
  #[13,2,21,2,2,21,2],
  #[13,2,21,2,8,13,2],
  #[15,2,21,2,0,21,2],
  #[13,2,13,2,0,21,2],
  #[13,8,13,2,2,21,2],
  #[13,8,13,2,8,13,2],
  #[15,8,13,2,0,21,2],
  #[15,0,21,2,2,21,2],
  #[15,0,21,2,8,13,2],
  #[21,2,21,2,0,21,2],
  #[1,0,21,2,0,21,4],
  #[15,2,21,2,2,21,2],
  #[15,2,21,2,8,13,2],
  #[1,2,21,2,0,21,4],
  #[13,2,15,2,0,21,2],
  #[13,2,13,2,2,21,2],
  #[13,2,13,2,8,13,2],
  #[15,2,13,2,0,21,2],
  #[15,8,13,2,2,21,2],
  #[15,8,13,2,8,13,2],
  #[21,2,13,2,0,21,2],
  #[1,8,13,2,0,21,4],
  #[21,2,21,2,2,21,2],
  #[1,0,21,2,2,21,4],
  #[21,2,21,2,8,13,2],
  #[1,0,21,2,8,13,4],
  #[21,8,13,2,0,21,2],
  #[13,2,21,2,0,21,8],
  #[1,0,21,2,0,21,2],
  #[1,2,21,2,2,21,4],
  #[1,2,21,2,8,13,4],
  #[1,2,21,2,0,21,2],
  #[13,4,1,2,0,21,2],
  #[13,2,15,2,2,21,2],
  #[13,2,15,2,8,13,2],
  #[15,2,15,2,0,21,2],
  #[15,2,13,2,2,21,2],
  #[15,2,13,2,8,13,2],
  #[1,2,13,2,0,21,4],
  #[21,2,13,2,2,21,2],
  #[1,8,13,2,2,21,4],
  #[21,2,13,2,8,13,2],
  #[1,8,13,2,8,13,4],
  #[21,2,15,2,0,21,2],
  #[13,2,13,2,0,21,8],
  #[1,8,13,2,0,21,2],
  #[21,8,13,2,2,21,2],
  #[13,2,21,2,2,21,8],
  #[1,0,21,2,2,21,2],
  #[21,8,13,2,8,13,2],
  #[13,2,21,2,8,13,8],
  #[1,0,21,2,8,13,2],
  #[13,8,13,2,0,21,8],
  #[3,0,21,2,0,21,2],
  #[1,2,21,2,2,21,2],
  #[1,2,21,2,8,13,2],
  #[3,2,21,2,0,21,2],
  #[13,2,1,2,0,21,2],
  #[13,4,1,2,2,21,2],
  #[13,4,1,2,8,13,2],
  #[15,4,1,2,0,21,2],
  #[15,2,15,2,2,21,2],
  #[15,2,15,2,8,13,2],
  #[1,2,15,2,0,21,4],
  #[1,2,13,2,2,21,4],
  #[1,2,13,2,8,13,4],
  #[1,2,13,2,0,21,2],
  #[21,2,15,2,2,21,2],
  #[13,2,13,2,2,21,8],
  #[1,8,13,2,2,21,2],
  #[21,2,15,2,8,13,2],
  #[13,2,13,2,8,13,8],
  #[1,8,13,2,8,13,2],
  #[21,4,1,2,0,21,2],
  #[13,2,15,2,0,21,8],
  #[3,8,13,2,0,21,2],
  #[13,8,13,2,2,21,8],
  #[3,0,21,2,2,21,2],
  #[13,8,13,2,8,13,8],
  #[3,0,21,2,8,13,2],
  #[3,2,21,2,2,21,2],
  #[3,2,21,2,8,13,2],
  #[13,2,3,2,0,21,2],
  #[13,2,1,2,2,21,2],
  #[13,2,1,2,8,13,2],
  #[15,2,1,2,0,21,2],
  #[15,4,1,2,2,21,2],
  #[15,4,1,2,8,13,2],
  #[21,2,1,2,0,21,2],
  #[1,4,1,2,0,21,4],
  #[1,2,15,2,2,21,4],
  #[1,2,15,2,8,13,4],
  #[1,2,15,2,0,21,2],
  #[1,2,13,2,2,21,2],
  #[1,2,13,2,8,13,2],
  #[3,2,13,2,0,21,2],
  #[21,4,1,2,2,21,2],
  #[13,2,15,2,2,21,8],
  #[3,8,13,2,2,21,2],
  #[21,4,1,2,8,13,2],
  #[13,2,15,2,8,13,8],
  #[3,8,13,2,8,13,2],
  #[13,4,1,2,0,21,8],
  #[13,2,3,2,2,21,2],
  #[13,2,3,2,8,13,2],
  #[15,2,3,2,0,21,2],
  #[15,2,1,2,2,21,2],
  #[15,2,1,2,8,13,2],
  #[1,2,1,2,0,21,4],
  #[21,2,1,2,2,21,2],
  #[1,4,1,2,2,21,4],
  #[21,2,1,2,8,13,2],
  #[1,4,1,2,8,13,4],
  #[21,2,3,2,0,21,2],
  #[13,2,1,2,0,21,8],
  #[1,4,1,2,0,21,2],
  #[1,2,15,2,2,21,2],
  #[1,2,15,2,8,13,2],
  #[3,2,15,2,0,21,2],
  #[3,2,13,2,2,21,2],
  #[3,2,13,2,8,13,2],
  #[13,4,1,2,2,21,8],
  #[13,4,1,2,8,13,8],
  #[15,2,3,2,2,21,2],
  #[15,2,3,2,8,13,2],
  #[1,2,3,2,0,21,4],
  #[1,2,1,2,2,21,4],
  #[1,2,1,2,8,13,4],
  #[1,2,1,2,0,21,2],
  #[21,2,3,2,2,21,2],
  #[13,2,1,2,2,21,8],
  #[1,4,1,2,2,21,2],
  #[21,2,3,2,8,13,2],
  #[13,2,1,2,8,13,8],
  #[1,4,1,2,8,13,2],
  #[13,2,3,2,0,21,8],
  #[3,4,1,2,0,21,2],
  #[3,2,15,2,2,21,2],
  #[3,2,15,2,8,13,2],
  #[1,2,3,2,2,21,4],
  #[1,2,3,2,8,13,4],
  #[1,2,3,2,0,21,2],
  #[1,2,1,2,2,21,2],
  #[1,2,1,2,8,13,2],
  #[3,2,1,2,0,21,2],
  #[13,2,3,2,2,21,8],
  #[3,4,1,2,2,21,2],
  #[13,2,3,2,8,13,8],
  #[3,4,1,2,8,13,2],
  #[1,2,3,2,2,21,2],
  #[1,2,3,2,8,13,2],
  #[3,2,3,2,0,21,2],
  #[3,2,1,2,2,21,2],
  #[3,2,1,2,8,13,2],
  #[3,2,3,2,2,21,2],
  #[3,2,3,2,8,13,2]
]

def edgeData : Array (Array Nat) := #[
  #[0,0,0,0,0,0,0],
  #[1,1,1,1,1,1,1],
  #[3,4,2,5,6,2,7],
  #[3,4,3,8,9,3,10],
  #[11,4,4,12,13,4,14],
  #[8,12,5,5,6,5,15],
  #[9,13,6,1,6,6,16],
  #[17,14,7,15,16,7,18],
  #[8,12,8,8,9,8,19],
  #[9,13,9,1,9,9,20],
  #[17,14,10,19,20,10,21],
  #[11,22,11,23,24,11,25],
  #[23,12,12,12,13,12,26],
  #[24,13,13,1,13,13,27],
  #[28,14,14,26,27,14,29],
  #[30,26,15,15,16,15,31],
  #[32,27,16,1,16,16,33],
  #[17,34,17,30,32,17,35],
  #[21,29,18,31,33,36,18],
  #[30,26,19,19,20,19,37],
  #[32,27,20,1,20,20,38],
  #[21,29,21,37,38,39,21],
  #[22,40,3,41,42,22,43],
  #[23,41,23,23,24,23,44],
  #[24,42,24,1,24,24,45],
  #[28,43,25,44,45,25,46],
  #[47,26,26,26,27,26,48],
  #[49,27,27,1,27,27,50],
  #[28,51,28,47,49,28,52],
  #[0,29,29,48,50,53,29],
  #[30,54,30,30,32,30,55],
  #[37,48,31,31,33,56,31],
  #[32,57,32,1,32,32,58],
  #[38,50,33,1,33,59,33],
  #[28,34,34,54,57,34,60],
  #[35,60,35,55,58,3,35],
  #[39,53,36,56,59,36,61],
  #[37,48,37,37,38,62,37],
  #[38,50,38,1,38,63,38],
  #[39,53,39,62,63,39,64],
  #[65,40,40,66,67,40,68],
  #[41,66,8,41,42,41,69],
  #[42,67,9,1,42,42,70],
  #[51,68,10,69,70,43,71],
  #[47,69,44,44,45,44,72],
  #[49,70,45,1,45,45,73],
  #[46,71,46,72,73,74,46],
  #[47,75,47,47,49,47,76],
  #[0,48,48,48,50,77,48],
  #[49,78,49,1,49,49,79],
  #[0,50,50,1,50,80,50],
  #[51,81,17,75,78,51,82],
  #[52,82,52,76,79,11,52],
  #[0,53,53,77,80,53,83],
  #[47,54,54,54,57,54,84],
  #[55,84,55,55,58,8,55],
  #[62,77,56,56,59,56,85],
  #[49,57,57,1,57,57,86],
  #[58,86,58,1,58,9,58],
  #[63,80,59,1,59,59,87],
  #[52,60,60,84,86,4,60],
  #[17,83,61,85,87,61,18],
  #[62,77,62,62,63,62,88],
  #[63,80,63,1,63,63,89],
  #[17,83,64,88,89,64,21],
  #[65,90,65,91,92,65,93],
  #[91,66,66,66,67,66,94],
  #[92,67,67,0,67,67,95],
  #[96,68,68,94,95,68,97],
  #[75,94,19,69,70,69,98],
  #[78,95,20,1,70,70,99],
  #[71,97,21,98,99,100,71],
  #[72,98,72,72,73,101,72],
  #[73,99,73,1,73,102,73],
  #[74,100,74,101,102,74,103],
  #[75,104,30,75,78,75,105],
  #[76,105,76,76,79,23,76],
  #[0,77,77,77,80,77,106],
  #[78,107,32,1,78,78,108],
  #[79,108,79,1,79,24,79],
  #[0,80,80,1,80,80,109],
  #[96,81,81,104,107,81,110],
  #[82,110,35,105,108,22,82],
  #[28,83,83,106,109,83,29],
  #[76,84,84,84,86,12,84],
  #[30,106,85,85,87,85,31],
  #[79,86,86,1,86,13,86],
  #[32,109,87,1,87,87,33],
  #[30,106,88,88,89,88,37],
  #[32,109,89,1,89,89,38],
  #[90,40,3,111,112,90,113],
  #[91,111,91,91,92,91,114],
  #[92,112,92,0,92,92,115],
  #[96,113,93,114,115,93,116],
  #[117,94,94,94,95,94,118],
  #[119,95,95,0,95,95,120],
  #[96,121,96,117,119,96,122],
  #[116,97,97,118,120,123,97],
  #[98,118,37,98,99,124,98],
  #[99,120,38,1,99,125,99],
  #[100,123,39,124,125,100,126],
  #[101,124,101,101,102,101,127],
  #[102,125,102,1,102,102,128],
  #[28,126,103,127,128,103,46],
  #[117,104,104,104,107,104,129],
  #[105,129,55,105,108,41,105],
  #[47,106,106,106,109,106,48],
  #[119,107,107,0,107,107,130],
  #[108,130,58,1,108,42,108],
  #[49,109,109,1,109,109,50],
  #[122,110,110,129,130,40,110],
  #[111,66,8,111,112,111,131],
  #[112,67,9,0,112,112,132],
  #[121,68,10,131,132,113,133],
  #[117,131,114,114,115,114,134],
  #[119,132,115,0,115,115,135],
  #[116,133,116,134,135,136,116],
  #[117,137,117,117,119,117,138],
  #[134,118,118,118,120,139,118],
  #[119,140,119,0,119,119,141],
  #[135,120,120,0,120,142,120],
  #[121,81,17,137,140,121,143],
  #[122,143,122,138,141,65,122],
  #[136,123,123,139,142,123,144],
  #[124,139,62,124,125,124,145],
  #[125,142,63,1,125,125,146],
  #[51,144,64,145,146,126,71],
  #[47,145,127,127,128,127,72],
  #[49,146,128,1,128,128,73],
  #[138,129,129,129,130,66,129],
  #[141,130,130,0,130,67,130],
  #[137,94,19,131,132,131,147],
  #[140,95,20,0,132,132,148],
  #[133,97,21,147,148,149,133],
  #[134,147,134,134,135,150,134],
  #[135,148,135,0,135,151,135],
  #[136,149,136,150,151,136,152],
  #[137,104,30,137,140,137,153],
  #[138,153,138,138,141,91,138],
  #[150,139,139,139,142,139,154],
  #[140,107,32,0,140,140,155],
  #[141,155,141,0,141,92,141],
  #[151,142,142,0,142,142,156],
  #[143,110,35,153,155,90,143],
  #[96,144,144,154,156,144,97],
  #[75,154,88,145,146,145,98],
  #[78,156,89,1,146,146,99],
  #[147,118,37,147,148,157,147],
  #[148,120,38,0,148,158,148],
  #[149,123,39,157,158,149,159],
  #[150,157,150,150,151,150,160],
  #[151,158,151,0,151,151,161],
  #[96,159,152,160,161,152,116],
  #[153,129,55,153,155,111,153],
  #[117,154,154,154,156,154,118],
  #[155,130,58,0,155,112,155],
  #[119,156,156,0,156,156,120],
  #[157,139,62,157,158,157,162],
  #[158,142,63,0,158,158,163],
  #[121,144,64,162,163,159,133],
  #[117,162,160,160,161,160,134],
  #[119,163,161,0,161,161,135],
  #[137,154,88,162,163,162,147],
  #[140,156,89,0,163,163,148]
]

def valueData : Array Nat := #[0,459986536544739960976801,350222927927847240009735,350222927927847240009735,317662237419939854134466,350222927927847240009735,420146866792108367271237,324986248039231722834374,350222927927847240009735,420146866792108367271237,324986248039231722834374,298961844466911608876997,317662237419939854134466,399399079054138315096670,266188407359488479526971,324986248039231722834374,403585305606588688725677,379181241872406733963195,261770128042743414773161,324986248039231722834374,403585305606588688725677,261770128042743414773161,234806307196199656610745,298961844466911608876997,379150441316488124752002,296041417981509638988728,266188407359488479526971,361499967277762505069783,305995735141128764341559,140018235427354285300255,379181241872406733963195,261770128042743414773161,434619290806914871142941,360480786694513157144833,349498410756037009242816,368761034488145019592044,291057412763925414787171,261770128042743414773161,360480786694513157144833,291057412763925414787171,71627103353454247076736,234806307196199656610745,302641926715928974551292,227166236605016578198205,296041417981509638988728,377601273887268978202697,286314497658584552231479,305995735141128764341559,140018235427354285300255,382085386380508271068127,244315192492594946332245,247536164136467029600353,302840784791012700742597,178311501201304305358456,349498410756037009242816,368761034488145019592044,291057412763925414787171,417160199784396744786041,429913753495534112960821,378430347062391645436483,339909482479033090154540,324986248039231722834374,291057412763925414787171,378430347062391645436483,324986248039231722834374,120305257933600152542210,71627103353454247076736,34993590743835752406490,71995909612485224843904,227166236605016578198205,298077551008986898597255,205227866405012431468127,286314497658584552231479,372991533378131475655368,292125722405166091403834,247536164136467029600353,302840784791012700742597,178311501201304305358456,308484157744445354556346,380850507641923866404667,273496111093636212265537,74356118768977928430212,242376909497098109694155,266188407359488479526971,339909482479033090154540,324986248039231722834374,412480495747652642362373,403585305606588688725677,324986248039231722834374,403585305606588688725677,183696868165347309214944,120305257933600152542210,72529979170448090598781,117384831448198182653941,71995909612485224843904,35123984086531019637833,127339148607817308006772,66024246954892552276519,205227866405012431468127,285751247039750140196304,217064545714695937624340,292125722405166091403834,375654254772603189293886,296041417981509638988728,74356118768977928430212,242376909497098109694155,266188407359488479526971,36041630263511454446934,306308487044363061318513,361499967277762505069783,72881922669587515875542,183696868165347309214944,149313105220213666868337,176056797574164230802404,117384831448198182653941,70980811741228944049476,107657911125273095896692,127339148607817308006772,66024246954892552276519,75464924234468236914906,32597684193832185218676,196426725105614682204552,124184198257701244407810,69098513247905484811913,217064545714695937624340,292000257960729022768935,227166236605016578198205,296041417981509638988728,377601273887268978202697,72881922669587515875542,35499273328981729460904,176056797574164230802404,144748729513271590914300,154118427374160084072326,107657911125273095896692,66371071232091441502147,113469135871854635069047,196426725105614682204552,124184198257701244407810,69098513247905484811913,155155336248730046873391,74230045495883832251446,33855383534651330041860,191267470466245762298354,71995909612485224843904,227166236605016578198205,298077551008986898597255,154118427374160084072326,132422425544034832513349,165955106683843590228539,113469135871854635069047,69033792626563155140665,117384831448198182653941,191267470466245762298354,71995909612485224843904,152979665548647753635558,35123984086531019637833,165955106683843590228539,138671436465013715085980,176056797574164230802404,117384831448198182653941,70980811741228944049476,176056797574164230802404,144748729513271590914300]

def remainingData : Array Nat := #[0,0,2,2,2,2,1,2,2,1,2,2,2,1,2,2,1,2,2,2,1,2,2,2,1,2,2,1,2,2,2,2,1,1,2,2,2,2,1,2,2,2,1,2,2,1,2,2,2,1,1,2,2,2,2,2,2,1,1,1,2,2,2,1,2,2,2,1,2,2,1,2,2,1,2,2,2,2,1,1,1,2,2,2,2,2,1,1,2,1,2,2,1,2,2,1,2,2,2,1,2,2,1,2,2,2,2,1,1,1,2,2,1,2,2,1,2,2,2,1,1,2,2,2,2,1,2,2,1,2,1,2,1,2,2,1,2,2,2,2,1,1,1,2,2,2,1,2,1,2,2,1,2,2,2,1,1,2,1,2,2,1,2,1]

abbrev Index := Fin 164

def state (i : Index) : StopNode Config :=
  if i.val = 0 then .failure else if i.val = 1 then .success
  else .active (fun j => cell ((stateData[i.val - 2]!)[j.val]!))

def next (i : Index) (e : Fin 7) : Index :=
  Fin.ofNat 164 ((edgeData[i.val]!)[e.val]!)

def value (i : Index) : Nat := valueData[i.val]!
def remaining (i : Index) : Nat := remainingData[i.val]!
def scale : Nat := 7 ^ 28

/-- Every clause below is evaluated on concrete finite data. In particular,
its first clause compares the exact full K2 successor, not a surrogate row. -/
private def RowFacts (i : Index) : Prop :=
  (∀ e : Fin 7, nodeEq (state (next i e)) (stepNode auditStep (state i) e)) ∧
  (7 * value i ≤ (List.ofFn (fun e : Fin 7 => value (next i e))).sum) ∧
  (value i ≤ scale * (successWeight (state i) + activeWeight (state i))) ∧
  (remaining i ≤ 2) ∧
  (activeWeight (state i) = if remaining i = 0 then 0 else 1) ∧
  (List.ofFn (fun e : Fin 7 => if remaining (next i e) = 1 then 1 else 0)).sum ≤
      (if remaining i = 1 then 6 else if remaining i = 2 then 1 else 0) ∧
  (List.ofFn (fun e : Fin 7 => if remaining (next i e) = 2 then 1 else 0)).sum ≤
      (if remaining i = 2 then 6 else 0)

private theorem checked_000 : RowFacts 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_001 : RowFacts 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_002 : RowFacts 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_003 : RowFacts 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_004 : RowFacts 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_005 : RowFacts 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_006 : RowFacts 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_007 : RowFacts 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_008 : RowFacts 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_009 : RowFacts 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_010 : RowFacts 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_011 : RowFacts 11 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_012 : RowFacts 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_013 : RowFacts 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_014 : RowFacts 14 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_015 : RowFacts 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_016 : RowFacts 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_017 : RowFacts 17 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_018 : RowFacts 18 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_019 : RowFacts 19 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_020 : RowFacts 20 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_021 : RowFacts 21 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_022 : RowFacts 22 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_023 : RowFacts 23 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_024 : RowFacts 24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_025 : RowFacts 25 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_026 : RowFacts 26 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_027 : RowFacts 27 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_028 : RowFacts 28 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_029 : RowFacts 29 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_030 : RowFacts 30 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_031 : RowFacts 31 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_032 : RowFacts 32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_033 : RowFacts 33 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_034 : RowFacts 34 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_035 : RowFacts 35 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_036 : RowFacts 36 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_037 : RowFacts 37 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_038 : RowFacts 38 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_039 : RowFacts 39 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_040 : RowFacts 40 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_041 : RowFacts 41 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_042 : RowFacts 42 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_043 : RowFacts 43 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_044 : RowFacts 44 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_045 : RowFacts 45 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_046 : RowFacts 46 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_047 : RowFacts 47 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_048 : RowFacts 48 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_049 : RowFacts 49 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_050 : RowFacts 50 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_051 : RowFacts 51 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_052 : RowFacts 52 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_053 : RowFacts 53 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_054 : RowFacts 54 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_055 : RowFacts 55 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_056 : RowFacts 56 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_057 : RowFacts 57 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_058 : RowFacts 58 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_059 : RowFacts 59 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_060 : RowFacts 60 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_061 : RowFacts 61 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_062 : RowFacts 62 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_063 : RowFacts 63 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_064 : RowFacts 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_065 : RowFacts 65 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_066 : RowFacts 66 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_067 : RowFacts 67 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_068 : RowFacts 68 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_069 : RowFacts 69 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_070 : RowFacts 70 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_071 : RowFacts 71 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_072 : RowFacts 72 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_073 : RowFacts 73 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_074 : RowFacts 74 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_075 : RowFacts 75 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_076 : RowFacts 76 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_077 : RowFacts 77 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_078 : RowFacts 78 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_079 : RowFacts 79 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_080 : RowFacts 80 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_081 : RowFacts 81 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_082 : RowFacts 82 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_083 : RowFacts 83 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_084 : RowFacts 84 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_085 : RowFacts 85 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_086 : RowFacts 86 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_087 : RowFacts 87 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_088 : RowFacts 88 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_089 : RowFacts 89 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_090 : RowFacts 90 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_091 : RowFacts 91 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_092 : RowFacts 92 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_093 : RowFacts 93 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_094 : RowFacts 94 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_095 : RowFacts 95 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_096 : RowFacts 96 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_097 : RowFacts 97 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_098 : RowFacts 98 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_099 : RowFacts 99 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_100 : RowFacts 100 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_101 : RowFacts 101 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_102 : RowFacts 102 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_103 : RowFacts 103 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_104 : RowFacts 104 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_105 : RowFacts 105 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_106 : RowFacts 106 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_107 : RowFacts 107 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_108 : RowFacts 108 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_109 : RowFacts 109 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_110 : RowFacts 110 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_111 : RowFacts 111 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_112 : RowFacts 112 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_113 : RowFacts 113 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_114 : RowFacts 114 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_115 : RowFacts 115 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_116 : RowFacts 116 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_117 : RowFacts 117 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_118 : RowFacts 118 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_119 : RowFacts 119 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_120 : RowFacts 120 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_121 : RowFacts 121 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_122 : RowFacts 122 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_123 : RowFacts 123 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_124 : RowFacts 124 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_125 : RowFacts 125 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_126 : RowFacts 126 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_127 : RowFacts 127 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_128 : RowFacts 128 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_129 : RowFacts 129 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_130 : RowFacts 130 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_131 : RowFacts 131 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_132 : RowFacts 132 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_133 : RowFacts 133 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_134 : RowFacts 134 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_135 : RowFacts 135 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_136 : RowFacts 136 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_137 : RowFacts 137 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_138 : RowFacts 138 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_139 : RowFacts 139 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_140 : RowFacts 140 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_141 : RowFacts 141 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_142 : RowFacts 142 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_143 : RowFacts 143 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_144 : RowFacts 144 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_145 : RowFacts 145 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_146 : RowFacts 146 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_147 : RowFacts 147 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_148 : RowFacts 148 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_149 : RowFacts 149 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_150 : RowFacts 150 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_151 : RowFacts 151 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_152 : RowFacts 152 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_153 : RowFacts 153 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_154 : RowFacts 154 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_155 : RowFacts 155 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_156 : RowFacts 156 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_157 : RowFacts 157 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_158 : RowFacts 158 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_159 : RowFacts 159 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_160 : RowFacts 160 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_161 : RowFacts 161 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_162 : RowFacts 162 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
private theorem checked_163 : RowFacts 163 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

-- The 164-deep `Fin.cases` nest (and its two direct readers below) need a deeper recursion
-- limit to elaborate.
set_option maxRecDepth 4096 in
private theorem all_rows : (i : Index) → RowFacts i :=
  (Fin.cases checked_000 (Fin.cases checked_001 (Fin.cases checked_002 (Fin.cases checked_003 (Fin.cases checked_004 (Fin.cases checked_005 (Fin.cases checked_006 (Fin.cases checked_007 (Fin.cases checked_008 (Fin.cases checked_009 (Fin.cases checked_010 (Fin.cases checked_011 (Fin.cases checked_012 (Fin.cases checked_013 (Fin.cases checked_014 (Fin.cases checked_015 (Fin.cases checked_016 (Fin.cases checked_017 (Fin.cases checked_018 (Fin.cases checked_019 (Fin.cases checked_020 (Fin.cases checked_021 (Fin.cases checked_022 (Fin.cases checked_023 (Fin.cases checked_024 (Fin.cases checked_025 (Fin.cases checked_026 (Fin.cases checked_027 (Fin.cases checked_028 (Fin.cases checked_029 (Fin.cases checked_030 (Fin.cases checked_031 (Fin.cases checked_032 (Fin.cases checked_033 (Fin.cases checked_034 (Fin.cases checked_035 (Fin.cases checked_036 (Fin.cases checked_037 (Fin.cases checked_038 (Fin.cases checked_039 (Fin.cases checked_040 (Fin.cases checked_041 (Fin.cases checked_042 (Fin.cases checked_043 (Fin.cases checked_044 (Fin.cases checked_045 (Fin.cases checked_046 (Fin.cases checked_047 (Fin.cases checked_048 (Fin.cases checked_049 (Fin.cases checked_050 (Fin.cases checked_051 (Fin.cases checked_052 (Fin.cases checked_053 (Fin.cases checked_054 (Fin.cases checked_055 (Fin.cases checked_056 (Fin.cases checked_057 (Fin.cases checked_058 (Fin.cases checked_059 (Fin.cases checked_060 (Fin.cases checked_061 (Fin.cases checked_062 (Fin.cases checked_063 (Fin.cases checked_064 (Fin.cases checked_065 (Fin.cases checked_066 (Fin.cases checked_067 (Fin.cases checked_068 (Fin.cases checked_069 (Fin.cases checked_070 (Fin.cases checked_071 (Fin.cases checked_072 (Fin.cases checked_073 (Fin.cases checked_074 (Fin.cases checked_075 (Fin.cases checked_076 (Fin.cases checked_077 (Fin.cases checked_078 (Fin.cases checked_079 (Fin.cases checked_080 (Fin.cases checked_081 (Fin.cases checked_082 (Fin.cases checked_083 (Fin.cases checked_084 (Fin.cases checked_085 (Fin.cases checked_086 (Fin.cases checked_087 (Fin.cases checked_088 (Fin.cases checked_089 (Fin.cases checked_090 (Fin.cases checked_091 (Fin.cases checked_092 (Fin.cases checked_093 (Fin.cases checked_094 (Fin.cases checked_095 (Fin.cases checked_096 (Fin.cases checked_097 (Fin.cases checked_098 (Fin.cases checked_099 (Fin.cases checked_100 (Fin.cases checked_101 (Fin.cases checked_102 (Fin.cases checked_103 (Fin.cases checked_104 (Fin.cases checked_105 (Fin.cases checked_106 (Fin.cases checked_107 (Fin.cases checked_108 (Fin.cases checked_109 (Fin.cases checked_110 (Fin.cases checked_111 (Fin.cases checked_112 (Fin.cases checked_113 (Fin.cases checked_114 (Fin.cases checked_115 (Fin.cases checked_116 (Fin.cases checked_117 (Fin.cases checked_118 (Fin.cases checked_119 (Fin.cases checked_120 (Fin.cases checked_121 (Fin.cases checked_122 (Fin.cases checked_123 (Fin.cases checked_124 (Fin.cases checked_125 (Fin.cases checked_126 (Fin.cases checked_127 (Fin.cases checked_128 (Fin.cases checked_129 (Fin.cases checked_130 (Fin.cases checked_131 (Fin.cases checked_132 (Fin.cases checked_133 (Fin.cases checked_134 (Fin.cases checked_135 (Fin.cases checked_136 (Fin.cases checked_137 (Fin.cases checked_138 (Fin.cases checked_139 (Fin.cases checked_140 (Fin.cases checked_141 (Fin.cases checked_142 (Fin.cases checked_143 (Fin.cases checked_144 (Fin.cases checked_145 (Fin.cases checked_146 (Fin.cases checked_147 (Fin.cases checked_148 (Fin.cases checked_149 (Fin.cases checked_150 (Fin.cases checked_151 (Fin.cases checked_152 (Fin.cases checked_153 (Fin.cases checked_154 (Fin.cases checked_155 (Fin.cases checked_156 (Fin.cases checked_157 (Fin.cases checked_158 (Fin.cases checked_159 (Fin.cases checked_160 (Fin.cases checked_161 (Fin.cases checked_162 (Fin.cases checked_163 (fun j => j.elim0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 4096 in
/-- Exact original scheduler transition on every state and all seven edges. -/
theorem checked_rows (i : Index) (e : Fin 7) :
    nodeEq (state (next i e)) (stepNode auditStep (state i) e) := (all_rows i).1 e

set_option maxRecDepth 4096 in
theorem rows (i : Index) (e : Fin 7) :
    state (next i e) = stepNode auditStep (state i) e :=
  nodeEq_eq _ _ (checked_rows i e)

theorem initial_state : state 2 = .active initial := nodeEq_eq _ _ (by decide +kernel)

theorem value_row (i : Index) :
    7 * value i ≤ (List.ofFn (fun e : Fin 7 => value (next i e))).sum :=
  (all_rows i).2.1

theorem value_bound (i : Index) :
    value i ≤ scale * (successWeight (state i) + activeWeight (state i)) :=
  (all_rows i).2.2.1

theorem remaining_bound (i : Index) : remaining i ≤ 2 := (all_rows i).2.2.2.1

theorem active_remaining (i : Index) :
    activeWeight (state i) = if remaining i = 0 then 0 else 1 :=
  (all_rows i).2.2.2.2.1

theorem service_histogram (i : Index) :
    (List.ofFn (fun e : Fin 7 => if remaining (next i e) = 1 then 1 else 0)).sum ≤
      (if remaining i = 1 then 6 else if remaining i = 2 then 1 else 0) ∧
    (List.ofFn (fun e : Fin 7 => if remaining (next i e) = 2 then 1 else 0)).sum ≤
      (if remaining i = 2 then 6 else 0) := (all_rows i).2.2.2.2.2

theorem numeric_margin : 2 * scale < 3 * (value 2 - (6 ^ 28 + 28 * 6 ^ 27)) := by decide +kernel

end LDSinkTwoGapRaceEntranceReverseRace.Certificate

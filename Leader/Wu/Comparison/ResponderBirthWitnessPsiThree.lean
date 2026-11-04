import Leader.Wu.Comparison.ResponderBirthFromCongest

set_option autoImplicit false
set_option Elab.async false

namespace ZZC5Witness

open PPLL

/-- Non-vacuity witness base: a departing, leaderless, label-zero, token-less
    agent for psi = 3. -/
def lW : AgentState 3 :=
  { leader := false, probe := false, phase := false, bit := false, wait := false,
    state := MainState.depart, path := PathInfo.some 0 0, reset := false,
    carry := false, count := 0, label := ⟨0, by decide⟩, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩, shield := false,
    write_state := WriteState.none, write := WriteAction.overwrite,
    last := false, last_set := false, last_unset := false, b_carry := false,
    gen_ws := false, ws_echo := false, signal_ws := false }

/-- The responder carries the same token payload. -/
def rW : AgentState 3 :=
  { lW with state := MainState.none, path := PathInfo.some 0 0 }

/-- The independent CHECK left endpoint, already in .equal with label 1. -/
def mW : AgentState 3 :=
  { lW with state := MainState.equal, label := ⟨1, by decide⟩ }

theorem w_hlLabel : lW.label = ⟨0, by decide⟩ := by decide +kernel

theorem w_hlLeader : lW.leader = false := by decide +kernel

theorem w_hlState : lW.state = MainState.depart := by decide +kernel

theorem w_hlPath : lW.path = PathInfo.some 0 0 := by decide +kernel

theorem w_hrPath : rW.path = PathInfo.some 0 0 := by decide +kernel

theorem w_h5path :
    (ZZRepairAll8.compareSigGuarded (by decide : 0 < 3) lW rW).1.path =
      PathInfo.some 0 0 := by decide +kernel

theorem w_h5label :
    (ZZRepairAll8.compareSigGuarded (by decide : 0 < 3) lW rW).1.label.val = 0 := by
  decide +kernel

theorem w_h5bit :
    (if (ZZRepairAll8.compareSigGuarded (by decide : 0 < 3) lW rW).1.bit then 1 else 0) =
      0 := by decide +kernel

theorem w_hm : mW.label.val < 2 ∧ mW.state = MainState.equal := by decide +kernel

theorem w_h5term_false :
    (ZZRepairAll8.compareSigGuarded (by decide : 0 < 3) lW rW).1.label ≠
      ⟨2, by decide⟩ := by decide +kernel

#print axioms w_h5path
#print axioms w_h5label
#print axioms w_h5bit
#print axioms w_hm
#print axioms w_h5term_false

end ZZC5Witness

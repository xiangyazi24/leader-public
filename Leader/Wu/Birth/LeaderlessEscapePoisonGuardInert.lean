import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZ9GuardInert

open PPLL PPLLRepair

private theorem hψ2 : 0 < 2 := by decide

/-- The poison token: path2 = (label 0, bit 0, position 1, action 5). -/
def poison : Path2Info := ⟨0, 0, 1, 5⟩

/-- The poison agent: the exact cell used by the counterexample. -/
def poisonR : AgentState 2 :=
  { leader := false
    probe := false
    phase := true
    bit := false
    wait := false
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := (0 : Fin 2)
    h_field := false
    path2 := some poison
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := ⟨0, by decide⟩
    bullet := ⟨0, by decide⟩
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }

/-- Candidate A's guard is inert on the poison token: its condition requires
position = 0 and action = 1, while the poison token has position = 1 and
action = 5, so the function returns its input unchanged. -/
theorem guard_inert_on_poison :
    compareBitUpdateRActionOne hψ2 poisonR = poisonR := by
  decide +kernel

#print axioms ZZ9GuardInert.guard_inert_on_poison

end ZZ9GuardInert

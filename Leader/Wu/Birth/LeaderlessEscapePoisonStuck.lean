import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZPoison5All8

open PPLL PPLLRepair

private def ring2 : DirectedRing 2 := ⟨by decide⟩

def poison : Path2Info := ⟨0, 0, 1, 5⟩

def poisonCell (lab : Fin 2) : AgentState 2 :=
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
    label := lab
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

def poisonProtocol : PopulationProtocol where
  Q := AgentState 2
  Y := LeaderOutput
  transition :=
    ZZRepairAll8.ppllIntegratedRepairAll5 (ψ := 2) (by decide) 2
  output := AgentState.outputFn

def poisonCfg : poisonProtocol.Configuration 2 :=
  fun i => poisonCell i

def hasLeaderBool (C : poisonProtocol.Configuration 2) : Bool :=
  (C (0 : Fin 2)).leader || (C (1 : Fin 2)).leader

def escapesAux : Nat → poisonProtocol.Configuration 2 → Bool
  | 0, C => hasLeaderBool C
  | fuel + 1, C =>
      hasLeaderBool C ||
      escapesAux fuel
        (poisonProtocol.step ring2 C (0 : Fin 2)) ||
      escapesAux fuel
        (poisonProtocol.step ring2 C (1 : Fin 2))

theorem poison_no_escape8 :
    escapesAux 8 poisonCfg = false := by
  decide +kernel

#print axioms ZZPoison5All8.poison_no_escape8

end ZZPoison5All8

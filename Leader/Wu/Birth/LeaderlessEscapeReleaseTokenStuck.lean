import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZRelease5

open PPLL PPLLRepair

private def ring2 : DirectedRing 2 := ⟨by decide⟩

private def prot : PopulationProtocol where
  Q := AgentState 2
  Y := LeaderOutput
  transition :=
    ZZRepairAll8.ppllIntegratedRepairAll5 (ψ := 2) (by decide) 2
  output := AgentState.outputFn

private abbrev RawCfg := prot.Configuration 2

def release5Token : Path2Info :=
  { label := 0
    bit := 0
    position := 1
    action := 5 }

def release5 (lab : Fin 2) : AgentState 2 :=
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
    path2 := some release5Token
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
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

def release5Cfg : RawCfg :=
  fun i => release5 i

def hasLeader (C : RawCfg) : Bool :=
  (C (0 : Fin 2)).leader || (C (1 : Fin 2)).leader

def escapesAux : Nat → RawCfg → Bool
  | 0, C => hasLeader C
  | k + 1, C =>
      hasLeader C ||
      escapesAux k (prot.step ring2 C (0 : Fin 2)) ||
      escapesAux k (prot.step ring2 C (1 : Fin 2))

theorem release5_no_escape8 :
    escapesAux 8 release5Cfg = false := by
  decide +kernel

#print axioms ZZRelease5.release5_no_escape8

end ZZRelease5

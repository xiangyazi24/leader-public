import Leader.Wu.Protocol.Repairs
import Leader.Wu.Birth.ClosedLeaderlessRingTwo

set_option autoImplicit false
set_option Elab.async false

namespace ZZCongestExit

open PPLL PPLLRepair

private theorem h2 : 0 < 2 := by decide
private def u : AgentState 2 := BoundedAgentState.erase Q16405.s

theorem u_label_zero : u.label = (0 : Fin 2) := by decide +kernel

theorem cmpUpdate_sets_congest :
    (cmpUpdate h2 u u).1.state = MainState.congest := by decide +kernel

theorem compareSigNoSourceRearm_no_congest :
    (compareSigNoSourceRearm h2 u u).1.state = MainState.none := by decide +kernel

#print axioms ZZCongestExit.cmpUpdate_sets_congest
#print axioms ZZCongestExit.compareSigNoSourceRearm_no_congest

end ZZCongestExit

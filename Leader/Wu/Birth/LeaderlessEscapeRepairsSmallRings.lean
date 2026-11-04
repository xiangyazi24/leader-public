import Leader.Wu.Birth.LeaderlessEscapeRepairs
import Leader.Wu.Birth.ClosedLeaderlessSmallRings

set_option autoImplicit false
set_option Elab.async false

namespace ZZRepairAllGen

open PPLL PPLLRepair

private theorem hψ2 : 0 < 2 := by decide
private theorem hψ3 : 0 < 3 := by decide

private def ring3 : DirectedRing 3 := ⟨by decide⟩
private def ring4 : DirectedRing 4 := ⟨by decide⟩

def prot2 : PopulationProtocol where
  Q := AgentState 2
  Y := LeaderOutput
  transition := ZZRepairAll.ppllIntegratedRepairAll hψ2 2
  output := AgentState.outputFn

def prot3 : PopulationProtocol where
  Q := AgentState 3
  Y := LeaderOutput
  transition := ZZRepairAll.ppllIntegratedRepairAll hψ3 3
  output := AgentState.outputFn

def C32 : prot2.Configuration 3 := fun _ => BoundedAgentState.erase ZZClosedLeaderlessGen.s2
def C42 : prot2.Configuration 4 := fun _ => BoundedAgentState.erase ZZClosedLeaderlessGen.s2
def C33 : prot3.Configuration 3 := fun _ => BoundedAgentState.erase ZZClosedLeaderlessGen.s3

theorem n3_psi2_escapes :
    ∃ e1 e2 e3 e4 e5 e6 e7 e8 : Fin 3, ∃ i : Fin 3,
      ((prot2.step ring3
        (prot2.step ring3
          (prot2.step ring3
            (prot2.step ring3
              (prot2.step ring3
                (prot2.step ring3
                  (prot2.step ring3
                    (prot2.step ring3 C32 e1) e2) e3) e4) e5) e6) e7) e8) i).leader = true := by
  decide +kernel

theorem n4_psi2_escapes :
    ∃ e1 e2 e3 e4 e5 e6 : Fin 4, ∃ i : Fin 4,
      ((prot2.step ring4
        (prot2.step ring4
          (prot2.step ring4
            (prot2.step ring4
              (prot2.step ring4
                (prot2.step ring4 C42 e1) e2) e3) e4) e5) e6) i).leader = true := by
  decide +kernel

theorem n3_psi3_escapes :
    ∃ e1 e2 e3 e4 e5 e6 : Fin 3, ∃ i : Fin 3,
      ((prot3.step ring3
        (prot3.step ring3
          (prot3.step ring3
            (prot3.step ring3
              (prot3.step ring3
                (prot3.step ring3 C33 e1) e2) e3) e4) e5) e6) i).leader = true := by
  decide +kernel

#print axioms ZZRepairAllGen.n3_psi2_escapes
#print axioms ZZRepairAllGen.n4_psi2_escapes
#print axioms ZZRepairAllGen.n3_psi3_escapes

end ZZRepairAllGen

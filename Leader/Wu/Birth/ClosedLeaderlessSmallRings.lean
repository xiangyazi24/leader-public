import Leader.Wu.Protocol.BoundedProtocol
import Leader.Wu.WriteSeq.WriterProducerRepair

set_option autoImplicit false
set_option Elab.async false

namespace ZZClosedLeaderlessGen

open PPLL PPLLRepair

private theorem hψ2 : 0 < 2 := by decide
private theorem hψ3 : 0 < 3 := by decide

def s2 : BoundedAgentState 2 2 :=
  let b := (WriterProducerRegression.clean hψ2 (fun _ => false) (0 : Fin 2)).base.core.core
  { b with leader := false, shield := false, gen_ws := false, phase := true }

def s3 : BoundedAgentState 3 3 :=
  let b := (WriterProducerRegression.clean hψ3 (fun _ => false) (0 : Fin 3)).base.core.core
  { b with leader := false, shield := false, gen_ws := false, phase := true }

private def ring3 : DirectedRing 3 := ⟨by decide⟩
private def ring4 : DirectedRing 4 := ⟨by decide⟩

def C32 : (PPLLRepair.integratedBoundedProtocol hψ2 2).Configuration 3 := fun _ => s2
def C42 : (PPLLRepair.integratedBoundedProtocol hψ2 2).Configuration 4 := fun _ => s2
def C33 : (PPLLRepair.integratedBoundedProtocol hψ3 3).Configuration 3 := fun _ => s3

theorem n3_psi2_closed :
    ∀ e i : Fin 3,
      (((PPLLRepair.integratedBoundedProtocol hψ2 2).step ring3 C32 e) i).leader = false := by
  decide +kernel

theorem n4_psi2_closed :
    ∀ e i : Fin 4,
      (((PPLLRepair.integratedBoundedProtocol hψ2 2).step ring4 C42 e) i).leader = false := by
  decide +kernel

theorem n3_psi3_closed :
    ∀ e i : Fin 3,
      (((PPLLRepair.integratedBoundedProtocol hψ3 3).step ring3 C33 e) i).leader = false := by
  decide +kernel

#print axioms ZZClosedLeaderlessGen.n3_psi2_closed
#print axioms ZZClosedLeaderlessGen.n4_psi2_closed
#print axioms ZZClosedLeaderlessGen.n3_psi3_closed

end ZZClosedLeaderlessGen

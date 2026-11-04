import Leader.Wu.Protocol.BoundedProtocol
import Leader.Wu.WriteSeq.WriterProducerRepair


set_option autoImplicit false
set_option Elab.async false


namespace Q16405


open PPLL PPLLRepair


private theorem hψ2 : 0 < 2 := by
  decide


def s : BoundedAgentState 2 2 :=
  let b :=
    (WriterProducerRegression.clean hψ2
      (fun _ => false) (0 : Fin 2)).base.core.core
  { b with
    leader := false
    shield := false
    gen_ws := false
    phase := true }


def rawS : AgentState 2 :=
  BoundedAgentState.erase s


theorem raw_pair_exact :
    PPLLRepair.ppllIntegratedRepair hψ2 2 rawS rawS =
      ({ rawS with h_field := true },
       { rawS with
           label := (1 : Fin 2)
           phase := false
           write_state := .depart }) := by
  decide +kernel


theorem raw_pair_leaderless :
    let q := PPLLRepair.ppllIntegratedRepair hψ2 2 rawS rawS
    q.1.leader = false ∧ q.2.leader = false := by
  decide +kernel


private def ring2 : DirectedRing 2 :=
  ⟨by decide⟩


def C :
    (PPLLRepair.integratedBoundedProtocol hψ2 2).Configuration 2 :=
  fun _ => s


theorem C_leaderless :
    ∀ i : Fin 2, (C i).leader = false := by
  decide +kernel


theorem every_edge_next_leaderless :
    ∀ e i : Fin 2,
      (((PPLLRepair.integratedBoundedProtocol hψ2 2).step
        ring2 C e) i).leader = false := by
  decide +kernel


#print axioms Q16405.raw_pair_exact
#print axioms Q16405.raw_pair_leaderless
#print axioms Q16405.every_edge_next_leaderless


end Q16405

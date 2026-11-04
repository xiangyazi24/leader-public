import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs
import Leader.Wu.Birth.ClosedLeaderlessSmallRings

set_option autoImplicit false
set_option Elab.async false

namespace ZZRepairAll8Gen

open PPLL PPLLRepair

private theorem hψ3 : 0 < 3 := by decide

private def ring3 : DirectedRing 3 := ⟨by decide⟩
private def ring4 : DirectedRing 4 := ⟨by decide⟩

/-- The ψ=3, κ=3 specialization of exactly the same six-repair transition
used by ZZRepairAll8.protocolAll8.  The existing protocolAll8 itself is
specialized to ψ=2, κ=2, so a separate package is required only for typing
the s3 witness. -/
def protocolAll8Psi3 : PopulationProtocol where
  Q := AgentState 3
  Y := LeaderOutput
  transition := ZZRepairAll8.ppllIntegratedRepairAll5 hψ3 3
  output := AgentState.outputFn

/-- Constant n=3 configuration from the ψ=2 isomorphic witness,
on the literal existing protocolAll8. -/
def C32 : ZZRepairAll8.protocolAll8.Configuration 3 :=
  fun _ => BoundedAgentState.erase ZZClosedLeaderlessGen.s2

/-- Constant n=4 configuration from the ψ=2 isomorphic witness,
on the literal existing protocolAll8. -/
def C42 : ZZRepairAll8.protocolAll8.Configuration 4 :=
  fun _ => BoundedAgentState.erase ZZClosedLeaderlessGen.s2

/-- Constant n=3 configuration from the ψ=3 isomorphic witness,
on the ψ=3 specialization of the same six-repair transition. -/
def C33 : protocolAll8Psi3.Configuration 3 :=
  fun _ => BoundedAgentState.erase ZZClosedLeaderlessGen.s3

/-- n=3, ψ=2: some eight-edge schedule reaches a leader. -/
theorem n3_psi2_escapes8 :
    ∃ e1 e2 e3 e4 e5 e6 e7 e8 : Fin 3, ∃ i : Fin 3,
      ((ZZRepairAll8.protocolAll8.step ring3
        (ZZRepairAll8.protocolAll8.step ring3
          (ZZRepairAll8.protocolAll8.step ring3
            (ZZRepairAll8.protocolAll8.step ring3
              (ZZRepairAll8.protocolAll8.step ring3
                (ZZRepairAll8.protocolAll8.step ring3
                  (ZZRepairAll8.protocolAll8.step ring3
                    (ZZRepairAll8.protocolAll8.step ring3 C32 e1)
                    e2)
                  e3)
                e4)
              e5)
            e6)
          e7)
        e8) i).leader = true := by
  decide +kernel

/-- n=4, ψ=2: some six-edge schedule reaches a leader. -/
theorem n4_psi2_escapes8 :
    ∃ e1 e2 e3 e4 e5 e6 : Fin 4, ∃ i : Fin 4,
      ((ZZRepairAll8.protocolAll8.step ring4
        (ZZRepairAll8.protocolAll8.step ring4
          (ZZRepairAll8.protocolAll8.step ring4
            (ZZRepairAll8.protocolAll8.step ring4
              (ZZRepairAll8.protocolAll8.step ring4
                (ZZRepairAll8.protocolAll8.step ring4 C42 e1)
                e2)
              e3)
            e4)
          e5)
        e6) i).leader = true := by
  decide +kernel

/-- n=3, ψ=3: some six-edge schedule reaches a leader. -/
theorem n3_psi3_escapes8 :
    ∃ e1 e2 e3 e4 e5 e6 : Fin 3, ∃ i : Fin 3,
      ((protocolAll8Psi3.step ring3
        (protocolAll8Psi3.step ring3
          (protocolAll8Psi3.step ring3
            (protocolAll8Psi3.step ring3
              (protocolAll8Psi3.step ring3
                (protocolAll8Psi3.step ring3 C33 e1)
                e2)
              e3)
            e4)
          e5)
        e6) i).leader = true := by
  decide +kernel

#print axioms ZZRepairAll8Gen.n3_psi2_escapes8
#print axioms ZZRepairAll8Gen.n4_psi2_escapes8
#print axioms ZZRepairAll8Gen.n3_psi3_escapes8

end ZZRepairAll8Gen

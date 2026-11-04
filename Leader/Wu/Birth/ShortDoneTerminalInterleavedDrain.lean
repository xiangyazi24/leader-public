import Leader.Wu.Birth.ShortDoneTerminalFramedDrain
import Leader.Wu.Birth.ShortDoneTerminalEntranceWidthTwoLaw

set_option autoImplicit false

namespace BirthShortDoneTerminalB1Capstone

open BirthShortDoneTerminalB1EntranceR2
open BirthShortDoneTerminalB1NextGateR2

variable {n psi kappa tau : Nat}

/-- The B1 interleaved-drain capstone with the width-two ordinary-edge law
    discharged by `BirthShortDoneTerminalB1EntranceR3.widthTwoOrdinaryEdgeLaw`. -/
theorem exists_B1_interleaved_drain_or_leader_unconditional
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n)
    (C : BirthShortDoneTerminalB1EntranceR2.FC n psi kappa tau)
    (hleaderless : BirthShortDoneTerminalFirstHit.Leaderless C)
    (steps : Nat) (hsteps : steps < n) :
    ∃ w : List (Fin n),
      let D := currentRun hpsi h2 ring C w
      (∃ i, (D i).core.core.leader = true) ∨
        (BirthShortDoneTerminalFirstHit.Leaderless D ∧
          CurrentNoPreparedDeletion hpsi D ∧
          CurrentRawAlignedPrefix hpsi ring root D steps) := by
  exact
    BirthShortDoneTerminalB1NextGateR2.exists_B1_interleaved_drain_or_leader
      (kappa := kappa) (tau := tau)
      hpsi h2 ring hn
      (BirthShortDoneTerminalB1EntranceR3.widthTwoOrdinaryEdgeLaw
        (kappa := kappa) (tau := tau) hpsi h2 hn ring)
      root C hleaderless steps hsteps

end BirthShortDoneTerminalB1Capstone

#print axioms BirthShortDoneTerminalB1Capstone.exists_B1_interleaved_drain_or_leader_unconditional

import Leader.Wu.Birth.ShortDoneTerminalEntranceDrain
import Leader.Wu.Birth.ShortDoneTerminalOrdinaryLabel

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthShortDoneTerminalB1EntranceR3

open BirthShortDoneTerminalB1EntranceR2

variable {n psi kappa tau : Nat}

/--
`ordinary_edge_label_or_physical_birth` is width-polymorphic, whereas
`WidthTwoOrdinaryEdgeLaw` fixes the current consumer width to `2`.
The leaderless/birth alternatives and the two label conclusions are otherwise
identical.  The two imported modules also each define a syntactically separate
`PreparedOrdinaryOpen`; their bodies are identical, so the bridge below makes
that definitional conversion explicit before specializing the one-edge theorem
to width two.
-/
theorem widthTwoOrdinaryEdgeLaw
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn : 1 < n)
    (ring : DirectedRing n) :
    WidthTwoOrdinaryEdgeLaw (kappa := kappa) (tau := tau)
      hpsi h2 hn ring := by
  intro C e hzero hopen
  have hopen' :
      BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hpsi
        (C e) (C (ring.rightNeighbor e)) := by
    simpa only [
      BirthShortDoneTerminalB1EntranceR2.PreparedOrdinaryOpen,
      BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen] using hopen
  exact
    BirthShortDoneTerminalOrdinaryLabelR1.ordinary_edge_label_or_physical_birth
      hpsi (by decide : 0 < 2) h2 hn ring C e hzero hopen'

/-- The B1 stopped ruler-prefix theorem with the width-two edge law discharged. -/
theorem current_stopped_labelSweepPrefix_outcome_of_open
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : FC n psi kappa tau)
    (hleaderless : BirthShortDoneTerminalFirstHit.Leaderless C)
    (steps : Nat) (hsteps : steps < n)
    (hopen : OrdinaryOpenAlong hpsi h2 ring C
      (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root steps)) :
    (∃ t, t ≤ steps ∧
        ∃ i,
          ((currentRun hpsi h2 ring C
            (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root t)) i).core.core.leader =
            true) ∨
      (let D := currentRun hpsi h2 ring C
          (PPLLPpsiLabelGeometry.labelSweepPrefixSchedule ring root steps)
       BirthShortDoneTerminalFirstHit.Leaderless D ∧
         CurrentRawAlignedPrefix hpsi ring root D steps) := by
  exact
    BirthShortDoneTerminalB1EntranceR2.current_stopped_labelSweepPrefix_outcome_of_open
      (kappa := kappa) (tau := tau)
      hpsi h2 ring hn
      (widthTwoOrdinaryEdgeLaw
        (kappa := kappa) (tau := tau) hpsi h2 hn ring)
      root C hleaderless steps hsteps hopen

end BirthShortDoneTerminalB1EntranceR3

#print axioms BirthShortDoneTerminalB1EntranceR3.widthTwoOrdinaryEdgeLaw
#print axioms BirthShortDoneTerminalB1EntranceR3.current_stopped_labelSweepPrefix_outcome_of_open

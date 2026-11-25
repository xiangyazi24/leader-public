import Leader.L4.ShortInheritedRank
import Leader.L4.ShortLeastForward

namespace L4.ShortArbitraryIssue
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetMIS1Ring
open ShortGateChart ShortLeastForward ShortInheritedRank ShortControllerEntrance

/-- The physical old-byte chart now discharges the final nomination
hypothesis of the inherited-rank clock, including parked ADMIT. -/
theorem actual_chart_issue0_mean {s n : Nat} (x : Raw s n) (A : H2Ready x)
    (r : Fin n) (R : header x r=true) (N : 9<n) :
    ∃ C : Chart (header x), C.root=r ∧ C.L≤9 ∧
      (∀ y : Raw s n, H2Ready y → (∀ q, header y q=header x q) →
        L4.IIDExpectedHittingTimeAtMost (rawNext s)
          (fun z : Raw s n => pc (z r).mis1=8) y (n*10^8095)) := by
  obtain ⟨C,Cr,Cs,g,Gp,Gl,G⟩ := chart_exists_gate x A.1 r R N
  have Nom : ForwardNomination (s:=s) C :=
    fun y Y H nonzero=>nominate_forward C (by omega) y Y H g Gp Gl G nonzero
  refine ⟨C,Cr,Cs,?_⟩
  intro y Y H
  have D := issue0_expected C Cs (by omega) Nom y Y H
  simpa only [Cr] using D

#print axioms actual_chart_issue0_mean
end L4.ShortArbitraryIssue

import Leader.L4.ShortArbitraryIssue
import Leader.L4.ShortActualIssueClock

namespace L4.ShortArbitraryClean
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetMIS1Ring
open ShortGateChart ShortLeastForward ShortInheritedRank ShortActualIssueClock

/-- Arbitrary inherited MIS1 bytes on a fixed H2Ready H1 fiber need
no prior good owner history. The monitored target counts a cleaned
chart only after an actual owner door mark with literal old ISSUE0. -/
theorem actual_owner_clean_mean {s n : Nat} (x : Raw s n) (A : H2Ready x)
    (r : Fin n) (R : header x r=true) (N : 9<n) :
    ∃ C : Chart (header x), C.root=r ∧ C.L≤9 ∧
      (∀ y : Raw s n, H2Ready y → (∀ q, header y q=header x q) →
        Height.IIDExpectedHittingTimeAtMost (ShortActualIssueClock.step C) (Goal C) (y,false)
          ((10^8095+19)*n)) := by
  obtain ⟨C,Cr,Cs,g,Gp,Gl,G⟩ := chart_exists_gate x A.1 r R N
  have Nom : ForwardNomination (s:=s) C :=
    fun y Y H nonzero=>nominate_forward C (by omega) y Y H g Gp Gl G nonzero
  exact ⟨C,Cr,Cs,fun y Y H=>from_inherited_expected C Cs (by omega) Nom y Y H⟩

#print axioms actual_owner_clean_mean
end L4.ShortArbitraryClean

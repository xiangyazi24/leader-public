import Leader.L4.ReportFastLateWitness
import Leader.L4.ReportLatePhysicalNomination

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportLeaseOwner ReportGoodEightBank ReportFastRawEvent ReportGenerationAncestry
open ReportLatePhysicalNomination

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}
variable {d : Sheet} {hh : ∃ i,h i=true} {G : GapInput h} {r : Owner h}

theorem late_debt_bound (C : Chart h) (x : Raw s n) (q : ReportLatePhysicalNomination.Stage)
    (I : On d C x q) : debt C.L C.a q≤C.a+2*C.L+3 := by
  cases q with
  | sealBack i =>
    have B := I.shape.2.1
    simp only [ReportLatePhysicalNomination.debt]
    omega
  | sealIssue | sealForward _ | commitIssue | commitForward _ | done =>
    simp only [ReportLatePhysicalNomination.debt] <;> omega

/-- The remaining semantic input to the late rank. A producer has to
enter from the actual staged history and keep its exact physical
witness through each nonterminal mark. No expected-time premise. -/
structure LateHistoryRows (d : Sheet) (hh : ∃ i,h i=true)
    (P : Raw s n→Prop) (G : GapInput h) (r : Owner h) where
  inv : ReportFastPostACQ.Context d hh P G r→List (Fin n)→Raw s n×ReportLatePhysicalNomination.Stage→Prop
  enter : ∀ (A : ReportFastPostACQ.Context d hh P G r) u,
    ReportFastPostACQ.UntilSeal A u →
    ReportFastPostACQ.Stop A (rawRun A.base u) →
    GoodEightBank d hh P G (rawRun A.base u) →
    inv A u (rawRun A.base u,.sealIssue)
  base : ∀ A u z, inv A u z→Cached d hh P z.1 ∧
    On d (charter G r) z.1 z.2 ∧ Enabled d G r z.1 z.2
  keep : ∀ A u z e, inv A u z→¬Finished (monitor d (charter G r) z e)→
    inv A u (monitor d (charter G r) z e)

noncomputable def LateHistoryRows.toLateSealCommit
    (R : LateHistoryRows d hh P G r) :
    LateSealCommit d hh P G r (publicationTarget G r)
      ((charter G r).a+2*(charter G r).L+3) := by
  let C := charter G r
  let targ := publicationTarget G r
  have endpoint (x : Raw s n) (e : Fin n) (T : ∃ j : Owner h,
    j.val=centre C ∧ classify d h x e=some j) : classify d h x e=some targ := by
    obtain ⟨j,E,H⟩ := T
    have J : j=targ := Subtype.ext E
    rw [J] at H
    exact H
  apply LateSealCommit.of_witness
  refine { centre_eq := rfl
           atRank := fun A u x k=>∃ q, R.inv A u (x,q) ∧ debt C.L C.a q=k
           enter := ?_
           bounds := ?_
           advance := ?_
           nominate := ?_ }
  · intro A u T S B
    exact ⟨_,.sealIssue,R.enter A u T S B,rfl⟩
  · intro A u x k W
    obtain ⟨q,I,E⟩ := W
    have B := R.base A u (x,q) I
    have ND : q≠.done := by
      intro Q
      subst q
      exact B.2.2
    rw [←E]
    exact ⟨debt_positive d C x q B.2.1 ND,late_debt_bound C x q B.2.1⟩
  · intro A u x e k W NC
    obtain ⟨q,I,E⟩ := W
    obtain ⟨Cache,On0,En⟩ := R.base A u (x,q) I
    have V := next_value d A.N hh G r A.fibre A.digit x Cache q On0 En e
    have ND : ¬Finished (monitor d C (x,q) e) :=
      fun T=>NC (endpoint x e (V.2.2.2 T))
    have Y := R.keep A u (x,q) e I ND
    refine ⟨debt C.L C.a (nextPhase C q e),⟨nextPhase C q e,Y,rfl⟩,?_⟩
    rw [←E]
    exact V.2.1
  · intro A u x k W
    obtain ⟨q,I,E⟩ := W
    obtain ⟨Cache,On0,En⟩ := R.base A u (x,q) I
    have ND : q≠.done := by intro Q; subst q; exact En
    obtain ⟨e,N⟩ := nomination_exists C q ND
    have V := next_value d A.N hh G r A.fibre A.digit x Cache q On0 En e
    refine ⟨e,?_⟩
    by_cases Hit : Finished (monitor d C (x,q) e)
    · exact .inl (endpoint x e (V.2.2.2 Hit))
    · have Y := R.keep A u (x,q) e I Hit
      exact .inr ⟨debt C.L C.a (nextPhase C q e),⟨nextPhase C q e,Y,rfl⟩,
        (by rw [←E]; exact V.2.2.1 N)⟩

#print axioms late_debt_bound
#print axioms LateHistoryRows.toLateSealCommit
end L4.ReportFastSplice

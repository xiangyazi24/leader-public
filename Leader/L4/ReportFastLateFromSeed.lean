import Leader.L4.ReportFastLateRankAdapter
import Leader.L4.ReportLateEnabledInvariant

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody
open ShortResetCycle (Chart)
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportLeaseOwner ReportGoodEightBank ReportFastRawEvent ReportGenerationAncestry
open ReportLatePhysicalNomination ReportLateEnabledInvariant
open ReportSealDescriptor

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

def LateSeedFacts (d : Sheet) (hh : ∃ i,h i=true)
    (P : Raw s n→Prop) (G : GapInput h) (r : Owner h)
    (x : Raw s n) : Prop :=
  (let C := charter G r
   let c := comparisonFile (params d s) (selectBytes d (x C.root))
   c/4≠3 ∧ c%4≠3) ∧
  Live d hh P G r x (x,.sealIssue)

/-- From the semantic seed only, every nonterminal actual mark keeps
the live late phase. All subsequent traffic and guards are discharged
by the literal joined rows, not a clock or path assumption. -/
def lateHistory_of_seed
    (d : Sheet) (hh : ∃ i,h i=true) (P : Raw s n→Prop)
    (G : GapInput h) (r : Owner h)
    (seed : ∀ (A : ReportFastPostACQ.Context d hh P G r) u,
      ReportFastPostACQ.UntilSeal A u →
      ReportFastPostACQ.Stop A (rawRun A.base u) →
      GoodEightBank d hh P G (rawRun A.base u) →
      LateSeedFacts d hh P G r (rawRun A.base u)) :
    LateHistoryRows d hh P G r where
  inv A u z :=
    let x := rawRun A.base u
    (let C := charter G r
     let c := comparisonFile (params d s) (selectBytes d (x C.root))
     c/4≠3 ∧ c%4≠3) ∧
    Live d hh P G r x z
  enter A u T Z B := seed A u T Z B
  base A u z H := ⟨H.2.cached,H.2.pose,
    enabled_of_live d A.N hh G r A.fibre (rawRun A.base u) H.1 z.1 z.2 H.2⟩
  keep A u z e H ND := by
    rcases live_next d A.N hh G r A.fibre A.digit (rawRun A.base u) H.1 z H.2 e with K|K
    · exact False.elim (ND K.1)
    · exact ⟨H.1,K⟩

noncomputable def lateSealCommit_of_seed
    (d : Sheet) (hh : ∃ i,h i=true) (P : Raw s n→Prop)
    (G : GapInput h) (r : Owner h)
    (seed : ∀ (A : ReportFastPostACQ.Context d hh P G r) u,
      ReportFastPostACQ.UntilSeal A u →
      ReportFastPostACQ.Stop A (rawRun A.base u) →
      GoodEightBank d hh P G (rawRun A.base u) →
      LateSeedFacts d hh P G r (rawRun A.base u)) :
    LateSealCommit d hh P G r (publicationTarget G r)
      ((charter G r).a+2*(charter G r).L+3) :=
  (lateHistory_of_seed d hh P G r seed).toLateSealCommit

end L4.ReportFastSplice

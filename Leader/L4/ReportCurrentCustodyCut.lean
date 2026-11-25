import Leader.L4.ReportSourceBankCut
import Leader.L4.ReportIndexedCurrentWait

namespace L4.ReportCurrentCustodyCut
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchAllOwners ReportGoodEightCut ReportSourceBankCut
open ReportByteRows ReportPrelaunchClock ReportIndexedCurrentWait

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- All currently waiting arithmetic owners on a single shared second-cut
history. Faulted walks are represented too; no progress claim is assumed. -/
def SharedWait (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n → Prop)
    (G : GapInput h) (x : Raw s n) : Prop :=
  ∃ z : Raw s n, ∃ w : List (Fin n),
    FirstCut d hh Q G z ∧ x=rawRun z w ∧
    ∀ C∈ownerCharts G, ∀ op : Nat, IndexedOp (params d s) op →
      readPC d C x=(2,op) →
      ∃ pre reset tail : List (Fin n),
        w=pre++reset++tail ∧ Generated d C (rawRun z pre) reset .done ∧
        CurrentWalk d C (rawRun (rawRun z pre) reset) tail op

def CurrentCustodyCut (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n → Prop)
    (G : GapInput h) (x : Raw s n) : Prop :=
  SourceBankCut d hh Q G x ∧ SharedWait d hh Q G x

theorem current_custody_of_source_bank (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (A : SourceBankCut d hh Q G x) : CurrentCustodyCut d hh Q G x :=
  ⟨A,all_current_walks_from_second_cut d N hh G F digit x A.1.1⟩

theorem current_custody_closed (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (e : Fin n)
    (A : CurrentCustodyCut d hh Q G x) : CurrentCustodyCut d hh Q G (rawNext s x e) :=
  current_custody_of_source_bank d N hh G F digit _ (source_bank_cut_closed d N hh G F digit x e A.1)

theorem current_custody_expected (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    IIDExpectedHittingTimeAtMost (rawNext s) (CurrentCustodyCut d hh Q G) x.val
      (2*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) := by
  have E := source_bank_cut_expected d N S hh G F x
  intro t
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s)
    (SourceBankCut d hh Q G) (CurrentCustodyCut d hh Q G)
    (current_custody_of_source_bank d N hh G F
      (ReportPrelaunchDoorProducer.digits_positive d S)) t x.val) (E t)

#print axioms current_custody_of_source_bank
#print axioms current_custody_closed
#print axioms current_custody_expected
end L4.ReportCurrentCustodyCut

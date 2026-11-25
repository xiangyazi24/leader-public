import Leader.L4.ReportFreshIndexedSource
import Leader.L4.ReportWriteRailSupplier

namespace L4.ReportSourceBankCut
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportGoodEightCut ReportGoodEightBank ReportFreshIndexedSource
open ReportWriteRailSupplier

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- Closed structural, bank and current source-history region. This
does not yet assert that old snapshot evaluations are ultimately correct. -/
def SourceBankCut (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n → Prop)
    (G : GapInput h) (x : Raw s n) : Prop :=
  GoodEightWith d hh Q G (FreshIndexedSourceEpoch d hh Q G) x

theorem source_bank_cut_of_second (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (A : SecondCutHistory d hh Q G x) : SourceBankCut d hh Q G x :=
  full_cut_of_history d N hh G F digit (rail_supplier d N hh G F digit)
    (FreshIndexedSourceEpoch d hh Q G) (fresh_indexed_source_rows d N hh G F digit) x A

theorem source_bank_cut_closed (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (e : Fin n)
    (A : SourceBankCut d hh Q G x) : SourceBankCut d hh Q G (rawNext s x e) :=
  full_cut_closed d N hh G F digit (rail_supplier d N hh G F digit)
    (FreshIndexedSourceEpoch d hh Q G) (fresh_indexed_source_rows d N hh G F digit) x e A

theorem source_bank_cut_expected (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    IIDExpectedHittingTimeAtMost (rawNext s) (SourceBankCut d hh Q G) x.val
      (2*ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) :=
  full_cut_expected d N S hh G F (rail_supplier d N hh G F
    (ReportPrelaunchDoorProducer.digits_positive d S))
    (FreshIndexedSourceEpoch d hh Q G)
    (fresh_indexed_source_rows d N hh G F (ReportPrelaunchDoorProducer.digits_positive d S)) x

end L4.ReportSourceBankCut

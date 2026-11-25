import Leader.L4.ReportIndexedSourcePrefix
import Leader.L4.ReportFreshAcqFile

namespace L4.ReportFreshIndexedSource
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerAcquireReturn
open ReportOwnerAcquireProvenance ReportOwnerCommandRail
open ReportGoodEightCut ReportGoodEightBank ReportFreshAcqFile
open ReportIndexedSourcePrefix

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- This theorem is on the supplied actual successful ACQ flight
    and its actual nonrestart suffix. No launch/return word is
    resampled, and the seed file is the real after-consume file. -/
theorem source_prefix_from_acq (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (issue : Raw s n) (X : Cached d hh Q issue)
    (I : ReportOwnerIssueControl.LegalIssue d C issue)
    (P : readPC d C issue=(1,acqOp (params d s)))
    (flight : List (Fin n))
    (T : BeforeConsume d C (rawNext s issue (door C)) flight)
    (Tag : (tok d C (rawRun (rawNext s issue (door C)) flight) 0).tag=3)
    (ND : (tok d C (rawRun (rawNext s issue (door C)) flight) 0).outcome≠1)
    (post : List (Fin n))
    (NR : NoRestartTape d C (rawNext s (rawRun (rawNext s issue (door C)) flight)
      (door C)) post) :
    let old := rawRun (rawNext s issue (door C)) flight
    let after := rawNext s old (door C)
    ∃ l, readPC d C after=(1,cmpOp (params d s)) ∧
      AckTape d C after post l ∧
      ownerCaptureSix d C after=(tok d C old 0).payload%64 ∧
      file d C (rawRun after post)=replay (params d s) (file d C after) l := by
  dsimp only
  let old := rawRun (rawNext s issue (door C)) flight
  let after := rawNext s old (door C)
  obtain ⟨Y,R,O,K,L,_⟩ := from_genuine_issue d C hh G F N issue X I P digit flight T Tag ND
  have A := raw_acq_consume_six d C hh G F N old Y R O K L ND digit
  have S := seed_after_acq d C after A.2.1 A.2.2.1
  have PC : PostAcqPC (params d s) (readPC d C after) := by
    rw [A.2.2.1]
    exact ⟨.inl rfl,Nat.le_refl _,by unfold cmpOp commitOp; omega⟩
  obtain ⟨l,H⟩ := ack_tape_run d C N hh G F digit after A.1 S PC post NR
  exact ⟨l,A.2.2.1,H,A.2.2.2,tape_replay d C after post l H⟩

def SourceHistory (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) (C : Chart h) (x : Raw s n) : Prop :=
  cmpOp (params d s)≤(readPC d C x).2 →
    ∃ a : Raw s n, ∃ reset lead flight post : List (Fin n),
      FirstCut d hh Q G a ∧ Generated d C a reset .done ∧
      let issue := rawRun (rawRun a reset) lead
      let old := rawRun (rawNext s issue (door C)) flight
      let after := rawNext s old (door C)
      x=rawRun after post ∧
      ReportOwnerIssueControl.LegalIssue d C issue ∧
      readPC d C issue=(1,acqOp (params d s)) ∧
      BeforeConsume d C (rawNext s issue (door C)) flight ∧
      (tok d C old 0).tag=3 ∧ (tok d C old 0).outcome≠1 ∧
      NoRestartTape d C after post ∧
      ∃ l,readPC d C after=(1,cmpOp (params d s)) ∧
        AckTape d C after post l ∧
        ownerCaptureSix d C after=(tok d C old 0).payload%64 ∧
        file d C x=replay (params d s) (file d C after) l

theorem source_history_of_acq (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (C : Chart h) (x : Raw s n)
    (A : FreshAcqEpoch d hh Q G C x) :
    SourceHistory d hh Q G C x := by
  intro Live
  obtain ⟨a,reset,lead,flight,post,B,R,E,I,P,T,Tag,ND,NR,_,_⟩ :=
    fresh_current_captures d N hh G F digit C x A Live
  let issue := rawRun (rawRun a reset) lead
  have B0 := first_cut_run d N hh G F digit a B reset
  have B1 := first_cut_run d N hh G F digit (rawRun a reset) B0 lead
  obtain ⟨l,PC,H,S,V⟩ :=
    source_prefix_from_acq d C N hh G F digit issue B1.1.1.1 I P flight T Tag ND post NR
  refine ⟨a,reset,lead,flight,post,B,R,E,I,P,T,Tag,ND,NR,l,PC,H,S,?_⟩
  rw [E]
  exact V

def FreshIndexedSourceEpoch (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) (C : Chart h) (x : Raw s n) : Prop :=
  FreshAcqEpoch d hh Q G C x ∧ SourceHistory d hh Q G C x

theorem fresh_indexed_source_rows (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) :
    FreshFileRows d hh Q G (FreshIndexedSourceEpoch d hh Q G) := by
  let A := fresh_acq_rows d N hh G F digit
  constructor
  · intro C a w B R P
    have J := A.seed C a w B R P
    exact ⟨J,source_history_of_acq d N hh G F digit C _ J⟩
  · intro C x e B Bank I
    have J := A.keep C x e B Bank I.1
    exact ⟨J,source_history_of_acq d N hh G F digit C _ J⟩

end L4.ReportFreshIndexedSource

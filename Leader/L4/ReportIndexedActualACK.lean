import Leader.L4.ReportIssuedSegment
import Leader.L4.ReportOwnerIndexedFlight
import Leader.L4.ReportIndexedLaunchData
import Leader.L4.ReportIndexedSourcePrefix

namespace L4.ReportIndexedActualACK
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerReverseControl
open ReportOwnerForwardControl ReportOwnerDoorProjection ReportOwnerForwardLocations
open ReportIssuedSegment ReportIndexedSourcePrefix ReportOwnerIndexedFlight ReportIndexedLaunchData
open ReportOwnerAcquireProvenance (BeforeConsume)

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- A literal launch row supplier, kept separate from chronological
issue extraction and the physical forward/return proof. -/
def ActualLaunch (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (Q : Raw s n → Prop) : Prop :=
  ∀ (a : Raw s n) (op : Nat), Cached d hh Q a → LegalIssue d C a →
    readPC d C a=(1,op) → IndexedOp (params d s) op →
    ForwardWait d C (rawNext s a (door C)) 0 →
    FState d C op (rawNext s a (door C)) 0
      (some (concreteSeed (params d s) (selectBytes d (a C.root)) op))

/-- Every real indexed ACK at the end of an actual word is furnished
by its own literal source issue and whole successful F/D walk. -/
theorem credit_actual_walk (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (w : List (Fin n)) (op : Nat) (Range : IndexedOp (params d s) op)
    (PC : (readPC d C (rawRun x w)).2=op)
    (Credit : CreditAt d C (rawRun x w) (door C))
    (Fresh : ActualLaunch d C hh Q) :
    ∃ pre fly : List (Fin n), ∃ sent recv : IndexedData,
      w=pre++door C::fly ∧
      let issue := rawRun x pre
      let y := rawNext s issue (door C)
      LegalIssue d C issue ∧ readPC d C issue=(1,op) ∧
      sent=concreteSeed (params d s) (selectBytes d (issue C.root)) op ∧
      FState d C op y 0 (some sent) ∧
      BeforeConsume d C y fly ∧
      Walk d C op y (some sent) fly (.backward 0 (some recv)) ∧
      tok d C (rawRun x w) 0=indexedD (params d s) op (some recv) := by
  have C0 := Credit
  obtain ⟨_,Rev,Tag,_,Live,_,_,_,_⟩ := C0
  have Wait : (readPC d C (rawRun x w)).1=2 := Rev.1.1
  obtain ⟨u,v,W,A,L,Forward,Issue,No⟩ := waiting_issued_segment d C N hh G F digit x X I w Wait
  let a := rawRun x u
  let y := rawNext s a (door C)
  have P : readPC d C a=(1,op) := Prod.ext L.2.1 (Issue.trans PC)
  let sent := concreteSeed (params d s) (selectBytes d (a C.root)) op
  have Seed := Fresh a op A L P Range Forward
  have Y := (cached_fibre d N hh Q F).closed a (door C) A
  have E : rawRun x w=rawRun y v := by
    rw [W,ShortOwnerEpochJS.raw_append]
    rfl
  obtain ⟨recv,Walk,Done⟩ := walk_successful_root d C op Range hh G F N y Y (some sent) Seed
    digit v No (E ▸ Tag) (E ▸ Live)
  exact ⟨u,v,sent,recv,W,L,P,rfl,Seed,No,Walk,E.symm ▸ Done.packet⟩

theorem literal_actual_launch (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) :
    ActualLaunch d C hh Q := by
  intro a op A L P Range W
  exact (ReportIndexedLaunchData.indexed_door_seed_of_forward
    d C op Range hh G F N a A L P W).2

/-- Link each indexed credit in a checked source log to its literal
packet walk. The ACK stays at its physical position on the same word. -/
theorem receipt_actual_walk (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l)
    (r : Receipt) (M : r∈l) (Range : IndexedOp (params d s) r.1) :
    ∃ pre fly post : List (Fin n), ∃ sent recv : IndexedData,
      w=(pre++door C::fly)++door C::post ∧
      let issue := rawRun x pre
      let y := rawNext s issue (door C)
      let old := rawRun y fly
      LegalIssue d C issue ∧ readPC d C issue=(1,r.1) ∧
      sent=concreteSeed (params d s) (selectBytes d (issue C.root)) r.1 ∧
      FState d C r.1 y 0 (some sent) ∧
      BeforeConsume d C y fly ∧
      Walk d C r.1 y (some sent) fly (.backward 0 (some recv)) ∧
      CreditAt d C old (door C) ∧
      r.2=tok d C old 0 ∧ r.2=indexedD (params d s) r.1 (some recv) := by
  obtain ⟨u,post,W,E,Credit⟩ := tape_receipt_origin d C x w l T r M
  have P : (readPC d C (rawRun x u)).2=r.1 := (congrArg Prod.fst E).symm
  obtain ⟨pre,fly,sent,recv,U,J,PC,Data,Seed,No,Walk,Tok⟩ :=
    credit_actual_walk d C N hh G F digit x X I u r.1 Range P Credit (literal_actual_launch d C N hh G F)
  have V : rawRun x u=rawRun (rawNext s (rawRun x pre) (door C)) fly := by
    rw [U,ShortOwnerEpochJS.raw_append]
    rfl
  exact ⟨pre,fly,post,sent,recv,W.trans (by rw [U]),J,PC,Data,Seed,No,Walk,V ▸ Credit,
    V ▸ congrArg Prod.snd E,(congrArg Prod.snd E).trans Tok⟩

end L4.ReportIndexedActualACK

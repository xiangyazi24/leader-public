import Leader.L4.ReportIndexedActualACK
import Leader.L4.ReportGoodEightCut

namespace L4.ReportIndexedCurrentWait
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportPrelaunchAllOwners ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportOwnerSerial
open ReportOwnerForwardControl ReportOwnerReverseControl
open ReportIndexedLaunchData ReportIssuedSegment ReportOwnerIndexedFlight ReportIndexedActualACK ReportGoodEightCut
open ReportOwnerAcquireProvenance (BeforeConsume)

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- An unfinished real indexed flight on this exact suffix. The current accumulator
may be poisoned (`none`); no successful reply, consume, or ACK is assumed. -/
def CurrentWalk (d : Sheet) (C : Chart h) (x : Raw s n) (w : List (Fin n)) (op : Nat) : Prop :=
  ∃ pre fly : List (Fin n), ∃ c : Cursor,
    w=pre++door C::fly ∧
    let issue := rawRun x pre
    let y := rawNext s issue (door C)
    let sent := concreteSeed (params d s) (selectBytes d (issue C.root)) op
    LegalIssue d C issue ∧ readPC d C issue=(1,op) ∧
    FState d C op y 0 (some sent) ∧
    BeforeConsume d C y fly ∧
    Walk d C op y (some sent) fly c ∧
    At d C op (rawRun x w) c

/-- From an arbitrary legal ISSUE anchor. This alone does not claim a genuine RESET. -/
theorem current_walk_from_issue (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (w : List (Fin n)) (op : Nat)
    (Range : IndexedOp (params d s) op) (PC : readPC d C (rawRun x w)=(2,op)) :
    CurrentWalk d C x w op := by
  obtain ⟨pre,fly,W,A,L,H,Same,No⟩ :=
    waiting_issued_segment d C N hh G F digit x X I w (congrArg Prod.fst PC)
  let a := rawRun x pre
  let y := rawNext s a (door C)
  have Op : (readPC d C (rawRun x w)).2=op := congrArg Prod.snd PC
  have P : readPC d C a=(1,op) := Prod.ext L.2.1 (Same.trans Op)
  let sent := concreteSeed (params d s) (selectBytes d (a C.root)) op
  have Seed := literal_actual_launch d C N hh G F a op A L P Range H
  have Y := (cached_fibre d N hh Q F).closed a (door C) A
  obtain ⟨_,c,J⟩ := walk_run d C op Range hh G F N y Y (some sent) Seed digit fly No
  have E : rawRun x w=rawRun y fly := by
    rw [W,ShortOwnerEpochJS.raw_append]
    rfl
  exact ⟨pre,fly,c,W,L,P,Seed,No,J,E.symm ▸ walk_at d C op y (some sent) fly c J⟩

/-- Exact same-tape strengthening: a genuine own RESET completed after the common
first cut, and the current indexed flight lies on its literal remaining suffix. -/
theorem current_walk_from_second_cut (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (z : Raw s n) (Z : FirstCut d hh Q G z)
    (w : List (Fin n)) (A : ∃ pre reset tail : List (Fin n),
      w=pre++reset++tail ∧ Generated d C (rawRun z pre) reset .done)
    (op : Nat) (Range : IndexedOp (params d s) op)
    (PC : readPC d C (rawRun z w)=(2,op)) :
    ∃ pre reset tail : List (Fin n),
      w=pre++reset++tail ∧ Generated d C (rawRun z pre) reset .done ∧
      CurrentWalk d C (rawRun (rawRun z pre) reset) tail op := by
  obtain ⟨pre,reset,tail,W,R⟩ := A
  have B := first_cut_run d N hh G F digit z Z pre
  obtain ⟨X,Park⟩ := cached_genuine_full_parked d C N hh F (rawRun z pre) B.1.1.1 reset R
  let a := rawRun (rawRun z pre) reset
  have P : readPC d C a=(1,1) := pc_fields d C a .issue1 (by decide) Park.1.1
  have I : LegalIssue d C a := by
    rcases seed_at_genuine_receipt d C N hh F (rawRun z pre) B.1.1.1 reset R with I|⟨k,J⟩|⟨k,J⟩
    · exact I
    · have H := J.1.1
      change (readPC d C a).1=2 at H
      rw [P] at H
      contradiction
    · have H := J.1.1
      change (readPC d C a).1=2 at H
      rw [P] at H
      contradiction
  have E : rawRun z w=rawRun a tail := by
    rw [W,ShortOwnerEpochJS.raw_append,ShortOwnerEpochJS.raw_append]
  exact ⟨pre,reset,tail,W,R,current_walk_from_issue d C N hh G F digit a X I tail op Range (E ▸ PC)⟩

/-- The common second-cut tape simultaneously supplies the exact live indexed
walk at each waiting owner. Owner membership alone does not replace that tape. -/
theorem all_current_walks_from_second_cut (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (A : SecondCutHistory d hh Q G x) :
    ∃ z : Raw s n, ∃ w : List (Fin n),
      FirstCut d hh Q G z ∧ x=rawRun z w ∧
      ∀ C∈ownerCharts G, ∀ op : Nat, IndexedOp (params d s) op →
        readPC d C x=(2,op) →
        ∃ pre reset tail : List (Fin n),
          w=pre++reset++tail ∧ Generated d C (rawRun z pre) reset .done ∧
          CurrentWalk d C (rawRun (rawRun z pre) reset) tail op := by
  obtain ⟨z,w,Z,E,All⟩ := A
  refine ⟨z,w,Z,E,?_⟩
  intro C M op Range PC
  exact current_walk_from_second_cut d C N hh G F digit z Z w (All C M) op Range (E ▸ PC)

end L4.ReportIndexedCurrentWait

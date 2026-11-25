import Leader.L4.ReportFastPostACQ
import Leader.L4.ReportFastAcqPrefix

namespace L4.ReportFastPostACQContext
open AllSizeProtocol PhysicalCustody ShortResetCycle
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportOwnerIssueControl
open ReportFastAcqAllowed ReportFastAcqTrack ReportFastAcqPrefix
open ReportFastNominationBridge ReportAdaptiveFibre ReportLeaseOwner
open ReportGoodEightCut ReportByteRows ReportFastPostACQ

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

/-- Build the arithmetic context only after the actual first ACQ hit.
Its issue anchor is the real pre-launch state and its flight word is
the complete mapped pre-consume tape from the genuine F launch. -/
theorem context_at_first_consume (d : Sheet) (B : Fin 5→Chart h) (D : Fin 5→Bool)
    (N : 1<n) (Spos : 0<s) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q)
    (r : Owner h) (Chart : B 2=charter G r)
    (x : Raw s n) (First : FirstCut d hh Q G x)
    (Issue : LegalIssue d (charter G r) x)
    (PC : readPC d (charter G r) x=(1,acqOp (params d s)))
    (Lroom : (params d s).digits≤(charter G r).a)
    (Mroom : (params d s).digits≤(charter G r).b)
    (Rroom : (params d s).digits≤(charter G r).L-((charter G r).a+(charter G r).b))
    (z : Z s n) (Seed : z.base.raw=rawNext s x (door (charter G r)))
    (w : List (Fin n)) (e : Fin n)
    (OnPrefix : ∀ u v,w=u++v →
      On d (B 2) (ReportFastAcqPrefix.run d B D z u).base.raw (ReportFastAcqPrefix.run d B D z u).base.cur)
    (Live : (ReportFastAcqPrefix.run d B D z w).base.cur≠.done)
    (Done : (ReportFastAcqPrefix.run d B D z (w++[e])).base.cur=.done) :
    ∃ A : Context d hh Q G r, A.issue=x ∧ A.flight=actual d B D z w ∧
      A.base=(ReportFastAcqPrefix.run d B D z (w++[e])).base.raw := by
  obtain ⟨Before,Mark,Tag,_,Good⟩ := first_done_inputs d B D z w e OnPrefix Live Done
  rw [Seed,Chart] at Before Tag Good
  let A : Context d hh Q G r := ⟨N,Spos,F,x,First,Issue,PC,actual d B D z w,
    Before,Tag,Good,Lroom,Mroom,Rroom⟩
  refine ⟨A,rfl,rfl,?_⟩
  rw [ReportFastAcqPrefix.run_raw,actual_snoc,ShortOwnerEpochJS.raw_snoc,Mark,Chart,Seed]
  rfl

#print axioms context_at_first_consume
end L4.ReportFastPostACQContext

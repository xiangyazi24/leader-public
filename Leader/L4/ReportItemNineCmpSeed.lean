import Leader.L4.ReportItemNineTrace

namespace L4.ReportItemNineCmpSeed
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows ReportPrelaunchK1Geometry ReportPrelaunchClock
open ReportOwnerReverseControl ReportIndexedSourcePrefix ReportItemNineTrace

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

/-- Zero comparison input immediately after the genuine ACQ root consume.
This is a raw-file fact, independent of authentication of selector/capture. -/
theorem raw_acq_consume_zero_cmp (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x)
    (Shape : ReverseWait d C x 0)
    (O : (readPC d C x).2=acqOp (params d s))
    (Tag : (tok d C x 0).tag=3)
    (Match : (tok d C x 0).opcode=acqOp (params d s))
    (Live : (tok d C x 0).fault=false) (ND : (tok d C x 0).outcome≠1) :
    item9Read (params d s) (rootBytes d C (rawNext s x (door C))) .input=0 := by
  let p := params d s
  let v := rootBytes d C x
  let u := rootBytes d C (rawNext s x (door C))
  let t := tok d C x 0
  have E := door_file d C x N ((cached_fibre d N hh Q F).mask x X)
  have Z := item9_acq_zero_cmp p v t Shape.1.1 O Tag Match Live ND
  have B := congrFun (item9_read_congr p u
    ((liftSourcePatch p (source p v t).1).apply v) E) .input
  exact B.trans Z

#print axioms raw_acq_consume_zero_cmp
end L4.ReportItemNineCmpSeed

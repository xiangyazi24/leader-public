import Leader.L4.ReportWriteHitLedger

namespace L4.ReportIndexedFlightContract
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows
open ReportPrelaunchK1Geometry ReportGenerationAncestry
open ReportLeaseOwner ReportLeaseGrants ReportGoodEightCut
open ReportOwnerCommandRail ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerAcquireReturn ReportIndexedSourcePrefix
open ReportJoinedWriteValue ReportWriteHitLedger

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def StagedWriteInstall (d : Sheet) (hh : ∃ i,h i=true)
    (Q : Raw s n→Prop) (G : GapInput h) : Prop :=
  ∀ (r : Owner h) (issue : Raw s n) (flight : List (Fin n))
    (j : Fin (params d s).digits) (f : Tok),
    let C := charter G r
    let p := params d s
    let cap := acqCaptureIndex p (selectBytes d (issue C.root))
    FirstCut d hh Q G issue →
    (∀ i,i<C.L→h (out C i)=true→rawGrant d issue (out C i) (C.route.port i)=true) →
    (∀ e,e<p.digits→e<C.a ∧ e<C.b ∧ e<C.L-C.a-C.b) →
    IssuedSegment d C issue flight (writeOp p+j.val) f →
    WriteFlightResult d C issue flight j (cap/2%2) f

theorem staged_write_install (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) :
    StagedWriteInstall d hh Q G := by
  intro r issue flight j f
  dsimp only
  intro A _Held Room H
  exact write_flight_result d N hh G F digit r issue flight j f
    A.1.1.1 (Room j.val j.isLt).2.1 H

/-- Exact StagedPrefixFrame type, now also for the header
    case and later enabled commands at different offsets. -/
theorem staged_prefix_frame (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) :
    StagedPrefixFrame d hh Q G := by
  intro r x e j prior
  dsimp only
  intro A Rail Past _Bound J
  exact staged_prefix_step d N hh G F r x e j (1-prior)
    A.1.1.1 Rail Past J

/-- This is the exact later-endpoint equality needed by the WRITE
    branch of CertifiedPrefix, after its *actual matching* ACK.
    All subsequent marks are from the same nonrestart generation. -/
theorem staged_credit_to_prefix (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (r : Owner h) (issue : Raw s n) (flight post : List (Fin n))
    (j : Fin (params d s).digits) (prior : Nat) (f : Tok)
    (J : j.val<(charter G r).b)
    (H : WriteFlightResult d (charter G r) issue flight j prior f)
    (PC : readPC d (charter G r)
      (rawRun (rawNext s issue (door (charter G r))) flight)=(2,writeOp (params d s)+j.val))
    (X : Cached d hh Q
      (rawNext s (rawRun (rawNext s issue (door (charter G r))) flight) (door (charter G r))))
    (A : StrongSerial d (charter G r)
      (rawNext s (rawRun (rawNext s issue (door (charter G r))) flight) (door (charter G r))))
    (NextPC : PostAcqPC (params d s) (readPC d (charter G r)
      (rawNext s (rawRun (rawNext s issue (door (charter G r))) flight) (door (charter G r)))))
    (NR : NoRestartTape d (charter G r)
      (rawNext s (rawRun (rawNext s issue (door (charter G r))) flight) (door (charter G r))) post) :
    let C := charter G r
    let p := params d s
    let old := rawRun (rawNext s issue (door C)) flight
    let after := rawNext s old (door C)
    reportDigitPair p (selectBytes d (rawRun after post (nextAt (centre C) j.val))) (1-prior)=
      BitVec.ofNat (2*ReportByteRows.d p) (f.payload%2^(2*ReportByteRows.d p)) := by
  dsimp only
  let C := charter G r
  let p := params d s
  let old := rawRun (rawNext s issue (door C)) flight
  let after := rawNext s old (door C)
  obtain ⟨pre,suf,k,E,K,Site,Lane,T,R,Off,Permit,Old,Target,Send,New,AtAck,Credit⟩ := H
  have L := preview_logical Credit.2.2.2.2.2.2.2.1
  change logical p.digits (readPC d C after).2=logical p.digits (readPC d C old).2+1 at L
  rw [PC] at L
  change logical p.digits (readPC d C after).2=logical p.digits (writeOp p+j.val)+1 at L
  have Past : logical p.digits (writeOp p+j.val)<logical p.digits (readPC d C after).2 := by omega
  rw [Site] at AtAck
  exact (staged_prefix_run d N hh G F digit r after post j (1-prior)
    X A NextPC Past J NR).trans AtAck

end L4.ReportIndexedFlightContract

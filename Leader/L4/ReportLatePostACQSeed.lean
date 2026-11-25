import Leader.L4.ReportFastLateFromSeed
import Leader.L4.ReportAcquireAllCaptures
import Leader.L4.ReportIndexedSideLease
import Leader.L4.ReportACQSelectedCapture

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportFastPostACQ
open ReportByteRows ReportRawProjection ReportOwnerIssueControl ReportOwnerAcquireReturn
open ReportOwnerCommandRail ReportACQToWriteNoCommit ReportACQSelectedCapture
open ReportAcquireAllCaptures ReportIndexedSideLease ReportIngressOwnership
open ReportGenerationAncestry (centre)
open ReportLeaseOwner ReportGoodEightBank ReportLateEnabledInvariant
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportFastRawEvent
open ReportSealDescriptor ReportDigitArithmetic

set_option maxRecDepth 16000
set_option maxHeartbeats 16000000
variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}
variable {d : Sheet} {hh : ∃ i,h i=true} {G : GapInput h} {r : Owner h}

private theorem fold_cmp_lt (β R x : Nat) (a : Bool) (c j : Nat) :
    (readWriteFold β R x a c j).outCmp < 3 := by
  induction j with
  | zero => change 0 < 3; decide
  | succ j IH =>
    change cmp (nextDigit β R x a c j (readWriteFold β R x a c j).carry).1
      (digit β j R) (readWriteFold β R x a c j).outCmp<3
    unfold cmp
    split
    · decide
    · split
      · decide
      · exact IH

theorem late_seed_actual (A : Context d hh P G r) (u : List (Fin n))
    (T : UntilSeal A u) (End : Stop A (rawRun A.base u)) :
    LateSeedFacts d hh P G r (rawRun A.base u) := by
  let C := charter G r
  let x := rawRun A.base u
  let p := params d s
  have Cmp := seed_info A
  have H := seal_handoff A u T End
  have NR := (literal_tape A u T).1
  have PC : readPC d C x=(1,sealOp p) := H.2.2.2.2.2.2.2.1
  have Maths := H.2.2.2.2.2.2.2.2.1
  have Out := (item9_at_seal p A.inputs (selectBytes d (x C.root)) Maths).2
  have HC := canonical_centre G r
  have Caps := all_captures_after_consume d C hh G A.fibre A.N A.issue A.first.1.1.1
    A.legal A.pc A.first.1.2 A.digit A.flight A.before A.tag A.good u NR
  have HH := held_end d (out C C.a) (C.route.port C.a) A.base u
    (Caps.2.2.2 C.a HC.2.1 HC.2.2.1).2
  rw [HC.2.2.2.1] at HH
  have BaseLT : (readPC d C A.base).2<sealOp p := by
    rw [Cmp.pc]
    change cmpOp p < sealOp p
    unfold cmpOp sealOp
    have Dig : 0<p.digits := A.digit
    omega
  have OldSel := authentic_capture_is_current d G r hh A.fibre A.N A.issue A.first.1.1.1
    A.legal A.pc A.digit A.flight A.before A.tag A.good [] trivial trivial BaseLT
  have NC : (readPC d C x).2≠commitOp p := by
    rw [PC]
    unfold sealOp commitOp
    omega
  have Safe := no_commit_before_noncommit_end d C hh A.fibre A.N A.digit A.base u
    Cmp.first.1.1.1 Cmp.post NR NC
  have Rail := (strong_run d C A.N hh G A.fibre A.digit A.base Cmp.first.1.1.1 Cmp.serial u).2.2
  have Sel := selector_through_no_commit d G r hh A.fibre A.N A.base u Cmp.first.1.1.1 Rail Safe
  have Capture := (raw_postacq_run d C hh A.fibre A.N A.digit A.base u
    Cmp.first.1.1.1 Cmp.post NR).2.2
  have EqCap : ReportWriterPayload.capturedSelector p (selectBytes d (x C.root))=
      ReportWriterPayload.capturedSelector p (selectBytes d (A.base C.root)) := by
    rw [captured_selector_index,captured_selector_index]
    change ownerCaptureIndex d C x / 2 % 2 = ownerCaptureIndex d C A.base / 2 % 2
    rw [Capture]
  refine ⟨?_,live_seed d hh G r x H.2.2.2.2.1.1.1.1 H.2.2.2.2.2.1
    ⟨H.2.2.2.2.2.2.1,PC⟩ (H.2.2.2.2.1.1.2 _ HC.2.2.1) HH ?_⟩
  · change (item9Read p (selectBytes d (x C.root)) .output)/4≠3 ∧
      (item9Read p (selectBytes d (x C.root)) .output)%4≠3
    rw [Out]
    have L : (item9Left p A.inputs p.digits).outCmp<3 := fold_cmp_lt .. 
    have R : (item9Right p A.inputs p.digits).outCmp<3 := fold_cmp_lt ..
    unfold item9Out
    omega
  · exact Sel.trans (OldSel.symm.trans
      (EqCap.symm.trans (ReportSealDescriptor.descriptor_fields p (selectBytes d (x C.root))).2.1.symm))

noncomputable def lateSealCommit_actual
    (d : Sheet) (hh : ∃ i,h i=true) (P : Raw s n→Prop)
    (G : GapInput h) (r : Owner h) :
    LateSealCommit d hh P G r (publicationTarget G r)
      ((charter G r).a+2*(charter G r).L+3) :=
  lateSealCommit_of_seed d hh P G r (fun A u T End _ => late_seed_actual A u T End)

#print axioms lateSealCommit_actual
#print axioms late_seed_actual
end L4.ReportFastSplice

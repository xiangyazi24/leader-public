import Leader.L4.ReportGenerationAncestry
import Leader.L4.ReportLeaseStep

/-! The nonheader old-pair WRITE owns digits in the inactive bank.
This uses only the local payload/centre relation, not Good8. -/
namespace L4.ReportJoinedBankFrame
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportRawProjection ReportLeaseStep ReportOwnerProvenanceTransport
open ReportGenerationAncestry

variable {s n : Nat} {h : Fin n→Bool}

/-- Exact selected report sheet; the other implementation sheet is
eliminated by the already checked raw pair projection. -/
theorem raw_left_bank_frame (d : Sheet) (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i) (H : h e=false)
    (sel : Nat) (S : sel<2)
    (D : rankReady (params d s) false (selectBytes d (x e)) 1=true →
      ancestryWriteTarget (params d s)
        (publicationToken (params d s) false (selectBytes d (x e)) 1)≠sel) :
    reportDigitPair (params d s) (selectBytes d (rawNext s x e e)) sel=
      reportDigitPair (params d s) (selectBytes d (x e)) sel := by
  let p := params d s
  let u := selectBytes d (x e)
  let v := selectBytes d (x (rightNeighbor e))
  have B := report_nonheader_left_bank_frame p (h (rightNeighbor e)) u v sel S D
  have A : reportDigitPair p (selectBytes d (rawNext s x e e)) sel=
      reportDigitPair p ((row p (false,h (rightNeighbor e)) (u,v)).1.apply u) sel := by
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    have L:=raw_low_pair d x e N mask (reportBankDigitAddress p sel i)
      (reportBankDigitAddress_lt p sel i I)
    rw [H] at L
    simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    exact L.1
  exact A.trans B

theorem raw_inactive_chart_write (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (H : h (out C k)=false) (P : C.route.port k=1)
    (sel : Nat) (S : sel<2)
    (D : ancestryWriteTarget (params d s) (tok d C x k)≠sel) :
    reportDigitPair (params d s)
      (selectBytes d (rawNext s x (out C k) (out C k))) sel=
      reportDigitPair (params d s) (selectBytes d (x (out C k))) sel := by
  apply raw_left_bank_frame d x (out C k) N mask H sel S
  intro _
  rw [predecessor_projection,H,P] at D
  exact D

#print axioms raw_left_bank_frame
#print axioms raw_inactive_chart_write
end L4.ReportJoinedBankFrame
namespace L4.ReportJoinedBankFrame
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportRawProjection ReportLeaseStep ReportByteRows
variable {s n : Nat} {h : Fin n→Bool}

theorem raw_right_bank_frame (d : Sheet) (x : Raw s n) (e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i) (sel : Nat) :
    reportDigitPair (params d s) (selectBytes d (rawNext s x e (rightNeighbor e))) sel=
      reportDigitPair (params d s) (selectBytes d (x (rightNeighbor e))) sel := by
  let p := params d s
  let u := selectBytes d (x e)
  let v := selectBytes d (x (rightNeighbor e))
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  let a := reportBankDigitAddress p sel i
  have L := (raw_low_pair d x e N mask a (reportBankDigitAddress_lt p sel i I)).2
  simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
  refine L.trans ?_
  apply Patch.hold
  exact report_right_digit_mask p (h e) (h (rightNeighbor e)) u v sel i I

/-- At a nonheader site on a fixed report sheet, every mark preserves
the logical selected digit pair if any enabled local WRITE targets
the other bank. Responder and spectator marks have no WRITE premise. -/
theorem raw_all_mark_nonheader_bank_frame (d : Sheet) (x : Raw s n)
    (a e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i) (H : h a=false)
    (sel : Nat) (S : sel<2)
    (D : e=a → let p := params d s
      let u := selectBytes d (x a)
      let t := publicationToken p false u 1
      rankReady p false u 1=true → t.fault=false → writeOp p≤t.opcode →
      t.opcode<sealOp p → reportOldOffset p false u=t.opcode-writeOp p →
      ancestryWriteTarget p t≠sel) :
    reportDigitPair (params d s) (selectBytes d (rawNext s x e a)) sel=
      reportDigitPair (params d s) (selectBytes d (x a)) sel := by
  by_cases E : e=a
  · subst e
    let p := params d s
    let u := selectBytes d (x a)
    let v := selectBytes d (x (rightNeighbor a))
    have B := report_nonheader_left_bank_frame_of_enabled p (h (rightNeighbor a)) u v sel S (D rfl)
    have A : reportDigitPair p (selectBytes d (rawNext s x a a)) sel=
        reportDigitPair p ((row p (false,h (rightNeighbor a)) (u,v)).1.apply u) sel := by
      apply BitVec.eq_of_getLsbD_eq
      intro i I
      have L:=raw_low_pair d x a N mask (reportBankDigitAddress p sel i)
        (reportBankDigitAddress_lt p sel i I)
      rw [H] at L
      simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
      exact L.1
    exact A.trans B
  · by_cases R : a=rightNeighbor e
    · rw [R]
      exact raw_right_bank_frame d x e N mask sel
    · rw [raw_spectator x e a (Ne.symm E) R]

#print axioms raw_right_bank_frame
#print axioms raw_all_mark_nonheader_bank_frame
end L4.ReportJoinedBankFrame

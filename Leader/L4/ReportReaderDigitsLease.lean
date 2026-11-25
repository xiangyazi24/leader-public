import Leader.L4.ReportJoinedBankFrame
import Leader.L4.ReportLeaseGrants

namespace L4.ReportReaderDigitsLease
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportRawProjection ReportLeaseStep ReportByteRows
open ReportLeaseGrants ReportJoinedBankFrame

variable {s n : Nat}

/-- The header digit pair in either bank is preserved across any raw
mark if the old K1 grant is false. A same-mark grant update does not
authorize this old-pair WRITE. -/
theorem no_writer_protects_digit_pair (sheet : Sheet) (x : Raw s n)
    (e a : Fin n) (N : 1<n)
    (Hdr : lower sheet (oldHeaders (rows s) (x a))=true)
    (Denied : rawGrant sheet x a 1=false) (sel : Nat) :
    reportDigitPair (params sheet s) (selectBytes sheet (rawNext s x e a)) sel=
      reportDigitPair (params sheet s) (selectBytes sheet (x a)) sel := by
  let h (i : Fin n) := lower sheet (oldHeaders (rows s) (x i))
  have mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i := fun _=>rfl
  by_cases E : e=a
  · subst e
    let p := params sheet s
    let u := selectBytes sheet (x a)
    let v := selectBytes sheet (x (rightNeighbor a))
    have G : reportOldGrant p u 1=false := Denied
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    let q := reportBankDigitAddress p sel i
    have L := raw_low_pair sheet x a N mask q (reportBankDigitAddress_lt p sel i I)
    change h a=true at Hdr
    rw [Hdr] at L
    simp only [reportDigitPair,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    refine L.1.trans ?_
    apply Patch.hold
    exact report_header_denied_left_digit_mask p (h (rightNeighbor a)) u v G sel i I
  · by_cases R : a=rightNeighbor e
    · rw [R]
      exact raw_right_bank_frame sheet x e N mask sel
    · rw [raw_spectator x e a (Ne.symm E) R]

/-- The checked compatibility condition and either held side-reader
grant imply the old writer denial. Both banks' digits are protected. -/
theorem reader_grant_protects_digit_pair (sheet : Sheet) (x : Raw s n)
    (e a : Fin n) (N : 1<n) (j : Fin 3)
    (Side : j=0 ∨ j=2)
    (Hdr : lower sheet (oldHeaders (rows s) (x a))=true)
    (C : Compatible (rawGrant sheet x a))
    (Held : rawGrant sheet x a j=true) (sel : Nat) :
    reportDigitPair (params sheet s) (selectBytes sheet (rawNext s x e a)) sel=
      reportDigitPair (params sheet s) (selectBytes sheet (x a)) sel := by
  apply no_writer_protects_digit_pair sheet x e a N Hdr _ sel
  apply Bool.eq_false_iff.mpr
  intro W
  exact Bool.noConfusion (Held.symm.trans
    (Side.elim (fun J=>J ▸ (C W).1) (fun J=>J ▸ (C W).2)))

#print axioms no_writer_protects_digit_pair
#print axioms reader_grant_protects_digit_pair
end L4.ReportReaderDigitsLease

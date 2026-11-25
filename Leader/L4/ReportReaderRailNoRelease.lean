import Leader.L4.ReportReaderSelectorLease

namespace L4.ReportReaderRailNoRelease
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportByteRows ReportLeaseGrants
open ReportGenerationAncestry ReportOwnerProvenanceTransport
open ReportPrelaunchClock ReportRawProjection ReportReaderSelectorLease BStarShort

variable {s n : Nat} {h : Fin n→Bool}

theorem rail_opcode (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (g : GenerationTag) (R : railState sheet C x g) :
    (readPC sheet C x).2=g.op := by
  unfold railState at R
  cases K : g.rail <;> rw [K] at R <;> exact congrArg Prod.snd R.1

/-- A healthy old F0 in this owner rail is exactly an own RESET
flight. E/T and reverse packets cannot be mistaken for release. -/
theorem reset_token_requires_zero (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (g : GenerationTag) (R : railState sheet C x g)
    (k : Nat) (K : k<C.L) (Tag : (tok sheet C x k).tag=2)
    (Live : (tok sheet C x k).fault=false)
    (Reset : (tok sheet C x k).opcode=0) : g.op=0 := by
  unfold railState at R
  cases E : g.rail with
  | issue =>
      rw [E] at R
      rw [R.2 k K] at Tag
      contradiction
  | forward i t =>
      rw [E] at R
      have T := R.2.2.2.2 k K
      by_cases B : k<i
      · rw [T,if_pos B] at Tag
        contradiction
      · rw [T,if_neg B] at Tag Live Reset
        by_cases P : k=i
        · rw [if_pos P] at Live Reset
          exact (R.2.2.2.1 Live).symm.trans Reset
        · rw [if_neg P] at Tag
          contradiction
  | reverse i t =>
      rw [E] at R
      have T := R.2.2.2.2 k K
      by_cases B : k<i
      · rw [T,if_pos B] at Tag
        contradiction
      · rw [T,if_neg B] at Tag
        by_cases P : k=i
        · rw [if_pos P,R.2.2.1] at Tag
          contradiction
        · rw [if_neg P] at Tag
          contradiction

/-- The post-ACQ positive owner opcode supplies the no-release premise
at its chart header. This uses the same owner/occurrence, rather than
a neighboring launch or a reconstructed tape. -/
theorem positive_rail_no_release (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (g : GenerationTag) (R : railState sheet C x g)
    (Pos : (readPC sheet C x).2≠0)
    (k : Nat) (K : k<C.L) (Header : h (out C k)=true) :
    (oldIncidence sheet x (out C k)).release (C.route.port k)=false := by
  apply Bool.eq_false_iff.mpr
  intro A
  have H : tok sheet C x k=reportK (params sheet s) true
      (selectBytes sheet (x (out C k))) (C.route.port k) := by
    rw [predecessor_projection,Header]
    rfl
  have B := (release_old_token (params sheet s) true
    (selectBytes sheet (x (out C k))) (C.route.port k)).mp A
  rw [←H] at B
  exact Pos ((rail_opcode sheet C x g R).trans
    (reset_token_requires_zero sheet C x g R k K B.1 B.2.1 B.2.2))

#print axioms rail_opcode
#print axioms reset_token_requires_zero
#print axioms positive_rail_no_release
end L4.ReportReaderRailNoRelease

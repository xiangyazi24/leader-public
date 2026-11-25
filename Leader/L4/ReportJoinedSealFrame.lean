import Leader.L4.ReportGenerationAncestry
import Leader.L4.ReportLeaseStep

namespace L4.ReportJoinedSealFrame
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetRawHooks
open ReportByteRows ReportLeaseStep ReportGenerationAncestry
variable {s n : Nat} {h : Fin n→Bool}

theorem raw_header_right_seal_step (d : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (Hdr : h (rightNeighbor e)=true) :
    let p := params d s
    let u := selectBytes d (x e)
    let v := selectBytes d (x (rightNeighbor e))
    let y := selectBytes d (rawNext s x e (rightNeighbor e))
    (ancestryCommitOpportunity p (h e) true u v → reportOldSeal p y=none) ∧
    (¬ancestryCommitOpportunity p (h e) true u v → reportOldSeal p y=reportOldSeal p v) := by
  dsimp only
  let p := params d s
  let u := selectBytes d (x e)
  let v := selectBytes d (x (rightNeighbor e))
  let y := selectBytes d (rawNext s x e (rightNeighbor e))
  have E : reportOldSeal p y=reportOldSeal p ((row p (h e,true) (u,v)).2.apply v) := by
    apply report_seal_of_extract
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    have L := (raw_low_pair d x e N mask (sealBase p+i)
      (by change sealBase p+i<grantBase p; unfold grantBase; omega)).2
    rw [Hdr] at L
    simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    exact L
  exact ⟨fun H => E.trans (report_header_right_seal_clear p _ _ _ H),
    fun H => E.trans (report_header_right_seal_hold p _ _ _ H)⟩

#print axioms raw_header_right_seal_step

theorem raw_header_left_seal_step (d : Sheet) (x : Raw s n) (e : Fin n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (Hdr : h e=true) :
    let p := params d s
    let u := selectBytes d (x e)
    let y := selectBytes d (rawNext s x e e)
    (reportHeaderResetSeal p u → reportOldSeal p y=none) ∧
    (reportHeaderSetSeal p u → reportOldSeal p y=some (publicationToken p true u 1).payload) ∧
    (¬reportHeaderResetSeal p u → ¬reportHeaderSetSeal p u → reportOldSeal p y=reportOldSeal p u) := by
  dsimp only
  let p := params d s
  let u := selectBytes d (x e)
  let v := selectBytes d (x (rightNeighbor e))
  let y := selectBytes d (rawNext s x e e)
  have E : reportOldSeal p y=reportOldSeal p ((row p (true,h (rightNeighbor e)) (u,v)).1.apply u) := by
    apply report_seal_of_extract
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    have L := (raw_low_pair d x e N mask (sealBase p+i)
      (by change sealBase p+i<grantBase p; unfold grantBase; omega)).1
    rw [Hdr] at L
    simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    exact L
  exact ⟨fun H => E.trans (report_header_left_seal_clear p _ _ _ H),
    fun H => E.trans (report_header_left_seal_install p _ _ _ H),
    fun A B => E.trans (report_header_left_seal_hold p _ _ _ A B)⟩

#print axioms raw_header_left_seal_step

/-- All-mark frame when the relevant old-pair seal actions are absent.
The two enabled cases are exported separately by the endpoint lemmas. -/
theorem raw_header_seal_hold_of_no_event (d : Sheet) (x : Raw s n)
    (a e : Fin n) (N : 1<n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i) (Hdr : h a=true)
    (NR : e=a → ¬reportHeaderResetSeal (params d s) (selectBytes d (x a)))
    (NS : e=a → ¬reportHeaderSetSeal (params d s) (selectBytes d (x a)))
    (NC : a=rightNeighbor e → ¬ancestryCommitOpportunity (params d s) (h e) true
      (selectBytes d (x e)) (selectBytes d (x a))) :
    reportOldSeal (params d s) (selectBytes d (rawNext s x e a))=
      reportOldSeal (params d s) (selectBytes d (x a)) := by
  by_cases E : e=a
  · subst e
    exact (raw_header_left_seal_step d x a N mask Hdr).2.2 (NR rfl) (NS rfl)
  · by_cases R : a=rightNeighbor e
    · subst a
      exact (raw_header_right_seal_step d x e N mask Hdr).2 (NC rfl)
    · rw [ReportRawProjection.raw_spectator x e a (Ne.symm E) R]

#print axioms raw_header_seal_hold_of_no_event
end L4.ReportJoinedSealFrame

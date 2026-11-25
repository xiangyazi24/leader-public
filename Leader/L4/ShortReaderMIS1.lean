import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortReaderMIS1
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow

private theorem reader_work_right {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) {k : Nat} (f : Field 96 k) (bound : f.offset+k≤93) :
    let z := ((MISByteRows.row (pairHeader x e) (pairIn x e)).2).apply (pairIn x e).2
    f.read (rawNext s x e (rightNeighbor e)).mis1=f.read z := by
  let h := pairHeader x e
  let old := pairIn x e
  have G : f.read (patchPair (ShortGeo.mis.patches 3 h old (BStarShort.shortMIS h old)) old).2
      = f.read (patchPair (BStarShort.shortMIS h old) old).2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have ho : ¬ShortGeo.mis.owned (f.offset+i) := by
      intro E
      have le := E.1
      change 93≤f.offset+i at le
      omega
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact (ShortGeo.work_agrees_outside _ 3 h old (BStarShort.shortMIS h old) _ ho).2
  dsimp only
  rw [show rawNext s x e (rightNeighbor e)=(largePair (rows s) (x e,x (rightNeighbor e))).2 by
    simp [rawNext,AllSizeS1Geometry.step,Ne.symm sep]]
  exact G

private theorem reader_work_left {s n : Nat} (x : Raw s n) (e : Fin n)
    {k : Nat} (f : Field 96 k) (W : ReaderWindow f) :
    let z := ((MISByteRows.row (pairHeader x e) (pairIn x e)).1).apply (pairIn x e).1
    f.read (rawNext s x e e).mis1=f.read z := by
  let h := pairHeader x e
  let old := pairIn x e
  have G : f.read (patchPair (ShortGeo.mis.patches 3 h old (BStarShort.shortMIS h old)) old).1
      = f.read (patchPair (BStarShort.shortMIS h old) old).1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have ho : ¬ShortGeo.mis.owned (f.offset+i) := by
      intro E
      have le := E.1
      change 93≤f.offset+i at le
      rcases W with H|H <;> omega
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact (ShortGeo.work_agrees_outside _ 3 h old (BStarShort.shortMIS h old) _ ho).1
  have E : f.read (patchPair (BStarShort.shortMIS h old) old).1 =
      f.read (patchPair (MISByteRows.row h old) old).1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact BStarShort.mis_apply_outside h old (f.offset+i) (by rcases W with H|H; exact .inl (by omega); exact .inr (by omega))
  dsimp only
  rw [show rawNext s x e e=(largePair (rows s) (x e,x (rightNeighbor e))).1 by
    simp [rawNext,AllSizeS1Geometry.step]]
  exact G.trans E

/-- Every physical mark retains a no-writer H1 header's bank and selector
fields, including when the protected header is the old responder.
No hypotheses are made about any other header or either adjacent token. -/
theorem no_writer_frame_raw {s n w : Nat} (x : Raw s n) (e i : Fin n)
    (f : Field 96 w) (W : ReaderWindow f)
    (head : header x i=true) (no : (x i).mis1.getLsbD 90=false) :
    f.read (rawNext s x e i).mis1=f.read (x i).mis1 := by
  by_cases Ei : i=e
  · subst i
    exact (reader_work_left x e f W).trans (by
      simpa only [pairHeader,pairIn,head] using
        reader_outgoing_pair f W (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 no)
  · by_cases Ri : i=rightNeighbor e
    · subst i
      have bd : f.offset+w≤93 := by
        rcases W with H|H <;> omega
      exact (reader_work_right x e (Ne.symm Ei) f bd).trans (by
        simpa only [pairHeader,pairIn,head] using
          reader_incoming_pair f W (header x e) (x e).mis1 (x (rightNeighbor e)).mis1 no)
    · rw [reset_remote_frame_raw x e i Ei Ri]

/-- In particular the actual selector and both (hence also the selected)
bank bits are stable in presence of either held reader and no writer. -/
theorem held_reader_frame_raw {s n : Nat} (x : Raw s n) (e i : Fin n)
    (head : header x i=true) (no : (x i).mis1.getLsbD 90=false)
    (_held : (x i).mis1.getLsbD 91=true ∨ (x i).mis1.getLsbD 89=true) :
    (lane 92 1 (by decide)).read (rawNext s x e i).mis1=
      (lane 92 1 (by decide)).read (x i).mis1 ∧
    (lane 87 2 (by decide)).read (rawNext s x e i).mis1=
      (lane 87 2 (by decide)).read (x i).mis1 := by
  refine ⟨no_writer_frame_raw x e i _ ?_ head no,no_writer_frame_raw x e i _ ?_ head no⟩
  · exact .inr ⟨by decide,by decide⟩
  · exact .inl ⟨by decide,by decide⟩

/-- The bank endpoint chosen by this row's single selector bit. -/
def selectedValue (w : BitVec 96) : Bool :=
  ((lane 87 2 (by decide)).read w).getLsbD
    (1-((lane 92 1 (by decide)).read w).toNat)

theorem held_reader_value_raw {s n : Nat} (x : Raw s n) (e i : Fin n)
    (head : header x i=true) (no : (x i).mis1.getLsbD 90=false)
    (held : (x i).mis1.getLsbD 91=true ∨ (x i).mis1.getLsbD 89=true) :
    selectedValue (rawNext s x e i).mis1=selectedValue (x i).mis1 := by
  have H := held_reader_frame_raw x e i head no held
  unfold selectedValue
  rw [H.1,H.2]

/-- Exact compatibility with the row's native selector/bank readout. -/
theorem selectedValue_eq (w : BitVec 96) :
    selectedValue w=w.getLsbD (88-get w 92 1 (by decide)) := by
  let i := get w 92 1 (by decide)
  have hi : i<2 := (BitVec.extractLsb' 92 1 w).isLt
  change ((BitVec.extractLsb' 87 2 w).getLsbD (1-i))=w.getLsbD (88-i)
  simp only [BitVec.getLsbD_extractLsb',show 1-i<2 by omega,decide_true,Bool.true_and]
  congr 1
  omega

end L4.ShortReaderMIS1

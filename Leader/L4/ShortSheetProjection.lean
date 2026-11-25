import Leader.L4.PhysicalShortSheet
import Leader.L4.BStarShort

namespace L4.ShortSheetProjection
open AllSizeProtocol PhysicalCustody PhysicalShortSheet MISByteCodec

/-- The joined pair uses the actual pre-mark per-sheet eligibility mask on
both endpoints. Includes cached geometry and grant filtering. -/
theorem exact_fields {s n k : Nat} (j : Sheet) (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (f : Field 96 k) :
    let h := (mask j x e, mask j x (rightNeighbor e))
    let z := (bytes j (x e), bytes j (x (rightNeighbor e)))
    let q := PhysicalShortSheet.pairStep (rows s) h z
    f.read (bytes j (rawNext s x e e)) = f.read q.1 ∧
      f.read (bytes j (rawNext s x e (rightNeighbor e))) = f.read q.2 := by
  have P := exact_raw_step j x e
  have L := congrArg (fun g => f.read (g e)) P
  have R := congrArg (fun g => f.read (g (rightNeighbor e))) P
  exact ⟨by simpa [sliceStep] using L, by simpa [sliceStep, Ne.symm sep] using R⟩

private theorem bit_not_owned (i : Nat) (h : i < 93) : ¬ ShortGeo.mis.owned i := by
  intro H
  change 93 ≤ i ∧ _ at H
  omega

/-- Any field entirely below the geometry cache agrees with the concrete
work row, including its real grant filter at bits 89..91. -/
theorem work_fields {a : LargeParams} (b : LargeRows a) (h : Pair Bool)
    (x : Pair (BitVec 96)) {k : Nat} (f : Field 96 k) (lo : f.offset+k ≤ 93) :
    let q := PhysicalShortSheet.pairStep b h x
    let w := patchPair (b.mis h x) x
    f.read q.1 = f.read w.1 ∧ f.read q.2 = f.read w.2 := by
  have O (i : Nat) (hi : i < k) : ¬ ShortGeo.mis.owned (f.offset+i) :=
    bit_not_owned _ (by omega)
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact (ShortGeo.work_agrees_outside _ 3 h x (b.mis h x) _ (O i hi)).1
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact (ShortGeo.work_agrees_outside _ 3 h x (b.mis h x) _ (O i hi)).2

/-- Any work field below the geometry cache can be read on the raw endpoints, uniformly
for MIS1, MIS2 and MIS3. No frozen-mask or layout assumption is used. -/
theorem work_to_raw_field {s n k : Nat} (j : Sheet) (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (f : Field 96 k) (lo : f.offset+k ≤ 93) :
    let h := (mask j x e, mask j x (rightNeighbor e))
    let z := (bytes j (x e), bytes j (x (rightNeighbor e)))
    let w := patchPair ((rows s).mis h z) z
    f.read (bytes j (rawNext s x e e)) = f.read w.1 ∧
      f.read (bytes j (rawNext s x e (rightNeighbor e))) = f.read w.2 := by
  have E := exact_fields j x e sep f
  have W := work_fields (rows s) (mask j x e, mask j x (rightNeighbor e))
    (bytes j (x e), bytes j (x (rightNeighbor e))) f lo
  exact ⟨E.1.trans W.1, E.2.trans W.2⟩

/-- Only the initiator grant band can differ from the underlying MIS byte
row. A disjoint field projection lifts both endpoint equalities. -/
theorem byte_work_to_raw_field {s n k : Nat} (j : Sheet) (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (f : Field 96 k) (lo : f.offset+k ≤ 93)
    (away : f.offset+k ≤ 89 ∨ 92 ≤ f.offset) :
    let h := (mask j x e, mask j x (rightNeighbor e))
    let z := (bytes j (x e), bytes j (x (rightNeighbor e)))
    let w := patchPair (MISByteRows.row h z) z
    f.read (bytes j (rawNext s x e e)) = f.read w.1 ∧
      f.read (bytes j (rawNext s x e (rightNeighbor e))) = f.read w.2 := by
  have W := work_to_raw_field j x e sep f lo
  refine ⟨W.1.trans ?_, W.2⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact BStarShort.mis_apply_outside _ _ _ (away.imp (by omega) (by omega))

/-- The original MIS1 token projection generalizes verbatim to every
physical short sheet, with the sheet's own actual old header flags. -/
theorem work_to_raw {s n : Nat} (j : Sheet) (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (k : Fin 3) :
    let h := (mask j x e, mask j x (rightNeighbor e))
    let z := (bytes j (x e), bytes j (x (rightNeighbor e)))
    let w := patchPair (MISByteRows.row h z) z
    (kField k).read (bytes j (rawNext s x e e)) = (kField k).read w.1 ∧
      (kField k).read (bytes j (rawNext s x e (rightNeighbor e))) = (kField k).read w.2 :=
  byte_work_to_raw_field j x e sep (kField k)
    (by change 19*(2-k.val)+19 ≤ 93; omega)
    (.inl (by change 19*(2-k.val)+19 ≤ 89; omega))

#print axioms exact_fields
#print axioms work_fields
#print axioms work_to_raw_field
#print axioms byte_work_to_raw_field
#print axioms work_to_raw
end L4.ShortSheetProjection

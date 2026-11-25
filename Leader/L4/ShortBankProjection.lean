import Leader.L4.ShortSelectorFlip
import Leader.L4.ShortReaderMIS1
import Leader.L4.ShortSelectorParity

namespace L4.ShortBankProjection
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow
open ShortReaderMIS1 ShortSelectorParity

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


theorem receiver_banks {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true) :
    let f := lane 87 2 (by decide)
    f.read (rawNext s x e (rightNeighbor e)).mis1 = f.read (x (rightNeighbor e)).mis1 := by
  exact (reader_work_right x e sep _ (by decide)).trans (by
    simpa only [pairHeader,pairIn,head] using
      bankproj_receiver_pair (header x e) (x e).mis1 (x (rightNeighbor e)).mis1)

private theorem bank_congr (v w : BitVec 96) (j : Nat) (J : j<2)
    (H : (lane 87 2 (by decide)).read v = (lane 87 2 (by decide)).read w) :
    v.getLsbD (88-j) = w.getLsbD (88-j) := by
  have e := congrArg (fun b : BitVec 2 => b.getLsbD (1-j)) H
  simp only [Field.read,BitVec.getLsbD_extractLsb',show 1-j<2 by omega,
    decide_true,Bool.true_and] at e
  change v.getLsbD (87+(1-j)) = w.getLsbD (87+(1-j)) at e
  rwa [show 87+(1-j)=88-j by omega] at e

theorem selector_stutter {s n : Nat} (x : Raw s n) (e i : Fin n)
    (head : header x i=true)
    (stab : (rawNext s x e i).mis1.getLsbD 92 = (x i).mis1.getLsbD 92) :
    selectedValue (rawNext s x e i).mis1 = selectedValue (x i).mis1 := by
  rw [selectedValue_eq,selectedValue_eq,selector_toNat,selector_toNat,stab,←selector_toNat]
  let j := get (x i).mis1 92 1 (by decide)
  have J : j<2 := ((lane 92 1 (by decide)).read (x i).mis1).isLt
  change (rawNext s x e i).mis1.getLsbD (88-j) = (x i).mis1.getLsbD (88-j)
  by_cases Ei : i=e
  · subst i
    let f := lane (88-j) 1 (by omega)
    have W : ReaderWindow f := .inl ⟨by change 87≤88-j; omega,by change 88-j+1≤89; omega⟩
    have H := (reader_work_left x e f W).trans (by
      simpa only [pairHeader,pairIn,head] using
        bankproj_initiator_pair (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1)
    have t := congrArg (fun b : BitVec 1 => b.getLsbD 0) H
    change (BitVec.extractLsb' (88-j) 1 (rawNext s x e e).mis1).getLsbD 0 = (BitVec.extractLsb' (88-j) 1 (x e).mis1).getLsbD 0 at t
    simpa only [BitVec.getLsbD_extractLsb',show 0<1 by decide,Nat.add_zero,decide_true,Bool.true_and] using t
  · by_cases Ri : i=rightNeighbor e
    · subst i
      exact bank_congr _ _ j J (receiver_banks x e (Ne.symm Ei) head)
    · rw [reset_remote_frame_raw x e i Ei Ri]

theorem selected_of_guard_write {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (guard : selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1)
    (write : (rawNext s x e (rightNeighbor e)).mis1.getLsbD 92 =
      ((((oldK (header x e) (x e).mis1 0).payload/2)%2)==1)) :
    selectedValue (rawNext s x e (rightNeighbor e)).mis1 =
      (((oldK (header x e) (x e).mis1 0).payload%2)==1) := by
  let j := ((oldK (header x e) (x e).mis1 0).payload/2)%2
  have J : j<2 := Nat.mod_lt _ (by decide)
  have w : (rawNext s x e (rightNeighbor e)).mis1.getLsbD 92 = (j==1) := write
  have D : (j==1).toNat=j := by
    by_cases E : j=1
    · simp [E]
    · have Z : j=0 := by omega
      simp [Z]
  rw [selectedValue_eq,selector_toNat,w,D]
  exact (bank_congr _ _ j J (receiver_banks x e sep head)).trans guard.2.2.2.2.2.2.2

/-- The native guarded COMMIT chooses the payload Boolean at the old
responder, with no assumptions on the other headers or neighboring tokens. -/
theorem guarded_commit_selected {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (guard : selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1) :
    selectedValue (rawNext s x e (rightNeighbor e)).mis1 =
      (((oldK (header x e) (x e).mis1 0).payload%2)==1) :=
  selected_of_guard_write x e sep head guard
    (ShortSelectorFlip.selector_responder_raw_publish x e sep head guard)

#print axioms guarded_commit_selected
#print axioms receiver_banks
#print axioms selector_stutter
#print axioms selected_of_guard_write
end L4.ShortBankProjection

import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortStageSealRowsRaw
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow

theorem left_bank_seal_projection {s n k : Nat} (x : Raw s n) (e : Fin n)
    (f : Field 96 k) (B : f.offset+k≤89) :
    f.read (rawNext s x e e).mis1 =
      f.read (((MISByteRows.row (pairHeader x e) (pairIn x e)).1).apply (x e).mis1) := by
  rw [show rawNext s x e e=(largePair (rows s) (x e,x (rightNeighbor e))).1 by
    simp [rawNext,AllSizeS1Geometry.step]]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have H : ¬ShortGeo.mis.owned (f.offset+i) := by
    intro E
    have F := E.1
    change 93≤f.offset+i at F
    omega
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  exact ((ShortGeo.work_agrees_outside _ 3 (pairHeader x e) (pairIn x e)
    (BStarShort.shortMIS (pairHeader x e) (pairIn x e)) _ H).1).trans
      (BStarShort.mis_apply_outside _ _ _ (.inl (by omega)))

theorem stage_out {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x e=true) (k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) 1=some k)
    (t : Token) (Tg : oldK true (x e).mis1 1=t) (tag : t.tag=2)
    (live : t.fault=false) (op : t.opcode=4) :
    let y := rawNext s x e
    (kField 1).read (y e).mis1=encode T ∧
      (kField k).read (y (rightNeighbor e)).mis1 =
        encode (if stageSealOwner (x e).mis1 t.payload then t else faultToken 2) := by
  have H := stage_forward_pair (header x (rightNeighbor e)) (x e).mis1
    (x (rightNeighbor e)).mis1 k t dst Tg tag live op
  have L := (work_to_raw x e sep 1).1
  have R := (work_to_raw x e sep k).2
  simp only [pairHeader,pairIn,head] at L R
  exact ⟨L.trans H.1,R.trans H.2⟩

theorem seal_out {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x e=true) (k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) 1=some k)
    (t : Token) (Tg : oldK true (x e).mis1 1=t) (tag : t.tag=2)
    (live : t.fault=false) (op : t.opcode=5) :
    let y := rawNext s x e
    (kField 1).read (y e).mis1=encode T ∧
      (kField k).read (y (rightNeighbor e)).mis1 =
        encode (if stageSealOwner (x e).mis1 t.payload && sealBankMatches (x e).mis1 t.payload
          then t else faultToken 2) := by
  have H := seal_forward_pair (header x (rightNeighbor e)) (x e).mis1
    (x (rightNeighbor e)).mis1 k t dst Tg tag live op
  have L := (work_to_raw x e sep 1).1
  have R := (work_to_raw x e sep k).2
  simp only [pairHeader,pairIn,head] at L R
  exact ⟨L.trans H.1,R.trans H.2⟩

theorem stage_bank {s n : Nat} (x : Raw s n) (e : Fin n) (head : header x e=true)
    (t : Token) (i : Fin 2) (Tg : oldK true (x e).mis1 1=t) (tag : t.tag=2)
    (live : t.fault=false) (op : t.opcode=4) :
    let f := lane (88-i.val) 1 (by omega)
    f.read (rawNext s x e e).mis1 =
      if stageSealOwner (x e).mis1 t.payload && i.val==(t.payload/2)%2 then
        BitVec.ofNat 1 (t.payload%2==1).toNat
      else f.read (x e).mis1 := by
  let f := lane (88-i.val) 1 (by omega)
  have A := left_bank_seal_projection x e f (by change 88-i.val+1≤89; omega)
  simp only [pairHeader,pairIn,head] at A
  exact A.trans (stage_bank_pair (header x (rightNeighbor e)) (x e).mis1
    (x (rightNeighbor e)).mis1 t i Tg tag live op)

theorem seal_value {s n : Nat} (x : Raw s n) (e : Fin n) (head : header x e=true)
    (t : Token) (Tg : oldK true (x e).mis1 1=t) (tag : t.tag=2)
    (live : t.fault=false) (op : t.opcode=5) :
    let f := lane 83 4 (by decide)
    f.read (rawNext s x e e).mis1 =
      if stageSealOwner (x e).mis1 t.payload && sealBankMatches (x e).mis1 t.payload
      then BitVec.ofNat 4 (8+t.payload) else f.read (x e).mis1 := by
  have A := left_bank_seal_projection x e (lane 83 4 (by decide)) (by decide)
  simp only [pairHeader,pairIn,head] at A
  exact A.trans (seal_value_pair (header x (rightNeighbor e)) (x e).mis1
    (x (rightNeighbor e)).mis1 t Tg tag live op)

#print axioms stage_out
#print axioms seal_out
#print axioms stage_bank
#print axioms seal_value
end L4.ShortStageSealRowsRaw

import Leader.L4.BStarBitGateArrival

namespace L4.BStarBitUniqueGate
open AllSizeProtocol BStarTrace BStarLongWork BStarLongCommand BStarLongClaims
open BStarH6WordChart BStarH6Ordinal BStarAcquireAnchors BStarLongFiberOwner
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarResetChartTouch BStarClearanceOffset BStarBitGateGeometry

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- On a fixed offset-correct owner chart, the BIT gate lies at just
one index, regardless of the scheduler or extent of the owner word. -/
theorem chart_no_second_gate {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ a,oldH6 B x a=oldH6 B base a)
    (ready : correct (oldH6 B base) hh 5 x)
    {i j : Nat} (I : i≤len) (J : j≤len)
    (G : gate bitOp (S.getD i fall).2 (longGeometry B (x (S.getD i fall).1))=true)
    (H : gate bitOp (S.getD j fall).2 (longGeometry B (x (S.getD j fall).1))=true) :
    i=j := by
  let hs := oldH6 B base
  let a := S.getD i fall
  let b := S.getD j fall
  have sz := C.length
  have ia : a∈S := by
    change S.getD i fall∈S
    rw [←List.getElem_eq_getD (h:=show i<S.length by omega)]
    exact List.getElem_mem _
  have ib : b∈S := by
    change S.getD j fall∈S
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  obtain ⟨ka,oa⟩ := (bit_gate_iff hp hh fixed ready a.1 a.2).mp G
  obtain ⟨kb,ob⟩ := (bit_gate_iff hp hh fixed ready b.1 b.2).mp H
  have qa : a.2=1 := Fin.ext ka
  have qb : b.2=1 := Fin.ext kb
  have Ha := (C.entries a ia).2
  have Hb := (C.entries b ib).2
  rw [qa] at Ha
  rw [qb] at Hb
  have W : word hs a.1=word hs b.1 := by
    have L := congrArg (fun v => addressWord (total hs) v (cmdDispl 1)) (Ha.trans Hb.symm)
    change addressWord (total hs) (owner (total hs) (word hs a.1) (cmdDispl 1)) (cmdDispl 1)=
      addressWord (total hs) (owner (total hs) (word hs b.1) (cmdDispl 1)) (cmdDispl 1) at L
    rw [address_inverse,address_inverse] at L
    rw [Int.emod_eq_of_lt (word_range hs a.1 hh).1 ((word_range hs a.1 hh).2),
      Int.emod_eq_of_lt (word_range hs b.1 hh).1 ((word_range hs b.1 hh).2)] at L
    exact L
  have eq := BStarNativeOffsetPhysical.same_ordinal_same_word hs hh a.1 b.1 (oa.trans ob.symm) W
  exact (List.getD_inj (by omega) (by omega) C.nodup).mp (Prod.ext eq (qa.trans qb.symm))

end L4.BStarBitUniqueGate

import Leader.L4.BStarNumericChartCoverage
import Leader.L4.BStarCopyRightStrip
import Leader.L4.BStarCommitOperands

namespace L4.BStarNativeCanonicalSites
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarH6Ordinal
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors BStarResetChartTouch
open BStarNumericChartCoverage BStarNumericConsecutive BStarNumericChronology BStarNumericCarry
open BStarCopyRightStrip (addr)
open BStarCommitOperands (first_word right_back)
open BStarLongFiberOwner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

private theorem addr_back (i : Fin n) (k : Nat) : addr (back i k) k=i := by
  induction k with
  | zero =>
    rw [back_zero]
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  | succ k ih =>
    have E : addr (back i (k+1)) (k+1)=addr (rightNeighbor (back i (k+1))) k := by
      apply Fin.ext
      unfold addr rightNeighbor
      dsimp
      rw [Nat.mod_add_mod]
      congr 1
      omega
    rw [E,right_back]
    exact ih

theorem canonical_sites {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {op width : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j=>S.getD j fall) len op x 0 w len ds)
    (flags : ∀ i, (longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (L : (significantSites hp base (fun j=>S.getD j fall) len).length=width)
    (j : Fin width) :
    digitSite hp base (fun k=>S.getD k fall) len width L j=addr (S.getD len fall).1 j.val := by
  let slot := fun k=>S.getD k fall
  let sites := significantSites hp base slot len
  let i := digitSite hp base slot len width L j
  let root := (slot len).1
  let h := oldH6 B base
  have jl : j.val<sites.length := by rw [L]; exact j.isLt
  have eqOrd := congrArg (fun s : List Nat => s[j.val]?) (aligned_ordinals hp C A flags notShort)
  rw [List.getElem?_map,List.getElem?_eq_getElem jl,List.getElem?_eq_getElem (by simp),
    List.getElem_range] at eqOrd
  have ord : ordinal h hh i=j.val := Option.some.inj eqOrd
  have inSites : i∈sites := List.getElem_mem jl
  unfold sites significantSites at inSites
  obtain ⟨k,hk,atK⟩ := List.mem_map.mp inSites
  have index := (List.mem_filter.mp hk).2
  have kl : k<len := List.mem_range.mp (List.mem_filter.mp hk).1
  have E : (slot k).2=1 := by
    unfold significantIndex at index
    exact Fin.ext (beq_iff_eq.mp (Bool.and_eq_true_iff.mp index).1)
  have klS : k<S.length := by have := C.length; omega
  have mem : slot k∈S := by
    dsimp only [slot]
    rw [←List.getElem_eq_getD (h:=klS)]
    exact List.getElem_mem _
  have atSite : slot k=(i,1) := Prod.ext atK E
  have own := (C.entries _ mem).2
  rw [atSite] at own
  have endpoint10 := endpoint_spec h hh o 10
  rw [←C.terminal] at endpoint10
  have rootH : h root=true := endpoint10.1
  have rootO : commandOwner h root 1=o.val := endpoint10.2.1
  have wi : word h i=word h root := by
    have O : owner (total h) (word h i) (cmdDispl 1)=
        owner (total h) (word h root) (cmdDispl 1) := own.trans rootO.symm
    have E := congrArg (fun t => addressWord (total h) t (cmdDispl 1)) O
    rw [address_inverse,address_inverse] at E
    rw [Int.emod_eq_of_lt (word_range h i hh).1 (word_range h i hh).2,
      Int.emod_eq_of_lt (word_range h root hh).1 (word_range h root hh).2] at E
    exact E
  obtain ⟨_,F⟩ := ordinal_spec h hh i
  have prev := first_word hh i (ordinal h hh i) F
  have eq := header_word_injective h (a₁:=⟨back i (ordinal h hh i),F.1⟩)
    (a₂:=⟨root,rootH⟩) (prev.trans wi)
  have near := congrArg Subtype.val eq
  change back i (ordinal h hh i)=root at near
  rw [ord] at near
  change i=addr root j.val
  rw [←near,addr_back]

end L4.BStarNativeCanonicalSites

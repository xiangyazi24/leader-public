import Leader.L4.BStarCommitOperands
import Leader.L4.BStarPaceWidth

namespace L4.Height.ProductionGeometry
open AllSizeProtocol BStarLongWork BStarTrace BStarH6WordChart BStarH6Ordinal BStarAcquireLiteralChain
open BStarAcquireVisitOrder BStarResetChartTouch BStarLongFiberOwner BStarAcquireAnchors

-- The ordinal injection of BStarGateOwnerUnique uses only these geometry imports.
private theorem ordinal_owner_inj {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i j : Fin n) (k : Fin 11) (O : ordinal h hh i=ordinal h hh j)
    (same : commandOwner h i k=commandOwner h j k) : i=j := by
  have wi := address_inverse (total h) (word h i) (cmdDispl k)
  have wj := address_inverse (total h) (word h j) (cmdDispl k)
  change addressWord (total h) (commandOwner h i k) _= _ at wi
  change addressWord (total h) (commandOwner h j k) _= _ at wj
  rw [Int.emod_eq_of_lt (word_range h i hh).1 (word_range h i hh).2] at wi
  rw [Int.emod_eq_of_lt (word_range h j hh).1 (word_range h j hh).2] at wj
  rw [same] at wi
  have E := wi.symm.trans wj
  let firstI : Header h := ⟨back i (ordinal h hh i),(ordinal_spec _ hh i).2.1⟩
  let firstJ : Header h := ⟨back j (ordinal h hh j),(ordinal_spec _ hh j).2.1⟩
  have H : firstI=firstJ := by
    apply header_word_injective h
    exact (BStarCommitOperands.first_word hh i _ (ordinal_spec _ hh i).2).trans
      (E.trans (BStarCommitOperands.first_word hh j _ (ordinal_spec _ hh j).2).symm)
  have eq : back i (ordinal h hh i)=back j (ordinal h hh i) := by
    have X : back i (ordinal h hh i)=back j (ordinal h hh j) := congrArg Subtype.val H
    exact X.trans (congrArg (back j) O.symm)
  have cancel (k : Nat) : back i k=back j k → i=j := by
    induction k with
    | zero => simp only [back_zero,imp_self]
    | succ k ih =>
      intro eq
      exact ih (by simpa only [BStarCommitOperands.right_back] using congrArg rightNeighbor eq)
  exact cancel _ eq

theorem ordinal_lt_width {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true) (W : Nat)
    (terminal : ∀ i,h (rightNeighbor i)=true → ordinal h hh i+1≤W)
    (i : Fin n) : ordinal h hh i<W := by
  by_cases next : h (rightNeighbor i)=true
  · exact terminal i next
  · have step := ordinal_body h hh i (Bool.eq_false_iff.mpr next)
    have boundNext := ordinal_lt_width h hh W terminal (rightNeighbor i)
    omega
termination_by n-ordinal h hh i
decreasing_by
  have bound := (ordinal_spec h hh (rightNeighbor i)).1
  omega

private theorem nodup_encode {A : Type} {f : A → Nat} (xs : List A) (nd : xs.Nodup)
    (inj : ∀ u ∈ xs, ∀ v ∈ xs, f u=f v → u=v) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp nd
    apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨v,hv,E⟩ := List.mem_map.mp member
      exact fresh ((inj v (List.mem_cons_of_mem _ hv) b List.mem_cons_self E) ▸ hv)
    · exact ih tail (fun u hu v hv => inj u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv))

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- The actual slot and ordinal inject all addresses of this owner's real
tour into 11W integers, even when the owner chart crosses the ring seam. -/
theorem chart_length {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (W : Nat)
    (terminal : ∀ i,oldH6 B base (rightNeighbor i)=true → oldOrdinal B base hh i+1≤W) :
    len+1≤11*W := by
  let h := oldH6 B base
  let enc (u : Pos n) := 11*ordinal h hh u.1+u.2.val
  have nd := nodup_encode (f:=enc) S C.nodup (by
    rintro ⟨i,k⟩ hi ⟨j,l⟩ hj E
    change 11*ordinal h hh i+k.val=11*ordinal h hh j+l.val at E
    have hk := k.isLt
    have hl := l.isLt
    have ord : ordinal h hh i=ordinal h hh j := by omega
    have eq : k=l := Fin.ext (by omega)
    subst l
    exact Prod.ext (ordinal_owner_inj h hh i j k ord
      ((C.entries (i,k) hi).2.trans (C.entries (j,k) hj).2.symm)) rfl)
  have sub : S.map enc ⊆ List.range (11*W) := by
    intro a ha
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
    have ord := ordinal_lt_width h hh W terminal v.1
    have hk := v.2.isLt
    apply List.mem_range.mpr
    dsimp [enc]
    omega
  simpa only [List.length_map,List.length_range,C.length] using nd.length_le_of_subset sub

#print axioms chart_length
end L4.Height.ProductionGeometry


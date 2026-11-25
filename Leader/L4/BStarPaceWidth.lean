import Leader.L4.BStarFenceReceiverChart

namespace L4.BStarPaceWidth
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarH6Ordinal
open BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain BStarAcquireRailCoverage
open BStarResetChartTouch BStarFenceReceiverChart

private theorem nodup_ofFn_injective {α : Type} {n : Nat}
    (f : Fin n → α) (inj : ∀ i j, f i=f j → i=j) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.nodup_cons]
    constructor
    · intro E
      obtain ⟨i,I⟩ := List.mem_ofFn.mp E
      exact Fin.succ_ne_zero i (inj _ _ I)
    · exact ih (fun i => f i.succ) (fun i j E => Fin.succ_inj.mp (inj _ _ E))

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- All distinct K7 digits of the actual receiving word lie inside
the owner chart, and its K10 terminal is a further occurrence.
Thus a completed forward PACE traversal pays at least width marks. -/
theorem receiver_width_le_len {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (width : Nat)
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1) :
    width ≤ len := by
  let i := (S.getD len fall).1
  let f : Fin width → Pos n := fun d => (digitFrom i d.val,7)
  obtain ⟨H,P,_⟩ := endpoint_spec (oldH6 B base) hh o 10
  rw [←C.terminal] at H P
  change oldH6 B base i=true at H
  change commandOwner (oldH6 B base) i 10=o.val at P
  have ord (d : Fin width) : oldOrdinal B base hh (f d).1=d.val :=
    (digit_from hp H width notShort d.val d.isLt).1
  have inj (a b : Fin width) (E : f a=f b) : a=b := by
    apply Fin.ext
    rw [←ord a,←ord b,E]
  have terminal : (i,(10:Fin 11))∈S := by
    have E : S.getD len fall=(i,10) := Prod.ext rfl (C.terminal ▸ rfl)
    have lt : len<S.length := by rw [C.length]; omega
    rw [←E,←List.getElem_eq_getD (h:=lt)]
    exact List.getElem_mem _
  have each (d : Fin width) : f d∈S := by
    have W := (digit_from hp H width notShort d.val d.isLt).2
    have own : commandOwner (oldH6 B base) (f d).1 (f d).2=o.val := by
      change commandOwner (oldH6 B base) (digitFrom i d.val) 7=o.val
      unfold commandOwner at P ⊢
      rw [W]
      exact P
    exact C.cover _ (by rfl) own
  let L : List (Pos n) := (i,10)::List.ofFn f
  have nodup : L.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,nodup_ofFn_injective f inj⟩
    intro Q
    obtain ⟨d,D⟩ := List.mem_ofFn.mp Q
    exact (by decide : (7:Fin 11)≠10) (congrArg Prod.snd D)
  have sub : L ⊆ S := by
    intro a A
    rcases List.mem_cons.mp A with E|E
    · exact E.symm ▸ terminal
    · obtain ⟨d,D⟩ := List.mem_ofFn.mp E
      exact D ▸ each d
  have Lsize : L.length=width+1 := by simp [L]
  have K := nodup.length_le_of_subset sub
  rw [Lsize,C.length] at K
  omega

end L4.BStarPaceWidth

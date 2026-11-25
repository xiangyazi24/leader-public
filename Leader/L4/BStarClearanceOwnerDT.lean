import Leader.L4.BStarClearanceAggregate
import Leader.L4.BStarClearanceLex

/-! Transfer of owner block charge through higher-priority ties.
Out-of-block effects may decrease a coordinate. -/
namespace L4.BStarClearanceOwnerDT
open BStarClearanceAggregate BStarClearanceLex

theorem chart_weak {A : Type} [DecidableEq A] (before after : A → Nat)
    (slots : List A) (blocks : List (List A))
    (ns : slots.Nodup) (nb : blocks.flatten.Nodup) (sub : blocks.flatten ⊆ slots)
    (outside : ∀ a∈remainder slots blocks, after a≤before a)
    (local_le : ∀ b∈blocks, total after b≤total before b) :
    total after slots≤total before slots := by
  have part := chart_partition slots blocks ns nb sub
  rw [perm_total after part,perm_total before part,total_append,total_append]
  exact Nat.add_le_add (block_total_le _ _ _ local_le) (sum_mono _ _ _ outside)

def coords {A : Type} (slots : List A) (f m d t : A → Nat) : Four :=
  ⟨total f slots,total m slots,total d slots,total t slots⟩

/-- A paying forward block is impossible on the F tie; a paying reverse
block is impossible on a subsequent D tie. This exclusion is owner-local:
other owners' command actions are not excluded or needed. -/
theorem owner_DT {A I : Type} [DecidableEq A]
    (slots : List A) (selected : List I) (block : I → List A)
    (f F d D t T : A → Nat) (isAdvance isReverse : I → Prop)
    (ns : slots.Nodup) (nb : (selected.map block).flatten.Nodup)
    (sub : (selected.map block).flatten ⊆ slots)
    (fOutside : ∀ a∈remainder slots (selected.map block), F a≤f a)
    (dOutside : ∀ a∈remainder slots (selected.map block), D a≤d a)
    (tOutside : ∀ a∈remainder slots (selected.map block), T a≤t a)
    (fWeak : ∀ i∈selected, total F (block i)≤total f (block i))
    (fCharge : ∀ i∈selected, isAdvance i → total F (block i)<total f (block i))
    (dWeak : ∀ i∈selected, ¬isAdvance i → total D (block i)≤total d (block i))
    (dCharge : ∀ i∈selected, isReverse i → total D (block i)<total d (block i))
    (tWeak : ∀ i∈selected, ¬isAdvance i → ¬isReverse i → total T (block i)≤total t (block i))
    (fTie : total F slots=total f slots) :
    total D slots≤total d slots ∧
      (total D slots=total d slots → total T slots≤total t slots) := by
  have fmap : ∀ b∈selected.map block, total F b≤total f b := by
    intro b h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    exact fWeak i hi
  have noF : ∀ i∈selected, ¬isAdvance i := by
    intro i hi H
    have N := chart_pays f F slots (selected.map block) ns nb sub fOutside fmap
      ⟨block i,List.mem_map.mpr ⟨i,hi,rfl⟩, fCharge i hi H⟩
    rw [fTie] at N
    exact Nat.lt_irrefl _ N
  have dmap : ∀ b∈selected.map block, total D b≤total d b := by
    intro b h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    exact dWeak i hi (noF i hi)
  refine ⟨chart_weak d D slots _ ns nb sub dOutside dmap,?_⟩
  intro dTie
  have noD : ∀ i∈selected, ¬isReverse i := by
    intro i hi H
    have N := chart_pays d D slots (selected.map block) ns nb sub dOutside dmap
      ⟨block i,List.mem_map.mpr ⟨i,hi,rfl⟩, dCharge i hi H⟩
    rw [dTie] at N
    exact Nat.lt_irrefl _ N
  apply chart_weak t T slots _ ns nb sub tOutside
  intro b h
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
  exact tWeak i hi (noF i hi) (noD i hi)

end L4.BStarClearanceOwnerDT

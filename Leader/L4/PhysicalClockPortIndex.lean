import Leader.L4.PhysicalClockPortBase

/-! Actual physical headers, indexed by their cyclic word addresses. -/
namespace L4.PhysicalClockPortIndex
open BStarH6WordChart BStarAcquireAnchors PhysicalClockPortBase

variable {n : Nat} {h : Fin n → Bool}

def index (hh : ∃ i, h i = true) (i : Header h) : Fin (total h) :=
  ⟨(word h i.val).toNat, by have H := word_range h i.val hh; omega⟩

theorem index_cast (hh : ∃ i, h i = true) (i : Header h) :
    ((index hh i).val : Int) = word h i.val :=
  Int.toNat_of_nonneg (word_range h i.val hh).1

theorem index_injective (hh : ∃ i, h i = true) : Function.Injective (index hh) := by
  intro i j E
  apply header_word_injective h
  change word h i.val = word h j.val
  rw [← index_cast hh i, ← index_cast hh j, E]

theorem index_surjective (hh : ∃ i, h i = true) : Function.Surjective (index hh) := by
  intro t
  have ht := t.isLt
  obtain ⟨i, E⟩ := header_word_exists h hh (t.val : Int) (by omega) (by omega)
  refine ⟨i, Fin.ext ?_⟩
  change (word h i.val).toNat = t.val
  simp [E]

noncomputable def atIndex (hh : ∃ i, h i = true) (t : Fin (total h)) : Header h :=
  Classical.choose (index_surjective hh t)

@[simp] theorem index_atIndex (hh : ∃ i, h i = true) (t : Fin (total h)) :
    index hh (atIndex hh t) = t :=
  Classical.choose_spec (index_surjective hh t)

@[simp] theorem atIndex_index (hh : ∃ i, h i = true) (i : Header h) :
    atIndex hh (index hh i) = i :=
  index_injective hh (index_atIndex hh (index hh i))

def next {m : Nat} (t : Fin m) : Fin m :=
  ⟨(t.val + 1) % m, Nat.mod_lt _ (by have H := t.isLt; omega)⟩

theorem index_right (hh : ∃ i, h i = true) (i : Header h) :
    index hh (neighborHeader hh i 2) = next (index hh i) := by
  apply Fin.ext
  have left := index_cast hh (neighborHeader hh i 2)
  rw [neighborHeader_word] at left
  change ((index hh (neighborHeader hh i 2)).val : Int) =
    (word h i.val + 2 - 1) % (total h : Int) at left
  rw [← index_cast hh i] at left
  have shift : ((index hh i).val : Int) + 2 - 1 = ((index hh i).val : Int) + 1 := by omega
  rw [shift, ← Int.natCast_one, ← Int.natCast_add, Int.ofNat_mod_ofNat] at left
  exact Int.ofNat_inj.mp left

theorem atIndex_next (hh : ∃ i, h i = true) (t : Fin (total h)) :
    atIndex hh (next t) = neighborHeader hh (atIndex hh t) 2 := by
  apply index_injective hh
  rw [index_atIndex, index_right, index_atIndex]

theorem next_index_left (hh : ∃ i, h i = true) (i : Header h) :
    next (index hh (neighborHeader hh i 0)) = index hh i := by
  rw [← index_right]
  exact neighbor_back_left hh i |>.symm ▸ rfl

theorem index_self (hh : ∃ i, h i = true) (i : Header h) :
    index hh (neighborHeader hh i 1) = index hh i := by rw [self_port]

#print axioms index_right
#print axioms atIndex_next
#print axioms next_index_left
#print axioms index_self
end L4.PhysicalClockPortIndex

import Leader.L4.BStarAcquireAnchors

namespace L4.PhysicalClockPortBase
open BStarH6WordChart BStarAcquireAnchors
variable {n : Nat}
def neighborAddress (m : Nat) (center : Int) (q : Fin 3) : Int :=
  (center+(q.val:Int)-1)%(m:Int)

noncomputable def neighborHeader {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (center : Header h) (q : Fin 3) : Header h := by
  let a := neighborAddress (total h) (word h center.val) q
  have M : 0<(total h : Int) := by exact_mod_cast total_pos h hh
  have lo : 0≤a := Int.emod_nonneg _ (Int.ne_of_gt M)
  have hi : a<(total h : Int) := Int.emod_lt_of_pos _ M
  exact Classical.choose (header_word_exists h hh a lo hi)

theorem neighborHeader_word {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (center : Header h) (q : Fin 3) :
    word h (neighborHeader hh center q).val=neighborAddress (total h) (word h center.val) q := by
  let a := neighborAddress (total h) (word h center.val) q
  have M : 0<(total h : Int) := by exact_mod_cast total_pos h hh
  exact Classical.choose_spec (header_word_exists h hh a
    (Int.emod_nonneg _ (Int.ne_of_gt M)) (Int.emod_lt_of_pos _ M))

theorem self_port {h : Fin n→Bool} (hh : ∃ i,h i=true) (i : Header h) :
    neighborHeader hh i 1=i := by
  apply header_word_injective h
  dsimp only
  rw [neighborHeader_word]
  have W := word_range h i.val hh
  unfold neighborAddress
  simp only [Fin.val_one, Int.ofNat_one, Int.add_sub_cancel]
  exact Int.emod_eq_of_lt W.1 W.2

theorem neighbor_back_left {h : Fin n→Bool} (hh : ∃ i,h i=true) (i : Header h) :
    neighborHeader hh (neighborHeader hh i 0) 2=i := by
  apply header_word_injective h
  dsimp only
  rw [neighborHeader_word,neighborHeader_word]
  have W := word_range h i.val hh
  unfold neighborAddress
  change ((((word h i.val - 1) % (total h : Int))+2-1) % (total h : Int))=word h i.val
  rw [show ∀ x : Int,x+2-1=x+1 by intro; omega, Int.emod_add_emod]
  rw [show ∀ x : Int,x-1+1=x by intro; omega]
  exact Int.emod_eq_of_lt W.1 W.2

end L4.PhysicalClockPortBase

import Leader.L4.PhysicalClockPortIndex

namespace L4.PhysicalClockPortTransfer
open BStarH6WordChart BStarAcquireAnchors
open PhysicalClockPortBase PhysicalClockPortIndex

/-- Transport a symmetric, reflexive record relation from enumerated
clock edges to all literal physical ports. Allows a singleton word ring. -/
theorem of_edges {n : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    {A : Type} (read : Header h→A) (ok : A→A→Prop)
    (self : ∀ a,ok a a) (symm : ∀ a b,ok a b→ok b a)
    (edge : ∀ j,ok (read (atIndex hh j)) (read (atIndex hh (next j)))) :
    ∀ i q,ok (read i) (read (neighborHeader hh i q)) := by
  intro i q
  have casesQ : q=0 ∨ q=1 ∨ q=2 := by
    have b := q.isLt
    rcases (show q.val=0 ∨ q.val=1 ∨ q.val=2 by omega) with v|v|v
    · exact .inl (Fin.ext v)
    · exact .inr (.inl (Fin.ext v))
    · exact .inr (.inr (Fin.ext v))
  rcases casesQ with rfl|rfl|rfl
  · apply symm
    simpa only [next_index_left,atIndex_index] using edge (index hh (neighborHeader hh i 0))
  · rw [self_port]
    exact self _
  · simpa only [←index_right,atIndex_index] using edge (index hh i)

#print axioms of_edges
end L4.PhysicalClockPortTransfer

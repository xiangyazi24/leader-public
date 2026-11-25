import Leader.L4.BStarFenceShadow

namespace L4.BStarFencePorts
open AllSizeProtocol BStarTrace BStarH6WordChart BStarH6Ordinal
open BStarCopyRightStrip (addr addr_next addr_inj)
open BStarFenceLineGeometry

/-- Labels are in travel order and include the outlet, not only the
interior HOP labels. The right terminal at the H6 site is paid by its
incoming physical edge, not its outgoing edge. -/
def leftPort {n h : Nat} (root : Fin n) (j : Fin h) : Fin n := addr root j.val

def rightCoord {h : Nat} (j : Fin h) : Nat := h-1-j.val

def rightPort {n h : Nat} (root : Fin n) (j : Fin h) : Fin n :=
  if j.val+1<h then addr root (h-2-j.val) else RearTrace.predecessor root

theorem left_labels_injective {n h : Nat} (root : Fin n) (cap : h≤n)
    {i j : Fin h} (E : leftPort root i=leftPort root j) : i=j :=
  Fin.ext (addr_inj root (Nat.lt_of_lt_of_le i.isLt cap) (Nat.lt_of_lt_of_le j.isLt cap) E)

private theorem address_ne_incoming {n : Nat} (root : Fin n) {i : Nat}
    (I : i+1<n) : addr root i≠RearTrace.predecessor root := by
  intro e
  have H : addr root (i+1)=addr root 0 := by
    rw [addr_next,e,RearTrace.right_predecessor]
    exact (Fin.ext (Nat.mod_eq_of_lt root.isLt)).symm
  have C := addr_inj root I (by have := root.isLt; omega) H
  omega

theorem right_labels_injective {n h : Nat} (root : Fin n) (cap : h≤n)
    {i j : Fin h} (E : rightPort root i=rightPort root j) : i=j := by
  have I := i.isLt
  have J := j.isLt
  by_cases a : i.val+1<h <;> by_cases b : j.val+1<h
  · simp only [rightPort,if_pos a,if_pos b] at E
    have F := addr_inj root (by omega) (by omega) E
    exact Fin.ext (by omega)
  · simp only [rightPort,if_pos a,if_neg b] at E
    exact (address_ne_incoming root (by omega) E).elim
  · simp only [rightPort,if_neg a,if_pos b] at E
    exact (address_ne_incoming root (by omega) E.symm).elim
  · exact Fin.ext (by omega)

theorem right_hop_endpoints {n h : Nat} (root : Fin n) (j : Fin h)
    (step : j.val+1<h) :
    let k := BStarFenceShadow.succIdx j step
    rightPort root j=addr root (rightCoord k) ∧
    rightNeighbor (rightPort root j)=addr root (rightCoord j) := by
  dsimp only
  have I := j.isLt
  rw [rightPort,if_pos step]
  change addr root (h-2-j.val)=addr root (h-1-(j.val+1)) ∧
    rightNeighbor (addr root (h-2-j.val))=addr root (h-1-j.val)
  constructor
  · congr 1
    omega
  · rw [←addr_next]
    congr 1
    omega

theorem right_outlet {n h : Nat} (root : Fin n) (j : Fin h)
    (last : ¬j.val+1<h) :
    rightPort root j=RearTrace.predecessor root ∧ rightCoord j=0 := by
  have I := j.isLt
  exact ⟨if_neg last, by unfold rightCoord; omega⟩

end L4.BStarFencePorts
